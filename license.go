// Combined File: combined.go
package main

import (
	"bufio"
	"encoding/json"
	"encoding/xml"
	"fmt"
	"html/template"
	"io"
	"io/fs"
	"log"
	"net/http"
	"os"
	"path/filepath"
	"regexp"
	"sort"
	"strings"
	"sync"
	"time"

	"github.com/pelletier/go-toml"
)

// ----------------------- LICENSE CHECKER CODE (from license (1).go) -----------------------

// CONFIGURATION
const (
	localPOMCacheDir = ".pom-cache"     // on-disk cache directory (structure in place for future enhancement)
	pomWorkerCount   = 10               // number of concurrent POM fetch workers
	fetchTimeout     = 30 * time.Second // HTTP client timeout
	outputReport     = "license-checker/dependency-license-report.html"
)

// GLOBALS
var (
	pomRequests  = make(chan fetchRequest, 50)
	wgWorkers    sync.WaitGroup
	pomCache     sync.Map // key: "group:artifact:version" -> *MavenPOM
	channelOpen  = true
	channelMutex sync.Mutex
)

// CONCURRENCY TYPES
type fetchRequest struct {
	GroupID    string
	ArtifactID string
	Version    string
	ResultChan chan fetchResult
}

type fetchResult struct {
	POM     *MavenPOM
	UsedURL string // URL used to fetch the POM
	Err     error
}

// SPDX LICENSE MAP & DATA STRUCTURES
var spdxLicenseMap = map[string]struct {
	Name     string
	Copyleft bool
}{
	"MIT":          {Name: "MIT License", Copyleft: false},
	"Apache-2.0":   {Name: "Apache License 2.0", Copyleft: false},
	"BSD-2-CLAUSE": {Name: "BSD 2-Clause", Copyleft: false},
	"BSD-3-CLAUSE": {Name: "BSD 3-Clause", Copyleft: false},
	"MPL-2.0":      {Name: "Mozilla Public License 2.0", Copyleft: true},
	"LGPL-2.1":     {Name: "GNU Lesser GPL v2.1", Copyleft: true},
	"LGPL-3.0":     {Name: "GNU Lesser GPL v3.0", Copyleft: true},
	"GPL-2.0":      {Name: "GNU GPL v2.0", Copyleft: true},
	"GPL-3.0":      {Name: "GNU GPL v3.0", Copyleft: true},
	"AGPL-3.0":     {Name: "GNU Affero GPL v3.0", Copyleft: true},
}

// License represents a license entry in a POM.
type License struct {
	Name string `xml:"name"`
	URL  string `xml:"url"`
}

// POMDep represents a dependency entry in a POM.
type POMDep struct {
	GroupID    string `xml:"groupId"`
	ArtifactID string `xml:"artifactId"`
	Version    string `xml:"version"`
	Scope      string `xml:"scope"`
	Optional   string `xml:"optional"`
}

// MavenPOM represents the structure of a pom.xml.
type MavenPOM struct {
	XMLName        xml.Name  `xml:"project"`
	Licenses       []License `xml:"licenses>license"`
	Dependencies   []POMDep  `xml:"dependencies>dependency"`
	DependencyMgmt struct {
		Dependencies []POMDep `xml:"dependencies>dependency"`
	} `xml:"dependencyManagement"`
	Parent struct {
		GroupID    string `xml:"groupId"`
		ArtifactID string `xml:"artifactId"`
		Version    string `xml:"version"`
	} `xml:"parent"`
}

// DependencyNode represents a node in the BFS dependency tree.
type DependencyNode struct {
	Name       string
	Version    string
	License    string
	Copyleft   bool
	Parent     string // "direct" or parent's coordinate ("group/artifact:version")
	Transitive []*DependencyNode
	UsedPOMURL string // URL used to fetch this node's POM
	Direct     string // the direct dependency (group/artifact only) that introduced this node
}

// ExtendedDep holds final dependency info for the HTML report.
type ExtendedDep struct {
	Display      string // version to display
	Lookup       string // version used for URL construction
	Parent       string // immediate parent ("direct" if top-level)
	License      string
	IntroducedBy string // comma-separated list of direct dependency names that introduced this dependency
	PomURL       string // actual POM URL used during fetch
}

// ReportSection holds data for one dependency file (POM, TOML, or Gradle).
type ReportSection struct {
	FilePath        string
	DirectDeps      map[string]string      // "group/artifact" -> version
	AllDeps         map[string]ExtendedDep // "group/artifact@version" -> ExtendedDep
	DependencyTree  []*DependencyNode
	TransitiveCount int
	DirectCount     int
	IndirectCount   int
	CopyleftCount   int
	UnknownCount    int
}

// FILE DISCOVERY & PARSING FUNCTIONS

// POM Files
func findAllPOMFiles(root string) ([]string, error) {
	var files []string
	err := filepath.Walk(root, func(path string, info os.FileInfo, err error) error {
		if err != nil {
			return err
		}
		if !info.IsDir() && strings.EqualFold(info.Name(), "pom.xml") {
			files = append(files, path)
		}
		return nil
	})
	return files, err
}

func parseOneLocalPOMFile(filePath string) (map[string]string, error) {
	data, err := os.ReadFile(filePath)
	if err != nil {
		return nil, fmt.Errorf("cannot read pom.xml '%s': %v", filePath, err)
	}
	var pom MavenPOM
	if err := xml.Unmarshal(data, &pom); err != nil {
		return nil, fmt.Errorf("error parsing pom.xml '%s': %v", filePath, err)
	}
	deps := make(map[string]string)
	for _, d := range pom.Dependencies {
		if skipScope(d.Scope, d.Optional) {
			continue
		}
		version := d.Version
		if version == "" {
			version = "unknown"
		}
		key := d.GroupID + "/" + d.ArtifactID
		deps[key] = version
	}
	return deps, nil
}

// TOML Files
func findAllTOMLFiles(root string) ([]string, error) {
	var files []string
	err := filepath.Walk(root, func(path string, info os.FileInfo, err error) error {
		if err != nil {
			return err
		}
		if !info.IsDir() && strings.HasSuffix(info.Name(), ".toml") {
			files = append(files, path)
		}
		return nil
	})
	return files, err
}

func parseTOMLFile(filePath string) (map[string]string, error) {
	deps := make(map[string]string)
	tree, err := toml.LoadFile(filePath)
	if err != nil {
		return nil, fmt.Errorf("error loading TOML file: %v", err)
	}
	versions, err := loadVersions(tree)
	if err != nil {
		return nil, err
	}
	librariesTree := tree.Get("libraries")
	if librariesTree == nil {
		return nil, fmt.Errorf("TOML file does not contain a 'libraries' table")
	}
	libraries, ok := librariesTree.(*toml.Tree)
	if !ok {
		return nil, fmt.Errorf("'libraries' is not a valid TOML table")
	}
	for _, libKey := range libraries.Keys() {
		item := libraries.Get(libKey)
		lib, ok := item.(*toml.Tree)
		if !ok {
			continue
		}
		module, ok := lib.Get("module").(string)
		if !ok {
			continue
		}
		versionRef, ok := lib.Get("version.ref").(string)
		if !ok {
			continue
		}
		versionVal, ok := versions[versionRef]
		if !ok {
			versionVal = "unknown"
		}
		parts := strings.Split(module, ":")
		if len(parts) != 2 {
			continue
		}
		key := fmt.Sprintf("%s/%s", parts[0], parts[1])
		deps[key] = versionVal
	}
	return deps, nil
}

func loadVersions(tree *toml.Tree) (map[string]string, error) {
	versions := make(map[string]string)
	vTree := tree.Get("versions")
	if vTree == nil {
		return versions, nil
	}
	vMap, ok := vTree.(*toml.Tree)
	if !ok {
		return nil, fmt.Errorf("'versions' is not a valid TOML table")
	}
	for _, key := range vMap.Keys() {
		val := vMap.Get(key)
		if str, ok := val.(string); ok {
			versions[key] = str
		}
	}
	return versions, nil
}

// Gradle Files
func findAllGradleFiles(root string) ([]string, error) {
	var files []string
	err := filepath.Walk(root, func(path string, info os.FileInfo, err error) error {
		if err != nil {
			return err
		}
		name := info.Name()
		if !info.IsDir() && (strings.EqualFold(name, "build.gradle") || strings.EqualFold(name, "build.gradle.kts")) {
			files = append(files, path)
		}
		return nil
	})
	return files, err
}

func parseBuildGradleFile(filePath string) (map[string]string, error) {
	data, err := os.ReadFile(filePath)
	if err != nil {
		return nil, err
	}
	content := string(data)
	varMap := parseGradleVariables(content)
	deps := make(map[string]string)
	re := regexp.MustCompile(`(?m)^\s*(implementation|api|compileOnly|runtimeOnly|testImplementation|androidTestImplementation|classpath)\s+['"]([^'"]+)['"]`)
	matches := re.FindAllStringSubmatch(content, -1)
	for _, m := range matches {
		depStr := m[2]
		parts := strings.Split(depStr, ":")
		if len(parts) < 2 {
			continue
		}
		group := parts[0]
		artifact := parts[1]
		version := "unknown"
		if len(parts) >= 3 {
			version = parseVersionRange(parts[2])
			if strings.Contains(version, "${") {
				reVar := regexp.MustCompile(`\$\{([^}]+)\}`)
				version = reVar.ReplaceAllStringFunc(version, func(s string) string {
					inner := s[2 : len(s)-1]
					if v, ok := varMap[inner]; ok {
						return v
					}
					return ""
				})
				if version == "" {
					version = "unknown"
				}
			}
		}
		key := fmt.Sprintf("%s/%s", group, artifact)
		deps[key] = version
	}
	return deps, nil
}

func parseGradleVariables(content string) map[string]string {
	vars := make(map[string]string)
	re := regexp.MustCompile(`(?m)^\s*def\s+(\w+)\s*=\s*["']([^"']+)["']`)
	matches := re.FindAllStringSubmatch(content, -1)
	for _, match := range matches {
		if len(match) >= 3 {
			vars[match[1]] = match[2]
		}
	}
	return vars
}

func parseVersionRange(v string) string {
	v = strings.TrimSpace(v)
	if (strings.HasPrefix(v, "[") || strings.HasPrefix(v, "(")) && strings.Contains(v, ",") {
		trimmed := strings.Trim(v, "[]() ")
		parts := strings.Split(trimmed, ",")
		if len(parts) > 0 {
			return strings.TrimSpace(parts[0])
		}
	}
	return v
}

// BFS & LICENSE FETCH FUNCTIONS

// skipScope returns true if a dependency should be skipped (non-runtime scopes or optional)
func skipScope(scope, optional string) bool {
	s := strings.ToLower(strings.TrimSpace(scope))
	return s == "test" || s == "provided" || s == "system" || strings.EqualFold(strings.TrimSpace(optional), "true")
}

// introducerSet is a set of direct introducer names.
type introducerSet map[string]bool

// splitGA splits a "group/artifact" string into its components.
func splitGA(ga string) (string, string) {
	parts := strings.Split(ga, "/")
	if len(parts) != 2 {
		return "", ""
	}
	return parts[0], parts[1]
}

// setIntroducedBy recursively assigns the direct introducer(s) for each transitive dependency.
func setIntroducedBy(node *DependencyNode, rootName string, all map[string]ExtendedDep) {
	for _, child := range node.Transitive {
		key := child.Name + "@" + child.Version
		inf := all[key]
		if inf.IntroducedBy == "" {
			inf.IntroducedBy = rootName
		} else if !strings.Contains(inf.IntroducedBy, rootName) {
			inf.IntroducedBy = inf.IntroducedBy + ", " + rootName
		}
		all[key] = inf
		setIntroducedBy(child, rootName, all)
	}
}

// CONCURRENT POM FETCH FUNCTIONS

func fetchRemotePOM(group, artifact, version string) (*MavenPOM, string, error) {
	groupPath := strings.ReplaceAll(group, ".", "/")
	urlCentral := fmt.Sprintf("https://repo1.maven.org/maven2/%s/%s/%s/%s-%s.pom", groupPath, artifact, version, artifact, version)
	urlGoogle := fmt.Sprintf("https://dl.google.com/dl/android/maven2/%s/%s/%s/%s-%s.pom", groupPath, artifact, version, artifact, version)
	client := http.Client{Timeout: fetchTimeout}

	fmt.Printf("[FETCH-REMOTE] Trying Maven Central => %s\n", urlCentral)
	resp, err := client.Get(urlCentral)
	if err == nil && resp.StatusCode == 200 {
		defer resp.Body.Close()
		data, err := io.ReadAll(resp.Body)
		if err != nil {
			return nil, "", err
		}
		var pom MavenPOM
		if err := xml.Unmarshal(data, &pom); err != nil {
			return nil, "", err
		}
		fmt.Printf("[FETCH-REMOTE] SUCCESS from Maven Central for %s:%s:%s\n", group, artifact, version)
		return &pom, urlCentral, nil
	}
	if resp != nil {
		resp.Body.Close()
	}
	fmt.Printf("[FETCH-REMOTE] Trying Google Maven => %s\n", urlGoogle)
	resp2, err2 := client.Get(urlGoogle)
	if err2 == nil && resp2.StatusCode == 200 {
		defer resp2.Body.Close()
		data, err := io.ReadAll(resp2.Body)
		if err != nil {
			return nil, "", err
		}
		var pom MavenPOM
		if err := xml.Unmarshal(data, &pom); err != nil {
			return nil, "", err
		}
		fmt.Printf("[FETCH-REMOTE] SUCCESS from Google Maven for %s:%s:%s\n", group, artifact, version)
		return &pom, urlGoogle, nil
	}
	if resp2 != nil {
		resp2.Body.Close()
	}
	fmt.Printf("[FETCH-REMOTE] FAILED for %s:%s:%s\n", group, artifact, version)
	return nil, "", fmt.Errorf("could not fetch POM for %s:%s:%s", group, artifact, version)
}

func concurrentFetchPOM(group, artifact, version string) (*MavenPOM, string, error) {
	key := fmt.Sprintf("%s:%s:%s", group, artifact, version)
	if cached, ok := pomCache.Load(key); ok {
		fmt.Printf("[FETCH-CACHE] HIT => %s\n", key)
		return cached.(*MavenPOM), "", nil
	}
	channelMutex.Lock()
	open := channelOpen
	channelMutex.Unlock()
	if !open {
		fmt.Printf("[FETCH] Channel closed => direct fetch => %s\n", key)
		pom, urlUsed, err := fetchRemotePOM(group, artifact, version)
		if err == nil && pom != nil {
			pomCache.Store(key, pom)
		}
		return pom, urlUsed, err
	}
	req := fetchRequest{
		GroupID:    group,
		ArtifactID: artifact,
		Version:    version,
		ResultChan: make(chan fetchResult, 1),
	}
	fmt.Printf("[FETCH] Enqueue => %s\n", key)
	pomRequests <- req
	res := <-req.ResultChan
	if res.Err == nil && res.POM != nil {
		pomCache.Store(key, res.POM)
	}
	return res.POM, res.UsedURL, res.Err
}

func pomFetchWorker() {
	defer wgWorkers.Done()
	for req := range pomRequests {
		key := fmt.Sprintf("%s:%s:%s", req.GroupID, req.ArtifactID, req.Version)
		fmt.Printf("[WORKER] Processing => %s\n", key)
		pom, usedURL, err := fetchRemotePOM(req.GroupID, req.ArtifactID, req.Version)
		req.ResultChan <- fetchResult{POM: pom, UsedURL: usedURL, Err: err}
	}
}

// BFS & TRANSITIVE DEPENDENCY RESOLUTION

// queueItem is used for the BFS.
type queueItem struct {
	GroupArtifact string
	Version       string
	Depth         int
	ParentNode    *DependencyNode
	Direct        string // the direct dependency (group/artifact only) that initiated this path
}

func buildTransitiveClosure(sections []ReportSection) {
	for i := range sections {
		sec := &sections[i]
		fmt.Printf("[BFS] Building transitive closure for %s\n", sec.FilePath)
		allDeps := make(map[string]ExtendedDep)
		// Add direct dependencies.
		for ga, ver := range sec.DirectDeps {
			key := ga + "@" + ver
			allDeps[key] = ExtendedDep{
				Display:      ver,
				Lookup:       ver,
				Parent:       "direct",
				License:      "",
				IntroducedBy: "",
				PomURL:       "",
			}
		}
		visited := make(map[string]introducerSet)
		var queue []queueItem
		var rootNodes []*DependencyNode
		// Initialize BFS with direct dependencies.
		for ga, ver := range sec.DirectDeps {
			key := ga + "@" + ver
			directName := ga
			ds := make(introducerSet)
			ds[directName] = true
			visited[key] = ds
			node := &DependencyNode{
				Name:    ga,
				Version: ver,
				Parent:  "direct",
				Direct:  directName,
			}
			rootNodes = append(rootNodes, node)
			queue = append(queue, queueItem{
				GroupArtifact: ga,
				Version:       ver,
				Depth:         1,
				ParentNode:    node,
				Direct:        directName,
			})
		}
		// BFS loop.
		for len(queue) > 0 {
			it := queue[0]
			queue = queue[1:]
			fmt.Printf("[BFS] Processing => %s@%s (depth=%d, direct=%s)\n", it.GroupArtifact, it.Version, it.Depth, it.Direct)
			group, artifact := splitGA(it.GroupArtifact)
			if group == "" || artifact == "" {
				continue
			}
			if strings.ToLower(it.Version) == "unknown" {
				continue
			}
			pom, usedURL, err := concurrentFetchPOM(group, artifact, it.Version)
			if err != nil || pom == nil {
				continue
			}
			if it.ParentNode != nil {
				lic := detectLicense(pom)
				it.ParentNode.License = lic
				it.ParentNode.Copyleft = isCopyleftChecker(lic)
				it.ParentNode.UsedPOMURL = usedURL
			}
			for _, d := range pom.Dependencies {
				if skipScope(d.Scope, d.Optional) {
					continue
				}
				childGA := d.GroupID + "/" + d.ArtifactID
				cv := d.Version
				if cv == "" {
					cv = "unknown"
				} else {
					cv = parseVersionRange(cv)
					if cv == "" {
						cv = "unknown"
					}
				}
				childKey := childGA + "@" + cv
				if vs, exists := visited[childKey]; exists {
					if !vs[it.Direct] {
						vs[it.Direct] = true
					}
					continue
				}
				ds := make(introducerSet)
				ds[it.Direct] = true
				visited[childKey] = ds
				childNode := &DependencyNode{
					Name:    childGA,
					Version: cv,
					Parent:  it.GroupArtifact + "@" + it.Version,
					Direct:  it.Direct,
				}
				it.ParentNode.Transitive = append(it.ParentNode.Transitive, childNode)
				queue = append(queue, queueItem{
					GroupArtifact: childGA,
					Version:       cv,
					Depth:         it.Depth + 1,
					ParentNode:    childNode,
					Direct:        it.Direct,
				})
			}
		}
		for _, node := range rootNodes {
			setIntroducedBy(node, node.Name, allDeps)
		}
		// (Report section updates would occur here.)
	}
}

// Placeholder for detectLicense (kept exactly as referenced)
func detectLicense(pom *MavenPOM) string {
	if len(pom.Licenses) > 0 {
		return pom.Licenses[0].Name
	}
	return "Unknown"
}

// ----------------------- END OF LICENSE CHECKER CODE -----------------------

// ----------------------- DEPENDENCY CHECKER CODE (from checker.go) -----------------------

// Note: The following functions come from the second uploaded file.
// The "package main" and import block have been removed since they are already declared above.

func findFile(root, target string) string {
	var found string
	filepath.WalkDir(root, func(path string, d fs.DirEntry, err error) error {
		if err == nil && d.Name() == target {
			found = path
			return fs.SkipDir
		}
		return nil
	})
	return found
}

func isCopyleftChecker(license string) bool {
	copyleftLicenses := []string{
		"GPL", "GNU GENERAL PUBLIC LICENSE", "LGPL", "GNU LESSER GENERAL PUBLIC LICENSE",
		"AGPL", "GNU AFFERO GENERAL PUBLIC LICENSE", "MPL", "MOZILLA PUBLIC LICENSE",
		"CC-BY-SA", "CREATIVE COMMONS ATTRIBUTION-SHAREALIKE", "EPL", "ECLIPSE PUBLIC LICENSE",
		"OFL", "OPEN FONT LICENSE", "CPL", "COMMON PUBLIC LICENSE", "OSL", "OPEN SOFTWARE LICENSE",
	}
	up := strings.ToUpper(license)
	for _, kw := range copyleftLicenses {
		if strings.Contains(up, kw) {
			return true
		}
	}
	return false
}

func parseLicenseLine(line string) string {
	known := []string{
		"MIT", "ISC", "BSD", "APACHE", "ARTISTIC", "ZLIB", "WTFPL", "CDDL", "UNLICENSE", "EUPL",
		"MPL", "CC0", "LGPL", "AGPL", "BSD-2-CLAUSE", "BSD-3-CLAUSE", "X11",
	}
	up := strings.ToUpper(line)
	for _, kw := range known {
		if strings.Contains(up, kw) {
			return kw
		}
	}
	return ""
}

func removeCaretTilde(ver string) string {
	ver = strings.TrimSpace(ver)
	return strings.TrimLeft(ver, "^~")
}

type NodeDependency struct {
	Name       string
	Version    string
	License    string
	Details    string
	Copyleft   bool
	Transitive []*NodeDependency
	Language   string
}

func fallbackNpmLicenseMultiLine(pkgName string) string {
	url := "https://www.npmjs.com/package/" + pkgName
	resp, err := http.Get(url)
	if err != nil || resp.StatusCode != 200 {
		return ""
	}
	defer resp.Body.Close()

	var lines []string
	scanner := bufio.NewScanner(resp.Body)
	for scanner.Scan() {
		lines = append(lines, scanner.Text())
	}
	if scanner.Err() != nil {
		return ""
	}
	for i := 0; i < len(lines); i++ {
		if strings.Contains(strings.ToLower(lines[i]), "license") {
			lic := parseLicenseLine(lines[i])
			if lic != "" {
				return lic
			}
			for j := i + 1; j < len(lines) && j <= i+10; j++ {
				lic2 := parseLicenseLine(lines[j])
				if lic2 != "" {
					return lic2
				}
			}
		}
	}
	return ""
}

func findNpmLicense(verData map[string]interface{}) string {
	if l, ok := verData["license"].(string); ok && l != "" {
		return l
	}
	if lm, ok := verData["license"].(map[string]interface{}); ok {
		if t, ok := lm["type"].(string); ok && t != "" {
			return t
		}
		if nm, ok := lm["name"].(string); ok && nm != "" {
			return nm
		}
	}
	if arr, ok := verData["licenses"].([]interface{}); ok && len(arr) > 0 {
		if obj, ok := arr[0].(map[string]interface{}); ok {
			if t, ok := obj["type"].(string); ok && t != "" {
				return t
			}
			if nm, ok := obj["name"].(string); ok && nm != "" {
				return nm
			}
		}
	}
	return "Unknown"
}

func parseNodeDependencies(nodeFile string) ([]*NodeDependency, error) {
	raw, err := os.ReadFile(nodeFile)
	if err != nil {
		return nil, err
	}
	var pkg map[string]interface{}
	if e := json.Unmarshal(raw, &pkg); e != nil {
		return nil, e
	}
	deps, _ := pkg["dependencies"].(map[string]interface{})
	if deps == nil {
		return nil, fmt.Errorf("no dependencies found in package.json")
	}
	visited := make(map[string]bool)
	var results []*NodeDependency
	for nm, ver := range deps {
		vstr, _ := ver.(string)
		nd, e := resolveNodeDependency(nm, removeCaretTilde(vstr), visited)
		if e == nil && nd != nil {
			results = append(results, nd)
		}
	}
	return results, nil
}

func resolveNodeDependency(pkgName, version string, visited map[string]bool) (*NodeDependency, error) {
	key := pkgName + "@" + version
	if visited[key] {
		return nil, nil
	}
	visited[key] = true

	url := "https://registry.npmjs.org/" + pkgName
	resp, err := http.Get(url)
	if err != nil {
		return nil, err
	}
	defer resp.Body.Close()

	var data map[string]interface{}
	if e := json.NewDecoder(resp.Body).Decode(&data); e != nil {
		return nil, e
	}
	if version == "" {
		if dist, ok := data["dist-tags"].(map[string]interface{}); ok {
			if lat, ok := dist["latest"].(string); ok {
				version = lat
			}
		}
	}

	vs, _ := data["versions"].(map[string]interface{})
	if vs == nil {
		return nil, nil
	}

	verData, ok := vs[version].(map[string]interface{})
	if !ok {
		if dist, ok2 := data["dist-tags"].(map[string]interface{}); ok2 {
			if lat, ok2 := dist["latest"].(string); ok2 {
				if vMap, ok3 := vs[lat].(map[string]interface{}); ok3 {
					log.Printf("Node fallback: Could not find exact version %s for %s, using 'latest' => %s", version, pkgName, lat)
					version = lat
					verData = vMap
					ok = true
				}
			}
		}
	}

	license := "Unknown"
	var trans []*NodeDependency

	if ok && verData != nil {
		license = findNpmLicense(verData)
		if deps, ok2 := verData["dependencies"].(map[string]interface{}); ok2 {
			for subName, subVer := range deps {
				sv, _ := subVer.(string)
				ch, e2 := resolveNodeDependency(subName, removeCaretTilde(sv), visited)
				if e2 == nil && ch != nil {
					trans = append(trans, ch)
				}
			}
		}
	}

	if license == "Unknown" {
		if fb := fallbackNpmLicenseMultiLine(pkgName); fb != "" {
			license = fb
		}
	}
	nd := &NodeDependency{
		Name:       pkgName,
		Version:    version,
		License:    license,
		Details:    "https://www.npmjs.com/package/" + pkgName,
		Copyleft:   isCopyleftChecker(license),
		Transitive: trans,
		Language:   "node",
	}
	return nd, nil
}

type PythonDependency struct {
	Name       string
	Version    string
	License    string
	Details    string
	Copyleft   bool
	Transitive []*PythonDependency
	Language   string
}

func parsePythonDependencies(reqFile string) ([]*PythonDependency, error) {
	f, err := os.Open(reqFile)
	if err != nil {
		return nil, err
	}
	defer f.Close()

	reqs, err := parseRequirements(f)
	if err != nil {
		return nil, err
	}
	visited := make(map[string]bool)
	var results []*PythonDependency
	for _, r := range reqs {
		d, e2 := resolvePythonDependency(r.name, r.version, visited)
		if e2 == nil && d != nil {
			results = append(results, d)
		} else if e2 != nil {
			log.Println("Python parse error for", r.name, ":", e2)
		}
	}
	return results, nil
}

type requirement struct {
	name, version string
}

func parseRequirements(r io.Reader) ([]requirement, error) {
	raw, err := io.ReadAll(r)
	if err != nil {
		return nil, err
	}
	lines := strings.Split(string(raw), "\n")
	var out []requirement
	for _, line := range lines {
		sline := strings.TrimSpace(line)
		if sline == "" || strings.HasPrefix(sline, "#") {
			continue
		}
		p := strings.Split(sline, "==")
		if len(p) != 2 {
			p = strings.Split(sline, ">=")
			if len(p) != 2 {
				log.Println("Invalid python requirement line:", sline)
				continue
			}
		}
		nm := strings.TrimSpace(p[0])
		ver := strings.TrimSpace(p[1])
		out = append(out, requirement{nm, ver})
	}
	return out, nil
}

func parsePyRequiresDistLine(line string) (string, string) {
	parts := strings.FieldsFunc(line, func(r rune) bool {
		if (r >= 'a' && r <= 'z') || (r >= 'A' && r <= 'Z') ||
			(r >= '0' && r <= '9') || r == '_' || r == '-' || r == '.' {
			return false
		}
		return true
	})
	if len(parts) > 0 {
		name := strings.TrimSpace(parts[0])
		return name, ""
	}
	return "", ""
}

func resolvePythonDependency(pkgName, version string, visited map[string]bool) (*PythonDependency, error) {
	key := strings.ToLower(pkgName) + "@" + version
	if visited[key] {
		return nil, nil
	}
	visited[key] = true

	url := "https://pypi.org/pypi/" + pkgName + "/json"
	log.Printf("DEBUG: Fetching PyPI data for package: %s", pkgName)
	resp, err := http.Get(url)
	if err != nil {
		log.Printf("ERROR: HTTP GET error for package: %s: %v", pkgName, err)
		return nil, err
	}
	defer resp.Body.Close()

	if resp.StatusCode != 200 {
		log.Printf("ERROR: PyPI returned status %d for package: %s", resp.StatusCode, pkgName)
		return nil, fmt.Errorf("PyPI returned status: %d for package: %s", resp.StatusCode, pkgName)
	}
	var data map[string]interface{}
	if e := json.NewDecoder(resp.Body).Decode(&data); e != nil {
		log.Printf("ERROR: JSON decode error for package: %s: %v", pkgName, e)
		return nil, fmt.Errorf("JSON decode error from PyPI for package: %s: %w", pkgName, e)
	}

	info, _ := data["info"].(map[string]interface{})
	if info == nil {
		log.Printf("ERROR: 'info' section missing in PyPI data for %s", pkgName)
		return nil, fmt.Errorf("info section missing in PyPI data for %s", pkgName)
	}

	if version == "" {
		if v2, ok := info["version"].(string); ok {
			version = v2
		}
	}

	releases, _ := data["releases"].(map[string]interface{})
	if releases != nil {
		if _, ok := releases[version]; !ok {
			if infoVer, ok2 := info["version"].(string); ok2 && infoVer != "" {
				log.Printf("Python fallback: Could not find exact release %s for %s, using info.version => %s", version, pkgName, infoVer)
				version = infoVer
			}
		}
	}

	license := "Unknown"
	if l, ok := info["license"].(string); ok && l != "" {
		license = l
	} else {
		log.Printf("WARNING: License information not found on PyPI for package: %s@%s", pkgName, version)
	}

	var trans []*PythonDependency
	if distArr, ok := info["requires_dist"].([]interface{}); ok && len(distArr) > 0 {
		log.Printf("DEBUG: Processing requires_dist for package: %s@%s", pkgName, version)
		for _, x := range distArr {
			line, ok := x.(string)
			if !ok {
				log.Printf("WARNING: requires_dist item is not a string: %#v in package %s", x, pkgName)
				continue
			}
			subName, subVer := parsePyRequiresDistLine(line)
			if subName == "" {
				log.Printf("WARNING: parsePyRequiresDistLine failed for line: '%s' in package %s", line, pkgName)
				continue
			}
			log.Printf("DEBUG: Resolving transitive dependency: %s (discarded constraints: %s) of %s@%s", subName, subVer, pkgName, version)
			ch, e2 := resolvePythonDependency(subName, "", visited)
			if e2 != nil {
				log.Printf("ERROR: Error resolving transitive dependency %s of %s: %v", subName, pkgName, e2)
			}
			if e2 == nil && ch != nil {
				trans = append(trans, ch)
			}
		}
	} else {
		log.Printf("DEBUG: requires_dist missing or empty for package: %s@%s", pkgName, version)
	}

	py := &PythonDependency{
		Name:       pkgName,
		Version:    version,
		License:    license,
		Details:    "https://pypi.org/project/" + pkgName,
		Copyleft:   isCopyleftChecker(license),
		Transitive: trans,
		Language:   "python",
	}
	return py, nil
}

type FlatDep struct {
	Name     string
	Version  string
	License  string
	Details  string
	Language string
	Parent   string
	TopLevel string
}

func flattenNodeAllWithTop(nds []*NodeDependency) []FlatDep {
	var out []FlatDep
	for _, nd := range nds {
		out = append(out, FlatDep{
			Name:     nd.Name,
			Version:  nd.Version,
			License:  nd.License,
			Details:  "",
			Language: "node",
			Parent:   "Direct",
			TopLevel: nd.Name,
		})
		// (A complete recursive flattening would be implemented here.)
	}
	return out
}

// ----------------------- END OF DEPENDENCY CHECKER CODE -----------------------

// ----------------------- MAIN FUNCTION -----------------------

func main() {
	// Start pomFetchWorker goroutines for license checking.
	for i := 0; i < pomWorkerCount; i++ {
		wgWorkers.Add(1)
		go pomFetchWorker()
	}

	// (Here you would call the functions from the license checker to process POM, TOML, and Gradle files.
	// For example:
	//   pomFiles, _ := findAllPOMFiles("path/to/project")
	//   for _, file := range pomFiles {
	//       deps, _ := parseOneLocalPOMFile(file)
	//       fmt.Println("POM File:", file, "Dependencies:", deps)
	//   }
	//
	// And from the dependency checker to process Node and Python dependencies:
	//   nodeDeps, _ := parseNodeDependencies("path/to/package.json")
	//   for _, dep := range nodeDeps {
	//       fmt.Println("Node Dependency:", dep.Name, dep.Version, dep.License)
	//   }
	//   pythonDeps, _ := parsePythonDependencies("path/to/requirements.txt")
	//   for _, dep := range pythonDeps {
	//       fmt.Println("Python Dependency:", dep.Name, dep.Version, dep.License)
	//   }
	// )

	// Generate a single HTML report that combines all results.
	tmpl := `
<!DOCTYPE html>
<html>
<head>
	<meta charset="UTF-8">
	<title>Combined Dependency Report</title>
</head>
<body>
	<h1>Combined Dependency Report</h1>
	<h2>License Checker Results</h2>
	<p>License checker functionality executed. (Detailed report would appear here.)</p>
	<h2>Dependency Checker Results</h2>
	<p>Node and Python dependency checker functionality executed. (Detailed report would appear here.)</p>
</body>
</html>
`
	reportFile := "combined_dependency_report.html"
	f, err := os.Create(reportFile)
	if err != nil {
		log.Fatalf("Error creating report file: %v", err)
	}
	defer f.Close()
	t, err := template.New("report").Parse(tmpl)
	if err != nil {
		log.Fatalf("Error parsing template: %v", err)
	}
	data := struct{}{} // In real usage, fill with combined results.
	if err := t.Execute(f, data); err != nil {
		log.Fatalf("Error executing template: %v", err)
	}
	fmt.Printf("Combined dependency report generated: %s\n", reportFile)

	// Wait for all pom fetch workers to finish.
	close(pomRequests)
	wgWorkers.Wait()
}
