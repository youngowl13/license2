// File: license_compliance_report.go
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

// ----------------------------------------------------------------------
// 1) CONFIG & GLOBALS (from license(1).go)
// ----------------------------------------------------------------------

const (
	localPOMCacheDir       = ".pom-cache"
	pomWorkerCount         = 10
	fetchTimeout           = 30 * time.Second
	outputReportJava       = "license-checker/dependency-license-report.html" // original from license(1).go
	outputReportFinal      = "license_compliance_report.html"                // final single HTML
)

// Used for concurrency in Maven BFS
var (
	pomRequests  = make(chan fetchRequest, 50)
	wgWorkers    sync.WaitGroup
	pomCache     sync.Map // key: "group:artifact:version" -> *MavenPOM
	channelOpen  = true
	channelMutex sync.Mutex
)

// ----------------------------------------------------------------------
// 2) TYPES FROM license(1).go
// ----------------------------------------------------------------------

// BFS concurrency
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

// SPDX LICENSE MAP (example from license(1).go)
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

// License in a POM
type License struct {
	Name string `xml:"name"`
	URL  string `xml:"url"`
}

// POMDep in a POM
type POMDep struct {
	GroupID    string `xml:"groupId"`
	ArtifactID string `xml:"artifactId"`
	Version    string `xml:"version"`
	Scope      string `xml:"scope"`
	Optional   string `xml:"optional"`
}

// MavenPOM structure
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

// DependencyNode for BFS tree (Java)
type DependencyNode struct {
	Name       string
	Version    string
	License    string
	Copyleft   bool
	Parent     string
	Transitive []*DependencyNode
	UsedPOMURL string
	Direct     string // direct dependency name
}

// ExtendedDep for HTML report
type ExtendedDep struct {
	Display      string
	Lookup       string
	Parent       string
	License      string
	IntroducedBy string
	PomURL       string
}

// ReportSection (for POM, TOML, Gradle)
type ReportSection struct {
	FilePath        string
	DirectDeps      map[string]string
	AllDeps         map[string]ExtendedDep
	DependencyTree  []*DependencyNode
	TransitiveCount int
	DirectCount     int
	IndirectCount   int
	CopyleftCount   int
	UnknownCount    int
}

// ----------------------------------------------------------------------
// 3) FILE DISCOVERY & PARSING (from license(1).go) for Java/TOML/Gradle
// ----------------------------------------------------------------------

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

// ----------------------------------------------------------------------
// 4) BFS & LICENSE FETCH (from license(1).go) for Java/TOML/Gradle
// ----------------------------------------------------------------------

func skipScope(scope, optional string) bool {
	s := strings.ToLower(strings.TrimSpace(scope))
	return s == "test" || s == "provided" || s == "system" || strings.EqualFold(strings.TrimSpace(optional), "true")
}

type introducerSet map[string]bool

func splitGA(ga string) (string, string) {
	parts := strings.Split(ga, "/")
	if len(parts) != 2 {
		return "", ""
	}
	return parts[0], parts[1]
}

func setIntroducedBy(node *DependencyNode, rootName string, all map[string]ExtendedDep) {
	for _, child := range node.Transitive {
		key := child.Name + "@" + child.Version
		inf := all[key]
		if inf.IntroducedBy == "" {
			inf.IntroducedBy = rootName
		} else if !strings.Contains(inf.IntroducedBy, rootName) {
			inf.IntroducedBy += ", " + rootName
		}
		all[key] = inf
		setIntroducedBy(child, rootName, all)
	}
}

// ----------------------------------------------------------------------
// 5) REMOTE FETCH FOR POM (from license(1).go)
// ----------------------------------------------------------------------

func fetchRemotePOM(group, artifact, version string) (*MavenPOM, string, error) {
	groupPath := strings.ReplaceAll(group, ".", "/")
	urlCentral := fmt.Sprintf("https://repo1.maven.org/maven2/%s/%s/%s/%s-%s.pom", groupPath, artifact, version, artifact, version)
	urlGoogle := fmt.Sprintf("https://dl.google.com/dl/android/maven2/%s/%s/%s/%s-%s.pom", groupPath, artifact, version, artifact, version)
	client := http.Client{Timeout: fetchTimeout}

	log.Printf("[FETCH-REMOTE] Trying Maven Central => %s\n", urlCentral)
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
		log.Printf("[FETCH-REMOTE] SUCCESS from Maven Central for %s:%s:%s\n", group, artifact, version)
		return &pom, urlCentral, nil
	}
	if resp != nil {
		resp.Body.Close()
	}

	log.Printf("[FETCH-REMOTE] Trying Google Maven => %s\n", urlGoogle)
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
		log.Printf("[FETCH-REMOTE] SUCCESS from Google Maven for %s:%s:%s\n", group, artifact, version)
		return &pom, urlGoogle, nil
	}
	if resp2 != nil {
		resp2.Body.Close()
	}
	log.Printf("[FETCH-REMOTE] FAILED for %s:%s:%s\n", group, artifact, version)
	return nil, "", fmt.Errorf("could not fetch POM for %s:%s:%s", group, artifact, version)
}

func concurrentFetchPOM(group, artifact, version string) (*MavenPOM, string, error) {
	key := fmt.Sprintf("%s:%s:%s", group, artifact, version)
	if cached, ok := pomCache.Load(key); ok {
		log.Printf("[FETCH-CACHE] HIT => %s\n", key)
		return cached.(*MavenPOM), "", nil
	}
	channelMutex.Lock()
	open := channelOpen
	channelMutex.Unlock()

	if !open {
		log.Printf("[FETCH] Channel closed => direct fetch => %s\n", key)
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
	log.Printf("[FETCH] Enqueue => %s\n", key)
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
		log.Printf("[WORKER] Processing => %s\n", key)
		pom, usedURL, err := fetchRemotePOM(req.GroupID, req.ArtifactID, req.Version)
		req.ResultChan <- fetchResult{POM: pom, UsedURL: usedURL, Err: err}
	}
}

// ----------------------------------------------------------------------
// 6) BFS FOR TRANSITIVE CLOSURE (from license(1).go)
// ----------------------------------------------------------------------

type queueItem struct {
	GroupArtifact string
	Version       string
	Depth         int
	ParentNode    *DependencyNode
	Direct        string
}

func buildTransitiveClosure(sections []ReportSection) {
	for i := range sections {
		sec := &sections[i]
		log.Printf("[BFS] Building transitive closure for %s\n", sec.FilePath)
		allDeps := make(map[string]ExtendedDep)

		// add direct dependencies
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

		// initialize BFS with direct
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

		// BFS loop
		for len(queue) > 0 {
			it := queue[0]
			queue = queue[1:]
			log.Printf("[BFS] Processing => %s@%s (depth=%d, direct=%s)\n",
				it.GroupArtifact, it.Version, it.Depth, it.Direct)

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
					// already visited, just update introducers
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

		// assign introducedBy
		for _, node := range rootNodes {
			setIntroducedBy(node, node.Name, allDeps)
		}

		// flatten BFS data back to sec.AllDeps
		// same logic as original code
		for k, v := range allDeps {
			sec.AllDeps[k] = v
		}
		sec.DependencyTree = rootNodes

		// compute counts
		sec.DirectCount = len(sec.DirectDeps)
		sec.TransitiveCount = 0
		sec.IndirectCount = 0
		sec.CopyleftCount = 0
		sec.UnknownCount = 0

		for key := range sec.AllDeps {
			if strings.Contains(key, "@") {
				ga := strings.Split(key, "@")
				if len(ga) == 2 {
					if ga[1] == "unknown" {
						sec.UnknownCount++
					} else {
						sec.TransitiveCount++
					}
				}
			}
		}
		sec.IndirectCount = sec.TransitiveCount - sec.DirectCount
		for _, root := range sec.DependencyTree {
			countCopyleftInTree(root, sec)
		}
	}
}

func detectLicense(pom *MavenPOM) string {
	if len(pom.Licenses) > 0 {
		return pom.Licenses[0].Name
	}
	return "Unknown"
}

// we rename the second isCopyleft => isCopyleftChecker
func isCopyleftChecker(license string) bool {
	// from checker.go logic
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

func countCopyleftInTree(node *DependencyNode, sec *ReportSection) {
	if node.Copyleft {
		sec.CopyleftCount++
	}
	for _, ch := range node.Transitive {
		countCopyleftInTree(ch, sec)
	}
}

// ----------------------------------------------------------------------
// 7) CODE FROM checker.go (Node & Python BFS) with minimal changes
// ----------------------------------------------------------------------

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

// Node BFS
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
					log.Printf("Node fallback: Could not find exact version %s for %s, using 'latest' => %s",
						version, pkgName, lat)
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

// Python BFS
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
				log.Printf("Python fallback: Could not find exact release %s for %s, using info.version => %s",
					version, pkgName, infoVer)
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
			log.Printf("DEBUG: Resolving transitive dependency: %s of %s@%s", subName, pkgName, version)
			ch, e2 := resolvePythonDependency(subName, "", visited)
			if e2 != nil {
				log.Printf("ERROR: Error resolving transitive dependency %s of %s: %v", subName, pkgName, e2)
			}
			if e2 == nil && ch != nil {
				trans = append(trans, ch)
			}
		}
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

// ----------------------------------------------------------------------
// 8) TEMPLATES: Merging original from license(1).go & from checker.go
// ----------------------------------------------------------------------

// This is the template from license(1).go (slightly renamed to avoid confusion).
// It displays Java/TOML/Gradle BFS results in the same style as the original code.
var reportTmplJava = `
<!DOCTYPE html>
<html>
<head>
    <meta charset="utf-8">
    <title>License Checker Report</title>
    <style>
        body { font-family: Arial, sans-serif; }
        h1 { color: #333; }
        .summary { margin-bottom: 20px; }
        table { border-collapse: collapse; width: 90%; margin-bottom: 30px; }
        th, td { border: 1px solid #ccc; padding: 6px 8px; }
        th { background: #f7f7f7; }
        .copyleft { background-color: #ffe6e6; }
        .unknown { background-color: #ffffcc; }
        .indent { margin-left: 20px; }
    </style>
</head>
<body>
<h1>Java/TOML/Gradle License Report</h1>

{{range .Sections}}
<h2>{{.FilePath}}</h2>
<p class="summary">
  Direct Dependencies: {{.DirectCount}} <br/>
  Transitive (including direct): {{.TransitiveCount}} <br/>
  Indirect: {{.IndirectCount}} <br/>
  Copyleft: {{.CopyleftCount}} <br/>
  Unknown Version: {{.UnknownCount}}
</p>

<ul>
  {{range .DependencyTree}}
    <li>
      <strong>{{.Name}}@{{.Version}}</strong>
      {{if eq .Parent "direct"}}(direct){{else}}(introduced by {{.Parent}}){{end}}
      <br/>
      License: <span {{if .Copyleft}}class="copyleft"{{else if eq .License "Unknown"}}class="unknown"{{end}}>{{.License}}</span>
      {{if .UsedPOMURL}} [ <a href="{{.UsedPOMURL}}" target="_blank">POM</a> ]{{end}}
      <div class="indent">
        {{template "transitive" .Transitive}}
      </div>
    </li>
  {{end}}
</ul>
<hr/>
{{end}}

{{define "transitive"}}
<ul>
  {{range .}}
  <li>
    <strong>{{.Name}}@{{.Version}}</strong>
    <br/>
    License: <span {{if .Copyleft}}class="copyleft"{{else if eq .License "Unknown"}}class="unknown"{{end}}>{{.License}}</span>
    {{if .UsedPOMURL}} [ <a href="{{.UsedPOMURL}}" target="_blank">POM</a> ]{{end}}
    <div class="indent">
      {{template "transitive" .Transitive}}
    </div>
  </li>
  {{end}}
</ul>
{{end}}

</body>
</html>
`

// Template from checker.go for Node/Python results (renamed to avoid collision).
var reportTmplNodePy = `
<!DOCTYPE html>
<html>
<head>
    <meta charset="utf-8">
    <title>Node/Python Dependency Report</title>
    <style>
        body { font-family: Arial, sans-serif; }
        table { border-collapse: collapse; width: 95%; margin: 20px 0; }
        th, td { border: 1px solid #ccc; padding: 6px 8px; }
        th { background: #f0f0f0; }
        .copyleft { background-color: #ffe6e6; }
        .unknown { background-color: #ffffcc; }
    </style>
</head>
<body>
<h1>Node/Python Dependency Report</h1>

<h2>Node Dependencies</h2>
<table>
  <tr>
    <th>Name</th><th>Version</th><th>License</th><th>Details</th>
  </tr>
  {{range .Node}}
  <tr>
    <td>{{.Name}}</td>
    <td>{{.Version}}</td>
    <td {{if .Copyleft}}class="copyleft"{{end}}>{{.License}}</td>
    <td><a href="{{.Details}}" target="_blank">Link</a></td>
  </tr>
  {{end}}
</table>

<h2>Python Dependencies</h2>
<table>
  <tr>
    <th>Name</th><th>Version</th><th>License</th><th>Details</th>
  </tr>
  {{range .Python}}
  <tr>
    <td>{{.Name}}</td>
    <td>{{.Version}}</td>
    <td {{if .Copyleft}}class="copyleft"{{end}}>{{.License}}</td>
    <td><a href="{{.Details}}" target="_blank">Link</a></td>
  </tr>
  {{end}}
</table>

</body>
</html>
`

// For our final single-file output, we’ll produce one HTML that *combines* the above two sections
// into a single document. We'll do it by simply concatenating them or by placing one after the other.
var mergedReportTmpl = `
<!DOCTYPE html>
<html>
<head>
    <meta charset="utf-8">
    <title>License Compliance Report</title>
    <style>
    body { font-family: Arial, sans-serif; }
    .copyleft { background-color: #ffe6e6; }
    .unknown { background-color: #ffffcc; }
    h1 { color: #333; margin-top: 0; }
    table { border-collapse: collapse; width: 95%; margin: 20px 0; }
    th, td { border: 1px solid #ccc; padding: 6px 8px; }
    th { background: #f7f7f7; }
    .indent { margin-left: 20px; }
    </style>
</head>
<body>

<!-- FIRST: Java/TOML/Gradle results (like license(1).go) -->
<h1>Java/TOML/Gradle License Report</h1>
{{range .JavaSections}}
<h2>{{.FilePath}}</h2>
<p>
  Direct: {{.DirectCount}} <br/>
  Transitive (incl. direct): {{.TransitiveCount}} <br/>
  Indirect: {{.IndirectCount}} <br/>
  Copyleft: {{.CopyleftCount}} <br/>
  Unknown: {{.UnknownCount}}
</p>
<ul>
  {{range .DependencyTree}}
    <li>
      <strong>{{.Name}}@{{.Version}}</strong>
      {{if eq .Parent "direct"}}(direct){{else}}(introduced by {{.Parent}}){{end}}
      <br/>
      License: <span {{if .Copyleft}}class="copyleft"{{else if eq .License "Unknown"}}class="unknown"{{end}}>{{.License}}</span>
      {{if .UsedPOMURL}} [<a href="{{.UsedPOMURL}}" target="_blank">POM</a>]{{end}}
      <div class="indent">{{template "transitive" .Transitive}}</div>
    </li>
  {{end}}
</ul>
<hr/>
{{end}}

{{define "transitive"}}
<ul>
  {{range .}}
  <li>
    <strong>{{.Name}}@{{.Version}}</strong>
    <br/>
    License: <span {{if .Copyleft}}class="copyleft"{{else if eq .License "Unknown"}}class="unknown"{{end}}>{{.License}}</span>
    {{if .UsedPOMURL}} [<a href="{{.UsedPOMURL}}" target="_blank">POM</a>]{{end}}
    <div class="indent">{{template "transitive" .Transitive}}</div>
  </li>
  {{end}}
</ul>
{{end}}

<!-- SECOND: Node & Python results (like checker.go) -->
<h1>Node/Python Dependency Report</h1>
<h2>Node Dependencies</h2>
<table>
  <tr>
    <th>Name</th><th>Version</th><th>License</th><th>Details</th>
  </tr>
  {{range .NodeDeps}}
  <tr>
    <td>{{.Name}}</td>
    <td>{{.Version}}</td>
    <td {{if .Copyleft}}class="copyleft"{{end}}>{{.License}}</td>
    <td><a href="{{.Details}}" target="_blank">Link</a></td>
  </tr>
  {{end}}
</table>

<h2>Python Dependencies</h2>
<table>
  <tr>
    <th>Name</th><th>Version</th><th>License</th><th>Details</th>
  </tr>
  {{range .PyDeps}}
  <tr>
    <td>{{.Name}}</td>
    <td>{{.Version}}</td>
    <td {{if .Copyleft}}class="copyleft"{{end}}>{{.License}}</td>
    <td><a href="{{.Details}}" target="_blank">Link</a></td>
  </tr>
  {{end}}
</table>

</body>
</html>
`

// ----------------------------------------------------------------------
// 9) MAIN FUNCTION: combine everything & produce single HTML
// ----------------------------------------------------------------------

func main() {
	// Start workers for Maven POM BFS
	for i := 0; i < pomWorkerCount; i++ {
		wgWorkers.Add(1)
		go pomFetchWorker()
	}

	// 1) Find & parse all POM, TOML, Gradle => build BFS
	var sections []ReportSection

	// example: you might pass the current dir "." or another path
	rootDir := "."

	pomFiles, _ := findAllPOMFiles(rootDir)
	for _, pf := range pomFiles {
		deps, err := parseOneLocalPOMFile(pf)
		if err != nil {
			log.Println("Error parsing POM:", err)
			continue
		}
		sec := ReportSection{
			FilePath:   pf,
			DirectDeps: deps,
			AllDeps:    make(map[string]ExtendedDep),
		}
		sections = append(sections, sec)
	}

	tomlFiles, _ := findAllTOMLFiles(rootDir)
	for _, tf := range tomlFiles {
		deps, err := parseTOMLFile(tf)
		if err != nil {
			log.Println("Error parsing TOML:", err)
			continue
		}
		sec := ReportSection{
			FilePath:   tf,
			DirectDeps: deps,
			AllDeps:    make(map[string]ExtendedDep),
		}
		sections = append(sections, sec)
	}

	gradleFiles, _ := findAllGradleFiles(rootDir)
	for _, gf := range gradleFiles {
		deps, err := parseBuildGradleFile(gf)
		if err != nil {
			log.Println("Error parsing Gradle:", err)
			continue
		}
		sec := ReportSection{
			FilePath:   gf,
			DirectDeps: deps,
			AllDeps:    make(map[string]ExtendedDep),
		}
		sections = append(sections, sec)
	}

	// BFS build
	buildTransitiveClosure(sections)

	// 2) Find & parse Node (package.json)
	nodeFile := findFile(rootDir, "package.json")
	var nodeDeps []*NodeDependency
	if nodeFile != "" {
		nd, err := parseNodeDependencies(nodeFile)
		if err == nil {
			nodeDeps = nd
		} else {
			log.Println("Error parsing Node dependencies:", err)
		}
	}

	// 3) Find & parse Python (requirements.txt)
	pyFile := findFile(rootDir, "requirements.txt")
	var pyDeps []*PythonDependency
	if pyFile != "" {
		pd, err := parsePythonDependencies(pyFile)
		if err == nil {
			pyDeps = pd
		} else {
			log.Println("Error parsing Python dependencies:", err)
		}
	}

	// done BFS => close channel, wait for workers
	close(pomRequests)
	wgWorkers.Wait()

	// 4) Render single HTML combining Java/TOML/Gradle + Node/Python
	type finalData struct {
		JavaSections []ReportSection
		NodeDeps     []*NodeDependency
		PyDeps       []*PythonDependency
	}
	fd := finalData{
		JavaSections: sections,
		NodeDeps:     nodeDeps,
		PyDeps:       pyDeps,
	}

	f, err := os.Create(outputReportFinal)
	if err != nil {
		log.Fatalf("Cannot create final HTML report: %v", err)
	}
	defer f.Close()

	tmpl, err := template.New("merged").Parse(mergedReportTmpl)
	if err != nil {
		log.Fatalf("Error parsing merged template: %v", err)
	}

	err = tmpl.Execute(f, fd)
	if err != nil {
		log.Fatalf("Error executing merged template: %v", err)
	}

	fmt.Println("License compliance report generated at:", outputReportFinal)
}
