package main

import (
	"encoding/json"
	"encoding/xml"
	"fmt"
	"html/template"
	"io"
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
// 1) GLOBAL CONSTANTS & VARIABLES
// ----------------------------------------------------------------------

const (
	pomWorkerCount    = 10
	fetchTimeout      = 30 * time.Second
	outputReportFinal = "license_compliance_report.html"
)

var (
	// Maven concurrency + caching
	pomRequests  = make(chan fetchRequest, 50)
	wgWorkers    sync.WaitGroup
	pomCache     sync.Map // key: "group:artifact:version" -> *MavenPOM
	channelOpen  = true
	channelMutex sync.Mutex

	// Node & Python caching
	nodeCache   sync.Map // key: "package@version" -> *DependencyNode
	pythonCache sync.Map // key: "package@version" -> *DependencyNode
)

// ----------------------------------------------------------------------
// 2) COMMON TYPES
// ----------------------------------------------------------------------

type DependencyNode struct {
	Name       string
	Version    string
	License    string
	Copyleft   bool
	Parent     string            // "direct" or parent's coordinate
	Transitive []*DependencyNode // BFS children
	UsedPOMURL string            // For Maven => actual POM fetch URL; for Node/Python => package page link
	Direct     string            // top-level dependency that introduced this node
}

type ExtendedDep struct {
	Display      string
	Lookup       string
	Parent       string
	License      string
	IntroducedBy string
	PomURL       string
}

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

	Flattened []FlattenedDep
}

// FlattenedDep holds data for each row in the final table.
type FlattenedDep struct {
	Dependency string
	Version    string
	Parent     string
	TopLevel   string
	License    string
	Copyleft   bool
	Details    string // raw HTML anchor link
}

type introducerSet map[string]bool

// ----------------------------------------------------------------------
// 3) MAVEN FETCHING
// ----------------------------------------------------------------------

type fetchRequest struct {
	GroupID    string
	ArtifactID string
	Version    string
	ResultChan chan fetchResult
}

type fetchResult struct {
	POM     *MavenPOM
	UsedURL string
	Err     error
}

// ----------------------------------------------------------------------
// 4) MAVEN XML STRUCTURES
// ----------------------------------------------------------------------

type LicenseXML struct {
	Name string `xml:"name"`
	URL  string `xml:"url"`
}

type POMDep struct {
	GroupID    string `xml:"groupId"`
	ArtifactID string `xml:"artifactId"`
	Version    string `xml:"version"`
	Scope      string `xml:"scope"`
	Optional   string `xml:"optional"`
}

type MavenPOM struct {
	Licenses       []LicenseXML `xml:"licenses>license"`
	Dependencies   []POMDep     `xml:"dependencies>dependency"`
	DependencyMgmt struct {
		Dependencies []POMDep `xml:"dependencies>dependency"`
	} `xml:"dependencyManagement"`
	Parent struct {
		GroupID    string `xml:"groupId"`
		ArtifactID string `xml:"artifactId"`
		Version    string `xml:"version"`
	} `xml:"parent"`
}

// ----------------------------------------------------------------------
// 5) FILE DISCOVERY
// ----------------------------------------------------------------------

func findAllPOMFiles(root string) ([]string, error) {
	var files []string
	err := filepath.Walk(root, func(path string, info os.FileInfo, err error) error {
		if err == nil && !info.IsDir() && strings.EqualFold(info.Name(), "pom.xml") {
			files = append(files, path)
		}
		return nil
	})
	return files, err
}

func findAllTOMLFiles(root string) ([]string, error) {
	var files []string
	err := filepath.Walk(root, func(path string, info os.FileInfo, err error) error {
		if err == nil && !info.IsDir() && strings.HasSuffix(info.Name(), ".toml") {
			files = append(files, path)
		}
		return nil
	})
	return files, err
}

func findAllGradleFiles(root string) ([]string, error) {
	var files []string
	err := filepath.Walk(root, func(path string, info os.FileInfo, err error) error {
		if err == nil && !info.IsDir() {
			name := info.Name()
			if strings.EqualFold(name, "build.gradle") || strings.EqualFold(name, "build.gradle.kts") {
				files = append(files, path)
			}
		}
		return nil
	})
	return files, err
}

func findFile(root, target string) string {
	var found string
	filepath.Walk(root, func(path string, info os.FileInfo, err error) error {
		if err == nil && info.Name() == target {
			found = path
			return filepath.SkipDir
		}
		return nil
	})
	return found
}

// ----------------------------------------------------------------------
// 6) UTILITY FUNCTIONS
// ----------------------------------------------------------------------

func skipScope(scope, optional string) bool {
	s := strings.ToLower(strings.TrimSpace(scope))
	return s == "test" || s == "provided" || s == "system" || strings.EqualFold(strings.TrimSpace(optional), "true")
}

func splitGA(ga string) (string, string) {
	parts := strings.Split(ga, "/")
	if len(parts) != 2 {
		return "", ""
	}
	return parts[0], parts[1]
}

func removeCaretTilde(ver string) string {
	return strings.TrimLeft(strings.TrimSpace(ver), "^~")
}

func detectLicense(pom *MavenPOM) string {
	if len(pom.Licenses) > 0 {
		return pom.Licenses[0].Name
	}
	return "Unknown"
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

// parseVersionRange attempts to handle [1.0.0,2.0.0)
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

// buildMavenLink => direct artifact link
func buildMavenLink(group, artifact, version string) string {
	if strings.HasPrefix(group, "com.android.tools") {
		// Google
		return fmt.Sprintf("https://maven.google.com/web/index.html#%s:%s:%s", group, artifact, version)
	}
	// Default => mvnrepository
	return fmt.Sprintf("https://mvnrepository.com/artifact/%s/%s/%s", group, artifact, version)
}

// ----------------------------------------------------------------------
// 7) PARSING: MAVEN, TOML, GRADLE
// ----------------------------------------------------------------------

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

// --------------
// FIXED parseTOMLFile with fallback
// --------------
func parseTOMLFile(filePath string) (map[string]string, error) {
	tree, err := toml.LoadFile(filePath)
	if err != nil {
		return nil, fmt.Errorf("error loading TOML file '%s': %v", filePath, err)
	}
	versions, err := loadVersions(tree)
	if err != nil {
		return nil, err
	}
	librariesTree := tree.Get("libraries")
	if librariesTree == nil {
		return nil, fmt.Errorf("TOML file '%s' missing 'libraries' table", filePath)
	}
	libraries, ok := librariesTree.(*toml.Tree)
	if !ok {
		return nil, fmt.Errorf("'libraries' is not a valid TOML table in '%s'", filePath)
	}
	deps := make(map[string]string)
	for _, libKey := range libraries.Keys() {
		item := libraries.Get(libKey)
		lib, ok := item.(*toml.Tree)
		if !ok {
			continue
		}
		module, _ := lib.Get("module").(string)
		if module == "" {
			continue
		}
		// Check "version.ref" or fallback to "version"
		versionRef, _ := lib.Get("version.ref").(string)
		if versionRef == "" {
			if directV, _ := lib.Get("version").(string); directV != "" {
				versionRef = directV
			}
		}
		versionVal := "unknown"
		if versionRef != "" {
			// If "versionRef" is in the "versions" map, use that
			if val, ok2 := versions[versionRef]; ok2 {
				versionVal = val
			} else {
				// Otherwise, treat "versionRef" as the direct version
				versionVal = versionRef
			}
		}
		parts := strings.Split(module, ":")
		if len(parts) != 2 {
			continue
		}
		key := parts[0] + "/" + parts[1]
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

// ----------------------------------------------------------------------
// 8) MAVEN BFS WORKER & FETCH
// ----------------------------------------------------------------------

func pomFetchWorker() {
	defer wgWorkers.Done()
	for req := range pomRequests {
		pom, usedURL, err := fetchRemotePOM(req.GroupID, req.ArtifactID, req.Version)
		req.ResultChan <- fetchResult{POM: pom, UsedURL: usedURL, Err: err}
	}
}

func fetchRemotePOM(group, artifact, version string) (*MavenPOM, string, error) {
	groupPath := strings.ReplaceAll(group, ".", "/")
	urlCentral := fmt.Sprintf("https://repo1.maven.org/maven2/%s/%s/%s/%s-%s.pom", groupPath, artifact, version, artifact, version)
	urlGoogle := fmt.Sprintf("https://dl.google.com/dl/android/maven2/%s/%s/%s/%s-%s.pom", groupPath, artifact, version, artifact, version)
	client := http.Client{Timeout: fetchTimeout}

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
		return &pom, urlCentral, nil
	}
	if resp != nil {
		resp.Body.Close()
	}
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
		return &pom, urlGoogle, nil
	}
	if resp2 != nil {
		resp2.Body.Close()
	}
	return nil, "", fmt.Errorf("could not fetch POM for %s:%s:%s", group, artifact, version)
}

func concurrentFetchPOM(group, artifact, version string) (*MavenPOM, string, error) {
	key := fmt.Sprintf("%s:%s:%s", group, artifact, version)
	if cached, ok := pomCache.Load(key); ok {
		return cached.(*MavenPOM), "", nil
	}
	channelMutex.Lock()
	open := channelOpen
	channelMutex.Unlock()
	if !open {
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
	pomRequests <- req
	res := <-req.ResultChan
	if res.Err == nil && res.POM != nil {
		pomCache.Store(key, res.POM)
	}
	return res.POM, res.UsedURL, res.Err
}

// ----------------------------------------------------------------------
// 9) MAVEN/TOML/GRADLE BFS
// ----------------------------------------------------------------------

type queueItem struct {
	GroupArtifact string
	Version       string
	Depth         int
	ParentNode    *DependencyNode
	Direct        string
}

func buildTransitiveClosureJavaLike(sections []ReportSection) {
	for i := range sections {
		sec := &sections[i]
		allDeps := make(map[string]ExtendedDep)
		var rootNodes []*DependencyNode
		var queue []queueItem
		visited := make(map[string]introducerSet)

		// Enqueue direct dependencies
		for ga, ver := range sec.DirectDeps {
			key := ga + "@" + ver
			ds := make(introducerSet)
			ds[ga] = true
			visited[key] = ds
			node := &DependencyNode{
				Name:    ga,
				Version: ver,
				Parent:  "direct",
				Direct:  ga,
			}
			rootNodes = append(rootNodes, node)
			queue = append(queue, queueItem{
				GroupArtifact: ga,
				Version:       ver,
				Depth:         1,
				ParentNode:    node,
				Direct:        ga,
			})
			allDeps[key] = ExtendedDep{Display: ver, Lookup: ver, Parent: "direct"}
		}

		// BFS loop
		for len(queue) > 0 {
			it := queue[0]
			queue = queue[1:]
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

		for _, root := range rootNodes {
			setIntroducedBy(root, root.Name, allDeps)
		}
		sec.DependencyTree = rootNodes
		for k, v := range allDeps {
			sec.AllDeps[k] = v
		}
		sec.DirectCount = len(sec.DirectDeps)
		for key := range sec.AllDeps {
			if strings.Contains(key, "@") {
				parts := strings.Split(key, "@")
				if len(parts) == 2 {
					if parts[1] == "unknown" {
						sec.UnknownCount++
					} else {
						sec.TransitiveCount++
					}
				}
			}
		}
		sec.IndirectCount = sec.TransitiveCount - sec.DirectCount

		// BFS => count copyleft
		for _, root := range rootNodes {
			countCopyleftInTree(root, sec)
		}

		// Sort BFS root nodes
		sort.Slice(rootNodes, func(i, j int) bool {
			return colorRank(rootNodes[i]) < colorRank(rootNodes[j])
		})
		for _, root := range rootNodes {
			sortDependencyNodes(root)
		}
	}
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

func countCopyleftInTree(node *DependencyNode, sec *ReportSection) {
	if node.Copyleft {
		sec.CopyleftCount++
	}
	for _, child := range node.Transitive {
		countCopyleftInTree(child, sec)
	}
}

// colorRank => 0=red(copyleft), 1=yellow(unknown), 2=green(known)
func colorRank(n *DependencyNode) int {
	if n.Copyleft {
		return 0
	} else if strings.EqualFold(n.License, "unknown") {
		return 1
	}
	return 2
}

func sortDependencyNodes(node *DependencyNode) {
	sort.Slice(node.Transitive, func(i, j int) bool {
		ri := colorRank(node.Transitive[i])
		rj := colorRank(node.Transitive[j])
		if ri != rj {
			return ri < rj
		}
		return node.Transitive[i].Name < node.Transitive[j].Name
	})
	for _, child := range node.Transitive {
		sortDependencyNodes(child)
	}
}

// ----------------------------------------------------------------------
// 10) NODE & PYTHON BFS WITH CACHING
// ----------------------------------------------------------------------

type requirement struct {
	name, version string
}

func parseNodeDependencies(nodeFile string) ([]*DependencyNode, error) {
	data, err := os.ReadFile(nodeFile)
	if err != nil {
		return nil, err
	}
	var pkg map[string]interface{}
	if err := json.Unmarshal(data, &pkg); err != nil {
		return nil, err
	}
	deps, ok := pkg["dependencies"].(map[string]interface{})
	if !ok || deps == nil {
		return nil, fmt.Errorf("no dependencies found in package.json")
	}
	visited := make(map[string]bool)
	var results []*DependencyNode
	for nm, ver := range deps {
		vstr, _ := ver.(string)
		nd, err := resolveNodeDependency(nm, removeCaretTilde(vstr), visited)
		if err == nil && nd != nil {
			results = append(results, nd)
		}
	}
	return results, nil
}

func resolveNodeDependency(pkgName, version string, visited map[string]bool) (*DependencyNode, error) {
	key := pkgName + "@" + version
	if visited[key] {
		return nil, nil
	}
	visited[key] = true
	if val, ok := nodeCache.Load(key); ok {
		return val.(*DependencyNode), nil
	}
	url := "https://registry.npmjs.org/" + pkgName
	resp, err := http.Get(url)
	if err != nil {
		return nil, err
	}
	defer resp.Body.Close()

	var data map[string]interface{}
	if err := json.NewDecoder(resp.Body).Decode(&data); err != nil {
		return nil, err
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
					version = lat
					verData = vMap
					ok = true
				}
			}
		}
	}
	license := "Unknown"
	var trans []*DependencyNode
	if ok && verData != nil {
		license = findNpmLicense(verData)
		if deps, ok2 := verData["dependencies"].(map[string]interface{}); ok2 {
			for subName, subVer := range deps {
				sv, _ := subVer.(string)
				child, err := resolveNodeDependency(subName, removeCaretTilde(sv), visited)
				if err == nil && child != nil {
					trans = append(trans, child)
				}
			}
		}
	}
	nd := &DependencyNode{
		Name:       pkgName,
		Version:    version,
		License:    license,
		UsedPOMURL: "https://www.npmjs.com/package/" + pkgName,
		Copyleft:   isCopyleftChecker(license),
		Transitive: trans,
		Direct:     pkgName,
	}
	nodeCache.Store(key, nd)
	return nd, nil
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

func parsePythonDependencies(reqFile string) ([]*DependencyNode, error) {
	data, err := os.ReadFile(reqFile)
	if err != nil {
		return nil, err
	}
	lines := strings.Split(string(data), "\n")
	var reqs []requirement
	for _, line := range lines {
		sline := strings.TrimSpace(line)
		if sline == "" || strings.HasPrefix(sline, "#") {
			continue
		}
		parts := strings.Split(sline, "==")
		if len(parts) != 2 {
			parts = strings.Split(sline, ">=")
			if len(parts) != 2 {
				log.Println("Invalid python requirement line:", sline)
				continue
			}
		}
		reqs = append(reqs, requirement{strings.TrimSpace(parts[0]), strings.TrimSpace(parts[1])})
	}
	visited := make(map[string]bool)
	var results []*DependencyNode
	for _, r := range reqs {
		nd, err := resolvePythonDependency(r.name, r.version, visited)
		if err == nil && nd != nil {
			results = append(results, nd)
		} else if err != nil {
			log.Println("Python parse error for", r.name, ":", err)
		}
	}
	return results, nil
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
		return strings.TrimSpace(parts[0]), ""
	}
	return "", ""
}

func resolvePythonDependency(pkgName, version string, visited map[string]bool) (*DependencyNode, error) {
	key := strings.ToLower(pkgName) + "@" + version
	if visited[key] {
		return nil, nil
	}
	visited[key] = true
	if val, ok := pythonCache.Load(key); ok {
		return val.(*DependencyNode), nil
	}
	url := "https://pypi.org/pypi/" + pkgName + "/json"
	resp, err := http.Get(url)
	if err != nil {
		return nil, err
	}
	defer resp.Body.Close()
	if resp.StatusCode != 200 {
		return nil, fmt.Errorf("PyPI returned status %d for package: %s", resp.StatusCode, pkgName)
	}
	var data map[string]interface{}
	if err := json.NewDecoder(resp.Body).Decode(&data); err != nil {
		return nil, err
	}
	info, ok := data["info"].(map[string]interface{})
	if !ok {
		return nil, fmt.Errorf("info missing for %s", pkgName)
	}
	if version == "" {
		if v, ok := info["version"].(string); ok {
			version = v
		}
	}
	releases, _ := data["releases"].(map[string]interface{})
	if releases != nil {
		if _, ok := releases[version]; !ok {
			if v, ok2 := info["version"].(string); ok2 && v != "" {
				version = v
			}
		}
	}
	license := "Unknown"
	if l, ok := info["license"].(string); ok && l != "" {
		license = l
	}
	var trans []*DependencyNode
	if arr, ok := info["requires_dist"].([]interface{}); ok && len(arr) > 0 {
		for _, x := range arr {
			line, _ := x.(string)
			subName, _ := parsePyRequiresDistLine(line)
			if subName == "" {
				continue
			}
			child, err := resolvePythonDependency(subName, "", visited)
			if err == nil && child != nil {
				trans = append(trans, child)
			}
		}
	}
	nd := &DependencyNode{
		Name:       pkgName,
		Version:    version,
		License:    license,
		UsedPOMURL: "https://pypi.org/project/" + pkgName,
		Copyleft:   isCopyleftChecker(license),
		Transitive: trans,
		Direct:     pkgName,
	}
	pythonCache.Store(key, nd)
	return nd, nil
}

// ----------------------------------------------------------------------
// 11) FLATTEN BFS => TABLE ROWS
// ----------------------------------------------------------------------

func flattenBFS(sec *ReportSection) {
	var copyleftRows, unknownRows, knownRows []FlattenedDep

	var walk func(node *DependencyNode)
	walk = func(node *DependencyNode) {
		// 1) If the version has a placeholder ${...}, treat as "unknown".
		// 2) Remove bracket/parenthesis chars: [ ] ( )
		versionToUse := node.Version
		if strings.Contains(versionToUse, "${") {
			versionToUse = "unknown"
		}
		versionToUse = strings.ReplaceAll(versionToUse, "[", "")
		versionToUse = strings.ReplaceAll(versionToUse, "]", "")
		versionToUse = strings.ReplaceAll(versionToUse, "(", "")
		versionToUse = strings.ReplaceAll(versionToUse, ")", "")

		lowerPath := strings.ToLower(sec.FilePath)
		var detail string

		if strings.HasSuffix(lowerPath, "pom.xml") ||
			strings.HasSuffix(lowerPath, "build.gradle") ||
			strings.HasSuffix(lowerPath, ".toml") {

			// For Maven/TOML/Gradle => direct artifact link
			grp, art := splitGA(node.Name)
			artifactURL := buildMavenLink(grp, art, versionToUse)
			detail = fmt.Sprintf(
				`<a href="%s" target="_blank">%s:%s:%s</a>`,
				artifactURL, grp, art, versionToUse,
			)

		} else if strings.Contains(lowerPath, "package.json") ||
			strings.Contains(lowerPath, "requirements.txt") {

			// Node/Python => link to package page
			detail = fmt.Sprintf(
				`<a href="%s" target="_blank">%s@%s</a>`,
				node.UsedPOMURL, node.Name, node.Version,
			)

		} else {
			// fallback
			detail = node.UsedPOMURL
		}

		row := FlattenedDep{
			Dependency: node.Name,
			Version:    versionToUse,
			Parent:     node.Parent,
			TopLevel:   node.Direct,
			License:    node.License,
			Copyleft:   node.Copyleft,
			Details:    detail,
		}

		if node.Copyleft {
			copyleftRows = append(copyleftRows, row)
		} else if strings.EqualFold(node.License, "unknown") {
			unknownRows = append(unknownRows, row)
		} else {
			knownRows = append(knownRows, row)
		}

		for _, child := range node.Transitive {
			walk(child)
		}
	}

	for _, root := range sec.DependencyTree {
		walk(root)
	}

	// Combine: copyleft first, unknown second, known last
	sec.Flattened = append(copyleftRows, append(unknownRows, knownRows...)...)
}

// ----------------------------------------------------------------------
// 12) TEMPLATE HELPER: dict
// ----------------------------------------------------------------------

func dict(values ...interface{}) map[string]interface{} {
	if len(values)%2 != 0 {
		panic("dict expects an even number of arguments")
	}
	m := make(map[string]interface{}, len(values)/2)
	for i := 0; i < len(values); i += 2 {
		key, ok := values[i].(string)
		if !ok {
			panic("dict keys must be strings")
		}
		m[key] = values[i+1]
	}
	return m
}

// ----------------------------------------------------------------------
// 13) FINAL HTML TEMPLATE
// ----------------------------------------------------------------------

var finalHTML = `
<!DOCTYPE html>
<html>
<head>
  <meta charset="utf-8">
  <title>Combined Dependency Report</title>
  <style>
    body { font-family: Arial, sans-serif; }
    h1, h2, h3 { margin-top: 1em; }
    table { border-collapse: collapse; width: 95%; margin: 1em 0; }
    th, td { border: 1px solid #ccc; padding: 6px 8px; }
    th { background: #f7f7f7; }

    tr.copyleft { background-color: #ffcccc; }
    tr.unknown  { background-color: #ffffcc; }
    tr.known    { background-color: #ccffcc; }

    li.copyleft { background-color: #ffcccc; margin-bottom: 0.3em; padding: 4px; }
    li.unknown  { background-color: #ffffcc; margin-bottom: 0.3em; padding: 4px; }
    li.known    { background-color: #ccffcc; margin-bottom: 0.3em; padding: 4px; }

    .toggle-btn { cursor: pointer; font-weight: bold; color: #007bff; margin-right: 5px; }
    .toggle-btn:hover { text-decoration: underline; }
    .hidden { display: none; }
    ul.tree { list-style-type: none; padding-left: 1em; }
  </style>
  <script>
    function toggleSubtree(id, btn) {
      var el = document.getElementById(id);
      if (!el) return;
      if (el.classList.contains('hidden')) {
        el.classList.remove('hidden');
        if (btn) btn.textContent = "▼";
      } else {
        el.classList.add('hidden');
        if (btn) btn.textContent = "▶";
      }
    }
  </script>
</head>
<body>
<h1>Combined Dependency Report</h1>

{{range .Sections}}
  {{$fp := .FilePath}}
  <h2>{{$fp}}</h2>
  <p>
    Direct Dependencies: {{.DirectCount}}<br/>
    Transitive (incl. direct): {{.TransitiveCount}}<br/>
    Indirect: {{.IndirectCount}}<br/>
    Copyleft: {{.CopyleftCount}}<br/>
    Unknown: {{.UnknownCount}}
  </p>

  <h3>Dependency Table</h3>
  <table>
    <tr>
      <th>Dependency</th>
      <th>Version</th>
      <th>Parent</th>
      <th>Top-Level</th>
      <th>License</th>
      <th>Project Details</th>
    </tr>
    {{range .Flattened}}
    <tr class="{{if .Copyleft}}copyleft{{else if eq .License "Unknown"}}unknown{{else}}known{{end}}">
      <td>{{.Dependency}}</td>
      <td>{{.Version}}</td>
      <td>{{.Parent}}</td>
      <td>{{.TopLevel}}</td>
      <td>{{.License}}</td>
      <td>{{.Details | safeHTML}}</td>
    </tr>
    {{end}}
  </table>

  <h3>Dependency Tree</h3>
  <ul class="tree">
    {{range $i, $root := .DependencyTree}}
    <li class="{{if $root.Copyleft}}copyleft{{else if eq $root.License "Unknown"}}unknown{{else}}known{{end}}">
      <span class="toggle-btn" onclick="toggleSubtree('node-{{$fp}}-{{$i}}', this)">▶</span>
      <strong>{{$root.Name}}@{{$root.Version}}</strong>
      {{if eq $root.Parent "direct"}}(direct){{else}}(introduced by {{$root.Parent}}){{end}}
      <br/>
      License: {{$root.License}}<br/>
      POM File Link: {{if $root.UsedPOMURL}}<a href="{{$root.UsedPOMURL}}" target="_blank">Open</a>{{else}}(none){{end}}

      {{if $root.Transitive}}
      <ul class="hidden" id="node-{{$fp}}-{{$i}}">
        {{template "subTree" (dict "Nodes" $root.Transitive "File" $fp "Prefix" (print $i))}}
      </ul>
      {{end}}
    </li>
    {{end}}
  </ul>
  <hr/>
{{end}}

{{define "subTree"}}
  {{$data := .}}
  {{range $j, $child := $data.Nodes}}
  <li class="{{if $child.Copyleft}}copyleft{{else if eq $child.License "Unknown"}}unknown{{else}}known{{end}}">
    <span class="toggle-btn" onclick="toggleSubtree('sub-{{$data.File}}-{{$data.Prefix}}-{{$j}}', this)">▶</span>
    <strong>{{$child.Name}}@{{$child.Version}}</strong>
    {{if eq $child.Parent "direct"}}(direct){{else}}(introduced by {{$child.Parent}}){{end}}
    <br/>
    License: {{$child.License}}<br/>
    POM File Link: {{if $child.UsedPOMURL}}<a href="{{$child.UsedPOMURL}}" target="_blank">Open</a>{{else}}(none){{end}}

    {{if $child.Transitive}}
    <ul class="hidden" id="sub-{{$data.File}}-{{$data.Prefix}}-{{$j}}">
      {{template "subTree" (dict "Nodes" $child.Transitive "File" $data.File "Prefix" (print $data.Prefix "-" $j))}}
    </ul>
    {{end}}
  </li>
  {{end}}
{{end}}
</body>
</html>
`

// ----------------------------------------------------------------------
// 16) MAIN
// ----------------------------------------------------------------------

func main() {
	// Start Maven BFS workers
	for i := 0; i < pomWorkerCount; i++ {
		wgWorkers.Add(1)
		go pomFetchWorker()
	}

	rootDir := "."

	var sections []ReportSection

	// 1) Maven
	pomFiles, err := findAllPOMFiles(rootDir)
	if err != nil {
		log.Println("Error finding pom.xml files:", err)
	}
	for _, pf := range pomFiles {
		deps, err := parseOneLocalPOMFile(pf)
		if err != nil {
			log.Println("Error parsing pom.xml:", err)
			continue
		}
		rs := ReportSection{
			FilePath:   pf,
			DirectDeps: deps,
			AllDeps:    make(map[string]ExtendedDep),
		}
		sections = append(sections, rs)
	}

	// 2) TOML
	tomlFiles, err := findAllTOMLFiles(rootDir)
	if err != nil {
		log.Println("Error finding .toml files:", err)
	}
	for _, tf := range tomlFiles {
		deps, err := parseTOMLFile(tf)
		if err != nil {
			log.Println("Error parsing TOML:", err)
			continue
		}
		rs := ReportSection{
			FilePath:   tf,
			DirectDeps: deps,
			AllDeps:    make(map[string]ExtendedDep),
		}
		sections = append(sections, rs)
	}

	// 3) Gradle
	gradleFiles, err := findAllGradleFiles(rootDir)
	if err != nil {
		log.Println("Error finding Gradle files:", err)
	}
	for _, gf := range gradleFiles {
		deps, err := parseBuildGradleFile(gf)
		if err != nil {
			log.Println("Error parsing Gradle:", err)
			continue
		}
		rs := ReportSection{
			FilePath:   gf,
			DirectDeps: deps,
			AllDeps:    make(map[string]ExtendedDep),
		}
		sections = append(sections, rs)
	}

	// BFS expansions for Maven/TOML/Gradle
	buildTransitiveClosureJavaLike(sections)

	// 4) Node BFS
	nodeFile := findFile(rootDir, "package.json")
	if nodeFile != "" {
		nodeDeps, err := parseNodeDependencies(nodeFile)
		if err != nil {
			log.Println("Error parsing Node BFS:", err)
		} else if len(nodeDeps) > 0 {
			direct := make(map[string]string)
			for _, n := range nodeDeps {
				direct[n.Name] = n.Version
			}
			rs := ReportSection{
				FilePath:       nodeFile,
				DirectDeps:     direct,
				AllDeps:        make(map[string]ExtendedDep),
				DependencyTree: nodeDeps,
			}
			rs.DirectCount = len(rs.DirectDeps)
			rs.TransitiveCount = countTotalDependencies(rs.DependencyTree)
			rs.IndirectCount = rs.TransitiveCount - rs.DirectCount
			sections = append(sections, rs)
		}
	}

	// 5) Python BFS
	pyFile := findFile(rootDir, "requirements.txt")
	if pyFile != "" {
		pyDeps, err := parsePythonDependencies(pyFile)
		if err != nil {
			log.Println("Error parsing Python BFS:", err)
		} else if len(pyDeps) > 0 {
			direct := make(map[string]string)
			for _, p := range pyDeps {
				direct[p.Name] = p.Version
			}
			rs := ReportSection{
				FilePath:       pyFile,
				DirectDeps:     direct,
				AllDeps:        make(map[string]ExtendedDep),
				DependencyTree: pyDeps,
			}
			rs.DirectCount = len(rs.DirectDeps)
			rs.TransitiveCount = countTotalDependencies(rs.DependencyTree)
			rs.IndirectCount = rs.TransitiveCount - rs.DirectCount
			sections = append(sections, rs)
		}
	}

	// Close BFS channel
	close(pomRequests)
	wgWorkers.Wait()

	// Flatten BFS => table
	for i := range sections {
		flattenBFS(&sections[i])
	}

	type finalData struct {
		Sections []ReportSection
	}
	fd := finalData{Sections: sections}

	funcMap := template.FuncMap{
		"safeHTML": func(s string) template.HTML {
			return template.HTML(s)
		},
		"dict": dict,
	}

	tmpl, err := template.New("report").Funcs(funcMap).Parse(finalHTML)
	if err != nil {
		log.Fatalf("Error parsing template: %v", err)
	}

	f, err := os.Create(outputReportFinal)
	if err != nil {
		log.Fatalf("Cannot create final HTML: %v", err)
	}
	defer f.Close()

	if err := tmpl.Execute(f, fd); err != nil {
		log.Fatalf("Error executing template: %v", err)
	}

	fmt.Println("Colored table + BFS dependency report generated at:", outputReportFinal)
}

// ----------------------------------------------------------------------
// 16) COUNT TOTAL DEPENDENCIES
// ----------------------------------------------------------------------

func countTotalDependencies(nodes []*DependencyNode) int {
	count := 0
	var rec func([]*DependencyNode)
	rec = func(nl []*DependencyNode) {
		for _, n := range nl {
			count++
			rec(n.Transitive)
		}
	}
	rec(nodes)
	return count
}
