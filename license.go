package main

import (
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
	"strings"
	"sync"
	"time"

	"github.com/pelletier/go-toml"
)

// ----------------------------------------------------------------------
// 1) GLOBAL CONFIG & SHARED TYPES
// ----------------------------------------------------------------------

const (
	localPOMCacheDir       = ".pom-cache"
	pomWorkerCount         = 10
	fetchTimeout           = 30 * time.Second
	outputReportFinal      = "license_compliance_report.html"
)

var (
	pomRequests  = make(chan fetchRequest, 50)
	wgWorkers    sync.WaitGroup
	pomCache     sync.Map // key: "group:artifact:version" -> *MavenPOM
	channelOpen  = true
	channelMutex sync.Mutex
)

// BFS concurrency for Maven
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
// 2) DEPENDENCY STRUCTS & REPORT SECTIONS
// ----------------------------------------------------------------------

// BFS Node (used by all file types)
type DependencyNode struct {
	Name       string
	Version    string
	License    string
	Copyleft   bool
	Parent     string // "direct" or e.g. "com.foo/bar@1.0"
	Transitive []*DependencyNode
	UsedPOMURL string // For Maven, store the actual POM link; for Node/Python, store the "Details" link
	Direct     string // BFS "root" name that introduced it
}

// ExtendedDep is used to store introducedBy, etc.
type ExtendedDep struct {
	Display      string
	Lookup       string
	Parent       string
	License      string
	IntroducedBy string
	PomURL       string
}

// Each discovered file => 1 "ReportSection"
type ReportSection struct {
	FilePath        string
	DirectDeps      map[string]string // "group/artifact" => version
	AllDeps         map[string]ExtendedDep
	DependencyTree  []*DependencyNode

	TransitiveCount int
	DirectCount     int
	IndirectCount   int
	CopyleftCount   int
	UnknownCount    int

	Flattened []FlattenedDep // We'll store a flattened table of BFS
}

// For the table portion
type FlattenedDep struct {
	Dependency string
	Version    string
	Parent     string
	TopLevel   string
	License    string
	Copyleft   bool
	Details    string // For Node/Python or Maven POM
}

// ----------------------------------------------------------------------
// 3) MAVEN/TOML/GRADLE STRUCTS & PARSING
// ----------------------------------------------------------------------

type License struct {
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

// Find pom.xml
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

// TOML
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

// Gradle
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
// 4) NODE & PYTHON PARSING
// ----------------------------------------------------------------------

type NodeDependency struct {
	Name       string
	Version    string
	License    string
	Details    string
	Copyleft   bool
	Transitive []*NodeDependency
	Language   string
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

// findFile for Node (`package.json`) & Python (`requirements.txt`)
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

// Node BFS
func parseNodeDependencies(nodeFile string) ([]*NodeDependency, error) {
	data, err := os.ReadFile(nodeFile)
	if err != nil {
		return nil, err
	}
	var pkg map[string]interface{}
	if e := json.Unmarshal(data, &pkg); e != nil {
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

func removeCaretTilde(ver string) string {
	ver = strings.TrimSpace(ver)
	return strings.TrimLeft(ver, "^~")
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
		// fallback to "latest"
		if dist, ok2 := data["dist-tags"].(map[string]interface{}); ok2 {
			if lat, ok2 := dist["latest"].(string); ok2 {
				if vMap, ok3 := vs[lat].(map[string]interface{}); ok3 {
					log.Printf("Node fallback: no exact version %s for %s, using 'latest' => %s",
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

// Python BFS
func parsePythonDependencies(reqFile string) ([]*PythonDependency, error) {
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
		reqs = append(reqs, requirement{nm, ver})
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
	resp, err := http.Get(url)
	if err != nil {
		return nil, err
	}
	defer resp.Body.Close()

	if resp.StatusCode != 200 {
		log.Printf("ERROR: PyPI returned %d for %s", resp.StatusCode, pkgName)
		return nil, fmt.Errorf("PyPI returned status: %d for package: %s", resp.StatusCode, pkgName)
	}
	var data map[string]interface{}
	if e := json.NewDecoder(resp.Body).Decode(&data); e != nil {
		return nil, e
	}

	info, _ := data["info"].(map[string]interface{})
	if info == nil {
		log.Printf("ERROR: 'info' missing in PyPI data for %s", pkgName)
		return nil, fmt.Errorf("info missing for %s", pkgName)
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
				version = infoVer
			}
		}
	}
	license := "Unknown"
	if l, ok := info["license"].(string); ok && l != "" {
		license = l
	}
	var trans []*PythonDependency
	if distArr, ok := info["requires_dist"].([]interface{}); ok && len(distArr) > 0 {
		for _, x := range distArr {
			line, _ := x.(string)
			if line == "" {
				continue
			}
			subName, _ := parsePyRequiresDistLine(line)
			if subName == "" {
				continue
			}
			ch, e2 := resolvePythonDependency(subName, "", visited)
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
// 5) HELPER: BFS WORKERS
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

// type that caused "undefined" error
type introducerSet map[string]bool

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
		if e := xml.Unmarshal(data, &pom); e != nil {
			return nil, "", e
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
		if e := xml.Unmarshal(data, &pom); e != nil {
			return nil, "", e
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

func pomFetchWorker() {
	defer wgWorkers.Done()
	for req := range pomRequests {
		pom, usedURL, err := fetchRemotePOM(req.GroupID, req.ArtifactID, req.Version)
		req.ResultChan <- fetchResult{POM: pom, UsedURL: usedURL, Err: err}
	}
}

// ----------------------------------------------------------------------
// 6) BFS FOR MAVEN/TOML/GRADLE
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
		// add direct
		for ga, ver := range sec.DirectDeps {
			key := ga + "@" + ver
			allDeps[key] = ExtendedDep{Display: ver, Lookup: ver, Parent: "direct"}
		}

		visited := make(map[string]introducerSet)
		var queue []queueItem
		var rootNodes []*DependencyNode

		// init BFS
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
		}

		// BFS
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
		// introducedBy
		for _, root := range rootNodes {
			setIntroducedBy(root, root.Name, allDeps)
		}
		for k, v := range allDeps {
			sec.AllDeps[k] = v
		}
		sec.DependencyTree = rootNodes

		// stats
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

		// count copyleft
		for _, root := range rootNodes {
			countCopyleftInTree(root, sec)
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
	for _, ch := range node.Transitive {
		countCopyleftInTree(ch, sec)
	}
}

// ----------------------------------------------------------------------
// 7) NODE/PYTHON => BFS -> "ReportSection"
// ----------------------------------------------------------------------

func convertNodeDepsToReportSection(filePath string, nodeDeps []*NodeDependency) ReportSection {
	directDeps := make(map[string]string)
	allDeps := make(map[string]ExtendedDep)
	var rootNodes []*DependencyNode

	// each top-level => BFS root
	for _, nd := range nodeDeps {
		key := nd.Name + "@" + nd.Version
		directDeps[nd.Name] = nd.Version
		allDeps[key] = ExtendedDep{Display: nd.Version, Lookup: nd.Version, Parent: "direct"}

		root := convertOneNodeDep(nd, "", "")
		rootNodes = append(rootNodes, root)
	}
	for _, root := range rootNodes {
		setIntroducedByNode(root, root.Name, allDeps)
	}

	sec := ReportSection{
		FilePath:   filePath,
		DirectDeps: directDeps,
		AllDeps:    allDeps,
	}
	sec.DependencyTree = rootNodes
	sec.DirectCount = len(directDeps)

	for k := range allDeps {
		if strings.Contains(k, "@") {
			parts := strings.Split(k, "@")
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
	for _, root := range rootNodes {
		countCopyleftInTree(root, &sec)
	}
	return sec
}

func convertOneNodeDep(nd *NodeDependency, parentGA, directName string) *DependencyNode {
	myParent := "direct"
	myDirect := nd.Name
	if parentGA != "" {
		myParent = parentGA
		myDirect = directName
	}
	node := &DependencyNode{
		Name:       nd.Name,
		Version:    nd.Version,
		License:    nd.License,
		Copyleft:   nd.Copyleft,
		Parent:     myParent,
		Direct:     myDirect,
		UsedPOMURL: nd.Details,
	}
	for _, child := range nd.Transitive {
		cn := convertOneNodeDep(child, nd.Name+"@"+nd.Version, nd.Name)
		node.Transitive = append(node.Transitive, cn)
	}
	return node
}

func setIntroducedByNode(node *DependencyNode, rootName string, all map[string]ExtendedDep) {
	key := node.Name + "@" + node.Version
	inf := all[key]
	if inf.IntroducedBy == "" {
		inf.IntroducedBy = rootName
	} else if !strings.Contains(inf.IntroducedBy, rootName) {
		inf.IntroducedBy += ", " + rootName
	}
	all[key] = inf
	for _, ch := range node.Transitive {
		setIntroducedByNode(ch, rootName, all)
	}
}

// Python BFS => convert to same BFS
func convertPythonDepsToReportSection(filePath string, pyDeps []*PythonDependency) ReportSection {
	directDeps := make(map[string]string)
	allDeps := make(map[string]ExtendedDep)
	var rootNodes []*DependencyNode

	for _, pd := range pyDeps {
		key := pd.Name + "@" + pd.Version
		directDeps[pd.Name] = pd.Version
		allDeps[key] = ExtendedDep{Display: pd.Version, Lookup: pd.Version, Parent: "direct"}

		root := convertOnePyDep(pd, "", "")
		rootNodes = append(rootNodes, root)
	}
	for _, root := range rootNodes {
		setIntroducedByPy(root, root.Name, allDeps)
	}

	sec := ReportSection{
		FilePath:   filePath,
		DirectDeps: directDeps,
		AllDeps:    allDeps,
	}
	sec.DependencyTree = rootNodes
	sec.DirectCount = len(directDeps)

	for k := range allDeps {
		if strings.Contains(k, "@") {
			parts := strings.Split(k, "@")
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
	for _, root := range rootNodes {
		countCopyleftInTree(root, &sec)
	}
	return sec
}

func convertOnePyDep(pd *PythonDependency, parentGA, directName string) *DependencyNode {
	myParent := "direct"
	myDirect := pd.Name
	if parentGA != "" {
		myParent = parentGA
		myDirect = directName
	}
	node := &DependencyNode{
		Name:       pd.Name,
		Version:    pd.Version,
		License:    pd.License,
		Copyleft:   pd.Copyleft,
		Parent:     myParent,
		Direct:     myDirect,
		UsedPOMURL: pd.Details,
	}
	for _, ch := range pd.Transitive {
		child := convertOnePyDep(ch, pd.Name+"@"+pd.Version, pd.Name)
		node.Transitive = append(node.Transitive, child)
	}
	return node
}

func setIntroducedByPy(node *DependencyNode, rootName string, all map[string]ExtendedDep) {
	key := node.Name + "@" + node.Version
	inf := all[key]
	if inf.IntroducedBy == "" {
		inf.IntroducedBy = rootName
	} else if !strings.Contains(inf.IntroducedBy, rootName) {
		inf.IntroducedBy += ", " + rootName
	}
	all[key] = inf
	for _, ch := range node.Transitive {
		setIntroducedByPy(ch, rootName, all)
	}
}

// ----------------------------------------------------------------------
// 8) FLATTEN BFS => TABLE
// ----------------------------------------------------------------------

func flattenBFS(sec *ReportSection) {
	var rows []FlattenedDep
	for _, root := range sec.DependencyTree {
		rows = flattenOneTree(root, rows)
	}
	sec.Flattened = rows
}

func flattenOneTree(node *DependencyNode, rows []FlattenedDep) []FlattenedDep {
	row := FlattenedDep{
		Dependency: node.Name,
		Version:    node.Version,
		Parent:     node.Parent,
		TopLevel:   node.Direct,
		License:    node.License,
		Copyleft:   node.Copyleft,
		Details:    node.UsedPOMURL, // For Node/Python or Maven
	}
	rows = append(rows, row)
	for _, child := range node.Transitive {
		rows = flattenOneTree(child, rows)
	}
	return rows
}

// ----------------------------------------------------------------------
// 9) FINAL HTML: BFS bullet-lists + Table for each file
// ----------------------------------------------------------------------
//
// We'll produce one BFS bullet-list and one table per file.

var finalHTML = `
<!DOCTYPE html>
<html>
<head>
  <meta charset="utf-8">
  <title>Combined BFS + Table Report</title>
  <style>
  body { font-family: Arial, sans-serif; }
  h1 { margin-top: 0; }
  h2 { margin-top: 1em; }
  .copyleft { background-color: #ffe6e6; }
  .unknown { background-color: #ffffcc; }

  ul { list-style-type: disc; margin-left: 2em; }
  li { margin-bottom: 0.5em; }

  table { border-collapse: collapse; width: 95%; margin: 1em 0; }
  th, td { border: 1px solid #ccc; padding: 6px 8px; }
  th { background: #f7f7f7; }
  </style>
</head>
<body>
<h1>Dependency Report: BFS + Table</h1>

{{range .Sections}}
<h2>{{.FilePath}}</h2>
<p>
  Direct: {{.DirectCount}}<br/>
  Transitive (incl. direct): {{.TransitiveCount}}<br/>
  Indirect: {{.IndirectCount}}<br/>
  Copyleft: {{.CopyleftCount}}<br/>
  Unknown: {{.UnknownCount}}
</p>

<!-- BFS Bullet-List -->
<h3>BFS Tree</h3>
<ul>
{{range .DependencyTree}}
  <li>
    <strong>{{.Name}}@{{.Version}}</strong>
    {{if eq .Parent "direct"}}(direct){{else}}(introduced by {{.Parent}}){{end}}
    <br/>
    License: <span {{if .Copyleft}}class="copyleft"{{else if eq .License "Unknown"}}class="unknown"{{end}}>{{.License}}</span>
    {{if .UsedPOMURL}} [<a href="{{.UsedPOMURL}}" target="_blank">Link</a>]{{end}}
    {{template "bfsList" .Transitive}}
  </li>
{{end}}
</ul>

<!-- Table -->
<h3>Flattened Table</h3>
<table>
  <tr>
    <th>Dependency</th>
    <th>Version</th>
    <th>Parent</th>
    <th>Top-Level</th>
    <th>License</th>
    <th>Details</th>
  </tr>
  {{range .Flattened}}
  <tr>
    <td>{{.Dependency}}</td>
    <td>{{.Version}}</td>
    <td>{{.Parent}}</td>
    <td>{{.TopLevel}}</td>
    <td {{if .Copyleft}}class="copyleft"{{else if eq .License "Unknown"}}class="unknown"{{end}}>{{.License}}</td>
    <td>
      {{if .Details}}<a href="{{.Details}}" target="_blank">Link</a>{{end}}
    </td>
  </tr>
  {{end}}
</table>
<hr/>
{{end}}

{{define "bfsList"}}
<ul>
  {{range .}}
  <li>
    <strong>{{.Name}}@{{.Version}}</strong>
    <br/>
    License: <span {{if .Copyleft}}class="copyleft"{{else if eq .License "Unknown"}}class="unknown"{{end}}>{{.License}}</span>
    {{if .UsedPOMURL}} [<a href="{{.UsedPOMURL}}" target="_blank">Link</a>]{{end}}
    {{template "bfsList" .Transitive}}
  </li>
  {{end}}
</ul>
{{end}}

</body>
</html>
`

// ----------------------------------------------------------------------
// 10) MAIN
// ----------------------------------------------------------------------

func main() {
	// Start Maven BFS workers
	for i := 0; i < pomWorkerCount; i++ {
		wgWorkers.Add(1)
		go pomFetchWorker()
	}

	rootDir := "."

	// Gather sections
	var sections []ReportSection

	// 1) Maven/TOML/Gradle
	pomFiles, _ := findAllPOMFiles(rootDir)
	for _, pf := range pomFiles {
		deps, err := parseOneLocalPOMFile(pf)
		if err != nil {
			log.Println("Error parsing POM:", err)
			continue
		}
		rs := ReportSection{
			FilePath:   pf,
			DirectDeps: deps,
			AllDeps:    make(map[string]ExtendedDep),
		}
		sections = append(sections, rs)
	}

	tomlFiles, _ := findAllTOMLFiles(rootDir)
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

	gradleFiles, _ := findAllGradleFiles(rootDir)
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

	// BFS expansions
	buildTransitiveClosureJavaLike(sections)

	// 2) Node => BFS
	nodeFile := findFile(rootDir, "package.json")
	if nodeFile != "" {
		nodeDeps, err := parseNodeDependencies(nodeFile)
		if err == nil && len(nodeDeps) > 0 {
			sec := convertNodeDepsToReportSection(nodeFile, nodeDeps)
			sections = append(sections, sec)
		} else if err != nil {
			log.Println("Error parsing Node deps:", err)
		}
	}

	// 3) Python => BFS
	pyFile := findFile(rootDir, "requirements.txt")
	if pyFile != "" {
		pyDeps, err := parsePythonDependencies(pyFile)
		if err == nil && len(pyDeps) > 0 {
			sec := convertPythonDepsToReportSection(pyFile, pyDeps)
			sections = append(sections, sec)
		} else if err != nil {
			log.Println("Error parsing Python deps:", err)
		}
	}

	// Close BFS channel, wait
	close(pomRequests)
	wgWorkers.Wait()

	// Flatten BFS => table for each file
	for i := range sections {
		flattenBFS(&sections[i])
	}

	// Render single HTML with BFS bullet-lists + table
	type finalData struct {
		Sections []ReportSection
	}
	fd := finalData{Sections: sections}

	f, err := os.Create(outputReportFinal)
	if err != nil {
		log.Fatalf("Cannot create final HTML: %v", err)
	}
	defer f.Close()

	tmpl, err := template.New("report").Parse(finalHTML)
	if err != nil {
		log.Fatalf("Error parsing template: %v", err)
	}
	if err := tmpl.Execute(f, fd); err != nil {
		log.Fatalf("Error executing template: %v", err)
	}

	fmt.Println("BFS + Table report generated:", outputReportFinal)
}
