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
	"strings"
	"sync"
	"time"

	"github.com/pelletier/go-toml"
)

// ----------------------------------------------------------------------
// Global Constants & Variables
// ----------------------------------------------------------------------

const (
	localPOMCacheDir  = ".pom-cache"
	pomWorkerCount    = 10
	fetchTimeout      = 30 * time.Second
	outputReportFinal = "license_compliance_report.html"
)

var (
	pomRequests  = make(chan fetchRequest, 50)
	wgWorkers    sync.WaitGroup
	pomCache     sync.Map // key: "group:artifact:version" -> *MavenPOM
	channelOpen  = true
	channelMutex sync.Mutex
)

// ----------------------------------------------------------------------
// Type Definitions
// ----------------------------------------------------------------------

// DependencyNode is our common type representing a dependency in the BFS tree.
type DependencyNode struct {
	Name       string
	Version    string
	License    string
	Copyleft   bool
	Parent     string            // "direct" or parent's coordinate (e.g. "group/artifact@version")
	Transitive []*DependencyNode // child dependencies
	UsedPOMURL string            // For Maven: POM URL; for Node/Python: Details link
	Direct     string            // Top-level dependency that introduced this node
}

// ExtendedDep is used for flattened information.
type ExtendedDep struct {
	Display      string
	Lookup       string
	Parent       string
	License      string
	IntroducedBy string
	PomURL       string
}

// ReportSection holds the BFS tree and flattened table rows for one file.
type ReportSection struct {
	FilePath        string
	DirectDeps      map[string]string // e.g. "com.google.guava/guava" -> "31.1-jre"
	AllDeps         map[string]ExtendedDep
	DependencyTree  []*DependencyNode

	TransitiveCount int
	DirectCount     int
	IndirectCount   int
	CopyleftCount   int
	UnknownCount    int

	Flattened []FlattenedDep // Flattened table rows
}

// FlattenedDep represents one row in the final table.
type FlattenedDep struct {
	Dependency string
	Version    string
	Parent     string
	TopLevel   string
	License    string
	Copyleft   bool
	Details    string // Link (Maven POM or Node/Python details)
}

// BFS types for Maven fetching.
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

// introducerSet is used in BFS bookkeeping.
type introducerSet map[string]bool

// ----------------------------------------------------------------------
// Maven XML Structures & Parsing
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
	XMLName        xml.Name     `xml:"project"`
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

// ----------------------------------------------------------------------
// TOML Parsing Functions
// ----------------------------------------------------------------------

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

// ----------------------------------------------------------------------
// Gradle Parsing Functions
// ----------------------------------------------------------------------

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
// Utility Functions: skipScope, splitGA, removeCaretTilde, detectLicense, isCopyleftChecker
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
	ver = strings.TrimSpace(ver)
	return strings.TrimLeft(ver, "^~")
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

// ----------------------------------------------------------------------
// Node & Python Parsing (Using common DependencyNode)
// ----------------------------------------------------------------------

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
		return nil, fmt.Errorf("info missing in PyPI data for %s", pkgName)
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
		Details:    "https://pypi.org/project/" + pkgName,
		Copyleft:   isCopyleftChecker(license),
		Transitive: trans,
		Language:   "python",
	}
	return nd, nil
}

// ----------------------------------------------------------------------
// Flattening Function: Flatten BFS Tree into Table Rows
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
		Details:    node.UsedPOMURL,
	}
	rows = append(rows, row)
	for _, child := range node.Transitive {
		rows = flattenOneTree(child, rows)
	}
	return rows
}

// ----------------------------------------------------------------------
// Final HTML Template (BFS Bullet-List + Table for Each File)
// ----------------------------------------------------------------------

var finalHTML = `
<!DOCTYPE html>
<html>
<head>
  <meta charset="utf-8">
  <title>Combined Dependency Report</title>
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
<h1>Combined Dependency Report</h1>
{{range .Sections}}
  <h2>{{.FilePath}}</h2>
  <p>
    Direct Dependencies: {{.DirectCount}}<br/>
    Transitive (incl. direct): {{.TransitiveCount}}<br/>
    Indirect: {{.IndirectCount}}<br/>
    Copyleft: {{.CopyleftCount}}<br/>
    Unknown: {{.UnknownCount}}
  </p>
  <h3>BFS Tree</h3>
  <ul>
    {{range .DependencyTree}}
      <li>
        <strong>{{.Name}}@{{.Version}}</strong> {{if eq .Parent "direct"}}(direct){{else}}(introduced by {{.Parent}}){{end}}<br/>
        License: <span {{if .Copyleft}}class="copyleft"{{else if eq .License "Unknown"}}class="unknown"{{end}}>{{.License}}</span>
        {{if .UsedPOMURL}} [<a href="{{.UsedPOMURL}}" target="_blank">Link</a>]{{end}}
        {{template "bfsList" .Transitive}}
      </li>
    {{end}}
  </ul>
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
        <td>{{if .Details}}<a href="{{.Details}}" target="_blank">Link</a>{{end}}</td>
      </tr>
    {{end}}
  </table>
  <hr/>
{{end}}
{{define "bfsList"}}
  <ul>
    {{range .}}
      <li>
        <strong>{{.Name}}@{{.Version}}</strong><br/>
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
// updateReportSection: updates counts and AllDeps from the DependencyTree
// ----------------------------------------------------------------------

func updateReportSection(rs *ReportSection) {
	rs.AllDeps = make(map[string]ExtendedDep)
	var traverse func(node *DependencyNode)
	traverse = func(node *DependencyNode) {
		key := node.Name + "@" + node.Version
		if _, exists := rs.AllDeps[key]; !exists {
			rs.AllDeps[key] = ExtendedDep{
				Display: node.Version,
				Lookup:  node.Version,
				Parent:  node.Parent,
				License: node.License,
				PomURL:  node.UsedPOMURL,
			}
		}
		for _, child := range node.Transitive {
			traverse(child)
		}
	}
	for _, root := range rs.DependencyTree {
		traverse(root)
	}
	rs.DirectCount = len(rs.DirectDeps)
	rs.TransitiveCount = len(rs.AllDeps)
	rs.IndirectCount = rs.TransitiveCount - rs.DirectCount

	var cCount, uCount int
	var countTraverse func(node *DependencyNode)
	countTraverse = func(node *DependencyNode) {
		if node.Copyleft {
			cCount++
		}
		if node.Version == "unknown" {
			uCount++
		}
		for _, child := range node.Transitive {
			countTraverse(child)
		}
	}
	for _, root := range rs.DependencyTree {
		countTraverse(root)
	}
	rs.CopyleftCount = cCount
	rs.UnknownCount = uCount
}

// ----------------------------------------------------------------------
// Main Function
// ----------------------------------------------------------------------

func main() {
	// Start Maven BFS workers
	for i := 0; i < pomWorkerCount; i++ {
		wgWorkers.Add(1)
		go pomFetchWorker()
	}

	rootDir := "."

	var sections []ReportSection

	// Maven Files
	pomFiles, _ := findAllPOMFiles(rootDir)
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

	// TOML Files
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

	// Gradle Files
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

	// BFS for Maven/TOML/Gradle
	buildTransitiveClosureJavaLike(sections)

	// Node Dependencies
	nodeFile := findFile(rootDir, "package.json")
	if nodeFile != "" {
		nodeDeps, err := parseNodeDependencies(nodeFile)
		if err == nil && len(nodeDeps) > 0 {
			directDeps := make(map[string]string)
			for _, d := range nodeDeps {
				directDeps[d.Name] = d.Version
			}
			rs := ReportSection{
				FilePath:       nodeFile,
				DirectDeps:     directDeps,
				AllDeps:        make(map[string]ExtendedDep),
				DependencyTree: nodeDeps,
			}
			updateReportSection(&rs)
			sections = append(sections, rs)
		} else if err != nil {
			log.Println("Error parsing Node dependencies:", err)
		}
	}

	// Python Dependencies
	pyFile := findFile(rootDir, "requirements.txt")
	if pyFile != "" {
		pyDeps, err := parsePythonDependencies(pyFile)
		if err == nil && len(pyDeps) > 0 {
			directDeps := make(map[string]string)
			for _, d := range pyDeps {
				directDeps[d.Name] = d.Version
			}
			rs := ReportSection{
				FilePath:       pyFile,
				DirectDeps:     directDeps,
				AllDeps:        make(map[string]ExtendedDep),
				DependencyTree: pyDeps,
			}
			updateReportSection(&rs)
			sections = append(sections, rs)
		} else if err != nil {
			log.Println("Error parsing Python dependencies:", err)
		}
	}

	close(pomRequests)
	wgWorkers.Wait()

	// Flatten BFS trees to table rows for each section
	for i := range sections {
		flattenBFS(&sections[i])
	}

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

	fmt.Println("Combined BFS and Table dependency report generated at:", outputReportFinal)
}
