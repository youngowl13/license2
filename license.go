package main

import (
	"encoding/json"
	"encoding/xml"
	"fmt"
	"html/template"
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
// 1) GLOBAL CONSTANTS & VARS
// ----------------------------------------------------------------------

const (
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
// 2) TYPES FOR DEPENDENCY TREES, BFS, & REPORT
// ----------------------------------------------------------------------

// DependencyNode is the BFS node for all file types.
type DependencyNode struct {
	Name       string
	Version    string
	License    string
	Copyleft   bool
	Parent     string            // "direct" or "group/artifact@version"
	Transitive []*DependencyNode // child dependencies
	UsedPOMURL string            // For Maven => POM link; for Node/Python => details link
	Direct     string            // BFS "root" name that introduced this node
}

// ExtendedDep for flattening, if needed
type ExtendedDep struct {
	Display      string
	Lookup       string
	Parent       string
	License      string
	IntroducedBy string
	PomURL       string
}

// ReportSection holds BFS & flattened table for one file.
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
	Flattened       []FlattenedDep
}

// FlattenedDep is a row in the color‐coded table.
type FlattenedDep struct {
	Dependency string
	Version    string
	Parent     string
	TopLevel   string
	License    string
	Copyleft   bool
	Details    string // e.g. Node/Python "Details" or Maven POM link
}

// For BFS concurrency
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

type introducerSet map[string]bool

// ----------------------------------------------------------------------
// 3) MAVEN STRUCTS & PARSING
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
		if err == nil && !info.IsDir() && strings.EqualFold(info.Name(), "pom.xml") {
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
// 4) TOML PARSING
// ----------------------------------------------------------------------

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

func parseTOMLFile(filePath string) (map[string]string, error) {
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
		return nil, fmt.Errorf("TOML file missing 'libraries' table")
	}
	libraries, ok := librariesTree.(*toml.Tree)
	if !ok {
		return nil, fmt.Errorf("'libraries' is not a valid TOML table")
	}
	deps := make(map[string]string)
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

// ----------------------------------------------------------------------
// 5) GRADLE PARSING
// ----------------------------------------------------------------------

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
// 6) BFS WORKER & UTILS
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
// 7) MAVEN BFS FOR MAVEN/TOML/GRADLE
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
		log.Printf("[BFS] Building BFS for %s", sec.FilePath)

		allDeps := make(map[string]ExtendedDep)
		for ga, ver := range sec.DirectDeps {
			key := ga + "@" + ver
			allDeps[key] = ExtendedDep{Display: ver, Lookup: ver, Parent: "direct"}
		}

		visited := make(map[string]introducerSet)
		var queue []queueItem
		var rootNodes []*DependencyNode

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

		// Mark introducedBy
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

		sec.CopyleftCount = 0
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
	for _, child := range node.Transitive {
		countCopyleftInTree(child, sec)
	}
}

// ----------------------------------------------------------------------
// 8) Node BFS & Python BFS => Full Transitive
// (Already integrated above in parseNodeDependencies, parsePythonDependencies)
// ----------------------------------------------------------------------

// ----------------------------------------------------------------------
// 9) FLATTEN BFS => TABLE
// ----------------------------------------------------------------------

func flattenBFS(sec *ReportSection) {
	var rows []FlattenedDep
	var walk func(node *DependencyNode)
	walk = func(node *DependencyNode) {
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
			walk(child)
		}
	}
	for _, root := range sec.DependencyTree {
		walk(root)
	}
	sec.Flattened = rows
}

// ----------------------------------------------------------------------
// 10) FINAL HTML TEMPLATE (TABLE FIRST, THEN COLLAPSIBLE BFS)
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
    /* Row-based coloring for copyleft or unknown */
    tr.copyleft { background-color: #ffe6e6; }
    tr.unknown { background-color: #ffffcc; }

    ul.tree { list-style-type: none; padding-left: 1em; }
    li.tree-item { margin-bottom: 0.5em; }

    /* Collapsible BFS logic */
    .toggle-btn { cursor: pointer; font-weight: bold; color: #007bff; margin-right: 5px; }
    .toggle-btn:hover { text-decoration: underline; }

    .hidden { display: none; }
  </style>
  <script>
  function toggleSubtree(btnId) {
    var ul = document.getElementById(btnId);
    if (!ul) return;
    if (ul.classList.contains('hidden')) {
      ul.classList.remove('hidden');
      // We can change the text or symbol if we want
    } else {
      ul.classList.add('hidden');
    }
  }
  </script>
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

<!-- 1) TABLE FIRST -->
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
  <tr {{if .Copyleft}}class="copyleft"{{else if eq .License "Unknown"}}class="unknown"{{end}}>
    <td>{{.Dependency}}</td>
    <td>{{.Version}}</td>
    <td>{{.Parent}}</td>
    <td>{{.TopLevel}}</td>
    <td>{{.License}}</td>
    <td>{{if .Details}}<a href="{{.Details}}" target="_blank">Link</a>{{end}}</td>
  </tr>
  {{end}}
</table>

<!-- 2) COLLAPSIBLE BFS TREE -->
<h3>Dependency Tree</h3>
<ul class="tree">
  {{range $i, $root := .DependencyTree}}
  <li class="tree-item">
    <!-- We give each sub-UL an ID so we can toggle it. -->
    <span class="toggle-btn" onclick="toggleSubtree('subtree-{{$.FilePath}}-{{$i}}')">[+/-]</span>
    <strong>{{$root.Name}}@{{$root.Version}}</strong>
    {{if eq $root.Parent "direct"}}(direct){{else}}(introduced by {{$root.Parent}}){{end}}
    <br/>
    License: <span {{if $root.Copyleft}}class="copyleft"{{else if eq $root.License "Unknown"}}class="unknown"{{end}}>{{$root.License}}</span>
    {{if $root.UsedPOMURL}} [<a href="{{$root.UsedPOMURL}}" target="_blank">Link</a>]{{end}}

    <ul class="hidden" id="subtree-{{$.FilePath}}-{{$i}}">
      {{template "subTree" $root.Transitive $.FilePath (print $i)}}
    </ul>
  </li>
  {{end}}
</ul>
<hr/>
{{end}}

{{define "subTree"}}
{{- $filePath := index . 1 -}}
{{- $parentIdx := index . 2 -}}
{{- $deps := index . 0 -}}
{{range $j, $child := $deps}}
<li class="tree-item">
  <span class="toggle-btn" onclick="toggleSubtree('subtree-{{$filePath}}-{{$parentIdx}}-{{$j}}')">[+/-]</span>
  <strong>{{$child.Name}}@{{$child.Version}}</strong>
  <br/>
  License: <span {{if $child.Copyleft}}class="copyleft"{{else if eq $child.License "Unknown"}}class="unknown"{{end}}>{{$child.License}}</span>
  {{if $child.UsedPOMURL}} [<a href="{{$child.UsedPOMURL}}" target="_blank">Link</a>]{{end}}

  {{if $child.Transitive}}
  <ul class="hidden" id="subtree-{{$filePath}}-{{$parentIdx}}-{{$j}}">
    {{template "subTree" $child.Transitive $filePath (print $parentIdx "-" $j)}}
  </ul>
  {{end}}
</li>
{{end}}
{{end}}

</body>
</html>
`

// ----------------------------------------------------------------------
// 11) MAIN
// ----------------------------------------------------------------------

func main() {
	// Start BFS workers for Maven
	for i := 0; i < pomWorkerCount; i++ {
		wgWorkers.Add(1)
		go pomFetchWorker()
	}

	rootDir := "."

	var sections []ReportSection

	// 1) Find & parse Maven POM files
	pomFiles, err := findAllPOMFiles(rootDir)
	if err != nil {
		log.Println("Error searching for pom.xml files:", err)
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

	// 2) Find & parse TOML files
	tomlFiles, err := findAllTOMLFiles(rootDir)
	if err != nil {
		log.Println("Error searching for .toml files:", err)
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

	// 3) Find & parse Gradle files
	gradleFiles, err := findAllGradleFiles(rootDir)
	if err != nil {
		log.Println("Error searching for Gradle files:", err)
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

	// 4) Node => parse full BFS
	nodeFile := findFile(rootDir, "package.json")
	if nodeFile != "" {
		nodeDeps, err := parseNodeDependencies(nodeFile)
		if err != nil {
			log.Println("Error parsing Node (package.json):", err)
		} else if len(nodeDeps) > 0 {
			direct := make(map[string]string)
			for _, nd := range nodeDeps {
				direct[nd.Name] = nd.Version
			}
			rs := ReportSection{
				FilePath:       nodeFile,
				DirectDeps:     direct,
				AllDeps:        make(map[string]ExtendedDep),
				DependencyTree: nodeDeps,
			}
			// Count direct vs. total
			rs.DirectCount = len(rs.DirectDeps)
			rs.TransitiveCount = countTotalDependencies(nodeDeps)
			rs.IndirectCount = rs.TransitiveCount - rs.DirectCount
			sections = append(sections, rs)
		}
	}

	// 5) Python => parse full BFS
	pyFile := findFile(rootDir, "requirements.txt")
	if pyFile != "" {
		pyDeps, err := parsePythonDependencies(pyFile)
		if err != nil {
			log.Println("Error parsing Python (requirements.txt):", err)
		} else if len(pyDeps) > 0 {
			direct := make(map[string]string)
			for _, nd := range pyDeps {
				direct[nd.Name] = nd.Version
			}
			rs := ReportSection{
				FilePath:       pyFile,
				DirectDeps:     direct,
				AllDeps:        make(map[string]ExtendedDep),
				DependencyTree: pyDeps,
			}
			rs.DirectCount = len(rs.DirectDeps)
			rs.TransitiveCount = countTotalDependencies(pyDeps)
			rs.IndirectCount = rs.TransitiveCount - rs.DirectCount
			sections = append(sections, rs)
		}
	}

	// Close BFS channel, wait
	close(pomRequests)
	wgWorkers.Wait()

	// Flatten BFS => table for each file
	for i := range sections {
		flattenBFS(&sections[i])
	}

	// Render single HTML
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

	fmt.Println("Dependency table (colored) + collapsible BFS report =>", outputReportFinal)
}

// countTotalDependencies recursively counts the total BFS nodes
func countTotalDependencies(nodes []*DependencyNode) int {
	count := 0
	var walk func([]*DependencyNode)
	walk = func(nl []*DependencyNode) {
		for _, n := range nl {
			count++
			walk(n.Transitive)
		}
	}
	walk(nodes)
	return count
}
