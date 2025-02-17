package main

import (
	"bytes"
	"encoding/xml"
	"errors"
	"fmt"
	"html/template"
	"io"
	"io/ioutil"
	"net/http"
	"os"
	"path/filepath"
	"regexp"
	"sort"
	"strings"
	"sync"
)

// -------------------------------------------------------------------------------------
// DATA STRUCTURES
// -------------------------------------------------------------------------------------

// GradleDependencyNode: hierarchical node for the tree view.
type GradleDependencyNode struct {
	Name       string
	Version    string
	License    string
	Copyleft   bool
	Parent     string // "direct" or "group:artifact:version"
	Transitive []*GradleDependencyNode
}

// ExtendedDepInfo: for the flat table of dependencies.
type ExtendedDepInfo struct {
	Display string // version
	Lookup  string // version for resolution
	Parent  string // "direct" or "group:artifact:version"
}

// GradleReportSection: one per build.gradle
type GradleReportSection struct {
	FilePath        string
	Dependencies    map[string]ExtendedDepInfo
	DependencyTree  []*GradleDependencyNode
	TransitiveCount int
}

// MavenPOM: minimal parse of a <project> POM.
type MavenPOM struct {
	XMLName        xml.Name    `xml:"project"`
	Parent         POMParent   `xml:"parent"`
	DependencyMgmt struct {
		Dependencies []POMDep `xml:"dependencies>dependency"`
	} `xml:"dependencyManagement"`
	Dependencies []POMDep `xml:"dependencies>dependency"`
	Licenses     []struct {
		Name string `xml:"name"`
	} `xml:"licenses>license"`

	GroupID    string `xml:"groupId"`
	ArtifactID string `xml:"artifactId"`
	Version    string `xml:"version"`
}

// POMParent: for <parent> info
type POMParent struct {
	GroupID    string `xml:"groupId"`
	ArtifactID string `xml:"artifactId"`
	Version    string `xml:"version"`
}

// POMDep: a single <dependency> entry
type POMDep struct {
	GroupID    string `xml:"groupId"`
	ArtifactID string `xml:"artifactId"`
	Version    string `xml:"version"`
	Scope      string `xml:"scope"`
	Optional   string `xml:"optional"`
}

// For BFS conflict resolution:
type depState struct {
	Version string
	Depth   int
}

// queueItem for BFS plus pointer to the parent node in the tree.
type queueItem struct {
	GroupArtifact string
	Version       string
	Depth         int
	ParentNode    *GradleDependencyNode
}

// For concurrency, we’ll maintain a channel of fetch requests:
type fetchRequest struct {
	GroupID    string
	ArtifactID string
	Version    string
	ResultChan chan fetchResult
}

// fetchResult: includes the POM or an error
type fetchResult struct {
	POM *MavenPOM
	Err error
}

// -------------------------------------------------------------------------------------
// GLOBAL VARS & CONCURRENCY
// -------------------------------------------------------------------------------------

// We store a concurrency-limited worker pool to fetch POMs in parallel
var (
	pomWorkerCount = 10 // tune as needed
	pomRequests    = make(chan fetchRequest, 50) // buffer of requests
	wgWorkers      sync.WaitGroup
)

// local disk cache folder
const localPOMCacheDir = ".pom-cache"

// spdxLicenseMap is a small sample of possible SPDX IDs -> type
// For real usage, expand this or use a library
var spdxLicenseMap = map[string]struct {
	Name     string
	Copyleft bool
}{
	"Apache-2.0": {Name: "Apache License 2.0", Copyleft: false},
	"MIT":        {Name: "MIT License", Copyleft: false},
	"BSD-2-Clause": {Name: "BSD 2-Clause", Copyleft: false},
	"BSD-3-Clause": {Name: "BSD 3-Clause", Copyleft: false},
	"MPL-2.0":    {Name: "Mozilla Public License 2.0", Copyleft: true},
	"LGPL-2.1":   {Name: "GNU Lesser General Public License v2.1", Copyleft: true},
	"LGPL-3.0":   {Name: "GNU Lesser General Public License v3.0", Copyleft: true},
	"GPL-2.0":    {Name: "GNU General Public License v2.0", Copyleft: true},
	"GPL-3.0":    {Name: "GNU General Public License v3.0", Copyleft: true},
	"AGPL-3.0":   {Name: "GNU Affero General Public License v3.0", Copyleft: true},
}

// We'll also keep a global memory cache to avoid re-parsing the same POM
var pomCache sync.Map // key = "group:artifact:version" => *MavenPOM

// We'll also store visited parent references to avoid infinite loops
var parentVisit sync.Map // key = "group:artifact:version" => bool

// -------------------------------------------------------------------------------------
// MAIN WORKER POOL INIT
// -------------------------------------------------------------------------------------

func init() {
	// Create local POM cache dir
	if err := os.MkdirAll(localPOMCacheDir, 0755); err != nil {
		fmt.Printf("Warning: Could not create local POM cache dir: %v\n", err)
	}

	// Start POM fetch workers
	wgWorkers.Add(pomWorkerCount)
	for i := 0; i < pomWorkerCount; i++ {
		go pomFetchWorker()
	}
}

func pomFetchWorker() {
	defer wgWorkers.Done()
	for req := range pomRequests {
		// handle request
		pom, err := retrieveOrLoadPOM(req.GroupID, req.ArtifactID, req.Version)
		req.ResultChan <- fetchResult{POM: pom, Err: err}
	}
}

// -------------------------------------------------------------------------------------
// STEP 1: FIND BUILD.GRADLE & PARSE DIRECT DEPS
// -------------------------------------------------------------------------------------

func findBuildGradleFiles(root string) ([]string, error) {
	var files []string
	err := filepath.Walk(root, func(path string, info os.FileInfo, err error) error {
		if err != nil {
			return err
		}
		if !info.IsDir() && strings.EqualFold(info.Name(), "build.gradle") {
			files = append(files, path)
		}
		return nil
	})
	return files, err
}

func parseVariables(content string) map[string]string {
	varMap := make(map[string]string)
	re := regexp.MustCompile(`(?m)^\s*def\s+(\w+)\s*=\s*["']([^"']+)["']`)
	all := re.FindAllStringSubmatch(content, -1)
	for _, match := range all {
		varMap[match[1]] = match[2]
	}
	return varMap
}

func parseBuildGradleFile(filePath string) (map[string]ExtendedDepInfo, error) {
	data, err := ioutil.ReadFile(filePath)
	if err != nil {
		return nil, err
	}
	content := string(data)
	varMap := parseVariables(content)
	deps := make(map[string]ExtendedDepInfo)

	re := regexp.MustCompile(`(?m)^\s*(implementation|api|compileOnly|runtimeOnly|testImplementation|androidTestImplementation|classpath)\s+['"]([^'"]+)['"]`)
	all := re.FindAllStringSubmatch(content, -1)
	for _, match := range all {
		depStr := match[2]
		parts := strings.Split(depStr, ":")
		if len(parts) < 2 {
			continue
		}
		group := parts[0]
		artifact := parts[1]
		version := "unknown"
		if len(parts) >= 3 {
			version = parts[2]
			// handle version ranges: just pick the lower bound if any
			version = parseVersionRange(version)
			// handle var interpolation
			if strings.Contains(version, "${") {
				reVar := regexp.MustCompile(`\$\{([^}]+)\}`)
				version = reVar.ReplaceAllStringFunc(version, func(s string) string {
					inner := s[2 : len(s)-1]
					if val, ok := varMap[inner]; ok {
						return val
					}
					return ""
				})
			}
		}
		key := group + "/" + artifact
		if _, ok := deps[key]; !ok {
			deps[key] = ExtendedDepInfo{
				Display: version,
				Lookup:  version,
				Parent:  "direct",
			}
		}
	}
	return deps, nil
}

func parseAllBuildGradleFiles(files []string) ([]GradleReportSection, error) {
	var sections []GradleReportSection
	for _, f := range files {
		directDeps, err := parseBuildGradleFile(f)
		if err != nil {
			fmt.Printf("Error parsing %s: %v\n", f, err)
			continue
		}
		sections = append(sections, GradleReportSection{
			FilePath:     f,
			Dependencies: directDeps,
		})
	}
	return sections, nil
}

// parseVersionRange: if the version looks like [1.2,2.0) or (,1.5], return the lower bound
func parseVersionRange(version string) string {
	version = strings.TrimSpace(version)
	if (strings.HasPrefix(version, "[") || strings.HasPrefix(version, "(")) &&
		strings.Contains(version, ",") {
		// e.g. [1.2,2.0) => pick "1.2"
		trimmed := strings.Trim(version, "[]() ")
		parts := strings.Split(trimmed, ",")
		if len(parts) > 0 {
			low := strings.TrimSpace(parts[0])
			if low == "" {
				// e.g. (,1.5], pick "1.5"? Actually let's treat empty as "0.0"
				low = "0.0"
			}
			return low
		}
	}
	return version
}

// -------------------------------------------------------------------------------------
// STEP 2: BFS + MULTI-LEVEL PARENT, CONCURRENT FETCH
// -------------------------------------------------------------------------------------

func buildTransitiveClosure(sections []GradleReportSection) {
	for i := range sections {
		sec := &sections[i]
		stateMap := make(map[string]depState)
		nodeMap := make(map[string]*GradleDependencyNode)
		var rootNodes []*GradleDependencyNode
		var queue []queueItem

		// Initialize BFS with direct deps
		for ga, info := range sec.Dependencies {
			node := &GradleDependencyNode{
				Name:   ga,
				Version: info.Lookup,
				Parent: "direct",
			}
			rootNodes = append(rootNodes, node)
			nodeMap[ga] = node
			stateMap[ga] = depState{Version: info.Lookup, Depth: 1}
			queue = append(queue, queueItem{
				GroupArtifact: ga,
				Version:       info.Lookup,
				Depth:         1,
				ParentNode:    node,
			})
		}

		// BFS
		for len(queue) > 0 {
			it := queue[0]
			queue = queue[1:]

			gid, aid := splitGA(it.GroupArtifact)
			if gid == "" || aid == "" {
				continue
			}
			// fetch concurrent
			pom, err := concurrentFetchPOM(gid, aid, it.Version)
			if err != nil || pom == nil {
				continue
			}

			// attach license to current node
			curNode := it.ParentNode
			if curNode != nil {
				licName := detectLicense(pom)
				curNode.License = licName
				curNode.Copyleft = isCopyleft(licName)
			}

			// parse <dependencyManagement>
			managed := parseManagedVersions(pom)
			// for each child
			for _, cd := range pom.Dependencies {
				if skipScope(cd.Scope, cd.Optional) {
					continue
				}
				childGA := cd.GroupID + "/" + cd.ArtifactID
				cv := parseVersionRange(strings.TrimSpace(cd.Version))
				if cv == "" {
					if mv, ok := managed[childGA]; ok && mv != "" {
						cv = mv
					} else {
						cv = fallbackVersionRange(pom, cd.GroupID, cd.ArtifactID)
					}
				}
				if cv == "" {
					continue
				}
				childDepth := it.Depth + 1
				curSt, seen := stateMap[childGA]
				if !seen {
					// new
					stateMap[childGA] = depState{Version: cv, Depth: childDepth}
					childNode := &GradleDependencyNode{
						Name:    childGA,
						Version: cv,
						Parent:  fmt.Sprintf("%s:%s", it.GroupArtifact, it.Version),
					}
					nodeMap[childGA] = childNode
					if it.ParentNode != nil {
						it.ParentNode.Transitive = append(it.ParentNode.Transitive, childNode)
					}
					queue = append(queue, queueItem{
						GroupArtifact: childGA,
						Version:       cv,
						Depth:         childDepth,
						ParentNode:    childNode,
					})
				} else {
					// conflict check
					if childDepth < curSt.Depth {
						stateMap[childGA] = depState{Version: cv, Depth: childDepth}
						childNode, ok := nodeMap[childGA]
						if !ok {
							childNode = &GradleDependencyNode{
								Name:    childGA,
								Version: cv,
								Parent:  fmt.Sprintf("%s:%s", it.GroupArtifact, it.Version),
							}
							nodeMap[childGA] = childNode
						} else {
							childNode.Version = cv
							childNode.Parent  = fmt.Sprintf("%s:%s", it.GroupArtifact, it.Version)
						}
						if it.ParentNode != nil {
							it.ParentNode.Transitive = append(it.ParentNode.Transitive, childNode)
						}
						queue = append(queue, queueItem{
							GroupArtifact: childGA,
							Version:       cv,
							Depth:         childDepth,
							ParentNode:    childNode,
						})
					}
				}
			}
		}

		sortRoots(rootNodes)
		sec.DependencyTree = rootNodes
		total := 0
		for _, r := range rootNodes {
			total += countNodes(r)
		}
		direct := len(rootNodes)
		sec.TransitiveCount = total - direct

		// fill final versions in Dependencies
		for _, r := range rootNodes {
			fillDepMap(r, sec.Dependencies)
		}
	}
}

// parseManagedVersions merges parent's <dependencyManagement> entries
func parseManagedVersions(pom *MavenPOM) map[string]string {
	res := make(map[string]string)
	for _, d := range pom.DependencyMgmt.Dependencies {
		if skipScope(d.Scope, d.Optional) {
			continue
		}
		if d.Version != "" {
			key := d.GroupID + "/" + d.ArtifactID
			res[key] = parseVersionRange(d.Version)
		}
	}
	return res
}

// skipScope returns true if test/provided/system or optional
func skipScope(scope, optional string) bool {
	s := strings.ToLower(strings.TrimSpace(scope))
	if s == "test" || s == "provided" || s == "system" {
		return true
	}
	if strings.ToLower(strings.TrimSpace(optional)) == "true" {
		return true
	}
	return false
}

func fallbackVersionRange(pom *MavenPOM, g, a string) string {
	// if child groupId == pom.GroupID => use pom.Version
	if g == pom.GroupID && pom.Version != "" {
		return parseVersionRange(pom.Version)
	}
	// or if g == parent's groupID => parent's version
	if g == pom.Parent.GroupID && pom.Parent.Version != "" {
		return parseVersionRange(pom.Parent.Version)
	}
	return ""
}

func sortRoots(roots []*GradleDependencyNode) {
	sort.Slice(roots, func(i, j int) bool {
		return roots[i].Name < roots[j].Name
	})
	for _, r := range roots {
		sortRoots(r.Transitive)
	}
}

func countNodes(n *GradleDependencyNode) int {
	cnt := 1
	for _, c := range n.Transitive {
		cnt += countNodes(c)
	}
	return cnt
}

func fillDepMap(n *GradleDependencyNode, deps map[string]ExtendedDepInfo) {
	key := n.Name
	info, ok := deps[key]
	if !ok {
		info = ExtendedDepInfo{Display: n.Version, Lookup: n.Version, Parent: n.Parent}
	} else {
		info.Display = n.Version
		info.Lookup  = n.Version
		info.Parent  = n.Parent
	}
	deps[key] = info
	for _, c := range n.Transitive {
		fillDepMap(c, deps)
	}
}

// -------------------------------------------------------------------------------------
// STEP 3: LICENSE DETECTION (Multi-level approach with SPDX and fallback keyword matching)
// -------------------------------------------------------------------------------------

func detectLicense(pom *MavenPOM) string {
	if len(pom.Licenses) == 0 {
		return "Unknown"
	}
	licText := pom.Licenses[0].Name
	licText = strings.TrimSpace(licText)
	if licText == "" {
		return "Unknown"
	}
	// check if it is an SPDX ID (like "Apache-2.0", "MIT", etc.)
	up := strings.ToUpper(licText)
	for spdxID, data := range spdxLicenseMap {
		if strings.EqualFold(licText, spdxID) {
			return data.Name // e.g. "Apache License 2.0"
		}
		if strings.EqualFold(up, spdxID) { // case-insensitive
			return data.Name
		}
	}
	// fallback to the raw name, might still match keyword-based approach in isCopyleft
	return licText
}

func isCopyleft(name string) bool {
	// first see if name exactly matches an spdx that is known copyleft
	for spdxID, data := range spdxLicenseMap {
		if data.Copyleft && (strings.EqualFold(name, data.Name) || strings.EqualFold(name, spdxID)) {
			return true
		}
	}
	// fallback: search for typical copyleft keywords
	copyleftKeywords := []string{
		"GPL", "LGPL", "AGPL", "CC BY-SA", "CC-BY-SA", "MPL", "EPL", "CPL",
		"CDDL", "EUPL", "Affero", "OSL", "CeCILL",
		"GNU General Public License",
		"GNU Lesser General Public License",
		"Mozilla Public License",
		"Common Development and Distribution License",
		"Eclipse Public License",
		"Common Public License",
		"European Union Public License",
		"Open Software License",
	}
	up := strings.ToUpper(name)
	for _, kw := range copyleftKeywords {
		if strings.Contains(up, strings.ToUpper(kw)) {
			return true
		}
	}
	return false
}

// -------------------------------------------------------------------------------------
// STEP 4: CONCURRENT POM FETCH + MULTI-LEVEL PARENT RECURSION
// -------------------------------------------------------------------------------------

// concurrentFetchPOM requests a POM from the worker pool
func concurrentFetchPOM(g, a, v string) (*MavenPOM, error) {
	// Check the in-memory map first
	key := fmt.Sprintf("%s:%s:%s", g, a, v)
	if cached, ok := pomCache.Load(key); ok {
		return cached.(*MavenPOM), nil
	}
	resultChan := make(chan fetchResult, 1)
	req := fetchRequest{
		GroupID:    g,
		ArtifactID: a,
		Version:    v,
		ResultChan: resultChan,
	}
	pomRequests <- req // send to worker
	res := <-resultChan
	if res.Err == nil && res.POM != nil {
		pomCache.Store(key, res.POM)
	}
	return res.POM, res.Err
}

// retrieveOrLoadPOM checks the disk cache, if not found fetch from Maven Central/Google, parse, then do multi-level parent
func retrieveOrLoadPOM(g, a, v string) (*MavenPOM, error) {
	if g == "" || a == "" || v == "" {
		return nil, errors.New("invalid group/artifact/version")
	}
	key := fmt.Sprintf("%s:%s:%s", g, a, v)
	if c, ok := pomCache.Load(key); ok {
		return c.(*MavenPOM), nil
	}

	// check local disk cache
	pom, err := loadPOMFromDisk(g, a, v)
	if err == nil && pom != nil {
		pomCache.Store(key, pom)
	} else {
		// fetch from remote
		pom, err = fetchPOMRemote(g, a, v)
		if err != nil {
			return nil, err
		}
		if err := savePOMToDisk(g, a, v, pom); err != nil {
			fmt.Printf("Warning: cannot save POM to disk: %v\n", err)
		}
		pomCache.Store(key, pom)
	}

	// Now multi-level parent recursion
	if pom != nil {
		if pom.GroupID == "" {
			pom.GroupID = pom.Parent.GroupID
		}
		if pom.Version == "" {
			pom.Version = pom.Parent.Version
		}
		err := loadAllParents(pom, 0) // up to some max depth
		if err != nil {
			// not necessarily fatal
			fmt.Printf("Warning: parent recursion error for %s:%s:%s => %v\n", g, a, v, err)
		}
	}

	return pom, nil
}

// loadAllParents recursively merges parents up the chain
func loadAllParents(pom *MavenPOM, depth int) error {
	if depth > 10 {
		return errors.New("max parent depth reached (possible cycle)")
	}
	if pom.Parent.GroupID == "" || pom.Parent.ArtifactID == "" || pom.Parent.Version == "" {
		return nil
	}
	parentKey := fmt.Sprintf("%s:%s:%s", pom.Parent.GroupID, pom.Parent.ArtifactID, pom.Parent.Version)
	if _, visited := parentVisit.Load(parentKey); visited {
		return errors.New("parent cycle detected")
	}
	parentVisit.Store(parentKey, true)

	parentPOM, err := retrieveOrLoadPOM(pom.Parent.GroupID, pom.Parent.ArtifactID, pom.Parent.Version)
	if err != nil {
		return err
	}
	if parentPOM != nil {
		// merge dependencyManagement
		pom.DependencyMgmt.Dependencies = mergeDepMgmt(parentPOM.DependencyMgmt.Dependencies, pom.DependencyMgmt.Dependencies)
		if pom.GroupID == "" {
			pom.GroupID = parentPOM.GroupID
		}
		if pom.Version == "" {
			pom.Version = parentPOM.Version
		}
		// Recurse
		return loadAllParents(parentPOM, depth+1)
	}
	return nil
}

// fetchPOMRemote tries Maven Central then Google
func fetchPOMRemote(g, a, v string) (*MavenPOM, error) {
	groupPath := strings.ReplaceAll(g, ".", "/")
	urlCentral := fmt.Sprintf("https://repo1.maven.org/maven2/%s/%s/%s/%s-%s.pom", groupPath, a, v, a, v)
	urlGoogle := fmt.Sprintf("https://dl.google.com/dl/android/maven2/%s/%s/%s/%s-%s.pom", groupPath, a, v, a, v)

	if pm, err := fetchPOMFromURL(urlCentral); err == nil {
		return pm, nil
	}
	if pm, err := fetchPOMFromURL(urlGoogle); err == nil {
		return pm, nil
	}
	return nil, fmt.Errorf("could not fetch POM for %s:%s:%s", g, a, v)
}

// -------------------------------------------------------------------------------------
// DISK CACHING
// -------------------------------------------------------------------------------------

func loadPOMFromDisk(g, a, v string) (*MavenPOM, error) {
	path := localCachePath(g, a, v)
	data, err := ioutil.ReadFile(path)
	if err != nil {
		return nil, err
	}
	var pom MavenPOM
	dec := xml.NewDecoder(bytes.NewReader(data))
	dec.Strict = false
	if err := dec.Decode(&pom); err != nil {
		return nil, err
	}
	return &pom, nil
}

func savePOMToDisk(g, a, v string, pom *MavenPOM) error {
	path := localCachePath(g, a, v)
	os.MkdirAll(filepath.Dir(path), 0755)
	out, err := os.Create(path)
	if err != nil {
		return err
	}
	defer out.Close()

	data, err := xml.MarshalIndent(pom, "", "  ")
	if err != nil {
		return err
	}
	_, err = out.Write(data)
	return err
}

func localCachePath(g, a, v string) string {
	// e.g. .pom-cache/com.google.guava/guava/30.1/guava-30.1.pom.xml
	groupPath := strings.ReplaceAll(g, ".", "/")
	return filepath.Join(localPOMCacheDir, groupPath, a, v, fmt.Sprintf("%s-%s.pom.xml", a, v))
}

// -------------------------------------------------------------------------------------
// STEP 5: TREE & TABLE HTML REPORT
// -------------------------------------------------------------------------------------

// buildGradleTreeHTML: no links inside the tree, only color-coded license
func buildGradleTreeHTML(node *GradleDependencyNode, level int) string {
	class := "non-copyleft"
	if node.License == "Unknown" {
		class = "unknown-license"
	} else if node.Copyleft {
		class = "copyleft"
	}
	summary := fmt.Sprintf("%s@%s (License: %s)", node.Name, node.Version, node.License)
	var sb strings.Builder
	sb.WriteString(fmt.Sprintf(`<details class="%s" style="margin-left:%dem;">`, class, level))
	sb.WriteString(fmt.Sprintf(`<summary>%s</summary>`, template.HTMLEscapeString(summary)))
	for _, c := range node.Transitive {
		sb.WriteString(buildGradleTreeHTML(c, level+1))
	}
	sb.WriteString(`</details>`)
	return sb.String()
}

func buildGradleTreesHTML(nodes []*GradleDependencyNode) template.HTML {
	var buf strings.Builder
	for _, n := range nodes {
		buf.WriteString(buildGradleTreeHTML(n, 0))
	}
	return template.HTML(buf.String())
}

// For table, we still do license info wrapper
type LicenseData struct {
	LicenseName string
	ProjectURL  string
	PomURL      string
}

func getLicenseInfoWrapper(dep, version string) LicenseData {
	parts := strings.Split(dep, "/")
	if len(parts) != 2 {
		return LicenseData{LicenseName: "Unknown"}
	}
	g, a := parts[0], parts[1]
	// We'll do a quick fetch (cached) for final license name
	pom, err := concurrentFetchPOM(g, a, version)
	if err != nil || pom == nil {
		return LicenseData{
			LicenseName: "Unknown",
			ProjectURL:  fmt.Sprintf("https://www.google.com/search?q=%s+%s+%s+license", g, a, version),
		}
	}
	licName := detectLicense(pom)
	groupPath := strings.ReplaceAll(g, ".", "/")
	pomURL := fmt.Sprintf("https://repo1.maven.org/maven2/%s/%s/%s/%s-%s.pom", groupPath, a, version, a, version)
	projectURL := fmt.Sprintf("https://repo1.maven.org/maven2/%s/%s/%s/", groupPath, a, version)
	return LicenseData{
		LicenseName: licName,
		ProjectURL:  projectURL,
		PomURL:      pomURL,
	}
}

func generateHTMLReport(sections []GradleReportSection) error {
	outputDir := "./license-checker"
	if err := os.MkdirAll(outputDir, 0755); err != nil {
		return err
	}

	const tmplText = `<!DOCTYPE html>
<html>
<head>
  <meta charset="UTF-8">
  <title>Gradle Dependency License Report</title>
  <style>
    body { font-family: Arial, sans-serif; margin: 20px; }
    h1 { color: #2c3e50; }
    h2 { margin-top: 40px; }
    table { width: 100%; border-collapse: collapse; margin-bottom: 40px; }
    th, td { border: 1px solid #ddd; padding: 8px; text-align: left; }
    th { background-color: #f2f2f2; }
    tr:nth-child(even) { background-color: #f9f9f9; }
    a { color: #3498db; text-decoration: none; }
    a:hover { text-decoration: underline; }
    tr.copyleft { background-color: #ffdddd; }
    tr.non-copyleft { background-color: #ddffdd; }
    tr.unknown-license { background-color: #ffffdd; }

    details.copyleft > summary {
      background-color: #ffdddd;
      padding: 2px 4px;
      border-radius: 4px;
    }
    details.unknown-license > summary {
      background-color: #ffffdd;
      padding: 2px 4px;
      border-radius: 4px;
    }
    details.non-copyleft > summary {
      background-color: #ddffdd;
      padding: 2px 4px;
      border-radius: 4px;
    }
  </style>
</head>
<body>
  <h1>Gradle Dependency License Report</h1>

  <p>This report uses concurrency, multi-level parent POM inheritance, a disk-based POM cache, 
  and simple version-range parsing ("nearest-wins"). 
  Real Gradle logic is more advanced. 
  Licenses are identified via a small SPDX map + keyword fallback.</p>

  {{ range . }}
    <h2>File: {{ .FilePath }}</h2>
    <p>Total Dependencies Found: {{ len .Dependencies }} ({{ .TransitiveCount }} transitive)</p>

    <h3>Dependencies Table</h3>
    <table>
      <thead>
        <tr>
          <th>Dependency</th>
          <th>Version</th>
          <th>License</th>
          <th>Parent</th>
          <th>Project Details</th>
          <th>POM File</th>
        </tr>
      </thead>
      <tbody>
        {{ range $dep, $info := .Dependencies }}
          {{ $licData := getLicenseInfoWrapper $dep $info.Lookup }}
          {{ if eq $licData.LicenseName "Unknown" }}
            <tr class="unknown-license">
          {{ else if isCopyleft $licData.LicenseName }}
            <tr class="copyleft">
          {{ else }}
            <tr class="non-copyleft">
          {{ end }}
            <td>{{ $dep }}</td>
            <td>{{ $info.Display }}</td>
            <td>{{ $licData.LicenseName }}</td>
            <td>{{ $info.Parent }}</td>
            {{ if $licData.ProjectURL }}
              <td><a href="{{ $licData.ProjectURL }}" target="_blank">View Details</a></td>
            {{ else }}
              <td></td>
            {{ end }}
            {{ if $licData.PomURL }}
              <td><a href="{{ $licData.PomURL }}" target="_blank">View POM</a></td>
            {{ else }}
              <td></td>
            {{ end }}
          </tr>
        {{ end }}
      </tbody>
    </table>

    <h3>Dependency Tree</h3>
    {{ buildGradleTreesHTML .DependencyTree }}
  {{ end }}
</body>
</html>
`

	tmpl, err := template.New("report").Funcs(template.FuncMap{
		"buildGradleTreesHTML": buildGradleTreesHTML,
		"getLicenseInfoWrapper": getLicenseInfoWrapper,
		"isCopyleft":            isCopyleft,
	}).Parse(tmplText)
	if err != nil {
		return err
	}

	outFile := filepath.Join(outputDir, "dependency-license-report.html")
	f, err := os.Create(outFile)
	if err != nil {
		return err
	}
	defer f.Close()

	if err := tmpl.Execute(f, sections); err != nil {
		return err
	}

	fmt.Printf("✅ License report generated at %s\n", outFile)
	return nil
}

// -------------------------------------------------------------------------------------
// MAIN + CLEANUP
// -------------------------------------------------------------------------------------

func main() {
	defer close(pomRequests) // stop sending new requests after main ends
	defer wgWorkers.Wait()   // wait for all workers to exit

	files, err := findBuildGradleFiles(".")
	if err != nil {
		fmt.Printf("Error finding build.gradle files: %v\n", err)
		os.Exit(1)
	}
	fmt.Printf("Found %d build.gradle file(s).\n", len(files))

	sections, err := parseAllBuildGradleFiles(files)
	if err != nil {
		fmt.Printf("Error parsing build.gradle files: %v\n", err)
		os.Exit(1)
	}

	// BFS transitive resolution
	buildTransitiveClosure(sections)

	// Generate HTML
	if err := generateHTMLReport(sections); err != nil {
		fmt.Printf("Error generating report: %v\n", err)
		os.Exit(1)
	}
}
