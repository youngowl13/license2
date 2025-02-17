package main

import (
	"bytes"
	"context"
	"encoding/xml"
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
	"time"
)

// -------------------------------------------------------------------------------------
// CONFIG & CONSTANTS
// -------------------------------------------------------------------------------------

// localPOMCacheDir is where we store fetched POM files to avoid re-downloading
const localPOMCacheDir = ".pom-cache"

// We'll limit concurrency to avoid too many simultaneous fetches
const pomWorkerCount = 10

// Maximum depth to resolve parent POMs to prevent infinite recursion
const maxParentDepth = 10

// HTTP timeout for fetching POM files
const httpTimeoutSeconds = 10

// Overall timeout for dependency fetching process (optional, can adjust or remove if not needed)
const dependencyFetchTimeoutMinutes = 20

// -------------------------------------------------------------------------------------
// DATA STRUCTURES
// -------------------------------------------------------------------------------------

// GradleDependencyNode represents a single node in the hierarchical dependency tree.
type GradleDependencyNode struct {
	Name       string
	Version    string
	License    string
	Copyleft   bool
	Parent     string
	Transitive []*GradleDependencyNode
}

// ExtendedDepInfo is for the flat table of dependencies.
type ExtendedDepInfo struct {
	Display string // displayed version
	Lookup  string // used for resolution
	Parent  string // "direct" or "group:artifact:version"
}

// GradleReportSection is produced for each build.gradle file found
type GradleReportSection struct {
	FilePath        string
	Dependencies    map[string]ExtendedDepInfo // final flat map after BFS
	DependencyTree  []*GradleDependencyNode    // hierarchical representation
	TransitiveCount int
}

// MavenPOM is the minimal structure we parse from each .pom file
type MavenPOM struct {
	XMLName        xml.Name    `xml:"project"`
	Parent         POMParent   `xml:"parent"`
	DependencyMgmt struct {
		Dependencies []POMDep `xml:"dependencies>dependency"`
	} `xml:"dependencyManagement"`
	Dependencies []POMDep `xml:"dependencies>dependency"`
	Licenses     []struct {
		Name string `xml:"name"`
	} `xml:"licenses>license"`

	GroupID    string `xml:"groupId"`
	ArtifactID string `xml:"artifactId"`
	Version    string `xml:"version"`
}

// POMParent holds <parent> info
type POMParent struct {
	GroupID    string `xml:"groupId"`
	ArtifactID string `xml:"artifactId"`
	Version    string `xml:"version"`
}

// POMDep is one <dependency> entry in <dependencies> or <dependencyManagement>.
type POMDep struct {
	GroupID    string `xml:"groupId"`
	ArtifactID string `xml:"artifactId"`
	Version    string `xml:"version"`
	Scope      string `xml:"scope"`
	Optional   string `xml:"optional"`
}

// We store BFS states as (version, depth) for each group/artifact
type depState struct {
	Version string
	Depth   int
}

// queueItem for BFS
type queueItem struct {
	GroupArtifact string
	Version       string
	Depth         int
	ParentNode    *GradleDependencyNode
}

// fetchRequest / fetchResult for concurrency
type fetchRequest struct {
	GroupID    string
	ArtifactID string
	Version    string
	ResultChan chan fetchResult
}

type fetchResult struct {
	POM *MavenPOM
	Err error
}

// -------------------------------------------------------------------------------------
// GLOBALS
// -------------------------------------------------------------------------------------

var (
	// We store processed POMs in memory to avoid re-processing
	pomCache sync.Map // key="group:artifact:version" => *MavenPOM
	// We store a guard to detect cycles in parent recursion
	parentVisit sync.Map
	// Channel for concurrency
	pomRequests = make(chan fetchRequest, 50)
	wgWorkers   sync.WaitGroup
)

// spdxLicenseMap holds some sample SPDX => (FriendlyName, Copyleft bool)
var spdxLicenseMap = map[string]struct {
	Name     string
	Copyleft bool
}{
	"MIT":        {Name: "MIT License", Copyleft: false},
	"Apache-2.0": {Name: "Apache License 2.0", Copyleft: false},
	"BSD-2-CLAUSE": {Name: "BSD 2-Clause", Copyleft: false},
	"BSD-3-CLAUSE": {Name: "BSD 3-Clause", Copyleft: false},
	"MPL-2.0":    {Name: "Mozilla Public License 2.0", Copyleft: true},
	"LGPL-2.1":   {Name: "GNU Lesser GPL v2.1", Copyleft: true},
	"LGPL-3.0":   {Name: "GNU Lesser GPL v3.0", Copyleft: true},
	"GPL-2.0":    {Name: "GNU GPL v2.0", Copyleft: true},
	"GPL-3.0":    {Name: "GNU GPL v3.0", Copyleft: true},
	"AGPL-3.0":   {Name: "GNU Affero GPL v3.0", Copyleft: true},
}

// -------------------------------------------------------------------------------------
// WORKER POOL INIT
// -------------------------------------------------------------------------------------

func init() {
	// Make sure .pom-cache folder exists
	_ = os.MkdirAll(localPOMCacheDir, 0755)
	// Start some worker goroutines
	wgWorkers.Add(pomWorkerCount)
	for i := 0; i < pomWorkerCount; i++ {
		go pomFetchWorker()
	}
}

// pomFetchWorker processes fetchRequests from the pomRequests channel in parallel.
func pomFetchWorker() {
	defer wgWorkers.Done()
	for req := range pomRequests {
		pom, err := retrieveOrLoadPOM(req.GroupID, req.ArtifactID, req.Version)
		req.ResultChan <- fetchResult{POM: pom, Err: err}
	}
}

// -------------------------------------------------------------------------------------
// STEP 1: FIND AND PARSE build.gradle
// -------------------------------------------------------------------------------------

func findBuildGradleFiles(root string) ([]string, error) {
	var files []string
	err := filepath.Walk(root, func(path string, info os.FileInfo, werr error) error {
		if werr != nil {
			return werr
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
	for _, m := range all {
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
				// variable interpolation
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
		if _, exists := deps[key]; !exists {
			deps[key] = ExtendedDepInfo{
				Display: version,
				Lookup:  version,
				Parent:  "direct",
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
			FilePath:     f,
			Dependencies: directDeps,
		})
	}
	return sections, nil
}

// parseVersionRange picks a lower-bound if version looks like [1.2,2.0) or (,1.5]
func parseVersionRange(v string) string {
	v = strings.TrimSpace(v)
	if (strings.HasPrefix(v, "[") || strings.HasPrefix(v, "(")) && strings.Contains(v, ",") {
		trimmed := strings.Trim(v, "[]() ")
		parts := strings.Split(trimmed, ",")
		if len(parts) > 0 {
			low := strings.TrimSpace(parts[0])
			if low == "" {
				low = "0.0"
			}
			return low
		}
	}
	return v
}

// -------------------------------------------------------------------------------------
// STEP 2: BFS + NEAREST-WINS + MULTI-LEVEL PARENT
// -------------------------------------------------------------------------------------

func buildTransitiveClosure(sections []GradleReportSection, ctx context.Context) {
	for i := range sections {
		sec := &sections[i]
		stateMap := make(map[string]depState)
		nodeMap := make(map[string]*GradleDependencyNode)
		var rootNodes []*GradleDependencyNode
		var queue []queueItem
		visitedDepsInBFS := make(map[string]bool) // Track visited dependencies in BFS

		// Initialize BFS with direct dependencies
		for ga, info := range sec.Dependencies {
			visitedDepsInBFS[ga] = true // Mark direct deps as visited initially
			n := &GradleDependencyNode{
				Name:    ga,
				Version: info.Lookup,
				Parent:  "direct",
			}
			rootNodes = append(rootNodes, n)
			nodeMap[ga] = n
			stateMap[ga] = depState{Version: info.Lookup, Depth: 1}
			queue = append(queue, queueItem{
				GroupArtifact: ga,
				Version:       info.Lookup,
				Depth:         1,
				ParentNode:    n,
			})
		}

		// BFS
		for len(queue) > 0 {
			select { // Check for timeout
			case <-ctx.Done():
				fmt.Println("⚠️ Dependency fetching timed out before completion.")
				return // Exit if context timeout exceeded
			default:
				// Continue BFS
			}

			it := queue[0]
			queue = queue[1:]

			gid, aid := splitGA(it.GroupArtifact)
			if gid == "" || aid == "" {
				continue
			}
			pom, err := concurrentFetchPOM(gid, aid, it.Version)
			if err != nil || pom == nil {
				fmt.Printf("⚠️ Could not process POM for %s:%s:%s. Skipping transitive dependencies for this branch.\n", gid, aid, it.Version)
				continue // Skip transitive deps for this branch on error
			}

			// attach license to the current node
			if it.ParentNode != nil {
				licName := detectLicense(pom)
				it.ParentNode.License = licName
				it.ParentNode.Copyleft = isCopyleft(licName)
			}

			managed := parseManagedVersions(pom)
			for _, d := range pom.Dependencies {
				if skipScope(d.Scope, d.Optional) {
					continue
				}
				childGA := d.GroupID + "/" + d.ArtifactID
				cv := parseVersionRange(d.Version)
				if cv == "" {
					if mv, ok := managed[childGA]; ok && mv != "" {
						cv = mv
					} else {
						cv = fallbackVersionRange(pom, d.GroupID, d.ArtifactID)
					}
				}
				if cv == "" {
					continue
				}
				childDepth := it.Depth + 1

				if _, alreadyVisitedInBFS := visitedDepsInBFS[childGA]; alreadyVisitedInBFS {
					continue // Skip if already visited in this BFS traversal (cycle detection)
				}

				curSt, seen := stateMap[childGA]
				if !seen {
					visitedDepsInBFS[childGA] = true // Mark as visited before enqueuing
					stateMap[childGA] = depState{Version: cv, Depth: childDepth}
					childNode := &GradleDependencyNode{
						Name:    childGA,
						Version: cv,
						Parent:  fmt.Sprintf("%s:%s", it.GroupArtifact, it.Version),
					}
					nodeMap[childGA] = childNode
					if it.ParentNode != nil {
						it.ParentNode.Transitive = append(it.ParentNode.Transitive, childNode)
					}
					queue = append(queue, queueItem{
						GroupArtifact: childGA,
						Version:       cv,
						Depth:         childDepth,
						ParentNode:    childNode,
					})
				} else {
					// conflict resolution - nearest wins
					if childDepth < curSt.Depth {
						visitedDepsInBFS[childGA] = true // Re-mark as visited if shallower path found
						stateMap[childGA] = depState{Version: cv, Depth: childDepth}
						childNode, ok := nodeMap[childGA]
						if !ok {
							childNode = &GradleDependencyNode{
								Name:    childGA,
								Version: cv,
								Parent:  fmt.Sprintf("%s:%s", it.GroupArtifact, it.Version),
							}
							nodeMap[childGA] = childNode
						} else {
							childNode.Version = cv
							childNode.Parent  = fmt.Sprintf("%s:%s", it.GroupArtifact, it.Version)
						}
						if it.ParentNode != nil {
							// Replace the old child node with the new one in parent's transitive list (if needed for correctness, otherwise just updating childNode might be enough for license report)
							it.ParentNode.Transitive = append(it.ParentNode.Transitive, childNode) // In nearest-wins, simply append. Consider if replacement is needed in other conflict resolution strategies.
						}
						queue = append(queue, queueItem{
							GroupArtifact: childGA,
							Version:       cv,
							Depth:         childDepth,
							ParentNode:    childNode,
						})
					}
				}
			}
		}

		sortRoots(rootNodes)
		sec.DependencyTree = rootNodes
		total := 0
		for _, rn := range rootNodes {
			total += countNodes(rn)
		}
		direct := len(rootNodes)
		sec.TransitiveCount = total - direct

		// fill final versions in the flat map
		for _, rn := range rootNodes {
			fillDepMap(rn, sec.Dependencies)
		}
	}
}

// splitGA splits "group/artifact" into (group, artifact).
func splitGA(ga string) (string, string) {
	parts := strings.Split(ga, "/")
	if len(parts) != 2 {
		return "", ""
	}
	return parts[0], parts[1]
}

// skipScope returns true if scope in {test, provided, system} or optional==true
func skipScope(scope, optional string) bool {
	s := strings.ToLower(strings.TrimSpace(scope))
	if s == "test" || s == "provided" || s == "system" {
		return true
	}
	if strings.EqualFold(strings.TrimSpace(optional), "true") {
		return true
	}
	return false
}

// parseManagedVersions merges <dependencyManagement>
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

// fallbackVersionRange tries to fill version from the parent's groupId/version if matching
func fallbackVersionRange(pom *MavenPOM, g, a string) string {
	if g == pom.GroupID && pom.Version != "" {
		return parseVersionRange(pom.Version)
	}
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
	count := 1
	for _, c := range n.Transitive {
		count += countNodes(c)
	}
	return count
}

// fillDepMap updates the final "flat" map from the BFS tree
func fillDepMap(n *GradleDependencyNode, depMap map[string]ExtendedDepInfo) {
	key := n.Name
	info, ok := depMap[key]
	if !ok {
		info = ExtendedDepInfo{Display: n.Version, Lookup: n.Version, Parent: n.Parent}
	} else {
		info.Display = n.Version
		info.Lookup  = n.Version
		info.Parent  = n.Parent
	}
	depMap[key] = info
	for _, c := range n.Transitive {
		fillDepMap(c, depMap)
	}
}

// -------------------------------------------------------------------------------------
// STEP 3: LICENSE DETECTION
// -------------------------------------------------------------------------------------

// detectLicense looks at the first <license><name> from the POM
// If it matches known SPDX IDs, we map it to a friendlier name
func detectLicense(pom *MavenPOM) string {
	if len(pom.Licenses) == 0 {
		return "Unknown"
	}
	lic := strings.TrimSpace(pom.Licenses[0].Name)
	if lic == "" {
		return "Unknown"
	}
	// Check if lic is an SPDX ID
	up := strings.ToUpper(lic)
	for spdxID, info := range spdxLicenseMap {
		if strings.EqualFold(lic, spdxID) || strings.EqualFold(up, spdxID) {
			return info.Name
		}
	}
	// else just return as-is
	return lic
}

// isCopyleft checks if license is recognized as copyleft, via spdxLicenseMap or fallback keywords
func isCopyleft(name string) bool {
	// first see if name exactly matches an spdx that is known copyleft
	for spdxID, data := range spdxLicenseMap {
		if data.Copyleft && (strings.EqualFold(name, data.Name) || strings.EqualFold(name, spdxID)) {
			return true
		}
	}
	// fallback keywords
	copyleftKeywords := []string{
		"GPL", "LGPL", "AGPL", "CC BY-SA", "MPL", "EPL", "CPL", "CDDL",
		"EUPL", "Affero", "OSL", "CeCILL", "GNU General Public License",
		"GNU Lesser General Public License", "Mozilla Public License",
		"Common Development and Distribution License", "Eclipse Public License",
		"Common Public License", "European Union Public License", "Open Software License",
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
// STEP 4: CONCURRENT POM FETCH + DISK CACHING
// -------------------------------------------------------------------------------------

// concurrentFetchPOM sends a request to the worker pool
func concurrentFetchPOM(g, a, v string) (*MavenPOM, error) {
	if g == "" || a == "" || v == "" {
		return nil, fmt.Errorf("invalid GAV: %s:%s:%s", g, a, v)
	}
	key := fmt.Sprintf("%s:%s:%s", g, a, v)
	if c, ok := pomCache.Load(key); ok {
		return c.(*MavenPOM), nil
	}
	resultChan := make(chan fetchResult, 1)
	pomRequests <- fetchRequest{
		GroupID:    g,
		ArtifactID: a,
		Version:    v,
		ResultChan: resultChan,
	}
	res := <-resultChan
	if res.Err != nil {
		fmt.Printf("⚠️ Error fetching POM for %s:%s:%s: %v\n", g, a, v, res.Err)
		return nil, nil // Return nil POM, nil error on fetch error to continue processing
	}
	if res.POM == nil {
		fmt.Printf("⚠️ No POM found for %s:%s:%s\n", g, a, v)
		return nil, nil // Return nil POM, nil error if POM is nil
	}
	pomCache.Store(key, res.POM)
	return res.POM, res.Err
}

// retrieveOrLoadPOM tries local disk first, then remote
func retrieveOrLoadPOM(g, a, v string) (*MavenPOM, error) {
	key := fmt.Sprintf("%s:%s:%s", g, a, v)
	if c, ok := pomCache.Load(key); ok {
		return c.(*MavenPOM), nil
	}
	pom, err := loadPOMFromDisk(g, a, v)
	if err == nil && pom != nil {
		pomCache.Store(key, pom)
	} else {
		// fetch remote
		pom, err = fetchRemotePOM(g, a, v)
		if err != nil {
			return nil, err
		}
		if pom != nil { // Save to disk only if fetch was successful and POM is not nil
			_ = savePOMToDisk(g, a, v, pom)
			pomCache.Store(key, pom)
		}
	}
	if pom == nil {
		return nil, fmt.Errorf("no POM for %s", key)
	}
	// multi-level parent
	if pom.GroupID == "" {
		pom.GroupID = pom.Parent.GroupID
	}
	if pom.Version == "" {
		pom.Version = pom.Parent.Version
	}
	err = loadAllParents(pom, 0)
	if err != nil {
		// not necessarily fatal, but log it
		fmt.Printf("⚠️ Error loading parent POMs for %s:%s:%s: %v\n", g, a, v, err)
	}
	return pom, nil
}

// loadAllParents merges parent recursively
func loadAllParents(p *MavenPOM, depth int) error {
	if depth > maxParentDepth {
		return fmt.Errorf("parent POM recursion depth exceeded limit (%d), possible cycle or very deep hierarchy for %s:%s:%s", maxParentDepth, p.GroupID, p.ArtifactID, p.Version)
	}
	if p.Parent.GroupID == "" || p.Parent.ArtifactID == "" || p.Parent.Version == "" {
		return nil
	}
	pkey := fmt.Sprintf("%s:%s:%s", p.Parent.GroupID, p.Parent.ArtifactID, p.Parent.Version)
	if _, visited := parentVisit.Load(pkey); visited {
		return fmt.Errorf("detected parent cycle: %s", pkey)
	}
	parentVisit.Store(pkey, true)
	parentPOM, err := retrieveOrLoadPOM(p.Parent.GroupID, p.Parent.ArtifactID, p.Parent.Version)
	if err != nil {
		return err
	}
	// merge <dependencyManagement>
	p.DependencyMgmt.Dependencies = mergeDepMgmt(parentPOM.DependencyMgmt.Dependencies, p.DependencyMgmt.Dependencies)
	if p.GroupID == "" {
		p.GroupID = parentPOM.GroupID
	}
	if p.Version == "" {
		p.Version = parentPOM.Version
	}
	return loadAllParents(parentPOM, depth+1)
}

// fetchRemotePOM tries Maven Central then Google
func fetchRemotePOM(g, a, v string) (*MavenPOM, error) {
	groupPath := strings.ReplaceAll(g, ".", "/")
	urlCentral := fmt.Sprintf("https://repo1.maven.org/maven2/%s/%s/%s/%s-%s.pom", groupPath, a, v, a, v)
	urlGoogle := fmt.Sprintf("https://dl.google.com/dl/android/maven2/%s/%s/%s/%s-%s.pom", groupPath, a, v, a, v)

	if pm, err := fetchPOMFromURL(urlCentral); err == nil {
		return pm, nil
	}
	if pm, err := fetchPOMFromURL(urlGoogle); err == nil {
		return pm, nil
	}
	return nil, fmt.Errorf("could not fetch remote POM for %s:%s:%s from Maven Central or Google Maven", g, a, v)
}

func fetchPOMFromURL(url string) (*MavenPOM, error) {
	client := http.Client{Timeout: httpTimeoutSeconds * time.Second} // Add HTTP timeout
	resp, err := client.Get(url)
	if err != nil {
		return nil, err
	}
	defer resp.Body.Close()
	if resp.StatusCode != 200 {
		return nil, fmt.Errorf("http status %d for %s", resp.StatusCode, url)
	}
	data, err := io.ReadAll(resp.Body)
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

// mergeDepMgmt merges parent's <dependencyManagement> with child's
func mergeDepMgmt(parent, child []POMDep) []POMDep {
	outMap := make(map[string]POMDep)
	for _, d := range parent {
		key := d.GroupID + ":" + d.ArtifactID
		outMap[key] = d
	}
	for _, d := range child {
		key := d.GroupID + ":" + d.ArtifactID
		outMap[key] = d
	}
	var merged []POMDep
	for _, val := range outMap {
		merged = append(merged, val)
	}
	sort.Slice(merged, func(i, j int) bool {
		return merged[i].GroupID < merged[j].GroupID
	})
	return merged
}

// load/save disk cache
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
	if err := os.MkdirAll(filepath.Dir(path), 0755); err != nil {
		return err
	}
	f, err := os.Create(path)
	if err != nil {
		return err
	}
	defer f.Close()
	out, err := xml.MarshalIndent(pom, "", "  ")
	if err != nil {
		return err
	}
	_, err = f.Write(out)
	return err
}

func localCachePath(g, a, v string) string {
	groupPath := strings.ReplaceAll(g, ".", "/")
	return filepath.Join(localPOMCacheDir, groupPath, a, v, fmt.Sprintf("%s-%s.pom.xml", a, v))
}

// -------------------------------------------------------------------------------------
// STEP 5: HTML REPORT
// -------------------------------------------------------------------------------------

// buildGradleTreeHTML recursively constructs <details> blocks for the dependency tree
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
	sb.WriteString("</details>")
	return sb.String()
}

func buildGradleTreesHTML(nodes []*GradleDependencyNode) template.HTML {
	var buf strings.Builder
	for _, n := range nodes {
		buf.WriteString(buildGradleTreeHTML(n, 0))
	}
	return template.HTML(buf.String())
}

// Table license data struct
type LicenseData struct {
	LicenseName string
	ProjectURL  string
	PomURL      string
}

func getLicenseInfoWrapper(dep, version string) LicenseData {
	parts := strings.Split(dep, "/")
	if len(parts) != 2 {
		return LicenseData{
			LicenseName: "Unknown",
		}
	}
	g, a := parts[0], parts[1]
	pom, err := concurrentFetchPOM(g, a, version)
	if err != nil || pom == nil {
		return LicenseData{
			LicenseName: "Unknown",
			ProjectURL:  fmt.Sprintf("https://www.google.com/search?q=%s+%s+%s+license", g, a, version),
		}
	}
	licenseName := detectLicense(pom)
	groupPath := strings.ReplaceAll(g, ".", "/")
	projURL := fmt.Sprintf("https://repo1.maven.org/maven2/%s/%s/%s/", groupPath, a, version)
	pomURL := fmt.Sprintf("https://repo1.maven.org/maven2/%s/%s/%s/%s-%s.pom", groupPath, a, version, a, version)
	return LicenseData{
		LicenseName: licenseName,
		ProjectURL:  projURL,
		PomURL:      pomURL,
	}
}

func generateHTMLReport(sections []GradleReportSection) error {
	outDir := "./license-checker"
	if err := os.MkdirAll(outDir, 0755); err != nil {
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
  <p>This includes concurrency, multi-level parents, disk caching, and partial version-range handling.</p>

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
		"isCopyleft":            isCopyleft,
	}).Parse(tmplText)
	if err != nil {
		return err
	}

	outputFile := filepath.Join(outDir, "dependency-license-report.html")
	f, err := os.Create(outputFile)
	if err != nil {
		return err
	}
	defer f.Close()

	if err := tmpl.Execute(f, sections); err != nil {
		return err
	}

	fmt.Printf("✅ License report generated at %s\n", outputFile)
	return nil
}

// -------------------------------------------------------------------------------------
// MAIN
// -------------------------------------------------------------------------------------

func main() {
	defer close(pomRequests) // close channel so workers exit
	defer wgWorkers.Wait()   // wait for them

	files, err := findBuildGradleFiles(".")
	if err != nil {
		fmt.Printf("Error: %v\n", err)
		os.Exit(1)
	}
	fmt.Printf("Found %d build.gradle file(s).\n", len(files))

	sections, err := parseAllBuildGradleFiles(files)
	if err != nil {
		fmt.Printf("Error parsing build.gradle: %v\n", err)
		os.Exit(1)
	}

	// Add context with timeout for the entire dependency fetching process
	ctx, cancel := context.WithTimeout(context.Background(), dependencyFetchTimeoutMinutes*time.Minute)
	defer cancel()

	buildTransitiveClosure(sections, ctx) // Pass context to buildTransitiveClosure

	if ctx.Err() == context.DeadlineExceeded { // Check if timeout occurred
		fmt.Println("⚠️ Dependency fetching process timed out and might be incomplete.")
	}

	if err := generateHTMLReport(sections); err != nil {
		fmt.Printf("Error generating HTML: %v\n", err)
		os.Exit(1)
	}
}
