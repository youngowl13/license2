package main

import (
	"bytes"
	"encoding/xml"
	"fmt"
	"html/template"
	"io"
	"net/http"
	"os"
	"path/filepath"
	"regexp"
	"sort"
	"strings"
	"sync"
	"time"
)

// -----------------------------------------------------------------------
// CONFIG & CONSTANTS
// -----------------------------------------------------------------------

const (
	localPOMCacheDir = ".pom-cache"         // Directory for disk caching of POMs
	pomWorkerCount   = 10                   // Number of concurrent POM fetch workers
	fetchTimeout     = 30 * time.Second     // HTTP request timeout
)

// -----------------------------------------------------------------------
// GLOBAL VARIABLES
// -----------------------------------------------------------------------

var (
	pomCache    sync.Map // key = "group:artifact:version" -> *MavenPOM
	parentVisit sync.Map // for cycle detection in parent resolution

	// Channel for POM fetch requests and wait group for workers.
	pomRequests = make(chan fetchRequest, 50)
	wgWorkers   sync.WaitGroup

	// Channel open flag
	channelOpen  = true
	channelMutex sync.Mutex

	// Known SPDX licenses and whether they are copyleft.
	spdxLicenseMap = map[string]struct {
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
)

// -----------------------------------------------------------------------
// DATA STRUCTURES
// -----------------------------------------------------------------------

// ExtendedDepInfo holds info for a dependency (for the flat table).
type ExtendedDepInfo struct {
	Display           string // What to display (e.g. "1.4.10" or "version not available")
	Lookup            string // Version as parsed from file (may be "unknown")
	Parent            string // "direct" or parent's GAV string
	License           string // Final license string
	LicenseProjectURL string // URL for project details (or Google search if unresolved)
	LicensePomURL     string // URL to view the POM file
}

// GradleDependencyNode represents a node in the dependency tree.
type GradleDependencyNode struct {
	Name       string
	Version    string
	License    string
	Copyleft   bool
	Parent     string // "direct" for direct deps or parent's GAV for transitive deps
	Transitive []*GradleDependencyNode
}

// GradleReportSection holds data for one build.gradle file.
type GradleReportSection struct {
	FilePath        string
	Dependencies    map[string]ExtendedDepInfo // Flat map with keys "group/artifact@version"
	DependencyTree  []*GradleDependencyNode    // Hierarchical dependency tree
	TransitiveCount int                        // Total transitive dependency count
	DirectCount     int                        // Count of direct dependencies
	IndirectCount   int                        // Count of indirect dependencies
	CopyleftCount   int                        // Count of copyleft licenses
	UnknownCount    int                        // Count of dependencies with "Unknown" license
}

// MavenPOM represents the structure parsed from a POM file.
type MavenPOM struct {
	XMLName        xml.Name `xml:"project"`
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

// POMParent holds the <parent> info.
type POMParent struct {
	GroupID    string `xml:"groupId"`
	ArtifactID string `xml:"artifactId"`
	Version    string `xml:"version"`
}

// POMDep represents one dependency entry in a POM.
type POMDep struct {
	GroupID    string `xml:"groupId"`
	ArtifactID string `xml:"artifactId"`
	Version    string `xml:"version"`
	Scope      string `xml:"scope"`
	Optional   string `xml:"optional"`
}

// depState is used during BFS to track version and depth.
type depState struct {
	Version string
	Depth   int
}

// queueItem represents an item in the BFS queue.
type queueItem struct {
	GroupArtifact string
	Version       string
	Depth         int
	ParentNode    *GradleDependencyNode
}

// fetchRequest is used to request a POM from a worker.
type fetchRequest struct {
	GroupID    string
	ArtifactID string
	Version    string
	ResultChan chan fetchResult
}

// fetchResult is the result from a worker.
type fetchResult struct {
	POM *MavenPOM
	Err error
}

// -----------------------------------------------------------------------
// HELPER FUNCTIONS
// -----------------------------------------------------------------------

// splitGA splits a string in the format "group/artifact" into group and artifact.
func splitGA(ga string) (string, string) {
	parts := strings.Split(ga, "/")
	if len(parts) != 2 {
		return "", ""
	}
	return parts[0], parts[1]
}

// skipScope returns true if the given dependency scope or optional flag means we skip it.
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

// parseVersionRange returns a version string from a range (e.g. "[1.2,2.0)") by choosing the lower bound.
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

// parseManagedVersions extracts managed versions from a POM's dependencyManagement section.
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

// fallbackVersionRange tries to use the POM's own version or its parent's version as a fallback.
func fallbackVersionRange(pom *MavenPOM, g, a string) string {
	if g == pom.GroupID && pom.Version != "" {
		return parseVersionRange(pom.Version)
	}
	if g == pom.Parent.GroupID && pom.Parent.Version != "" {
		return parseVersionRange(pom.Parent.Version)
	}
	return ""
}

// sortRoots recursively sorts dependency tree nodes.
func sortRoots(roots []*GradleDependencyNode) {
	sort.Slice(roots, func(i, j int) bool {
		return roots[i].Name < roots[j].Name
	})
	for _, r := range roots {
		sortRoots(r.Transitive)
	}
}

// countNodes returns the total number of nodes in a dependency tree.
func countNodes(n *GradleDependencyNode) int {
	count := 1
	for _, c := range n.Transitive {
		count += countNodes(c)
	}
	return count
}

// fillDepMap recursively fills a flat map of dependencies from the tree.
// The key is "group/artifact@version".
func fillDepMap(n *GradleDependencyNode, depMap map[string]ExtendedDepInfo) {
	key := fmt.Sprintf("%s@%s", n.Name, n.Version)
	info, exists := depMap[key]
	if !exists {
		info = ExtendedDepInfo{
			Display: n.Version,
			Lookup:  n.Version,
			Parent:  n.Parent,
		}
	} else {
		info.Display = n.Version
		info.Lookup = n.Version
		info.Parent = n.Parent
	}
	depMap[key] = info
	for _, c := range n.Transitive {
		fillDepMap(c, depMap)
	}
}

// -----------------------------------------------------------------------
// LICENSE DETECTION FUNCTIONS
// -----------------------------------------------------------------------

func detectLicense(pom *MavenPOM) string {
	if len(pom.Licenses) == 0 {
		return "Unknown"
	}
	lic := strings.TrimSpace(pom.Licenses[0].Name)
	if lic == "" {
		return "Unknown"
	}
	up := strings.ToUpper(lic)
	for spdxID, data := range spdxLicenseMap {
		if strings.EqualFold(lic, spdxID) || up == strings.ToUpper(spdxID) {
			return data.Name
		}
	}
	return lic
}

func isCopyleft(name string) bool {
	// First, check against the SPDX map.
	for spdxID, data := range spdxLicenseMap {
		if data.Copyleft && (strings.EqualFold(name, data.Name) || strings.EqualFold(name, spdxID)) {
			return true
		}
	}
	// Fallback: check common keywords.
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

// -----------------------------------------------------------------------
// POM FETCH FUNCTIONS & DISK CACHING
// -----------------------------------------------------------------------

type fetchRequest struct {
	GroupID    string
	ArtifactID string
	Version    string
	ResultChan chan fetchResult
}

type fetchResult struct {
	POM *MavenPOM
	Err error
}

func concurrentFetchPOM(g, a, v string) (*MavenPOM, error) {
	key := fmt.Sprintf("%s:%s:%s", g, a, v)
	if c, ok := pomCache.Load(key); ok {
		return c.(*MavenPOM), nil
	}
	channelMutex.Lock()
	open := channelOpen
	channelMutex.Unlock()
	if !open {
		pom, err := fetchRemotePOM(g, a, v)
		if err == nil && pom != nil {
			pomCache.Store(key, pom)
		}
		return pom, err
	}
	resultChan := make(chan fetchResult, 1)
	pomRequests <- fetchRequest{
		GroupID:    g,
		ArtifactID: a,
		Version:    v,
		ResultChan: resultChan,
	}
	res := <-resultChan
	if res.Err == nil && res.POM != nil {
		pomCache.Store(key, res.POM)
	}
	return res.POM, res.Err
}

func retrieveOrLoadPOM(g, a, v string) (*MavenPOM, error) {
	key := fmt.Sprintf("%s:%s:%s", g, a, v)
	if c, ok := pomCache.Load(key); ok {
		return c.(*MavenPOM), nil
	}
	pom, err := loadPOMFromDisk(g, a, v)
	if err == nil && pom != nil {
		pomCache.Store(key, pom)
		return pom, nil
	}
	pom, err = fetchRemotePOM(g, a, v)
	if err != nil {
		return nil, err
	}
	_ = savePOMToDisk(g, a, v, pom)
	pomCache.Store(key, pom)
	if pom == nil {
		return nil, fmt.Errorf("no POM for %s", key)
	}
	if pom.GroupID == "" {
		pom.GroupID = pom.Parent.GroupID
	}
	if pom.Version == "" {
		pom.Version = pom.Parent.Version
	}
	_ = loadAllParents(pom, 0)
	return pom, nil
}

func loadAllParents(p *MavenPOM, depth int) error {
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
	p.DependencyMgmt.Dependencies = mergeDepMgmt(parentPOM.DependencyMgmt.Dependencies, p.DependencyMgmt.Dependencies)
	if p.GroupID == "" {
		p.GroupID = parentPOM.GroupID
	}
	if p.Version == "" {
		p.Version = parentPOM.Version
	}
	return loadAllParents(parentPOM, depth+1)
}

func fetchRemotePOM(g, a, v string) (*MavenPOM, error) {
	groupPath := strings.ReplaceAll(g, ".", "/")
	urlCentral := fmt.Sprintf("https://repo1.maven.org/maven2/%s/%s/%s/%s-%s.pom", groupPath, a, v, a, v)
	urlGoogle := fmt.Sprintf("https://dl.google.com/dl/android/maven2/%s/%s/%s/%s-%s.pom", groupPath, a, v, a, v)
	if pm, err := fetchPOMFromURL(urlCentral); err == nil && pm != nil {
		return pm, nil
	}
	if pm, err := fetchPOMFromURL(urlGoogle); err == nil && pm != nil {
		return pm, nil
	}
	return nil, fmt.Errorf("could not fetch remote POM for %s:%s:%s", g, a, v)
}

func fetchPOMFromURL(url string) (*MavenPOM, error) {
	client := http.Client{Timeout: fetchTimeout}
	resp, err := client.Get(url)
	if err != nil {
		return nil, err
	}
	defer resp.Body.Close()
	if resp.StatusCode != 200 {
		return nil, fmt.Errorf("HTTP %d for %s", resp.StatusCode, url)
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

func loadPOMFromDisk(g, a, v string) (*MavenPOM, error) {
	path := localCachePath(g, a, v)
	data, err := os.ReadFile(path)
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
	out, err := xml.MarshalIndent(pom, "", "  ")
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

// -----------------------------------------------------------------------
// BFS: Build Transitive Closure & Flat Map
// -----------------------------------------------------------------------

func buildTransitiveClosure(sections []GradleReportSection) {
	for i := range sections {
		sec := &sections[i]
		fmt.Printf("Building transitive closure for %s\n", sec.FilePath)
		stateMap := make(map[string]depState)
		nodeMap := make(map[string]*GradleDependencyNode)
		flatDeps := make(map[string]ExtendedDepInfo)

		// Initialize flatDeps with direct dependencies.
		for k, v := range sec.Dependencies {
			flatDeps[k] = v
		}
		var rootNodes []*GradleDependencyNode
		var queue []queueItem
		visitedBFS := make(map[string]bool)

		// Initialize BFS with direct dependencies.
		for depKey, info := range sec.Dependencies {
			visitedBFS[depKey] = true
			parts := strings.Split(depKey, "@")
			if len(parts) != 2 {
				continue
			}
			ga := parts[0]
			n := &GradleDependencyNode{
				Name:    ga,
				Version: info.Lookup,
				Parent:  "direct",
			}
			rootNodes = append(rootNodes, n)
			nodeMap[depKey] = n
			stateMap[depKey] = depState{Version: info.Lookup, Depth: 1}
			queue = append(queue, queueItem{
				GroupArtifact: ga,
				Version:       info.Lookup,
				Depth:         1,
				ParentNode:    n,
			})
		}

		// Process BFS queue.
		for len(queue) > 0 {
			it := queue[0]
			queue = queue[1:]
			fmt.Printf("BFS: Processing %s (depth %d)\n", it.GroupArtifact, it.Depth)
			gid, aid := splitGA(it.GroupArtifact)
			if gid == "" || aid == "" {
				continue
			}
			if strings.Contains(it.Version, "${") || strings.ToLower(it.Version) == "unknown" {
				latest, err := getLatestVersion(gid, aid)
				if err != nil {
					it.Version = "unknown"
				} else {
					it.Version = latest
				}
			}
			pom, err := concurrentFetchPOM(gid, aid, it.Version)
			if err != nil || pom == nil {
				continue
			}
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
				if cv == "" || strings.Contains(cv, "${") {
					if mv, ok := managed[childGA]; ok && mv != "" {
						cv = mv
					} else {
						latest, err := getLatestVersion(d.GroupID, d.ArtifactID)
						if err != nil {
							continue
						}
						cv = latest
					}
				}
				if cv == "" {
					continue
				}
				childDepth := it.Depth + 1
				childKey := fmt.Sprintf("%s@%s", childGA, cv)
				if _, found := visitedBFS[childKey]; found {
					continue
				}
				visitedBFS[childKey] = true
				_, seen := stateMap[childKey]
				if !seen {
					stateMap[childKey] = depState{Version: cv, Depth: childDepth}
					childNode := &GradleDependencyNode{
						Name:    childGA,
						Version: cv,
						Parent:  fmt.Sprintf("%s:%s", it.GroupArtifact, it.Version),
					}
					nodeMap[childKey] = childNode
					flatDeps[childKey] = ExtendedDepInfo{
						Display: cv,
						Lookup:  cv,
						Parent:  fmt.Sprintf("%s:%s", it.GroupArtifact, it.Version),
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
					fmt.Printf("BFS: Added %s (depth %d)\n", childKey, childDepth)
				} else {
					current := stateMap[childKey]
					if childDepth < current.Depth {
						stateMap[childKey] = depState{Version: cv, Depth: childDepth}
						childNode, ok := nodeMap[childKey]
						if !ok {
							childNode = &GradleDependencyNode{
								Name:    childGA,
								Version: cv,
								Parent:  fmt.Sprintf("%s:%s", it.GroupArtifact, it.Version),
							}
							nodeMap[childKey] = childNode
						} else {
							childNode.Version = cv
							childNode.Parent = fmt.Sprintf("%s:%s", it.GroupArtifact, it.Version)
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
		// Fill flat dependency map from the BFS tree.
		for _, rn := range rootNodes {
			fillDepMap(rn, flatDeps)
		}
		sec.Dependencies = flatDeps
		sortRoots(rootNodes)
		sec.DependencyTree = rootNodes

		// Compute transitive count as total nodes minus direct ones.
		totalNodes := 0
		for _, rn := range rootNodes {
			totalNodes += countNodes(rn)
		}
		directCount := 0
		for key, info := range sec.Dependencies {
			if info.Parent == "direct" || strings.HasSuffix(key, "@unknown") {
				directCount++
			}
		}
		sec.TransitiveCount = totalNodes - directCount
	}
}

// -----------------------------------------------------------------------
// PRECOMPUTE LICENSE INFO (after BFS)
// -----------------------------------------------------------------------

func precomputeLicenseInfo(sections []GradleReportSection) {
	for idx := range sections {
		sec := &sections[idx]
		for depKey, info := range sec.Dependencies {
			parts := strings.Split(depKey, "@")
			if len(parts) != 2 {
				continue
			}
			ga := parts[0]
			version := info.Lookup
			gaParts := strings.Split(ga, "/")
			if len(gaParts) != 2 {
				continue
			}
			g, a := gaParts[0], gaParts[1]
			if strings.ToLower(version) == "unknown" {
				info.License = "Unknown"
				info.LicenseProjectURL = fmt.Sprintf("https://www.google.com/search?q=%s+%s+license", g, a)
				info.LicensePomURL = ""
			} else {
				pom, err := concurrentFetchPOM(g, a, version)
				if err != nil || pom == nil {
					info.License = "Unknown"
					info.LicenseProjectURL = fmt.Sprintf("https://www.google.com/search?q=%s+%s+%s+license", g, a, version)
					info.LicensePomURL = ""
				} else {
					lic := detectLicense(pom)
					fmt.Printf("Precompute: %s -> License: '%s'\n", depKey, lic)
					info.License = lic
					groupPath := strings.ReplaceAll(g, ".", "/")
					info.LicenseProjectURL = fmt.Sprintf("https://repo1.maven.org/maven2/%s/%s/%s/", groupPath, a, version)
					info.LicensePomURL = fmt.Sprintf("https://repo1.maven.org/maven2/%s/%s/%s/%s-%s.pom", groupPath, a, version, a, version)
				}
			}
			sec.Dependencies[depKey] = info
		}
	}
}

// -----------------------------------------------------------------------
// COMPUTE SUMMARY METRICS (after license precomputation)
// -----------------------------------------------------------------------

func computeSummary(sections []GradleReportSection) {
	for idx := range sections {
		sec := &sections[idx]
		var directCount, indirectCount, copyleftCount, unknownCount int
		for _, info := range sec.Dependencies {
			if info.Parent == "direct" {
				directCount++
			} else {
				indirectCount++
			}
			if isCopyleft(info.License) {
				copyleftCount++
			}
			if info.License == "Unknown" {
				unknownCount++
			}
		}
		sec.DirectCount = directCount
		sec.IndirectCount = indirectCount
		sec.CopyleftCount = copyleftCount
		sec.UnknownCount = unknownCount
	}
}

// -----------------------------------------------------------------------
// HTML REPORT & CONSOLE REPORT
// -----------------------------------------------------------------------

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
  {{ range . }}
    <h2>File: {{ .FilePath }}</h2>
    <p>
      Direct Dependencies: {{ .DirectCount }}<br>
      Indirect Dependencies: {{ .IndirectCount }}<br>
      Copyleft Dependencies: {{ .CopyleftCount }}<br>
      Unknown License Dependencies: {{ .UnknownCount }}
    </p>
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
          <tr {{ if eq $info.License "Unknown" }}class="unknown-license"{{ else if isCopyleft $info.License }}class="copyleft"{{ else }}class="non-copyleft"{{ end }}>
            <td>{{ $dep }}</td>
            <td>{{ $info.Display }}</td>
            <td>{{ $info.License }}</td>
            <td>{{ $info.Parent }}</td>
            {{ if $info.LicenseProjectURL }}
              <td><a href="{{ $info.LicenseProjectURL }}" target="_blank">View Details</a></td>
            {{ else }}
              <td></td>
            {{ end }}
            {{ if $info.LicensePomURL }}
              <td><a href="{{ $info.LicensePomURL }}" target="_blank">View POM</a></td>
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
		"isCopyleft":           isCopyleft,
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

// -----------------------------------------------------------------------
// CONSOLE REPORT
// -----------------------------------------------------------------------

func printConsoleReport(sections []GradleReportSection) {
	fmt.Println("----- Console Dependency Report -----")
	for _, sec := range sections {
		fmt.Printf("File: %s\n", sec.FilePath)
		fmt.Printf("Direct Dependencies: %d, Indirect: %d, Copyleft: %d, Unknown: %d\n",
			sec.DirectCount, sec.IndirectCount, sec.CopyleftCount, sec.UnknownCount)
		fmt.Println("Flat Dependencies:")
		var keys []string
		for k := range sec.Dependencies {
			keys = append(keys, k)
		}
		sort.Strings(keys)
		for _, k := range keys {
			info := sec.Dependencies[k]
			fmt.Printf("  %s -> %s (Parent=%s, License=%s)\n", k, info.Display, info.Parent, info.License)
		}
		fmt.Println("Dependency Tree:")
		for _, node := range sec.DependencyTree {
			printTreeNode(node, 0)
		}
		fmt.Println("-------------------------------------")
	}
}

func printTreeNode(node *GradleDependencyNode, indent int) {
	prefix := strings.Repeat("  ", indent)
	fmt.Printf("%s%s@%s (License=%s)\n", prefix, node.Name, node.Version, node.License)
	for _, c := range node.Transitive {
		printTreeNode(c, indent+1)
	}
}

// -----------------------------------------------------------------------
// MAIN FUNCTION
// -----------------------------------------------------------------------

func main() {
	// Start worker pool.
	for i := 0; i < pomWorkerCount; i++ {
		wgWorkers.Add(1)
		go pomFetchWorker()
	}

	fmt.Println("Starting dependency analysis...")

	files, err := findBuildGradleFiles(".")
	if err != nil {
		fmt.Printf("Error scanning for build.gradle files: %v\n", err)
		os.Exit(1)
	}
	fmt.Printf("Found %d build.gradle file(s).\n", len(files))

	sections, err := parseAllBuildGradleFiles(files)
	if err != nil {
		fmt.Printf("Error parsing build.gradle files: %v\n", err)
		os.Exit(1)
	}

	fmt.Println("Starting transitive dependency resolution...")
	buildTransitiveClosure(sections)

	// Close channel and wait for workers.
	channelMutex.Lock()
	channelOpen = false
	channelMutex.Unlock()
	close(pomRequests)
	wgWorkers.Wait()

	// Precompute license info AFTER BFS.
	precomputeLicenseInfo(sections)

	// Compute summary metrics AFTER license info is updated.
	computeSummary(sections)

	fmt.Println("Generating HTML report...")
	if err := generateHTMLReport(sections); err != nil {
		fmt.Printf("Error generating HTML report: %v\n", err)
		os.Exit(1)
	}

	fmt.Println("Printing console report...")
	printConsoleReport(sections)
	fmt.Println("Analysis complete.")
}
