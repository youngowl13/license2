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
	localPOMCacheDir = ".pom-cache"  // Directory for disk caching of POMs
	pomWorkerCount   = 10            // Number of concurrent POM fetch workers
	fetchTimeout     = 30 * time.Second // HTTP request timeout
)

var (
	// Channel-based concurrency
	pomRequests = make(chan fetchRequest, 50)
	wgWorkers   sync.WaitGroup

	// We keep a global map of fetched POMs: key = "group:artifact:version"
	pomCache sync.Map

	// We track visited parents to detect cycles
	parentVisit sync.Map

	// Flag to indicate if pomRequests is still open
	channelOpen  = true
	channelMutex sync.Mutex

	// We define some known SPDX => (FriendlyName, Copyleft)
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

// ExtendedDepInfo is the flat table entry for a single dependency.
type ExtendedDepInfo struct {
	Display           string // displayed version
	Lookup            string // version used for resolution
	Parent            string // "direct" or "someParent:version"
	License           string // final license string
	LicenseProjectURL string // project details link
	LicensePomURL     string // POM file link
}

// GradleDependencyNode is a node in the dependency tree.
type GradleDependencyNode struct {
	Name       string
	Version    string
	License    string
	Copyleft   bool
	Parent     string
	Transitive []*GradleDependencyNode
}

// GradleReportSection holds data for one build.gradle file.
type GradleReportSection struct {
	FilePath        string
	Dependencies    map[string]ExtendedDepInfo // e.g. "group/artifact@version" => ExtendedDepInfo
	DependencyTree  []*GradleDependencyNode
	TransitiveCount int
	DirectCount     int
	IndirectCount   int
	CopyleftCount   int
	UnknownCount    int
}

// MavenPOM is the structure we parse from a .pom file.
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

// POMParent is the <parent> block in a POM.
type POMParent struct {
	GroupID    string `xml:"groupId"`
	ArtifactID string `xml:"artifactId"`
	Version    string `xml:"version"`
}

// POMDep is a single dependency in <dependencies>.
type POMDep struct {
	GroupID    string `xml:"groupId"`
	ArtifactID string `xml:"artifactId"`
	Version    string `xml:"version"`
	Scope      string `xml:"scope"`
	Optional   string `xml:"optional"`
}

type depState struct {
	Version string
	Depth   int
}

type queueItem struct {
	GroupArtifact string
	Version       string
	Depth         int
	ParentNode    *GradleDependencyNode
}

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

// -----------------------------------------------------------------------
// MAIN
// -----------------------------------------------------------------------

func main() {
	// Start the worker pool
	for i := 0; i < pomWorkerCount; i++ {
		wgWorkers.Add(1)
		go pomFetchWorker()
	}

	fmt.Println("Starting dependency analysis...")

	// 1) Find all build.gradle
	files, err := findBuildGradleFiles(".")
	if err != nil {
		fmt.Printf("Error finding build.gradle: %v\n", err)
		os.Exit(1)
	}
	fmt.Printf("Found %d build.gradle file(s).\n", len(files))

	// 2) Parse them into sections
	sections, err := parseAllBuildGradleFiles(files)
	if err != nil {
		fmt.Printf("Error parsing build.gradle files: %v\n", err)
		os.Exit(1)
	}

	// 3) BFS to build the tree + flat map
	fmt.Println("Starting transitive dependency resolution...")
	buildTransitiveClosure(sections)

	// 4) Close the channel and wait for workers
	channelMutex.Lock()
	channelOpen = false
	channelMutex.Unlock()
	close(pomRequests)
	wgWorkers.Wait()

	// 5) Precompute final license info in the flat map
	precomputeLicenseInfo(sections)

	// 6) Compute summary metrics AFTER the license info is updated
	computeSummary(sections)

	// 7) Generate HTML
	fmt.Println("Generating HTML report...")
	if err := generateHTMLReport(sections); err != nil {
		fmt.Printf("Error generating HTML report: %v\n", err)
		os.Exit(1)
	}

	// 8) Print console report
	fmt.Println("Printing console report...")
	printConsoleReport(sections)

	fmt.Println("Analysis complete.")
}

// -----------------------------------------------------------------------
// WORKER POOL
// -----------------------------------------------------------------------

func pomFetchWorker() {
	defer wgWorkers.Done()
	for req := range pomRequests {
		fmt.Printf("Worker: Starting fetch for %s:%s:%s\n", req.GroupID, req.ArtifactID, req.Version)
		pom, err := retrieveOrLoadPOM(req.GroupID, req.ArtifactID, req.Version)
		req.ResultChan <- fetchResult{POM: pom, Err: err}
	}
}

// -----------------------------------------------------------------------
// STEP 1: FIND & PARSE build.gradle
// -----------------------------------------------------------------------

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

func parseAllBuildGradleFiles(files []string) ([]GradleReportSection, error) {
	var sections []GradleReportSection
	for _, f := range files {
		fmt.Printf("Parsing file: %s\n", f)
		deps, err := parseBuildGradleFile(f)
		if err != nil {
			fmt.Printf("Error parsing %s: %v\n", f, err)
			continue
		}
		sections = append(sections, GradleReportSection{
			FilePath:     f,
			Dependencies: deps,
		})
	}
	return sections, nil
}

func parseBuildGradleFile(filePath string) (map[string]ExtendedDepInfo, error) {
	data, err := os.ReadFile(filePath)
	if err != nil {
		return nil, err
	}
	content := string(data)
	varMap := parseVariables(content)

	deps := make(map[string]ExtendedDepInfo)
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
				// variable interpolation
				reVar := regexp.MustCompile(`\$\{([^}]+)\}`)
				version = reVar.ReplaceAllStringFunc(version, func(s string) string {
					inner := s[2 : len(s)-1]
					if val, ok := varMap[inner]; ok {
						return val
					}
					return ""
				})
				if version == "" {
					version = "unknown"
				}
			}
		}
		// Unique key: "group/artifact@version"
		key := fmt.Sprintf("%s@%s", group+"/"+artifact, version)
		deps[key] = ExtendedDepInfo{
			Display: version,
			Lookup:  version,
			Parent:  "direct",
		}
	}
	return deps, nil
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

// -----------------------------------------------------------------------
// STEP 2: BFS + MULTI-LEVEL PARENT
// -----------------------------------------------------------------------

func buildTransitiveClosure(sections []GradleReportSection) {
	for i := range sections {
		sec := &sections[i]
		fmt.Printf("Building transitive closure for %s\n", sec.FilePath)

		stateMap := make(map[string]depState)
		nodeMap := make(map[string]*GradleDependencyNode)
		flatDeps := make(map[string]ExtendedDepInfo)

		// Initialize from direct
		for k, v := range sec.Dependencies {
			flatDeps[k] = v
		}
		var rootNodes []*GradleDependencyNode
		var queue []queueItem
		visitedBFS := make(map[string]bool)

		// BFS queue init
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

		// BFS
		for len(queue) > 0 {
			it := queue[0]
			queue = queue[1:]
			gid, aid := splitGA(it.GroupArtifact)
			if gid == "" || aid == "" {
				continue
			}
			// dynamic version?
			if strings.Contains(it.Version, "${") || strings.ToLower(it.Version) == "unknown" {
				latest, err := getLatestVersion(gid, aid)
				if err != nil {
					fmt.Printf("BFS: Failed to resolve latest version for %s/%s\n", gid, aid)
					it.Version = "unknown"
				} else {
					it.Version = latest
				}
			}
			pom, err := concurrentFetchPOM(gid, aid, it.Version)
			if err != nil || pom == nil {
				continue
			}
			// attach license to the BFS node
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
				curSt, seen := stateMap[childKey]
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
				} else {
					// conflict resolution
					if childDepth < curSt.Depth {
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
		// fill flat map from BFS tree
		for _, rn := range rootNodes {
			fillDepMap(rn, flatDeps)
		}
		sec.Dependencies = flatDeps
		sortRoots(rootNodes)
		sec.DependencyTree = rootNodes

		totalNodes := 0
		for _, rn := range rootNodes {
			totalNodes += countNodes(rn)
		}
		sec.TransitiveCount = totalNodes - len(rootNodes) // basic measure
	}
}

// -----------------------------------------------------------------------
// STEP 3: LICENSE DETECTION
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
	// check if lic is an SPDX ID
	for spdxID, data := range spdxLicenseMap {
		if strings.EqualFold(lic, spdxID) || up == strings.ToUpper(spdxID) {
			return data.Name
		}
	}
	return lic
}

func isCopyleft(name string) bool {
	// check spdxLicenseMap
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

// -----------------------------------------------------------------------
// STEP 4: CONCURRENT POM FETCH & DISK CACHING
// -----------------------------------------------------------------------

func pomFetchWorker() {
	defer wgWorkers.Done()
	for req := range pomRequests {
		pom, err := retrieveOrLoadPOM(req.GroupID, req.ArtifactID, req.Version)
		req.ResultChan <- fetchResult{POM: pom, Err: err}
	}
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
		// channel closed => do direct fetch
		pom, err := fetchRemotePOM(g, a, v)
		if err == nil && pom != nil {
			pomCache.Store(key, pom)
		}
		return pom, err
	}
	resultChan := make(chan fetchResult, 1)
	pomRequests <- fetchRequest{GroupID: g, ArtifactID: a, Version: v, ResultChan: resultChan}
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
	if pom == nil {
		return nil, fmt.Errorf("no POM for %s", key)
	}
	pomCache.Store(key, pom)
	_ = savePOMToDisk(g, a, v, pom)

	// fill group/version from parent if missing
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

// -----------------------------------------------------------------------
// fillDepMap: BFS -> Flat
// -----------------------------------------------------------------------

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
// Precompute license info AFTER BFS
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

			// If version is unknown, mark license unknown
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
// computeSummary: after precomputeLicenseInfo
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
// generateHTMLReport
// -----------------------------------------------------------------------

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
// HELPER
// -----------------------------------------------------------------------

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
