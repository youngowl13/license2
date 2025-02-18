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
	localPOMCacheDir = ".pom-cache"     // Where to store fetched POMs
	pomWorkerCount   = 10               // Number of concurrent fetch workers
	fetchTimeout     = 30 * time.Second // HTTP GET timeout
)

// -----------------------------------------------------------------------
// GLOBALS
// -----------------------------------------------------------------------

var (
	pomRequests = make(chan fetchRequest, 50)
	wgWorkers   sync.WaitGroup

	pomCache    sync.Map // key="group:artifact:version" => *MavenPOM
	parentVisit sync.Map // detect cycles for parent POM resolution

	channelOpen  = true
	channelMutex sync.Mutex

	// Minimal SPDx => (FriendlyName, Copyleft)
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

type ExtendedDepInfo struct {
	Display           string
	Lookup            string
	Parent            string
	License           string
	LicenseProjectURL string
	LicensePomURL     string
}

type GradleDependencyNode struct {
	Name       string
	Version    string
	License    string
	Copyleft   bool
	Parent     string
	Transitive []*GradleDependencyNode
}

type GradleReportSection struct {
	FilePath        string
	Dependencies    map[string]ExtendedDepInfo
	DependencyTree  []*GradleDependencyNode
	TransitiveCount int
	DirectCount     int
	IndirectCount   int
	CopyleftCount   int
	UnknownCount    int
}

type MavenPOM struct {
	XMLName        xml.Name `xml:"project"`
	Parent         POMParent
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

type POMParent struct {
	GroupID    string `xml:"groupId"`
	ArtifactID string `xml:"artifactId"`
	Version    string `xml:"version"`
}

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
// FIND & PARSE build.gradle
// -----------------------------------------------------------------------

// findBuildGradleFiles scans for files named "build.gradle" (case-insensitive).
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

// parseVariables extracts lines like: def kotlinVersion = "1.6.10"
func parseVariables(content string) map[string]string {
	varMap := make(map[string]string)
	reVar := regexp.MustCompile(`(?m)^\s*def\s+(\w+)\s*=\s*["']([^"']+)["']`)
	all := reVar.FindAllStringSubmatch(content, -1)
	for _, m := range all {
		varMap[m[1]] = m[2]
	}
	return varMap
}

// parseBuildGradleFile reads direct dependencies from one build.gradle
func parseBuildGradleFile(filePath string) (map[string]ExtendedDepInfo, error) {
	data, err := os.ReadFile(filePath)
	if err != nil {
		return nil, err
	}
	content := string(data)
	varMap := parseVariables(content)
	deps := make(map[string]ExtendedDepInfo)

	reDep := regexp.MustCompile(`(?m)^\s*(implementation|api|compileOnly|runtimeOnly|testImplementation|androidTestImplementation|classpath)\s+['"]([^'"]+)['"]`)
	matches := reDep.FindAllStringSubmatch(content, -1)
	for _, sub := range matches {
		depStr := sub[2]
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
				reInter := regexp.MustCompile(`\$\{([^}]+)\}`)
				version = reInter.ReplaceAllStringFunc(version, func(s string) string {
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
		// Unique key => "group/artifact@version"
		key := fmt.Sprintf("%s@%s", group+"/"+artifact, version)
		deps[key] = ExtendedDepInfo{
			Display: version,
			Lookup:  version,
			Parent:  "direct",
		}
	}
	return deps, nil
}

// parseAllBuildGradleFiles processes a list of file paths
func parseAllBuildGradleFiles(paths []string) ([]GradleReportSection, error) {
	var sections []GradleReportSection
	for _, f := range paths {
		fmt.Printf("Parsing file: %s\n", f)
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

// parseVersionRange picks a lower bound if version is [1.2,2.0)
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
// BFS
// -----------------------------------------------------------------------

func buildTransitiveClosure(sections []GradleReportSection) {
	for i := range sections {
		sec := &sections[i]
		fmt.Printf("BFS: Starting for %s\n", sec.FilePath)

		stateMap := make(map[string]depState)
		nodeMap := make(map[string]*GradleDependencyNode)
		flatDeps := make(map[string]ExtendedDepInfo)

		for k, v := range sec.Dependencies {
			flatDeps[k] = v
		}

		var roots []*GradleDependencyNode
		var queue []queueItem
		visited := make(map[string]bool)

		// BFS init from direct
		for depKey, info := range sec.Dependencies {
			visited[depKey] = true
			parts := strings.Split(depKey, "@")
			if len(parts) != 2 {
				continue
			}
			ga := parts[0]
			node := &GradleDependencyNode{
				Name:    ga,
				Version: info.Lookup,
				Parent:  "direct",
			}
			roots = append(roots, node)
			nodeMap[depKey] = node
			stateMap[depKey] = depState{Version: info.Lookup, Depth: 1}
			queue = append(queue, queueItem{
				GroupArtifact: ga,
				Version:       info.Lookup,
				Depth:         1,
				ParentNode:    node,
			})
		}

		for len(queue) > 0 {
			it := queue[0]
			queue = queue[1:]
			gid, aid := splitGA(it.GroupArtifact)
			if gid == "" || aid == "" {
				continue
			}
			// dynamic version if unknown
			if strings.ToLower(it.Version) == "unknown" || strings.Contains(it.Version, "${") {
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
				lic := detectLicense(pom)
				it.ParentNode.License = lic
				it.ParentNode.Copyleft = isCopyleft(lic)
			}
			// parseManaged
			man := parseManagedVersions(pom)
			for _, d := range pom.Dependencies {
				if skipScope(d.Scope, d.Optional) {
					continue
				}
				childGA := d.GroupID + "/" + d.ArtifactID
				cv := parseVersionRange(d.Version)
				if cv == "" || strings.Contains(cv, "${") {
					if mv, ok := man[childGA]; ok && mv != "" {
						cv = mv
					} else {
						latest, e2 := getLatestVersion(d.GroupID, d.ArtifactID)
						if e2 != nil {
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
				if _, found := visited[childKey]; found {
					continue
				}
				visited[childKey] = true
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
		for _, root := range roots {
			fillDepMap(root, flatDeps)
		}
		sec.Dependencies = flatDeps
		sortRoots(roots)
		sec.DependencyTree = roots

		// compute total BFS nodes
		totalNodes := 0
		for _, r := range roots {
			totalNodes += countNodes(r)
		}
		directCount := 0
		for k, inf := range sec.Dependencies {
			if inf.Parent == "direct" || strings.HasSuffix(k, "@unknown") {
				directCount++
			}
		}
		sec.TransitiveCount = totalNodes - directCount
	}
}

// -----------------------------------------------------------------------
// POM & DISK
// -----------------------------------------------------------------------

func retrieveOrLoadPOM(g, a, v string) (*MavenPOM, error) {
	key := fmt.Sprintf("%s:%s:%s", g, a, v)
	if c, ok := pomCache.Load(key); ok {
		return c.(*MavenPOM), nil
	}
	pom, err := loadPOMFromDisk(g, a, v)
	if err == nil && pom != nil {
		pomCache.Store(key, pom)
	} else {
		pom, err = fetchRemotePOM(g, a, v)
		if err != nil {
			return nil, err
		}
		pomCache.Store(key, pom)
		_ = savePOMToDisk(g, a, v, pom)
	}
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

func fetchRemotePOM(g, a, v string) (*MavenPOM, error) {
	groupPath := strings.ReplaceAll(g, ".", "/")
	urlCentral := fmt.Sprintf("https://repo1.maven.org/maven2/%s/%s/%s/%s-%s.pom",
		groupPath, a, v, a, v)
	urlGoogle := fmt.Sprintf("https://dl.google.com/dl/android/maven2/%s/%s/%s/%s-%s.pom",
		groupPath, a, v, a, v)
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
	if e2 := dec.Decode(&pom); e2 != nil {
		return nil, e2
	}
	return &pom, nil
}

func loadAllParents(p *MavenPOM, depth int) error {
	if p.Parent.GroupID == "" || p.Parent.ArtifactID == "" || p.Parent.Version == "" {
		return nil
	}
	pkey := fmt.Sprintf("%s:%s:%s", p.Parent.GroupID, p.Parent.ArtifactID, p.Parent.Version)
	if _, visited := parentVisit.Load(pkey); visited {
		return fmt.Errorf("cycle: %s", pkey)
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

func mergeDepMgmt(parent, child []POMDep) []POMDep {
	out := make(map[string]POMDep)
	for _, d := range parent {
		key := d.GroupID + ":" + d.ArtifactID
		out[key] = d
	}
	for _, d := range child {
		key := d.GroupID + ":" + d.ArtifactID
		out[key] = d
	}
	var merged []POMDep
	for _, val := range out {
		merged = append(merged, val)
	}
	sort.Slice(merged, func(i, j int) bool {
		return merged[i].GroupID < merged[j].GroupID
	})
	return merged
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
	if e2 := dec.Decode(&pom); e2 != nil {
		return nil, e2
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
// STEP 3: PRECOMPUTE LICENSE INFO
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
			gaParts := strings.Split(ga, "/")
			if len(gaParts) != 2 {
				continue
			}
			g, a := gaParts[0], gaParts[1]
			if strings.ToLower(info.Lookup) == "unknown" || strings.Contains(info.Lookup, "${") {
				info.License = "Unknown"
				info.LicenseProjectURL = fmt.Sprintf("https://www.google.com/search?q=%s+%s+license", g, a)
				info.LicensePomURL = ""
			} else {
				pom, err := concurrentFetchPOM(g, a, info.Lookup)
				if err != nil || pom == nil {
					info.License = "Unknown"
					info.LicenseProjectURL = fmt.Sprintf("https://www.google.com/search?q=%s+%s+%s+license", g, a, info.Lookup)
					info.LicensePomURL = ""
				} else {
					lic := detectLicense(pom)
					info.License = lic
					groupPath := strings.ReplaceAll(g, ".", "/")
					info.LicenseProjectURL = fmt.Sprintf("https://repo1.maven.org/maven2/%s/%s/%s/", groupPath, a, info.Lookup)
					info.LicensePomURL = fmt.Sprintf("https://repo1.maven.org/maven2/%s/%s/%s/%s-%s.pom",
						groupPath, a, info.Lookup, a, info.Lookup)
				}
			}
			sec.Dependencies[depKey] = info
		}
	}
}

// -----------------------------------------------------------------------
// STEP 4: GENERATE HTML REPORT
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
	const tmplSrc = `<!DOCTYPE html>
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
		"isCopyleft":           isCopyleft,
		"buildGradleTreesHTML": buildGradleTreesHTML,
	}).Parse(tmplSrc)
	if err != nil {
		return err
	}
	outPath := filepath.Join(outDir, "dependency-license-report.html")
	f, err := os.Create(outPath)
	if err != nil {
		return err
	}
	defer f.Close()
	if err := tmpl.Execute(f, sections); err != nil {
		return err
	}
	fmt.Printf("✅ License report generated at %s\n", outPath)
	return nil
}

// -----------------------------------------------------------------------
// CONSOLE REPORT
// -----------------------------------------------------------------------

func printConsoleReport(sections []GradleReportSection) {
	fmt.Println("----- Console Dependency Report -----")
	for _, sec := range sections {
		fmt.Printf("File: %s\n", sec.FilePath)
		fmt.Printf("Direct: %d, Indirect: %d, Copyleft: %d, Unknown: %d\n",
			sec.DirectCount, sec.IndirectCount, sec.CopyleftCount, sec.UnknownCount)

		fmt.Println("Flat Dependencies:")
		var keys []string
		for k := range sec.Dependencies {
			keys = append(keys, k)
		}
		sort.Strings(keys)
		for _, k := range keys {
			info := sec.Dependencies[k]
			fmt.Printf("  %s -> %s (Parent=%s, License=%s)\n",
				k, info.Display, info.Parent, info.License)
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
// MAIN
// -----------------------------------------------------------------------

func main() {
	// start concurrency pool
	for i := 0; i < pomWorkerCount; i++ {
		wgWorkers.Add(1)
		go pomFetchWorker()
	}

	fmt.Println("Starting dependency analysis...")

	// Step 1: find build.gradle
	files, err := findBuildGradleFiles(".")
	if err != nil {
		fmt.Printf("Error scanning for build.gradle files: %v\n", err)
		os.Exit(1)
	}
	fmt.Printf("Found %d build.gradle file(s).\n", len(files))

	// Step 2: parse direct dependencies
	sections, err := parseAllBuildGradleFiles(files)
	if err != nil {
		fmt.Printf("Error parsing build.gradle: %v\n", err)
		os.Exit(1)
	}

	// Step 3: BFS => transitive
	fmt.Println("Starting transitive dependency resolution...")
	buildTransitiveClosure(sections)

	// close channel, wait for concurrency
	channelMutex.Lock()
	channelOpen = false
	channelMutex.Unlock()
	close(pomRequests)
	wgWorkers.Wait()

	// Step 4: precompute license in the final flat map
	fmt.Println("Precomputing license info after BFS...")
	precomputeLicenseInfo(sections)

	// Step 5: compute final summary
	for idx := range sections {
		sec := &sections[idx]
		var directCount, indirectCount, copyleftCount, unknownCount int
		for _, info := range sec.Dependencies {
			if info.Parent == "direct" || strings.HasSuffix(info.Lookup, "unknown") {
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

	// Step 6: generate HTML
	fmt.Println("Generating HTML report...")
	if err := generateHTMLReport(sections); err != nil {
		fmt.Printf("Error generating HTML: %v\n", err)
		os.Exit(1)
	}

	// Step 7: print console
	fmt.Println("Printing console report...")
	printConsoleReport(sections)
	fmt.Println("Analysis complete.")
}
