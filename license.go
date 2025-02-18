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
	localPOMCacheDir = ".pom-cache"      // Directory for disk caching of POMs
	pomWorkerCount   = 10                // Number of worker goroutines
	fetchTimeout     = 30 * time.Second  // HTTP request timeout
)

// -----------------------------------------------------------------------
// GLOBALS
// -----------------------------------------------------------------------

var (
	pomCache    sync.Map // key="group:artifact:version" => *MavenPOM
	parentVisit sync.Map // detect cycles in parent resolution

	// Worker concurrency
	pomRequests = make(chan fetchRequest, 50)
	wgWorkers   sync.WaitGroup

	channelOpen  = true
	channelMutex sync.Mutex

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

// ExtendedDepInfo holds the flat-table data for one dependency.
type ExtendedDepInfo struct {
	Display           string
	Lookup            string
	Parent            string
	License           string
	LicenseProjectURL string
	LicensePomURL     string
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

// GradleReportSection represents one build.gradle's results.
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

// MavenPOM represents the structure of a .pom file.
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

// POMParent is <parent> in a POM.
type POMParent struct {
	GroupID    string `xml:"groupId"`
	ArtifactID string `xml:"artifactId"`
	Version    string `xml:"version"`
}

// POMDep is <dependency> in a POM.
type POMDep struct {
	GroupID    string `xml:"groupId"`
	ArtifactID string `xml:"artifactId"`
	Version    string `xml:"version"`
	Scope      string `xml:"scope"`
	Optional   string `xml:"optional"`
}

// depState holds BFS info
type depState struct {
	Version string
	Depth   int
}

// queueItem is used in BFS queue
type queueItem struct {
	GroupArtifact string
	Version       string
	Depth         int
	ParentNode    *GradleDependencyNode
}

// fetchRequest is used by concurrency
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

// parseVersionRange picks a lower bound if the version looks like "[1.2,2.0)".
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

// skipScope returns true if scope/optional means we skip the dependency.
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

// splitGA splits "group/artifact" into group, artifact.
func splitGA(ga string) (string, string) {
	parts := strings.Split(ga, "/")
	if len(parts) != 2 {
		return "", ""
	}
	return parts[0], parts[1]
}

// parseManagedVersions merges <dependencyManagement> from a POM.
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

// fillDepMap recursively populates the flat map from the BFS tree.
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

// sortRoots sorts the tree nodes.
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

// isCopyleft checks if a given license name is recognized as copyleft.
func isCopyleft(name string) bool {
	for spdxID, data := range spdxLicenseMap {
		if data.Copyleft && (strings.EqualFold(name, data.Name) || strings.EqualFold(name, spdxID)) {
			return true
		}
	}
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

// detectLicense picks the first license name from <licenses> in the POM.
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

// -----------------------------------------------------------------------
// getLatestVersion fetches from Maven Central or Google Maven
// -----------------------------------------------------------------------

func getLatestVersion(g, a string) (string, error) {
	groupPath := strings.ReplaceAll(g, ".", "/")
	mavenURL := fmt.Sprintf("https://repo1.maven.org/maven2/%s/%s/maven-metadata.xml", groupPath, a)
	version, err := fetchLatestVersionFromURL(mavenURL)
	if err == nil && version != "" {
		return version, nil
	}
	googleURL := fmt.Sprintf("https://dl.google.com/dl/android/maven2/%s/%s/maven-metadata.xml", groupPath, a)
	version, err = fetchLatestVersionFromURL(googleURL)
	if err == nil && version != "" {
		return version, nil
	}
	return "", fmt.Errorf("could not resolve version for %s:%s", g, a)
}

func fetchLatestVersionFromURL(url string) (string, error) {
	client := http.Client{Timeout: 15 * time.Second}
	resp, err := client.Get(url)
	if err != nil {
		return "", err
	}
	defer resp.Body.Close()
	if resp.StatusCode != 200 {
		return "", fmt.Errorf("HTTP %d for %s", resp.StatusCode, url)
	}
	data, err := io.ReadAll(resp.Body)
	if err != nil {
		return "", err
	}
	type Versioning struct {
		Latest   string   `xml:"latest"`
		Release  string   `xml:"release"`
		Versions []string `xml:"versions>version"`
	}
	type Metadata struct {
		GroupID    string     `xml:"groupId"`
		ArtifactID string     `xml:"artifactId"`
		Versioning Versioning `xml:"versioning"`
	}
	var md Metadata
	if err := xml.Unmarshal(data, &md); err != nil {
		return "", err
	}
	if md.Versioning.Release != "" {
		return md.Versioning.Release, nil
	}
	if md.Versioning.Latest != "" {
		return md.Versioning.Latest, nil
	}
	if len(md.Versioning.Versions) > 0 {
		return md.Versioning.Versions[len(md.Versioning.Versions)-1], nil
	}
	return "", fmt.Errorf("no version found in metadata at %s", url)
}

// -----------------------------------------------------------------------
// parse build.gradle
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
	data, err := os.ReadFile(filePath)
	if err != nil {
		return nil, err
	}
	content := string(data)
	varMap := parseVariables(content)
	deps := make(map[string]ExtendedDepInfo)

	reDep := regexp.MustCompile(`(?m)^\s*(implementation|api|compileOnly|runtimeOnly|testImplementation|androidTestImplementation|classpath)\s+['"]([^'"]+)['"]`)
	matches := reDep.FindAllStringSubmatch(content, -1)
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
		// Unique key: group/artifact@version
		key := fmt.Sprintf("%s@%s", group+"/"+artifact, version)
		deps[key] = ExtendedDepInfo{
			Display: version,
			Lookup:  version,
			Parent:  "direct",
		}
	}
	return deps, nil
}

func parseAllBuildGradleFiles(files []string) ([]GradleReportSection, error) {
	var sections []GradleReportSection
	for _, f := range files {
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

// -----------------------------------------------------------------------
// BFS & buildTransitiveClosure
// -----------------------------------------------------------------------

func buildTransitiveClosure(sections []GradleReportSection) {
	for i := range sections {
		sec := &sections[i]
		fmt.Printf("Building transitive closure for %s\n", sec.FilePath)
		stateMap := make(map[string]depState)
		nodeMap := make(map[string]*GradleDependencyNode)
		flatDeps := make(map[string]ExtendedDepInfo)

		// copy direct dependencies
		for k, v := range sec.Dependencies {
			flatDeps[k] = v
		}
		var rootNodes []*GradleDependencyNode
		var queue []queueItem
		visited := make(map[string]bool)

		// init BFS
		for depKey, info := range sec.Dependencies {
			visited[depKey] = true
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
			// attach license to BFS node
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
						latest, err2 := getLatestVersion(d.GroupID, d.ArtifactID)
						if err2 != nil {
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
// precomputeLicenseInfo AFTER BFS
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
// computeSummary (AFTER precomputeLicenseInfo)
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
// BUILD TREE HTML
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
      background-color: #ffdddd; padding: 2px 4px; border-radius: 4px;
    }
    details.unknown-license > summary {
      background-color: #ffffdd; padding: 2px 4px; border-radius: 4px;
    }
    details.non-copyleft > summary {
      background-color: #ddffdd; padding: 2px 4px; border-radius: 4px;
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
// WORKER POOL
// -----------------------------------------------------------------------

func pomFetchWorker() {
	defer wgWorkers.Done()
	for req := range pomRequests {
		pom, err := retrieveOrLoadPOM(req.GroupID, req.ArtifactID, req.Version)
		req.ResultChan <- fetchResult{POM: pom, Err: err}
	}
}

// -----------------------------------------------------------------------
// MAIN
// -----------------------------------------------------------------------

func main() {
	// Start worker goroutines
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

	// Mark channel closed, wait for workers to finish
	channelMutex.Lock()
	channelOpen = false
	channelMutex.Unlock()
	close(pomRequests)
	wgWorkers.Wait()

	// Precompute license info after BFS
	precomputeLicenseInfo(sections)

	// Compute summary metrics after license is known
	computeSummary(sections)

	// Generate HTML
	fmt.Println("Generating HTML report...")
	if err := generateHTMLReport(sections); err != nil {
		fmt.Printf("Error generating HTML report: %v\n", err)
		os.Exit(1)
	}

	// Print console
	fmt.Println("Printing console report...")
	printConsoleReport(sections)
	fmt.Println("Analysis complete.")
}
