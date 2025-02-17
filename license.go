package main

import (
	"bytes"
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
)

// -------------------------------------------------------------------------------------
// DATA STRUCTURES
// -------------------------------------------------------------------------------------

// GradleDependencyNode represents one node in the dependency tree.
// This is where we store the hierarchy (Transitive children) plus license info, etc.
type GradleDependencyNode struct {
	Name       string                   // e.g. "androidx.appcompat:appcompat" or just "appcompat"
	Version    string                   // e.g. "1.4.2"
	License    string                   // e.g. "Apache-2.0" or "MIT" or "Unknown"
	Details    string                   // e.g. a link to project details
	PomURL     string                   // e.g. a link to the .pom file
	Copyleft   bool                     // true if the license is recognized as copyleft
	Parent     string                   // "direct" if top-level, or "group:artifact:version" if transitive
	Language   string                   // For labeling "Kotlin/Gradle" or similar if needed
	Transitive []*GradleDependencyNode  // children
}

// For tabular display we also keep the older concept of ExtendedDepInfo:
type ExtendedDepInfo struct {
	Display string
	Lookup  string
	Parent  string // "direct" or "group:artifact:version"
}

// GradleReportSection holds data for one build.gradle file
type GradleReportSection struct {
	FilePath       string                                   // path of the build.gradle
	Dependencies   map[string]ExtendedDepInfo               // the old "flat" map of dependencies
	DependencyTree []*GradleDependencyNode                  // new tree-based structure for the same dependencies
	TransitiveCount int                                      // how many are transitive (for stats)
}

// LicenseData is used to return a single object from template funcs
type LicenseData struct {
	LicenseName string
	ProjectURL  string
	PomURL      string
}

// -------------------------------------------------------------------------------------
// STEP 1: FIND AND PARSE DIRECT DEPENDENCIES IN build.gradle FILES
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

// parseVariables scans lines like `def cameraVersion = "1.2.3"`
func parseVariables(content string) map[string]string {
	varMap := make(map[string]string)
	re := regexp.MustCompile(`(?m)^\s*def\s+(\w+)\s*=\s*["']([^"']+)["']`)
	all := re.FindAllStringSubmatch(content, -1)
	for _, m := range all {
		varMap[m[1]] = m[2]
	}
	return varMap
}

// parseBuildGradleFile extracts direct dependencies from a single build.gradle file (flat approach).
func parseBuildGradleFile(filePath string) (map[string]ExtendedDepInfo, error) {
	deps := make(map[string]ExtendedDepInfo)
	data, err := ioutil.ReadFile(filePath)
	if err != nil {
		return nil, err
	}
	content := string(data)
	varMap := parseVariables(content)

	// Regex for lines like: implementation "group:artifact:version"
	re := regexp.MustCompile(`(?m)^\s*(implementation|api|compileOnly|runtimeOnly|testImplementation|androidTestImplementation|classpath)\s+['"]([^'"]+)['"]`)
	all := re.FindAllStringSubmatch(content, -1)
	for _, m := range all {
		depStr := m[2] // e.g. "androidx.appcompat:appcompat:1.4.2"
		parts := strings.Split(depStr, ":")
		if len(parts) < 2 {
			continue
		}
		group := parts[0]
		artifact := parts[1]
		version := "unknown"
		if len(parts) >= 3 {
			version = parts[2]
			// handle version range [x,y)
			if strings.HasPrefix(version, "[") {
				trimmed := strings.Trim(version, "[]")
				toks := strings.Split(trimmed, ",")
				if len(toks) > 0 {
					version = strings.TrimSpace(toks[0])
				}
			}
			// handle variable interpolation
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

// parseAllBuildGradleFiles finds all build.gradle files and gets direct dependencies for each.
func parseAllBuildGradleFiles(files []string) ([]GradleReportSection, error) {
	var sections []GradleReportSection
	for _, f := range files {
		parsedDeps, err := parseBuildGradleFile(f)
		if err != nil {
			fmt.Printf("Error parsing %s: %v\n", f, err)
			continue
		}
		sections = append(sections, GradleReportSection{
			FilePath:     f,
			Dependencies: parsedDeps,
		})
	}
	return sections, nil
}

// -------------------------------------------------------------------------------------
// STEP 2: BFS + RECURSIVE POM PARSING -> Build Tree of GradleDependencyNode
// -------------------------------------------------------------------------------------

// We'll do something akin to "nearest-wins" BFS for each build.gradle's direct dependencies,
// then build a tree of GradleDependencyNodes, linking children to parents.

// We'll keep a global cache of POMs to avoid refetching
var pomCache sync.Map // key = "group:artifact:version" => *MavenPOM

// We'll keep a structure for the POM and relevant bits
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

// BFS state:
type depState struct {
	Version string
	Depth   int
}

// queueItem holds info for BFS plus a pointer to the parent node (so we can attach children).
type queueItem struct {
	GroupArtifact string
	Version       string
	Depth         int
	ParentNode    *GradleDependencyNode
}

// buildTransitiveClosure creates the BFS for each GradleReportSection, constructing a tree.
func buildTransitiveClosure(sections []GradleReportSection) {
	for si := range sections {
		section := &sections[si]
		// We'll build "rootNodes" for direct dependencies
		var rootNodes []*GradleDependencyNode
		stateMap := make(map[string]depState) // track best version & BFS depth
		nodeMap := make(map[string]*GradleDependencyNode) // "group/artifact" -> node

		// Initialize BFS queue with direct dependencies
		var queue []queueItem
		for ga, info := range section.Dependencies {
			// Create a node for the direct dep
			node := &GradleDependencyNode{
				Name:     ga,
				Version:  info.Lookup,
				Parent:   "direct",
				Language: "Gradle",
			}
			rootNodes = append(rootNodes, node)
			nodeMap[ga] = node

			// BFS item
			queue = append(queue, queueItem{
				GroupArtifact: ga,
				Version:       info.Lookup,
				Depth:         1,
				ParentNode:    node, // top-level
			})
			stateMap[ga] = depState{Version: info.Lookup, Depth: 1}
		}

		// BFS
		for len(queue) > 0 {
			it := queue[0]
			queue = queue[1:]

			gid, aid := splitGA(it.GroupArtifact)
			if gid == "" || aid == "" {
				continue
			}
			pom, err := fetchAndParsePOM(gid, aid, it.Version)
			if err != nil {
				continue
			}

			// Attach license info to the node (if not yet attached)
			curNode := it.ParentNode
			if curNode != nil {
				licenseName, projectURL, pomURL := getLicenseInfo(gid, aid, it.Version)
				curNode.License = licenseName
				curNode.Details = projectURL
				curNode.PomURL = pomURL
				curNode.Copyleft = isCopyleft(licenseName)
			}

			managedVersions := parseDependencyManagement(pom)

			// For each child in the POM's dependencies, see if we BFS them
			for _, childDep := range pom.Dependencies {
				if skipDependency(childDep.Scope, childDep.Optional) {
					continue
				}
				childGA := childDep.GroupID + "/" + childDep.ArtifactID
				childVersion := childDep.Version
				if childVersion == "" {
					// check managed
					if mv, ok := managedVersions[childGA]; ok && mv != "" {
						childVersion = mv
					} else {
						childVersion = fallbackVersionFromParent(childDep.GroupID, childDep.ArtifactID, pom)
					}
				}
				if childVersion == "" {
					continue
				}

				childDepth := it.Depth + 1
				curSt, exists := stateMap[childGA]
				if !exists {
					// new
					stateMap[childGA] = depState{Version: childVersion, Depth: childDepth}
					// create child node
					childNode := &GradleDependencyNode{
						Name:     childGA,
						Version:  childVersion,
						Parent:   fmt.Sprintf("%s:%s", it.GroupArtifact, it.Version),
						Language: "Gradle",
					}
					// attach to parent's Transitive slice
					if it.ParentNode != nil {
						it.ParentNode.Transitive = append(it.ParentNode.Transitive, childNode)
					}
					nodeMap[childGA] = childNode

					// enqueue
					queue = append(queue, queueItem{
						GroupArtifact: childGA,
						Version:       childVersion,
						Depth:         childDepth,
						ParentNode:    childNode,
					})
				} else {
					// we've seen this GA
					if childDepth < curSt.Depth {
						// we found a shallower path => override
						stateMap[childGA] = depState{Version: childVersion, Depth: childDepth}
						// we may rebuild the child node or re-link it. For simplicity, we just re-link:
						childNode, ok := nodeMap[childGA]
						if !ok {
							childNode = &GradleDependencyNode{
								Name:     childGA,
								Version:  childVersion,
								Parent:   fmt.Sprintf("%s:%s", it.GroupArtifact, it.Version),
								Language: "Gradle",
							}
							nodeMap[childGA] = childNode
						} else {
							childNode.Version = childVersion
							childNode.Parent = fmt.Sprintf("%s:%s", it.GroupArtifact, it.Version)
						}
						// attach child to parent's Transitive
						if it.ParentNode != nil {
							it.ParentNode.Transitive = append(it.ParentNode.Transitive, childNode)
						}
						// re-enqueue
						queue = append(queue, queueItem{
							GroupArtifact: childGA,
							Version:       childVersion,
							Depth:         childDepth,
							ParentNode:    childNode,
						})
					} else {
						// do nothing, we keep the older, shallower version
					}
				}
			}
		}

		// Sort children by Name for stable output
		sortTreeNodes(rootNodes)

		// Store the final tree in the section
		section.DependencyTree = rootNodes

		// Also fill in "TransitiveCount" for display
		// We can do a quick DFS to count total nodes minus direct
		totalCount := 0
		for _, rn := range rootNodes {
			totalCount += countNodes(rn)
		}
		directCount := len(rootNodes)
		section.TransitiveCount = totalCount - directCount

		// Also fill ExtendedDepInfo from the actual final BFS tree if we want them consistent
		for _, rn := range rootNodes {
			fillExtendedDepMap(rn, section.Dependencies)
		}
	}
}

// skipDependency returns true if scope is test/provided/system or optional is true
func skipDependency(scope, optional string) bool {
	s := strings.ToLower(strings.TrimSpace(scope))
	if s == "test" || s == "provided" || s == "system" {
		return true
	}
	o := strings.ToLower(strings.TrimSpace(optional))
	if o == "true" {
		return true
	}
	return false
}

func parseDependencyManagement(pom *MavenPOM) map[string]string {
	res := make(map[string]string)
	for _, d := range pom.DependencyMgmt.Dependencies {
		if skipDependency(d.Scope, d.Optional) {
			continue
		}
		if d.Version != "" {
			ga := d.GroupID + "/" + d.ArtifactID
			res[ga] = d.Version
		}
	}
	return res
}

func fallbackVersionFromParent(g, a string, pom *MavenPOM) string {
	pg := pom.Parent.GroupID
	pv := pom.Parent.Version
	if g == pom.GroupID && pom.Version != "" {
		return pom.Version
	}
	if g == pg && pv != "" {
		return pv
	}
	return ""
}

func splitGA(ga string) (string, string) {
	parts := strings.Split(ga, "/")
	if len(parts) != 2 {
		return "", ""
	}
	return parts[0], parts[1]
}

// fillExtendedDepMap updates the Dependencies map with final version info from the node tree
func fillExtendedDepMap(node *GradleDependencyNode, depMap map[string]ExtendedDepInfo) {
	key := node.Name
	info, ok := depMap[key]
	if !ok {
		info = ExtendedDepInfo{
			Display: node.Version,
			Lookup:  node.Version,
			Parent:  node.Parent,
		}
	} else {
		info.Display = node.Version
		info.Lookup  = node.Version
		info.Parent  = node.Parent
	}
	depMap[key] = info
	for _, child := range node.Transitive {
		fillExtendedDepMap(child, depMap)
	}
}

func countNodes(root *GradleDependencyNode) int {
	count := 1
	for _, c := range root.Transitive {
		count += countNodes(c)
	}
	return count
}

func sortTreeNodes(nodes []*GradleDependencyNode) {
	// Sort current level
	sort.Slice(nodes, func(i, j int) bool {
		return nodes[i].Name < nodes[j].Name
	})
	// Recursively sort children
	for _, n := range nodes {
		sortTreeNodes(n.Transitive)
	}
}

// -------------------------------------------------------------------------------------
// POM FETCH/CACHE
// -------------------------------------------------------------------------------------

func fetchAndParsePOM(groupID, artifactID, version string) (*MavenPOM, error) {
	key := fmt.Sprintf("%s:%s:%s", groupID, artifactID, version)
	if cached, ok := pomCache.Load(key); ok {
		return cached.(*MavenPOM), nil
	}

	pom, err := retrievePOM(groupID, artifactID, version)
	if err != nil {
		return nil, err
	}

	// fill groupId, version if missing from parent
	if pom.GroupID == "" {
		pom.GroupID = pom.Parent.GroupID
	}
	if pom.Version == "" {
		pom.Version = pom.Parent.Version
	}

	// if there's a parent, retrieve it
	if pom.Parent.GroupID != "" && pom.Parent.ArtifactID != "" && pom.Parent.Version != "" {
		parentKey := fmt.Sprintf("%s:%s:%s", pom.Parent.GroupID, pom.Parent.ArtifactID, pom.Parent.Version)
		var parentPOM *MavenPOM
		if p, ok := pomCache.Load(parentKey); ok {
			parentPOM = p.(*MavenPOM)
		} else {
			parentPOM, _ = retrievePOM(pom.Parent.GroupID, pom.Parent.ArtifactID, pom.Parent.Version)
			if parentPOM != nil {
				pomCache.Store(parentKey, parentPOM)
			}
		}
		if parentPOM != nil {
			// merge <dependencyManagement>
			pom.DependencyMgmt.Dependencies = mergeDepMgmt(parentPOM.DependencyMgmt.Dependencies, pom.DependencyMgmt.Dependencies)
			// if still missing groupId/version, fill from parent
			if pom.GroupID == "" {
				pom.GroupID = parentPOM.GroupID
			}
			if pom.Version == "" {
				pom.Version = parentPOM.Version
			}
		}
	}

	pomCache.Store(key, pom)
	return pom, nil
}

func retrievePOM(groupID, artifactID, version string) (*MavenPOM, error) {
	groupPath := strings.ReplaceAll(groupID, ".", "/")
	centralURL := fmt.Sprintf("https://repo1.maven.org/maven2/%s/%s/%s/%s-%s.pom",
		groupPath, artifactID, version, artifactID, version)
	googleURL := fmt.Sprintf("https://dl.google.com/dl/android/maven2/%s/%s/%s/%s-%s.pom",
		groupPath, artifactID, version, artifactID, version)

	if pom, err := fetchPOMFromURL(centralURL); err == nil {
		return pom, nil
	}
	if pom, err := fetchPOMFromURL(googleURL); err == nil {
		return pom, nil
	}
	return nil, fmt.Errorf("unable to fetch POM for %s:%s:%s", groupID, artifactID, version)
}

func fetchPOMFromURL(url string) (*MavenPOM, error) {
	resp, err := http.Get(url)
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

// -------------------------------------------------------------------------------------
// STEP 3: LICENSE LOOKUP & COPYLEFT DETECTION
// -------------------------------------------------------------------------------------

func getLicenseInfo(groupID, artifactID, version string) (string, string, string) {
	pom, err := fetchAndParsePOM(groupID, artifactID, version)
	if err != nil || pom == nil {
		return "Unknown", fmt.Sprintf("https://www.google.com/search?q=%s+%s+%s+license", groupID, artifactID, version), ""
	}
	groupPath := strings.ReplaceAll(groupID, ".", "/")
	centralURL := fmt.Sprintf("https://repo1.maven.org/maven2/%s/%s/%s/", groupPath, artifactID, version)
	pomURL := fmt.Sprintf("https://repo1.maven.org/maven2/%s/%s/%s/%s-%s.pom", groupPath, artifactID, version, artifactID, version)

	if len(pom.Licenses) > 0 {
		return pom.Licenses[0].Name, centralURL, pomURL
	}
	return "Unknown", centralURL, pomURL
}

func isCopyleft(licenseName string) bool {
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
	up := strings.ToUpper(licenseName)
	for _, kw := range copyleftKeywords {
		if strings.Contains(up, strings.ToUpper(kw)) {
			return true
		}
	}
	return false
}

// A helper function for templates that returns a single object
func getLicenseInfoWrapper(dep, version string) LicenseData {
	parts := strings.Split(dep, "/")
	if len(parts) != 2 {
		return LicenseData{LicenseName: "Unknown"}
	}
	g, a := parts[0], parts[1]
	lic, proj, pom := getLicenseInfo(g, a, version)
	return LicenseData{
		LicenseName: lic,
		ProjectURL:  proj,
		PomURL:      pom,
	}
}

// -------------------------------------------------------------------------------------
// STEP 4: TREE RENDERING TO HTML (<details> / <summary>)
// -------------------------------------------------------------------------------------

// buildGradleTreesHTML renders multiple root nodes (direct dependencies) as separate <details> blocks.
func buildGradleTreesHTML(nodes []*GradleDependencyNode) template.HTML {
	var buf strings.Builder
	for _, node := range nodes {
		html := buildGradleTreeHTML(node, 0)
		buf.WriteString(html)
	}
	return template.HTML(buf.String())
}

// buildGradleTreeHTML recursively builds <details><summary> for the given node and its children.
// We'll add a CSS class for copyleft, unknown, etc. for color-coding in the tree as well.
func buildGradleTreeHTML(node *GradleDependencyNode, level int) string {
	// Decide a CSS class for the license
	class := "non-copyleft"
	if node.License == "Unknown" {
		class = "unknown-license"
	} else if node.Copyleft {
		class = "copyleft"
	}
	// We'll format the summary line as: name@version (License: X)
	summaryLine := fmt.Sprintf("%s@%s (License: %s)", node.Name, node.Version, node.License)

	// Build the <summary> with class
	var sb strings.Builder
	sb.WriteString(fmt.Sprintf(`<details class="%s" style="margin-left:%dem;">`, class, level))
	sb.WriteString(fmt.Sprintf(`<summary>%s</summary>`, template.HTMLEscapeString(summaryLine)))

	// If there's a POM or details link, we can optionally show them in a small line
	if node.PomURL != "" || node.Details != "" {
		sb.WriteString("<div style='margin-left:2em; font-size:0.9em;'>")
		if node.Details != "" {
			sb.WriteString(fmt.Sprintf(`<a href="%s" target="_blank">Project Details</a> &nbsp;`, template.HTMLEscapeString(node.Details)))
		}
		if node.PomURL != "" {
			sb.WriteString(fmt.Sprintf(`<a href="%s" target="_blank">POM File</a>`, template.HTMLEscapeString(node.PomURL)))
		}
		sb.WriteString("</div>")
	}

	// Recursively build children
	for _, child := range node.Transitive {
		sb.WriteString(buildGradleTreeHTML(child, level+1))
	}
	sb.WriteString("</details>")
	return sb.String()
}

// -------------------------------------------------------------------------------------
// STEP 5: HTML REPORT GENERATION
// -------------------------------------------------------------------------------------

func generateHTMLReport(sections []GradleReportSection) error {
	outputDir := "./license-checker"
	if _, err := os.Stat(outputDir); os.IsNotExist(err) {
		if err := os.Mkdir(outputDir, 0755); err != nil {
			return err
		}
	}

	const tmplText = `<!DOCTYPE html>
<html>
<head>
    <meta charset="UTF-8">
    <title>Gradle Dependency Tree Report</title>
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

        /* For the tree: color the <summary> if copyleft, etc. */
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
    <p>This report includes both a table of dependencies and a tree-based view using <code>&lt;details&gt;</code> / <code>&lt;summary&gt;</code> elements.</p>

    {{range .}}
        <h2>File: {{.FilePath}}</h2>
        <p>Total Dependencies Found: {{len .Dependencies}} ({{.TransitiveCount}} transitive)</p>

        <h3>Gradle Dependencies Tree View</h3>
        {{ buildGradleTreesHTML .DependencyTree }}

        <h3>Flat Dependencies Table</h3>
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
                        <td>{{$dep}}</td>
                        <td>{{$info.Display}}</td>
                        <td>{{$licData.LicenseName}}</td>
                        <td>{{$info.Parent}}</td>
                        {{if $licData.ProjectURL}}
                          <td><a href="{{$licData.ProjectURL}}" target="_blank">View Details</a></td>
                        {{else}}
                          <td></td>
                        {{end}}
                        {{if $licData.PomURL}}
                          <td><a href="{{$licData.PomURL}}" target="_blank">View POM</a></td>
                        {{else}}
                          <td></td>
                        {{end}}
                    </tr>
                {{ end }}
            </tbody>
        </table>

    {{end}}
</body>
</html>`

	tmpl, err := template.New("report").Funcs(template.FuncMap{
		"buildGradleTreesHTML": buildGradleTreesHTML,
		"isCopyleft":           isCopyleft,
		"getLicenseInfoWrapper": getLicenseInfoWrapper,
	}).Parse(tmplText)
	if err != nil {
		return err
	}

	reportFile := filepath.Join(outputDir, "dependency-license-report.html")
	f, err := os.Create(reportFile)
	if err != nil {
		return err
	}
	defer f.Close()

	if err := tmpl.Execute(f, sections); err != nil {
		return err
	}

	fmt.Printf("✅ Report generated at %s\n", reportFile)
	return nil
}

// -------------------------------------------------------------------------------------
// MAIN
// -------------------------------------------------------------------------------------

func main() {
	files, err := findBuildGradleFiles(".")
	if err != nil {
		fmt.Printf("Error finding build.gradle files: %v\n", err)
		os.Exit(1)
	}
	fmt.Printf("Found %d build.gradle file(s)\n", len(files))

	sections, err := parseAllBuildGradleFiles(files)
	if err != nil {
		fmt.Printf("Error parsing build.gradle files: %v\n", err)
		os.Exit(1)
	}

	buildTransitiveClosure(sections)

	if err := generateHTMLReport(sections); err != nil {
		fmt.Printf("Error generating HTML report: %v\n", err)
		os.Exit(1)
	}
}
