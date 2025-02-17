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
// Data Structures
// -------------------------------------------------------------------------------------

// DepVersion holds two version strings:
// - Display: shown in the report's Version column
// - Lookup:  used for POM/License fetching
type DepVersion struct {
    Display string
    Lookup  string
}

// ExtendedDepInfo holds the dependency + its immediate parent (for the final HTML report).
// - Parent = "direct" if declared in build.gradle
// - Parent = "group:artifact:version" if discovered transitively
type ExtendedDepInfo struct {
    DepVersion
    Parent string
}

// License represents the license details from a POM file.
type License struct {
    Name string `xml:"name"`
    URL  string `xml:"url"`
}

// MavenPOM represents the structure of a Maven POM file. We parse just the essential parts.
type MavenPOM struct {
    XMLName            xml.Name       `xml:"project"`
    Parent             POMParent      `xml:"parent"`
    DependencyMgmt     POMDepMgmt     `xml:"dependencyManagement"`
    Dependencies       []POMDep       `xml:"dependencies>dependency"`
    Licenses           []License      `xml:"licenses>license"`
    GroupID            string         `xml:"groupId"`
    ArtifactID         string         `xml:"artifactId"`
    Version            string         `xml:"version"`
}

// POMParent holds <parent> info if present (for inheritance).
type POMParent struct {
    GroupID    string `xml:"groupId"`
    ArtifactID string `xml:"artifactId"`
    Version    string `xml:"version"`
}

// POMDepMgmt holds a <dependencyManagement> section, which can have its own <dependencies>.
type POMDepMgmt struct {
    Dependencies []POMDep `xml:"dependencies>dependency"`
}

// POMDep is a minimal struct for each <dependency> in <dependencies> or <dependencyManagement>.
type POMDep struct {
    GroupID    string `xml:"groupId"`
    ArtifactID string `xml:"artifactId"`
    Version    string `xml:"version"`
    Scope      string `xml:"scope"`
    Optional   string `xml:"optional"`
}

// GradleReportSection holds data for one build.gradle file:
// - FilePath for reference
// - Dependencies map: key="group/artifact", value=ExtendedDepInfo
// - TransitiveCount for display
type GradleReportSection struct {
    FilePath        string
    Dependencies    map[string]ExtendedDepInfo
    TransitiveCount int
}

// We define a struct to carry final license info for template usage.
type LicenseData struct {
    LicenseName string
    ProjectURL  string
    PomURL      string
}

// -------------------------------------------------------------------------------------
// Step 1: Find and Parse Direct Dependencies from build.gradle
// -------------------------------------------------------------------------------------

// findBuildGradleFiles finds all "build.gradle" files (case-insensitive) under root.
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
    if err != nil {
        return nil, err
    }
    return files, nil
}

// parseVariables scans for variable definitions like: def cameraVersion = "1.2.3"
func parseVariables(content string) map[string]string {
    varMap := make(map[string]string)
    re := regexp.MustCompile(`(?m)^\s*def\s+(\w+)\s*=\s*["']([^"']+)["']`)
    matches := re.FindAllStringSubmatch(content, -1)
    for _, match := range matches {
        varMap[match[1]] = match[2]
    }
    return varMap
}

// parseBuildGradleFile extracts direct dependencies from a single build.gradle file.
func parseBuildGradleFile(filePath string) (map[string]DepVersion, error) {
    deps := make(map[string]DepVersion)
    contentBytes, err := ioutil.ReadFile(filePath)
    if err != nil {
        return nil, fmt.Errorf("cannot read file %s: %v", filePath, err)
    }
    content := string(contentBytes)
    varMap := parseVariables(content)

    // Regex for e.g. implementation "group:artifact:version"
    re := regexp.MustCompile(`(?m)^\s*(implementation|api|compileOnly|runtimeOnly|testImplementation|androidTestImplementation|classpath)\s+['"]([^'"]+)['"]`)
    matches := re.FindAllStringSubmatch(content, -1)
    for _, match := range matches {
        depStr := match[2] // e.g. "androidx.appcompat:appcompat:1.4.2"
        parts := strings.Split(depStr, ":")
        if len(parts) < 2 {
            continue
        }
        group := parts[0]
        artifact := parts[1]
        var version string
        if len(parts) >= 3 {
            version = parts[2]
            // handle version range [1.0,2.0)
            if strings.HasPrefix(version, "[") {
                trimmed := strings.Trim(version, "[]")
                tokens := strings.Split(trimmed, ",")
                if len(tokens) > 0 {
                    version = strings.TrimSpace(tokens[0])
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
        if version == "" {
            version = "unknown"
        }
        key := group + "/" + artifact
        if _, exists := deps[key]; !exists {
            deps[key] = DepVersion{
                Display: version,
                Lookup:  version,
            }
        }
    }
    return deps, nil
}

// parseAllBuildGradleFiles returns a slice of GradleReportSection with direct dependencies.
func parseAllBuildGradleFiles(files []string) ([]GradleReportSection, error) {
    var sections []GradleReportSection
    for _, f := range files {
        directDeps, err := parseBuildGradleFile(f)
        if err != nil {
            fmt.Printf("Error parsing %s: %v\n", f, err)
            continue
        }
        depMap := make(map[string]ExtendedDepInfo)
        for k, v := range directDeps {
            depMap[k] = ExtendedDepInfo{
                DepVersion: v,
                Parent:     "direct",
            }
        }
        sections = append(sections, GradleReportSection{
            FilePath:     f,
            Dependencies: depMap,
        })
    }
    return sections, nil
}

// -------------------------------------------------------------------------------------
// Step 2: BFS-Based Transitive Dependency Resolution with "Nearest Wins" & Parent POM Support
// -------------------------------------------------------------------------------------

// We'll maintain a global lock-free cache for POM retrieval
var pomCache sync.Map // key = "group:artifact:version" => *MavenPOM

// DepState tracks the chosen version & depth for each "group/artifact" we’ve encountered.
type DepState struct {
    Version string // final chosen version
    Depth   int    // BFS depth (1 = direct, 2 = child of direct, etc.)
}

// We'll store our BFS queue items here
type queueItem struct {
    GroupArtifact string // e.g. "androidx.appcompat/appcompat"
    Version       string // e.g. "1.4.2"
    Depth         int    // BFS depth
    ParentGAV     string // immediate parent's "g:a:v" or "direct"
}

func buildTransitiveClosure(sections []GradleReportSection) {
    for i := range sections {
        // We'll do BFS for each build.gradle’s direct dependencies
        stateMap := make(map[string]DepState) // track best version & depth for each group/artifact
        var queue []queueItem

        // Initialize queue with direct dependencies
        for depKey, info := range sections[i].Dependencies {
            q := queueItem{
                GroupArtifact: depKey,
                Version:       info.Lookup,
                Depth:         1,
                ParentGAV:     "direct",
            }
            stateMap[depKey] = DepState{Version: info.Lookup, Depth: 1}
            queue = append(queue, q)
        }

        // BFS loop
        for len(queue) > 0 {
            // pop front
            item := queue[0]
            queue = queue[1:]

            gid, aid := splitGA(item.GroupArtifact)
            if gid == "" || aid == "" {
                continue
            }

            // fetch POM
            pom, err := fetchAndParsePOM(gid, aid, item.Version)
            if err != nil {
                // skip
                continue
            }

            // gather managedVersions from <dependencyManagement> if present
            managedVersions := parseManagedVersions(pom)

            // For each child <dependency>, see if we should add it to BFS
            for _, childDep := range pom.Dependencies {
                if skipDependency(childDep.Scope, childDep.Optional) {
                    continue
                }
                childGA := childDep.GroupID + "/" + childDep.ArtifactID
                childVersion := childDep.Version
                // if childVersion is missing, check <dependencyManagement>
                if childVersion == "" {
                    if mv, ok := managedVersions[childGA]; ok && mv != "" {
                        childVersion = mv
                    }
                }
                // if STILL empty, try parent's groupId/version if the child uses placeholders
                if childVersion == "" {
                    childVersion = fallbackVersionFromParent(childDep.GroupID, childDep.ArtifactID, pom)
                }
                if childVersion == "" {
                    continue // no version found
                }

                // Now apply "nearest-wins" version conflict resolution
                childDepth := item.Depth + 1
                curState, exists := stateMap[childGA]
                if !exists {
                    // Not seen yet => store & enqueue
                    stateMap[childGA] = DepState{Version: childVersion, Depth: childDepth}
                    queue = append(queue, queueItem{
                        GroupArtifact: childGA,
                        Version:       childVersion,
                        Depth:         childDepth,
                        ParentGAV:     fmt.Sprintf("%s:%s", item.GroupArtifact, item.Version),
                    })
                } else {
                    // We have seen this GA. If we discovered a shallower path, we override & re-queue
                    if childDepth < curState.Depth {
                        // override
                        stateMap[childGA] = DepState{Version: childVersion, Depth: childDepth}
                        queue = append(queue, queueItem{
                            GroupArtifact: childGA,
                            Version:       childVersion,
                            Depth:         childDepth,
                            ParentGAV:     fmt.Sprintf("%s:%s", item.GroupArtifact, item.Version),
                        })
                    }
                }
            }
        }

        // After BFS completes, we have final version for each GA. We'll store them in a local map while also
        // reconstructing immediate parent references. We'll do a second BFS pass to fill in the "Parent" fields.

        depMap := make(map[string]ExtendedDepInfo)
        var queue2 []queueItem
        visited2 := make(map[string]bool)

        // Initialize from direct
        for depKey, info := range sections[i].Dependencies {
            depMap[depKey] = ExtendedDepInfo{
                DepVersion: info.DepVersion,
                Parent:     "direct",
            }
            queue2 = append(queue2, queueItem{
                GroupArtifact: depKey,
                Version:       info.Lookup,
                Depth:         1,
                ParentGAV:     "direct",
            })
            visited2[fmt.Sprintf("%s@%s", depKey, info.Lookup)] = true
        }

        for len(queue2) > 0 {
            it := queue2[0]
            queue2 = queue2[1:]

            gid, aid := splitGA(it.GroupArtifact)
            pom, err := fetchAndParsePOM(gid, aid, it.Version)
            if err != nil {
                continue
            }

            managedVersions := parseManagedVersions(pom)
            for _, cd := range pom.Dependencies {
                if skipDependency(cd.Scope, cd.Optional) {
                    continue
                }
                childGA := cd.GroupID + "/" + cd.ArtifactID
                // final version from BFS
                childVersion := cd.Version
                if childVersion == "" {
                    if mv, ok := managedVersions[childGA]; ok && mv != "" {
                        childVersion = mv
                    } else {
                        childVersion = fallbackVersionFromParent(cd.GroupID, cd.ArtifactID, pom)
                    }
                }
                if childVersion == "" {
                    continue
                }
                // see if BFS decided on a different version
                final := stateMap[childGA]
                if final.Version == "" {
                    continue
                }
                if final.Version != childVersion {
                    childVersion = final.Version
                }
                key := childGA

                // If not in depMap, add it with a parent reference
                if _, exists := depMap[key]; !exists {
                    depMap[key] = ExtendedDepInfo{
                        DepVersion: DepVersion{
                            Display: childVersion,
                            Lookup:  childVersion,
                        },
                        Parent: fmt.Sprintf("%s:%s", it.GroupArtifact, it.Version),
                    }
                }

                // If not visited, enqueue
                visitKey := fmt.Sprintf("%s@%s", key, childVersion)
                if !visited2[visitKey] {
                    visited2[visitKey] = true
                    queue2 = append(queue2, queueItem{
                        GroupArtifact: key,
                        Version:       childVersion,
                        Depth:         it.Depth + 1,
                        ParentGAV:     fmt.Sprintf("%s:%s", it.GroupArtifact, it.Version),
                    })
                }
            }
        }

        // Now merge depMap back into sections[i].Dependencies
        for k, v := range depMap {
            sections[i].Dependencies[k] = v
        }

        // Calculate how many are transitive
        directCount := 0
        for _, v := range sections[i].Dependencies {
            if v.Parent == "direct" {
                directCount++
            }
        }
        sections[i].TransitiveCount = len(sections[i].Dependencies) - directCount
    }
}

// skipDependency returns true if we should skip test/provided/optional dependencies.
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

// parseManagedVersions creates a map of "group/artifact" -> version from <dependencyManagement>.
func parseManagedVersions(pom *MavenPOM) map[string]string {
    result := make(map[string]string)
    for _, d := range pom.DependencyMgmt.Dependencies {
        if skipDependency(d.Scope, d.Optional) {
            continue
        }
        if d.Version == "" {
            continue
        }
        ga := d.GroupID + "/" + d.ArtifactID
        result[ga] = d.Version
    }
    return result
}

// fallbackVersionFromParent tries to see if the child matches the POM’s <groupId> or the parent's groupId
// if the child simply omitted <version>. This is very naive parent inheritance logic.
func fallbackVersionFromParent(childGroup, childArtifact string, pom *MavenPOM) string {
    parentGroup := pom.Parent.GroupID
    parentVersion := pom.Parent.Version

    if childGroup == pom.GroupID && pom.Version != "" {
        return pom.Version
    }
    if childGroup == parentGroup && parentVersion != "" {
        return parentVersion
    }
    return ""
}

// splitGA splits "group/artifact" into (group, artifact).
func splitGA(ga string) (string, string) {
    parts := strings.Split(ga, "/")
    if len(parts) != 2 {
        return "", ""
    }
    return parts[0], parts[1]
}

// -------------------------------------------------------------------------------------
// POM Fetching and Caching
// -------------------------------------------------------------------------------------

// fetchAndParsePOM fetches the POM from either Maven Central or Google, plus checks <parent> if needed.
func fetchAndParsePOM(groupID, artifactID, version string) (*MavenPOM, error) {
    // If we have it in cache, return
    key := fmt.Sprintf("%s:%s:%s", groupID, artifactID, version)
    if cached, ok := pomCache.Load(key); ok {
        return cached.(*MavenPOM), nil
    }

    pom, err := retrievePOM(groupID, artifactID, version)
    if err != nil {
        return nil, err
    }

    // Attempt to fill the local groupId/version from <parent> if missing
    if pom.GroupID == "" {
        pom.GroupID = pom.Parent.GroupID
    }
    if pom.Version == "" {
        pom.Version = pom.Parent.Version
    }

    // If the POM has a parent, we parse that parent's POM for <dependencyManagement> too.
    // Then we can merge. This is a partial approach.
    if pom.Parent.GroupID != "" && pom.Parent.ArtifactID != "" && pom.Parent.Version != "" {
        parentKey := fmt.Sprintf("%s:%s:%s", pom.Parent.GroupID, pom.Parent.ArtifactID, pom.Parent.Version)
        parentPOM, ok := pomCache.Load(parentKey)
        var parent *MavenPOM
        if !ok {
            // fetch parent's POM
            parent, _ = retrievePOM(pom.Parent.GroupID, pom.Parent.ArtifactID, pom.Parent.Version)
            if parent != nil {
                // store
                pomCache.Store(parentKey, parent)
            }
        } else {
            parent = parentPOM.(*MavenPOM)
        }
        // If we found a parent, merge parent's <dependencyManagement> into this POM's <dependencyManagement>
        if parent != nil {
            pom.DependencyMgmt.Dependencies = mergeDepMgmt(parent.DependencyMgmt.Dependencies, pom.DependencyMgmt.Dependencies)
            // If after that we still have no groupId, version, use parent's
            if pom.GroupID == "" {
                pom.GroupID = parent.GroupID
            }
            if pom.Version == "" {
                pom.Version = parent.Version
            }
        }
    }

    pomCache.Store(key, pom)
    return pom, nil
}

// retrievePOM tries Maven Central then Google Maven
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

// fetchPOMFromURL fetches and unmarshals a Maven POM from a given URL
func fetchPOMFromURL(url string) (*MavenPOM, error) {
    resp, err := http.Get(url)
    if err != nil {
        return nil, fmt.Errorf("GET error for %s: %v", url, err)
    }
    defer resp.Body.Close()
    if resp.StatusCode != http.StatusOK {
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
        return nil, fmt.Errorf("XML decode error: %v", err)
    }
    return &pom, nil
}

// mergeDepMgmt merges parent's <dependencyManagement> entries with child's. Child entries override parent's if same G/A.
func mergeDepMgmt(parent, child []POMDep) []POMDep {
    // build a map from parent's
    outMap := make(map[string]POMDep)
    for _, d := range parent {
        key := d.GroupID + ":" + d.ArtifactID
        outMap[key] = d
    }
    // child overrides
    for _, d := range child {
        key := d.GroupID + ":" + d.ArtifactID
        outMap[key] = d
    }
    // convert back to slice
    var merged []POMDep
    for _, val := range outMap {
        merged = append(merged, val)
    }
    // sort for stable output
    sort.Slice(merged, func(i, j int) bool {
        return merged[i].GroupID < merged[j].GroupID
    })
    return merged
}

// -------------------------------------------------------------------------------------
// Step 3: License Lookup & Copyleft
// -------------------------------------------------------------------------------------

// getLicenseInfo returns (licenseName, projectURL, POMFileURL).
func getLicenseInfo(groupID, artifactID, version string) (string, string, string) {
    // Try to fetch the POM (cached or live). If fail => unknown
    pom, err := fetchAndParsePOM(groupID, artifactID, version)
    if err != nil || pom == nil {
        return "Unknown", fmt.Sprintf("https://www.google.com/search?q=%s+%s+%s+license", groupID, artifactID, version), ""
    }
    // We'll guess that the best "project URL" is the location from Maven Central if found.
    groupPath := strings.ReplaceAll(groupID, ".", "/")
    centralURL := fmt.Sprintf("https://repo1.maven.org/maven2/%s/%s/%s/", groupPath, artifactID, version)
    pomURL := fmt.Sprintf("https://repo1.maven.org/maven2/%s/%s/%s/%s-%s.pom",
        groupPath, artifactID, version, artifactID, version)

    licenseName := "Unknown"
    if len(pom.Licenses) > 0 {
        licenseName = pom.Licenses[0].Name
    }
    return licenseName, centralURL, pomURL
}

// isCopyleft checks for known copyleft license keywords
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

// getLicenseInfoWrapper returns a single struct for template usage
func getLicenseInfoWrapper(dep, version string) LicenseData {
    parts := strings.Split(dep, "/")
    if len(parts) != 2 {
        return LicenseData{LicenseName: "Unknown"}
    }
    g, a := parts[0], parts[1]
    licName, projURL, pomURL := getLicenseInfo(g, a, version)
    return LicenseData{
        LicenseName: licName,
        ProjectURL:  projURL,
        PomURL:      pomURL,
    }
}

// -------------------------------------------------------------------------------------
// Step 4: HTML Report
// -------------------------------------------------------------------------------------

func generateHTMLReport(sections []GradleReportSection) error {
    outputDir := "./license-checker"
    if _, err := os.Stat(outputDir); os.IsNotExist(err) {
        if err := os.Mkdir(outputDir, 0755); err != nil {
            return fmt.Errorf("error creating output directory: %v", err)
        }
    }

    const tmplText = `<!DOCTYPE html>
<html>
<head>
    <meta charset="UTF-8">
    <title>Kotlin Dependency License Report</title>
    <style>
        body { font-family: Arial, sans-serif; margin: 20px; }
        h1 { color: #2c3e50; }
        h2 { color: #34495e; margin-top: 40px; }
        table { width: 100%; border-collapse: collapse; margin-bottom: 40px; }
        th, td { border: 1px solid #ddd; padding: 8px; text-align: left; }
        th { background-color: #f2f2f2; }
        tr:nth-child(even) { background-color: #f9f9f9; }
        a { color: #3498db; text-decoration: none; }
        a:hover { text-decoration: underline; }
        tr.copyleft { background-color: #ffdddd; }
        tr.non-copyleft { background-color: #ddffdd; }
        tr.unknown-license { background-color: #ffffdd; }
        .small { color: #666; font-size: 0.9em; }
    </style>
</head>
<body>
    <h1>Kotlin Dependency License Report (Recursive POM Parsing + Parent Inheritance + Nearest-Wins)</h1>

    <p class="small">This report includes version conflict resolution (nearest-wins) & parent POM inheritance 
       for missing dependency versions. Test/optional/provided dependencies are skipped. 
       We do not handle custom repositories or advanced parent inheritance beyond the immediate parent. 
       Real Maven/Gradle logic is more complex.</p>

    {{range .}}
        <h2>File: {{.FilePath}}</h2>
        <p>Total Dependencies Found: {{len .Dependencies}} 
           ({{.TransitiveCount}} transitive)</p>
        <table>
            <thead>
                <tr>
                    <th>Dependency (group/artifact)</th>
                    <th>Version</th>
                    <th>License</th>
                    <th>Parent</th>
                    <th>Project Details</th>
                    <th>POM File</th>
                </tr>
            </thead>
            <tbody>
                {{range $dep, $info := .Dependencies}}
                {{ $licenseData := getLicenseInfoWrapper $dep $info.Lookup }}
                {{ if eq $licenseData.LicenseName "Unknown" }}
                    <tr class="unknown-license">
                {{ else if isCopyleft $licenseData.LicenseName }}
                    <tr class="copyleft">
                {{ else }}
                    <tr class="non-copyleft">
                {{ end }}
                    <td>{{$dep}}</td>
                    <td>{{$info.Display}}</td>
                    <td>{{$licenseData.LicenseName}}</td>
                    <td>{{$info.Parent}}</td>
                    {{if $licenseData.ProjectURL}}
                        <td><a href="{{$licenseData.ProjectURL}}" target="_blank">View Details</a></td>
                    {{else}}
                        <td></td>
                    {{end}}
                    {{if $licenseData.PomURL}}
                        <td><a href="{{$licenseData.PomURL}}" target="_blank">View POM</a></td>
                    {{else}}
                        <td></td>
                    {{end}}
                </tr>
                {{end}}
            </tbody>
        </table>
    {{end}}
</body>
</html>`

    tmpl, err := template.New("report").Funcs(template.FuncMap{
        "getLicenseInfoWrapper": getLicenseInfoWrapper,
        "isCopyleft":            isCopyleft,
    }).Parse(tmplText)
    if err != nil {
        return fmt.Errorf("template parse error: %v", err)
    }

    reportPath := filepath.Join(outputDir, "dependency-license-report.html")
    file, err := os.Create(reportPath)
    if err != nil {
        return fmt.Errorf("error creating report file: %v", err)
    }
    defer file.Close()

    if err := tmpl.Execute(file, sections); err != nil {
        return fmt.Errorf("error executing template: %v", err)
    }

    fmt.Printf("✅ License report generated at %s\n", reportPath)
    return nil
}

// -------------------------------------------------------------------------------------
// main()
// -------------------------------------------------------------------------------------

func main() {
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

    // Build the full transitive closure with BFS + nearest-wins + parent POM logic
    buildTransitiveClosure(sections)

    if err := generateHTMLReport(sections); err != nil {
        fmt.Printf("Error generating HTML report: %v\n", err)
        os.Exit(1)
    }
}
