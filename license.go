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
	"os/exec"
	"path/filepath"
	"regexp"
	"strings"
	"sync"
)

// -------------------------------------------------------------------------------------
// Data Structures
// -------------------------------------------------------------------------------------

// DepVersion holds two version strings:
// - Display: Shown in the report’s Version column.
// - Lookup:  Used for constructing POM URLs and retrieving license info.
type DepVersion struct {
	Display string
	Lookup  string
}

// ExtendedDepInfo holds the DepVersion plus the dependency’s immediate parent:
// - If it's a direct dependency, Parent = "direct".
// - If it's transitive, Parent = GAV of the direct parent in the tree.
type ExtendedDepInfo struct {
	DepVersion
	Parent string
}

// License represents the license details from a POM file.
type License struct {
	Name string `xml:"name"`
	URL  string `xml:"url"`
}

// MavenPOM represents the structure of a Maven POM file.
type MavenPOM struct {
	XMLName  xml.Name  `xml:"project"`
	Licenses []License `xml:"licenses>license"`
}

// GradleReportSection holds information for a single build.gradle file:
// - FilePath: The path to the build.gradle
// - RawTreeOutput: The raw text from the `gradle dependencies` command (for display in <pre>).
// - Dependencies: A map of "group/artifact" => ExtendedDepInfo. Versions, parent info, etc.
type GradleReportSection struct {
	FilePath     string
	RawTreeOutput string
	Dependencies map[string]ExtendedDepInfo
}

// -------------------------------------------------------------------------------------
// Step 1: Find build.gradle files
// -------------------------------------------------------------------------------------

// findBuildGradleFiles recursively finds all files named "build.gradle" (case-insensitive) starting from root.
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
		return nil, fmt.Errorf("error walking the path %q: %v", root, err)
	}
	return files, nil
}

// -------------------------------------------------------------------------------------
// Step 2: Execute "gradle dependencies" and capture output
// -------------------------------------------------------------------------------------

// runGradleDependencies runs `gradle dependencies` (or `./gradlew dependencies` if gradlew is available)
// in the directory containing the build.gradle file and returns the captured output as a string.
func runGradleDependencies(buildGradlePath string) (string, error) {
	dir := filepath.Dir(buildGradlePath)

	// Check if there's a gradlew wrapper in that directory or above:
	gradleCmd := "gradle"
	for curDir := dir; curDir != "/" && curDir != "."; curDir = filepath.Dir(curDir) {
		wrapperPath := filepath.Join(curDir, "gradlew")
		if _, err := os.Stat(wrapperPath); err == nil {
			gradleCmd = wrapperPath
			break
		}
	}

	// We run "gradle dependencies". You might want to add flags like "--no-daemon" or a specific configuration.
	cmd := exec.Command(gradleCmd, "dependencies")
	cmd.Dir = dir

	var outBuf, errBuf bytes.Buffer
	cmd.Stdout = &outBuf
	cmd.Stderr = &errBuf

	if err := cmd.Run(); err != nil {
		return "", fmt.Errorf("error running '%s dependencies' in %s: %v\nStderr: %s",
			gradleCmd, dir, err, errBuf.String())
	}
	return outBuf.String(), nil
}

// -------------------------------------------------------------------------------------
// Step 3: Parse the Gradle dependency tree output
// -------------------------------------------------------------------------------------

// parseDependencyLineRegex extracts GAV from lines like:
// "+--- com.example:my-lib:1.2.3" or "\--- androidx.appcompat:appcompat:1.4.2 (*)"
// It captures the group, artifact, and version (still including " (*)" if present).
// We'll strip " (*)" later to handle repeated dependencies.
var parseDependencyLineRegex = regexp.MustCompile(`(?:\+---|\\\---)\s+([\w\.\-]+):([\w\.\-]+):([\w\.\-]+(?:\s*\(\*\))?)`)

// parseDependencyTreeOutput parses the raw text from "gradle dependencies" and extracts
// each dependency with its immediate parent. We use indentation to determine parent-child relationships.
// Returns a map of "group/artifact" => ExtendedDepInfo, storing the first parent encountered if any.
func parseDependencyTreeOutput(output string) map[string]ExtendedDepInfo {
	depsMap := make(map[string]ExtendedDepInfo)

	lines := strings.Split(output, "\n")

	// We'll keep a stack where each entry is (indentLevel, "group:artifact:version").
	// Indent level is determined by the number of leading "|    " blocks.
	type stackEntry struct {
		level int
		gav   string // e.g. "androidx.appcompat:appcompat:1.4.2"
	}

	var stack []stackEntry

	// helper to find indentation level from leading "|    " sequences
	getIndentLevel := func(line string) int {
		// Count how many times we see "|    " from the start of the line
		prefix := 0
		for {
			if strings.HasPrefix(line, "|    ") {
				line = line[5:] // remove the first 5 characters: "|    "
				prefix++
			} else {
				break
			}
		}
		return prefix
	}

	for _, line := range lines {
		trimmed := strings.TrimSpace(line)
		if trimmed == "" {
			continue
		}

		// Check if the line has a dependency marker: +--- or \---
		if strings.Contains(line, "+---") || strings.Contains(line, "\\---") {
			// We have a dependency line, parse it
			matches := parseDependencyLineRegex.FindStringSubmatch(line)
			if len(matches) == 4 {
				group := matches[1]
				artifact := matches[2]
				version := matches[3]
				// remove " (*)" if present:
				version = strings.TrimSpace(strings.ReplaceAll(version, "(*)", ""))

				// Determine indent level => who is the parent
				level := getIndentLevel(line)

				// Pop from stack until top has level < current
				for len(stack) > 0 && stack[len(stack)-1].level >= level {
					stack = stack[:len(stack)-1]
				}

				var parentLabel string
				if len(stack) == 0 {
					// top-level => direct dependency
					parentLabel = "direct"
				} else {
					parentLabel = stack[len(stack)-1].gav
				}

				// Prepare a GAV string for the current line
				currentGAV := fmt.Sprintf("%s:%s:%s", group, artifact, version)

				// store in map => "group/artifact" => ExtendedDepInfo
				key := group + "/" + artifact
				if _, exists := depsMap[key]; !exists {
					depsMap[key] = ExtendedDepInfo{
						DepVersion: DepVersion{
							Display: version,
							Lookup:  version,
						},
						Parent: parentLabel,
					}
				}

				// push this new item to the stack
				stack = append(stack, stackEntry{
					level: level,
					gav:   currentGAV,
				})
			}
		}
	}

	return depsMap
}

// -------------------------------------------------------------------------------------
// Step 4: License Fetching (unchanged from original, with concurrency improvements)
// -------------------------------------------------------------------------------------

// getLatestVersionFromMavenCentral fetches the latest version from Maven Central metadata.
func getLatestVersionFromMavenCentral(groupID, artifactID string) (string, error) {
	groupPath := strings.ReplaceAll(groupID, ".", "/")
	metadataURL := fmt.Sprintf("https://repo1.maven.org/maven2/%s/%s/maven-metadata.xml", groupPath, artifactID)
	resp, err := http.Get(metadataURL)
	if err != nil {
		return "", fmt.Errorf("error fetching maven metadata from %s: %v", metadataURL, err)
	}
	defer resp.Body.Close()
	if resp.StatusCode != http.StatusOK {
		return "", fmt.Errorf("error fetching maven metadata from %s: status code %d", metadataURL, resp.StatusCode)
	}
	data, err := io.ReadAll(resp.Body)
	if err != nil {
		return "", fmt.Errorf("error reading maven metadata from %s: %v", metadataURL, err)
	}
	type metadata struct {
		Release string `xml:"versioning>release"`
		Latest  string `xml:"versioning>latest"`
	}
	var m metadata
	if err := xml.Unmarshal(data, &m); err != nil {
		return "", fmt.Errorf("error parsing maven metadata: %v", err)
	}
	if m.Release != "" {
		return m.Release, nil
	}
	if m.Latest != "" {
		return m.Latest, nil
	}
	return "", fmt.Errorf("no version found in metadata")
}

// getLatestVersionFromGoogleMaven fetches the latest version from Google Maven metadata.
func getLatestVersionFromGoogleMaven(groupID, artifactID string) (string, error) {
	groupPath := strings.ReplaceAll(groupID, ".", "/")
	metadataURL := fmt.Sprintf("https://dl.google.com/dl/android/maven2/%s/%s/maven-metadata.xml", groupPath, artifactID)
	resp, err := http.Get(metadataURL)
	if err != nil {
		return "", fmt.Errorf("error fetching google maven metadata from %s: %v", metadataURL, err)
	}
	defer resp.Body.Close()
	if resp.StatusCode != http.StatusOK {
		return "", fmt.Errorf("error fetching google maven metadata from %s: status code %d", metadataURL, resp.StatusCode)
	}
	data, err := io.ReadAll(resp.Body)
	if err != nil {
		return "", fmt.Errorf("error reading google maven metadata from %s: %v", metadataURL, err)
	}
	type metadata struct {
		Release string `xml:"versioning>release"`
		Latest  string `xml:"versioning>latest"`
	}
	var m metadata
	if err := xml.Unmarshal(data, &m); err != nil {
		return "", fmt.Errorf("error parsing google maven metadata: %v", err)
	}
	if m.Release != "" {
		return m.Release, nil
	}
	if m.Latest != "" {
		return m.Latest, nil
	}
	return "", fmt.Errorf("no version found in google maven metadata")
}

// fetchPOMFromURL fetches and unmarshals a Maven POM.
func fetchPOMFromURL(url string) (*MavenPOM, error) {
	resp, err := http.Get(url)
	if err != nil {
		return nil, fmt.Errorf("error fetching POM from %s: %v", url, err)
	}
	defer resp.Body.Close()
	if resp.StatusCode != http.StatusOK {
		return nil, fmt.Errorf("error fetching POM from %s: status code %d", url, resp.StatusCode)
	}
	data, err := io.ReadAll(resp.Body)
	if err != nil {
		return nil, fmt.Errorf("error reading POM from %s: %v", url, err)
	}
	var pom MavenPOM
	decoder := xml.NewDecoder(bytes.NewReader(data))
	decoder.Strict = false
	if err := decoder.Decode(&pom); err != nil {
		return nil, fmt.Errorf("error unmarshalling POM from %s: %v", url, err)
	}
	return &pom, nil
}

// fetchPOM tries to fetch from Maven Central and Google Maven concurrently.
func fetchPOM(groupID, artifactID, version string) (string, string, *MavenPOM, error) {
	groupPath := strings.ReplaceAll(groupID, ".", "/")
	mavenPOMURL := fmt.Sprintf("https://repo1.maven.org/maven2/%s/%s/%s/%s-%s.pom", groupPath, artifactID, version, artifactID, version)
	googlePOMURL := fmt.Sprintf("https://dl.google.com/dl/android/maven2/%s/%s/%s/%s-%s.pom", groupPath, artifactID, version, artifactID, version)

	type result struct {
		pom        *MavenPOM
		sourceURL  string // URL used to fetch the POM file.
		projectURL string // For "View Details" link.
		err        error
	}

	resultCh := make(chan result, 2)
	var wg sync.WaitGroup
	wg.Add(2)

	go func() {
		defer wg.Done()
		pom, err := fetchPOMFromURL(mavenPOMURL)
		projectURL := fmt.Sprintf("https://repo1.maven.org/maven2/%s/%s/%s/", groupPath, artifactID, version)
		resultCh <- result{pom, mavenPOMURL, projectURL, err}
	}()
	go func() {
		defer wg.Done()
		pom, err := fetchPOMFromURL(googlePOMURL)
		projectURL := fmt.Sprintf("https://maven.google.com/web/index.html#%s:%s:%s", groupID, artifactID, version)
		resultCh <- result{pom, googlePOMURL, projectURL, err}
	}()

	go func() {
		wg.Wait()
		close(resultCh)
	}()

	var finalSourceURL, finalProjectURL string
	var finalPOM *MavenPOM
	var finalError error

	for res := range resultCh {
		if res.err == nil && res.pom != nil {
			finalSourceURL = res.sourceURL
			finalProjectURL = res.projectURL
			finalPOM = res.pom
			finalError = nil
			break
		} else {
			finalError = res.err
		}
	}

	if finalPOM == nil {
		searchURL := fmt.Sprintf("https://www.google.com/search?q=%s+%s+%s+license", groupID, artifactID, version)
		return "", searchURL, nil, finalError
	}
	return finalSourceURL, finalProjectURL, finalPOM, nil
}

// getLicenseInfo returns (licenseName, projectURL, POMFileURL).
// If not found, it returns ("Unknown", fallbackSearchURL, "").
func getLicenseInfo(groupID, artifactID, version string) (string, string, string) {
	sourceURL, projectURL, pom, err := fetchPOM(groupID, artifactID, version)
	if err != nil || pom == nil || len(pom.Licenses) == 0 {
		return "Unknown", fmt.Sprintf("https://www.google.com/search?q=%s+%s+%s+license", groupID, artifactID, version), ""
	}
	return pom.Licenses[0].Name, projectURL, sourceURL
}

// isCopyleft helps determine if the license appears to be copyleft by searching for typical keywords.
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
	licenseNameUpper := strings.ToUpper(licenseName)
	for _, keyword := range copyleftKeywords {
		if strings.Contains(licenseNameUpper, strings.ToUpper(keyword)) {
			return true
		}
	}
	return false
}

// -------------------------------------------------------------------------------------
// Step 5: Primary flow: For each build.gradle, run Gradle, parse tree, fetch licenses.
// -------------------------------------------------------------------------------------

// parseAllBuildGradleFiles processes each build.gradle file.
// 1. Runs `gradle dependencies` (or `gradlew dependencies`).
// 2. Parses the output for dependency GAV + parent relationships.
// 3. Looks up missing versions if needed (if any are not resolved, but typically Gradle resolves them).
// 4. Returns a slice of GradleReportSection (one per build.gradle).
func parseAllBuildGradleFiles(filePaths []string) ([]GradleReportSection, error) {
	var sections []GradleReportSection

	for _, buildFile := range filePaths {
		fmt.Printf("Processing: %s\n", buildFile)

		output, err := runGradleDependencies(buildFile)
		if err != nil {
			fmt.Printf("Error running Gradle 'dependencies' for %s: %v\n", buildFile, err)
			continue
		}

		depsMap := parseDependencyTreeOutput(output)

		// Optional: If any version is "unknown" or we want to do dynamic version resolution, do it here.
		// But typically, Gradle has already resolved versions in the tree output.

		// Attempt dynamic lookup if version is blank or "unknown" (rare in transitive context).
		for key, dep := range depsMap {
			if dep.Lookup == "unknown" || dep.Lookup == "" {
				parts := strings.Split(key, "/")
				if len(parts) == 2 {
					group, artifact := parts[0], parts[1]
					if ver, errCentral := getLatestVersionFromMavenCentral(group, artifact); errCentral == nil && ver != "" {
						dep.Lookup = ver
					} else if verGoogle, errGoogle := getLatestVersionFromGoogleMaven(group, artifact); errGoogle == nil && verGoogle != "" {
						dep.Lookup = verGoogle
					}
					depsMap[key] = dep
				}
			}
		}

		sections = append(sections, GradleReportSection{
			FilePath:      buildFile,
			RawTreeOutput: output,
			Dependencies:  depsMap,
		})
	}

	return sections, nil
}

// -------------------------------------------------------------------------------------
// Step 6: HTML Report Generation
// -------------------------------------------------------------------------------------

// In the HTML, we want:
// 1) A <pre> block showing the raw "gradle dependencies" output (the entire tree).
// 2) A table listing each unique dependency with columns:
//    - Dependency (group/artifact)
//    - Version
//    - License
//    - Parent
//    - Project Details (link)
//    - POM File (link)

func getLicenseInfoWrapper(dep, version string) (name, detailsURL, pomURL string) {
	parts := strings.Split(dep, "/")
	if len(parts) != 2 {
		return "Unknown", "", ""
	}
	groupID, artifactID := parts[0], parts[1]
	licenseName, projectURL, pomFileURL := getLicenseInfo(groupID, artifactID, version)
	return licenseName, projectURL, pomFileURL
}

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
        pre {
            background: #f6f8fa;
            border: 1px solid #ddd;
            padding: 10px;
            overflow: auto;
            max-height: 400px;
        }
    </style>
</head>
<body>
    <h1>Kotlin Dependency License Report</h1>
    {{range .}}
        <h2>File: {{.FilePath}}</h2>

        <h3>Full Dependency Tree</h3>
        <pre>{{.RawTreeOutput}}</pre>

        <h3>Dependencies Table</h3>
        {{if .Dependencies}}
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
                {{range $dep, $info := .Dependencies}}
                {{ $licenseName, $projectURL, $pomURL := getLicenseInfoWrapper $dep $info.Lookup }}
                {{ if eq $licenseName "Unknown" }}
                    <tr class="unknown-license">
                {{ else if isCopyleft $licenseName }}
                    <tr class="copyleft">
                {{ else }}
                    <tr class="non-copyleft">
                {{ end }}
                    <td>{{$dep}}</td>
                    <td>{{$info.Display}}</td>
                    <td>{{$licenseName}}</td>
                    <td>{{$info.Parent}}</td>
                    {{if $projectURL}}
                        <td><a href="{{$projectURL}}" target="_blank">View Details</a></td>
                    {{else}}
                        <td></td>
                    {{end}}
                    {{if $pomURL}}
                        <td><a href="{{$pomURL}}" target="_blank">View POM</a></td>
                    {{else}}
                        <td></td>
                    {{end}}
                </tr>
                {{end}}
            </tbody>
        </table>
        {{else}}
            <p>No dependencies found in this file.</p>
        {{end}}
    {{end}}
</body>
</html>`

	tmpl, err := template.New("report").Funcs(template.FuncMap{
		"getLicenseInfoWrapper": getLicenseInfoWrapper,
		"isCopyleft":            isCopyleft,
	}).Parse(tmplText)
	if err != nil {
		return fmt.Errorf("error creating template: %v", err)
	}

	reportPath := filepath.Join(outputDir, "dependency-license-report.html")
	file, err := os.Create(reportPath)
	if err != nil {
		return fmt.Errorf("error creating report file: %v", err)
	}
	defer file.Close()

	err = tmpl.Execute(file, sections)
	if err != nil {
		return fmt.Errorf("error generating report: %v", err)
	}

	fmt.Printf("✅ License report successfully generated at %s\n", reportPath)
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

	// Generate the HTML report
	if err := generateHTMLReport(sections); err != nil {
		fmt.Printf("Error generating report: %v\n", err)
		os.Exit(1)
	}
}
