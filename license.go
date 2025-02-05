package main

import (
	"bytes"
	"encoding/xml"
	"fmt"
	"html/template"
	"io/ioutil"
	"net/http"
	"os"
	"path/filepath"
	"regexp"
	"strings"
	"sync"
)

// DepVersion holds two version strings:
// - Display: What is shown in the report’s Version column.
//            If no literal version is declared in the build.gradle file,
//            this is set to "version not found in build.gradle file".
// - Lookup:  The version used for constructing POM URLs and retrieving license info.
//            (If missing, dynamic lookup is attempted.)
type DepVersion struct {
	Display string
	Lookup  string
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

// GradleReportSection holds the file path of one build.gradle file and its extracted dependencies.
type GradleReportSection struct {
	FilePath     string
	Dependencies map[string]DepVersion
}

// parseVariables scans the file content for variable definitions.
// For example, a line like: def cameraxVersion = "1.1.0-alpha05"
func parseVariables(content string) map[string]string {
	varMap := make(map[string]string)
	re := regexp.MustCompile(`(?m)^\s*def\s+(\w+)\s*=\s*["']([^"']+)["']`)
	matches := re.FindAllStringSubmatch(content, -1)
	for _, match := range matches {
		varMap[match[1]] = match[2]
	}
	return varMap
}

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

// parseBuildGradleFile parses a single build.gradle file to extract dependency declarations
// and perform variable substitution for versions.
func parseBuildGradleFile(filePath string) (map[string]DepVersion, error) {
	dependencies := make(map[string]DepVersion)
	contentBytes, err := ioutil.ReadFile(filePath)
	if err != nil {
		return nil, fmt.Errorf("cannot read file %s: %v", filePath, err)
	}
	content := string(contentBytes)

	// First, parse variable definitions.
	varMap := parseVariables(content)

	// Regular expression to match dependency declarations for common configurations.
	re := regexp.MustCompile(`(?m)^\s*(implementation|api|compileOnly|runtimeOnly|testImplementation|androidTestImplementation)\s+['"]([^'"]+)['"]`)
	matches := re.FindAllStringSubmatch(content, -1)
	for _, match := range matches {
		// match[2] is the dependency string, e.g. "androidx.appcompat:appcompat:1.4.2" 
		// or "com.onesignal:OneSignal:[4.0.0, 4.99.99]" or "androidx.camera:camera-core:${cameraxVersion}"
		depStr := match[2]
		parts := strings.Split(depStr, ":")
		var group, artifact, version string
		if len(parts) >= 3 {
			group = parts[0]
			artifact = parts[1]
			version = parts[2]
			// Handle version range: if version starts with "[" then pick the first version inside the brackets.
			if strings.HasPrefix(version, "[") {
				trimmed := strings.Trim(version, "[]")
				tokens := strings.Split(trimmed, ",")
				if len(tokens) > 0 {
					version = strings.TrimSpace(tokens[0])
				}
			}
			// If version contains variable interpolation, substitute it.
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
		} else {
			if len(parts) >= 2 {
				group = parts[0]
				artifact = parts[1]
			}
			version = ""
		}
		key := fmt.Sprintf("%s/%s", group, artifact)
		var depVer DepVersion
		if version == "" {
			depVer = DepVersion{
				Display: "version not found in build.gradle file",
				Lookup:  "unknown",
			}
		} else {
			depVer = DepVersion{
				Display: version,
				Lookup:  version,
			}
		}
		if _, exists := dependencies[key]; !exists {
			dependencies[key] = depVer
		}
	}
	return dependencies, nil
}

// parseAllBuildGradleFiles processes each build.gradle file and returns a slice of GradleReportSection.
func parseAllBuildGradleFiles(filePaths []string) ([]GradleReportSection, error) {
	var sections []GradleReportSection
	for _, f := range filePaths {
		deps, err := parseBuildGradleFile(f)
		if err != nil {
			fmt.Printf("Error parsing file %s: %v\n", f, err)
			continue
		}
		// For dependencies with missing Lookup version, attempt dynamic lookup.
		for key, dep := range deps {
			if dep.Lookup == "unknown" {
				parts := strings.Split(key, "/")
				if len(parts) == 2 {
					group := parts[0]
					artifact := parts[1]
					if ver, err := getLatestVersionFromMavenCentral(group, artifact); err == nil && ver != "" {
						dep.Lookup = ver
					} else if ver, err := getLatestVersionFromGoogleMaven(group, artifact); err == nil && ver != "" {
						dep.Lookup = ver
					}
					deps[key] = dep
				}
			}
		}
		sections = append(sections, GradleReportSection{
			FilePath:     f,
			Dependencies: deps,
		})
	}
	return sections, nil
}

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
	data, err := ioutil.ReadAll(resp.Body)
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
	data, err := ioutil.ReadAll(resp.Body)
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

func fetchPOMFromURL(url string) (*MavenPOM, error) {
	resp, err := http.Get(url)
	if err != nil {
		return nil, fmt.Errorf("error fetching POM from %s: %v", url, err)
	}
	defer resp.Body.Close()
	if resp.StatusCode != http.StatusOK {
		return nil, fmt.Errorf("error fetching POM from %s: status code %d", url, resp.StatusCode)
	}
	data, err := ioutil.ReadAll(resp.Body)
	if err != nil {
		return nil, fmt.Errorf("error reading POM from %s: %v", url, err)
	}
	var pom MavenPOM
	err = xml.Unmarshal(data, &pom)
	if err != nil {
		return nil, fmt.Errorf("error unmarshalling POM from %s: %v", url, err)
	}
	return &pom, nil
}

func fetchPOM(groupID, artifactID, version string) (string, string, *MavenPOM, error) {
	groupPath := strings.ReplaceAll(groupID, ".", "/")
	mavenPOMURL := fmt.Sprintf("https://repo1.maven.org/maven2/%s/%s/%s/%s-%s.pom", groupPath, artifactID, version, artifactID, version)
	googlePOMURL := fmt.Sprintf("https://dl.google.com/dl/android/maven2/%s/%s/%s/%s-%s.pom", groupPath, artifactID, version, artifactID, version)
	type result struct {
		pom        *MavenPOM
		sourceURL  string
		projectURL string
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

func getLicenseInfo(groupID, artifactID, version string) (string, string, string) {
	sourceURL, projectURL, pom, err := fetchPOM(groupID, artifactID, version)
	if err != nil || pom == nil || len(pom.Licenses) == 0 {
		return "Unknown", fmt.Sprintf("https://www.google.com/search?q=%s+%s+%s+license", groupID, artifactID, version), ""
	}
	return pom.Licenses[0].Name, projectURL, sourceURL
}

func splitDependency(dep string) (string, string, error) {
	parts := strings.Split(dep, "/")
	if len(parts) != 2 {
		return "", "", fmt.Errorf("invalid dependency format: %s", dep)
	}
	return parts[0], parts[1], nil
}

type LicenseInfo struct {
	Name       string
	URL        string // "View Details" link
	POMFileURL string // "View POM" link
}

func getLicenseInfoWrapper(dep, version string) LicenseInfo {
	groupID, artifactID, err := splitDependency(dep)
	if err != nil {
		fmt.Printf("Warning: Invalid dependency format '%s': %v\n", dep, err)
		return LicenseInfo{"Unknown", "", ""}
	}
	name, url, pomurl := getLicenseInfo(groupID, artifactID, version)
	return LicenseInfo{Name: name, URL: url, POMFileURL: pomurl}
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
	licenseNameUpper := strings.ToUpper(licenseName)
	for _, keyword := range copyleftKeywords {
		if strings.Contains(licenseNameUpper, strings.ToUpper(keyword)) {
			return true
		}
	}
	return false
}

func generateHTMLReport(sections []GradleReportSection) error {
	// Generate the report in the folder "license-checker" in the current working directory.
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
    <title>Build.gradle Dependency License Report</title>
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
    </style>
</head>
<body>
    <h1>Build.gradle Dependency License Report</h1>
    {{range .}}
        <h2>File: {{.FilePath}}</h2>
        {{if .Dependencies}}
        <table>
            <thead>
                <tr>
                    <th>Dependency</th>
                    <th>Version</th>
                    <th>License</th>
                    <th>Project Details</th>
                    <th>POM File</th>
                </tr>
            </thead>
            <tbody>
                {{range $dep, $ver := .Dependencies}}
                {{ $info := getLicenseInfoWrapper $dep $ver.Lookup }}
                {{ if eq $info.Name "Unknown" }}
                    <tr class="unknown-license">
                {{ else if isCopyleft $info.Name }}
                    <tr class="copyleft">
                {{ else }}
                    <tr class="non-copyleft">
                {{ end }}
                    <td>{{$dep}}</td>
                    <td>{{$ver.Display}}</td>
                    <td>{{$info.Name}}</td>
                    <td><a href="{{$info.URL}}" target="_blank">View Details</a></td>
                    <td><a href="{{$info.POMFileURL}}" target="_blank">View POM</a></td>
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

func captureOutput(f func()) string {
	var buf bytes.Buffer
	oldStdout := os.Stdout
	oldStderr := os.Stderr
	defer func() {
		os.Stdout = oldStdout
		os.Stderr = oldStderr
	}()
	r, w, _ := os.Pipe()
	os.Stdout = w
	os.Stderr = w
	f()
	w.Close()
	buf.ReadFrom(r)
	return buf.String()
}

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
	output := captureOutput(func() {
		err = generateHTMLReport(sections)
		if err != nil {
			fmt.Printf("Error generating report: %v\n", err)
			os.Exit(1)
		}
	})
	logPath := "output.txt"
	if err := ioutil.WriteFile(logPath, []byte(output), 0644); err != nil {
		fmt.Printf("Error saving output to %s: %v\n", logPath, err)
		os.Exit(1)
	}
	fmt.Printf("Output saved to: %s\n", logPath)
}
