#!/usr/bin/env pwsh
<#
.SYNOPSIS
    Captures Lean InfoView diagnostics and project information to LeanInfoView.txt.
    
.DESCRIPTION
    This script runs 'lake build', captures all output, and generates a comprehensive
    report with project information, build diagnostics, and file status.
    Can optionally include file-specific diagnostics for a given Lean file.
    Output is always written to LeanInfoView.txt in the project root.
    
.PARAMETER File
    Optional: Name of a Lean file to analyze (e.g., "Recursion.lean").
    If provided, includes file-specific diagnostics in the report.
    
.PARAMETER Verbose
    Show detailed output to console while capture is happening.
    
.EXAMPLE
    .\capture_infoview.ps1
    .\capture_infoview.ps1 -Verbose
    .\capture_infoview.ps1 -File "Recursion.lean"
    .\capture_infoview.ps1 -File "Recursion.lean" -Verbose
#>

param(
    [string]$File = "",
    [switch]$Verbose
)

# Salida fija
$OutputFile = "LeanInfoView.txt"

# ============================================================================
# CONFIGURATION
# ============================================================================
$ErrorActionPreference = "Continue"
$timestamp = Get-Date -Format "yyyy-MM-dd HH:mm:ss"
$timestampFile = Get-Date -Format "yyyy-MM-dd_HHmmss"

# Paths
$projectRoot = Get-Location
$sourceDir = Join-Path $projectRoot "ZfcSetTheory"
$outputPath = Join-Path $projectRoot $OutputFile
$buildLogPath = Join-Path $projectRoot "build_log.txt"

# File-specific diagnostics
$targetFile = ""
$targetFilePath = ""

if ($File) {
    # Buscar el archivo en el directorio ZfcSetTheory
    if (Test-Path (Join-Path $sourceDir $File)) {
        $targetFilePath = Join-Path $sourceDir $File
        $targetFile = $File
    } elseif (Test-Path $File) {
        # Si se proporciona ruta relativa
        $targetFilePath = (Resolve-Path $File).Path
        $targetFile = $File
    } else {
        if ($Verbose) {
            Write-Host "⚠️  File not found: $File" -ForegroundColor Yellow
        }
    }
}

# ============================================================================
# HELPER FUNCTIONS
# ============================================================================

function Write-Section {
    param([string]$Title)
    ""
    "=" * 80
    "=== $Title ==="
    "=" * 80
    ""
}

function Write-Subsection {
    param([string]$Title)
    ""
    "--- $Title ---"
    ""
}

function Write-TimeElapsed {
    param(
        [datetime]$Start,
        [datetime]$End
    )
    $elapsed = $End - $Start
    "⏱️  Time elapsed: $($elapsed.TotalSeconds) seconds"
}

# ============================================================================
# MAIN SCRIPT
# ============================================================================

# Initialize output array
$output = @()

# SECTION 1: Header and Metadata
$output += Write-Section "LEAN PROJECT BUILD DIAGNOSTICS"
$output += "Project Root:     $projectRoot"
$output += "Report Generated: $timestamp"
$output += "Report File:      $OutputFile"
$output += ""

# SECTION 2: Environment Information
$output += Write-Section "ENVIRONMENT INFORMATION"
$output += "Operating System: $([System.Runtime.InteropServices.RuntimeInformation]::OSDescription)"
$output += "PowerShell Version: $($PSVersionTable.PSVersion)"
$output += "Current Directory: $(Get-Location)"
$output += ""

# Get Lean version
try {
    $leanVersion = & lean --version 2>&1
    $output += "Lean Version:     $leanVersion"
} catch {
    $output += "Lean Version:     [ERROR: Could not determine]"
}

# Get Lake version
try {
    $lakeVersion = & lake --version 2>&1
    $output += "Lake Version:     $lakeVersion"
} catch {
    $output += "Lake Version:     [ERROR: Could not determine]"
}
$output += ""

# SECTION 3: Project Structure
$output += Write-Section "PROJECT STRUCTURE"
$leanFiles = @(Get-ChildItem $sourceDir -Filter "*.lean" -Recurse)
$output += "Total Lean Files:  $($leanFiles.Count)"
$output += ""
$output += "Files:"
foreach ($file in $leanFiles | Sort-Object Name) {
    $size = $file.Length
    $output += "  • $($file.Name) ($size bytes)"
}
$output += ""

# SECTION 4: Build Output
$output += Write-Section "BUILD DIAGNOSTICS"
$buildStartTime = Get-Date
$output += "Build started: $($buildStartTime.ToString('yyyy-MM-dd HH:mm:ss'))"
$output += ""

# Run build and capture output
if ($Verbose) {
    Write-Host "🔨 Running: lake build..." -ForegroundColor Cyan
}

try {
    $buildOutput = & lake build 2>&1
    $buildEndTime = Get-Date
    
    $output += $buildOutput
    $output += ""
    $output += Write-TimeElapsed $buildStartTime $buildEndTime
    $output += "Build completed: $($buildEndTime.ToString('yyyy-MM-dd HH:mm:ss'))"
} catch {
    $buildEndTime = Get-Date
    $output += "ERROR during build: $_"
    $output += Write-TimeElapsed $buildStartTime $buildEndTime
}
$output += ""

# SECTION 5: File-Specific Diagnostics (if requested)
if ($targetFile -and $targetFilePath) {
    $output += Write-Section "FILE-SPECIFIC DIAGNOSTICS: $targetFile"
    
    # File metadata
    $fileInfo = Get-Item $targetFilePath
    $output += "File Path:        $targetFilePath"
    $output += "File Size:        $($fileInfo.Length) bytes"
    $output += "Last Modified:    $($fileInfo.LastWriteTime.ToString('yyyy-MM-dd HH:mm:ss'))"
    $output += ""
    
    # Line count
    $lineCount = (Get-Content $targetFilePath | Measure-Object -Line).Lines
    $output += "Total Lines:      $lineCount"
    $output += ""
    
    # Check for sorry statements
    $sorryMatches = @(Select-String -Pattern "sorry" -Path $targetFilePath -ErrorAction SilentlyContinue)
    if ($sorryMatches.Count -gt 0) {
        $output += "Sorry Statements: $($sorryMatches.Count)"
        $output += ""
        foreach ($match in $sorryMatches) {
            $output += "  Line $($match.LineNumber): $($match.Line.Trim())"
        }
    } else {
        $output += "Sorry Statements: 0 ✓"
    }
    $output += ""
    
    # Check for type errors/compilation issues with lean
    $output += Write-Subsection "Lean Validation"
    try {
        if ($Verbose) {
            Write-Host "🔍 Validating file with Lean..." -ForegroundColor Cyan
        }
        
        # Try to compile just this file
        $validationOutput = & lake build 2>&1 | Select-String "error|warning" | Select-String $targetFile
        
        if ($validationOutput) {
            $output += "Issues found:"
            $output += $validationOutput
        } else {
            $output += "✓ No errors or warnings specific to this file"
        }
    } catch {
        $output += "Could not run validation: $_"
    }
    $output += ""
    
    # Show imports
    $imports = @(Select-String -Pattern "^import " -Path $targetFilePath | 
        ForEach-Object { $_.Line.Trim() })
    
    if ($imports.Count -gt 0) {
        $output += Write-Subsection "Imports"
        foreach ($import in $imports) {
            $output += "  $import"
        }
        $output += ""
    }
    
    # Show exports
    $exports = @(Select-String -Pattern "^export " -Path $targetFilePath | 
        ForEach-Object { $_.Line.Trim() })
    
    if ($exports.Count -gt 0) {
        $output += Write-Subsection "Exports"
        foreach ($export in $exports) {
            $output += "  $export"
        }
        $output += ""
    }
}

# SECTION 6: Project Status
$output += Write-Section "PROJECT STATUS"

# Count sorry statements
$sorryCount = 0
$sorryFiles = @()
foreach ($file in $leanFiles) {
    $matches = @(Select-String -Pattern "sorry" -Path $file.FullName -ErrorAction SilentlyContinue)
    if ($matches.Count -gt 0) {
        $sorryCount += $matches.Count
        $sorryFiles += @{
            File  = $file.Name
            Count = $matches.Count
            Lines = $matches.LineNumber
        }
    }
}

$output += "Sorry Statements: $sorryCount"
if ($sorryCount -gt 0) {
    $output += ""
    $output += "Files with 'sorry':"
    foreach ($item in $sorryFiles) {
        $output += "  • $($item.File) - $($item.Count) occurrence(s) at lines: $($item.Lines -join ', ')"
    }
}
$output += ""

# SECTION 7: File Modification Times
$output += Write-Section "FILE MODIFICATION TIMES"
$output += "(Most recently modified files first)"
$output += ""
$leanFiles | 
    Sort-Object LastWriteTime -Descending | 
    Select-Object -First 10 | 
    ForEach-Object {
        $output += "$($_.Name) - $($_.LastWriteTime.ToString('yyyy-MM-dd HH:mm:ss'))"
    }
$output += ""

# SECTION 8: Module Dependencies
$output += Write-Section "MODULE DEPENDENCIES"
$output += "Scanning import statements..."
$output += ""

$importMap = @{}
foreach ($file in $leanFiles) {
    $imports = Select-String -Pattern "^import ZfcSetTheory\." -Path $file.FullName | 
        ForEach-Object { $_.Line.Trim() }
    
    if ($imports) {
        $importMap[$file.BaseName] = @($imports)
    }
}

if ($importMap.Count -gt 0) {
    foreach ($module in ($importMap.Keys | Sort-Object)) {
        $output += "$module.lean:"
        foreach ($import in $importMap[$module]) {
            $output += "  └─ $import"
        }
    }
} else {
    $output += "[No interdependencies found or unable to parse]"
}
$output += ""

# SECTION 9: Build Artifacts
$output += Write-Section "BUILD ARTIFACTS"
if (Test-Path ".lake") {
    $buildDir = Get-ChildItem ".lake" -Recurse -ErrorAction SilentlyContinue | 
        Measure-Object
    $output += "Lake build directory exists: Yes"
    $output += "Build artifacts count: $($buildDir.Count)"
} else {
    $output += "Lake build directory exists: No"
}
$output += ""

# SECTION 10: Configuration Files
$output += Write-Section "CONFIGURATION FILES"
$configFiles = @("lakefile.lean", "lean-toolchain", ".aider.conf.yml", "lake-manifest.json")
foreach ($configFile in $configFiles) {
    if (Test-Path $configFile) {
        $fileInfo = Get-Item $configFile
        $output += "✓ $configFile ($($fileInfo.Length) bytes)"
    } else {
        $output += "✗ $configFile [not found]"
    }
}
$output += ""

# SECTION 11: Summary Statistics
$output += Write-Section "SUMMARY STATISTICS"
$totalLines = 0
foreach ($file in $leanFiles) {
    $totalLines += (Get-Content $file.FullName | Measure-Object -Line).Lines
}
$output += "Total source code lines: $totalLines"
$output += "Total modules: $($leanFiles.Count)"
$output += "Build artifacts: $(if (Test-Path ".lake") { "Generated" } else { "Not generated" })"
$output += ""

# SECTION 12: Footer
$output += "=" * 80
$output += "End of report: $(Get-Date -Format 'yyyy-MM-dd HH:mm:ss')"
$output += "=" * 80

# ============================================================================
# WRITE OUTPUT
# ============================================================================

# Write to file
$output | Out-File -FilePath $outputPath -Encoding UTF8

# Display summary
Write-Host ""
Write-Host "✅ Report generated successfully!" -ForegroundColor Green
Write-Host "📄 Output file: $outputPath" -ForegroundColor Cyan
Write-Host "📊 Total lines written: $($output.Count)" -ForegroundColor Cyan
Write-Host ""

if ($Verbose) {
    Write-Host "Content preview:" -ForegroundColor Cyan
    $output | Select-Object -First 50 | Write-Host
    if ($output.Count -gt 50) {
        Write-Host "... ($($output.Count - 50) more lines)"
    }
}

exit 0
