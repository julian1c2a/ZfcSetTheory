#!/usr/bin/env pwsh

# Script para ejecutar lake build y reportar todos los errores encontrados
# Incluye sorry statements, type errors, warnings y otros problemas de Lean

$ErrorActionPreference = "Continue"

Write-Host "====================================================================" -ForegroundColor Cyan
Write-Host "Building ZfcSetTheory - Complete Error Diagnostics" -ForegroundColor Cyan
Write-Host "====================================================================" -ForegroundColor Cyan
Write-Host ("Timestamp: {0:yyyy-MM-dd HH:mm}" -f (Get-Date)) -ForegroundColor Gray
Write-Host ""

# Crear log
$logFile = "build_log.txt"
$logContent = @"
===== ZfcSetTheory Build Log =====
Timestamp: $(Get-Date -Format 'yyyy-MM-dd HH:mm')

"@

# Ejecutar lake build
Write-Host "Executing: lake build"
$buildOutput = & lake build 2>&1 | Tee-Object -Variable buildContent

# Agregar output del build
$logContent += "===== LAKE BUILD OUTPUT =====`r`n"
$logContent += ($buildContent | Out-String)
$logContent += "`r`n"

# Buscar sorry statements
Write-Host "Scanning for sorry statements..."
$logContent += "===== SORRY STATEMENTS =====`r`n`r`n"

$sorryCount = 0
Get-ChildItem -Path "ZfcSetTheory\" -Filter "*.lean" -Recurse | ForEach-Object {
    $sorries = Select-String -Pattern "sorry" -Path $_.FullName -ErrorAction SilentlyContinue
    if ($sorries) {
        $logContent += "File: $($_.FullName)`r`n"
        $sorries | ForEach-Object {
            $logContent += "$($_.LineNumber): $($_.Line)`r`n"
            $sorryCount++
        }
        $logContent += "`r`n"
    }
}

if ($sorryCount -eq 0) {
    $logContent += "No sorry statements found.`r`n"
}

# Buscar errores de tipo comunes en los archivos .lean
Write-Host "Scanning for type errors..."
$logContent += "`r`n===== LEAN TYPE ERRORS IN SOURCE FILES =====`r`n`r`n"

$typeErrors = @()
Get-ChildItem -Path "ZfcSetTheory\" -Filter "*.lean" -Recurse | ForEach-Object {
    # Patrones comunes de código que causa errores
    $patterns = @(
        "Eq_of_OrderedPairs_given_projections.*hp_cart\.1",
        "subset_of_mem_successor\s+[^(]*$",
        "mem_successor_iff",
        "Unknown identifier"
    )
    
    $content = Get-Content -Path $_.FullName -Raw
    foreach ($pattern in $patterns) {
        if ($content -match $pattern) {
            $typeErrors += $_
        }
    }
}

if ($typeErrors.Count -gt 0) {
    $typeErrors | ForEach-Object {
        $logContent += "File with potential type errors: $($_.FullName)`r`n"
    }
    $logContent += "`r`nFiles with known problematic patterns: $($typeErrors.Count)`r`n"
} else {
    $logContent += "No obvious type error patterns detected in source files.`r`n"
}

# Resumen
$logContent += "`r`n===== SUMMARY =====`r`n"
$logContent += "Sorry statements: $sorryCount`r`n"
$logContent += "Files with potential type errors: $($typeErrors.Count)`r`n"
$logContent += "Completed at: $(Get-Date -Format 'yyyy-MM-dd HH:mm')`r`n"

# Guardar log
$logContent | Set-Content -Path $logFile -Encoding UTF8

# Mostrar resumen en consola
Write-Host ""
Write-Host "====================================================================" -ForegroundColor Green
Write-Host "BUILD COMPLETE" -ForegroundColor Green
Write-Host "====================================================================" -ForegroundColor Green
Write-Host "Sorry statements: $sorryCount" -ForegroundColor Yellow
Write-Host "Files with potential errors: $($typeErrors.Count)" -ForegroundColor Yellow
Write-Host "Full log: $logFile" -ForegroundColor Cyan
Write-Host ""

# Mostrar últimas líneas del log
Write-Host "--- Build Log Content ---" -ForegroundColor Gray
Get-Content $logFile

Write-Host ""
Read-Host "Press Enter to continue..."
