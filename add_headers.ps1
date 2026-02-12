#!/usr/bin/env pwsh

$header = @"
/-
Copyright (c) 2025. All rights reserved.
Author: Julian Calderon Almendros
License: MIT
-/

"@

$count = 0
$files = Get-ChildItem "ZfcSetTheory\*.lean"

foreach ($f in $files) {
    $content = Get-Content $f.FullName -Raw
    
    if ($content -notmatch "Copyright") {
        $newContent = $header + $content
        Set-Content -Path $f.FullName -Value $newContent -Encoding UTF8
        Write-Host "OK: $($f.Name)"
        $count++
    } else {
        Write-Host "SKIP: $($f.Name)"
    }
}

Write-Host "`nActualizados: $count"
