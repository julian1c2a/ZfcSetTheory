# Automatiza el ciclo: unlock → git add → git commit → git push → lock
# Uso: .\guarda_y_sube.ps1 "Mensaje del commit"

param(
    [Parameter(Mandatory=$true)]
    [string]$CommitMessage
)

$ErrorActionPreference = "Stop"

Write-Host "=== Iniciando guarda_y_sube ===" -ForegroundColor Cyan

# 1. Verificar que estamos en un repositorio git
if (-not (Test-Path ".git")) {
    Write-Host "ERROR: No estás en la raíz de un repositorio git." -ForegroundColor Red
    exit 1
}

# 2. Obtener lista de archivos bloqueados
$lockedFiles = @()
if (Test-Path "locked_files.txt") {
    $lockedFiles = Get-Content "locked_files.txt" | Where-Object { $_ -match '\S' }
}

Write-Host "Archivos bloqueados encontrados: $($lockedFiles.Count)" -ForegroundColor Yellow

# 3. Desbloquear temporalmente todos los archivos bloqueados
Write-Host "`n--- Desbloqueando archivos temporalmente ---" -ForegroundColor Cyan
foreach ($file in $lockedFiles) {
    if (Test-Path $file) {
        bash git-lock.bash unlock $file
        if ($LASTEXITCODE -ne 0) {
            Write-Host "ERROR: No se pudo desbloquear $file" -ForegroundColor Red
            exit 1
        }
    }
}

# 4. Git add de todos los cambios
Write-Host "`n--- Añadiendo cambios al stage ---" -ForegroundColor Cyan
git add -A
if ($LASTEXITCODE -ne 0) {
    Write-Host "ERROR: git add falló" -ForegroundColor Red
    # Re-bloquear archivos antes de salir
    foreach ($file in $lockedFiles) {
        if (Test-Path $file) {
            bash git-lock.bash lock $file
        }
    }
    exit 1
}

# 5. Git commit
Write-Host "`n--- Creando commit ---" -ForegroundColor Cyan
git commit -m $CommitMessage
if ($LASTEXITCODE -ne 0) {
    Write-Host "ERROR: git commit falló" -ForegroundColor Red
    # Re-bloquear archivos antes de salir
    foreach ($file in $lockedFiles) {
        if (Test-Path $file) {
            bash git-lock.bash lock $file
        }
    }
    exit 1
}

# 6. Git push
Write-Host "`n--- Subiendo cambios al remoto ---" -ForegroundColor Cyan
git push
if ($LASTEXITCODE -ne 0) {
    Write-Host "ERROR: git push falló" -ForegroundColor Red
    # Re-bloquear archivos antes de salir
    foreach ($file in $lockedFiles) {
        if (Test-Path $file) {
            bash git-lock.bash lock $file
        }
    }
    exit 1
}

# 7. Re-bloquear todos los archivos
Write-Host "`n--- Re-bloqueando archivos ---" -ForegroundColor Cyan
foreach ($file in $lockedFiles) {
    if (Test-Path $file) {
        bash git-lock.bash lock $file
        if ($LASTEXITCODE -ne 0) {
            Write-Host "ADVERTENCIA: No se pudo re-bloquear $file" -ForegroundColor Yellow
        }
    }
}

Write-Host "`n=== ✓ Proceso completado exitosamente ===" -ForegroundColor Green
Write-Host "Commit: $CommitMessage" -ForegroundColor Green
Write-Host "Archivos re-bloqueados: $($lockedFiles.Count)" -ForegroundColor Green
