@echo off
REM Script para ejecutar lake build con información sobre sorry y warnings
REM Captura diagnosticos completos, busca sorry statements y warnings

setlocal enabledelayedexpansion

echo ====================================================================
echo Building ZfcSetTheory - Detailed Diagnostics
echo ====================================================================
echo Timestamp: %date% %time%
echo.

REM Crear archivo de log con timestamp
(
    echo ===== ZfcSetTheory Build Log =====
    echo Timestamp: %date% %time%
    echo.
) > build_log.txt

REM Ejecutar lake build
echo Building...
lake build >> build_log.txt 2>&1

REM Buscar sorry statements
echo. >> build_log.txt
echo ===== SORRY STATEMENTS ===== >> build_log.txt
echo. >> build_log.txt

setlocal enabledelayedexpansion
set sorryCount=0
for /r ZfcSetTheory %%f in (*.lean) do (
    findstr "sorry" "%%f" > nul 2>&1
    if not errorlevel 1 (
        echo File: %%f >> build_log.txt
        findstr /n "sorry" "%%f" >> build_log.txt
        set /a sorryCount+=1
        echo. >> build_log.txt
    )
)

if %sorryCount% equ 0 (
    echo No sorry statements found. >> build_log.txt
)

REM Ejecutar verificación detallada de archivos problemáticos con Lean
echo. >> build_log.txt
echo ===== LEAN DIRECT DIAGNOSTICS ===== >> build_log.txt
echo. >> build_log.txt
echo Checking Recursion.lean for detailed type errors... >> build_log.txt
echo. >> build_log.txt

REM Encontrar Lean en la instalación de elan
for /f "tokens=*" %%i in ('where lean.exe 2^>nul ^| findstr /i "toolchain\|elan"') do (
    set LEAN_PATH=%%i
    goto found_lean
)
set LEAN_PATH=

:found_lean
if defined LEAN_PATH (
    echo Using Lean from: %LEAN_PATH% >> build_log.txt
    "%LEAN_PATH%" ZfcSetTheory\Recursion.lean 2>> build_log.txt | findstr /i "error\|unknown\|mismatch" >> build_log.txt
) else (
    echo Warning: Lean compiler not found for detailed diagnostics >> build_log.txt
)

REM Búsqueda de warnings
echo. >> build_log.txt
echo ===== BUILD WARNINGS AND ERRORS ===== >> build_log.txt

REM Búsqueda de warnings
setlocal enabledelayedexpansion
findstr /i "warning" build_log.txt > nul 2>&1
if not errorlevel 1 (
    echo Warnings detected in build output. >> build_log.txt
) else (
    echo No warnings detected. >> build_log.txt
)

REM Búsqueda de errores de Lean (Unknown identifier, Type mismatch, etc.)
echo. >> build_log.txt
echo ===== LEAN TYPE/COMPILATION ERRORS ===== >> build_log.txt
echo. >> build_log.txt

set errorCount=0
findstr /i "unknown identifier\|type mismatch\|application type mismatch\|tactic.*failed" build_log.txt > nul 2>&1
if not errorlevel 1 (
    echo Errors detected:
    findstr /i "unknown identifier\|type mismatch\|application type mismatch\|tactic.*failed" build_log.txt >> build_log.txt
    for /f %%a in ('findstr /i /c:"unknown identifier" build_log.txt ^| find /c /v ""') do set /a errorCount+=%%a
    for /f %%a in ('findstr /i /c:"type mismatch" build_log.txt ^| find /c /v ""') do set /a errorCount+=%%a
) else (
    echo No Lean type/compilation errors detected. >> build_log.txt
)

REM Resumen final
echo. >> build_log.txt
echo ===== SUMMARY ===== >> build_log.txt
echo Sorry statements: %sorryCount% >> build_log.txt
echo Lean errors: %errorCount% >> build_log.txt
echo Completed at: %date% %time% >> build_log.txt

REM Mostrar resumen en consola
echo.
echo ====================================================================
echo BUILD COMPLETE
echo ====================================================================
echo Sorry statements found: %sorryCount%
echo Lean errors found: %errorCount%
echo Full log: build_log.txt
echo.

REM Mostrar últimas líneas del log
echo --- Last 30 lines of build log ---
for /f "skip=999999 tokens=*" %%a in ('findstr /n "." build_log.txt') do set "var=%%a"
REM Mostrar el contenido del log
type build_log.txt

echo.
echo Press any key to continue...
pause >nul

