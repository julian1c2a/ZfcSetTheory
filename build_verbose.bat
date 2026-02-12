@echo off
REM Script para ejecutar lake build con toda la información disponible
REM Captura stdout, stderr y lo guarda en build_log.txt

echo Building ZfcSetTheory project...
echo Timestamp: %date% %time%
echo.

REM Ejecutar lake build y capturar toda la salida
lake build > build_log.txt 2>&1

REM Mostrar el resultado
echo.
echo Build completado. Revisa build_log.txt para ver los detalles.
echo.
type build_log.txt

pause
