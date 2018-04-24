@echo off
SetLocal EnableDelayedExpansion

REM ======== Basic configuration ========

set BASE_DIR=%~dp0
set MAIN=viper.voila.VoilaRunner

REM ======== Arguments ========

set USE_NG=false
set LOGBACK_XML=%BASE_DIR%\..\..\conf\logback.xml
set VOILA_JAR=%BASE_DIR%\..\..\target\scala-2.11\voila.jar
set FWD_ARGS=

:parse_args
if not %1.==. (
  if /I %1.==ng. (
    set USE_NG=%2
    shift
    shift
  ) else if /I %1.==logback. (
		set LOGBACK_XML=%2
		shift
		shift
  ) else if /I %1.==jar. (
		set VOILA_JAR=%2
		shift
		shift
	) else (
		set FWD_ARGS=%FWD_ARGS% %1
		shift
	)

	goto :parse_args
)

REM ======== Validation ========

if not exist %VOILA_JAR% (
  echo %CD%
  echo Error: Cannot find %VOILA_JAR%
  goto exit
)

REM ======== Java ========

set JAVA_EXE=java
set JVM_OPTS=-Xss64m -Dlogback.configurationFile=%LOGBACK_XML%
set CP=%VOILA_JAR%

REM ======== Voila ========

set MAIN_OPTS=
REM --z3Exe %BASE_DIR%\programs\z3\bin\z3.exe

REM ======== Command ========

set NG=%BASE_DIR%\ng.exe

if /I %USE_NG%==true (
  set CMD=%NG% %MAIN% %MAIN_OPTS% %FWD_ARGS%
) else (
  set CMD=%JAVA_EXE% %JVM_OPTS% -cp "%CP%" %MAIN% %MAIN_OPTS% %FWD_ARGS%
)

REM ======== Executing  ========

REM echo.
REM echo %CMD%
REM echo.

call %CMD%

:exit
exit /B 0
