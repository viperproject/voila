@echo off
SetLocal EnableDelayedExpansion

REM ======== Basic configuration ========

set BASE_DIR=%~dp0
set MAIN=com.martiansoftware.nailgun.NGServer

REM ======== Arguments ========

set VOILA=voila
set FWD_ARGS=

:parse_args
if not %1.==. (
  if /I %1.==jar. (
		set VOILA=%2
		shift
		shift
	) else (
		set FWD_ARGS=%FWD_ARGS% %1
		shift
	)

	goto :parse_args
)

set VOILA_JAR=%BASE_DIR%\%VOILA%.jar

REM ======== Validation ========

if not exist %VOILA_JAR% (
  echo %CD%
  echo Error: Cannot find %VOILA_JAR%
  goto exit
)

REM ======== Path-dependent configuration ========

set JAVA_EXE=java
set CP=%BASE_DIR%\nailgun-server-0.9.1.jar
set CP=%CP%;%VOILA_JAR%

REM ======== Java ========

set JVM_OPTS=-Xss64m
set MAIN_OPTS=
set CMD=%JAVA_EXE% %JVM_OPTS% -cp "%CP%" %MAIN% %MAIN_OPTS% %FWD_ARGS%

REM ======== Executing  ========

REM echo.
REM echo %CMD%
REM echo.

call %CMD%

:exit
exit /B 0
