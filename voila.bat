@echo off
SetLocal EnableDelayedExpansion

set JAR_IN_TARGET=".\target\scala-2.13\voila.jar"
set JAR_IN_HERE=".\voila.jar"
set JAR=

if exist "%JAR_IN_TARGET%" (
  set JAR=%JAR_IN_TARGET%
) else (
  if exist "%JAR_IN_HERE%" (
    set JAR=%JAR_IN_HERE%
  ) else (
    echo Error: Neither found %JAR_IN_TARGET%, nor %JAR_IN_HERE%. Did you download a prebuilt JAR file, or sbt-assembled one yourself ^(see README.md^)?
    exit /b 1
  )
)

java ^
  -Dlogback.configurationFile=logback.xml ^
  -Dfile.ending=UTF8 ^
  -Xss128m ^
  -jar "%JAR%" ^
  %*

exit /b 0
