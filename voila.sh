#!/bin/bash

function abort() {
  echo $@ >&2
  exit 1
}

JAR_IN_TARGET="./target/scala-2.13/voila.jar"
JAR_IN_HERE="./voila.jar"
JAR=

if [ -f "$JAR_IN_TARGET" ]; then
  JAR=$JAR_IN_TARGET
elif [ -f "$JAR_IN_HERE" ]; then
  JAR=$JAR_IN_HERE
else
  abort "Could not find voila.jar"
fi

echo "Running Voila from $JAR"

java \
  -Dlogback.configurationFile=logback.xml \
  -Dfile.ending=UTF8 \
  -Xss128m \
  -jar "$JAR" \
  $@
