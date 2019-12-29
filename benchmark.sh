#!/bin/bash

PROGRAM_NAME=${0##*/} # https://stackoverflow.com/a/3588939

PAUSE="false"
VOILATESTS_REPETITIONS=10
VOILATESTS_CSV="benchmark_$(date +%Y-%m-%d_%H-%M).csv"
VOILATESTS_TARGET="src/test/resources/"
VOILATESTS_VLOPTS=

function usage() {
  echo "Usage:"
  echo "  $PROGRAM_NAME [options]";
  echo
  echo "Options:"
  echo "  -h, --help"
  echo "  -t, --target-directory <path/to/target/files/> (default: $VOILATESTS_TARGET)"  
  echo "  -p, --pause [true|false] (default: $PAUSE, if empty: true)"
  echo "  -r, --repetitions <n> (default: $VOILATESTS_REPETITIONS)"
  echo "  -c, --csv-file <path/to/file.csv> (default: $VOILATESTS_CSV)"
  echo "  -a, --voila-args <args> (optional)"
  echo "          Additional Voila arguments. <args> must have the following"
  echo "          format: a comma-separated list of Voila arguments, with an "
  echo "          equals sign (i.e. '=') between key-value arguments."
  echo
  echo "JVM properties: "
}

function die() {
  EXIT_CODE=$1
  shift
  echo $@ >&2
  exit $EXIT_CODE
}

function quit_or_continue() {
  read -p "Press Q to abort, any other key to continue ..." -n 1 -s KEY
  echo
  if [[ ${KEY^^} == "Q" ]]; then exit; fi # https://stackoverflow.com/a/32210715
}

function set_boolean_flag() {
  local -n REFVAR=$1 # https://stackoverflow.com/a/50281697

  if [[ $3 == "" ]]; then
    REFVAR="true"
  else
    [[ $3 == "true" ]] || [[ $3 == "false" ]] || die 2 "Option '$2' takes arguments 'true' or 'false', but got '$3'"
    REFVAR=$3
  fi  
}

# Declare valid arguments and parse provided ones
TEMP=$(getopt \
-n $PROGRAM_NAME \
-o hp::t:r:c:a: \
--long \
pause::,\
target-directory:,\
repetitions:,\
csv-file:,\
voila-args:,\
help \
-- "$@")
# --quiet \  ## suppress getopt errors

# if [ $? -ne 0 ]; then
#   echo "Error parsing arguments. Try $PROGRAM_NAME --help" >&2
#   exit 2
# fi
[ $? -eq 0 ] || { echo; usage; exit 2; }

eval set -- "$TEMP"
while true; do
  case $1 in
    -h|--help) usage; exit 0 ;;
    -p|--pause)
      set_boolean_flag PAUSE $1 $2
      shift ;;
    -t|--target-directory) VOILATESTS_TARGET=$2; shift ;;    
    -r|--repetitions) VOILATESTS_REPETITIONS=$2; shift ;;
    -c|--csv-file) VOILATESTS_CSV=$2; shift ;;
    -a|--voila-args) VOILATESTS_VLOPTS=$2; shift ;;
    --) shift; break ;; # no more arguments to parse                                
    *) die 2 "Unhandled option '$1'" ;;
  esac
  shift
done

# echo "Trailing arguments \$@: '$@'"

([[ $VOILATESTS_TARGET != "" ]] && [[ -d $VOILATESTS_TARGET ]]) || die 1 "Target '$VOILATESTS_TARGET' is not a directory"

# http://mywiki.wooledge.org/BashFAQ/050
SBT_ARGS="
  test:runMain 
  -DVOILATESTS_TARGET=$VOILATESTS_TARGET
  -DVOILATESTS_REPETITIONS=$VOILATESTS_REPETITIONS 
  -DVOILATESTS_CSV=$VOILATESTS_CSV
  -DVOILATESTS_VLOPTS=$VOILATESTS_VLOPTS
  org.scalatest.tools.Runner 
  -o -s 
  viper.voila.PortableVoilaTests"

if [[ $PAUSE == "true" ]]; then
  echo "About to execute sbt with the following arguments: $SBT_ARGS"
  echo
  quit_or_continue
fi

sbt "$SBT_ARGS"
