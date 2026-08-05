#!/bin/bash
# `set_option maxErrors` inside the file does NOT lift the cap -- the message
# limit is read from the initial options, before the file's commands run.  So it
# goes on the command line, and each probe is elaborated directly with
# `lake env lean` rather than through `lake build`.
set -u
export PATH=$HOME/.elan/bin:$PATH
HERE=$(cd "$(dirname "$0")" && pwd)
MODE=${1:-one}   # one | all | vacuity
# The scripts use 3.12 f-string nesting; a bare `python3` is 3.6 on some
# clusters and dies with a SyntaxError that reads like a bug in the emitter.
PY=${PYTHON:-$(command -v python3.12 || command -v python3)}
SRC=$(ls Descent/*.lean | grep -v TProbe)
rm -f Descent/TProbe*.lean
case "$MODE" in
  all)     "$PY" "$HERE/mutate.py" --all-at-once Descent $SRC
           G=TACGUARD-C2 ;;
  vacuity) "$PY" "$HERE/mutate.py" --vacuity Descent $SRC
           G=VACGUARD-C3 ;;
  *)       "$PY" "$HERE/mutate.py" Descent $SRC
           G=TACGUARD-C1 ;;
esac
"$PY" "$HERE/calibrate.py" Descent $G
rm -rf .mutlogs && mkdir -p .mutlogs
# The options MUST be on the command line.  `set_option maxErrors` inside the
# file does not lift the message cap, and `lake env lean` does not apply the
# library's `leanOptions`, so `autoImplicit` has to be turned off here or a
# dropped binder silently returns as a fresh implicit variable.
ls Descent/TProbe*.lean | \
  xargs -P "${JOBS:-24}" -I{} sh -c 'lake env lean -DmaxErrors=1000000 \
      -DautoImplicit=false -DrelaxedAutoImplicit=false "$1" \
      > .mutlogs/$(basename "$1" .lean).log 2>&1' _ {}
cat .mutlogs/*.log > mutation-$MODE.log
rm -rf .mutlogs
echo "TRUNCATED=$(grep -c 'maximum number of errors' mutation-$MODE.log)"
case "$MODE" in
  all)     "$PY" "$HERE/score.py" mutation-$MODE.log Descent ALLMUT UNCONDITIONAL ;;
  vacuity) "$PY" "$HERE/score.py" mutation-$MODE.log Descent VACMUT VACUOUS ;;
  *)       "$PY" "$HERE/score.py" mutation-$MODE.log Descent MUT DROPPABLE ;;
esac
rm -f Descent/TProbe*.lean
