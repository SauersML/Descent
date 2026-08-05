#!/usr/bin/env bash
# Run the GitHub Actions gate list, in order, on a machine that can build.
#
#   /Users/user/msi-node/msi 'PARTITION=sioux bash /projects/standard/hsiehph/sauer354/descent/scripts/ci-mirror.sh'
#
# WHY THIS EXISTS. `prover.yml` is fifteen gates and only one of them is the
# Lean build. The other fourteen are Python, they are ordered -- calibrations
# gate the detectors they calibrate -- and a path or import error in any of them
# fails the workflow just as hard as a broken proof. Discovering that from a
# pushed commit costs a full remote round trip per attempt, and the flatten
# touched every one of their paths at once.
#
# THIS SCRIPT IS NOT THE AUTHORITY; `prover.yml` IS. Keeping the two in step is
# the whole risk, so the list below is written in the same order, with the same
# working directories, and `workflow_paths.py` -- which reads prover.yml itself
# and asserts every path it names is tracked in git -- runs as one of the steps.
# A step that exists here and not there, or vice versa, is a defect in this file.
#
# It does NOT reproduce the runner: no cold toolchain, no cache restore, no
# `lake exe cache get`. It answers exactly one question -- would these fifteen
# commands pass on this tree -- and it answers it in minutes rather than in a
# push.
set -uo pipefail

ROOT=${DESCENT_ROOT:-/projects/standard/hsiehph/sauer354}
REPO=${DESCENT_REPO:-$ROOT/descent}
PY=${DESCENT_PY:-/usr/bin/python3.12}

export PATH=$ROOT/.elan/bin:$PATH
export ELAN_HOME=$ROOT/.elan

# Same compute-node guarantee as cluster-lean-build.sh, and for the same reason:
# the relay lands on a login node, and the Lean build here is not a small job.
CPUS=${CPUS:-32}
MEM=${MEM:-96g}
TIMELIMIT=${TIMELIMIT:-1:00:00}
if [ -z "${SLURM_JOB_ID:-}" ]; then
  exec sbatch --job-name=ci-mirror --partition="${PARTITION:-agsmall}" \
    --nodes=1 --ntasks=1 \
    --cpus-per-task="$CPUS" --mem="$MEM" --time="$TIMELIMIT" \
    --output="$ROOT/ci-mirror-%j.out" "$0" "$@"
fi

cd "$REPO" || { echo "NO_REPO"; exit 1; }
git fetch -q origin && git merge -q --ff-only origin/main 2>/dev/null \
  && echo "SYNC_OK" || echo "SYNC_FAILED_RUNNING_AT_EXISTING_HEAD"
echo "CI_MIRROR_AT_REV=$(git rev-parse --short HEAD)"
echo

_fail=0
_ran=0

# Every gate reports its own name and exit code on one line, so the log can be
# read by grepping for STEP_FAIL and nothing else.  A step is never skipped on
# an earlier failure: the point of running all of them is to learn about all of
# them in one pass, which is exactly what a push-and-wait loop cannot do.
step() {
  local name=$1 wd=$2; shift 2
  _ran=$((_ran + 1))
  local log="$ROOT/ci-mirror-${SLURM_JOB_ID:-manual}-$(printf '%02d' "$_ran").log"
  ( cd "$REPO/$wd" && "$@" ) > "$log" 2>&1
  local rc=$?
  if [ "$rc" -eq 0 ]; then
    echo "STEP_OK   [$_ran] $name"
  else
    echo "STEP_FAIL [$_ran] $name  (exit $rc)  log: $log"
    sed -n '1,12p' "$log" | sed 's/^/          | /'
    _fail=$((_fail + 1))
  fi
}

step "Build project"                      .                                lake build Descent ValidationShared
step "Calibrate the laundering detector"  .                                "$PY" validation/code/test_check.py
step "Code validation (source text)"      .                                "$PY" validation/code/check.py
step "Code validation (elaborated env)"   .                                lake env lean validation/code/Check.lean
step "Verify arithmetic runtime semantics" validation/empirical/invariants "$PY" test_lean_semantics.py
step "Regenerate extracted definition table" .                             "$PY" validation/empirical/extract/emit.py
step "Calibrate the identity gate"        validation/empirical/differential "$PY" test_identity_gate.py
step "Calibrate the round-trip checks"    validation/empirical/differential "$PY" test_roundtrip.py
step "Parser and translator ground truth" validation/empirical/extract     "$PY" test_parser.py
step "Calibrate the differential battery gate" validation/empirical/differential "$PY" test_battery_gate.py
step "Differential battery"               validation/empirical/differential "$PY" run.py
step "Calibrate the metamorphic gate"     .                                "$PY" validation/empirical/metamorphic/test_metamorphic.py
step "Metamorphic relation gate"          .                                "$PY" validation/empirical/metamorphic/run.py
step "Workflow-path guard"                .                                "$PY" validation/code/workflow_paths.py
step "Vacuous reference evaluations"      .                                "$PY" validation/empirical/reference_eval/degenerate.py --gate

echo
echo "CI_MIRROR_STEPS=$_ran"
echo "CI_MIRROR_FAILED=$_fail"
[ "$_fail" -eq 0 ] && echo "CI_MIRROR=GREEN" || echo "CI_MIRROR=RED"
exit "$_fail"
