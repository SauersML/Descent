#!/usr/bin/env bash
# Instrumented Lean build against the shared cluster checkout.
#
# Run this from the relay, never on this laptop:
#
#   /Users/user/msi-node/msi 'bash /projects/standard/hsiehph/sauer354/gnomon/scripts/cluster-lean-build.sh Calibrator.ProjectionShiftBounds Calibrator.MetricSpecificPortability'
#
# with no arguments it builds the whole Calibrator target.
#
# ---------------------------------------------------------------------------
# WHY THIS EXISTS
#
# On 2026-08-02 a build report meant nothing five separate times, each with a
# different cause and the same symptom:
#
#   1. the relay killed the process tree when the call returned, so a job that
#      ran for 25 minutes wrote nothing;
#   2. `lake` was absent from the relay's PATH, so the job died instantly in a
#      way that reads as "never started";
#   3. an `&&` chain aborted at a stuck `git pull`, so lake never ran;
#   4. concurrent `lake build` against one checkout serialised on the package
#      lock in `.lake`, parking at high wall clock and near-zero CPU;
#   5. the reader counted `^error:` and matched a *git* line -- "the following
#      untracked working tree files would be overwritten by merge" -- so a job
#      in which lake never ran reported "1 error", which read as PROGRESS
#      against the previous run's count.
#
# The fifth is the worst, because the other four produce an absence and it
# produced a plausible number. A build that never happened was indistinguishable
# from a nearly-clean one.
#
# The rule the five share: A MEASUREMENT THAT CANNOT REPORT ITS OWN ABSENCE WILL
# EVENTUALLY REPORT SOMEONE ELSE'S ANSWER AS ITS OWN. So this script makes the
# log say what happened to it.
#
# ---------------------------------------------------------------------------
# THE LOG CONTRACT -- every reader depends on these, do not reword them
#
#   SYNC_OK | SYNC_FAILED_BUILDING_AT_EXISTING_HEAD   did the checkout move?
#   BUILT_AT_REV=<sha>                                what was actually built
#   GUARD_EXIT=<code>                                 structural guard result
#   LAKE_EXIT=<code>                                  lake's own exit status
#
# HOW TO READ A LOG, in order. Absence is the signal:
#
#   no BUILT_AT_REV   -> the job died before sync finished. No build happened.
#   no LAKE_EXIT      -> lake was killed or is still running. INCOMPLETE, not
#                        clean; a truncated log with few errors is not a result.
#   LAKE_EXIT=0       -> build succeeded.
#   otherwise         -> count Lean errors, and ONLY Lean errors:
#
#       grep -c '^error: proofs/'      <- correct
#       grep -c '^error:'              <- WRONG, matches git and lake messages
#
# Always quote BUILT_AT_REV when reporting a count. An error list without a
# commit is not evidence; that rule cost this effort three false reports before
# it was adopted.
#
# ---------------------------------------------------------------------------
# BEFORE YOU RUN IT
#
# * ONE BUILD AT A TIME against the shared checkout. Concurrent invocations
#   serialise on the `.lake` package lock and nobody finishes. A private clone
#   only helps if its `.lake` is genuinely COPIED -- `cp -al` hardlinks and a
#   symlink both share the lock inode and deadlock identically.
# * Diagnose a suspected deadlock by CPU TIME, not by the log:
#       ps -eo pid=,etimes=,time=,args= | grep -E 'lake|lean'
#   parked on the lock  = large elapsed, near-zero CPU.
#   never started       = neither.
#   actually working    = CPU climbing.
# * DO NOT REBUILD MATHLIB. It is warm at ~2934 oleans. If the count is far
#   below that or `Mathlib.olean` is missing, the olean chain is broken and
#   every error list from this checkout is untrustworthy -- definitions that
#   plainly exist get reported as unknown identifiers. Restore with
#   `lake exe cache get`, which downloads prebuilt oleans in minutes, rather
#   than recompiling for hours. Check first:
#       find .lake/packages/mathlib/.lake/build/lib/lean -name '*.olean' | wc -l
# * Never run heavy compute on a login node; submit with sbatch.
# ---------------------------------------------------------------------------

set -uo pipefail

ROOT=/projects/standard/hsiehph/sauer354
REPO=$ROOT/gnomon
TARGETS=("$@")
if [ ${#TARGETS[@]} -eq 0 ]; then TARGETS=(Calibrator); fi

export PATH=$ROOT/.elan/bin:$PATH
export ELAN_HOME=$ROOT/.elan

cd "$REPO" || { echo "NO_REPO"; exit 1; }

# Sync forward only. A fast-forward merge cannot discard a commit: it refuses
# instead, which is what we want on a clone that has no push credentials and so
# routinely holds commits that exist nowhere else. Never `reset --hard` here --
# `git fetch && git reset --hard origin/main` reads as maximally careful and is
# exactly what orphans those commits.
git fetch -q origin
if git merge -q --ff-only origin/main 2>/dev/null; then
  echo SYNC_OK
else
  echo SYNC_FAILED_BUILDING_AT_EXISTING_HEAD
fi

echo "BUILT_AT_REV=$(git rev-parse --short HEAD)"

python3 -S scripts/check-identifications.py > "$ROOT/guard-${SLURM_JOB_ID:-manual}.txt" 2>&1
echo "GUARD_EXIT=$?"

lake build "${TARGETS[@]}"
echo "LAKE_EXIT=$?"
