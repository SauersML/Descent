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
#   MATHLIB_ROOT=present|MISSING                      is the toolchain whole?
#   MATHLIB_OLEAN_COUNT=<n>                           how whole? healthy ~2934
#   TOOLCHAIN_DAMAGED=1                               emitted only when broken
#   GUARD_EXIT=<code>                                 structural guard result
#   LAKE_EXIT=<code>                                  lake's own exit status
#   MODULE_STATUS <mod> COMPILED|STALE|ABSENT         per module, one line each
#   MODULES_COMPILED / MODULES_STALE / MODULES_ABSENT summary counts
#
# HOW TO READ A LOG, in order. Absence is the signal:
#
#   no BUILT_AT_REV   -> the job died before sync finished. No build happened.
#   TOOLCHAIN_DAMAGED -> treat error lists as SUSPECT, not as void, and see
#                        "ON THE 59" below before concluding anything. A
#                        damaged olean chain really can report definitions that
#                        exist as unknown identifiers -- but on 2026-08-02 that
#                        explanation was applied to a 59-error list and builds
#                        were halted for hours, and the errors turned out to be
#                        REAL. The root cause was a namespace boundary, not a
#                        broken chain: five declarations in
#                        `Calibrator.TransportedMetrics` were referenced bare,
#                        and Lean AUTO-BINDS an unresolved bare name as an
#                        implicit variable rather than reporting it missing,
#                        which is why one cause produced three different error
#                        texts ("unknown identifier", "function expected at",
#                        and the discriminating "LOCAL VARIABLE ... has no
#                        definition").
#                        The lesson: a plausible mechanism that explains the
#                        symptom is not a diagnosis. BUILD SOMETHING SMALL --
#                        one leaf module -- and see whether it is clean. That
#                        test takes minutes and settles it.
#   no LAKE_EXIT      -> lake was killed or is still running. INCOMPLETE, not
#                        clean; a truncated log with few errors is not a result.
#   LAKE_EXIT=0       -> build succeeded.
#   otherwise         -> count Lean errors, and ONLY Lean errors:
#
#       grep -c '^error: proofs/'      <- correct
#       grep -c '^error:'              <- WRONG, matches git and lake messages
#
#   THEN, AND THIS IS NOT OPTIONAL, check MODULE_STATUS for the files you care
#   about. "NO ERRORS FOR FILE X" IS ONLY MEANINGFUL IF X COMPILED. On
#   2026-08-02 a cancelled build produced a log with zero errors in
#   PortabilityDrift; the file was 76 seconds into compiling and its olean was
#   stale, so the clean record was absence of evidence and the 59-error cluster
#   it appeared to clear was still entirely unmeasured. A killed, cancelled or
#   timed-out build leaves a log INDISTINGUISHABLE from a clean partial one.
#
#   The mtime comparison is the sixth check added to this file and the only one
#   that catches all six causes at once, because it tests the ARTIFACT rather
#   than the log: whatever went wrong -- relay kill, missing PATH, aborted &&
#   chain, lock deadlock, miscounted grep, cancellation -- an olean older than
#   its source means that module was not built. An error count without a
#   compiled-module list is the same defect as an error count without a commit.
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
# * DO NOT REBUILD MATHLIB CASUALLY. Check the count first:
#       find .lake/packages/mathlib/.lake/build/lib/lean -name '*.olean' | wc -l
#
#   `lake exe cache get` DOES NOT WORK ON THIS CLUSTER. Verified 2026-08-02, and
#   the reason is not what it looks like: the download is fine, but `cache` is a
#   Lean EXECUTABLE that lake must compile first, and compiling anything to
#   native code needs the toolchain's clang, which cannot start here --
#       clang: /lib64/libm.so.6: version `GLIBC_2.29' not found
#              (required by .../libclang-cpp.so.19.1 and .../libLLVM.so.19.1)
#   while every node ships GLIBC 2.28 (`ldd --version` -> 2.28). So the advice
#   this file used to give -- "restore in minutes with cache get" -- sends you
#   to a dead end, and recompiling Mathlib from source is currently the ONLY
#   path to a complete Mathlib. Budget hours, submit it once, centrally, and let
#   it finish rather than cancelling and restarting.
#
#   Note WHY .olean builds still work while `cache` does not: producing an olean
#   is pure Lean elaboration and never invokes clang. Only native-code targets
#   (executables, `:c.o`) need it. That is the whole difference.
#
#   UNTESTED LEAD, worth ten minutes before anyone budgets hours again: system
#   `gcc` is 8.5.0 and DOES compile against the Lean headers here (verified with
#   a trivial translation unit and `-I <toolchain>/include`). If lake honours
#   `LEAN_CC=gcc`, `cache get` may build and the whole problem evaporates. I did
#   not run it, because doing so writes into a shared tree during someone else's
#   rebuild. Try it in an isolated clone first.
# * Never run heavy compute on a login node; submit with sbatch.
# ---------------------------------------------------------------------------

set -uo pipefail

ROOT=/projects/standard/hsiehph/sauer354
REPO=$ROOT/gnomon
TARGETS=("$@")
if [ ${#TARGETS[@]} -eq 0 ]; then TARGETS=(Calibrator); fi

export PATH=$ROOT/.elan/bin:$PATH
export ELAN_HOME=$ROOT/.elan

# COMPUTE-NODE GUARANTEE. The bare relay lands on a login node (ahl03), so a
# `lake build` invoked through it runs there. On 2026-08-02 that put 160 lean
# processes on shared interactive infrastructure at load average 31, each
# getting about one percent of a core, while recompiling Mathlib. Nobody chose
# that; the invocation everyone copied did it silently. So the script resubmits
# itself rather than trusting the caller to remember.
#
# CAPACITY IS NOT THE CONSTRAINT. agsmall, aglarge, msismall and sioux are all
# available; pick whichever has queue with PARTITION=<p>. Serialising every
# build against one shared checkout was the right answer only while everyone
# shared one `.lake` and contended for its package lock. With real capacity the
# better answer is SEPARATE BUILD TREES ON SEPARATE NODES, and the lock stops
# being a bottleneck at all -- but a separate tree only helps if its `.lake` is
# genuinely COPIED. `cp -al` hardlinks and a symlink both share the lock inode
# and deadlock exactly as the shared tree does.
#
# --output must be on shared storage under /projects. /tmp is node-local, so a
# log written there is invisible to the next call -- and the relay does not land
# on the same node twice, which makes that a silent cause of an empty log. On
# acn112/116 /tmp is also RAM-backed tmpfs shared with other users.
if [ -z "${SLURM_JOB_ID:-}" ]; then
  exec sbatch --job-name=leanbld --partition="${PARTITION:-agsmall}" \
    --nodes=1 --ntasks=1 \
    --cpus-per-task=8 --mem=32g --time=2:00:00 \
    --output="$ROOT/leanbuild-%j.out" "$0" "$@"
fi

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

# Toolchain precondition. A build against a half-rebuilt Mathlib emits a
# plausible error list that means nothing, which is the failure mode this whole
# file exists to prevent -- so refuse rather than report it. Restore with
# `lake exe cache get` (a download, minutes) rather than recompiling (hours).
MLROOT=.lake/packages/mathlib/.lake/build/lib/lean/Mathlib.olean
OLEANS=$(find .lake/packages/mathlib/.lake/build/lib/lean -name '*.olean' 2>/dev/null | wc -l)
echo "MATHLIB_OLEAN_COUNT=$OLEANS"
if [ -f "$MLROOT" ]; then echo "MATHLIB_ROOT=present"; else echo "MATHLIB_ROOT=MISSING"; fi
if [ ! -f "$MLROOT" ] || [ "$OLEANS" -lt 2900 ]; then
  echo "TOOLCHAIN_DAMAGED=1"
  if [ "${FORCE_DAMAGED_BUILD:-0}" != "1" ]; then
    echo "REFUSING_TO_BUILD: error lists from a damaged olean chain are not evidence."
    echo "Restore with 'lake exe cache get', or set FORCE_DAMAGED_BUILD=1 to override."
    exit 2
  fi
fi

python3 -S scripts/check-identifications.py > "$ROOT/guard-${SLURM_JOB_ID:-manual}.txt" 2>&1
echo "GUARD_EXIT=$?"

lake build "${TARGETS[@]}"
echo "LAKE_EXIT=$?"

# ---------------------------------------------------------------------------
# PER-MODULE COMPILED/STALE TABLE.
#
# This tests the ARTIFACT, not the log, and that is the whole point. Every
# other check in this file infers what happened from what lake printed; this
# one asks the filesystem whether each module's olean is newer than its source.
# An olean older than its source means that module WAS NOT BUILT in this run,
# no matter how clean the log looks.
#
# It exists because on 2026-08-02 a cancelled build produced a log with zero
# errors in PortabilityDrift, which read as a 59-error cluster cleared. The
# file had been compiling for 76 seconds when the job was cancelled and its
# olean was stale. "No errors for file X" is only meaningful if X compiled, and
# a killed, cancelled or timed-out build is indistinguishable from a clean
# partial one at the level of the log.
#
# Note the asymmetry that makes this worth running unprompted: a module can be
# STALE because it failed, or because the build never reached it, and BOTH look
# like silence. Only ABSENT/STALE/COMPILED distinguishes "clean" from "not
# attempted".
echo "--- MODULE STATUS ---"
_compiled=0; _stale=0; _absent=0
while IFS= read -r src; do
  rel=${src#proofs/}                 # Calibrator/Foo/Bar.lean
  mod=${rel%.lean}                   # Calibrator/Foo/Bar
  olean=".lake/build/lib/lean/${mod}.olean"
  name=${mod//\//.}                  # Calibrator.Foo.Bar
  if [ ! -f "$olean" ]; then
    echo "MODULE_STATUS $name ABSENT"; _absent=$((_absent+1))
  elif [ "$olean" -nt "$src" ]; then
    echo "MODULE_STATUS $name COMPILED"; _compiled=$((_compiled+1))
  else
    echo "MODULE_STATUS $name STALE"; _stale=$((_stale+1))
  fi
done < <(find proofs -name '*.lean' | sort)
echo "MODULES_COMPILED=$_compiled"
echo "MODULES_STALE=$_stale"
echo "MODULES_ABSENT=$_absent"
