#!/usr/bin/env bash
# Instrumented Lean build against the shared cluster checkout.
#
# Run this from the relay, never on this laptop:
#
#   /Users/user/msi-node/msi 'bash /projects/standard/hsiehph/sauer354/gnomon/scripts/cluster-lean-build.sh Descent.ProjectionShiftBounds Descent.MetricSpecificPortability'
#
# with no arguments it builds the whole Descent target.
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
#   LAUNDER_GUARD_EXIT=<code>                         source-text laundering guard
#   LAUNDER_ENV_EXIT=<code>|SKIPPED_BUILD_FAILED      elaborated-telescope scan
#   LAKE_EXIT=<code>                                  lake's own exit status
#   MODULE_STATUS <mod> COMPILED|STALE|ABSENT         per module, one line each
#   MODULES_COMPILED / MODULES_STALE / MODULES_ABSENT summary counts
#   ORPHAN_MODULES=<n> / ORPHAN <mod>                 on disk, unreachable from root
#   COVERAGE_EXIT=0|1                                 did the build cover the corpus?
#   WHOLE_CORPUS_INCOMPLETE=0|1                       full build left work undone
#   STALE_MTIME_ONLY=<n>                              stale mtimes, lake says clean
#
#   COVERAGE_EXIT=1 or WHOLE_CORPUS_INCOMPLETE=1 exits the script with code 3 even
#   when LAKE_EXIT=0. THAT COMBINATION IS THE POINT: lake can succeed on every
#   target it was given and still have compiled none of the modules you care
#   about. `LAKE_EXIT=0` means "the targets built", never "the corpus is green".
#
#   STALE_MTIME_ONLY is the deliberately NON-fatal case: `git merge` bumps source
#   mtimes, lake skips the rebuild on content traces, and the olean ends up older
#   than its source without anything being wrong. The first run of the coverage
#   guard fired on four such modules in a build with LAKE_EXIT=0 and zero errors.
#   A guard that fires on the normal case gets ignored -- so ABSENT (no olean at
#   all, never built under any reading) is fatal, while STALE is fatal only when
#   lake ALSO failed.
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
#                        `Descent.TransportedMetrics` were referenced bare,
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
#
#                        AUTO-BINDING RECURRED TWICE ON 2026-08-02 EVENING, and
#                        the two cases wanted OPPOSITE repairs. Test which you
#                        have with a two-second grep for the bare name before
#                        theorising -- that grep settles it either way, and it
#                        correctly falsified this hypothesis for four other
#                        files the same evening.
#
#                          CausalInference: 35 errors, two texts, one cause.
#                          `r2FromSignalVariance` moved into
#                          `Descent.TransportedMetrics`, and OPEN DOES NOT
#                          TRAVEL THROUGH IMPORT -- the `open` that
#                          `OpenQuestions` added for itself did nothing for a
#                          file that imports `OpenQuestions`. That is how a
#                          consumer gets missed. Repair: add the `open`.
#
#                          Conventions: same two texts, and `open` would have
#                          been WRONG. The bare name was the left side of a
#                          bridge theorem `bare = TransportedMetrics.bare`
#                          whose local definition had been deleted. Adding the
#                          `open` would have made it
#                          `TransportedMetrics.X = TransportedMetrics.X`, i.e.
#                          silently converted a build error into a VACUOUS
#                          theorem -- and its neighbour was already exactly
#                          that, `X = X` proved by `unfold X X`. Repair:
#                          delete the dead bridge.
#
#                        So: `open` is right only when the bare name has a real
#                        referent AND the statement stays non-vacuous. CHECK
#                        THAT THE TWO SIDES STILL DIFFER before adding it.
#
#   A FILE THAT FAILS TO PARSE HAS NO ERROR COUNT. `unexpected token 'end';
#                        expected 'lemma'` and friends TRUNCATE the measured
#                        region: everything below the parse error is never
#                        elaborated, so the file's error count is a FLOOR, not
#                        a measurement. On 2026-08-02 `DemographicHistory`
#                        reported "2 errors" while everything below line 69 was
#                        unmeasured. This is the same defect as an error count
#                        without a commit and an error count without a
#                        MODULE_STATUS: a number that looks like a measurement
#                        and is a lower bound. Grep the error list for parse
#                        errors FIRST -- `unexpected token`, `expected` -- and
#                        treat any file carrying one as UNMEASURED, not as
#                        nearly clean.
#   `-/` INSIDE PROSE ENDS THE COMMENT. A doc comment containing the ordinary
#                        phrase `low-/high-frequency` closes at that slash: the
#                        remaining prose is parsed as commands and the file dies
#                        with `unexpected identifier; expected command` dozens of
#                        lines later, nowhere near the cause. Cost a whole-corpus
#                        build on 2026-08-02. When a parse error points at plain
#                        English, search the comment ABOVE it for `-/`; the usual
#                        sources are `X-/Y` alternatives and arrow-like glyphs.
#   no LAKE_EXIT      -> lake was killed or is still running. INCOMPLETE, not
#                        clean; a truncated log with few errors is not a result.
#   LAKE_EXIT=0       -> build succeeded.
#   otherwise         -> count Lean errors, and ONLY Lean errors:
#
#       grep -c '^error: Descent/'     <- correct
#       grep -c '^error:'              <- WRONG, matches git and lake messages
#
#   READING LEAN ERRORS: THREE SHAPES OF "unfold failed", ALL PRINTING THE SAME
#   MESSAGE AND ALL WANTING DIFFERENT REPAIRS. Found the hard way on
#   2026-08-02, across DGP and PortabilityDrift:
#
#     (a) THE NAME MOVED.       A definition no longer routes through the name
#                               being unfolded. Repair: restore the routing.
#                               Canonical instance, 2026-08-02:
#                               `PopulationGeneticsFoundations.hetDecayFactor`
#                               still RE-TYPED the body of
#                               `hetDecayFromScaled` instead of delegating to
#                               it, so `unfold hetDecayFactor
#                               hetDecayFromScaled` unfolded the copy and then
#                               found no second name left in the goal. A
#                               half-done "one home each" move looks exactly
#                               like a missing reducibility attribute. Repair
#                               is to DELEGATE, not to drop the second name --
#                               dropping it hides the duplicated body, which
#                               was the actual defect, and the same latent
#                               break was sitting in `Conventions` and
#                               `DemographicHistory`.
#     (b) THE REQUEST IS
#         IMPOSSIBLE.           The name is an inductive CONSTRUCTOR, e.g.
#                               `Pop.source`. Constructors have no body, so this
#                               could never have worked. Repair: DELETE the
#                               token; the surrounding proof is fine.
#     (c) THE REQUEST IS
#         REDUNDANT.            `unfold` is NOT idempotent. A name listed twice
#                               unfolds on the first occurrence and ERRORS on
#                               the second, because the constant is gone by
#                               then. Repair: delete the duplicate.
#
#   The message cannot distinguish these, and reading (b) as (a) sends you
#   hunting for reducibility attributes that do not exist. CHECK WHAT THE NAME
#   IS before theorising: `inductive` constructor, or `def`?
#
#   AND THE GENERAL FORM OF THAT TRAP, which cost the most time of anything
#   today: A TOOL REPORTS THE FAILURE IT CAN EXPRESS, NOT THE FAILURE THAT
#   OCCURRED. The clearest instance was `linarith failed to find a
#   contradiction` whose actual cause was a MISSING SIMP LEMMA: a `@[simp]`
#   pair had one half stated (`residualBurden_source`) and the other missing,
#   so target-side facts were phrased about one name while goals said another.
#   `linarith` was handed a hypothesis about a term ABSENT FROM ITS GOAL and
#   truthfully reported that it could not close the arithmetic. Nobody would
#   reach "missing bridge lemma" from that message. So when a tactic fails on
#   something that looks obviously true, READ THE PRINTED GOAL and check that
#   every hypothesis you supplied actually mentions a term that occurs in it.
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
#
# ---------------------------------------------------------------------------
# NEGATIVE RESULT: DO NOT REBUILD THE "DUPLICATE unfold ARGUMENT" SCANNER.
#
# Having found one `unfold` list that named the same constant twice, the
# obvious next move is a scan over every `unfold` block in a file. I wrote it
# on 2026-08-02. IT REPORTED TEN HITS, OF WHICH ONE WAS REAL, and it is not
# fixable by tightening the regex in any way I could see.
#
# The reason is structural. An `unfold` tactic's argument list continues onto
# following lines by INDENTATION, and the tactic lines that follow it are
# indented too. So any indent-based capture swallows the subsequent `have`,
# `exact` and `simp` lines, and then reports ordinary repeated words -- `have`,
# `exact`, `0`, `:=`, `by` -- as duplicate unfold arguments. Distinguishing a
# continued argument list from the next tactic needs the parser, not a regex.
#
# IT WAS NOT COMMITTED AND ITS OUTPUT WAS NOT USED AS EVIDENCE. The rule this
# is an instance of: a detector with a 90% false-positive rate is WORSE THAN NO
# DETECTOR, because it gets ignored within a day and its real hits become
# invisible along with the noise. Most checks that fail here fail by being
# unable to FIRE; this one fails by firing too easily, and that is equally
# disqualifying. The real duplicate was found by the compiler, which is the
# tool that actually parses the file.
# ---------------------------------------------------------------------------

set -uo pipefail

ROOT=${DESCENT_ROOT:-/projects/standard/hsiehph/sauer354}
# The cluster's default python3 is 3.6.8 and predates `from __future__ import
# annotations`, so a guard written against a modern Python dies with a
# SyntaxError and reports a NONZERO exit. A guard that never ran is then
# indistinguishable from a guard that failed, unless somebody reads the
# traceback. Pin the interpreter, and fail loudly if it is missing rather than
# falling back to one that cannot run the guards.
GUARD_PY=${DESCENT_PY:-/usr/bin/python3.12}
if ! "$GUARD_PY" -c 'import sys; assert sys.version_info >= (3, 9)' 2>/dev/null; then
  echo "GUARD_PY_UNUSABLE=$GUARD_PY"
  echo "!!! No usable Python for the guards. Set DESCENT_PY to a 3.9+ interpreter."
  echo "!!! Guard results below would be interpreter failures, not findings."
  exit 4
fi
echo "GUARD_PY=$GUARD_PY"


# The shared checkout runs many commits behind and carries dirty files, so a
# build of it reports the state of that tree rather than the state of the
# corpus. Point DESCENT_REPO at a clean clone at a named revision when you want
# a number anyone can trust, and record the revision beside the number.
REPO=${DESCENT_REPO:-$ROOT/gnomon}
TARGETS=("$@")
if [ ${#TARGETS[@]} -eq 0 ]; then TARGETS=(Descent); fi

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

"$GUARD_PY" -S validation/code/check.py --only identifications \
  > "$ROOT/guard-${SLURM_JOB_ID:-manual}.txt" 2>&1
echo "GUARD_EXIT=$?"

# Laundering guard.  Runs BEFORE lake, like the structural guard, because it reads
# source text and therefore needs no oleans -- a build that dies in the toolchain
# still gets this answer.  The elaborated-telescope half (the LAUNDERING scan in
# Check.lean) needs the oleans and runs after the build, below.
"$GUARD_PY" -S validation/code/check.py --only laundering \
  > "$ROOT/launder-${SLURM_JOB_ID:-manual}.txt" 2>&1
echo "LAUNDER_GUARD_EXIT=$?"
"$GUARD_PY" -S validation/code/check.py --only laundering --summary 2>&1 \
  | sed -n '3,20p' | sed 's/^/LAUNDER_/'

lake build "${TARGETS[@]}"
_lake_exit=$?
echo "LAKE_EXIT=$_lake_exit"

# The environment-level laundering scan needs a successful build: it walks the
# fully elaborated type of every `Descent` declaration.  Reporting it as
# SKIPPED when the build failed matters -- an absent scan must not read as a
# clean one, which is the rule the rest of this file was written around.
if [ "$_lake_exit" -eq 0 ]; then
  lake env lean validation/code/Check.lean \
    > "$ROOT/launder-env-${SLURM_JOB_ID:-manual}.txt" 2>&1
  echo "LAUNDER_ENV_EXIT=$?"
  grep -E '^LAUNDER_(SCANNED|PREMISES|FATAL|TOTAL)' \
    "$ROOT/launder-env-${SLURM_JOB_ID:-manual}.txt" || true
else
  echo "LAUNDER_ENV_EXIT=SKIPPED_BUILD_FAILED"
fi

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
  rel=$src                           # Descent/Foo/Bar.lean
  mod=${rel%.lean}                   # Descent/Foo/Bar
  olean=".lake/build/lib/lean/${mod}.olean"
  name=${mod//\//.}                  # Descent.Foo.Bar
  if [ ! -f "$olean" ]; then
    echo "MODULE_STATUS $name ABSENT"; _absent=$((_absent+1))
  elif [ "$olean" -nt "$src" ]; then
    echo "MODULE_STATUS $name COMPILED"; _compiled=$((_compiled+1))
  else
    echo "MODULE_STATUS $name STALE"; _stale=$((_stale+1))
  fi
done < <(find Descent Descent.lean -name '*.lean' | sort)
# validation is excluded on purpose, and the exclusion is not cosmetic.
# Two of its modules belong to the ValidationShared library, which this script
# is not asked to build, and three are detector scripts that run under
# `lake env lean` and by design never produce an olean at all. Counting those
# five as ABSENT made a fully green Descent build report WHOLE_CORPUS
# INCOMPLETE and exit 3, so a correct build looked like a failed one. A guard
# that fires on the healthy case is a guard everyone learns to ignore.
echo "MODULES_COMPILED=$_compiled"
echo "MODULES_STALE=$_stale"
echo "MODULES_ABSENT=$_absent"

# ---------------------------------------------------------------------------
# COVERAGE GUARD. THE BUILD MUST COVER ITS OWN CORPUS.
#
# On 2026-02 this script reported zero errors on whole-corpus builds, repeatedly,
# while eight modules were never compiled at all: `Descent.ResonanceSpectrum`
# and seven `Descent.BundleRigidity.*` submodules sat outside the import
# closure of `Descent.lean`, so `lake build Descent` never reached
# them. Naming them as explicit targets produced errors immediately -- a missing
# `Real.log` import that had been red all day. The root module itself was also
# never elaborated until `CondensationUnification` compiled, and it was carrying
# a theorem over two names that have never been defined in this corpus.
#
# So every "0 errors" excluded the one file that transitively covers everything.
# MODULES_ABSENT was reporting this truthfully the whole time, as a line in a
# summary that nobody interrogated. A count is not a signal until something
# fails on it. This is that something.
#
# The orphan check below is the durable half, and it does NOT depend on the
# build succeeding: it compares the files on disk against the transitive import
# closure of the root module. A file that no target can reach is UNBUILT, not
# clean, and adding it here is not the fix -- adding it to the ROOT is.
echo "--- COVERAGE ---"
_orphans=$(python3 - <<'PYEOF'
import os, re, sys
root = "Descent.lean"
if not os.path.exists(root):
    print("ROOT_MISSING"); sys.exit(0)
imports = {}
for d, _, fs in os.walk("Descent"):
    for f in fs:
        if f.endswith(".lean"):
            p = os.path.join(d, f)
            mod = p[:-5].replace(os.sep, ".")
            imports[mod] = re.findall(r"^import (Descent\.\S+)", open(p, encoding="utf-8").read(), re.M)
seen = set()
def walk(m):
    for i in imports.get(m, []):
        if i not in seen:
            seen.add(i); walk(i)
for r in re.findall(r"^import (Descent\.\S+)", open(root, encoding="utf-8").read(), re.M):
    seen.add(r); walk(r)
for o in sorted(set(imports) - seen):
    print(o)
PYEOF
)
if [ -n "$_orphans" ]; then
  echo "ORPHAN_MODULES=$(echo "$_orphans" | wc -l | tr -d ' ')"
  echo "$_orphans" | sed 's/^/ORPHAN /'
  echo "COVERAGE_EXIT=1"
  echo "!!! MODULES ON DISK ARE OUTSIDE THE ROOT IMPORT CLOSURE. They were NOT built,"
  echo "!!! and their silence in this log is ABSENCE OF EVIDENCE. Add them to"
  echo "!!! Descent.lean -- not to this script's target list."
  _coverage=1
else
  echo "ORPHAN_MODULES=0"
  echo "COVERAGE_EXIT=0"
  _coverage=0
fi

# On a whole-corpus run every module must actually have compiled. On a targeted
# run most modules are legitimately untouched, so this only fires for the full
# build -- otherwise it would cry wolf on every one-module check and be ignored,
# which is how a guard becomes decoration.
_whole=0
if [ ${#TARGETS[@]} -eq 1 ] && [ "${TARGETS[0]}" = "Descent" ]; then _whole=1; fi
#
# STALE IS NOT ALWAYS A FAILURE, and getting this wrong makes the guard useless.
# `git merge` rewrites every file it touches, which bumps source mtimes; lake
# then decides via CONTENT traces that the module is up to date and does not
# rebuild it, leaving an olean older than its source. That is a benign mtime
# artifact, not an unbuilt module -- and on the first run of this guard it fired
# on four modules in a build with LAKE_EXIT=0 and zero errors. A guard that cries
# wolf on the normal case gets ignored, which is how a guard becomes decoration.
#
# So the two signals are separated by what each can actually prove:
#   ABSENT  -> no olean exists. That module was NEVER built, under any reading.
#              Always a failure.
#   STALE   -> olean older than source. Only conclusive when lake did NOT report
#              success; with LAKE_EXIT=0 lake has asserted every target is up to
#              date, and the mtime is the weaker evidence. Reported, not fatal.
if [ "$_whole" = "1" ]; then
  if [ "$_absent" -gt 0 ]; then
    echo "WHOLE_CORPUS_INCOMPLETE=1"
    echo "!!! A whole-corpus build left $_absent module(s) with NO OLEAN AT ALL."
    echo "!!! Those were never built, so any error count above is a FLOOR."
    _coverage=1
  elif [ "$_stale" -gt 0 ] && [ "${_lake_exit:-1}" != "0" ]; then
    echo "WHOLE_CORPUS_INCOMPLETE=1"
    echo "!!! lake FAILED and left $_stale STALE module(s): they were not reached."
    echo "!!! Their silence is absence of evidence. Check MODULE_STATUS per file."
    _coverage=1
  else
    echo "WHOLE_CORPUS_INCOMPLETE=0"
    if [ "$_stale" -gt 0 ]; then
      echo "STALE_MTIME_ONLY=$_stale  (LAKE_EXIT=0: lake reports these up to date;"
      echo "                          a merge or checkout touched the sources.)"
    fi
  fi
fi

# Make the guard bite: a coverage failure is a script failure, so a caller that
# only checks the exit code still learns about it.
if [ "$_coverage" = "1" ]; then exit 3; fi
