#!/bin/bash
#SBATCH --job-name=inv-stability
#SBATCH --array=0-38
#SBATCH --time=00:40:00
#SBATCH --mem=4G
#SBATCH --cpus-per-task=1
#SBATCH --output=/projects/standard/hsiehph/sauer354/inv_stability/spec_%a.out
#SBATCH --open-mode=truncate
#
# Seed-stability sweep as a JOB ARRAY: one task per simulation spec.
#
# The serial version takes about eight minutes for each Wright-Fisher spec and
# runs 39 of them end to end. As an array it costs the SLOWEST spec, not the
# sum, and it fixes the exposure the serial version has: that one writes its
# JSON only at the end, so a node failure at spec 30 loses everything. Here a
# dead node loses ONE spec, and the other 38 results are already on disk.
#
# --output is on /projects/standard shared storage on purpose. Node-local /tmp
# is invisible to the next relay call, which is a third way to get an empty log
# that looks like a clean run -- alongside a job killed before it writes, and a
# stale log left by a previous run.
#
# --open-mode=truncate so a re-run of one array index cannot leave the previous
# answer in place for a task that failed early. Same rule as `rm -f` first.
#
# REGENERATE defs.json BEFORE SUBMITTING. The staleness guard refuses a table
# older than the corpus, and 39 tasks cannot each regenerate it -- they would
# race on the same file. One serial extract, then submit:
#
#   cd <clone>/proofs/validation/invariants
#   python3 extract_defs.py                       # <-- required
#   mkdir -p /projects/standard/hsiehph/sauer354/inv_stability
#   sbatch --partition=agsmall cluster/stability_array.sbatch
#
# Do not merge origin/main into the clone while the array is in flight: that
# touches the .lean files, and every task starting afterwards will refuse on
# staleness. The guard is right to; a sweep spanning two revisions is two
# sweeps.
#     (or amdsmall / msismall / sioux -- whichever schedules first)
#
# Collect:
#   python3 cluster/collect_stability.py    # merges spec_*.json, names gaps

set -uo pipefail
module load python3/3.10.9_anaconda2023.03_libmamba

cd "$SLURM_SUBMIT_DIR" || exit 1

OUTDIR=/projects/standard/hsiehph/sauer354/inv_stability
mkdir -p "$OUTDIR"

echo "spec index      : ${SLURM_ARRAY_TASK_ID}"
echo "node            : $(hostname)"
echo "corpus revision : $(git rev-parse --short HEAD 2>/dev/null || echo unknown)"
echo "dirty           : $(test -n "$(git status --porcelain 2>/dev/null)" && echo yes || echo no)"
echo

python3 -u cluster/run_stability.py \
    --seeds 8 \
    --only-index "${SLURM_ARRAY_TASK_ID}" \
    --json-out "$OUTDIR/spec_${SLURM_ARRAY_TASK_ID}.json"
rc=$?

echo
echo "exit: $rc"
exit $rc
