#!/bin/bash
#SBATCH --job-name=pc-proof-fast
#SBATCH --partition=msismall
#SBATCH --cpus-per-task=4
#SBATCH --mem=4G
#SBATCH --time=00:05:00
#SBATCH --output=pc-proof-fast-%j.out

set -euo pipefail

cd "$SLURM_SUBMIT_DIR"
export PATH="$HOME/.elan/bin:$PATH"

# Build only the ancestry-correctability proof graph.  In particular, do not
# pass Lake's `-R`/`--reconfigure` flag: that invalidates the warm incremental
# state and turns a leaf check into a project-wide replay.
# Use every allocated core; Lake defaults to a conservative job count.
lake build "${1:-Calibrator.PCCorrectability}" --jobs "${SLURM_CPUS_PER_TASK:-4}"
