#!/usr/bin/env bash
# Run the symbolic checks on the cluster.  Nothing here executes locally.
#
#   bash proofs/validation/symbolic/cluster_run.sh            # full pipeline
#   bash proofs/validation/symbolic/cluster_run.sh smoke      # regressions only, ~2 min
#
# The smoke target exists because the pipeline is a ~15 minute job and the
# regression suite decides in two minutes whether the interpreter and sympy
# version behave as the checks expect.  Run smoke first; if it fails, the full
# run's output would not be trustworthy anyway.

set -u  # not -e: a failing step should still let later steps report

module load python3/3.10.9_anaconda2023.03_libmamba

HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
cd "$HERE" || exit 1

echo "=== interpreter and library versions (please return this block) ==="
python3 -c 'import sys, sympy, numpy; print("python", sys.version.split()[0]); print("sympy", sympy.__version__); print("numpy", numpy.__version__)'
echo

# The definition table comes from the shared extract API; the local parse is
# needed only for theorem statements and is regenerated here because decls.json
# is deliberately untracked (it is large and derived).
echo "=== regenerating the local theorem parse ==="
python3 leanparse.py
echo

if [ "${1:-full}" = "smoke" ]; then
  echo "=== regression suite (21 assertions) ==="
  python3 test_regressions.py
  exit $?
fi

echo "=== full pipeline ==="
python3 run_all.py
echo

# Regressions run AFTER the pipeline in the full path, because several of them
# assert over the freshly written results (e.g. that no FIXED_POINT_FAILS
# survives).  Running them first would test the committed results instead, which
# is what `smoke` deliberately does as a fast interpreter check.
echo "=== regression suite (against the results just produced) ==="
python3 test_regressions.py
echo

echo "=== slice ledger (consumes check7) ==="
python3 slice_ledger.py
echo

echo "=== cross-tier reconciliation ==="
python3 reconcile_coverage.py
