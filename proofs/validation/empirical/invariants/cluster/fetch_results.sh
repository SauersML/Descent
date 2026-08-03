#!/usr/bin/env bash
# Bring cluster results back into the repo.  THE CLUSTER IS WRITE-ONLY COMPUTE.
#
# The cluster checkout has no push credentials, so anything produced there
# exists in exactly one place until it is pulled back deliberately. Another
# agent had all seven of its result files living only on MSI for a whole
# session, surviving repeated `git reset --hard` purely because untracked
# files are spared -- one `git clean` and the day was gone.
#
# "It is on the cluster" is one copy, not a backup.
#
# Usage:  bash cluster/fetch_results.sh
# Idempotent. Fetches whatever exists, reports what does not, exits non-zero
# only if NOTHING came back (which almost always means the run never wrote).
set -uo pipefail

MSI=/Users/user/msi-node/msi
REMOTE_WT=/projects/standard/hsiehph/sauer354/ranges_wt/proofs/validation/invariants
REMOTE_HOME=/projects/standard/hsiehph/sauer354
HERE="$(cd "$(dirname "$0")" && pwd)"
DEST="$HERE/runs"
mkdir -p "$DEST"

got=0

fetch() {   # fetch <remote-abs-path> <local-name>
  local src="$1" name="$2" tmp
  tmp="$(mktemp)"
  if "$MSI" "cat '$src' 2>/dev/null" > "$tmp" 2>/dev/null && [ -s "$tmp" ]; then
    mv "$tmp" "$DEST/$name"
    printf '  fetched  %-44s %s bytes\n' "$name" "$(wc -c < "$DEST/$name" | tr -d ' ')"
    got=$((got+1))
  else
    rm -f "$tmp"
    printf '  ABSENT   %-44s (run has not written it)\n' "$name"
  fi
}

echo "pulling cluster results into $DEST"

# stdout logs, written to the home dir by the detached launches
fetch "$REMOTE_HOME/out_stability.txt"  out_stability.txt
fetch "$REMOTE_HOME/out_theorems.txt"   out_theorems_equalsfix.txt
fetch "$REMOTE_HOME/out_theorems2.txt"  out_theorems_nonfinite.txt
fetch "$REMOTE_HOME/out_seeds.txt"      out_seed_variation.txt
fetch "$REMOTE_HOME/out_all.txt"        out_all.txt

# result JSON, written next to the scripts in the private clone
for f in results_simulation_stability.json results_theorems.json \
         results_ranges.json results_invariants.json results_simulation.json \
         results_falsifiability.json results_seed_variation.json \
         coverage.json unreachable.json; do
  fetch "$REMOTE_WT/$f" "$f"
done

# the revision those numbers belong to, so they are never orphaned from it
"$MSI" "cd $REMOTE_WT && git rev-parse --short HEAD 2>/dev/null" \
  > "$DEST/REVISION.txt" 2>/dev/null || true
echo "  cluster revision: $(cat "$DEST/REVISION.txt" 2>/dev/null || echo unknown)"

echo "$got file(s) retrieved"
[ "$got" -gt 0 ]
