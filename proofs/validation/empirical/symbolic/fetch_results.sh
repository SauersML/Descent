#!/usr/bin/env bash
# Bring the symbolic tier's artifacts back from the cluster.
#
#   bash proofs/validation/empirical/symbolic/fetch_results.sh
#
# WHY THIS EXISTS. Generated artifacts are gitignored and live at a shared path
# OUTSIDE any working tree, so no git command can reach them -- which protects
# them from `git reset --hard` and `git clean` on the shared checkout, the
# mechanism that orphaned twelve of these files earlier today. But outside git
# also means no backup through git, and a gitignored file on a credential-less
# node exists in exactly one place on earth.
#
# So: two homes. Shared cluster storage is where the pipeline writes; this
# pulls a copy back to the local checkout, where it is still gitignored but at
# least no longer singular. Neither copy is authoritative on its own -- each
# artifact carries the revision it was generated from (see provenance.py), and
# that is what tells you whether a copy is current.
#
# Anything a run has not written is reported ABSENT rather than skipped
# silently, because a missing artifact read as an empty result is the failure
# this whole tier keeps finding in other people's code and its own.

set -u

REMOTE_ART="/projects/standard/hsiehph/sauer354/gnomon-artifacts/symbolic"
HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
LOCAL_ART="$HERE/fetched"
RELAY="/Users/user/msi-node/msi"

FILES="decls.json results_check1.json results_check1b.json results_check2.json \
results_check3.json results_check4.json results_check5.json results_check6.json \
results_check7.json results_check8.json results_homonyms.json coverage.json \
findings.json slice_ledger.json reconciled_coverage.json parser_audit.json \
c7.log c8.log ledger.log recon.log"

mkdir -p "$LOCAL_ART"

echo "=== cluster revision and artifact provenance ==="
$RELAY "cd /projects/standard/hsiehph/sauer354/gnomon && git rev-parse --short HEAD && cd proofs/validation/symbolic && module load python3/3.10.9_anaconda2023.03_libmamba >/dev/null 2>&1 && python3 provenance.py"

echo
echo "=== fetching into $LOCAL_ART ==="
for f in $FILES; do
  # Base64 so the relay's stdout cannot corrupt bytes; empty output means the
  # run never wrote the file, which is reported rather than passed over.
  b64=$($RELAY "test -f $REMOTE_ART/$f && base64 -w0 $REMOTE_ART/$f" 2>/dev/null)
  if [ -z "$b64" ]; then
    printf '  %-32s ABSENT (no run has written it)\n' "$f"
    continue
  fi
  printf '%s' "$b64" | base64 -d > "$LOCAL_ART/$f" 2>/dev/null
  if [ -s "$LOCAL_ART/$f" ]; then
    printf '  %-32s %s bytes\n' "$f" "$(wc -c < "$LOCAL_ART/$f" | tr -d ' ')"
  else
    printf '  %-32s FETCH FAILED (decoded empty)\n' "$f"
  fi
done

echo
echo "Fetched copies are gitignored. They are a second home, not a backup:"
echo "each artifact records the revision it was generated from, and THAT is"
echo "what says whether a copy is current. Regenerate rather than trust age."
