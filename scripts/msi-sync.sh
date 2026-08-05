#!/usr/bin/env bash
# Push the Lean sources to the warm MSI checkout and (optionally) build there.
#   scripts/msi-sync.sh            just sync
#   scripts/msi-sync.sh build      sync, then `lake build Descent` on the node
# Only source is shipped; .lake/ on the node is the warm cache and is preserved.
set -euo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
REMOTE="/projects/standard/hsiehph/sauer354/descent"
MSI="${MSI:-$HOME/msi-node/msi}"
TAR="$(mktemp -t descent-src).tar.gz"
cd "$ROOT"
tar czf "$TAR" Descent Descent.lean lakefile.lean lean-toolchain lake-manifest.json
"$MSI" put "$TAR" "$REMOTE/.src-sync.tar.gz" >/dev/null
rm -f "$TAR"
# Replace Descent/ wholesale so deletions and renames propagate.
"$MSI" "cd $REMOTE && rm -rf Descent && tar xzf .src-sync.tar.gz && rm -f .src-sync.tar.gz && echo synced"
if [ "${1:-}" = build ]; then
  shift
  "$MSI" "cd $REMOTE && nice -n 5 lake build ${*:-Descent} 2>&1 | tail -60"
fi
