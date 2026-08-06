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
# COPYFILE_DISABLE, or macOS `tar` writes an AppleDouble `._X` beside every file
# it archives -- the extended attributes, including the `com.apple.provenance`
# whose "unknown extended header keyword" warning this used to print on every
# run. Extracted on the node they become 289 files named `._Something.lean`,
# which are not UTF-8 and are not Lean. Guards that route through
# `lean_sources` drop them; `run_heads` hand-rolled its walk and reported 271
# findings asking the heads to import `Descent.Spectral.._CirculationDefect`.
# Both ends are fixed: the guard no longer sees them and the tar no longer
# makes them.
export COPYFILE_DISABLE=1
tar czf "$TAR" Descent Descent.lean lakefile.lean lean-toolchain lake-manifest.json validation
"$MSI" put "$TAR" "$REMOTE/.src-sync.tar.gz" >/dev/null
rm -f "$TAR"
# Overlay, never delete: the remote checkout is shared with other sessions, and a
# wholesale replacement of Descent/ would destroy work this tarball does not carry.
"$MSI" "cd $REMOTE && tar xzf .src-sync.tar.gz && rm -f .src-sync.tar.gz && echo synced"
if [ "${1:-}" = build ]; then
  shift
  "$MSI" "cd $REMOTE && nice -n 5 lake build ${*:-Descent} 2>&1 | tail -60"
fi
