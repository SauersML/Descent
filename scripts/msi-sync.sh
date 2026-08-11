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
# `Counterexamples` is a second lean_lib target and ships with the rest: a library that
# is not synced is not built, and a deliberately-wrong body that nothing type-checks is
# worse than one inside the corpus, because it rots silently.
#
# TRACKED FILES ONLY (2026-08-11). The tar used to archive whole directories, so one
# agent's sync shipped every other agent's uncommitted files — including untracked
# never-compiled WIP, which broke the node for whoever synced next and got them blamed
# for a red build they did not cause. Shipping `git ls-files` keeps the edit->sync->build
# loop (working-tree content of TRACKED files still ships, committed or not) while
# untracked files stay home. A NEW file must be `git add -N`ed (intent-to-add) before it
# syncs — that is the declaration that it belongs to the build.
UNTRACKED=$(git ls-files --others --exclude-standard Descent Counterexamples PartialSymmetry validation | grep '\.lean$' || true)
if [ -n "$UNTRACKED" ]; then
  echo "msi-sync: NOT shipping untracked files (git add -N to include):" >&2
  echo "$UNTRACKED" | sed 's/^/  /' >&2
fi
git ls-files -z Descent Descent.lean Counterexamples Counterexamples.lean \
  PartialSymmetry PartialSymmetry.lean \
  lakefile.lean lean-toolchain lake-manifest.json validation | tar czf "$TAR" --null -T -
"$MSI" put "$TAR" "$REMOTE/.src-sync.tar.gz" >/dev/null
rm -f "$TAR"
# Overlay, never delete: the remote checkout is shared with other sessions, and a
# wholesale replacement of Descent/ would destroy work this tarball does not carry.
"$MSI" "cd $REMOTE && tar xzf .src-sync.tar.gz && rm -f .src-sync.tar.gz && echo synced"
if [ "${1:-}" = build ]; then
  shift
  "$MSI" "cd $REMOTE && nice -n 5 lake build ${*:-Descent} 2>&1 | tail -60"
fi
