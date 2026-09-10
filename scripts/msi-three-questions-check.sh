#!/usr/bin/env bash
# Run on MSI. Reuse the pinned warm cache read-only; write only to shared storage.
set -euo pipefail
proof_root=/projects/standard/hsiehph/sauer354/descent-three-questions
proof_cache=/tmp/descent-proof-20260910
proof_mathlib="$proof_cache/mathlib4-f897ebcf72cd16f89ab4577d0c826cd14afaafc7"
proof_paths="$proof_root:$proof_cache/project:$proof_mathlib/.lake/build/lib/lean"
for proof_dep in "$proof_mathlib"/.lake/packages/*; do
  proof_paths="$proof_paths:$proof_dep/.lake/build/lib/lean"
done
cd "$proof_root"
for proof_module in "$@"; do
  proof_file="${proof_module//.//}"
  # A validation build must never overwrite an entry in the shared warm cache.
  test ! -L "$proof_file.olean"
  env LEAN_PATH="$proof_paths" timeout 55s "$proof_cache/lean424/bin/lean" \
    -j 1 -M 2048 -DautoImplicit=false -DrelaxedAutoImplicit=false \
    -o "$proof_file.olean" "$proof_file.lean"
  printf 'COMPILED %s\n' "$proof_module"
done
