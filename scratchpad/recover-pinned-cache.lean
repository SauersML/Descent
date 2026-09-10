/-
Offline, git-free cache recovery for mathlib4 commit
f897ebcf72cd16f89ab4577d0c826cd14afaafc7 and Lean 4.24.0.

Bootstrap ONLY these unmodified pinned utility sources, in this order:
  Cache/Lean.lean -> Cache/Lean.olean
  Cache/IO.lean -> Cache/IO.olean
  Cache/Hashing.lean -> Cache/Hashing.olean
They import only each other and the installed Lean/Std library.

Run this file with that toolchain's `lean --run` from the private project root.
LEAN_PATH points to the private bootstrap directory containing `Cache/` oleans.
LEAN_SRC_PATH lists the pinned mathlib source root and all pinned dependency
source roots. MATHLIB_CACHE_DIR points to the existing shared .ltar directory.
The pinned mathlib lakefile.lean, lean-toolchain, and lake-manifest.json must be
unchanged: the official hash computation below reads those exact files.

Arguments are exact module names or source file paths accepted by the pinned
Cache.IO parser. Unlike the full cache CLI, only these roots and their import
closure are hashed. No Lake invocation, git command, HTTP request, ProofWidgets
release fetch, cache archive modification, or theorem-library compilation occurs.

Output files are written only in the current private working directory:
  recover-pinned-cache.json: present archives, with official Mathlib base remapping.
  recover-pinned-cache-missing.tsv: missing modules and their exact archive names.

Exit 0 means all requested root closures have existing archives; exit 2 means
some matching archives are absent; exit 3 means some source roots could not hash.
Existence is not an archive integrity check. Unpack separately with existing
leantar 0.1.15, from this same working directory:
  leantar-0.1.15 -x -j - < recover-pinned-cache.json
Do NOT add --delete-corrupted: the shared input archive directory stays read-only.
-/
import Cache.Hashing

open Cache.IO Cache.Hashing

def main (args : List String) : IO UInt32 := CacheM.run do
  if args.isEmpty then
    IO.eprintln "Usage: lean --run recover-pinned-cache.lean Mathlib.Module ..."
    return 3
  let roots ← parseArgs ("offline-recover" :: args)
  let (_, memo) ← StateT.run
    (roots.toArray.mapM fun (mod, source) ↦ getHash mod source)
    { rootHash := ← getRootHash }
  let mut invalid := false
  for (mod, _) in roots.toArray do
    if !memo.hashMap.contains mod then
      IO.eprintln s!"Requested root has no valid source hash: {mod}"
      invalid := true
  if invalid then return 3
  let present ← memo.hashMap.filterExists true
  let missing ← memo.hashMap.filterExists false
  IO.println s!"Required modules: {memo.hashMap.size}; existing archives: {present.size}; missing: {missing.size}"
  let isMathlibRoot ← Cache.IO.isMathlibRoot
  let mathlibBase := (← read).mathlibDepPath.toString
  let config : Array Lean.Json := present.fold (init := #[]) fun config mod hash ↦
    let file := (CACHEDIR / hash.asLTar).toString
    if isMathlibRoot || !isFromMathlib mod then
      config.push (.str file)
    else
      config.push (.mkObj [("file", .str file), ("base", .str mathlibBase)])
  IO.FS.writeFile "recover-pinned-cache.json" (Lean.Json.compress (.arr config))
  let missingLines := missing.toArray.toList.map fun (mod, hash) ↦
    s!"{mod}\t{hash.asLTar}"
  IO.FS.writeFile "recover-pinned-cache-missing.tsv"
    (String.intercalate "\n" missingLines ++ if missingLines.isEmpty then "" else "\n")
  IO.println "Wrote recover-pinned-cache.json and recover-pinned-cache-missing.tsv"
  return if missing.isEmpty then 0 else 2
