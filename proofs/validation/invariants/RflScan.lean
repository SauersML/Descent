/-
Copyright (c) 2026 Sauers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sauers
-/
/-
Enumerate the theorems whose PROOF TERM is `Eq.refl`, from the elaborated
environment rather than from source text.

Three text scans of the same nine modules returned 2, 16 and 3, with zero
overlap in names between the last two: a non-greedy regex spans declarations,
an anchored one misses `rfl` on its own line, and a block splitter trips on a
`:=` inside the statement. Lean is whitespace-insensitive and its proofs are
not a regular language; the environment is the only authority.

Writes `proofs/validation/invariants/rfl_scan_results.json`: every hit by name
and module, stamped with the revision it was measured at. Read that file, not a
commit message. The "8 of 8 classified" quoted for this scan was measured with a
module allow-list of ten popgen modules that this file no longer contains, so it
does not describe what this file now does.
-/
import Calibrator
import Lean
import Shared.DeclFilter
import Shared.Results

open Lean Elab Command

/-- Strip leading lambda binders. A theorem with binders stores its proof as
`fun a b c => Eq.refl _`, so testing the head of the whole value asks whether a
LAMBDA is `Eq.refl` -- which is never true. The first version of this scan did
exactly that and reported 0 of 0, a clean-looking null that a positive control
on two known `:= rfl` theorems refuted immediately. -/
private partial def rflScanUnderBinders : Expr → Expr
  | .lam _ _ b _ => rflScanUnderBinders b
  | e            => e

/-- Is this proof term literally a reflexivity proof? -/
private def rflScanIsReflProof (e : Expr) : Bool :=
  (rflScanUnderBinders e).getAppFn.isConstOf ``Eq.refl

/-- Compiler-generated theorems: equation lemmas (`f.eq_1`), `sizeOf_spec`,
`injEq`, and friends. They are `rfl` by construction and are not written by
anyone, so counting them answers a different question than "which HAND-WRITTEN
theorems close by rfl". The unfiltered scan returned 19; eleven were these.

The test is now `Shared.isGenerated`, shared with the other detectors. The
private copy this replaces was one of three that disagreed, and it was the
narrowest: it excluded neither projection functions nor the constructor family,
so it reported `Foo.rec`, `Foo.casesOn` and `Foo.ext_iff` as hand-written, and
it missed `ndrec` and `noConfusion` that the axiom scan caught. See
`proofs/validation/inflation/CROSSCHECK.md` §4. -/
private def rflScanIsGenerated (env : Environment) (n : Name) : Bool :=
  Shared.isGenerated env n

run_cmd do
  let env ← getEnv
  let mut n := 0
  let mut scanned := 0
  let mut hits : Array Json := #[]
  for (name, ci) in env.constants.toList do
    match ci with
    | .thmInfo ti =>
      if (`Calibrator).isPrefixOf name then
        match env.getModuleFor? name with
        | some m =>
          unless rflScanIsGenerated env name do
            scanned := scanned + 1
            if rflScanIsReflProof ti.value then
              logInfo m!"RFL\t{m}\t{name}"
              n := n + 1
              hits := hits.push <| Json.mkObj
                [ ("theorem", toJson name.toString), ("module", toJson m.toString) ]
        | none => pure ()
    | _ => pure ()
  logInfo m!"TOTAL_RFL_THEOREMS\t{n}"
  Shared.Results.write "proofs/validation/invariants/rfl_scan_results.json" "RflScan"
    [ -- The denominator this scan never used to report. Without it a hit count
      -- cannot be read as a rate, and "8 of 8" was quoted as though it could.
      ("handWrittenTheoremsScanned", toJson scanned),
      ("rflTheoremCount", toJson n),
      -- No module allow-list: this scans every `Calibrator` module. The commit
      -- that reported 8 restricted to ten popgen modules; that list is gone.
      ("moduleFilter", Json.null),
      ("rflTheorems", Json.arr hits) ]
