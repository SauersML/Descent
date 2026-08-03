/-
Enumerate the theorems whose PROOF TERM is `Eq.refl`, from the elaborated
environment rather than from source text.

Three text scans of the same nine modules returned 2, 16 and 3, with zero
overlap in names between the last two: a non-greedy regex spans declarations,
an anchored one misses `rfl` on its own line, and a block splitter trips on a
`:=` inside the statement. Lean is whitespace-insensitive and its proofs are
not a regular language; the environment is the only authority.
-/
import Calibrator
import Lean

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

/-- Modules in the population-genetics slice.  Names are prefixed
`rflScan` because `slice` and `isReflProof` both collide with
declarations already in scope once `Calibrator` (and Mathlib
beneath it) is imported -- the first attempt bound `slice` to
`Lean.ParserDescr.slice`. -/
private def rflScanModules : List Name :=
  [`Calibrator.LDDecayTheory, `Calibrator.Conventions,
   `Calibrator.PopulationGeneticsFoundations, `Calibrator.DemographicHistory,
   `Calibrator.DriftRegime, `Calibrator.LongitudinalPortability,
   `Calibrator.HumanDemography, `Calibrator.AncestrySpecificArchitecture,
   `Calibrator.AncestrySpecificPower, `Calibrator.GeneticArchitectureDiscovery]

/-- Compiler-generated theorems: equation lemmas (`f.eq_1`), `sizeOf_spec`,
`injEq`, and friends. They are `rfl` by construction and are not written by
anyone, so counting them answers a different question than "which HAND-WRITTEN
theorems close by rfl". The unfiltered scan returned 19; eleven were these. -/
private def rflScanIsGenerated (n : Name) : Bool :=
  n.isInternalDetail ||
  (match n with
   | .str _ s =>
       s.startsWith "eq_" || s == "sizeOf_spec" || s == "injEq" ||
       s == "noConfusionType" || s == "below" || s == "brecOn" ||
       s.startsWith "proof_" || s.startsWith "match_"
   | _ => false)

run_cmd do
  let env ← getEnv
  let mut n := 0
  for (name, ci) in env.constants.toList do
    match ci with
    | .thmInfo ti =>
      if (`Calibrator).isPrefixOf name then
        match env.getModuleFor? name with
        | some m =>
          if rflScanModules.contains m && rflScanIsReflProof ti.value
              && !rflScanIsGenerated name then
            logInfo m!"RFL\t{m}\t{name}"
            n := n + 1
        | none => pure ()
    | _ => pure ()
  logInfo m!"TOTAL_RFL_THEOREMS\t{n}"
