/-
Report the transitive axiom closure of every `Calibrator` declaration, and fail
on anything outside the three foundations Lean's own standard library rests on.

WHY THIS EXISTS.  `scripts/check-identifications.py` guards `sorry` with

    re.finditer(r'\bsorry\b', src)

over the source text.  That is a scan of what a person typed, and the question
is what the KERNEL accepted.  The two come apart in the direction that matters:

  * A declaration can depend on `sorryAx` with no `sorry` in its source.  On
    2026-08-03 `proofs/Calibrator/ConditionalGain.lean` reopened the namespace
    `FiniteCoupledPhaseLaw` without re-declaring its `variable {n d : ℕ}`, so
    `toFiberCoupling` mentioned two unbound identifiers.  Lean recovered from
    the elaboration error by inserting synthetic sorries, and reported
    `declaration uses 'sorry'` for two theorems whose source text contains no
    such word.  A text scan cannot see those, and the ledger it checks them
    against would not have been consulted.
  * Conversely the word appears in three docstrings in this corpus that discuss
    the ledger, so the text scan has to special-case its own false positives.

Nothing else in the repository looks at axioms at all: there is no
`#print axioms`, no `collectAxioms`, and no `lean4checker` invocation anywhere
in `proofs/`, `scripts/`, or `.github/workflows/`.  A custom `axiom` declared in
any module, or a `native_decide` anywhere, would be reported by no guard.

Run:
  lake env lean proofs/validation/invariants/AxiomScan.lean

Exit is nonzero when a declaration depends on anything outside ALLOWED, so this
can be wired into the same job as the build.
-/
import Calibrator
import Lean.Util.CollectAxioms

open Lean Elab Command

namespace AxiomScan

/-- The axioms a Mathlib development is entitled to.  `propext`, `Classical.choice`
and `Quot.sound` are Lean's foundations, not assumptions this corpus is making.

Deliberately absent, and each one a different failure:
`sorryAx` (an unfinished or error-recovered proof), `Lean.ofReduceBool` and
`Lean.trustCompiler` (`native_decide`, which moves the compiler into the trusted
base), and every axiom declared in this repository. -/
def allowed : List Name :=
  [``propext, ``Classical.choice, ``Quot.sound]

/-- Lean's own generated equation and match lemmas: `f.eq_def`, `f.eq_1`,
`f.match_1`, `f.proof_2`.  The suffix is `eq_` or `match_` or `proof_` followed
by *digits*, or the literal `eq_def`.

MATCHING ON THE BARE PREFIX IS WRONG AND WAS WRONG HERE.  `startsWith "eq_"`
excludes every hand-written theorem in the ordinary Mathlib naming style
`eq_<conclusion>_of_<hypothesis>`, and this corpus has four:
`Calibrator.eq_of_ae_eq_of_continuous` and, in `BundleRigidity`,
`eq_zero_of_tauOdd_of_tauEven`, `eq_empty_of_core_empty` and
`eq_zero_of_bounded_by_linear`.  A guard that silently drops four theorems from
the scan is worse than no guard, because its clean report is read as coverage. -/
def isGeneratedEquation (f : String) : Bool :=
  f == "eq_def" ||
  (["eq_", "match_", "proof_"].any f.startsWith &&
    (f.dropWhile (· != '_') |>.drop 1 |>.all Char.isDigit) &&
    f.any Char.isDigit)

/-- Whether a value-bearing declaration was authored in the corpus rather
than generated automatically for an inductive type or structure.  Generated
recursors, projections, `injEq` declarations, and extensionality lemmas are
already in the dependency closure of their user-authored roots; asking
`collectAxioms` to recompute their closures individually is redundant and was
large enough to exhaust the CI job after a successful full build.

The redundancy argument is what makes the filter safe, and it is worth stating
precisely: a generated declaration is elaborated from a user-authored root, so
its axiom closure is contained in that root's.  Skipping it therefore cannot
hide an axiom the scan would otherwise report.  That argument covers exactly
the names below and nothing else, which is why the equation-lemma test above is
by shape rather than by prefix. -/
def userWritten (env : Environment) (n : Name) : Bool :=
  !n.isInternalDetail
  && !(env.isProjectionFn n)
  && (match n with
      | .str _ f => !(isGeneratedEquation f ||
                       ["mk", "injEq", "eta", "sizeOf", "noConfusion",
                        "noConfusionType", "rec", "recOn", "casesOn", "brecOn",
                        "below", "ndrec", "toCtorIdx", "ofNat", "sizeOf_spec",
                        "mk.sizeOf_spec", "ext", "ext_iff"].contains f)
      | _ => false)

end AxiomScan

run_cmd do
  let env ← getEnv
  let allowed := AxiomScan.allowed
  let mut offenders : Array (Name × Name × Array Name) := #[]
  let mut scanned := 0
  for (name, ci) in env.constants.toList do
    unless (`Calibrator).isPrefixOf name do continue
    -- Scan every axiom, including unused custom axioms.  For value-bearing
    -- declarations scan user-authored roots: generated declarations cannot
    -- introduce an axiom absent from those roots, and explicit source guards
    -- independently reject custom elaborators and compiler-backed proofs.
    match ci with
    | .axiomInfo _ =>
      scanned := scanned + 1
      let ax ← Lean.collectAxioms name
      let bad := ax.filter fun a => !(allowed.contains a)
      if !bad.isEmpty then
        let m := (env.getModuleFor? name).getD `«unknown»
        offenders := offenders.push (m, name, bad)
    | .thmInfo _ | .defnInfo _ | .opaqueInfo _ =>
      unless AxiomScan.userWritten env name do continue
      scanned := scanned + 1
      let ax ← Lean.collectAxioms name
      let bad := ax.filter fun a => !(allowed.contains a)
      if !bad.isEmpty then
        let m := (env.getModuleFor? name).getD `«unknown»
        offenders := offenders.push (m, name, bad)
    | _ => pure ()
  for (m, name, bad) in offenders do
    logError m!"AXIOM\t{m}\t{name}\t{bad.toList}"
  logInfo m!"AXIOM_SCAN_SCANNED\t{scanned}"
  logInfo m!"AXIOM_SCAN_OFFENDERS\t{offenders.size}"
  logInfo m!"AXIOM_SCAN_ALLOWED\t{allowed}"
