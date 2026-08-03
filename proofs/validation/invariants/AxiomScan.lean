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

end AxiomScan

run_cmd do
  let env ← getEnv
  let allowed := AxiomScan.allowed
  let mut offenders : Array (Name × Name × Array Name) := #[]
  let mut scanned := 0
  for (name, ci) in env.constants.toList do
    unless (`Calibrator).isPrefixOf name do continue
    -- Scan axioms themselves as well as every value-bearing declaration.  An
    -- unused custom axiom is still forbidden production state, and generated
    -- declarations need no special case: a clean generated declaration has a
    -- clean closure, while filtering it would create a trust blind spot.
    match ci with
    | .axiomInfo _ | .thmInfo _ | .defnInfo _ | .opaqueInfo _ =>
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
