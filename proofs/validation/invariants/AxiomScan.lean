/-
Copyright (c) 2026 Sauers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sauers
-/
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

Exit is nonzero when a declaration depends on a custom axiom or on a compiler
axiom, so this can be wired into the same job as the build.  It is NOT nonzero
for `sorryAx`, which is reported as an admission and counted; see `admissible`
below for why closing that exit too would select for laundering rather than for
proof.  The source-level counterpart is the admissions list in
`scripts/check-identifications.py`, which likewise reports `sorry` and fails on
`admit`.  The two are not redundant: the text scan names the line a person
typed, and this scan names every declaration the KERNEL knows to be incomplete,
including the error-recovery cases whose source contains no such word.
-/
import Calibrator
import Lean.Util.CollectAxioms

open Lean Elab Command

namespace AxiomScan

/-- The axioms a Mathlib development is entitled to.  `propext`, `Classical.choice`
and `Quot.sound` are Lean's foundations, not assumptions this corpus is making.

Deliberately absent, and each one a different failure: `Lean.ofReduceBool` and
`Lean.trustCompiler` (`native_decide`, which moves the compiler into the trusted
base), and every axiom declared in this repository. -/
def allowed : List Name :=
  [``propext, ``Classical.choice, ``Quot.sound]

/-- `sorryAx` is an ADMISSION, not an offence, and this scan reports it without
failing.  That is a deliberate asymmetry, and it is the whole point of the split.

A guard that fails the build on `sorryAx` while also failing it on custom axioms,
`native_decide` and rebound notation has closed every exit at once.  What it has
actually done is make the honest admission the MOST expensive option available:
writing `sorry` breaks CI, whereas weakening the statement until it is provable,
moving the hard half into a hypothesis nobody discharges, or proving the theorem
about a degenerate surrogate all leave a green build.  The guard then selects for
exactly the four laundering families the rest of this directory exists to detect.

So the order of preference this file encodes, worst to best:

  * a custom axiom, a compiler-backed proof, a rebound `+` -- REJECTED, always;
  * a theorem whose statement was quietly weakened to fit the proof available --
    not visible here at all, which is why `Inflation.lean` and the vacuity and
    range detectors exist;
  * an admitted proof obligation, named and counted -- REPORTED, and allowed to
    stay in the corpus for as long as it takes to discharge;
  * a proof.

An admission is a debt with the debtor's name on it.  The closure is transitive,
so every downstream consumer reports it too and the printed list is the blast
radius, not a single line.  That is the property that makes it safe to permit:
nothing that rests on an admission can look finished.

`ADMISSION_SCAN_COUNT` is printed unconditionally, including when it is zero, so
that "no admissions" is a measurement rather than the absence of a line. -/
def admissible : List Name :=
  [``sorryAx]

/-- Lean's own generated equation and match lemmas: `f.eq_def`, `f.eq_1`,
`f.match_1`, `f.proof_2`.  The suffix is `eq_` or `match_` or `proof_` followed
by *digits*, or the literal `eq_def`.

The test is by SHAPE and not by prefix.  `startsWith "eq_"` would exclude every
hand-written theorem in the ordinary Mathlib naming style
`eq_<conclusion>_of_<hypothesis>`, of which this corpus has four:
`Calibrator.eq_of_ae_eq_of_continuous` and, in `BundleRigidity`,
`eq_zero_of_tauOdd_of_tauEven`, `eq_empty_of_core_empty` and
`eq_zero_of_bounded_by_linear`.  A guard that silently drops theorems from the
scan is worse than no guard, because its clean report is read as coverage. -/
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

/-- Classify one declaration's axiom closure.

`none` means clean.  `some (false, bad)` is an ADMISSION: everything outside the
foundations is admissible, i.e. the closure's only extra entry is `sorryAx`.
`some (true, bad)` is an OFFENCE and fails the run.

A declaration that depends on BOTH `sorryAx` and a custom axiom is an offence,
not an admission -- otherwise adding one `sorry` anywhere in a proof would buy
silence for every axiom it also happens to rest on. -/
def classify (allowed admissible : List Name) (ax : Array Name) :
    Option (Bool × Array Name) :=
  let bad := ax.filter fun a ↦ !(allowed.contains a)
  if bad.isEmpty then none
  else some (bad.any fun a ↦ !(admissible.contains a), bad)

/-- The names this scan is responsible for. -/
def roots (env : Environment) : Array Name := Id.run do
  let mut out := #[]
  for (name, ci) in env.constants.toList do
    unless (`Calibrator).isPrefixOf name do continue
    -- Scan every axiom, including unused custom axioms.  For value-bearing
    -- declarations scan user-authored roots: generated declarations cannot
    -- introduce an axiom absent from those roots, and explicit source guards
    -- independently reject custom elaborators and compiler-backed proofs.
    match ci with
    | .axiomInfo _ => out := out.push name
    | .thmInfo _ | .defnInfo _ | .opaqueInfo _ =>
      if userWritten env name then out := out.push name
    | _ => pure ()
  return out

/-- The union of the axiom closures of `names`, in ONE traversal.

ONE traversal is not an optimisation, it is what makes the scan terminate.
`Lean.collectAxioms` starts from an empty `visited` set on every call, so
calling it per declaration re-walks the shared Mathlib closure from scratch each
time: at Lean 4.24.0 that is 88 seconds for 400 theorems, and the full
8111-constant run dies with SIGBUS having produced no output.  A scan that
crashes reports nothing, and nothing is indistinguishable from clean unless the
exit status is read.

Threading one `CollectAxioms.State` through every root makes the walk linear in
the union of the closures.  The `visited` set is what does it, and it is also
why this cannot attribute an axiom to a declaration: once a constant is visited
for one root, later roots reaching it add nothing.  Attribution is `witnessesOf`
below, and it runs only when there is something to attribute. -/
def unionOfClosures (env : Environment) (names : Array Name) : Array Name :=
  let st := names.foldl
    (fun st n => (((CollectAxioms.collect n).run env).run st).2)
    ({} : CollectAxioms.State)
  st.axioms

/-- Which roots actually depend on `target`, up to `limit` of them.

Runs only when `unionOfClosures` has already found `target`, so the expensive
per-declaration walk is paid on the interesting path and never on the clean
one.  Capped because the point is to name the debtor, not to enumerate every
consumer -- and the cap is reported, so a truncated list cannot be misread as a
complete one. -/
def witnessesOf (env : Environment) (names : Array Name) (target : Name)
    (limit : Nat) : Array Name := Id.run do
  let mut out := #[]
  for n in names do
    if out.size ≥ limit then break
    let ax := (((CollectAxioms.collect n).run env).run {}).2.axioms
    if ax.contains target then out := out.push n
  return out

end AxiomScan

run_cmd do
  let env ← getEnv
  let allowed := AxiomScan.allowed
  let admissible := AxiomScan.admissible
  let names := AxiomScan.roots env
  let scanned := names.size
  let union := AxiomScan.unionOfClosures env names
  let extra := union.filter fun a => !(allowed.contains a)
  let offending := extra.filter fun a => !(admissible.contains a)
  let admitted := extra.filter fun a => admissible.contains a
  let mut offenders : Array (Name × Name × Array Name) := #[]
  let mut admissions : Array (Name × Name × Array Name) := #[]
  for a in offending do
    for n in AxiomScan.witnessesOf env names a 20 do
      offenders := offenders.push ((env.getModuleFor? n).getD `«unknown», n, #[a])
  for a in admitted do
    for n in AxiomScan.witnessesOf env names a 40 do
      admissions := admissions.push ((env.getModuleFor? n).getD `«unknown», n, #[a])
  -- `logError` is what makes the run exit nonzero, so it marks offences only.
  for (m, name, bad) in offenders do
    logError m!"AXIOM\t{m}\t{name}\t{bad.toList}"
  -- Admissions are printed one per declaration, at the same volume and in the
  -- same format.  The transitive closure means this list names every consumer
  -- as well as the admitted declaration itself, which is the intended reading:
  -- it is the blast radius of the debt, not a single site.
  for (m, name, bad) in admissions do
    logInfo m!"ADMISSION\t{m}\t{name}\t{bad.toList}"
  logInfo m!"AXIOM_SCAN_SCANNED\t{scanned}"
  logInfo m!"AXIOM_SCAN_OFFENDERS\t{offenders.size}"
  -- Printed even at zero: a missing line reads as "not measured", and the whole
  -- reason admissions are permitted is that they are counted in the open.
  logInfo m!"ADMISSION_SCAN_COUNT\t{admissions.size}"
  logInfo m!"AXIOM_SCAN_ALLOWED\t{allowed}"
  logInfo m!"AXIOM_SCAN_ADMISSIBLE\t{admissible}"
