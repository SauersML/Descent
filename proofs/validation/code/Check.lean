/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Calibrator
import Lean
import Lean.Util.CollectAxioms
import Shared.DeclFilter
import Shared.Results

/-!
# Code validation, elaborated-environment half

Every check in this file reads the ELABORATED ENVIRONMENT: what the kernel
accepted, not what a person typed.  `proofs/validation/code/check.py` is the
source-text half.  The two are not redundant and neither subsumes the other:

  * the text scan names the line a person typed, and can see a comment, a
    docstring, a `variable` line, and a file that does not compile;
  * this scan sees the premises Lean actually inserted, a definition that
    unfolds to something other than its written form, a proof term's real head
    symbol, whether a type is inhabited, and the transitive axiom closure --
    none of which exists in the source text at all.

Run, after a successful build of `Calibrator` and `ValidationShared`:

    lake env lean proofs/validation/code/Check.lean

Exit is nonzero when any FATAL finding survives.  Admissions (`sorryAx`) are
reported and counted but do NOT fail the run; see `Axioms.admissible` for why
closing that exit would select for laundering rather than for proof.

## The four scans, and what each one is for

  AXIOMS      the transitive axiom closure of every declaration.  Fails on a
              custom axiom or a compiler axiom (`native_decide`).  Reports
              `sorryAx` as an admission.
  LAUNDERING  the premises the kernel sees.  Fails when a theorem's name is a
              claim its TYPE does not support.
  INFLATION   theorems whose proof is their own assumed hypothesis, and
              assumption-carrying structures the corpus never constructs.
  RFL         theorems whose proof term is literally `Eq.refl`.

## One shared declaration filter

All four scans ask "did a person write this declaration", and all four now ask
`Shared.userWritten`.  THIS FILE IS WHERE THAT WAS FIXED.  Before the merge the
axiom and laundering scans each carried a private copy of the filter and the
inflation and rfl scans used `Shared`; the copies disagreed, so tools reported
totals over different populations while looking equally authoritative.
`Shared.DeclFilter` carries the row-by-row table of how they differed.

The private copies differed from `Shared` in one respect: neither excluded
`eq_unfold`, Lean's generated unfolding lemma.  Unifying therefore drops a
handful of generated lemmas from the axiom and laundering populations.  That is
a correction in the safe direction -- a generated lemma's axiom closure is
contained in that of the user-authored root it was generated from, so nothing
the scan would otherwise report can be hidden by it -- but it does mean
`AXIOM_SCAN_SCANNED` and `LAUNDER_SCANNED` are not comparable across this
change.  Do not read a drop in those denominators as work disappearing.
-/

open Lean Elab Command Meta

namespace Check

/-- Is `n` declared in a `Calibrator` module, rather than in Mathlib?

`getRoot` and not `isPrefixOf`: they agree on every name in this corpus, and
`getRoot` says what is meant. -/
def isOurs (n : Name) : Bool := n.getRoot == `Calibrator

/-- The single answer to "did a person write this".  See the module docstring
above and `Shared.DeclFilter` for why there is exactly one. -/
abbrev userWritten (env : Environment) (n : Name) : Bool := Shared.userWritten env n

/-- The head constant of a type, if it has one. -/
def headConst? (e : Expr) : Option Name := e.getAppFn.constName?

/-- Strip leading lambda binders, returning the body.

A theorem with binders stores its proof as `fun a b c ↦ Eq.refl _`, so testing
the head of the whole value asks whether a LAMBDA is `Eq.refl` -- which is never
true.  The first version of the rfl scan did exactly that and reported 0 of 0, a
clean-looking null that a positive control on two known `:= rfl` theorems
refuted immediately. -/
partial def stripLams : Expr → Expr
  | .lam _ _ b _ => stripLams b
  | .mdata _ b => stripLams b
  | e => e

/-- `Module.lean:LINE` for a declaration, from the environment's own ranges. -/
def whereIs (env : Environment) (n : Name) : CoreM String := do
  let mod := match env.getModuleFor? n with
    | some m => m.toString
    | none => "?"
  match ← findDeclarationRanges? n with
  | some r => return s!"{mod}:{r.range.pos.line}"
  | none => return mod

/-! ## AXIOMS — the transitive axiom closure

Report the transitive axiom closure of every `Calibrator` declaration, and fail
on anything outside the three foundations Lean's own standard library rests on.

WHY THIS EXISTS.  The source-text half guards `sorry` with a regex over the
source text.  That is a scan of what a person typed, and the question is what
the KERNEL accepted.  The two come apart in the direction that matters:

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
-/

namespace Axioms

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
exactly the laundering families the LAUNDERING scan below exists to detect.

So the order of preference this file encodes, worst to best:

  * a custom axiom, a compiler-backed proof, a rebound `+` -- REJECTED, always;
  * a theorem whose statement was quietly weakened to fit the proof available --
    not visible here at all, which is why the LAUNDERING and INFLATION scans
    below and the vacuity and range detectors under `empirical/` exist;
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

/-- The names this scan is responsible for.

Scan every axiom, including unused custom axioms.  For value-bearing
declarations scan user-authored roots: generated declarations cannot introduce
an axiom absent from those roots, and explicit source guards independently
reject custom elaborators and compiler-backed proofs. -/
def roots (env : Environment) : Array Name := Id.run do
  let mut out := #[]
  for (name, ci) in env.constants.toList do
    unless Check.isOurs name do continue
    match ci with
    | .axiomInfo _ => out := out.push name
    | .thmInfo _ | .defnInfo _ | .opaqueInfo _ =>
      if Check.userWritten env name then out := out.push name
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
    (fun st n ↦ (((CollectAxioms.collect n).run env).run st).2)
    ({} : CollectAxioms.State)
  st.axioms

/-- User-authored declarations that directly introduce or use `target`.

`unionOfClosures` already answers the transitive question once.  Attribution
must not call `collectAxioms` again for each root: doing so re-walked Mathlib
forty times whenever `sorryAx` was present and turned a seconds-scale audit into
a fourteen-minute job.  A direct occurrence names the actual debtor.  An axiom
is included by its own name; an admission is included where the elaborated
proof term contains `sorryAx`.  Downstream consumers remain transitively marked
by Lean's ordinary `#print axioms` semantics, but are not mislabeled as forty
separate admissions. -/
def directDebtorsOf (env : Environment) (names : Array Name) (target : Name) :
    Array Name := Id.run do
  let mut out := #[]
  for n in names do
    if n == target then
      out := out.push n
      continue
    let some ci := env.find? n | continue
    let some value := ci.value? | continue
    if value.getUsedConstants.contains target then out := out.push n
  return out

end Axioms

/-! ## LAUNDERING — the premises the kernel sees

Report, for every user-authored `Calibrator` declaration, the premises the KERNEL sees,
and fail on the ones that make a theorem's name a claim its type does not support.

The patterns below all have a CLEAN axiom report, which is why the AXIOMS scan cannot
see them: none is a trust bypass.  They are valid proofs of a weaker, conditional,
vacuous, or circular statement, checked correctly and then advertised under the intended
theorem's name.  `theorem P_from_P (h : P) : P := h` has a clean `#print axioms`.

This is the elaborated-telescope half of the guard.  `check.py` is the source-text
half, and four things only this half can see:

  * a premise from an `export`ed or `open`ed instance, which appears in no binder;
  * the `variable` binders Lean actually inserted -- it includes a section variable only
    when the declaration mentions it, so the source line over-reports;
  * a definition that unfolds to something other than its written form;
  * whether a structure parameter's type is inhabited, which needs a search for a term of
    that type rather than a name lookup.

WHAT IS REPORTED

  LAUNDER_TAUTOLOGY   the conclusion is syntactically one of the premises: `P → P`
                      under a name that claims `P`.
  LAUNDER_DEFEQ_BRIDGE a premise and conclusion become equal only after unfolding.
                      Reported, not fatal: named representation bridges are useful.
  LAUNDER_PROJECTION  the proof term, after stripping lambdas, is a projection or
                      application of a bound premise.  Reported for review; not fatal
                      by itself because elimination and representation lemmas have
                      exactly this proof shape.
  LAUNDER_CERT        a corpus-defined parameter structure has Prop-valued fields and
                      the environment holds no closed term of that type.  Reported for
                      review, not fatal by shape alone: model domains and algebraic
                      interfaces also package laws in Prop-valued fields.  The source
                      guard separately rejects advertised theorem carriers.
  LAUNDER_PREMISE     a hidden Prop-valued premise (implicit, strict implicit, or instance).
                      All Prop premises still contribute to `LAUNDER_PREMISES`; ordinary
                      explicit side conditions are aggregated rather than printed thousands
                      of times.
  LAUNDER_EMPTY       a parameter type proved uninhabited, or `Empty` / `PEmpty` / `Fin 0`.
  LAUNDER_ASSUMPTION  an instance premise of class `Fact`, `Nonempty` or `Inhabited`:
                      assumptions in instance syntax.

A `sorry` is preferred to every one of these.  `sorryAx` is visible to the AXIOMS scan;
a laundered premise is visible to neither guard nor reader.
-/

namespace Laundering

/-- Classes that are ordinary mathematical structure rather than smuggled content.
A theorem about a normed space is not assuming a normed space exists; it is naming the
category it is stated in.  A theorem carrying `[Fact (p < 1)]` is assuming `p < 1`. -/
def assumptionClasses : List Name :=
  [``Fact, ``Nonempty, ``Inhabited]

/-- A structure declared in this corpus whose fields include at least one Prop.
Such a parameter is a CERTIFICATE: the caller hands over finished mathematics. -/
def certificateFields (env : Environment) (S : Name) : MetaM (Array Name) := do
  let some info := getStructureInfo? env S | return #[]
  let mut out := #[]
  for f in info.fieldNames do
    let some proj := env.find? (S ++ f) | continue
    -- The `isProp` test MUST happen inside the telescope.  Returning the body
    -- out of `forallTelescopeReducing` leaks the fvars it bound, and the check
    -- then runs in a context where they do not exist -- which surfaces much
    -- later as `unknown free variable`, nowhere near the cause.
    let isP ← forallTelescopeReducing proj.type fun _ b ↦ isProp b
    if isP then out := out.push f
  return out

/-- Every structure the corpus exhibits a closed term of, in ONE pass.

`hasWitness S` used to walk `env.constants` for each `S` it was asked about.
The environment holds the whole of Mathlib, and the walk runs
`forallTelescopeReducing` on every constant in it, so the cost is
(structures asked about) x (constants in Mathlib) x (one telescope each).

That cost was invisible while `S.mk.inj` was passing the generated-declaration
filter: the scan reached the 100-error ceiling and exited long before it had
asked about many structures. With the filter corrected the scan runs to the end
of the corpus, and at that point it does not finish inside fifteen minutes.

One pass, building the set. The predicate is unchanged: a closed term of `S ..`,
or a proof of `Nonempty (S ..)`, with no `Prop` argument in its telescope --
a witness that itself needs a hypothesis discharged is not a closed term. Thus
this distinguishes structures the corpus constructs from structures it only
consumes without relocating the mathematical obligation into a premise. -/
def witnessedStructures (env : Environment) : MetaM NameSet := do
  let mut out : NameSet := {}
  for (n, ci) in env.constants.toList do
    unless Check.isOurs n do continue
    unless ci.isDefinition || ci.isCtor || ci.isTheorem do continue
    if n.isInternalDetail then continue
    let s? ← forallTelescopeReducing ci.type fun args body ↦ do
      -- Either a term of `S ..`, or a proof of `Nonempty (S ..)`.  A theorem witnesses
      -- a Prop-valued structure; a `Nonempty` proof witnesses a data one.
      let body := match body.getAppFn.constName? with
        | some ``Nonempty => (body.getAppArgs[0]?).getD body
        | _ => body
      let some h := Check.headConst? body | return none
      for a in args do
        if ← isProp (← inferType a) then return none
      return some h
    if let some h := s? then out := out.insert h
  return out

/-- After stripping leading lambdas, is the proof term an application or projection of a
BOUND VARIABLE?  Then the mathematics arrived as an argument. -/
partial def endsInParameter (e : Expr) : Bool :=
  match e with
  | .lam _ _ b _ => endsInParameter b
  | .mdata _ b => endsInParameter b
  | .letE _ _ _ b _ => endsInParameter b
  | .proj _ _ b => b.getAppFn.isBVar || b.getAppFn.isFVar
  | .app .. => e.getAppFn.isBVar || e.getAppFn.isFVar
  | .bvar _ => true
  | .fvar _ => true
  | _ => false

structure Finding where
  tag : String
  fatal : Bool
  mod : Name
  decl : Name
  detail : String

end Laundering

/-! ## INFLATION — theorems whose proof is their own assumed hypothesis

WHY THIS IS A LEAN METAPROGRAM AND NOT A GREP.  The question is what a proof
TERM is, and that is only visible after elaboration.  Three separate text scans
of this same question gave 2, 16 and 3 hits with no overlap in names, and one of
them reported a word out of a docstring as a theorem.  The environment cannot
make that mistake: a theorem is a `thmInfo`, its proof is an `Expr`, and a field
access is a projection whether it was written `S.barrier`, `S.1`, or reached
through dot notation.

Writes `proofs/validation/code/results/inflation.json`: every hit by name,
untruncated, stamped with the revision it was measured at.  Read that file
rather than a commit message.  The 12/354/2 figures quoted for this tool were
never backed by one and describe a tree 55 commits behind HEAD.
-/

namespace Inflation

/-- Structures declared here that carry at least one `Prop`-valued field. -/
def assumptionCarriers (env : Environment) : MetaM (Array (Name × Array Name)) := do
  let mut out := #[]
  for (n, _ci) in env.constants.toList do
    unless Check.isOurs n do continue
    let some info := getStructureInfo? env n | continue
    let mut props := #[]
    for f in info.fieldNames do
      let some proj := env.find? (n ++ f) | continue
      -- See `Laundering.certificateFields`: the `isProp` test must run INSIDE
      -- the telescope or the fvars it bound leak into a context without them.
      let isP ← forallTelescopeReducing proj.type fun _ b ↦ isProp b
      if isP then props := props.push f
    if props.size > 0 then out := out.push (n, props)
  return out

/-- Every constant name appearing in an expression.

    Lean's own `getUsedConstants` rather than a hand-rolled recursion: proof
    terms produced by tactic blocks are large and heavily shared, and an
    uncached structural walk re-visits the same subterms exponentially often.
    The first version of this scan did exactly that and did not finish. -/
def constsOf (e : Expr) : NameSet :=
  e.getUsedConstants.foldl (fun s n ↦ s.insert n) NameSet.empty

/-- Record every carrier whose CONSTRUCTOR appears among these constants.

    Pattern-matches on `.str p "mk"`.  `Name.getString!` PANICS on anonymous and
    numeric names, and the environment is full of both (`_private.…`, macro
    scopes), so calling it on every constant of every proof term brought the
    whole run down with `unreachable code has been reached`. -/
def noteConstructors (carriers : NameSet) (cs : NameSet) (acc : NameSet) : NameSet :=
  cs.fold (init := acc) fun acc c ↦
    match c with
    | .str p "mk" => if carriers.contains p then acc.insert p else acc
    | _ => acc

end Inflation

/-! ## RFL — theorems whose proof term is literally `Eq.refl`

Enumerated from the elaborated environment rather than from source text.

Three text scans of the same nine modules returned 2, 16 and 3, with zero
overlap in names between the last two: a non-greedy regex spans declarations, an
anchored one misses `rfl` on its own line, and a block splitter trips on a `:=`
inside the statement.  Lean is whitespace-insensitive and its proofs are not a
regular language; the environment is the only authority.

Writes `proofs/validation/code/results/rfl.json`: every hit by name and module,
stamped with the revision it was measured at.  Read that file, not a commit
message.  The "8 of 8 classified" quoted for this scan was measured with a
module allow-list of ten popgen modules that no version of this scan now
contains, so it does not describe what this file does.
-/

namespace Rfl

/-- Is this proof term literally a reflexivity proof? -/
def isReflProof (e : Expr) : Bool :=
  (Check.stripLams e).getAppFn.isConstOf ``Eq.refl

end Rfl


/-! ## JUNK — definitions that can return a totality artifact and never say so

Mathlib totalises partial operations: `x / 0 = 0`, `Real.log 0 = 0`,
`Real.sqrt x = 0` for `x < 0`, `x⁻¹` at `0`.  A definition built from these
returns a number at every point of its type, and at some of those points the
number is the convention showing through rather than the modelled quantity.
Nothing errors, nothing is flagged, and the value is usually in range.

The corpus convention is to NAME such a branch: a theorem stating what the
definition returns there, with a docstring saying what the quantity actually
does at that point and what consumers must require.  See
`stabilizingNsFromObservedCorrelation_perfect_is_junk`.

WHY THIS SCAN IS HERE AND NOT IN PYTHON.  `junk_gap.py` reads source text and is
blind to aliasing.  Twice during this corpus's development a deduplication pass
rewrote `bitSign := ![-1, 1]` to `bitSign := driftFieldB`, and the text scan
stopped seeing a vector literal it had been matching on.  This scan reads the
elaborated environment, so an alias, an abbreviation and a literal are the same
expression to it.

WHAT IT CANNOT DO.  It cannot decide REACHABILITY -- whether the junk point lies
inside the definition's admissible box.  That is the three-part test in
`proofs/validation/empirical/invariants/totality.py`, and it is undecidable in
general.  So this scan enforces the weaker, checkable contract: every definition
that CAN reach a junk value either names the branch or appears in `exempt` with
a reason.  A definition whose guard provably cannot vanish is not a defect, and
saying so in `exempt` is the whole cost of clearing it.
-/

namespace Junk

/-- The totalised partial operations. -/
def junkOps : List Name := [``HDiv.hDiv, ``Inv.inv, ``Real.log, ``Real.sqrt]

/-- Definitions checked by hand whose guard cannot vanish anywhere in the type,
so there is no branch to name.  A list with reasons rather than a pattern:
every attempt to generalise these into a rule also swallowed definitions whose
guard genuinely can vanish.  `scalarRowResolvent` divides by
`1 + latent ^ 2 * quadraticForm`, which looks exactly like `sigmoid`'s
denominator and is not, because `quadraticForm` may be negative. -/
def exempt : List (Name × String) :=
  [ (`Calibrator.sigmoid, "1 + Real.exp (-x) ≥ 1"),
    (`Calibrator.standardNormalPdf, "Real.sqrt (2 * Real.pi) ≠ 0"),
    (`Calibrator.squaringFixedPoint, "scale ^ 2 + 4 ≥ 4"),
    (`Calibrator.characteristicAmplitude, "a sum of squares is nonnegative"),
    (`Calibrator.gaussianCriticalMultiplier, "condensationConstant is proved positive"),
    (`Calibrator.chain, "2 * k + 1 ≠ 0 for k : ℕ"),
    (`Calibrator.uniformOccupancyDistinctHaplotypes, "(2 : ℝ) ^ k ≠ 0"),
    (`Calibrator.chain, "2 * k + 1 ≥ 1 for k : ℕ"),
    (`Calibrator.meffPerturbed, "((n : ℝ) + 1)⁻¹ with n : ℕ, so the base is ≥ 1"),
    (`Calibrator.probitScaleFactor,
      "1 + a0 ^ 2 * ouVariance ≥ 1, since ouVariance_nonneg"),
    (`Calibrator.probitIntercept, "divides by probitScaleFactor, proved positive"),
    (`Calibrator.BoundedLogDistortion, "a Prop, not a value: the log sits under a binder"),
    (`Calibrator.fairTwoPointVariance, "divides by the numeral 4"),
    (`Calibrator.informationCrossoverTime, "divides by the numeral 2"),
    (`Calibrator.horizonPolynomial, "coefficients are numerals"),
    (`Calibrator.copiedBinaryJointExpectation, "divides by the numeral 2"),
    (`Calibrator.twoMechanismMixture, "coefficients are numerals"),
    (`Calibrator.threeMechanismMixture, "coefficients are numerals"),
    (`Calibrator.condensationConstant, "Real.log 2 with a numeral argument"),
    (`Calibrator.gaussianJetVariance, "Real.pi ^ 2 / 2 with numeral divisor"),
    (`Calibrator.gaussianKurtosisMaf, "Real.sqrt 3 with a numeral argument"),
    (`Calibrator.expanderAgreementFloor, "Real.sqrt 5 with a numeral argument"),
    (`Calibrator.ldPruningDetectionDeficit, "divides by Real.pi * (1 + decay ^ 2) ≥ π"),
    (`Calibrator.ldBandDetectionShare, "divides by Real.pi * (1 + decay ^ 2) ≥ π"),
    (`Calibrator.posteriorPrecision, "1 / prior_var + data_precision; prior_var is a model field"),
    (`Calibrator.standardNormalPdf, "Real.sqrt (2 * Real.pi) ≠ 0"),
    (`Calibrator.characteristicAmplitude, "Real.sqrt of a sum of squares"),
    (`Calibrator.outerAtom, "Real.sqrt (1 + w) under the module's own w ≥ 0 convention"),
    (`Calibrator.conditionalGainFunctional, "branches on the amplitude being zero already"),
    (`Calibrator.equalVarianceGaussianAUCFromSignalVariance, "branches on vNoise = 0 already"),
    (`Calibrator.equalVarianceGaussianAUCFromExplainedR2, "branches on 1 ≤ r2 already"),
    (`Calibrator.fiberConditional, "branches on the fiber being hit already"),
    (`Calibrator.samplePCOverlapSq, "branches on the BBP threshold already"),
    (`Calibrator.hasInteraction, "a Prop: the quotient sits under a binder"),
    (`Calibrator.exitLevels, "a Set: the quotient sits under a binder"),
    (`Calibrator.hetRecurrence, "proof by induction, not a value"),
    (`Calibrator.hetMutationDriftRecurrence, "proof by induction, not a value"),
    (`Calibrator.rsquared, "an integral expression: the quotient sits under ∫"),
    (`Calibrator.peelSet, "a Set: the preimage sits under a binder"),
    (`Calibrator.logSqGaussianLaw, "a Measure, not a real value"),
    (`Calibrator.jProfile, "Real.log (1 ± s) on the module's own |s| < 1 convention"),
    (`Calibrator.hardCallLatticeSpan, "Real.log at latticeCriticalMaf, proved in (0,1)"),
    (`Calibrator.gaussianProfileLogLik, "a log-likelihood: variance positive by model"),
    (`Calibrator.liabilitySensitivity, "Real.sqrt of h_sq and R2, both model-bounded in [0,1]"),
    (`Calibrator.liabilitySpecificity, "Real.sqrt of h_sq and R2, both model-bounded in [0,1]"),
    (`Calibrator.Expected_Abs_Shift, "Real.sqrt of a variance, nonnegative by construction"),
    (`Calibrator.serialFounderWithinTime, "Real.exp arguments, and 2 * N with N a census size"),
    (`Calibrator.sigmaThetaFromObservedSelectedVariance, "Real.sqrt of an observed variance excess") ]

/-- Is this a numeric literal, or a ratio or negation of them?

A divisor built only from numerals cannot vanish, so `(p₁ + p₂) / 2` has no junk
branch.  The first version of this scan tested only whether `HDiv.hDiv` occurred
anywhere in the body, and reported 496 definitions -- including every weight
vector defined as `![3 / 4, 1 / 4]`.  Counting those as open work is the scan's
own false positive and makes the total meaningless. -/
partial def isLiteral (e : Expr) : Bool :=
  match e.getAppFn.constName? with
  | some ``OfNat.ofNat => true
  | some ``Neg.neg => match e.getAppArgs[2]? with
      | some a => isLiteral a
      | none => false
  | some ``HDiv.hDiv =>
      match e.getAppArgs[4]?, e.getAppArgs[5]? with
      | some a, some b => isLiteral a && isLiteral b
      | _, _ => false
  | _ => e.isRawNatLit

/-- Does this application totalise a partial operation on a NON-CONSTANT
operand?  The operand position differs per operation: `HDiv.hDiv` and `Inv.inv`
are heterogeneous-operation classes carrying instance arguments ahead of the
values, while `Real.log` and `Real.sqrt` take their argument first. -/
def riskyHere (e : Expr) : Bool :=
  let args := e.getAppArgs
  match e.getAppFn.constName? with
  | some ``HDiv.hDiv => match args[5]? with
      | some d => !isLiteral d
      | none => false
  | some ``Inv.inv => match args[2]? with
      | some d => !isLiteral d
      | none => false
  | some ``Real.log => match args[0]? with
      | some d => !isLiteral d
      | none => false
  | some ``Real.sqrt => match args[0]? with
      | some d => !isLiteral d
      | none => false
  | _ => false

/-- Does this value apply a totalised partial operation to something that can
vanish?  Walks the definition body only; theorem proof terms are never scanned,
so the exponential-revisit hazard recorded on `Inflation.constsOf` does not
arise here. -/
partial def usesJunkOp (e : Expr) : Bool :=
  riskyHere e ||
    (match e with
      | .app f a => usesJunkOp f || usesJunkOp a
      | .lam _ t b _ => usesJunkOp t || usesJunkOp b
      | .forallE _ t b _ => usesJunkOp t || usesJunkOp b
      | .letE _ t v b _ => usesJunkOp t || usesJunkOp v || usesJunkOp b
      | .mdata _ b => usesJunkOp b
      | .proj _ _ b => usesJunkOp b
      | _ => false)

/-- Does the type carry a hypothesis that rules the junk point out before the
body runs -- a positivity, a nonzero, or an order bound?

Recurses into the BINDER TYPE as well as the body. Several definitions here take
their guard universally quantified -- `reverseBridge` and `transportedResponse`
both take `∀ y, 0 < transportMass P population y` -- and a version that looked
only at the head of each binder type saw a `forallE` there and missed them. Those
definitions cannot reach their junk point at all, and were being reported as open
work. -/
partial def hasGuardBinder : Expr → Bool
  | .forallE _ t b _ =>
      (match t.getAppFn.constName? with
        | some ``LT.lt | some ``LE.le | some ``Ne => true
        | _ => false) || hasGuardBinder t || hasGuardBinder b
  | .mdata _ b => hasGuardBinder b
  | _ => false

/-- Does this structure carry a domain fact as a field?

Checks each field's PROJECTION TYPE for an order or disequality constant, rather
than the field's name. Name-based matching catches `Ne_pos` and `mu_nonneg` and
misses `h_k : 0 < k` and `h_variances : ∀ i, 0 < variances i`, which are just as
binding. A definition taking such a structure cannot reach its junk point however
it is called: `EvolutionaryParameters` carries `Ne_pos`, so `fstDriftMigration`
never divides by zero.

The Python scan `junk_gap.py` has had this check since early on; this one did
not, and the difference was the largest remaining gap between the two totals. -/
def structureCarriesDomainFact (env : Environment) (S : Name) : Bool :=
  (getStructureFields env S).any fun f ↦
    match env.find? (S ++ f) with
    | some ci =>
        (Inflation.constsOf ci.type).fold (init := false) fun acc n ↦
          acc || n == ``LT.lt || n == ``LE.le || n == ``Ne
    | none => false

/-- Does any argument of this definition have a structure type carrying a domain
fact? -/
partial def argumentStructureGuards (env : Environment) : Expr → Bool
  | .forallE _ t b _ =>
      (match t.getAppFn.constName? with
        | some S => isStructure env S && structureCarriesDomainFact env S
        | none => false) || argumentStructureGuards env b
  | .mdata _ b => argumentStructureGuards env b
  | _ => false

/-- Every theorem name in the corpus that names a junk branch. -/
def namedBranches (env : Environment) : Array String := Id.run do
  let mut out : Array String := #[]
  for (n, ci) in env.constants.toList do
    if isOurs n && ci.isTheorem then
      let s := n.toString
      if (s.splitOn "_is_junk").length > 1 then
        out := out.push s
  return out

end Junk

end Check

/-! ## Driver

One `run_cmd` for all four scans.  They share the environment traversal cost and,
more importantly, they share the declaration filter: running them as four
separate files is how the filter came to have three disagreeing copies.

`logError` is what makes the run exit nonzero, so it marks offences only.
Everything else is `logInfo` or `IO.println`.
-/

open Check in
run_cmd do
  let env ← getEnv

  ---------------------------------------------------------------------------
  -- AXIOMS
  ---------------------------------------------------------------------------
  let allowed := Axioms.allowed
  let admissible := Axioms.admissible
  let names := Axioms.roots env
  let scanned := names.size
  let union := Axioms.unionOfClosures env names
  let extra := union.filter fun a ↦ !(allowed.contains a)
  let offending := extra.filter fun a ↦ !(admissible.contains a)
  let admitted := extra.filter fun a ↦ admissible.contains a
  let mut offenders : Array (Name × Name × Array Name) := #[]
  let mut admissions : Array (Name × Name × Array Name) := #[]
  for a in offending do
    for n in Axioms.directDebtorsOf env names a do
      offenders := offenders.push ((env.getModuleFor? n).getD `«unknown», n, #[a])
  for a in admitted do
    for n in Axioms.directDebtorsOf env names a do
      admissions := admissions.push ((env.getModuleFor? n).getD `«unknown», n, #[a])
  for (m, name, bad) in offenders do
    logError m!"AXIOM\t{m}\t{name}\t{bad.toList}"
  -- Admissions are printed one per direct debtor.  The union check above is
  -- transitive; this attribution list intentionally names where the debt enters
  -- the corpus rather than an arbitrary capped prefix of downstream consumers.
  for (m, name, bad) in admissions do
    logInfo m!"ADMISSION\t{m}\t{name}\t{bad.toList}"
  logInfo m!"AXIOM_SCAN_SCANNED\t{scanned}"
  logInfo m!"AXIOM_SCAN_OFFENDERS\t{offenders.size}"
  -- Printed even at zero: a missing line reads as "not measured", and the whole
  -- reason admissions are permitted is that they are counted in the open.
  logInfo m!"ADMISSION_SCAN_COUNT\t{admissions.size}"
  logInfo m!"AXIOM_SCAN_ALLOWED\t{allowed}"
  logInfo m!"AXIOM_SCAN_ADMISSIBLE\t{admissible}"

  ---------------------------------------------------------------------------
  -- LAUNDERING
  ---------------------------------------------------------------------------
  let mut findings : Array Laundering.Finding := #[]
  let mut lScanned := 0
  let mut premises := 0
  -- structure name -> (Prop fields, is inhabited); computed once, not per use site
  let mut certCache : Std.HashMap Name (Array Name × Bool) := {}
  -- The inhabited half comes from one environment pass rather than one per
  -- structure; see `Laundering.witnessedStructures` for why that matters.
  let witnessed ← liftTermElabM <| Laundering.witnessedStructures env

  for (name, ci) in env.constants.toList do
    unless isOurs name do continue
    unless ci.isTheorem do continue
    unless userWritten env name do continue
    lScanned := lScanned + 1
    let mod := (env.getModuleFor? name).getD `«unknown»

    let (newFindings, newPremises, cache) ←
      liftTermElabM <| Meta.forallTelescopeReducing ci.type fun args concl ↦ do
        let mut fs : Array Laundering.Finding := #[]
        let mut prems := 0
        let mut cache := certCache
        for a in args do
          let ty ← inferType a
          let bi ← a.fvarId!.getBinderInfo
          let nm := (← a.fvarId!.getUserName)
          if ← isProp ty then
            prems := prems + 1
            -- A literal P → P is fatal.  Definitional equality after unfolding
            -- is not: representation bridges deliberately expose the same fact
            -- through two public interfaces.
            if ty == concl then
              fs := fs.push ⟨"LAUNDER_TAUTOLOGY", true, mod, name,
                s!"premise `{nm}` is the conclusion; this proves P → P"⟩
            else if ← isDefEq ty concl then
              fs := fs.push ⟨"LAUNDER_DEFEQ_BRIDGE", false, mod, name,
                s!"premise `{nm}` and conclusion agree after unfolding"⟩
            else
              match bi with
              | .instImplicit =>
                  fs := fs.push ⟨"LAUNDER_PREMISE", false, mod, name,
                    s!"instance premise `{nm} : {← ppExpr ty}`"⟩
              | .implicit =>
                  fs := fs.push ⟨"LAUNDER_PREMISE", false, mod, name,
                    s!"implicit premise `{nm} : {← ppExpr ty}`"⟩
              | .strictImplicit =>
                  fs := fs.push ⟨"LAUNDER_PREMISE", false, mod, name,
                    s!"strict-implicit premise `{nm} : {← ppExpr ty}`"⟩
              | .default => pure ()
              if let some h := headConst? ty then
                if Laundering.assumptionClasses.contains h then
                  fs := fs.push ⟨"LAUNDER_ASSUMPTION", false, mod, name,
                    s!"`{h}` premise `{nm}` is an assumption in instance syntax"⟩
          else
            -- Data parameters: empty domains, and unbuilt certificates.
            if let some h := headConst? ty then
              if h == ``Empty || h == ``PEmpty then
                fs := fs.push ⟨"LAUNDER_EMPTY", true, mod, name,
                  s!"parameter `{nm} : {h}` -- the statement is vacuous"⟩
              -- Mathlib typeclasses such as `TopologicalSpace`, `Ring`, and
              -- `MeasurableSpace` also have Prop-valued fields.  They are part
              -- of the ambient language, not theorem certificates declared by
              -- this corpus.  Treating them as unbuilt Calibrator carriers
              -- made every ordinary polymorphic theorem a fatal false positive.
              else if Check.isOurs h && (getStructureInfo? env h).isSome then
                let entry ← match cache[h]? with
                  | some e => pure e
                  | none => do
                      let flds ← Laundering.certificateFields env h
                      let e := (flds, witnessed.contains h)
                      cache := cache.insert h e
                      pure e
                let (flds, wit) := entry
                if !flds.isEmpty && !wit then
                  fs := fs.push ⟨"LAUNDER_CERT", false, mod, name,
                    s!"parameter `{nm} : {h}` bundles the premises {flds.toList}, and no \
                       closed term of `{h}` exists in the corpus: nothing shows this \
                       theorem is about anything"⟩
        return (fs, prems, cache)
    findings := findings ++ newFindings
    premises := premises + newPremises
    certCache := cache

    -- PROJECTION: the proof term bottoms out in one of its own parameters.
    if let some val := ci.value? then
      if Laundering.endsInParameter val then
        findings := findings.push ⟨"LAUNDER_PROJECTION", false, mod, name,
          "proof term is an application or projection of a parameter"⟩

  let fatal := findings.filter (·.fatal)
  for f in findings do
    if f.fatal then
      logError m!"{f.tag}\t{f.mod}\t{f.decl}\t{f.detail}"
    else
      logInfo m!"{f.tag}\t{f.mod}\t{f.decl}\t{f.detail}"
  logInfo m!"LAUNDER_SCANNED\t{lScanned}"
  logInfo m!"LAUNDER_PREMISES\t{premises}"
  logInfo m!"LAUNDER_FATAL\t{fatal.size}"
  logInfo m!"LAUNDER_TOTAL\t{findings.size}"

  ---------------------------------------------------------------------------
  -- INFLATION and RFL
  --
  -- One pass over the constants for both: each needs `thmInfo` values, and the
  -- inflation scan additionally needs `defnInfo` values to see which carriers
  -- ever get constructed.
  ---------------------------------------------------------------------------
  let carriers ← liftTermElabM <| Inflation.assumptionCarriers env
  let carrierNames : NameSet := carriers.foldl (fun s (n, _) ↦ s.insert n) NameSet.empty
  -- projection constants for Prop fields, e.g. `Calibrator.ChaosSpectroscopy.barrier`
  let mut propProj : NameSet := NameSet.empty
  for (s, fs) in carriers do
    for f in fs do propProj := propProj.insert (s ++ f)

  let mut exactHits : Array (Name × Name) := #[]
  let mut usesHits  : Array (Name × Name) := #[]
  let mut builtInstances : NameSet := NameSet.empty
  let mut nthm := 0
  let mut rflCount := 0
  let mut rflHits : Array Json := #[]

  for (n, ci) in env.constants.toList do
    unless isOurs n do continue
    match ci with
    | .thmInfo ti =>
      unless userWritten env n do continue
      nthm := nthm + 1
      let body := stripLams ti.value
      -- PATTERN 1: the whole proof is a Prop-field projection of an argument.
      let hd := body.getAppFn
      match hd with
      | .const c _ => if propProj.contains c then exactHits := exactHits.push (n, c)
      | _ =>
        match body with
        | .proj s i _ =>
          match getStructureInfo? env s with
          | some info =>
            if i < info.fieldNames.size then
              let f := s ++ info.fieldNames[i]!
              if propProj.contains f then exactHits := exactHits.push (n, f)
          | none => pure ()
        | _ => pure ()
      -- PATTERNS 2/3: the proof MENTIONS such a projection anywhere.
      let cs := Inflation.constsOf ti.value
      for c in propProj.toList do
        if cs.contains c then
          if !(exactHits.any (fun (a, b) ↦ a == n && b == c)) then
            usesHits := usesHits.push (n, c)
      -- record which carrier structures ever get CONSTRUCTED
      builtInstances := Inflation.noteConstructors carrierNames cs builtInstances
      -- RFL, over the same population.  `nthm` IS the rfl denominator: both
      -- scans want hand-written `Calibrator` theorems, and before the merge
      -- they computed that population with two different filters.
      if Rfl.isReflProof ti.value then
        let m := (env.getModuleFor? n).getD `«unknown»
        logInfo m!"RFL\t{m}\t{n}"
        rflCount := rflCount + 1
        rflHits := rflHits.push <| Json.mkObj
          [ ("theorem", toJson n.toString), ("module", toJson m.toString) ]
    | .defnInfo di =>
      unless userWritten env n do continue
      let cs := Inflation.constsOf di.value
      builtInstances := Inflation.noteConstructors carrierNames cs builtInstances
    | _ => pure ()

  -- Every loop below builds the console line and the stored JSON entry from the
  -- same values in the same pass.  Not a stylistic choice: a printed total and
  -- a stored list assembled separately can disagree, and a stored list that
  -- disagrees with the console is worse than no stored list at all.
  IO.println s!"theorems examined (Calibrator only): {nthm}"
  IO.println s!"assumption-carrying structures      : {carriers.size}"
  IO.println ""
  IO.println "=== PATTERN 1: the proof IS the hypothesis (exact projection)"
  IO.println s!"    {exactHits.size} theorem(s)"
  let mut exactJson : Array Json := #[]
  for (t, f) in exactHits do
    let loc ← liftCoreM <| whereIs env t
    let built := builtInstances.contains f.getPrefix
    IO.println s!"  {t}   [{loc}]"
    IO.println s!"      consumes: {f}   [carrier instance built: {built}]"
    exactJson := exactJson.push <| Json.mkObj
      [ ("theorem", toJson t.toString), ("location", toJson loc),
        ("consumes", toJson f.toString), ("carrierInstanceBuilt", toJson built) ]
  IO.println ""
  IO.println "=== PATTERNS 2/3: the proof MENTIONS an assumed field"
  let usedTheorems := usesHits.foldl (fun s (t, _) ↦ s.insert t) NameSet.empty
  IO.println s!"    {usedTheorems.size} distinct theorem(s), {usesHits.size} theorem/field pair(s)"
  let mut usesJson : Array Json := #[]
  for (t, f) in usesHits do
    let loc ← liftCoreM <| whereIs env t
    IO.println s!"  {t}   [{loc}]  <- {f}"
    usesJson := usesJson.push <| Json.mkObj
      [ ("theorem", toJson t.toString), ("location", toJson loc),
        ("field", toJson f.toString) ]
  IO.println ""
  IO.println "=== PATTERN 4: assumption-carrying structures with NO instance built"
  let mut none_ := 0
  let mut uninhabitedJson : Array Json := #[]
  for (s, fs) in carriers do
    if !builtInstances.contains s then
      none_ := none_ + 1
      let loc ← liftCoreM <| whereIs env s
      IO.println s!"  {s}   ({fs.size} Prop field(s))  [{loc}]"
      uninhabitedJson := uninhabitedJson.push <| Json.mkObj
        [ ("structure", toJson s.toString), ("location", toJson loc),
          ("propFields", toJson (fs.map (fun f ↦ f.toString))) ]
  IO.println s!"    {none_} of {carriers.size} carriers are never constructed"
  logInfo m!"TOTAL_RFL_THEOREMS\t{rflCount}"


  ---------------------------------------------------------------------------
  -- JUNK
  ---------------------------------------------------------------------------
  let named := Junk.namedBranches env
  -- Match on the LAST name component. The list was written as `Calibrator.foo`,
  -- but several of these definitions sit in nested namespaces -- `chain` is
  -- `Calibrator.BundleRigidity.chain` -- so full-name matching silently failed
  -- for them and they stayed on the open list despite being exempt.
  let exemptNames := Junk.exempt.map (fun p ↦ p.fst.getString!)
  let mut junkScanned := 0
  let mut junkNamed := 0
  let mut junkGuarded := 0
  let mut junkExempt := 0
  let mut junkOpen : Array (Name × String) := #[]
  for (n, ci) in env.constants.toList do
    if isOurs n && userWritten env n && !ci.isTheorem then
      if let some v := ci.value? then
        if Junk.usesJunkOp v then
          junkScanned := junkScanned + 1
          let base := n.getString!
          if exemptNames.contains base then
            junkExempt := junkExempt + 1
          else if named.any (fun t ↦ (t.splitOn base).length > 1) then
            junkNamed := junkNamed + 1
          else if Junk.hasGuardBinder ci.type
              || Junk.argumentStructureGuards env ci.type then
            junkGuarded := junkGuarded + 1
          else
            let loc ← liftCoreM <| whereIs env n
            junkOpen := junkOpen.push (n, loc)
  IO.println s!"JUNK: {junkScanned} definitions can return a totality artifact"
  IO.println <|
    s!"  {junkNamed} name the branch, {junkGuarded} rule it out by hypothesis, " ++
      s!"{junkExempt} exempt"
  for (n, loc) in junkOpen do
    IO.println s!"  OPEN  {n}   [{loc}]"
  logInfo m!"JUNK_SCANNED\t{junkScanned}"
  logInfo m!"JUNK_NAMED\t{junkNamed}"
  logInfo m!"JUNK_OPEN\t{junkOpen.size}"

  ---------------------------------------------------------------------------
  -- Stored results
  ---------------------------------------------------------------------------
  Shared.Results.write "proofs/validation/code/results/inflation.json" "Inflation"
    [ ("theoremsExamined", toJson nthm),
      ("assumptionCarryingStructures", toJson carriers.size),
      -- Pattern 1 pushes at most once per theorem, so this size IS a theorem count.
      ("pattern1Count", toJson exactHits.size),
      ("pattern1", Json.arr exactJson),
      -- Patterns 2/3 push once per (theorem, field), so the two differ and both
      -- are stored.  Reporting only the pair count as a theorem count is the
      -- error that turned an unknown number of theorems into the quoted "354".
      ("pattern23DistinctTheorems", toJson usedTheorems.size),
      ("pattern23PairCount", toJson usesHits.size),
      ("pattern23", Json.arr usesJson),
      ("pattern4UninhabitedCount", toJson none_),
      ("pattern4", Json.arr uninhabitedJson) ]

  Shared.Results.write "proofs/validation/code/results/rfl.json" "RflScan"
    [ -- The denominator this scan never used to report. Without it a hit count
      -- cannot be read as a rate, and "8 of 8" was quoted as though it could.
      ("handWrittenTheoremsScanned", toJson nthm),
      ("rflTheoremCount", toJson rflCount),
      -- No module allow-list: this scans every `Calibrator` module. The commit
      -- that reported 8 restricted to ten popgen modules; that list is gone.
      ("moduleFilter", Json.null),
      ("rflTheorems", Json.arr rflHits) ]

  Shared.Results.write "proofs/validation/code/results/axioms.json" "AxiomScan"
    [ ("scanned", toJson scanned),
      ("offenderCount", toJson offenders.size),
      ("offenders", Json.arr (offenders.map fun (m, n, bad) ↦ Json.mkObj
        [ ("module", toJson m.toString), ("declaration", toJson n.toString),
          ("axioms", toJson (bad.map (·.toString))) ])),
      ("admissionCount", toJson admissions.size),
      ("admissions", Json.arr (admissions.map fun (m, n, bad) ↦ Json.mkObj
        [ ("module", toJson m.toString), ("declaration", toJson n.toString),
          ("axioms", toJson (bad.map (·.toString))) ])),
      ("allowed", toJson (allowed.map (·.toString))),
      ("admissible", toJson (admissible.map (·.toString))) ]

  Shared.Results.write "proofs/validation/code/results/laundering.json" "LaunderingScan"
    [ ("scanned", toJson lScanned),
      ("premises", toJson premises),
      ("fatalCount", toJson fatal.size),
      ("totalCount", toJson findings.size),
      ("findings", Json.arr (findings.map fun f ↦ Json.mkObj
        [ ("tag", toJson f.tag), ("fatal", toJson f.fatal),
          ("module", toJson f.mod.toString), ("declaration", toJson f.decl.toString),
          ("detail", toJson f.detail) ])) ]
