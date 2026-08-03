/-
Copyright (c) 2026 Sauers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sauers
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

  LAUNDER_TAUTOLOGY   the conclusion is definitionally one of the premises: `P → P`
                      under a name that claims `P`.
  LAUNDER_PROJECTION  the proof term, after stripping lambdas, is a projection or
                      application of a bound premise.  The mathematics is the caller's.
  LAUNDER_CERT        a parameter is a structure with Prop-valued fields and the
                      environment holds no closed term of that type.  Conditional on a
                      certificate the corpus never builds, and possibly vacuous.
  LAUNDER_PREMISE     a Prop-valued premise, explicit or implicit or instance.  The
                      conditionality ledger: its count is the size of what is assumed.
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

/-- Is there a closed term of type `S ..` anywhere in the environment -- that is, does
the corpus CONSTRUCT one of these, or only consume them?

A witness may take data parameters and may not take Prop-valued ones: a family of
models indexed by a frequency inhabits the class, while a "witness" that first demands
the hard theorem inhabits nothing and merely relocates the obligation. -/
def hasWitness (env : Environment) (S : Name) : MetaM Bool := do
  for (n, ci) in env.constants.toList do
    unless Check.isOurs n do continue
    unless ci.isDefinition || ci.isCtor || ci.isTheorem do continue
    if n.isInternalDetail then continue
    let ok ← forallTelescopeReducing ci.type fun args body ↦ do
      -- Either a term of `S ..`, or a proof of `Nonempty (S ..)`.  A theorem witnesses
      -- a Prop-valued structure; a `Nonempty` proof witnesses a data one.
      let body := match body.getAppFn.constName? with
        | some ``Nonempty => (body.getAppArgs[0]?).getD body
        | _ => body
      if Check.headConst? body != some S then return false
      for a in args do
        if ← isProp (← inferType a) then return false
      return true
    if ok then return true
  return false

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
    for n in Axioms.witnessesOf env names a 20 do
      offenders := offenders.push ((env.getModuleFor? n).getD `«unknown», n, #[a])
  for a in admitted do
    for n in Axioms.witnessesOf env names a 40 do
      admissions := admissions.push ((env.getModuleFor? n).getD `«unknown», n, #[a])
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

  ---------------------------------------------------------------------------
  -- LAUNDERING
  ---------------------------------------------------------------------------
  let mut findings : Array Laundering.Finding := #[]
  let mut lScanned := 0
  let mut premises := 0
  -- structure name -> (Prop fields, is inhabited); computed once, not per use site
  let mut certCache : Std.HashMap Name (Array Name × Bool) := {}

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
            -- TAUTOLOGY: this premise IS the conclusion.
            if ← isDefEq ty concl then
              fs := fs.push ⟨"LAUNDER_TAUTOLOGY", true, mod, name,
                s!"premise `{nm}` is the conclusion; this proves P → P"⟩
            else
              let kind := match bi with
                | .instImplicit => "instance"
                | .implicit => "implicit"
                | .strictImplicit => "strict-implicit"
                | .default => "explicit"
              fs := fs.push ⟨"LAUNDER_PREMISE", false, mod, name,
                s!"{kind} premise `{nm} : {← ppExpr ty}`"⟩
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
              else if (getStructureInfo? env h).isSome then
                let entry ← match cache[h]? with
                  | some e => pure e
                  | none => do
                      let flds ← Laundering.certificateFields env h
                      let wit ← Laundering.hasWitness env h
                      let e := (flds, wit)
                      cache := cache.insert h e
                      pure e
                let (flds, wit) := entry
                if !flds.isEmpty && !wit then
                  fs := fs.push ⟨"LAUNDER_CERT", true, mod, name,
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
        findings := findings.push ⟨"LAUNDER_PROJECTION", true, mod, name,
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
