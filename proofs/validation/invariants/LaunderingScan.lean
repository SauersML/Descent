/-
Report, for every user-authored `Calibrator` declaration, the premises the KERNEL sees,
and fail on the ones that make a theorem's name a claim its type does not support.

The patterns below all have a CLEAN axiom report, which is why `AxiomScan.lean` cannot
see them: none is a trust bypass.  They are valid proofs of a weaker, conditional,
vacuous, or circular statement, checked correctly and then advertised under the intended
theorem's name.  `theorem P_from_P (h : P) : P := h` has a clean `#print axioms`.

This is the elaborated-telescope half of the guard.  `scripts/check-laundering.py` is the
source-text half, and four things only this half can see:

  * a premise from an `export`ed or `open`ed instance, which appears in no binder;
  * the `variable` binders Lean actually inserted -- it includes a section variable only
    when the declaration mentions it, so the source line over-reports;
  * a definition that unfolds to something other than its written form;
  * whether a structure parameter's type is inhabited, which needs a search for a term of
    that type rather than a name lookup.

Run, after a successful build of `Calibrator`:

    lake env lean proofs/validation/invariants/LaunderingScan.lean

Exit is nonzero when any FATAL finding survives.

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

A `sorry` is preferred to every one of these.  `sorryAx` is visible to `AxiomScan.lean`;
a laundered premise is visible to neither guard nor reader.
-/
import Calibrator
import Lean.Util.CollectAxioms

open Lean Elab Command Meta

namespace LaunderingScan

/-- Classes that are ordinary mathematical structure rather than smuggled content.
A theorem about a normed space is not assuming a normed space exists; it is naming the
category it is stated in.  A theorem carrying `[Fact (p < 1)]` is assuming `p < 1`. -/
def assumptionClasses : List Name :=
  [``Fact, ``Nonempty, ``Inhabited]

/-- The same generated-declaration filter `AxiomScan.lean` uses, and for the same
reason: recursors, projections and equation lemmas are elaborated from user-authored
roots, so scanning them separately reports the same premises many times over. -/
def isGeneratedEquation (f : String) : Bool :=
  f == "eq_def" ||
  (["eq_", "match_", "proof_"].any f.startsWith &&
    (f.dropWhile (· != '_') |>.drop 1 |>.all Char.isDigit) &&
    f.any Char.isDigit)

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

/-- Whether an expression is a proposition in the current local context. -/
def isPropType (e : Expr) : MetaM Bool := do
  isProp e

/-- The head constant of a type, if it has one. -/
def headConst? (e : Expr) : Option Name :=
  e.getAppFn.constName?

/-- A structure declared in this corpus whose fields include at least one Prop.
Such a parameter is a CERTIFICATE: the caller hands over finished mathematics. -/
def certificateFields (env : Environment) (S : Name) : MetaM (Array Name) := do
  let some info := getStructureInfo? env S | return #[]
  let mut out := #[]
  for f in info.fieldNames do
    let some proj := env.find? (S ++ f) | continue
    let ty ← forallTelescopeReducing proj.type fun _ b => pure b
    if ← isProp ty then out := out.push f
  return out

/-- Is there a closed term of type `S ..` anywhere in the environment -- that is, does
the corpus CONSTRUCT one of these, or only consume them?

A witness may take data parameters and may not take Prop-valued ones: a family of
models indexed by a frequency inhabits the class, while a "witness" that first demands
the hard theorem inhabits nothing and merely relocates the obligation. -/
def hasWitness (env : Environment) (S : Name) : MetaM Bool := do
  for (n, ci) in env.constants.toList do
    unless (`Calibrator).isPrefixOf n do continue
    unless ci.isDefinition || ci.isCtor || ci.isTheorem do continue
    if n.isInternalDetail then continue
    let ok ← forallTelescopeReducing ci.type fun args body => do
      -- Either a term of `S ..`, or a proof of `Nonempty (S ..)`.  A theorem witnesses
      -- a Prop-valued structure; a `Nonempty` proof witnesses a data one.
      let body := match body.getAppFn.constName? with
        | some ``Nonempty => (body.getAppArgs[0]?).getD body
        | _ => body
      if headConst? body != some S then return false
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

end LaunderingScan

open LaunderingScan in
run_cmd do
  let env ← getEnv
  let mut findings : Array Finding := #[]
  let mut scanned := 0
  let mut premises := 0
  -- structure name -> (has a Prop field, is inhabited); computed once, not per use site
  let mut certCache : Std.HashMap Name (Array Name × Bool) := {}

  for (name, ci) in env.constants.toList do
    unless (`Calibrator).isPrefixOf name do continue
    unless ci.isTheorem do continue
    unless userWritten env name do continue
    scanned := scanned + 1
    let mod := (env.getModuleFor? name).getD `«unknown»

    let (newFindings, newPremises, cache) ←
      liftTermElabM <| Meta.forallTelescopeReducing ci.type fun args concl => do
        let mut fs : Array Finding := #[]
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
                if assumptionClasses.contains h then
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
                      let flds ← certificateFields env h
                      let wit ← hasWitness env h
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
      if endsInParameter val then
        findings := findings.push ⟨"LAUNDER_PROJECTION", true, mod, name,
          "proof term is an application or projection of a parameter"⟩

  let fatal := findings.filter (·.fatal)
  for f in findings do
    if f.fatal then
      logError m!"{f.tag}\t{f.mod}\t{f.decl}\t{f.detail}"
    else
      logInfo m!"{f.tag}\t{f.mod}\t{f.decl}\t{f.detail}"
  logInfo m!"LAUNDER_SCANNED\t{scanned}"
  logInfo m!"LAUNDER_PREMISES\t{premises}"
  logInfo m!"LAUNDER_FATAL\t{fatal.size}"
  logInfo m!"LAUNDER_TOTAL\t{findings.size}"
