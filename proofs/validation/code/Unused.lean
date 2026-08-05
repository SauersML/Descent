/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Calibrator
import Lean
import Shared.DeclFilter

/-!
# Unused-hypothesis scan, over the kernel-accepted proof terms

A hypothesis that no proof term mentions is a hypothesis the theorem does not
need.  Carrying it does not make the theorem false -- it makes it *weaker* than
it reads, and it misrepresents what the result depends on.  Three kinds of
misrepresentation showed up the first time this ran:

  * a modelling premise nobody uses.  Three of `Calibrator.FoldedSpectrum`'s
    identifiability results took an `InLinkageEquilibrium` premise, and a joint
    genotype distribution as a parameter purely to state it, while the proofs
    are functions of the panel's frequencies and weights alone.  A reader of the
    signature would conclude the result is scoped to equilibrium panels.  It is
    not scoped at all.
  * an instance binder narrower than the upstream lemma.  `integrable_prod_mul`
    was `Integrable.mul_prod` with two unused `SigmaFinite` instances attached;
    their being dead is exactly the evidence that the corpus copy was strictly
    less general than the Mathlib original it duplicated.
  * a conclusion that is one of its own hypotheses in heavier notation.  Five
    dead premises on `am_ld_breaks_cross_population` were the tell: once the
    shared term cancels, the inequality *is* the premise `r_t < r_s`.

Run, after a successful build of `Calibrator` and `ValidationShared`:

    lake env lean proofs/validation/code/Unused.lean

## What it does, and why it needs no rebuild

For each user-written `Calibrator` theorem it walks two telescopes in parallel:
the raw `forallE` chain of the TYPE and the `lam` chain of the VALUE.  A binder
at position `i` is reported when its de Bruijn variable occurs in NEITHER the
rest of the type nor the rest of the proof term.  Occurrence-freedom in a
kernel-accepted term is a proof that the argument is deletable, so this replaces
a per-hypothesis mutate-and-rebuild loop -- one 25-second pass over the built
environment answers the question for the whole corpus at once, and it cannot be
fooled by a tactic block that merely mentions a name it does not use.

## Calibration, and the direction of its error

Plant these four declarations in a `Calibrator` module and rerun:

    theorem zz_used       (n : Nat) (h : 0 < n) : n ≠ 0     := Nat.pos_iff_ne_zero.mp h
    theorem zz_unused     (n : Nat) (h : 0 < n) : 0 < n + 1 := Nat.succ_pos n
    theorem zz_used_tac   (n : Nat) (h : 2 < n) : 1 < n     := by omega
    theorem zz_unused_tac (n : Nat) (h : 2 < n) : 0 < n + 1 := by omega

The scan must report `zz_unused` and must stay silent on `zz_used` and
`zz_used_tac`.  It also stays silent on `zz_unused_tac`, and that miss is the
instrument's one known blind spot: `omega`, `linarith` and `simp_all` splice
every hypothesis in scope into the certificate they emit, so a hypothesis they
did not need still occurs in the term.  **`UNUSED_PROP` is therefore a lower
bound**, and a theorem's absence from the report is not evidence its hypotheses
are live.  There is no false-positive direction: a reported binder is provably
deletable.
-/

open Lean Elab Command Meta

namespace Unused

/-- Guard string.  Printed as `GUARD` so a run can prove it came from this
source rather than from a stale olean. -/
def guard : String := "MUTGUARD-A2"

/-- Is `n` declared in a `Calibrator` module?  `getRoot`, as in `Check.isOurs`. -/
def isOurs (n : Name) : Bool := n.getRoot == `Calibrator

/-- Positions of `forallE` binders whose bound variable does not occur in the
rest of the TYPE.  Index 0 is the outermost binder. -/
partial def typeUnused (e : Expr) (i : Nat := 0)
    (acc : Array (Nat × Name) := #[]) : Array (Nat × Name) :=
  match e with
  | .forallE n _ b _ =>
      typeUnused b (i + 1) (if b.hasLooseBVar 0 then acc else acc.push (i, n))
  | _ => acc

/-- Positions of `lam` binders whose bound variable does not occur in the rest
of the proof TERM, together with how many binders the term abstracts.

The count matters: a term may be eta-short of its type's telescope, and a binder
the term never abstracts is passed on to whatever the term reduces to rather
than discarded.  Positions at or beyond the count are not reported. -/
partial def valUnused (e : Expr) (i : Nat := 0)
    (acc : Array (Nat × Name) := #[]) : (Array (Nat × Name) × Nat) :=
  match e with
  | .lam n _ b _ =>
      valUnused b (i + 1) (if b.hasLooseBVar 0 then acc else acc.push (i, n))
  | _ => (acc, i)

end Unused

open Unused in
run_cmd liftTermElabM do
  let env ← getEnv
  IO.println s!"GUARD\t{Unused.guard}"
  let mut scanned := 0
  let mut totalProp := 0
  let mut unusedProp := 0
  let mut rows : Array String := #[]
  for (name, ci) in env.constants.toList do
    unless Unused.isOurs name do continue
    unless ci.isTheorem do continue
    unless Shared.userWritten env name do continue
    let some val := ci.value? | continue
    scanned := scanned + 1
    let mod := (env.getModuleFor? name).getD `«unknown»
    let tSet := (Unused.typeUnused ci.type).map (·.1)
    let (vU, nLam) := Unused.valUnused val
    let vSet := vU.map (·.1)
    -- Binder types come from a proper telescope: the raw `forallE` domains
    -- carry loose bound variables and cannot be pretty-printed.
    let info ← forallTelescope ci.type fun args _ ↦ args.mapM fun a ↦ do
      let ty ← inferType a
      pure ((← ppExpr ty).pretty, ← isProp ty, ← a.fvarId!.getUserName)
    let mut props := 0
    for h : i in [0:info.size] do
      let (tyStr, isP, bn) := info[i]
      if isP then
        props := props + 1
        if tSet.contains i && vSet.contains i && i < nLam then
          unusedProp := unusedProp + 1
          rows := rows.push s!"UNUSED\t{mod}\t{name}\t{bn}\t{tyStr}"
    totalProp := totalProp + props
  for r in rows do IO.println r
  IO.println s!"SCANNED\t{scanned}"
  IO.println s!"PROP_BINDERS\t{totalProp}"
  IO.println s!"UNUSED_PROP\t{unusedProp}"
