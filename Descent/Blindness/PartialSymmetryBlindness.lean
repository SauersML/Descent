/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Blindness.ObservationalCeiling
import Descent.Core.PartialBijection

assert_below Descent.Conditionals Descent.Portability Descent.Decision Descent.Program

namespace Descent.Blindness

open Descent.Core

/-!
# Symmetries defined only where the correspondence is

`ObservationalSymmetry` demands that the observation be unmoved at EVERY parameter, and that
is the right demand when the transformation is total: it is what makes the invariance a law
about the observation rather than a coincidence at the witness. Some transformations are not
total. Two pangenome builds agree on a core and diverge on an accessory; a rewrite matches
some storage nodes and leaves others unmatched; a correspondence is a partial bijection with
a source and a target rather than a function. Demanding invariance off the correspondence
asks for something the transformation does not claim.

`PartialObservationalSymmetry` is the domain-restricted variant. It carries a `domain`, the
invariance is quantified over it, and the moved witness is required to lie in it. Everything
downstream is unchanged, because the blindness argument only ever evaluates the observation
at the witness and its image: `toProbeBlindness` and `no_target_criterion` read exactly as
they do for the total structure.

## The Core-side half

`AgreesOnSource` is the equality this variant needs from `Descent.Core.FinitePartialBijection`:
every point the bridge matches is reported identically on both sides. It is an EQUALITY, not
a bound, and deliberately — `ProbeBlindness.no_criterion_of_factors` turns on functions
respecting equality, and the bounded case is a different theorem with a stability hypothesis
on the criterion (`ApproxProbeBlindness.no_stable_criterion`). The disagreement bounds in
`Descent.Core.PartialBijectionSandwich` are the quantitative neighbours of this predicate;
this is their zero case, which is the case an exact impossibility needs.

`partialObservationalSymmetry_of_agreesOnSource` is the join: a partial self-correspondence
that agrees with an observation on its source, and moves a target somewhere on that source,
is a partial observational symmetry — so the impossibility follows without a new argument.

## What is not claimed

Nothing here says a partial correspondence is a symmetry of anything in particular. It says
what a partial correspondence must satisfy to be one, and supplies the two witnesses that
make the predicates non-vacuous. Which pangenome rewrites satisfy it is an empirical question
about a graph builder, and the corpus's answer for the total case is
`Descent.Blindness.PangenomeCovariance`.
-/

/-- A **partial observational symmetry**: a transformation the observation cannot see WHERE
IT IS DEFINED, together with a parameter in that domain whose target it moves. -/
structure PartialObservationalSymmetry {Parameter Data Target : Type*}
    (observe : Parameter → Data) (target : Parameter → Target) where
  /-- Where the transformation claims to act. -/
  domain : Parameter → Prop
  /-- The transformation the observation cannot see on that domain. -/
  transform : Parameter → Parameter
  /-- Every parameter in the domain is reported identically to its image. -/
  observation_invariant : ∀ parameter, domain parameter →
    observe (transform parameter) = observe parameter
  /-- A parameter at which the transformation changes the answer. -/
  moved : Parameter
  /-- It lies in the domain, so the invariance applies to it. -/
  moved_mem : domain moved
  /-- It does change the answer there. -/
  target_moved : target (transform moved) ≠ target moved

/-- **The class is inhabited.**  A theorem quantified over an uninhabited structure says
nothing, so the corpus constructs one.  The witness is chosen to be genuinely partial rather
than a total symmetry in disguise: its transformation is claimed only at `false`, which is
exactly where the target moves. -/
def PartialObservationalSymmetry.witness :
    PartialObservationalSymmetry (fun _flag : Bool ↦ ()) (id : Bool → Bool) where
  domain := fun flag ↦ flag = false
  transform := fun _flag ↦ true
  observation_invariant := fun _flag _hdomain ↦ rfl
  moved := false
  moved_mem := rfl
  target_moved := by decide

namespace PartialObservationalSymmetry

variable {Parameter Data Target : Type*} {observe : Parameter → Data}
  {target : Parameter → Target}

/-- **A partial symmetry is still a blindness witness.** The argument never evaluates the
observation off the domain, so restricting it costs nothing. -/
def toProbeBlindness (S : PartialObservationalSymmetry observe target) (P : Parameter → Prop)
    (hpositive : P (S.transform S.moved)) (hnegative : ¬ P S.moved) :
    ProbeBlindness observe P where
  positive := S.transform S.moved
  negative := S.moved
  same_data := S.observation_invariant S.moved S.moved_mem
  holds := hpositive
  fails := hnegative

/-- The canonical instance, as in the total case: the property *"the target takes the value it
takes after the transformation"* is flipped by construction. -/
def targetBlindness (S : PartialObservationalSymmetry observe target) :
    ProbeBlindness observe (fun parameter ↦ target parameter = target (S.transform S.moved)) :=
  S.toProbeBlindness _ rfl (fun hmoved ↦ S.target_moved hmoved.symm)

/-- **No criterion built from the observation reads the target.** -/
theorem no_target_criterion (S : PartialObservationalSymmetry observe target) :
    ¬ ∃ decide : Data → Prop, ∀ parameter : Parameter,
      target parameter = target (S.transform S.moved) ↔ decide (observe parameter) :=
  S.targetBlindness.no_criterion

end PartialObservationalSymmetry

/-- **Every total symmetry is a partial one**, on the whole parameter space. This is why the
total development needs no restating against the variant: it is the special case
`domain = fun _ ↦ True`, and every theorem above applies to it unchanged. -/
def ObservationalSymmetry.toPartial {Parameter Data Target : Type*}
    {observe : Parameter → Data} {target : Parameter → Target}
    (S : ObservationalSymmetry observe target) :
    PartialObservationalSymmetry observe target where
  domain := fun _parameter ↦ True
  transform := S.transform
  observation_invariant := fun parameter _hdomain ↦ S.observation_invariant parameter
  moved := S.moved
  moved_mem := trivial
  target_moved := S.target_moved

/-- **A bridge agrees on its source** with a pair of readouts when every point it matches is
reported identically on both sides. This is the exact equality a partial symmetry needs, and
the zero case of the disagreement bounds in `Descent.Core.PartialBijectionSandwich`. -/
def AgreesOnSource {Y Z : FiniteModel} {Value : Type*}
    (bridge : FinitePartialBijection Y Z) (readSource : Y → Value) (readTarget : Z → Value) :
    Prop :=
  ∀ y : Y, ∀ hy : y ∈ bridge.source, readTarget (bridge.apply y hy) = readSource y

/-- **The predicate is inhabited**, and by the reading that says what it means: a readout
carrying no information is agreed on by every bridge, so agreement is a constraint on the
readouts and not a property some bridges happen to have. -/
theorem agreesOnSource_const {Y Z : FiniteModel} {Value : Type*}
    (bridge : FinitePartialBijection Y Z) (value : Value) :
    AgreesOnSource bridge (fun _y ↦ value) (fun _z ↦ value) :=
  fun _y _hy ↦ rfl

/-- **A self-correspondence agreeing with an observation on its source is a partial
observational symmetry.** The transformation moves a matched point along the bridge and fixes
everything unmatched, so its invariance is exactly `AgreesOnSource` and its domain is exactly
the bridge's source.

Assumes: `AgreesOnSource bridge observe observe`, i.e. the bridge is a symmetry OF the
observation on the part of the model it matches. -/
noncomputable def partialObservationalSymmetry_of_agreesOnSource
    {Y : FiniteModel} {Data Target : Type*}
    (bridge : FinitePartialBijection Y Y) (observe : Y → Data) (target : Y → Target)
    (hagrees : AgreesOnSource bridge observe observe)
    (moved : Y) (hmoved : moved ∈ bridge.source)
    (hmovedTarget : target (bridge.apply moved hmoved) ≠ target moved) :
    PartialObservationalSymmetry observe target where
  domain := fun point ↦ point ∈ bridge.source
  transform := fun point ↦
    if hpoint : point ∈ bridge.source then bridge.apply point hpoint else point
  observation_invariant := by
    intro point hpoint
    rw [dif_pos hpoint]
    exact hagrees point hpoint
  moved := moved
  moved_mem := hmoved
  target_moved := by
    rw [dif_pos hmoved]
    exact hmovedTarget

/-- **The impossibility, for a partial correspondence.** No criterion reading an observation
that a bridge preserves on its source decides a target the bridge moves there. -/
theorem no_criterion_of_agreesOnSource
    {Y : FiniteModel} {Data Target : Type*}
    (bridge : FinitePartialBijection Y Y) (observe : Y → Data) (target : Y → Target)
    (hagrees : AgreesOnSource bridge observe observe)
    (moved : Y) (hmoved : moved ∈ bridge.source)
    (hmovedTarget : target (bridge.apply moved hmoved) ≠ target moved) :
    ¬ IdentifiedBy observe target := by
  intro hidentified
  exact hmovedTarget (hidentified (bridge.apply moved hmoved) moved (hagrees moved hmoved))

end Descent.Blindness
