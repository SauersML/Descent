/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Core.GroupoidBisection
import Descent.Core.PermExtension
import Descent.Layer

assert_below Descent.Meta Descent.Foundations Descent.Coalescent Descent.Pangenome Descent.PopGen
assert_below Descent.Spectral Descent.Blindness Descent.Conditionals Descent.Portability
assert_below Descent.Decision Descent.Program

/-!
# Completing partial bisections of finite groupoids

A partial bisection selects some source objects, equally many target objects, and one
arrow from each selected source to its selected target. It is a matching of part of a
groupoid's object set, carrying a reason -- an arrow -- for each match it makes.

The theorem is that a partial matching is always the restriction of a total one:
`PartialBisection.complete` extends any partial bisection to a `Bisection`. Two facts
make it work. Each selected arrow stays inside one connected component, so the
selected sources and the selected targets have equal counts SEPARATELY in every
component; extending a pair of injections to a permutation therefore succeeds
componentwise. And on the objects the completion invents, connectedness supplies an
arrow, because the completed object map never leaves the component it started in.

This is the sense in which the library is about PARTIAL symmetry: the object it
studies is a symmetry defined on part of a structure, and the question is what it
takes to finish one. For a family of homologous genomic copies, a partial bisection is
a homology assignment that covers only some copies -- the ones whose alignment is
unambiguous -- and completion says the ambiguous remainder can always be filled in,
though never uniquely, and only within a connected component.
-/

namespace Descent.Core
namespace FiniteGroupoid

open CategoryTheory

universe u v

variable {C : Type u} [Groupoid.{v} C] [Fintype C]

/-- Connectedness of objects in a groupoid: two objects are related when an arrow
joins them, which is an equivalence because the groupoid has identities, inverses,
and composition. -/
def connectedSetoid (C : Type u) [Groupoid.{v} C] : Setoid C where
  r X Y := Nonempty (X ⟶ Y)
  iseqv := ⟨fun X ↦ ⟨𝟙 X⟩,
    fun ⟨f⟩ ↦ ⟨inv f⟩,
    fun ⟨f⟩ ⟨g⟩ ↦ ⟨f ≫ g⟩⟩

/-- A bisection defined on only a finite set of source objects. -/
structure PartialBisection (C : Type u) [Groupoid.{v} C] where
  /-- The selected source objects. -/
  source : Finset C
  /-- The selected target objects. -/
  target : Finset C
  /-- The matching of selected sources with selected targets. -/
  objEquiv : ↑source ≃ ↑target
  /-- The arrow realizing each match. -/
  hom : ∀ X : ↑source, X.1 ⟶ (objEquiv X).1

/-- **The partial bisection is inhabited.** A theorem quantified over an uninhabited
structure is true and empty, and the completion theorem below is quantified over this
one. The empty matching selects no object and so owes no arrow; completing it is the
statement that some permutation of the objects exists, which is the weakest true case
of the theorem rather than a degenerate exception to it.

    Empirical status: NOT AN EMPIRICAL CLAIM -- this is a SHAPE, not a quantity.
    A matching of objects asserts nothing about a population, so no measurement can
    bear on it. -/
def PartialBisection.empty : PartialBisection C where
  source := (∅ : Finset C)
  target := (∅ : Finset C)
  objEquiv := Equiv.refl _
  hom X := absurd X.2 (Finset.notMem_empty _)

namespace PartialBisection

variable (a : PartialBisection C)

/-- The set of connected components. -/
private abbrev Component := Quotient (connectedSetoid C)

/-- The component an object lies in. -/
private abbrev componentMap : C → Component (C := C) :=
  Quotient.mk (connectedSetoid C)

/-- The objects lying in one component. -/
private abbrev ComponentFiber (q : Component (C := C)) :=
  {X : C // componentMap (C := C) X = q}

/-- The selected source objects lying in one component. -/
private abbrev SourceFiber (q : Component (C := C)) :=
  {X : ↑a.source // componentMap (C := C) X.1 = q}

/-- The selected source objects in one connected component, included into
that component's full object fiber. -/
private def sourceFiberInclusion (q : Component (C := C)) :
    SourceFiber a q → ComponentFiber (C := C) q :=
  fun X ↦ ⟨X.1.1, X.2⟩

/-- The selected targets of source objects in one component. The partial
bisection arrow proves that the target remains in the same component.

REPAIR ON EXTRACTION: the source rewrote by `X.2` backwards, which asks for a motive
that does not typecheck because `X`'s own type mentions the term being abstracted.
Naming the component equality and rewriting forwards says the same thing. -/
private def sourceFiberTarget (q : Component (C := C)) :
    SourceFiber a q → ComponentFiber (C := C) q := fun X ↦ by
  refine ⟨(a.objEquiv X.1).1, ?_⟩
  have h : componentMap (C := C) (a.objEquiv X.1).1 =
      componentMap (C := C) X.1.1 :=
    Quotient.sound ⟨CategoryTheory.inv (a.hom X.1)⟩
  rw [h]
  exact X.2

omit [Fintype C] in
/-- REPAIR ON EXTRACTION: `congrArg Subtype.val` left the subtype ambiguous and
unified it at the wrong level; the projection is written out here. -/
private theorem sourceFiberInclusion_injective (q : Component (C := C)) :
    Function.Injective (sourceFiberInclusion a q) := by
  intro X Y hXY
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg (fun z : ComponentFiber (C := C) q ↦ z.1) hXY

omit [Fintype C] in
/-- REPAIR ON EXTRACTION: as for `sourceFiberInclusion_injective`. -/
private theorem sourceFiberTarget_injective (q : Component (C := C)) :
    Function.Injective (sourceFiberTarget a q) := by
  intro X Y hXY
  apply Subtype.ext
  apply a.objEquiv.injective
  apply Subtype.ext
  exact congrArg (fun z : ComponentFiber (C := C) q ↦ z.1) hXY

/-- Complete the selected object matching separately inside one connected
component. -/
private noncomputable def fiberCompletion (q : Component (C := C)) :
    Equiv.Perm (ComponentFiber (C := C) q) :=
  Classical.choose (perm_exists_extending_pair
    (sourceFiberInclusion a q) (sourceFiberTarget a q)
    (sourceFiberInclusion_injective a q) (sourceFiberTarget_injective a q))

private theorem fiberCompletion_spec (q : Component (C := C))
    (X : SourceFiber a q) :
    fiberCompletion a q (sourceFiberInclusion a q X) =
      sourceFiberTarget a q X :=
  Classical.choose_spec (perm_exists_extending_pair
    (sourceFiberInclusion a q) (sourceFiberTarget a q)
    (sourceFiberInclusion_injective a q) (sourceFiberTarget_injective a q)) X

/-- The global object permutation obtained by completing independently in
each connected component. -/
noncomputable def completionObjEquiv : C ≃ C :=
  (Equiv.sigmaFiberEquiv (componentMap (C := C))).symm |>.trans
    ((Equiv.sigmaCongrRight fun q ↦ fiberCompletion a q).trans
      (Equiv.sigmaFiberEquiv (componentMap (C := C))))

/-- Completion never leaves the component it started in.

REPAIR ON EXTRACTION: the source closed this by `rfl`. It is not definitional --
the component is preserved because the completed point is drawn from the fibre, which
is a propositional fact carried by that point's own subtype proof, and that proof is
what discharges it. -/
theorem completionObjEquiv_component (X : C) :
    componentMap (C := C) (a.completionObjEquiv X) =
      componentMap (C := C) X :=
  (fiberCompletion a (componentMap (C := C) X) ⟨X, rfl⟩).2

/-- Completion agrees with the prescribed partial object map. -/
theorem completionObjEquiv_apply_of_mem (X : C) (hX : X ∈ a.source) :
    a.completionObjEquiv X = a.objEquiv ⟨X, hX⟩ := by
  let q := componentMap (C := C) X
  let x : SourceFiber a q := ⟨⟨X, hX⟩, rfl⟩
  have hx := fiberCompletion_spec a q x
  exact congrArg Subtype.val hx

/-- **Every partial bisection of a finite groupoid extends to a total bisection.**
On unselected objects, an arrow exists because the completed object permutation stays
in the same connected component. -/
noncomputable def complete : Bisection C where
  objEquiv := a.completionObjEquiv
  hom X := by
    by_cases hX : X ∈ a.source
    · exact a.hom ⟨X, hX⟩ ≫
        eqToHom (a.completionObjEquiv_apply_of_mem X hX).symm
    · have hconnected : Nonempty (X ⟶ a.completionObjEquiv X) :=
        Quotient.exact (a.completionObjEquiv_component X).symm
      exact Classical.choice hconnected

/-- On the selected source, completion changes only the definitional target
identification forced by the extended object permutation. -/
theorem complete_hom_of_mem (X : C) (hX : X ∈ a.source) :
    (a.complete).hom X = a.hom ⟨X, hX⟩ ≫
      eqToHom (a.completionObjEquiv_apply_of_mem X hX).symm := by
  simp only [complete, hX, dite_true]

end PartialBisection

/-! ## What was left behind

The source module continued with `finsetImageEquiv` and two
`partialPullbackBisectionOfCardinalPreserving` definitions. They are not extracted,
for reasons that are not stylistic:

* `finsetImageEquiv` destructures an `∃` to build the data of an `Equiv`, which
  eliminates a `Prop` into `Type` and is rejected.
* the pullbacks pass `horbit X hX`, a single orbit-cardinality equation, to
  `nonempty_hom_of_map_nonempty`, whose corresponding argument is `∀ X, ...`; and they
  destructure `Nonempty` to produce data. Both are type errors, and repairing the
  first means weakening a hypothesis of `FiniteGroupoidCounting`.

None of this is partial-symmetry mathematics -- it is the bookkeeping of the
compressor argument the source repo was building, and it belongs with that argument.
The completion theorem above is the part that is about partial bisections, and it
stands on its own.

## Provenance

Extracted from github.com/SauersML/nonsofic_existence (Apache 2.0, same
owner). Original path: `NonsoficGroupsExist/Matching/FiniteGroupoidPartialBisection.lean`,
the completion half only. The namespace is renamed `Descent.Core` and the imports
repointed; the repairs are noted at the declarations they apply to.

The source repo holds no olean for this module, so none of its defects had been
caught there. Two declarations that followed the completion theorem --
`finsetImageEquiv` and the two cardinal-preserving partial pullbacks -- are NOT
extracted: see the note at the end of this file.
-/

end FiniteGroupoid
end Descent.Core
