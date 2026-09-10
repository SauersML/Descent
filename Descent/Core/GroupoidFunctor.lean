/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Core.GroupoidPresentation
import Descent.Layer

assert_below Descent.Meta Descent.Foundations Descent.Coalescent Descent.Pangenome Descent.PopGen
assert_below Descent.Spectral Descent.Blindness Descent.Conditionals Descent.Portability
assert_below Descent.Decision Descent.Program

/-!
# Functors between groupoids given by finite representative systems

The compressor argument first defines its action on finite partial-bijection
representatives and proves the required identities only modulo the cluster
relations.  This file is the quotient-safe interface turning exactly those
finite statements into an honest functor, and a relation-reflection statement
into categorical faithfulness.
-/

namespace Descent.Core

open CategoryTheory

universe u v w

namespace GroupoidPresentation

variable {I : Type u} {J : Type v}

/-- Representative-level data sufficient to descend a functor through two
groupoid presentations. -/
structure FunctorData (P : GroupoidPresentation I)
    (Q : GroupoidPresentation J) where
  obj : I → J
  map : ∀ {X Y}, P.Rep X Y → Q.Rep (obj X) (obj Y)
  map_respects : ∀ {X Y} {f g : P.Rep X Y},
    P.rel X Y f g → Q.rel (obj X) (obj Y) (map f) (map g)
  map_one : ∀ X, Q.rel (obj X) (obj X) (map (P.one X)) (Q.one (obj X))
  map_comp : ∀ {X Y Z} (f : P.Rep X Y) (g : P.Rep Y Z),
    Q.rel (obj X) (obj Z) (map (P.comp f g)) (Q.comp (map f) (map g))

variable {P : GroupoidPresentation I} {Q : GroupoidPresentation J}

/-- Descend representative-level functor data to the quotient groupoids.

REPAIR ON EXTRACTION. The source wrote the result type as `P.Obj ⟶ Q.Obj`, a quiver
arrow, where the fields supplied below (`obj`, `map`, `map_id`, `map_comp`) are exactly
the fields of a functor. `⟶` between two objects of `Type u` is the function type, which
has no `obj` field, so the declaration could not elaborate; the source repo has no olean
for this module, which is the same finding from the other side. `⥤` is the intended
arrow and the only one under which the body type-checks. -/
def FunctorData.toFunctor (data : FunctorData P Q) : P.Obj ⥤ Q.Obj where
  obj X := ⟨data.obj X.val⟩
  map {X Y} f := Quotient.map data.map (fun _ _ h ↦ data.map_respects h) f
  map_id X := by
    exact Quotient.sound (data.map_one X.val)
  map_comp {X Y Z} f g := by
    induction f using Quotient.inductionOn with
    | _ f =>
      induction g using Quotient.inductionOn with
      | _ g => exact Quotient.sound (data.map_comp f g)

@[simp] theorem FunctorData.toFunctor_obj_val (data : FunctorData P Q)
    (X : P.Obj) : (data.toFunctor.obj X).val = data.obj X.val := rfl

theorem FunctorData.toFunctor_map_ofRep (data : FunctorData P Q)
    {X Y : P.Obj} (f : P.Rep X.val Y.val) :
    data.toFunctor.map (P.ofRep f) = Q.ofRep (data.map f) := rfl

/-- If the representative map reflects the cluster relation, the descended
functor is faithful. 
## Provenance

Extracted from github.com/SauersML/nonsofic_existence (Apache 2.0, same
owner). Original path: `NonsoficGroupsExist/Matching/FiniteGroupoidFunctor.lean`.
The namespace `NonsoficGroupsExist` is renamed `Descent.Core` and the
imports repointed; the mathematics is unchanged except where a repair is
noted at the declaration it applies to.
-/
def FunctorData.faithful (data : FunctorData P Q)
    (hreflects : ∀ {X Y} {f g : P.Rep X Y},
      Q.rel (data.obj X) (data.obj Y) (data.map f) (data.map g) →
        P.rel X Y f g) : data.toFunctor.Faithful where
  map_injective := by
    intro X Y f g hfg
    induction f using Quotient.inductionOn with
    | _ f =>
      induction g using Quotient.inductionOn with
      | _ g =>
        apply Quotient.sound
        apply hreflects
        exact Quotient.exact hfg

/-- **The functor data is inhabited.** A theorem quantified over an uninhabited
structure is true and empty, and every statement above is quantified over this one.
The identity descent -- send each object and each representative to itself -- satisfies
all four laws by reflexivity of the presentation's own setoids.

    Empirical status: NOT AN EMPIRICAL CLAIM -- this is a SHAPE, not a quantity.
    A descent of functor data asserts nothing about a population, so no measurement
    can bear on it. -/
def FunctorData.id : FunctorData P P where
  obj X := X
  map f := f
  map_respects h := h
  map_one X := (P.rel X X).iseqv.refl (P.one X)
  map_comp f g := (P.rel _ _).iseqv.refl (P.comp f g)

end GroupoidPresentation
end Descent.Core
