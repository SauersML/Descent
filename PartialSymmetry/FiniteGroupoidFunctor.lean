/-
Released under Apache 2.0 license as described in the file LICENSE.

Extracted from github.com/SauersML/nonsofic_existence (Apache 2.0, same
owner). Original path: `NonsoficGroupsExist/Matching/FiniteGroupoidFunctor.lean`.
The namespace `NonsoficGroupsExist` is renamed `PartialSymmetry` and the
imports repointed; the mathematics is unchanged except where a repair is
noted at the declaration it applies to.
-/
import PartialSymmetry.FiniteGroupoidPresentation

/-!
# Functors between groupoids given by finite representative systems

The compressor argument first defines its action on finite partial-bijection
representatives and proves the required identities only modulo the cluster
relations.  This file is the quotient-safe interface turning exactly those
finite statements into an honest functor, and a relation-reflection statement
into categorical faithfulness.
-/

namespace PartialSymmetry

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
def FunctorData.toFunctor (D : FunctorData P Q) : P.Obj ⥤ Q.Obj where
  obj X := ⟨D.obj X.val⟩
  map {X Y} f := Quotient.map D.map (fun _ _ h ↦ D.map_respects h) f
  map_id X := by
    exact Quotient.sound (D.map_one X.val)
  map_comp {X Y Z} f g := by
    induction f using Quotient.inductionOn with
    | _ f =>
      induction g using Quotient.inductionOn with
      | _ g => exact Quotient.sound (D.map_comp f g)

@[simp] theorem FunctorData.toFunctor_obj_val (D : FunctorData P Q)
    (X : P.Obj) : (D.toFunctor.obj X).val = D.obj X.val := rfl

theorem FunctorData.toFunctor_map_ofRep (D : FunctorData P Q)
    {X Y : P.Obj} (f : P.Rep X.val Y.val) :
    D.toFunctor.map (P.ofRep f) = Q.ofRep (D.map f) := rfl

/-- If the representative map reflects the cluster relation, the descended
functor is faithful. -/
def FunctorData.faithful (D : FunctorData P Q)
    (hreflects : ∀ {X Y} {f g : P.Rep X Y},
      Q.rel (D.obj X) (D.obj Y) (D.map f) (D.map g) →
        P.rel X Y f g) : D.toFunctor.Faithful where
  map_injective := by
    intro X Y f g hfg
    induction f using Quotient.inductionOn with
    | _ f =>
      induction g using Quotient.inductionOn with
      | _ g =>
        apply Quotient.sound
        apply hreflects
        exact Quotient.exact hfg

end GroupoidPresentation
end PartialSymmetry
