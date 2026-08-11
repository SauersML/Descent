/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.GroupTheory.Perm.Basic
import PartialSymmetry.FiniteGroupoidBisection

/-!
# Bisections of a groupoid form a group

`Bisection C` was extracted with no algebraic structure on it: the source repo used
bisections only as things to transport across a functor, never composed two of them.
The wreath decomposition is a statement about a GROUP of bisections, so the group is
built here.

The composite of `β` after `γ` sends `X` along `γ.hom X` and then along `β.hom` at the
object `γ` landed on. Multiplication is written so that `objEquiv` is a homomorphism to
`Equiv.Perm C`, whose law is `(f * g) x = f (g x)`; hence `β * γ` does `γ` first.

The one technical obstacle is that `hom` has a type depending on `objEquiv` -- an
arrow `X ⟶ objEquiv X` -- so two bisections cannot be compared field by field until
their object permutations are known equal. `Bisection.ext'` is the resulting
extensionality principle: pointwise equality of the permutations, and equality of the
arrows once the target has been transported along it. Every group axiom below is
discharged through it, and for all of them except `inv_mul_cancel` the permutations
agree definitionally, so the transport is the identity.
-/

namespace PartialSymmetry
namespace FiniteGroupoid

open CategoryTheory

universe u v

variable {C : Type u} [Groupoid.{v} C]

namespace Bisection

/-- **Extensionality for bisections.** Two bisections are equal when their object
permutations agree pointwise and their arrows agree after the target identification
that equality forces.

The transport cannot be avoided: `β.hom X` and `γ.hom X` live in the Hom-sets
`X ⟶ β.objEquiv X` and `X ⟶ γ.objEquiv X`, which are not the same type until
`hobj` is known, so there is no statement of the form `β.hom X = γ.hom X` to make. -/
theorem ext' {β γ : Bisection C} (hobj : ∀ X, β.objEquiv X = γ.objEquiv X)
    (hhom : ∀ X, β.hom X ≫ eqToHom (hobj X) = γ.hom X) : β = γ := by
  obtain ⟨e, f⟩ := β
  obtain ⟨e', f'⟩ := γ
  have h : e = e' := Equiv.ext hobj
  subst h
  have hf : f = f' := by
    funext X
    simpa using hhom X
  subst hf
  rfl

/-- The identity bisection: no object moves, and every object is joined to itself by
its identity arrow. -/
instance : One (Bisection C) where
  one := { objEquiv := Equiv.refl C, hom := fun X ↦ 𝟙 X }

@[simp] theorem one_objEquiv : (1 : Bisection C).objEquiv = Equiv.refl C := rfl

@[simp] theorem one_hom (X : C) : (1 : Bisection C).hom X = 𝟙 X := rfl

/-- Composition of bisections: `β * γ` travels along `γ` first and then along `β`,
matching the law `(f * g) x = f (g x)` on `Equiv.Perm C`. -/
instance : Mul (Bisection C) where
  mul β γ :=
    { objEquiv := γ.objEquiv.trans β.objEquiv
      hom := fun X ↦ γ.hom X ≫ β.hom (γ.objEquiv X) }

@[simp] theorem mul_objEquiv (β γ : Bisection C) :
    (β * γ).objEquiv = γ.objEquiv.trans β.objEquiv := rfl

@[simp] theorem mul_hom (β γ : Bisection C) (X : C) :
    (β * γ).hom X = γ.hom X ≫ β.hom (γ.objEquiv X) := rfl

/-- The inverse bisection. Its arrow out of `X` is the groupoid inverse of the arrow
`β` supplies out of the object `β` sent to `X`; the `eqToHom` is the identification
of `X` with `β.objEquiv (β.objEquiv.symm X)` that makes the two composable. -/
noncomputable instance : Inv (Bisection C) where
  inv β :=
    { objEquiv := β.objEquiv.symm
      hom := fun X ↦ eqToHom (β.objEquiv.apply_symm_apply X).symm ≫
        CategoryTheory.inv (β.hom (β.objEquiv.symm X)) }

@[simp] theorem inv_objEquiv (β : Bisection C) : β⁻¹.objEquiv = β.objEquiv.symm := rfl

@[simp] theorem inv_hom (β : Bisection C) (X : C) :
    β⁻¹.hom X = eqToHom (β.objEquiv.apply_symm_apply X).symm ≫
      CategoryTheory.inv (β.hom (β.objEquiv.symm X)) := rfl

/-- Transporting an inverted bisection arrow along an equality of its source is the
same as inverting the arrow at the transported source. This is the one place the
dependent typing of `hom` has to be worked through by hand, and it is what makes
`inv_mul_cancel` come out. -/
theorem eqToHom_inv_hom_eqToHom (β : Bisection C) {W X : C} (h : W = X) :
    eqToHom (congrArg β.objEquiv h).symm ≫
        CategoryTheory.inv (β.hom W) ≫ eqToHom h =
      CategoryTheory.inv (β.hom X) := by
  subst h
  simp

noncomputable instance : Group (Bisection C) where
  mul_assoc β γ δ := ext' (fun _ ↦ rfl) (by intro X; simp)
  one_mul β := ext' (fun _ ↦ rfl) (by intro X; simp)
  mul_one β := ext' (fun _ ↦ rfl) (by intro X; simp)
  inv_mul_cancel β := by
    refine ext' (fun X ↦ β.objEquiv.symm_apply_apply X) ?_
    intro X
    have hW : β.objEquiv.symm (β.objEquiv X) = X := β.objEquiv.symm_apply_apply X
    simp only [mul_hom, inv_hom, inv_objEquiv, one_hom, Category.assoc]
    rw [eqToHom_inv_hom_eqToHom β hW]
    simp

/-- The object permutation of a bisection, as a group homomorphism. Its kernel is the
bisections that move no object -- the sections of the isotropy groups. -/
def objEquivHom : Bisection C →* Equiv.Perm C where
  toFun β := β.objEquiv
  map_one' := rfl
  map_mul' _ _ := rfl

@[simp] theorem objEquivHom_apply (β : Bisection C) : objEquivHom β = β.objEquiv := rfl

end Bisection
end FiniteGroupoid
end PartialSymmetry
