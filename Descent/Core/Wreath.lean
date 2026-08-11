/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Layer
import Mathlib.Algebra.Group.Pi.Basic
import Mathlib.GroupTheory.Perm.Basic

assert_below Descent.Meta Descent.Foundations Descent.Coalescent Descent.Pangenome Descent.PopGen
assert_below Descent.Spectral Descent.Blindness Descent.Conditionals Descent.Portability
assert_below Descent.Decision Descent.Program

/-!
# The permutation wreath product `A ≀ Sym Ω`

`Wreath A Ω` is the set of pairs (one element of `A` at each point of `Ω`, one
permutation of `Ω`) under the law

  `(d, σ) * (e, τ) = (fun y ↦ e y * d (τ y), σ * τ)`.

This is `A^Ω ⋊ Sym Ω`, the semidirect product in which `Sym Ω` acts on `A^Ω` by
permuting coordinates. The `d (τ y)` -- the coordinate of the LEFT factor read at
the point the RIGHT factor's permutation has already moved `y` to -- is the whole
content of the word "twisted"; delete the `τ` and the law is the direct product's
and the group is wrong.

`toPerm` embeds it in `Sym (Ω × A)`: the permutation moves the `Ω` coordinate by
`σ` and translates the `A` coordinate by the fibre element sitting at the point it
came from. Mathlib's `RegularWreathProduct` is a different object -- there the top
group acts on ITSELF by translation, so the base is `Q → D` for the acting group
`Q`. The base here is an arbitrary index set with `Sym Ω` acting tautologically,
which is the case the groupoid decomposition produces and which
`RegularWreathProduct` does not cover.

Nothing in this file is finite. The source needed `Fintype` to count Hamming
disagreements; the group law and the embedding need no such hypothesis, so none is
imposed.
-/

namespace Descent.Core

universe u v

/-- The permutation wreath product `A ≀ Sym Ω`: a fibre element at every point of
the index set, together with a permutation of the index set. -/
@[ext]
structure Wreath (A : Type u) (Ω : Type v) where
  /-- The fibre element sitting at each point of the index set. -/
  coord : Ω → A
  /-- The permutation of the index set. -/
  perm : Equiv.Perm Ω

namespace Wreath

variable {A : Type u} {Ω : Type v} [Group A]

/-- The twisted product: the right factor's permutation moves the point at which
the left factor's coordinate is read. -/
instance : Mul (Wreath A Ω) where
  mul a b := ⟨fun y ↦ b.coord y * a.coord (b.perm y), a.perm * b.perm⟩

@[simp] theorem mul_coord (a b : Wreath A Ω) (y : Ω) :
    (a * b).coord y = b.coord y * a.coord (b.perm y) := rfl

@[simp] theorem mul_perm (a b : Wreath A Ω) : (a * b).perm = a.perm * b.perm := rfl

/-- The identity: the trivial fibre element everywhere, and the identity
permutation. -/
instance : One (Wreath A Ω) where one := ⟨1, 1⟩

@[simp] theorem one_coord (y : Ω) : (1 : Wreath A Ω).coord y = 1 := rfl

@[simp] theorem one_perm : (1 : Wreath A Ω).perm = 1 := rfl

/-- The inverse. The coordinate at `y` inverts the coordinate the element carried
at the point `y` came from, which is where the twist reappears. -/
instance : Inv (Wreath A Ω) where
  inv a := ⟨fun y ↦ (a.coord (a.perm⁻¹ y))⁻¹, a.perm⁻¹⟩

@[simp] theorem inv_coord (a : Wreath A Ω) (y : Ω) :
    a⁻¹.coord y = (a.coord (a.perm⁻¹ y))⁻¹ := rfl

@[simp] theorem inv_perm (a : Wreath A Ω) : a⁻¹.perm = a.perm⁻¹ := rfl

instance : Group (Wreath A Ω) where
  mul_assoc a b c := by ext y <;> simp [mul_assoc]
  one_mul a := by ext y <;> simp
  mul_one a := by ext y <;> simp
  inv_mul_cancel a := by ext y <;> simp

/-- **The embedding `A ≀ Sym Ω ↪ Sym (Ω × A)`.** The wreath element `(d, σ)` acts
on `Ω × A` by `(y, a) ↦ (σ y, a * d y)`: it permutes the fibres by `σ` and
translates within the fibre over `y` by the coordinate stored at `y`.

This is the construction the source repo used to turn a monomial matrix with
`m`-th root of unity phases into an honest permutation of `m` times as many
points; the phases were `ZMod m` and the translation was addition. -/
def toPerm (w : Wreath A Ω) : Equiv.Perm (Ω × A) where
  toFun p := (w.perm p.1, p.2 * w.coord p.1)
  invFun p := (w.perm⁻¹ p.1, p.2 * (w.coord (w.perm⁻¹ p.1))⁻¹)
  left_inv p := by simp
  right_inv p := by simp

@[simp] theorem toPerm_apply (w : Wreath A Ω) (p : Ω × A) :
    w.toPerm p = (w.perm p.1, p.2 * w.coord p.1) := rfl

/-- **The multiplication law**, transported to `Sym (Ω × A)`. Composing the two
permutations reads the left factor's coordinate at the point the right factor has
already moved to, which is exactly the twist in the wreath law -- so the twist is
not a convention but a consequence of composing the two actions. -/
theorem toPerm_mul (a b : Wreath A Ω) : (a * b).toPerm = a.toPerm * b.toPerm := by
  ext p <;> simp [mul_assoc]

@[simp] theorem toPerm_one : (1 : Wreath A Ω).toPerm = 1 := by
  ext p <;> simp

/-- The embedding as a group homomorphism. -/
def toPermHom : Wreath A Ω →* Equiv.Perm (Ω × A) where
  toFun := toPerm
  map_one' := toPerm_one
  map_mul' := toPerm_mul

@[simp] theorem toPermHom_apply (w : Wreath A Ω) : toPermHom w = w.toPerm := rfl

/-- The embedding is injective: testing the permutation on the identity fibre
element recovers both the permutation and every coordinate. 
## Provenance

Generalized from github.com/SauersML/nonsofic_existence (Apache 2.0, same
owner). Original path: `NonsoficGroupsExist/Sofic/MonomialModel.lean`, the
`wreathModel`/`wreathPerm` construction only. There the fibre group was `ZMod m`
written additively, because the monomial matrices being untwisted carried `m`-th
roots of unity; here it is an arbitrary group written multiplicatively, which is
what the bisection decomposition needs and what the argument always used.
-/
theorem toPerm_injective :
    Function.Injective (toPerm : Wreath A Ω → Equiv.Perm (Ω × A)) := by
  intro a b hab
  ext y
  · have h := congrArg (fun σ : Equiv.Perm (Ω × A) ↦ (σ (y, 1)).2) hab
    simpa using h
  · have h := congrArg (fun σ : Equiv.Perm (Ω × A) ↦ (σ (y, 1)).1) hab
    simpa using h

theorem toPermHom_injective :
    Function.Injective (toPermHom : Wreath A Ω →* Equiv.Perm (Ω × A)) :=
  toPerm_injective

end Wreath
end Descent.Core
