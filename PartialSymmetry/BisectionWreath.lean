/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import PartialSymmetry.BisectionGroup
import PartialSymmetry.Wreath

/-!
# Bisections of a connected groupoid are a wreath product

For a connected groupoid `C` with object set `Ω` and a base object `x`,

  `Bis(C) ≅ Aut_C(x) ≀ Sym Ω = Aut_C(x)^Ω ⋊ Sym Ω`.

A bisection carries two independent pieces of information and the isomorphism
separates them: WHERE each object goes (an element of `Sym Ω`) and, once a transport
`s_y : x ⟶ y` has been chosen at every object, WHICH arrow was used, read as an
element of the single group `Aut_C(x)` by conjugating it back to the base point. The
coordinates are the conjugates `s_y ≫ β.hom y ≫ (s_{σ y})⁻¹`.

The twist in the wreath law is not imposed; it is measured. Composing bisections
reads the left factor's arrow at the object the right factor has already moved to, so
the coordinate function of a product is `fun y ↦ c y * b (τ y)` -- which is the law
`PartialSymmetry.Wreath` was given, and the reason that file states it with the `τ`
inside.

Connectedness enters only to supply the transports, and it is the whole of what is
needed: no finiteness hypothesis appears here, though the source repo's groupoids
were finite. The isomorphism DEPENDS on the chosen transports; a different choice
changes it by an inner automorphism of the coordinate group at each point, which is
why the statement takes `s` as an argument rather than hiding it behind an
existential.

## Biological reading

Take `Ω` to be the copies of a homologous region within a genome -- a segmental
duplication family, or the copies of a gene after amplification -- and `C` the
groupoid whose arrows `y ⟶ z` are the homologies between copies, composable and
invertible, but with no distinguished copy. Then a bisection is a global relabelling
of the family: it says which copy each copy is being identified with, and by which
homology.

The theorem says such a relabelling is exactly two independent things: an exchange of
the copies (`Sym Ω`) and, at each copy, an internal state drawn from one fixed group
(`Aut_C(x)^Ω`) -- the self-homologies of a single copy, which is where phase,
orientation, or register of a tandem repeat lives. The semidirect product, not the
direct product, is what the biology gives: permuting the copies transports the
internal states with them, so the two factors do not commute.
-/

namespace PartialSymmetry
namespace FiniteGroupoid

open CategoryTheory

universe u v

variable {C : Type u} [Groupoid.{v} C]

namespace Bisection

variable (x : C) (s : ∀ Y : C, x ⟶ Y)

/-- The coordinate of a bisection at an object: its arrow out of that object,
conjugated back to the base point along the chosen transports. -/
noncomputable def coordAt (β : Bisection C) (Y : C) : x ⟶ x :=
  s Y ≫ β.hom Y ≫ CategoryTheory.inv (s (β.objEquiv Y))

/-- A bisection, read in the coordinates the transports provide. -/
noncomputable def toWreath (β : Bisection C) : Wreath (x ⟶ x) C where
  coord := coordAt x s β
  perm := β.objEquiv

@[simp] theorem toWreath_coord (β : Bisection C) (Y : C) :
    (toWreath x s β).coord Y = s Y ≫ β.hom Y ≫ CategoryTheory.inv (s (β.objEquiv Y)) :=
  rfl

@[simp] theorem toWreath_perm (β : Bisection C) :
    (toWreath x s β).perm = β.objEquiv := rfl

/-- The inverse reading: a permutation together with one base-point automorphism per
object assembles into a bisection, by transporting out to the base point, applying
the automorphism there, and transporting back. -/
noncomputable def ofWreath (w : Wreath (x ⟶ x) C) : Bisection C where
  objEquiv := w.perm
  hom Y := CategoryTheory.inv (s Y) ≫ w.coord Y ≫ s (w.perm Y)

@[simp] theorem ofWreath_objEquiv (w : Wreath (x ⟶ x) C) :
    (ofWreath x s w).objEquiv = w.perm := rfl

@[simp] theorem ofWreath_hom (w : Wreath (x ⟶ x) C) (Y : C) :
    (ofWreath x s w).hom Y = CategoryTheory.inv (s Y) ≫ w.coord Y ≫ s (w.perm Y) :=
  rfl

theorem toWreath_ofWreath (w : Wreath (x ⟶ x) C) :
    toWreath x s (ofWreath x s w) = w := by
  ext Y
  · simp
  · simp

theorem ofWreath_toWreath (β : Bisection C) :
    ofWreath x s (toWreath x s β) = β := by
  refine ext' (fun _ ↦ rfl) ?_
  intro Y
  simp

/-- Reading a product in coordinates multiplies the readings, in the wreath product
and not the direct product: the left factor's coordinate is read at the object the
right factor's permutation has already moved to. -/
theorem toWreath_mul (β γ : Bisection C) :
    toWreath x s (β * γ) = toWreath x s β * toWreath x s γ := by
  ext Y
  · simp [Groupoid.vertexGroup, Category.assoc]
  · simp

/-- **Bisections of a connected groupoid are a wreath product.**

`Bis(C) ≅ Aut_C(x) ≀ Sym Ω`, given a base object `x` and a transport `s y : x ⟶ y`
at every object -- which is exactly what connectedness supplies. -/
noncomputable def mulEquivWreath : Bisection C ≃* Wreath (x ⟶ x) C where
  toFun := toWreath x s
  invFun := ofWreath x s
  left_inv := ofWreath_toWreath x s
  right_inv := toWreath_ofWreath x s
  map_mul' := toWreath_mul x s

@[simp] theorem mulEquivWreath_apply (β : Bisection C) :
    mulEquivWreath x s β = toWreath x s β := rfl

@[simp] theorem mulEquivWreath_symm_apply (w : Wreath (x ⟶ x) C) :
    (mulEquivWreath x s).symm w = ofWreath x s w := rfl

end Bisection

/-- **The wreath decomposition, from connectedness alone.**

A groupoid in which every object is reachable from the base object `x` has its
bisection group isomorphic to `Aut_C(x) ≀ Sym Ω`: internal copy states at each
object, times an exchange of the objects.

The transports are chosen here rather than supplied, so the statement is an
existence claim and the isomorphism is noncomputable; `Bisection.mulEquivWreath`
is the same theorem with the choice exposed. -/
theorem nonempty_bisection_mulEquiv_wreath (x : C)
    (hconn : ∀ Y : C, Nonempty (x ⟶ Y)) :
    Nonempty (Bisection C ≃* Wreath (x ⟶ x) C) :=
  ⟨Bisection.mulEquivWreath x fun Y ↦ (hconn Y).some⟩

end FiniteGroupoid
end PartialSymmetry
