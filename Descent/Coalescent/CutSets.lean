/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Coalescent.Split
import Mathlib.Tactic

assert_below Descent.Pangenome Descent.PopGen Descent.Spectral Descent.Blindness Descent.Conditionals Descent.Portability Descent.Decision Descent.Program

namespace Descent

/-!
# Naming each cut once

`Descent.Coalescent.Split` shows every state below `η` is a cut `splitBy η S`, and that the
cut along `S` and the cut along the rest of `S`'s class are the same state
(`splitBy_compl`).  So cuts are named twice, and a count of cut sets over-counts states by
exactly two.  `Descent.Coalescent.Program`'s open item 1 is the bijection that removes the
double-naming.

The trick that removes it is to break the tie with a basepoint rather than by dividing by
two.  Each class has a canonical representative -- `Quotient.out` -- and of the two sides of
a cut, exactly one omits it.  Normalising to that side names each cut once:

  a CUT SET is a nonempty subset of a single class that omits that class's representative,

and `splitBy η` is injective on cut sets (`splitBy_injective_on_cutSets`) and hits every
state below `η` (`exists_cutSet_of_covers`).  Counting cut sets is then counting subsets:
the cut sets inside a class of size `λ` are the nonempty subsets of the other `λ - 1`
elements, so there are `2^{λ-1} - 1` of them, matching `Program.two_mul_cutCount_add_two`
without any division.

What this file does NOT do is assemble those two theorems and the subset count into the
cardinality `#{ξ ; ξ ≺ η} = Σ_c (2^{λ_c - 1} - 1)`.  That is a sum over classes of a count of
subsets, and it is not written.

## Main results

- `IsCutSet`: a nonempty subset of one class omitting that class's representative.
- `splitBy_injective_on_cutSets`: distinct cut sets give distinct states.
- `exists_cutSet_of_covers`: every state below `η` is the cut along a cut set.
-/

namespace Coalescent

open scoped Classical

/-- **A cut set.**  Nonempty, contained in a single class, and omitting that class's
canonical representative -- the last condition being what names each cut once instead of
twice. -/
def IsCutSet {n : ℕ} (η : ER n) (S : Finset (Fin n)) : Prop :=
  S.Nonempty ∧ (∀ x ∈ S, ∀ y ∈ S, η.r x y) ∧ (∀ x ∈ S, (Quotient.mk η x).out ∉ S)

/-- The representative of a class never lies in a cut set of that class -- nor in a cut set
of any other class, since it is not related to those.  Either way it is outside, which is
what the injectivity argument needs. -/
theorem out_not_mem_cutSet {n : ℕ} {η : ER n} {S : Finset (Fin n)} (hS : IsCutSet η S)
    (x : Fin n) : (Quotient.mk η x).out ∉ S := by
  intro hmem
  have hcl : Quotient.mk η ((Quotient.mk η x).out) = Quotient.mk η x := Quotient.out_eq _
  have := hS.2.2 _ hmem
  rw [hcl] at this
  exact this hmem

/-- **Distinct cut sets give distinct states.**  If the cuts agree, then for each `x` in one
set the pair `(x, r)` with `r` the class representative is split by one cut, hence by the
other -- and `r` is outside both, so `x` is in both. -/
theorem splitBy_injective_on_cutSets {n : ℕ} (η : ER n) {S T : Finset (Fin n)}
    (hS : IsCutSet η S) (hT : IsCutSet η T) (h : splitBy η S = splitBy η T) : S = T := by
  classical
  have hkey := (splitBy_eq_iff η S T).mp h
  have hforward : ∀ {A B : Finset (Fin n)}, IsCutSet η A → IsCutSet η B →
      (∀ x y : Fin n, η.r x y → ((x ∈ A ↔ y ∈ A) ↔ (x ∈ B ↔ y ∈ B))) → A ⊆ B := by
    intro A B hA hB hiff x hx
    set r := (Quotient.mk η x).out with hr
    have hrx : η.r x r := by
      have : Quotient.mk η r = Quotient.mk η x := Quotient.out_eq _
      exact Quotient.exact this.symm
    have hrA : r ∉ A := out_not_mem_cutSet hA x
    have hrB : r ∉ B := out_not_mem_cutSet hB x
    have hnotiff : ¬ (x ∈ A ↔ r ∈ A) := by
      intro hiffA
      exact hrA (hiffA.mp hx)
    have hnotiffB : ¬ (x ∈ B ↔ r ∈ B) := fun hc ↦ hnotiff ((hiff x r hrx).mpr hc)
    by_contra hxB
    exact hnotiffB ⟨fun hc ↦ absurd hc hxB, fun hc ↦ absurd hc hrB⟩
  refine Finset.Subset.antisymm (hforward hS hT hkey) (hforward hT hS ?_)
  intro x y hxy
  exact (hkey x y hxy).symm

/-- The class of `x`, as a `Finset`. -/
noncomputable def classFinset {n : ℕ} (η : ER n) (x : Fin n) : Finset (Fin n) :=
  Finset.univ.filter fun y ↦ η.r y x

theorem mem_classFinset {n : ℕ} (η : ER n) (x y : Fin n) :
    y ∈ classFinset η x ↔ η.r y x := by
  simp [classFinset]

/-- Cutting along `S` and along the rest of `S`'s class agree, in the `classFinset` form the
normalisation below uses. -/
theorem splitBy_compl_classFinset {n : ℕ} (η : ER n) (S : Finset (Fin n)) (a : Fin n)
    (hSa : ∀ x ∈ S, η.r x a) :
    splitBy η S = splitBy η (classFinset η a \ S) :=
  splitBy_compl η S a hSa

/-- **Every cover is a proper cut**, with the witnesses the normalisation needs. -/
theorem exists_properCut_of_covers {n : ℕ} {ξ η : ER n} (hcov : Covers ξ η) :
    ∃ S : Finset (Fin n), ξ = splitBy η S ∧ S.Nonempty ∧
      ∃ a, (∀ x ∈ S, η.r x a) ∧ ∃ w, η.r w a ∧ w ∉ S := by
  classical
  obtain ⟨a, b, hab, rfl⟩ := (covers_iff_exists_merge ξ η).mp hcov
  obtain ⟨x₀, hx₀⟩ := quotient_mk_surjective ξ a
  obtain ⟨w, hw⟩ := quotient_mk_surjective ξ b
  refine ⟨Finset.univ.filter fun x ↦ Quotient.mk ξ x = a, eq_splitBy_merge ξ hab,
    ⟨x₀, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx₀⟩⟩, x₀, ?_, w, ?_, ?_⟩
  · intro x hx
    have hxa : Quotient.mk ξ x = a := (Finset.mem_filter.mp hx).2
    exact le_merge ξ a b (Quotient.exact (hxa.trans hx₀.symm))
  · exact (merge ξ a b).iseqv.symm (merge_rel ξ a b hx₀ hw)
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [hw]
    exact fun h ↦ hab h.symm

/-- **Every state below `η` is the cut along a cut set.**  `exists_properCut_of_covers` gives
a cut; if it contains its class's representative, `splitBy_compl` swaps to the other side,
which does not.  Normalising this way is what makes the naming unique. -/
theorem exists_cutSet_of_covers {n : ℕ} {η ξ : ER n} (hcov : Covers ξ η) :
    ∃ T : Finset (Fin n), IsCutSet η T ∧ ξ = splitBy η T := by
  classical
  obtain ⟨S, hξS, hSne, a, hSa, w, hwa, hwS⟩ := exists_properCut_of_covers hcov
  by_cases hrep : (Quotient.mk η a).out ∈ S
  · -- the representative is on `S`'s side; take the other side
    refine ⟨classFinset η a \ S, ⟨⟨w, ?_⟩, ?_, ?_⟩, ?_⟩
    · exact Finset.mem_sdiff.mpr ⟨(mem_classFinset η a w).mpr hwa, hwS⟩
    · intro x hx y hy
      have hxa : η.r x a := (mem_classFinset η a x).mp (Finset.mem_sdiff.mp hx).1
      have hya : η.r y a := (mem_classFinset η a y).mp (Finset.mem_sdiff.mp hy).1
      exact η.iseqv.trans hxa (η.iseqv.symm hya)
    · intro x hx hmem
      have hxa : η.r x a := (mem_classFinset η a x).mp (Finset.mem_sdiff.mp hx).1
      have hcl : Quotient.mk η x = Quotient.mk η a := Quotient.sound hxa
      rw [hcl] at hmem
      exact (Finset.mem_sdiff.mp hmem).2 hrep
    · rw [hξS]
      exact splitBy_compl_classFinset η S a hSa
  · refine ⟨S, ⟨hSne, ?_, ?_⟩, hξS⟩
    · intro x hx y hy
      exact η.iseqv.trans (hSa x hx) (η.iseqv.symm (hSa y hy))
    · intro x hx hmem
      have hcl : Quotient.mk η x = Quotient.mk η a := Quotient.sound (hSa x hx)
      rw [hcl] at hmem
      exact hrep hmem

/-- Cut sets inside a class sit in that class with its representative removed, which is the
`λ - 1` elements the `2^{λ-1} - 1` counts subsets of. -/
theorem cutSet_subset_erase {n : ℕ} {η : ER n} {S : Finset (Fin n)} (hS : IsCutSet η S)
    {x : Fin n} (hx : x ∈ S) :
    S ⊆ (classFinset η x).erase (Quotient.mk η x).out := by
  intro y hy
  refine Finset.mem_erase.mpr ⟨?_, ?_⟩
  · intro hcontra
    exact out_not_mem_cutSet hS x (hcontra ▸ hy)
  · exact (mem_classFinset η x y).mpr (hS.2.1 y hy x hx)

end Coalescent

end Descent
