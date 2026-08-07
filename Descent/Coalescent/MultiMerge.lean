/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Coalescent.Lambda
import Descent.Coalescent.StateSpace
import Mathlib.Tactic

assert_below Descent.Pangenome Descent.PopGen Descent.Spectral Descent.Conditionals
assert_below Descent.Portability Descent.Decision Descent.Program

-- LAYER DEBT. This file cannot yet assert it is below `Descent.Blindness`:
--   Blindness: reaches 1 module(s) -- `Descent.Blindness.MultipleMergerBlindness`
-- The repair is to move what it reaches for DOWN, not to move this file up.

namespace Descent

/-!
# Merging any number of blocks at once

`Descent.Coalescent.StateSpace` merges two blocks, because Kingman's coalescent never merges
more.  `Descent.Coalescent.Lambda` shows Kingman is the `δ₀` fibre of Pitman's family, in
which any `k` of `b` blocks merge at once.  For the state space to serve that family it has
to be able to perform those mergers, and this file gives it that.

`mergeSet ξ S a` folds every block in `S` onto `a`.  It is the same kernel trick as
`StateSpace.mergeMap` -- an equivalence relation by construction -- and the two-element case
is `merge` (`mergeSet_pair`).  The theorem that generalises `blocks_merge` is
`blocks_mergeSet`: merging `|S|` blocks into one drops the block count by `|S| - 1`, which
for `|S| = 2` is Kingman's drop of one and for `|S| = b` is the total collapse of a
`Λ`-coalescent's largest possible jump.

With it, the state space is no longer specific to binary mergers: a `Λ`- or `Ξ`-coalescent
moves through the same `𝓔ₙ`, along edges this file supplies.  What is NOT here is the rate
attached to those edges -- that is `Lambda.lambdaRate_consistent`'s business -- nor the
process itself.

## Main results

- `mergeSet`: fold a set of blocks onto one of them.
- `mergeSet_pair`: the two-element case is `StateSpace.merge`.
- `le_mergeSet`: merging coarsens.
- `blocks_mergeSet`: **`|S|` blocks become one, so the count drops by `|S| - 1`.**
- `blocks_mergeSet_pair`: which recovers K-C (1.4).
-/

namespace Coalescent

open scoped Classical

/-- Fold every block in `S` onto `a`. -/
noncomputable def mergeSetMap {n : ℕ} (ξ : ER n) (S : Finset (Quotient ξ)) (a : Quotient ξ) :
    Quotient ξ → Quotient ξ := fun c ↦ if c ∈ S then a else c

/-- **Merge a whole set of blocks at once.**  The `Λ`-coalescent's move: `|S|` blocks become
one.  Written as a kernel, so it is an equivalence relation with no argument.

Empirical status: NOT AN EMPIRICAL CLAIM.  It is the edge set of the multiple-merger
coalescent's transition graph, not a claim about any population. -/
noncomputable def mergeSet {n : ℕ} (ξ : ER n) (S : Finset (Quotient ξ)) (a : Quotient ξ) :
    ER n :=
  Setoid.ker fun x ↦ mergeSetMap ξ S a (Quotient.mk ξ x)

theorem mergeSetMap_of_mem {n : ℕ} (ξ : ER n) {S : Finset (Quotient ξ)} {a c : Quotient ξ}
    (h : c ∈ S) : mergeSetMap ξ S a c = a := by
  simp [mergeSetMap, h]

theorem mergeSetMap_of_not_mem {n : ℕ} (ξ : ER n) {S : Finset (Quotient ξ)} {a c : Quotient ξ}
    (h : c ∉ S) : mergeSetMap ξ S a c = c := by
  simp [mergeSetMap, h]

/-- Merging coarsens: every pair related by `ξ` stays related. -/
theorem le_mergeSet {n : ℕ} (ξ : ER n) (S : Finset (Quotient ξ)) (a : Quotient ξ) :
    ξ ≤ mergeSet ξ S a := by
  intro x y hxy
  show mergeSetMap ξ S a (Quotient.mk ξ x) = mergeSetMap ξ S a (Quotient.mk ξ y)
  exact congrArg _ (Quotient.sound hxy)

/-- The image of the fold: everything outside `S`, plus the block they all became. -/
theorem range_mergeSetMap {n : ℕ} (ξ : ER n) {S : Finset (Quotient ξ)} {a : Quotient ξ}
    (ha : a ∈ S) :
    Set.range (fun x : Fin n ↦ mergeSetMap ξ S a (Quotient.mk ξ x))
      = {c | c ∉ S} ∪ {a} := by
  ext c
  simp only [Set.mem_range, Set.mem_union, Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · rintro ⟨x, rfl⟩
    by_cases hx : Quotient.mk ξ x ∈ S
    · exact Or.inr (mergeSetMap_of_mem ξ hx)
    · rw [mergeSetMap_of_not_mem ξ hx]
      exact Or.inl hx
  · rintro (hc | rfl)
    · obtain ⟨x, hx⟩ := quotient_mk_surjective ξ c
      refine ⟨x, ?_⟩
      rw [hx, mergeSetMap_of_not_mem ξ hc]
    · obtain ⟨x, hx⟩ := quotient_mk_surjective ξ c
      refine ⟨x, ?_⟩
      rw [hx, mergeSetMap_of_mem ξ (hx ▸ ha)]

/-- **`|S|` blocks become one.**  Merging a set of `|S|` blocks drops the block count by
`|S| - 1`, generalising `StateSpace.blocks_merge`, which is the case `|S| = 2`. -/
theorem blocks_mergeSet {n : ℕ} (ξ : ER n) {S : Finset (Quotient ξ)} {a : Quotient ξ}
    (ha : a ∈ S) : blocks (mergeSet ξ S a) + (S.card - 1) = blocks ξ := by
  classical
  letI : Fintype (Quotient ξ) := Fintype.ofFinite _
  have hnotmem : a ∉ {c : Quotient ξ | c ∉ S} := by
    simp only [Set.mem_setOf_eq, not_not]
    exact ha
  have hrange : blocks (mergeSet ξ S a)
      = Nat.card ({c : Quotient ξ | c ∉ S} : Set _) + 1 := by
    unfold blocks mergeSet
    rw [Nat.card_congr (Setoid.quotientKerEquivRange _),
      Nat.card_congr (Equiv.setCongr (range_mergeSetMap ξ ha)), Set.union_singleton,
      Set.Nat.card_coe_set_eq, Set.Nat.card_coe_set_eq,
      Set.ncard_insert_of_not_mem hnotmem (Set.toFinite _)]
  have hcompl : Nat.card ({c : Quotient ξ | c ∉ S} : Set _)
      = Fintype.card (Quotient ξ) - S.card := by
    rw [Set.Nat.card_coe_set_eq, Set.ncard_eq_toFinset_card']
    have hset : {c : Quotient ξ | c ∉ S}.toFinset = Sᶜ := by
      ext c
      simp
    rw [hset, Finset.card_compl]
  have hcard : blocks ξ = Fintype.card (Quotient ξ) := Nat.card_eq_fintype_card
  have hle : S.card ≤ Fintype.card (Quotient ξ) := by
    rw [← Finset.card_univ]
    exact Finset.card_le_card (Finset.subset_univ S)
  have hpos : 1 ≤ S.card := Finset.card_pos.mpr ⟨a, ha⟩
  rw [hrange, hcompl, hcard]
  omega

/-- The two-element case is `StateSpace.merge`: folding `{a, b}` onto `a` is folding `b`
onto `a`. -/
theorem mergeSet_pair {n : ℕ} (ξ : ER n) {a b : Quotient ξ} (hab : a ≠ b) :
    mergeSet ξ {a, b} a = merge ξ a b := by
  refine Setoid.ext fun x y ↦ ?_
  have hmap : ∀ c : Quotient ξ, mergeSetMap ξ {a, b} a c = mergeMap ξ a b c := by
    intro c
    by_cases hc : c = b
    · rw [hc, mergeSetMap_of_mem ξ (by simp), mergeMap_apply_self]
    · by_cases hca : c = a
      · rw [hca, mergeSetMap_of_mem ξ (by simp), mergeMap_apply_of_ne ξ a b a hab]
      · rw [mergeSetMap_of_not_mem ξ (by simp [hca, hc]), mergeMap_apply_of_ne ξ a b c hc]
  constructor
  · intro h
    show mergeMap ξ a b (Quotient.mk ξ x) = mergeMap ξ a b (Quotient.mk ξ y)
    rw [← hmap, ← hmap]
    exact h
  · intro h
    show mergeSetMap ξ {a, b} a (Quotient.mk ξ x) = mergeSetMap ξ {a, b} a (Quotient.mk ξ y)
    rw [hmap, hmap]
    exact h

/-- **K-C (1.4) recovered.**  At `|S| = 2` the general drop is Kingman's drop of one, so the
binary theory is the special case it should be. -/
theorem blocks_mergeSet_pair {n : ℕ} (ξ : ER n) {a b : Quotient ξ} (hab : a ≠ b) :
    blocks (mergeSet ξ {a, b} a) + 1 = blocks ξ := by
  have hcard : ({a, b} : Finset (Quotient ξ)).card = 2 := Finset.card_pair hab
  have h := blocks_mergeSet ξ (S := {a, b}) (a := a) (by simp)
  rw [hcard] at h
  simpa using h

end Coalescent

end Descent
