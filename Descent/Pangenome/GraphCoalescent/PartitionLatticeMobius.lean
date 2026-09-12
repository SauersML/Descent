/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Pangenome.GraphCoalescent.ConnectivityCumulantDegree
import Descent.Pangenome.GraphCoalescent.MultiplicativeConnectionLaw
import Mathlib.Combinatorics.Enumerative.IncidenceAlgebra
import Mathlib.Combinatorics.Enumerative.Stirling

assert_below Descent.PopGen Descent.Spectral Descent.Blindness Descent.Conditionals
assert_below Descent.Portability Descent.Decision Descent.Program

/-!
# The Möbius function of the partition lattice

Theorem D of the pangenome hidden-clock note uses the partition-lattice Möbius coefficient
`μ(σ, ⊤) = (-1)^{|σ|-1} (|σ|-1)!`. `Descent.Pangenome.TripleGluing` has that coefficient at order
three and names arbitrary order as unproved. `ConnectivityCumulant` proves that
`mobiusCoefficient` obeys the defining recursion of `μ(·, ⊤)` on every upper interval. This
module identifies it with the Möbius function of Mathlib's incidence algebra, and records the
Stirling-number route to the same value.

`instLocallyFiniteOrderFinpartition` equips the partitions of a finite set with the locally
finite order that `IncidenceAlgebra.mu` needs. `mu_finpartition_top` is the arbitrary-order
statement: on a nonempty set, `IncidenceAlgebra.mu ℤ σ ⊤ = (-1)^{|σ|-1} (|σ|-1)!`. The proof is
downward well-founded induction on the finite lattice, through Mathlib's
`mu_eq_neg_sum_Ioc_of_ne` and `ConnectivityCumulant.sum_mobiusCoefficient_upper`.

`card_filter_card_parts_eq_stirlingSecond` shows that the partitions of `t` into `j` parts number
`S(|t|, j)`, through the insertion bijection of `LahWeights` with weight one.
`sum_stirlingSecond_mul_mobiusCoefficient` is the Stirling identity
`Σ_j S(k, j) (-1)^{j-1} (j-1)! = [k = 1]`. `sum_mobiusCoefficient_eq_sum_stirlingSecond` regroups
the Möbius sum over all partitions by the number of parts, so that sum is the Stirling sum.
`topMobius_eq_mobiusCoefficient` records that `MultiplicativeConnectionLaw.topMobius`, the
coefficient of the multiplicative-coalescent law (F4), is the same quantity.

## Empirical status

None. The bodies here are finite combinatorics on the partition lattice and identities of
integer sequences, so no measurement can bear on them.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Pangenome.GraphCoalescent

open Finset
open scoped Classical

noncomputable section

variable {α : Type*} [DecidableEq α] {s : Finset α}

/-- The partitions of a finite set, ordered by refinement, form a locally finite order. -/
instance instLocallyFiniteOrderFinpartition : LocallyFiniteOrder (Finpartition s) :=
  Fintype.toLocallyFiniteOrder

/-- **NOTE (D3): the partition-lattice Möbius value, at every order.** On a nonempty finite set,
the Möbius function of Mathlib's incidence algebra on the partition lattice is
`μ(σ, ⊤) = (-1)^{|σ|-1} (|σ|-1)!`. -/
theorem mu_finpartition_top (hs : s.Nonempty) (σ : Finpartition s) :
    IncidenceAlgebra.mu ℤ σ ⊤ = mobiusCoefficient #σ.parts := by
  refine WellFoundedGT.induction
    (C := fun σ : Finpartition s ↦ IncidenceAlgebra.mu ℤ σ ⊤ = mobiusCoefficient #σ.parts) σ ?_
  intro σ ih
  by_cases htop : σ = ⊤
  · rw [htop, IncidenceAlgebra.mu_apply, if_pos rfl, (card_parts_eq_one_iff ⊤ hs).mpr rfl,
      mobiusCoefficient_one]
  · rw [IncidenceAlgebra.mu_eq_neg_sum_Ioc_of_ne htop]
    have hsum := sum_mobiusCoefficient_upper σ hs
    rw [if_neg fun h1 ↦ htop ((card_parts_eq_one_iff σ hs).mp h1)] at hsum
    have hfilter : univ.filter (fun x : Finpartition s ↦ σ ≤ x) = insert σ (Ioc σ ⊤) := by
      ext x
      simp only [mem_filter, mem_univ, true_and, mem_insert, mem_Ioc, le_top, and_true]
      constructor
      · intro h
        rcases h.eq_or_lt with h' | h'
        · exact Or.inl h'.symm
        · exact Or.inr h'
      · rintro (h | h)
        · exact h ▸ le_rfl
        · exact h.le
    rw [hfilter, sum_insert fun h ↦ lt_irrefl σ (mem_Ioc.mp h).1] at hsum
    rw [sum_congr rfl fun x hx ↦ ih x (mem_Ioc.mp hx).1]
    linarith

/-- **Stirling numbers count set partitions.** The partitions of `t` into `j` parts number
`S(|t|, j)`. -/
theorem card_filter_card_parts_eq_stirlingSecond (t : Finset α) (j : ℕ) :
    #(univ.filter fun ρ : Finpartition t ↦ #ρ.parts = j) = Nat.stirlingSecond #t j := by
  rw [card_filter]
  induction t using Finset.induction_on generalizing j with
  | empty =>
    rw [sum_eq_single (⊥ : Finpartition (∅ : Finset α))
      (fun P _ hne ↦ absurd (finpartition_empty_eq_bot P) hne) (fun h ↦ absurd (mem_univ _) h)]
    cases j with
    | zero => simp
    | succ j => simp
  | insert a t ha ih =>
    rw [sum_finpartition_insert ha, card_insert_of_notMem ha]
    have hstep : ∀ P : Finpartition t,
        ∑ r ∈ insert ∅ P.parts, (if #(insertAt P ha r).parts = j then 1 else 0)
          = (if #P.parts + 1 = j then 1 else 0) + j * (if #P.parts = j then 1 else 0) := by
      intro P
      have hparts : ∀ r ∈ P.parts, (if #(insertAt P ha r).parts = j then 1 else 0)
          = (if #P.parts = j then 1 else 0) := fun r hr ↦ by
        rw [card_parts_insertAt_of_mem P ha hr]
      rw [sum_insert P.empty_notMem_parts, card_parts_insertAt_empty, sum_congr rfl hparts,
        sum_const, smul_eq_mul]
      congr 1
      split_ifs with hj
      · rw [hj]
      · rw [mul_zero, mul_zero]
    rw [sum_congr rfl fun P _ ↦ hstep P, sum_add_distrib, ← mul_sum, ih j]
    cases j with
    | zero =>
      rw [sum_eq_zero fun P _ ↦ if_neg (Nat.succ_ne_zero _), zero_mul, zero_add]
      rfl
    | succ j =>
      simp only [Nat.add_right_cancel_iff]
      rw [ih j, Nat.stirlingSecond_succ_succ]
      ring

/-- **The Stirling identity.** `Σ_j S(k, j) (-1)^{j-1} (j-1)! = [k = 1]` for `k ≥ 1`, written
with `k + 1` in place of `k`. -/
theorem sum_stirlingSecond_mul_mobiusCoefficient (k : ℕ) :
    ∑ j ∈ range (k + 2), (Nat.stirlingSecond (k + 1) j : ℤ) * mobiusCoefficient j
      = if k = 0 then 1 else 0 := by
  set f : ℕ → ℤ := fun j ↦ (Nat.stirlingSecond k j : ℤ) * mobiusCoefficient j with hf
  set g : ℕ → ℤ := fun j ↦ (Nat.stirlingSecond k j : ℤ) * mobiusCoefficient (j + 1) with hg
  have hrec : ∀ j : ℕ, (Nat.stirlingSecond (k + 1) (j + 1) : ℤ) * mobiusCoefficient (j + 1)
      = ((j : ℤ) + 1) * f (j + 1) + g j := by
    intro j
    simp only [hf, hg, Nat.stirlingSecond_succ_succ]
    push_cast
    ring
  have hshift : ∑ j ∈ range (k + 2), (Nat.stirlingSecond (k + 1) j : ℤ) * mobiusCoefficient j
      = ∑ j ∈ range (k + 1), (((j : ℤ) + 1) * f (j + 1) + g j) := by
    rw [sum_range_succ', sum_congr rfl fun j _ ↦ hrec j]
    have hzero : (Nat.stirlingSecond (k + 1) 0 : ℤ) * mobiusCoefficient 0 = 0 := by
      rw [show Nat.stirlingSecond (k + 1) 0 = 0 from rfl, Nat.cast_zero, zero_mul]
    rw [hzero, add_zero]
  have htop : ∑ j ∈ range (k + 1), ((j : ℤ) + 1) * f (j + 1)
      = ∑ j ∈ range (k + 1), (j : ℤ) * f j := by
    have h1 := sum_range_succ' (fun i : ℕ ↦ (i : ℤ) * f i) (k + 1)
    have h2 := sum_range_succ (fun i : ℕ ↦ (i : ℤ) * f i) (k + 1)
    have hzero : f (k + 1) = 0 := by
      simp only [hf, Nat.stirlingSecond_eq_zero_of_lt (Nat.lt_succ_self k), Nat.cast_zero,
        zero_mul]
    simp only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, zero_mul, add_zero, hzero,
      mul_zero] at h1 h2
    linarith
  have hpoint : ∀ j ∈ range (k + 1),
      (j : ℤ) * f j + g j = if j = 0 then (Nat.stirlingSecond k j : ℤ) else 0 := by
    intro j _
    rcases Nat.eq_zero_or_pos j with hj | hj
    · subst hj
      simp [hf, hg, mobiusCoefficient_one]
    · rw [if_neg hj.ne']
      have h := mobiusCoefficient_succ_add j hj
      simp only [hf, hg]
      linear_combination (Nat.stirlingSecond k j : ℤ) * h
  rw [hshift, sum_add_distrib, htop, ← sum_add_distrib, sum_congr rfl hpoint, sum_ite_eq',
    if_pos (mem_range.mpr (Nat.succ_pos k))]
  cases k with
  | zero => simp
  | succ k => simp [Nat.stirlingSecond]

/-- The Möbius coefficient of `MultiplicativeConnectionLaw`, which enters the law (F4) of the
multiplicative coalescent, is `mobiusCoefficient`: the two developments name one quantity. -/
theorem topMobius_eq_mobiusCoefficient : topMobius = mobiusCoefficient := rfl

/-- Grouping the partitions of `t` by their number of parts turns the Möbius sum of
`ConnectivityCumulant.sum_mobiusCoefficient_finpartition` into the Stirling sum. -/
theorem sum_mobiusCoefficient_eq_sum_stirlingSecond (t : Finset α) :
    ∑ ρ : Finpartition t, mobiusCoefficient #ρ.parts
      = ∑ j ∈ range (#t + 1), (Nat.stirlingSecond #t j : ℤ) * mobiusCoefficient j := by
  rw [← sum_fiberwise_of_maps_to (g := fun ρ : Finpartition t ↦ #ρ.parts) (t := range (#t + 1))
    (fun ρ _ ↦ mem_range.mpr (Nat.lt_succ_of_le ρ.card_parts_le_card))]
  refine sum_congr rfl fun j _ ↦ ?_
  have hconst : ∀ ρ ∈ univ.filter (fun ρ : Finpartition t ↦ #ρ.parts = j),
      mobiusCoefficient #ρ.parts = mobiusCoefficient j := fun ρ hρ ↦ by
    rw [(mem_filter.mp hρ).2]
  rw [sum_congr rfl hconst, sum_const, nsmul_eq_mul, card_filter_card_parts_eq_stirlingSecond]

end

end Descent.Pangenome.GraphCoalescent
