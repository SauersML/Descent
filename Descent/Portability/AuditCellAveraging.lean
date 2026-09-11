/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.AuditRangeCaps
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

assert_below Descent.Decision Descent.Program

/-!
Decision-Directed Portability, Proposition 17. Replacing probabilities in
one nonempty decision cell by their exact arithmetic mean preserves its
sum and interval constraints. Weighted reciprocal contributions decrease
when the coefficient is constant on the cell. No approximation or binning
of distinct coefficients is used.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.AuditCellAveraging

open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The arithmetic mean of the probabilities in one cell. -/
noncomputable def cellMean (s : Finset ι) (p : ι → ℝ) : ℝ := (∑ i ∈ s, p i) / s.card

/-- Average exactly within the selected cell, retaining every other probability. -/
noncomputable def averageCell (s : Finset ι) (p : ι → ℝ) (i : ι) : ℝ :=
  if i ∈ s then cellMean s p else p i

/-- Every common lower bound remains a lower bound for the cell average. -/
theorem le_cellMean (s : Finset ι) (p : ι → ℝ) (hs : s.Nonempty) (l : ℝ)
    (hl : ∀ i ∈ s, l ≤ p i) : l ≤ cellMean s p := by
  have hn : (0 : ℝ) < s.card := by exact_mod_cast hs.card_pos
  apply (le_div_iff₀ hn).mpr
  have hh := Finset.sum_le_sum hl
  simpa [mul_comm] using hh

/-- Every common upper bound remains an upper bound for the cell average. -/
theorem cellMean_le (s : Finset ι) (p : ι → ℝ) (hs : s.Nonempty) (u : ℝ)
    (hu : ∀ i ∈ s, p i ≤ u) : cellMean s p ≤ u := by
  have hn : (0 : ℝ) < s.card := by exact_mod_cast hs.card_pos
  apply (div_le_iff₀ hn).mpr
  have hh := Finset.sum_le_sum hu
  simpa [mul_comm] using hh

/-- Positive original probabilities make the exact cell average positive. -/
theorem cellMean_pos (s : Finset ι) (p : ι → ℝ) (hs : s.Nonempty)
    (hp : ∀ i ∈ s, 0 < p i) : 0 < cellMean s p := by
  unfold cellMean
  exact div_pos (Finset.sum_pos hp hs) (by exact_mod_cast hs.card_pos)

/-- Averaging preserves the cell's exact total request probability. -/
theorem cell_sum (s : Finset ι) (p : ι → ℝ) (hs : s.Nonempty) :
    (∑ i ∈ s, averageCell s p i) = ∑ i ∈ s, p i := by
  have hn : (s.card : ℝ) ≠ 0 := by exact_mod_cast hs.card_pos.ne'
  calc
    _ = ∑ _i ∈ s, cellMean s p := Finset.sum_congr rfl
      (fun i hi ↦ by simp only [averageCell, if_pos hi])
    _ = (s.card : ℝ) * cellMean s p := by simp
    _ = _ := mul_div_cancel₀ _ hn

/-- A cell average weakly reduces its total reciprocal contribution. -/
theorem reciprocal_sum_le (s : Finset ι) (p : ι → ℝ) (hs : s.Nonempty)
    (hp : ∀ i ∈ s, 0 < p i) :
    (∑ i ∈ s, 1 / averageCell s p i) ≤ ∑ i ∈ s, 1 / p i := by
  have hh := Finset.sq_sum_div_le_sum_sq_div s (fun _ ↦ (1 : ℝ)) hp
  have hn : (s.card : ℝ) ≠ 0 := by exact_mod_cast hs.card_pos.ne'
  have hP : (∑ i ∈ s, p i) ≠ 0 := (Finset.sum_pos hp hs).ne'
  simp only [one_pow, Finset.sum_const, nsmul_eq_mul, mul_one] at hh
  have he : (∑ i ∈ s, 1 / averageCell s p i) = (s.card : ℝ) ^ 2 / (∑ i ∈ s, p i) := by
    calc
      _ = ∑ _i ∈ s, 1 / cellMean s p := Finset.sum_congr rfl
        (fun i hi ↦ by simp only [averageCell, if_pos hi])
      _ = (s.card : ℝ) * (1 / cellMean s p) := by simp
      _ = _ := by unfold cellMean; field_simp
  rwa [he]

/-- If summands agree outside a cell, a comparison of cell sums extends to the whole frame. -/
theorem extend_sum_le (s : Finset ι) (f g : ι → ℝ)
    (hout : ∀ i ∉ s, f i = g i) (hin : (∑ i ∈ s, f i) ≤ ∑ i ∈ s, g i) :
    (∑ i, f i) ≤ ∑ i, g i := by
  rw [← s.sum_add_sum_compl f, ← s.sum_add_sum_compl g]
  apply add_le_add hin
  apply le_of_eq
  apply Finset.sum_congr rfl
  intro i hi
  exact hout i (Finset.mem_compl.mp hi)

/-- Constant cell coefficients give an exact whole-frame cost preservation identity. -/
theorem weighted_sum_eq (s : Finset ι) (p c : ι → ℝ) (hs : s.Nonempty)
    (c₀ : ℝ) (hc : ∀ i ∈ s, c i = c₀) :
    (∑ i, c i * averageCell s p i) = ∑ i, c i * p i := by
  have he : (∑ i ∈ s, c i * averageCell s p i) = ∑ i ∈ s, c i * p i := by
    calc
      _ = c₀ * ∑ i ∈ s, averageCell s p i := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun i hi ↦ by rw [hc i hi])
      _ = c₀ * ∑ i ∈ s, p i := by rw [cell_sum s p hs]
      _ = _ := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun i hi ↦ by rw [hc i hi])
  have hout (i : ι) (hi : i ∉ s) : c i * averageCell s p i = c i * p i := by
    simp [averageCell, hi]
  exact le_antisymm (extend_sum_le s _ _ hout he.le)
    (extend_sum_le s _ _ (fun i hi ↦ (hout i hi).symm) he.ge)

/-- Constant nonnegative cell coefficients yield a smaller total weighted audit variance. -/
theorem weighted_reciprocal_le (s : Finset ι) (p a : ι → ℝ) (hs : s.Nonempty)
    (hp : ∀ i ∈ s, 0 < p i) (a₀ : ℝ) (ha₀ : 0 ≤ a₀) (ha : ∀ i ∈ s, a i = a₀) :
    (∑ i, a i / averageCell s p i) ≤ ∑ i, a i / p i := by
  apply extend_sum_le s
  · intro i hi
    simp [averageCell, hi]
  · calc
      _ = a₀ * ∑ i ∈ s, 1 / averageCell s p i := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun i hi ↦ by rw [ha i hi]; ring)
      _ ≤ a₀ * ∑ i ∈ s, 1 / p i :=
        mul_le_mul_of_nonneg_left (reciprocal_sum_le s p hs hp) ha₀
      _ = _ := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun i hi ↦ by rw [ha i hi]; ring)

end Descent.Portability.AuditCellAveraging
