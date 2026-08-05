/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Coalescent.BlockCountMatrix
import Descent.Coalescent.SemigroupLimit
import Mathlib.Analysis.Matrix
import Mathlib.Tactic

namespace Descent

/-!
# The block-count matrix, assembled

`Descent.Coalescent.BlockCountMatrix` counts every entry of the one-generation row: the
diagonal is `WrightFisher.noCoalescenceProb`, the tail below the subdiagonal is `k⁴/N²`, and
the row sums to one.  `Descent.Coalescent.SemigroupLimit.tendsto_pow_of_expansion` consumes
`P_N = 1 + N⁻¹Q + O(N⁻²)`.  This file is the join: the entries become a `Matrix`, the row
bounds become a norm bound, and the many-state instantiation of K-G (2.14) has no missing
ingredient.

The norm is the row-sum norm -- `‖A‖ = max_i Σ_j |A i j|` -- which is what makes a stochastic
matrix a contraction, and is the norm K-G (2.12) writes down.  Mathlib keeps its instances in
the scoped namespace `Matrix.Norms.Operator`, so they are opened here rather than globally.

## Main results

- `linfty_norm_le_of_rows`: a row-wise bound is a norm bound.
- `blockTransition_eq_zero_of_lt`: a generation cannot increase the lineage count.
- `blockMatrix`, `blockGenerator`: the one-generation operator and `Q`.
- `sum_row_blockMatrix`: **each row is a probability distribution**.
- `norm_blockMatrix_le_one`: hence the operator is a contraction, K-G (2.12).
-/

namespace Coalescent

open Finset Matrix
open scoped Matrix.Norms.Operator NNReal

/-- A bound on every row sum is a bound on the row-sum norm. -/
theorem linfty_norm_le_of_rows {m : Type*} [Fintype m] [DecidableEq m]
    {A : Matrix m m ℝ} {C : ℝ≥0} (h : ∀ i, ∑ j, ‖A i j‖₊ ≤ C) : ‖A‖ ≤ (C : ℝ) := by
  rw [Matrix.linfty_opNorm_def]
  exact_mod_cast Finset.sup_le fun i _ ↦ h i

/-- **A generation cannot increase the lineage count.**  The image of a map on `k` points has
at most `k` elements, so the transition to more than `k` has no witnesses. -/
theorem blockTransition_eq_zero_of_lt {N k j : ℕ} (hkj : k < j) :
    blockTransition N k j = 0 := by
  classical
  unfold blockTransition
  have hempty : (Finset.univ.filter fun f : Fin k → Fin N ↦
      (Finset.univ.image f).card = j) = ∅ := by
    refine Finset.filter_eq_empty_iff.mpr fun f _ ↦ ?_
    intro hcard
    have hle := Finset.card_image_le (s := (Finset.univ : Finset (Fin k))) (f := f)
    simp only [Finset.card_univ, Fintype.card_fin] at hle
    omega
  rw [hempty]
  simp

/-- The one-generation block-count operator, indexed by lineage count. -/
noncomputable def blockMatrix (n N : ℕ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  fun k j ↦ blockTransition N k j

/-- The coalescent's generator on lineage counts: `-d_k` on the diagonal and `d_k` one step
down, which is K-G (2.10) with `q_{ξη}` summed over the covers of a `k`-block state. -/
noncomputable def blockGenerator (n : ℕ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  fun k j ↦ if (j : ℕ) = (k : ℕ) then -deathRate k
    else if (j : ℕ) + 1 = (k : ℕ) then deathRate k else 0

theorem blockTransition_nonneg {N k j : ℕ} (hN : 0 < N) : 0 ≤ blockTransition N k j := by
  unfold blockTransition
  have : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  positivity

/-- **Each row of the one-generation operator is a probability distribution.**  The entries
above the diagonal vanish and the rest sum to one, which is `BlockCountMatrix.sum_blockTransition`
read on the full index set. -/
theorem sum_row_blockMatrix {n N : ℕ} (hN : 0 < N) (k : Fin (n + 1)) :
    ∑ j : Fin (n + 1), blockMatrix n N k j = 1 := by
  classical
  have hk : (k : ℕ) ≤ n := Nat.lt_succ_iff.mp k.isLt
  have hsplit : ∑ j : Fin (n + 1), blockTransition N (k : ℕ) (j : ℕ)
      = ∑ j ∈ Finset.range ((k : ℕ) + 1), blockTransition N (k : ℕ) j := by
    rw [Fin.sum_univ_eq_sum_range (fun j ↦ blockTransition N (k : ℕ) j) (n + 1)]
    refine (Finset.sum_subset ?_ ?_).symm
    · intro x hx
      have hx' := Finset.mem_range.mp hx
      exact Finset.mem_range.mpr (by omega)
    · intro x hx hnot
      have hxk : (k : ℕ) < x := by
        by_contra hc
        exact hnot (Finset.mem_range.mpr (by omega))
      exact blockTransition_eq_zero_of_lt hxk
  unfold blockMatrix
  rw [hsplit]
  exact sum_blockTransition hN

/-- **The one-generation operator is a contraction**, K-G (2.12): a stochastic matrix has
row-sum norm one. -/
theorem norm_blockMatrix_le_one {n N : ℕ} (hN : 0 < N) : ‖blockMatrix n N‖ ≤ 1 := by
  classical
  refine linfty_norm_le_of_rows (C := 1) fun k ↦ ?_
  rw [← NNReal.coe_le_coe]
  push_cast
  have hnorm : ∀ j : Fin (n + 1), ‖blockMatrix n N k j‖ = blockMatrix n N k j := fun j ↦
    Real.norm_of_nonneg (blockTransition_nonneg hN)
  simp only [hnorm]
  exact le_of_eq (sum_row_blockMatrix hN k)

end Coalescent

end Descent
