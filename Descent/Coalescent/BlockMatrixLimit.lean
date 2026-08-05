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
- `sum_range_blockTransition`: the mass below the subdiagonal is the two-drop probability.
- `row_diff_bound`: **the row is within `(d_k/N)² + 2k⁴/N²` of `1 + N⁻¹Q`**, which is
  K-G (2.11) for the block-count chain.

What is left is to read `row_diff_bound` as a norm bound through `linfty_norm_le_of_rows` --
the same conversion `norm_blockMatrix_le_one` already makes -- and hand the result to
`SemigroupLimit.tendsto_pow_of_expansion`.  The `Fin (n+1)` index arithmetic that conversion
needs, matching `k - 1` against the generator's subdiagonal, is the only thing between here
and `P_N^N → exp Q` for the whole chain.
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

/-! ### The row difference

`WrightFisher.coalescenceProb_le` and `.le_coalescenceProb` place the diagonal within
`(d_k/N)²/2` of `1 - d_k/N`.  `BlockCountMatrix.twoDropProb_le` places everything below the
subdiagonal within `k⁴/N²` of zero.  The subdiagonal is then whatever the row has left, and
the row sums to one -- so its deviation is at most the sum of the other two.  Three bounds,
one subtraction, and the row is within `O(N⁻²)` of `1 + N⁻¹Q`. -/

/-- The mass strictly below the subdiagonal is the two-drop probability. -/
theorem sum_range_blockTransition {N k : ℕ} (hN : 0 < N) :
    ∑ j ∈ Finset.range (k - 1), blockTransition N k j
      = ((Finset.univ.filter fun f : Fin k → Fin N ↦
          (Finset.univ.image f).card + 2 ≤ k).card : ℝ) / (N : ℝ) ^ k := by
  classical
  have hmem : ∀ f ∈ (Finset.univ.filter fun f : Fin k → Fin N ↦
      (Finset.univ.image f).card + 2 ≤ k), (Finset.univ.image f).card ∈ Finset.range (k - 1) := by
    intro f hf
    have := (Finset.mem_filter.mp hf).2
    exact Finset.mem_range.mpr (by omega)
  have hpart := Finset.card_eq_sum_card_fiberwise hmem
  have hfib : ∀ j ∈ Finset.range (k - 1),
      ((Finset.univ.filter fun f : Fin k → Fin N ↦
          (Finset.univ.image f).card + 2 ≤ k).filter
        fun f ↦ (Finset.univ.image f).card = j)
      = Finset.univ.filter fun f : Fin k → Fin N ↦ (Finset.univ.image f).card = j := by
    intro j hj
    have hjk : j + 2 ≤ k := by
      have := Finset.mem_range.mp hj
      omega
    ext f
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, and_iff_right_iff_imp]
    intro hcard
    omega
  rw [hpart, Finset.sum_congr rfl (fun j hj ↦ congrArg Finset.card (hfib j hj))]
  unfold blockTransition
  rw [← Finset.sum_div, ← Nat.cast_sum]

/-- **The row is within `O(N⁻²)` of `1 + N⁻¹Q`.**  The diagonal deviates by at most
`(d_k/N)²/2`, the tail by at most `k⁴/N²`, and the subdiagonal -- being one minus the other
two -- by at most their sum. -/
theorem row_diff_bound {N k : ℕ} (hN : 0 < N) (hk : 2 ≤ k) (hkN : k ≤ N) :
    |blockTransition N k k - (1 - deathRate k / (N : ℝ))|
        + |blockTransition N k (k - 1) - deathRate k / (N : ℝ)|
        + ∑ j ∈ Finset.range (k - 1), blockTransition N k j
      ≤ (deathRate k / (N : ℝ)) ^ 2 + 2 * ((k : ℝ) ^ 4 / (N : ℝ) ^ 2) := by
  classical
  have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  set T := ∑ j ∈ Finset.range (k - 1), blockTransition N k j with hT
  have hTnn : 0 ≤ T := Finset.sum_nonneg fun j _ ↦ blockTransition_nonneg hN
  have hTle : T ≤ (k : ℝ) ^ 4 / (N : ℝ) ^ 2 := by
    rw [hT, sum_range_blockTransition hN]
    exact twoDropProb_le hN hk
  have hdiag : blockTransition N k k = noCoalescenceProb N k := blockTransition_diag hN
  have hup : 1 - noCoalescenceProb N k ≤ deathRate k / (N : ℝ) := coalescenceProb_le hN hkN
  have hlow : deathRate k / (N : ℝ) - (deathRate k / (N : ℝ)) ^ 2 / 2
      ≤ 1 - noCoalescenceProb N k := le_coalescenceProb hN hkN
  have hA : |blockTransition N k k - (1 - deathRate k / (N : ℝ))|
      ≤ (deathRate k / (N : ℝ)) ^ 2 / 2 := by
    rw [hdiag, abs_le]
    constructor <;> linarith
  -- the subdiagonal is one minus the diagonal minus the tail
  have hsub : blockTransition N k (k - 1) = 1 - blockTransition N k k - T := by
    have hsplit : ∑ j ∈ Finset.range (k + 1), blockTransition N k j
        = (∑ j ∈ Finset.range (k - 1), blockTransition N k j)
          + blockTransition N k (k - 1) + blockTransition N k k := by
      have h1 : k + 1 = (k - 1) + 1 + 1 := by omega
      rw [h1, Finset.sum_range_succ, Finset.sum_range_succ]
      congr 2
      omega
    have := sum_blockTransition (N := N) (k := k) hN
    rw [hsplit] at this
    linarith
  have hB : |blockTransition N k (k - 1) - deathRate k / (N : ℝ)|
      ≤ (deathRate k / (N : ℝ)) ^ 2 / 2 + T := by
    rw [hsub, hdiag, abs_le]
    constructor <;> linarith
  linarith

/-! ### The row bound as a norm bound -/

/-- Rows `0` and `1` are exact: with no pair to merge, the generation cannot lose a lineage,
so the operator agrees with `1 + N⁻¹Q` there on the nose. -/
theorem row_small {N k : ℕ} (hN : 0 < N) (hk : k ≤ 1) : blockTransition N k k = 1 := by
  rw [blockTransition_diag hN]
  interval_cases k
  · simp
  · exact noCoalescenceProb_one hN

/-- **Every row of the difference is `O(N⁻²)`**, with a constant depending only on the state
count.  For `k ≥ 2` this is `row_diff_bound` with `d_k ≤ n²`; for `k ≤ 1` the row vanishes,
because a generation with fewer than two lineages cannot lose one. -/
theorem row_sum_diff_le {n N : ℕ} (hN : 0 < N) (hnN : n ≤ N) (k : Fin (n + 1)) :
    ∑ j : Fin (n + 1),
        |blockMatrix n N k j - ((1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
          + (1 / (N : ℝ)) • blockGenerator n) k j|
      ≤ 3 * (n : ℝ) ^ 4 / (N : ℝ) ^ 2 := by
  classical
  have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hkn : (k : ℕ) ≤ n := Nat.lt_succ_iff.mp k.isLt
  have hnR : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  -- the entries of the comparison operator
  have hentry : ∀ j : Fin (n + 1),
      ((1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) + (1 / (N : ℝ)) • blockGenerator n) k j
        = (if (k : ℕ) = (j : ℕ) then 1 else 0)
          + (1 / (N : ℝ)) * (if (j : ℕ) = (k : ℕ) then -deathRate (k : ℕ)
              else if (j : ℕ) + 1 = (k : ℕ) then deathRate (k : ℕ) else 0) := by
    intro j
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, blockGenerator]
    congr 1
    rw [Matrix.one_apply]
    by_cases h : k = j
    · simp [h]
    · have : (k : ℕ) ≠ (j : ℕ) := fun hc ↦ h (Fin.ext hc)
      simp [h, this]
  by_cases hk1 : (k : ℕ) ≤ 1
  · -- the row is exact
    have hdiag : blockTransition N (k : ℕ) (k : ℕ) = 1 := row_small hN hk1
    have hd0 : deathRate (k : ℕ) = 0 := by
      unfold deathRate
      interval_cases h : (k : ℕ) <;> norm_num
    have hzero : ∀ j : Fin (n + 1),
        blockMatrix n N k j - ((1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
          + (1 / (N : ℝ)) • blockGenerator n) k j = 0 := by
      intro j
      rw [hentry j]
      unfold blockMatrix
      by_cases h : (j : ℕ) = (k : ℕ)
      · rw [h, hdiag, hd0]
        simp
      · have hother : blockTransition N (k : ℕ) (j : ℕ) = 0 := by
          have hsum := sum_row_blockMatrix hN k
          have hnn : ∀ i : Fin (n + 1), 0 ≤ blockMatrix n N k i := fun i ↦
            blockTransition_nonneg hN
          have hle : blockMatrix n N k j + blockMatrix n N k k
              ≤ ∑ i : Fin (n + 1), blockMatrix n N k i := by
            have hjk : j ≠ k := fun hc ↦ h (by rw [hc])
            calc blockMatrix n N k j + blockMatrix n N k k
                = ∑ i ∈ ({j, k} : Finset (Fin (n + 1))), blockMatrix n N k i := by
                  rw [Finset.sum_insert (by simpa using hjk), Finset.sum_singleton]
              _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
                  (fun i _ _ ↦ hnn i)
          have hkk : blockMatrix n N k k = 1 := hdiag
          have := hnn j
          unfold blockMatrix at hle hkk
          linarith
        rw [hother, hd0]
        simp [h, Ne.symm h, show ¬((k : ℕ) = (j : ℕ)) from fun hc ↦ h hc.symm]
    simp only [hzero, abs_zero, Finset.sum_const_zero]
    positivity
  · -- the row with a subdiagonal
    push_neg at hk1
    have hk2 : 2 ≤ (k : ℕ) := hk1
    have hkN : (k : ℕ) ≤ N := le_trans hkn hnN
    have hbound := row_diff_bound (N := N) (k := (k : ℕ)) hN hk2 hkN
    -- the index one below `k`
    have hk1lt : (k : ℕ) - 1 < n + 1 := by omega
    set k' : Fin (n + 1) := ⟨(k : ℕ) - 1, hk1lt⟩ with hk'
    have hkk' : k ≠ k' := by
      intro hc
      have : (k : ℕ) = (k : ℕ) - 1 := congrArg Fin.val hc
      omega
    have hsplit : ∑ j : Fin (n + 1),
        |blockMatrix n N k j - ((1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
          + (1 / (N : ℝ)) • blockGenerator n) k j|
        = |blockMatrix n N k k - ((1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
            + (1 / (N : ℝ)) • blockGenerator n) k k|
          + |blockMatrix n N k k' - ((1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
            + (1 / (N : ℝ)) • blockGenerator n) k k'|
          + ∑ j ∈ (Finset.univ.erase k).erase k',
              |blockMatrix n N k j - ((1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
                + (1 / (N : ℝ)) • blockGenerator n) k j| := by
      rw [← Finset.sum_erase_add _ _ (Finset.mem_univ k),
        ← Finset.sum_erase_add _ _ (Finset.mem_erase.mpr ⟨Ne.symm hkk', Finset.mem_univ k'⟩)]
      ring
    have hrest : ∀ j ∈ (Finset.univ.erase k).erase k',
        |blockMatrix n N k j - ((1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
          + (1 / (N : ℝ)) • blockGenerator n) k j| = blockMatrix n N k j := by
      intro j hj
      have hjk' : j ≠ k' := (Finset.mem_erase.mp hj).1
      have hjk : j ≠ k := (Finset.mem_erase.mp (Finset.mem_erase.mp hj).2).1
      have h2 : ¬((j : ℕ) = (k : ℕ)) := fun hc ↦ hjk (Fin.ext hc)
      have h1 : ¬((k : ℕ) = (j : ℕ)) := fun hc ↦ h2 hc.symm
      have h3 : ¬((j : ℕ) + 1 = (k : ℕ)) := by
        intro hc
        exact hjk' (Fin.ext (by simp only [hk']; omega))
      rw [hentry j]
      simp only [h1, h2, h3, if_false, mul_zero, add_zero, sub_zero]
      exact abs_of_nonneg (blockTransition_nonneg hN)
    have hdiagval : ((1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
        + (1 / (N : ℝ)) • blockGenerator n) k k = 1 - deathRate (k : ℕ) / (N : ℝ) := by
      rw [hentry k]
      simp
      ring
    have hsubval : ((1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
        + (1 / (N : ℝ)) • blockGenerator n) k k' = deathRate (k : ℕ) / (N : ℝ) := by
      have h1 : ¬((k : ℕ) = (k' : ℕ)) := by simp only [hk']; omega
      have h2 : ¬((k' : ℕ) = (k : ℕ)) := fun hc ↦ h1 hc.symm
      have h3 : (k' : ℕ) + 1 = (k : ℕ) := by simp only [hk']; omega
      rw [hentry k']
      simp only [h1, h2, h3, if_false, if_true, if_pos]
      ring
    have hk'val : (k' : ℕ) = (k : ℕ) - 1 := rfl
    have hTeq : ∑ j ∈ (Finset.univ.erase k).erase k', blockMatrix n N k j
        = ∑ j ∈ Finset.range ((k : ℕ) - 1), blockTransition N (k : ℕ) j := by
      have hall : ∑ j : Fin (n + 1), blockMatrix n N k j = 1 := sum_row_blockMatrix hN k
      have hsp : ∑ j : Fin (n + 1), blockMatrix n N k j
          = blockMatrix n N k k + blockMatrix n N k k'
            + ∑ j ∈ (Finset.univ.erase k).erase k', blockMatrix n N k j := by
        rw [← Finset.sum_erase_add _ _ (Finset.mem_univ k),
          ← Finset.sum_erase_add _ _ (Finset.mem_erase.mpr ⟨Ne.symm hkk', Finset.mem_univ k'⟩)]
        ring
      have hsum2 : ∑ j ∈ Finset.range ((k : ℕ) + 1), blockTransition N (k : ℕ) j = 1 :=
        sum_blockTransition hN
      have hsp2 : ∑ j ∈ Finset.range ((k : ℕ) + 1), blockTransition N (k : ℕ) j
          = (∑ j ∈ Finset.range ((k : ℕ) - 1), blockTransition N (k : ℕ) j)
            + blockTransition N (k : ℕ) ((k : ℕ) - 1) + blockTransition N (k : ℕ) (k : ℕ) := by
        have h1 : (k : ℕ) + 1 = ((k : ℕ) - 1) + 1 + 1 := by omega
        rw [h1, Finset.sum_range_succ, Finset.sum_range_succ]
        congr 2
        omega
      rw [hsp] at hall
      rw [hsp2] at hsum2
      unfold blockMatrix at hall
      rw [hk'val] at hall
      linarith
    rw [hsplit, hdiagval, hsubval, Finset.sum_congr rfl hrest, hTeq]
    unfold blockMatrix
    rw [hk'val]
    have hdle : deathRate (k : ℕ) ≤ (n : ℝ) ^ 2 := by
      unfold deathRate
      have hkR : (k : ℝ) ≤ (n : ℝ) := by exact_mod_cast hkn
      have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg _
      nlinarith
    have hd0 : 0 ≤ deathRate (k : ℕ) := le_of_lt (deathRate_pos hk2)
    have hsq : (deathRate (k : ℕ) / (N : ℝ)) ^ 2 ≤ (n : ℝ) ^ 4 / (N : ℝ) ^ 2 := by
      rw [div_pow, div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [sq_nonneg (deathRate (k : ℕ)), pow_le_pow_left hd0 hdle 2]
    have hk4 : ((k : ℕ) : ℝ) ^ 4 ≤ (n : ℝ) ^ 4 := by
      have hkR : ((k : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hkn
      have hk0 : (0 : ℝ) ≤ ((k : ℕ) : ℝ) := Nat.cast_nonneg _
      exact pow_le_pow_left hk0 hkR 4
    have hNsq : (0 : ℝ) < (N : ℝ) ^ 2 := by positivity
    have hdiv : 2 * (((k : ℕ) : ℝ) ^ 4 / (N : ℝ) ^ 2) ≤ 2 * ((n : ℝ) ^ 4 / (N : ℝ) ^ 2) := by
      have := div_le_div_of_nonneg_right hk4 hNsq
      linarith [div_le_div_of_nonneg_right hk4 hNsq]
    have hfinal : 3 * (n : ℝ) ^ 4 / (N : ℝ) ^ 2
        = (n : ℝ) ^ 4 / (N : ℝ) ^ 2 + 2 * ((n : ℝ) ^ 4 / (N : ℝ) ^ 2) := by ring
    rw [hfinal]
    linarith [hbound]

end Coalescent

end Descent
