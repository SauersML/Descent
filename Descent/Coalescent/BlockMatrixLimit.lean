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

/-- Dividing both sides of an inequality by a fixed positive number. -/
private theorem div_le_div_of_nonneg_right' {a b c : ℝ} (h : a ≤ b) (hc : 0 < c) :
    a / c ≤ b / c := by
  gcongr

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
      have h01 : (k : ℕ) = 0 ∨ (k : ℕ) = 1 := by omega
      rcases h01 with h | h <;> rw [h] <;>
        simp [deathRate, Descent.Core.pairCount]
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
          rw [hsum] at hle
          have hkk : blockMatrix n N k k = 1 := hdiag
          have hj := hnn j
          simp only [blockMatrix, Matrix.of_apply] at hle hkk hj
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
      simp only [blockMatrix, Matrix.of_apply] at hall ⊢
      rw [hk'val] at hall
      linarith
    rw [hsplit, hdiagval, hsubval, Finset.sum_congr rfl hrest, hTeq]
    simp only [blockMatrix, Matrix.of_apply]
    rw [hk'val]
    have hkR : ((k : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hkn
    have hk0 : (0 : ℝ) ≤ ((k : ℕ) : ℝ) := Nat.cast_nonneg _
    have hdle : deathRate (k : ℕ) ≤ (n : ℝ) ^ 2 := by
      simp only [deathRate, Descent.Core.pairCount]
      nlinarith [sq_nonneg (((k : ℕ) : ℝ) - (n : ℝ)), sq_nonneg ((n : ℝ) - 1)]
    have hd0 : 0 ≤ deathRate (k : ℕ) := le_of_lt (deathRate_pos hk2)
    have hNsq : (0 : ℝ) < (N : ℝ) ^ 2 := by positivity
    have hsq : (deathRate (k : ℕ) / (N : ℝ)) ^ 2 ≤ (n : ℝ) ^ 4 / (N : ℝ) ^ 2 := by
      rw [div_pow]
      have : deathRate (k : ℕ) ^ 2 ≤ (n : ℝ) ^ 4 := by nlinarith
      exact div_le_div_of_nonneg_right' this hNsq
    have hk4 : 2 * (((k : ℕ) : ℝ) ^ 4 / (N : ℝ) ^ 2) ≤ 2 * ((n : ℝ) ^ 4 / (N : ℝ) ^ 2) := by
      have h4 : ((k : ℕ) : ℝ) ^ 4 ≤ (n : ℝ) ^ 4 := by
        have hsq2 : ((k : ℕ) : ℝ) ^ 2 ≤ (n : ℝ) ^ 2 := by nlinarith
        nlinarith [sq_nonneg (((k : ℕ) : ℝ) ^ 2), sq_nonneg ((n : ℝ) ^ 2)]
      have := div_le_div_of_nonneg_right' h4 hNsq
      linarith
    have hfinal : 3 * (n : ℝ) ^ 4 / (N : ℝ) ^ 2
        = (n : ℝ) ^ 4 / (N : ℝ) ^ 2 + 2 * ((n : ℝ) ^ 4 / (N : ℝ) ^ 2) := by ring
    rw [hfinal]
    linarith [hbound]


/-! ### `Q` factors through a stochastic matrix, and the limit -/

/-- Real-valued form of the row bound, which is the form a `C/N²` estimate arrives in. -/
theorem linfty_norm_le_of_rows' {m : Type*} [Fintype m] [DecidableEq m]
    {A : Matrix m m ℝ} {C : ℝ} (hC : 0 ≤ C) (h : ∀ i, ∑ j, |A i j| ≤ C) : ‖A‖ ≤ C := by
  have h' : ∀ i, ∑ j, ‖A i j‖₊ ≤ C.toNNReal := by
    intro i
    rw [← NNReal.coe_le_coe, Real.coe_toNNReal C hC]
    push_cast
    simpa [Real.norm_eq_abs] using h i
  simpa [Real.coe_toNNReal C hC] using linfty_norm_le_of_rows h'

/-- **The rate ladder is increasing**: more lineages, more pairs. -/
theorem deathRate_mono {k n : ℕ} (h : k ≤ n) : deathRate k ≤ deathRate n := by
  simp only [deathRate, Descent.Core.pairCount]
  have hkR : ((k : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast h
  have hk0 : (0 : ℝ) ≤ ((k : ℕ) : ℝ) := Nat.cast_nonneg _
  nlinarith

/-- **The stochastic matrix `Q` factors through**, `S = 1 + Q/d_n`.

Uniformisation: divide the generator by the largest exit rate and add the identity.  Every
entry is then non-negative -- the diagonal because `d_k ≤ d_n`, the subdiagonal because
`d_k ≥ 0` -- and each row still sums to one, because `Q`'s rows sum to zero. -/
noncomputable def blockStochastic (n : ℕ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  1 + (deathRate n)⁻¹ • blockGenerator n

/-- The entries of `S`, read off. -/
theorem blockStochastic_apply {n : ℕ} (k j : Fin (n + 1)) :
    blockStochastic n k j
      = (if (k : ℕ) = (j : ℕ) then 1 else 0)
        + (deathRate n)⁻¹ * (if (j : ℕ) = (k : ℕ) then -deathRate (k : ℕ)
            else if (j : ℕ) + 1 = (k : ℕ) then deathRate (k : ℕ) else 0) := by
  simp only [blockStochastic, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, blockGenerator]
  congr 1
  rw [Matrix.one_apply]
  by_cases h : k = j
  · simp [h]
  · have : (k : ℕ) ≠ (j : ℕ) := fun hc ↦ h (Fin.ext hc)
    simp [h, this]

/-- **`S` is a contraction**, because its rows are probability distributions. -/
theorem norm_blockStochastic_le_one {n : ℕ} (hn : 2 ≤ n) : ‖blockStochastic n‖ ≤ 1 := by
  classical
  have han : 0 < deathRate n := deathRate_pos hn
  refine linfty_norm_le_of_rows' zero_le_one fun k ↦ ?_
  have hkn : (k : ℕ) ≤ n := Nat.lt_succ_iff.mp k.isLt
  have hdk0 : 0 ≤ deathRate (k : ℕ) := by
    simp only [deathRate, Descent.Core.pairCount]
    rcases Nat.eq_zero_or_pos (k : ℕ) with h | h
    · simp [h]
    · have : (1 : ℝ) ≤ ((k : ℕ) : ℝ) := by exact_mod_cast h
      nlinarith
  have hratio : deathRate (k : ℕ) / deathRate n ≤ 1 :=
    (div_le_one han).mpr (deathRate_mono hkn)
  have hratio0 : 0 ≤ deathRate (k : ℕ) / deathRate n := by positivity
  by_cases hk0 : (k : ℕ) = 0
  · have hall : ∀ j : Fin (n + 1), |blockStochastic n k j| = if k = j then 1 else 0 := by
      intro j
      rw [blockStochastic_apply]
      by_cases h : (j : ℕ) = (k : ℕ)
      · have hkj : k = j := Fin.ext h.symm
        simp [h, hkj, hk0, deathRate, Descent.Core.pairCount]
      · have hkj : ¬ k = j := fun hc ↦ h (by rw [hc])
        have h3 : ¬((j : ℕ) + 1 = (k : ℕ)) := by omega
        simp [h, h3, hkj, fun hc : (k : ℕ) = (j : ℕ) ↦ h hc.symm]
    simp only [hall]
    rw [Finset.sum_ite_eq Finset.univ k (fun _ ↦ (1 : ℝ))]
    simp
  · -- the row has a subdiagonal entry
    have hk1lt : (k : ℕ) - 1 < n + 1 := by omega
    set k' : Fin (n + 1) := ⟨(k : ℕ) - 1, hk1lt⟩ with hk'
    have hkk' : k ≠ k' := by
      intro hc
      have : (k : ℕ) = (k : ℕ) - 1 := congrArg Fin.val hc
      omega
    have hrest : ∀ j ∈ (Finset.univ.erase k).erase k', |blockStochastic n k j| = 0 := by
      intro j hj
      have hjk' : j ≠ k' := (Finset.mem_erase.mp hj).1
      have hjk : j ≠ k := (Finset.mem_erase.mp (Finset.mem_erase.mp hj).2).1
      have h2 : ¬((j : ℕ) = (k : ℕ)) := fun hc ↦ hjk (Fin.ext hc)
      have h1 : ¬((k : ℕ) = (j : ℕ)) := fun hc ↦ h2 hc.symm
      have h3 : ¬((j : ℕ) + 1 = (k : ℕ)) := by
        intro hc
        exact hjk' (Fin.ext (by simp only [hk']; omega))
      rw [blockStochastic_apply]
      simp [h1, h2, h3]
    have hdiag : blockStochastic n k k = 1 - deathRate (k : ℕ) / deathRate n := by
      rw [blockStochastic_apply]
      simp only [if_pos rfl]
      field_simp
    have hsub : blockStochastic n k k' = deathRate (k : ℕ) / deathRate n := by
      have h1 : ¬((k : ℕ) = (k' : ℕ)) := by simp only [hk']; omega
      have h2 : ¬((k' : ℕ) = (k : ℕ)) := fun hc ↦ h1 hc.symm
      have h3 : (k' : ℕ) + 1 = (k : ℕ) := by simp only [hk']; omega
      rw [blockStochastic_apply, if_neg h1, if_neg h2, if_pos h3]
      field_simp
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ k),
      ← Finset.sum_erase_add _ _ (Finset.mem_erase.mpr ⟨Ne.symm hkk', Finset.mem_univ k'⟩),
      Finset.sum_congr rfl hrest]
    rw [hdiag, hsub, abs_of_nonneg (by linarith : (0:ℝ) ≤ 1 - deathRate (k:ℕ) / deathRate n),
      abs_of_nonneg hratio0]
    simp

/-- **`Q = d_n · (S - 1)`**, the factorisation `norm_exp_smul_sub_one_le_one` wants. -/
theorem blockGenerator_eq_smul {n : ℕ} (hn : 2 ≤ n) :
    blockGenerator n = deathRate n • (blockStochastic n - 1) := by
  have han : deathRate n ≠ 0 := ne_of_gt (deathRate_pos hn)
  unfold blockStochastic
  rw [add_sub_cancel_left, smul_smul, mul_inv_cancel₀ han, one_smul]

/-- **The generator generates a contraction semigroup**, `‖exp(tQ)‖ ≤ 1` for `t ≥ 0`. -/
theorem norm_exp_smul_blockGenerator_le_one {n : ℕ} (hn : 2 ≤ n) {t : ℝ} (ht : 0 ≤ t) :
    ‖exp ℝ (t • blockGenerator n)‖ ≤ 1 := by
  rw [blockGenerator_eq_smul hn, smul_smul]
  exact norm_exp_smul_sub_one_le_one _ (norm_blockStochastic_le_one hn) _
    (mul_nonneg ht (le_of_lt (deathRate_pos hn)))

/-- **The one-generation operator**, extended by the identity at `N = 0` so that it is a
contraction for every `N`.  The limit is taken along `N → ∞`, so the value there is inert. -/
noncomputable def blockOperator (n N : ℕ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  if N = 0 then 1 else blockMatrix n N

/-- **K-G (2.14) for the block count: `P_N^N → exp Q`.**

This is the theorem the whole file exists for.  A Wright--Fisher population of size `N`,
watched for `N` generations, has its sample's ancestral lineage count converge in law to
Kingman's pure-death chain -- the one with rate `d_k = k(k-1)/2` out of level `k`.

Every hypothesis is now a theorem of this corpus rather than an assumption:
`norm_blockMatrix_le_one` for the contraction, `norm_exp_smul_blockGenerator_le_one` for the
limit semigroup, and `row_sum_diff_le` for the one-generation expansion `P_N = 1 + N⁻¹Q +
O(N⁻²)`.  The `O(N⁻²)` is where the biology sits: the error is the probability that two
distinct pairs of lineages coalesce in the same generation, and it is `O(N⁻²)` because two
independent coincidences are needed.  That is why the coalescent is binary.

    Empirical status: DERIVED -- from the Wright-Fisher reproduction mechanism, with no
    coefficient posited.  What is assumed is the mechanism: uniform, independent parent
    choice in a constant population of size N.  Which populations reproduce that way is
    an empirical question the mechanism modules record. -/
theorem tendsto_blockOperator_pow {n : ℕ} (hn : 2 ≤ n) :
    Filter.Tendsto (fun N : ℕ ↦ blockOperator n N ^ N) Filter.atTop
      (nhds (exp ℝ (blockGenerator n))) := by
  refine tendsto_pow_of_expansion (blockGenerator n) (3 * (n : ℝ) ^ 4) (by positivity)
    (blockOperator n) (fun N ↦ ?_) (fun N ↦ ?_) ?_
  · -- contraction
    unfold blockOperator
    by_cases hN : N = 0
    · simp [hN]
    · rw [if_neg hN]
      exact norm_blockMatrix_le_one (Nat.pos_of_ne_zero hN)
  · -- the limit semigroup is a contraction
    exact norm_exp_smul_blockGenerator_le_one hn (by positivity)
  · -- the one-generation expansion
    filter_upwards [Filter.eventually_ge_atTop (max 1 n)] with N hN
    have hN1 : 0 < N := lt_of_lt_of_le Nat.zero_lt_one (le_trans (le_max_left _ _) hN)
    have hnN : n ≤ N := le_trans (le_max_right _ _) hN
    have hC : (0 : ℝ) ≤ 3 * (n : ℝ) ^ 4 / (N : ℝ) ^ 2 := by positivity
    refine linfty_norm_le_of_rows' hC fun k ↦ ?_
    simpa using row_sum_diff_le hN1 hnN k

end Coalescent

end Descent
