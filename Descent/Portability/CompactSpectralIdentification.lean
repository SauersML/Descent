/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.CompactMeasurementMinimax

assert_below Descent.Decision Descent.Program

/-!
The compact deflation scales are genuine singular values of the original target:
each positive scale has a unit right eigenvector of its original Gram operator.
The exact adaptive error is therefore a spectral law, not a renamed optimization.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.CompactSpectralIdentification

open scoped BigOperators
open CompactSingularSequence CompactTargetDeflation AdaptiveLinearMeasurements

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

/-- Earlier deflations leave a later leading direction's target image unchanged. -/
theorem direction_image (L : E →L[ℝ] F) (hc : IsCompactOperator L) (i : ℕ) :
    (residual L hc i).1 (direction L hc i) = L (direction L hc i) := by
  rw [residual_decomposition]
  have hz : (∑ j ∈ Finset.range i, inner ℝ (direction L hc j) (direction L hc i) •
      (residual L hc j).1 (direction L hc j)) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    have ho : inner ℝ (direction L hc j) (direction L hc i) = 0 := by
      rw [real_inner_comm]
      exact directions_orthogonal L hc j i (Finset.mem_range.mp hj)
    rw [ho, zero_smul]
  rw [hz, sub_zero]

/-- Cross terms in the original target obey the true singular equation. -/
theorem original_cross (L : E →L[ℝ] F) (hc : IsCompactOperator L) (i : ℕ) (x : E) :
    inner ℝ (L (direction L hc i)) (L x) =
      ‖(residual L hc i).1‖ ^ 2 * inner ℝ (direction L hc i) x := by
  induction i using Nat.strong_induction_on generalizing x with
  | h i ih =>
    have hdecomp : L x = (residual L hc i).1 x +
        ∑ j ∈ Finset.range i, inner ℝ (direction L hc j) x •
          (residual L hc j).1 (direction L hc j) := by
      rw [residual_decomposition]
      abel
    rw [hdecomp, inner_add_right, inner_sum]
    have hz : (∑ j ∈ Finset.range i, inner ℝ (L (direction L hc i))
        (inner ℝ (direction L hc j) x •
          (residual L hc j).1 (direction L hc j))) = 0 := by
      apply Finset.sum_eq_zero
      intro j hj
      have hji := Finset.mem_range.mp hj
      have ho : inner ℝ (direction L hc j) (direction L hc i) = 0 := by
        rw [real_inner_comm]
        exact directions_orthogonal L hc j i hji
      have horth : inner ℝ (L (direction L hc i)) (L (direction L hc j)) = 0 := by
        rw [real_inner_comm, ih j hji (direction L hc i), ho, mul_zero]
      rw [inner_smul_right, direction_image, horth, mul_zero]
    rw [hz, add_zero, ← direction_image L hc i]
    exact singular_cross _ _ _ (direction_spec L hc i).2.2

/-- These are eigenvectors of L†L itself, not only of intermediate residuals. -/
theorem original_gram (L : E →L[ℝ] F) (hc : IsCompactOperator L) (i : ℕ) :
    L.adjoint (L (direction L hc i)) = ‖(residual L hc i).1‖ ^ 2 • direction L hc i := by
  apply ext_inner_right ℝ
  intro x
  rw [L.adjoint_inner_left, real_inner_smul_left, original_cross]

/-- Singular scales are the nonincreasing norms of compact residuals, indexed from zero. -/
noncomputable def singularValue (L : E →L[ℝ] F) (hc : IsCompactOperator L) (i : ℕ) : ℝ :=
  ‖(residual L hc i).1‖

theorem singularValue_nonneg (L : E →L[ℝ] F) (hc : IsCompactOperator L) (i : ℕ) :
    0 ≤ singularValue L hc i := norm_nonneg _

theorem singularValue_antitone (L : E →L[ℝ] F) (hc : IsCompactOperator L) :
    Antitone (singularValue L hc) := residual_norm_antitone L hc

/-- Every positive scale is an attained singular value of the original target operator. -/
theorem positive_singularValue (L : E →L[ℝ] F) (hc : IsCompactOperator L) (i : ℕ)
    (hi : 0 < singularValue L hc i) :
    ‖direction L hc i‖ = 1 ∧ ‖L (direction L hc i)‖ = singularValue L hc i ∧
      L.adjoint (L (direction L hc i)) = singularValue L hc i ^ 2 • direction L hc i := by
  have hR : (residual L hc i).1 ≠ 0 := norm_pos_iff.mp hi
  refine ⟨leading_unit _ _ hR, ?_, original_gram L hc i⟩
  rw [← direction_image]
  exact (direction_spec L hc i).2.1

/-- Exact compact spectral minimax law for every finite noiseless adaptive query budget. -/
theorem adaptive_spectral_minimax (L : E →L[ℝ] F) (hc : IsCompactOperator L)
    (q : ℕ) (radius : ℝ) (hr : 0 ≤ radius) :
    IsLeast {risk : ℝ | ∃ procedure : Procedure E F q, UniformRisk procedure L radius risk}
      (radius ^ 2 * singularValue L hc q ^ 2) :=
  CompactMeasurementMinimax.adaptive_minimax L hc q radius hr

end Descent.Portability.CompactSpectralIdentification
