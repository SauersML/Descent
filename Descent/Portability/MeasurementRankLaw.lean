/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.SpectralMeasurementMinimax
import Mathlib.LinearAlgebra.Matrix.Rank

assert_below Descent.Decision Descent.Program

/-!
The exact number of ideal adaptive linear measurements needed to remove
target uncertainty is the rank of the actual target map. The active eigenvalue
count is derived from its Gram matrix and rank-nullity.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.MeasurementRankLaw

open FiniteTargetSpectrum SpectralMeasurementMinimax AdaptiveLinearMeasurements

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [CompleteSpace F]

noncomputable def targetRank (L : E →L[ℝ] F) : ℕ :=
  Module.finrank ℝ (LinearMap.range L.toLinearMap)

omit [CompleteSpace F] in
theorem targetRank_le_dimension (L : E →L[ℝ] F) : targetRank L ≤ Module.finrank ℝ E := by
  have h := L.toLinearMap.finrank_range_add_finrank_ker
  dsimp [targetRank]
  omega

theorem gram_kernel (L : E →L[ℝ] F) :
    LinearMap.ker (gram L).toLinearMap = LinearMap.ker L.toLinearMap := by
  ext v
  change gram L v = 0 ↔ L v = 0
  constructor
  · intro hv
    have h := L.apply_norm_sq_eq_inner_adjoint_right v
    change ‖L v‖ ^ 2 = inner ℝ v (gram L v) at h
    rw [hv, inner_zero_right] at h
    exact norm_eq_zero.mp (by nlinarith [norm_nonneg (L v)])
  · intro hv
    simp [gram, hv]

theorem gram_rank (L : E →L[ℝ] F) :
    Module.finrank ℝ (LinearMap.range (gram L).toLinearMap) = targetRank L := by
  have hL := L.toLinearMap.finrank_range_add_finrank_ker
  have hG := (gram L).toLinearMap.finrank_range_add_finrank_ker
  rw [gram_kernel] at hG
  dsimp [targetRank]
  omega

theorem gram_matrix (L : E →L[ℝ] F) :
    LinearMap.toMatrix (rightBasis L).toBasis (rightBasis L).toBasis (gram L).toLinearMap =
      Matrix.diagonal (squaredSingularValues L) := by
  ext i j
  rw [LinearMap.toMatrix_apply]
  change (rightBasis L).toBasis.repr (gram L (rightBasis L j)) i = _
  rw [OrthonormalBasis.coe_toBasis_repr_apply, ← coordinate_repr,
    gram_rightBasis, map_smul, coordinate_basis]
  by_cases hij : i = j <;> simp [Matrix.diagonal, hij]

theorem targetRank_eq_active (L : E →L[ℝ] F) :
    targetRank L = Fintype.card
      {i : Fin (Module.finrank ℝ E) // squaredSingularValues L i ≠ 0} := by
  classical
  have h := Matrix.rank_eq_finrank_range_toLin
    (LinearMap.toMatrix (rightBasis L).toBasis (rightBasis L).toBasis (gram L).toLinearMap)
    (rightBasis L).toBasis (rightBasis L).toBasis
  rw [Matrix.toLin_toMatrix, gram_matrix, Matrix.rank_diagonal, gram_rank] at h
  exact h.symm

theorem eigenvalue_zero_iff_rank_le (L : E →L[ℝ] F) (i : Fin (Module.finrank ℝ E)) :
    squaredSingularValues L i = 0 ↔ targetRank L ≤ i.val := by
  classical
  rw [targetRank_eq_active]
  constructor
  · intro hi
    have hindex (j : {j : Fin (Module.finrank ℝ E) // squaredSingularValues L j ≠ 0}) :
        j.val.val < i.val := by
      by_contra hn
      have hj : squaredSingularValues L j.val ≤ 0 := by
        simpa only [hi] using squaredSingularValues_antitone L (Nat.le_of_not_gt hn)
      exact j.property (le_antisymm hj (squaredSingularValues_nonneg L _))
    let indexMap := fun j : {j : Fin (Module.finrank ℝ E) // squaredSingularValues L j ≠ 0} ↦
      (⟨j.val.val, hindex j⟩ : Fin i.val)
    have hh := Fintype.card_le_of_injective indexMap (by
      intro j k h
      apply Subtype.ext
      apply Fin.ext
      exact congrArg (fun z : Fin i.val ↦ z.val) h)
    simpa only [Fintype.card_fin] using hh
  · intro hcount
    by_contra hi
    have hipos : 0 < squaredSingularValues L i :=
      lt_of_le_of_ne (squaredSingularValues_nonneg L _) (Ne.symm hi)
    let indexMap : Fin (i.val + 1) →
        {j : Fin (Module.finrank ℝ E) // squaredSingularValues L j ≠ 0} := fun j ↦
      ⟨⟨j.val, by have hj := j.isLt; have hi' := i.isLt; omega⟩, by
        apply ne_of_gt
        apply hipos.trans_le
        apply squaredSingularValues_antitone L
        change j.val ≤ i.val
        have hj := j.isLt
        omega⟩
    have hh := Fintype.card_le_of_injective indexMap (by
      intro j k h
      apply Fin.ext
      exact congrArg (fun z ↦ z.val.val) h)
    simp only [Fintype.card_fin] at hh
    omega

theorem residualEigenvalue_zero_iff (L : E →L[ℝ] F) (q : ℕ) :
    residualEigenvalue L q = 0 ↔ targetRank L ≤ q := by
  by_cases hq : q < Module.finrank ℝ E
  · simpa only [residualEigenvalue, dif_pos hq] using eigenvalue_zero_iff_rank_le L ⟨q, hq⟩
  · simp only [residualEigenvalue, dif_neg hq, true_iff]
    exact (targetRank_le_dimension L).trans (Nat.le_of_not_gt hq)

theorem zero_risk_iff (L : E →L[ℝ] F) (q : ℕ) (radius : ℝ) (hr : 0 < radius) :
    (∃ procedure : Procedure E F q, UniformRisk procedure L radius 0) ↔ targetRank L ≤ q := by
  constructor
  · intro h
    have hl := (adaptive_minimax_all_budgets L q radius hr.le).2 h
    apply (residualEigenvalue_zero_iff L q).mp
    have hn : 0 ≤ residualEigenvalue L q := by
      unfold residualEigenvalue
      split_ifs <;> simp [squaredSingularValues_nonneg]
    have hrsq : 0 < radius ^ 2 := sq_pos_of_pos hr
    nlinarith
  · intro h
    have hh := (adaptive_minimax_all_budgets L q radius hr.le).1
    rw [(residualEigenvalue_zero_iff L q).mpr h, mul_zero] at hh
    exact hh

/-- For a positive uncertainty radius the minimal exact measurement budget is
the dimension of the target image, including adaptive strategies. -/
theorem minimal_exact_measurement_count (L : E →L[ℝ] F) (radius : ℝ) (hr : 0 < radius) :
    IsLeast {q : ℕ | ∃ procedure : Procedure E F q, UniformRisk procedure L radius 0}
      (targetRank L) := by
  refine ⟨(zero_risk_iff L (targetRank L) radius hr).mpr le_rfl, ?_⟩
  intro q hq
  exact (zero_risk_iff L q radius hr).mp hq

end Descent.Portability.MeasurementRankLaw
