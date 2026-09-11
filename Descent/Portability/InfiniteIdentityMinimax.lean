/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.AdaptiveLinearMeasurements

assert_below Descent.Decision Descent.Program

/-!
The identity target on an infinite-dimensional inner product space retains the
entire squared uncertainty radius after any finite deterministic adaptive query
budget. This shows why compactness in the continuum theorem is substantive.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.InfiniteIdentityMinimax

open AdaptiveLinearMeasurements TargetUncertainty

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Finitely many scalar linear observations leave a unit direction unidentified. -/
theorem infinite_common_kernel (hinfinite : ¬ FiniteDimensional ℝ E) (q : ℕ)
    (questions : Fin q → E →L[ℝ] ℝ) :
    ∃ v : E, ‖v‖ = 1 ∧ ∀ i, questions i v = 0 := by
  let Q : E →ₗ[ℝ] (Fin q → ℝ) := LinearMap.pi (fun i ↦ (questions i).toLinearMap)
  have hker : LinearMap.ker Q ≠ ⊥ := by
    intro hbot
    exact hinfinite (FiniteDimensional.of_injective Q (LinearMap.ker_eq_bot.mp hbot))
  obtain ⟨v, hv, hvne⟩ := (LinearMap.ker Q).ne_bot_iff.mp hker
  have hz : ∀ i, questions i v = 0 := by
    intro i
    exact congrFun (LinearMap.mem_ker.mp hv) i
  refine ⟨‖v‖⁻¹ • v, ?_, ?_⟩
  · simp only [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_nonneg (norm_nonneg v),
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr hvne)]
  · intro i
    simp only [map_smul, hz i, smul_zero]

/-- Adaptivity cannot reduce identity-target worst-case loss on the full ball. -/
theorem adaptive_lower (hinfinite : ¬ FiniteDimensional ℝ E) (q : ℕ)
    (procedure : Procedure E E q) (radius risk : ℝ) (hr : 0 ≤ radius)
    (h : UniformRisk procedure (ContinuousLinearMap.id ℝ E) radius risk) :
    radius ^ 2 ≤ risk := by
  obtain ⟨v, hv, hz⟩ := infinite_common_kernel hinfinite q procedure.zeroQuestions
  have hpluszero : ∀ i, procedure.zeroQuestions i (radius • v) = 0 := by
    intro i
    simp only [map_smul, hz i, smul_zero]
  have hminuszero : ∀ i, procedure.zeroQuestions i (-(radius • v)) = 0 := by
    intro i
    simp only [map_neg, hpluszero i, neg_zero]
  have hnorm : ‖radius • v‖ ≤ radius := by
    simp only [norm_smul, Real.norm_eq_abs, abs_of_nonneg hr, hv, mul_one]
    exact le_rfl
  have hp := h (radius • v) hnorm
  have hm := h (-(radius • v)) (by simpa only [norm_neg] using hnorm)
  rw [procedure.run_eq_zeroPrediction _ hpluszero] at hp
  rw [procedure.run_eq_zeroPrediction _ hminuszero] at hm
  have hb := two_point_lower (radius • v) procedure.zeroPrediction risk hp hm
  simpa only [norm_smul, Real.norm_eq_abs, abs_of_nonneg hr, hv, mul_one] using hb

/-- Exact minimax error is the full squared radius for every finite query budget. -/
theorem identity_minimax (hinfinite : ¬ FiniteDimensional ℝ E) (q : ℕ)
    (radius : ℝ) (hr : 0 ≤ radius) :
    IsLeast {risk : ℝ | ∃ procedure : Procedure E E q,
      UniformRisk procedure (ContinuousLinearMap.id ℝ E) radius risk} (radius ^ 2) := by
  refine ⟨⟨Procedure.fixed (fun _ ↦ 0) (fun _ ↦ 0), ?_⟩, ?_⟩
  · intro x hx
    simp only [Procedure.fixed_run, ContinuousLinearMap.id_apply, sub_zero]
    exact (sq_le_sq₀ (norm_nonneg _) hr).mpr hx
  · rintro risk ⟨procedure, h⟩
    exact adaptive_lower hinfinite q procedure radius risk hr h

end Descent.Portability.InfiniteIdentityMinimax
