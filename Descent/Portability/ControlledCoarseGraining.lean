/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.DynamicBlindness
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

assert_below Descent.Decision Descent.Program

/-!
A quantitative defect identity for lifting coarse observables through known
fine and coarse dynamics. The operators may act on spaces of different sizes.
The contraction corollary requires contraction in the chosen operator norm;
that hypothesis is automatic for Markov observable semigroups in supremum norm.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.ControlledCoarseGraining

open MeasureTheory
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

noncomputable def evolution (generator : E →L[ℝ] E) (time : ℝ) : E →L[ℝ] E :=
  NormedSpace.exp ℝ (time • generator)

noncomputable def defect (fine : E →L[ℝ] E) (coarse : F →L[ℝ] F)
    (lift : F →L[ℝ] E) : F →L[ℝ] E := fine.comp lift - lift.comp coarse

noncomputable def defectIntegrand (fine : E →L[ℝ] E) (coarse : F →L[ℝ] F)
    (lift : F →L[ℝ] E) (horizon time : ℝ) : F →L[ℝ] E :=
  (evolution fine (horizon - time)).comp ((defect fine coarse lift).comp (evolution coarse time))

theorem evolution_continuous (generator : E →L[ℝ] E) : Continuous (evolution generator) := by
  exact continuous_iff_continuousAt.mpr fun time ↦
    (hasDerivAt_exp_smul_const generator time).continuousAt

theorem defectIntegrand_continuous (fine : E →L[ℝ] E) (coarse : F →L[ℝ] F)
    (lift : F →L[ℝ] E) (horizon : ℝ) : Continuous (defectIntegrand fine coarse lift horizon) := by
  exact ((evolution_continuous fine).comp (continuous_const.sub continuous_id)).clm_comp
    (continuous_const.clm_comp (evolution_continuous coarse))

private theorem bridge_derivative (fine : E →L[ℝ] E) (coarse : F →L[ℝ] F)
    (lift : F →L[ℝ] E) (horizon time : ℝ) :
    HasDerivAt (fun moment ↦ (evolution fine (horizon - moment)).comp
      (lift.comp (evolution coarse moment)))
      (-defectIntegrand fine coarse lift horizon time) time := by
  have hf := (hasDerivAt_exp_smul_const fine (horizon - time)).scomp time
    ((hasDerivAt_id time).const_sub horizon)
  have hc := (hasDerivAt_const time lift).clm_comp (hasDerivAt_exp_smul_const' coarse time)
  have hd := hf.clm_comp hc
  convert hd using 1
  ext vector
  simp [defectIntegrand, defect, evolution, Function.comp_def, ContinuousLinearMap.mul_def]
  abel

/-- Exact Duhamel formula: all coarse prediction error is transported generator defect. -/
theorem defect_integral_identity (fine : E →L[ℝ] E) (coarse : F →L[ℝ] F)
    (lift : F →L[ℝ] E) (horizon : ℝ) :
    (evolution fine horizon).comp lift - lift.comp (evolution coarse horizon) =
      ∫ time in 0..horizon, defectIntegrand fine coarse lift horizon time := by
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun time _ ↦ bridge_derivative fine coarse lift horizon time)
    ((defectIntegrand_continuous fine coarse lift horizon).neg.intervalIntegrable 0 horizon)
  simp only [intervalIntegral.integral_neg, evolution, sub_self, zero_smul,
    NormedSpace.exp_zero, ContinuousLinearMap.one_def, ContinuousLinearMap.id_comp,
    sub_zero, ContinuousLinearMap.comp_id]
    at hFTC
  have heq := congrArg Neg.neg hFTC
  simpa only [neg_neg, neg_sub, evolution] using heq.symm

/-- A contraction semigroup turns the exact defect identity into a linear-in-time bound. -/
theorem contraction_defect_bound (fine : E →L[ℝ] E) (coarse : F →L[ℝ] F)
    (lift : F →L[ℝ] E) (horizon : ℝ) (hhorizon : 0 ≤ horizon)
    (hfine : ∀ time, 0 ≤ time → ‖evolution fine time‖ ≤ 1)
    (hcoarse : ∀ time, 0 ≤ time → ‖evolution coarse time‖ ≤ 1) :
    ‖(evolution fine horizon).comp lift - lift.comp (evolution coarse horizon)‖ ≤
      horizon * ‖defect fine coarse lift‖ := by
  rw [defect_integral_identity]
  have hbound : ∀ time ∈ Set.uIoc (0 : ℝ) horizon,
      ‖defectIntegrand fine coarse lift horizon time‖ ≤ ‖defect fine coarse lift‖ := by
    intro time htime
    rw [Set.uIoc_of_le hhorizon] at htime
    have hfirst := hfine (horizon - time) (by linarith [htime.2])
    have hsecond := hcoarse time (le_of_lt htime.1)
    apply le_trans ((evolution fine (horizon - time)).opNorm_comp_le _)
    apply le_trans (mul_le_mul_of_nonneg_left
      ((defect fine coarse lift).opNorm_comp_le _) (norm_nonneg _))
    calc
      _ ≤ 1 * (‖defect fine coarse lift‖ * 1) := by gcongr
      _ = _ := by ring
  have hi := intervalIntegral.norm_integral_le_of_norm_le_const hbound
  simpa only [sub_zero, abs_of_nonneg hhorizon, mul_comm] using hi

/-- Zero generator defect gives exact closure at every time. -/
theorem exact_closure_of_zero_defect (fine : E →L[ℝ] E) (coarse : F →L[ℝ] F)
    (lift : F →L[ℝ] E) (hdefect : defect fine coarse lift = 0) (horizon : ℝ) :
    (evolution fine horizon).comp lift = lift.comp (evolution coarse horizon) := by
  apply sub_eq_zero.mp
  rw [defect_integral_identity]
  simp [defectIntegrand, hdefect]

end Descent.Portability.ControlledCoarseGraining
