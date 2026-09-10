/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.OptimalMeasurementAllocation
import Mathlib.MeasureTheory.Function.L2Space

assert_below Descent.Decision Descent.Program

/-!
A joint certificate for model discrepancy, unresolved target bias, measurement
noise, and numerical error. The root mean squared error is an actual integral
on the measurement probability space. Independence is not presumed to remove
cross terms; the sharper squared identity requires proved orthogonality.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.CombinedPredictionCertificate

open MeasureTheory
open scoped RealInnerProductSpace

variable {Ω E : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

omit [IsProbabilityMeasure μ] in
theorem norm_sq_integral (f : Lp E 2 μ) : ‖f‖ ^ 2 = ∫ ω, ‖f ω‖ ^ 2 ∂μ := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  simp only [real_inner_self_eq_norm_sq]

omit [IsProbabilityMeasure μ] in
theorem rmse_eq_norm (f : Lp E 2 μ) : Real.sqrt (∫ ω, ‖f ω‖ ^ 2 ∂μ) = ‖f‖ := by
  rw [← norm_sq_integral, Real.sqrt_sq (norm_nonneg f)]

theorem norm_le_of_ae_bound (f : Lp E 2 μ) (bound : ℝ) (hb : 0 ≤ bound)
    (hf : ∀ᵐ ω ∂μ, ‖f ω‖ ≤ bound) : ‖f‖ ≤ bound := by
  have hi : Integrable (fun ω ↦ ‖f ω‖ ^ 2) μ := by
    simpa only [real_inner_self_eq_norm_sq] using L2.integrable_inner (𝕜 := ℝ) f f
  have hs : ‖f‖ ^ 2 ≤ bound ^ 2 := by
    rw [norm_sq_integral]
    calc
      (∫ ω, ‖f ω‖ ^ 2 ∂μ) ≤ ∫ _ : Ω, bound ^ 2 ∂μ := by
        apply integral_mono_ae hi (integrable_const _)
        filter_upwards [hf] with ω hω
        nlinarith [norm_nonneg (f ω)]
      _ = bound ^ 2 := by simp
  nlinarith [norm_nonneg f]

/-- The four-term certificate in root mean squared target error. -/
theorem combined_rmse (error model bias noise numerical : Lp E 2 μ)
    (modelBound biasBound varianceBound numericalBound : ℝ)
    (hsplit : error = model + bias + noise + numerical)
    (hm : 0 ≤ modelBound) (hb : 0 ≤ biasBound) (hn : 0 ≤ numericalBound)
    (hmodel : ∀ᵐ ω ∂μ, ‖model ω‖ ≤ modelBound)
    (hbias : ∀ᵐ ω ∂μ, ‖bias ω‖ ≤ biasBound)
    (hnoise : (∫ ω, ‖noise ω‖ ^ 2 ∂μ) ≤ varianceBound)
    (hnumerical : ∀ᵐ ω ∂μ, ‖numerical ω‖ ≤ numericalBound) :
    Real.sqrt (∫ ω, ‖error ω‖ ^ 2 ∂μ) ≤
      modelBound + biasBound + Real.sqrt varianceBound + numericalBound := by
  have hm' := norm_le_of_ae_bound model modelBound hm hmodel
  have hb' := norm_le_of_ae_bound bias biasBound hb hbias
  have hn' := norm_le_of_ae_bound numerical numericalBound hn hnumerical
  have hv : ‖noise‖ ≤ Real.sqrt varianceBound := by
    rw [← norm_sq_integral] at hnoise
    exact (Real.le_sqrt (norm_nonneg noise) ((sq_nonneg _).trans hnoise)).mpr hnoise
  rw [rmse_eq_norm, hsplit]
  calc
    ‖model + bias + noise + numerical‖ ≤ ‖model + bias + noise‖ + ‖numerical‖ := norm_add_le _ _
    _ ≤ ‖model + bias‖ + ‖noise‖ + ‖numerical‖ := add_le_add_right (norm_add_le _ _) _
    _ ≤ ‖model‖ + ‖bias‖ + ‖noise‖ + ‖numerical‖ := by
      exact add_le_add_right (add_le_add_right (norm_add_le _ _) _) _
    _ ≤ modelBound + biasBound + Real.sqrt varianceBound + numericalBound := by linarith

omit [IsProbabilityMeasure μ] in
/-- Orthogonal bias and noise add in squared risk, with no unproved cancellation. -/
theorem orthogonal_squared_error (bias noise : Lp E 2 μ) (horthogonal : inner ℝ bias noise = 0) :
    (∫ ω, ‖(bias + noise) ω‖ ^ 2 ∂μ) =
      (∫ ω, ‖bias ω‖ ^ 2 ∂μ) + ∫ ω, ‖noise ω‖ ^ 2 ∂μ := by
  simp only [← norm_sq_integral]
  rw [norm_add_sq_real, horthogonal]
  ring

open OptimalMeasurementAllocation

/-- With the optimal positive-mode allocation, the measurement term has the
explicit budget dependence from the report's allocation theorem. -/
theorem allocated_combined_rmse {I : Type*} [Fintype I] [Nonempty I]
    (amplitude cost : I → ℝ) (budget : ℝ)
    (ha : ∀ mode, 0 < amplitude mode) (hc : ∀ mode, 0 < cost mode) (hbudget : 0 < budget)
    (error model bias noise numerical : Lp E 2 μ) (modelBound biasBound numericalBound : ℝ)
    (hsplit : error = model + bias + noise + numerical)
    (hm : 0 ≤ modelBound) (hb : 0 ≤ biasBound) (hn : 0 ≤ numericalBound)
    (hmodel : ∀ᵐ ω ∂μ, ‖model ω‖ ≤ modelBound)
    (hbias : ∀ᵐ ω ∂μ, ‖bias ω‖ ≤ biasBound)
    (hnoise : (∫ ω, ‖noise ω‖ ^ 2 ∂μ) ≤
      variance amplitude (optimalEffort amplitude cost budget))
    (hnumerical : ∀ᵐ ω ∂μ, ‖numerical ω‖ ≤ numericalBound) :
    Real.sqrt (∫ ω, ‖error ω‖ ^ 2 ∂μ) ≤ modelBound + biasBound +
      weightedAmplitude amplitude cost / Real.sqrt budget + numericalBound := by
  have hh := combined_rmse error model bias noise numerical modelBound biasBound
    (variance amplitude (optimalEffort amplitude cost budget)) numericalBound hsplit
      hm hb hn hmodel hbias hnoise hnumerical
  rw [optimal_variance amplitude cost budget ha hc hbudget, Real.sqrt_div (sq_nonneg _),
    Real.sqrt_sq (weightedAmplitude_pos amplitude cost ha hc).le] at hh
  exact hh

end Descent.Portability.CombinedPredictionCertificate
