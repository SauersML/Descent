/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.HWEJumpRepresentation

assert_below Descent.Decision Descent.Program

/-!
All integer moments and their integrability for an actual signed exponential image
of a Gaussian. The formulas are obtained from the Gaussian integral and the two
pushforward measures, including zero variance and zero amplitude.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.GaussianImageMoments

open scoped NNReal
open MeasureTheory ProbabilityTheory HWEAmplitudeWeakLimit HWETiltedKernelLaw SymmetricImageLaw

/-- Integer powers of the amplitude are exact exponential Gaussian test functions. -/
theorem amplitude_power (c x : ℝ) (n : ℕ) :
    (c * Real.exp (-x)) ^ n = c ^ n * Real.exp (-(n : ℝ) * x) := by
  rw [mul_pow, ← Real.exp_nat_mul]
  congr 2
  ring

/-- Every integer power of the Gaussian amplitude is actually integrable. -/
theorem amplitude_power_integrable (mean : ℝ) (v : ℝ≥0) (c : ℝ) (n : ℕ) :
    Integrable (fun x ↦ (c * Real.exp (-x)) ^ n) (gaussianReal mean v) := by
  simp_rw [amplitude_power]
  exact (integrable_exp_mul_gaussianReal (μ := mean) (v := v) (-(n : ℝ))).const_mul (c ^ n)

/-- Its moment follows from the actual Gaussian moment-generating integral. -/
theorem amplitude_power_integral (mean : ℝ) (v : ℝ≥0) (c : ℝ) (n : ℕ) :
    (∫ x, (c * Real.exp (-x)) ^ n ∂gaussianReal mean v) =
      c ^ n * Real.exp (mean * (-(n : ℝ)) + (v : ℝ) * (n : ℝ) ^ 2 / 2) := by
  simp_rw [amplitude_power]
  rw [integral_const_mul]
  have hm := congrFun (mgf_fun_id_gaussianReal (μ := mean) (v := v)) (-(n : ℝ))
  simpa only [mgf, neg_sq] using congrArg (fun z : ℝ ↦ c ^ n * z) hm

/-- Integrability of the actual pushforward mark distribution, not only its parametrization. -/
theorem image_power_integrable (mean : ℝ) (v : ℝ≥0) (c : ℝ) (n : ℕ) :
    Integrable (fun y : ℝ ↦ y ^ n)
      ((gaussianReal mean v).map (fun x ↦ c * Real.exp (-x))) := by
  apply (integrable_map_measure (by fun_prop) (by fun_prop)).mpr
  exact amplitude_power_integrable mean v c n

/-- Exact moment under the actual pushforward distribution. -/
theorem image_power_integral (mean : ℝ) (v : ℝ≥0) (c : ℝ) (n : ℕ) :
    (∫ y : ℝ, y ^ n ∂((gaussianReal mean v).map (fun x ↦ c * Real.exp (-x)))) =
      c ^ n * Real.exp (mean * (-(n : ℝ)) + (v : ℝ) * (n : ℝ) ^ 2 / 2) := by
  rw [integral_map (by fun_prop) (by fun_prop)]
  exact amplitude_power_integral mean v c n

/-- Both sign classes give integrable moments under the constructed fair-sign mixture. -/
theorem signed_power_integrable (mean : ℝ) (v : ℝ≥0) (c : ℝ) (n : ℕ) :
    Integrable (fun y : ℝ ↦ y ^ n)
      (pairLaw ⟨gaussianReal mean v, inferInstance⟩ (amplitudeMap c) : Measure ℝ) := by
  simp only [pairLaw, blend, ProbabilityMeasure.coe_mk, ProbabilityMeasure.map,
    amplitudeMap, ContinuousMap.coe_mk, ← neg_mul]
  exact ((image_power_integrable mean v c n).smul_measure ENNReal.ofReal_ne_top).add_measure
    ((image_power_integrable mean v (-c) n).smul_measure ENNReal.ofReal_ne_top)

/-- Complete signed Gaussian-image moment formula for every natural order. -/
theorem signed_power_integral (mean : ℝ) (v : ℝ≥0) (c : ℝ) (n : ℕ) :
    (∫ y : ℝ, y ^ n ∂(pairLaw ⟨gaussianReal mean v, inferInstance⟩
      (amplitudeMap c) : Measure ℝ)) =
        (c ^ n + (-c) ^ n) / 2 *
          Real.exp (mean * (-(n : ℝ)) + (v : ℝ) * (n : ℝ) ^ 2 / 2) := by
  simp only [pairLaw, blend, ProbabilityMeasure.coe_mk, ProbabilityMeasure.map,
    amplitudeMap, ContinuousMap.coe_mk, ← neg_mul]
  rw [integral_add_measure
    ((image_power_integrable mean v c n).smul_measure ENNReal.ofReal_ne_top)
    ((image_power_integrable mean v (-c) n).smul_measure ENNReal.ofReal_ne_top)]
  simp only [integral_smul_measure, smul_eq_mul, image_power_integral]
  norm_num
  ring

end Descent.Portability.GaussianImageMoments
