/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.DensityRelativeEntropy
import Mathlib.Probability.Distributions.Gaussian.Real

assert_below Descent.Decision Descent.Program

/-!
The explicit density ratio for a Gaussian variance perturbation is connected to
the actual Gaussian probability measure. Normalization and integrability follow
from that density calculation, supplying concrete building blocks for spectral
coordinates of the covariance-perturbation experiment.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.GaussianVarianceDensity

open scoped NNReal
open MeasureTheory ProbabilityTheory DensityRelativeEntropy

/-- Density ratio of a centered Gaussian of variance a against the standard Gaussian. -/
noncomputable def ratio (a x : ℝ) : ℝ :=
  (Real.sqrt a)⁻¹ * Real.exp ((1 - a⁻¹) * x ^ 2 / 2)

/-- Every nondegenerate variance gives a strictly positive density ratio. -/
theorem ratio_pos (a x : ℝ) (ha : 0 < a) : 0 < ratio a x :=
  mul_pos (inv_pos.mpr (Real.sqrt_pos.mpr ha)) (Real.exp_pos _)

/-- The density ratio is continuous in the observed coordinate. -/
theorem ratio_continuous (a : ℝ) : Continuous (ratio a) := by
  unfold ratio
  fun_prop

/-- Exact density multiplication for the actual one-dimensional Gaussian experiment. -/
theorem density_identity (a : ℝ) (ha : 0 < a) (x : ℝ) :
    gaussianPDFReal 0 1 x * ratio a x = gaussianPDFReal 0 ⟨a, ha.le⟩ x := by
  have he : -(x ^ 2) / 2 + (1 - a⁻¹) * x ^ 2 / 2 = -(x ^ 2) / (2 * a) := by
    field_simp
    ring
  simp only [gaussianPDFReal, NNReal.coe_one, NNReal.coe_mk, mul_one, sub_zero, ratio]
  rw [Real.sqrt_mul (by positivity : 0 ≤ 2 * Real.pi) a, mul_inv]
  calc
    _ = (Real.sqrt (2 * Real.pi))⁻¹ * (Real.sqrt a)⁻¹ *
        Real.exp (-(x ^ 2) / 2 + (1 - a⁻¹) * x ^ 2 / 2) := by
      rw [Real.exp_add]
      ring
    _ = _ := by rw [he]

/-- Changing the standard Gaussian by this ratio gives exactly the stated Gaussian measure. -/
theorem densityLaw_eq_gaussian (a : ℝ) (ha : 0 < a) :
    densityLaw (gaussianReal 0 1) (ratio a) = gaussianReal 0 ⟨a, ha.le⟩ := by
  have hv : (⟨a, ha.le⟩ : ℝ≥0) ≠ 0 := by
    intro h
    have hh := congrArg (fun v : ℝ≥0 ↦ (v : ℝ)) h
    exact ha.ne' hh
  rw [densityLaw, gaussianReal_of_var_ne_zero 0 one_ne_zero,
    gaussianReal_of_var_ne_zero 0 hv,
    ← withDensity_mul volume (measurable_gaussianPDF 0 1)
      (ratio_continuous a).measurable.ennreal_ofReal]
  congr 1
  funext x
  change ENNReal.ofReal (gaussianPDFReal 0 1 x) * ENNReal.ofReal (ratio a x) =
    ENNReal.ofReal (gaussianPDFReal 0 ⟨a, ha.le⟩ x)
  rw [← ENNReal.ofReal_mul (gaussianPDFReal_nonneg _ _ _), density_identity a ha x]

/-- Integrability is derived from the actual Gaussian density, not postulated for the ratio. -/
theorem ratio_integrable (a : ℝ) (ha : 0 < a) : Integrable (ratio a) (gaussianReal 0 1) := by
  rw [gaussianReal_of_var_ne_zero 0 one_ne_zero,
    integrable_withDensity_iff_integrable_smul' (measurable_gaussianPDF 0 1)
      (Filter.Eventually.of_forall (fun _ ↦ gaussianPDF_lt_top))]
  simp only [toReal_gaussianPDF, smul_eq_mul, density_identity a ha]
  exact integrable_gaussianPDFReal _ _

/-- Exact expectation one follows from the known normalized Gaussian experiment. -/
theorem ratio_integral (a : ℝ) (ha : 0 < a) : (∫ x, ratio a x ∂gaussianReal 0 1) = 1 := by
  rw [integral_gaussianReal_eq_integral_smul one_ne_zero]
  simp only [smul_eq_mul, density_identity a ha]
  apply integral_gaussianPDFReal_eq_one
  intro h
  have hh := congrArg (fun v : ℝ≥0 ↦ (v : ℝ)) h
  exact ha.ne' hh

end Descent.Portability.GaussianVarianceDensity
