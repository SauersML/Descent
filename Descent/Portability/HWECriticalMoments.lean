/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.GaussianCompoundMoments
import Descent.Portability.HWEJumpMoments

assert_below Descent.Decision Descent.Program

/-!
The constructed heterogeneous HWE critical law is centered and has variance one.
Its full-distribution fourth cumulant at critical block intensity r is exp(4K)/r.
All moments used here are finite Lebesgue integrals under that actual limit law.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.HWECriticalMoments

open scoped NNReal MeasureTheory
open MeasureTheory ProbabilityTheory HWECriticalLimitLaw HWEJumpMoments GaussianCompoundMoments

/-- The actual critical law has integrable powers through order four. -/
theorem critical_power_integrable (K : ℝ≥0) (c : ℝ) (n : ℕ) (hn : n ≤ 4) :
    Integrable (fun x : ℝ ↦ x ^ n) (criticalLaw K c : Measure ℝ) :=
  gaussian_compound_power_integrable (gaussianVariance K) (jumpIntensity K c) (jumpLaw K c)
    (jump_power_integrable K c) (jump_mean K c) n hn

/-- The complete limit, including both its Gaussian and jump components, is centered. -/
theorem critical_mean (K : ℝ≥0) (c : ℝ) :
    (∫ x : ℝ, x ∂(criticalLaw K c : Measure ℝ)) = 0 :=
  gaussian_compound_mean (gaussianVariance K) (jumpIntensity K c) (jumpLaw K c)
    (jump_power_integrable K c) (jump_mean K c)

/-- No variance is lost in the near-balanced critical weak limit. -/
theorem critical_second (K : ℝ≥0) (c : ℝ) (hc : c ≠ 0) :
    (∫ x : ℝ, x ^ 2 ∂(criticalLaw K c : Measure ℝ)) = 1 := by
  change (∫ x : ℝ, x ^ 2 ∂(gaussianReal 0 (gaussianVariance K) ∗
    CompoundPoissonMarkLaw.compoundMeasure (jumpIntensity K c) (jumpLaw K c))) = _
  rw [gaussian_compound_second _ _ _ (jump_power_integrable K c) (jump_mean K c),
    weighted_jump_second K c hc]
  change 1 - Real.exp (-4 * (K : ℝ)) + Real.exp (-4 * (K : ℝ)) = 1
  ring

/-- Actual probabilistic variance of the identity under the critical law. -/
theorem critical_variance (K : ℝ≥0) (c : ℝ) (hc : c ≠ 0) :
    variance (fun x : ℝ ↦ x) (criticalLaw K c : Measure ℝ) = 1 := by
  rw [variance_eq_integral (by fun_prop), critical_mean]
  simpa only [sub_zero] using critical_second K c hc

/-- Fourth cumulant of the full limit, evaluated from its actual probability integrals. -/
theorem critical_fourth_cumulant (K : ℝ≥0) (r : ℝ) (hr : 0 < r) :
    (∫ x : ℝ, x ^ 4 ∂(criticalLaw K (1 / Real.sqrt r) : Measure ℝ)) -
      3 * (∫ x : ℝ, x ^ 2 ∂(criticalLaw K (1 / Real.sqrt r) : Measure ℝ)) ^ 2 =
        Real.exp (4 * (K : ℝ)) / r := by
  change (∫ x : ℝ, x ^ 4 ∂(gaussianReal 0 (gaussianVariance K) ∗
    CompoundPoissonMarkLaw.compoundMeasure (jumpIntensity K (1 / Real.sqrt r))
      (jumpLaw K (1 / Real.sqrt r)))) - 3 * (∫ x : ℝ, x ^ 2
    ∂(gaussianReal 0 (gaussianVariance K) ∗
      CompoundPoissonMarkLaw.compoundMeasure (jumpIntensity K (1 / Real.sqrt r))
        (jumpLaw K (1 / Real.sqrt r)))) ^ 2 = _
  rw [gaussian_compound_fourth_cumulant _ _ _
    (jump_power_integrable K _) (jump_mean K _), weighted_jump_fourth K r hr]

/-- The exact fourth moment is strictly above the centered unit Gaussian value. -/
theorem critical_fourth (K : ℝ≥0) (r : ℝ) (hr : 0 < r) :
    (∫ x : ℝ, x ^ 4 ∂(criticalLaw K (1 / Real.sqrt r) : Measure ℝ)) =
      3 + Real.exp (4 * (K : ℝ)) / r := by
  have hc : 1 / Real.sqrt r ≠ 0 := one_div_ne_zero (Real.sqrt_ne_zero'.mpr hr)
  have hh := critical_fourth_cumulant K r hr
  rw [critical_second K _ hc] at hh
  linarith

/-- The actual critical law cannot be the centered unit Gaussian. -/
theorem critical_ne_standardGaussian (K : ℝ≥0) (r : ℝ) (hr : 0 < r) :
    (criticalLaw K (1 / Real.sqrt r) : Measure ℝ) ≠ gaussianReal 0 1 := by
  intro he
  have hh := critical_fourth K r hr
  rw [he, GaussianPolynomialMoments.fourth_moment] at hh
  have hp : 0 < Real.exp (4 * (K : ℝ)) / r := div_pos (Real.exp_pos _) hr
  norm_num at hh
  linarith

/-- Mean and variance force any putative Gaussian representation to be the standard one. -/
theorem critical_ne_gaussian (K : ℝ≥0) (r : ℝ) (hr : 0 < r) (m : ℝ) (v : ℝ≥0) :
    (criticalLaw K (1 / Real.sqrt r) : Measure ℝ) ≠ gaussianReal m v := by
  intro he
  have hc : 1 / Real.sqrt r ≠ 0 := one_div_ne_zero (Real.sqrt_ne_zero'.mpr hr)
  have hm := critical_mean K (1 / Real.sqrt r)
  rw [he, integral_id_gaussianReal] at hm
  have hv := critical_variance K (1 / Real.sqrt r) hc
  rw [he, variance_fun_id_gaussianReal] at hv
  have hv' : v = 1 := NNReal.eq hv
  exact critical_ne_standardGaussian K r hr (by simpa only [hm, hv'] using he)

/-- Non-Gaussianity in Mathlib's intrinsic Gaussian-measure definition. -/
theorem critical_not_isGaussian (K : ℝ≥0) (r : ℝ) (hr : 0 < r) :
    ¬IsGaussian (criticalLaw K (1 / Real.sqrt r) : Measure ℝ) := by
  intro h
  letI := h
  have he := IsGaussian.map_eq_gaussianReal
    (μ := (criticalLaw K (1 / Real.sqrt r) : Measure ℝ)) (ContinuousLinearMap.id ℝ ℝ)
  change Measure.map (id : ℝ → ℝ) (criticalLaw K (1 / Real.sqrt r) : Measure ℝ) = _ at he
  rw [Measure.map_id] at he
  exact critical_ne_gaussian K r hr _ _ he

end Descent.Portability.HWECriticalMoments
