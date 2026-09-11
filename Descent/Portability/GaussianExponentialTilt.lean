/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.HWEAmplitudeWeakLimit

assert_below Descent.Decision Descent.Program

/-!
Exponential tilting of the actual real Gaussian measure, derived by completing
the square in its density. The integral identity includes zero variance and
arbitrary real test functions; no tilted Gaussian law is supplied as a premise.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.GaussianExponentialTilt

open scoped NNReal
open MeasureTheory ProbabilityTheory

/-- Completing the square gives the exact tilted Gaussian density. -/
theorem density_tilt (v : ℝ≥0) (hv : v ≠ 0) (a x : ℝ) :
    Real.exp (a * x) * gaussianPDFReal 0 v x =
      Real.exp (a ^ 2 * (v : ℝ) / 2) * gaussianPDFReal (a * (v : ℝ)) v x := by
  have hv' : (v : ℝ) ≠ 0 := by exact_mod_cast hv
  have he : a * x + (-(x - 0) ^ 2 / (2 * (v : ℝ))) =
      a ^ 2 * (v : ℝ) / 2 + (-(x - a * (v : ℝ)) ^ 2 / (2 * (v : ℝ))) := by
    field_simp
    <;> ring
  unfold gaussianPDFReal
  calc
    _ = (Real.sqrt (2 * Real.pi * (v : ℝ)))⁻¹ *
        Real.exp (a * x + (-(x - 0) ^ 2 / (2 * (v : ℝ)))) := by rw [Real.exp_add]; ring
    _ = _ := by rw [he, Real.exp_add]; ring

/-- Actual Gaussian exponential change of measure, including the point-mass case. -/
theorem integral_tilt (v : ℝ≥0) (a : ℝ) (f : ℝ → ℝ) :
    (∫ x, Real.exp (a * x) * f x ∂gaussianReal 0 v) =
      Real.exp (a ^ 2 * (v : ℝ) / 2) * (∫ x, f x ∂gaussianReal (a * (v : ℝ)) v) := by
  by_cases hv : v = 0
  · simp [hv]
  · rw [integral_gaussianReal_eq_integral_smul hv,
      integral_gaussianReal_eq_integral_smul hv, ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with x
    simp only [smul_eq_mul]
    have hh := density_tilt v hv a x
    nlinarith [congrArg (fun z : ℝ ↦ z * f x) hh]

end Descent.Portability.GaussianExponentialTilt
