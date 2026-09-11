/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.GaussianVarianceDensity
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

assert_below Descent.Decision Descent.Program

/-!
Explicit derivatives of the actual Gaussian variance density ratio through order
three. The logarithmic representation and its derivatives are proved directly;
these formulas provide the polynomial and Gaussian domination terms needed for
the covariance-family density remainder.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.GaussianVarianceJet

open scoped Topology
open Filter GaussianVarianceDensity

/-- Logarithm of the variance density ratio on positive variances. -/
noncomputable def logProfile (a x : ℝ) : ℝ :=
  -Real.log a / 2 + (1 - a⁻¹) * x ^ 2 / 2

/-- First variance derivative of the log density ratio. -/
noncomputable def logFirst (a x : ℝ) : ℝ := -a⁻¹ / 2 + x ^ 2 * (a⁻¹) ^ 2 / 2

/-- Second variance derivative of the log density ratio. -/
noncomputable def logSecond (a x : ℝ) : ℝ := (a⁻¹) ^ 2 / 2 - x ^ 2 * (a⁻¹) ^ 3

/-- Third variance derivative of the log density ratio. -/
noncomputable def logThird (a x : ℝ) : ℝ := -(a⁻¹) ^ 3 + 3 * x ^ 2 * (a⁻¹) ^ 4

/-- The explicit log profile exponentiates to the actual Gaussian density ratio. -/
theorem ratio_eq_exp (a x : ℝ) (ha : 0 < a) : ratio a x = Real.exp (logProfile a x) := by
  have he : Real.exp (-Real.log a / 2) = (Real.sqrt a)⁻¹ := by
    rw [show -Real.log a / 2 = -(Real.log a / 2) by ring,
      ← Real.log_sqrt ha.le, Real.exp_neg, Real.exp_log (Real.sqrt_pos.mpr ha)]
  rw [logProfile, Real.exp_add, he]
  rfl

/-- First derivative of the logarithmic profile from the real logarithm and reciprocal rules. -/
theorem logProfile_hasDerivAt (a x : ℝ) (ha : a ≠ 0) :
    HasDerivAt (fun b ↦ logProfile b x) (logFirst a x) a := by
  have hh := ((Real.hasDerivAt_log ha).neg.div_const 2).add
    ((((hasDerivAt_const a 1).sub ((hasDerivAt_id a).inv ha)).mul_const (x ^ 2)).div_const 2)
  convert hh using 1
  simp only [logFirst, div_eq_mul_inv, inv_pow, id_eq]
  ring

/-- Differentiating the first log derivative gives its stated second derivative. -/
theorem logFirst_hasDerivAt (a x : ℝ) (ha : a ≠ 0) :
    HasDerivAt (fun b ↦ logFirst b x) (logSecond a x) a := by
  have hi := (hasDerivAt_id a).inv ha
  have hh := (hi.neg.div_const 2).add (((hi.pow 2).const_mul (x ^ 2)).div_const 2)
  convert hh using 1
  simp only [logSecond, div_eq_mul_inv, inv_pow, Pi.inv_apply, id_eq]
  ring

/-- Differentiating the second log derivative gives its stated third derivative. -/
theorem logSecond_hasDerivAt (a x : ℝ) (ha : a ≠ 0) :
    HasDerivAt (fun b ↦ logSecond b x) (logThird a x) a := by
  have hi := (hasDerivAt_id a).inv ha
  have hh := ((hi.pow 2).div_const 2).sub ((hi.pow 3).const_mul (x ^ 2))
  convert hh using 1
  simp only [logThird, div_eq_mul_inv, inv_pow, Pi.inv_apply, id_eq]
  ring

/-- The actual variance density ratio has its directly derived first derivative. -/
theorem ratio_hasDerivAt (a x : ℝ) (ha : 0 < a) :
    HasDerivAt (fun b ↦ ratio b x) (ratio a x * logFirst a x) a := by
  have hh := (logProfile_hasDerivAt a x ha.ne').exp
  have he : (fun b ↦ ratio b x) =ᶠ[𝓝 a] (fun b ↦ Real.exp (logProfile b x)) := by
    filter_upwards [eventually_gt_nhds ha] with b hb
    exact ratio_eq_exp b x hb
  have hd := hh.congr_of_eventuallyEq he
  simpa only [← ratio_eq_exp a x ha, mul_comm] using hd

/-- The derivative of the first density derivative is its exact second density derivative. -/
theorem ratio_first_hasDerivAt (a x : ℝ) (ha : 0 < a) :
    HasDerivAt (fun b ↦ ratio b x * logFirst b x)
      (ratio a x * (logFirst a x ^ 2 + logSecond a x)) a := by
  have hh := (ratio_hasDerivAt a x ha).mul (logFirst_hasDerivAt a x ha.ne')
  convert hh using 1
  ring

/-- The exact third density derivative controls the quadratic Taylor remainder. -/
theorem ratio_second_hasDerivAt (a x : ℝ) (ha : 0 < a) :
    HasDerivAt (fun b ↦ ratio b x * (logFirst b x ^ 2 + logSecond b x))
      (ratio a x * (logFirst a x ^ 3 + 3 * logFirst a x * logSecond a x + logThird a x)) a := by
  have hh := (ratio_hasDerivAt a x ha).mul
    (((logFirst_hasDerivAt a x ha.ne').pow 2).add (logSecond_hasDerivAt a x ha.ne'))
  convert hh using 1
  simp only [Pi.add_apply, Pi.pow_apply]
  ring

/-- The reference density ratio is exactly one. -/
theorem ratio_one (x : ℝ) : ratio 1 x = 1 := by simp [ratio]

/-- At variance one the first derivative is the second Hermite polynomial divided by two. -/
theorem ratio_first_at_one (x : ℝ) :
    HasDerivAt (fun a ↦ ratio a x) ((x ^ 2 - 1) / 2) 1 := by
  have hh := ratio_hasDerivAt 1 x (by norm_num)
  convert hh using 1
  simp only [ratio_one, one_mul, logFirst, inv_one, one_pow]
  ring

/-- At variance one the second derivative is the fourth Hermite polynomial divided by four. -/
theorem ratio_second_at_one (x : ℝ) :
    HasDerivAt (fun a ↦ ratio a x * logFirst a x) ((x ^ 4 - 6 * x ^ 2 + 3) / 4) 1 := by
  have hh := ratio_first_hasDerivAt 1 x (by norm_num)
  convert hh using 1
  simp only [ratio_one, one_mul, logFirst, logSecond, inv_one, one_pow]
  ring

end Descent.Portability.GaussianVarianceJet
