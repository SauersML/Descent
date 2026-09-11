/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.SineCompensator
import Mathlib.Topology.ContinuousMap.Bounded.Normed

assert_below Descent.Decision Descent.Program

/-!
An explicit bounded continuous version of (exp(ity)-1-ity)/y^2. Sinc gives its
real part and the sine compensator gives its imaginary part. The value at zero
and the exact quadratic identity are proved without a removable-singularity premise.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.CompensatedCharacteristicKernel

open scoped BoundedContinuousFunction
open SineCompensator

noncomputable def realPart (t y : ℝ) : ℝ :=
  -(t ^ 2 / 2) * Real.sinc (t * y / 2) ^ 2

noncomputable def imaginaryPart (t y : ℝ) : ℝ :=
  t ^ 2 * compensator (t * y)

noncomputable def value (t y : ℝ) : ℂ :=
  (realPart t y : ℂ) + (imaginaryPart t y : ℂ) * Complex.I

/-- The explicit real and imaginary parts are continuous at every amplitude. -/
theorem continuous_value (t : ℝ) : Continuous (value t) := by
  have hi : Continuous (imaginaryPart t) := continuous_const.mul
    (continuous_compensator.comp (continuous_const.mul continuous_id))
  have hr : Continuous (realPart t) := by unfold realPart; fun_prop
  exact (Complex.continuous_ofReal.comp hr).add
    ((Complex.continuous_ofReal.comp hi).mul continuous_const)

/-- A concrete global bound sufficient for testing weak convergence. -/
theorem value_bound (t y : ℝ) : ‖value t y‖ ≤ 5 * t ^ 2 / 2 := by
  have hs : Real.sinc (t * y / 2) ^ 2 ≤ 1 := by
    nlinarith [Real.abs_sinc_le_one (t * y / 2), sq_abs (Real.sinc (t * y / 2)),
      mul_nonneg (abs_nonneg (Real.sinc (t * y / 2)))
        (sub_nonneg.mpr (Real.abs_sinc_le_one (t * y / 2)))]
  have hr : |realPart t y| ≤ t ^ 2 / 2 := by
    rw [realPart, abs_mul, abs_neg, abs_of_nonneg (div_nonneg (sq_nonneg t) (by norm_num)),
      abs_of_nonneg (sq_nonneg (Real.sinc (t * y / 2)))]
    exact mul_le_of_le_one_right (by positivity) hs
  have hi : |imaginaryPart t y| ≤ 2 * t ^ 2 := by
    rw [imaginaryPart, abs_mul, abs_of_nonneg (sq_nonneg t)]
    nlinarith [mul_le_mul_of_nonneg_left (global_bound (t * y)) (sq_nonneg t)]
  have hn := norm_add_le (realPart t y : ℂ) ((imaginaryPart t y : ℂ) * Complex.I)
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_I, mul_one] at hn
  exact hn.trans (by linarith)

/-- The compensated characteristic kernel as an actual bounded continuous test. -/
noncomputable def kernel (t : ℝ) : ℝ →ᵇ ℂ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (value t) (continuous_value t)
    (5 * t ^ 2 / 2) (value_bound t)

@[simp] theorem kernel_apply (t y : ℝ) : kernel t y = value t y := rfl

/-- The zero amplitude contributes exactly the Gaussian coefficient. -/
theorem kernel_zero (t : ℝ) : kernel t 0 = (-(t ^ 2 / 2) : ℝ) := by
  simp [kernel_apply, value, realPart, imaginaryPart]

/-- The real quadratic remainder identity is exact at every amplitude. -/
theorem real_quadratic (t y : ℝ) : y ^ 2 * realPart t y = Real.cos (t * y) - 1 := by
  have hh := CosineArrayLimit.cosine_deficit t y
  unfold realPart
  nlinarith

/-- The imaginary quadratic remainder identity is also exact at zero. -/
theorem imaginary_quadratic (t y : ℝ) :
    y ^ 2 * imaginaryPart t y = Real.sin (t * y) - t * y := by
  by_cases ht : t = 0
  · simp [ht, imaginaryPart]
  by_cases hy : y = 0
  · simp [hy, imaginaryPart]
  unfold imaginaryPart compensator
  field_simp

/-- The original compensated exponential is recovered exactly by multiplication by y squared. -/
theorem quadratic_identity (t y : ℝ) :
    (y : ℂ) ^ 2 * kernel t y = Complex.exp ((t * y : ℝ) * Complex.I) - 1 -
      ((t * y : ℝ) : ℂ) * Complex.I := by
  rw [← Complex.ofReal_pow]
  apply Complex.ext
  · simpa only [kernel_apply, value, Complex.mul_re, Complex.add_re,
      Complex.sub_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, Complex.one_re, zero_mul, mul_zero,
      zero_add, add_zero, sub_zero, mul_one, Complex.exp_ofReal_mul_I_re] using
      real_quadratic t y
  · simpa only [kernel_apply, value, Complex.mul_im, Complex.add_im,
      Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im, Complex.one_im, zero_mul, mul_zero, zero_add, add_zero,
      sub_zero, mul_one, Complex.exp_ofReal_mul_I_im] using imaginary_quadratic t y

end Descent.Portability.CompensatedCharacteristicKernel
