/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.GaussianPanelLaw
import Mathlib.Probability.Moments.MGFAnalytic
import Mathlib.Analysis.Calculus.Deriv.Polynomial

assert_below Descent.Decision Descent.Program

/-!
Gaussian polynomial moments from differentiation under the actual Gaussian
integral. The recurrence retains the variance and every moment order.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.GaussianPolynomialMoments

open MeasureTheory ProbabilityTheory Polynomial

noncomputable def momentPolynomial (variance : ℝ) : ℕ → Polynomial ℝ
  | 0 => 1
  | n + 1 => (momentPolynomial variance n).derivative +
      C variance * X * momentPolynomial variance n

theorem tilted_power_moment (variance : NNReal) (n : ℕ) (t : ℝ) :
    (∫ x : ℝ, x ^ n * Real.exp (t * x) ∂gaussianReal 0 variance) =
      (momentPolynomial variance n).eval t * Real.exp ((variance : ℝ) * t ^ 2 / 2) := by
  induction n generalizing t with
  | zero =>
    simpa only [pow_zero, one_mul, momentPolynomial, eval_one, zero_mul, zero_add] using
      congrFun (mgf_fun_id_gaussianReal (μ := 0) (v := variance)) t
  | succ n ih =>
    have hraw := hasDerivAt_integral_pow_mul_exp_real
      (X := fun x : ℝ ↦ x) (μ := gaussianReal 0 variance) (t := t)
      (by simp) n
    have he : HasDerivAt (fun s : ℝ ↦ Real.exp ((variance : ℝ) * s ^ 2 / 2))
        (Real.exp ((variance : ℝ) * t ^ 2 / 2) * ((variance : ℝ) * t)) t := by
      convert ((((hasDerivAt_id t).pow 2).const_mul (variance : ℝ)).div_const 2).exp using 1
      simp only [Pi.pow_apply, id_eq]
      ring
    have hd := ((momentPolynomial variance n).hasDerivAt t).mul he
    have hfun : (fun s : ℝ ↦ ∫ x : ℝ, x ^ n * Real.exp (s * x) ∂gaussianReal 0 variance) =
        fun s ↦ (momentPolynomial variance n).eval s * Real.exp ((variance : ℝ) * s ^ 2 / 2) :=
      funext ih
    rw [hfun] at hraw
    rw [hraw.unique hd]
    simp only [momentPolynomial, eval_add, eval_mul, eval_C, eval_X]
    ring

theorem power_moment (variance : NNReal) (n : ℕ) :
    (∫ x : ℝ, x ^ n ∂gaussianReal 0 variance) = (momentPolynomial variance n).eval 0 := by
  simpa only [zero_mul, zero_pow (by decide : 2 ≠ 0), mul_zero, zero_div,
    Real.exp_zero, mul_one] using tilted_power_moment variance n 0

theorem first_moment (variance : NNReal) : (∫ x : ℝ, x ∂gaussianReal 0 variance) = 0 := by
  simp

theorem second_moment (variance : NNReal) :
    (∫ x : ℝ, x ^ 2 ∂gaussianReal 0 variance) = variance := by
  rw [power_moment]
  simp [momentPolynomial]

theorem third_moment (variance : NNReal) :
    (∫ x : ℝ, x ^ 3 ∂gaussianReal 0 variance) = 0 := by
  rw [power_moment]
  simp [momentPolynomial, derivative_mul]

theorem fourth_moment (variance : NNReal) :
    (∫ x : ℝ, x ^ 4 ∂gaussianReal 0 variance) = 3 * (variance : ℝ) ^ 2 := by
  rw [power_moment]
  simp [momentPolynomial, derivative_mul]
  ring

end Descent.Portability.GaussianPolynomialMoments
