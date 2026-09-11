/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.GaussianHermiteLaw
import Mathlib.Probability.Moments.Variance

assert_below Descent.Decision Descent.Program

/-!
The zero-mean Gaussian loss-noise identity is derived from the actual Gaussian
measure and its proved polynomial moments. No Gaussian floor is an input.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.GaussianLossNoise

open MeasureTheory ProbabilityTheory Polynomial GaussianHermiteLaw GaussianPolynomialMoments
open scoped ProbabilityTheory

/-- Squaring a centered Gaussian residual gives loss variance twice the square
of its residual variance, including the degenerate zero-variance case. -/
theorem gaussian_squared_loss_variance (v : NNReal) :
    Var[(fun x : ℝ ↦ x ^ 2); gaussianReal 0 v] = 2 * (v : ℝ) ^ 2 := by
  rw [variance_eq_integral (by fun_prop), second_moment]
  have hpoly : ((X : Polynomial ℝ) ^ 2 - C (v : ℝ)) ^ 2 =
      X ^ 4 - (2 * (v : ℝ)) • X ^ 2 + C ((v : ℝ) ^ 2) := by
    simp only [Algebra.smul_def, algebraMap_eq, map_mul, map_ofNat, map_pow]
    ring
  have hsecond : integratePolynomial v (X ^ 2) = (v : ℝ) := by
    simpa [integratePolynomial] using second_moment v
  have hfourth : integratePolynomial v (X ^ 4) = 3 * (v : ℝ) ^ 2 := by
    simpa [integratePolynomial] using fourth_moment v
  have he : (∫ x : ℝ, (x ^ 2 - (v : ℝ)) ^ 2 ∂gaussianReal 0 v) =
      integratePolynomial v ((X ^ 2 - C (v : ℝ)) ^ 2) := by
    simp [integratePolynomial]
  rw [he, hpoly, map_add, map_sub, map_smul, integratePolynomial_C, hsecond, hfourth]
  simp only [smul_eq_mul]
  ring

end Descent.Portability.GaussianLossNoise
