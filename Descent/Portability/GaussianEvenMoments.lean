/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.GaussianHermiteLaw

assert_below Descent.Decision Descent.Program

/-!
Every centered Gaussian even moment is a strictly positive universal constant
times the corresponding power of its variance. This includes zero variance.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.GaussianEvenMoments

open MeasureTheory ProbabilityTheory GaussianPolynomialMoments GaussianHermiteLaw

noncomputable def evenConstant (k : ℕ) : ℝ := (momentPolynomial 1 (2 * k)).eval 0

theorem evenConstant_pos (k : ℕ) : 0 < evenConstant k := by
  letI : NoAtoms (gaussianReal 0 1) := noAtoms_gaussianReal (by norm_num)
  have hc : evenConstant k = ∫ x : ℝ, x ^ (2 * k) ∂gaussianReal 0 1 := by
    simpa only [evenConstant, NNReal.coe_one] using (power_moment 1 (2 * k)).symm
  rw [hc]
  apply (integral_pos_iff_support_of_nonneg _ (integrable_power 1 (2 * k))).mpr
  · have hm : (gaussianReal 0 1) ({0}ᶜ : Set ℝ) = 1 := by simp
    have hpos : 0 < (gaussianReal 0 1) ({0}ᶜ : Set ℝ) := by rw [hm]; norm_num
    apply hpos.trans_le
    apply measure_mono
    intro x hx
    exact pow_ne_zero _ (by simpa using hx)
  · intro x
    change 0 ≤ x ^ (2 * k)
    rw [pow_mul]
    exact pow_nonneg (sq_nonneg x) _

theorem gaussian_sqrt_scale (variance : NNReal) :
    (gaussianReal 0 1).map (fun x : ℝ ↦ Real.sqrt variance * x) = gaussianReal 0 variance := by
  rw [gaussianReal_map_const_mul, mul_zero, mul_one]
  congr 1
  apply Subtype.ext
  exact Real.sq_sqrt variance.coe_nonneg

theorem even_power_moment (variance : NNReal) (k : ℕ) :
    (∫ x : ℝ, x ^ (2 * k) ∂gaussianReal 0 variance) =
      evenConstant k * (variance : ℝ) ^ k := by
  rw [← gaussian_sqrt_scale variance, integral_map (by fun_prop) (by fun_prop)]
  simp only [mul_pow, integral_const_mul]
  rw [pow_mul, Real.sq_sqrt variance.coe_nonneg, power_moment 1]
  exact mul_comm _ _

end Descent.Portability.GaussianEvenMoments
