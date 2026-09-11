/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.GaussianImageMoments

assert_below Descent.Decision Descent.Program

/-!
The actual jump law in the HWE critical limit has finite moments of every order.
Its mean, second, third, and fourth moments are evaluated exactly, as are the
intensity-weighted second and fourth jump moments needed for the limit cumulants.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.HWEJumpMoments

open scoped NNReal
open MeasureTheory ProbabilityTheory HWECriticalLimitLaw GaussianImageMoments

/-- All moments of the actual HWE jump law are integrable. -/
theorem jump_power_integrable (K : ℝ≥0) (c : ℝ) (n : ℕ) :
    Integrable (fun x : ℝ ↦ x ^ n) (jumpLaw K c : Measure ℝ) :=
  signed_power_integrable (8 * (K : ℝ)) (4 * K) c n

/-- The fair signed jumps are centered. -/
theorem jump_mean (K : ℝ≥0) (c : ℝ) : (∫ x : ℝ, x ∂(jumpLaw K c : Measure ℝ)) = 0 := by
  simpa only [pow_one, add_neg_cancel, zero_div, zero_mul] using
    signed_power_integral (8 * (K : ℝ)) (4 * K) c 1

/-- Exact second moment of the original jump mark after undoing square bias. -/
theorem jump_second (K : ℝ≥0) (c : ℝ) :
    (∫ x : ℝ, x ^ 2 ∂(jumpLaw K c : Measure ℝ)) = c ^ 2 * Real.exp (-8 * (K : ℝ)) := by
  rw [jumpLaw, signed_power_integral]
  have he : 8 * (K : ℝ) * (-(2 : ℝ)) + (4 * (K : ℝ)) * (2 : ℝ) ^ 2 / 2 =
      -8 * (K : ℝ) := by ring
  simp only [Nat.cast_ofNat, NNReal.coe_mul, NNReal.coe_ofNat, he, neg_sq]
  ring

/-- The third moment vanishes by the actual independent fair sign. -/
theorem jump_third (K : ℝ≥0) (c : ℝ) :
    (∫ x : ℝ, x ^ 3 ∂(jumpLaw K c : Measure ℝ)) = 0 := by
  rw [jumpLaw, signed_power_integral]
  have he : c ^ 3 + (-c) ^ 3 = 0 := by ring
  rw [he, zero_div, zero_mul]

/-- The fourth jump moment is c to the fourth, independently of K. -/
theorem jump_fourth (K : ℝ≥0) (c : ℝ) :
    (∫ x : ℝ, x ^ 4 ∂(jumpLaw K c : Measure ℝ)) = c ^ 4 := by
  rw [jumpLaw, signed_power_integral]
  have he : 8 * (K : ℝ) * (-(4 : ℝ)) + (4 * (K : ℝ)) * (4 : ℝ) ^ 2 / 2 = 0 := by ring
  simp only [Nat.cast_ofNat, NNReal.coe_mul, NNReal.coe_ofNat, he, Real.exp_zero, mul_one]
  ring

/-- Intensity times the actual jump second moment is exactly exp(-4K). -/
theorem weighted_jump_second (K : ℝ≥0) (c : ℝ) (hc : c ≠ 0) :
    (jumpIntensity K c : ℝ) * (∫ x : ℝ, x ^ 2 ∂(jumpLaw K c : Measure ℝ)) =
      Real.exp (-4 * (K : ℝ)) := by
  rw [jump_second]
  change (c ^ 2)⁻¹ * Real.exp (4 * (K : ℝ)) *
    (c ^ 2 * Real.exp (-8 * (K : ℝ))) = _
  have he : Real.exp (4 * (K : ℝ)) * Real.exp (-8 * (K : ℝ)) =
      Real.exp (-4 * (K : ℝ)) := by rw [← Real.exp_add]; congr 1; ring
  calc
    _ = ((c ^ 2)⁻¹ * c ^ 2) *
        (Real.exp (4 * (K : ℝ)) * Real.exp (-8 * (K : ℝ))) := by ring
    _ = _ := by rw [inv_mul_cancel₀ (pow_ne_zero _ hc), one_mul, he]

/-- At critical intensity r the intensity-weighted fourth jump moment is exp(4K)/r. -/
theorem weighted_jump_fourth (K : ℝ≥0) (r : ℝ) (hr : 0 < r) :
    (jumpIntensity K (1 / Real.sqrt r) : ℝ) *
      (∫ x : ℝ, x ^ 4 ∂(jumpLaw K (1 / Real.sqrt r) : Measure ℝ)) =
        Real.exp (4 * (K : ℝ)) / r := by
  rw [jump_fourth, HWENearBalancedTheorem.critical_jump_intensity K r hr]
  have hs : Real.sqrt r ^ 4 = r ^ 2 := by
    rw [show (4 : ℕ) = 2 * 2 by decide, pow_mul, Real.sq_sqrt hr.le]
  rw [div_pow, one_pow, hs]
  field_simp

end Descent.Portability.HWEJumpMoments
