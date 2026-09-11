/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.HWEHierarchyLimitLaw
import Descent.Portability.HWEJumpMoments

assert_below Descent.Decision Descent.Program

/-!
The hierarchy's recovered jump parameters simplify to the report's explicit
factorial formula. The jump variance is exactly the Poisson mass of its count
layer, computed from the actual probability law of the marks.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.HWEHierarchyParameters

open scoped BigOperators NNReal
open MeasureTheory ProbabilityTheory HWEHierarchyLimitLaw HWEFixedLayerInputs
open HWECriticalLimitLaw HWEJumpMoments

/-- Exact squared amplitude of the surviving count layer. -/
theorem layerAmplitude_sq (κ C : ℝ) (hC : 0 < C) (r : ℕ) :
    layerAmplitude κ C r ^ 2 = (4 * κ ^ 2) ^ r / C := by
  have hp : ((-2 * κ) ^ r) ^ 2 = (4 * κ ^ 2) ^ r := by
    rw [← pow_mul, Nat.mul_comm r 2, pow_mul]
    congr 1
    ring
  rw [layerAmplitude, mul_pow, div_pow, one_pow, Real.sq_sqrt hC.le, hp]
  ring

/-- The recovered original Poisson intensity is C exp(4 κ²) divided by r factorial. -/
theorem layerIntensity_explicit (κ C : ℝ) (hκ : κ ≠ 0) (hC : 0 < C) (r : ℕ) :
    (layerIntensity κ C r : ℝ) = C * Real.exp (4 * κ ^ 2) / (r.factorial : ℝ) := by
  have hp : (4 * κ ^ 2) ^ r ≠ 0 :=
    pow_ne_zero _ (mul_ne_zero (by norm_num) (pow_ne_zero _ hκ))
  have he : Real.exp (-(4 * κ ^ 2)) * Real.exp (8 * κ ^ 2) =
      Real.exp (4 * κ ^ 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  change poissonPMFReal (4 * energy κ) r * (layerAmplitude κ C r ^ 2)⁻¹ *
    Real.exp (8 * (energy κ : ℝ)) = _
  rw [layerAmplitude_sq κ C hC r, poissonPMFReal]
  simp only [energy, NNReal.coe_mk, NNReal.coe_mul, NNReal.coe_ofNat]
  calc
    _ = C / (r.factorial : ℝ) *
        (Real.exp (-(4 * κ ^ 2)) * Real.exp (8 * κ ^ 2)) := by
      field_simp
    _ = _ := by rw [he]; ring

/-- The integer-layer intensity is strictly positive for every finite layer. -/
theorem layerIntensity_pos (κ C : ℝ) (hκ : κ ≠ 0) (hC : 0 < C) (r : ℕ) :
    0 < (layerIntensity κ C r : ℝ) := by
  rw [layerIntensity_explicit κ C hκ hC r]
  exact div_pos (mul_pos hC (Real.exp_pos _)) (by exact_mod_cast Nat.factorial_pos r)

/-- The Poisson marks contribute exactly the probability of the retained count layer. -/
theorem layer_jump_variance (κ C : ℝ) (hκ : κ ≠ 0) (hC : 0 < C) (r : ℕ) :
    (layerIntensity κ C r : ℝ) *
      (∫ x : ℝ, x ^ 2 ∂(jumpLaw (energy κ) (layerAmplitude κ C r) : Measure ℝ)) =
        poissonPMFReal (4 * energy κ) r := by
  rw [jump_second]
  have hc := pow_ne_zero 2 (layerAmplitude_ne_zero κ C hκ hC r)
  have he : Real.exp (8 * (energy κ : ℝ)) * Real.exp (-8 * (energy κ : ℝ)) = 1 := by
    rw [← Real.exp_add, show 8 * (energy κ : ℝ) + -8 * (energy κ : ℝ) = 0 by ring,
      Real.exp_zero]
  change poissonPMFReal (4 * energy κ) r * (layerAmplitude κ C r ^ 2)⁻¹ *
    Real.exp (8 * (energy κ : ℝ)) *
      (layerAmplitude κ C r ^ 2 * Real.exp (-8 * (energy κ : ℝ))) = _
  calc
    _ = poissonPMFReal (4 * energy κ) r *
        ((layerAmplitude κ C r ^ 2)⁻¹ * layerAmplitude κ C r ^ 2) *
          (Real.exp (8 * (energy κ : ℝ)) * Real.exp (-8 * (energy κ : ℝ))) := by ring
    _ = _ := by rw [inv_mul_cancel₀ hc, he, mul_one, mul_one]

end Descent.Portability.HWEHierarchyParameters
