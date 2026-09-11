/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.SymmetricImageLaw
import Descent.Portability.GaussianExponentialTilt

assert_below Descent.Decision Descent.Program

/-!
The compensated kernel integral under the derived HWE amplitude mixture is
computed explicitly. Undoing square bias shifts the Gaussian log coordinate by
8K and multiplies the jump intensity by exp(4K), as stated in the critical law.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.HWETiltedKernelLaw

open scoped Topology NNReal BoundedContinuousFunction
open MeasureTheory ProbabilityTheory HWEAmplitudeWeakLimit RademacherArrayWeakLimit
open SymmetricImageLaw CompensatedCharacteristicKernel GaussianExponentialTilt

/-- Continuous amplitude map used for both tilted and original jump marks. -/
noncomputable def amplitudeMap (c : ℝ) : C(ℝ, ℝ) :=
  ⟨fun x ↦ c * Real.exp (-x), by fun_prop⟩

theorem signedLognormal_pair (K : ℝ≥0) (c : ℝ) :
    signedLognormal K c = pairLaw (centeredGaussian (4 * K)) (amplitudeMap c) := by
  simp only [signedLognormal, pairLaw, lognormal, amplitudeMap, ContinuousMap.coe_mk, neg_mul]

/-- The Gaussian and jump parts of the limiting kernel integral are separated exactly. -/
theorem mixture_kernel (K : ℝ≥0) (c t : ℝ) :
    (∫ y, kernel t y ∂(amplitudeLimit K c : Measure ℝ)) =
      (((1 - Real.exp (-4 * (K : ℝ))) * (-(t ^ 2 / 2)) + Real.exp (-4 * (K : ℝ)) *
        (∫ x, realPart t (c * Real.exp (-x)) ∂gaussianReal 0 (4 * K)) : ℝ) : ℂ) := by
  rw [amplitudeLimit, integral_blend_complex, signedLognormal_pair, integral_pair_kernel]
  simp only [ProbabilityMeasure.coe_mk, integral_dirac, kernel_zero, amplitudeMap,
    ContinuousMap.coe_mk, centeredGaussian]
  push_cast
  simp only [integral_complex_ofReal]

/-- At nonzero amplitude the real kernel is the cosine remainder divided by amplitude squared. -/
theorem realPart_log_amplitude (c : ℝ) (hc : c ≠ 0) (t x : ℝ) :
    realPart t (c * Real.exp (-x)) = (c ^ 2)⁻¹ * Real.exp (2 * x) *
      (Real.cos (t * (c * Real.exp (-x))) - 1) := by
  have hz : c * Real.exp (-x) ≠ 0 := mul_ne_zero hc (Real.exp_ne_zero _)
  have hh := real_quadratic t (c * Real.exp (-x))
  calc
    _ = (Real.cos (t * (c * Real.exp (-x))) - 1) / (c * Real.exp (-x)) ^ 2 := by
      apply (eq_div_iff (pow_ne_zero _ hz)).mpr
      nlinarith
    _ = _ := by
      have he : Real.exp (2 * x) = Real.exp x ^ 2 := by
        simpa only [Nat.cast_ofNat] using Real.exp_nat_mul x 2
      rw [Real.exp_neg, he]
      field_simp

/-- Undoing square bias gives the actual shifted Gaussian log-coordinate integral. -/
theorem tilted_kernel_integral (K : ℝ≥0) (c : ℝ) (hc : c ≠ 0) (t : ℝ) :
    (∫ x, realPart t (c * Real.exp (-x)) ∂gaussianReal 0 (4 * K)) =
      (c ^ 2)⁻¹ * Real.exp (8 * (K : ℝ)) *
        (∫ x, Real.cos (t * (c * Real.exp (-x))) - 1
          ∂gaussianReal (8 * (K : ℝ)) (4 * K)) := by
  simp_rw [realPart_log_amplitude c hc t]
  have he (x : ℝ) : (c ^ 2)⁻¹ * Real.exp (2 * x) *
      (Real.cos (t * (c * Real.exp (-x))) - 1) =
        (c ^ 2)⁻¹ * (Real.exp (2 * x) * (Real.cos (t * (c * Real.exp (-x))) - 1)) := by ring
  simp_rw [he]
  rw [integral_const_mul, integral_tilt]
  have hmean : 2 * ((4 * K : ℝ≥0) : ℝ) = 8 * (K : ℝ) := by push_cast; ring
  have hvar : (2 : ℝ) ^ 2 * ((4 * K : ℝ≥0) : ℝ) / 2 = 8 * (K : ℝ) := by push_cast; ring
  rw [hmean, hvar]
  ring

/-- Explicit generator with the Gaussian variance and original jump intensity. -/
theorem explicit_kernel_generator (K : ℝ≥0) (c : ℝ) (hc : c ≠ 0) (t : ℝ) :
    (∫ y, kernel t y ∂(amplitudeLimit K c : Measure ℝ)) =
      ((-(t ^ 2 / 2) * (1 - Real.exp (-4 * (K : ℝ))) +
        ((c ^ 2)⁻¹ * Real.exp (4 * (K : ℝ))) *
          (∫ x, Real.cos (t * (c * Real.exp (-x))) - 1
            ∂gaussianReal (8 * (K : ℝ)) (4 * K)) : ℝ) : ℂ) := by
  rw [mixture_kernel, tilted_kernel_integral K c hc t]
  have he : Real.exp (-4 * (K : ℝ)) * Real.exp (8 * (K : ℝ)) =
      Real.exp (4 * (K : ℝ)) := by rw [← Real.exp_add]; congr 1; ring
  congr 1
  nlinarith [congrArg (fun z : ℝ ↦ (c ^ 2)⁻¹ * z *
    (∫ x, Real.cos (t * (c * Real.exp (-x))) - 1
      ∂gaussianReal (8 * (K : ℝ)) (4 * K))) he]

end Descent.Portability.HWETiltedKernelLaw
