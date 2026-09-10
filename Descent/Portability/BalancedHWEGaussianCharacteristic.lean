/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.BalancedHWECompoundPoisson
import Descent.Portability.RealVaryingEuler
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc

assert_below Descent.Decision Descent.Program

/-!
In the balanced high-intensity phase the exact characteristic functions converge
to the standard Gaussian characteristic function. This module proves the
characteristic limit; it does not assume or assert a general Levy continuity theorem.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.BalancedHWEGaussianCharacteristic

open scoped BigOperators Topology
open Filter Foundations HWEInteractionLaw BalancedHWEInteraction
open BalancedHWEVanishingLaw BalancedHWECompoundPoisson

/-- An exact sinc identity isolates the Gaussian coefficient without a Taylor remainder. -/
theorem cosine_generator_identity (r t : ℝ) (hr : 0 < r) :
    r * (Real.cos (t * (Real.sqrt r)⁻¹) - 1) =
      -(t ^ 2 / 2) * Real.sinc (t * (Real.sqrt r)⁻¹ / 2) ^ 2 := by
  let z := t * (Real.sqrt r)⁻¹ / 2
  have hz : 2 * z = t * (Real.sqrt r)⁻¹ := by dsimp [z]; ring
  have hsin : Real.sin z = Real.sinc z * z := by
    by_cases h : z = 0
    · simp [h]
    · rw [Real.sinc_of_ne_zero h, div_mul_cancel₀ _ h]
  have hcos : Real.cos (t * (Real.sqrt r)⁻¹) - 1 = -2 * Real.sin z ^ 2 := by
    have h := Real.sin_sq_eq_half_sub (x := z)
    rw [hz] at h
    linarith
  have hinv : r * ((Real.sqrt r)⁻¹) ^ 2 = 1 := by
    rw [inv_pow, Real.sq_sqrt hr.le, mul_inv_cancel₀ hr.ne']
  rw [hcos, hsin]
  calc
    _ = -(t ^ 2 / 2) * Real.sinc z ^ 2 * (r * ((Real.sqrt r)⁻¹) ^ 2) := by
      dsimp [z]
      ring
    _ = _ := by rw [hinv, mul_one]

/-- A diverging intensity makes the compensated cosine exponent exactly Gaussian in the limit. -/
theorem cosine_generator_limit (r : ℕ → ℝ) (hr : Tendsto r atTop atTop) (t : ℝ) :
    Tendsto (fun m ↦ r m * (Real.cos (t * (Real.sqrt (r m))⁻¹) - 1)) atTop
      (nhds (-(t ^ 2 / 2))) := by
  have hs : Tendsto (fun m ↦ (Real.sqrt (r m))⁻¹) atTop (nhds 0) := by
    simpa only [Function.comp_def, Real.sqrt_inv, Real.sqrt_zero] using
      (Real.continuous_sqrt.tendsto 0).comp (tendsto_inv_atTop_zero.comp hr)
  have hz : Tendsto (fun m ↦ t * (Real.sqrt (r m))⁻¹ / 2) atTop (nhds 0) := by
    simpa only [mul_zero, zero_div] using (tendsto_const_nhds.mul hs).div_const 2
  have hsin := (Real.continuous_sinc.tendsto 0).comp hz
  have h := (tendsto_const_nhds (x := -(t ^ 2 / 2))).mul (hsin.pow 2)
  simp only [Real.sinc_zero, one_pow, mul_one] at h
  apply h.congr'
  filter_upwards [hr.eventually (eventually_gt_atTop 0)] with m hm
  exact (cosine_generator_identity (r m) t hm).symm

/-- Diverging nonzero-block intensity forces the number of independent blocks to diverge. -/
theorem high_intensity_row_size (N : ℕ → ℕ)
    (hr : Tendsto (fun m ↦ (N m : ℝ) * (1 / 2 : ℝ) ^ m) atTop atTop) :
    Tendsto N atTop atTop := by
  apply tendsto_atTop.2
  intro B
  filter_upwards [hr.eventually (eventually_ge_atTop (B : ℝ))] with m hm
  have hle : (N m : ℝ) * (1 / 2 : ℝ) ^ m ≤ N m :=
    mul_le_of_le_one_right (Nat.cast_nonneg _) (pow_le_one₀ (by norm_num) (by norm_num))
  exact_mod_cast hm.trans hle

/-- The exact scalar characteristic formula converges to the Gaussian exponential. -/
theorem scalar_characteristic_limit (N : ℕ → ℕ)
    (hr : Tendsto (fun m ↦ (N m : ℝ) * (1 / 2 : ℝ) ^ m) atTop atTop) (t : ℝ) :
    Tendsto (fun m ↦ (1 + (1 / 2 : ℝ) ^ m *
      (Real.cos (t * unitAmplitude m (N m)) - 1)) ^ N m) atTop
      (nhds (Real.exp (-(t ^ 2 / 2)))) := by
  let r (m : ℕ) := (N m : ℝ) * (1 / 2 : ℝ) ^ m
  let u (m : ℕ) := r m * (Real.cos (t * unitAmplitude m (N m)) - 1)
  have hN := high_intensity_row_size N hr
  have hu : Tendsto u atTop (nhds (-(t ^ 2 / 2))) := by
    simpa only [u, unitAmplitude_eq_inverse_sqrt] using cosine_generator_limit r hr t
  have h := RealVaryingEuler.varying_euler_limit N u (-(t ^ 2 / 2)) hN hu
  apply h.congr'
  filter_upwards [hN.eventually (eventually_gt_atTop 0)] with m hm
  congr 1
  dsimp [u, r]
  have hn : (N m : ℝ) ≠ 0 := by positivity
  field_simp

/-- The actual genotype experiment has the full standard Gaussian characteristic limit. -/
theorem gaussian_characteristic_limit (N : ℕ → ℕ)
    (hr : Tendsto (fun m ↦ (N m : ℝ) * (1 / 2 : ℝ) ^ m) atTop atTop) (t : ℝ) :
    Tendsto (fun m ↦ complexExpectation (rowLaw m (N m))
      (fun sample ↦ Complex.exp ((t * rowScore (unitAmplitude m (N m)) sample : ℝ) *
        Complex.I))) atTop (nhds ((Real.exp (-(t ^ 2 / 2)) : ℝ) : ℂ)) := by
  apply (scalar_characteristic_limit N hr t).ofReal.congr'
  filter_upwards [eventually_gt_atTop 0] with m hm
  exact (row_characteristic m (N m) hm (unitAmplitude m (N m)) t).symm

end Descent.Portability.BalancedHWEGaussianCharacteristic
