/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.GaussianDensityOverlap

assert_below Descent.Decision Descent.Program

/-!
A concrete square-integrable envelope for Gaussian covariance perturbations.
The exponential envelope is integrable under the actual standard product law;
its squared integral reduces to a normalized Gaussian of variance three.
Cubic polynomial factors can be absorbed into this envelope with an explicit
constant, leaving no integrable-domination hypothesis to be supplied later.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.GaussianEnvelopeIntegrability

open MeasureTheory ProbabilityTheory GaussianVarianceDensity
open scoped BigOperators

variable {ι : Type*} [Fintype ι]

/-- Squared Euclidean radius in the product coordinates. -/
noncomputable def energy (x : ι → ℝ) : ℝ := ∑ i, x i ^ 2

/-- A fixed exponential envelope whose square is Gaussian-integrable. -/
noncomputable def envelope (x : ι → ℝ) : ℝ := Real.exp (energy x / 6)

/-- The coordinate energy and its individual summands are nonnegative. -/
theorem energy_nonneg (x : ι → ℝ) : 0 ≤ energy x :=
  Finset.sum_nonneg (fun i _ ↦ sq_nonneg (x i))

/-- Every coordinate's squared value is bounded by the total energy. -/
theorem coordinate_sq_le (x : ι → ℝ) (i : ι) : x i ^ 2 ≤ energy x :=
  Finset.single_le_sum (fun j _ ↦ sq_nonneg (x j)) (Finset.mem_univ i)

/-- The one-dimensional squared envelope is a scalar times a normalized Gaussian ratio. -/
theorem coordinate_exp_identity (x : ℝ) :
    Real.exp (x ^ 2 / 3) = Real.sqrt 3 * ratio 3 x := by
  unfold ratio
  have he : (1 - (3 : ℝ)⁻¹) * x ^ 2 / 2 = x ^ 2 / 3 := by ring
  rw [he, ← mul_assoc, mul_inv_cancel₀ (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 3)).ne',
    one_mul]

/-- A concrete change of Gaussian variance proves integrability of each exponential factor. -/
theorem coordinate_exp_integrable :
    Integrable (fun x : ℝ ↦ Real.exp (x ^ 2 / 3)) (gaussianReal 0 1) := by
  simp_rw [coordinate_exp_identity]
  exact (ratio_integrable 3 (by norm_num)).const_mul _

/-- The square of the full exponential envelope factors over independent coordinates. -/
theorem envelope_sq (x : ι → ℝ) :
    envelope x ^ 2 = ∏ i, Real.exp (x i ^ 2 / 3) := by
  rw [envelope, ← Real.exp_nat_mul]
  have he : (2 : ℝ) * (energy x / 6) = ∑ i, x i ^ 2 / 3 := by
    rw [energy, ← Finset.sum_div]
    ring
  norm_num only [Nat.cast_ofNat]
  rw [he, Real.exp_sum]

/-- The required squared dominating function is integrable under the actual reference law. -/
theorem envelope_sq_integrable :
    Integrable (fun x : ι → ℝ ↦ envelope x ^ 2)
      (Measure.pi (fun _ : ι ↦ gaussianReal 0 1)) := by
  simp_rw [envelope_sq]
  exact Integrable.fintype_prod (fun _ ↦ coordinate_exp_integrable)

/-- Cubic growth can be absorbed into a small extra exponential factor. -/
theorem cubic_absorption (r : ℝ) (hr : 0 ≤ r) :
    (1 + r) ^ 3 * Real.exp (r / 10) ≤ 45 ^ 3 * Real.exp (r / 6) := by
  have he := Real.add_one_le_exp (r / 45)
  have hbase : 1 + r ≤ 45 * Real.exp (r / 45) := by linarith
  have hp := pow_le_pow_left₀ (by linarith : 0 ≤ 1 + r) hbase 3
  have hh := mul_le_mul_of_nonneg_right hp (Real.exp_pos (r / 10)).le
  have hid : (45 * Real.exp (r / 45)) ^ 3 * Real.exp (r / 10) =
      45 ^ 3 * Real.exp (r / 6) := by
    rw [mul_pow, ← Real.exp_nat_mul, mul_assoc, ← Real.exp_add]
    congr 2
    ring
  exact hh.trans_eq hid

end Descent.Portability.GaussianEnvelopeIntegrability
