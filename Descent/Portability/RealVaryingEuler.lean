/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.BanachEulerExponential
import Mathlib.Analysis.SpecialFunctions.Exponential

assert_below Descent.Decision Descent.Program

/-!
The real Euler exponential limit allows both the number of steps and the
numerator to vary. Uniform factorial domination controls the whole binomial
series, avoiding any assumption that the numerator is fixed.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.RealVaryingEuler

open scoped Topology
open Filter

/-- The Euler product with a convergent numerator and divergent step count. -/
theorem varying_euler_limit (N : ℕ → ℕ) (u : ℕ → ℝ) (v : ℝ)
    (hN : Tendsto N atTop atTop) (hu : Tendsto u atTop (nhds v)) :
    Tendsto (fun m ↦ (1 + u m / N m) ^ N m) atTop (nhds (Real.exp v)) := by
  let C := |v| + 1
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hbound : ∀ᶠ m in atTop, |u m| ≤ C := by
    filter_upwards [hu.eventually (Metric.ball_mem_nhds v (by norm_num : (0 : ℝ) < 1))]
      with m hm
    have hm' : |u m - v| < 1 := by simpa only [Metric.mem_ball, Real.dist_eq] using hm
    have habs := abs_add_le (u m - v) v
    simp only [sub_add_cancel] at habs
    dsimp only [C]
    linarith
  have hsum : Summable (fun k : ℕ ↦ (k.factorial : ℝ)⁻¹ * C ^ k) := by
    simpa only [smul_eq_mul] using
      (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) C).summable
  have hlim := tendsto_tsum_of_dominated_convergence hsum
    (fun k ↦ ((BanachEulerExponential.coefficient_limit k).comp hN).mul (hu.pow k))
    (show ∀ᶠ m in atTop, ∀ k : ℕ,
      ‖(((N m).choose k : ℝ) / (N m : ℝ) ^ k) * u m ^ k‖ ≤
        (k.factorial : ℝ)⁻¹ * C ^ k from by
      filter_upwards [hbound, hN.eventually (eventually_gt_atTop 0)] with m hm hmN k
      rw [Real.norm_eq_abs, abs_mul, abs_pow,
        abs_of_nonneg (show (0 : ℝ) ≤ ((N m).choose k : ℝ) / (N m : ℝ) ^ k by positivity)]
      exact mul_le_mul (BanachEulerExponential.coefficient_bound (N m) k hmN)
        (pow_le_pow_left₀ (abs_nonneg _) hm k) (by positivity) (by positivity))
  have heq : (∑' k : ℕ, (k.factorial : ℝ)⁻¹ * v ^ k) = Real.exp v := by
    simpa only [smul_eq_mul, ← Real.exp_eq_exp_ℝ] using
      (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) v).tsum_eq
  rw [heq] at hlim
  convert hlim using 1
  funext m
  have h := BanachEulerExponential.euler_eq_series (u m) (N m)
  simpa only [smul_eq_mul, div_eq_mul_inv, mul_comm] using h

end Descent.Portability.RealVaryingEuler
