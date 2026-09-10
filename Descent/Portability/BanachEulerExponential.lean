/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Layer
import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.SpecialFunctions.Choose
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Choose.Sum

assert_below Descent.Decision Descent.Program

/-!
The Euler product converges to the exponential in a complete real normed
algebra. The proof expands the actual product, derives the binomial coefficient
limit and factorial domination, and applies dominated convergence to the series.
This permits Poisson limits of whole bounded-observable transition operators.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.BanachEulerExponential

open scoped BigOperators Topology
open Filter Asymptotics

/-- The rescaled binomial coefficient converges to the exponential-series coefficient. -/
theorem coefficient_limit (k : ℕ) :
    Tendsto (fun n : ℕ ↦ (n.choose k : ℝ) / (n : ℝ) ^ k) atTop
      (nhds ((k.factorial : ℝ)⁻¹)) := by
  have heq := (isEquivalent_choose k).div
    (IsEquivalent.refl (u := fun n : ℕ ↦ (n : ℝ) ^ k) (l := atTop))
  apply heq.symm.tendsto_nhds
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hnp : (n : ℝ) ≠ 0 := by positivity
  have hkp : (k.factorial : ℝ) ≠ 0 := by positivity
  simp only [Pi.div_apply]
  field_simp

/-- Factorial domination holds uniformly at every positive row size. -/
theorem coefficient_bound (n k : ℕ) (hn : 0 < n) :
    (n.choose k : ℝ) / (n : ℝ) ^ k ≤ (k.factorial : ℝ)⁻¹ := by
  have hp : 0 < (n : ℝ) ^ k := by positivity
  calc
    (n.choose k : ℝ) / (n : ℝ) ^ k ≤
        ((n : ℝ) ^ k / (k.factorial : ℝ)) / (n : ℝ) ^ k :=
      div_le_div_of_nonneg_right (Nat.choose_le_pow_div k n) hp.le
    _ = (k.factorial : ℝ)⁻¹ := by
      have hkp : (k.factorial : ℝ) ≠ 0 := by positivity
      field_simp

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]

omit [CompleteSpace A] in
/-- The finite Euler product is exactly a finitely supported infinite series. -/
theorem euler_eq_series (a : A) (n : ℕ) :
    (1 + (n : ℝ)⁻¹ • a) ^ n =
      ∑' k : ℕ, ((n.choose k : ℝ) / (n : ℝ) ^ k) • a ^ k := by
  rw [tsum_eq_sum (s := Finset.range (n + 1)) (fun k hk ↦ by
    have hnk : n < k := by simpa only [Finset.mem_range, not_lt] using hk
    simp only [Nat.choose_eq_zero_of_lt hnk, Nat.cast_zero, zero_div, zero_smul])]
  rw [add_comm, (Commute.one_right ((n : ℝ)⁻¹ • a)).add_pow]
  apply Finset.sum_congr rfl
  intro k _
  simp only [one_pow, mul_one]
  calc
    ((n : ℝ)⁻¹ • a) ^ k * (n.choose k : A) =
        (n.choose k : A) * ((n : ℝ)⁻¹ • a) ^ k := (Nat.cast_comm _ _).symm
    _ = (n.choose k : ℝ) • (((n : ℝ)⁻¹) ^ k • a ^ k) := by
      rw [smul_pow, Nat.cast_smul_eq_nsmul, nsmul_eq_mul]
    _ = ((n.choose k : ℝ) / (n : ℝ) ^ k) • a ^ k := by
      rw [smul_smul, inv_pow, div_eq_mul_inv]

/-- Norm convergence of the Euler approximation to the full operator exponential. -/
theorem euler_tends_exp (a : A) :
    Tendsto (fun n : ℕ ↦ (1 + (n : ℝ)⁻¹ • a) ^ n) atTop
      (nhds (NormedSpace.exp ℝ a)) := by
  have hsum : Summable (fun k : ℕ ↦ (k.factorial : ℝ)⁻¹ * ‖a ^ k‖) := by
    convert (NormedSpace.norm_expSeries_summable' (𝕂 := ℝ) a) using 1
    funext k
    rw [norm_smul, Real.norm_eq_abs, abs_inv,
      abs_of_nonneg (show (0 : ℝ) ≤ (k.factorial : ℝ) by positivity)]
  have hlim := tendsto_tsum_of_dominated_convergence hsum
    (fun k ↦ (coefficient_limit k).smul_const (a ^ k))
    (show ∀ᶠ n : ℕ in atTop, ∀ k : ℕ,
      ‖((n.choose k : ℝ) / (n : ℝ) ^ k) • a ^ k‖ ≤
        (k.factorial : ℝ)⁻¹ * ‖a ^ k‖ from by
      filter_upwards [eventually_gt_atTop 0] with n hn k
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact mul_le_mul_of_nonneg_right (coefficient_bound n k hn) (norm_nonneg _))
  rw [(NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) a).tsum_eq] at hlim
  simpa only [← euler_eq_series] using hlim

end Descent.Portability.BanachEulerExponential
