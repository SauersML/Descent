/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.BalancedHWEJumpOperator

assert_below Descent.Decision Descent.Program

/-!
A finite limiting jump intensity and a convergent amplitude determine the exact
bounded-observable limit of the balanced HWE array. Dominated Euler coefficients
control the full series; continuity is required only for evaluated finite powers.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.BalancedHWEFiniteIntensity

open scoped BigOperators BoundedContinuousFunction Topology
open Filter Foundations HWEInteractionLaw BalancedHWEInteraction
open IndependentShiftOperator BalancedHWEOperatorLimit BalancedHWEJumpOperator

noncomputable local instance : NormedRing Operator := ContinuousLinearMap.toNormedRing
local instance : IsTopologicalRing Operator :=
  NonUnitalSeminormedRing.toIsTopologicalRing
local instance : SMul Operator Operator := ⟨(· * ·)⟩
local instance : IsScalarTower ℝ Operator Operator :=
  IsScalarTower.right (R := ℝ) (A := Operator)

/-- An evaluated exponential series, with the intensity pulled out of each power. -/
theorem evaluated_exponential_series (r a : ℝ) (f : Observable) :
    (NormedSpace.exp ℝ (r • generator a)) f 0 =
      ∑' k : ℕ, (k.factorial : ℝ)⁻¹ * (r ^ k * ((generator a ^ k) f 0)) := by
  have h := (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) (r • generator a)).map
    (observer f 0) (observer f 0).continuous
  symm
  convert h.tsum_eq using 1
  apply tsum_congr
  intro k
  simp only [Function.comp_apply, map_smul, smul_pow, observer_apply,
    smul_eq_mul]

/-- Exact limiting expectation for every bounded continuous observable under
arbitrary finite intensity and amplitude limits. -/
theorem finite_intensity_observable_limit (N : ℕ → ℕ) (a : ℕ → ℝ) (r b : ℝ)
    (hN : Tendsto N atTop atTop)
    (hr : Tendsto (fun m ↦ (N m : ℝ) * (1 / 2 : ℝ) ^ m) atTop (nhds r))
    (ha : Tendsto a atTop (nhds b)) (f : Observable) :
    Tendsto (fun m ↦ (rowLaw m (N m)).expectation
      (fun sample ↦ f (rowScore (a m) sample))) atTop
      (nhds ((NormedSpace.exp ℝ (r • generator b)) f 0)) := by
  let intensity (m : ℕ) := (N m : ℝ) * (1 / 2 : ℝ) ^ m
  let C := |r| + 1
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hbound : ∀ᶠ m in atTop, |intensity m| ≤ C := by
    filter_upwards [hr.eventually (Metric.ball_mem_nhds r (by norm_num : (0 : ℝ) < 1))]
      with m hm
    have hm' : |intensity m - r| < 1 := by simpa only [Metric.mem_ball, Real.dist_eq] using hm
    have habs := abs_add_le (intensity m - r) r
    simp only [sub_add_cancel] at habs
    dsimp only [C]
    linarith
  have hsum : Summable (fun k : ℕ ↦
      ((k.factorial : ℝ)⁻¹ * (2 * C) ^ k) * ‖f‖) := by
    have h := (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) (2 * C)).summable
    simpa only [smul_eq_mul] using h.mul_right ‖f‖
  have hterm : ∀ k : ℕ, Tendsto
      (fun m ↦ (((N m).choose k : ℝ) / (N m : ℝ) ^ k) *
        (intensity m ^ k * ((generator (a m) ^ k) f 0))) atTop
      (nhds ((k.factorial : ℝ)⁻¹ * (r ^ k * ((generator b ^ k) f 0)))) := by
    intro k
    have hg := (generator_power_continuous k f).tendsto (b, 0)
      |>.comp (ha.prodMk_nhds tendsto_const_nhds)
    exact ((BanachEulerExponential.coefficient_limit k).comp hN).mul
      ((hr.pow k).mul hg)
  have hdom : ∀ᶠ m in atTop, ∀ k : ℕ,
      ‖(((N m).choose k : ℝ) / (N m : ℝ) ^ k) *
        (intensity m ^ k * ((generator (a m) ^ k) f 0))‖ ≤
      ((k.factorial : ℝ)⁻¹ * (2 * C) ^ k) * ‖f‖ := by
    filter_upwards [hbound, hN.eventually (eventually_gt_atTop 0)] with m hm hmN k
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_pow,
      abs_of_nonneg (show (0 : ℝ) ≤ ((N m).choose k : ℝ) / (N m : ℝ) ^ k by positivity)]
    calc
      _ ≤ (k.factorial : ℝ)⁻¹ * (C ^ k * ((2 : ℝ) ^ k * ‖f‖)) := by
        apply mul_le_mul (BanachEulerExponential.coefficient_bound (N m) k hmN)
        · exact mul_le_mul (pow_le_pow_left₀ (abs_nonneg _) hm k)
            (generator_power_bound k (a m) f 0) (abs_nonneg _) (by positivity)
        · positivity
        · positivity
      _ = _ := by rw [mul_pow]; ring
  have hlim := tendsto_tsum_of_dominated_convergence hsum hterm hdom
  rw [← evaluated_exponential_series] at hlim
  apply hlim.congr'
  filter_upwards [eventually_gt_atTop 0, hN.eventually (eventually_gt_atTop 0)] with m hm hmN
  exact (row_euler_series m (N m) hm hmN (a m) f).symm

end Descent.Portability.BalancedHWEFiniteIntensity
