/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Layer
import Mathlib.InformationTheory.KullbackLeibler.KLFun
import Mathlib.Analysis.Calculus.LHopital
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Topology.Piecewise
import Mathlib.Tactic

assert_below Descent.Decision Descent.Program

/-!
A globally bounded quadratic factor for the relative-entropy integrand. Its
continuous value at density ratio one is one half. These facts allow dominated
convergence to turn an actual second-order density expansion into the report's
fourth-order information asymptotic without assuming the entropy expansion.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.EntropyQuadraticFactor

open scoped Topology
open Filter Set InformationTheory

/-- The continuous quadratic coefficient of relative entropy at density ratio one. -/
noncomputable def quadraticFactor (r : ℝ) : ℝ :=
  if r = 1 then 1 / 2 else klFun r / (r - 1) ^ 2

/-- Relative entropy is bounded by the chi-square integrand on every nonnegative density ratio. -/
theorem klFun_le_square (r : ℝ) (hr : 0 ≤ r) : klFun r ≤ (r - 1) ^ 2 := by
  rcases eq_or_lt_of_le hr with he | hp
  · subst r
    norm_num [klFun]
  · have hh := mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos hp) hr
    unfold klFun
    nlinarith

/-- The exact quadratic factor is between zero and one globally on nonnegative ratios. -/
theorem quadraticFactor_bounds (r : ℝ) (hr : 0 ≤ r) :
    0 ≤ quadraticFactor r ∧ quadraticFactor r ≤ 1 := by
  by_cases h : r = 1
  · norm_num [quadraticFactor, h]
  · have hp : 0 < (r - 1) ^ 2 := sq_pos_of_ne_zero (sub_ne_zero.mpr h)
    simp only [quadraticFactor, h, if_false]
    exact ⟨div_nonneg (klFun_nonneg hr) hp.le,
      (div_le_one hp).mpr (klFun_le_square r hr)⟩

/-- Exact factorization, including density ratios equal to one. -/
theorem klFun_factorization (r : ℝ) : klFun r = quadraticFactor r * (r - 1) ^ 2 := by
  by_cases h : r = 1
  · simp [quadraticFactor, h, klFun_one]
  · simp only [quadraticFactor, h, if_false]
    exact (div_mul_cancel₀ _ (pow_ne_zero _ (sub_ne_zero.mpr h))).symm

/-- The scalar second-order entropy coefficient follows from its actual logarithmic derivative. -/
theorem quadratic_ratio_limit :
    Tendsto (fun r : ℝ ↦ klFun r / (r - 1) ^ 2) (𝓝[≠] 1) (𝓝 (1 / 2 : ℝ)) := by
  have hlog := (hasDerivAt_iff_tendsto_slope.mp (Real.hasDerivAt_log (by norm_num : (1 : ℝ) ≠ 0)))
  have hd : Tendsto (fun r : ℝ ↦ Real.log r / (2 * (r - 1)))
      (𝓝[≠] 1) (𝓝 (1 / 2 : ℝ)) := by
    have hh := hlog.div_const 2
    convert hh using 1
    · funext r
      simp only [slope_def_field, Real.log_one, sub_zero]
      rw [div_div, mul_comm (r - 1) 2]
    · norm_num
  apply HasDerivAt.lhopital_zero_nhdsNE
    (f' := Real.log) (g' := fun r : ℝ ↦ 2 * (r - 1)) _ _ _ _ _ hd
  · filter_upwards [eventually_nhdsWithin_of_eventually_nhds
      (eventually_ne_nhds (by norm_num : (1 : ℝ) ≠ 0))] with r hr
    exact hasDerivAt_klFun hr
  · filter_upwards with r
    convert ((hasDerivAt_id r).sub_const 1).pow 2 using 1
    dsimp
    ring
  · filter_upwards [self_mem_nhdsWithin] with r hr
    exact mul_ne_zero (by norm_num) (sub_ne_zero.mpr hr)
  · simpa only [klFun_one] using continuous_klFun.continuousAt.tendsto.mono_left
      (nhdsWithin_le_nhds : 𝓝[≠] (1 : ℝ) ≤ 𝓝 1)
  · have hh : ContinuousAt (fun r : ℝ ↦ (r - 1) ^ 2) 1 := by fun_prop
    simpa using hh.tendsto.mono_left (nhdsWithin_le_nhds : 𝓝[≠] (1 : ℝ) ≤ 𝓝 1)

/-- The removable singularity is filled by the exact one-half entropy coefficient. -/
theorem quadraticFactor_continuousAt_one : ContinuousAt quadraticFactor 1 := by
  have hh := continuousAt_update_same.mpr quadratic_ratio_limit
  convert hh using 1
  funext r
  simp [quadraticFactor, Function.update_apply]

end Descent.Portability.EntropyQuadraticFactor
