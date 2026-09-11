/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.SmallArrayContinuity
import Mathlib.Analysis.Calculus.DSlope
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

assert_below Descent.Decision Descent.Program

/-!
A real triangular product limit derived from the continuous divided difference
of log(1-x). Initial rows need not have positive factors; uniform smallness makes
all factors positive eventually, exactly where logarithms are used.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.SmallRealProduct

open scoped BigOperators Topology
open Filter SmallArrayContinuity

/-- The logarithmic first-order coefficient is derived at zero. -/
theorem log_one_sub_derivative : HasDerivAt (fun x : ℝ ↦ Real.log (1 - x)) (-1) 0 := by
  convert ((hasDerivAt_id (0 : ℝ)).const_sub 1).log (by norm_num) using 1
  norm_num

/-- The divided-difference identity is exact, including a zero argument. -/
theorem log_slope_identity (x : ℝ) :
    x * dslope (fun y : ℝ ↦ Real.log (1 - y)) 0 x = Real.log (1 - x) := by
  simpa only [sub_zero, smul_eq_mul, Real.log_one] using
    sub_smul_dslope (fun y : ℝ ↦ Real.log (1 - y)) 0 x

/-- Vanishing nonnegative factors with convergent total intensity have an exponential product. -/
theorem product_limit (p : (m : ℕ) → Fin m → ℝ) (hp : ∀ m i, 0 ≤ p m i)
    (ε : ℕ → ℝ) (hcap : ∀ m i, p m i ≤ ε m) (hε : Tendsto ε atTop (𝓝 0))
    (s : ℝ) (hs : Tendsto (fun m ↦ ∑ i, p m i) atTop (𝓝 s)) :
    Tendsto (fun m ↦ ∏ i, (1 - p m i)) atTop (𝓝 (Real.exp (-s))) := by
  have hg : ContinuousAt (dslope (fun y : ℝ ↦ Real.log (1 - y)) 0) 0 :=
    continuousAt_dslope_same.mpr log_one_sub_derivative.differentiableAt
  have hsum := weighted_continuous_limit _ hg p p hp ε
    (fun m i ↦ by simpa only [abs_of_nonneg (hp m i)] using hcap m i) hε s hs
  simp only [log_slope_identity, dslope_same, log_one_sub_derivative.deriv, mul_neg_one] at hsum
  have hexp := Real.continuous_exp.continuousAt.tendsto.comp hsum
  apply hexp.congr'
  filter_upwards [hε.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))] with m hm
  change Real.exp (∑ i, Real.log (1 - p m i)) = _
  rw [Real.exp_sum]
  apply Finset.prod_congr rfl
  intro i _
  exact Real.exp_log (sub_pos.mpr ((hcap m i).trans_lt hm))

end Descent.Portability.SmallRealProduct
