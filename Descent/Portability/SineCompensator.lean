/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.CosineArrayLimit
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

assert_below Descent.Decision Descent.Program

/-!
The imaginary part of the compensated characteristic kernel uses
(sin x - x)/x^2, extended by its exact value zero at the origin. A cubic sine
bound proves continuity there, and a global bound makes it a bounded test.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.SineCompensator

open scoped Topology
open Filter

/-- A concrete cubic remainder bound for real sine near zero. -/
theorem sine_cubic_bound (x : ℝ) (hx : |x| ≤ 1) : |Real.sin x - x| ≤ |x| ^ 3 / 4 := by
  have hp (u : ℝ) (hu : 0 ≤ u) (hu1 : u ≤ 1) : |Real.sin u - u| ≤ u ^ 3 / 4 := by
    by_cases hz : u = 0
    · simp [hz]
    · have hl := Real.sin_gt_sub_cube (lt_of_le_of_ne hu (Ne.symm hz)) hu1
      have hh := Real.sin_le hu
      rw [abs_of_nonpos (sub_nonpos.mpr hh)]
      linarith
  by_cases hpos : 0 ≤ x
  · simpa only [abs_of_nonneg hpos] using hp x hpos (by simpa [abs_of_nonneg hpos] using hx)
  · have hneg : x ≤ 0 := le_of_not_ge hpos
    have hh := hp (-x) (neg_nonneg.mpr hneg) (by simpa [abs_of_nonpos hneg] using hx)
    simpa only [Real.sin_neg, neg_sub_neg, abs_sub_comm, abs_of_nonpos hneg] using hh

/-- The zero extension is already exact under real division at zero. -/
noncomputable def compensator (x : ℝ) : ℝ := (Real.sin x - x) / x ^ 2

@[simp] theorem compensator_zero : compensator 0 = 0 := by simp [compensator]

/-- A vanishing linear bound controls the removable singularity. -/
theorem near_bound (x : ℝ) (hx : |x| ≤ 1) : |compensator x| ≤ |x| / 4 := by
  by_cases hz : x = 0
  · simp [hz]
  · rw [compensator, abs_div, abs_of_nonneg (sq_nonneg x), div_le_iff₀ (sq_pos_of_ne_zero hz)]
    have hh := sine_cubic_bound x hx
    have he : |x| ^ 3 / 4 = |x| / 4 * x ^ 2 := by rw [pow_succ, sq_abs]; ring
    exact hh.trans_eq he

/-- The exact sine compensator is continuous, including at zero. -/
theorem continuous_compensator : Continuous compensator := by
  apply continuous_iff_continuousAt.mpr
  intro x
  by_cases hx : x = 0
  · subst x
    change Tendsto compensator (𝓝 0) (𝓝 (compensator 0))
    rw [compensator_zero]
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    have hb : Tendsto (fun y : ℝ ↦ |y| / 4) (𝓝 0) (𝓝 0) := by
      simpa using (continuous_abs.tendsto (0 : ℝ)).div_const 4
    apply squeeze_zero' (Eventually.of_forall (fun y ↦ norm_nonneg _)) ?_ hb
    filter_upwards [(continuous_abs.tendsto (0 : ℝ)).eventually
      (gt_mem_nhds (by norm_num : |(0 : ℝ)| < 1))] with y hy
    exact near_bound y hy.le
  · exact (Real.continuous_sin.continuousAt.sub continuousAt_id).div
      (continuousAt_id.pow 2) (pow_ne_zero _ hx)

/-- A global bound independent of the argument. -/
theorem global_bound (x : ℝ) : |compensator x| ≤ 2 := by
  by_cases hx : |x| ≤ 1
  · exact (near_bound x hx).trans (by linarith)
  · have hbig : 1 < |x| := lt_of_not_ge hx
    have hz : x ≠ 0 := by intro hz; norm_num [hz] at hbig
    rw [compensator, abs_div, abs_of_nonneg (sq_nonneg x), div_le_iff₀ (sq_pos_of_ne_zero hz)]
    have hh := (abs_sub (Real.sin x) x).trans
      (add_le_add_right (Real.abs_sin_le_one x) |x|)
    nlinarith [sq_abs x, sq_nonneg (|x| - 1)]

/-- The sine compensator is odd, so symmetric laws cancel its expectation. -/
theorem compensator_neg (x : ℝ) : compensator (-x) = -compensator x := by
  simp only [compensator, Real.sin_neg, neg_sq]
  ring

end Descent.Portability.SineCompensator
