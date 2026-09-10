/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.ExactMetricEvaluation

assert_below Descent.Decision Descent.Program

/-!
Sharp continuous measurement allocation for selected unbiased modes. Each
amplitude is the product of target singular value and measurement noise scale.
The minimizer concerns positive-contribution modes and continuous effort.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.OptimalMeasurementAllocation

variable {I : Type*} [Fintype I]

noncomputable def variance (amplitude effort : I → ℝ) : ℝ :=
  ∑ mode, amplitude mode ^ 2 / effort mode

noncomputable def spending (cost effort : I → ℝ) : ℝ := ∑ mode, cost mode * effort mode

noncomputable def weightedAmplitude (amplitude cost : I → ℝ) : ℝ :=
  ∑ mode, amplitude mode * Real.sqrt (cost mode)

theorem variance_nonneg (amplitude effort : I → ℝ) (heffort : ∀ mode, 0 < effort mode) :
    0 ≤ variance amplitude effort :=
  Finset.sum_nonneg (fun mode _ ↦ div_nonneg (sq_nonneg _) (heffort mode).le)

/-- Every positive effort allocation obeys the exact Cauchy-Schwarz budget bound. -/
theorem allocation_lower_bound (amplitude cost effort : I → ℝ) (budget : ℝ)
    (hcost : ∀ mode, 0 ≤ cost mode) (heffort : ∀ mode, 0 < effort mode)
    (hbudget : 0 < budget) (hspending : spending cost effort ≤ budget) :
    weightedAmplitude amplitude cost ^ 2 / budget ≤ variance amplitude effort := by
  have he (mode : I) : Real.sqrt (effort mode) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.mpr (heffort mode))
  have hcross (mode : I) : (amplitude mode / Real.sqrt (effort mode)) *
      (Real.sqrt (cost mode) * Real.sqrt (effort mode)) =
        amplitude mode * Real.sqrt (cost mode) := by field_simp [he mode]
  have hfirst (mode : I) : (amplitude mode / Real.sqrt (effort mode)) ^ 2 =
      amplitude mode ^ 2 / effort mode := by
    rw [div_pow, Real.sq_sqrt (heffort mode).le]
  have hsecond (mode : I) : (Real.sqrt (cost mode) * Real.sqrt (effort mode)) ^ 2 =
      cost mode * effort mode := by
    rw [mul_pow, Real.sq_sqrt (hcost mode), Real.sq_sqrt (heffort mode).le]
  have hc := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun mode ↦ amplitude mode / Real.sqrt (effort mode))
    (fun mode ↦ Real.sqrt (cost mode) * Real.sqrt (effort mode))
  simp_rw [hcross, hfirst, hsecond] at hc
  apply (div_le_iff₀ hbudget).mpr
  exact hc.trans (mul_le_mul_of_nonneg_left hspending (variance_nonneg _ _ heffort))

variable [Nonempty I]

theorem weightedAmplitude_pos (amplitude cost : I → ℝ)
    (ha : ∀ mode, 0 < amplitude mode) (hc : ∀ mode, 0 < cost mode) :
    0 < weightedAmplitude amplitude cost := by
  apply Finset.sum_pos
  · intro mode _
    exact mul_pos (ha mode) (Real.sqrt_pos.mpr (hc mode))
  · exact Finset.univ_nonempty

noncomputable def optimalEffort (amplitude cost : I → ℝ) (budget : ℝ) (mode : I) : ℝ :=
  budget * amplitude mode / (Real.sqrt (cost mode) * weightedAmplitude amplitude cost)

theorem optimalEffort_pos (amplitude cost : I → ℝ) (budget : ℝ)
    (ha : ∀ mode, 0 < amplitude mode) (hc : ∀ mode, 0 < cost mode) (hb : 0 < budget)
    (mode : I) : 0 < optimalEffort amplitude cost budget mode :=
  div_pos (mul_pos hb (ha mode))
    (mul_pos (Real.sqrt_pos.mpr (hc mode)) (weightedAmplitude_pos amplitude cost ha hc))

/-- The continuous optimum uses exactly the available budget. -/
theorem optimal_spending (amplitude cost : I → ℝ) (budget : ℝ)
    (ha : ∀ mode, 0 < amplitude mode) (hc : ∀ mode, 0 < cost mode) :
    spending cost (optimalEffort amplitude cost budget) = budget := by
  have hw := ne_of_gt (weightedAmplitude_pos amplitude cost ha hc)
  have hterm (mode : I) : cost mode * optimalEffort amplitude cost budget mode =
      (budget / weightedAmplitude amplitude cost) *
        (amplitude mode * Real.sqrt (cost mode)) := by
    have hs := ne_of_gt (Real.sqrt_pos.mpr (hc mode))
    unfold optimalEffort
    field_simp
    rw [Real.sq_sqrt (hc mode).le]
    ring
  simp only [spending, hterm, ← Finset.mul_sum]
  change (budget / weightedAmplitude amplitude cost) * weightedAmplitude amplitude cost = budget
  exact div_mul_cancel₀ _ hw

/-- The lower variance bound is attained, not merely approached. -/
theorem optimal_variance (amplitude cost : I → ℝ) (budget : ℝ)
    (ha : ∀ mode, 0 < amplitude mode) (hc : ∀ mode, 0 < cost mode) (hb : 0 < budget) :
    variance amplitude (optimalEffort amplitude cost budget) =
      weightedAmplitude amplitude cost ^ 2 / budget := by
  have hw := ne_of_gt (weightedAmplitude_pos amplitude cost ha hc)
  have hterm (mode : I) : amplitude mode ^ 2 / optimalEffort amplitude cost budget mode =
      (weightedAmplitude amplitude cost / budget) *
        (amplitude mode * Real.sqrt (cost mode)) := by
    have hs := ne_of_gt (Real.sqrt_pos.mpr (hc mode))
    have ham := ne_of_gt (ha mode)
    unfold optimalEffort
    field_simp
  simp only [variance, hterm, ← Finset.mul_sum]
  change (weightedAmplitude amplitude cost / budget) * weightedAmplitude amplitude cost = _
  ring

/-- Exact optimality among every admissible continuous positive-effort design. -/
theorem optimal_among_allocations (amplitude cost : I → ℝ) (budget : ℝ)
    (ha : ∀ mode, 0 < amplitude mode) (hc : ∀ mode, 0 < cost mode) (hb : 0 < budget)
    (effort : I → ℝ) (he : ∀ mode, 0 < effort mode) (hspend : spending cost effort ≤ budget) :
    variance amplitude (optimalEffort amplitude cost budget) ≤ variance amplitude effort := by
  rw [optimal_variance amplitude cost budget ha hc hb]
  exact allocation_lower_bound amplitude cost effort budget (fun mode ↦ (hc mode).le) he hb hspend

end Descent.Portability.OptimalMeasurementAllocation
