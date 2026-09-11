/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.AuditVarianceGeometry

assert_below Descent.Decision Descent.Program

/-!
Decision-Directed Portability, Theorem 14: exact coordinate minimization
for the dual labeling design. The square-root rule is clipped to the actual
probability floor and cap. Zero variance contributions and a zero budget
multiplier are included without division by zero in the allocation rule.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.AuditAllocationCoordinate

open AuditVarianceGeometry

/-- A coordinate of the labeling-design Lagrangian. -/
noncomputable def objective (A b p : ℝ) : ℝ := A / p + b * p

/-- The exact coordinate choice, with the zero-multiplier problem solved separately. -/
noncomputable def choice (A b floor : ℝ) : ℝ :=
  if b = 0 then 1 else clip floor 1 (Real.sqrt (A / b))

/-- Positive floors make both the chosen and competing probabilities defined. -/
theorem choice_mem (A b floor : ℝ) (hf : floor ≤ 1) :
    choice A b floor ∈ Set.Icc floor 1 := by
  unfold choice
  split_ifs
  · exact ⟨hf, le_refl 1⟩
  · exact clip_mem floor 1 _ hf

/-- Exact algebraic difference, with denominators retained until positivity is available. -/
theorem objective_difference (A b p r : ℝ) (hp : p ≠ 0) (hr : r ≠ 0) :
    p * r * (objective A b p - objective A b r) = (p - r) * (b * p * r - A) := by
  unfold objective
  field_simp
  ring

/-- For a positive cost multiplier the clipped square root minimizes the entire interval. -/
theorem positive_multiplier_minimum (A b floor p : ℝ) (hA : 0 ≤ A) (hb : 0 < b)
    (hf : 0 < floor) (hp : p ∈ Set.Icc floor 1) :
    objective A b (clip floor 1 (Real.sqrt (A / b))) ≤ objective A b p := by
  let s := Real.sqrt (A / b)
  let r := clip floor 1 s
  have hs : 0 ≤ s := Real.sqrt_nonneg _
  have hsq : b * s ^ 2 = A := by
    dsimp [s]
    rw [Real.sq_sqrt (div_nonneg hA hb.le)]
    exact mul_div_cancel₀ A hb.ne'
  have hr : 0 < r := hf.trans_le (clip_mem floor 1 s (hp.1.trans hp.2)).1
  have hpp : 0 < p := hf.trans_le hp.1
  have hn : 0 ≤ (p - r) * (r - s) := by
    have hh := clip_normal floor 1 s p hp
    change (p - r) * (s - r) ≤ 0 at hh
    nlinarith
  have hfirst : 0 ≤ b * r * (p - r) ^ 2 := by positivity
  have hsecond : 0 ≤ b * (r + s) * ((p - r) * (r - s)) :=
    mul_nonneg (mul_nonneg hb.le (add_nonneg hr.le hs)) hn
  have he : (p - r) * (b * p * r - A) =
      b * r * (p - r) ^ 2 + b * (r + s) * ((p - r) * (r - s)) := by
    rw [← hsq]
    ring
  have hd := objective_difference A b p r hpp.ne' hr.ne'
  rw [he] at hd
  have hden : 0 < p * r := mul_pos hpp hr
  change objective A b r ≤ objective A b p
  nlinarith

/-- With zero multiplier, sampling probability one minimizes the reciprocal variance term. -/
theorem zero_multiplier_minimum (A p : ℝ) (hA : 0 ≤ A) (hp : 0 < p ∧ p ≤ 1) :
    objective A 0 1 ≤ objective A 0 p := by
  simp only [objective, div_one, zero_mul, add_zero]
  apply (le_div_iff₀ hp.1).mpr
  nlinarith

/-- The computed choice attains the coordinate infimum, including both degeneracies. -/
theorem choice_minimum (A b floor p : ℝ) (hA : 0 ≤ A) (hb : 0 ≤ b)
    (hf : 0 < floor) (hp : p ∈ Set.Icc floor 1) :
    objective A b (choice A b floor) ≤ objective A b p := by
  by_cases hz : b = 0
  · rw [choice, if_pos hz, hz]
    exact zero_multiplier_minimum A p hA ⟨hf.trans_le hp.1, hp.2⟩
  · rw [choice, if_neg hz]
    exact positive_multiplier_minimum A b floor p hA (lt_of_le_of_ne hb (Ne.symm hz)) hf hp

/-- A zero variance contribution with a positive multiplier selects exactly the floor. -/
theorem zero_contribution (b floor : ℝ) (hb : 0 < b) (hf : 0 ≤ floor) :
    choice 0 b floor = floor := by
  simp only [choice, if_neg hb.ne', zero_div, Real.sqrt_zero, clip]
  rw [min_eq_right (by norm_num), max_eq_left hf]

end Descent.Portability.AuditAllocationCoordinate
