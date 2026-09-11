/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.AncientPrediction.Risk
import Mathlib.MeasureTheory.Function.ConditionalExpectation.CondexpL2

assert_below Descent.Decision Descent.Program

/-!
# Actual conditional-expectation value of information

Theorem 3 with nested sigma-algebras and genuine L² conditional expectations.
The orthogonality conditions of `information_gain_budget` are derived here.
The implemented richer-information predictor can be arbitrary and incorrect.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.AncientPrediction

open MeasureTheory
open scoped RealInnerProductSpace
variable {Ω : Type*} {m₀ m₁ m : MeasurableSpace Ω} {μ : @Measure Ω m}

theorem conditional_residual_orthogonal (hm : m₁ ≤ m) (Y g : Lp ℝ 2 μ)
    (hg : AEStronglyMeasurable[m₁] g μ) :
    ⟪Y - (condExpL2 ℝ ℝ hm Y : Lp ℝ 2 μ), g⟫ = 0 := by
  rw [inner_sub_left, inner_condExpL2_eq_inner_fun hm Y g hg, sub_self]

/-- Equations (5.1) and (5.2), without assumed zero cross terms. -/
theorem conditional_information_budget (h₀₁ : m₀ ≤ m₁) (h₁ : m₁ ≤ m)
    (Y f : Lp ℝ 2 μ) (hf : AEStronglyMeasurable[m₁] f μ) :
    ‖Y - f‖ ^ 2 - ‖Y - (condExpL2 ℝ ℝ (h₀₁.trans h₁) Y : Lp ℝ 2 μ)‖ ^ 2 =
      ‖f - (condExpL2 ℝ ℝ h₁ Y : Lp ℝ 2 μ)‖ ^ 2 -
      ‖(condExpL2 ℝ ℝ h₁ Y : Lp ℝ 2 μ) -
        (condExpL2 ℝ ℝ (h₀₁.trans h₁) Y : Lp ℝ 2 μ)‖ ^ 2 := by
  have hmeas₁ := aestronglyMeasurable_condExpL2 (𝕜 := ℝ) h₁ Y
  have hmeas₀ := (aestronglyMeasurable_condExpL2 (𝕜 := ℝ) (h₀₁.trans h₁) Y).mono h₀₁
  apply information_gain_budget
  · rw [inner_sub_right, conditional_residual_orthogonal h₁ Y _ hmeas₁,
      conditional_residual_orthogonal h₁ Y _ hmeas₀, sub_self]
  · rw [inner_sub_right, conditional_residual_orthogonal h₁ Y f hf,
      conditional_residual_orthogonal h₁ Y _ hmeas₁, sub_self]

theorem conditional_information_gain (h₀₁ : m₀ ≤ m₁) (h₁ : m₁ ≤ m) (Y : Lp ℝ 2 μ) :
    ‖Y - (condExpL2 ℝ ℝ (h₀₁.trans h₁) Y : Lp ℝ 2 μ)‖ ^ 2 -
      ‖Y - (condExpL2 ℝ ℝ h₁ Y : Lp ℝ 2 μ)‖ ^ 2 =
      ‖(condExpL2 ℝ ℝ h₁ Y : Lp ℝ 2 μ) -
        (condExpL2 ℝ ℝ (h₀₁.trans h₁) Y : Lp ℝ 2 μ)‖ ^ 2 := by
  have h := conditional_information_budget h₀₁ h₁ Y
    (condExpL2 ℝ ℝ h₁ Y) (aestronglyMeasurable_condExpL2 h₁ Y)
  simp only [sub_self, norm_zero, zero_pow (by decide : 2 ≠ 0), zero_sub] at h
  linarith

end Descent.Portability.AncientPrediction
