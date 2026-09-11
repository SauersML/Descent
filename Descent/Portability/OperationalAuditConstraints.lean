/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Layer
import Mathlib.Tactic

assert_below Descent.Decision Descent.Program

/-!
Decision-Directed Portability, Theorem 18: fixed operational requirements
compile to linear targets on expected frame masses. Positive-denominator
conditions are retained. These are ratios of population-average masses,
not expectations of random empirical ratios.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.OperationalAuditConstraints

open scoped BigOperators

variable {ι : Type*} [Fintype ι]

/-- Known frame alert mass for a fixed, possibly randomized, decision rule. -/
noncomputable def alert (w d : ι → ℝ) : ℝ := ∑ i, w i * d i

/-- Frame prevalence, determined by the target outcome means. -/
noncomputable def prevalence (w μ : ι → ℝ) : ℝ := ∑ i, w i * μ i

/-- Frame true-positive mass for the fixed rule. -/
noncomputable def truePositive (w d μ : ι → ℝ) : ℝ := ∑ i, w i * d i * μ i

/-- Precision certification preserves the strictly positive alert denominator. -/
theorem precision_requirement (A T p₀ : ℝ) (hA : 0 < A) :
    p₀ ≤ T / A ↔ 0 ≤ T - p₀ * A := by
  rw [le_div_iff₀ hA]
  exact sub_nonneg.symm

/-- Recall certification preserves the strictly positive prevalence denominator. -/
theorem recall_requirement (π T r₀ : ℝ) (hπ : 0 < π) :
    r₀ ≤ T / π ↔ 0 ≤ T - r₀ * π := by
  rw [le_div_iff₀ hπ]
  exact sub_nonneg.symm

/-- The F1 count denominator simplifies to alert mass plus prevalence. -/
theorem f1_denominator (A T π : ℝ) : 2 * T + (A - T) + (π - T) = A + π := by
  ring

/-- F1 certification is affine at a fixed required F1 level. -/
theorem f1_requirement (A T π f₀ : ℝ) (h : 0 < A + π) :
    f₀ ≤ 2 * T / (A + π) ↔ 0 ≤ 2 * T - f₀ * (A + π) := by
  rw [le_div_iff₀ h]
  exact sub_nonneg.symm

/-- False-positive-rate certification keeps the nonzero nondisease mass condition. -/
theorem false_positive_requirement (A T π α : ℝ) (hπ : π < 1) :
    (A - T) / (1 - π) ≤ α ↔ A - T - α * (1 - π) ≤ 0 := by
  rw [div_le_iff₀ (sub_pos.mpr hπ)]
  exact sub_nonpos.symm

/-- Classification net benefit is an affine label contrast. -/
theorem net_benefit (A T c : ℝ) : T - c * (A - T) = (1 + c) * T - c * A := by
  ring

/-- Comparing two rules' net benefits again needs only a paired label contrast. -/
theorem net_benefit_difference (A₀ T₀ A₁ T₁ c : ℝ) :
    (T₁ - c * (A₁ - T₁)) - (T₀ - c * (A₀ - T₀)) =
      (1 + c) * (T₁ - T₀) - c * (A₁ - A₀) := by
  ring

/-- The recall requirement compiles to one explicit linear mean summary. -/
theorem recall_linear_target (w d μ : ι → ℝ) (r₀ : ℝ) :
    truePositive w d μ - r₀ * prevalence w μ = ∑ i, w i * (d i - r₀) * μ i := by
  unfold truePositive prevalence
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- The F1 requirement has a known constant and a single linear label contrast. -/
theorem f1_linear_target (w d μ : ι → ℝ) (f₀ : ℝ) :
    2 * truePositive w d μ - f₀ * (alert w d + prevalence w μ) =
      -f₀ * alert w d + ∑ i, w i * (2 * d i - f₀) * μ i := by
  have hh : (∑ i, w i * (2 * d i - f₀) * μ i) =
      2 * truePositive w d μ - f₀ * prevalence w μ := by
    unfold truePositive prevalence
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hh]
  ring

/-- Only disagreement rows contribute to the paired true-positive contrast. -/
theorem paired_true_positive (w d₀ d₁ μ : ι → ℝ) :
    truePositive w d₁ μ - truePositive w d₀ μ =
      ∑ i, w i * (d₁ i - d₀ i) * μ i := by
  unfold truePositive
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

end Descent.Portability.OperationalAuditConstraints
