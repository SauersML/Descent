/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.ReportConditionalRiskLaw
import Mathlib.Probability.CondVar

assert_below Descent.Decision Descent.Program

/-!
# Exact information classification for individual loss

Apply these theorems to L=(Y-score)^2, requiring L in L² (a fourth-moment
condition on the residual). The smaller sigma field represents distance and
the larger one any specified richer pre-outcome information. No ancestry or
context variable is assumed informative or uninformative.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.LossInformationClassification

open MeasureTheory ProbabilityTheory ReportConditionalRiskLaw
open scoped ProbabilityTheory

variable {Ω : Type*} {m₀ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {mD mW : MeasurableSpace Ω} {L : Ω → ℝ}

/-- Variance captured by the optimal predictor with the specified information. -/
noncomputable def captured (μ : Measure Ω) (m : MeasurableSpace Ω) (L : Ω → ℝ) : ℝ :=
  ∫ ω, (μ[L | m] ω - μ[L]) ^ 2 ∂μ

theorem captured_eq_variance (hm : mD ≤ m₀) :
    captured μ mD L = Var[μ[L | mD]; μ] := by
  rw [variance_eq_integral (stronglyMeasurable_condExp.mono hm).aemeasurable,
    integral_condExp hm]
  rfl

/-- Unpredictable given W, predictable but discarded by D, and retained by D.
The terms are derived from conditional expectation on one probability space. -/
theorem variance_three_way (hDW : mD ≤ mW) (hW : mW ≤ m₀) (hL : MemLp L 2 μ) :
    Var[L; μ] = captured μ mD L +
      (∫ ω, (μ[L | mW] ω - μ[L | mD] ω) ^ 2 ∂μ) +
      ∫ ω, Var[L; μ | mW] ω ∂μ := by
  have h := nonlinear_risk_decomposition_conditional_variance hDW hW hL
    (memLp_const (μ[L])) (stronglyMeasurable_const : StronglyMeasurable[mD] (fun _ : Ω ↦ μ[L]))
  rw [variance_eq_integral hL.aestronglyMeasurable.aemeasurable]
  change (∫ ω, (L ω - μ[L]) ^ 2 ∂μ) = _
  change (∫ ω, (L ω - μ[L]) ^ 2 ∂μ) =
    (∫ ω, Var[L; μ | mW] ω ∂μ) +
      (∫ ω, (μ[L | mW] ω - μ[L | mD] ω) ^ 2 ∂μ) + captured μ mD L at h
  linarith

/-- Exact incremental information gain, including when W adds socioeconomic
information to distance. No causal interpretation is assigned to the gain. -/
theorem captured_gain (hDW : mD ≤ mW) (hW : mW ≤ m₀) (hL : MemLp L 2 μ) :
    captured μ mW L - captured μ mD L =
      ∫ ω, (μ[L | mW] ω - μ[L | mD] ω) ^ 2 ∂μ := by
  have h := variance_three_way hDW hW hL
  have hself := variance_three_way (le_refl mW) hW hL
  simp only [sub_self, zero_pow (by decide : 2 ≠ 0), integral_zero, add_zero] at hself
  linarith

/-- Necessary and sufficient condition for distance to retain all expected-loss
information available in W. This is an almost-sure statement, not pointwise. -/
theorem no_information_loss_iff (hDW : mD ≤ mW) (hW : mW ≤ m₀)
    (hL : MemLp L 2 μ) :
    captured μ mW L = captured μ mD L ↔ μ[L | mW] =ᵐ[μ] μ[L | mD] := by
  have hi := (hL.condExp (m := mW)).sub (hL.condExp (m := mD))
  have hz := integral_eq_zero_iff_of_nonneg
    (fun ω ↦ sq_nonneg (μ[L | mW] ω - μ[L | mD] ω)) hi.integrable_sq
  rw [← sub_eq_zero, captured_gain hDW hW hL]
  rw [hz]
  constructor
  · intro h
    filter_upwards [h] with ω hω
    exact sub_eq_zero.mp (sq_eq_zero_iff.mp hω)
  · intro h
    filter_upwards [h] with ω hω
    simp [hω]

/-- Context increases the oracle explained fraction by exactly the normalized
conditional-mean gap, with positive total variance required for reporting. -/
theorem explained_fraction_gain (hDW : mD ≤ mW) (hW : mW ≤ m₀)
    (hL : MemLp L 2 μ) (hpos : 0 < Var[L; μ]) :
    0 ≤ captured μ mW L / Var[L; μ] - captured μ mD L / Var[L; μ] ∧
      captured μ mW L / Var[L; μ] - captured μ mD L / Var[L; μ] =
        (∫ ω, (μ[L | mW] ω - μ[L | mD] ω) ^ 2 ∂μ) / Var[L; μ] := by
  rw [← sub_div, captured_gain hDW hW hL]
  exact ⟨div_nonneg (integral_nonneg (fun _ ↦ sq_nonneg _)) hpos.le, rfl⟩

/-- Strict improvement is equivalent to failure of almost-sure sufficiency. -/
theorem strict_information_gain_iff (hDW : mD ≤ mW) (hW : mW ≤ m₀)
    (hL : MemLp L 2 μ) :
    captured μ mD L < captured μ mW L ↔ ¬ μ[L | mW] =ᵐ[μ] μ[L | mD] := by
  have hnonneg : 0 ≤ captured μ mW L - captured μ mD L := by
    rw [captured_gain hDW hW hL]
    exact integral_nonneg (fun _ ↦ sq_nonneg _)
  have heq := no_information_loss_iff hDW hW hL
  constructor
  · intro hlt he
    have := heq.mpr he
    linarith
  · intro hne
    have hn : captured μ mW L ≠ captured μ mD L := fun h ↦ hne (heq.mp h)
    exact lt_of_le_of_ne (sub_nonneg.mp hnonneg) (Ne.symm hn)

end Descent.Portability.LossInformationClassification
