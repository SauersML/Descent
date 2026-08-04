/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Dirac
import Mathlib.Tactic

namespace Calibrator

/-!
# Which lineage summaries can see a multiple-merger regime?

A finite measure `Λ` on merger fractions determines the standard `Λ`-coalescent rate

`λ b k = ∫ x^(k-2) (1-x)^(b-k) dΛ(x)`

at which a specified `k`-tuple among `b` active lineages merges.  This file formalizes the
smallest possible identifiability calculation.  When `Λ` is normalized to a probability
measure, `λ 2 2 = 1` for every model: no normalized pair-merger-rate statistic can identify
the selection or reproduction regime.  At three lineages, however, `λ 3 3 = ∫ x dΛ`; the
first moment of the merger-fraction law is already visible.

This is an exact information boundary, not an asymptotic approximation.  The Dirac witnesses
show that two normalized merger laws can agree on every two-lineage rate while their
three-lineage rates are separated by an arbitrary change in merger fraction.  The final
section records the commonly used one-parameter rate chart `1 / (θ + 2)` and proves that the
three-lineage statistic identifies its parameter on the biological domain `θ > -2`.

The file deliberately does not assert that a particular selected-front model converges to a
given `Λ`-coalescent.  Such convergence requires model-specific front and genealogy theorems;
the results below say exactly what becomes identifiable once a normalized `Λ` law is given.
-/

open MeasureTheory

/-- Rate at which a specified `k`-tuple among `b` active lineages merges in a
`Λ`-coalescent.  Natural-number subtraction makes the definition total; the biological range
is `2 ≤ k ≤ b`. -/
noncomputable def lambdaCoalescentMergerRate
    (Λ : Measure ℝ) (b k : ℕ) : ℝ :=
  ∫ x, x ^ (k - 2) * (1 - x) ^ (b - k) ∂Λ

/-- **Universal pairwise blindness.**  After the conventional probability normalization of
`Λ`, every multiple-merger model has the same two-lineage merger rate. -/
@[simp] theorem lambdaCoalescentMergerRate_two_two
    (Λ : Measure ℝ) [IsProbabilityMeasure Λ] :
    lambdaCoalescentMergerRate Λ 2 2 = 1 := by
  simp [lambdaCoalescentMergerRate]

/-- Therefore no statistic that sees a normalized `Λ` only through its pair-merger rate can
distinguish two merger laws. -/
theorem lambdaCoalescent_pairwise_rate_blind
    (Λ₁ Λ₂ : Measure ℝ) [IsProbabilityMeasure Λ₁] [IsProbabilityMeasure Λ₂] :
    lambdaCoalescentMergerRate Λ₁ 2 2 =
      lambdaCoalescentMergerRate Λ₂ 2 2 := by
  simp

/-- Three simultaneous lineages expose the first moment of the merger-fraction law. -/
theorem lambdaCoalescentMergerRate_three_three (Λ : Measure ℝ) :
    lambdaCoalescentMergerRate Λ 3 3 = ∫ x, x ∂Λ := by
  simp [lambdaCoalescentMergerRate]

/-- A point-mass merger law has three-lineage rate equal to its merger fraction. -/
@[simp] theorem lambdaCoalescentMergerRate_dirac_three_three (fraction : ℝ) :
    lambdaCoalescentMergerRate (Measure.dirac fraction) 3 3 = fraction := by
  rw [lambdaCoalescentMergerRate_three_three]
  simp

/-- **Exact smallest-sample separation.**  Point-mass merger laws at fractions zero and one
are indistinguishable at two lineages and maximally separated at three lineages. -/
theorem pairwise_blind_three_lineage_separates_dirac :
    lambdaCoalescentMergerRate (Measure.dirac 0) 2 2 =
        lambdaCoalescentMergerRate (Measure.dirac 1) 2 2 ∧
      lambdaCoalescentMergerRate (Measure.dirac 0) 3 3 = 0 ∧
      lambdaCoalescentMergerRate (Measure.dirac 1) 3 3 = 1 := by
  simp

/-! ## A one-parameter merger-rate chart -/

/-- Normalized pairwise rate in the `θ` rate chart. -/
noncomputable def betaFamilyPairMergerRate (_θ : ℝ) : ℝ :=
  1

/-- Three-lineage simultaneous-merger rate in the `θ` rate chart. -/
noncomputable def betaFamilyTripleMergerRate (θ : ℝ) : ℝ :=
  1 / (θ + 2)

/-- Pairwise summaries erase the parameter completely. -/
theorem betaFamilyPairMergerRate_blind (θ₁ θ₂ : ℝ) :
    betaFamilyPairMergerRate θ₁ = betaFamilyPairMergerRate θ₂ :=
  rfl

/-- Three-lineage rates identify the parameter throughout the biological domain. -/
theorem betaFamilyTripleMergerRate_injective_on
    {θ₁ θ₂ : ℝ} (hθ₁ : -2 < θ₁) (hθ₂ : -2 < θ₂)
    (hrate : betaFamilyTripleMergerRate θ₁ = betaFamilyTripleMergerRate θ₂) :
    θ₁ = θ₂ := by
  have hne₁ : θ₁ + 2 ≠ 0 := by linarith
  have hne₂ : θ₂ + 2 ≠ 0 := by linarith
  unfold betaFamilyTripleMergerRate at hrate
  field_simp [hne₁, hne₂] at hrate
  linarith

/-- Increasing `θ` strictly decreases the visible three-lineage rate. -/
theorem betaFamilyTripleMergerRate_strictAnti
    {θ₁ θ₂ : ℝ} (hθ₁ : -2 < θ₁) (hθ : θ₁ < θ₂) :
    betaFamilyTripleMergerRate θ₂ < betaFamilyTripleMergerRate θ₁ := by
  unfold betaFamilyTripleMergerRate
  have hpos₁ : 0 < θ₁ + 2 := by linarith
  have hpos₂ : 0 < θ₂ + 2 := by linarith
  exact one_div_lt_one_div_of_lt hpos₁ (by linarith)

end Calibrator
