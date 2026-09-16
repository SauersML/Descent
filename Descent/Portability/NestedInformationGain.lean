/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.ReportConditionalRiskLaw

assert_below Descent.Decision Descent.Program

/-!
# Nested information: the exact gain of a richer genetic representation

Let `F ⊆ G` be two information fields -- `F = σ(S, A, C)` the retained scores,
ancestry and context, `G = σ(G, A, C)` the genome with the same context -- and let
`p₀ = E[Y ∣ F]`, `p₁ = E[Y ∣ G]` be the two optimal predictors.  Then

`E[(Y − p₀)²] − E[(Y − p₁)²] = E[(p₁ − p₀)²]`  (`nested_information_gain`).

For a `{0,1}` outcome the left side is the improvement in optimal Brier risk, so the
recoverable gain is exactly the variation in true individual probability that the
retained representation erased.  It is the binary specialisation of the corpus's
nested-information decomposition (`ReportConditionalRiskLaw.risk_pythagoras`), stated
so that the two conditional expectations are Mathlib's and nothing is postulated about
either field: no independence, no Gaussianity, no finiteness.

Two companions fix the hypotheses of the other two design results:

* `residual_feature_orthogonal`: conditional centring `r = φ − E[φ ∣ Z]` makes the
  residual feature orthogonal to every square-integrable `Z`-measurable base predictor.
  This is the hypothesis `ResidualGeneticRepair` takes on its expectation functional.
* `approximation_excess_le`: a `G`-measurable approximation of the conditional
  probability within `ε` almost everywhere costs at most `ε²` in squared risk.  This is
  the report-level approximation statement: judge a compression by the probability
  reports it preserves, not by which posterior moments it keeps.

## Empirical status

None. Every body is an instance of conditional-mean Pythagoras on a probability space;
nothing here names a cohort or a measurement.
-/

namespace Descent.Portability.NestedInformationGain

open MeasureTheory

variable {Ω : Type*} {m₀ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {Y : Ω → ℝ}

/-- **Nested information gain.**  With `p₀ = E[Y ∣ F]` and `p₁ = E[Y ∣ G]` for `F ⊆ G`,
`E[(Y − p₀)²] − E[(Y − p₁)²] = E[(p₁ − p₀)²]`.  For a binary outcome this is the
exact improvement in optimal Brier risk available from the richer information. -/
theorem nested_information_gain {mF mG : MeasurableSpace Ω} (hFG : mF ≤ mG)
    (hG : mG ≤ m₀)
    (hY : MemLp Y 2 μ) :
    (∫ ω, (Y ω - μ[Y | mF] ω) ^ 2 ∂μ) - (∫ ω, (Y ω - μ[Y | mG] ω) ^ 2 ∂μ)
      = ∫ ω, (μ[Y | mG] ω - μ[Y | mF] ω) ^ 2 ∂μ := by
  have h := ReportConditionalRiskLaw.risk_pythagoras hG hY (hY.condExp (m := mF))
    (stronglyMeasurable_condExp.mono hFG)
  linarith

/-- The richer information never loses: the optimal risk on `G` is at most that on `F`. -/
theorem nested_information_gain_nonneg {mF mG : MeasurableSpace Ω} (hFG : mF ≤ mG)
    (hG : mG ≤ m₀) (hY : MemLp Y 2 μ) :
    (∫ ω, (Y ω - μ[Y | mG] ω) ^ 2 ∂μ) ≤ ∫ ω, (Y ω - μ[Y | mF] ω) ^ 2 ∂μ := by
  have h := nested_information_gain hFG hG hY
  have hnn : 0 ≤ ∫ ω, (μ[Y | mG] ω - μ[Y | mF] ω) ^ 2 ∂μ :=
    integral_nonneg fun _ ↦ sq_nonneg _
  linarith

/-- **Conditional centring gives orthogonality.**  For `r = φ − E[φ ∣ Z]` and any
square-integrable `Z`-measurable base predictor `f₀`, `E[r f₀] = 0`. -/
theorem residual_feature_orthogonal {m : MeasurableSpace Ω} (hm : m ≤ m₀)
    {φ f₀ : Ω → ℝ}
    (hφ : MemLp φ 2 μ) (hf : MemLp f₀ 2 μ) (hfm : StronglyMeasurable[m] f₀) :
    (∫ ω, (φ ω - μ[φ | m] ω) * f₀ ω ∂μ) = 0 :=
  ReportConditionalRiskLaw.residual_orthogonal hm hφ hf hfm

/-- **Report approximation.**  A `G`-measurable approximation `g` of the conditional
mean within `ε` almost everywhere costs at most `ε²` in squared risk. -/
theorem approximation_excess_le {mG : MeasurableSpace Ω} (hG : mG ≤ m₀) (hY : MemLp Y 2 μ)
    {g : Ω → ℝ} (hg : MemLp g 2 μ) (hgm : StronglyMeasurable[mG] g) {ε : ℝ}
    (hε : ∀ᵐ ω ∂μ, |μ[Y | mG] ω - g ω| ≤ ε) :
    (∫ ω, (Y ω - g ω) ^ 2 ∂μ) - (∫ ω, (Y ω - μ[Y | mG] ω) ^ 2 ∂μ) ≤ ε ^ 2 := by
  rw [ReportConditionalRiskLaw.risk_pythagoras hG hY hg hgm]
  have hd : MemLp (μ[Y | mG] - g) 2 μ := hY.condExp.sub hg
  have hle : ∀ᵐ ω ∂μ, (μ[Y | mG] ω - g ω) ^ 2 ≤ ε ^ 2 := by
    filter_upwards [hε] with ω hω
    exact sq_le_sq' (abs_le.mp hω).1 (abs_le.mp hω).2
  have hint : (∫ ω, (μ[Y | mG] ω - g ω) ^ 2 ∂μ) ≤ ∫ _ω, ε ^ 2 ∂μ :=
    integral_mono_ae hd.integrable_sq (integrable_const _) hle
  have hconst : (∫ _ω, ε ^ 2 ∂μ) = ε ^ 2 := by simp
  linarith

/-- **Fitted risk decomposes exactly.**  Any square-integrable `G`-measurable fitted
predictor `p̂` pays the oracle risk of `G` plus its own estimation error,
`E[(Y − p̂)²] = E[(Y − E[Y ∣ G])²] + E[(p̂ − E[Y ∣ G])²]`: the realised benefit of
richer information is its oracle gain less the extra estimation error it costs. -/
theorem fitted_risk_decomposition {mG : MeasurableSpace Ω} (hG : mG ≤ m₀) (hY : MemLp Y 2 μ)
    {g : Ω → ℝ} (hg : MemLp g 2 μ) (hgm : StronglyMeasurable[mG] g) :
    (∫ ω, (Y ω - g ω) ^ 2 ∂μ) =
      (∫ ω, (Y ω - μ[Y | mG] ω) ^ 2 ∂μ) + ∫ ω, (μ[Y | mG] ω - g ω) ^ 2 ∂μ :=
  ReportConditionalRiskLaw.risk_pythagoras hG hY hg hgm

end Descent.Portability.NestedInformationGain
