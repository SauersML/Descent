/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.EndToEndSensitivityRates
import Descent.Portability.EndToEndCorrelationSeries
import Mathlib.Analysis.Calculus.SmoothSeries

assert_below Descent.Decision Descent.Program

/-!
# The sensitivity of the expected squared correlation

`EndToEndCorrelationSeries` writes the expected squared correlation `E[N / D]` of a deme, for a
score and an outcome in the unit interval, as the series `Σₖ cₖ · (U_{4(k+1)} H_{4(k+1)}(x₀))` of
propagated moments of `N (1 - D)ᵏ`.  `EndToEndSensitivityRates` differentiates each term along a
history of segment epochs and fixed pulses.  This module differentiates the series termwise.

Summability.  When `0 ≤ N ≤ D ≤ 1` the partial sums of `N (1 - D)ᵏ` are at most one
(`sum_range_expansion_terms_le_one`, from `PositiveRatioExpansion.tsum_expansion_terms`), so under
every Markov kernel the expected terms are nonnegative with partial sums at most one and form a
summable series (`summable_integral_seriesTerm`).

The derivative.  Along a segment history, if the stagewise sensitivities of the terms are bounded
on `(0, 1)` by a summable sequence, the expected squared correlation is differentiable at every
interior parameter with derivative the series of the term sensitivities
(`hasDerivAt_expectedSquaredCorrelation_segmentHistory`), by
`hasDerivAt_tsum_of_isPreconnected` on the open interval.

Scope.  The summable bound on the term sensitivities is a hypothesis; no bound for the propagator
derivatives at growing budgets is proved here.  The score and the outcome take values in the unit
interval.

## Empirical status

None.  The bodies here are a geometric partial-sum bound, integrals of bounded polynomials and
termwise differentiation of a series of supplied sensitivities, so no measurement can bear on them.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.EndToEndSensitivitySeries

open MeasureTheory ProbabilityTheory MvPolynomial Descent.Coalescent PartialHaplotypeCarrier
  PartialHaplotypeDualGenerator PartialHaplotypeDualSemigroup NeutralFellerGenerator
  NeutralPolynomialSemigroup PartialHaplotypeMicroscopicApproximation PartialHaplotypePulseKernel
  NeutralPulseHistoryKernel ReplicaMetricInstances PositiveRatioExpansion EndToEndPortabilityLaw
  EndToEndCorrelationSeries EndToEndSensitivityLaw EndToEndSensitivityRates
open scoped Matrix NNReal

noncomputable section

/-- The partial sums of `N (1 - D)ᵏ` are at most one when `0 ≤ N ≤ D ≤ 1`. -/
theorem sum_range_expansion_terms_le_one {num den : ℝ} (hnum : 0 ≤ num) (hle : num ≤ den)
    (hden : den ≤ 1) (n : ℕ) : ∑ k ∈ Finset.range n, num * (1 - den) ^ k ≤ 1 := by
  have hterm : ∀ k : ℕ, 0 ≤ num * (1 - den) ^ k :=
    fun k ↦ mul_nonneg hnum (pow_nonneg (by linarith) k)
  refine ((summable_expansion_terms num den hnum hle hden).sum_le_tsum (Finset.range n)
    fun k _ ↦ hterm k).trans ?_
  rw [tsum_expansion_terms num den hnum hle hden]
  split_ifs with hpositive
  · rw [div_le_iff₀ hpositive, one_mul]
    exact hle
  · exact zero_le_one

variable {Deme Locus : Type*} {Allele : Locus → Type*}
variable [Fintype Deme] [DecidableEq Deme] [Fintype Locus] [DecidableEq Locus]
  [∀ ℓ, Fintype (Allele ℓ)] [∀ ℓ, DecidableEq (Allele ℓ)]

/-- **The expected series terms are summable.**  For a score and an outcome in the unit interval,
under every Markov kernel the expectations of `N (1 - D)ᵏ` form a summable series. -/
theorem summable_integral_seriesTerm
    (κ : Kernel (FrequencyState Deme Locus Allele) (FrequencyState Deme Locus Allele))
    [IsMarkovKernel κ] (x0 : FrequencyState Deme Locus Allele) (deme : Deme)
    (score outcome : FullHaplotype Locus Allele → ℝ)
    (hscore0 : ∀ hap, 0 ≤ score hap) (hscore1 : ∀ hap, score hap ≤ 1)
    (houtcome0 : ∀ hap, 0 ≤ outcome hap) (houtcome1 : ∀ hap, outcome hap ≤ 1) :
    Summable fun k : ℕ ↦ ∫ y, correlationNumerator (stateLaw y deme) score outcome
      * (1 - correlationDenominator (stateLaw y deme) score outcome) ^ k ∂(κ x0) := by
  have hbounds : ∀ y : FrequencyState Deme Locus Allele,
      0 ≤ correlationNumerator (stateLaw y deme) score outcome
        ∧ correlationNumerator (stateLaw y deme) score outcome
          ≤ correlationDenominator (stateLaw y deme) score outcome
        ∧ correlationDenominator (stateLaw y deme) score outcome ≤ 1 := fun y ↦
    ⟨correlationNumerator_nonneg _ score outcome,
      correlationNumerator_le_denominator _ score outcome,
      correlationDenominator_le_one _ score outcome hscore0 hscore1 houtcome0 houtcome1⟩
  have hintegrable : ∀ k : ℕ, Integrable (fun y ↦
      correlationNumerator (stateLaw y deme) score outcome
        * (1 - correlationDenominator (stateLaw y deme) score outcome) ^ k) (κ x0) := by
    intro k
    have hfunction : (fun y : FrequencyState Deme Locus Allele ↦
        correlationNumerator (stateLaw y deme) score outcome
          * (1 - correlationDenominator (stateLaw y deme) score outcome) ^ k)
        = ⇑(polynomialFunction (seriesTermPolynomial deme score outcome k)) :=
      funext fun y ↦ (polynomialFunction_seriesTermPolynomial deme score outcome k y).symm
    rw [hfunction]
    exact (BoundedContinuousFunction.mkOfCompact
      (polynomialFunction (seriesTermPolynomial deme score outcome k))).integrable _
  refine summable_of_sum_range_le (c := 1)
    (fun k ↦ integral_nonneg fun y ↦
      mul_nonneg (hbounds y).1 (pow_nonneg (sub_nonneg.mpr (hbounds y).2.2) k)) fun n ↦ ?_
  rw [← integral_finset_sum (Finset.range n) fun k _ ↦ hintegrable k]
  calc ∫ y, ∑ k ∈ Finset.range n, correlationNumerator (stateLaw y deme) score outcome
          * (1 - correlationDenominator (stateLaw y deme) score outcome) ^ k ∂(κ x0)
      ≤ ∫ _y, (1 : ℝ) ∂(κ x0) :=
        integral_mono (integrable_finset_sum _ fun k _ ↦ hintegrable k) (integrable_const 1)
          fun y ↦ sum_range_expansion_terms_le_one (hbounds y).1 (hbounds y).2.1 (hbounds y).2.2 n
    _ = 1 := by rw [integral_const, measureReal_univ_eq_one, one_smul]

/-- **The sensitivity of the expected squared correlation along a segment history.**  For a score
and an outcome in the unit interval, if the stagewise sensitivities of the series terms are bounded
on `(0, 1)` by a summable sequence, then at every interior parameter the expected squared
correlation has derivative the series of the term sensitivities. -/
theorem hasDerivAt_expectedSquaredCorrelation_segmentHistory (ℓ₀ : Locus)
    (hap₀ : FullHaplotype Locus Allele) {θ₀ : ℝ} (hθ₀ : θ₀ ∈ Set.Ioo (0 : ℝ) 1)
    (history : List ((NeutralRates Deme Locus Allele × NeutralRates Deme Locus Allele × ℝ≥0)
      ⊕ PulseMatrix Deme))
    (x0 : FrequencyState Deme Locus Allele) (deme : Deme)
    (score outcome : FullHaplotype Locus Allele → ℝ)
    (hscore0 : ∀ hap, 0 ≤ score hap) (hscore1 : ∀ hap, score hap ≤ 1)
    (houtcome0 : ∀ hap, 0 ≤ outcome hap) (houtcome1 : ∀ hap, outcome hap ≤ 1)
    {bound : ℕ → ℝ} (hsummable : Summable bound)
    (hbound : ∀ k : ℕ, ∀ θ ∈ Set.Ioo (0 : ℝ) 1,
      |historySensitivity (fun _ ↦ 4 * (k + 1)) θ (history.map segmentEvent)
        (familyDerivative (fun _ ↦ 4 * (k + 1)) θ)
        (budgetCoefficients ℓ₀ (fun _ ↦ 4 * (k + 1)) (seriesTermPolynomial deme score outcome k))
        (budgetMomentFeature (fun _ ↦ 4 * (k + 1)) x0)| ≤ bound k) :
    HasDerivAt (fun θ ↦ expectedSquaredCorrelation
        (historyEventKernel ℓ₀ hap₀ ((history.map segmentEvent).map fun event ↦ event θ)) x0 deme
        score outcome)
      (∑' k : ℕ, historySensitivity (fun _ ↦ 4 * (k + 1)) θ₀ (history.map segmentEvent)
        (familyDerivative (fun _ ↦ 4 * (k + 1)) θ₀)
        (budgetCoefficients ℓ₀ (fun _ ↦ 4 * (k + 1)) (seriesTermPolynomial deme score outcome k))
        (budgetMomentFeature (fun _ ↦ 4 * (k + 1)) x0)) θ₀ := by
  have hfun : (fun θ ↦ expectedSquaredCorrelation
      (historyEventKernel ℓ₀ hap₀ ((history.map segmentEvent).map fun event ↦ event θ)) x0 deme
      score outcome)
      = fun θ ↦ ∑' k : ℕ, budgetCoefficients ℓ₀ (fun _ ↦ 4 * (k + 1))
          (seriesTermPolynomial deme score outcome k)
        ⬝ᵥ (historyEventPropagator (fun _ ↦ 4 * (k + 1))
            ((history.map segmentEvent).map fun event ↦ event θ)
          *ᵥ budgetMomentFeature (fun _ ↦ 4 * (k + 1)) x0) :=
    funext fun θ ↦ expectedSquaredCorrelation_historyEventKernel ℓ₀ hap₀ _ x0 deme score outcome
      hscore0 hscore1 houtcome0 houtcome1
  have hterms : Summable fun k : ℕ ↦ budgetCoefficients ℓ₀ (fun _ ↦ 4 * (k + 1))
        (seriesTermPolynomial deme score outcome k)
      ⬝ᵥ (historyEventPropagator (fun _ ↦ 4 * (k + 1))
          ((history.map segmentEvent).map fun event ↦ event θ₀)
        *ᵥ budgetMomentFeature (fun _ ↦ 4 * (k + 1)) x0) := by
    haveI := isMarkovKernel_historyEventKernel ℓ₀ hap₀
      ((history.map segmentEvent).map fun event ↦ event θ₀)
    exact (summable_integral_seriesTerm
      (historyEventKernel ℓ₀ hap₀ ((history.map segmentEvent).map fun event ↦ event θ₀)) x0 deme
      score outcome hscore0 hscore1 houtcome0 houtcome1).congr fun k ↦
        integral_seriesTerm_historyEventKernel ℓ₀ hap₀ _ x0 deme score outcome k
  rw [hfun]
  exact hasDerivAt_tsum_of_isPreconnected hsummable isOpen_Ioo isPreconnected_Ioo
    (fun k θ hθ ↦ hasDerivAt_dotProduct_segmentHistory (fun _ ↦ 4 * (k + 1)) hθ history _ _)
    (fun k θ hθ ↦ by
      rw [Real.norm_eq_abs]
      exact hbound k θ hθ) hθ₀ hterms hθ₀

end

end Descent.Portability.EndToEndSensitivitySeries
