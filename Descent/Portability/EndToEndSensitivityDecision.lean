/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.EndToEndSensitivityRatePathMetrics
import Descent.Portability.EndToEndLogLossLaw
import Descent.Portability.EndToEndDecisionLaw

assert_below Descent.Decision Descent.Program

/-!
# The sensitivity of the logarithmic and decision metrics to demography

`EndToEndLogLossLaw` writes the expected entropy of a report law, the expected conditional entropy
(the expected repaired log loss) and the expected mutual information of score and outcome as
series over `k` of budget-`(k + 2)` pairings with the propagated moments, divided by `k + 1`.  It
also shows that the expected log loss of fixed group forecasts is a single budget-1 pairing.
`EndToEndDecisionLaw` writes the expected confusion table of a rule, the expected net benefit and
threshold-metric portability through the budget-1 moments.  This module differentiates all these
metrics along a history of segment epochs and fixed pulses, and along a segment of two continuous
rate histories.

Series of pairings.  If a function of the parameter is, at every parameter, the sum of a series of
propagated pairings divided by `k + 1`, and the stagewise sensitivities of the terms are bounded
on `(0, 1)` by a summable sequence, then at every interior parameter the function has as
derivative the series of the term sensitivities.  This holds along a segment history
(`hasDerivAt_of_hasSum_dotProduct_segmentHistory`) and along a segment of rate histories, with
the sensitivity matrix `ratePathSensitivity` (`hasDerivAt_of_hasSum_dotProduct_rateSegment`).  The
proof is `hasDerivAt_tsum_of_isPreconnected` on the open interval.

The entropies.  Under the history kernel and under the rate-history kernel, each of the three
expected entropies has a series of propagated pairings as sum
(`hasSum_expectedEntropy_historyEventKernel`, `hasSum_expectedEntropy_rateHistoryKernel`,
`hasSum_expectedConditionalEntropy_historyEventKernel`,
`hasSum_expectedConditionalEntropy_rateHistoryKernel`,
`hasSum_expectedMutualInformation_historyEventKernel`,
`hasSum_expectedMutualInformation_rateHistoryKernel`).  So each has the termwise derivative
wherever the term sensitivities have a summable bound (`hasDerivAt_expectedEntropy_segmentHistory`,
`hasDerivAt_expectedEntropy_rateSegment`, `hasDerivAt_expectedConditionalEntropy_segmentHistory`,
`hasDerivAt_expectedConditionalEntropy_rateSegment`,
`hasDerivAt_expectedMutualInformation_segmentHistory`,
`hasDerivAt_expectedMutualInformation_rateSegment`).

Fixed forecasts.  The expected log loss of fixed group forecasts is a budget-1 pairing, so it has
the stagewise sensitivity along a segment history, and the pairing with the sensitivity matrix
along a segment of rate histories, as derivative
(`hasDerivAt_expectedForecastLogLoss_segmentHistory`,
`hasDerivAt_expectedForecastLogLoss_rateSegment`).  No hypothesis is needed.

Decision metrics.  Every cell of the expected confusion table, the expected prevalence, the
expected called fraction and the expected net benefit at every threshold are budget-1 pairings
(`integral_prevalence_historyEventKernel`, `integral_prevalence_rateHistoryKernel`).  So they have
the stagewise sensitivity along a segment history, and the pairing with the sensitivity matrix
along a segment of rate histories, as derivatives, with no hypothesis
(`hasDerivAt_expectedConfusion_segmentHistory`, `hasDerivAt_expectedConfusion_rateSegment`,
`hasDerivAt_integral_prevalence_segmentHistory`, `hasDerivAt_integral_prevalence_rateSegment`,
`hasDerivAt_integral_calledFraction_segmentHistory`,
`hasDerivAt_integral_calledFraction_rateSegment`, `hasDerivAt_expectedNetBenefit_segmentHistory`,
`hasDerivAt_expectedNetBenefit_rateSegment`).

Threshold-metric portability.  Sensitivity, specificity and the positive and negative predictive
values are cell ratios `table x / (table x + table y)` (`cellRatio`,
`tableSensitivity_eq_cellRatio`, `tableSpecificity_eq_cellRatio`, `tablePPV_eq_cellRatio`,
`tableNPV_eq_cellRatio`).  The portability of a cell ratio of the expected tables is the cross
ratio `E_t x (E_s x + E_s y) / ((E_t x + E_t y) E_s x)` (`expectedMetricPortability_cellRatio`).
It therefore has the cross-ratio derivative of `EndToEndSensitivityMetrics` wherever
`(E_t x + E_t y) E_s x ≠ 0` (`hasDerivAt_expectedMetricPortability_cellRatio_segmentHistory`,
`hasDerivAt_expectedMetricPortability_cellRatio_rateSegment`).  With positive expected cells, the
portability decreases exactly when the relative sensitivity of the target ratio is below that of
the source (`deriv_expectedMetricPortability_cellRatio_segmentHistory_neg_iff`,
`deriv_expectedMetricPortability_cellRatio_rateSegment_neg_iff`), by
`EndToEndSensitivityMetrics.crossRatioDerivative_neg_iff_of_pos`.

Significance.  The information a score carries about the outcome and its repaired log loss move
with the demography.  Their first-order change is the series of the first-order changes of
finitely many propagated moments at each budget, and the log loss of fixed forecasts changes by
one finite computation.  Every threshold metric a clinical score is reported by, and its
portability, changes by budget-1 computations, with a sign criterion that says whether
sensitivity, specificity or a predictive value ports worse.

Scope.  The summable bound on the term sensitivities of the entropy series is a hypothesis.  The
division-free tail bound `(1 - x)ᴷ⁺¹ / (K + 1)` of `EndToEndLogLossLaw` controls the values of the
terms, not their derivatives, and no bound for the propagator derivatives at growing budgets is
proved here.  The threshold metrics are in ratio-of-expectations form; the expected per-population
recall and precision, which are series, are not differentiated.  Pulses and durations are fixed,
the derivatives are two-sided at interior parameters, score groups form a finite alphabet, the
rule is deterministic, and outcomes are binary.

## Empirical status

None.  The bodies here are termwise differentiation of series of supplied sensitivities and
derivatives of finite pairings with propagators and of rational functions of them, so no
measurement can bear on them.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.EndToEndSensitivityDecision

open MeasureTheory ProbabilityTheory MvPolynomial Descent.Coalescent PartialHaplotypeCarrier
  PartialHaplotypeDualGenerator PartialHaplotypeDualSemigroup NeutralFellerGenerator
  NeutralPolynomialSemigroup PartialHaplotypeMicroscopicApproximation PartialHaplotypePulseKernel
  NeutralPulseHistoryKernel NeutralRateHistoryRealization NeutralRateHistoryKernel
  ReplicaMetricInstances EndToEndPortabilityLaw EndToEndDiscriminationLaw EndToEndBrierLaw
  EndToEndLogLossLaw EndToEndDecisionLaw EndToEndSensitivityLaw EndToEndSensitivityMetrics
  EndToEndSensitivityRates EndToEndSensitivityRatePath EndToEndSensitivityRatePathMetrics
open scoped Matrix NNReal

noncomputable section

variable {Deme Locus : Type*} {Allele : Locus → Type*}
variable [Fintype Deme] [DecidableEq Deme] [Fintype Locus] [DecidableEq Locus]
  [∀ ℓ, Fintype (Allele ℓ)] [∀ ℓ, DecidableEq (Allele ℓ)]

/-! ## Termwise differentiation of series of propagated pairings -/

/-- **A series of propagated pairings along a segment history.**  If `F θ` is the sum over `k` of
`c_k · U_{k+2}(θ) H_{k+2}(x₀) / (k + 1)` at every parameter, and the stagewise sensitivities of the
terms are bounded on `(0, 1)` by a summable sequence, then at every interior parameter `F` has as
derivative the series of the term sensitivities. -/
theorem hasDerivAt_of_hasSum_dotProduct_segmentHistory {θ₀ : ℝ} (hθ₀ : θ₀ ∈ Set.Ioo (0 : ℝ) 1)
    (history : List ((NeutralRates Deme Locus Allele × NeutralRates Deme Locus Allele × ℝ≥0)
      ⊕ PulseMatrix Deme))
    (x0 : FrequencyState Deme Locus Allele)
    (c : ∀ k : ℕ, BudgetConfiguration Deme Locus Allele (fun _ ↦ k + 2) → ℝ) {F : ℝ → ℝ}
    (hF : ∀ θ, HasSum (fun k : ℕ ↦ (c k ⬝ᵥ (historyEventPropagator (fun _ ↦ k + 2)
        ((history.map segmentEvent).map fun event ↦ event θ)
          *ᵥ budgetMomentFeature (fun _ ↦ k + 2) x0)) / ((k : ℝ) + 1)) (F θ))
    {bound : ℕ → ℝ} (hsummable : Summable bound)
    (hbound : ∀ k : ℕ, ∀ θ ∈ Set.Ioo (0 : ℝ) 1,
      |historySensitivity (fun _ ↦ k + 2) θ (history.map segmentEvent)
          (familyDerivative (fun _ ↦ k + 2) θ) (c k) (budgetMomentFeature (fun _ ↦ k + 2) x0)
        / ((k : ℝ) + 1)| ≤ bound k) :
    HasDerivAt F
      (∑' k : ℕ, historySensitivity (fun _ ↦ k + 2) θ₀ (history.map segmentEvent)
          (familyDerivative (fun _ ↦ k + 2) θ₀) (c k) (budgetMomentFeature (fun _ ↦ k + 2) x0)
        / ((k : ℝ) + 1)) θ₀ := by
  have hderiv : ∀ (k : ℕ) (θ : ℝ), θ ∈ Set.Ioo (0 : ℝ) 1 →
      HasDerivAt (fun θ' ↦ (c k ⬝ᵥ (historyEventPropagator (fun _ ↦ k + 2)
          ((history.map segmentEvent).map fun event ↦ event θ')
            *ᵥ budgetMomentFeature (fun _ ↦ k + 2) x0)) / ((k : ℝ) + 1))
        (historySensitivity (fun _ ↦ k + 2) θ (history.map segmentEvent)
            (familyDerivative (fun _ ↦ k + 2) θ) (c k) (budgetMomentFeature (fun _ ↦ k + 2) x0)
          / ((k : ℝ) + 1)) θ := fun k θ hθ ↦
    (hasDerivAt_dotProduct_segmentHistory (fun _ ↦ k + 2) hθ history (c k)
      (budgetMomentFeature (fun _ ↦ k + 2) x0)).div_const ((k : ℝ) + 1)
  have hnorm : ∀ (k : ℕ) (θ : ℝ), θ ∈ Set.Ioo (0 : ℝ) 1 →
      ‖historySensitivity (fun _ ↦ k + 2) θ (history.map segmentEvent)
          (familyDerivative (fun _ ↦ k + 2) θ) (c k) (budgetMomentFeature (fun _ ↦ k + 2) x0)
        / ((k : ℝ) + 1)‖ ≤ bound k := fun k θ hθ ↦ by
    rw [Real.norm_eq_abs]
    exact hbound k θ hθ
  have hseries := hasDerivAt_tsum_of_isPreconnected hsummable
    (isOpen_Ioo : IsOpen (Set.Ioo (0 : ℝ) 1)) isPreconnected_Ioo hderiv hnorm hθ₀ (hF θ₀).summable
    hθ₀
  exact hseries.congr_of_eventuallyEq (Filter.Eventually.of_forall fun θ ↦ (hF θ).tsum_eq.symm)

/-- **A series of propagated pairings along a segment of rate histories.**  If `F θ` is the sum
over `k` of `c_k · U_{k+2}(θ) H_{k+2}(x₀) / (k + 1)` with the propagator of the rate history
`t ↦ rateSegment (first t) (second t) θ`, and the pairings with the sensitivity matrices are bounded
on `(0, 1)` by a summable sequence, then at every interior parameter `F` has as derivative the
series of those pairings. -/
theorem hasDerivAt_of_hasSum_dotProduct_rateSegment
    {first second : ℝ → NeutralRates Deme Locus Allele} {T : ℝ} (hT : 0 ≤ T)
    (hfirst : ∀ capacity : Locus → ℕ,
      ContinuousOn (fun t ↦ dualGenerator (first t) capacity) (Set.Icc 0 T))
    (hsecond : ∀ capacity : Locus → ℕ,
      ContinuousOn (fun t ↦ dualGenerator (second t) capacity) (Set.Icc 0 T))
    {θ₀ : ℝ} (hθ₀ : θ₀ ∈ Set.Ioo (0 : ℝ) 1) (x0 : FrequencyState Deme Locus Allele)
    (c : ∀ k : ℕ, BudgetConfiguration Deme Locus Allele (fun _ ↦ k + 2) → ℝ) {F : ℝ → ℝ}
    (hF : ∀ θ, HasSum (fun k : ℕ ↦ (c k ⬝ᵥ (rateHistoryDualPropagator
        (fun t ↦ rateSegment (first t) (second t) θ) (fun _ ↦ k + 2) T
          *ᵥ budgetMomentFeature (fun _ ↦ k + 2) x0)) / ((k : ℝ) + 1)) (F θ))
    {bound : ℕ → ℝ} (hsummable : Summable bound)
    (hbound : ∀ k : ℕ, ∀ θ ∈ Set.Ioo (0 : ℝ) 1,
      |(c k ⬝ᵥ (ratePathSensitivity first second (fun _ ↦ k + 2) T θ
          *ᵥ budgetMomentFeature (fun _ ↦ k + 2) x0)) / ((k : ℝ) + 1)| ≤ bound k) :
    HasDerivAt F
      (∑' k : ℕ, (c k ⬝ᵥ (ratePathSensitivity first second (fun _ ↦ k + 2) T θ₀
          *ᵥ budgetMomentFeature (fun _ ↦ k + 2) x0)) / ((k : ℝ) + 1)) θ₀ := by
  have hderiv : ∀ (k : ℕ) (θ : ℝ), θ ∈ Set.Ioo (0 : ℝ) 1 →
      HasDerivAt (fun θ' ↦ (c k ⬝ᵥ (rateHistoryDualPropagator
          (fun t ↦ rateSegment (first t) (second t) θ') (fun _ ↦ k + 2) T
            *ᵥ budgetMomentFeature (fun _ ↦ k + 2) x0)) / ((k : ℝ) + 1))
        ((c k ⬝ᵥ (ratePathSensitivity first second (fun _ ↦ k + 2) T θ
          *ᵥ budgetMomentFeature (fun _ ↦ k + 2) x0)) / ((k : ℝ) + 1)) θ := fun k θ hθ ↦
    (hasDerivAt_dotProduct_rateHistoryDualPropagator_segment hT (hfirst (fun _ ↦ k + 2))
      (hsecond (fun _ ↦ k + 2)) hθ (c k) (budgetMomentFeature (fun _ ↦ k + 2) x0)).div_const
      ((k : ℝ) + 1)
  have hnorm : ∀ (k : ℕ) (θ : ℝ), θ ∈ Set.Ioo (0 : ℝ) 1 →
      ‖(c k ⬝ᵥ (ratePathSensitivity first second (fun _ ↦ k + 2) T θ
          *ᵥ budgetMomentFeature (fun _ ↦ k + 2) x0)) / ((k : ℝ) + 1)‖ ≤ bound k :=
    fun k θ hθ ↦ by
      rw [Real.norm_eq_abs]
      exact hbound k θ hθ
  have hseries := hasDerivAt_tsum_of_isPreconnected hsummable
    (isOpen_Ioo : IsOpen (Set.Ioo (0 : ℝ) 1)) isPreconnected_Ioo hderiv hnorm hθ₀ (hF θ₀).summable
    hθ₀
  exact hseries.congr_of_eventuallyEq (Filter.Eventually.of_forall fun θ ↦ (hF θ).tsum_eq.symm)

/-! ## The entropy of a report law -/

section Entropy

variable {Report : Type*} [Fintype Report] [DecidableEq Report]

/-- **The expected entropy along a history of epochs, splits and pulses as a series of propagated
pairings.** -/
theorem hasSum_expectedEntropy_historyEventKernel (ℓ₀ : Locus) (hap₀ : FullHaplotype Locus Allele)
    (events : List ((NeutralRates Deme Locus Allele × ℝ≥0) ⊕ PulseMatrix Deme))
    (x0 : FrequencyState Deme Locus Allele) (deme : Deme)
    (report : FullHaplotype Locus Allele → Report) :
    HasSum (fun k : ℕ ↦ (budgetCoefficients ℓ₀ (fun _ ↦ k + 2)
          (demePolynomial deme (entropyTermPolynomial report k))
        ⬝ᵥ (historyEventPropagator (fun _ ↦ k + 2) events
          *ᵥ budgetMomentFeature (fun _ ↦ k + 2) x0)) / ((k : ℝ) + 1))
      (expectedEntropy (historyEventKernel ℓ₀ hap₀ events) x0 deme report) := by
  haveI := isMarkovKernel_historyEventKernel ℓ₀ hap₀ events
  have hsum := hasSum_expectedEntropy (historyEventKernel ℓ₀ hap₀ events) x0 deme report
  have hfun : (fun k : ℕ ↦ (∫ y, reportEntropyTerm ((stateLaw y deme).pushforward report) k
        ∂(historyEventKernel ℓ₀ hap₀ events x0)) / ((k : ℝ) + 1))
      = fun k : ℕ ↦ (budgetCoefficients ℓ₀ (fun _ ↦ k + 2)
          (demePolynomial deme (entropyTermPolynomial report k))
        ⬝ᵥ (historyEventPropagator (fun _ ↦ k + 2) events
          *ᵥ budgetMomentFeature (fun _ ↦ k + 2) x0)) / ((k : ℝ) + 1) := by
    funext k
    rw [← integral_eval_stateLaw_historyEventKernel ℓ₀ hap₀ events (k + 2) x0 deme _
      (totalDegree_entropyTermPolynomial_le report k)]
    simp only [eval_entropyTermPolynomial]
  rw [hfun] at hsum
  exact hsum

/-- **The expected entropy along a rate history as a series of propagated pairings.** -/
theorem hasSum_expectedEntropy_rateHistoryKernel {rates : ℝ → NeutralRates Deme Locus Allele}
    {T : ℝ} (hT : 0 ≤ T)
    (hcontinuous : ∀ capacity : Locus → ℕ,
      ContinuousOn (fun t ↦ dualGenerator (rates t) capacity) (Set.Icc 0 T))
    (ℓ₀ : Locus) (hap₀ : FullHaplotype Locus Allele) (x0 : FrequencyState Deme Locus Allele)
    (deme : Deme) (report : FullHaplotype Locus Allele → Report) :
    HasSum (fun k : ℕ ↦ (budgetCoefficients ℓ₀ (fun _ ↦ k + 2)
          (demePolynomial deme (entropyTermPolynomial report k))
        ⬝ᵥ (rateHistoryDualPropagator rates (fun _ ↦ k + 2) T
          *ᵥ budgetMomentFeature (fun _ ↦ k + 2) x0)) / ((k : ℝ) + 1))
      (expectedEntropy (rateHistoryKernel rates ℓ₀ hap₀ hT hcontinuous) x0 deme report) := by
  haveI := isMarkovKernel_rateHistoryKernel hT hcontinuous ℓ₀ hap₀
  have hsum := hasSum_expectedEntropy (rateHistoryKernel rates ℓ₀ hap₀ hT hcontinuous) x0 deme
    report
  have hfun : (fun k : ℕ ↦ (∫ y, reportEntropyTerm ((stateLaw y deme).pushforward report) k
        ∂(rateHistoryKernel rates ℓ₀ hap₀ hT hcontinuous x0)) / ((k : ℝ) + 1))
      = fun k : ℕ ↦ (budgetCoefficients ℓ₀ (fun _ ↦ k + 2)
          (demePolynomial deme (entropyTermPolynomial report k))
        ⬝ᵥ (rateHistoryDualPropagator rates (fun _ ↦ k + 2) T
          *ᵥ budgetMomentFeature (fun _ ↦ k + 2) x0)) / ((k : ℝ) + 1) := by
    funext k
    rw [← integral_eval_stateLaw_rateHistoryKernel hT hcontinuous ℓ₀ hap₀ (k + 2) x0 deme _
      (totalDegree_entropyTermPolynomial_le report k)]
    simp only [eval_entropyTermPolynomial]
  rw [hfun] at hsum
  exact hsum

/-- **The sensitivity of the expected entropy along a segment history.**  If the stagewise
sensitivities of the entropy terms are bounded on `(0, 1)` by a summable sequence, then at every
interior parameter the expected entropy of the report law of a deme has derivative the series of
the term sensitivities. -/
theorem hasDerivAt_expectedEntropy_segmentHistory (ℓ₀ : Locus)
    (hap₀ : FullHaplotype Locus Allele) {θ₀ : ℝ} (hθ₀ : θ₀ ∈ Set.Ioo (0 : ℝ) 1)
    (history : List ((NeutralRates Deme Locus Allele × NeutralRates Deme Locus Allele × ℝ≥0)
      ⊕ PulseMatrix Deme))
    (x0 : FrequencyState Deme Locus Allele) (deme : Deme)
    (report : FullHaplotype Locus Allele → Report) {bound : ℕ → ℝ} (hsummable : Summable bound)
    (hbound : ∀ k : ℕ, ∀ θ ∈ Set.Ioo (0 : ℝ) 1,
      |historySensitivity (fun _ ↦ k + 2) θ (history.map segmentEvent)
          (familyDerivative (fun _ ↦ k + 2) θ)
          (budgetCoefficients ℓ₀ (fun _ ↦ k + 2)
            (demePolynomial deme (entropyTermPolynomial report k)))
          (budgetMomentFeature (fun _ ↦ k + 2) x0)
        / ((k : ℝ) + 1)| ≤ bound k) :
    HasDerivAt (fun θ ↦ expectedEntropy
        (historyEventKernel ℓ₀ hap₀ ((history.map segmentEvent).map fun event ↦ event θ)) x0 deme
        report)
      (∑' k : ℕ, historySensitivity (fun _ ↦ k + 2) θ₀ (history.map segmentEvent)
          (familyDerivative (fun _ ↦ k + 2) θ₀)
          (budgetCoefficients ℓ₀ (fun _ ↦ k + 2)
            (demePolynomial deme (entropyTermPolynomial report k)))
          (budgetMomentFeature (fun _ ↦ k + 2) x0)
        / ((k : ℝ) + 1)) θ₀ :=
  hasDerivAt_of_hasSum_dotProduct_segmentHistory hθ₀ history x0
    (fun k ↦ budgetCoefficients ℓ₀ (fun _ ↦ k + 2)
      (demePolynomial deme (entropyTermPolynomial report k)))
    (fun θ ↦ hasSum_expectedEntropy_historyEventKernel ℓ₀ hap₀
      ((history.map segmentEvent).map fun event ↦ event θ) x0 deme report)
    hsummable hbound

/-- **The sensitivity of the expected entropy along a segment of rate histories.**  If the
pairings of the entropy terms with the sensitivity matrices are bounded on `(0, 1)` by a summable
sequence, then at every interior parameter the expected entropy of the report law of a deme has
derivative the series of those pairings. -/
theorem hasDerivAt_expectedEntropy_rateSegment
    {first second : ℝ → NeutralRates Deme Locus Allele} {T : ℝ} (hT : 0 ≤ T)
    (hfirst : ∀ capacity : Locus → ℕ,
      ContinuousOn (fun t ↦ dualGenerator (first t) capacity) (Set.Icc 0 T))
    (hsecond : ∀ capacity : Locus → ℕ,
      ContinuousOn (fun t ↦ dualGenerator (second t) capacity) (Set.Icc 0 T))
    (ℓ₀ : Locus) (hap₀ : FullHaplotype Locus Allele) {θ₀ : ℝ} (hθ₀ : θ₀ ∈ Set.Ioo (0 : ℝ) 1)
    (x0 : FrequencyState Deme Locus Allele) (deme : Deme)
    (report : FullHaplotype Locus Allele → Report) {bound : ℕ → ℝ} (hsummable : Summable bound)
    (hbound : ∀ k : ℕ, ∀ θ ∈ Set.Ioo (0 : ℝ) 1,
      |(budgetCoefficients ℓ₀ (fun _ ↦ k + 2)
          (demePolynomial deme (entropyTermPolynomial report k))
        ⬝ᵥ (ratePathSensitivity first second (fun _ ↦ k + 2) T θ
          *ᵥ budgetMomentFeature (fun _ ↦ k + 2) x0)) / ((k : ℝ) + 1)| ≤ bound k) :
    HasDerivAt (fun θ ↦ expectedEntropy (segmentKernel hT hfirst hsecond ℓ₀ hap₀ θ) x0 deme report)
      (∑' k : ℕ, (budgetCoefficients ℓ₀ (fun _ ↦ k + 2)
          (demePolynomial deme (entropyTermPolynomial report k))
        ⬝ᵥ (ratePathSensitivity first second (fun _ ↦ k + 2) T θ₀
          *ᵥ budgetMomentFeature (fun _ ↦ k + 2) x0)) / ((k : ℝ) + 1)) θ₀ :=
  hasDerivAt_of_hasSum_dotProduct_rateSegment hT hfirst hsecond hθ₀ x0
    (fun k ↦ budgetCoefficients ℓ₀ (fun _ ↦ k + 2)
      (demePolynomial deme (entropyTermPolynomial report k)))
    (fun θ ↦ hasSum_expectedEntropy_rateHistoryKernel hT
      (continuousOn_dualGenerator_rateSegment hfirst hsecond θ) ℓ₀ hap₀ x0 deme report)
    hsummable hbound

end Entropy

/-! ## Conditional entropy, mutual information and fixed forecasts -/

section ScoreOutcome

variable {Score : Type*} [Fintype Score] [DecidableEq Score]

/-- **The expected conditional entropy along a history of epochs, splits and pulses as a series of
propagated pairings.** -/
theorem hasSum_expectedConditionalEntropy_historyEventKernel (ℓ₀ : Locus)
    (hap₀ : FullHaplotype Locus Allele)
    (events : List ((NeutralRates Deme Locus Allele × ℝ≥0) ⊕ PulseMatrix Deme))
    (x0 : FrequencyState Deme Locus Allele) (deme : Deme)
    (report : FullHaplotype Locus Allele → Score × Bool) :
    HasSum (fun k : ℕ ↦ (budgetCoefficients ℓ₀ (fun _ ↦ k + 2)
          (demePolynomial deme (conditionalEntropyTermPolynomial report k))
        ⬝ᵥ (historyEventPropagator (fun _ ↦ k + 2) events
          *ᵥ budgetMomentFeature (fun _ ↦ k + 2) x0)) / ((k : ℝ) + 1))
      (expectedConditionalEntropy (historyEventKernel ℓ₀ hap₀ events) x0 deme report) := by
  haveI := isMarkovKernel_historyEventKernel ℓ₀ hap₀ events
  have hsum := hasSum_expectedConditionalEntropy (historyEventKernel ℓ₀ hap₀ events) x0 deme
    report
  have hfun : (fun k : ℕ ↦ (∫ y, eval (stateLaw y deme).mass
        (conditionalEntropyTermPolynomial report k) ∂(historyEventKernel ℓ₀ hap₀ events x0))
          / ((k : ℝ) + 1))
      = fun k : ℕ ↦ (budgetCoefficients ℓ₀ (fun _ ↦ k + 2)
          (demePolynomial deme (conditionalEntropyTermPolynomial report k))
        ⬝ᵥ (historyEventPropagator (fun _ ↦ k + 2) events
          *ᵥ budgetMomentFeature (fun _ ↦ k + 2) x0)) / ((k : ℝ) + 1) := by
    funext k
    rw [integral_eval_stateLaw_historyEventKernel ℓ₀ hap₀ events (k + 2) x0 deme _
      (totalDegree_conditionalEntropyTermPolynomial_le report k)]
  rw [hfun] at hsum
  exact hsum

/-- **The expected conditional entropy along a rate history as a series of propagated
pairings.** -/
theorem hasSum_expectedConditionalEntropy_rateHistoryKernel
    {rates : ℝ → NeutralRates Deme Locus Allele} {T : ℝ} (hT : 0 ≤ T)
    (hcontinuous : ∀ capacity : Locus → ℕ,
      ContinuousOn (fun t ↦ dualGenerator (rates t) capacity) (Set.Icc 0 T))
    (ℓ₀ : Locus) (hap₀ : FullHaplotype Locus Allele) (x0 : FrequencyState Deme Locus Allele)
    (deme : Deme) (report : FullHaplotype Locus Allele → Score × Bool) :
    HasSum (fun k : ℕ ↦ (budgetCoefficients ℓ₀ (fun _ ↦ k + 2)
          (demePolynomial deme (conditionalEntropyTermPolynomial report k))
        ⬝ᵥ (rateHistoryDualPropagator rates (fun _ ↦ k + 2) T
          *ᵥ budgetMomentFeature (fun _ ↦ k + 2) x0)) / ((k : ℝ) + 1))
      (expectedConditionalEntropy (rateHistoryKernel rates ℓ₀ hap₀ hT hcontinuous) x0 deme
        report) := by
  haveI := isMarkovKernel_rateHistoryKernel hT hcontinuous ℓ₀ hap₀
  have hsum := hasSum_expectedConditionalEntropy (rateHistoryKernel rates ℓ₀ hap₀ hT hcontinuous)
    x0 deme report
  have hfun : (fun k : ℕ ↦ (∫ y, eval (stateLaw y deme).mass
        (conditionalEntropyTermPolynomial report k)
          ∂(rateHistoryKernel rates ℓ₀ hap₀ hT hcontinuous x0)) / ((k : ℝ) + 1))
      = fun k : ℕ ↦ (budgetCoefficients ℓ₀ (fun _ ↦ k + 2)
          (demePolynomial deme (conditionalEntropyTermPolynomial report k))
        ⬝ᵥ (rateHistoryDualPropagator rates (fun _ ↦ k + 2) T
          *ᵥ budgetMomentFeature (fun _ ↦ k + 2) x0)) / ((k : ℝ) + 1) := by
    funext k
    rw [integral_eval_stateLaw_rateHistoryKernel hT hcontinuous ℓ₀ hap₀ (k + 2) x0 deme _
      (totalDegree_conditionalEntropyTermPolynomial_le report k)]
  rw [hfun] at hsum
  exact hsum

/-- **The expected mutual information along a history of epochs, splits and pulses as a series of
propagated pairings.** -/
theorem hasSum_expectedMutualInformation_historyEventKernel (ℓ₀ : Locus)
    (hap₀ : FullHaplotype Locus Allele)
    (events : List ((NeutralRates Deme Locus Allele × ℝ≥0) ⊕ PulseMatrix Deme))
    (x0 : FrequencyState Deme Locus Allele) (deme : Deme)
    (report : FullHaplotype Locus Allele → Score × Bool) :
    HasSum (fun k : ℕ ↦ (budgetCoefficients ℓ₀ (fun _ ↦ k + 2)
          (demePolynomial deme (mutualInformationTermPolynomial report k))
        ⬝ᵥ (historyEventPropagator (fun _ ↦ k + 2) events
          *ᵥ budgetMomentFeature (fun _ ↦ k + 2) x0)) / ((k : ℝ) + 1))
      (expectedMutualInformation (historyEventKernel ℓ₀ hap₀ events) x0 deme report) := by
  haveI := isMarkovKernel_historyEventKernel ℓ₀ hap₀ events
  have hsum := hasSum_expectedMutualInformation (historyEventKernel ℓ₀ hap₀ events) x0 deme
    report
  have hfun : (fun k : ℕ ↦ (∫ y, eval (stateLaw y deme).mass
        (mutualInformationTermPolynomial report k) ∂(historyEventKernel ℓ₀ hap₀ events x0))
          / ((k : ℝ) + 1))
      = fun k : ℕ ↦ (budgetCoefficients ℓ₀ (fun _ ↦ k + 2)
          (demePolynomial deme (mutualInformationTermPolynomial report k))
        ⬝ᵥ (historyEventPropagator (fun _ ↦ k + 2) events
          *ᵥ budgetMomentFeature (fun _ ↦ k + 2) x0)) / ((k : ℝ) + 1) := by
    funext k
    rw [integral_eval_stateLaw_historyEventKernel ℓ₀ hap₀ events (k + 2) x0 deme _
      (totalDegree_mutualInformationTermPolynomial_le report k)]
  rw [hfun] at hsum
  exact hsum

/-- **The expected mutual information along a rate history as a series of propagated
pairings.** -/
theorem hasSum_expectedMutualInformation_rateHistoryKernel
    {rates : ℝ → NeutralRates Deme Locus Allele} {T : ℝ} (hT : 0 ≤ T)
    (hcontinuous : ∀ capacity : Locus → ℕ,
      ContinuousOn (fun t ↦ dualGenerator (rates t) capacity) (Set.Icc 0 T))
    (ℓ₀ : Locus) (hap₀ : FullHaplotype Locus Allele) (x0 : FrequencyState Deme Locus Allele)
    (deme : Deme) (report : FullHaplotype Locus Allele → Score × Bool) :
    HasSum (fun k : ℕ ↦ (budgetCoefficients ℓ₀ (fun _ ↦ k + 2)
          (demePolynomial deme (mutualInformationTermPolynomial report k))
        ⬝ᵥ (rateHistoryDualPropagator rates (fun _ ↦ k + 2) T
          *ᵥ budgetMomentFeature (fun _ ↦ k + 2) x0)) / ((k : ℝ) + 1))
      (expectedMutualInformation (rateHistoryKernel rates ℓ₀ hap₀ hT hcontinuous) x0 deme
        report) := by
  haveI := isMarkovKernel_rateHistoryKernel hT hcontinuous ℓ₀ hap₀
  have hsum := hasSum_expectedMutualInformation (rateHistoryKernel rates ℓ₀ hap₀ hT hcontinuous)
    x0 deme report
  have hfun : (fun k : ℕ ↦ (∫ y, eval (stateLaw y deme).mass
        (mutualInformationTermPolynomial report k)
          ∂(rateHistoryKernel rates ℓ₀ hap₀ hT hcontinuous x0)) / ((k : ℝ) + 1))
      = fun k : ℕ ↦ (budgetCoefficients ℓ₀ (fun _ ↦ k + 2)
          (demePolynomial deme (mutualInformationTermPolynomial report k))
        ⬝ᵥ (rateHistoryDualPropagator rates (fun _ ↦ k + 2) T
          *ᵥ budgetMomentFeature (fun _ ↦ k + 2) x0)) / ((k : ℝ) + 1) := by
    funext k
    rw [integral_eval_stateLaw_rateHistoryKernel hT hcontinuous ℓ₀ hap₀ (k + 2) x0 deme _
      (totalDegree_mutualInformationTermPolynomial_le report k)]
  rw [hfun] at hsum
  exact hsum

/-- **The sensitivity of the expected repaired log loss along a segment history.**  If the
stagewise sensitivities of the conditional entropy terms are bounded on `(0, 1)` by a summable
sequence, then at every interior parameter the expected conditional entropy of outcome given score
has derivative the series of the term sensitivities. -/
theorem hasDerivAt_expectedConditionalEntropy_segmentHistory (ℓ₀ : Locus)
    (hap₀ : FullHaplotype Locus Allele) {θ₀ : ℝ} (hθ₀ : θ₀ ∈ Set.Ioo (0 : ℝ) 1)
    (history : List ((NeutralRates Deme Locus Allele × NeutralRates Deme Locus Allele × ℝ≥0)
      ⊕ PulseMatrix Deme))
    (x0 : FrequencyState Deme Locus Allele) (deme : Deme)
    (report : FullHaplotype Locus Allele → Score × Bool) {bound : ℕ → ℝ}
    (hsummable : Summable bound)
    (hbound : ∀ k : ℕ, ∀ θ ∈ Set.Ioo (0 : ℝ) 1,
      |historySensitivity (fun _ ↦ k + 2) θ (history.map segmentEvent)
          (familyDerivative (fun _ ↦ k + 2) θ)
          (budgetCoefficients ℓ₀ (fun _ ↦ k + 2)
            (demePolynomial deme (conditionalEntropyTermPolynomial report k)))
          (budgetMomentFeature (fun _ ↦ k + 2) x0)
        / ((k : ℝ) + 1)| ≤ bound k) :
    HasDerivAt (fun θ ↦ expectedConditionalEntropy
        (historyEventKernel ℓ₀ hap₀ ((history.map segmentEvent).map fun event ↦ event θ)) x0 deme
        report)
      (∑' k : ℕ, historySensitivity (fun _ ↦ k + 2) θ₀ (history.map segmentEvent)
          (familyDerivative (fun _ ↦ k + 2) θ₀)
          (budgetCoefficients ℓ₀ (fun _ ↦ k + 2)
            (demePolynomial deme (conditionalEntropyTermPolynomial report k)))
          (budgetMomentFeature (fun _ ↦ k + 2) x0)
        / ((k : ℝ) + 1)) θ₀ :=
  hasDerivAt_of_hasSum_dotProduct_segmentHistory hθ₀ history x0
    (fun k ↦ budgetCoefficients ℓ₀ (fun _ ↦ k + 2)
      (demePolynomial deme (conditionalEntropyTermPolynomial report k)))
    (fun θ ↦ hasSum_expectedConditionalEntropy_historyEventKernel ℓ₀ hap₀
      ((history.map segmentEvent).map fun event ↦ event θ) x0 deme report)
    hsummable hbound

/-- **The sensitivity of the expected repaired log loss along a segment of rate histories**, under
a summable bound on the pairings of the conditional entropy terms with the sensitivity
matrices. -/
theorem hasDerivAt_expectedConditionalEntropy_rateSegment
    {first second : ℝ → NeutralRates Deme Locus Allele} {T : ℝ} (hT : 0 ≤ T)
    (hfirst : ∀ capacity : Locus → ℕ,
      ContinuousOn (fun t ↦ dualGenerator (first t) capacity) (Set.Icc 0 T))
    (hsecond : ∀ capacity : Locus → ℕ,
      ContinuousOn (fun t ↦ dualGenerator (second t) capacity) (Set.Icc 0 T))
    (ℓ₀ : Locus) (hap₀ : FullHaplotype Locus Allele) {θ₀ : ℝ} (hθ₀ : θ₀ ∈ Set.Ioo (0 : ℝ) 1)
    (x0 : FrequencyState Deme Locus Allele) (deme : Deme)
    (report : FullHaplotype Locus Allele → Score × Bool) {bound : ℕ → ℝ}
    (hsummable : Summable bound)
    (hbound : ∀ k : ℕ, ∀ θ ∈ Set.Ioo (0 : ℝ) 1,
      |(budgetCoefficients ℓ₀ (fun _ ↦ k + 2)
          (demePolynomial deme (conditionalEntropyTermPolynomial report k))
        ⬝ᵥ (ratePathSensitivity first second (fun _ ↦ k + 2) T θ
          *ᵥ budgetMomentFeature (fun _ ↦ k + 2) x0)) / ((k : ℝ) + 1)| ≤ bound k) :
    HasDerivAt (fun θ ↦ expectedConditionalEntropy (segmentKernel hT hfirst hsecond ℓ₀ hap₀ θ) x0
        deme report)
      (∑' k : ℕ, (budgetCoefficients ℓ₀ (fun _ ↦ k + 2)
          (demePolynomial deme (conditionalEntropyTermPolynomial report k))
        ⬝ᵥ (ratePathSensitivity first second (fun _ ↦ k + 2) T θ₀
          *ᵥ budgetMomentFeature (fun _ ↦ k + 2) x0)) / ((k : ℝ) + 1)) θ₀ :=
  hasDerivAt_of_hasSum_dotProduct_rateSegment hT hfirst hsecond hθ₀ x0
    (fun k ↦ budgetCoefficients ℓ₀ (fun _ ↦ k + 2)
      (demePolynomial deme (conditionalEntropyTermPolynomial report k)))
    (fun θ ↦ hasSum_expectedConditionalEntropy_rateHistoryKernel hT
      (continuousOn_dualGenerator_rateSegment hfirst hsecond θ) ℓ₀ hap₀ x0 deme report)
    hsummable hbound

/-- **The sensitivity of the expected mutual information along a segment history**, under a
summable bound on the stagewise sensitivities of the mutual information terms. -/
theorem hasDerivAt_expectedMutualInformation_segmentHistory (ℓ₀ : Locus)
    (hap₀ : FullHaplotype Locus Allele) {θ₀ : ℝ} (hθ₀ : θ₀ ∈ Set.Ioo (0 : ℝ) 1)
    (history : List ((NeutralRates Deme Locus Allele × NeutralRates Deme Locus Allele × ℝ≥0)
      ⊕ PulseMatrix Deme))
    (x0 : FrequencyState Deme Locus Allele) (deme : Deme)
    (report : FullHaplotype Locus Allele → Score × Bool) {bound : ℕ → ℝ}
    (hsummable : Summable bound)
    (hbound : ∀ k : ℕ, ∀ θ ∈ Set.Ioo (0 : ℝ) 1,
      |historySensitivity (fun _ ↦ k + 2) θ (history.map segmentEvent)
          (familyDerivative (fun _ ↦ k + 2) θ)
          (budgetCoefficients ℓ₀ (fun _ ↦ k + 2)
            (demePolynomial deme (mutualInformationTermPolynomial report k)))
          (budgetMomentFeature (fun _ ↦ k + 2) x0)
        / ((k : ℝ) + 1)| ≤ bound k) :
    HasDerivAt (fun θ ↦ expectedMutualInformation
        (historyEventKernel ℓ₀ hap₀ ((history.map segmentEvent).map fun event ↦ event θ)) x0 deme
        report)
      (∑' k : ℕ, historySensitivity (fun _ ↦ k + 2) θ₀ (history.map segmentEvent)
          (familyDerivative (fun _ ↦ k + 2) θ₀)
          (budgetCoefficients ℓ₀ (fun _ ↦ k + 2)
            (demePolynomial deme (mutualInformationTermPolynomial report k)))
          (budgetMomentFeature (fun _ ↦ k + 2) x0)
        / ((k : ℝ) + 1)) θ₀ :=
  hasDerivAt_of_hasSum_dotProduct_segmentHistory hθ₀ history x0
    (fun k ↦ budgetCoefficients ℓ₀ (fun _ ↦ k + 2)
      (demePolynomial deme (mutualInformationTermPolynomial report k)))
    (fun θ ↦ hasSum_expectedMutualInformation_historyEventKernel ℓ₀ hap₀
      ((history.map segmentEvent).map fun event ↦ event θ) x0 deme report)
    hsummable hbound

/-- **The sensitivity of the expected mutual information along a segment of rate histories**, under
a summable bound on the pairings of the mutual information terms with the sensitivity
matrices. -/
theorem hasDerivAt_expectedMutualInformation_rateSegment
    {first second : ℝ → NeutralRates Deme Locus Allele} {T : ℝ} (hT : 0 ≤ T)
    (hfirst : ∀ capacity : Locus → ℕ,
      ContinuousOn (fun t ↦ dualGenerator (first t) capacity) (Set.Icc 0 T))
    (hsecond : ∀ capacity : Locus → ℕ,
      ContinuousOn (fun t ↦ dualGenerator (second t) capacity) (Set.Icc 0 T))
    (ℓ₀ : Locus) (hap₀ : FullHaplotype Locus Allele) {θ₀ : ℝ} (hθ₀ : θ₀ ∈ Set.Ioo (0 : ℝ) 1)
    (x0 : FrequencyState Deme Locus Allele) (deme : Deme)
    (report : FullHaplotype Locus Allele → Score × Bool) {bound : ℕ → ℝ}
    (hsummable : Summable bound)
    (hbound : ∀ k : ℕ, ∀ θ ∈ Set.Ioo (0 : ℝ) 1,
      |(budgetCoefficients ℓ₀ (fun _ ↦ k + 2)
          (demePolynomial deme (mutualInformationTermPolynomial report k))
        ⬝ᵥ (ratePathSensitivity first second (fun _ ↦ k + 2) T θ
          *ᵥ budgetMomentFeature (fun _ ↦ k + 2) x0)) / ((k : ℝ) + 1)| ≤ bound k) :
    HasDerivAt (fun θ ↦ expectedMutualInformation (segmentKernel hT hfirst hsecond ℓ₀ hap₀ θ) x0
        deme report)
      (∑' k : ℕ, (budgetCoefficients ℓ₀ (fun _ ↦ k + 2)
          (demePolynomial deme (mutualInformationTermPolynomial report k))
        ⬝ᵥ (ratePathSensitivity first second (fun _ ↦ k + 2) T θ₀
          *ᵥ budgetMomentFeature (fun _ ↦ k + 2) x0)) / ((k : ℝ) + 1)) θ₀ :=
  hasDerivAt_of_hasSum_dotProduct_rateSegment hT hfirst hsecond hθ₀ x0
    (fun k ↦ budgetCoefficients ℓ₀ (fun _ ↦ k + 2)
      (demePolynomial deme (mutualInformationTermPolynomial report k)))
    (fun θ ↦ hasSum_expectedMutualInformation_rateHistoryKernel hT
      (continuousOn_dualGenerator_rateSegment hfirst hsecond θ) ℓ₀ hap₀ x0 deme report)
    hsummable hbound

/-- **The sensitivity of the expected log loss of fixed forecasts along a segment history**, with
no hypothesis: the stagewise sensitivity of a budget-1 pairing. -/
theorem hasDerivAt_expectedForecastLogLoss_segmentHistory (ℓ₀ : Locus)
    (hap₀ : FullHaplotype Locus Allele) {θ₀ : ℝ} (hθ₀ : θ₀ ∈ Set.Ioo (0 : ℝ) 1)
    (history : List ((NeutralRates Deme Locus Allele × NeutralRates Deme Locus Allele × ℝ≥0)
      ⊕ PulseMatrix Deme))
    (x0 : FrequencyState Deme Locus Allele) (deme : Deme)
    (report : FullHaplotype Locus Allele → Score × Bool) (value : Score → ℝ) :
    HasDerivAt (fun θ ↦ expectedForecastLogLoss
        (historyEventKernel ℓ₀ hap₀ ((history.map segmentEvent).map fun event ↦ event θ)) x0 deme
        report value)
      (historySensitivity (fun _ ↦ 1) θ₀ (history.map segmentEvent)
        (familyDerivative (fun _ ↦ 1) θ₀)
        (budgetCoefficients ℓ₀ (fun _ ↦ 1) (demePolynomial deme
          (expectationPolynomial fun hap ↦ -Real.log (groupForecast value (report hap)))))
        (budgetMomentFeature (fun _ ↦ 1) x0)) θ₀ :=
  hasDerivAt_of_eq_dotProduct (history.map segmentEvent) (familyDerivative (fun _ ↦ 1) θ₀)
    (hasDerivAt_familyDerivative_segmentHistory (fun _ ↦ 1) hθ₀ history) _ _ fun θ ↦ by
      haveI := isMarkovKernel_historyEventKernel ℓ₀ hap₀
        ((history.map segmentEvent).map fun event ↦ event θ)
      exact expectedForecastLogLoss_eq_dotProduct ℓ₀
        (historyEventKernel ℓ₀ hap₀ ((history.map segmentEvent).map fun event ↦ event θ))
        (historyEventPropagator (fun _ ↦ 1) ((history.map segmentEvent).map fun event ↦ event θ))
        (hasDualMoments_historyEventKernel ℓ₀ hap₀
          ((history.map segmentEvent).map fun event ↦ event θ) 1) x0 deme report value

/-- **The sensitivity of the expected log loss of fixed forecasts along a segment of rate
histories**, with no hypothesis: a budget-1 pairing with the sensitivity matrix. -/
theorem hasDerivAt_expectedForecastLogLoss_rateSegment
    {first second : ℝ → NeutralRates Deme Locus Allele} {T : ℝ} (hT : 0 ≤ T)
    (hfirst : ∀ capacity : Locus → ℕ,
      ContinuousOn (fun t ↦ dualGenerator (first t) capacity) (Set.Icc 0 T))
    (hsecond : ∀ capacity : Locus → ℕ,
      ContinuousOn (fun t ↦ dualGenerator (second t) capacity) (Set.Icc 0 T))
    (ℓ₀ : Locus) (hap₀ : FullHaplotype Locus Allele) {θ₀ : ℝ} (hθ₀ : θ₀ ∈ Set.Ioo (0 : ℝ) 1)
    (x0 : FrequencyState Deme Locus Allele) (deme : Deme)
    (report : FullHaplotype Locus Allele → Score × Bool) (value : Score → ℝ) :
    HasDerivAt (fun θ ↦ expectedForecastLogLoss (segmentKernel hT hfirst hsecond ℓ₀ hap₀ θ) x0
        deme report value)
      (budgetCoefficients ℓ₀ (fun _ ↦ 1) (demePolynomial deme
          (expectationPolynomial fun hap ↦ -Real.log (groupForecast value (report hap))))
        ⬝ᵥ (ratePathSensitivity first second (fun _ ↦ 1) T θ₀
          *ᵥ budgetMomentFeature (fun _ ↦ 1) x0)) θ₀ :=
  hasDerivAt_of_eq_dotProduct_rateSegment hT (hfirst _) (hsecond _) hθ₀ _ _ fun θ ↦ by
    haveI := isMarkovKernel_rateHistoryKernel hT
      (continuousOn_dualGenerator_rateSegment hfirst hsecond θ) ℓ₀ hap₀
    exact expectedForecastLogLoss_eq_dotProduct ℓ₀
      (rateHistoryKernel (fun t ↦ rateSegment (first t) (second t) θ) ℓ₀ hap₀ hT
        (continuousOn_dualGenerator_rateSegment hfirst hsecond θ))
      (rateHistoryDualPropagator (fun t ↦ rateSegment (first t) (second t) θ) (fun _ ↦ 1) T)
      (hasDualMoments_rateHistoryKernel hT (continuousOn_dualGenerator_rateSegment hfirst hsecond θ)
        ℓ₀ hap₀ 1) x0 deme report value

end ScoreOutcome

/-! ## The confusion table, prevalence, called fraction and net benefit -/

section Decision

variable {Score : Type*} [Fintype Score]

/-- **The sensitivity of an expected confusion cell along a segment history**, with no hypothesis:
the stagewise sensitivity of a budget-1 pairing. -/
theorem hasDerivAt_expectedConfusion_segmentHistory (ℓ₀ : Locus)
    (hap₀ : FullHaplotype Locus Allele) {θ₀ : ℝ} (hθ₀ : θ₀ ∈ Set.Ioo (0 : ℝ) 1)
    (history : List ((NeutralRates Deme Locus Allele × NeutralRates Deme Locus Allele × ℝ≥0)
      ⊕ PulseMatrix Deme))
    (x0 : FrequencyState Deme Locus Allele) (deme : Deme)
    (report : FullHaplotype Locus Allele → Score × Bool) (called : Score → Bool)
    (cell : Bool × Bool) :
    HasDerivAt (fun θ ↦ expectedConfusion
        (historyEventKernel ℓ₀ hap₀ ((history.map segmentEvent).map fun event ↦ event θ)) x0 deme
        report called cell)
      (historySensitivity (fun _ ↦ 1) θ₀ (history.map segmentEvent)
        (familyDerivative (fun _ ↦ 1) θ₀)
        (budgetCoefficients ℓ₀ (fun _ ↦ 1)
          (demePolynomial deme (cellPolynomial (confusionReport report called) cell)))
        (budgetMomentFeature (fun _ ↦ 1) x0)) θ₀ :=
  hasDerivAt_of_eq_dotProduct (history.map segmentEvent) (familyDerivative (fun _ ↦ 1) θ₀)
    (hasDerivAt_familyDerivative_segmentHistory (fun _ ↦ 1) hθ₀ history) _ _ fun θ ↦ by
      have hcell := congrFun (expectedConfusion_historyEventKernel ℓ₀ hap₀
        ((history.map segmentEvent).map fun event ↦ event θ) x0 deme report called) cell
      exact hcell

/-- **The sensitivity of an expected confusion cell along a segment of rate histories**, with no
hypothesis: a budget-1 pairing with the sensitivity matrix. -/
theorem hasDerivAt_expectedConfusion_rateSegment
    {first second : ℝ → NeutralRates Deme Locus Allele} {T : ℝ} (hT : 0 ≤ T)
    (hfirst : ∀ capacity : Locus → ℕ,
      ContinuousOn (fun t ↦ dualGenerator (first t) capacity) (Set.Icc 0 T))
    (hsecond : ∀ capacity : Locus → ℕ,
      ContinuousOn (fun t ↦ dualGenerator (second t) capacity) (Set.Icc 0 T))
    (ℓ₀ : Locus) (hap₀ : FullHaplotype Locus Allele) {θ₀ : ℝ} (hθ₀ : θ₀ ∈ Set.Ioo (0 : ℝ) 1)
    (x0 : FrequencyState Deme Locus Allele) (deme : Deme)
    (report : FullHaplotype Locus Allele → Score × Bool) (called : Score → Bool)
    (cell : Bool × Bool) :
    HasDerivAt (fun θ ↦ expectedConfusion (segmentKernel hT hfirst hsecond ℓ₀ hap₀ θ) x0 deme report
        called cell)
      (budgetCoefficients ℓ₀ (fun _ ↦ 1)
          (demePolynomial deme (cellPolynomial (confusionReport report called) cell))
        ⬝ᵥ (ratePathSensitivity first second (fun _ ↦ 1) T θ₀
          *ᵥ budgetMomentFeature (fun _ ↦ 1) x0)) θ₀ :=
  hasDerivAt_of_eq_dotProduct_rateSegment hT (hfirst _) (hsecond _) hθ₀ _ _ fun θ ↦ by
    have hcell := congrFun (expectedConfusion_rateHistoryKernel hT
      (continuousOn_dualGenerator_rateSegment hfirst hsecond θ) ℓ₀ hap₀ x0 deme report called) cell
    exact hcell

/-- **The sensitivity of the expected net benefit along a segment history**, at every threshold,
with no hypothesis. -/
theorem hasDerivAt_expectedNetBenefit_segmentHistory (ℓ₀ : Locus)
    (hap₀ : FullHaplotype Locus Allele) {θ₀ : ℝ} (hθ₀ : θ₀ ∈ Set.Ioo (0 : ℝ) 1)
    (history : List ((NeutralRates Deme Locus Allele × NeutralRates Deme Locus Allele × ℝ≥0)
      ⊕ PulseMatrix Deme))
    (x0 : FrequencyState Deme Locus Allele) (deme : Deme)
    (report : FullHaplotype Locus Allele → Score × Bool) (called : Score → Bool) (t : ℝ) :
    HasDerivAt (fun θ ↦ expectedNetBenefit
        (historyEventKernel ℓ₀ hap₀ ((history.map segmentEvent).map fun event ↦ event θ)) x0 deme
        report called t)
      (historySensitivity (fun _ ↦ 1) θ₀ (history.map segmentEvent)
        (familyDerivative (fun _ ↦ 1) θ₀)
        (budgetCoefficients ℓ₀ (fun _ ↦ 1)
          (demePolynomial deme (netBenefitPolynomial report called t)))
        (budgetMomentFeature (fun _ ↦ 1) x0)) θ₀ :=
  hasDerivAt_of_eq_dotProduct (history.map segmentEvent) (familyDerivative (fun _ ↦ 1) θ₀)
    (hasDerivAt_familyDerivative_segmentHistory (fun _ ↦ 1) hθ₀ history) _ _ fun θ ↦
      expectedNetBenefit_historyEventKernel ℓ₀ hap₀
        ((history.map segmentEvent).map fun event ↦ event θ) x0 deme report called t

/-- **The sensitivity of the expected net benefit along a segment of rate histories**, at every
threshold, with no hypothesis. -/
theorem hasDerivAt_expectedNetBenefit_rateSegment
    {first second : ℝ → NeutralRates Deme Locus Allele} {T : ℝ} (hT : 0 ≤ T)
    (hfirst : ∀ capacity : Locus → ℕ,
      ContinuousOn (fun t ↦ dualGenerator (first t) capacity) (Set.Icc 0 T))
    (hsecond : ∀ capacity : Locus → ℕ,
      ContinuousOn (fun t ↦ dualGenerator (second t) capacity) (Set.Icc 0 T))
    (ℓ₀ : Locus) (hap₀ : FullHaplotype Locus Allele) {θ₀ : ℝ} (hθ₀ : θ₀ ∈ Set.Ioo (0 : ℝ) 1)
    (x0 : FrequencyState Deme Locus Allele) (deme : Deme)
    (report : FullHaplotype Locus Allele → Score × Bool) (called : Score → Bool) (t : ℝ) :
    HasDerivAt (fun θ ↦ expectedNetBenefit (segmentKernel hT hfirst hsecond ℓ₀ hap₀ θ) x0 deme
        report called t)
      (budgetCoefficients ℓ₀ (fun _ ↦ 1)
          (demePolynomial deme (netBenefitPolynomial report called t))
        ⬝ᵥ (ratePathSensitivity first second (fun _ ↦ 1) T θ₀
          *ᵥ budgetMomentFeature (fun _ ↦ 1) x0)) θ₀ :=
  hasDerivAt_of_eq_dotProduct_rateSegment hT (hfirst _) (hsecond _) hθ₀ _ _ fun θ ↦
    expectedNetBenefit_rateHistoryKernel hT
      (continuousOn_dualGenerator_rateSegment hfirst hsecond θ) ℓ₀ hap₀ x0 deme report called t

/-- **The expected prevalence along a history of epochs, splits and pulses** is a budget-1
pairing. -/
theorem integral_prevalence_historyEventKernel (ℓ₀ : Locus) (hap₀ : FullHaplotype Locus Allele)
    (events : List ((NeutralRates Deme Locus Allele × ℝ≥0) ⊕ PulseMatrix Deme))
    (x0 : FrequencyState Deme Locus Allele) (deme : Deme)
    (report : FullHaplotype Locus Allele → Score × Bool) :
    ∫ y, ((stateLaw y deme).pushforward report).binaryCaseMass Prod.snd
        ∂(historyEventKernel ℓ₀ hap₀ events x0)
      = budgetCoefficients ℓ₀ (fun _ ↦ 1)
          (demePolynomial deme (expectationPolynomial fun hap ↦ if (report hap).2 then 1 else 0))
        ⬝ᵥ (historyEventPropagator (fun _ ↦ 1) events *ᵥ budgetMomentFeature (fun _ ↦ 1) x0) := by
  rw [← integral_eval_stateLaw_historyEventKernel ℓ₀ hap₀ events 1 x0 deme _
    (totalDegree_expectationPolynomial_le fun hap ↦ if (report hap).2 then 1 else 0)]
  simp only [FiniteReportLaw.binaryCaseMass, FiniteReportLaw.expectation_pushforward,
    eval_expectationPolynomial]

/-- **The expected prevalence along a rate history** is a budget-1 pairing. -/
theorem integral_prevalence_rateHistoryKernel {rates : ℝ → NeutralRates Deme Locus Allele}
    {T : ℝ} (hT : 0 ≤ T)
    (hcontinuous : ∀ capacity : Locus → ℕ,
      ContinuousOn (fun t ↦ dualGenerator (rates t) capacity) (Set.Icc 0 T))
    (ℓ₀ : Locus) (hap₀ : FullHaplotype Locus Allele) (x0 : FrequencyState Deme Locus Allele)
    (deme : Deme) (report : FullHaplotype Locus Allele → Score × Bool) :
    ∫ y, ((stateLaw y deme).pushforward report).binaryCaseMass Prod.snd
        ∂(rateHistoryKernel rates ℓ₀ hap₀ hT hcontinuous x0)
      = budgetCoefficients ℓ₀ (fun _ ↦ 1)
          (demePolynomial deme (expectationPolynomial fun hap ↦ if (report hap).2 then 1 else 0))
        ⬝ᵥ (rateHistoryDualPropagator rates (fun _ ↦ 1) T
          *ᵥ budgetMomentFeature (fun _ ↦ 1) x0) := by
  rw [← integral_eval_stateLaw_rateHistoryKernel hT hcontinuous ℓ₀ hap₀ 1 x0 deme _
    (totalDegree_expectationPolynomial_le fun hap ↦ if (report hap).2 then 1 else 0)]
  simp only [FiniteReportLaw.binaryCaseMass, FiniteReportLaw.expectation_pushforward,
    eval_expectationPolynomial]

/-- **The sensitivity of the expected prevalence along a segment history**, with no
hypothesis. -/
theorem hasDerivAt_integral_prevalence_segmentHistory (ℓ₀ : Locus)
    (hap₀ : FullHaplotype Locus Allele) {θ₀ : ℝ} (hθ₀ : θ₀ ∈ Set.Ioo (0 : ℝ) 1)
    (history : List ((NeutralRates Deme Locus Allele × NeutralRates Deme Locus Allele × ℝ≥0)
      ⊕ PulseMatrix Deme))
    (x0 : FrequencyState Deme Locus Allele) (deme : Deme)
    (report : FullHaplotype Locus Allele → Score × Bool) :
    HasDerivAt (fun θ ↦ ∫ y, ((stateLaw y deme).pushforward report).binaryCaseMass Prod.snd
        ∂(historyEventKernel ℓ₀ hap₀ ((history.map segmentEvent).map fun event ↦ event θ) x0))
      (historySensitivity (fun _ ↦ 1) θ₀ (history.map segmentEvent)
        (familyDerivative (fun _ ↦ 1) θ₀)
        (budgetCoefficients ℓ₀ (fun _ ↦ 1)
          (demePolynomial deme (expectationPolynomial fun hap ↦ if (report hap).2 then 1 else 0)))
        (budgetMomentFeature (fun _ ↦ 1) x0)) θ₀ :=
  hasDerivAt_of_eq_dotProduct (history.map segmentEvent) (familyDerivative (fun _ ↦ 1) θ₀)
    (hasDerivAt_familyDerivative_segmentHistory (fun _ ↦ 1) hθ₀ history) _ _ fun θ ↦
      integral_prevalence_historyEventKernel ℓ₀ hap₀
        ((history.map segmentEvent).map fun event ↦ event θ) x0 deme report

/-- **The sensitivity of the expected prevalence along a segment of rate histories**, with no
hypothesis. -/
theorem hasDerivAt_integral_prevalence_rateSegment
    {first second : ℝ → NeutralRates Deme Locus Allele} {T : ℝ} (hT : 0 ≤ T)
    (hfirst : ∀ capacity : Locus → ℕ,
      ContinuousOn (fun t ↦ dualGenerator (first t) capacity) (Set.Icc 0 T))
    (hsecond : ∀ capacity : Locus → ℕ,
      ContinuousOn (fun t ↦ dualGenerator (second t) capacity) (Set.Icc 0 T))
    (ℓ₀ : Locus) (hap₀ : FullHaplotype Locus Allele) {θ₀ : ℝ} (hθ₀ : θ₀ ∈ Set.Ioo (0 : ℝ) 1)
    (x0 : FrequencyState Deme Locus Allele) (deme : Deme)
    (report : FullHaplotype Locus Allele → Score × Bool) :
    HasDerivAt (fun θ ↦ ∫ y, ((stateLaw y deme).pushforward report).binaryCaseMass Prod.snd
        ∂(segmentKernel hT hfirst hsecond ℓ₀ hap₀ θ x0))
      (budgetCoefficients ℓ₀ (fun _ ↦ 1)
          (demePolynomial deme (expectationPolynomial fun hap ↦ if (report hap).2 then 1 else 0))
        ⬝ᵥ (ratePathSensitivity first second (fun _ ↦ 1) T θ₀
          *ᵥ budgetMomentFeature (fun _ ↦ 1) x0)) θ₀ :=
  hasDerivAt_of_eq_dotProduct_rateSegment hT (hfirst _) (hsecond _) hθ₀ _ _ fun θ ↦
    integral_prevalence_rateHistoryKernel hT
      (continuousOn_dualGenerator_rateSegment hfirst hsecond θ) ℓ₀ hap₀ x0 deme report

/-- **The sensitivity of the expected called fraction along a segment history**, with no
hypothesis: the sum of the sensitivities of the true and false positive cells. -/
theorem hasDerivAt_integral_calledFraction_segmentHistory (ℓ₀ : Locus)
    (hap₀ : FullHaplotype Locus Allele) {θ₀ : ℝ} (hθ₀ : θ₀ ∈ Set.Ioo (0 : ℝ) 1)
    (history : List ((NeutralRates Deme Locus Allele × NeutralRates Deme Locus Allele × ℝ≥0)
      ⊕ PulseMatrix Deme))
    (x0 : FrequencyState Deme Locus Allele) (deme : Deme)
    (report : FullHaplotype Locus Allele → Score × Bool) (called : Score → Bool) :
    HasDerivAt (fun θ ↦ ∫ y, calledMass ((stateLaw y deme).pushforward report) called true
          + calledMass ((stateLaw y deme).pushforward report) called false
        ∂(historyEventKernel ℓ₀ hap₀ ((history.map segmentEvent).map fun event ↦ event θ) x0))
      (historySensitivity (fun _ ↦ 1) θ₀ (history.map segmentEvent)
          (familyDerivative (fun _ ↦ 1) θ₀)
          (budgetCoefficients ℓ₀ (fun _ ↦ 1)
            (demePolynomial deme (cellPolynomial (confusionReport report called) (true, true))))
          (budgetMomentFeature (fun _ ↦ 1) x0)
        + historySensitivity (fun _ ↦ 1) θ₀ (history.map segmentEvent)
          (familyDerivative (fun _ ↦ 1) θ₀)
          (budgetCoefficients ℓ₀ (fun _ ↦ 1)
            (demePolynomial deme (cellPolynomial (confusionReport report called) (true, false))))
          (budgetMomentFeature (fun _ ↦ 1) x0)) θ₀ := by
  refine ((hasDerivAt_expectedConfusion_segmentHistory ℓ₀ hap₀ hθ₀ history x0 deme report called
    (true, true)).fun_add (hasDerivAt_expectedConfusion_segmentHistory ℓ₀ hap₀ hθ₀ history x0
      deme report called (true, false))).congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun θ ↦ ?_)
  beta_reduce
  haveI := isMarkovKernel_historyEventKernel ℓ₀ hap₀
    ((history.map segmentEvent).map fun event ↦ event θ)
  rw [(integral_prevalence_calledFraction_eq_momentConfusion ℓ₀ _ _
      (hasDualMoments_historyEventKernel ℓ₀ hap₀
        ((history.map segmentEvent).map fun event ↦ event θ) 1) x0 deme report called).2,
    expectedConfusion_historyEventKernel]

/-- **The sensitivity of the expected called fraction along a segment of rate histories**, with no
hypothesis. -/
theorem hasDerivAt_integral_calledFraction_rateSegment
    {first second : ℝ → NeutralRates Deme Locus Allele} {T : ℝ} (hT : 0 ≤ T)
    (hfirst : ∀ capacity : Locus → ℕ,
      ContinuousOn (fun t ↦ dualGenerator (first t) capacity) (Set.Icc 0 T))
    (hsecond : ∀ capacity : Locus → ℕ,
      ContinuousOn (fun t ↦ dualGenerator (second t) capacity) (Set.Icc 0 T))
    (ℓ₀ : Locus) (hap₀ : FullHaplotype Locus Allele) {θ₀ : ℝ} (hθ₀ : θ₀ ∈ Set.Ioo (0 : ℝ) 1)
    (x0 : FrequencyState Deme Locus Allele) (deme : Deme)
    (report : FullHaplotype Locus Allele → Score × Bool) (called : Score → Bool) :
    HasDerivAt (fun θ ↦ ∫ y, calledMass ((stateLaw y deme).pushforward report) called true
          + calledMass ((stateLaw y deme).pushforward report) called false
        ∂(segmentKernel hT hfirst hsecond ℓ₀ hap₀ θ x0))
      (budgetCoefficients ℓ₀ (fun _ ↦ 1)
          (demePolynomial deme (cellPolynomial (confusionReport report called) (true, true)))
        ⬝ᵥ (ratePathSensitivity first second (fun _ ↦ 1) T θ₀
          *ᵥ budgetMomentFeature (fun _ ↦ 1) x0)
        + budgetCoefficients ℓ₀ (fun _ ↦ 1)
          (demePolynomial deme (cellPolynomial (confusionReport report called) (true, false)))
        ⬝ᵥ (ratePathSensitivity first second (fun _ ↦ 1) T θ₀
          *ᵥ budgetMomentFeature (fun _ ↦ 1) x0)) θ₀ := by
  refine ((hasDerivAt_expectedConfusion_rateSegment hT hfirst hsecond ℓ₀ hap₀ hθ₀ x0 deme report
    called (true, true)).fun_add (hasDerivAt_expectedConfusion_rateSegment hT hfirst hsecond ℓ₀
      hap₀ hθ₀ x0 deme report called (true, false))).congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun θ ↦ ?_)
  simp only [segmentKernel]
  haveI := isMarkovKernel_rateHistoryKernel hT
    (continuousOn_dualGenerator_rateSegment hfirst hsecond θ) ℓ₀ hap₀
  rw [(integral_prevalence_calledFraction_eq_momentConfusion ℓ₀ _ _
      (hasDualMoments_rateHistoryKernel hT (continuousOn_dualGenerator_rateSegment hfirst hsecond θ)
        ℓ₀ hap₀ 1) x0 deme report called).2,
    expectedConfusion_rateHistoryKernel]

/-! ## Threshold-metric portability -/

/-- **A cell ratio** `table x / (table x + table y)` of a confusion table indexed by call and
outcome. -/
def cellRatio (x y : Bool × Bool) (table : Bool × Bool → ℝ) : ℝ :=
  table x / (table x + table y)

/-- Sensitivity is the cell ratio of the true positives against the false negatives. -/
theorem tableSensitivity_eq_cellRatio : tableSensitivity = cellRatio (true, true) (false, true) :=
  rfl

/-- Specificity is the cell ratio of the true negatives against the false positives. -/
theorem tableSpecificity_eq_cellRatio :
    tableSpecificity = cellRatio (false, false) (true, false) :=
  rfl

/-- The positive predictive value is the cell ratio of the true positives against the false
positives. -/
theorem tablePPV_eq_cellRatio : tablePPV = cellRatio (true, true) (true, false) :=
  rfl

/-- The negative predictive value is the cell ratio of the true negatives against the false
negatives. -/
theorem tableNPV_eq_cellRatio : tableNPV = cellRatio (false, false) (false, true) :=
  rfl

/-- **Cell-ratio portability as a cross ratio** `E_t x (E_s x + E_s y) / ((E_t x + E_t y) E_s x)`
of the expected confusion tables. -/
theorem expectedMetricPortability_cellRatio
    (κ : Kernel (FrequencyState Deme Locus Allele) (FrequencyState Deme Locus Allele))
    (x0 : FrequencyState Deme Locus Allele) (source target : Deme)
    (report : FullHaplotype Locus Allele → Score × Bool) (called : Score → Bool)
    (x y : Bool × Bool) :
    expectedMetricPortability κ x0 source target report called (cellRatio x y)
      = expectedConfusion κ x0 target report called x
          * (expectedConfusion κ x0 source report called x
            + expectedConfusion κ x0 source report called y)
        / ((expectedConfusion κ x0 target report called x
            + expectedConfusion κ x0 target report called y)
          * expectedConfusion κ x0 source report called x) := by
  rw [expectedMetricPortability, cellRatio, cellRatio, div_div_div_eq]

/-- **The sensitivity of cell-ratio portability along a segment history**, wherever
`(E_t x + E_t y) E_s x ≠ 0`.  Sensitivity, specificity and the predictive values are cell ratios
(`tableSensitivity_eq_cellRatio`, `tableSpecificity_eq_cellRatio`, `tablePPV_eq_cellRatio`,
`tableNPV_eq_cellRatio`). -/
theorem hasDerivAt_expectedMetricPortability_cellRatio_segmentHistory (ℓ₀ : Locus)
    (hap₀ : FullHaplotype Locus Allele) {θ₀ : ℝ} (hθ₀ : θ₀ ∈ Set.Ioo (0 : ℝ) 1)
    (history : List ((NeutralRates Deme Locus Allele × NeutralRates Deme Locus Allele × ℝ≥0)
      ⊕ PulseMatrix Deme))
    (x0 : FrequencyState Deme Locus Allele) (source target : Deme)
    (report : FullHaplotype Locus Allele → Score × Bool) (called : Score → Bool)
    (x y : Bool × Bool)
    (hdenominator : (expectedConfusion
          (historyEventKernel ℓ₀ hap₀ ((history.map segmentEvent).map fun event ↦ event θ₀)) x0
          target report called x
        + expectedConfusion
          (historyEventKernel ℓ₀ hap₀ ((history.map segmentEvent).map fun event ↦ event θ₀)) x0
          target report called y)
      * expectedConfusion
          (historyEventKernel ℓ₀ hap₀ ((history.map segmentEvent).map fun event ↦ event θ₀)) x0
          source report called x ≠ 0) :
    HasDerivAt (fun θ ↦ expectedMetricPortability
        (historyEventKernel ℓ₀ hap₀ ((history.map segmentEvent).map fun event ↦ event θ)) x0
        source target report called (cellRatio x y))
      (crossRatioDerivative
        (expectedConfusion
          (historyEventKernel ℓ₀ hap₀ ((history.map segmentEvent).map fun event ↦ event θ₀)) x0
          target report called x)
        (expectedConfusion
            (historyEventKernel ℓ₀ hap₀ ((history.map segmentEvent).map fun event ↦ event θ₀)) x0
            source report called x
          + expectedConfusion
            (historyEventKernel ℓ₀ hap₀ ((history.map segmentEvent).map fun event ↦ event θ₀)) x0
            source report called y)
        (expectedConfusion
            (historyEventKernel ℓ₀ hap₀ ((history.map segmentEvent).map fun event ↦ event θ₀)) x0
            target report called x
          + expectedConfusion
            (historyEventKernel ℓ₀ hap₀ ((history.map segmentEvent).map fun event ↦ event θ₀)) x0
            target report called y)
        (expectedConfusion
          (historyEventKernel ℓ₀ hap₀ ((history.map segmentEvent).map fun event ↦ event θ₀)) x0
          source report called x)
        (historySensitivity (fun _ ↦ 1) θ₀ (history.map segmentEvent)
          (familyDerivative (fun _ ↦ 1) θ₀)
          (budgetCoefficients ℓ₀ (fun _ ↦ 1)
            (demePolynomial target (cellPolynomial (confusionReport report called) x)))
          (budgetMomentFeature (fun _ ↦ 1) x0))
        (historySensitivity (fun _ ↦ 1) θ₀ (history.map segmentEvent)
            (familyDerivative (fun _ ↦ 1) θ₀)
            (budgetCoefficients ℓ₀ (fun _ ↦ 1)
              (demePolynomial source (cellPolynomial (confusionReport report called) x)))
            (budgetMomentFeature (fun _ ↦ 1) x0)
          + historySensitivity (fun _ ↦ 1) θ₀ (history.map segmentEvent)
            (familyDerivative (fun _ ↦ 1) θ₀)
            (budgetCoefficients ℓ₀ (fun _ ↦ 1)
              (demePolynomial source (cellPolynomial (confusionReport report called) y)))
            (budgetMomentFeature (fun _ ↦ 1) x0))
        (historySensitivity (fun _ ↦ 1) θ₀ (history.map segmentEvent)
            (familyDerivative (fun _ ↦ 1) θ₀)
            (budgetCoefficients ℓ₀ (fun _ ↦ 1)
              (demePolynomial target (cellPolynomial (confusionReport report called) x)))
            (budgetMomentFeature (fun _ ↦ 1) x0)
          + historySensitivity (fun _ ↦ 1) θ₀ (history.map segmentEvent)
            (familyDerivative (fun _ ↦ 1) θ₀)
            (budgetCoefficients ℓ₀ (fun _ ↦ 1)
              (demePolynomial target (cellPolynomial (confusionReport report called) y)))
            (budgetMomentFeature (fun _ ↦ 1) x0))
        (historySensitivity (fun _ ↦ 1) θ₀ (history.map segmentEvent)
          (familyDerivative (fun _ ↦ 1) θ₀)
          (budgetCoefficients ℓ₀ (fun _ ↦ 1)
            (demePolynomial source (cellPolynomial (confusionReport report called) x)))
          (budgetMomentFeature (fun _ ↦ 1) x0))) θ₀ :=
  (hasDerivAt_crossRatio
    (hasDerivAt_expectedConfusion_segmentHistory ℓ₀ hap₀ hθ₀ history x0 target report called x)
    ((hasDerivAt_expectedConfusion_segmentHistory ℓ₀ hap₀ hθ₀ history x0 source report called
      x).fun_add
      (hasDerivAt_expectedConfusion_segmentHistory ℓ₀ hap₀ hθ₀ history x0 source report called y))
    ((hasDerivAt_expectedConfusion_segmentHistory ℓ₀ hap₀ hθ₀ history x0 target report called
      x).fun_add
      (hasDerivAt_expectedConfusion_segmentHistory ℓ₀ hap₀ hθ₀ history x0 target report called y))
    (hasDerivAt_expectedConfusion_segmentHistory ℓ₀ hap₀ hθ₀ history x0 source report called x)
    hdenominator).congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun _ ↦
      expectedMetricPortability_cellRatio _ x0 source target report called x y)

/-- **The sensitivity of cell-ratio portability along a segment of rate histories**, wherever
`(E_t x + E_t y) E_s x ≠ 0`. -/
theorem hasDerivAt_expectedMetricPortability_cellRatio_rateSegment
    {first second : ℝ → NeutralRates Deme Locus Allele} {T : ℝ} (hT : 0 ≤ T)
    (hfirst : ∀ capacity : Locus → ℕ,
      ContinuousOn (fun t ↦ dualGenerator (first t) capacity) (Set.Icc 0 T))
    (hsecond : ∀ capacity : Locus → ℕ,
      ContinuousOn (fun t ↦ dualGenerator (second t) capacity) (Set.Icc 0 T))
    (ℓ₀ : Locus) (hap₀ : FullHaplotype Locus Allele) {θ₀ : ℝ} (hθ₀ : θ₀ ∈ Set.Ioo (0 : ℝ) 1)
    (x0 : FrequencyState Deme Locus Allele) (source target : Deme)
    (report : FullHaplotype Locus Allele → Score × Bool) (called : Score → Bool)
    (x y : Bool × Bool)
    (hdenominator : (expectedConfusion (segmentKernel hT hfirst hsecond ℓ₀ hap₀ θ₀) x0 target
          report called x
        + expectedConfusion (segmentKernel hT hfirst hsecond ℓ₀ hap₀ θ₀) x0 target report called y)
      * expectedConfusion (segmentKernel hT hfirst hsecond ℓ₀ hap₀ θ₀) x0 source report called x
        ≠ 0) :
    HasDerivAt (fun θ ↦ expectedMetricPortability (segmentKernel hT hfirst hsecond ℓ₀ hap₀ θ) x0
        source target report called (cellRatio x y))
      (crossRatioDerivative
        (expectedConfusion (segmentKernel hT hfirst hsecond ℓ₀ hap₀ θ₀) x0 target report called x)
        (expectedConfusion (segmentKernel hT hfirst hsecond ℓ₀ hap₀ θ₀) x0 source report called x
          + expectedConfusion (segmentKernel hT hfirst hsecond ℓ₀ hap₀ θ₀) x0 source report called
            y)
        (expectedConfusion (segmentKernel hT hfirst hsecond ℓ₀ hap₀ θ₀) x0 target report called x
          + expectedConfusion (segmentKernel hT hfirst hsecond ℓ₀ hap₀ θ₀) x0 target report called
            y)
        (expectedConfusion (segmentKernel hT hfirst hsecond ℓ₀ hap₀ θ₀) x0 source report called x)
        (budgetCoefficients ℓ₀ (fun _ ↦ 1)
            (demePolynomial target (cellPolynomial (confusionReport report called) x))
          ⬝ᵥ (ratePathSensitivity first second (fun _ ↦ 1) T θ₀
            *ᵥ budgetMomentFeature (fun _ ↦ 1) x0))
        (budgetCoefficients ℓ₀ (fun _ ↦ 1)
            (demePolynomial source (cellPolynomial (confusionReport report called) x))
          ⬝ᵥ (ratePathSensitivity first second (fun _ ↦ 1) T θ₀
            *ᵥ budgetMomentFeature (fun _ ↦ 1) x0)
          + budgetCoefficients ℓ₀ (fun _ ↦ 1)
            (demePolynomial source (cellPolynomial (confusionReport report called) y))
          ⬝ᵥ (ratePathSensitivity first second (fun _ ↦ 1) T θ₀
            *ᵥ budgetMomentFeature (fun _ ↦ 1) x0))
        (budgetCoefficients ℓ₀ (fun _ ↦ 1)
            (demePolynomial target (cellPolynomial (confusionReport report called) x))
          ⬝ᵥ (ratePathSensitivity first second (fun _ ↦ 1) T θ₀
            *ᵥ budgetMomentFeature (fun _ ↦ 1) x0)
          + budgetCoefficients ℓ₀ (fun _ ↦ 1)
            (demePolynomial target (cellPolynomial (confusionReport report called) y))
          ⬝ᵥ (ratePathSensitivity first second (fun _ ↦ 1) T θ₀
            *ᵥ budgetMomentFeature (fun _ ↦ 1) x0))
        (budgetCoefficients ℓ₀ (fun _ ↦ 1)
            (demePolynomial source (cellPolynomial (confusionReport report called) x))
          ⬝ᵥ (ratePathSensitivity first second (fun _ ↦ 1) T θ₀
            *ᵥ budgetMomentFeature (fun _ ↦ 1) x0))) θ₀ :=
  (hasDerivAt_crossRatio
    (hasDerivAt_expectedConfusion_rateSegment hT hfirst hsecond ℓ₀ hap₀ hθ₀ x0 target report
      called x)
    ((hasDerivAt_expectedConfusion_rateSegment hT hfirst hsecond ℓ₀ hap₀ hθ₀ x0 source report
      called x).fun_add
      (hasDerivAt_expectedConfusion_rateSegment hT hfirst hsecond ℓ₀ hap₀ hθ₀ x0 source report
        called y))
    ((hasDerivAt_expectedConfusion_rateSegment hT hfirst hsecond ℓ₀ hap₀ hθ₀ x0 target report
      called x).fun_add
      (hasDerivAt_expectedConfusion_rateSegment hT hfirst hsecond ℓ₀ hap₀ hθ₀ x0 target report
        called y))
    (hasDerivAt_expectedConfusion_rateSegment hT hfirst hsecond ℓ₀ hap₀ hθ₀ x0 source report
      called x)
    hdenominator).congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun _ ↦
      expectedMetricPortability_cellRatio _ x0 source target report called x y)

/-- **When cell-ratio portability decreases along a segment history.**  With positive expected
cells at `θ₀`, the portability of `table x / (table x + table y)` has negative derivative exactly
when the relative sensitivity of the target ratio,
`E_t x'/E_t x - (E_t x + E_t y)'/(E_t x + E_t y)`, is below that of the source. -/
theorem deriv_expectedMetricPortability_cellRatio_segmentHistory_neg_iff (ℓ₀ : Locus)
    (hap₀ : FullHaplotype Locus Allele) {θ₀ : ℝ} (hθ₀ : θ₀ ∈ Set.Ioo (0 : ℝ) 1)
    (history : List ((NeutralRates Deme Locus Allele × NeutralRates Deme Locus Allele × ℝ≥0)
      ⊕ PulseMatrix Deme))
    (x0 : FrequencyState Deme Locus Allele) (source target : Deme)
    (report : FullHaplotype Locus Allele → Score × Bool) (called : Score → Bool)
    (x y : Bool × Bool)
    (htargetCell : 0 < expectedConfusion
      (historyEventKernel ℓ₀ hap₀ ((history.map segmentEvent).map fun event ↦ event θ₀)) x0
      target report called x)
    (hsourceSum : 0 < expectedConfusion
        (historyEventKernel ℓ₀ hap₀ ((history.map segmentEvent).map fun event ↦ event θ₀)) x0
        source report called x
      + expectedConfusion
        (historyEventKernel ℓ₀ hap₀ ((history.map segmentEvent).map fun event ↦ event θ₀)) x0
        source report called y)
    (htargetSum : 0 < expectedConfusion
        (historyEventKernel ℓ₀ hap₀ ((history.map segmentEvent).map fun event ↦ event θ₀)) x0
        target report called x
      + expectedConfusion
        (historyEventKernel ℓ₀ hap₀ ((history.map segmentEvent).map fun event ↦ event θ₀)) x0
        target report called y)
    (hsourceCell : 0 < expectedConfusion
      (historyEventKernel ℓ₀ hap₀ ((history.map segmentEvent).map fun event ↦ event θ₀)) x0
      source report called x) :
    deriv (fun θ ↦ expectedMetricPortability
        (historyEventKernel ℓ₀ hap₀ ((history.map segmentEvent).map fun event ↦ event θ)) x0
        source target report called (cellRatio x y)) θ₀ < 0
      ↔ historySensitivity (fun _ ↦ 1) θ₀ (history.map segmentEvent)
            (familyDerivative (fun _ ↦ 1) θ₀)
            (budgetCoefficients ℓ₀ (fun _ ↦ 1)
              (demePolynomial target (cellPolynomial (confusionReport report called) x)))
            (budgetMomentFeature (fun _ ↦ 1) x0)
          / expectedConfusion
            (historyEventKernel ℓ₀ hap₀ ((history.map segmentEvent).map fun event ↦ event θ₀)) x0
            target report called x
        - (historySensitivity (fun _ ↦ 1) θ₀ (history.map segmentEvent)
              (familyDerivative (fun _ ↦ 1) θ₀)
              (budgetCoefficients ℓ₀ (fun _ ↦ 1)
                (demePolynomial target (cellPolynomial (confusionReport report called) x)))
              (budgetMomentFeature (fun _ ↦ 1) x0)
            + historySensitivity (fun _ ↦ 1) θ₀ (history.map segmentEvent)
              (familyDerivative (fun _ ↦ 1) θ₀)
              (budgetCoefficients ℓ₀ (fun _ ↦ 1)
                (demePolynomial target (cellPolynomial (confusionReport report called) y)))
              (budgetMomentFeature (fun _ ↦ 1) x0))
          / (expectedConfusion
              (historyEventKernel ℓ₀ hap₀ ((history.map segmentEvent).map fun event ↦ event θ₀))
              x0 target report called x
            + expectedConfusion
              (historyEventKernel ℓ₀ hap₀ ((history.map segmentEvent).map fun event ↦ event θ₀))
              x0 target report called y)
        < historySensitivity (fun _ ↦ 1) θ₀ (history.map segmentEvent)
            (familyDerivative (fun _ ↦ 1) θ₀)
            (budgetCoefficients ℓ₀ (fun _ ↦ 1)
              (demePolynomial source (cellPolynomial (confusionReport report called) x)))
            (budgetMomentFeature (fun _ ↦ 1) x0)
          / expectedConfusion
            (historyEventKernel ℓ₀ hap₀ ((history.map segmentEvent).map fun event ↦ event θ₀)) x0
            source report called x
        - (historySensitivity (fun _ ↦ 1) θ₀ (history.map segmentEvent)
              (familyDerivative (fun _ ↦ 1) θ₀)
              (budgetCoefficients ℓ₀ (fun _ ↦ 1)
                (demePolynomial source (cellPolynomial (confusionReport report called) x)))
              (budgetMomentFeature (fun _ ↦ 1) x0)
            + historySensitivity (fun _ ↦ 1) θ₀ (history.map segmentEvent)
              (familyDerivative (fun _ ↦ 1) θ₀)
              (budgetCoefficients ℓ₀ (fun _ ↦ 1)
                (demePolynomial source (cellPolynomial (confusionReport report called) y)))
              (budgetMomentFeature (fun _ ↦ 1) x0))
          / (expectedConfusion
              (historyEventKernel ℓ₀ hap₀ ((history.map segmentEvent).map fun event ↦ event θ₀))
              x0 source report called x
            + expectedConfusion
              (historyEventKernel ℓ₀ hap₀ ((history.map segmentEvent).map fun event ↦ event θ₀))
              x0 source report called y) := by
  rw [(hasDerivAt_expectedMetricPortability_cellRatio_segmentHistory ℓ₀ hap₀ hθ₀ history x0 source
    target report called x y (mul_pos htargetSum hsourceCell).ne').deriv]
  exact crossRatioDerivative_neg_iff_of_pos _ _ _ _ htargetCell hsourceSum htargetSum hsourceCell

/-- **When cell-ratio portability decreases along a segment of rate histories.**  With positive
expected cells at `θ₀`, the portability of `table x / (table x + table y)` has negative derivative
exactly when the relative sensitivity of the target ratio is below that of the source. -/
theorem deriv_expectedMetricPortability_cellRatio_rateSegment_neg_iff
    {first second : ℝ → NeutralRates Deme Locus Allele} {T : ℝ} (hT : 0 ≤ T)
    (hfirst : ∀ capacity : Locus → ℕ,
      ContinuousOn (fun t ↦ dualGenerator (first t) capacity) (Set.Icc 0 T))
    (hsecond : ∀ capacity : Locus → ℕ,
      ContinuousOn (fun t ↦ dualGenerator (second t) capacity) (Set.Icc 0 T))
    (ℓ₀ : Locus) (hap₀ : FullHaplotype Locus Allele) {θ₀ : ℝ} (hθ₀ : θ₀ ∈ Set.Ioo (0 : ℝ) 1)
    (x0 : FrequencyState Deme Locus Allele) (source target : Deme)
    (report : FullHaplotype Locus Allele → Score × Bool) (called : Score → Bool)
    (x y : Bool × Bool)
    (htargetCell : 0 < expectedConfusion (segmentKernel hT hfirst hsecond ℓ₀ hap₀ θ₀) x0 target
      report called x)
    (hsourceSum : 0 < expectedConfusion (segmentKernel hT hfirst hsecond ℓ₀ hap₀ θ₀) x0 source
        report called x
      + expectedConfusion (segmentKernel hT hfirst hsecond ℓ₀ hap₀ θ₀) x0 source report called y)
    (htargetSum : 0 < expectedConfusion (segmentKernel hT hfirst hsecond ℓ₀ hap₀ θ₀) x0 target
        report called x
      + expectedConfusion (segmentKernel hT hfirst hsecond ℓ₀ hap₀ θ₀) x0 target report called y)
    (hsourceCell : 0 < expectedConfusion (segmentKernel hT hfirst hsecond ℓ₀ hap₀ θ₀) x0 source
      report called x) :
    deriv (fun θ ↦ expectedMetricPortability (segmentKernel hT hfirst hsecond ℓ₀ hap₀ θ) x0 source
        target report called (cellRatio x y)) θ₀ < 0
      ↔ budgetCoefficients ℓ₀ (fun _ ↦ 1)
              (demePolynomial target (cellPolynomial (confusionReport report called) x))
            ⬝ᵥ (ratePathSensitivity first second (fun _ ↦ 1) T θ₀
              *ᵥ budgetMomentFeature (fun _ ↦ 1) x0)
          / expectedConfusion (segmentKernel hT hfirst hsecond ℓ₀ hap₀ θ₀) x0 target report called
            x
        - (budgetCoefficients ℓ₀ (fun _ ↦ 1)
              (demePolynomial target (cellPolynomial (confusionReport report called) x))
            ⬝ᵥ (ratePathSensitivity first second (fun _ ↦ 1) T θ₀
              *ᵥ budgetMomentFeature (fun _ ↦ 1) x0)
            + budgetCoefficients ℓ₀ (fun _ ↦ 1)
              (demePolynomial target (cellPolynomial (confusionReport report called) y))
            ⬝ᵥ (ratePathSensitivity first second (fun _ ↦ 1) T θ₀
              *ᵥ budgetMomentFeature (fun _ ↦ 1) x0))
          / (expectedConfusion (segmentKernel hT hfirst hsecond ℓ₀ hap₀ θ₀) x0 target report
              called x
            + expectedConfusion (segmentKernel hT hfirst hsecond ℓ₀ hap₀ θ₀) x0 target report
              called y)
        < budgetCoefficients ℓ₀ (fun _ ↦ 1)
              (demePolynomial source (cellPolynomial (confusionReport report called) x))
            ⬝ᵥ (ratePathSensitivity first second (fun _ ↦ 1) T θ₀
              *ᵥ budgetMomentFeature (fun _ ↦ 1) x0)
          / expectedConfusion (segmentKernel hT hfirst hsecond ℓ₀ hap₀ θ₀) x0 source report called
            x
        - (budgetCoefficients ℓ₀ (fun _ ↦ 1)
              (demePolynomial source (cellPolynomial (confusionReport report called) x))
            ⬝ᵥ (ratePathSensitivity first second (fun _ ↦ 1) T θ₀
              *ᵥ budgetMomentFeature (fun _ ↦ 1) x0)
            + budgetCoefficients ℓ₀ (fun _ ↦ 1)
              (demePolynomial source (cellPolynomial (confusionReport report called) y))
            ⬝ᵥ (ratePathSensitivity first second (fun _ ↦ 1) T θ₀
              *ᵥ budgetMomentFeature (fun _ ↦ 1) x0))
          / (expectedConfusion (segmentKernel hT hfirst hsecond ℓ₀ hap₀ θ₀) x0 source report
              called x
            + expectedConfusion (segmentKernel hT hfirst hsecond ℓ₀ hap₀ θ₀) x0 source report
              called y) := by
  rw [(hasDerivAt_expectedMetricPortability_cellRatio_rateSegment hT hfirst hsecond ℓ₀ hap₀ hθ₀ x0
    source target report called x y (mul_pos htargetSum hsourceCell).ne').deriv]
  exact crossRatioDerivative_neg_iff_of_pos _ _ _ _ htargetCell hsourceSum htargetSum hsourceCell

end Decision

end

end Descent.Portability.EndToEndSensitivityDecision
