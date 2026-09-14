/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.PortabilityMomentLadder

assert_below Descent.Decision Descent.Program

/-!
# The top rung of the moment ladder under any process law

`PortabilityMomentLadder.expectedMetrics_eq_of_momentsAgreeAt_all` shows that two histories of
epochs whose propagated moments agree at every budget have the same expected per-population
squared correlation and the same expected AUC.  Those two metrics are expectations of ratios, not
rational functions of finitely many moments, so only the top rung of the ladder reaches them.
This module states that rung for every process law with dual moments.

The series.  Under every Markov kernel the expected squared correlation of a score and an outcome
in the unit interval is the series of expectations of `N (1 - D)ᵏ`
(`EndToEndCorrelationSeries.expectedSquaredCorrelation_eq_tsum`), with `N (1 - D)ᵏ` a frequency
polynomial of total degree at most `4 (k + 1)`.  The expected AUC is the series of expectations of
the AUC terms, of degree at most `2 (k + 1)` (`EndToEndDiscriminationLaw.expectedAUC_eq_tsum`).
So two Markov kernels that agree on the expectation of every frequency polynomial have one expected
squared correlation and one expected AUC in every deme, term by term
(`expectedMetrics_eq_of_polynomialsAgreeAt_all`).

The comparison.  A history of epochs, splits and pulses and a continuous rate history whose
propagated moments agree at every budget therefore give every score the same expected squared
correlation and expected AUC in every deme (`expectedMetrics_historyEvent_eq_rateHistory`).

Significance.  The per-population metrics a study reports, averaged over the randomness of the
populations a history produces, are no more sensitive to the demography than its moment sequence,
whatever kind of process law carries it.

Scope.  The score and the quantitative outcome take values in the unit interval.  Agreement at
every budget is the hypothesis; no finite budget fixes these metrics, and no explicit pair of
histories separating a finite budget from the expected metrics is constructed here.

## Empirical status

None.  The bodies here are termwise comparisons of series of polynomial integrals against Markov
kernels, so no measurement can bear on them.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.PortabilityMomentLadderSeries

open MeasureTheory ProbabilityTheory MvPolynomial Descent.Coalescent PartialHaplotypeCarrier
  PartialHaplotypeDualGenerator PartialHaplotypeDualSemigroup NeutralFellerGenerator
  NeutralPolynomialSemigroup PartialHaplotypeMicroscopicApproximation PartialHaplotypePulseKernel
  NeutralPulseHistoryKernel NeutralRateHistoryRealization NeutralRateHistoryKernel
  ReplicaMetricInstances EndToEndPortabilityLaw EndToEndCorrelationSeries
  EndToEndDiscriminationLaw PortabilityMomentLadder
open scoped Matrix NNReal

noncomputable section

variable {Deme Locus : Type*} {Allele : Locus → Type*}
variable [Fintype Deme] [DecidableEq Deme] [Fintype Locus] [DecidableEq Locus]
  [∀ ℓ, Fintype (Allele ℓ)] [∀ ℓ, DecidableEq (Allele ℓ)]

attribute [local instance] isMarkovKernel_historyEventKernel isMarkovKernel_rateHistoryKernel

/-- **Every degree fixes the expected metrics under any process law.**  Two Markov kernels that
agree, from their initial states, on the expectation of every frequency polynomial give every deme
the same expected squared correlation of a score and an outcome in the unit interval, and the same
expected AUC of the score for every binary endpoint.

Assumes: agreement at every degree. -/
theorem expectedMetrics_eq_of_polynomialsAgreeAt_all
    {κ₁ κ₂ : Kernel (FrequencyState Deme Locus Allele) (FrequencyState Deme Locus Allele)}
    [IsMarkovKernel κ₁] [IsMarkovKernel κ₂] {x₁ x₂ : FrequencyState Deme Locus Allele}
    (h : ∀ n : ℕ, PolynomialsAgreeAt n κ₁ κ₂ x₁ x₂) (deme : Deme)
    (score outcome : FullHaplotype Locus Allele → ℝ) (case : FullHaplotype Locus Allele → Bool)
    (hscore0 : ∀ hap, 0 ≤ score hap) (hscore1 : ∀ hap, score hap ≤ 1)
    (houtcome0 : ∀ hap, 0 ≤ outcome hap) (houtcome1 : ∀ hap, outcome hap ≤ 1) :
    expectedSquaredCorrelation κ₁ x₁ deme score outcome
        = expectedSquaredCorrelation κ₂ x₂ deme score outcome
      ∧ expectedAUC κ₁ x₁ deme score case = expectedAUC κ₂ x₂ deme score case := by
  constructor
  · rw [expectedSquaredCorrelation_eq_tsum κ₁ x₁ deme score outcome hscore0 hscore1 houtcome0
        houtcome1,
      expectedSquaredCorrelation_eq_tsum κ₂ x₂ deme score outcome hscore0 hscore1 houtcome0
        houtcome1]
    refine tsum_congr fun k ↦ ?_
    simpa only [polynomialFunction_seriesTermPolynomial] using
      h (4 * (k + 1)) (seriesTermPolynomial deme score outcome k)
        (totalDegree_seriesTermPolynomial_le deme score outcome k)
  · rw [expectedAUC_eq_tsum κ₁ x₁ deme score case, expectedAUC_eq_tsum κ₂ x₂ deme score case]
    refine tsum_congr fun k ↦ ?_
    simpa only [polynomialFunction_apply, eval_demePolynomial, eval_aucTerm] using
      h (2 * (k + 1))
        (demePolynomial deme
          (aucNumeratorPolynomial score case * (1 - aucDenominatorPolynomial case) ^ k))
        ((totalDegree_rename_le _ _).trans (totalDegree_aucTerm_le score case k))

/-- **An event history and a rate history with equal moment sequences give equal expected
metrics.**  If a history of epochs, splits and pulses from `x₁` and a rate history with continuous
dual generator from `x₂` have equal propagated moments at every budget, every score and outcome in
the unit interval, and every binary endpoint, have the same expected squared correlation and
expected AUC in every deme under both.

Assumes: equal propagated moments at every budget. -/
theorem expectedMetrics_historyEvent_eq_rateHistory (ℓ₀ : Locus)
    (hap₀ : FullHaplotype Locus Allele)
    (events : List ((NeutralRates Deme Locus Allele × ℝ≥0) ⊕ PulseMatrix Deme))
    {rates : ℝ → NeutralRates Deme Locus Allele} {T : ℝ} (hT : 0 ≤ T)
    (hcontinuous : ∀ capacity : Locus → ℕ,
      ContinuousOn (fun t ↦ dualGenerator (rates t) capacity) (Set.Icc 0 T))
    {x₁ x₂ : FrequencyState Deme Locus Allele}
    (hmoments : ∀ n : ℕ,
      historyEventPropagator (fun _ ↦ n) events *ᵥ budgetMomentFeature (fun _ ↦ n) x₁
        = rateHistoryDualPropagator rates (fun _ ↦ n) T *ᵥ budgetMomentFeature (fun _ ↦ n) x₂)
    (deme : Deme) (score outcome : FullHaplotype Locus Allele → ℝ)
    (case : FullHaplotype Locus Allele → Bool)
    (hscore0 : ∀ hap, 0 ≤ score hap) (hscore1 : ∀ hap, score hap ≤ 1)
    (houtcome0 : ∀ hap, 0 ≤ outcome hap) (houtcome1 : ∀ hap, outcome hap ≤ 1) :
    expectedSquaredCorrelation (historyEventKernel ℓ₀ hap₀ events) x₁ deme score outcome
        = expectedSquaredCorrelation (rateHistoryKernel rates ℓ₀ hap₀ hT hcontinuous) x₂ deme
            score outcome
      ∧ expectedAUC (historyEventKernel ℓ₀ hap₀ events) x₁ deme score case
        = expectedAUC (rateHistoryKernel rates ℓ₀ hap₀ hT hcontinuous) x₂ deme score case :=
  expectedMetrics_eq_of_polynomialsAgreeAt_all
    (fun n ↦ polynomialsAgreeAt_of_hasDualMoments ℓ₀
      (hasDualMoments_historyEventKernel ℓ₀ hap₀ events n)
      (hasDualMoments_rateHistoryKernel hT hcontinuous ℓ₀ hap₀ n) (hmoments n))
    deme score outcome case hscore0 hscore1 houtcome0 houtcome1

end

end Descent.Portability.PortabilityMomentLadderSeries
