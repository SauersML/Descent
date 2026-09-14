/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.PortabilityMomentLadder
import Descent.Portability.EndToEndLogLossLaw

assert_below Descent.Decision Descent.Program

/-!
# The information rung of the moment ladder under any process law

`EndToEndLogLossLaw` writes the expected entropy of a report law, the expected conditional entropy
of a binary outcome given a score, and the expected mutual information as series of expectations
of frequency polynomials, and proves along histories of epochs that equal propagated moments give
equal values.  This module lifts that to every process law with dual moments, so the top rung of
`PortabilityMomentLadder` reaches the logarithmic metrics too.

The terms.  Under every Markov kernel the expected entropy is the series, over orders `k`, of the
expected order-`k` entropy term divided by `k + 1` (`EndToEndLogLossLaw.hasSum_expectedEntropy`),
and each term is a frequency polynomial of total degree at most `k + 2`
(`eval_entropyTermPolynomial`, `totalDegree_entropyTermPolynomial_le`).  The conditional entropy
and the mutual information have the same form (`hasSum_expectedConditionalEntropy`,
`hasSum_expectedMutualInformation`).

The rung.  Two Markov kernels that agree on the expectation of every frequency polynomial have the
same expected entropy, conditional entropy and mutual information of every report map in every deme
(`expectedInformation_eq_of_polynomialsAgreeAt_all`).  A history of epochs, splits and pulses and a
continuous rate history with equal propagated moments at every budget therefore agree on all three
(`expectedInformation_historyEvent_eq_rateHistory`).

Significance.  With `PortabilityMomentLadderSeries` this covers every expected metric of the
catalogue that is a limit of polynomial expectations: squared correlation, AUC, entropy,
conditional entropy and mutual information.  Each depends on the process law only through its
moment sequence, whichever kind of process carries it.

Scope.  Agreement at every budget is the hypothesis.  Whether a finite budget fixes the expected
entropies is not settled here, as in `EndToEndLogLossLaw`.

## Empirical status

None.  The bodies here are termwise comparisons of convergent series of polynomial integrals
against Markov kernels, so no measurement can bear on them.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.PortabilityMomentLadderEntropy

open MeasureTheory ProbabilityTheory MvPolynomial Descent.Coalescent PartialHaplotypeCarrier
  PartialHaplotypeDualGenerator PartialHaplotypeDualSemigroup NeutralFellerGenerator
  NeutralPolynomialSemigroup PartialHaplotypeMicroscopicApproximation PartialHaplotypePulseKernel
  NeutralPulseHistoryKernel NeutralRateHistoryRealization NeutralRateHistoryKernel
  ReplicaMetricInstances EndToEndPortabilityLaw EndToEndDiscriminationLaw EndToEndLogLossLaw
  PortabilityMomentLadder
open scoped Matrix NNReal

noncomputable section

variable {Deme Locus : Type*} {Allele : Locus → Type*}
variable [Fintype Deme] [DecidableEq Deme] [Fintype Locus] [DecidableEq Locus]
  [∀ ℓ, Fintype (Allele ℓ)] [∀ ℓ, DecidableEq (Allele ℓ)]

attribute [local instance] isMarkovKernel_historyEventKernel isMarkovKernel_rateHistoryKernel

/-- **Every degree fixes the information metrics under any process law.**  Two Markov kernels that
agree, from their initial states, on the expectation of every frequency polynomial give every report
map of a score and a binary outcome, in every deme, the same expected entropy of the report law,
the same expected conditional entropy of the outcome given the score, and the same expected mutual
information.

Assumes: agreement at every degree. -/
theorem expectedInformation_eq_of_polynomialsAgreeAt_all
    {κ₁ κ₂ : Kernel (FrequencyState Deme Locus Allele) (FrequencyState Deme Locus Allele)}
    [IsMarkovKernel κ₁] [IsMarkovKernel κ₂] {x₁ x₂ : FrequencyState Deme Locus Allele}
    (h : ∀ n : ℕ, PolynomialsAgreeAt n κ₁ κ₂ x₁ x₂) (deme : Deme)
    {Score : Type*} [Fintype Score] [DecidableEq Score]
    (report : FullHaplotype Locus Allele → Score × Bool) :
    expectedEntropy κ₁ x₁ deme report = expectedEntropy κ₂ x₂ deme report
      ∧ expectedConditionalEntropy κ₁ x₁ deme report
        = expectedConditionalEntropy κ₂ x₂ deme report
      ∧ expectedMutualInformation κ₁ x₁ deme report
        = expectedMutualInformation κ₂ x₂ deme report := by
  have hterm : ∀ (p : MvPolynomial (FullHaplotype Locus Allele) ℝ) (d : ℕ), p.totalDegree ≤ d →
      ∫ y, eval (stateLaw y deme).mass p ∂(κ₁ x₁)
        = ∫ y, eval (stateLaw y deme).mass p ∂(κ₂ x₂) := by
    intro p d hp
    simpa only [polynomialFunction_apply, eval_demePolynomial] using
      h d (demePolynomial deme p) ((totalDegree_rename_le _ _).trans hp)
  refine ⟨?_, ?_, ?_⟩
  · refine (hasSum_expectedEntropy κ₁ x₁ deme report).unique ?_
    convert hasSum_expectedEntropy κ₂ x₂ deme report using 1
    refine funext fun order ↦ ?_
    dsimp only
    congr 1
    simpa only [eval_entropyTermPolynomial] using
      hterm (entropyTermPolynomial report order) (order + 2)
        (totalDegree_entropyTermPolynomial_le report order)
  · refine (hasSum_expectedConditionalEntropy κ₁ x₁ deme report).unique ?_
    convert hasSum_expectedConditionalEntropy κ₂ x₂ deme report using 1
    refine funext fun order ↦ ?_
    dsimp only
    congr 1
    exact hterm (conditionalEntropyTermPolynomial report order) (order + 2)
      (totalDegree_conditionalEntropyTermPolynomial_le report order)
  · refine (hasSum_expectedMutualInformation κ₁ x₁ deme report).unique ?_
    convert hasSum_expectedMutualInformation κ₂ x₂ deme report using 1
    refine funext fun order ↦ ?_
    dsimp only
    congr 1
    exact hterm (mutualInformationTermPolynomial report order) (order + 2)
      (totalDegree_mutualInformationTermPolynomial_le report order)

/-- **An event history and a rate history with equal moment sequences carry the same
information.**  If a history of epochs, splits and pulses from `x₁` and a rate history with
continuous dual generator from `x₂` have equal propagated moments at every budget, every report map
has the same expected entropy, conditional entropy and mutual information in every deme under both.

Assumes: equal propagated moments at every budget. -/
theorem expectedInformation_historyEvent_eq_rateHistory (ℓ₀ : Locus)
    (hap₀ : FullHaplotype Locus Allele)
    (events : List ((NeutralRates Deme Locus Allele × ℝ≥0) ⊕ PulseMatrix Deme))
    {rates : ℝ → NeutralRates Deme Locus Allele} {T : ℝ} (hT : 0 ≤ T)
    (hcontinuous : ∀ capacity : Locus → ℕ,
      ContinuousOn (fun t ↦ dualGenerator (rates t) capacity) (Set.Icc 0 T))
    {x₁ x₂ : FrequencyState Deme Locus Allele}
    (hmoments : ∀ n : ℕ,
      historyEventPropagator (fun _ ↦ n) events *ᵥ budgetMomentFeature (fun _ ↦ n) x₁
        = rateHistoryDualPropagator rates (fun _ ↦ n) T *ᵥ budgetMomentFeature (fun _ ↦ n) x₂)
    (deme : Deme) {Score : Type*} [Fintype Score] [DecidableEq Score]
    (report : FullHaplotype Locus Allele → Score × Bool) :
    expectedEntropy (historyEventKernel ℓ₀ hap₀ events) x₁ deme report
        = expectedEntropy (rateHistoryKernel rates ℓ₀ hap₀ hT hcontinuous) x₂ deme report
      ∧ expectedConditionalEntropy (historyEventKernel ℓ₀ hap₀ events) x₁ deme report
        = expectedConditionalEntropy (rateHistoryKernel rates ℓ₀ hap₀ hT hcontinuous) x₂ deme
            report
      ∧ expectedMutualInformation (historyEventKernel ℓ₀ hap₀ events) x₁ deme report
        = expectedMutualInformation (rateHistoryKernel rates ℓ₀ hap₀ hT hcontinuous) x₂ deme
            report :=
  expectedInformation_eq_of_polynomialsAgreeAt_all
    (fun n ↦ polynomialsAgreeAt_of_hasDualMoments ℓ₀
      (hasDualMoments_historyEventKernel ℓ₀ hap₀ events n)
      (hasDualMoments_rateHistoryKernel hT hcontinuous ℓ₀ hap₀ n) (hmoments n))
    deme report

end

end Descent.Portability.PortabilityMomentLadderEntropy
