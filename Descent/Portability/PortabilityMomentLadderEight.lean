/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.PortabilityMomentLadder

assert_below Descent.Decision Descent.Program

/-!
# The budget-8 rung of the moment ladder across kinds of process law

`PortabilityMomentLadder.portabilityReport_and_training_eq_of_momentsAgreeAt_eight` covers two
histories of epochs with equal propagated budget-8 moments.  They have the same portability report,
the same joint portability ratio of NOTE2 (27), and the same GWAS-trained accuracy at every cohort
size.  This module carries that rung to other kinds of process law.

The joint ratio.  The joint numerator `N_t D_s` and denominator `D_t N_s` are frequency polynomials
of total degree at most eight in the two demes (`EndToEndPortabilityLaw.jointNumeratorPolynomial`,
`totalDegree_jointNumeratorPolynomial_le`).  So two Markov kernels that agree up to degree eight
have one joint ratio (`expectedJointPortability_eq_of_polynomialsAgreeAt_eight`).

The comparison.  Take a history of epochs, splits and pulses from `x₁` and a rate history with
continuous dual generator from `x₂` whose propagated budget-8 moments agree.  They give every score
the same portability report and the same joint ratio.  For every source cohort of at least two
individuals and every tag coding they also give the same expected GWAS-trained accuracy
(`reports_historyEvent_eq_rateHistory_eight`).  Under both kernels the trained accuracy is the one
rational function `momentTrainedAccuracy` of the propagated budget-8 moments
(`EndToEndGWASTrainingHistory.expectedTrainedAccuracy_historyEventKernel`,
`expectedTrainedAccuracy_rateHistoryKernel`).

Significance.  The two-deme quantities, the joint ratio and training in one deme deployed in
another, read the process law at budget eight.  Whether the demography is written as epochs and
pulses or as a continuous rate path makes no difference to them.

Scope.  The trained accuracy is compared through the closed forms of the two history kernels.  Its
agreement under two arbitrary process laws that agree up to degree eight is not stated here.

## Empirical status

None.  The bodies here are compositions of polynomial integrals against Markov kernels, so no
measurement can bear on them.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.PortabilityMomentLadderEight

open MeasureTheory ProbabilityTheory MvPolynomial Descent.Coalescent PartialHaplotypeCarrier
  PartialHaplotypeDualGenerator PartialHaplotypeDualSemigroup NeutralFellerGenerator
  NeutralPolynomialSemigroup PartialHaplotypeMicroscopicApproximation PartialHaplotypePulseKernel
  NeutralPulseHistoryKernel NeutralRateHistoryRealization NeutralRateHistoryKernel
  ReplicaMetricInstances EndToEndPortabilityLaw EndToEndDiscriminationLaw
  EndToEndGWASTrainingHistory PortabilityMomentLadder
open scoped Matrix NNReal

noncomputable section

variable {Deme Locus : Type*} {Allele : Locus → Type*}
variable [Fintype Deme] [DecidableEq Deme] [Fintype Locus] [DecidableEq Locus]
  [∀ ℓ, Fintype (Allele ℓ)] [∀ ℓ, DecidableEq (Allele ℓ)]

attribute [local instance] isMarkovKernel_historyEventKernel isMarkovKernel_rateHistoryKernel

/-- **Budget eight fixes the joint ratio under any process law.**  Two Markov kernels that agree,
from their initial states, on every frequency polynomial of total degree at most eight give every
score, outcome, source and target the same joint portability ratio of NOTE2 (27).

Assumes: agreement up to degree eight. -/
theorem expectedJointPortability_eq_of_polynomialsAgreeAt_eight
    {κ₁ κ₂ : Kernel (FrequencyState Deme Locus Allele) (FrequencyState Deme Locus Allele)}
    {x₁ x₂ : FrequencyState Deme Locus Allele} (h : PolynomialsAgreeAt 8 κ₁ κ₂ x₁ x₂)
    (source target : Deme) (score outcome : FullHaplotype Locus Allele → ℝ) :
    expectedJointPortability κ₁ x₁ source target score outcome
      = expectedJointPortability κ₂ x₂ source target score outcome := by
  have hnumerator : ∫ y, correlationNumerator (stateLaw y target) score outcome
        * correlationDenominator (stateLaw y source) score outcome ∂(κ₁ x₁)
      = ∫ y, correlationNumerator (stateLaw y target) score outcome
        * correlationDenominator (stateLaw y source) score outcome ∂(κ₂ x₂) := by
    simpa only [polynomialFunction_jointNumeratorPolynomial] using
      h (jointNumeratorPolynomial source target score outcome)
        (totalDegree_jointNumeratorPolynomial_le source target score outcome)
  have hdenominator : ∫ y, correlationDenominator (stateLaw y target) score outcome
        * correlationNumerator (stateLaw y source) score outcome ∂(κ₁ x₁)
      = ∫ y, correlationDenominator (stateLaw y target) score outcome
        * correlationNumerator (stateLaw y source) score outcome ∂(κ₂ x₂) := by
    simpa only [polynomialFunction_jointDenominatorPolynomial] using
      h (jointDenominatorPolynomial source target score outcome)
        (totalDegree_jointDenominatorPolynomial_le source target score outcome)
  rw [expectedJointPortability, expectedJointPortability, hnumerator, hdenominator]

/-- **An event history and a rate history with equal budget-8 moments agree on every two-deme
metric.**  If a history of epochs, splits and pulses from `x₁` and a rate history with continuous
dual generator from `x₂` have equal propagated budget-8 moments, every score has the same
portability report and joint ratio under both, and for every source cohort of at least two
individuals and every tag coding the GWAS-trained score has the same expected accuracy.

Assumes: equal propagated budget-8 moments. -/
theorem reports_historyEvent_eq_rateHistory_eight {J : Type*} [Fintype J] (ℓ₀ : Locus)
    (hap₀ : FullHaplotype Locus Allele)
    (events : List ((NeutralRates Deme Locus Allele × ℝ≥0) ⊕ PulseMatrix Deme))
    {rates : ℝ → NeutralRates Deme Locus Allele} {T : ℝ} (hT : 0 ≤ T)
    (hcontinuous : ∀ capacity : Locus → ℕ,
      ContinuousOn (fun t ↦ dualGenerator (rates t) capacity) (Set.Icc 0 T))
    {x₁ x₂ : FrequencyState Deme Locus Allele}
    (hmoments : historyEventPropagator (fun _ ↦ 8) events *ᵥ budgetMomentFeature (fun _ ↦ 8) x₁
      = rateHistoryDualPropagator rates (fun _ ↦ 8) T *ᵥ budgetMomentFeature (fun _ ↦ 8) x₂)
    (source target : Deme) (score outcome : FullHaplotype Locus Allele → ℝ)
    (case : FullHaplotype Locus Allele → Bool) :
    portabilityReport (historyEventKernel ℓ₀ hap₀ events) x₁ source target score outcome case
        = portabilityReport (rateHistoryKernel rates ℓ₀ hap₀ hT hcontinuous) x₂ source target score
            outcome case
      ∧ expectedJointPortability (historyEventKernel ℓ₀ hap₀ events) x₁ source target score outcome
        = expectedJointPortability (rateHistoryKernel rates ℓ₀ hap₀ hT hcontinuous) x₂ source
            target score outcome
      ∧ ∀ size : ℕ, 2 ≤ size → ∀ genotype : FullHaplotype Locus Allele → J → ℝ,
        expectedTrainedAccuracy (historyEventKernel ℓ₀ hap₀ events) x₁ source target size
            genotype outcome
          = expectedTrainedAccuracy (rateHistoryKernel rates ℓ₀ hap₀ hT hcontinuous) x₂ source
            target size genotype outcome := by
  have hagree : PolynomialsAgreeAt 8 (historyEventKernel ℓ₀ hap₀ events)
      (rateHistoryKernel rates ℓ₀ hap₀ hT hcontinuous) x₁ x₂ :=
    polynomialsAgreeAt_of_hasDualMoments ℓ₀ (hasDualMoments_historyEventKernel ℓ₀ hap₀ events 8)
      (hasDualMoments_rateHistoryKernel hT hcontinuous ℓ₀ hap₀ 8) hmoments
  refine ⟨portabilityReport_eq_of_polynomialsAgreeAt_four (hagree.mono (by norm_num : 4 ≤ 8))
      source target score outcome case,
    expectedJointPortability_eq_of_polynomialsAgreeAt_eight hagree source target score outcome,
    fun _size hsize genotype ↦ ?_⟩
  rw [expectedTrainedAccuracy_historyEventKernel ℓ₀ hap₀ events x₁ source target hsize genotype
      outcome,
    expectedTrainedAccuracy_rateHistoryKernel hT hcontinuous ℓ₀ hap₀ x₂ source target hsize
      genotype outcome,
    hmoments]

end

end Descent.Portability.PortabilityMomentLadderEight
