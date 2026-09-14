/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.EndToEndPooledCalibration
import Descent.Portability.EndToEndDiscriminationLaw
import Descent.Portability.EndToEndGWASTrainingHistory

assert_below Descent.Decision Descent.Program

/-!
# The moment ladder: what a demography contributes to every metric of portability

A neutral demographic history of epochs, splits and admixture pulses, run from a frequency state
`x₀`, is a Markov process law on multi-deme haplotype frequencies
(`NeutralPulseHistoryKernel.historyEventKernel`).  The end-to-end laws of this corpus evaluate the
metrics of a score under that law one at a time.  This module states the single fact they share:
the demography enters every one of them only through its propagated configuration moments
`U_n · H_n(x₀)`, and one rung of that ladder fixes a whole report.

The statistic.  `MomentsAgreeAt n first second x₁ x₂` says that two histories, from two initial
states, have equal propagated budget-`n` moments.  A history agrees with itself
(`momentsAgreeAt_refl`), and agreement descends the ladder: agreement at a budget is agreement at
every smaller budget (`MomentsAgreeAt.mono`, from
`EndToEndDiscriminationLaw.historyEventMoments_eq_of_le`, because both are integrals of one
configuration moment under one process law).

The report.  `portabilityReport` collects, for a score, a quantitative outcome and a binary
endpoint, in a source and a target deme: the pooled haplotype law of each deme, the calibration
slope and intercept of expectations in each deme, and the calibration, squared-correlation and AUC
portabilities of expectations.  Every master-theorem deployment read in a pooled law is a function
of that law (`EndToEndPooledCalibration.pooledPopulation`), so the pooled laws carry the deployed
mean squared error and the best fixed recalibration as well.

The ladder.
* Budget 4 fixes the whole report (`portabilityReport_eq_of_momentsAgreeAt_four`): the pooled laws
  at budget 1, the AUC portability at budget 2, the calibration slopes and calibration portability
  at budget 2, the intercepts at budget 3, and the squared-correlation portability at budget 4.
* Budget 8 fixes, in addition, the joint portability ratio of NOTE2 (27) and the expected accuracy
  of the score trained by a marginal GWAS on a source cohort of any size at least two
  (`portabilityReport_and_training_eq_of_momentsAgreeAt_eight`).
* Agreement at every budget fixes the expected per-population squared correlation and the expected
  AUC, the metrics that are not rational in finitely many moments
  (`expectedMetrics_eq_of_momentsAgreeAt_all`).

Significance.  Portability is not a function of a genetic distance, of `F_ST`, or of any other
scalar summary of a demography: the master theorem's minimality witnesses rule scalars out.  What
it is a function of is exactly this ladder.  Every quantity the report contains is a propagator
applied to initial moments followed by one rational function, and two demographies that no finite
moment distinguishes give every population of every score the same report.

Scope.  Event histories only; the rate-history kernels have the same dot-product forms, but
agreement between an event history and a rate history is not stated here.  The report uses the
ratio-of-expectations queries of NOTE2 §6.2 and the pooled laws; only the last rung reaches
expected per-population metrics.  Whether a smaller rung can hold while a larger one fails, for
two explicit histories, is not settled here.

## Empirical status

None.  The bodies here are compositions of polynomial integrals against Markov kernels whose
moments are matrix computations of supplied rates, so no measurement can bear on them.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.PortabilityMomentLadder

open MeasureTheory ProbabilityTheory MvPolynomial Descent.Coalescent PartialHaplotypeCarrier
  PartialHaplotypeDualGenerator PartialHaplotypeDualSemigroup NeutralFellerGenerator
  NeutralPolynomialSemigroup PartialHaplotypeMicroscopicApproximation PartialHaplotypePulseKernel
  NeutralPulseHistoryKernel NeutralRateHistoryRealization NeutralRateHistoryKernel
  ReplicaMetricInstances EndToEndPortabilityLaw EndToEndCalibrationLaw EndToEndCorrelationSeries
  EndToEndDiscriminationLaw EndToEndPooledCalibration EndToEndGWASTrainingHistory
open scoped Matrix NNReal

noncomputable section

variable {Deme Locus : Type*} {Allele : Locus → Type*}
variable [Fintype Deme] [DecidableEq Deme] [Fintype Locus] [DecidableEq Locus]
  [∀ ℓ, Fintype (Allele ℓ)] [∀ ℓ, DecidableEq (Allele ℓ)]

/-! ## The statistic -/

/-- **Two histories agree at budget `n`**: from their initial states, their propagated budget-`n`
configuration moments are equal. -/
def MomentsAgreeAt (n : ℕ)
    (first second : List ((NeutralRates Deme Locus Allele × ℝ≥0) ⊕ PulseMatrix Deme))
    (x₁ x₂ : FrequencyState Deme Locus Allele) : Prop :=
  historyEventPropagator (fun _ ↦ n) first *ᵥ budgetMomentFeature (fun _ ↦ n) x₁
    = historyEventPropagator (fun _ ↦ n) second *ᵥ budgetMomentFeature (fun _ ↦ n) x₂

/-- A history, from one initial state, agrees with itself at every budget. -/
theorem momentsAgreeAt_refl (n : ℕ)
    (history : List ((NeutralRates Deme Locus Allele × ℝ≥0) ⊕ PulseMatrix Deme))
    (x₀ : FrequencyState Deme Locus Allele) : MomentsAgreeAt n history history x₀ x₀ :=
  rfl

/-- **Agreement descends the ladder.**  Two histories that agree at a budget agree at every smaller
budget.

Assumes: agreement at the larger budget. -/
theorem MomentsAgreeAt.mono (ℓ₀ : Locus) (hap₀ : FullHaplotype Locus Allele) {m n : ℕ}
    (hmn : m ≤ n)
    {first second : List ((NeutralRates Deme Locus Allele × ℝ≥0) ⊕ PulseMatrix Deme)}
    {x₁ x₂ : FrequencyState Deme Locus Allele} (h : MomentsAgreeAt n first second x₁ x₂) :
    MomentsAgreeAt m first second x₁ x₂ :=
  historyEventMoments_eq_of_le ℓ₀ hap₀ hmn h

/-! ## The report -/

/-- **The portability report of a score** for a source and a target deme. -/
structure PortabilityReport (Hap : Type*) [Fintype Hap] where
  /-- The pooled haplotype law of the source deme. -/
  sourcePooledLaw : FiniteReportLaw Hap
  /-- The pooled haplotype law of the target deme. -/
  targetPooledLaw : FiniteReportLaw Hap
  /-- The calibration slope of expectations in the source deme. -/
  sourceSlope : ℝ
  /-- The calibration slope of expectations in the target deme. -/
  targetSlope : ℝ
  /-- The calibration intercept of expectations in the source deme. -/
  sourceIntercept : ℝ
  /-- The calibration intercept of expectations in the target deme. -/
  targetIntercept : ℝ
  /-- The calibration portability of expectations. -/
  calibrationPortability : ℝ
  /-- The squared-correlation portability of expectations. -/
  accuracyPortability : ℝ
  /-- The AUC portability of expectations for the binary endpoint. -/
  aucPortability : ℝ

/-- **The portability report under a kernel** started at `x₀`, for a score, a quantitative outcome
and a binary endpoint. -/
def portabilityReport
    (κ : Kernel (FrequencyState Deme Locus Allele) (FrequencyState Deme Locus Allele))
    [IsMarkovKernel κ] (x0 : FrequencyState Deme Locus Allele) (source target : Deme)
    (score outcome : FullHaplotype Locus Allele → ℝ) (case : FullHaplotype Locus Allele → Bool) :
    PortabilityReport (FullHaplotype Locus Allele) where
  sourcePooledLaw := pooledLaw κ x0 source
  targetPooledLaw := pooledLaw κ x0 target
  sourceSlope := expectedCalibrationSlope κ x0 source score outcome
  targetSlope := expectedCalibrationSlope κ x0 target score outcome
  sourceIntercept := expectedCalibrationIntercept κ x0 source score outcome
  targetIntercept := expectedCalibrationIntercept κ x0 target score outcome
  calibrationPortability := expectedCalibrationPortability κ x0 source target score outcome
  accuracyPortability := expectedPortability κ x0 source target score outcome
  aucPortability := expectedAUCPortability κ x0 source target score case

/-! ## The ladder -/

/-- **Budget four fixes the report.**  Two histories whose propagated budget-4 moments agree give
every score, outcome, binary endpoint, source and target the same portability report: pooled
laws, calibration slopes and intercepts, and calibration, squared-correlation and AUC
portabilities.

Assumes: agreement at budget four. -/
theorem portabilityReport_eq_of_momentsAgreeAt_four (ℓ₀ : Locus)
    (hap₀ : FullHaplotype Locus Allele)
    {first second : List ((NeutralRates Deme Locus Allele × ℝ≥0) ⊕ PulseMatrix Deme)}
    {x₁ x₂ : FrequencyState Deme Locus Allele} (h : MomentsAgreeAt 4 first second x₁ x₂)
    (source target : Deme) (score outcome : FullHaplotype Locus Allele → ℝ)
    (case : FullHaplotype Locus Allele → Bool) :
    portabilityReport (historyEventKernel ℓ₀ hap₀ first) x₁ source target score outcome case
      = portabilityReport (historyEventKernel ℓ₀ hap₀ second) x₂ source target score outcome
          case := by
  have hone : MomentsAgreeAt 1 first second x₁ x₂ := h.mono ℓ₀ hap₀ (by norm_num : 1 ≤ 4)
  have htwo : MomentsAgreeAt 2 first second x₁ x₂ := h.mono ℓ₀ hap₀ (by norm_num : 2 ≤ 4)
  simp only [portabilityReport, PortabilityReport.mk.injEq]
  exact ⟨pooledLaw_eq_of_moments_eq ℓ₀ hap₀ hone source,
    pooledLaw_eq_of_moments_eq ℓ₀ hap₀ hone target,
    expectedCalibrationSlope_eq_of_moments_eq ℓ₀ hap₀ (by norm_num : 2 ≤ 4) h source score
      outcome,
    expectedCalibrationSlope_eq_of_moments_eq ℓ₀ hap₀ (by norm_num : 2 ≤ 4) h target score
      outcome,
    expectedCalibrationIntercept_eq_of_moments_eq ℓ₀ hap₀ (by norm_num : 3 ≤ 4) h source score
      outcome,
    expectedCalibrationIntercept_eq_of_moments_eq ℓ₀ hap₀ (by norm_num : 3 ≤ 4) h target score
      outcome,
    expectedCalibrationPortability_eq_of_moments_eq ℓ₀ hap₀ (by norm_num : 2 ≤ 4) h source target
      score outcome,
    expectedPortability_eq_of_moments_eq ℓ₀ hap₀ h source target score outcome,
    expectedAUCPortability_eq_of_moments_eq ℓ₀ hap₀ htwo source target score case⟩

/-- **Budget eight fixes the report, the joint ratio and trained accuracy.**  Two histories whose
propagated budget-8 moments agree have the same portability report, the same joint portability
ratio of NOTE2 (27), and, for every source cohort of at least two individuals and every tag coding,
the same expected accuracy of the score trained by a marginal GWAS in the source and deployed in the
target.

Assumes: agreement at budget eight. -/
theorem portabilityReport_and_training_eq_of_momentsAgreeAt_eight {J : Type*} [Fintype J]
    (ℓ₀ : Locus) (hap₀ : FullHaplotype Locus Allele)
    {first second : List ((NeutralRates Deme Locus Allele × ℝ≥0) ⊕ PulseMatrix Deme)}
    {x₁ x₂ : FrequencyState Deme Locus Allele} (h : MomentsAgreeAt 8 first second x₁ x₂)
    (source target : Deme) (score outcome : FullHaplotype Locus Allele → ℝ)
    (case : FullHaplotype Locus Allele → Bool) :
    portabilityReport (historyEventKernel ℓ₀ hap₀ first) x₁ source target score outcome case
        = portabilityReport (historyEventKernel ℓ₀ hap₀ second) x₂ source target score outcome
            case
      ∧ expectedJointPortability (historyEventKernel ℓ₀ hap₀ first) x₁ source target score outcome
        = expectedJointPortability (historyEventKernel ℓ₀ hap₀ second) x₂ source target score
            outcome
      ∧ ∀ size : ℕ, 2 ≤ size → ∀ genotype : FullHaplotype Locus Allele → J → ℝ,
        expectedTrainedAccuracy (historyEventKernel ℓ₀ hap₀ first) x₁ source target size
            genotype outcome
          = expectedTrainedAccuracy (historyEventKernel ℓ₀ hap₀ second) x₂ source target size
            genotype outcome :=
  ⟨portabilityReport_eq_of_momentsAgreeAt_four ℓ₀ hap₀ (h.mono ℓ₀ hap₀ (by norm_num : 4 ≤ 8))
      source target score outcome case,
    expectedJointPortability_eq_of_moments_eq ℓ₀ hap₀ h source target score outcome,
    fun _size hsize genotype ↦
      expectedTrainedAccuracy_eq_of_moments_eq ℓ₀ hap₀ h source target hsize genotype outcome⟩

/-- **Every budget fixes the expected metrics.**  Two histories whose propagated moments agree at
every budget have, in every deme, the same expected squared correlation of a score in the unit
interval against a binary endpoint, and the same expected AUC.

Assumes: agreement at every budget. -/
theorem expectedMetrics_eq_of_momentsAgreeAt_all (ℓ₀ : Locus)
    (hap₀ : FullHaplotype Locus Allele)
    {first second : List ((NeutralRates Deme Locus Allele × ℝ≥0) ⊕ PulseMatrix Deme)}
    {x₁ x₂ : FrequencyState Deme Locus Allele} (h : ∀ n : ℕ, MomentsAgreeAt n first second x₁ x₂)
    (deme : Deme) (score : FullHaplotype Locus Allele → ℝ)
    (case : FullHaplotype Locus Allele → Bool)
    (hscore0 : ∀ hap, 0 ≤ score hap) (hscore1 : ∀ hap, score hap ≤ 1) :
    expectedSquaredCorrelation (historyEventKernel ℓ₀ hap₀ first) x₁ deme score
        (fun hap ↦ if case hap then 1 else 0)
      = expectedSquaredCorrelation (historyEventKernel ℓ₀ hap₀ second) x₂ deme score
        (fun hap ↦ if case hap then 1 else 0)
    ∧ expectedAUC (historyEventKernel ℓ₀ hap₀ first) x₁ deme score case
      = expectedAUC (historyEventKernel ℓ₀ hap₀ second) x₂ deme score case :=
  expectedSquaredCorrelation_and_expectedAUC_eq_of_moments_eq ℓ₀ hap₀
    (fun k ↦ h (4 * (k + 1))) deme score case hscore0 hscore1

end

end Descent.Portability.PortabilityMomentLadder
