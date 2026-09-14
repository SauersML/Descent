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

Any process law.  The report depends on the process law only through polynomial expectations, so
the ladder holds for every Markov kernel on frequency states with dual moments, NOTE1 (20).
`PolynomialsAgreeAt n κ₁ κ₂ x₁ x₂` says that two kernels, from two initial states, give every
frequency polynomial of total degree at most `n` one expectation (`polynomialsAgreeAt_refl`,
`PolynomialsAgreeAt.mono`).  Equal propagated moments give it for any two kernels with dual
moments (`polynomialsAgreeAt_of_hasDualMoments`), two event histories included
(`MomentsAgreeAt.polynomialsAgreeAt`), and agreement up to degree four fixes the report
(`portabilityReport_eq_of_polynomialsAgreeAt_four`).  So a history of epochs, splits and pulses
and a continuous rate history whose propagated budget-4 moments agree are indistinguishable by
every metric of the report (`portabilityReport_historyEvent_eq_rateHistory`).

Significance.  Portability is not a function of a genetic distance, of `F_ST`, or of any other
scalar summary of a demography: the master theorem's minimality witnesses rule scalars out.  What
it is a function of is exactly this ladder.  Every quantity the report contains is a propagator
applied to initial moments followed by one rational function, and two demographies that no finite
moment distinguishes give every population of every score the same report.

Scope.  The budget-8 and every-budget rungs are stated for event histories.  The report uses the
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

attribute [local instance] isMarkovKernel_historyEventKernel isMarkovKernel_rateHistoryKernel

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

/-! ## Any process law with dual moments -/

/-- **Two process laws agree up to degree `n`**: from their initial states, every frequency
polynomial of total degree at most `n` has one expectation under both. -/
def PolynomialsAgreeAt (n : ℕ)
    (κ₁ κ₂ : Kernel (FrequencyState Deme Locus Allele) (FrequencyState Deme Locus Allele))
    (x₁ x₂ : FrequencyState Deme Locus Allele) : Prop :=
  ∀ p : FrequencyPolynomial Deme Locus Allele, p.totalDegree ≤ n →
    ∫ y, polynomialFunction p y ∂(κ₁ x₁) = ∫ y, polynomialFunction p y ∂(κ₂ x₂)

/-- A process law, from one initial state, agrees with itself at every degree. -/
theorem polynomialsAgreeAt_refl (n : ℕ)
    (κ : Kernel (FrequencyState Deme Locus Allele) (FrequencyState Deme Locus Allele))
    (x₀ : FrequencyState Deme Locus Allele) : PolynomialsAgreeAt n κ κ x₀ x₀ :=
  fun _ _ ↦ rfl

/-- **Agreement up to a degree is agreement up to every smaller degree.**

Assumes: agreement up to the larger degree. -/
theorem PolynomialsAgreeAt.mono {m n : ℕ} (hmn : m ≤ n)
    {κ₁ κ₂ : Kernel (FrequencyState Deme Locus Allele) (FrequencyState Deme Locus Allele)}
    {x₁ x₂ : FrequencyState Deme Locus Allele} (h : PolynomialsAgreeAt n κ₁ κ₂ x₁ x₂) :
    PolynomialsAgreeAt m κ₁ κ₂ x₁ x₂ :=
  fun p hp ↦ h p (hp.trans hmn)

/-- **Equal propagated moments give equal polynomial observables.**  Two Markov kernels whose
budget-`n` configuration moments are matrices applied to the initial moments, and whose propagated
budget-`n` moments agree, agree on every frequency polynomial of total degree at most `n`.

Assumes: `HasDualMoments κ₁ n M₁`, `HasDualMoments κ₂ n M₂` and equal propagated moments. -/
theorem polynomialsAgreeAt_of_hasDualMoments (ℓ₀ : Locus) {n : ℕ}
    {κ₁ κ₂ : Kernel (FrequencyState Deme Locus Allele) (FrequencyState Deme Locus Allele)}
    [IsMarkovKernel κ₁] [IsMarkovKernel κ₂] {M₁ M₂ : BudgetMatrix Deme Locus Allele n}
    (h₁ : HasDualMoments κ₁ n M₁) (h₂ : HasDualMoments κ₂ n M₂)
    {x₁ x₂ : FrequencyState Deme Locus Allele}
    (hmoments : M₁ *ᵥ budgetMomentFeature (fun _ ↦ n) x₁
      = M₂ *ᵥ budgetMomentFeature (fun _ ↦ n) x₂) :
    PolynomialsAgreeAt n κ₁ κ₂ x₁ x₂ := by
  intro p hp
  rw [integral_polynomial_eq_dotProduct ℓ₀ (fun _ ↦ n) κ₁ M₁ h₁ p
      (withinBudget_of_totalDegree_le ℓ₀ p hp) x₁,
    integral_polynomial_eq_dotProduct ℓ₀ (fun _ ↦ n) κ₂ M₂ h₂ p
      (withinBudget_of_totalDegree_le ℓ₀ p hp) x₂, hmoments]

/-- **Agreement of two event histories is agreement of their process laws.**

Assumes: agreement at budget `n`. -/
theorem MomentsAgreeAt.polynomialsAgreeAt (ℓ₀ : Locus) (hap₀ : FullHaplotype Locus Allele)
    {n : ℕ} {first second : List ((NeutralRates Deme Locus Allele × ℝ≥0) ⊕ PulseMatrix Deme)}
    {x₁ x₂ : FrequencyState Deme Locus Allele} (h : MomentsAgreeAt n first second x₁ x₂) :
    PolynomialsAgreeAt n (historyEventKernel ℓ₀ hap₀ first) (historyEventKernel ℓ₀ hap₀ second)
      x₁ x₂ :=
  polynomialsAgreeAt_of_hasDualMoments ℓ₀ (hasDualMoments_historyEventKernel ℓ₀ hap₀ first n)
    (hasDualMoments_historyEventKernel ℓ₀ hap₀ second n) h

/-- **Budget four fixes the report under any process law.**  Two Markov kernels that agree, from
their initial states, on every frequency polynomial of total degree at most four give every score,
outcome, binary endpoint, source and target the same portability report.

Assumes: agreement up to degree four. -/
theorem portabilityReport_eq_of_polynomialsAgreeAt_four
    {κ₁ κ₂ : Kernel (FrequencyState Deme Locus Allele) (FrequencyState Deme Locus Allele)}
    [IsMarkovKernel κ₁] [IsMarkovKernel κ₂] {x₁ x₂ : FrequencyState Deme Locus Allele}
    (h : PolynomialsAgreeAt 4 κ₁ κ₂ x₁ x₂) (source target : Deme)
    (score outcome : FullHaplotype Locus Allele → ℝ) (case : FullHaplotype Locus Allele → Bool) :
    portabilityReport κ₁ x₁ source target score outcome case
      = portabilityReport κ₂ x₂ source target score outcome case := by
  have hmass : ∀ (deme : Deme) (hap : FullHaplotype Locus Allele),
      ∫ y, (stateLaw y deme).mass hap ∂(κ₁ x₁) = ∫ y, (stateLaw y deme).mass hap ∂(κ₂ x₂) :=
    fun deme hap ↦ by
      simpa only [polynomialFunction_demePolynomial_X] using
        h (demePolynomial deme (X hap))
          ((totalDegree_demePolynomial_X_le deme hap).trans (by norm_num))
  have hcovariance : ∀ (deme : Deme) (first second : FullHaplotype Locus Allele → ℝ),
      ∫ y, (stateLaw y deme).covariance first second ∂(κ₁ x₁)
        = ∫ y, (stateLaw y deme).covariance first second ∂(κ₂ x₂) :=
    fun deme first second ↦ by
      simpa only [polynomialFunction_demeCovariancePolynomial] using
        h (demeCovariancePolynomial deme first second)
          ((totalDegree_demeCovariancePolynomial_le deme first second).trans (by norm_num))
  have hvariance : ∀ (deme : Deme) (value : FullHaplotype Locus Allele → ℝ),
      ∫ y, (stateLaw y deme).variance value ∂(κ₁ x₁)
        = ∫ y, (stateLaw y deme).variance value ∂(κ₂ x₂) :=
    fun deme value ↦ hcovariance deme value value
  have hslope : ∀ deme : Deme, expectedCalibrationSlope κ₁ x₁ deme score outcome
      = expectedCalibrationSlope κ₂ x₂ deme score outcome := fun deme ↦ by
    rw [expectedCalibrationSlope, expectedCalibrationSlope, hcovariance deme score outcome,
      hvariance deme score]
  have hintercept : ∀ deme : Deme, expectedCalibrationIntercept κ₁ x₁ deme score outcome
      = expectedCalibrationIntercept κ₂ x₂ deme score outcome := fun deme ↦ by
    have hinterceptNumerator := h (interceptNumeratorPolynomial deme score outcome)
      ((totalDegree_interceptNumeratorPolynomial_le deme score outcome).trans (by norm_num))
    simp only [polynomialFunction_interceptNumeratorPolynomial] at hinterceptNumerator
    rw [expectedCalibrationIntercept, expectedCalibrationIntercept, hinterceptNumerator,
      hvariance deme score]
  have hnumerator : ∀ deme : Deme,
      ∫ y, correlationNumerator (stateLaw y deme) score outcome ∂(κ₁ x₁)
        = ∫ y, correlationNumerator (stateLaw y deme) score outcome ∂(κ₂ x₂) := fun deme ↦ by
    simpa only [polynomialFunction_numeratorPolynomial] using
      h (numeratorPolynomial deme score outcome)
        (totalDegree_numeratorPolynomial_le deme score outcome)
  have hdenominator : ∀ deme : Deme,
      ∫ y, correlationDenominator (stateLaw y deme) score outcome ∂(κ₁ x₁)
        = ∫ y, correlationDenominator (stateLaw y deme) score outcome ∂(κ₂ x₂) := fun deme ↦ by
    simpa only [polynomialFunction_denominatorPolynomial] using
      h (denominatorPolynomial deme score outcome)
        (totalDegree_denominatorPolynomial_le deme score outcome)
  have haucNumerator : ∀ deme : Deme,
      ∫ y, aucNumerator (stateLaw y deme) score case ∂(κ₁ x₁)
        = ∫ y, aucNumerator (stateLaw y deme) score case ∂(κ₂ x₂) := fun deme ↦ by
    simpa only [polynomialFunction_apply, eval_demePolynomial, eval_aucNumeratorPolynomial] using
      h (demePolynomial deme (aucNumeratorPolynomial score case))
        ((totalDegree_rename_le _ _).trans
          ((totalDegree_aucNumeratorPolynomial_le score case).trans (by norm_num)))
  have haucDenominator : ∀ deme : Deme,
      ∫ y, aucDenominator (stateLaw y deme) case ∂(κ₁ x₁)
        = ∫ y, aucDenominator (stateLaw y deme) case ∂(κ₂ x₂) := fun deme ↦ by
    simpa only [polynomialFunction_apply, eval_demePolynomial, eval_aucDenominatorPolynomial]
      using h (demePolynomial deme (aucDenominatorPolynomial case))
        ((totalDegree_rename_le _ _).trans
          ((totalDegree_aucDenominatorPolynomial_le case).trans (by norm_num)))
  simp only [portabilityReport, PortabilityReport.mk.injEq]
  refine ⟨?_, ?_, hslope source, hslope target, hintercept source, hintercept target, ?_, ?_, ?_⟩
  · ext hap
    exact hmass source hap
  · ext hap
    exact hmass target hap
  · rw [expectedCalibrationPortability, expectedCalibrationPortability, hslope source,
      hslope target]
  · rw [expectedPortability, expectedPortability, hnumerator target, hdenominator source,
      hdenominator target, hnumerator source]
  · rw [expectedAUCPortability, expectedAUCPortability, haucNumerator target,
      haucDenominator source, haucDenominator target, haucNumerator source]

/-- **An event history and a rate history with equal propagated moments are indistinguishable.**
If a history of epochs, splits and pulses from `x₁` and a rate history with continuous dual
generator from `x₂` have equal propagated budget-4 moments, every score, outcome, binary endpoint,
source and target has the same portability report under both.

Assumes: equal propagated budget-4 moments. -/
theorem portabilityReport_historyEvent_eq_rateHistory (ℓ₀ : Locus)
    (hap₀ : FullHaplotype Locus Allele)
    (events : List ((NeutralRates Deme Locus Allele × ℝ≥0) ⊕ PulseMatrix Deme))
    {rates : ℝ → NeutralRates Deme Locus Allele} {T : ℝ} (hT : 0 ≤ T)
    (hcontinuous : ∀ capacity : Locus → ℕ,
      ContinuousOn (fun t ↦ dualGenerator (rates t) capacity) (Set.Icc 0 T))
    {x₁ x₂ : FrequencyState Deme Locus Allele}
    (hmoments : historyEventPropagator (fun _ ↦ 4) events *ᵥ budgetMomentFeature (fun _ ↦ 4) x₁
      = rateHistoryDualPropagator rates (fun _ ↦ 4) T *ᵥ budgetMomentFeature (fun _ ↦ 4) x₂)
    (source target : Deme) (score outcome : FullHaplotype Locus Allele → ℝ)
    (case : FullHaplotype Locus Allele → Bool) :
    portabilityReport (historyEventKernel ℓ₀ hap₀ events) x₁ source target score outcome case
      = portabilityReport (rateHistoryKernel rates ℓ₀ hap₀ hT hcontinuous) x₂ source target score
          outcome case :=
  portabilityReport_eq_of_polynomialsAgreeAt_four
    (polynomialsAgreeAt_of_hasDualMoments ℓ₀ (hasDualMoments_historyEventKernel ℓ₀ hap₀ events 4)
      (hasDualMoments_rateHistoryKernel hT hcontinuous ℓ₀ hap₀ 4) hmoments)
    source target score outcome case

end

end Descent.Portability.PortabilityMomentLadder
