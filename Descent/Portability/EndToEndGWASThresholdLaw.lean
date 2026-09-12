/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.EndToEndAscertainedLaw
import Descent.Portability.EndToEndGWASTrainingHistory

assert_below Descent.Decision Descent.Program

/-!
# The exact accuracy of a GWAS score thresholded on its own training cohort

`EndToEndGWASTrainingLaw` trains a score on a fixed tag set.  `EndToEndAscertainedLaw` keeps tags by
a rule read on a panel, with weights that do not come from the panel.  Clumping and thresholding
does both on one cohort: the same individuals estimate the effects and decide which tags keep
them.  This module gives the exact accuracy of such scores, and the winner's curse they carry.

Learned scores.  A learner is any statistic `learn` of a training cohort of `n` individuals drawn
from the source law; its value on a cohort is a weight vector.  The expected target correlation
numerator and denominator of the learned score are the second-moment matrix of the learned weights
read against the target matrices `16 c cᵀ` and `16 C_t(X_i, X_j) V_t(Y)` (`learnedNumerator_eq`,
`learnedDenominator_eq`).  The marginal-effect GWAS is the learner `gwasWeights`
(`trainedAccuracy_eq_learnedAccuracy`).  With one tag every learner gives the target squared
correlation of the tag, whatever its second moment (`learnedAccuracy_unique`).

Thresholding.  `covarianceThresholdWeights` keeps a tag's sample covariance with the outcome when
that covariance is at least `t` in absolute value, and zeroes it otherwise.  It is the corpus
p-value stage `PThresholdTrainingLaw.thresholdWeights` read on the cohort's own table with `−|ĉ_j|`
as the p-value (`covarianceThresholdWeights_eq_thresholdWeights`).  At `t ≤ 0` it is the
unthresholded GWAS (`covarianceThresholdWeights_of_nonpos`, `thresholdedAccuracy_of_nonpos`).  The
threshold here is on the sample covariance.  No polynomial form of the rule is needed: a cohort
expectation is a finite sum over cohorts, so every rule computable from the cohort gives an exact
law at the same budget.  A t-statistic or p-value cutoff, and clumping on the cohort's own LD, are
each their own `learn`.

The law along a history.  At a state, the second moments of a learner are the acceptance
polynomials of `EndToEndAscertainedLaw` of the products `learn_i learn_j`, over a panel of `n` draws
from the source deme, of total degree at most `n`.  The target matrices are polynomials of degree at
most four (`learnedPolynomial`, `polynomialFunction_learnedPolynomial`,
`totalDegree_learnedPolynomial_le`, `learnedNumerator_stateLaw`, `learnedDenominator_stateLaw`).  So
along a history of epochs, splits and pulses, or a rate history, the expected numerator and
denominator are budget-`(n + 4)` pairings with the propagated moments `U · H_{n+4}(x₀)`
(`integral_learnedNumerator_historyEventKernel`, `integral_learnedDenominator_historyEventKernel`,
and the rate forms).  The expected learned accuracy, thresholded scores included, is the rational
function `momentLearnedAccuracy` of `U · H_{n+4}(x₀)` (`expectedLearnedAccuracy_historyEventKernel`,
`expectedLearnedAccuracy_rateHistoryKernel`).  Equal propagated budget-`(n + 4)` moments give equal
accuracy (`expectedLearnedAccuracy_eq_of_moments_eq`).  The budget is `n + 4`, not `n + 8`: the
cohort monomials carry degree `n` in the source frequencies and absorb the source moments, and only
the target matrices add degree.

The winner's curse.
* An observable covaries nonnegatively with every monotone function of itself
  (`covariance_monotone_nonneg`), so selecting an upper tail raises the mean
  (`expectation_mul_le_expectation_upperTail`).
* In magnitude the curse holds for every cohort size, threshold and tag:
  `|w_j| P(|ŵ_j| ≥ t) ≤ E|ŵ_j 1{|ŵ_j| ≥ t}|`.  Conditional on selection, the selected estimate is on
  average at least as large as the true effect (`abs_marginalWeights_mul_le_expectation_abs`,
  `abs_marginalWeights_le_conditional`).
* The signed statement is false for two-sided selection.  On a three-haplotype law whose rare
  haplotype carries an extreme tag and an opposite extreme outcome, the true effect is positive and
  below the threshold, selection has positive probability, and the expected selected weight is
  negative (`curseWitness_marginalWeights`, `curseWitness_selection`).
* On the same law the population thresholded weight is zero, so the population thresholded accuracy
  is zero, while the thresholded accuracy of a cohort of two is positive (`curseWitness_accuracy`).

Scope.  Haploid individuals, one training cohort, the ratio-of-expectations query, and outcomes that
are functions of the individual.  The law is exact, not efficient: a cohort of `n` from a law on
`|Ω|` individuals has `|Ω|^n` terms, and the budget grows with `n`.  No large-cohort limit of the
thresholded law is stated, and thresholding has no general sign on accuracy.

## Empirical status

None.  The bodies here are finite sums over independent product laws, polynomial identities and
integrals of polynomials against Markov kernels, so no measurement can bear on them.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.EndToEndGWASThresholdLaw

open MeasureTheory ProbabilityTheory MvPolynomial Descent.Coalescent PartialHaplotypeCarrier
  PartialHaplotypeDualGenerator PartialHaplotypeDualSemigroup NeutralFellerGenerator
  NeutralPolynomialSemigroup PartialHaplotypeMicroscopicApproximation PartialHaplotypePulseKernel
  NeutralPulseHistoryKernel NeutralRateHistoryRealization NeutralRateHistoryKernel
  ReplicaMetricInstances EndToEndPortabilityLaw EndToEndDiploidHistoryLaw EndToEndAscertainedLaw
  TrainingNoiseAccuracy FourCellCohortLaw EndToEndGWASTrainingLaw EndToEndGWASTrainingHistory
open scoped Matrix NNReal

noncomputable section

/-! ## Scores learned from a training cohort -/

section Learned

variable {Ω J : Type*} [Fintype Ω] [Fintype J]

/-- **The expected target correlation numerator of a learned score.**  The weights are any
statistic `learn` of a training cohort of `size` individuals from the source law. -/
def learnedNumerator (source target : FiniteReportLaw Ω) (size : ℕ)
    (learn : (Fin size → Ω) → J → ℝ) (genotype : Ω → J → ℝ) (outcome : Ω → ℝ) : ℝ :=
  (cohortLaw source size).expectation fun sample ↦
    correlationNumerator target (linearScore genotype (learn sample)) outcome

/-- **The expected target correlation denominator of a learned score.** -/
def learnedDenominator (source target : FiniteReportLaw Ω) (size : ℕ)
    (learn : (Fin size → Ω) → J → ℝ) (genotype : Ω → J → ℝ) (outcome : Ω → ℝ) : ℝ :=
  (cohortLaw source size).expectation fun sample ↦
    correlationDenominator target (linearScore genotype (learn sample)) outcome

/-- **The learned accuracy**: the expected target numerator over the expected target denominator.
NOTE2 §6.2 query: a ratio of expectations over the training cohort. -/
def learnedAccuracy (source target : FiniteReportLaw Ω) (size : ℕ)
    (learn : (Fin size → Ω) → J → ℝ) (genotype : Ω → J → ℝ) (outcome : Ω → ℝ) : ℝ :=
  learnedNumerator source target size learn genotype outcome
    / learnedDenominator source target size learn genotype outcome

/-- The trained accuracy of the marginal-effect GWAS is the learned accuracy of the learner
`gwasWeights`. -/
theorem trainedAccuracy_eq_learnedAccuracy (source target : FiniteReportLaw Ω) (size : ℕ)
    (genotype : Ω → J → ℝ) (outcome : Ω → ℝ) :
    trainedAccuracy source target size genotype outcome
      = learnedAccuracy source target size (gwasWeights genotype outcome) genotype outcome :=
  rfl

/-- **The learned numerator is a quadratic form in the second-moment matrix of the learned
weights**, read against the target numerator matrix `16 c cᵀ`. -/
theorem learnedNumerator_eq (source target : FiniteReportLaw Ω) (size : ℕ)
    (learn : (Fin size → Ω) → J → ℝ) (genotype : Ω → J → ℝ) (outcome : Ω → ℝ) :
    learnedNumerator source target size learn genotype outcome
      = ∑ i, ∑ j, numeratorMatrix target genotype outcome i j
          * (cohortLaw source size).expectation (fun sample ↦ learn sample i * learn sample j) := by
  rw [learnedNumerator]
  simp only [correlationNumerator_linearScore]
  rw [FiniteIndependentMoments.expectation_sum]
  simp only [FiniteIndependentMoments.expectation_sum, expectation_const_mul_observable]

/-- **The learned denominator is a quadratic form in the second-moment matrix of the learned
weights**, read against the target denominator matrix `16 C_t(X_i, X_j) V_t(Y)`. -/
theorem learnedDenominator_eq (source target : FiniteReportLaw Ω) (size : ℕ)
    (learn : (Fin size → Ω) → J → ℝ) (genotype : Ω → J → ℝ) (outcome : Ω → ℝ) :
    learnedDenominator source target size learn genotype outcome
      = ∑ i, ∑ j, denominatorMatrix target genotype outcome i j
          * (cohortLaw source size).expectation (fun sample ↦ learn sample i * learn sample j) := by
  rw [learnedDenominator]
  simp only [correlationDenominator_linearScore]
  rw [FiniteIndependentMoments.expectation_sum]
  simp only [FiniteIndependentMoments.expectation_sum, expectation_const_mul_observable]

/-- **With a single tag, every learner gives the target accuracy of the tag.**  Both accumulators
are the second moment of the learned weight times a target constant, so the learned accuracy is the
target squared-correlation ratio of the tag whenever that second moment is nonzero. -/
theorem learnedAccuracy_unique [Unique J] (source target : FiniteReportLaw Ω) (size : ℕ)
    (learn : (Fin size → Ω) → J → ℝ) (genotype : Ω → J → ℝ) (outcome : Ω → ℝ)
    (hsecond : (cohortLaw source size).expectation
      (fun sample ↦ learn sample default * learn sample default) ≠ 0) :
    learnedAccuracy source target size learn genotype outcome
      = correlationNumerator target (fun individual ↦ genotype individual default) outcome
        / correlationDenominator target (fun individual ↦ genotype individual default) outcome := by
  rw [learnedAccuracy, learnedNumerator_eq, learnedDenominator_eq]
  simp only [Fintype.sum_unique]
  rw [mul_div_mul_right _ _ hsecond]
  simp only [numeratorMatrix, denominatorMatrix, marginalWeights, correlationNumerator,
    correlationDenominator, FiniteReportLaw.variance, sq]

/-! ## Thresholding on the training cohort -/

/-- **The covariance-thresholded GWAS weights.**  A tag keeps its sample covariance with the
outcome when that covariance is at least `t` in absolute value, and gets weight zero otherwise.
Selection and estimation read the same training cohort. -/
def covarianceThresholdWeights (t : ℝ) (genotype : Ω → J → ℝ) (outcome : Ω → ℝ) {size : ℕ}
    (sample : Fin size → Ω) : J → ℝ :=
  fun marker ↦
    if t ≤ |gwasWeights genotype outcome sample marker| then
      gwasWeights genotype outcome sample marker
    else 0

/-- **The cohort's GWAS table**: the corpus clumped table of a training cohort, with every tag
usable and clumped, the negative absolute sample covariance as the ranking p-value, and the sample
covariance as the effect. -/
def cohortClumpedTable (genotype : Ω → J → ℝ) (outcome : Ω → ℝ) {size : ℕ}
    (sample : Fin size → Ω) : PThresholdTrainingLaw.ClumpedTable J where
  usable := Finset.univ
  clumped := Finset.univ
  pValue marker := -|gwasWeights genotype outcome sample marker|
  effect := gwasWeights genotype outcome sample

/-- **The covariance threshold is the corpus p-value stage of clumping and thresholding**, read on
the cohort's own table at p-value threshold `−t`. -/
theorem covarianceThresholdWeights_eq_thresholdWeights (t : ℝ) (genotype : Ω → J → ℝ)
    (outcome : Ω → ℝ) {size : ℕ} (sample : Fin size → Ω) :
    covarianceThresholdWeights t genotype outcome sample
      = PThresholdTrainingLaw.thresholdWeights (cohortClumpedTable genotype outcome sample)
          (-t) := by
  funext marker
  by_cases hselect : t ≤ |gwasWeights genotype outcome sample marker| <;>
    simp [covarianceThresholdWeights, PThresholdTrainingLaw.thresholdWeights,
      PThresholdTrainingLaw.thresholdRows, cohortClumpedTable, hselect]

/-- A nonpositive threshold keeps every tag: the thresholded weights are the GWAS weights. -/
theorem covarianceThresholdWeights_of_nonpos {t : ℝ} (ht : t ≤ 0) (genotype : Ω → J → ℝ)
    (outcome : Ω → ℝ) (size : ℕ) :
    (covarianceThresholdWeights t genotype outcome : (Fin size → Ω) → J → ℝ)
      = gwasWeights genotype outcome :=
  funext fun _ ↦ funext fun _ ↦ if_pos (ht.trans (abs_nonneg _))

/-- **The thresholded accuracy**: the learned accuracy of the covariance-thresholded GWAS. -/
def thresholdedAccuracy (source target : FiniteReportLaw Ω) (size : ℕ) (t : ℝ)
    (genotype : Ω → J → ℝ) (outcome : Ω → ℝ) : ℝ :=
  learnedAccuracy source target size (covarianceThresholdWeights t genotype outcome) genotype
    outcome

/-- A nonpositive threshold gives the trained accuracy of the unthresholded GWAS. -/
theorem thresholdedAccuracy_of_nonpos (source target : FiniteReportLaw Ω) (size : ℕ) {t : ℝ}
    (ht : t ≤ 0) (genotype : Ω → J → ℝ) (outcome : Ω → ℝ) :
    thresholdedAccuracy source target size t genotype outcome
      = trainedAccuracy source target size genotype outcome := by
  rw [thresholdedAccuracy, covarianceThresholdWeights_of_nonpos ht genotype outcome size,
    trainedAccuracy_eq_learnedAccuracy]

/-- **The population thresholded weights**: the threshold applied to the true marginal effects. -/
def populationThresholdWeights (law : FiniteReportLaw Ω) (t : ℝ) (genotype : Ω → J → ℝ)
    (outcome : Ω → ℝ) : J → ℝ :=
  fun marker ↦
    if t ≤ |marginalWeights law genotype outcome marker| then
      marginalWeights law genotype outcome marker
    else 0

/-! ## The winner's curse -/

/-- **An observable covaries nonnegatively with every monotone function of itself.**  The pair
kernel of two independent draws is a product of two differences of one sign. -/
theorem covariance_monotone_nonneg (law : FiniteReportLaw Ω) (value : Ω → ℝ) {g : ℝ → ℝ}
    (hg : Monotone g) : 0 ≤ law.covariance value fun individual ↦ g (value individual) := by
  rw [← expectation_sampleCovariance law (le_refl 2)]
  refine ReplicaDomainCertificate.expectation_nonneg _ _ fun sample ↦ ?_
  rw [sampleCovariance_two]
  refine div_nonneg ?_ zero_le_two
  rcases le_total (value (sample 0)) (value (sample 1)) with h | h
  · nlinarith [sub_nonpos.mpr h, sub_nonpos.mpr (hg h)]
  · nlinarith [sub_nonneg.mpr h, sub_nonneg.mpr (hg h)]

/-- **Selecting an upper tail raises the mean**: `E[X] P(X ≥ t) ≤ E[X 1{X ≥ t}]`. -/
theorem expectation_mul_le_expectation_upperTail (law : FiniteReportLaw Ω) (value : Ω → ℝ)
    (t : ℝ) :
    law.expectation value
        * law.expectation (fun individual ↦ if t ≤ value individual then 1 else 0)
      ≤ law.expectation fun individual ↦
          value individual * if t ≤ value individual then 1 else 0 := by
  have hmonotone : Monotone fun x : ℝ ↦ if t ≤ x then (1 : ℝ) else 0 := by
    intro a b hab
    show (if t ≤ a then (1 : ℝ) else 0) ≤ if t ≤ b then 1 else 0
    split_ifs <;> first | norm_num | linarith
  have h := covariance_monotone_nonneg law value hmonotone
  rw [FiniteReportLaw.covariance_eq_rawMoments] at h
  linarith

/-- The magnitude of an expectation is at most the expectation of the magnitude. -/
theorem abs_expectation_le_expectation_abs (law : FiniteReportLaw Ω) (value : Ω → ℝ) :
    |law.expectation value| ≤ law.expectation fun individual ↦ |value individual| := by
  have hupper := BellmanReportBounds.expectation_mono law value _
    fun individual ↦ le_abs_self (value individual)
  have hlower := BellmanReportBounds.expectation_mono law
    (fun individual ↦ -1 * |value individual|) value fun individual ↦ by
      have hneg := neg_abs_le (value individual)
      linarith
  rw [expectation_const_mul_observable] at hlower
  exact abs_le.mpr ⟨by linarith, hupper⟩

/-- **The winner's curse in magnitude.**  For every cohort size `n ≥ 2`, threshold `t` and tag, the
true marginal magnitude times the selection probability is at most the expected magnitude of the
thresholded weight: `|w_j| P(|ŵ_j| ≥ t) ≤ E|ŵ_j 1{|ŵ_j| ≥ t}|`. -/
theorem abs_marginalWeights_mul_le_expectation_abs (law : FiniteReportLaw Ω) {size : ℕ}
    (hsize : 2 ≤ size) (t : ℝ) (genotype : Ω → J → ℝ) (outcome : Ω → ℝ) (marker : J) :
    |marginalWeights law genotype outcome marker|
        * (cohortLaw law size).expectation (fun sample ↦
          if t ≤ |gwasWeights genotype outcome sample marker| then 1 else 0)
      ≤ (cohortLaw law size).expectation fun sample ↦
          |covarianceThresholdWeights t genotype outcome sample marker| := by
  have hselection : (cohortLaw law size).expectation
        (fun sample ↦ |gwasWeights genotype outcome sample marker|)
        * (cohortLaw law size).expectation (fun sample ↦
          if t ≤ |gwasWeights genotype outcome sample marker| then (1 : ℝ) else 0)
      ≤ (cohortLaw law size).expectation fun sample ↦
          |gwasWeights genotype outcome sample marker|
            * if t ≤ |gwasWeights genotype outcome sample marker| then (1 : ℝ) else 0 :=
    expectation_mul_le_expectation_upperTail (cohortLaw law size)
      (fun sample ↦ |gwasWeights genotype outcome sample marker|) t
  have hmean : |marginalWeights law genotype outcome marker|
      ≤ (cohortLaw law size).expectation fun sample ↦
          |gwasWeights genotype outcome sample marker| := by
    rw [← expectation_gwasWeights law hsize genotype outcome marker]
    exact abs_expectation_le_expectation_abs _ _
  have hprobability : 0 ≤ (cohortLaw law size).expectation (fun sample ↦
      if t ≤ |gwasWeights genotype outcome sample marker| then (1 : ℝ) else 0) :=
    ReplicaDomainCertificate.expectation_nonneg _ _ fun sample ↦ by split_ifs <;> norm_num
  have hpoint : (fun sample ↦ |gwasWeights genotype outcome sample marker|
      * if t ≤ |gwasWeights genotype outcome sample marker| then (1 : ℝ) else 0)
      = fun sample ↦ |covarianceThresholdWeights t genotype outcome sample marker| := by
    funext sample
    simp only [covarianceThresholdWeights]
    split_ifs <;> simp
  rw [hpoint] at hselection
  exact (mul_le_mul_of_nonneg_right hmean hprobability).trans hselection

/-- **The winner's curse conditional on selection.**  Whenever the tag is selected with positive
probability, the expected magnitude of the selected estimate given selection is at least the true
marginal magnitude. -/
theorem abs_marginalWeights_le_conditional (law : FiniteReportLaw Ω) {size : ℕ}
    (hsize : 2 ≤ size) (t : ℝ) (genotype : Ω → J → ℝ) (outcome : Ω → ℝ) (marker : J)
    (hselected : 0 < (cohortLaw law size).expectation (fun sample ↦
      if t ≤ |gwasWeights genotype outcome sample marker| then 1 else 0)) :
    |marginalWeights law genotype outcome marker|
      ≤ (cohortLaw law size).expectation (fun sample ↦
            |covarianceThresholdWeights t genotype outcome sample marker|)
        / (cohortLaw law size).expectation (fun sample ↦
            if t ≤ |gwasWeights genotype outcome sample marker| then 1 else 0) :=
  (le_div_iff₀ hselected).mpr
    (abs_marginalWeights_mul_le_expectation_abs law hsize t genotype outcome marker)

/-- A cohort of two reads any statistic as the double sum over its two members. -/
theorem expectation_cohortLaw_two_eq_sum (law : FiniteReportLaw Ω)
    (statistic : (Fin 2 → Ω) → ℝ) :
    (cohortLaw law 2).expectation statistic
      = ∑ first, ∑ second, law.mass first * (law.mass second * statistic ![first, second]) := by
  have hpair : (cohortLaw law 2).expectation statistic
      = (cohortLaw law 2).expectation fun sample ↦ statistic ![sample 0, sample 1] := by
    congr 1
    funext sample
    congr 1
    funext member
    fin_cases member <;> rfl
  rw [hpair, expectation_cohortLaw_two law fun first second ↦ statistic ![first, second]]
  simp only [FiniteReportLaw.expectation, Finset.mul_sum]

end Learned

/-! ## A one-tag witness -/

/-- The witness law on three haplotypes, with masses `999/2000, 999/2000, 1/1000`: a common pair
and one rare haplotype. -/
def curseWitnessLaw : FiniteReportLaw (Fin 3) where
  mass := ![999 / 2000, 999 / 2000, 1 / 1000]
  mass_nonneg := by
    intro haplotype
    fin_cases haplotype <;> norm_num
  mass_sum := by
    simp [Fin.sum_univ_three] <;> norm_num

/-- The witness tag, `0, 1, 10` on the three haplotypes. -/
def curseWitnessGenotype (haplotype : Fin 3) (_ : Unit) : ℝ :=
  ![0, 1, 10] haplotype

/-- The witness outcome, `0, 1, −10` on the three haplotypes: the rare haplotype carries an extreme
tag and an extreme outcome of the opposite sign. -/
def curseWitnessOutcome (haplotype : Fin 3) : ℝ :=
  ![0, 1, -10] haplotype

/-- The true marginal effect of the witness is `600399/4000000`, positive and below one. -/
theorem curseWitness_marginalWeights :
    marginalWeights curseWitnessLaw curseWitnessGenotype curseWitnessOutcome ()
      = 600399 / 4000000 := by
  simp [marginalWeights, FiniteReportLaw.covariance_eq_rawMoments, FiniteReportLaw.expectation,
    Fin.sum_univ_three, curseWitnessLaw, curseWitnessGenotype, curseWitnessOutcome] <;> norm_num

/-- At threshold one the population thresholded weight of the witness is zero. -/
theorem curseWitness_populationThresholdWeights :
    populationThresholdWeights curseWitnessLaw 1 curseWitnessGenotype curseWitnessOutcome = 0 := by
  funext marker
  cases marker
  simp only [populationThresholdWeights, curseWitness_marginalWeights, Pi.zero_apply]
  norm_num [le_abs']

/-- **Two-sided selection can reverse the sign.**  On the witness law, with a cohort of two and
threshold one, selection has positive probability while the expected selected weight is negative,
although the true effect is positive. -/
theorem curseWitness_selection :
    0 < (cohortLaw curseWitnessLaw 2).expectation (fun sample ↦
        if (1 : ℝ) ≤ |gwasWeights curseWitnessGenotype curseWitnessOutcome sample ()| then 1 else 0)
      ∧ (cohortLaw curseWitnessLaw 2).expectation (fun sample ↦
        covarianceThresholdWeights 1 curseWitnessGenotype curseWitnessOutcome sample ()) < 0 := by
  constructor
  · rw [expectation_cohortLaw_two_eq_sum]
    simp [Fin.sum_univ_three, gwasWeights, sampleCovariance_two, curseWitnessLaw,
      curseWitnessGenotype, curseWitnessOutcome, le_abs'] <;> norm_num [le_abs']
  · rw [expectation_cohortLaw_two_eq_sum]
    simp [Fin.sum_univ_three, covarianceThresholdWeights, gwasWeights, sampleCovariance_two,
      curseWitnessLaw, curseWitnessGenotype, curseWitnessOutcome, le_abs'] <;> norm_num [le_abs']

/-- The thresholded weight of the witness has a positive second moment over a cohort of two. -/
theorem curseWitness_secondMoment :
    0 < (cohortLaw curseWitnessLaw 2).expectation (fun sample ↦
      covarianceThresholdWeights 1 curseWitnessGenotype curseWitnessOutcome sample default
        * covarianceThresholdWeights 1 curseWitnessGenotype curseWitnessOutcome sample
          default) := by
  rw [expectation_cohortLaw_two_eq_sum]
  simp [Fin.sum_univ_three, covarianceThresholdWeights, gwasWeights, sampleCovariance_two,
    curseWitnessLaw, curseWitnessGenotype, curseWitnessOutcome, le_abs'] <;> norm_num [le_abs']

/-- **Thresholded training differs from the population thresholded law.**  On the witness law, at
threshold one, the population thresholded score has accuracy zero, and the score thresholded on a
training cohort of two, deployed in the same law, has positive accuracy. -/
theorem curseWitness_accuracy :
    correlationNumerator curseWitnessLaw (linearScore curseWitnessGenotype
          (populationThresholdWeights curseWitnessLaw 1 curseWitnessGenotype curseWitnessOutcome))
          curseWitnessOutcome
        / correlationDenominator curseWitnessLaw (linearScore curseWitnessGenotype
          (populationThresholdWeights curseWitnessLaw 1 curseWitnessGenotype curseWitnessOutcome))
          curseWitnessOutcome = 0
      ∧ 0 < thresholdedAccuracy curseWitnessLaw curseWitnessLaw 2 1 curseWitnessGenotype
          curseWitnessOutcome := by
  constructor
  · rw [curseWitness_populationThresholdWeights, correlationNumerator, covariance_linearScore]
    simp
  · rw [thresholdedAccuracy,
      learnedAccuracy_unique _ _ _ _ _ _ curseWitness_secondMoment.ne']
    have hcovariance : curseWitnessLaw.covariance
        (fun individual ↦ curseWitnessGenotype individual default) curseWitnessOutcome
        = 600399 / 4000000 :=
      curseWitness_marginalWeights
    rw [correlationNumerator, hcovariance]
    refine div_pos (by norm_num) ?_
    simp [correlationDenominator, FiniteReportLaw.variance_eq_rawMoments,
      FiniteReportLaw.expectation, Fin.sum_univ_three, curseWitnessLaw, curseWitnessGenotype,
      curseWitnessOutcome] <;> norm_num

/-! ## Learned scores along a demographic history -/

section History

variable {Deme Locus : Type*} {Allele : Locus → Type*}
variable [Fintype Deme] [DecidableEq Deme] [Fintype Locus] [DecidableEq Locus]
  [∀ ℓ, Fintype (Allele ℓ)] [∀ ℓ, DecidableEq (Allele ℓ)]
variable {J : Type*} [Fintype J]

/-- **The learned accumulator polynomial**: the acceptance polynomials of the products of learned
weights over a panel of `size` draws from the source deme, read against a target matrix of
polynomials. -/
def learnedPolynomial (source target : Deme) (size : ℕ)
    (learn : (Fin size → FullHaplotype Locus Allele) → J → ℝ)
    (targetMatrix : J → J → MvPolynomial (FullHaplotype Locus Allele) ℝ) :
    FrequencyPolynomial Deme Locus Allele :=
  ∑ i, ∑ j, demePolynomial target (targetMatrix i j)
    * acceptancePolynomial (fun _ : Fin size ↦ source)
      fun sample ↦ learn sample i * learn sample j

/-- At a state, the learned polynomial reads the target matrix at the target deme's law against the
cohort second moments of the learned weights in the source deme. -/
theorem polynomialFunction_learnedPolynomial (source target : Deme) (size : ℕ)
    (learn : (Fin size → FullHaplotype Locus Allele) → J → ℝ)
    (targetMatrix : J → J → MvPolynomial (FullHaplotype Locus Allele) ℝ)
    (y : FrequencyState Deme Locus Allele) :
    polynomialFunction (learnedPolynomial source target size learn targetMatrix) y
      = ∑ i, ∑ j, eval (stateLaw y target).mass (targetMatrix i j)
          * (cohortLaw (stateLaw y source) size).expectation
            (fun sample ↦ learn sample i * learn sample j) := by
  rw [polynomialFunction_apply, learnedPolynomial]
  simp only [map_sum, map_mul]
  refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
  rw [eval_demePolynomial, ← polynomialFunction_apply, polynomialFunction_acceptancePolynomial]
  rfl

/-- **The learned polynomial has total degree at most `size + 4`** when the target matrix has
degree at most four. -/
theorem totalDegree_learnedPolynomial_le (source target : Deme) (size : ℕ)
    (learn : (Fin size → FullHaplotype Locus Allele) → J → ℝ)
    (targetMatrix : J → J → MvPolynomial (FullHaplotype Locus Allele) ℝ)
    (htarget : ∀ i j, (targetMatrix i j).totalDegree ≤ 4) :
    (learnedPolynomial source target size learn targetMatrix).totalDegree ≤ size + 4 := by
  refine (totalDegree_finset_sum _ _).trans (Finset.sup_le fun i _ ↦ ?_)
  refine (totalDegree_finset_sum _ _).trans (Finset.sup_le fun j _ ↦ ?_)
  have htargetDeme : (demePolynomial target (targetMatrix i j)).totalDegree ≤ 4 :=
    (totalDegree_rename_le _ _).trans (htarget i j)
  have hpanel := totalDegree_acceptancePolynomial_le (fun _ : Fin size ↦ source)
    fun sample : Fin size → FullHaplotype Locus Allele ↦ learn sample i * learn sample j
  rw [Fintype.card_fin] at hpanel
  exact (totalDegree_mul _ _).trans (by omega)

/-- At a state, the learned numerator is the learned polynomial of the numerator matrix. -/
theorem learnedNumerator_stateLaw (source target : Deme) (size : ℕ)
    (learn : (Fin size → FullHaplotype Locus Allele) → J → ℝ)
    (genotype : FullHaplotype Locus Allele → J → ℝ) (outcome : FullHaplotype Locus Allele → ℝ)
    (y : FrequencyState Deme Locus Allele) :
    learnedNumerator (stateLaw y source) (stateLaw y target) size learn genotype outcome
      = polynomialFunction (learnedPolynomial source target size learn
          (numeratorMatrixPolynomial genotype outcome)) y := by
  rw [learnedNumerator_eq, polynomialFunction_learnedPolynomial]
  simp only [eval_numeratorMatrixPolynomial]

/-- At a state, the learned denominator is the learned polynomial of the denominator matrix. -/
theorem learnedDenominator_stateLaw (source target : Deme) (size : ℕ)
    (learn : (Fin size → FullHaplotype Locus Allele) → J → ℝ)
    (genotype : FullHaplotype Locus Allele → J → ℝ) (outcome : FullHaplotype Locus Allele → ℝ)
    (y : FrequencyState Deme Locus Allele) :
    learnedDenominator (stateLaw y source) (stateLaw y target) size learn genotype outcome
      = polynomialFunction (learnedPolynomial source target size learn
          (denominatorMatrixPolynomial genotype outcome)) y := by
  rw [learnedDenominator_eq, polynomialFunction_learnedPolynomial]
  simp only [eval_denominatorMatrixPolynomial]

/-- **The expected learned numerator along a history** is a budget-`(size + 4)` pairing. -/
theorem integral_learnedNumerator_historyEventKernel (ℓ₀ : Locus)
    (hap₀ : FullHaplotype Locus Allele)
    (events : List ((NeutralRates Deme Locus Allele × ℝ≥0) ⊕ PulseMatrix Deme))
    (x0 : FrequencyState Deme Locus Allele) (source target : Deme) (size : ℕ)
    (learn : (Fin size → FullHaplotype Locus Allele) → J → ℝ)
    (genotype : FullHaplotype Locus Allele → J → ℝ) (outcome : FullHaplotype Locus Allele → ℝ) :
    ∫ y, learnedNumerator (stateLaw y source) (stateLaw y target) size learn genotype outcome
        ∂(historyEventKernel ℓ₀ hap₀ events x0)
      = budgetCoefficients ℓ₀ (fun _ ↦ size + 4)
          (learnedPolynomial source target size learn (numeratorMatrixPolynomial genotype outcome))
        ⬝ᵥ (historyEventPropagator (fun _ ↦ size + 4) events
          *ᵥ budgetMomentFeature (fun _ ↦ size + 4) x0) :=
  integral_historyEventKernel_of_totalDegree_le ℓ₀ hap₀ events x0 _
    (totalDegree_learnedPolynomial_le source target size learn _
      (totalDegree_numeratorMatrixPolynomial_le genotype outcome)) _
    fun y ↦ (learnedNumerator_stateLaw source target size learn genotype outcome y).symm

/-- **The expected learned denominator along a history** is a budget-`(size + 4)` pairing. -/
theorem integral_learnedDenominator_historyEventKernel (ℓ₀ : Locus)
    (hap₀ : FullHaplotype Locus Allele)
    (events : List ((NeutralRates Deme Locus Allele × ℝ≥0) ⊕ PulseMatrix Deme))
    (x0 : FrequencyState Deme Locus Allele) (source target : Deme) (size : ℕ)
    (learn : (Fin size → FullHaplotype Locus Allele) → J → ℝ)
    (genotype : FullHaplotype Locus Allele → J → ℝ) (outcome : FullHaplotype Locus Allele → ℝ) :
    ∫ y, learnedDenominator (stateLaw y source) (stateLaw y target) size learn genotype outcome
        ∂(historyEventKernel ℓ₀ hap₀ events x0)
      = budgetCoefficients ℓ₀ (fun _ ↦ size + 4)
          (learnedPolynomial source target size learn
            (denominatorMatrixPolynomial genotype outcome))
        ⬝ᵥ (historyEventPropagator (fun _ ↦ size + 4) events
          *ᵥ budgetMomentFeature (fun _ ↦ size + 4) x0) :=
  integral_historyEventKernel_of_totalDegree_le ℓ₀ hap₀ events x0 _
    (totalDegree_learnedPolynomial_le source target size learn _
      (totalDegree_denominatorMatrixPolynomial_le genotype outcome)) _
    fun y ↦ (learnedDenominator_stateLaw source target size learn genotype outcome y).symm

/-- **The expected learned numerator along a rate history** is a budget-`(size + 4)` pairing. -/
theorem integral_learnedNumerator_rateHistoryKernel {rates : ℝ → NeutralRates Deme Locus Allele}
    {T : ℝ} (hT : 0 ≤ T)
    (hcontinuous : ∀ capacity : Locus → ℕ,
      ContinuousOn (fun t ↦ dualGenerator (rates t) capacity) (Set.Icc 0 T))
    (ℓ₀ : Locus) (hap₀ : FullHaplotype Locus Allele) (x0 : FrequencyState Deme Locus Allele)
    (source target : Deme) (size : ℕ) (learn : (Fin size → FullHaplotype Locus Allele) → J → ℝ)
    (genotype : FullHaplotype Locus Allele → J → ℝ) (outcome : FullHaplotype Locus Allele → ℝ) :
    ∫ y, learnedNumerator (stateLaw y source) (stateLaw y target) size learn genotype outcome
        ∂(rateHistoryKernel rates ℓ₀ hap₀ hT hcontinuous x0)
      = budgetCoefficients ℓ₀ (fun _ ↦ size + 4)
          (learnedPolynomial source target size learn (numeratorMatrixPolynomial genotype outcome))
        ⬝ᵥ (rateHistoryDualPropagator rates (fun _ ↦ size + 4) T
          *ᵥ budgetMomentFeature (fun _ ↦ size + 4) x0) :=
  integral_rateHistoryKernel_of_totalDegree_le hT hcontinuous ℓ₀ hap₀ x0 _
    (totalDegree_learnedPolynomial_le source target size learn _
      (totalDegree_numeratorMatrixPolynomial_le genotype outcome)) _
    fun y ↦ (learnedNumerator_stateLaw source target size learn genotype outcome y).symm

/-- **The expected learned denominator along a rate history** is a budget-`(size + 4)`
pairing. -/
theorem integral_learnedDenominator_rateHistoryKernel
    {rates : ℝ → NeutralRates Deme Locus Allele} {T : ℝ} (hT : 0 ≤ T)
    (hcontinuous : ∀ capacity : Locus → ℕ,
      ContinuousOn (fun t ↦ dualGenerator (rates t) capacity) (Set.Icc 0 T))
    (ℓ₀ : Locus) (hap₀ : FullHaplotype Locus Allele) (x0 : FrequencyState Deme Locus Allele)
    (source target : Deme) (size : ℕ) (learn : (Fin size → FullHaplotype Locus Allele) → J → ℝ)
    (genotype : FullHaplotype Locus Allele → J → ℝ) (outcome : FullHaplotype Locus Allele → ℝ) :
    ∫ y, learnedDenominator (stateLaw y source) (stateLaw y target) size learn genotype outcome
        ∂(rateHistoryKernel rates ℓ₀ hap₀ hT hcontinuous x0)
      = budgetCoefficients ℓ₀ (fun _ ↦ size + 4)
          (learnedPolynomial source target size learn
            (denominatorMatrixPolynomial genotype outcome))
        ⬝ᵥ (rateHistoryDualPropagator rates (fun _ ↦ size + 4) T
          *ᵥ budgetMomentFeature (fun _ ↦ size + 4) x0) :=
  integral_rateHistoryKernel_of_totalDegree_le hT hcontinuous ℓ₀ hap₀ x0 _
    (totalDegree_learnedPolynomial_le source target size learn _
      (totalDegree_denominatorMatrixPolynomial_le genotype outcome)) _
    fun y ↦ (learnedDenominator_stateLaw source target size learn genotype outcome y).symm

/-- **The expected learned accuracy of a kernel**: the expected target numerator of the learned
score over its expected target denominator, over the populations of the kernel and the training
cohort drawn in the source deme of each.  NOTE2 §6.2 query: a ratio of expectations. -/
def expectedLearnedAccuracy
    (κ : Kernel (FrequencyState Deme Locus Allele) (FrequencyState Deme Locus Allele))
    (x0 : FrequencyState Deme Locus Allele) (source target : Deme) (size : ℕ)
    (learn : (Fin size → FullHaplotype Locus Allele) → J → ℝ)
    (genotype : FullHaplotype Locus Allele → J → ℝ) (outcome : FullHaplotype Locus Allele → ℝ) :
    ℝ :=
  (∫ y, learnedNumerator (stateLaw y source) (stateLaw y target) size learn genotype outcome
      ∂(κ x0))
    / ∫ y, learnedDenominator (stateLaw y source) (stateLaw y target) size learn genotype outcome
        ∂(κ x0)

/-- **The rational learned accuracy** of a budget-`(size + 4)` moment vector. -/
def momentLearnedAccuracy (ℓ₀ : Locus) (source target : Deme) (size : ℕ)
    (learn : (Fin size → FullHaplotype Locus Allele) → J → ℝ)
    (genotype : FullHaplotype Locus Allele → J → ℝ) (outcome : FullHaplotype Locus Allele → ℝ)
    (v : BudgetConfiguration Deme Locus Allele (fun _ ↦ size + 4) → ℝ) : ℝ :=
  (budgetCoefficients ℓ₀ (fun _ ↦ size + 4)
      (learnedPolynomial source target size learn (numeratorMatrixPolynomial genotype outcome))
    ⬝ᵥ v)
    / (budgetCoefficients ℓ₀ (fun _ ↦ size + 4)
        (learnedPolynomial source target size learn (denominatorMatrixPolynomial genotype outcome))
      ⬝ᵥ v)

/-- **The end-to-end law of learned and thresholded scores along a history of epochs, splits and
pulses.**  The expected accuracy of a score learned on a cohort of `size` haplotypes of the source
deme, the covariance-thresholded GWAS included, is the rational function `momentLearnedAccuracy` of
the chronological propagator applied to the budget-`(size + 4)` moments of the initial state. -/
theorem expectedLearnedAccuracy_historyEventKernel (ℓ₀ : Locus)
    (hap₀ : FullHaplotype Locus Allele)
    (events : List ((NeutralRates Deme Locus Allele × ℝ≥0) ⊕ PulseMatrix Deme))
    (x0 : FrequencyState Deme Locus Allele) (source target : Deme) (size : ℕ)
    (learn : (Fin size → FullHaplotype Locus Allele) → J → ℝ)
    (genotype : FullHaplotype Locus Allele → J → ℝ) (outcome : FullHaplotype Locus Allele → ℝ) :
    expectedLearnedAccuracy (historyEventKernel ℓ₀ hap₀ events) x0 source target size learn
        genotype outcome
      = momentLearnedAccuracy ℓ₀ source target size learn genotype outcome
          (historyEventPropagator (fun _ ↦ size + 4) events
            *ᵥ budgetMomentFeature (fun _ ↦ size + 4) x0) := by
  rw [expectedLearnedAccuracy, integral_learnedNumerator_historyEventKernel,
    integral_learnedDenominator_historyEventKernel]
  rfl

/-- **The end-to-end law of learned and thresholded scores along a rate history.** -/
theorem expectedLearnedAccuracy_rateHistoryKernel {rates : ℝ → NeutralRates Deme Locus Allele}
    {T : ℝ} (hT : 0 ≤ T)
    (hcontinuous : ∀ capacity : Locus → ℕ,
      ContinuousOn (fun t ↦ dualGenerator (rates t) capacity) (Set.Icc 0 T))
    (ℓ₀ : Locus) (hap₀ : FullHaplotype Locus Allele) (x0 : FrequencyState Deme Locus Allele)
    (source target : Deme) (size : ℕ) (learn : (Fin size → FullHaplotype Locus Allele) → J → ℝ)
    (genotype : FullHaplotype Locus Allele → J → ℝ) (outcome : FullHaplotype Locus Allele → ℝ) :
    expectedLearnedAccuracy (rateHistoryKernel rates ℓ₀ hap₀ hT hcontinuous) x0 source target size
        learn genotype outcome
      = momentLearnedAccuracy ℓ₀ source target size learn genotype outcome
          (rateHistoryDualPropagator rates (fun _ ↦ size + 4) T
            *ᵥ budgetMomentFeature (fun _ ↦ size + 4) x0) := by
  rw [expectedLearnedAccuracy, integral_learnedNumerator_rateHistoryKernel,
    integral_learnedDenominator_rateHistoryKernel]
  rfl

/-- **Learned accuracy sees the history only through finitely many moments.**  Two histories, from
two initial states, whose propagated budget-`(size + 4)` moments agree give equal expected learned
accuracy for every learner on cohorts of that size, thresholded GWAS scores included, and every tag
set, outcome, source and target. -/
theorem expectedLearnedAccuracy_eq_of_moments_eq (ℓ₀ : Locus) (hap₀ : FullHaplotype Locus Allele)
    {first second : List ((NeutralRates Deme Locus Allele × ℝ≥0) ⊕ PulseMatrix Deme)}
    {x₁ x₂ : FrequencyState Deme Locus Allele} {size : ℕ}
    (hmoments : historyEventPropagator (fun _ ↦ size + 4) first
        *ᵥ budgetMomentFeature (fun _ ↦ size + 4) x₁
      = historyEventPropagator (fun _ ↦ size + 4) second
        *ᵥ budgetMomentFeature (fun _ ↦ size + 4) x₂)
    (source target : Deme) (learn : (Fin size → FullHaplotype Locus Allele) → J → ℝ)
    (genotype : FullHaplotype Locus Allele → J → ℝ) (outcome : FullHaplotype Locus Allele → ℝ) :
    expectedLearnedAccuracy (historyEventKernel ℓ₀ hap₀ first) x₁ source target size learn genotype
        outcome
      = expectedLearnedAccuracy (historyEventKernel ℓ₀ hap₀ second) x₂ source target size learn
          genotype outcome := by
  rw [expectedLearnedAccuracy_historyEventKernel, expectedLearnedAccuracy_historyEventKernel,
    hmoments]

end History

end

end Descent.Portability.EndToEndGWASThresholdLaw
