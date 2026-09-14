/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.EndToEndGWASCalibrationLaw
import Descent.Portability.EndToEndGWASThresholdLaw

assert_below Descent.Decision Descent.Program

/-!
# The calibration of a score learned and thresholded on its own training cohort

`EndToEndGWASThresholdLaw` gives the exact accuracy of any score learned from a training cohort,
the covariance-thresholded GWAS included, and the winner's curse that thresholding carries.
`EndToEndGWASCalibrationLaw` gives the calibration of the unthresholded GWAS score.  This module
gives the calibration of every learned score.

The exact law.  A learner `learn` is any statistic of a training cohort of `n` individuals drawn
from the source law.  For the learned score `S_l = ∑ l_j X_j` deployed in a target law:
* the expected target covariance with the outcome reads the first moments of the learned weights
  against the target marginal effects, `E C_t(S_l, Y) = ∑ c_j E l_j` (`learnedCovariance_eq`);
* the expected target score variance and the expected intercept accumulator read the second-moment
  matrix of the learned weights against the target tag covariance and the target intercept matrix
  (`learnedVariance_eq`, `learnedInterceptAccumulator_eq`).
So the calibration slope and intercept of expectations have an exact law for every learner
(`learnedCalibrationSlope`, `learnedCalibrationIntercept`).  The GWAS is the learner `gwasWeights`
(`trainedCalibrationSlope_eq_learnedCalibrationSlope`).

Attenuation towards the mean weights.  The expected covariance is the target covariance of the
score whose weights are the mean learned weights.  The expected variance is that score's target
variance plus the tag covariance read against the covariance matrix of the learned weights, a
nonnegative noise form (`learnedCovariance_eq_mean`, `learnedVariance_eq_add`,
`learnedNoiseForm_nonneg`).  So every learned slope is the slope of the mean-weight score times a
factor in `[0, 1]`, and its magnitude is at most that slope's (`learnedCalibrationSlope_eq_mul`,
`abs_learnedCalibrationSlope_le`).

The winner's curse on calibration.
* The curse bound `|w| P(sel) ≤ E|ŵ_t|` of `abs_marginalWeights_mul_le_expectation_abs` and the
  nonnegative square `E(|ŵ_t| − |w| 1{sel})²` give `|w| |E ŵ_t| ≤ E ŵ_t²` for every cohort size,
  threshold and tag (`abs_marginalWeights_mul_abs_expectation_le`).
* Hence with one tag, at every threshold, the magnitude of the thresholded slope is at most the
  magnitude of the population slope of the marginal score
  (`abs_learnedCalibrationSlope_threshold_le`).  Selection on the training cohort never sharpens
  calibration beyond the population.
* The sign can reverse.  On the three-haplotype law of `curseWitness_selection`, trained and
  deployed in that law with a cohort of two at threshold one, the thresholded slope is negative,
  while the unthresholded trained slope is positive and below the population slope
  (`curseWitness_calibration`).  Thresholding pushes the slope below the attenuated slope and past
  zero.

Along a history.  At a state the moments of a learner are acceptance polynomials of degree at most
`n` in the source frequencies.  The covariance reads the first moments against the degree-2 target
marginal effects, the variance reads the second moments against the degree-2 tag covariance, and
the intercept against the degree-3 intercept matrix (`learnedCovariancePolynomial`,
`totalDegree_learnedPolynomial_le_add`).  So along epochs, splits and pulses, or along a rate
history, the learned slope of expectations is a rational function of the propagated
budget-`(n + 2)` moments, and the intercept of the budget-`(n + 3)` moments
(`expectedLearnedCalibrationSlope_historyEventKernel`,
`expectedLearnedCalibrationIntercept_historyEventKernel`, and the `rateHistoryKernel` forms).  Equal
propagated moments give equal slope and intercept for every learner on cohorts of that size
(`expectedLearnedCalibrationSlope_eq_of_moments_eq`,
`expectedLearnedCalibrationIntercept_eq_of_moments_eq`).  Both budgets are below the budget
`n + 4` of accuracy, whose numerator reads the second moments against the degree-4 product
`16 c_i c_j`.

Significance.  Clumping and thresholding decides calibration as exactly as accuracy, at a smaller
moment budget, and the winner's curse bounds the slope it can reach: never beyond the population
slope in magnitude, and not always of the right sign.

Scope.  Haploid individuals, one training cohort, the ratio-of-expectations query, and outcomes that
are functions of the individual.  The curse bound on the slope is for one tag; with several tags
the selected weights of different tags interact through the tag covariance and no general bound is
stated.  The budgets are upper bounds from the degree count.

## Empirical status

None.  The bodies here are finite sums over independent product laws, order facts about them, and
integrals of polynomials against Markov kernels, so no measurement can bear on them.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.EndToEndGWASThresholdCalibration

open MeasureTheory ProbabilityTheory MvPolynomial Descent.Coalescent PartialHaplotypeCarrier
  PartialHaplotypeDualGenerator PartialHaplotypeDualSemigroup NeutralFellerGenerator
  NeutralPolynomialSemigroup PartialHaplotypeMicroscopicApproximation PartialHaplotypePulseKernel
  NeutralPulseHistoryKernel NeutralRateHistoryRealization NeutralRateHistoryKernel
  ReplicaMetricInstances EndToEndPortabilityLaw EndToEndDiploidHistoryLaw EndToEndAscertainedLaw
  TrainingNoiseAccuracy FourCellCohortLaw EndToEndGWASTrainingLaw EndToEndGWASTrainingHistory
  EndToEndGWASThresholdLaw EndToEndGWASCalibrationLaw
open scoped Matrix NNReal

noncomputable section

/-! ## The calibration of learned scores -/

section Learned

variable {Ω : Type*} [Fintype Ω] {J : Type*} [Fintype J]

/-- **The expected target score–outcome covariance of a learned score.**  The weights are any
statistic `learn` of a training cohort of `size` individuals from the source law. -/
def learnedCovariance (source target : FiniteReportLaw Ω) (size : ℕ)
    (learn : (Fin size → Ω) → J → ℝ) (genotype : Ω → J → ℝ) (outcome : Ω → ℝ) : ℝ :=
  (cohortLaw source size).expectation fun sample ↦
    target.covariance (linearScore genotype (learn sample)) outcome

/-- **The expected target score variance of a learned score.** -/
def learnedVariance (source target : FiniteReportLaw Ω) (size : ℕ)
    (learn : (Fin size → Ω) → J → ℝ) (genotype : Ω → J → ℝ) : ℝ :=
  (cohortLaw source size).expectation fun sample ↦
    target.variance (linearScore genotype (learn sample))

/-- **The expected target intercept accumulator of a learned score**,
`E[μ_t(Y) V_t(S_l) − C_t(S_l, Y) μ_t(S_l)]` over the training cohort. -/
def learnedInterceptAccumulator (source target : FiniteReportLaw Ω) (size : ℕ)
    (learn : (Fin size → Ω) → J → ℝ) (genotype : Ω → J → ℝ) (outcome : Ω → ℝ) : ℝ :=
  (cohortLaw source size).expectation fun sample ↦
    target.expectation outcome * target.variance (linearScore genotype (learn sample))
      - target.covariance (linearScore genotype (learn sample)) outcome
        * target.expectation (linearScore genotype (learn sample))

/-- **The learned calibration slope**: the expected target covariance of the learned score with
the outcome over its expected target variance.  NOTE2 §6.2 query: a ratio of expectations. -/
def learnedCalibrationSlope (source target : FiniteReportLaw Ω) (size : ℕ)
    (learn : (Fin size → Ω) → J → ℝ) (genotype : Ω → J → ℝ) (outcome : Ω → ℝ) : ℝ :=
  learnedCovariance source target size learn genotype outcome
    / learnedVariance source target size learn genotype

/-- **The learned calibration intercept**: the expected intercept accumulator over the expected
target score variance.  NOTE2 §6.2 query: a ratio of expectations. -/
def learnedCalibrationIntercept (source target : FiniteReportLaw Ω) (size : ℕ)
    (learn : (Fin size → Ω) → J → ℝ) (genotype : Ω → J → ℝ) (outcome : Ω → ℝ) : ℝ :=
  learnedInterceptAccumulator source target size learn genotype outcome
    / learnedVariance source target size learn genotype

/-- **The mean learned weights**: the expectation of each learned weight over the training
cohort. -/
def meanLearnedWeights (source : FiniteReportLaw Ω) (size : ℕ)
    (learn : (Fin size → Ω) → J → ℝ) : J → ℝ :=
  fun marker ↦ (cohortLaw source size).expectation fun sample ↦ learn sample marker

/-- **The covariance matrix of the learned weights** over the training cohort. -/
def learnedWeightCovariance (source : FiniteReportLaw Ω) (size : ℕ)
    (learn : (Fin size → Ω) → J → ℝ) (i j : J) : ℝ :=
  (cohortLaw source size).covariance (fun sample ↦ learn sample i) fun sample ↦ learn sample j

/-- **The learned noise form**: the covariance matrix of the learned weights read against the
target tag covariance. -/
def learnedNoiseForm (source target : FiniteReportLaw Ω) (size : ℕ)
    (learn : (Fin size → Ω) → J → ℝ) (genotype : Ω → J → ℝ) : ℝ :=
  ∑ i, ∑ j, tagCovariance target genotype i j * learnedWeightCovariance source size learn i j

/-- **The expected covariance reads the first moments of the learned weights** against the target
marginal effects. -/
theorem learnedCovariance_eq (source target : FiniteReportLaw Ω) (size : ℕ)
    (learn : (Fin size → Ω) → J → ℝ) (genotype : Ω → J → ℝ) (outcome : Ω → ℝ) :
    learnedCovariance source target size learn genotype outcome
      = ∑ j, marginalWeights target genotype outcome j
          * (cohortLaw source size).expectation (fun sample ↦ learn sample j) := by
  rw [learnedCovariance]
  simp only [covariance_linearScore]
  rw [FiniteIndependentMoments.expectation_sum]
  refine Finset.sum_congr rfl fun marker _ ↦ ?_
  have hswap : (fun sample : Fin size → Ω ↦ learn sample marker
      * target.covariance (fun individual ↦ genotype individual marker) outcome)
      = fun sample ↦ target.covariance (fun individual ↦ genotype individual marker) outcome
        * learn sample marker :=
    funext fun _ ↦ mul_comm _ _
  rw [hswap, expectation_const_mul_observable]
  rfl

/-- **The expected variance reads the second moments of the learned weights** against the target
tag covariance. -/
theorem learnedVariance_eq (source target : FiniteReportLaw Ω) (size : ℕ)
    (learn : (Fin size → Ω) → J → ℝ) (genotype : Ω → J → ℝ) :
    learnedVariance source target size learn genotype
      = ∑ i, ∑ j, tagCovariance target genotype i j
          * (cohortLaw source size).expectation (fun sample ↦ learn sample i * learn sample j) := by
  rw [learnedVariance]
  simp only [variance_linearScore_eq]
  rw [FiniteIndependentMoments.expectation_sum]
  simp only [FiniteIndependentMoments.expectation_sum, expectation_const_mul_observable]

/-- **The expected intercept accumulator reads the second moments of the learned weights** against
the target intercept matrix. -/
theorem learnedInterceptAccumulator_eq (source target : FiniteReportLaw Ω) (size : ℕ)
    (learn : (Fin size → Ω) → J → ℝ) (genotype : Ω → J → ℝ) (outcome : Ω → ℝ) :
    learnedInterceptAccumulator source target size learn genotype outcome
      = ∑ i, ∑ j, interceptMatrix target genotype outcome i j
          * (cohortLaw source size).expectation (fun sample ↦ learn sample i * learn sample j) := by
  rw [learnedInterceptAccumulator]
  simp only [interceptAccumulator_linearScore_eq]
  rw [FiniteIndependentMoments.expectation_sum]
  simp only [FiniteIndependentMoments.expectation_sum, expectation_const_mul_observable]

/-- The trained calibration slope of the marginal-effect GWAS is the learned calibration slope of
the learner `gwasWeights`. -/
theorem trainedCalibrationSlope_eq_learnedCalibrationSlope (source target : FiniteReportLaw Ω)
    (size : ℕ) (genotype : Ω → J → ℝ) (outcome : Ω → ℝ) :
    trainedCalibrationSlope source target size genotype outcome
      = learnedCalibrationSlope source target size (gwasWeights genotype outcome) genotype
          outcome :=
  rfl

/-! ## Attenuation towards the mean learned weights -/

/-- **The expected covariance is the covariance of the mean-weight score.** -/
theorem learnedCovariance_eq_mean (source target : FiniteReportLaw Ω) (size : ℕ)
    (learn : (Fin size → Ω) → J → ℝ) (genotype : Ω → J → ℝ) (outcome : Ω → ℝ) :
    learnedCovariance source target size learn genotype outcome
      = target.covariance (linearScore genotype (meanLearnedWeights source size learn))
          outcome := by
  rw [learnedCovariance_eq, covariance_linearScore]
  exact Finset.sum_congr rfl fun marker _ ↦ mul_comm _ _

/-- **The expected variance is the variance of the mean-weight score plus the noise form.** -/
theorem learnedVariance_eq_add (source target : FiniteReportLaw Ω) (size : ℕ)
    (learn : (Fin size → Ω) → J → ℝ) (genotype : Ω → J → ℝ) :
    learnedVariance source target size learn genotype
      = target.variance (linearScore genotype (meanLearnedWeights source size learn))
        + learnedNoiseForm source target size learn genotype := by
  rw [learnedVariance_eq, variance_linearScore_eq, learnedNoiseForm, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  simp only [meanLearnedWeights, learnedWeightCovariance, FiniteReportLaw.covariance_eq_rawMoments]
  ring

/-- **The noise form is nonnegative**: the covariance matrix of the learned weights is positive
semidefinite, each quadratic form being the cohort variance of a linear statistic of the weights. -/
theorem learnedNoiseForm_nonneg (source target : FiniteReportLaw Ω) (size : ℕ)
    (learn : (Fin size → Ω) → J → ℝ) (genotype : Ω → J → ℝ) :
    0 ≤ learnedNoiseForm source target size learn genotype :=
  sum_tagCovariance_mul_nonneg target genotype _ fun u ↦
    le_of_le_of_eq ((cohortLaw source size).variance_nonneg (linearScore learn u))
      (variance_linearScore (cohortLaw source size) learn u)

/-- A ratio over a sum is the ratio over its first term times that term over the sum, whenever the
first term is nonzero. -/
theorem learnedRatio_eq_mul_attenuation (c : ℝ) {α : ℝ} (hα : α ≠ 0) (τ : ℝ) :
    c / (α + τ) = c / α * (α / (α + τ)) := by
  rw [div_mul_div_comm, mul_comm c α, mul_div_mul_left c _ hα]

/-- **Every learned slope is attenuated towards the slope of its mean weights.**  The learned
calibration slope is the target slope of the score with the mean learned weights times the factor
`α / (α + τ)`, with `α` that score's target variance and `τ` the noise form.  There is no side
condition: where `α = 0` Cauchy–Schwarz forces the covariance to vanish. -/
theorem learnedCalibrationSlope_eq_mul (source target : FiniteReportLaw Ω) (size : ℕ)
    (learn : (Fin size → Ω) → J → ℝ) (genotype : Ω → J → ℝ) (outcome : Ω → ℝ) :
    learnedCalibrationSlope source target size learn genotype outcome
      = target.covariance (linearScore genotype (meanLearnedWeights source size learn)) outcome
          / target.variance (linearScore genotype (meanLearnedWeights source size learn))
        * (target.variance (linearScore genotype (meanLearnedWeights source size learn))
          / (target.variance (linearScore genotype (meanLearnedWeights source size learn))
            + learnedNoiseForm source target size learn genotype)) := by
  rw [learnedCalibrationSlope, learnedCovariance_eq_mean, learnedVariance_eq_add]
  by_cases hzero :
      target.variance (linearScore genotype (meanLearnedWeights source size learn)) = 0
  · have hsquare := target.covariance_sq_le_variance_mul
      (linearScore genotype (meanLearnedWeights source size learn)) outcome
    rw [hzero, zero_mul] at hsquare
    have hcovariance : target.covariance
        (linearScore genotype (meanLearnedWeights source size learn)) outcome = 0 :=
      (pow_eq_zero_iff two_ne_zero).mp (le_antisymm hsquare (sq_nonneg _))
    rw [hcovariance, zero_div, zero_div, zero_mul]
  · exact learnedRatio_eq_mul_attenuation _ hzero _

/-- **No learner sharpens the slope of its mean weights**: the magnitude of the learned slope is at
most the magnitude of the target slope of the mean-weight score. -/
theorem abs_learnedCalibrationSlope_le (source target : FiniteReportLaw Ω) (size : ℕ)
    (learn : (Fin size → Ω) → J → ℝ) (genotype : Ω → J → ℝ) (outcome : Ω → ℝ) :
    |learnedCalibrationSlope source target size learn genotype outcome|
      ≤ |target.covariance (linearScore genotype (meanLearnedWeights source size learn)) outcome
          / target.variance (linearScore genotype (meanLearnedWeights source size learn))| := by
  have hvariance :=
    target.variance_nonneg (linearScore genotype (meanLearnedWeights source size learn))
  have hnoise := learnedNoiseForm_nonneg source target size learn genotype
  have hfactor : |target.variance (linearScore genotype (meanLearnedWeights source size learn))
      / (target.variance (linearScore genotype (meanLearnedWeights source size learn))
        + learnedNoiseForm source target size learn genotype)| ≤ 1 := by
    rw [abs_of_nonneg (div_nonneg hvariance (add_nonneg hvariance hnoise))]
    rcases hvariance.eq_or_lt with hzero | hpositive
    · rw [← hzero, zero_div]
      exact zero_le_one
    · exact (div_le_one (by linarith)).mpr (by linarith)
  rw [learnedCalibrationSlope_eq_mul, abs_mul]
  exact mul_le_of_le_one_right (abs_nonneg _) hfactor

/-! ## The winner's curse on calibration -/

omit [Fintype J] in
/-- **The second moment of a thresholded weight dominates the true effect times its mean.**  For
every cohort size `n ≥ 2`, threshold `t` and tag, `|w_j| |E ŵ_t,j| ≤ E ŵ_t,j²`.  The nonnegative
square `E(|ŵ_t,j| − |w_j| 1{sel})² = E ŵ_t,j² − 2 |w_j| E|ŵ_t,j| + w_j² P(sel)` combines with the
curse bound `|w_j| P(sel) ≤ E|ŵ_t,j|`. -/
theorem abs_marginalWeights_mul_abs_expectation_le (law : FiniteReportLaw Ω) {size : ℕ}
    (hsize : 2 ≤ size) (t : ℝ) (genotype : Ω → J → ℝ) (outcome : Ω → ℝ) (marker : J) :
    |marginalWeights law genotype outcome marker|
        * |(cohortLaw law size).expectation (fun sample ↦
          covarianceThresholdWeights t genotype outcome sample marker)|
      ≤ (cohortLaw law size).expectation fun sample ↦
          covarianceThresholdWeights t genotype outcome sample marker
            * covarianceThresholdWeights t genotype outcome sample marker := by
  have hcurse := abs_marginalWeights_mul_le_expectation_abs law hsize t genotype outcome marker
  have hmean := abs_expectation_le_expectation_abs (cohortLaw law size)
    fun sample ↦ covarianceThresholdWeights t genotype outcome sample marker
  have hsquare : 0 ≤ (cohortLaw law size).expectation fun sample ↦
      (|covarianceThresholdWeights t genotype outcome sample marker|
        - |marginalWeights law genotype outcome marker|
          * if t ≤ |gwasWeights genotype outcome sample marker| then 1 else 0) ^ 2 :=
    ReplicaDomainCertificate.expectation_nonneg _ _ fun _ ↦ sq_nonneg _
  have hexpand : (cohortLaw law size).expectation (fun sample ↦
      (|covarianceThresholdWeights t genotype outcome sample marker|
        - |marginalWeights law genotype outcome marker|
          * if t ≤ |gwasWeights genotype outcome sample marker| then 1 else 0) ^ 2)
      = (cohortLaw law size).expectation (fun sample ↦
          covarianceThresholdWeights t genotype outcome sample marker
            * covarianceThresholdWeights t genotype outcome sample marker)
        - 2 * |marginalWeights law genotype outcome marker|
          * (cohortLaw law size).expectation (fun sample ↦
            |covarianceThresholdWeights t genotype outcome sample marker|)
        + |marginalWeights law genotype outcome marker| ^ 2
          * (cohortLaw law size).expectation (fun sample ↦
            if t ≤ |gwasWeights genotype outcome sample marker| then 1 else 0) := by
    simp only [FiniteReportLaw.expectation, Finset.mul_sum, ← Finset.sum_sub_distrib,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun sample _ ↦ ?_
    simp only [covarianceThresholdWeights]
    split_ifs
    · rw [← abs_mul_abs_self (gwasWeights genotype outcome sample marker)]
      ring
    · simp
  have hsq : |marginalWeights law genotype outcome marker| ^ 2
      * (cohortLaw law size).expectation (fun sample ↦
        if t ≤ |gwasWeights genotype outcome sample marker| then 1 else 0)
      = |marginalWeights law genotype outcome marker|
        * (|marginalWeights law genotype outcome marker|
          * (cohortLaw law size).expectation (fun sample ↦
            if t ≤ |gwasWeights genotype outcome sample marker| then 1 else 0)) := by
    ring
  have hselected := mul_le_mul_of_nonneg_left hcurse
    (abs_nonneg (marginalWeights law genotype outcome marker))
  have hmagnitude := mul_le_mul_of_nonneg_left hmean
    (abs_nonneg (marginalWeights law genotype outcome marker))
  rw [hexpand] at hsquare
  linarith

/-- An algebraic form of the curse on a one-tag slope: a bound `|w| |m| ≤ B` makes the ratio
`c m / (v B)` at most `w c / (v w²)` in magnitude, for nonnegative `v` and `B` and nonzero `w`. -/
theorem abs_div_mul_le_of_curse {c m v B w : ℝ} (hv : 0 ≤ v) (hB : 0 ≤ B) (hw : w ≠ 0)
    (hbound : |w| * |m| ≤ B) : |c * m / (v * B)| ≤ |w * c / (v * (w * w))| := by
  rcases hv.eq_or_lt with hzero | hvpositive
  · rw [← hzero, zero_mul, div_zero, abs_zero]
    exact abs_nonneg _
  rcases hB.eq_or_lt with hzero | hBpositive
  · rw [← hzero, mul_zero, div_zero, abs_zero]
    exact abs_nonneg _
  have hden₁ : 0 < v * B := mul_pos hvpositive hBpositive
  have hden₂ : 0 < v * (w * w) := mul_pos hvpositive (mul_self_pos.mpr hw)
  rw [abs_div, abs_div, abs_of_pos hden₁, abs_of_pos hden₂, abs_mul, abs_mul,
    div_le_div_iff₀ hden₁ hden₂]
  have hproduct := mul_le_mul_of_nonneg_left hbound
    (mul_nonneg (mul_nonneg (abs_nonneg c) (abs_nonneg w)) hvpositive.le)
  calc |c| * |m| * (v * (w * w)) = |c| * |w| * v * (|w| * |m|) := by
        rw [← abs_mul_abs_self w]
        ring
    _ ≤ |c| * |w| * v * B := hproduct
    _ = |w| * |c| * (v * B) := by ring

/-- The expected covariance of a one-tag learned score is the target marginal effect times the
mean learned weight. -/
theorem learnedCovariance_unique [Unique J] (source target : FiniteReportLaw Ω) (size : ℕ)
    (learn : (Fin size → Ω) → J → ℝ) (genotype : Ω → J → ℝ) (outcome : Ω → ℝ) :
    learnedCovariance source target size learn genotype outcome
      = marginalWeights target genotype outcome default
        * (cohortLaw source size).expectation (fun sample ↦ learn sample default) := by
  rw [learnedCovariance_eq]
  simp only [Fintype.sum_unique]

/-- The expected variance of a one-tag learned score is the target tag variance times the second
moment of the learned weight. -/
theorem learnedVariance_unique [Unique J] (source target : FiniteReportLaw Ω) (size : ℕ)
    (learn : (Fin size → Ω) → J → ℝ) (genotype : Ω → J → ℝ) :
    learnedVariance source target size learn genotype
      = tagCovariance target genotype default default
        * (cohortLaw source size).expectation
          (fun sample ↦ learn sample default * learn sample default) := by
  rw [learnedVariance_eq]
  simp only [Fintype.sum_unique]

/-- **Thresholding never sharpens a one-tag slope beyond the population.**  For one tag, every
cohort size `n ≥ 2` and every threshold, the magnitude of the calibration slope of the score
thresholded on its training cohort is at most the magnitude of the population slope of the marginal
score, whenever the true marginal effect is nonzero.  Assumes: the source marginal effect of the
tag is nonzero. -/
theorem abs_learnedCalibrationSlope_threshold_le [Unique J] (source target : FiniteReportLaw Ω)
    {size : ℕ} (hsize : 2 ≤ size) (t : ℝ) (genotype : Ω → J → ℝ) (outcome : Ω → ℝ)
    (hsignal : marginalWeights source genotype outcome default ≠ 0) :
    |learnedCalibrationSlope source target size (covarianceThresholdWeights t genotype outcome)
        genotype outcome|
      ≤ |populationCalibrationSlope source target genotype outcome| := by
  have hbound :=
    abs_marginalWeights_mul_abs_expectation_le source hsize t genotype outcome default
  have hvariance : 0 ≤ tagCovariance target genotype default default :=
    target.variance_nonneg _
  have hsecond : 0 ≤ (cohortLaw source size).expectation (fun sample ↦
      covarianceThresholdWeights t genotype outcome sample default
        * covarianceThresholdWeights t genotype outcome sample default) :=
    ReplicaDomainCertificate.expectation_nonneg _ _ fun _ ↦ mul_self_nonneg _
  rw [learnedCalibrationSlope, learnedCovariance_unique, learnedVariance_unique,
    populationCalibrationSlope, covariance_linearScore, variance_linearScore_eq]
  simp only [Fintype.sum_unique]
  exact abs_div_mul_le_of_curse hvariance hsecond hsignal hbound

end Learned

end

end Descent.Portability.EndToEndGWASThresholdCalibration
