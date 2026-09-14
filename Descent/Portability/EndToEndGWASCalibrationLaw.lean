/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.EndToEndCalibrationLaw
import Descent.Portability.EndToEndGWASTrainingHistory

assert_below Descent.Decision Descent.Program

/-!
# The calibration of a score trained by a finite-sample GWAS

`EndToEndGWASTrainingLaw` gives the exact expected accuracy of the marginal-effect GWAS score
trained on `n` source individuals, and `EndToEndCalibrationLaw` the calibration of a fixed score
along a history.  This module gives the calibration of the trained score `S_ŵ = ∑ ŵ_j X_j` in a
target law: the regression of the outcome on the score, its slope and its intercept, as ratios of
expectations over the training cohort (NOTE2 §6.2 query).

The accumulators.  For `n ≥ 2`, with `w` the source marginal effects and `S_w` the population
marginal score:
* the expected target covariance has no sampling term, `E C_t(S_ŵ, Y) = ∑ w_j C_t(X_j, Y)
  = C_t(S_w, Y)`, because the weights are unbiased (`trainedCovariance_eq`);
* the expected target score variance is the sampling form `α + β / n + γ / (n (n − 1))`, with
  `α = wᵀ Σ_t w = V_t(S_w)` and `β`, `γ` the corpus excess and pairing matrices read against the
  target tag covariance `Σ_t` (`trainedVariance_eq`, `tagCovariance`, `excessForm`,
  `pairingForm`);
* the expected intercept accumulator `E[μ_t(Y) V_t(S_ŵ) − C_t(S_ŵ, Y) μ_t(S_ŵ)]` is a sampling
  form whose population term is the accumulator of `S_w` (`trainedInterceptAccumulator_eq`).
Both noise forms are nonnegative: a positive semidefinite matrix read against a covariance matrix
is a target expectation of a quadratic form (`sum_tagCovariance_mul_nonneg`, `excessForm_nonneg`,
`pairingForm_nonneg`).  The pairing form is at least `α` (`variance_le_pairingForm`).

The attenuation law.  The trained slope is the population slope `C_t(S_w, Y) / α` times the exact
attenuation factor `α / (α + τ_n)`, `τ_n = β / n + γ / (n (n − 1))`, with no side condition
(`trainedCalibrationSlope_eq_mul_attenuationFactor`, `attenuationFactor`).  The factor lies in
`[0, 1]`, rises with `n` and tends to one (`attenuationFactor_nonneg`, `attenuationFactor_le_one`,
`attenuationFactor_monotone`, `tendsto_attenuationFactor`).  Hence the trained slope tends to the
population slope (`tendsto_trainedCalibrationSlope`).  When the population slope is nonnegative the
trained slope is at most it and rises with `n`
(`trainedCalibrationSlope_le_populationCalibrationSlope`, `trainedCalibrationSlope_monotone`).  A
positive population covariance makes the attenuation strict at every finite `n`
(`trainedCalibrationSlope_lt_populationCalibrationSlope`).  The trained intercept tends to the
population intercept (`tendsto_trainedCalibrationIntercept`).  The population slope is the corpus
least-squares slope of `S_w` (`populationCalibrationSlope_eq_getD`).

The contrast with accuracy.  Accuracy is a mediant of population and noise terms and is not
monotone in `n`: finite training can raise it above the population value
(`EndToEndGWASTrainingLaw.populationAccuracy_lt_trainedAccuracy`).  Calibration attenuation is
monotone: finite training only shrinks a nonnegative slope, by a factor that rises to one.  With
one tag the two separate completely.  Training on the uniform law of two biallelic loci and
deploying in the same law leaves the accuracy at its population value for every `n` and strictly
attenuates the slope (`calibrationWitness`).

Along a history.  The trained covariance is a frequency polynomial of degree four.  The population,
excess and pairing forms of the variance have degree six: degree-4 source matrices read against the
degree-2 target tag covariance.  The intercept forms have degree seven, against the degree-3
intercept matrix (`trainedCovariancePolynomial`, `tagCovariancePolynomial`,
`interceptMatrixPolynomial`, `totalDegree_trainedPolynomial_le_add`).  So along epochs, splits and
pulses, or along a rate history, the trained slope of expectations is a rational function of the
propagated budget-6 moments and `n`, and the intercept of the budget-7 moments
(`expectedTrainedCalibrationSlope_historyEventKernel`,
`expectedTrainedCalibrationIntercept_historyEventKernel`, and the `rateHistoryKernel` forms).  Two
histories with equal propagated moments have equal trained slope and intercept for every `n`
(`expectedTrainedCalibrationSlope_eq_of_moments_eq`,
`expectedTrainedCalibrationIntercept_eq_of_moments_eq`).  Both budgets are below the budget eight
of accuracy, whose numerator reads the degree-4 source matrices against the degree-4 target
product `16 c_i c_j`.  Under a kernel with finite moments the attenuation law holds for the ratio
of expectations over populations, with integrated forms
(`expectedTrainedCalibrationSlope_eq_mul_attenuationFactor`,
`expectedTrainedCalibrationSlope_monotone`).

Significance.  A score trained on finitely many individuals is miscalibrated in the target in a
fixed direction and by an exact factor, and demography reaches that factor only through finitely
many moments.

Scope.  One draw per individual from a finite law, the marginal sample covariance with no LD
adjustment and no threshold selected on the cohort, and the ratio-of-expectations query over the
cohort and the history.  The expectation of each cohort's slope is not stated.  The budgets six and
seven are upper bounds from the degree count; that no smaller budget suffices is not proved.

## Empirical status

None.  The bodies here are identities between finite sums over stipulated finite laws, integrals
of polynomials against Markov kernels, and order facts about sampling forms, so no measurement can
bear on them.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.EndToEndGWASCalibrationLaw

open MeasureTheory ProbabilityTheory MvPolynomial Filter Topology Descent.Coalescent
  PartialHaplotypeCarrier PartialHaplotypeDualGenerator PartialHaplotypeDualSemigroup
  NeutralFellerGenerator NeutralPolynomialSemigroup PartialHaplotypeMicroscopicApproximation
  PartialHaplotypePulseKernel NeutralPulseHistoryKernel NeutralRateHistoryRealization
  NeutralRateHistoryKernel ReplicaMetricInstances EndToEndPortabilityLaw EndToEndDiploidHistoryLaw
  TrainingNoiseAccuracy FourCellCohortLaw EndToEndGWASTrainingLaw EndToEndGWASTrainingHistory
open scoped Matrix NNReal

noncomputable section

/-! ## The trained score in a target law -/

section Finite

variable {Ω : Type*} [Fintype Ω] {J : Type*}

/-- **The target tag covariance matrix** `Σ_t(i, j) = C_t(X_i, X_j)`. -/
def tagCovariance (target : FiniteReportLaw Ω) (genotype : Ω → J → ℝ) (i j : J) : ℝ :=
  target.covariance (fun individual ↦ genotype individual i)
    (fun individual ↦ genotype individual j)

/-- **The target intercept matrix** `μ_t(Y) C_t(X_i, X_j) − C_t(X_i, Y) μ_t(X_j)`, whose quadratic
form at a weight vector is the intercept accumulator of the linear score. -/
def interceptMatrix (target : FiniteReportLaw Ω) (genotype : Ω → J → ℝ) (outcome : Ω → ℝ)
    (i j : J) : ℝ :=
  target.expectation outcome * tagCovariance target genotype i j
    - marginalWeights target genotype outcome i
      * target.expectation (fun individual ↦ genotype individual j)

variable [Fintype J]

/-- **The expected target score–outcome covariance of a GWAS score** trained on a cohort of `size`
individuals from the source law. -/
def trainedCovariance (source target : FiniteReportLaw Ω) (size : ℕ) (genotype : Ω → J → ℝ)
    (outcome : Ω → ℝ) : ℝ :=
  (cohortLaw source size).expectation fun sample ↦
    target.covariance (linearScore genotype (gwasWeights genotype outcome sample)) outcome

/-- **The expected target score variance of a GWAS score** trained on a cohort of `size`
individuals from the source law. -/
def trainedVariance (source target : FiniteReportLaw Ω) (size : ℕ) (genotype : Ω → J → ℝ)
    (outcome : Ω → ℝ) : ℝ :=
  (cohortLaw source size).expectation fun sample ↦
    target.variance (linearScore genotype (gwasWeights genotype outcome sample))

/-- **The expected target intercept accumulator of a GWAS score**,
`E[μ_t(Y) V_t(S_ŵ) − C_t(S_ŵ, Y) μ_t(S_ŵ)]` over the training cohort. -/
def trainedInterceptAccumulator (source target : FiniteReportLaw Ω) (size : ℕ)
    (genotype : Ω → J → ℝ) (outcome : Ω → ℝ) : ℝ :=
  (cohortLaw source size).expectation fun sample ↦
    target.expectation outcome
        * target.variance (linearScore genotype (gwasWeights genotype outcome sample))
      - target.covariance (linearScore genotype (gwasWeights genotype outcome sample)) outcome
        * target.expectation (linearScore genotype (gwasWeights genotype outcome sample))

/-- **The trained calibration slope**: the expected target covariance of the GWAS score with the
outcome over its expected target variance.  NOTE2 §6.2 query: a ratio of expectations. -/
def trainedCalibrationSlope (source target : FiniteReportLaw Ω) (size : ℕ)
    (genotype : Ω → J → ℝ) (outcome : Ω → ℝ) : ℝ :=
  trainedCovariance source target size genotype outcome
    / trainedVariance source target size genotype outcome

/-- **The trained calibration intercept**: the expected intercept accumulator over the expected
target score variance.  NOTE2 §6.2 query: a ratio of expectations. -/
def trainedCalibrationIntercept (source target : FiniteReportLaw Ω) (size : ℕ)
    (genotype : Ω → J → ℝ) (outcome : Ω → ℝ) : ℝ :=
  trainedInterceptAccumulator source target size genotype outcome
    / trainedVariance source target size genotype outcome

/-- **The population calibration slope** of the population marginal score `S_w` in the target,
`C_t(S_w, Y) / V_t(S_w)`. -/
def populationCalibrationSlope (source target : FiniteReportLaw Ω) (genotype : Ω → J → ℝ)
    (outcome : Ω → ℝ) : ℝ :=
  target.covariance (linearScore genotype (marginalWeights source genotype outcome)) outcome
    / target.variance (linearScore genotype (marginalWeights source genotype outcome))

/-- **The population calibration intercept** of the population marginal score in the target,
`(μ_t(Y) V_t(S_w) − C_t(S_w, Y) μ_t(S_w)) / V_t(S_w)`. -/
def populationCalibrationIntercept (source target : FiniteReportLaw Ω) (genotype : Ω → J → ℝ)
    (outcome : Ω → ℝ) : ℝ :=
  (target.expectation outcome
        * target.variance (linearScore genotype (marginalWeights source genotype outcome))
      - target.covariance (linearScore genotype (marginalWeights source genotype outcome)) outcome
        * target.expectation (linearScore genotype (marginalWeights source genotype outcome)))
    / target.variance (linearScore genotype (marginalWeights source genotype outcome))

/-- **The excess form** `β = ∑ᵢⱼ Σ_t(i, j) E_ij`: the source excess matrix read against the target
tag covariance. -/
def excessForm (source target : FiniteReportLaw Ω) (genotype : Ω → J → ℝ) (outcome : Ω → ℝ) :
    ℝ :=
  ∑ i, ∑ j, tagCovariance target genotype i j * weightExcess source genotype outcome i j

/-- **The pairing form** `γ = ∑ᵢⱼ Σ_t(i, j) P_ij`: the source pairing matrix read against the
target tag covariance. -/
def pairingForm (source target : FiniteReportLaw Ω) (genotype : Ω → J → ℝ) (outcome : Ω → ℝ) :
    ℝ :=
  ∑ i, ∑ j, tagCovariance target genotype i j * weightPairing source genotype outcome i j

/-- **The population slope is the corpus least-squares slope** of the population marginal score,
read as zero where the score is constant in the target. -/
theorem populationCalibrationSlope_eq_getD (source target : FiniteReportLaw Ω)
    (genotype : Ω → J → ℝ) (outcome : Ω → ℝ) :
    populationCalibrationSlope source target genotype outcome
      = (target.calibrationSlope
          (linearScore genotype (marginalWeights source genotype outcome)) outcome).getD 0 := by
  unfold populationCalibrationSlope FiniteReportLaw.calibrationSlope
  split_ifs with hpositive
  · rfl
  · rw [le_antisymm (not_lt.mp hpositive) (target.variance_nonneg _), div_zero, Option.getD_none]

/-! ## Reading the accumulators as quadratic forms in the weights -/

/-- The target variance of a linear score is the tag covariance read against the weights. -/
theorem variance_linearScore_eq (target : FiniteReportLaw Ω) (genotype : Ω → J → ℝ)
    (weights : J → ℝ) :
    target.variance (linearScore genotype weights)
      = ∑ i, ∑ j, tagCovariance target genotype i j * (weights i * weights j) := by
  rw [variance_linearScore]
  exact Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ mul_comm _ _

/-- The intercept accumulator of a linear score is the intercept matrix read against the
weights. -/
theorem interceptAccumulator_linearScore_eq (target : FiniteReportLaw Ω) (genotype : Ω → J → ℝ)
    (outcome : Ω → ℝ) (weights : J → ℝ) :
    target.expectation outcome * target.variance (linearScore genotype weights)
        - target.covariance (linearScore genotype weights) outcome
          * target.expectation (linearScore genotype weights)
      = ∑ i, ∑ j, interceptMatrix target genotype outcome i j * (weights i * weights j) := by
  rw [variance_linearScore_eq, covariance_linearScore, expectation_linearScore, Finset.mul_sum,
    Finset.sum_mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  simp only [interceptMatrix, marginalWeights]
  ring

/-- **The expected target covariance has no sampling term.**  The GWAS weights are unbiased and
the covariance is linear in them, so `E C_t(S_ŵ, Y) = ∑ w_j C_t(X_j, Y) = C_t(S_w, Y)`. -/
theorem trainedCovariance_eq (source target : FiniteReportLaw Ω) {size : ℕ} (hsize : 2 ≤ size)
    (genotype : Ω → J → ℝ) (outcome : Ω → ℝ) :
    trainedCovariance source target size genotype outcome
      = target.covariance (linearScore genotype (marginalWeights source genotype outcome))
          outcome := by
  simp only [trainedCovariance, covariance_linearScore]
  rw [FiniteIndependentMoments.expectation_sum]
  refine Finset.sum_congr rfl fun marker _ ↦ ?_
  have hswap : (fun sample : Fin size → Ω ↦ gwasWeights genotype outcome sample marker
      * target.covariance (fun individual ↦ genotype individual marker) outcome)
      = fun sample ↦ target.covariance (fun individual ↦ genotype individual marker) outcome
        * gwasWeights genotype outcome sample marker :=
    funext fun sample ↦ mul_comm _ _
  rw [hswap, expectation_const_mul_observable, expectation_gwasWeights _ hsize, mul_comm]

/-- **The expected target score variance is a sampling form**: the target variance of the
population marginal score, plus the excess form over `n`, plus the pairing form over
`n (n − 1)`. -/
theorem trainedVariance_eq (source target : FiniteReportLaw Ω) {size : ℕ} (hsize : 2 ≤ size)
    (genotype : Ω → J → ℝ) (outcome : Ω → ℝ) :
    trainedVariance source target size genotype outcome
      = samplingForm
          (target.variance (linearScore genotype (marginalWeights source genotype outcome)))
          (excessForm source target genotype outcome) (pairingForm source target genotype outcome)
          size := by
  rw [trainedVariance, variance_linearScore_eq, excessForm, pairingForm]
  simp only [variance_linearScore_eq]
  exact expectation_quadraticForm_gwasWeights source hsize genotype outcome _

/-- **The expected intercept accumulator is a sampling form** whose population term is the
intercept accumulator of the population marginal score. -/
theorem trainedInterceptAccumulator_eq (source target : FiniteReportLaw Ω) {size : ℕ}
    (hsize : 2 ≤ size) (genotype : Ω → J → ℝ) (outcome : Ω → ℝ) :
    trainedInterceptAccumulator source target size genotype outcome
      = samplingForm
          (target.expectation outcome
              * target.variance (linearScore genotype (marginalWeights source genotype outcome))
            - target.covariance (linearScore genotype (marginalWeights source genotype outcome))
                outcome
              * target.expectation (linearScore genotype (marginalWeights source genotype outcome)))
          (∑ i, ∑ j, interceptMatrix target genotype outcome i j
            * weightExcess source genotype outcome i j)
          (∑ i, ∑ j, interceptMatrix target genotype outcome i j
            * weightPairing source genotype outcome i j) size := by
  rw [trainedInterceptAccumulator, interceptAccumulator_linearScore_eq]
  simp only [interceptAccumulator_linearScore_eq]
  exact expectation_quadraticForm_gwasWeights source hsize genotype outcome _

/-! ## The noise forms -/

/-- **A positive semidefinite matrix read against a target tag covariance is nonnegative.**  The
tag covariance is a target expectation of the products of centered tags, so exchanging the sums
turns the reading into a target expectation of the quadratic form at the centered tag vector. -/
theorem sum_tagCovariance_mul_nonneg (target : FiniteReportLaw Ω) (genotype : Ω → J → ℝ)
    (matrix : J → J → ℝ) (hmatrix : ∀ u : J → ℝ, 0 ≤ ∑ i, ∑ j, u i * u j * matrix i j) :
    0 ≤ ∑ i, ∑ j, tagCovariance target genotype i j * matrix i j := by
  have hcovariance : ∀ i j, tagCovariance target genotype i j
      = ∑ individual, target.mass individual
        * ((genotype individual i - target.expectation fun other ↦ genotype other i)
          * (genotype individual j - target.expectation fun other ↦ genotype other j)) :=
    fun _ _ ↦ rfl
  have hexchange : ∑ individual, target.mass individual * ∑ i, ∑ j,
        (genotype individual i - target.expectation fun other ↦ genotype other i)
          * (genotype individual j - target.expectation fun other ↦ genotype other j)
          * matrix i j
      = ∑ i, ∑ j, tagCovariance target genotype i j * matrix i j := by
    simp only [hcovariance, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun j _ ↦ Finset.sum_congr rfl fun individual _ ↦ by ring
  rw [← hexchange]
  exact Finset.sum_nonneg fun individual _ ↦
    mul_nonneg (target.mass_nonneg individual) (hmatrix _)

/-- **The excess form is nonnegative.** -/
theorem excessForm_nonneg (source target : FiniteReportLaw Ω) (genotype : Ω → J → ℝ)
    (outcome : Ω → ℝ) : 0 ≤ excessForm source target genotype outcome :=
  sum_tagCovariance_mul_nonneg target genotype _
    (quadraticForm_weightExcess_nonneg source genotype outcome)

/-- **The pairing form is nonnegative.** -/
theorem pairingForm_nonneg (source target : FiniteReportLaw Ω) (genotype : Ω → J → ℝ)
    (outcome : Ω → ℝ) : 0 ≤ pairingForm source target genotype outcome :=
  sum_tagCovariance_mul_nonneg target genotype _
    (quadraticForm_weightPairing_nonneg source genotype outcome)

/-- **The pairing form splits**: the source outcome variance times the reading of the source tag
covariance against the target one, plus the target variance of the population marginal score. -/
theorem pairingForm_eq (source target : FiniteReportLaw Ω) (genotype : Ω → J → ℝ)
    (outcome : Ω → ℝ) :
    pairingForm source target genotype outcome
      = source.variance outcome
          * ∑ i, ∑ j, tagCovariance target genotype i j * tagCovariance source genotype i j
        + target.variance (linearScore genotype (marginalWeights source genotype outcome)) := by
  rw [pairingForm, variance_linearScore_eq, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  simp only [weightPairing, tagCovariance]
  ring

/-- **The pairing form is at least the population term** `α = V_t(S_w)`. -/
theorem variance_le_pairingForm (source target : FiniteReportLaw Ω) (genotype : Ω → J → ℝ)
    (outcome : Ω → ℝ) :
    target.variance (linearScore genotype (marginalWeights source genotype outcome))
      ≤ pairingForm source target genotype outcome := by
  have htrace := sum_tagCovariance_mul_nonneg target genotype (tagCovariance source genotype)
    fun u ↦ le_of_le_of_eq (source.variance_nonneg (linearScore genotype u))
      (variance_linearScore source genotype u)
  have hproduct := mul_nonneg (source.variance_nonneg outcome) htrace
  rw [pairingForm_eq]
  linarith

end Finite

/-! ## The attenuation factor -/

/-- **The attenuation factor** `α / (α + β / n + γ / (n (n − 1)))`: the population term of a
sampling form over the form. -/
def attenuationFactor (population excess pairing : ℝ) (size : ℕ) : ℝ :=
  population / samplingForm population excess pairing size

/-- The attenuation factor is nonnegative. -/
theorem attenuationFactor_nonneg {α β γ : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β) (hγ : 0 ≤ γ) {size : ℕ}
    (hsize : 2 ≤ size) : 0 ≤ attenuationFactor α β γ size :=
  div_nonneg hα (hα.trans (le_samplingForm hβ hγ hsize))

/-- **The attenuation factor is at most one.** -/
theorem attenuationFactor_le_one {α β γ : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β) (hγ : 0 ≤ γ) {size : ℕ}
    (hsize : 2 ≤ size) : attenuationFactor α β γ size ≤ 1 := by
  rcases hα.eq_or_lt with hzero | hpositive
  · subst hzero
    rw [attenuationFactor, zero_div]
    exact zero_le_one
  · exact (div_le_one (hpositive.trans_le (le_samplingForm hβ hγ hsize))).mpr
      (le_samplingForm hβ hγ hsize)

/-- **The attenuation factor rises with the cohort size.** -/
theorem attenuationFactor_monotone {α β γ : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β) (hγ : 0 ≤ γ)
    {small large : ℕ} (hsmall : 2 ≤ small) (hle : small ≤ large) :
    attenuationFactor α β γ small ≤ attenuationFactor α β γ large := by
  rcases hα.eq_or_lt with hzero | hpositive
  · subst hzero
    simp only [attenuationFactor, zero_div, le_refl]
  · exact div_le_div_of_nonneg_left hα
      (hpositive.trans_le (le_samplingForm hβ hγ (hsmall.trans hle)))
      (samplingForm_antitone hβ hγ hsmall hle)

/-- **The attenuation factor tends to one** as the cohort grows, whenever the population term is
nonzero. -/
theorem tendsto_attenuationFactor {α : ℝ} (hα : α ≠ 0) (β γ : ℝ) :
    Tendsto (fun size : ℕ ↦ attenuationFactor α β γ size) atTop (𝓝 1) := by
  have hlimit := (tendsto_const_nhds (x := α)).div (tendsto_samplingForm α β γ) hα
  rw [div_self hα] at hlimit
  exact hlimit

/-- **A ratio over a sampling form is the ratio over its population term times the attenuation
factor**, whenever the population term is nonzero. -/
theorem div_samplingForm_eq_mul_attenuationFactor (c : ℝ) {α : ℝ} (hα : α ≠ 0) (β γ : ℝ)
    (size : ℕ) :
    c / samplingForm α β γ size = c / α * attenuationFactor α β γ size := by
  rw [attenuationFactor, div_mul_div_comm, mul_comm c α, mul_div_mul_left c _ hα]

/-! ## The attenuation law of the trained slope -/

section Attenuation

variable {Ω : Type*} [Fintype Ω] {J : Type*} [Fintype J]

/-- **The exact attenuation law.**  The trained calibration slope is the population slope
`C_t(S_w, Y) / α` times the attenuation factor `α / (α + β / n + γ / (n (n − 1)))`, with
`α = V_t(S_w)` and the excess and pairing forms `β`, `γ`.  There is no side condition: where
`α = 0` Cauchy–Schwarz forces the covariance to vanish and both sides are zero. -/
theorem trainedCalibrationSlope_eq_mul_attenuationFactor (source target : FiniteReportLaw Ω)
    {size : ℕ} (hsize : 2 ≤ size) (genotype : Ω → J → ℝ) (outcome : Ω → ℝ) :
    trainedCalibrationSlope source target size genotype outcome
      = populationCalibrationSlope source target genotype outcome
        * attenuationFactor
            (target.variance (linearScore genotype (marginalWeights source genotype outcome)))
            (excessForm source target genotype outcome) (pairingForm source target genotype outcome)
            size := by
  rw [trainedCalibrationSlope, trainedCovariance_eq source target hsize,
    trainedVariance_eq source target hsize, populationCalibrationSlope]
  by_cases hzero :
      target.variance (linearScore genotype (marginalWeights source genotype outcome)) = 0
  · have hsquare := target.covariance_sq_le_variance_mul
      (linearScore genotype (marginalWeights source genotype outcome)) outcome
    rw [hzero, zero_mul] at hsquare
    have hcovariance : target.covariance
        (linearScore genotype (marginalWeights source genotype outcome)) outcome = 0 :=
      (pow_eq_zero_iff two_ne_zero).mp (le_antisymm hsquare (sq_nonneg _))
    rw [hcovariance, zero_div, zero_div, zero_mul]
  · exact div_samplingForm_eq_mul_attenuationFactor _ hzero _ _ _

/-- **Finite training never amplifies a nonnegative slope.** -/
theorem trainedCalibrationSlope_le_populationCalibrationSlope (source target : FiniteReportLaw Ω)
    {size : ℕ} (hsize : 2 ≤ size) (genotype : Ω → J → ℝ) (outcome : Ω → ℝ)
    (hslope : 0 ≤ populationCalibrationSlope source target genotype outcome) :
    trainedCalibrationSlope source target size genotype outcome
      ≤ populationCalibrationSlope source target genotype outcome := by
  rw [trainedCalibrationSlope_eq_mul_attenuationFactor source target hsize]
  exact mul_le_of_le_one_right hslope (attenuationFactor_le_one (target.variance_nonneg _)
    (excessForm_nonneg source target genotype outcome)
    (pairingForm_nonneg source target genotype outcome) hsize)

/-- **The trained slope rises with the cohort size** when the population slope is nonnegative.
Accuracy has no such monotonicity (`populationAccuracy_lt_trainedAccuracy`). -/
theorem trainedCalibrationSlope_monotone (source target : FiniteReportLaw Ω) {small large : ℕ}
    (hsmall : 2 ≤ small) (hle : small ≤ large) (genotype : Ω → J → ℝ) (outcome : Ω → ℝ)
    (hslope : 0 ≤ populationCalibrationSlope source target genotype outcome) :
    trainedCalibrationSlope source target small genotype outcome
      ≤ trainedCalibrationSlope source target large genotype outcome := by
  rw [trainedCalibrationSlope_eq_mul_attenuationFactor source target hsmall,
    trainedCalibrationSlope_eq_mul_attenuationFactor source target (hsmall.trans hle)]
  exact mul_le_mul_of_nonneg_left (attenuationFactor_monotone (target.variance_nonneg _)
    (excessForm_nonneg source target genotype outcome)
    (pairingForm_nonneg source target genotype outcome) hsmall hle) hslope

/-- **The trained slope tends to the population slope** as the cohort grows, with no side
condition. -/
theorem tendsto_trainedCalibrationSlope (source target : FiniteReportLaw Ω)
    (genotype : Ω → J → ℝ) (outcome : Ω → ℝ) :
    Tendsto (fun size : ℕ ↦ trainedCalibrationSlope source target size genotype outcome) atTop
      (𝓝 (populationCalibrationSlope source target genotype outcome)) := by
  have hproduct : Tendsto (fun size : ℕ ↦ populationCalibrationSlope source target genotype outcome
      * attenuationFactor
          (target.variance (linearScore genotype (marginalWeights source genotype outcome)))
          (excessForm source target genotype outcome) (pairingForm source target genotype outcome)
          size) atTop (𝓝 (populationCalibrationSlope source target genotype outcome)) := by
    by_cases hzero :
        target.variance (linearScore genotype (marginalWeights source genotype outcome)) = 0
    · have hslope : populationCalibrationSlope source target genotype outcome = 0 := by
        rw [populationCalibrationSlope, hzero, div_zero]
      simp only [hslope, zero_mul]
      exact tendsto_const_nhds
    · simpa only [mul_one] using (tendsto_const_nhds
        (x := populationCalibrationSlope source target genotype outcome)).mul
          (tendsto_attenuationFactor hzero (excessForm source target genotype outcome)
            (pairingForm source target genotype outcome))
  exact hproduct.congr' ((eventually_ge_atTop 2).mono fun _ hsize ↦
    (trainedCalibrationSlope_eq_mul_attenuationFactor source target hsize genotype outcome).symm)

/-- **Finite training strictly attenuates a positive slope.**  If the population marginal score
has positive target covariance with the outcome, its target variance is positive by
Cauchy–Schwarz and the pairing form is at least that variance, so at every finite `n` the trained
slope lies strictly below the population slope. -/
theorem trainedCalibrationSlope_lt_populationCalibrationSlope (source target : FiniteReportLaw Ω)
    {size : ℕ} (hsize : 2 ≤ size) (genotype : Ω → J → ℝ) (outcome : Ω → ℝ)
    (hcovariance : 0 < target.covariance
      (linearScore genotype (marginalWeights source genotype outcome)) outcome) :
    trainedCalibrationSlope source target size genotype outcome
      < populationCalibrationSlope source target genotype outcome := by
  have hN : (2 : ℝ) ≤ size := by exact_mod_cast hsize
  have hvariance : 0 < target.variance
      (linearScore genotype (marginalWeights source genotype outcome)) := by
    refine (target.variance_nonneg _).lt_of_ne fun hzero ↦ ?_
    have hsquare := target.covariance_sq_le_variance_mul
      (linearScore genotype (marginalWeights source genotype outcome)) outcome
    rw [← hzero, zero_mul] at hsquare
    have hpositive := pow_pos hcovariance 2
    linarith
  have hpairing := hvariance.trans_le (variance_le_pairingForm source target genotype outcome)
  have hexcess : 0 ≤ excessForm source target genotype outcome / size :=
    div_nonneg (excessForm_nonneg source target genotype outcome) (by linarith)
  have hnoise : 0 < pairingForm source target genotype outcome / (size * (size - 1)) :=
    div_pos hpairing (mul_pos (by linarith) (by linarith))
  rw [trainedCalibrationSlope, trainedCovariance_eq source target hsize,
    trainedVariance_eq source target hsize, populationCalibrationSlope, samplingForm]
  exact div_lt_div_of_pos_left hcovariance hvariance (by linarith)

/-- The expected target score variance tends to the target variance of the population marginal
score. -/
theorem tendsto_trainedVariance (source target : FiniteReportLaw Ω) (genotype : Ω → J → ℝ)
    (outcome : Ω → ℝ) :
    Tendsto (fun size : ℕ ↦ trainedVariance source target size genotype outcome) atTop
      (𝓝 (target.variance (linearScore genotype (marginalWeights source genotype outcome)))) :=
  (tendsto_samplingForm _ _ _).congr' ((eventually_ge_atTop 2).mono fun _ hsize ↦
    (trainedVariance_eq source target hsize genotype outcome).symm)

/-- The expected intercept accumulator tends to the intercept accumulator of the population
marginal score. -/
theorem tendsto_trainedInterceptAccumulator (source target : FiniteReportLaw Ω)
    (genotype : Ω → J → ℝ) (outcome : Ω → ℝ) :
    Tendsto (fun size : ℕ ↦ trainedInterceptAccumulator source target size genotype outcome)
      atTop (𝓝 (target.expectation outcome
          * target.variance (linearScore genotype (marginalWeights source genotype outcome))
        - target.covariance (linearScore genotype (marginalWeights source genotype outcome))
            outcome
          * target.expectation (linearScore genotype (marginalWeights source genotype outcome)))) :=
  (tendsto_samplingForm _ _ _).congr' ((eventually_ge_atTop 2).mono fun _ hsize ↦
    (trainedInterceptAccumulator_eq source target hsize genotype outcome).symm)

/-- **The trained intercept tends to the population intercept** as the cohort grows, wherever the
population marginal score varies in the target. -/
theorem tendsto_trainedCalibrationIntercept (source target : FiniteReportLaw Ω)
    (genotype : Ω → J → ℝ) (outcome : Ω → ℝ)
    (hvariance :
      target.variance (linearScore genotype (marginalWeights source genotype outcome)) ≠ 0) :
    Tendsto (fun size : ℕ ↦ trainedCalibrationIntercept source target size genotype outcome)
      atTop (𝓝 (populationCalibrationIntercept source target genotype outcome)) :=
  (tendsto_trainedInterceptAccumulator source target genotype outcome).div
    (tendsto_trainedVariance source target genotype outcome) hvariance

end Attenuation

/-! ## Target matrices as polynomials -/

section Polynomials

variable {H : Type*} [Fintype H] {J : Type*}

/-- The tag covariance matrix `C(X_i, X_j)`, as polynomials of degree two. -/
def tagCovariancePolynomial (genotype : H → J → ℝ) (i j : J) : MvPolynomial H ℝ :=
  covariancePolynomial (fun individual ↦ genotype individual i)
    (fun individual ↦ genotype individual j)

/-- The intercept matrix `μ(Y) C(X_i, X_j) − C(X_i, Y) μ(X_j)`, as polynomials of degree three. -/
def interceptMatrixPolynomial (genotype : H → J → ℝ) (outcome : H → ℝ) (i j : J) :
    MvPolynomial H ℝ :=
  expectationPolynomial outcome * tagCovariancePolynomial genotype i j
    - covariancePolynomial (fun individual ↦ genotype individual i) outcome
      * expectationPolynomial fun individual ↦ genotype individual j

/-- The tag covariance polynomial evaluates to the tag covariance. -/
theorem eval_tagCovariancePolynomial (law : FiniteReportLaw H) (genotype : H → J → ℝ)
    (i j : J) :
    eval law.mass (tagCovariancePolynomial genotype i j) = tagCovariance law genotype i j :=
  eval_covariancePolynomial law _ _

/-- The intercept matrix polynomial evaluates to the intercept matrix. -/
theorem eval_interceptMatrixPolynomial (law : FiniteReportLaw H) (genotype : H → J → ℝ)
    (outcome : H → ℝ) (i j : J) :
    eval law.mass (interceptMatrixPolynomial genotype outcome i j)
      = interceptMatrix law genotype outcome i j := by
  rw [interceptMatrixPolynomial, map_sub, map_mul, map_mul, eval_expectationPolynomial,
    eval_tagCovariancePolynomial, eval_covariancePolynomial, eval_expectationPolynomial]
  rfl

/-- The tag covariance polynomial has total degree at most two. -/
theorem totalDegree_tagCovariancePolynomial_le (genotype : H → J → ℝ) (i j : J) :
    (tagCovariancePolynomial genotype i j).totalDegree ≤ 2 :=
  totalDegree_covariancePolynomial_le _ _

/-- The intercept matrix polynomial has total degree at most three. -/
theorem totalDegree_interceptMatrixPolynomial_le (genotype : H → J → ℝ) (outcome : H → ℝ)
    (i j : J) : (interceptMatrixPolynomial genotype outcome i j).totalDegree ≤ 3 := by
  have hmean := totalDegree_expectationPolynomial_le outcome
  have htag := totalDegree_tagCovariancePolynomial_le genotype i j
  have hmarginal :=
    totalDegree_covariancePolynomial_le (fun individual ↦ genotype individual i) outcome
  have hmarker := totalDegree_expectationPolynomial_le fun individual ↦ genotype individual j
  refine (totalDegree_sub _ _).trans (max_le ?_ ?_)
  · exact (totalDegree_mul _ _).trans (by omega)
  · exact (totalDegree_mul _ _).trans (by omega)

end Polynomials

/-! ## The calibration accumulators as frequency polynomials of two demes -/

variable {Deme Locus : Type*} {Allele : Locus → Type*}
variable [Fintype Deme] [DecidableEq Deme] [Fintype Locus] [DecidableEq Locus]
  [∀ ℓ, Fintype (Allele ℓ)] [∀ ℓ, DecidableEq (Allele ℓ)]

section Accumulators

variable {J : Type*} [Fintype J]

/-- **The trained covariance polynomial** `∑_j C_t(X_j, Y) C_s(X_j, Y)`: the target marginal
effects read against the source ones, a frequency polynomial of the two demes. -/
def trainedCovariancePolynomial (source target : Deme)
    (genotype : FullHaplotype Locus Allele → J → ℝ) (outcome : FullHaplotype Locus Allele → ℝ) :
    FrequencyPolynomial Deme Locus Allele :=
  ∑ marker, demePolynomial target
      (covariancePolynomial (fun individual ↦ genotype individual marker) outcome)
    * demePolynomial source
      (covariancePolynomial (fun individual ↦ genotype individual marker) outcome)

/-- At a state, the trained covariance polynomial is the target covariance of the population
marginal score of the source deme with the outcome. -/
theorem polynomialFunction_trainedCovariancePolynomial (source target : Deme)
    (genotype : FullHaplotype Locus Allele → J → ℝ) (outcome : FullHaplotype Locus Allele → ℝ)
    (y : FrequencyState Deme Locus Allele) :
    polynomialFunction (trainedCovariancePolynomial source target genotype outcome) y
      = (stateLaw y target).covariance
          (linearScore genotype (marginalWeights (stateLaw y source) genotype outcome))
          outcome := by
  rw [covariance_linearScore]
  simp only [polynomialFunction_apply, trainedCovariancePolynomial, map_sum, map_mul,
    eval_demePolynomial, eval_covariancePolynomial]
  exact Finset.sum_congr rfl fun marker _ ↦ mul_comm _ _

/-- **The trained covariance polynomial has total degree at most four.** -/
theorem totalDegree_trainedCovariancePolynomial_le (source target : Deme)
    (genotype : FullHaplotype Locus Allele → J → ℝ) (outcome : FullHaplotype Locus Allele → ℝ) :
    (trainedCovariancePolynomial source target genotype outcome).totalDegree ≤ 4 := by
  refine (totalDegree_finset_sum _ _).trans (Finset.sup_le fun marker _ ↦ ?_)
  have hdegree : ∀ deme : Deme, (demePolynomial deme
      (covariancePolynomial (fun individual ↦ genotype individual marker) outcome)).totalDegree
      ≤ 2 :=
    fun deme ↦ (totalDegree_rename_le _ _).trans (totalDegree_covariancePolynomial_le _ outcome)
  have htarget := hdegree target
  have hsource := hdegree source
  exact (totalDegree_mul _ _).trans (by omega)

/-- **A trained polynomial has total degree at most the sum of the degrees** of its target and
source matrices.  The double sum is read as one sum over pairs of tags. -/
theorem totalDegree_trainedPolynomial_le_add (source target : Deme)
    (sourceMatrix targetMatrix : J → J → MvPolynomial (FullHaplotype Locus Allele) ℝ) {a b : ℕ}
    (hsource : ∀ i j, (sourceMatrix i j).totalDegree ≤ a)
    (htarget : ∀ i j, (targetMatrix i j).totalDegree ≤ b) :
    (trainedPolynomial source target sourceMatrix targetMatrix).totalDegree ≤ b + a := by
  rw [trainedPolynomial, ← Fintype.sum_prod_type']
  refine (totalDegree_finset_sum _ _).trans (Finset.sup_le fun pair _ ↦ ?_)
  exact (totalDegree_mul _ _).trans (add_le_add
    ((totalDegree_rename_le _ _).trans (htarget pair.1 pair.2))
    ((totalDegree_rename_le _ _).trans (hsource pair.1 pair.2)))

/-- At a state, the product polynomial read against the tag covariance is the target variance of
the population marginal score of the source deme. -/
theorem polynomialFunction_populationVariance (source target : Deme)
    (genotype : FullHaplotype Locus Allele → J → ℝ) (outcome : FullHaplotype Locus Allele → ℝ)
    (y : FrequencyState Deme Locus Allele) :
    polynomialFunction (trainedPolynomial source target (weightProductPolynomial genotype outcome)
        (tagCovariancePolynomial genotype)) y
      = (stateLaw y target).variance
          (linearScore genotype (marginalWeights (stateLaw y source) genotype outcome)) := by
  rw [variance_linearScore_eq]
  simp only [polynomialFunction_trainedPolynomial, eval_weightProductPolynomial,
    eval_tagCovariancePolynomial]

/-- At a state, the excess polynomial read against the tag covariance is the excess form. -/
theorem polynomialFunction_excessForm (source target : Deme)
    (genotype : FullHaplotype Locus Allele → J → ℝ) (outcome : FullHaplotype Locus Allele → ℝ)
    (y : FrequencyState Deme Locus Allele) :
    polynomialFunction (trainedPolynomial source target (weightExcessPolynomial genotype outcome)
        (tagCovariancePolynomial genotype)) y
      = excessForm (stateLaw y source) (stateLaw y target) genotype outcome := by
  simp only [polynomialFunction_trainedPolynomial, eval_weightExcessPolynomial,
    eval_tagCovariancePolynomial, excessForm]

/-- At a state, the pairing polynomial read against the tag covariance is the pairing form. -/
theorem polynomialFunction_pairingForm (source target : Deme)
    (genotype : FullHaplotype Locus Allele → J → ℝ) (outcome : FullHaplotype Locus Allele → ℝ)
    (y : FrequencyState Deme Locus Allele) :
    polynomialFunction (trainedPolynomial source target (weightPairingPolynomial genotype outcome)
        (tagCovariancePolynomial genotype)) y
      = pairingForm (stateLaw y source) (stateLaw y target) genotype outcome := by
  simp only [polynomialFunction_trainedPolynomial, eval_weightPairingPolynomial,
    eval_tagCovariancePolynomial, pairingForm]

/-- At a state, the product polynomial read against the intercept matrix is the intercept
accumulator of the population marginal score of the source deme. -/
theorem polynomialFunction_populationInterceptAccumulator (source target : Deme)
    (genotype : FullHaplotype Locus Allele → J → ℝ) (outcome : FullHaplotype Locus Allele → ℝ)
    (y : FrequencyState Deme Locus Allele) :
    polynomialFunction (trainedPolynomial source target (weightProductPolynomial genotype outcome)
        (interceptMatrixPolynomial genotype outcome)) y
      = (stateLaw y target).expectation outcome
          * (stateLaw y target).variance
            (linearScore genotype (marginalWeights (stateLaw y source) genotype outcome))
        - (stateLaw y target).covariance
            (linearScore genotype (marginalWeights (stateLaw y source) genotype outcome)) outcome
          * (stateLaw y target).expectation
            (linearScore genotype (marginalWeights (stateLaw y source) genotype outcome)) := by
  rw [interceptAccumulator_linearScore_eq]
  simp only [polynomialFunction_trainedPolynomial, eval_weightProductPolynomial,
    eval_interceptMatrixPolynomial]

/-- **At a state, the trained covariance is a polynomial observable** of total degree at most
four. -/
theorem trainedCovariance_stateLaw (source target : Deme) {size : ℕ} (hsize : 2 ≤ size)
    (genotype : FullHaplotype Locus Allele → J → ℝ) (outcome : FullHaplotype Locus Allele → ℝ)
    (y : FrequencyState Deme Locus Allele) :
    trainedCovariance (stateLaw y source) (stateLaw y target) size genotype outcome
      = polynomialFunction (trainedCovariancePolynomial source target genotype outcome) y := by
  rw [trainedCovariance_eq _ _ hsize, polynomialFunction_trainedCovariancePolynomial]

/-- **At a state, the trained variance is a sampling form of three polynomial observables** of
total degree at most six. -/
theorem trainedVariance_stateLaw (source target : Deme) {size : ℕ} (hsize : 2 ≤ size)
    (genotype : FullHaplotype Locus Allele → J → ℝ) (outcome : FullHaplotype Locus Allele → ℝ)
    (y : FrequencyState Deme Locus Allele) :
    trainedVariance (stateLaw y source) (stateLaw y target) size genotype outcome
      = samplingForm
          (polynomialFunction (trainedPolynomial source target
            (weightProductPolynomial genotype outcome) (tagCovariancePolynomial genotype)) y)
          (polynomialFunction (trainedPolynomial source target
            (weightExcessPolynomial genotype outcome) (tagCovariancePolynomial genotype)) y)
          (polynomialFunction (trainedPolynomial source target
            (weightPairingPolynomial genotype outcome) (tagCovariancePolynomial genotype)) y)
          size := by
  rw [trainedVariance_eq _ _ hsize, polynomialFunction_populationVariance,
    polynomialFunction_excessForm, polynomialFunction_pairingForm]

/-- **At a state, the trained intercept accumulator is a sampling form of three polynomial
observables** of total degree at most seven. -/
theorem trainedInterceptAccumulator_stateLaw (source target : Deme) {size : ℕ}
    (hsize : 2 ≤ size) (genotype : FullHaplotype Locus Allele → J → ℝ)
    (outcome : FullHaplotype Locus Allele → ℝ) (y : FrequencyState Deme Locus Allele) :
    trainedInterceptAccumulator (stateLaw y source) (stateLaw y target) size genotype outcome
      = samplingForm
          (polynomialFunction (trainedPolynomial source target
            (weightProductPolynomial genotype outcome)
            (interceptMatrixPolynomial genotype outcome)) y)
          (polynomialFunction (trainedPolynomial source target
            (weightExcessPolynomial genotype outcome)
            (interceptMatrixPolynomial genotype outcome)) y)
          (polynomialFunction (trainedPolynomial source target
            (weightPairingPolynomial genotype outcome)
            (interceptMatrixPolynomial genotype outcome)) y)
          size := by
  rw [trainedInterceptAccumulator_eq _ _ hsize, polynomialFunction_populationInterceptAccumulator]
  simp only [polynomialFunction_trainedPolynomial, eval_weightExcessPolynomial,
    eval_weightPairingPolynomial, eval_interceptMatrixPolynomial]

end Accumulators

/-! ## Calibration of expectations under a kernel -/

section Expected

variable {J : Type*} [Fintype J]

/-- **The trained calibration slope of expectations under a kernel**: the expected target
covariance of the GWAS score with the outcome over its expected target variance, the expectations
taken over the populations of the kernel and the training cohort drawn in the source deme of each.
NOTE2 §6.2 query: a ratio of expectations. -/
def expectedTrainedCalibrationSlope
    (κ : Kernel (FrequencyState Deme Locus Allele) (FrequencyState Deme Locus Allele))
    (x0 : FrequencyState Deme Locus Allele) (source target : Deme) (size : ℕ)
    (genotype : FullHaplotype Locus Allele → J → ℝ) (outcome : FullHaplotype Locus Allele → ℝ) :
    ℝ :=
  (∫ y, trainedCovariance (stateLaw y source) (stateLaw y target) size genotype outcome ∂(κ x0))
    / ∫ y, trainedVariance (stateLaw y source) (stateLaw y target) size genotype outcome ∂(κ x0)

/-- **The trained calibration intercept of expectations under a kernel**: the expected intercept
accumulator over the expected target score variance.  NOTE2 §6.2 query: a ratio of
expectations. -/
def expectedTrainedCalibrationIntercept
    (κ : Kernel (FrequencyState Deme Locus Allele) (FrequencyState Deme Locus Allele))
    (x0 : FrequencyState Deme Locus Allele) (source target : Deme) (size : ℕ)
    (genotype : FullHaplotype Locus Allele → J → ℝ) (outcome : FullHaplotype Locus Allele → ℝ) :
    ℝ :=
  (∫ y, trainedInterceptAccumulator (stateLaw y source) (stateLaw y target) size genotype outcome
      ∂(κ x0))
    / ∫ y, trainedVariance (stateLaw y source) (stateLaw y target) size genotype outcome ∂(κ x0)

/-- **The rational trained calibration slope** of a budget-`n` moment vector and a cohort size:
a coefficient vector over a sampling form of coefficient vectors. -/
def momentTrainedCalibrationSlope (ℓ₀ : Locus) (n : ℕ) (source target : Deme)
    (genotype : FullHaplotype Locus Allele → J → ℝ) (outcome : FullHaplotype Locus Allele → ℝ)
    (size : ℕ) (v : BudgetConfiguration Deme Locus Allele (fun _ ↦ n) → ℝ) : ℝ :=
  (budgetCoefficients ℓ₀ (fun _ ↦ n) (trainedCovariancePolynomial source target genotype outcome)
      ⬝ᵥ v)
    / samplingForm
      (budgetCoefficients ℓ₀ (fun _ ↦ n) (trainedPolynomial source target
        (weightProductPolynomial genotype outcome) (tagCovariancePolynomial genotype)) ⬝ᵥ v)
      (budgetCoefficients ℓ₀ (fun _ ↦ n) (trainedPolynomial source target
        (weightExcessPolynomial genotype outcome) (tagCovariancePolynomial genotype)) ⬝ᵥ v)
      (budgetCoefficients ℓ₀ (fun _ ↦ n) (trainedPolynomial source target
        (weightPairingPolynomial genotype outcome) (tagCovariancePolynomial genotype)) ⬝ᵥ v) size

/-- **The rational trained calibration intercept** of a budget-`n` moment vector and a cohort
size: a ratio of two sampling forms of coefficient vectors. -/
def momentTrainedCalibrationIntercept (ℓ₀ : Locus) (n : ℕ) (source target : Deme)
    (genotype : FullHaplotype Locus Allele → J → ℝ) (outcome : FullHaplotype Locus Allele → ℝ)
    (size : ℕ) (v : BudgetConfiguration Deme Locus Allele (fun _ ↦ n) → ℝ) : ℝ :=
  samplingForm
      (budgetCoefficients ℓ₀ (fun _ ↦ n) (trainedPolynomial source target
        (weightProductPolynomial genotype outcome) (interceptMatrixPolynomial genotype outcome))
        ⬝ᵥ v)
      (budgetCoefficients ℓ₀ (fun _ ↦ n) (trainedPolynomial source target
        (weightExcessPolynomial genotype outcome) (interceptMatrixPolynomial genotype outcome))
        ⬝ᵥ v)
      (budgetCoefficients ℓ₀ (fun _ ↦ n) (trainedPolynomial source target
        (weightPairingPolynomial genotype outcome) (interceptMatrixPolynomial genotype outcome))
        ⬝ᵥ v) size
    / samplingForm
      (budgetCoefficients ℓ₀ (fun _ ↦ n) (trainedPolynomial source target
        (weightProductPolynomial genotype outcome) (tagCovariancePolynomial genotype)) ⬝ᵥ v)
      (budgetCoefficients ℓ₀ (fun _ ↦ n) (trainedPolynomial source target
        (weightExcessPolynomial genotype outcome) (tagCovariancePolynomial genotype)) ⬝ᵥ v)
      (budgetCoefficients ℓ₀ (fun _ ↦ n) (trainedPolynomial source target
        (weightPairingPolynomial genotype outcome) (tagCovariancePolynomial genotype)) ⬝ᵥ v) size

end Expected

section MomentKernel

variable {J : Type*} [Fintype J] (ℓ₀ : Locus) {n : ℕ}
  (κ : Kernel (FrequencyState Deme Locus Allele) (FrequencyState Deme Locus Allele))
  [IsMarkovKernel κ]
  (M : Matrix (BudgetConfiguration Deme Locus Allele (fun _ ↦ n))
    (BudgetConfiguration Deme Locus Allele (fun _ ↦ n)) ℝ)
  (hmoment : ∀ (x : FrequencyState Deme Locus Allele)
    (ξ : BudgetConfiguration Deme Locus Allele (fun _ ↦ n)),
    ∫ y, polynomialFunction (momentPolynomial ξ.1) y ∂(κ x)
      = (M *ᵥ budgetMomentFeature (fun _ ↦ n) x) ξ)

include hmoment

/-- **The expected trained covariance under a kernel with budget-`n` moments**, `n ≥ 4`, is a
coefficient vector dotted with the propagated moments. -/
theorem integral_trainedCovariance_eq (hn : 4 ≤ n) (x0 : FrequencyState Deme Locus Allele)
    (source target : Deme) {size : ℕ} (hsize : 2 ≤ size)
    (genotype : FullHaplotype Locus Allele → J → ℝ) (outcome : FullHaplotype Locus Allele → ℝ) :
    ∫ y, trainedCovariance (stateLaw y source) (stateLaw y target) size genotype outcome ∂(κ x0)
      = budgetCoefficients ℓ₀ (fun _ ↦ n)
          (trainedCovariancePolynomial source target genotype outcome)
        ⬝ᵥ (M *ᵥ budgetMomentFeature (fun _ ↦ n) x0) :=
  EndToEndCalibrationLaw.integral_eq_dotProduct_of_totalDegree_le ℓ₀ κ M hmoment _
    ((totalDegree_trainedCovariancePolynomial_le source target genotype outcome).trans hn) _
    (fun y ↦ (trainedCovariance_stateLaw source target hsize genotype outcome y).symm) x0

/-- **The expected trained variance under a kernel with budget-`n` moments**, `n ≥ 6`, is a
sampling form of coefficient vectors dotted with the propagated moments. -/
theorem integral_trainedVariance_eq (hn : 6 ≤ n) (x0 : FrequencyState Deme Locus Allele)
    (source target : Deme) {size : ℕ} (hsize : 2 ≤ size)
    (genotype : FullHaplotype Locus Allele → J → ℝ) (outcome : FullHaplotype Locus Allele → ℝ) :
    ∫ y, trainedVariance (stateLaw y source) (stateLaw y target) size genotype outcome ∂(κ x0)
      = samplingForm
          (budgetCoefficients ℓ₀ (fun _ ↦ n) (trainedPolynomial source target
              (weightProductPolynomial genotype outcome) (tagCovariancePolynomial genotype))
            ⬝ᵥ (M *ᵥ budgetMomentFeature (fun _ ↦ n) x0))
          (budgetCoefficients ℓ₀ (fun _ ↦ n) (trainedPolynomial source target
              (weightExcessPolynomial genotype outcome) (tagCovariancePolynomial genotype))
            ⬝ᵥ (M *ᵥ budgetMomentFeature (fun _ ↦ n) x0))
          (budgetCoefficients ℓ₀ (fun _ ↦ n) (trainedPolynomial source target
              (weightPairingPolynomial genotype outcome) (tagCovariancePolynomial genotype))
            ⬝ᵥ (M *ᵥ budgetMomentFeature (fun _ ↦ n) x0)) size := by
  simp only [trainedVariance_stateLaw source target hsize genotype outcome]
  exact integral_samplingForm_polynomialFunction ℓ₀ κ M hmoment x0 size _ _ _
    ((totalDegree_trainedPolynomial_le_add _ _ _ _
      (totalDegree_weightProductPolynomial_le genotype outcome)
      (totalDegree_tagCovariancePolynomial_le genotype)).trans hn)
    ((totalDegree_trainedPolynomial_le_add _ _ _ _
      (totalDegree_weightExcessPolynomial_le genotype outcome)
      (totalDegree_tagCovariancePolynomial_le genotype)).trans hn)
    ((totalDegree_trainedPolynomial_le_add _ _ _ _
      (totalDegree_weightPairingPolynomial_le genotype outcome)
      (totalDegree_tagCovariancePolynomial_le genotype)).trans hn)

/-- **The expected trained intercept accumulator under a kernel with budget-`n` moments**,
`n ≥ 7`, is a sampling form of coefficient vectors dotted with the propagated moments. -/
theorem integral_trainedInterceptAccumulator_eq (hn : 7 ≤ n)
    (x0 : FrequencyState Deme Locus Allele) (source target : Deme) {size : ℕ} (hsize : 2 ≤ size)
    (genotype : FullHaplotype Locus Allele → J → ℝ) (outcome : FullHaplotype Locus Allele → ℝ) :
    ∫ y, trainedInterceptAccumulator (stateLaw y source) (stateLaw y target) size genotype outcome
        ∂(κ x0)
      = samplingForm
          (budgetCoefficients ℓ₀ (fun _ ↦ n) (trainedPolynomial source target
              (weightProductPolynomial genotype outcome)
              (interceptMatrixPolynomial genotype outcome))
            ⬝ᵥ (M *ᵥ budgetMomentFeature (fun _ ↦ n) x0))
          (budgetCoefficients ℓ₀ (fun _ ↦ n) (trainedPolynomial source target
              (weightExcessPolynomial genotype outcome)
              (interceptMatrixPolynomial genotype outcome))
            ⬝ᵥ (M *ᵥ budgetMomentFeature (fun _ ↦ n) x0))
          (budgetCoefficients ℓ₀ (fun _ ↦ n) (trainedPolynomial source target
              (weightPairingPolynomial genotype outcome)
              (interceptMatrixPolynomial genotype outcome))
            ⬝ᵥ (M *ᵥ budgetMomentFeature (fun _ ↦ n) x0)) size := by
  simp only [trainedInterceptAccumulator_stateLaw source target hsize genotype outcome]
  exact integral_samplingForm_polynomialFunction ℓ₀ κ M hmoment x0 size _ _ _
    ((totalDegree_trainedPolynomial_le_add _ _ _ _
      (totalDegree_weightProductPolynomial_le genotype outcome)
      (totalDegree_interceptMatrixPolynomial_le genotype outcome)).trans hn)
    ((totalDegree_trainedPolynomial_le_add _ _ _ _
      (totalDegree_weightExcessPolynomial_le genotype outcome)
      (totalDegree_interceptMatrixPolynomial_le genotype outcome)).trans hn)
    ((totalDegree_trainedPolynomial_le_add _ _ _ _
      (totalDegree_weightPairingPolynomial_le genotype outcome)
      (totalDegree_interceptMatrixPolynomial_le genotype outcome)).trans hn)

/-- **The trained slope under a kernel with budget-`n` moments**, `n ≥ 6`, is the rational
trained slope of the propagated moments. -/
theorem expectedTrainedCalibrationSlope_eq_momentTrainedCalibrationSlope (hn : 6 ≤ n)
    (x0 : FrequencyState Deme Locus Allele) (source target : Deme) {size : ℕ} (hsize : 2 ≤ size)
    (genotype : FullHaplotype Locus Allele → J → ℝ) (outcome : FullHaplotype Locus Allele → ℝ) :
    expectedTrainedCalibrationSlope κ x0 source target size genotype outcome
      = momentTrainedCalibrationSlope ℓ₀ n source target genotype outcome size
          (M *ᵥ budgetMomentFeature (fun _ ↦ n) x0) := by
  rw [expectedTrainedCalibrationSlope,
    integral_trainedCovariance_eq ℓ₀ κ M hmoment (by omega) x0 source target hsize,
    integral_trainedVariance_eq ℓ₀ κ M hmoment hn x0 source target hsize]
  rfl

/-- **The trained intercept under a kernel with budget-`n` moments**, `n ≥ 7`, is the rational
trained intercept of the propagated moments. -/
theorem expectedTrainedCalibrationIntercept_eq_momentTrainedCalibrationIntercept (hn : 7 ≤ n)
    (x0 : FrequencyState Deme Locus Allele) (source target : Deme) {size : ℕ} (hsize : 2 ≤ size)
    (genotype : FullHaplotype Locus Allele → J → ℝ) (outcome : FullHaplotype Locus Allele → ℝ) :
    expectedTrainedCalibrationIntercept κ x0 source target size genotype outcome
      = momentTrainedCalibrationIntercept ℓ₀ n source target genotype outcome size
          (M *ᵥ budgetMomentFeature (fun _ ↦ n) x0) := by
  rw [expectedTrainedCalibrationIntercept,
    integral_trainedInterceptAccumulator_eq ℓ₀ κ M hmoment hn x0 source target hsize,
    integral_trainedVariance_eq ℓ₀ κ M hmoment (by omega) x0 source target hsize]
  rfl

/-- **The attenuation law under a kernel.**  Under a kernel with budget-`n` moments, `n ≥ 6`, the
trained slope of expectations is the population slope of expectations `E C_t(S_w, Y) / E V_t(S_w)`
times the attenuation factor of the integrated population, excess and pairing forms, wherever the
expected population variance is nonzero. -/
theorem expectedTrainedCalibrationSlope_eq_mul_attenuationFactor (hn : 6 ≤ n)
    (x0 : FrequencyState Deme Locus Allele) (source target : Deme) {size : ℕ} (hsize : 2 ≤ size)
    (genotype : FullHaplotype Locus Allele → J → ℝ) (outcome : FullHaplotype Locus Allele → ℝ)
    (hpopulation : ∫ y, (stateLaw y target).variance
      (linearScore genotype (marginalWeights (stateLaw y source) genotype outcome)) ∂(κ x0) ≠ 0) :
    expectedTrainedCalibrationSlope κ x0 source target size genotype outcome
      = (∫ y, (stateLaw y target).covariance
            (linearScore genotype (marginalWeights (stateLaw y source) genotype outcome)) outcome
            ∂(κ x0))
          / (∫ y, (stateLaw y target).variance
            (linearScore genotype (marginalWeights (stateLaw y source) genotype outcome)) ∂(κ x0))
        * attenuationFactor
          (∫ y, (stateLaw y target).variance
            (linearScore genotype (marginalWeights (stateLaw y source) genotype outcome)) ∂(κ x0))
          (∫ y, excessForm (stateLaw y source) (stateLaw y target) genotype outcome ∂(κ x0))
          (∫ y, pairingForm (stateLaw y source) (stateLaw y target) genotype outcome ∂(κ x0))
          size := by
  have hvariance := EndToEndCalibrationLaw.integral_eq_dotProduct_of_totalDegree_le ℓ₀ κ M
    hmoment _ ((totalDegree_trainedPolynomial_le_add _ _ _ _
      (totalDegree_weightProductPolynomial_le genotype outcome)
      (totalDegree_tagCovariancePolynomial_le genotype)).trans hn) _
    (polynomialFunction_populationVariance source target genotype outcome) x0
  have hexcess := EndToEndCalibrationLaw.integral_eq_dotProduct_of_totalDegree_le ℓ₀ κ M
    hmoment _ ((totalDegree_trainedPolynomial_le_add _ _ _ _
      (totalDegree_weightExcessPolynomial_le genotype outcome)
      (totalDegree_tagCovariancePolynomial_le genotype)).trans hn) _
    (polynomialFunction_excessForm source target genotype outcome) x0
  have hpairing := EndToEndCalibrationLaw.integral_eq_dotProduct_of_totalDegree_le ℓ₀ κ M
    hmoment _ ((totalDegree_trainedPolynomial_le_add _ _ _ _
      (totalDegree_weightPairingPolynomial_le genotype outcome)
      (totalDegree_tagCovariancePolynomial_le genotype)).trans hn) _
    (polynomialFunction_pairingForm source target genotype outcome) x0
  have hcovariance : ∫ y, trainedCovariance (stateLaw y source) (stateLaw y target) size genotype
        outcome ∂(κ x0)
      = ∫ y, (stateLaw y target).covariance
          (linearScore genotype (marginalWeights (stateLaw y source) genotype outcome)) outcome
          ∂(κ x0) := by
    simp only [trainedCovariance_eq _ _ hsize]
  rw [hvariance] at hpopulation
  rw [expectedTrainedCalibrationSlope, hcovariance,
    integral_trainedVariance_eq ℓ₀ κ M hmoment hn x0 source target hsize, hvariance, hexcess,
    hpairing]
  exact div_samplingForm_eq_mul_attenuationFactor _ hpopulation _ _ _

/-- **The trained slope of expectations rises with the cohort size** under a kernel with
budget-`n` moments, `n ≥ 6`, when the expected population variance is positive and the expected
population covariance is nonnegative. -/
theorem expectedTrainedCalibrationSlope_monotone (hn : 6 ≤ n)
    (x0 : FrequencyState Deme Locus Allele) (source target : Deme) {small large : ℕ}
    (hsmall : 2 ≤ small) (hle : small ≤ large)
    (genotype : FullHaplotype Locus Allele → J → ℝ) (outcome : FullHaplotype Locus Allele → ℝ)
    (hpopulation : 0 < ∫ y, (stateLaw y target).variance
      (linearScore genotype (marginalWeights (stateLaw y source) genotype outcome)) ∂(κ x0))
    (hcovariance : 0 ≤ ∫ y, (stateLaw y target).covariance
      (linearScore genotype (marginalWeights (stateLaw y source) genotype outcome)) outcome
      ∂(κ x0)) :
    expectedTrainedCalibrationSlope κ x0 source target small genotype outcome
      ≤ expectedTrainedCalibrationSlope κ x0 source target large genotype outcome := by
  rw [expectedTrainedCalibrationSlope_eq_mul_attenuationFactor ℓ₀ κ M hmoment hn x0 source target
      hsmall genotype outcome hpopulation.ne',
    expectedTrainedCalibrationSlope_eq_mul_attenuationFactor ℓ₀ κ M hmoment hn x0 source target
      (hsmall.trans hle) genotype outcome hpopulation.ne']
  exact mul_le_mul_of_nonneg_left (attenuationFactor_monotone hpopulation.le
    (integral_nonneg fun y ↦
      excessForm_nonneg (stateLaw y source) (stateLaw y target) genotype outcome)
    (integral_nonneg fun y ↦
      pairingForm_nonneg (stateLaw y source) (stateLaw y target) genotype outcome) hsmall hle)
    (div_nonneg hcovariance hpopulation.le)

end MomentKernel

/-! ## The law along a history of epochs, splits and pulses -/

section Histories

variable {J : Type*} [Fintype J]

/-- **The trained calibration slope along a history.**  The slope of expectations of a score
trained by a GWAS on `n` haplotypes of the source deme and deployed in the target deme is the
rational function `momentTrainedCalibrationSlope` of the chronological propagator applied to the
budget-6 moments of the initial state, and of `n`. -/
theorem expectedTrainedCalibrationSlope_historyEventKernel (ℓ₀ : Locus)
    (hap₀ : FullHaplotype Locus Allele)
    (events : List ((NeutralRates Deme Locus Allele × ℝ≥0) ⊕ PulseMatrix Deme))
    (x0 : FrequencyState Deme Locus Allele) (source target : Deme) {size : ℕ} (hsize : 2 ≤ size)
    (genotype : FullHaplotype Locus Allele → J → ℝ) (outcome : FullHaplotype Locus Allele → ℝ) :
    expectedTrainedCalibrationSlope (historyEventKernel ℓ₀ hap₀ events) x0 source target size
        genotype outcome
      = momentTrainedCalibrationSlope ℓ₀ 6 source target genotype outcome size
          (historyEventPropagator (fun _ ↦ 6) events *ᵥ budgetMomentFeature (fun _ ↦ 6) x0) := by
  haveI := isMarkovKernel_historyEventKernel ℓ₀ hap₀ events
  exact expectedTrainedCalibrationSlope_eq_momentTrainedCalibrationSlope ℓ₀
    (historyEventKernel ℓ₀ hap₀ events) (historyEventPropagator (fun _ ↦ 6) events)
    (integral_momentPolynomial_historyEventKernel ℓ₀ hap₀ (fun _ ↦ 6) events) le_rfl x0 source
    target hsize genotype outcome

/-- **The trained calibration intercept along a history** is the rational function
`momentTrainedCalibrationIntercept` of the propagated budget-7 moments and of `n`. -/
theorem expectedTrainedCalibrationIntercept_historyEventKernel (ℓ₀ : Locus)
    (hap₀ : FullHaplotype Locus Allele)
    (events : List ((NeutralRates Deme Locus Allele × ℝ≥0) ⊕ PulseMatrix Deme))
    (x0 : FrequencyState Deme Locus Allele) (source target : Deme) {size : ℕ} (hsize : 2 ≤ size)
    (genotype : FullHaplotype Locus Allele → J → ℝ) (outcome : FullHaplotype Locus Allele → ℝ) :
    expectedTrainedCalibrationIntercept (historyEventKernel ℓ₀ hap₀ events) x0 source target size
        genotype outcome
      = momentTrainedCalibrationIntercept ℓ₀ 7 source target genotype outcome size
          (historyEventPropagator (fun _ ↦ 7) events *ᵥ budgetMomentFeature (fun _ ↦ 7) x0) := by
  haveI := isMarkovKernel_historyEventKernel ℓ₀ hap₀ events
  exact expectedTrainedCalibrationIntercept_eq_momentTrainedCalibrationIntercept ℓ₀
    (historyEventKernel ℓ₀ hap₀ events) (historyEventPropagator (fun _ ↦ 7) events)
    (integral_momentPolynomial_historyEventKernel ℓ₀ hap₀ (fun _ ↦ 7) events) le_rfl x0 source
    target hsize genotype outcome

/-- **The trained slope sees the history only through finitely many moments.**  Two histories,
from two initial states, whose propagated budget-6 moments agree give equal trained calibration
slope of expectations for every cohort size, tag set, outcome, source and target. -/
theorem expectedTrainedCalibrationSlope_eq_of_moments_eq (ℓ₀ : Locus)
    (hap₀ : FullHaplotype Locus Allele)
    {first second : List ((NeutralRates Deme Locus Allele × ℝ≥0) ⊕ PulseMatrix Deme)}
    {x₁ x₂ : FrequencyState Deme Locus Allele}
    (hmoments : historyEventPropagator (fun _ ↦ 6) first *ᵥ budgetMomentFeature (fun _ ↦ 6) x₁
      = historyEventPropagator (fun _ ↦ 6) second *ᵥ budgetMomentFeature (fun _ ↦ 6) x₂)
    (source target : Deme) {size : ℕ} (hsize : 2 ≤ size)
    (genotype : FullHaplotype Locus Allele → J → ℝ) (outcome : FullHaplotype Locus Allele → ℝ) :
    expectedTrainedCalibrationSlope (historyEventKernel ℓ₀ hap₀ first) x₁ source target size
        genotype outcome
      = expectedTrainedCalibrationSlope (historyEventKernel ℓ₀ hap₀ second) x₂ source target size
          genotype outcome := by
  rw [expectedTrainedCalibrationSlope_historyEventKernel ℓ₀ hap₀ first x₁ source target hsize,
    expectedTrainedCalibrationSlope_historyEventKernel ℓ₀ hap₀ second x₂ source target hsize,
    hmoments]

/-- **The trained intercept sees the history only through finitely many moments**: the propagated
budget-7 moments. -/
theorem expectedTrainedCalibrationIntercept_eq_of_moments_eq (ℓ₀ : Locus)
    (hap₀ : FullHaplotype Locus Allele)
    {first second : List ((NeutralRates Deme Locus Allele × ℝ≥0) ⊕ PulseMatrix Deme)}
    {x₁ x₂ : FrequencyState Deme Locus Allele}
    (hmoments : historyEventPropagator (fun _ ↦ 7) first *ᵥ budgetMomentFeature (fun _ ↦ 7) x₁
      = historyEventPropagator (fun _ ↦ 7) second *ᵥ budgetMomentFeature (fun _ ↦ 7) x₂)
    (source target : Deme) {size : ℕ} (hsize : 2 ≤ size)
    (genotype : FullHaplotype Locus Allele → J → ℝ) (outcome : FullHaplotype Locus Allele → ℝ) :
    expectedTrainedCalibrationIntercept (historyEventKernel ℓ₀ hap₀ first) x₁ source target size
        genotype outcome
      = expectedTrainedCalibrationIntercept (historyEventKernel ℓ₀ hap₀ second) x₂ source target
          size genotype outcome := by
  rw [expectedTrainedCalibrationIntercept_historyEventKernel ℓ₀ hap₀ first x₁ source target hsize,
    expectedTrainedCalibrationIntercept_historyEventKernel ℓ₀ hap₀ second x₂ source target hsize,
    hmoments]

/-- **Along a history the trained slope of expectations rises with the cohort size** when the
expected target variance of the population marginal score is positive and its expected target
covariance with the outcome is nonnegative. -/
theorem expectedTrainedCalibrationSlope_historyEventKernel_monotone (ℓ₀ : Locus)
    (hap₀ : FullHaplotype Locus Allele)
    (events : List ((NeutralRates Deme Locus Allele × ℝ≥0) ⊕ PulseMatrix Deme))
    (x0 : FrequencyState Deme Locus Allele) (source target : Deme) {small large : ℕ}
    (hsmall : 2 ≤ small) (hle : small ≤ large)
    (genotype : FullHaplotype Locus Allele → J → ℝ) (outcome : FullHaplotype Locus Allele → ℝ)
    (hpopulation : 0 < ∫ y, (stateLaw y target).variance
      (linearScore genotype (marginalWeights (stateLaw y source) genotype outcome))
      ∂(historyEventKernel ℓ₀ hap₀ events x0))
    (hcovariance : 0 ≤ ∫ y, (stateLaw y target).covariance
      (linearScore genotype (marginalWeights (stateLaw y source) genotype outcome)) outcome
      ∂(historyEventKernel ℓ₀ hap₀ events x0)) :
    expectedTrainedCalibrationSlope (historyEventKernel ℓ₀ hap₀ events) x0 source target small
        genotype outcome
      ≤ expectedTrainedCalibrationSlope (historyEventKernel ℓ₀ hap₀ events) x0 source target
          large genotype outcome := by
  haveI := isMarkovKernel_historyEventKernel ℓ₀ hap₀ events
  exact expectedTrainedCalibrationSlope_monotone ℓ₀ (historyEventKernel ℓ₀ hap₀ events)
    (historyEventPropagator (fun _ ↦ 6) events)
    (integral_momentPolynomial_historyEventKernel ℓ₀ hap₀ (fun _ ↦ 6) events) le_rfl x0 source
    target hsmall hle genotype outcome hpopulation hcovariance

/-! ## The law along a time-varying rate history -/

/-- **The trained calibration slope along a rate history** is the rational function
`momentTrainedCalibrationSlope` of the propagator of the rate history applied to the budget-6
moments of the initial state, and of the cohort size. -/
theorem expectedTrainedCalibrationSlope_rateHistoryKernel
    {rates : ℝ → NeutralRates Deme Locus Allele} {T : ℝ} (hT : 0 ≤ T)
    (hcontinuous : ∀ capacity : Locus → ℕ,
      ContinuousOn (fun t ↦ dualGenerator (rates t) capacity) (Set.Icc 0 T))
    (ℓ₀ : Locus) (hap₀ : FullHaplotype Locus Allele) (x0 : FrequencyState Deme Locus Allele)
    (source target : Deme) {size : ℕ} (hsize : 2 ≤ size)
    (genotype : FullHaplotype Locus Allele → J → ℝ) (outcome : FullHaplotype Locus Allele → ℝ) :
    expectedTrainedCalibrationSlope (rateHistoryKernel rates ℓ₀ hap₀ hT hcontinuous) x0 source
        target size genotype outcome
      = momentTrainedCalibrationSlope ℓ₀ 6 source target genotype outcome size
          (rateHistoryDualPropagator rates (fun _ ↦ 6) T
            *ᵥ budgetMomentFeature (fun _ ↦ 6) x0) := by
  haveI := isMarkovKernel_rateHistoryKernel hT hcontinuous ℓ₀ hap₀
  exact expectedTrainedCalibrationSlope_eq_momentTrainedCalibrationSlope ℓ₀
    (rateHistoryKernel rates ℓ₀ hap₀ hT hcontinuous) (rateHistoryDualPropagator rates (fun _ ↦ 6) T)
    (integral_momentPolynomial_rateHistoryKernel hT hcontinuous ℓ₀ hap₀ (fun _ ↦ 6)) le_rfl x0
    source target hsize genotype outcome

/-- **The trained calibration intercept along a rate history** is the rational function
`momentTrainedCalibrationIntercept` of the propagated budget-7 moments and of the cohort size. -/
theorem expectedTrainedCalibrationIntercept_rateHistoryKernel
    {rates : ℝ → NeutralRates Deme Locus Allele} {T : ℝ} (hT : 0 ≤ T)
    (hcontinuous : ∀ capacity : Locus → ℕ,
      ContinuousOn (fun t ↦ dualGenerator (rates t) capacity) (Set.Icc 0 T))
    (ℓ₀ : Locus) (hap₀ : FullHaplotype Locus Allele) (x0 : FrequencyState Deme Locus Allele)
    (source target : Deme) {size : ℕ} (hsize : 2 ≤ size)
    (genotype : FullHaplotype Locus Allele → J → ℝ) (outcome : FullHaplotype Locus Allele → ℝ) :
    expectedTrainedCalibrationIntercept (rateHistoryKernel rates ℓ₀ hap₀ hT hcontinuous) x0 source
        target size genotype outcome
      = momentTrainedCalibrationIntercept ℓ₀ 7 source target genotype outcome size
          (rateHistoryDualPropagator rates (fun _ ↦ 7) T
            *ᵥ budgetMomentFeature (fun _ ↦ 7) x0) := by
  haveI := isMarkovKernel_rateHistoryKernel hT hcontinuous ℓ₀ hap₀
  exact expectedTrainedCalibrationIntercept_eq_momentTrainedCalibrationIntercept ℓ₀
    (rateHistoryKernel rates ℓ₀ hap₀ hT hcontinuous) (rateHistoryDualPropagator rates (fun _ ↦ 7) T)
    (integral_momentPolynomial_rateHistoryKernel hT hcontinuous ℓ₀ hap₀ (fun _ ↦ 7)) le_rfl x0
    source target hsize genotype outcome

end Histories

end

end Descent.Portability.EndToEndGWASCalibrationLaw
