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

end

end Descent.Portability.EndToEndGWASCalibrationLaw
