/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.EndToEndDiploidHistoryLaw
import Descent.Portability.EndToEndGWASTrainingLaw

assert_below Descent.Decision Descent.Program

/-!
# The exact accuracy of a GWAS-trained score along a demographic history

`EndToEndGWASTrainingLaw` gives the exact accuracy of a score trained by a finite-sample GWAS in a
source law and deployed in a target law.  This module composes it with a demographic history.

The composition.  A neutral history runs from a frequency state `x₀`: a list of epochs, splits and
admixture pulses (`historyEventKernel`), or a rate path with continuous dual generator
(`rateHistoryKernel`).  At the end of the history the populations are random.  A cohort of `n`
haplotypes is drawn from the source deme of the realised population, the marginal-effect GWAS is
run on it, and the score is deployed in the target deme of the same population.  The query is the
ratio of expectations of NOTE2 §6.2 over the history and the cohort together: the expected target
correlation numerator over the expected denominator (`expectedTrainedAccuracy`).

The polynomials.  The product, excess and pairing matrices of the source are polynomials of total
degree at most four in the source frequencies (`weightProductPolynomial`,
`weightExcessPolynomial`, `weightPairingPolynomial`, with their `eval_` and `totalDegree_`
lemmas).  The fourth co-moment enters through the corpus pair polynomial of two pair kernels
(`fourthCoMomentPolynomial`, `eval_fourthCoMomentPolynomial`).  The target matrices have degree at
most four in the target frequencies (`numeratorMatrixPolynomial`, `denominatorMatrixPolynomial`),
so every accumulator is a frequency polynomial of total degree at most eight in the two demes
jointly (`trainedPolynomial`, `totalDegree_trainedPolynomial_le`).

The law.
* The expected GWAS weights of a history are budget-2 dot products, and their second moments are
  sampling forms of budget-4 dot products (`integral_expectation_gwasWeights_historyEventKernel`,
  `integral_expectation_gwasWeights_mul_historyEventKernel`).
* The expected numerator and denominator are sampling forms `a·v + b·v / n + c·v / (n (n − 1))`
  with written-out coefficient vectors, where `v = U · H₈(x₀)` are the propagated budget-8 moments
  (`integral_trainedNumerator_historyEventKernel`,
  `integral_trainedDenominator_historyEventKernel`).
* The expected trained accuracy is the rational function `momentTrainedAccuracy` of `v` and `n`
  (`expectedTrainedAccuracy_historyEventKernel`, `expectedTrainedAccuracy_rateHistoryKernel`).
* Two histories with equal propagated budget-8 moments give equal trained accuracy for every
  cohort size, tag set, outcome, source and target (`expectedTrainedAccuracy_eq_of_moments_eq`).
* Both expected accumulators decrease in `n` (`integral_trainedNumerator_antitone`,
  `integral_trainedDenominator_antitone`).  As `n → ∞` the trained accuracy tends to the ratio of
  expectations of the population marginal score of each population
  (`tendsto_momentTrainedAccuracy`, `tendsto_expectedTrainedAccuracy_historyEventKernel`).

The budget is eight, not six.  The numerator reads a degree-4 source quantity against the degree-4
target product `16 c_i c_j`, and the denominator reads it against `16 C_t(X_i, X_j) V_t(Y)`, also
of degree four.

Scope.  Haploid individuals drawn from the deme haplotype law, one training cohort per population,
the ratio-of-expectations query, and outcomes that are functions of the haplotype.  The gamete-pair
law of `EndToEndDiploidLaw` is a finite law, so `EndToEndGWASTrainingLaw` applies to it verbatim,
but its composition with a history doubles every degree and needs budget sixteen, which is not
stated here.

## Empirical status

None.  The bodies are integrals of polynomials against Markov kernels and finite-sum identities, so
no measurement can bear on them.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.EndToEndGWASTrainingHistory

open MeasureTheory ProbabilityTheory MvPolynomial Filter Topology Descent.Coalescent
  PartialHaplotypeCarrier PartialHaplotypeDualGenerator PartialHaplotypeDualSemigroup
  NeutralFellerGenerator NeutralPolynomialSemigroup PartialHaplotypeMicroscopicApproximation
  PartialHaplotypePulseKernel NeutralPulseHistoryKernel NeutralRateHistoryRealization
  NeutralRateHistoryKernel ReplicaMetricInstances EndToEndPortabilityLaw EndToEndDiploidHistoryLaw
  TrainingNoiseAccuracy FourCellCohortLaw EndToEndGWASTrainingLaw
open scoped Matrix NNReal

noncomputable section

/-! ## Source and target matrices as polynomials -/

section Polynomials

variable {H : Type*} [Fintype H]

/-- **The fourth co-moment polynomial**: twice the pair polynomial of the product of two pair
kernels, minus the three pairings. -/
def fourthCoMomentPolynomial (first second third fourth : H → ℝ) : MvPolynomial H ℝ :=
  C 2 * pairPolynomial (fun a b ↦ (first a - first b) * (second a - second b) / 2
      * ((third a - third b) * (fourth a - fourth b) / 2))
    - covariancePolynomial first second * covariancePolynomial third fourth
    - covariancePolynomial first third * covariancePolynomial second fourth
    - covariancePolynomial first fourth * covariancePolynomial second third

/-- The fourth co-moment polynomial evaluates to the fourth central co-moment. -/
theorem eval_fourthCoMomentPolynomial (law : FiniteReportLaw H)
    (first second third fourth : H → ℝ) :
    eval law.mass (fourthCoMomentPolynomial first second third fourth)
      = fourthCoMoment law first second third fourth := by
  rw [fourthCoMoment_eq_pairExpectation, fourthCoMomentPolynomial]
  simp only [map_sub, map_mul, eval_C, eval_pairPolynomial, eval_covariancePolynomial]

/-- The fourth co-moment polynomial has total degree at most four. -/
theorem totalDegree_fourthCoMomentPolynomial_le (first second third fourth : H → ℝ) :
    (fourthCoMomentPolynomial first second third fourth).totalDegree ≤ 4 := by
  have hpair := totalDegree_pairPolynomial_le fun a b ↦
    (first a - first b) * (second a - second b) / 2
      * ((third a - third b) * (fourth a - fourth b) / 2)
  have h12 := totalDegree_covariancePolynomial_le first second
  have h34 := totalDegree_covariancePolynomial_le third fourth
  have h13 := totalDegree_covariancePolynomial_le first third
  have h24 := totalDegree_covariancePolynomial_le second fourth
  have h14 := totalDegree_covariancePolynomial_le first fourth
  have h23 := totalDegree_covariancePolynomial_le second third
  refine (totalDegree_sub _ _).trans (max_le ((totalDegree_sub _ _).trans
    (max_le ((totalDegree_sub _ _).trans (max_le ?_ ?_)) ?_)) ?_)
  · refine (totalDegree_mul _ _).trans ?_
    rw [totalDegree_C]
    omega
  · exact (totalDegree_mul _ _).trans (by omega)
  · exact (totalDegree_mul _ _).trans (by omega)
  · exact (totalDegree_mul _ _).trans (by omega)

variable {J : Type*}

/-- The product matrix `w_i w_j` of the population marginal effects, as polynomials. -/
def weightProductPolynomial (genotype : H → J → ℝ) (outcome : H → ℝ) (i j : J) :
    MvPolynomial H ℝ :=
  covariancePolynomial (fun individual ↦ genotype individual i) outcome
    * covariancePolynomial (fun individual ↦ genotype individual j) outcome

/-- The excess matrix `E_ij = K(X_i, Y, X_j, Y) − w_i w_j`, as polynomials. -/
def weightExcessPolynomial (genotype : H → J → ℝ) (outcome : H → ℝ) (i j : J) :
    MvPolynomial H ℝ :=
  fourthCoMomentPolynomial (fun individual ↦ genotype individual i) outcome
      (fun individual ↦ genotype individual j) outcome
    - weightProductPolynomial genotype outcome i j

/-- The pairing matrix `P_ij = C(X_i, X_j) V_Y + w_i w_j`, as polynomials. -/
def weightPairingPolynomial (genotype : H → J → ℝ) (outcome : H → ℝ) (i j : J) :
    MvPolynomial H ℝ :=
  covariancePolynomial (fun individual ↦ genotype individual i)
      (fun individual ↦ genotype individual j) * covariancePolynomial outcome outcome
    + weightProductPolynomial genotype outcome i j

/-- The numerator target matrix `16 c_i c_j`, as polynomials. -/
def numeratorMatrixPolynomial (genotype : H → J → ℝ) (outcome : H → ℝ) (i j : J) :
    MvPolynomial H ℝ :=
  C 16 * weightProductPolynomial genotype outcome i j

/-- The denominator target matrix `16 C(X_i, X_j) V_Y`, as polynomials. -/
def denominatorMatrixPolynomial (genotype : H → J → ℝ) (outcome : H → ℝ) (i j : J) :
    MvPolynomial H ℝ :=
  C 16 * (covariancePolynomial (fun individual ↦ genotype individual i)
    (fun individual ↦ genotype individual j) * covariancePolynomial outcome outcome)

/-- The product matrix polynomial evaluates to the product of the marginal effects. -/
theorem eval_weightProductPolynomial (law : FiniteReportLaw H) (genotype : H → J → ℝ)
    (outcome : H → ℝ) (i j : J) :
    eval law.mass (weightProductPolynomial genotype outcome i j)
      = marginalWeights law genotype outcome i * marginalWeights law genotype outcome j := by
  rw [weightProductPolynomial, map_mul, eval_covariancePolynomial, eval_covariancePolynomial]
  rfl

/-- The excess matrix polynomial evaluates to the excess matrix. -/
theorem eval_weightExcessPolynomial (law : FiniteReportLaw H) (genotype : H → J → ℝ)
    (outcome : H → ℝ) (i j : J) :
    eval law.mass (weightExcessPolynomial genotype outcome i j)
      = weightExcess law genotype outcome i j := by
  rw [weightExcessPolynomial, map_sub, eval_fourthCoMomentPolynomial,
    eval_weightProductPolynomial]
  rfl

/-- The pairing matrix polynomial evaluates to the pairing matrix. -/
theorem eval_weightPairingPolynomial (law : FiniteReportLaw H) (genotype : H → J → ℝ)
    (outcome : H → ℝ) (i j : J) :
    eval law.mass (weightPairingPolynomial genotype outcome i j)
      = weightPairing law genotype outcome i j := by
  rw [weightPairingPolynomial, map_add, map_mul, eval_covariancePolynomial,
    eval_covariancePolynomial, eval_weightProductPolynomial]
  rfl

/-- The numerator target matrix polynomial evaluates to the numerator matrix. -/
theorem eval_numeratorMatrixPolynomial (law : FiniteReportLaw H) (genotype : H → J → ℝ)
    (outcome : H → ℝ) (i j : J) :
    eval law.mass (numeratorMatrixPolynomial genotype outcome i j)
      = numeratorMatrix law genotype outcome i j := by
  rw [numeratorMatrixPolynomial, map_mul, eval_C, eval_weightProductPolynomial]
  rfl

/-- The denominator target matrix polynomial evaluates to the denominator matrix. -/
theorem eval_denominatorMatrixPolynomial (law : FiniteReportLaw H) (genotype : H → J → ℝ)
    (outcome : H → ℝ) (i j : J) :
    eval law.mass (denominatorMatrixPolynomial genotype outcome i j)
      = denominatorMatrix law genotype outcome i j := by
  rw [denominatorMatrixPolynomial, map_mul, map_mul, eval_C, eval_covariancePolynomial,
    eval_covariancePolynomial]
  rfl

/-- The product matrix polynomial has total degree at most four. -/
theorem totalDegree_weightProductPolynomial_le (genotype : H → J → ℝ) (outcome : H → ℝ)
    (i j : J) : (weightProductPolynomial genotype outcome i j).totalDegree ≤ 4 := by
  have hi := totalDegree_covariancePolynomial_le (fun individual ↦ genotype individual i) outcome
  have hj := totalDegree_covariancePolynomial_le (fun individual ↦ genotype individual j) outcome
  exact (totalDegree_mul _ _).trans (by omega)

/-- The excess matrix polynomial has total degree at most four. -/
theorem totalDegree_weightExcessPolynomial_le (genotype : H → J → ℝ) (outcome : H → ℝ)
    (i j : J) : (weightExcessPolynomial genotype outcome i j).totalDegree ≤ 4 :=
  (totalDegree_sub _ _).trans (max_le (totalDegree_fourthCoMomentPolynomial_le _ _ _ _)
    (totalDegree_weightProductPolynomial_le genotype outcome i j))

/-- The pairing matrix polynomial has total degree at most four. -/
theorem totalDegree_weightPairingPolynomial_le (genotype : H → J → ℝ) (outcome : H → ℝ)
    (i j : J) : (weightPairingPolynomial genotype outcome i j).totalDegree ≤ 4 := by
  have hij := totalDegree_covariancePolynomial_le (fun individual ↦ genotype individual i)
    (fun individual ↦ genotype individual j)
  have houtcome := totalDegree_covariancePolynomial_le outcome outcome
  refine (totalDegree_add _ _).trans
    (max_le ?_ (totalDegree_weightProductPolynomial_le genotype outcome i j))
  exact (totalDegree_mul _ _).trans (by omega)

/-- The numerator target matrix polynomial has total degree at most four. -/
theorem totalDegree_numeratorMatrixPolynomial_le (genotype : H → J → ℝ) (outcome : H → ℝ)
    (i j : J) : (numeratorMatrixPolynomial genotype outcome i j).totalDegree ≤ 4 := by
  refine (totalDegree_mul _ _).trans ?_
  rw [totalDegree_C, zero_add]
  exact totalDegree_weightProductPolynomial_le genotype outcome i j

/-- The denominator target matrix polynomial has total degree at most four. -/
theorem totalDegree_denominatorMatrixPolynomial_le (genotype : H → J → ℝ) (outcome : H → ℝ)
    (i j : J) : (denominatorMatrixPolynomial genotype outcome i j).totalDegree ≤ 4 := by
  have hij := totalDegree_covariancePolynomial_le (fun individual ↦ genotype individual i)
    (fun individual ↦ genotype individual j)
  have houtcome := totalDegree_covariancePolynomial_le outcome outcome
  refine (totalDegree_mul _ _).trans ?_
  rw [totalDegree_C, zero_add]
  exact (totalDegree_mul _ _).trans (by omega)

end Polynomials

/-! ## The accumulators as frequency polynomials of two demes -/

variable {Deme Locus : Type*} {Allele : Locus → Type*}
variable [Fintype Deme] [DecidableEq Deme] [Fintype Locus] [DecidableEq Locus]
  [∀ ℓ, Fintype (Allele ℓ)] [∀ ℓ, DecidableEq (Allele ℓ)]

section Accumulators

variable {J : Type*} [Fintype J]

/-- **The trained accumulator polynomial**: a source matrix of polynomials read against a target
matrix of polynomials, as a frequency polynomial of the two demes. -/
def trainedPolynomial (source target : Deme)
    (sourceMatrix targetMatrix : J → J → MvPolynomial (FullHaplotype Locus Allele) ℝ) :
    FrequencyPolynomial Deme Locus Allele :=
  ∑ i, ∑ j, demePolynomial target (targetMatrix i j) * demePolynomial source (sourceMatrix i j)

/-- At a state, the trained polynomial reads the target matrix at the target deme's law against
the source matrix at the source deme's law. -/
theorem polynomialFunction_trainedPolynomial (source target : Deme)
    (sourceMatrix targetMatrix : J → J → MvPolynomial (FullHaplotype Locus Allele) ℝ)
    (y : FrequencyState Deme Locus Allele) :
    polynomialFunction (trainedPolynomial source target sourceMatrix targetMatrix) y
      = ∑ i, ∑ j, eval (stateLaw y target).mass (targetMatrix i j)
          * eval (stateLaw y source).mass (sourceMatrix i j) := by
  simp only [polynomialFunction_apply, trainedPolynomial, map_sum, map_mul, eval_demePolynomial]

/-- **The trained polynomial has total degree at most eight** when both matrices have degree at
most four. -/
theorem totalDegree_trainedPolynomial_le (source target : Deme)
    (sourceMatrix targetMatrix : J → J → MvPolynomial (FullHaplotype Locus Allele) ℝ)
    (hsource : ∀ i j, (sourceMatrix i j).totalDegree ≤ 4)
    (htarget : ∀ i j, (targetMatrix i j).totalDegree ≤ 4) :
    (trainedPolynomial source target sourceMatrix targetMatrix).totalDegree ≤ 8 := by
  refine (totalDegree_finset_sum _ _).trans (Finset.sup_le fun i _ ↦ ?_)
  refine (totalDegree_finset_sum _ _).trans (Finset.sup_le fun j _ ↦ ?_)
  have htargetDeme : (demePolynomial target (targetMatrix i j)).totalDegree ≤ 4 :=
    (totalDegree_rename_le _ _).trans (htarget i j)
  have hsourceDeme : (demePolynomial source (sourceMatrix i j)).totalDegree ≤ 4 :=
    (totalDegree_rename_le _ _).trans (hsource i j)
  exact (totalDegree_mul _ _).trans (by omega)

/-- At a state, the product polynomial read against the numerator matrix is the target numerator
of the population marginal score of the source deme. -/
theorem polynomialFunction_populationNumerator (source target : Deme)
    (genotype : FullHaplotype Locus Allele → J → ℝ) (outcome : FullHaplotype Locus Allele → ℝ)
    (y : FrequencyState Deme Locus Allele) :
    polynomialFunction (trainedPolynomial source target (weightProductPolynomial genotype outcome)
        (numeratorMatrixPolynomial genotype outcome)) y
      = correlationNumerator (stateLaw y target)
          (linearScore genotype (marginalWeights (stateLaw y source) genotype outcome))
          outcome := by
  rw [correlationNumerator_linearScore]
  simp only [polynomialFunction_trainedPolynomial, eval_weightProductPolynomial,
    eval_numeratorMatrixPolynomial]

/-- At a state, the product polynomial read against the denominator matrix is the target
denominator of the population marginal score of the source deme. -/
theorem polynomialFunction_populationDenominator (source target : Deme)
    (genotype : FullHaplotype Locus Allele → J → ℝ) (outcome : FullHaplotype Locus Allele → ℝ)
    (y : FrequencyState Deme Locus Allele) :
    polynomialFunction (trainedPolynomial source target (weightProductPolynomial genotype outcome)
        (denominatorMatrixPolynomial genotype outcome)) y
      = correlationDenominator (stateLaw y target)
          (linearScore genotype (marginalWeights (stateLaw y source) genotype outcome))
          outcome := by
  rw [correlationDenominator_linearScore]
  simp only [polynomialFunction_trainedPolynomial, eval_weightProductPolynomial,
    eval_denominatorMatrixPolynomial]

/-- **At a state, the trained numerator is a sampling form of three polynomial observables** of
total degree at most eight. -/
theorem trainedNumerator_stateLaw (source target : Deme) {size : ℕ} (hsize : 2 ≤ size)
    (genotype : FullHaplotype Locus Allele → J → ℝ) (outcome : FullHaplotype Locus Allele → ℝ)
    (y : FrequencyState Deme Locus Allele) :
    trainedNumerator (stateLaw y source) (stateLaw y target) size genotype outcome
      = samplingForm
          (polynomialFunction (trainedPolynomial source target
            (weightProductPolynomial genotype outcome)
            (numeratorMatrixPolynomial genotype outcome)) y)
          (polynomialFunction (trainedPolynomial source target
            (weightExcessPolynomial genotype outcome)
            (numeratorMatrixPolynomial genotype outcome)) y)
          (polynomialFunction (trainedPolynomial source target
            (weightPairingPolynomial genotype outcome)
            (numeratorMatrixPolynomial genotype outcome)) y) size := by
  rw [trainedNumerator_eq _ _ hsize, correlationNumerator_linearScore]
  simp only [polynomialFunction_trainedPolynomial, eval_weightProductPolynomial,
    eval_weightExcessPolynomial, eval_weightPairingPolynomial, eval_numeratorMatrixPolynomial]

/-- **At a state, the trained denominator is a sampling form of three polynomial observables** of
total degree at most eight. -/
theorem trainedDenominator_stateLaw (source target : Deme) {size : ℕ} (hsize : 2 ≤ size)
    (genotype : FullHaplotype Locus Allele → J → ℝ) (outcome : FullHaplotype Locus Allele → ℝ)
    (y : FrequencyState Deme Locus Allele) :
    trainedDenominator (stateLaw y source) (stateLaw y target) size genotype outcome
      = samplingForm
          (polynomialFunction (trainedPolynomial source target
            (weightProductPolynomial genotype outcome)
            (denominatorMatrixPolynomial genotype outcome)) y)
          (polynomialFunction (trainedPolynomial source target
            (weightExcessPolynomial genotype outcome)
            (denominatorMatrixPolynomial genotype outcome)) y)
          (polynomialFunction (trainedPolynomial source target
            (weightPairingPolynomial genotype outcome)
            (denominatorMatrixPolynomial genotype outcome)) y) size := by
  rw [trainedDenominator_eq _ _ hsize, correlationDenominator_linearScore]
  simp only [polynomialFunction_trainedPolynomial, eval_weightProductPolynomial,
    eval_weightExcessPolynomial, eval_weightPairingPolynomial, eval_denominatorMatrixPolynomial]

/-- The expected trained numerator is integrable under every Markov kernel. -/
theorem integrable_trainedNumerator
    (κ : Kernel (FrequencyState Deme Locus Allele) (FrequencyState Deme Locus Allele))
    [IsMarkovKernel κ] (x0 : FrequencyState Deme Locus Allele) (source target : Deme)
    {size : ℕ} (hsize : 2 ≤ size) (genotype : FullHaplotype Locus Allele → J → ℝ)
    (outcome : FullHaplotype Locus Allele → ℝ) :
    Integrable (fun y ↦ trainedNumerator (stateLaw y source) (stateLaw y target) size genotype
      outcome) (κ x0) := by
  have hcontinuous : Continuous fun y ↦
      trainedNumerator (stateLaw y source) (stateLaw y target) size genotype outcome := by
    simp only [trainedNumerator_stateLaw source target hsize genotype outcome, samplingForm]
    exact ((polynomialFunction _).continuous.add
      ((polynomialFunction _).continuous.div_const _)).add
        ((polynomialFunction _).continuous.div_const _)
  exact (BoundedContinuousFunction.mkOfCompact ⟨_, hcontinuous⟩).integrable _

/-- The expected trained denominator is integrable under every Markov kernel. -/
theorem integrable_trainedDenominator
    (κ : Kernel (FrequencyState Deme Locus Allele) (FrequencyState Deme Locus Allele))
    [IsMarkovKernel κ] (x0 : FrequencyState Deme Locus Allele) (source target : Deme)
    {size : ℕ} (hsize : 2 ≤ size) (genotype : FullHaplotype Locus Allele → J → ℝ)
    (outcome : FullHaplotype Locus Allele → ℝ) :
    Integrable (fun y ↦ trainedDenominator (stateLaw y source) (stateLaw y target) size genotype
      outcome) (κ x0) := by
  have hcontinuous : Continuous fun y ↦
      trainedDenominator (stateLaw y source) (stateLaw y target) size genotype outcome := by
    simp only [trainedDenominator_stateLaw source target hsize genotype outcome, samplingForm]
    exact ((polynomialFunction _).continuous.add
      ((polynomialFunction _).continuous.div_const _)).add
        ((polynomialFunction _).continuous.div_const _)
  exact (BoundedContinuousFunction.mkOfCompact ⟨_, hcontinuous⟩).integrable _

/-- **The expected trained numerator of a kernel decreases in the cohort size.** -/
theorem integral_trainedNumerator_antitone
    (κ : Kernel (FrequencyState Deme Locus Allele) (FrequencyState Deme Locus Allele))
    [IsMarkovKernel κ] (x0 : FrequencyState Deme Locus Allele) (source target : Deme)
    {small large : ℕ} (hsmall : 2 ≤ small) (hle : small ≤ large)
    (genotype : FullHaplotype Locus Allele → J → ℝ) (outcome : FullHaplotype Locus Allele → ℝ) :
    ∫ y, trainedNumerator (stateLaw y source) (stateLaw y target) large genotype outcome ∂(κ x0)
      ≤ ∫ y, trainedNumerator (stateLaw y source) (stateLaw y target) small genotype outcome
          ∂(κ x0) :=
  integral_mono (integrable_trainedNumerator κ x0 source target (hsmall.trans hle) genotype outcome)
    (integrable_trainedNumerator κ x0 source target hsmall genotype outcome)
    fun _ ↦ trainedNumerator_antitone _ _ hsmall hle genotype outcome

/-- **The expected trained denominator of a kernel decreases in the cohort size.** -/
theorem integral_trainedDenominator_antitone
    (κ : Kernel (FrequencyState Deme Locus Allele) (FrequencyState Deme Locus Allele))
    [IsMarkovKernel κ] (x0 : FrequencyState Deme Locus Allele) (source target : Deme)
    {small large : ℕ} (hsmall : 2 ≤ small) (hle : small ≤ large)
    (genotype : FullHaplotype Locus Allele → J → ℝ) (outcome : FullHaplotype Locus Allele → ℝ) :
    ∫ y, trainedDenominator (stateLaw y source) (stateLaw y target) large genotype outcome ∂(κ x0)
      ≤ ∫ y, trainedDenominator (stateLaw y source) (stateLaw y target) small genotype outcome
          ∂(κ x0) :=
  integral_mono
    (integrable_trainedDenominator κ x0 source target (hsmall.trans hle) genotype outcome)
    (integrable_trainedDenominator κ x0 source target hsmall genotype outcome)
    fun _ ↦ trainedDenominator_antitone _ _ hsmall hle genotype outcome

/-- **The expected trained accuracy of a kernel**: the expected target numerator of the GWAS score
over its expected target denominator, the expectations taken over the populations of the kernel
and the training cohort drawn in the source deme of each.  NOTE2 §6.2 query: a ratio of
expectations. -/
def expectedTrainedAccuracy
    (κ : Kernel (FrequencyState Deme Locus Allele) (FrequencyState Deme Locus Allele))
    (x0 : FrequencyState Deme Locus Allele) (source target : Deme) (size : ℕ)
    (genotype : FullHaplotype Locus Allele → J → ℝ) (outcome : FullHaplotype Locus Allele → ℝ) :
    ℝ :=
  (∫ y, trainedNumerator (stateLaw y source) (stateLaw y target) size genotype outcome ∂(κ x0))
    / ∫ y, trainedDenominator (stateLaw y source) (stateLaw y target) size genotype outcome
        ∂(κ x0)

/-- **The rational trained accuracy** of a budget-`n` moment vector and a cohort size: a ratio of
two sampling forms with written-out coefficient vectors. -/
def momentTrainedAccuracy (ℓ₀ : Locus) (n : ℕ) (source target : Deme)
    (genotype : FullHaplotype Locus Allele → J → ℝ) (outcome : FullHaplotype Locus Allele → ℝ)
    (size : ℕ) (v : BudgetConfiguration Deme Locus Allele (fun _ ↦ n) → ℝ) : ℝ :=
  samplingForm
      (budgetCoefficients ℓ₀ (fun _ ↦ n) (trainedPolynomial source target
        (weightProductPolynomial genotype outcome) (numeratorMatrixPolynomial genotype outcome))
        ⬝ᵥ v)
      (budgetCoefficients ℓ₀ (fun _ ↦ n) (trainedPolynomial source target
        (weightExcessPolynomial genotype outcome) (numeratorMatrixPolynomial genotype outcome))
        ⬝ᵥ v)
      (budgetCoefficients ℓ₀ (fun _ ↦ n) (trainedPolynomial source target
        (weightPairingPolynomial genotype outcome) (numeratorMatrixPolynomial genotype outcome))
        ⬝ᵥ v) size
    / samplingForm
      (budgetCoefficients ℓ₀ (fun _ ↦ n) (trainedPolynomial source target
        (weightProductPolynomial genotype outcome) (denominatorMatrixPolynomial genotype outcome))
        ⬝ᵥ v)
      (budgetCoefficients ℓ₀ (fun _ ↦ n) (trainedPolynomial source target
        (weightExcessPolynomial genotype outcome) (denominatorMatrixPolynomial genotype outcome))
        ⬝ᵥ v)
      (budgetCoefficients ℓ₀ (fun _ ↦ n) (trainedPolynomial source target
        (weightPairingPolynomial genotype outcome) (denominatorMatrixPolynomial genotype outcome))
        ⬝ᵥ v) size

/-- **The rational trained accuracy tends to the population marginal-score ratio** as the cohort
grows, wherever the population denominator term is nonzero. -/
theorem tendsto_momentTrainedAccuracy (ℓ₀ : Locus) (n : ℕ) (source target : Deme)
    (genotype : FullHaplotype Locus Allele → J → ℝ) (outcome : FullHaplotype Locus Allele → ℝ)
    (v : BudgetConfiguration Deme Locus Allele (fun _ ↦ n) → ℝ)
    (hpopulation : budgetCoefficients ℓ₀ (fun _ ↦ n) (trainedPolynomial source target
      (weightProductPolynomial genotype outcome) (denominatorMatrixPolynomial genotype outcome))
        ⬝ᵥ v ≠ 0) :
    Tendsto (fun size : ℕ ↦ momentTrainedAccuracy ℓ₀ n source target genotype outcome size v)
      atTop (𝓝 ((budgetCoefficients ℓ₀ (fun _ ↦ n) (trainedPolynomial source target
          (weightProductPolynomial genotype outcome) (numeratorMatrixPolynomial genotype outcome))
          ⬝ᵥ v)
        / (budgetCoefficients ℓ₀ (fun _ ↦ n) (trainedPolynomial source target
          (weightProductPolynomial genotype outcome) (denominatorMatrixPolynomial genotype outcome))
          ⬝ᵥ v))) :=
  (tendsto_samplingForm _ _ _).div (tendsto_samplingForm _ _ _) hpopulation

/-! ## Integrating sampling forms against a kernel with the dual moments -/

section MomentKernel

variable (ℓ₀ : Locus) {n : ℕ}
  (κ : Kernel (FrequencyState Deme Locus Allele) (FrequencyState Deme Locus Allele))
  [IsMarkovKernel κ]
  (M : Matrix (BudgetConfiguration Deme Locus Allele (fun _ ↦ n))
    (BudgetConfiguration Deme Locus Allele (fun _ ↦ n)) ℝ)
  (hmoment : ∀ (x : FrequencyState Deme Locus Allele)
    (ξ : BudgetConfiguration Deme Locus Allele (fun _ ↦ n)),
    ∫ y, polynomialFunction (momentPolynomial ξ.1) y ∂(κ x)
      = (M *ᵥ budgetMomentFeature (fun _ ↦ n) x) ξ)

include hmoment

/-- **A sampling form of polynomial observables integrates through the moments.**  Under a Markov
kernel whose budget-`n` moments are `M`, a sampling form of three polynomial observables of degree
at most `n` integrates to the sampling form of their coefficient vectors dotted with the propagated
moments. -/
theorem integral_samplingForm_polynomialFunction (x0 : FrequencyState Deme Locus Allele)
    (size : ℕ) (population excess pairing : FrequencyPolynomial Deme Locus Allele)
    (hpopulation : population.totalDegree ≤ n) (hexcess : excess.totalDegree ≤ n)
    (hpairing : pairing.totalDegree ≤ n) :
    ∫ y, samplingForm (polynomialFunction population y) (polynomialFunction excess y)
        (polynomialFunction pairing y) size ∂(κ x0)
      = samplingForm
          (budgetCoefficients ℓ₀ (fun _ ↦ n) population
            ⬝ᵥ (M *ᵥ budgetMomentFeature (fun _ ↦ n) x0))
          (budgetCoefficients ℓ₀ (fun _ ↦ n) excess
            ⬝ᵥ (M *ᵥ budgetMomentFeature (fun _ ↦ n) x0))
          (budgetCoefficients ℓ₀ (fun _ ↦ n) pairing
            ⬝ᵥ (M *ᵥ budgetMomentFeature (fun _ ↦ n) x0)) size := by
  have hint : ∀ g : FrequencyState Deme Locus Allele → ℝ, Continuous g → Integrable g (κ x0) :=
    fun g hg ↦ (BoundedContinuousFunction.mkOfCompact ⟨g, hg⟩).integrable _
  have hA := (polynomialFunction population).continuous
  have hB := (polynomialFunction excess).continuous.div_const (size : ℝ)
  have hC := (polynomialFunction pairing).continuous.div_const ((size : ℝ) * ((size : ℝ) - 1))
  simp only [samplingForm]
  rw [integral_add (hint _ (hA.add hB)) (hint _ hC), integral_add (hint _ hA) (hint _ hB),
    integral_div, integral_div,
    integral_polynomial_eq_dotProduct ℓ₀ (fun _ ↦ n) κ M hmoment population
      (withinBudget_of_totalDegree_le ℓ₀ population hpopulation) x0,
    integral_polynomial_eq_dotProduct ℓ₀ (fun _ ↦ n) κ M hmoment excess
      (withinBudget_of_totalDegree_le ℓ₀ excess hexcess) x0,
    integral_polynomial_eq_dotProduct ℓ₀ (fun _ ↦ n) κ M hmoment pairing
      (withinBudget_of_totalDegree_le ℓ₀ pairing hpairing) x0]

/-- **The expected trained numerator under a kernel with budget-`n` moments**, `n ≥ 8`, is a
sampling form of coefficient vectors dotted with the propagated moments. -/
theorem integral_trainedNumerator_eq (hn : 8 ≤ n) (x0 : FrequencyState Deme Locus Allele)
    (source target : Deme) {size : ℕ} (hsize : 2 ≤ size)
    (genotype : FullHaplotype Locus Allele → J → ℝ) (outcome : FullHaplotype Locus Allele → ℝ) :
    ∫ y, trainedNumerator (stateLaw y source) (stateLaw y target) size genotype outcome ∂(κ x0)
      = samplingForm
          (budgetCoefficients ℓ₀ (fun _ ↦ n) (trainedPolynomial source target
              (weightProductPolynomial genotype outcome)
              (numeratorMatrixPolynomial genotype outcome))
            ⬝ᵥ (M *ᵥ budgetMomentFeature (fun _ ↦ n) x0))
          (budgetCoefficients ℓ₀ (fun _ ↦ n) (trainedPolynomial source target
              (weightExcessPolynomial genotype outcome)
              (numeratorMatrixPolynomial genotype outcome))
            ⬝ᵥ (M *ᵥ budgetMomentFeature (fun _ ↦ n) x0))
          (budgetCoefficients ℓ₀ (fun _ ↦ n) (trainedPolynomial source target
              (weightPairingPolynomial genotype outcome)
              (numeratorMatrixPolynomial genotype outcome))
            ⬝ᵥ (M *ᵥ budgetMomentFeature (fun _ ↦ n) x0)) size := by
  simp only [trainedNumerator_stateLaw source target hsize genotype outcome]
  exact integral_samplingForm_polynomialFunction ℓ₀ κ M hmoment x0 size _ _ _
    ((totalDegree_trainedPolynomial_le _ _ _ _
      (totalDegree_weightProductPolynomial_le genotype outcome)
      (totalDegree_numeratorMatrixPolynomial_le genotype outcome)).trans hn)
    ((totalDegree_trainedPolynomial_le _ _ _ _
      (totalDegree_weightExcessPolynomial_le genotype outcome)
      (totalDegree_numeratorMatrixPolynomial_le genotype outcome)).trans hn)
    ((totalDegree_trainedPolynomial_le _ _ _ _
      (totalDegree_weightPairingPolynomial_le genotype outcome)
      (totalDegree_numeratorMatrixPolynomial_le genotype outcome)).trans hn)

/-- **The expected trained denominator under a kernel with budget-`n` moments**, `n ≥ 8`, is a
sampling form of coefficient vectors dotted with the propagated moments. -/
theorem integral_trainedDenominator_eq (hn : 8 ≤ n) (x0 : FrequencyState Deme Locus Allele)
    (source target : Deme) {size : ℕ} (hsize : 2 ≤ size)
    (genotype : FullHaplotype Locus Allele → J → ℝ) (outcome : FullHaplotype Locus Allele → ℝ) :
    ∫ y, trainedDenominator (stateLaw y source) (stateLaw y target) size genotype outcome ∂(κ x0)
      = samplingForm
          (budgetCoefficients ℓ₀ (fun _ ↦ n) (trainedPolynomial source target
              (weightProductPolynomial genotype outcome)
              (denominatorMatrixPolynomial genotype outcome))
            ⬝ᵥ (M *ᵥ budgetMomentFeature (fun _ ↦ n) x0))
          (budgetCoefficients ℓ₀ (fun _ ↦ n) (trainedPolynomial source target
              (weightExcessPolynomial genotype outcome)
              (denominatorMatrixPolynomial genotype outcome))
            ⬝ᵥ (M *ᵥ budgetMomentFeature (fun _ ↦ n) x0))
          (budgetCoefficients ℓ₀ (fun _ ↦ n) (trainedPolynomial source target
              (weightPairingPolynomial genotype outcome)
              (denominatorMatrixPolynomial genotype outcome))
            ⬝ᵥ (M *ᵥ budgetMomentFeature (fun _ ↦ n) x0)) size := by
  simp only [trainedDenominator_stateLaw source target hsize genotype outcome]
  exact integral_samplingForm_polynomialFunction ℓ₀ κ M hmoment x0 size _ _ _
    ((totalDegree_trainedPolynomial_le _ _ _ _
      (totalDegree_weightProductPolynomial_le genotype outcome)
      (totalDegree_denominatorMatrixPolynomial_le genotype outcome)).trans hn)
    ((totalDegree_trainedPolynomial_le _ _ _ _
      (totalDegree_weightExcessPolynomial_le genotype outcome)
      (totalDegree_denominatorMatrixPolynomial_le genotype outcome)).trans hn)
    ((totalDegree_trainedPolynomial_le _ _ _ _
      (totalDegree_weightPairingPolynomial_le genotype outcome)
      (totalDegree_denominatorMatrixPolynomial_le genotype outcome)).trans hn)

/-- **The expected trained accuracy under a kernel with budget-`n` moments**, `n ≥ 8`, is the
rational trained accuracy of the propagated moments. -/
theorem expectedTrainedAccuracy_eq_momentTrainedAccuracy (hn : 8 ≤ n)
    (x0 : FrequencyState Deme Locus Allele) (source target : Deme) {size : ℕ} (hsize : 2 ≤ size)
    (genotype : FullHaplotype Locus Allele → J → ℝ) (outcome : FullHaplotype Locus Allele → ℝ) :
    expectedTrainedAccuracy κ x0 source target size genotype outcome
      = momentTrainedAccuracy ℓ₀ n source target genotype outcome size
          (M *ᵥ budgetMomentFeature (fun _ ↦ n) x0) := by
  rw [expectedTrainedAccuracy,
    integral_trainedNumerator_eq ℓ₀ κ M hmoment hn x0 source target hsize,
    integral_trainedDenominator_eq ℓ₀ κ M hmoment hn x0 source target hsize]
  rfl

end MomentKernel

/-! ## The law along a history of epochs, splits and pulses -/

/-- **The expected GWAS weights along a history** are budget-2 dot products: the coefficient
vectors of the source covariance polynomials dotted with the propagated budget-2 moments. -/
theorem integral_expectation_gwasWeights_historyEventKernel (ℓ₀ : Locus)
    (hap₀ : FullHaplotype Locus Allele)
    (events : List ((NeutralRates Deme Locus Allele × ℝ≥0) ⊕ PulseMatrix Deme))
    (x0 : FrequencyState Deme Locus Allele) (source : Deme) {size : ℕ} (hsize : 2 ≤ size)
    (genotype : FullHaplotype Locus Allele → J → ℝ) (outcome : FullHaplotype Locus Allele → ℝ)
    (marker : J) :
    ∫ y, (cohortLaw (stateLaw y source) size).expectation
        (fun sample ↦ gwasWeights genotype outcome sample marker)
        ∂(historyEventKernel ℓ₀ hap₀ events x0)
      = budgetCoefficients ℓ₀ (fun _ ↦ 2)
          (demePolynomial source
            (covariancePolynomial (fun individual ↦ genotype individual marker) outcome))
        ⬝ᵥ (historyEventPropagator (fun _ ↦ 2) events *ᵥ budgetMomentFeature (fun _ ↦ 2) x0) :=
  integral_historyEventKernel_of_totalDegree_le ℓ₀ hap₀ events x0
    (demePolynomial source
      (covariancePolynomial (fun individual ↦ genotype individual marker) outcome))
    ((totalDegree_rename_le _ _).trans (totalDegree_covariancePolynomial_le _ outcome)) _
    fun y ↦ by
      rw [polynomialFunction_apply, eval_demePolynomial, eval_covariancePolynomial]
      exact (expectation_gwasWeights _ hsize genotype outcome marker).symm

/-- **The second moments of the GWAS weights along a history** are sampling forms of budget-4 dot
products. -/
theorem integral_expectation_gwasWeights_mul_historyEventKernel (ℓ₀ : Locus)
    (hap₀ : FullHaplotype Locus Allele)
    (events : List ((NeutralRates Deme Locus Allele × ℝ≥0) ⊕ PulseMatrix Deme))
    (x0 : FrequencyState Deme Locus Allele) (source : Deme) {size : ℕ} (hsize : 2 ≤ size)
    (genotype : FullHaplotype Locus Allele → J → ℝ) (outcome : FullHaplotype Locus Allele → ℝ)
    (i j : J) :
    ∫ y, (cohortLaw (stateLaw y source) size).expectation
        (fun sample ↦ gwasWeights genotype outcome sample i * gwasWeights genotype outcome sample j)
        ∂(historyEventKernel ℓ₀ hap₀ events x0)
      = samplingForm
          (budgetCoefficients ℓ₀ (fun _ ↦ 4)
              (demePolynomial source (weightProductPolynomial genotype outcome i j))
            ⬝ᵥ (historyEventPropagator (fun _ ↦ 4) events *ᵥ budgetMomentFeature (fun _ ↦ 4) x0))
          (budgetCoefficients ℓ₀ (fun _ ↦ 4)
              (demePolynomial source (weightExcessPolynomial genotype outcome i j))
            ⬝ᵥ (historyEventPropagator (fun _ ↦ 4) events *ᵥ budgetMomentFeature (fun _ ↦ 4) x0))
          (budgetCoefficients ℓ₀ (fun _ ↦ 4)
              (demePolynomial source (weightPairingPolynomial genotype outcome i j))
            ⬝ᵥ (historyEventPropagator (fun _ ↦ 4) events *ᵥ budgetMomentFeature (fun _ ↦ 4) x0))
          size := by
  haveI := isMarkovKernel_historyEventKernel ℓ₀ hap₀ events
  have hpoint : ∀ y : FrequencyState Deme Locus Allele,
      (cohortLaw (stateLaw y source) size).expectation
        (fun sample ↦ gwasWeights genotype outcome sample i * gwasWeights genotype outcome sample j)
      = samplingForm
          (polynomialFunction
            (demePolynomial source (weightProductPolynomial genotype outcome i j)) y)
          (polynomialFunction
            (demePolynomial source (weightExcessPolynomial genotype outcome i j)) y)
          (polynomialFunction
            (demePolynomial source (weightPairingPolynomial genotype outcome i j)) y)
          size := by
    intro y
    rw [expectation_gwasWeights_mul _ hsize]
    simp only [polynomialFunction_apply, eval_demePolynomial, eval_weightProductPolynomial,
      eval_weightExcessPolynomial, eval_weightPairingPolynomial]
  simp only [hpoint]
  exact integral_samplingForm_polynomialFunction ℓ₀ (historyEventKernel ℓ₀ hap₀ events)
    (historyEventPropagator (fun _ ↦ 4) events)
    (integral_momentPolynomial_historyEventKernel ℓ₀ hap₀ (fun _ ↦ 4) events) x0 size _ _ _
    ((totalDegree_rename_le _ _).trans
      (totalDegree_weightProductPolynomial_le genotype outcome i j))
    ((totalDegree_rename_le _ _).trans
      (totalDegree_weightExcessPolynomial_le genotype outcome i j))
    ((totalDegree_rename_le _ _).trans
      (totalDegree_weightPairingPolynomial_le genotype outcome i j))

/-- **The expected trained numerator along a history** is a sampling form of budget-8 dot
products. -/
theorem integral_trainedNumerator_historyEventKernel (ℓ₀ : Locus)
    (hap₀ : FullHaplotype Locus Allele)
    (events : List ((NeutralRates Deme Locus Allele × ℝ≥0) ⊕ PulseMatrix Deme))
    (x0 : FrequencyState Deme Locus Allele) (source target : Deme) {size : ℕ} (hsize : 2 ≤ size)
    (genotype : FullHaplotype Locus Allele → J → ℝ) (outcome : FullHaplotype Locus Allele → ℝ) :
    ∫ y, trainedNumerator (stateLaw y source) (stateLaw y target) size genotype outcome
        ∂(historyEventKernel ℓ₀ hap₀ events x0)
      = samplingForm
          (budgetCoefficients ℓ₀ (fun _ ↦ 8) (trainedPolynomial source target
              (weightProductPolynomial genotype outcome)
              (numeratorMatrixPolynomial genotype outcome))
            ⬝ᵥ (historyEventPropagator (fun _ ↦ 8) events *ᵥ budgetMomentFeature (fun _ ↦ 8) x0))
          (budgetCoefficients ℓ₀ (fun _ ↦ 8) (trainedPolynomial source target
              (weightExcessPolynomial genotype outcome)
              (numeratorMatrixPolynomial genotype outcome))
            ⬝ᵥ (historyEventPropagator (fun _ ↦ 8) events *ᵥ budgetMomentFeature (fun _ ↦ 8) x0))
          (budgetCoefficients ℓ₀ (fun _ ↦ 8) (trainedPolynomial source target
              (weightPairingPolynomial genotype outcome)
              (numeratorMatrixPolynomial genotype outcome))
            ⬝ᵥ (historyEventPropagator (fun _ ↦ 8) events *ᵥ budgetMomentFeature (fun _ ↦ 8) x0))
          size := by
  haveI := isMarkovKernel_historyEventKernel ℓ₀ hap₀ events
  exact integral_trainedNumerator_eq ℓ₀ (historyEventKernel ℓ₀ hap₀ events)
    (historyEventPropagator (fun _ ↦ 8) events)
    (integral_momentPolynomial_historyEventKernel ℓ₀ hap₀ (fun _ ↦ 8) events) le_rfl x0 source
    target hsize genotype outcome

/-- **The expected trained denominator along a history** is a sampling form of budget-8 dot
products. -/
theorem integral_trainedDenominator_historyEventKernel (ℓ₀ : Locus)
    (hap₀ : FullHaplotype Locus Allele)
    (events : List ((NeutralRates Deme Locus Allele × ℝ≥0) ⊕ PulseMatrix Deme))
    (x0 : FrequencyState Deme Locus Allele) (source target : Deme) {size : ℕ} (hsize : 2 ≤ size)
    (genotype : FullHaplotype Locus Allele → J → ℝ) (outcome : FullHaplotype Locus Allele → ℝ) :
    ∫ y, trainedDenominator (stateLaw y source) (stateLaw y target) size genotype outcome
        ∂(historyEventKernel ℓ₀ hap₀ events x0)
      = samplingForm
          (budgetCoefficients ℓ₀ (fun _ ↦ 8) (trainedPolynomial source target
              (weightProductPolynomial genotype outcome)
              (denominatorMatrixPolynomial genotype outcome))
            ⬝ᵥ (historyEventPropagator (fun _ ↦ 8) events *ᵥ budgetMomentFeature (fun _ ↦ 8) x0))
          (budgetCoefficients ℓ₀ (fun _ ↦ 8) (trainedPolynomial source target
              (weightExcessPolynomial genotype outcome)
              (denominatorMatrixPolynomial genotype outcome))
            ⬝ᵥ (historyEventPropagator (fun _ ↦ 8) events *ᵥ budgetMomentFeature (fun _ ↦ 8) x0))
          (budgetCoefficients ℓ₀ (fun _ ↦ 8) (trainedPolynomial source target
              (weightPairingPolynomial genotype outcome)
              (denominatorMatrixPolynomial genotype outcome))
            ⬝ᵥ (historyEventPropagator (fun _ ↦ 8) events *ᵥ budgetMomentFeature (fun _ ↦ 8) x0))
          size := by
  haveI := isMarkovKernel_historyEventKernel ℓ₀ hap₀ events
  exact integral_trainedDenominator_eq ℓ₀ (historyEventKernel ℓ₀ hap₀ events)
    (historyEventPropagator (fun _ ↦ 8) events)
    (integral_momentPolynomial_historyEventKernel ℓ₀ hap₀ (fun _ ↦ 8) events) le_rfl x0 source
    target hsize genotype outcome

/-- **The end-to-end trained-accuracy law along a history of epochs, splits and pulses.**  The
expected accuracy of a score trained by a GWAS on `n` haplotypes of the source deme and deployed in
the target deme is the rational function `momentTrainedAccuracy` of the chronological propagator
applied to the budget-8 moments of the initial state, and of `n`. -/
theorem expectedTrainedAccuracy_historyEventKernel (ℓ₀ : Locus)
    (hap₀ : FullHaplotype Locus Allele)
    (events : List ((NeutralRates Deme Locus Allele × ℝ≥0) ⊕ PulseMatrix Deme))
    (x0 : FrequencyState Deme Locus Allele) (source target : Deme) {size : ℕ} (hsize : 2 ≤ size)
    (genotype : FullHaplotype Locus Allele → J → ℝ) (outcome : FullHaplotype Locus Allele → ℝ) :
    expectedTrainedAccuracy (historyEventKernel ℓ₀ hap₀ events) x0 source target size genotype
        outcome
      = momentTrainedAccuracy ℓ₀ 8 source target genotype outcome size
          (historyEventPropagator (fun _ ↦ 8) events *ᵥ budgetMomentFeature (fun _ ↦ 8) x0) := by
  haveI := isMarkovKernel_historyEventKernel ℓ₀ hap₀ events
  exact expectedTrainedAccuracy_eq_momentTrainedAccuracy ℓ₀ (historyEventKernel ℓ₀ hap₀ events)
    (historyEventPropagator (fun _ ↦ 8) events)
    (integral_momentPolynomial_historyEventKernel ℓ₀ hap₀ (fun _ ↦ 8) events) le_rfl x0 source
    target hsize genotype outcome

/-- **Trained accuracy sees the history only through finitely many moments.**  Two histories, from
two initial states, whose propagated budget-8 moments agree give equal expected trained accuracy
for every cohort size, tag set, outcome, source and target. -/
theorem expectedTrainedAccuracy_eq_of_moments_eq (ℓ₀ : Locus) (hap₀ : FullHaplotype Locus Allele)
    {first second : List ((NeutralRates Deme Locus Allele × ℝ≥0) ⊕ PulseMatrix Deme)}
    {x₁ x₂ : FrequencyState Deme Locus Allele}
    (hmoments : historyEventPropagator (fun _ ↦ 8) first *ᵥ budgetMomentFeature (fun _ ↦ 8) x₁
      = historyEventPropagator (fun _ ↦ 8) second *ᵥ budgetMomentFeature (fun _ ↦ 8) x₂)
    (source target : Deme) {size : ℕ} (hsize : 2 ≤ size)
    (genotype : FullHaplotype Locus Allele → J → ℝ) (outcome : FullHaplotype Locus Allele → ℝ) :
    expectedTrainedAccuracy (historyEventKernel ℓ₀ hap₀ first) x₁ source target size genotype
        outcome
      = expectedTrainedAccuracy (historyEventKernel ℓ₀ hap₀ second) x₂ source target size genotype
          outcome := by
  rw [expectedTrainedAccuracy_historyEventKernel ℓ₀ hap₀ first x₁ source target hsize,
    expectedTrainedAccuracy_historyEventKernel ℓ₀ hap₀ second x₂ source target hsize, hmoments]

/-- **The large-cohort limit along a history.**  As the cohort grows, the expected trained accuracy
tends to the expected target numerator of the population marginal score of each population over
its expected target denominator, wherever that denominator is nonzero. -/
theorem tendsto_expectedTrainedAccuracy_historyEventKernel (ℓ₀ : Locus)
    (hap₀ : FullHaplotype Locus Allele)
    (events : List ((NeutralRates Deme Locus Allele × ℝ≥0) ⊕ PulseMatrix Deme))
    (x0 : FrequencyState Deme Locus Allele) (source target : Deme)
    (genotype : FullHaplotype Locus Allele → J → ℝ) (outcome : FullHaplotype Locus Allele → ℝ)
    (hpopulation : ∫ y, correlationDenominator (stateLaw y target)
        (linearScore genotype (marginalWeights (stateLaw y source) genotype outcome)) outcome
        ∂(historyEventKernel ℓ₀ hap₀ events x0) ≠ 0) :
    Tendsto (fun size : ℕ ↦ expectedTrainedAccuracy (historyEventKernel ℓ₀ hap₀ events) x0 source
        target size genotype outcome) atTop
      (𝓝 ((∫ y, correlationNumerator (stateLaw y target)
          (linearScore genotype (marginalWeights (stateLaw y source) genotype outcome)) outcome
          ∂(historyEventKernel ℓ₀ hap₀ events x0))
        / ∫ y, correlationDenominator (stateLaw y target)
          (linearScore genotype (marginalWeights (stateLaw y source) genotype outcome)) outcome
          ∂(historyEventKernel ℓ₀ hap₀ events x0))) := by
  have hnumerator := integral_historyEventKernel_of_totalDegree_le ℓ₀ hap₀ events x0
    (trainedPolynomial source target (weightProductPolynomial genotype outcome)
      (numeratorMatrixPolynomial genotype outcome))
    (totalDegree_trainedPolynomial_le _ _ _ _
      (totalDegree_weightProductPolynomial_le genotype outcome)
      (totalDegree_numeratorMatrixPolynomial_le genotype outcome)) _
    (polynomialFunction_populationNumerator source target genotype outcome)
  have hdenominator := integral_historyEventKernel_of_totalDegree_le ℓ₀ hap₀ events x0
    (trainedPolynomial source target (weightProductPolynomial genotype outcome)
      (denominatorMatrixPolynomial genotype outcome))
    (totalDegree_trainedPolynomial_le _ _ _ _
      (totalDegree_weightProductPolynomial_le genotype outcome)
      (totalDegree_denominatorMatrixPolynomial_le genotype outcome)) _
    (polynomialFunction_populationDenominator source target genotype outcome)
  rw [hdenominator] at hpopulation
  rw [hnumerator, hdenominator]
  exact (tendsto_momentTrainedAccuracy ℓ₀ 8 source target genotype outcome _ hpopulation).congr'
    ((eventually_ge_atTop 2).mono fun _ hsize ↦
      (expectedTrainedAccuracy_historyEventKernel ℓ₀ hap₀ events x0 source target hsize genotype
        outcome).symm)

/-! ## The law along a time-varying rate history -/

/-- **The end-to-end trained-accuracy law along a rate history.**  The expected trained accuracy is
the rational function `momentTrainedAccuracy` of the propagator of the rate history applied to the
budget-8 moments of the initial state, and of the cohort size. -/
theorem expectedTrainedAccuracy_rateHistoryKernel {rates : ℝ → NeutralRates Deme Locus Allele}
    {T : ℝ} (hT : 0 ≤ T)
    (hcontinuous : ∀ capacity : Locus → ℕ,
      ContinuousOn (fun t ↦ dualGenerator (rates t) capacity) (Set.Icc 0 T))
    (ℓ₀ : Locus) (hap₀ : FullHaplotype Locus Allele) (x0 : FrequencyState Deme Locus Allele)
    (source target : Deme) {size : ℕ} (hsize : 2 ≤ size)
    (genotype : FullHaplotype Locus Allele → J → ℝ) (outcome : FullHaplotype Locus Allele → ℝ) :
    expectedTrainedAccuracy (rateHistoryKernel rates ℓ₀ hap₀ hT hcontinuous) x0 source target size
        genotype outcome
      = momentTrainedAccuracy ℓ₀ 8 source target genotype outcome size
          (rateHistoryDualPropagator rates (fun _ ↦ 8) T
            *ᵥ budgetMomentFeature (fun _ ↦ 8) x0) := by
  haveI := isMarkovKernel_rateHistoryKernel hT hcontinuous ℓ₀ hap₀
  exact expectedTrainedAccuracy_eq_momentTrainedAccuracy ℓ₀
    (rateHistoryKernel rates ℓ₀ hap₀ hT hcontinuous) (rateHistoryDualPropagator rates (fun _ ↦ 8) T)
    (integral_momentPolynomial_rateHistoryKernel hT hcontinuous ℓ₀ hap₀ (fun _ ↦ 8)) le_rfl x0
    source target hsize genotype outcome

end Accumulators

end

end Descent.Portability.EndToEndGWASTrainingHistory
