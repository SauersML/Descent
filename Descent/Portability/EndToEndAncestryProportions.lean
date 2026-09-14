/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.EndToEndAdmixedGenotypes

assert_below Descent.Decision Descent.Program

/-!
# The portability law for individuals with varying ancestry proportions

`EndToEndAdmixedGenotypes` carries the diploid score to F1 individuals, whose two gametes come from
two different demes.  This module lets the ancestry proportion vary between individuals.  An
individual's proportion `θ` is drawn from a finite ancestry law `Θ` on the unit interval.  Given
`θ`, each gamete is drawn independently, from deme `a` with probability `θ` and from deme `b`
otherwise.

Moments of the proportion.  A quadratic in `θ` integrates through `E θ` and `E θ²`
(`expectation_proportionQuadratic`, `expectation_proportionAffine`).

The individual.  At proportion `θ` a gamete has the mixture law of the two demes
(`ancestryGamete`, `expectation_ancestryGamete`).  Its covariance is `θ C_a + (1 - θ) C_b` plus the
switching term `θ (1 - θ) (μ_{S,b} - μ_{S,a}) (μ_{Y,b} - μ_{Y,a})` (`covariance_ancestryGamete`).
An individual carries two independent mixture gametes: the F1 gamete pair of
`EndToEndAdmixedGenotypes` formed from the mixture law twice (`ancestryIndividual`).  For additive
lifts its mean is affine in `θ`, its product moment is quadratic in `θ`, and its covariance is
twice the gamete covariance (`expectation_ancestryIndividual_diploidSum`,
`expectation_ancestryIndividual_diploidSum_mul`, `covariance_ancestryIndividual_diploidSum`).

Special cases.
* Proportion one is random union in deme `a` (`covariance_ancestryIndividual_one`).
* Proportion one half has the F1 mean (`expectation_ancestryIndividual_half`) but not the F1
  covariance.  Its two gametes may come from one deme, which adds
  `(1 / 2) (μ_{S,b} - μ_{S,a}) (μ_{Y,b} - μ_{Y,a})`
  (`covariance_ancestryIndividual_half_sub_admixedMating`).  An F1 cross is proportion one half
  with the gametes forced to differ, so neither F1 crosses nor the pooled cohort
  `EndToEndAdmixedGenotypes.cohortMating` are ancestry cohorts.

The cohort.  The cohort draws `θ` from `Θ` and then forms the individual (`ancestryMating`).
* The cohort mean is `2 (E θ μ_a + (1 - E θ) μ_b)`, linear in `E θ`
  (`expectation_ancestryMating_diploidSum`).
* The cohort covariance of additive lifts is `2 E θ C_a + 2 (1 - E θ) C_b` plus the between-deme
  term `(2 (E θ - E θ²) + 4 (E θ² - (E θ)²)) (μ_{S,b} - μ_{S,a}) (μ_{Y,b} - μ_{Y,a})`
  (`covariance_ancestryMating_diploidSum`).  Its coefficient has two sources: `2 E[θ (1 - θ)]`
  from gametes switching between demes inside an individual, and `4 Var θ` from ancestry varying
  between individuals.

Along a history.  The cohort covariance is a frequency polynomial of degree two in the haplotype
frequencies of `a` and `b`, whose coefficients read `E θ` and `E θ²`
(`ancestryCovariancePolynomial`, `polynomialFunction_ancestryCovariancePolynomial`,
`totalDegree_ancestryCovariancePolynomial_le`).  So the cohort calibration slope of expectations is
the rational function `momentAncestryCalibrationSlope` of the propagated budget-`n` moments for
every `n ≥ 2`, along an event history and along a rate history
(`expectedAncestryCalibrationSlope_historyEventKernel`,
`expectedAncestryCalibrationSlope_rateHistoryKernel`).  Under every kernel, two ancestry laws with
equal `E θ` and `E θ²` give equal cohort calibration slope
(`expectedAncestryCalibrationSlope_eq_of_ancestryMoments_eq`).

Significance.  Variation in ancestry proportion reaches the calibration slope only through the
first two moments of the ancestry law, and at the budget of one deme.  The difference of the two
deme means enters only through the between-deme term, which grows with the variance of ancestry
and with gamete switching.

Scope.  Given `θ` the two gametes are drawn independently, so there is no admixture linkage and no
assortative mating by ancestry.  Each gamete comes from one deme as a whole haplotype, so local
ancestry does not vary along it.  Proportions come from a finite law, and score and outcome are
the same haploid functions in both demes.  Only the calibration slope is carried along a history;
the cohort squared correlation is not stated.  Every history result is the ratio-of-expectations
query of NOTE2 §6.2.

## Empirical status

None.  The bodies are finite sums against constructed laws, polynomial identities and integrals of
polynomials against Markov kernels, so no measurement can bear on them.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.EndToEndAncestryProportions

open MeasureTheory ProbabilityTheory MvPolynomial Descent.Coalescent PartialHaplotypeCarrier
  PartialHaplotypeDualGenerator PartialHaplotypeDualSemigroup NeutralFellerGenerator
  NeutralPolynomialSemigroup PartialHaplotypeMicroscopicApproximation PartialHaplotypePulseKernel
  NeutralPulseHistoryKernel NeutralRateHistoryRealization NeutralRateHistoryKernel
  ReplicaMetricInstances EndToEndPortabilityLaw EndToEndCalibrationLaw EndToEndDiploidLaw
  EndToEndDiploidHistoryLaw EndToEndAdmixedGenotypes
open scoped Matrix NNReal

noncomputable section

/-! ## Moments of the ancestry proportion -/

section Proportions

variable {A : Type*} [Fintype A]

/-- **A quadratic in the ancestry proportion integrates through its first two moments.** -/
theorem expectation_proportionQuadratic (ancestry : FiniteReportLaw A) (proportion : A → ℝ)
    (a b c : ℝ) :
    ancestry.expectation (fun i ↦ a + b * proportion i + c * proportion i ^ 2)
      = a + b * ancestry.expectation proportion
        + c * ancestry.expectation (fun i ↦ proportion i ^ 2) := by
  have hpoint : ∀ i, ancestry.mass i * (a + b * proportion i + c * proportion i ^ 2)
      = a * ancestry.mass i + b * (ancestry.mass i * proportion i)
        + c * (ancestry.mass i * proportion i ^ 2) := fun i ↦ by ring
  simp only [FiniteReportLaw.expectation, hpoint, Finset.sum_add_distrib, ← Finset.mul_sum,
    ancestry.mass_sum, mul_one]

/-- An affine function of the ancestry proportion integrates through its mean. -/
theorem expectation_proportionAffine (ancestry : FiniteReportLaw A) (proportion : A → ℝ)
    (a b : ℝ) :
    ancestry.expectation (fun i ↦ a + b * proportion i)
      = a + b * ancestry.expectation proportion := by
  have h := expectation_proportionQuadratic ancestry proportion a b 0
  simp only [zero_mul, add_zero] at h
  exact h

end Proportions

/-! ## The individual at a given ancestry proportion -/

section Genotypes

variable {H : Type*} [Fintype H] [DecidableEq H]

/-- **The gamete at ancestry proportion `θ`**: drawn from the first deme's law with probability `θ`
and from the second deme's law otherwise. -/
def ancestryGamete (θ : ℝ) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (first second : FiniteReportLaw H) :
    FiniteReportLaw H :=
  (FiniteDemographicSampling.bernoulli θ hθ0 hθ1).bind fun fromFirst ↦ cond fromFirst first second

/-- The gamete at proportion `θ` integrates an observable as the `θ`-mixture of the two deme
expectations. -/
theorem expectation_ancestryGamete (θ : ℝ) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (first second : FiniteReportLaw H) (value : H → ℝ) :
    (ancestryGamete θ hθ0 hθ1 first second).expectation value
      = θ * first.expectation value + (1 - θ) * second.expectation value := by
  rw [ancestryGamete, FiniteReportLaw.expectation_bind]
  show ∑ fromFirst, (FiniteDemographicSampling.bernoulli θ hθ0 hθ1).mass fromFirst
      * (cond fromFirst first second).expectation value = _
  rw [Fintype.sum_bool]
  rfl

/-- **The gamete covariance at proportion `θ`**: the `θ`-mixture of the two deme covariances plus
the switching term `θ (1 - θ) (μ_{S,b} - μ_{S,a}) (μ_{Y,b} - μ_{Y,a})`. -/
theorem covariance_ancestryGamete (θ : ℝ) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (first second : FiniteReportLaw H) (score outcome : H → ℝ) :
    (ancestryGamete θ hθ0 hθ1 first second).covariance score outcome
      = θ * first.covariance score outcome + (1 - θ) * second.covariance score outcome
        + θ * (1 - θ) * ((second.expectation score - first.expectation score)
          * (second.expectation outcome - first.expectation outcome)) := by
  rw [FiniteReportLaw.covariance_eq_rawMoments, FiniteReportLaw.covariance_eq_rawMoments first,
    FiniteReportLaw.covariance_eq_rawMoments second, expectation_ancestryGamete,
    expectation_ancestryGamete, expectation_ancestryGamete]
  ring

/-- **The individual at ancestry proportion `θ`**: two independent gametes, each drawn from the
mixture law at `θ`. -/
def ancestryIndividual (θ : ℝ) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (first second : FiniteReportLaw H) :
    FiniteReportLaw (H × H) :=
  admixedMating (ancestryGamete θ hθ0 hθ1 first second) (ancestryGamete θ hθ0 hθ1 first second)

/-- The mean of an additive lift at proportion `θ` is affine in `θ`. -/
theorem expectation_ancestryIndividual_diploidSum (θ : ℝ) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (first second : FiniteReportLaw H) (value : H → ℝ) :
    (ancestryIndividual θ hθ0 hθ1 first second).expectation (diploidSum value)
      = 2 * second.expectation value
        + 2 * (first.expectation value - second.expectation value) * θ := by
  rw [ancestryIndividual, expectation_admixedMating_diploidSum, expectation_ancestryGamete]
  ring

/-- The product moment of additive lifts at proportion `θ` is quadratic in `θ`. -/
theorem expectation_ancestryIndividual_diploidSum_mul (θ : ℝ) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (first second : FiniteReportLaw H) (score outcome : H → ℝ) :
    (ancestryIndividual θ hθ0 hθ1 first second).expectation
        (fun pair ↦ diploidSum score pair * diploidSum outcome pair)
      = (2 * second.expectation (fun h ↦ score h * outcome h)
          + 2 * second.expectation score * second.expectation outcome)
        + (2 * (first.expectation (fun h ↦ score h * outcome h)
            - second.expectation (fun h ↦ score h * outcome h))
          + 2 * ((first.expectation score - second.expectation score)
              * second.expectation outcome
            + second.expectation score
              * (first.expectation outcome - second.expectation outcome))) * θ
        + 2 * ((first.expectation score - second.expectation score)
          * (first.expectation outcome - second.expectation outcome)) * θ ^ 2 := by
  rw [ancestryIndividual, expectation_admixedMating_diploidSum_mul, expectation_ancestryGamete,
    expectation_ancestryGamete, expectation_ancestryGamete]
  ring

/-- **The individual covariance at proportion `θ`** is twice the gamete covariance. -/
theorem covariance_ancestryIndividual_diploidSum (θ : ℝ) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (first second : FiniteReportLaw H) (score outcome : H → ℝ) :
    (ancestryIndividual θ hθ0 hθ1 first second).covariance (diploidSum score) (diploidSum outcome)
      = 2 * (θ * first.covariance score outcome + (1 - θ) * second.covariance score outcome
        + θ * (1 - θ) * ((second.expectation score - first.expectation score)
          * (second.expectation outcome - first.expectation outcome))) := by
  rw [ancestryIndividual, covariance_admixedMating_diploidSum, covariance_ancestryGamete]
  ring

/-- **Proportion one is random union in the first deme.** -/
theorem covariance_ancestryIndividual_one (first second : FiniteReportLaw H)
    (score outcome : H → ℝ) :
    (ancestryIndividual 1 zero_le_one le_rfl first second).covariance (diploidSum score)
        (diploidSum outcome)
      = (FiniteReproductiveKernel.independentMating first).covariance (diploidSum score)
          (diploidSum outcome) := by
  rw [covariance_ancestryIndividual_diploidSum, covariance_independentMating_diploidSum]
  ring

/-- **Proportion one half has the F1 mean.** -/
theorem expectation_ancestryIndividual_half (first second : FiniteReportLaw H) (value : H → ℝ) :
    (ancestryIndividual (1 / 2) (by norm_num) (by norm_num) first second).expectation
        (diploidSum value)
      = (admixedMating first second).expectation (diploidSum value) := by
  rw [expectation_ancestryIndividual_diploidSum, expectation_admixedMating_diploidSum]
  ring

/-- **Proportion one half is not an F1 cross.**  Its two gametes may come from one deme, which adds
`(1 / 2) (μ_{S,b} - μ_{S,a}) (μ_{Y,b} - μ_{Y,a})` to the F1 covariance. -/
theorem covariance_ancestryIndividual_half_sub_admixedMating (first second : FiniteReportLaw H)
    (score outcome : H → ℝ) :
    (ancestryIndividual (1 / 2) (by norm_num) (by norm_num) first second).covariance
        (diploidSum score) (diploidSum outcome)
      - (admixedMating first second).covariance (diploidSum score) (diploidSum outcome)
      = 1 / 2 * ((second.expectation score - first.expectation score)
        * (second.expectation outcome - first.expectation outcome)) := by
  rw [covariance_ancestryIndividual_diploidSum, covariance_admixedMating_diploidSum]
  ring

/-! ## The ancestry cohort -/

variable {A : Type*} [Fintype A]

/-- **The ancestry cohort.**  An individual's ancestry proportion is read through `proportion` from
a draw of the finite law `ancestry`, and given it the individual is formed at that proportion. -/
def ancestryMating (ancestry : FiniteReportLaw A) (proportion : A → ℝ)
    (h0 : ∀ i, 0 ≤ proportion i) (h1 : ∀ i, proportion i ≤ 1) (first second : FiniteReportLaw H) :
    FiniteReportLaw (H × H) :=
  ancestry.bind fun i ↦ ancestryIndividual (proportion i) (h0 i) (h1 i) first second

/-- The cohort integrates an observable over the ancestry law of the individual expectations. -/
theorem expectation_ancestryMating (ancestry : FiniteReportLaw A) (proportion : A → ℝ)
    (h0 : ∀ i, 0 ≤ proportion i) (h1 : ∀ i, proportion i ≤ 1) (first second : FiniteReportLaw H)
    (φ : H × H → ℝ) :
    (ancestryMating ancestry proportion h0 h1 first second).expectation φ
      = ancestry.expectation fun i ↦
          (ancestryIndividual (proportion i) (h0 i) (h1 i) first second).expectation φ :=
  FiniteReportLaw.expectation_bind ancestry
    (fun i ↦ ancestryIndividual (proportion i) (h0 i) (h1 i) first second) φ

/-- **The cohort mean is linear in the mean ancestry proportion.** -/
theorem expectation_ancestryMating_diploidSum (ancestry : FiniteReportLaw A) (proportion : A → ℝ)
    (h0 : ∀ i, 0 ≤ proportion i) (h1 : ∀ i, proportion i ≤ 1) (first second : FiniteReportLaw H)
    (value : H → ℝ) :
    (ancestryMating ancestry proportion h0 h1 first second).expectation (diploidSum value)
      = 2 * (ancestry.expectation proportion * first.expectation value
        + (1 - ancestry.expectation proportion) * second.expectation value) := by
  rw [expectation_ancestryMating]
  simp only [expectation_ancestryIndividual_diploidSum]
  rw [expectation_proportionAffine ancestry proportion]
  ring

/-- **The cohort covariance.**  The deme covariances mixed at the mean proportion, plus the
between-deme term with coefficient `2 E[θ (1 - θ)] + 4 Var θ`: gamete switching inside an
individual, and ancestry varying between individuals. -/
theorem covariance_ancestryMating_diploidSum (ancestry : FiniteReportLaw A) (proportion : A → ℝ)
    (h0 : ∀ i, 0 ≤ proportion i) (h1 : ∀ i, proportion i ≤ 1) (first second : FiniteReportLaw H)
    (score outcome : H → ℝ) :
    (ancestryMating ancestry proportion h0 h1 first second).covariance (diploidSum score)
        (diploidSum outcome)
      = 2 * ancestry.expectation proportion * first.covariance score outcome
        + 2 * (1 - ancestry.expectation proportion) * second.covariance score outcome
        + (2 * (ancestry.expectation proportion - ancestry.expectation (fun i ↦ proportion i ^ 2))
            + 4 * (ancestry.expectation (fun i ↦ proportion i ^ 2)
              - ancestry.expectation proportion ^ 2))
          * ((second.expectation score - first.expectation score)
            * (second.expectation outcome - first.expectation outcome)) := by
  rw [FiniteReportLaw.covariance_eq_rawMoments, expectation_ancestryMating,
    expectation_ancestryMating, expectation_ancestryMating]
  simp only [expectation_ancestryIndividual_diploidSum,
    expectation_ancestryIndividual_diploidSum_mul]
  rw [expectation_proportionQuadratic ancestry proportion,
    expectation_proportionAffine ancestry proportion,
    expectation_proportionAffine ancestry proportion,
    FiniteReportLaw.covariance_eq_rawMoments first, FiniteReportLaw.covariance_eq_rawMoments second]
  ring

end Genotypes

/-! ## The ancestry cohort along a history -/

section History

variable {A : Type*} [Fintype A]
variable {Deme Locus : Type*} {Allele : Locus → Type*}
variable [Fintype Deme] [DecidableEq Deme] [Fintype Locus] [DecidableEq Locus]
  [∀ ℓ, Fintype (Allele ℓ)] [∀ ℓ, DecidableEq (Allele ℓ)]

/-- The ancestry cohort of a deme pair at a state. -/
def stateAncestryLaw (y : FrequencyState Deme Locus Allele) (ancestry : FiniteReportLaw A)
    (proportion : A → ℝ) (h0 : ∀ i, 0 ≤ proportion i) (h1 : ∀ i, proportion i ≤ 1)
    (first second : Deme) :
    FiniteReportLaw (FullHaplotype Locus Allele × FullHaplotype Locus Allele) :=
  ancestryMating ancestry proportion h0 h1 (stateLaw y first) (stateLaw y second)

/-- **The cohort covariance of additive score and outcome as a frequency polynomial** of degree
two, given the mean `E θ` and the second moment `E θ²` of the ancestry proportion. -/
def ancestryCovariancePolynomial (meanProportion squareProportion : ℝ) (first second : Deme)
    (score outcome : FullHaplotype Locus Allele → ℝ) : FrequencyPolynomial Deme Locus Allele :=
  MvPolynomial.C (2 * meanProportion) * demeCovariancePolynomial first score outcome
    + MvPolynomial.C (2 * (1 - meanProportion)) * demeCovariancePolynomial second score outcome
    + MvPolynomial.C (2 * (meanProportion - squareProportion)
        + 4 * (squareProportion - meanProportion ^ 2))
      * ((demeMeanPolynomial second score - demeMeanPolynomial first score)
        * (demeMeanPolynomial second outcome - demeMeanPolynomial first outcome))

/-- At a state, the ancestry covariance polynomial at the moments of the ancestry law is the
covariance of the additive lifts under the cohort law. -/
theorem polynomialFunction_ancestryCovariancePolynomial (ancestry : FiniteReportLaw A)
    (proportion : A → ℝ) (h0 : ∀ i, 0 ≤ proportion i) (h1 : ∀ i, proportion i ≤ 1)
    (first second : Deme) (score outcome : FullHaplotype Locus Allele → ℝ)
    (y : FrequencyState Deme Locus Allele) :
    polynomialFunction (ancestryCovariancePolynomial (ancestry.expectation proportion)
        (ancestry.expectation fun i ↦ proportion i ^ 2) first second score outcome) y
      = (stateAncestryLaw y ancestry proportion h0 h1 first second).covariance (diploidSum score)
          (diploidSum outcome) := by
  rw [stateAncestryLaw, covariance_ancestryMating_diploidSum,
    ← polynomialFunction_demeCovariancePolynomial first score outcome y,
    ← polynomialFunction_demeCovariancePolynomial second score outcome y,
    ← polynomialFunction_demeMeanPolynomial first score y,
    ← polynomialFunction_demeMeanPolynomial second score y,
    ← polynomialFunction_demeMeanPolynomial first outcome y,
    ← polynomialFunction_demeMeanPolynomial second outcome y]
  simp only [polynomialFunction_apply, ancestryCovariancePolynomial, map_add, map_sub, map_mul,
    eval_C]

/-- At a state, the ancestry covariance polynomial of an observable with itself is its variance
under the cohort law. -/
theorem polynomialFunction_ancestryVariance (ancestry : FiniteReportLaw A) (proportion : A → ℝ)
    (h0 : ∀ i, 0 ≤ proportion i) (h1 : ∀ i, proportion i ≤ 1) (first second : Deme)
    (value : FullHaplotype Locus Allele → ℝ) (y : FrequencyState Deme Locus Allele) :
    polynomialFunction (ancestryCovariancePolynomial (ancestry.expectation proportion)
        (ancestry.expectation fun i ↦ proportion i ^ 2) first second value value) y
      = (stateAncestryLaw y ancestry proportion h0 h1 first second).variance (diploidSum value) :=
  polynomialFunction_ancestryCovariancePolynomial ancestry proportion h0 h1 first second value value
    y

/-- The ancestry covariance polynomial has total degree at most two. -/
theorem totalDegree_ancestryCovariancePolynomial_le (meanProportion squareProportion : ℝ)
    (first second : Deme) (score outcome : FullHaplotype Locus Allele → ℝ) :
    (ancestryCovariancePolynomial meanProportion squareProportion first second score
      outcome).totalDegree ≤ 2 :=
  (totalDegree_add _ _).trans <| max_le
    ((totalDegree_add _ _).trans <| max_le
      ((totalDegree_mul _ _).trans <| by
        simpa only [totalDegree_C, zero_add] using
          totalDegree_demeCovariancePolynomial_le first score outcome)
      ((totalDegree_mul _ _).trans <| by
        simpa only [totalDegree_C, zero_add] using
          totalDegree_demeCovariancePolynomial_le second score outcome))
    ((totalDegree_mul _ _).trans <| by
      rw [totalDegree_C, zero_add]
      exact (totalDegree_mul _ _).trans <| Nat.add_le_add
        ((totalDegree_sub _ _).trans <| max_le (totalDegree_demeMeanPolynomial_le second score)
          (totalDegree_demeMeanPolynomial_le first score))
        ((totalDegree_sub _ _).trans <| max_le (totalDegree_demeMeanPolynomial_le second outcome)
          (totalDegree_demeMeanPolynomial_le first outcome)))

/-! ## The cohort calibration slope -/

/-- **The cohort calibration slope of expectations**: the expected cohort covariance over the
expected cohort score variance. -/
def expectedAncestryCalibrationSlope
    (κ : Kernel (FrequencyState Deme Locus Allele) (FrequencyState Deme Locus Allele))
    (x0 : FrequencyState Deme Locus Allele) (ancestry : FiniteReportLaw A) (proportion : A → ℝ)
    (h0 : ∀ i, 0 ≤ proportion i) (h1 : ∀ i, proportion i ≤ 1) (first second : Deme)
    (score outcome : FullHaplotype Locus Allele → ℝ) : ℝ :=
  (∫ y, (stateAncestryLaw y ancestry proportion h0 h1 first second).covariance (diploidSum score)
      (diploidSum outcome) ∂(κ x0))
    / ∫ y, (stateAncestryLaw y ancestry proportion h0 h1 first second).variance (diploidSum score)
      ∂(κ x0)

/-- **The rational cohort calibration slope** of a budget-`n` moment vector, given the mean and
the second moment of the ancestry proportion. -/
def momentAncestryCalibrationSlope (ℓ₀ : Locus) (n : ℕ) (meanProportion squareProportion : ℝ)
    (first second : Deme) (score outcome : FullHaplotype Locus Allele → ℝ)
    (v : BudgetConfiguration Deme Locus Allele (fun _ ↦ n) → ℝ) : ℝ :=
  (budgetCoefficients ℓ₀ (fun _ ↦ n)
      (ancestryCovariancePolynomial meanProportion squareProportion first second score outcome)
      ⬝ᵥ v)
    / (budgetCoefficients ℓ₀ (fun _ ↦ n)
      (ancestryCovariancePolynomial meanProportion squareProportion first second score score)
      ⬝ᵥ v)

/-- **The cohort calibration slope along a history of epochs, splits and pulses.**  At every
budget `n ≥ 2` it is the rational cohort slope of the propagated budget-`n` moments, read at the
mean and second moment of the ancestry proportion. -/
theorem expectedAncestryCalibrationSlope_historyEventKernel (ℓ₀ : Locus)
    (hap₀ : FullHaplotype Locus Allele)
    (events : List ((NeutralRates Deme Locus Allele × ℝ≥0) ⊕ PulseMatrix Deme)) {n : ℕ}
    (hn : 2 ≤ n) (x0 : FrequencyState Deme Locus Allele) (ancestry : FiniteReportLaw A)
    (proportion : A → ℝ) (h0 : ∀ i, 0 ≤ proportion i) (h1 : ∀ i, proportion i ≤ 1)
    (first second : Deme) (score outcome : FullHaplotype Locus Allele → ℝ) :
    expectedAncestryCalibrationSlope (historyEventKernel ℓ₀ hap₀ events) x0 ancestry proportion h0
        h1 first second score outcome
      = momentAncestryCalibrationSlope ℓ₀ n (ancestry.expectation proportion)
          (ancestry.expectation fun i ↦ proportion i ^ 2) first second score outcome
          (historyEventPropagator (fun _ ↦ n) events *ᵥ budgetMomentFeature (fun _ ↦ n) x0) := by
  rw [expectedAncestryCalibrationSlope,
    integral_historyEventKernel_of_totalDegree_le ℓ₀ hap₀ events x0 _
      ((totalDegree_ancestryCovariancePolynomial_le (ancestry.expectation proportion)
        (ancestry.expectation fun i ↦ proportion i ^ 2) first second score outcome).trans hn) _
      (polynomialFunction_ancestryCovariancePolynomial ancestry proportion h0 h1 first second score
        outcome),
    integral_historyEventKernel_of_totalDegree_le ℓ₀ hap₀ events x0 _
      ((totalDegree_ancestryCovariancePolynomial_le (ancestry.expectation proportion)
        (ancestry.expectation fun i ↦ proportion i ^ 2) first second score score).trans hn) _
      (polynomialFunction_ancestryVariance ancestry proportion h0 h1 first second score)]
  rfl

/-- **The cohort calibration slope along a time-varying rate history**, at every budget `n ≥ 2`. -/
theorem expectedAncestryCalibrationSlope_rateHistoryKernel
    {rates : ℝ → NeutralRates Deme Locus Allele} {T : ℝ} (hT : 0 ≤ T)
    (hcontinuous : ∀ capacity : Locus → ℕ,
      ContinuousOn (fun t ↦ dualGenerator (rates t) capacity) (Set.Icc 0 T))
    (ℓ₀ : Locus) (hap₀ : FullHaplotype Locus Allele) {n : ℕ} (hn : 2 ≤ n)
    (x0 : FrequencyState Deme Locus Allele) (ancestry : FiniteReportLaw A) (proportion : A → ℝ)
    (h0 : ∀ i, 0 ≤ proportion i) (h1 : ∀ i, proportion i ≤ 1) (first second : Deme)
    (score outcome : FullHaplotype Locus Allele → ℝ) :
    expectedAncestryCalibrationSlope (rateHistoryKernel rates ℓ₀ hap₀ hT hcontinuous) x0 ancestry
        proportion h0 h1 first second score outcome
      = momentAncestryCalibrationSlope ℓ₀ n (ancestry.expectation proportion)
          (ancestry.expectation fun i ↦ proportion i ^ 2) first second score outcome
          (rateHistoryDualPropagator rates (fun _ ↦ n) T
            *ᵥ budgetMomentFeature (fun _ ↦ n) x0) := by
  rw [expectedAncestryCalibrationSlope,
    integral_rateHistoryKernel_of_totalDegree_le hT hcontinuous ℓ₀ hap₀ x0 _
      ((totalDegree_ancestryCovariancePolynomial_le (ancestry.expectation proportion)
        (ancestry.expectation fun i ↦ proportion i ^ 2) first second score outcome).trans hn) _
      (polynomialFunction_ancestryCovariancePolynomial ancestry proportion h0 h1 first second score
        outcome),
    integral_rateHistoryKernel_of_totalDegree_le hT hcontinuous ℓ₀ hap₀ x0 _
      ((totalDegree_ancestryCovariancePolynomial_le (ancestry.expectation proportion)
        (ancestry.expectation fun i ↦ proportion i ^ 2) first second score score).trans hn) _
      (polynomialFunction_ancestryVariance ancestry proportion h0 h1 first second score)]
  rfl

/-- **The cohort sees the ancestry law only through its first two moments.**  Under every kernel,
two ancestry laws whose proportions have equal means and equal second moments give equal cohort
calibration slope. -/
theorem expectedAncestryCalibrationSlope_eq_of_ancestryMoments_eq
    (κ : Kernel (FrequencyState Deme Locus Allele) (FrequencyState Deme Locus Allele))
    (x0 : FrequencyState Deme Locus Allele) {B : Type*} [Fintype B]
    (ancestry₁ : FiniteReportLaw A) (proportion₁ : A → ℝ) (h0₁ : ∀ i, 0 ≤ proportion₁ i)
    (h1₁ : ∀ i, proportion₁ i ≤ 1) (ancestry₂ : FiniteReportLaw B) (proportion₂ : B → ℝ)
    (h0₂ : ∀ i, 0 ≤ proportion₂ i) (h1₂ : ∀ i, proportion₂ i ≤ 1)
    (hmean : ancestry₁.expectation proportion₁ = ancestry₂.expectation proportion₂)
    (hsquare : ancestry₁.expectation (fun i ↦ proportion₁ i ^ 2)
      = ancestry₂.expectation (fun i ↦ proportion₂ i ^ 2))
    (first second : Deme) (score outcome : FullHaplotype Locus Allele → ℝ) :
    expectedAncestryCalibrationSlope κ x0 ancestry₁ proportion₁ h0₁ h1₁ first second score outcome
      = expectedAncestryCalibrationSlope κ x0 ancestry₂ proportion₂ h0₂ h1₂ first second score
          outcome := by
  simp only [expectedAncestryCalibrationSlope, stateAncestryLaw, FiniteReportLaw.variance,
    covariance_ancestryMating_diploidSum, hmean, hsquare]

end History

end

end Descent.Portability.EndToEndAncestryProportions
