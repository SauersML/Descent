/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.EndToEndDiploidCalibration

assert_below Descent.Decision Descent.Program

/-!
# The portability law for admixed genotypes

`EndToEndDiploidLaw` draws both gametes of an individual from one deme.  This module draws them
from two.  An F1 individual carries one gamete from deme `a` and, independently given the frequency
state, one gamete from deme `b`.  The module carries the additive diploid score from a source deme
to such individuals along the history kernels.

The F1 gamete pair.  The admixed genotype law is the product of the two deme haplotype laws
(`admixedMating`, the corpus joint law with a constant kernel).  An observable of the pair
integrates as a draw from `b` nested in a draw from `a` (`expectation_admixedMating`).  Each gamete
carries its own deme's law (`expectation_admixedMating_gametes`), and a product of observables of
the two gametes has the product of the two deme means (`expectation_admixedMating_cross`).  A deme
crossed with itself is random union of gametes (`expectation_admixedMating_self`).

F1 moments.  Take the additive lifts `S(h₁) + S(h₂)` and `Y(h₁) + Y(h₂)`.
* The mean is `μ_a + μ_b` (`expectation_admixedMating_diploidSum`).
* The product moment is the two within-deme product moments plus the cross-deme products
  `μ_{S,a} μ_{Y,b} + μ_{Y,a} μ_{S,b}` (`expectation_admixedMating_diploidSum_mul`).  These are the
  cross terms of the product of the means, so they cancel.  The covariance is `C_a + C_b` and each
  variance is `V_a + V_b` (`covariance_admixedMating_diploidSum`,
  `variance_admixedMating_diploidSum`).
* The squared correlation is `(C_a + C_b)² / ((V_{S,a} + V_{S,b}) (V_{Y,a} + V_{Y,b}))` and the
  calibration slope is `(C_a + C_b) / (V_{S,a} + V_{S,b})`
  (`squaredCorrelation_admixedMating_diploidSum`, `calibrationSlope_admixedMating_diploidSum`).
  Neither is an average of the two deme metrics.

The law along a history.  The F1 mean, covariance, and correlation numerator and denominator are
frequency polynomials in the haplotype frequencies of `a` and `b`, of total degree one, two, four
and four (`admixedMeanPolynomial`, `admixedCovariancePolynomial`, `admixedNumeratorPolynomial`,
`admixedDenominatorPolynomial`, with their `polynomialFunction_` and `totalDegree_` lemmas).
Along a history of epochs, splits and pulses their expectations are coefficient vectors dotted with
the propagated budget-`n` moments: for `n ≥ 1` for the mean, `n ≥ 2` for covariance and variance,
and `n ≥ 4` for numerator and denominator (`integral_admixedMean_historyEventKernel`,
`integral_admixedCovariance_historyEventKernel`, `integral_admixedVariance_historyEventKernel`,
`integral_admixedNumerator_historyEventKernel`, `integral_admixedDenominator_historyEventKernel`).

Portability to admixed individuals.  Take a source deme `s` forming diploids at inbreeding
coefficient `F_s`, and a target population of F1 crosses of `a` and `b`.
* The portability of expected accuracies `(E N_ab · E D_s) / (E D_ab · E N_s)`
  (`expectedAdmixedPortability`) does not depend on `F_s` under any kernel, because `4 (1 + F_s)²`
  cancels (`expectedAdmixedPortability_eq_haploidSource`).
* Along an event history or a rate history it is the rational function `admixedMomentPortability`
  of the propagated budget-4 moments (`expectedAdmixedPortability_historyEventKernel`,
  `expectedAdmixedPortability_rateHistoryKernel`).
* Two histories with equal propagated budget-4 moments give equal portability for every source and
  every deme pair (`expectedAdmixedPortability_eq_of_moments_eq`).
* The F1 calibration slope of expectations and its portability from the diploid source are
  rational in the budget-2 moments (`expectedAdmixedCalibrationSlope_historyEventKernel`,
  `expectedAdmixedCalibrationPortability_historyEventKernel`).

The admixture cohort.  Pool F1 crosses, with probability `π`, with diploids of `a` formed at `F_a`
(`cohortMating`).  Its expectations are the `π`-mixture (`expectation_cohortMating`).  Its
covariance is the mixture of the F1 and deme covariances plus the between-group term
`π (1 - π) (μ_{S,b} - μ_{S,a}) (μ_{Y,b} - μ_{Y,a})` (`covariance_cohortMating_diploidSum`).  That
covariance is a frequency polynomial of degree two (`polynomialFunction_cohortCovariancePolynomial`,
`totalDegree_cohortCovariancePolynomial_le`).  So the cohort calibration slope, a ratio of mixed
expectations, is rational in the budget-2 moments
(`expectedCohortCalibrationSlope_historyEventKernel`).

Significance.  Admixed individuals keep the finite-moment structure of the one-deme law at the same
budgets: four for accuracy and two for the calibration slope.  The target of portability is a pair
of demes rather than one deme, and its second moments are sums over the pair.  Inside a covariance
the two parental demes meet only through products of their means.  Those cancel for F1
individuals and survive in a cohort as the between-group term.

Scope.  The gametes of an F1 individual are drawn independently given the frequency state, with no
identity by descent between them.  Later admixed generations, admixture linkage, ancestry
proportions varying between individuals, and ancestry-specific effects are not covered.  Score and
outcome are additive lifts of haploid functions, so dominance on admixed genotypes is not carried
along a history.  Every history result is the ratio-of-expectations query of NOTE2 §6.2.

## Empirical status

None.  The bodies are finite sums against constructed laws, polynomial identities and integrals of
polynomials against Markov kernels, so no measurement can bear on them.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.EndToEndAdmixedGenotypes

open MeasureTheory ProbabilityTheory MvPolynomial Descent.Coalescent PartialHaplotypeCarrier
  PartialHaplotypeDualGenerator PartialHaplotypeDualSemigroup NeutralFellerGenerator
  NeutralPolynomialSemigroup PartialHaplotypeMicroscopicApproximation PartialHaplotypePulseKernel
  NeutralPulseHistoryKernel NeutralRateHistoryRealization NeutralRateHistoryKernel
  ReplicaMetricInstances EndToEndPortabilityLaw EndToEndCalibrationLaw EndToEndDiploidLaw
  EndToEndDiploidHistoryLaw EndToEndDiploidCalibration
open scoped Matrix NNReal

noncomputable section

/-! ## The gamete pair of an F1 individual -/

section Genotypes

variable {H : Type*} [Fintype H] [DecidableEq H]

/-- **The gamete pair of an F1 individual.**  One gamete is drawn from the law of the first
parental deme and, independently, the other from the law of the second. -/
def admixedMating (first second : FiniteReportLaw H) : FiniteReportLaw (H × H) :=
  first.joint fun _ ↦ second

/-- An observable of the F1 gamete pair integrates as a draw from the second deme nested in a draw
from the first. -/
theorem expectation_admixedMating (first second : FiniteReportLaw H) (φ : H × H → ℝ) :
    (admixedMating first second).expectation φ =
      first.expectation fun a ↦ second.expectation fun b ↦ φ (a, b) :=
  FiniteReportLaw.expectation_joint first (fun _ ↦ second) φ

/-- **A deme crossed with itself is random union of gametes**: every observable of the pair has its
random-union expectation. -/
theorem expectation_admixedMating_self (law : FiniteReportLaw H) (φ : H × H → ℝ) :
    (admixedMating law law).expectation φ
      = (FiniteReproductiveKernel.independentMating law).expectation φ := by
  rw [expectation_admixedMating, expectation_independentMating]

/-- **Each gamete carries its parental deme's law.** -/
theorem expectation_admixedMating_gametes (first second : FiniteReportLaw H) (value : H → ℝ) :
    (admixedMating first second).expectation (fun pair ↦ value pair.1) = first.expectation value ∧
      (admixedMating first second).expectation (fun pair ↦ value pair.2)
        = second.expectation value := by
  refine ⟨?_, ?_⟩
  · rw [expectation_admixedMating]
    exact congrArg first.expectation
      (funext fun a ↦ FiniteIndependentMoments.expectation_const second (value a))
  · rw [expectation_admixedMating]
    exact FiniteIndependentMoments.expectation_const first (second.expectation value)

/-- **The two gametes are independent**: the product of an observable of the first gamete and an
observable of the second integrates to the product of the two deme means. -/
theorem expectation_admixedMating_cross (first second : FiniteReportLaw H) (f g : H → ℝ) :
    (admixedMating first second).expectation (fun pair ↦ f pair.1 * g pair.2)
      = first.expectation f * second.expectation g := by
  have hinner : ∀ a, second.expectation (fun b ↦ f a * g b) = f a * second.expectation g := by
    intro a
    simp only [FiniteReportLaw.expectation, Finset.mul_sum]
    exact Finset.sum_congr rfl fun b _ ↦ mul_left_comm _ _ _
  rw [expectation_admixedMating]
  show (first.expectation fun a ↦ second.expectation fun b ↦ f a * g b) = _
  simp only [hinner]
  simp only [FiniteReportLaw.expectation, Finset.sum_mul, mul_assoc]

/-- **The F1 mean is the sum of the two parental deme means.** -/
theorem expectation_admixedMating_diploidSum (first second : FiniteReportLaw H) (value : H → ℝ) :
    (admixedMating first second).expectation (diploidSum value)
      = first.expectation value + second.expectation value := by
  obtain ⟨hfirst, hsecond⟩ := expectation_admixedMating_gametes first second value
  rw [← hfirst, ← hsecond]
  simp only [diploidSum, FiniteReportLaw.expectation, mul_add, Finset.sum_add_distrib]

/-- **The F1 product moment.**  Within each gamete it is the deme's own product moment; across the
two gametes it is a product of means of the two demes. -/
theorem expectation_admixedMating_diploidSum_mul (first second : FiniteReportLaw H)
    (score outcome : H → ℝ) :
    (admixedMating first second).expectation
        (fun pair ↦ diploidSum score pair * diploidSum outcome pair)
      = first.expectation (fun h ↦ score h * outcome h)
          + second.expectation (fun h ↦ score h * outcome h)
        + (first.expectation score * second.expectation outcome
          + first.expectation outcome * second.expectation score) := by
  obtain ⟨hfirst, hsecond⟩ :=
    expectation_admixedMating_gametes first second fun h ↦ score h * outcome h
  rw [← hfirst, ← hsecond, ← expectation_admixedMating_cross first second score outcome,
    ← expectation_admixedMating_cross first second outcome score]
  simp only [diploidSum, FiniteReportLaw.expectation, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun pair _ ↦ by ring

/-- **The F1 covariance is the sum of the two parental deme covariances.**  The cross-deme
products of means in the product moment are those of the product of the means, and cancel. -/
theorem covariance_admixedMating_diploidSum (first second : FiniteReportLaw H)
    (score outcome : H → ℝ) :
    (admixedMating first second).covariance (diploidSum score) (diploidSum outcome)
      = first.covariance score outcome + second.covariance score outcome := by
  rw [FiniteReportLaw.covariance_eq_rawMoments, FiniteReportLaw.covariance_eq_rawMoments,
    FiniteReportLaw.covariance_eq_rawMoments, expectation_admixedMating_diploidSum_mul,
    expectation_admixedMating_diploidSum, expectation_admixedMating_diploidSum]
  ring

/-- **The F1 variance is the sum of the two parental deme variances.** -/
theorem variance_admixedMating_diploidSum (first second : FiniteReportLaw H) (value : H → ℝ) :
    (admixedMating first second).variance (diploidSum value)
      = first.variance value + second.variance value :=
  covariance_admixedMating_diploidSum first second value value

/-- **The F1 squared correlation** of additive score and outcome: the squared sum of the two deme
covariances over the product of the summed variances, defined when both sums are positive. -/
theorem squaredCorrelation_admixedMating_diploidSum (first second : FiniteReportLaw H)
    (score outcome : H → ℝ) :
    (admixedMating first second).squaredCorrelation (diploidSum score) (diploidSum outcome)
      = if 0 < first.variance score + second.variance score
          ∧ 0 < first.variance outcome + second.variance outcome then
        some ((first.covariance score outcome + second.covariance score outcome) ^ 2
          / ((first.variance score + second.variance score)
            * (first.variance outcome + second.variance outcome)))
      else none := by
  rw [FiniteReportLaw.squaredCorrelation, variance_admixedMating_diploidSum,
    variance_admixedMating_diploidSum, covariance_admixedMating_diploidSum]

/-- **The F1 calibration slope** of additive score and outcome: the summed covariance over the
summed score variance, defined when that sum is positive. -/
theorem calibrationSlope_admixedMating_diploidSum (first second : FiniteReportLaw H)
    (score outcome : H → ℝ) :
    (admixedMating first second).calibrationSlope (diploidSum score) (diploidSum outcome)
      = if 0 < first.variance score + second.variance score then
        some ((first.covariance score outcome + second.covariance score outcome)
          / (first.variance score + second.variance score))
      else none := by
  rw [FiniteReportLaw.calibrationSlope, variance_admixedMating_diploidSum,
    covariance_admixedMating_diploidSum]

/-! ## The admixture cohort -/

/-- **The admixture cohort.**  With probability `π` an individual is an F1 cross of the two demes;
otherwise it is a diploid of the first deme formed at inbreeding coefficient `F`. -/
def cohortMating (proportion : ℝ) (hp0 : 0 ≤ proportion) (hp1 : proportion ≤ 1)
    (first second : FiniteReportLaw H) (F : ℝ) (hF0 : 0 ≤ F) (hF1 : F ≤ 1) :
    FiniteReportLaw (H × H) :=
  (FiniteDemographicSampling.bernoulli proportion hp0 hp1).bind fun admixed ↦
    cond admixed (admixedMating first second) (inbredMating first F hF0 hF1)

/-- The cohort integrates an observable as the `π`-mixture of the F1 and deme expectations. -/
theorem expectation_cohortMating (proportion : ℝ) (hp0 : 0 ≤ proportion) (hp1 : proportion ≤ 1)
    (first second : FiniteReportLaw H) (F : ℝ) (hF0 : 0 ≤ F) (hF1 : F ≤ 1) (φ : H × H → ℝ) :
    (cohortMating proportion hp0 hp1 first second F hF0 hF1).expectation φ
      = proportion * (admixedMating first second).expectation φ
        + (1 - proportion) * (inbredMating first F hF0 hF1).expectation φ := by
  rw [cohortMating, FiniteReportLaw.expectation_bind]
  show ∑ admixed, (FiniteDemographicSampling.bernoulli proportion hp0 hp1).mass admixed
      * (cond admixed (admixedMating first second) (inbredMating first F hF0 hF1)).expectation φ
    = _
  rw [Fintype.sum_bool]
  rfl

/-- **The cohort covariance**: the `π`-mixture of the F1 covariance and the deme covariance, plus
the between-group term `π (1 - π) (μ_{S,b} - μ_{S,a}) (μ_{Y,b} - μ_{Y,a})`. -/
theorem covariance_cohortMating_diploidSum (proportion : ℝ) (hp0 : 0 ≤ proportion)
    (hp1 : proportion ≤ 1) (first second : FiniteReportLaw H) (F : ℝ) (hF0 : 0 ≤ F) (hF1 : F ≤ 1)
    (score outcome : H → ℝ) :
    (cohortMating proportion hp0 hp1 first second F hF0 hF1).covariance (diploidSum score)
        (diploidSum outcome)
      = proportion * (first.covariance score outcome + second.covariance score outcome)
        + (1 - proportion) * (2 * (1 + F) * first.covariance score outcome)
        + proportion * (1 - proportion)
          * ((second.expectation score - first.expectation score)
            * (second.expectation outcome - first.expectation outcome)) := by
  have hadmixed := covariance_admixedMating_diploidSum first second score outcome
  have hinbred := covariance_inbredMating_diploidSum first F hF0 hF1 score outcome
  rw [FiniteReportLaw.covariance_eq_rawMoments (admixedMating first second),
    expectation_admixedMating_diploidSum, expectation_admixedMating_diploidSum,
    sub_eq_iff_eq_add] at hadmixed
  rw [FiniteReportLaw.covariance_eq_rawMoments (inbredMating first F hF0 hF1),
    expectation_inbredMating_diploidSum, expectation_inbredMating_diploidSum,
    sub_eq_iff_eq_add] at hinbred
  rw [FiniteReportLaw.covariance_eq_rawMoments, expectation_cohortMating, expectation_cohortMating,
    expectation_cohortMating, expectation_admixedMating_diploidSum,
    expectation_admixedMating_diploidSum, expectation_inbredMating_diploidSum,
    expectation_inbredMating_diploidSum, hadmixed, hinbred]
  ring

end Genotypes

/-! ## Admixed genotypes along a history -/

section History

variable {Deme Locus : Type*} {Allele : Locus → Type*}
variable [Fintype Deme] [DecidableEq Deme] [Fintype Locus] [DecidableEq Locus]
  [∀ ℓ, Fintype (Allele ℓ)] [∀ ℓ, DecidableEq (Allele ℓ)]

/-- The F1 gamete-pair law of a deme pair at a state. -/
def stateAdmixedLaw (y : FrequencyState Deme Locus Allele) (first second : Deme) :
    FiniteReportLaw (FullHaplotype Locus Allele × FullHaplotype Locus Allele) :=
  admixedMating (stateLaw y first) (stateLaw y second)

/-- The F1 mean of an additive observable, as a frequency polynomial of degree one in the
haplotype frequencies of the two parental demes. -/
def admixedMeanPolynomial (first second : Deme) (value : FullHaplotype Locus Allele → ℝ) :
    FrequencyPolynomial Deme Locus Allele :=
  demeMeanPolynomial first value + demeMeanPolynomial second value

/-- The F1 covariance of additive score and outcome, as a frequency polynomial of degree two. -/
def admixedCovariancePolynomial (first second : Deme)
    (score outcome : FullHaplotype Locus Allele → ℝ) : FrequencyPolynomial Deme Locus Allele :=
  demeCovariancePolynomial first score outcome + demeCovariancePolynomial second score outcome

/-- The F1 correlation numerator `16 (C_a + C_b)²`, as a frequency polynomial of degree four. -/
def admixedNumeratorPolynomial (first second : Deme)
    (score outcome : FullHaplotype Locus Allele → ℝ) : FrequencyPolynomial Deme Locus Allele :=
  MvPolynomial.C 16 * admixedCovariancePolynomial first second score outcome ^ 2

/-- The F1 correlation denominator `16 (V_{S,a} + V_{S,b}) (V_{Y,a} + V_{Y,b})`, as a frequency
polynomial of degree four. -/
def admixedDenominatorPolynomial (first second : Deme)
    (score outcome : FullHaplotype Locus Allele → ℝ) : FrequencyPolynomial Deme Locus Allele :=
  MvPolynomial.C 16 * (admixedCovariancePolynomial first second score score
    * admixedCovariancePolynomial first second outcome outcome)

/-- At a state, the F1 mean polynomial is the mean of the additive lift under the F1 law. -/
theorem polynomialFunction_admixedMeanPolynomial (first second : Deme)
    (value : FullHaplotype Locus Allele → ℝ) (y : FrequencyState Deme Locus Allele) :
    polynomialFunction (admixedMeanPolynomial first second value) y
      = (stateAdmixedLaw y first second).expectation (diploidSum value) := by
  rw [stateAdmixedLaw, expectation_admixedMating_diploidSum,
    ← polynomialFunction_demeMeanPolynomial first value y,
    ← polynomialFunction_demeMeanPolynomial second value y]
  simp only [polynomialFunction_apply, admixedMeanPolynomial, map_add]

/-- At a state, the F1 covariance polynomial is the covariance of the additive lifts under the F1
law. -/
theorem polynomialFunction_admixedCovariancePolynomial (first second : Deme)
    (score outcome : FullHaplotype Locus Allele → ℝ) (y : FrequencyState Deme Locus Allele) :
    polynomialFunction (admixedCovariancePolynomial first second score outcome) y
      = (stateAdmixedLaw y first second).covariance (diploidSum score) (diploidSum outcome) := by
  rw [stateAdmixedLaw, covariance_admixedMating_diploidSum,
    ← polynomialFunction_demeCovariancePolynomial first score outcome y,
    ← polynomialFunction_demeCovariancePolynomial second score outcome y]
  simp only [polynomialFunction_apply, admixedCovariancePolynomial, map_add]

/-- At a state, the F1 numerator polynomial is the correlation numerator of the F1 law. -/
theorem polynomialFunction_admixedNumeratorPolynomial (first second : Deme)
    (score outcome : FullHaplotype Locus Allele → ℝ) (y : FrequencyState Deme Locus Allele) :
    polynomialFunction (admixedNumeratorPolynomial first second score outcome) y
      = correlationNumerator (stateAdmixedLaw y first second) (diploidSum score)
          (diploidSum outcome) := by
  rw [correlationNumerator,
    ← polynomialFunction_admixedCovariancePolynomial first second score outcome y]
  simp only [polynomialFunction_apply, admixedNumeratorPolynomial, map_mul, map_pow, eval_C]

/-- At a state, the F1 denominator polynomial is the correlation denominator of the F1 law. -/
theorem polynomialFunction_admixedDenominatorPolynomial (first second : Deme)
    (score outcome : FullHaplotype Locus Allele → ℝ) (y : FrequencyState Deme Locus Allele) :
    polynomialFunction (admixedDenominatorPolynomial first second score outcome) y
      = correlationDenominator (stateAdmixedLaw y first second) (diploidSum score)
          (diploidSum outcome) := by
  rw [correlationDenominator, FiniteReportLaw.variance, FiniteReportLaw.variance,
    ← polynomialFunction_admixedCovariancePolynomial first second score score y,
    ← polynomialFunction_admixedCovariancePolynomial first second outcome outcome y]
  simp only [polynomialFunction_apply, admixedDenominatorPolynomial, map_mul, eval_C]

/-- The F1 mean polynomial has total degree at most one. -/
theorem totalDegree_admixedMeanPolynomial_le (first second : Deme)
    (value : FullHaplotype Locus Allele → ℝ) :
    (admixedMeanPolynomial first second value).totalDegree ≤ 1 :=
  (totalDegree_add _ _).trans
    (max_le (totalDegree_demeMeanPolynomial_le first value)
      (totalDegree_demeMeanPolynomial_le second value))

/-- The F1 covariance polynomial has total degree at most two. -/
theorem totalDegree_admixedCovariancePolynomial_le (first second : Deme)
    (score outcome : FullHaplotype Locus Allele → ℝ) :
    (admixedCovariancePolynomial first second score outcome).totalDegree ≤ 2 :=
  (totalDegree_add _ _).trans
    (max_le (totalDegree_demeCovariancePolynomial_le first score outcome)
      (totalDegree_demeCovariancePolynomial_le second score outcome))

/-- The F1 numerator polynomial has total degree at most four. -/
theorem totalDegree_admixedNumeratorPolynomial_le (first second : Deme)
    (score outcome : FullHaplotype Locus Allele → ℝ) :
    (admixedNumeratorPolynomial first second score outcome).totalDegree ≤ 4 := by
  have hcovariance := totalDegree_admixedCovariancePolynomial_le first second score outcome
  have hpow := totalDegree_pow (admixedCovariancePolynomial first second score outcome) 2
  refine (totalDegree_mul _ _).trans ?_
  rw [totalDegree_C]
  omega

/-- The F1 denominator polynomial has total degree at most four. -/
theorem totalDegree_admixedDenominatorPolynomial_le (first second : Deme)
    (score outcome : FullHaplotype Locus Allele → ℝ) :
    (admixedDenominatorPolynomial first second score outcome).totalDegree ≤ 4 := by
  have hscore := totalDegree_admixedCovariancePolynomial_le first second score score
  have houtcome := totalDegree_admixedCovariancePolynomial_le first second outcome outcome
  have hproduct := totalDegree_mul (admixedCovariancePolynomial first second score score)
    (admixedCovariancePolynomial first second outcome outcome)
  refine (totalDegree_mul _ _).trans ?_
  rw [totalDegree_C]
  omega

/-! ## F1 moments at their budgets -/

/-- **The expected F1 mean along a history**, at every budget `n ≥ 1`. -/
theorem integral_admixedMean_historyEventKernel (ℓ₀ : Locus) (hap₀ : FullHaplotype Locus Allele)
    (events : List ((NeutralRates Deme Locus Allele × ℝ≥0) ⊕ PulseMatrix Deme)) {n : ℕ}
    (hn : 1 ≤ n) (x0 : FrequencyState Deme Locus Allele) (first second : Deme)
    (value : FullHaplotype Locus Allele → ℝ) :
    ∫ y, (stateAdmixedLaw y first second).expectation (diploidSum value)
        ∂(historyEventKernel ℓ₀ hap₀ events x0)
      = budgetCoefficients ℓ₀ (fun _ ↦ n) (admixedMeanPolynomial first second value)
        ⬝ᵥ (historyEventPropagator (fun _ ↦ n) events *ᵥ budgetMomentFeature (fun _ ↦ n) x0) :=
  integral_historyEventKernel_of_totalDegree_le ℓ₀ hap₀ events x0 _
    ((totalDegree_admixedMeanPolynomial_le first second value).trans hn) _
    (polynomialFunction_admixedMeanPolynomial first second value)

/-- **The expected F1 covariance along a history**, at every budget `n ≥ 2`. -/
theorem integral_admixedCovariance_historyEventKernel (ℓ₀ : Locus)
    (hap₀ : FullHaplotype Locus Allele)
    (events : List ((NeutralRates Deme Locus Allele × ℝ≥0) ⊕ PulseMatrix Deme)) {n : ℕ}
    (hn : 2 ≤ n) (x0 : FrequencyState Deme Locus Allele) (first second : Deme)
    (score outcome : FullHaplotype Locus Allele → ℝ) :
    ∫ y, (stateAdmixedLaw y first second).covariance (diploidSum score) (diploidSum outcome)
        ∂(historyEventKernel ℓ₀ hap₀ events x0)
      = budgetCoefficients ℓ₀ (fun _ ↦ n) (admixedCovariancePolynomial first second score outcome)
        ⬝ᵥ (historyEventPropagator (fun _ ↦ n) events *ᵥ budgetMomentFeature (fun _ ↦ n) x0) :=
  integral_historyEventKernel_of_totalDegree_le ℓ₀ hap₀ events x0 _
    ((totalDegree_admixedCovariancePolynomial_le first second score outcome).trans hn) _
    (polynomialFunction_admixedCovariancePolynomial first second score outcome)

/-- **The expected F1 variance along a history**, at every budget `n ≥ 2`. -/
theorem integral_admixedVariance_historyEventKernel (ℓ₀ : Locus)
    (hap₀ : FullHaplotype Locus Allele)
    (events : List ((NeutralRates Deme Locus Allele × ℝ≥0) ⊕ PulseMatrix Deme)) {n : ℕ}
    (hn : 2 ≤ n) (x0 : FrequencyState Deme Locus Allele) (first second : Deme)
    (value : FullHaplotype Locus Allele → ℝ) :
    ∫ y, (stateAdmixedLaw y first second).variance (diploidSum value)
        ∂(historyEventKernel ℓ₀ hap₀ events x0)
      = budgetCoefficients ℓ₀ (fun _ ↦ n) (admixedCovariancePolynomial first second value value)
        ⬝ᵥ (historyEventPropagator (fun _ ↦ n) events *ᵥ budgetMomentFeature (fun _ ↦ n) x0) :=
  integral_admixedCovariance_historyEventKernel ℓ₀ hap₀ events hn x0 first second value value

/-- **The expected F1 correlation numerator along a history**, at every budget `n ≥ 4`. -/
theorem integral_admixedNumerator_historyEventKernel (ℓ₀ : Locus)
    (hap₀ : FullHaplotype Locus Allele)
    (events : List ((NeutralRates Deme Locus Allele × ℝ≥0) ⊕ PulseMatrix Deme)) {n : ℕ}
    (hn : 4 ≤ n) (x0 : FrequencyState Deme Locus Allele) (first second : Deme)
    (score outcome : FullHaplotype Locus Allele → ℝ) :
    ∫ y, correlationNumerator (stateAdmixedLaw y first second) (diploidSum score)
        (diploidSum outcome) ∂(historyEventKernel ℓ₀ hap₀ events x0)
      = budgetCoefficients ℓ₀ (fun _ ↦ n) (admixedNumeratorPolynomial first second score outcome)
        ⬝ᵥ (historyEventPropagator (fun _ ↦ n) events *ᵥ budgetMomentFeature (fun _ ↦ n) x0) :=
  integral_historyEventKernel_of_totalDegree_le ℓ₀ hap₀ events x0 _
    ((totalDegree_admixedNumeratorPolynomial_le first second score outcome).trans hn) _
    (polynomialFunction_admixedNumeratorPolynomial first second score outcome)

/-- **The expected F1 correlation denominator along a history**, at every budget `n ≥ 4`. -/
theorem integral_admixedDenominator_historyEventKernel (ℓ₀ : Locus)
    (hap₀ : FullHaplotype Locus Allele)
    (events : List ((NeutralRates Deme Locus Allele × ℝ≥0) ⊕ PulseMatrix Deme)) {n : ℕ}
    (hn : 4 ≤ n) (x0 : FrequencyState Deme Locus Allele) (first second : Deme)
    (score outcome : FullHaplotype Locus Allele → ℝ) :
    ∫ y, correlationDenominator (stateAdmixedLaw y first second) (diploidSum score)
        (diploidSum outcome) ∂(historyEventKernel ℓ₀ hap₀ events x0)
      = budgetCoefficients ℓ₀ (fun _ ↦ n)
          (admixedDenominatorPolynomial first second score outcome)
        ⬝ᵥ (historyEventPropagator (fun _ ↦ n) events *ᵥ budgetMomentFeature (fun _ ↦ n) x0) :=
  integral_historyEventKernel_of_totalDegree_le ℓ₀ hap₀ events x0 _
    ((totalDegree_admixedDenominatorPolynomial_le first second score outcome).trans hn) _
    (polynomialFunction_admixedDenominatorPolynomial first second score outcome)

/-! ## Portability from a diploid source deme to admixed individuals -/

/-- **Expected portability to admixed individuals**: the ratio `(E N_ab · E D_s) / (E D_ab · E N_s)`
of expected correlation numerators and denominators of the additive diploid score, with the F1
crosses of `first` and `second` as target and the diploids of `source`, formed at its inbreeding
coefficient, as source. -/
def expectedAdmixedPortability
    (κ : Kernel (FrequencyState Deme Locus Allele) (FrequencyState Deme Locus Allele))
    (x0 : FrequencyState Deme Locus Allele) (source first second : Deme) (inbreeding : Deme → ℝ)
    (hF0 : ∀ other, 0 ≤ inbreeding other) (hF1 : ∀ other, inbreeding other ≤ 1)
    (score outcome : FullHaplotype Locus Allele → ℝ) : ℝ :=
  ((∫ y, correlationNumerator (stateAdmixedLaw y first second) (diploidSum score)
        (diploidSum outcome) ∂(κ x0))
      * ∫ y, correlationDenominator (stateGenotypeLaw y source inbreeding hF0 hF1)
        (diploidSum score) (diploidSum outcome) ∂(κ x0))
    / ((∫ y, correlationDenominator (stateAdmixedLaw y first second) (diploidSum score)
        (diploidSum outcome) ∂(κ x0))
      * ∫ y, correlationNumerator (stateGenotypeLaw y source inbreeding hF0 hF1)
        (diploidSum score) (diploidSum outcome) ∂(κ x0))

/-- **The source inbreeding coefficient cancels.**  Under every kernel the portability to admixed
individuals reads the source deme through its haploid numerator and denominator: `4 (1 + F_s)²`
multiplies both and cancels. -/
theorem expectedAdmixedPortability_eq_haploidSource
    (κ : Kernel (FrequencyState Deme Locus Allele) (FrequencyState Deme Locus Allele))
    (x0 : FrequencyState Deme Locus Allele) (source first second : Deme) (inbreeding : Deme → ℝ)
    (hF0 : ∀ other, 0 ≤ inbreeding other) (hF1 : ∀ other, inbreeding other ≤ 1)
    (score outcome : FullHaplotype Locus Allele → ℝ) :
    expectedAdmixedPortability κ x0 source first second inbreeding hF0 hF1 score outcome
      = ((∫ y, correlationNumerator (stateAdmixedLaw y first second) (diploidSum score)
            (diploidSum outcome) ∂(κ x0))
          * ∫ y, correlationDenominator (stateLaw y source) score outcome ∂(κ x0))
        / ((∫ y, correlationDenominator (stateAdmixedLaw y first second) (diploidSum score)
            (diploidSum outcome) ∂(κ x0))
          * ∫ y, correlationNumerator (stateLaw y source) score outcome ∂(κ x0)) := by
  have hscale : 4 * (1 + inbreeding source) ^ 2 ≠ 0 :=
    (mul_pos (by norm_num) (pow_pos (by linarith [hF0 source]) 2)).ne'
  simp only [expectedAdmixedPortability, stateGenotypeLaw,
    correlationNumerator_inbredMating_diploidSum, correlationDenominator_inbredMating_diploidSum,
    integral_const_mul]
  rw [mul_left_comm _ (4 * (1 + inbreeding source) ^ 2),
    mul_left_comm _ (4 * (1 + inbreeding source) ^ 2)]
  exact mul_div_mul_left _ _ hscale

/-- **The rational portability function to admixed individuals** of a budget-4 moment vector: the
F1 coefficient vectors of the deme pair against the haploid coefficient vectors of the source. -/
def admixedMomentPortability (ℓ₀ : Locus) (source first second : Deme)
    (score outcome : FullHaplotype Locus Allele → ℝ)
    (v : BudgetConfiguration Deme Locus Allele (fun _ ↦ 4) → ℝ) : ℝ :=
  ((budgetCoefficients ℓ₀ (fun _ ↦ 4) (admixedNumeratorPolynomial first second score outcome)
        ⬝ᵥ v)
      * (budgetCoefficients ℓ₀ (fun _ ↦ 4) (denominatorPolynomial source score outcome) ⬝ᵥ v))
    / ((budgetCoefficients ℓ₀ (fun _ ↦ 4)
        (admixedDenominatorPolynomial first second score outcome) ⬝ᵥ v)
      * (budgetCoefficients ℓ₀ (fun _ ↦ 4) (numeratorPolynomial source score outcome) ⬝ᵥ v))

/-- **The portability law to admixed individuals along a history of epochs, splits and pulses.**
The expected portability of the additive diploid score from a source deme to the F1 crosses of a
deme pair is the rational function `admixedMomentPortability` of the chronological propagator
applied to the budget-4 moments of `x₀`, whatever the source inbreeding coefficient. -/
theorem expectedAdmixedPortability_historyEventKernel (ℓ₀ : Locus)
    (hap₀ : FullHaplotype Locus Allele)
    (events : List ((NeutralRates Deme Locus Allele × ℝ≥0) ⊕ PulseMatrix Deme))
    (x0 : FrequencyState Deme Locus Allele) (source first second : Deme) (inbreeding : Deme → ℝ)
    (hF0 : ∀ other, 0 ≤ inbreeding other) (hF1 : ∀ other, inbreeding other ≤ 1)
    (score outcome : FullHaplotype Locus Allele → ℝ) :
    expectedAdmixedPortability (historyEventKernel ℓ₀ hap₀ events) x0 source first second
        inbreeding hF0 hF1 score outcome
      = admixedMomentPortability ℓ₀ source first second score outcome
          (historyEventPropagator (fun _ ↦ 4) events *ᵥ budgetMomentFeature (fun _ ↦ 4) x0) := by
  rw [expectedAdmixedPortability_eq_haploidSource,
    integral_admixedNumerator_historyEventKernel ℓ₀ hap₀ events le_rfl,
    integral_admixedDenominator_historyEventKernel ℓ₀ hap₀ events le_rfl,
    integral_correlationNumerator_historyEventKernel,
    integral_correlationDenominator_historyEventKernel]
  rfl

/-- **The portability law to admixed individuals along a time-varying rate history.** -/
theorem expectedAdmixedPortability_rateHistoryKernel
    {rates : ℝ → NeutralRates Deme Locus Allele} {T : ℝ} (hT : 0 ≤ T)
    (hcontinuous : ∀ capacity : Locus → ℕ,
      ContinuousOn (fun t ↦ dualGenerator (rates t) capacity) (Set.Icc 0 T))
    (ℓ₀ : Locus) (hap₀ : FullHaplotype Locus Allele) (x0 : FrequencyState Deme Locus Allele)
    (source first second : Deme) (inbreeding : Deme → ℝ) (hF0 : ∀ other, 0 ≤ inbreeding other)
    (hF1 : ∀ other, inbreeding other ≤ 1) (score outcome : FullHaplotype Locus Allele → ℝ) :
    expectedAdmixedPortability (rateHistoryKernel rates ℓ₀ hap₀ hT hcontinuous) x0 source first
        second inbreeding hF0 hF1 score outcome
      = admixedMomentPortability ℓ₀ source first second score outcome
          (rateHistoryDualPropagator rates (fun _ ↦ 4) T
            *ᵥ budgetMomentFeature (fun _ ↦ 4) x0) := by
  rw [expectedAdmixedPortability_eq_haploidSource,
    integral_rateHistoryKernel_of_totalDegree_le hT hcontinuous ℓ₀ hap₀ x0 _
      (totalDegree_admixedNumeratorPolynomial_le first second score outcome) _
      (polynomialFunction_admixedNumeratorPolynomial first second score outcome),
    integral_rateHistoryKernel_of_totalDegree_le hT hcontinuous ℓ₀ hap₀ x0 _
      (totalDegree_admixedDenominatorPolynomial_le first second score outcome) _
      (polynomialFunction_admixedDenominatorPolynomial first second score outcome),
    integral_correlationNumerator_rateHistoryKernel,
    integral_correlationDenominator_rateHistoryKernel]
  rfl

/-- **Portability to admixed individuals sees the history only through finitely many moments.**
Two histories, from two initial states, whose propagated budget-4 moments agree give equal
portability for every source deme, every deme pair and every additive score and outcome. -/
theorem expectedAdmixedPortability_eq_of_moments_eq (ℓ₀ : Locus)
    (hap₀ : FullHaplotype Locus Allele) (source first second : Deme) (inbreeding : Deme → ℝ)
    (hF0 : ∀ other, 0 ≤ inbreeding other) (hF1 : ∀ other, inbreeding other ≤ 1)
    (score outcome : FullHaplotype Locus Allele → ℝ)
    {events₁ events₂ : List ((NeutralRates Deme Locus Allele × ℝ≥0) ⊕ PulseMatrix Deme)}
    {x₁ x₂ : FrequencyState Deme Locus Allele}
    (hmoments : historyEventPropagator (fun _ ↦ 4) events₁ *ᵥ budgetMomentFeature (fun _ ↦ 4) x₁
      = historyEventPropagator (fun _ ↦ 4) events₂ *ᵥ budgetMomentFeature (fun _ ↦ 4) x₂) :
    expectedAdmixedPortability (historyEventKernel ℓ₀ hap₀ events₁) x₁ source first second
        inbreeding hF0 hF1 score outcome
      = expectedAdmixedPortability (historyEventKernel ℓ₀ hap₀ events₂) x₂ source first second
          inbreeding hF0 hF1 score outcome := by
  rw [expectedAdmixedPortability_historyEventKernel, expectedAdmixedPortability_historyEventKernel,
    hmoments]

/-! ## Calibration on admixed individuals -/

/-- **The F1 calibration slope of expectations**: the expected F1 covariance of additive score and
outcome over the expected F1 score variance. -/
def expectedAdmixedCalibrationSlope
    (κ : Kernel (FrequencyState Deme Locus Allele) (FrequencyState Deme Locus Allele))
    (x0 : FrequencyState Deme Locus Allele) (first second : Deme)
    (score outcome : FullHaplotype Locus Allele → ℝ) : ℝ :=
  (∫ y, (stateAdmixedLaw y first second).covariance (diploidSum score) (diploidSum outcome)
      ∂(κ x0))
    / ∫ y, (stateAdmixedLaw y first second).variance (diploidSum score) ∂(κ x0)

/-- **The calibration portability to admixed individuals**: the F1 slope of expectations over the
diploid slope of expectations of the source deme. -/
def expectedAdmixedCalibrationPortability
    (κ : Kernel (FrequencyState Deme Locus Allele) (FrequencyState Deme Locus Allele))
    (x0 : FrequencyState Deme Locus Allele) (source first second : Deme) (inbreeding : Deme → ℝ)
    (hF0 : ∀ other, 0 ≤ inbreeding other) (hF1 : ∀ other, inbreeding other ≤ 1)
    (score outcome : FullHaplotype Locus Allele → ℝ) : ℝ :=
  expectedAdmixedCalibrationSlope κ x0 first second score outcome
    / expectedDiploidCalibrationSlope κ x0 source inbreeding hF0 hF1 (diploidSum score)
      (diploidSum outcome)

/-- **The rational F1 calibration slope** of a budget-`n` moment vector. -/
def momentAdmixedCalibrationSlope (ℓ₀ : Locus) (n : ℕ) (first second : Deme)
    (score outcome : FullHaplotype Locus Allele → ℝ)
    (v : BudgetConfiguration Deme Locus Allele (fun _ ↦ n) → ℝ) : ℝ :=
  (budgetCoefficients ℓ₀ (fun _ ↦ n) (admixedCovariancePolynomial first second score outcome)
      ⬝ᵥ v)
    / (budgetCoefficients ℓ₀ (fun _ ↦ n) (admixedCovariancePolynomial first second score score)
      ⬝ᵥ v)

/-- **The F1 calibration slope along a history** is, at every budget `n ≥ 2`, the rational F1
slope of the propagated budget-`n` moments. -/
theorem expectedAdmixedCalibrationSlope_historyEventKernel (ℓ₀ : Locus)
    (hap₀ : FullHaplotype Locus Allele)
    (events : List ((NeutralRates Deme Locus Allele × ℝ≥0) ⊕ PulseMatrix Deme)) {n : ℕ}
    (hn : 2 ≤ n) (x0 : FrequencyState Deme Locus Allele) (first second : Deme)
    (score outcome : FullHaplotype Locus Allele → ℝ) :
    expectedAdmixedCalibrationSlope (historyEventKernel ℓ₀ hap₀ events) x0 first second score
        outcome
      = momentAdmixedCalibrationSlope ℓ₀ n first second score outcome
          (historyEventPropagator (fun _ ↦ n) events *ᵥ budgetMomentFeature (fun _ ↦ n) x0) := by
  rw [expectedAdmixedCalibrationSlope,
    integral_admixedCovariance_historyEventKernel ℓ₀ hap₀ events hn,
    integral_admixedVariance_historyEventKernel ℓ₀ hap₀ events hn]
  rfl

/-- **Calibration portability to admixed individuals along a history.**  At every budget `n ≥ 2`
it is the rational F1 slope of the deme pair over the haploid rational slope of the source deme,
both of the propagated budget-`n` moments, whatever the source inbreeding coefficient. -/
theorem expectedAdmixedCalibrationPortability_historyEventKernel (ℓ₀ : Locus)
    (hap₀ : FullHaplotype Locus Allele)
    (events : List ((NeutralRates Deme Locus Allele × ℝ≥0) ⊕ PulseMatrix Deme)) {n : ℕ}
    (hn : 2 ≤ n) (x0 : FrequencyState Deme Locus Allele) (source first second : Deme)
    (inbreeding : Deme → ℝ) (hF0 : ∀ other, 0 ≤ inbreeding other)
    (hF1 : ∀ other, inbreeding other ≤ 1) (score outcome : FullHaplotype Locus Allele → ℝ) :
    expectedAdmixedCalibrationPortability (historyEventKernel ℓ₀ hap₀ events) x0 source first
        second inbreeding hF0 hF1 score outcome
      = momentAdmixedCalibrationSlope ℓ₀ n first second score outcome
          (historyEventPropagator (fun _ ↦ n) events *ᵥ budgetMomentFeature (fun _ ↦ n) x0)
        / momentCalibrationSlope ℓ₀ n source score outcome
          (historyEventPropagator (fun _ ↦ n) events *ᵥ budgetMomentFeature (fun _ ↦ n) x0) := by
  rw [expectedAdmixedCalibrationPortability,
    expectedAdmixedCalibrationSlope_historyEventKernel ℓ₀ hap₀ events hn,
    expectedDiploidCalibrationSlope_diploidSum_historyEventKernel ℓ₀ hap₀ events hn]

/-! ## The admixture cohort along a history -/

/-- The admixture cohort of a deme pair at a state: F1 crosses of `first` and `second` with
probability `π`, and diploids of `first` at its inbreeding coefficient otherwise. -/
def stateCohortLaw (y : FrequencyState Deme Locus Allele) (proportion : ℝ) (hp0 : 0 ≤ proportion)
    (hp1 : proportion ≤ 1) (first second : Deme) (inbreeding : Deme → ℝ)
    (hF0 : ∀ other, 0 ≤ inbreeding other) (hF1 : ∀ other, inbreeding other ≤ 1) :
    FiniteReportLaw (FullHaplotype Locus Allele × FullHaplotype Locus Allele) :=
  cohortMating proportion hp0 hp1 (stateLaw y first) (stateLaw y second) (inbreeding first)
    (hF0 first) (hF1 first)

/-- The cohort covariance of additive score and outcome, as a frequency polynomial of degree
two: the mixture of the F1 and deme covariance polynomials and the between-group product of the
differences of the deme mean polynomials. -/
def cohortCovariancePolynomial (proportion : ℝ) (first second : Deme) (inbreeding : Deme → ℝ)
    (score outcome : FullHaplotype Locus Allele → ℝ) : FrequencyPolynomial Deme Locus Allele :=
  MvPolynomial.C proportion * admixedCovariancePolynomial first second score outcome
    + MvPolynomial.C (1 - proportion)
      * (MvPolynomial.C (2 * (1 + inbreeding first))
        * demeCovariancePolynomial first score outcome)
    + MvPolynomial.C (proportion * (1 - proportion))
      * ((demeMeanPolynomial second score - demeMeanPolynomial first score)
        * (demeMeanPolynomial second outcome - demeMeanPolynomial first outcome))

/-- At a state, the cohort covariance polynomial is the covariance of the additive lifts under the
cohort law. -/
theorem polynomialFunction_cohortCovariancePolynomial (proportion : ℝ) (hp0 : 0 ≤ proportion)
    (hp1 : proportion ≤ 1) (first second : Deme) (inbreeding : Deme → ℝ)
    (hF0 : ∀ other, 0 ≤ inbreeding other) (hF1 : ∀ other, inbreeding other ≤ 1)
    (score outcome : FullHaplotype Locus Allele → ℝ) (y : FrequencyState Deme Locus Allele) :
    polynomialFunction (cohortCovariancePolynomial proportion first second inbreeding score outcome)
        y
      = (stateCohortLaw y proportion hp0 hp1 first second inbreeding hF0 hF1).covariance
          (diploidSum score) (diploidSum outcome) := by
  have hcovariance : ∀ (deme : Deme) (f g : FullHaplotype Locus Allele → ℝ),
      MvPolynomial.eval y.1 (demeCovariancePolynomial deme f g)
        = (stateLaw y deme).covariance f g :=
    fun deme f g ↦ polynomialFunction_demeCovariancePolynomial deme f g y
  have hmean : ∀ (deme : Deme) (f : FullHaplotype Locus Allele → ℝ),
      MvPolynomial.eval y.1 (demeMeanPolynomial deme f) = (stateLaw y deme).expectation f :=
    fun deme f ↦ polynomialFunction_demeMeanPolynomial deme f y
  rw [stateCohortLaw, covariance_cohortMating_diploidSum]
  simp only [polynomialFunction_apply, cohortCovariancePolynomial, admixedCovariancePolynomial,
    map_add, map_sub, map_mul, eval_C, hcovariance, hmean]

/-- At a state, the cohort covariance polynomial of an observable with itself is its variance under
the cohort law. -/
theorem polynomialFunction_cohortVariance (proportion : ℝ) (hp0 : 0 ≤ proportion)
    (hp1 : proportion ≤ 1) (first second : Deme) (inbreeding : Deme → ℝ)
    (hF0 : ∀ other, 0 ≤ inbreeding other) (hF1 : ∀ other, inbreeding other ≤ 1)
    (value : FullHaplotype Locus Allele → ℝ) (y : FrequencyState Deme Locus Allele) :
    polynomialFunction (cohortCovariancePolynomial proportion first second inbreeding value value) y
      = (stateCohortLaw y proportion hp0 hp1 first second inbreeding hF0 hF1).variance
          (diploidSum value) :=
  polynomialFunction_cohortCovariancePolynomial proportion hp0 hp1 first second inbreeding hF0 hF1
    value value y

/-- The cohort covariance polynomial has total degree at most two. -/
theorem totalDegree_cohortCovariancePolynomial_le (proportion : ℝ) (first second : Deme)
    (inbreeding : Deme → ℝ) (score outcome : FullHaplotype Locus Allele → ℝ) :
    (cohortCovariancePolynomial proportion first second inbreeding score outcome).totalDegree
      ≤ 2 := by
  have hconstant : ∀ (c : ℝ) (p : FrequencyPolynomial Deme Locus Allele), p.totalDegree ≤ 2 →
      (MvPolynomial.C c * p).totalDegree ≤ 2 := fun c p hp ↦
    (totalDegree_mul _ _).trans (by rw [totalDegree_C, zero_add]; exact hp)
  have hdifference : ∀ value : FullHaplotype Locus Allele → ℝ,
      (demeMeanPolynomial second value - demeMeanPolynomial first value).totalDegree ≤ 1 :=
    fun value ↦ (totalDegree_sub _ _).trans
      (max_le (totalDegree_demeMeanPolynomial_le second value)
        (totalDegree_demeMeanPolynomial_le first value))
  refine (totalDegree_add _ _).trans (max_le ((totalDegree_add _ _).trans (max_le ?_ ?_)) ?_)
  · exact hconstant _ _ (totalDegree_admixedCovariancePolynomial_le first second score outcome)
  · exact hconstant _ _
      (hconstant _ _ (totalDegree_demeCovariancePolynomial_le first score outcome))
  · exact hconstant _ _
      ((totalDegree_mul _ _).trans (Nat.add_le_add (hdifference score) (hdifference outcome)))

/-- **The cohort calibration slope of expectations**: the expected pooled covariance over the
expected pooled score variance of the admixture cohort. -/
def expectedCohortCalibrationSlope
    (κ : Kernel (FrequencyState Deme Locus Allele) (FrequencyState Deme Locus Allele))
    (x0 : FrequencyState Deme Locus Allele) (proportion : ℝ) (hp0 : 0 ≤ proportion)
    (hp1 : proportion ≤ 1) (first second : Deme) (inbreeding : Deme → ℝ)
    (hF0 : ∀ other, 0 ≤ inbreeding other) (hF1 : ∀ other, inbreeding other ≤ 1)
    (score outcome : FullHaplotype Locus Allele → ℝ) : ℝ :=
  (∫ y, (stateCohortLaw y proportion hp0 hp1 first second inbreeding hF0 hF1).covariance
      (diploidSum score) (diploidSum outcome) ∂(κ x0))
    / ∫ y, (stateCohortLaw y proportion hp0 hp1 first second inbreeding hF0 hF1).variance
      (diploidSum score) ∂(κ x0)

/-- **The cohort calibration slope along a history** is, at every budget `n ≥ 2`, the ratio of the
cohort covariance polynomials' coefficient vectors dotted with the propagated budget-`n` moments. -/
theorem expectedCohortCalibrationSlope_historyEventKernel (ℓ₀ : Locus)
    (hap₀ : FullHaplotype Locus Allele)
    (events : List ((NeutralRates Deme Locus Allele × ℝ≥0) ⊕ PulseMatrix Deme)) {n : ℕ}
    (hn : 2 ≤ n) (x0 : FrequencyState Deme Locus Allele) (proportion : ℝ) (hp0 : 0 ≤ proportion)
    (hp1 : proportion ≤ 1) (first second : Deme) (inbreeding : Deme → ℝ)
    (hF0 : ∀ other, 0 ≤ inbreeding other) (hF1 : ∀ other, inbreeding other ≤ 1)
    (score outcome : FullHaplotype Locus Allele → ℝ) :
    expectedCohortCalibrationSlope (historyEventKernel ℓ₀ hap₀ events) x0 proportion hp0 hp1 first
        second inbreeding hF0 hF1 score outcome
      = (budgetCoefficients ℓ₀ (fun _ ↦ n)
            (cohortCovariancePolynomial proportion first second inbreeding score outcome)
          ⬝ᵥ (historyEventPropagator (fun _ ↦ n) events *ᵥ budgetMomentFeature (fun _ ↦ n) x0))
        / (budgetCoefficients ℓ₀ (fun _ ↦ n)
            (cohortCovariancePolynomial proportion first second inbreeding score score)
          ⬝ᵥ (historyEventPropagator (fun _ ↦ n) events
            *ᵥ budgetMomentFeature (fun _ ↦ n) x0)) := by
  rw [expectedCohortCalibrationSlope,
    integral_historyEventKernel_of_totalDegree_le ℓ₀ hap₀ events x0 _
      ((totalDegree_cohortCovariancePolynomial_le proportion first second inbreeding score
        outcome).trans hn) _
      (polynomialFunction_cohortCovariancePolynomial proportion hp0 hp1 first second inbreeding hF0
        hF1 score outcome),
    integral_historyEventKernel_of_totalDegree_le ℓ₀ hap₀ events x0 _
      ((totalDegree_cohortCovariancePolynomial_le proportion first second inbreeding score
        score).trans hn) _
      (polynomialFunction_cohortVariance proportion hp0 hp1 first second inbreeding hF0 hF1 score)]

end History

end

end Descent.Portability.EndToEndAdmixedGenotypes
