/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.EndToEndPortabilityRateLipschitz

assert_below Descent.Decision Descent.Program

/-!
# The end-to-end calibration law of polygenic-score portability

`EndToEndPortabilityLaw` carries a demographic history to the portability of accuracy, the
squared correlation.  This module carries it to calibration: the regression of the outcome on
the score, its slope and its intercept, from source to target.

The input.  A neutral history runs from a frequency state `x₀`: a list of epochs, splits and
admixture pulses (`historyEventKernel`), or a rate path with continuous dual generator
(`rateHistoryKernel`).  A score `S` and an outcome `Y` are functions of the haplotype.  In deme
`j` the corpus metrics of the haplotype law are the means `μ_S`, `μ_Y`, the covariance `C_SY`
and the variances `V_S`, `V_Y` (`FiniteReportLaw.expectation`, `covariance`, `variance`).

Propagated moments.  A mean is a frequency polynomial of degree one and a covariance one of
degree two (`demeMeanPolynomial`, `demeCovariancePolynomial`), so under either history kernel
`E μ`, `E C_SY`, `E V_S` and `E V_Y` are coefficient vectors dotted with the propagator applied
to the budget-`n` configuration moments of `x₀`, for every budget `n ≥ 1` for means and `n ≥ 2`
for covariances (`integral_expectation_historyEventKernel`,
`integral_covariance_historyEventKernel`, `integral_variance_historyEventKernel` and the
`rateHistoryKernel` forms).

Calibration of expectations.  The slope `E C_SY / E V_S` (`expectedCalibrationSlope`), the
portability `slope_t / slope_s = E C_t · E V_s / (E V_t · E C_s)`
(`expectedCalibrationPortability`, `expectedCalibrationPortability_eq_cross`) and the intercept
`E[μ_Y V_S - C_SY μ_S] / E V_S` (`expectedCalibrationIntercept`) are rational functions of the
propagated moments, at budget 2 for slope and portability and budget 3 for the intercept, whose
numerator has degree three (`expectedCalibrationSlope_historyEventKernel`,
`expectedCalibrationPortability_historyEventKernel`,
`expectedCalibrationIntercept_historyEventKernel`, and the rate forms).  Two histories that agree
on those propagated moments have equal calibration slope, portability and intercept of
expectations (`expectedCalibrationSlope_eq_of_moments_eq`,
`expectedCalibrationPortability_eq_of_moments_eq`,
`expectedCalibrationIntercept_eq_of_moments_eq`).  The portability is NOTE2 (27)'s
`PortabilityRatioQueries.portabilityRatio` of the four accumulators `C_s`, `V_s`, `C_t`, `V_t`
in expectation (`expectedCalibrationPortability_eq_portabilityRatio`).

The queries.  Every result above is the ratio-of-expectations query of NOTE2 §6.2.  It is not
the expectation of the per-population slope: it is the `V_S`-weighted expectation of the corpus
calibration slope, read as zero where the slope is undefined, over the expected weight
(`expectedCalibrationSlope_eq_weighted`), and likewise for the intercept
(`expectedCalibrationIntercept_eq_weighted`).  The weights make the ratio finite-moment: the
unweighted expectation of a ratio is not a rational function of finitely many moments.

Lipschitz dependence on the rate path.  The portability of expectations is the cross ratio of
`PortabilityMetricCompilation.abs_crossRatio_sub_le` on budget-2 moments.  Composed with the
propagator bound of `EndToEndPortabilityLipschitz`, it moves by at most an explicit constant
times the `L¹([0, T])` distance of the dual generator paths, wherever the expected target score
variance and the expected source covariance stay at least `δ`
(`abs_momentCalibrationPortability_rateHistory_sub_le`,
`abs_expectedCalibrationPortability_rateHistory_sub_le`).

Significance.  Demography reaches calibration, not only accuracy, as one finite matrix
computation: a propagator applied to budget-2 or budget-3 moments, then one rational function
with written-out coefficients.

Scope.  One chromosome is sampled per individual.  The expectation of the per-population slope
or intercept, the expectation-of-a-ratio query of NOTE2 §6.2, is not stated here.  The Lipschitz
bound is local: it needs the lower bound `δ` under both histories, and it covers rate histories
whose dual generators are continuous on the horizon.

## Empirical status

None.  The bodies here are polynomial identities, integrals of polynomials against Markov
kernels whose moments are matrix computations of supplied rates, and norm inequalities, so no
measurement can bear on them.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.EndToEndCalibrationLaw

open MeasureTheory ProbabilityTheory MvPolynomial Descent.Coalescent PartialHaplotypeCarrier
  PartialHaplotypeDualGenerator PartialHaplotypeDualSemigroup NeutralFellerGenerator
  NeutralPolynomialSemigroup PartialHaplotypeMicroscopicApproximation PartialHaplotypePulseKernel
  NeutralPulseHistoryKernel NeutralRateHistoryRealization NeutralRateHistoryKernel
  ReplicaMetricInstances EndToEndPortabilityLaw EndToEndPortabilityLipschitz
  EndToEndPortabilityRateLipschitz
open scoped Matrix NNReal Matrix.Norms.Operator

noncomputable section

variable {Deme Locus : Type*} {Allele : Locus → Type*}
variable [Fintype Deme] [DecidableEq Deme] [Fintype Locus] [DecidableEq Locus]
  [∀ ℓ, Fintype (Allele ℓ)] [∀ ℓ, DecidableEq (Allele ℓ)]

/-! ## Calibration accumulators as frequency polynomials -/

/-- The mean of a haplotype observable in one deme, as a frequency polynomial of degree one. -/
def demeMeanPolynomial (deme : Deme) (value : FullHaplotype Locus Allele → ℝ) :
    FrequencyPolynomial Deme Locus Allele :=
  demePolynomial deme (expectationPolynomial value)

/-- The covariance of two haplotype observables in one deme, as a frequency polynomial of degree
two. -/
def demeCovariancePolynomial (deme : Deme) (first second : FullHaplotype Locus Allele → ℝ) :
    FrequencyPolynomial Deme Locus Allele :=
  demePolynomial deme (covariancePolynomial first second)

/-- The intercept accumulator `μ_Y V_S - C_SY μ_S` of one deme, as a frequency polynomial of
degree three. -/
def interceptNumeratorPolynomial (deme : Deme) (score outcome : FullHaplotype Locus Allele → ℝ) :
    FrequencyPolynomial Deme Locus Allele :=
  demeMeanPolynomial deme outcome * demeCovariancePolynomial deme score score
    - demeCovariancePolynomial deme score outcome * demeMeanPolynomial deme score

/-- At a state, the mean polynomial is the corpus expectation under the deme's haplotype law. -/
theorem polynomialFunction_demeMeanPolynomial (deme : Deme)
    (value : FullHaplotype Locus Allele → ℝ) (y : FrequencyState Deme Locus Allele) :
    polynomialFunction (demeMeanPolynomial deme value) y = (stateLaw y deme).expectation value := by
  rw [polynomialFunction_apply, demeMeanPolynomial, eval_demePolynomial,
    eval_expectationPolynomial]

/-- At a state, the covariance polynomial is the corpus covariance under the deme's haplotype
law. -/
theorem polynomialFunction_demeCovariancePolynomial (deme : Deme)
    (first second : FullHaplotype Locus Allele → ℝ) (y : FrequencyState Deme Locus Allele) :
    polynomialFunction (demeCovariancePolynomial deme first second) y
      = (stateLaw y deme).covariance first second := by
  rw [polynomialFunction_apply, demeCovariancePolynomial, eval_demePolynomial,
    eval_covariancePolynomial]

/-- At a state, the intercept polynomial is `μ_Y V_S - C_SY μ_S` of the deme's haplotype law. -/
theorem polynomialFunction_interceptNumeratorPolynomial (deme : Deme)
    (score outcome : FullHaplotype Locus Allele → ℝ) (y : FrequencyState Deme Locus Allele) :
    polynomialFunction (interceptNumeratorPolynomial deme score outcome) y
      = (stateLaw y deme).expectation outcome * (stateLaw y deme).variance score
        - (stateLaw y deme).covariance score outcome * (stateLaw y deme).expectation score := by
  simp only [polynomialFunction_apply, interceptNumeratorPolynomial, demeMeanPolynomial,
    demeCovariancePolynomial, map_sub, map_mul, eval_demePolynomial, eval_expectationPolynomial,
    eval_covariancePolynomial, FiniteReportLaw.variance]

/-- The mean polynomial has total degree at most one. -/
theorem totalDegree_demeMeanPolynomial_le (deme : Deme) (value : FullHaplotype Locus Allele → ℝ) :
    (demeMeanPolynomial deme value).totalDegree ≤ 1 :=
  (totalDegree_rename_le _ _).trans (totalDegree_expectationPolynomial_le value)

/-- The covariance polynomial has total degree at most two. -/
theorem totalDegree_demeCovariancePolynomial_le (deme : Deme)
    (first second : FullHaplotype Locus Allele → ℝ) :
    (demeCovariancePolynomial deme first second).totalDegree ≤ 2 :=
  (totalDegree_rename_le _ _).trans (totalDegree_covariancePolynomial_le first second)

/-- The intercept polynomial has total degree at most three. -/
theorem totalDegree_interceptNumeratorPolynomial_le (deme : Deme)
    (score outcome : FullHaplotype Locus Allele → ℝ) :
    (interceptNumeratorPolynomial deme score outcome).totalDegree ≤ 3 := by
  have hmeanOutcome := totalDegree_demeMeanPolynomial_le deme outcome
  have hmeanScore := totalDegree_demeMeanPolynomial_le deme score
  have hvariance := totalDegree_demeCovariancePolynomial_le deme score score
  have hcovariance := totalDegree_demeCovariancePolynomial_le deme score outcome
  refine (totalDegree_sub _ _).trans (max_le ?_ ?_)
  · exact (totalDegree_mul _ _).trans (by omega)
  · exact (totalDegree_mul _ _).trans (by omega)

/-! ## Integrating calibration accumulators against a kernel -/

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

/-- An observable that agrees with a frequency polynomial of total degree at most `n` integrates,
under a Markov kernel whose budget-`n` configuration moments are `M` applied to the initial
moments, to the coefficient vector of the polynomial dotted with the propagated moments. -/
theorem integral_eq_dotProduct_of_totalDegree_le (p : FrequencyPolynomial Deme Locus Allele)
    (hp : p.totalDegree ≤ n) (g : FrequencyState Deme Locus Allele → ℝ)
    (hg : ∀ y, polynomialFunction p y = g y) (x0 : FrequencyState Deme Locus Allele) :
    ∫ y, g y ∂(κ x0)
      = budgetCoefficients ℓ₀ (fun _ ↦ n) p ⬝ᵥ (M *ᵥ budgetMomentFeature (fun _ ↦ n) x0) := by
  rw [← integral_polynomial_eq_dotProduct ℓ₀ (fun _ ↦ n) κ M hmoment p
    (withinBudget_of_totalDegree_le ℓ₀ p hp) x0]
  exact integral_congr_ae (Filter.Eventually.of_forall fun y ↦ (hg y).symm)

/-- Expected deme means through the moments, at every budget `n ≥ 1`. -/
theorem integral_expectation_eq_dotProduct (hn : 1 ≤ n) (x0 : FrequencyState Deme Locus Allele)
    (deme : Deme) (value : FullHaplotype Locus Allele → ℝ) :
    ∫ y, (stateLaw y deme).expectation value ∂(κ x0)
      = budgetCoefficients ℓ₀ (fun _ ↦ n) (demeMeanPolynomial deme value)
        ⬝ᵥ (M *ᵥ budgetMomentFeature (fun _ ↦ n) x0) :=
  integral_eq_dotProduct_of_totalDegree_le ℓ₀ κ M hmoment _
    ((totalDegree_demeMeanPolynomial_le deme value).trans hn) _
    (polynomialFunction_demeMeanPolynomial deme value) x0

/-- Expected deme covariances through the moments, at every budget `n ≥ 2`. -/
theorem integral_covariance_eq_dotProduct (hn : 2 ≤ n) (x0 : FrequencyState Deme Locus Allele)
    (deme : Deme) (first second : FullHaplotype Locus Allele → ℝ) :
    ∫ y, (stateLaw y deme).covariance first second ∂(κ x0)
      = budgetCoefficients ℓ₀ (fun _ ↦ n) (demeCovariancePolynomial deme first second)
        ⬝ᵥ (M *ᵥ budgetMomentFeature (fun _ ↦ n) x0) :=
  integral_eq_dotProduct_of_totalDegree_le ℓ₀ κ M hmoment _
    ((totalDegree_demeCovariancePolynomial_le deme first second).trans hn) _
    (polynomialFunction_demeCovariancePolynomial deme first second) x0

/-- Expected deme variances through the moments, at every budget `n ≥ 2`. -/
theorem integral_variance_eq_dotProduct (hn : 2 ≤ n) (x0 : FrequencyState Deme Locus Allele)
    (deme : Deme) (value : FullHaplotype Locus Allele → ℝ) :
    ∫ y, (stateLaw y deme).variance value ∂(κ x0)
      = budgetCoefficients ℓ₀ (fun _ ↦ n) (demeCovariancePolynomial deme value value)
        ⬝ᵥ (M *ᵥ budgetMomentFeature (fun _ ↦ n) x0) :=
  integral_covariance_eq_dotProduct ℓ₀ κ M hmoment hn x0 deme value value

end MomentKernel

/-! ## Propagated calibration moments along a history of epochs, splits and pulses -/

/-- **Expected deme means along a history.**  For every budget `n ≥ 1`, the expected mean of a
haplotype observable in a deme is the coefficient vector of its mean polynomial dotted with the
chronological propagator applied to the budget-`n` moments of the initial state. -/
theorem integral_expectation_historyEventKernel (ℓ₀ : Locus) (hap₀ : FullHaplotype Locus Allele)
    (events : List ((NeutralRates Deme Locus Allele × ℝ≥0) ⊕ PulseMatrix Deme)) {n : ℕ}
    (hn : 1 ≤ n) (x0 : FrequencyState Deme Locus Allele) (deme : Deme)
    (value : FullHaplotype Locus Allele → ℝ) :
    ∫ y, (stateLaw y deme).expectation value ∂(historyEventKernel ℓ₀ hap₀ events x0)
      = budgetCoefficients ℓ₀ (fun _ ↦ n) (demeMeanPolynomial deme value)
        ⬝ᵥ (historyEventPropagator (fun _ ↦ n) events *ᵥ budgetMomentFeature (fun _ ↦ n) x0) := by
  haveI := isMarkovKernel_historyEventKernel ℓ₀ hap₀ events
  exact integral_expectation_eq_dotProduct ℓ₀ (historyEventKernel ℓ₀ hap₀ events) _
    (integral_momentPolynomial_historyEventKernel ℓ₀ hap₀ (fun _ ↦ n) events) hn x0 deme value

/-- **Expected deme covariances along a history**, at every budget `n ≥ 2`. -/
theorem integral_covariance_historyEventKernel (ℓ₀ : Locus) (hap₀ : FullHaplotype Locus Allele)
    (events : List ((NeutralRates Deme Locus Allele × ℝ≥0) ⊕ PulseMatrix Deme)) {n : ℕ}
    (hn : 2 ≤ n) (x0 : FrequencyState Deme Locus Allele) (deme : Deme)
    (first second : FullHaplotype Locus Allele → ℝ) :
    ∫ y, (stateLaw y deme).covariance first second ∂(historyEventKernel ℓ₀ hap₀ events x0)
      = budgetCoefficients ℓ₀ (fun _ ↦ n) (demeCovariancePolynomial deme first second)
        ⬝ᵥ (historyEventPropagator (fun _ ↦ n) events *ᵥ budgetMomentFeature (fun _ ↦ n) x0) := by
  haveI := isMarkovKernel_historyEventKernel ℓ₀ hap₀ events
  exact integral_covariance_eq_dotProduct ℓ₀ (historyEventKernel ℓ₀ hap₀ events) _
    (integral_momentPolynomial_historyEventKernel ℓ₀ hap₀ (fun _ ↦ n) events) hn x0 deme first
    second

/-- **Expected deme variances along a history**, at every budget `n ≥ 2`. -/
theorem integral_variance_historyEventKernel (ℓ₀ : Locus) (hap₀ : FullHaplotype Locus Allele)
    (events : List ((NeutralRates Deme Locus Allele × ℝ≥0) ⊕ PulseMatrix Deme)) {n : ℕ}
    (hn : 2 ≤ n) (x0 : FrequencyState Deme Locus Allele) (deme : Deme)
    (value : FullHaplotype Locus Allele → ℝ) :
    ∫ y, (stateLaw y deme).variance value ∂(historyEventKernel ℓ₀ hap₀ events x0)
      = budgetCoefficients ℓ₀ (fun _ ↦ n) (demeCovariancePolynomial deme value value)
        ⬝ᵥ (historyEventPropagator (fun _ ↦ n) events *ᵥ budgetMomentFeature (fun _ ↦ n) x0) :=
  integral_covariance_historyEventKernel ℓ₀ hap₀ events hn x0 deme value value

/-! ## Propagated calibration moments along a rate history -/

/-- **Expected deme means along a rate history**, at every budget `n ≥ 1`. -/
theorem integral_expectation_rateHistoryKernel {rates : ℝ → NeutralRates Deme Locus Allele}
    {T : ℝ} (hT : 0 ≤ T)
    (hcontinuous : ∀ capacity : Locus → ℕ,
      ContinuousOn (fun t ↦ dualGenerator (rates t) capacity) (Set.Icc 0 T))
    (ℓ₀ : Locus) (hap₀ : FullHaplotype Locus Allele) {n : ℕ} (hn : 1 ≤ n)
    (x0 : FrequencyState Deme Locus Allele) (deme : Deme)
    (value : FullHaplotype Locus Allele → ℝ) :
    ∫ y, (stateLaw y deme).expectation value ∂(rateHistoryKernel rates ℓ₀ hap₀ hT hcontinuous x0)
      = budgetCoefficients ℓ₀ (fun _ ↦ n) (demeMeanPolynomial deme value)
        ⬝ᵥ (rateHistoryDualPropagator rates (fun _ ↦ n) T
          *ᵥ budgetMomentFeature (fun _ ↦ n) x0) := by
  haveI := isMarkovKernel_rateHistoryKernel hT hcontinuous ℓ₀ hap₀
  exact integral_expectation_eq_dotProduct ℓ₀ (rateHistoryKernel rates ℓ₀ hap₀ hT hcontinuous) _
    (integral_momentPolynomial_rateHistoryKernel hT hcontinuous ℓ₀ hap₀ (fun _ ↦ n)) hn x0 deme
    value

/-- **Expected deme covariances along a rate history**, at every budget `n ≥ 2`. -/
theorem integral_covariance_rateHistoryKernel {rates : ℝ → NeutralRates Deme Locus Allele}
    {T : ℝ} (hT : 0 ≤ T)
    (hcontinuous : ∀ capacity : Locus → ℕ,
      ContinuousOn (fun t ↦ dualGenerator (rates t) capacity) (Set.Icc 0 T))
    (ℓ₀ : Locus) (hap₀ : FullHaplotype Locus Allele) {n : ℕ} (hn : 2 ≤ n)
    (x0 : FrequencyState Deme Locus Allele) (deme : Deme)
    (first second : FullHaplotype Locus Allele → ℝ) :
    ∫ y, (stateLaw y deme).covariance first second
        ∂(rateHistoryKernel rates ℓ₀ hap₀ hT hcontinuous x0)
      = budgetCoefficients ℓ₀ (fun _ ↦ n) (demeCovariancePolynomial deme first second)
        ⬝ᵥ (rateHistoryDualPropagator rates (fun _ ↦ n) T
          *ᵥ budgetMomentFeature (fun _ ↦ n) x0) := by
  haveI := isMarkovKernel_rateHistoryKernel hT hcontinuous ℓ₀ hap₀
  exact integral_covariance_eq_dotProduct ℓ₀ (rateHistoryKernel rates ℓ₀ hap₀ hT hcontinuous) _
    (integral_momentPolynomial_rateHistoryKernel hT hcontinuous ℓ₀ hap₀ (fun _ ↦ n)) hn x0 deme
    first second

/-- **Expected deme variances along a rate history**, at every budget `n ≥ 2`. -/
theorem integral_variance_rateHistoryKernel {rates : ℝ → NeutralRates Deme Locus Allele}
    {T : ℝ} (hT : 0 ≤ T)
    (hcontinuous : ∀ capacity : Locus → ℕ,
      ContinuousOn (fun t ↦ dualGenerator (rates t) capacity) (Set.Icc 0 T))
    (ℓ₀ : Locus) (hap₀ : FullHaplotype Locus Allele) {n : ℕ} (hn : 2 ≤ n)
    (x0 : FrequencyState Deme Locus Allele) (deme : Deme)
    (value : FullHaplotype Locus Allele → ℝ) :
    ∫ y, (stateLaw y deme).variance value ∂(rateHistoryKernel rates ℓ₀ hap₀ hT hcontinuous x0)
      = budgetCoefficients ℓ₀ (fun _ ↦ n) (demeCovariancePolynomial deme value value)
        ⬝ᵥ (rateHistoryDualPropagator rates (fun _ ↦ n) T
          *ᵥ budgetMomentFeature (fun _ ↦ n) x0) :=
  integral_covariance_rateHistoryKernel hT hcontinuous ℓ₀ hap₀ hn x0 deme value value

/-! ## The calibration of expectations -/

/-- **The calibration slope of expectations**: the expected score–outcome covariance of a deme
over its expected score variance, `E C_SY / E V_S`, under a kernel started at `x₀`.  NOTE2 §6.2
query: a ratio of expectations. -/
def expectedCalibrationSlope
    (κ : Kernel (FrequencyState Deme Locus Allele) (FrequencyState Deme Locus Allele))
    (x0 : FrequencyState Deme Locus Allele) (deme : Deme)
    (score outcome : FullHaplotype Locus Allele → ℝ) : ℝ :=
  (∫ y, (stateLaw y deme).covariance score outcome ∂(κ x0))
    / ∫ y, (stateLaw y deme).variance score ∂(κ x0)

/-- **The calibration portability of expectations**: the target calibration slope of
expectations over the source one.  NOTE2 §6.2 query: a ratio of expectations. -/
def expectedCalibrationPortability
    (κ : Kernel (FrequencyState Deme Locus Allele) (FrequencyState Deme Locus Allele))
    (x0 : FrequencyState Deme Locus Allele) (source target : Deme)
    (score outcome : FullHaplotype Locus Allele → ℝ) : ℝ :=
  expectedCalibrationSlope κ x0 target score outcome
    / expectedCalibrationSlope κ x0 source score outcome

/-- **The calibration intercept of expectations**: the expected intercept accumulator
`E[μ_Y V_S - C_SY μ_S]` of a deme over its expected score variance.  NOTE2 §6.2 query: a ratio of
expectations. -/
def expectedCalibrationIntercept
    (κ : Kernel (FrequencyState Deme Locus Allele) (FrequencyState Deme Locus Allele))
    (x0 : FrequencyState Deme Locus Allele) (deme : Deme)
    (score outcome : FullHaplotype Locus Allele → ℝ) : ℝ :=
  (∫ y, ((stateLaw y deme).expectation outcome * (stateLaw y deme).variance score
      - (stateLaw y deme).covariance score outcome * (stateLaw y deme).expectation score)
      ∂(κ x0))
    / ∫ y, (stateLaw y deme).variance score ∂(κ x0)

/-- **The cross form.**  The calibration portability of expectations is
`E C_t · E V_s / (E V_t · E C_s)`, with no side condition. -/
theorem expectedCalibrationPortability_eq_cross
    (κ : Kernel (FrequencyState Deme Locus Allele) (FrequencyState Deme Locus Allele))
    (x0 : FrequencyState Deme Locus Allele) (source target : Deme)
    (score outcome : FullHaplotype Locus Allele → ℝ) :
    expectedCalibrationPortability κ x0 source target score outcome
      = (∫ y, (stateLaw y target).covariance score outcome ∂(κ x0))
          * (∫ y, (stateLaw y source).variance score ∂(κ x0))
        / ((∫ y, (stateLaw y target).variance score ∂(κ x0))
          * ∫ y, (stateLaw y source).covariance score outcome ∂(κ x0)) := by
  rw [expectedCalibrationPortability, expectedCalibrationSlope, expectedCalibrationSlope,
    div_div_div_eq]

/-- **NOTE2 (27) for calibration.**  The calibration portability of expectations is the corpus
portability ratio of the four accumulators: the expected source covariance and score variance and
the expected target covariance and score variance. -/
theorem expectedCalibrationPortability_eq_portabilityRatio
    (κ : Kernel (FrequencyState Deme Locus Allele) (FrequencyState Deme Locus Allele))
    (x0 : FrequencyState Deme Locus Allele) (source target : Deme)
    (score outcome : FullHaplotype Locus Allele → ℝ) :
    expectedCalibrationPortability κ x0 source target score outcome
      = PortabilityRatioQueries.portabilityRatio
          (fun _ : Unit ↦ ∫ y, (stateLaw y source).covariance score outcome ∂(κ x0))
          (fun _ ↦ ∫ y, (stateLaw y source).variance score ∂(κ x0))
          (fun _ ↦ ∫ y, (stateLaw y target).covariance score outcome ∂(κ x0))
          (fun _ ↦ ∫ y, (stateLaw y target).variance score ∂(κ x0)) () :=
  rfl

/-! ## Ratios of expectations as weighted expectations of ratios -/

/-- The score variance times the corpus calibration slope, read as zero where it is undefined, is
the covariance: where the variance vanishes Cauchy–Schwarz forces the covariance to vanish. -/
theorem variance_mul_getD_calibrationSlope {Ω : Type*} [Fintype Ω] (law : FiniteReportLaw Ω)
    (score outcome : Ω → ℝ) :
    law.variance score * (law.calibrationSlope score outcome).getD 0
      = law.covariance score outcome := by
  unfold FiniteReportLaw.calibrationSlope
  split_ifs with hpositive
  · exact mul_div_cancel₀ _ hpositive.ne'
  · have hzero : law.variance score = 0 :=
      le_antisymm (not_lt.mp hpositive) (law.variance_nonneg score)
    have hsquare : law.covariance score outcome ^ 2 = 0 := by
      refine le_antisymm ?_ (sq_nonneg _)
      have hcauchy := law.covariance_sq_le_variance_mul score outcome
      rwa [hzero, zero_mul] at hcauchy
    rw [(pow_eq_zero_iff two_ne_zero).mp hsquare, Option.getD_none, mul_zero]

/-- The score variance times the corpus intercept `μ_Y - slope · μ_S`, with the slope read as
zero where it is undefined, is the intercept accumulator `μ_Y V_S - C_SY μ_S`. -/
theorem variance_mul_intercept {Ω : Type*} [Fintype Ω] (law : FiniteReportLaw Ω)
    (score outcome : Ω → ℝ) :
    law.variance score * (law.expectation outcome
        - (law.calibrationSlope score outcome).getD 0 * law.expectation score)
      = law.expectation outcome * law.variance score
        - law.covariance score outcome * law.expectation score := by
  rw [← variance_mul_getD_calibrationSlope law score outcome]
  ring

/-- **The slope of expectations is a weighted expectation of slopes.**  `E C_SY / E V_S` is the
expectation of the corpus calibration slope of each population, read as zero where it is
undefined, weighted by the population's score variance, over the expected weight.  This is how the
ratio-of-expectations query of NOTE2 §6.2 relates to the expectation of the slope. -/
theorem expectedCalibrationSlope_eq_weighted
    (κ : Kernel (FrequencyState Deme Locus Allele) (FrequencyState Deme Locus Allele))
    (x0 : FrequencyState Deme Locus Allele) (deme : Deme)
    (score outcome : FullHaplotype Locus Allele → ℝ) :
    expectedCalibrationSlope κ x0 deme score outcome
      = (∫ y, (stateLaw y deme).variance score
          * ((stateLaw y deme).calibrationSlope score outcome).getD 0 ∂(κ x0))
        / ∫ y, (stateLaw y deme).variance score ∂(κ x0) := by
  simp only [expectedCalibrationSlope, variance_mul_getD_calibrationSlope]

/-- **The intercept of expectations is a weighted expectation of intercepts**, with the same
score-variance weights. -/
theorem expectedCalibrationIntercept_eq_weighted
    (κ : Kernel (FrequencyState Deme Locus Allele) (FrequencyState Deme Locus Allele))
    (x0 : FrequencyState Deme Locus Allele) (deme : Deme)
    (score outcome : FullHaplotype Locus Allele → ℝ) :
    expectedCalibrationIntercept κ x0 deme score outcome
      = (∫ y, (stateLaw y deme).variance score
          * ((stateLaw y deme).expectation outcome
            - ((stateLaw y deme).calibrationSlope score outcome).getD 0
              * (stateLaw y deme).expectation score) ∂(κ x0))
        / ∫ y, (stateLaw y deme).variance score ∂(κ x0) := by
  simp only [expectedCalibrationIntercept, variance_mul_intercept]

/-! ## The rational calibration functions -/

/-- **The rational calibration slope** of a budget-`n` moment vector. -/
def momentCalibrationSlope (ℓ₀ : Locus) (n : ℕ) (deme : Deme)
    (score outcome : FullHaplotype Locus Allele → ℝ)
    (v : BudgetConfiguration Deme Locus Allele (fun _ ↦ n) → ℝ) : ℝ :=
  (budgetCoefficients ℓ₀ (fun _ ↦ n) (demeCovariancePolynomial deme score outcome) ⬝ᵥ v)
    / (budgetCoefficients ℓ₀ (fun _ ↦ n) (demeCovariancePolynomial deme score score) ⬝ᵥ v)

/-- **The rational calibration portability** of a budget-`n` moment vector. -/
def momentCalibrationPortability (ℓ₀ : Locus) (n : ℕ) (source target : Deme)
    (score outcome : FullHaplotype Locus Allele → ℝ)
    (v : BudgetConfiguration Deme Locus Allele (fun _ ↦ n) → ℝ) : ℝ :=
  momentCalibrationSlope ℓ₀ n target score outcome v
    / momentCalibrationSlope ℓ₀ n source score outcome v

/-- **The rational calibration intercept** of a budget-`n` moment vector. -/
def momentCalibrationIntercept (ℓ₀ : Locus) (n : ℕ) (deme : Deme)
    (score outcome : FullHaplotype Locus Allele → ℝ)
    (v : BudgetConfiguration Deme Locus Allele (fun _ ↦ n) → ℝ) : ℝ :=
  (budgetCoefficients ℓ₀ (fun _ ↦ n) (interceptNumeratorPolynomial deme score outcome) ⬝ᵥ v)
    / (budgetCoefficients ℓ₀ (fun _ ↦ n) (demeCovariancePolynomial deme score score) ⬝ᵥ v)

/-- The rational calibration portability in cross form. -/
theorem momentCalibrationPortability_eq_cross (ℓ₀ : Locus) (n : ℕ) (source target : Deme)
    (score outcome : FullHaplotype Locus Allele → ℝ)
    (v : BudgetConfiguration Deme Locus Allele (fun _ ↦ n) → ℝ) :
    momentCalibrationPortability ℓ₀ n source target score outcome v
      = (budgetCoefficients ℓ₀ (fun _ ↦ n) (demeCovariancePolynomial target score outcome) ⬝ᵥ v)
          * (budgetCoefficients ℓ₀ (fun _ ↦ n) (demeCovariancePolynomial source score score)
            ⬝ᵥ v)
        / ((budgetCoefficients ℓ₀ (fun _ ↦ n) (demeCovariancePolynomial target score score) ⬝ᵥ v)
          * (budgetCoefficients ℓ₀ (fun _ ↦ n) (demeCovariancePolynomial source score outcome)
            ⬝ᵥ v)) := by
  rw [momentCalibrationPortability, momentCalibrationSlope, momentCalibrationSlope,
    div_div_div_eq]

section MomentLaws

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

/-- Under a kernel with budget-`n` moments `M`, `n ≥ 2`, the calibration slope of expectations is
the rational slope of the propagated moments. -/
theorem expectedCalibrationSlope_eq_momentCalibrationSlope (hn : 2 ≤ n)
    (x0 : FrequencyState Deme Locus Allele) (deme : Deme)
    (score outcome : FullHaplotype Locus Allele → ℝ) :
    expectedCalibrationSlope κ x0 deme score outcome
      = momentCalibrationSlope ℓ₀ n deme score outcome
          (M *ᵥ budgetMomentFeature (fun _ ↦ n) x0) := by
  rw [expectedCalibrationSlope, momentCalibrationSlope,
    integral_covariance_eq_dotProduct ℓ₀ κ M hmoment hn x0 deme score outcome,
    integral_variance_eq_dotProduct ℓ₀ κ M hmoment hn x0 deme score]

/-- Under a kernel with budget-`n` moments `M`, `n ≥ 2`, the calibration portability of
expectations is the rational portability of the propagated moments. -/
theorem expectedCalibrationPortability_eq_momentCalibrationPortability (hn : 2 ≤ n)
    (x0 : FrequencyState Deme Locus Allele) (source target : Deme)
    (score outcome : FullHaplotype Locus Allele → ℝ) :
    expectedCalibrationPortability κ x0 source target score outcome
      = momentCalibrationPortability ℓ₀ n source target score outcome
          (M *ᵥ budgetMomentFeature (fun _ ↦ n) x0) := by
  rw [expectedCalibrationPortability, momentCalibrationPortability,
    expectedCalibrationSlope_eq_momentCalibrationSlope ℓ₀ κ M hmoment hn x0 target,
    expectedCalibrationSlope_eq_momentCalibrationSlope ℓ₀ κ M hmoment hn x0 source]

/-- Under a kernel with budget-`n` moments `M`, `n ≥ 3`, the calibration intercept of
expectations is the rational intercept of the propagated moments. -/
theorem expectedCalibrationIntercept_eq_momentCalibrationIntercept (hn : 3 ≤ n)
    (x0 : FrequencyState Deme Locus Allele) (deme : Deme)
    (score outcome : FullHaplotype Locus Allele → ℝ) :
    expectedCalibrationIntercept κ x0 deme score outcome
      = momentCalibrationIntercept ℓ₀ n deme score outcome
          (M *ᵥ budgetMomentFeature (fun _ ↦ n) x0) := by
  rw [expectedCalibrationIntercept, momentCalibrationIntercept,
    integral_eq_dotProduct_of_totalDegree_le ℓ₀ κ M hmoment _
      ((totalDegree_interceptNumeratorPolynomial_le deme score outcome).trans hn) _
      (polynomialFunction_interceptNumeratorPolynomial deme score outcome) x0,
    integral_variance_eq_dotProduct ℓ₀ κ M hmoment (by omega) x0 deme score]

end MomentLaws

/-! ## The end-to-end calibration law along a history of epochs, splits and pulses -/

/-- **The calibration slope of expectations along a history.**  For every budget `n ≥ 2` it is
the rational slope of the chronological propagator applied to the budget-`n` moments of `x₀`. -/
theorem expectedCalibrationSlope_historyEventKernel (ℓ₀ : Locus)
    (hap₀ : FullHaplotype Locus Allele)
    (events : List ((NeutralRates Deme Locus Allele × ℝ≥0) ⊕ PulseMatrix Deme)) {n : ℕ}
    (hn : 2 ≤ n) (x0 : FrequencyState Deme Locus Allele) (deme : Deme)
    (score outcome : FullHaplotype Locus Allele → ℝ) :
    expectedCalibrationSlope (historyEventKernel ℓ₀ hap₀ events) x0 deme score outcome
      = momentCalibrationSlope ℓ₀ n deme score outcome
          (historyEventPropagator (fun _ ↦ n) events *ᵥ budgetMomentFeature (fun _ ↦ n) x0) := by
  haveI := isMarkovKernel_historyEventKernel ℓ₀ hap₀ events
  exact expectedCalibrationSlope_eq_momentCalibrationSlope ℓ₀ (historyEventKernel ℓ₀ hap₀ events)
    _ (integral_momentPolynomial_historyEventKernel ℓ₀ hap₀ (fun _ ↦ n) events) hn x0 deme score
    outcome

/-- **The end-to-end calibration portability law along a history.**  For every budget `n ≥ 2`,
`E C_t · E V_s / (E V_t · E C_s)` is the rational portability of the chronological propagator
applied to the budget-`n` moments of `x₀`. -/
theorem expectedCalibrationPortability_historyEventKernel (ℓ₀ : Locus)
    (hap₀ : FullHaplotype Locus Allele)
    (events : List ((NeutralRates Deme Locus Allele × ℝ≥0) ⊕ PulseMatrix Deme)) {n : ℕ}
    (hn : 2 ≤ n) (x0 : FrequencyState Deme Locus Allele) (source target : Deme)
    (score outcome : FullHaplotype Locus Allele → ℝ) :
    expectedCalibrationPortability (historyEventKernel ℓ₀ hap₀ events) x0 source target score
        outcome
      = momentCalibrationPortability ℓ₀ n source target score outcome
          (historyEventPropagator (fun _ ↦ n) events *ᵥ budgetMomentFeature (fun _ ↦ n) x0) := by
  haveI := isMarkovKernel_historyEventKernel ℓ₀ hap₀ events
  exact expectedCalibrationPortability_eq_momentCalibrationPortability ℓ₀
    (historyEventKernel ℓ₀ hap₀ events) _
    (integral_momentPolynomial_historyEventKernel ℓ₀ hap₀ (fun _ ↦ n) events) hn x0 source target
    score outcome

/-- **The calibration intercept of expectations along a history.**  For every budget `n ≥ 3` it
is the rational intercept of the chronological propagator applied to the budget-`n` moments of
`x₀`. -/
theorem expectedCalibrationIntercept_historyEventKernel (ℓ₀ : Locus)
    (hap₀ : FullHaplotype Locus Allele)
    (events : List ((NeutralRates Deme Locus Allele × ℝ≥0) ⊕ PulseMatrix Deme)) {n : ℕ}
    (hn : 3 ≤ n) (x0 : FrequencyState Deme Locus Allele) (deme : Deme)
    (score outcome : FullHaplotype Locus Allele → ℝ) :
    expectedCalibrationIntercept (historyEventKernel ℓ₀ hap₀ events) x0 deme score outcome
      = momentCalibrationIntercept ℓ₀ n deme score outcome
          (historyEventPropagator (fun _ ↦ n) events *ᵥ budgetMomentFeature (fun _ ↦ n) x0) := by
  haveI := isMarkovKernel_historyEventKernel ℓ₀ hap₀ events
  exact expectedCalibrationIntercept_eq_momentCalibrationIntercept ℓ₀
    (historyEventKernel ℓ₀ hap₀ events) _
    (integral_momentPolynomial_historyEventKernel ℓ₀ hap₀ (fun _ ↦ n) events) hn x0 deme score
    outcome

/-- **The calibration slope sees the history only through finitely many moments.**  Two
histories, from two initial states, whose propagated budget-`n` moments agree, `n ≥ 2`, have
equal calibration slope of expectations for every score, outcome and deme. -/
theorem expectedCalibrationSlope_eq_of_moments_eq (ℓ₀ : Locus) (hap₀ : FullHaplotype Locus Allele)
    {first second : List ((NeutralRates Deme Locus Allele × ℝ≥0) ⊕ PulseMatrix Deme)}
    {x₁ x₂ : FrequencyState Deme Locus Allele} {n : ℕ} (hn : 2 ≤ n)
    (hmoments : historyEventPropagator (fun _ ↦ n) first *ᵥ budgetMomentFeature (fun _ ↦ n) x₁
      = historyEventPropagator (fun _ ↦ n) second *ᵥ budgetMomentFeature (fun _ ↦ n) x₂)
    (deme : Deme) (score outcome : FullHaplotype Locus Allele → ℝ) :
    expectedCalibrationSlope (historyEventKernel ℓ₀ hap₀ first) x₁ deme score outcome
      = expectedCalibrationSlope (historyEventKernel ℓ₀ hap₀ second) x₂ deme score outcome := by
  rw [expectedCalibrationSlope_historyEventKernel ℓ₀ hap₀ first hn,
    expectedCalibrationSlope_historyEventKernel ℓ₀ hap₀ second hn, hmoments]

/-- **Calibration portability sees the history only through finitely many moments.**  Two
histories, from two initial states, whose propagated budget-`n` moments agree, `n ≥ 2`, have
equal calibration portability of expectations for every score, outcome, source and target. -/
theorem expectedCalibrationPortability_eq_of_moments_eq (ℓ₀ : Locus)
    (hap₀ : FullHaplotype Locus Allele)
    {first second : List ((NeutralRates Deme Locus Allele × ℝ≥0) ⊕ PulseMatrix Deme)}
    {x₁ x₂ : FrequencyState Deme Locus Allele} {n : ℕ} (hn : 2 ≤ n)
    (hmoments : historyEventPropagator (fun _ ↦ n) first *ᵥ budgetMomentFeature (fun _ ↦ n) x₁
      = historyEventPropagator (fun _ ↦ n) second *ᵥ budgetMomentFeature (fun _ ↦ n) x₂)
    (source target : Deme) (score outcome : FullHaplotype Locus Allele → ℝ) :
    expectedCalibrationPortability (historyEventKernel ℓ₀ hap₀ first) x₁ source target score
        outcome
      = expectedCalibrationPortability (historyEventKernel ℓ₀ hap₀ second) x₂ source target score
          outcome := by
  rw [expectedCalibrationPortability_historyEventKernel ℓ₀ hap₀ first hn,
    expectedCalibrationPortability_historyEventKernel ℓ₀ hap₀ second hn, hmoments]

/-- **The calibration intercept sees the history only through finitely many moments**, at every
budget `n ≥ 3`. -/
theorem expectedCalibrationIntercept_eq_of_moments_eq (ℓ₀ : Locus)
    (hap₀ : FullHaplotype Locus Allele)
    {first second : List ((NeutralRates Deme Locus Allele × ℝ≥0) ⊕ PulseMatrix Deme)}
    {x₁ x₂ : FrequencyState Deme Locus Allele} {n : ℕ} (hn : 3 ≤ n)
    (hmoments : historyEventPropagator (fun _ ↦ n) first *ᵥ budgetMomentFeature (fun _ ↦ n) x₁
      = historyEventPropagator (fun _ ↦ n) second *ᵥ budgetMomentFeature (fun _ ↦ n) x₂)
    (deme : Deme) (score outcome : FullHaplotype Locus Allele → ℝ) :
    expectedCalibrationIntercept (historyEventKernel ℓ₀ hap₀ first) x₁ deme score outcome
      = expectedCalibrationIntercept (historyEventKernel ℓ₀ hap₀ second) x₂ deme score
          outcome := by
  rw [expectedCalibrationIntercept_historyEventKernel ℓ₀ hap₀ first hn,
    expectedCalibrationIntercept_historyEventKernel ℓ₀ hap₀ second hn, hmoments]

/-! ## The end-to-end calibration law along a rate history -/

/-- **The calibration slope of expectations along a rate history**, at every budget `n ≥ 2`. -/
theorem expectedCalibrationSlope_rateHistoryKernel {rates : ℝ → NeutralRates Deme Locus Allele}
    {T : ℝ} (hT : 0 ≤ T)
    (hcontinuous : ∀ capacity : Locus → ℕ,
      ContinuousOn (fun t ↦ dualGenerator (rates t) capacity) (Set.Icc 0 T))
    (ℓ₀ : Locus) (hap₀ : FullHaplotype Locus Allele) {n : ℕ} (hn : 2 ≤ n)
    (x0 : FrequencyState Deme Locus Allele) (deme : Deme)
    (score outcome : FullHaplotype Locus Allele → ℝ) :
    expectedCalibrationSlope (rateHistoryKernel rates ℓ₀ hap₀ hT hcontinuous) x0 deme score
        outcome
      = momentCalibrationSlope ℓ₀ n deme score outcome
          (rateHistoryDualPropagator rates (fun _ ↦ n) T
            *ᵥ budgetMomentFeature (fun _ ↦ n) x0) := by
  haveI := isMarkovKernel_rateHistoryKernel hT hcontinuous ℓ₀ hap₀
  exact expectedCalibrationSlope_eq_momentCalibrationSlope ℓ₀
    (rateHistoryKernel rates ℓ₀ hap₀ hT hcontinuous) _
    (integral_momentPolynomial_rateHistoryKernel hT hcontinuous ℓ₀ hap₀ (fun _ ↦ n)) hn x0 deme
    score outcome

/-- **The end-to-end calibration portability law along a rate history**, at every budget
`n ≥ 2`. -/
theorem expectedCalibrationPortability_rateHistoryKernel
    {rates : ℝ → NeutralRates Deme Locus Allele} {T : ℝ} (hT : 0 ≤ T)
    (hcontinuous : ∀ capacity : Locus → ℕ,
      ContinuousOn (fun t ↦ dualGenerator (rates t) capacity) (Set.Icc 0 T))
    (ℓ₀ : Locus) (hap₀ : FullHaplotype Locus Allele) {n : ℕ} (hn : 2 ≤ n)
    (x0 : FrequencyState Deme Locus Allele) (source target : Deme)
    (score outcome : FullHaplotype Locus Allele → ℝ) :
    expectedCalibrationPortability (rateHistoryKernel rates ℓ₀ hap₀ hT hcontinuous) x0 source
        target score outcome
      = momentCalibrationPortability ℓ₀ n source target score outcome
          (rateHistoryDualPropagator rates (fun _ ↦ n) T
            *ᵥ budgetMomentFeature (fun _ ↦ n) x0) := by
  haveI := isMarkovKernel_rateHistoryKernel hT hcontinuous ℓ₀ hap₀
  exact expectedCalibrationPortability_eq_momentCalibrationPortability ℓ₀
    (rateHistoryKernel rates ℓ₀ hap₀ hT hcontinuous) _
    (integral_momentPolynomial_rateHistoryKernel hT hcontinuous ℓ₀ hap₀ (fun _ ↦ n)) hn x0 source
    target score outcome

/-- **The calibration intercept of expectations along a rate history**, at every budget
`n ≥ 3`. -/
theorem expectedCalibrationIntercept_rateHistoryKernel
    {rates : ℝ → NeutralRates Deme Locus Allele} {T : ℝ} (hT : 0 ≤ T)
    (hcontinuous : ∀ capacity : Locus → ℕ,
      ContinuousOn (fun t ↦ dualGenerator (rates t) capacity) (Set.Icc 0 T))
    (ℓ₀ : Locus) (hap₀ : FullHaplotype Locus Allele) {n : ℕ} (hn : 3 ≤ n)
    (x0 : FrequencyState Deme Locus Allele) (deme : Deme)
    (score outcome : FullHaplotype Locus Allele → ℝ) :
    expectedCalibrationIntercept (rateHistoryKernel rates ℓ₀ hap₀ hT hcontinuous) x0 deme score
        outcome
      = momentCalibrationIntercept ℓ₀ n deme score outcome
          (rateHistoryDualPropagator rates (fun _ ↦ n) T
            *ᵥ budgetMomentFeature (fun _ ↦ n) x0) := by
  haveI := isMarkovKernel_rateHistoryKernel hT hcontinuous ℓ₀ hap₀
  exact expectedCalibrationIntercept_eq_momentCalibrationIntercept ℓ₀
    (rateHistoryKernel rates ℓ₀ hap₀ hT hcontinuous) _
    (integral_momentPolynomial_rateHistoryKernel hT hcontinuous ℓ₀ hap₀ (fun _ ↦ n)) hn x0 deme
    score outcome

/-! ## Calibration portability is Lipschitz in the rate history -/

/-- **Calibration portability of the moment law is Lipschitz in the rate path.**  For two rate
histories with continuous dual generators, where the target score variance and the source
covariance of the propagated budget-2 moments are at least `δ` under both, the rational
calibration portability moves by at most `4 B³ ‖a‖₁ ‖b‖₁ ‖c‖₁ ‖d‖₁ / δ⁴` times `B` times the
propagator bound, with `a`, `b`, `c`, `d` the coefficient vectors of the target covariance, the
source score variance, the target score variance and the source covariance. -/
theorem abs_momentCalibrationPortability_rateHistory_sub_le
    {first second : ℝ → NeutralRates Deme Locus Allele} {T : ℝ} (hT : 0 ≤ T)
    (hfirst : ∀ capacity : Locus → ℕ,
      ContinuousOn (fun t ↦ dualGenerator (first t) capacity) (Set.Icc 0 T))
    (hsecond : ∀ capacity : Locus → ℕ,
      ContinuousOn (fun t ↦ dualGenerator (second t) capacity) (Set.Icc 0 T))
    (ℓ₀ : Locus) (x0 : FrequencyState Deme Locus Allele) (source target : Deme)
    (score outcome : FullHaplotype Locus Allele → ℝ) {δ : ℝ} (hδ : 0 < δ)
    (htarget₁ : δ ≤ budgetCoefficients ℓ₀ (fun _ ↦ 2) (demeCovariancePolynomial target score score)
      ⬝ᵥ (rateHistoryDualPropagator first (fun _ ↦ 2) T *ᵥ budgetMomentFeature (fun _ ↦ 2) x0))
    (hsource₁ : δ ≤ budgetCoefficients ℓ₀ (fun _ ↦ 2)
        (demeCovariancePolynomial source score outcome)
      ⬝ᵥ (rateHistoryDualPropagator first (fun _ ↦ 2) T *ᵥ budgetMomentFeature (fun _ ↦ 2) x0))
    (htarget₂ : δ ≤ budgetCoefficients ℓ₀ (fun _ ↦ 2) (demeCovariancePolynomial target score score)
      ⬝ᵥ (rateHistoryDualPropagator second (fun _ ↦ 2) T *ᵥ budgetMomentFeature (fun _ ↦ 2) x0))
    (hsource₂ : δ ≤ budgetCoefficients ℓ₀ (fun _ ↦ 2)
        (demeCovariancePolynomial source score outcome)
      ⬝ᵥ (rateHistoryDualPropagator second (fun _ ↦ 2) T
        *ᵥ budgetMomentFeature (fun _ ↦ 2) x0)) :
    |momentCalibrationPortability ℓ₀ 2 source target score outcome
        (rateHistoryDualPropagator first (fun _ ↦ 2) T *ᵥ budgetMomentFeature (fun _ ↦ 2) x0)
      - momentCalibrationPortability ℓ₀ 2 source target score outcome
        (rateHistoryDualPropagator second (fun _ ↦ 2) T *ᵥ budgetMomentFeature (fun _ ↦ 2) x0)|
      ≤ 4 * featureBound (first 0) (fun _ ↦ 2) ^ 3
          * (∑ i, |budgetCoefficients ℓ₀ (fun _ ↦ 2)
              (demeCovariancePolynomial target score outcome) i|)
          * (∑ i, |budgetCoefficients ℓ₀ (fun _ ↦ 2)
              (demeCovariancePolynomial source score score) i|)
          * (∑ i, |budgetCoefficients ℓ₀ (fun _ ↦ 2)
              (demeCovariancePolynomial target score score) i|)
          * (∑ i, |budgetCoefficients ℓ₀ (fun _ ↦ 2)
              (demeCovariancePolynomial source score outcome) i|)
          / δ ^ 4
        * ((∫ s in (0 : ℝ)..T, ‖dualGeneratorPath first (fun _ ↦ 2) T s
              - dualGeneratorPath second (fun _ ↦ 2) T s‖)
            * Real.exp (∫ s in (0 : ℝ)..T, ‖dualGeneratorPath first (fun _ ↦ 2) T s‖)
            * Real.exp (∫ s in (0 : ℝ)..T, ‖dualGeneratorPath second (fun _ ↦ 2) T s‖)
          * featureBound (first 0) (fun _ ↦ 2)) := by
  have hbound := featureBound_nonneg (first 0) (fun _ ↦ 2)
  have hmass : ∀ w : BudgetConfiguration Deme Locus Allele (fun _ ↦ 2) → ℝ, 0 ≤ ∑ i, |w i| :=
    fun w ↦ Finset.sum_nonneg fun i _ ↦ abs_nonneg (w i)
  have hdistance : ‖rateHistoryDualPropagator first (fun _ ↦ 2) T
        *ᵥ budgetMomentFeature (fun _ ↦ 2) x0
      - rateHistoryDualPropagator second (fun _ ↦ 2) T *ᵥ budgetMomentFeature (fun _ ↦ 2) x0‖
      ≤ (∫ s in (0 : ℝ)..T, ‖dualGeneratorPath first (fun _ ↦ 2) T s
              - dualGeneratorPath second (fun _ ↦ 2) T s‖)
            * Real.exp (∫ s in (0 : ℝ)..T, ‖dualGeneratorPath first (fun _ ↦ 2) T s‖)
            * Real.exp (∫ s in (0 : ℝ)..T, ‖dualGeneratorPath second (fun _ ↦ 2) T s‖)
          * featureBound (first 0) (fun _ ↦ 2) :=
    le_trans (norm_propagated_sub_le (first 0) (fun _ ↦ 2) _ _ x0)
      (mul_le_mul_of_nonneg_right
        (norm_rateHistoryDualPropagator_sub_le hT (hfirst (fun _ ↦ 2)) (hsecond (fun _ ↦ 2)))
        hbound)
  rw [momentCalibrationPortability_eq_cross, momentCalibrationPortability_eq_cross]
  refine le_trans (PortabilityMetricCompilation.abs_crossRatio_sub_le
    (budgetMomentFeature (Deme := Deme) (Locus := Locus) (Allele := Allele) (fun _ ↦ 2)) hδ
    (abs_budgetMomentFeature_le (first 0) (fun _ ↦ 2)) _ _ _ _
    (rateHistoryDualPropagator_mulVec_mem_realizationBody hT (hfirst _) x0)
    (rateHistoryDualPropagator_mulVec_mem_realizationBody hT (hsecond _) x0)
    htarget₁ hsource₁ htarget₂ hsource₂) ?_
  refine mul_le_mul_of_nonneg_left hdistance (div_nonneg ?_ (pow_nonneg hδ.le 4))
  exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg
    (mul_nonneg (by norm_num) (pow_nonneg hbound 3)) (hmass _)) (hmass _)) (hmass _)) (hmass _)

/-- **Calibration portability under the process law is Lipschitz in the rate path.**  For two
rate histories with continuous dual generators, where the expected target score variance and the
expected source covariance are at least `δ` under both neutral Markov kernels, the calibration
portability of expectations moves by at most the composed constant times the `L¹([0, T])`
distance of the dual generator paths. -/
theorem abs_expectedCalibrationPortability_rateHistory_sub_le
    {first second : ℝ → NeutralRates Deme Locus Allele} {T : ℝ} (hT : 0 ≤ T)
    (hfirst : ∀ capacity : Locus → ℕ,
      ContinuousOn (fun t ↦ dualGenerator (first t) capacity) (Set.Icc 0 T))
    (hsecond : ∀ capacity : Locus → ℕ,
      ContinuousOn (fun t ↦ dualGenerator (second t) capacity) (Set.Icc 0 T))
    (ℓ₀ : Locus) (hap₀ : FullHaplotype Locus Allele) (x0 : FrequencyState Deme Locus Allele)
    (source target : Deme) (score outcome : FullHaplotype Locus Allele → ℝ) {δ : ℝ} (hδ : 0 < δ)
    (htarget₁ : δ ≤ ∫ y, (stateLaw y target).variance score
      ∂(rateHistoryKernel first ℓ₀ hap₀ hT hfirst x0))
    (hsource₁ : δ ≤ ∫ y, (stateLaw y source).covariance score outcome
      ∂(rateHistoryKernel first ℓ₀ hap₀ hT hfirst x0))
    (htarget₂ : δ ≤ ∫ y, (stateLaw y target).variance score
      ∂(rateHistoryKernel second ℓ₀ hap₀ hT hsecond x0))
    (hsource₂ : δ ≤ ∫ y, (stateLaw y source).covariance score outcome
      ∂(rateHistoryKernel second ℓ₀ hap₀ hT hsecond x0)) :
    |expectedCalibrationPortability (rateHistoryKernel first ℓ₀ hap₀ hT hfirst) x0 source target
        score outcome
      - expectedCalibrationPortability (rateHistoryKernel second ℓ₀ hap₀ hT hsecond) x0 source
          target score outcome|
      ≤ 4 * featureBound (first 0) (fun _ ↦ 2) ^ 3
          * (∑ i, |budgetCoefficients ℓ₀ (fun _ ↦ 2)
              (demeCovariancePolynomial target score outcome) i|)
          * (∑ i, |budgetCoefficients ℓ₀ (fun _ ↦ 2)
              (demeCovariancePolynomial source score score) i|)
          * (∑ i, |budgetCoefficients ℓ₀ (fun _ ↦ 2)
              (demeCovariancePolynomial target score score) i|)
          * (∑ i, |budgetCoefficients ℓ₀ (fun _ ↦ 2)
              (demeCovariancePolynomial source score outcome) i|)
          / δ ^ 4
        * ((∫ s in (0 : ℝ)..T, ‖dualGeneratorPath first (fun _ ↦ 2) T s
              - dualGeneratorPath second (fun _ ↦ 2) T s‖)
            * Real.exp (∫ s in (0 : ℝ)..T, ‖dualGeneratorPath first (fun _ ↦ 2) T s‖)
            * Real.exp (∫ s in (0 : ℝ)..T, ‖dualGeneratorPath second (fun _ ↦ 2) T s‖)
          * featureBound (first 0) (fun _ ↦ 2)) := by
  rw [integral_variance_rateHistoryKernel hT hfirst ℓ₀ hap₀ (le_refl 2) x0 target
    score] at htarget₁
  rw [integral_variance_rateHistoryKernel hT hsecond ℓ₀ hap₀ (le_refl 2) x0 target
    score] at htarget₂
  rw [integral_covariance_rateHistoryKernel hT hfirst ℓ₀ hap₀ (le_refl 2) x0 source score
    outcome] at hsource₁
  rw [integral_covariance_rateHistoryKernel hT hsecond ℓ₀ hap₀ (le_refl 2) x0 source score
    outcome] at hsource₂
  rw [expectedCalibrationPortability_rateHistoryKernel hT hfirst ℓ₀ hap₀ (le_refl 2),
    expectedCalibrationPortability_rateHistoryKernel hT hsecond ℓ₀ hap₀ (le_refl 2)]
  exact abs_momentCalibrationPortability_rateHistory_sub_le hT hfirst hsecond ℓ₀ x0 source target
    score outcome hδ htarget₁ hsource₁ htarget₂ hsource₂

end

end Descent.Portability.EndToEndCalibrationLaw
