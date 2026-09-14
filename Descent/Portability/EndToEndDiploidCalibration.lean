/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.EndToEndCalibrationLaw
import Descent.Portability.EndToEndDiploidHistoryLaw

assert_below Descent.Decision Descent.Program

/-!
# The calibration law of scores read on diploid genotypes

`EndToEndCalibrationLaw` carries a demographic history to the calibration of a score read on one
haplotype: the regression slope of the outcome on the score, its portability and its intercept.
This module carries it to scores and outcomes read on the gamete pair of `EndToEndDiploidLaw`, with
dominance and interaction between the gametes included.  It also shows that dominance breaks the
haploid transfer.

Calibration of expectations on gamete pairs.  Each deme forms its gamete pairs at its own
inbreeding coefficient.  The slope `E C_SY / E V_S`, its target-over-source portability, and the
intercept `E[μ_Y V_S - C_SY μ_S] / E V_S` are read on those laws (`expectedDiploidCalibrationSlope`,
`expectedDiploidCalibrationPortability`, `expectedDiploidCalibrationIntercept`).  As in the haploid
law, each is the ratio-of-expectations query of NOTE2 §6.2.

The additive transfer.  For additive lifts `S(h₁) + S(h₂)` and `Y(h₁) + Y(h₂)` at any inbreeding
coefficients in the unit interval, the covariance and the score variance of a deme both carry
`2 (1 + F)` and the means carry `2` (`EndToEndDiploidLaw`).
* The slope and the portability of expectations are the haploid ones, and the intercept is twice
  the haploid one (`expectedDiploidCalibrationSlope_diploidSum`,
  `expectedDiploidCalibrationPortability_diploidSum`,
  `expectedDiploidCalibrationIntercept_diploidSum`).
* Along a history of epochs, splits and pulses, or along a rate history, they are the haploid
  rational functions of the propagated budget-2 moments for slope and portability and budget-3
  moments for the intercept (`expectedDiploidCalibrationSlope_diploidSum_historyEventKernel`,
  `expectedDiploidCalibrationPortability_diploidSum_historyEventKernel`,
  `expectedDiploidCalibrationIntercept_diploidSum_historyEventKernel`, and the `rateHistoryKernel`
  forms).

Any gamete-pair observables.  The mean of a gamete-pair observable is a frequency polynomial of
degree two, a covariance one of degree four, and the intercept accumulator one of degree six
(`diploidMeanPolynomial`, `diploidCovariancePolynomial`, `diploidInterceptPolynomial`, with their
`polynomialFunction_` and `totalDegree_` lemmas).
* Under a Markov kernel whose budget-`n` moments are a matrix `M`, the slope and portability of
  expectations are rational functions of `M · Hₙ(x₀)` for `n ≥ 4`, and the intercept for `n ≥ 6`
  (`expectedDiploidCalibrationSlope_eq_moment`, `expectedDiploidCalibrationPortability_eq_moment`,
  `expectedDiploidCalibrationIntercept_eq_moment`).
* The propagator is the chronological one along an event history and the rate-history one along a
  rate path (`expectedDiploidCalibrationSlope_historyEventKernel`,
  `expectedDiploidCalibrationPortability_historyEventKernel`,
  `expectedDiploidCalibrationIntercept_historyEventKernel`, and the `rateHistoryKernel` forms).
* Two event histories with equal propagated moments give equal slope, portability and intercept
  (`expectedDiploidCalibrationSlope_eq_of_moments_eq`,
  `expectedDiploidCalibrationPortability_eq_of_moments_eq`,
  `expectedDiploidCalibrationIntercept_eq_of_moments_eq`).
* For additive lifts the budget-4 slope of the budget-4 moments of a history is the haploid
  budget-2 slope, and the budget-6 intercept is twice the haploid budget-3 intercept
  (`momentDiploidCalibrationSlope_diploidSum_historyEventKernel`,
  `momentDiploidCalibrationIntercept_diploidSum_historyEventKernel`).

The boundary.  At one biallelic site with allele frequency one half, the additive score and the
recessive homozygote indicator have diploid calibration slope `1 / 2` for every inbreeding
coefficient, and intercept `E Y - (1 / 2) E S = (F - 1) / 4`
(`calibrationSlope_inbredMating_diploidProduct`).  The allele regressed on itself in one haplotype
has slope `1` (`calibrationSlope_fairSwitch_alleleValue`).  So the slope does not transfer from the
haploid law under random union, and the intercept moves with the inbreeding coefficient
(`diploidProduct_breaks_calibration_transfer`).

Significance.  Calibration of genotype-read scores keeps the finite-moment structure of the
haploid calibration law.  For additive scores and outcomes it is the haploid law itself, with the
intercept doubled.  Under dominance the budget doubles, the inbreeding coefficients enter the
coefficients, and the haploid slope is no longer the answer.

Scope.  The gamete pair is the one of `EndToEndDiploidLaw`: both gametes are drawn from the deme's
own haplotype law, and identity by descent is one whole-haplotype event with a coefficient supplied
per deme.  Every result is the ratio-of-expectations query; the expectation of the per-population
slope or intercept is not stated.  The boundary witness is one law at one site.

## Empirical status

None.  The bodies are polynomial identities, finite sums against constructed laws and integrals of
polynomials against Markov kernels, so no measurement can bear on them.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.EndToEndDiploidCalibration

open MeasureTheory ProbabilityTheory MvPolynomial Descent.Coalescent PartialHaplotypeCarrier
  PartialHaplotypeDualGenerator PartialHaplotypeDualSemigroup NeutralFellerGenerator
  NeutralPolynomialSemigroup PartialHaplotypeMicroscopicApproximation PartialHaplotypePulseKernel
  NeutralPulseHistoryKernel NeutralRateHistoryRealization NeutralRateHistoryKernel
  ReplicaMetricInstances EndToEndPortabilityLaw EndToEndCalibrationLaw EndToEndDiploidLaw
  EndToEndDiploidHistoryLaw
open scoped Matrix NNReal

noncomputable section

section History

variable {Deme Locus : Type*} {Allele : Locus → Type*}
variable [Fintype Deme] [DecidableEq Deme] [Fintype Locus] [DecidableEq Locus]
  [∀ ℓ, Fintype (Allele ℓ)] [∀ ℓ, DecidableEq (Allele ℓ)]

/-! ## Calibration of expectations on gamete pairs -/

/-- **The diploid calibration slope of expectations**: the expected covariance of two gamete-pair
observables in a deme over the expected variance of the score, `E C_SY / E V_S`, each deme forming
its gamete pairs at its own inbreeding coefficient.  NOTE2 §6.2 query: a ratio of expectations. -/
def expectedDiploidCalibrationSlope
    (κ : Kernel (FrequencyState Deme Locus Allele) (FrequencyState Deme Locus Allele))
    (x0 : FrequencyState Deme Locus Allele) (deme : Deme) (inbreeding : Deme → ℝ)
    (hF0 : ∀ other, 0 ≤ inbreeding other) (hF1 : ∀ other, inbreeding other ≤ 1)
    (score outcome : FullHaplotype Locus Allele × FullHaplotype Locus Allele → ℝ) : ℝ :=
  (∫ y, (stateGenotypeLaw y deme inbreeding hF0 hF1).covariance score outcome ∂(κ x0))
    / ∫ y, (stateGenotypeLaw y deme inbreeding hF0 hF1).variance score ∂(κ x0)

/-- **The diploid calibration portability of expectations**: the target diploid slope of
expectations over the source one. -/
def expectedDiploidCalibrationPortability
    (κ : Kernel (FrequencyState Deme Locus Allele) (FrequencyState Deme Locus Allele))
    (x0 : FrequencyState Deme Locus Allele) (source target : Deme) (inbreeding : Deme → ℝ)
    (hF0 : ∀ other, 0 ≤ inbreeding other) (hF1 : ∀ other, inbreeding other ≤ 1)
    (score outcome : FullHaplotype Locus Allele × FullHaplotype Locus Allele → ℝ) : ℝ :=
  expectedDiploidCalibrationSlope κ x0 target inbreeding hF0 hF1 score outcome
    / expectedDiploidCalibrationSlope κ x0 source inbreeding hF0 hF1 score outcome

/-- **The diploid calibration intercept of expectations**: the expected intercept accumulator
`E[μ_Y V_S - C_SY μ_S]` of the gamete-pair law of a deme over its expected score variance. -/
def expectedDiploidCalibrationIntercept
    (κ : Kernel (FrequencyState Deme Locus Allele) (FrequencyState Deme Locus Allele))
    (x0 : FrequencyState Deme Locus Allele) (deme : Deme) (inbreeding : Deme → ℝ)
    (hF0 : ∀ other, 0 ≤ inbreeding other) (hF1 : ∀ other, inbreeding other ≤ 1)
    (score outcome : FullHaplotype Locus Allele × FullHaplotype Locus Allele → ℝ) : ℝ :=
  (∫ y, ((stateGenotypeLaw y deme inbreeding hF0 hF1).expectation outcome
        * (stateGenotypeLaw y deme inbreeding hF0 hF1).variance score
      - (stateGenotypeLaw y deme inbreeding hF0 hF1).covariance score outcome
        * (stateGenotypeLaw y deme inbreeding hF0 hF1).expectation score) ∂(κ x0))
    / ∫ y, (stateGenotypeLaw y deme inbreeding hF0 hF1).variance score ∂(κ x0)

/-! ## The additive transfer -/

/-- **The additive diploid slope of expectations is the haploid one.**  Covariance and score
variance both carry `2 (1 + F)`, which cancels, under every kernel. -/
theorem expectedDiploidCalibrationSlope_diploidSum
    (κ : Kernel (FrequencyState Deme Locus Allele) (FrequencyState Deme Locus Allele))
    (x0 : FrequencyState Deme Locus Allele) (deme : Deme) (inbreeding : Deme → ℝ)
    (hF0 : ∀ other, 0 ≤ inbreeding other) (hF1 : ∀ other, inbreeding other ≤ 1)
    (score outcome : FullHaplotype Locus Allele → ℝ) :
    expectedDiploidCalibrationSlope κ x0 deme inbreeding hF0 hF1 (diploidSum score)
        (diploidSum outcome)
      = expectedCalibrationSlope κ x0 deme score outcome := by
  have hscale : 2 * (1 + inbreeding deme) ≠ 0 :=
    (by linarith [hF0 deme] : (0 : ℝ) < 2 * (1 + inbreeding deme)).ne'
  simp only [expectedDiploidCalibrationSlope, expectedCalibrationSlope, stateGenotypeLaw,
    covariance_inbredMating_diploidSum, variance_inbredMating_diploidSum, integral_const_mul]
  exact mul_div_mul_left _ _ hscale

/-- **The additive diploid calibration portability of expectations is the haploid one**, under
every kernel and whatever the source and target inbreeding coefficients. -/
theorem expectedDiploidCalibrationPortability_diploidSum
    (κ : Kernel (FrequencyState Deme Locus Allele) (FrequencyState Deme Locus Allele))
    (x0 : FrequencyState Deme Locus Allele) (source target : Deme) (inbreeding : Deme → ℝ)
    (hF0 : ∀ other, 0 ≤ inbreeding other) (hF1 : ∀ other, inbreeding other ≤ 1)
    (score outcome : FullHaplotype Locus Allele → ℝ) :
    expectedDiploidCalibrationPortability κ x0 source target inbreeding hF0 hF1 (diploidSum score)
        (diploidSum outcome)
      = expectedCalibrationPortability κ x0 source target score outcome := by
  rw [expectedDiploidCalibrationPortability, expectedDiploidCalibrationSlope_diploidSum,
    expectedDiploidCalibrationSlope_diploidSum, expectedCalibrationPortability]

/-- **The additive diploid intercept of expectations is twice the haploid one.**  The intercept
accumulator carries `4 (1 + F)` and the score variance `2 (1 + F)`, under every kernel. -/
theorem expectedDiploidCalibrationIntercept_diploidSum
    (κ : Kernel (FrequencyState Deme Locus Allele) (FrequencyState Deme Locus Allele))
    (x0 : FrequencyState Deme Locus Allele) (deme : Deme) (inbreeding : Deme → ℝ)
    (hF0 : ∀ other, 0 ≤ inbreeding other) (hF1 : ∀ other, inbreeding other ≤ 1)
    (score outcome : FullHaplotype Locus Allele → ℝ) :
    expectedDiploidCalibrationIntercept κ x0 deme inbreeding hF0 hF1 (diploidSum score)
        (diploidSum outcome)
      = 2 * expectedCalibrationIntercept κ x0 deme score outcome := by
  have hscale : 2 * (1 + inbreeding deme) ≠ 0 :=
    (by linarith [hF0 deme] : (0 : ℝ) < 2 * (1 + inbreeding deme)).ne'
  have hpoint : ∀ y : FrequencyState Deme Locus Allele,
      (stateGenotypeLaw y deme inbreeding hF0 hF1).expectation (diploidSum outcome)
          * (stateGenotypeLaw y deme inbreeding hF0 hF1).variance (diploidSum score)
        - (stateGenotypeLaw y deme inbreeding hF0 hF1).covariance (diploidSum score)
            (diploidSum outcome)
          * (stateGenotypeLaw y deme inbreeding hF0 hF1).expectation (diploidSum score)
      = 2 * (2 * (1 + inbreeding deme))
          * ((stateLaw y deme).expectation outcome * (stateLaw y deme).variance score
            - (stateLaw y deme).covariance score outcome
              * (stateLaw y deme).expectation score) := by
    intro y
    simp only [stateGenotypeLaw, expectation_inbredMating_diploidSum,
      variance_inbredMating_diploidSum, covariance_inbredMating_diploidSum]
    ring
  have hvariance : ∀ y : FrequencyState Deme Locus Allele,
      (stateGenotypeLaw y deme inbreeding hF0 hF1).variance (diploidSum score)
        = 2 * (1 + inbreeding deme) * (stateLaw y deme).variance score :=
    fun y ↦ variance_inbredMating_diploidSum _ _ _ _ score
  have hcancel : ∀ c a b : ℝ, c ≠ 0 → 2 * c * a / (c * b) = 2 * (a / b) := fun c a b hc ↦ by
    rw [mul_assoc, mul_div_assoc, mul_div_mul_left _ _ hc]
  simp only [expectedDiploidCalibrationIntercept, hpoint]
  simp only [hvariance, integral_const_mul, expectedCalibrationIntercept]
  exact hcancel _ _ _ hscale

/-- **The additive diploid slope along a history** is, for every budget `n ≥ 2`, the haploid
rational slope of the chronological propagator applied to the budget-`n` moments of `x₀`. -/
theorem expectedDiploidCalibrationSlope_diploidSum_historyEventKernel (ℓ₀ : Locus)
    (hap₀ : FullHaplotype Locus Allele)
    (events : List ((NeutralRates Deme Locus Allele × ℝ≥0) ⊕ PulseMatrix Deme)) {n : ℕ}
    (hn : 2 ≤ n) (x0 : FrequencyState Deme Locus Allele) (deme : Deme) (inbreeding : Deme → ℝ)
    (hF0 : ∀ other, 0 ≤ inbreeding other) (hF1 : ∀ other, inbreeding other ≤ 1)
    (score outcome : FullHaplotype Locus Allele → ℝ) :
    expectedDiploidCalibrationSlope (historyEventKernel ℓ₀ hap₀ events) x0 deme inbreeding hF0 hF1
        (diploidSum score) (diploidSum outcome)
      = momentCalibrationSlope ℓ₀ n deme score outcome
          (historyEventPropagator (fun _ ↦ n) events *ᵥ budgetMomentFeature (fun _ ↦ n) x0) := by
  rw [expectedDiploidCalibrationSlope_diploidSum,
    expectedCalibrationSlope_historyEventKernel ℓ₀ hap₀ events hn]

/-- **The additive diploid calibration portability along a history**, at every budget `n ≥ 2`. -/
theorem expectedDiploidCalibrationPortability_diploidSum_historyEventKernel (ℓ₀ : Locus)
    (hap₀ : FullHaplotype Locus Allele)
    (events : List ((NeutralRates Deme Locus Allele × ℝ≥0) ⊕ PulseMatrix Deme)) {n : ℕ}
    (hn : 2 ≤ n) (x0 : FrequencyState Deme Locus Allele) (source target : Deme)
    (inbreeding : Deme → ℝ) (hF0 : ∀ other, 0 ≤ inbreeding other)
    (hF1 : ∀ other, inbreeding other ≤ 1) (score outcome : FullHaplotype Locus Allele → ℝ) :
    expectedDiploidCalibrationPortability (historyEventKernel ℓ₀ hap₀ events) x0 source target
        inbreeding hF0 hF1 (diploidSum score) (diploidSum outcome)
      = momentCalibrationPortability ℓ₀ n source target score outcome
          (historyEventPropagator (fun _ ↦ n) events *ᵥ budgetMomentFeature (fun _ ↦ n) x0) := by
  rw [expectedDiploidCalibrationPortability_diploidSum,
    expectedCalibrationPortability_historyEventKernel ℓ₀ hap₀ events hn]

/-- **The additive diploid intercept along a history** is, for every budget `n ≥ 3`, twice the
haploid rational intercept of the propagated budget-`n` moments. -/
theorem expectedDiploidCalibrationIntercept_diploidSum_historyEventKernel (ℓ₀ : Locus)
    (hap₀ : FullHaplotype Locus Allele)
    (events : List ((NeutralRates Deme Locus Allele × ℝ≥0) ⊕ PulseMatrix Deme)) {n : ℕ}
    (hn : 3 ≤ n) (x0 : FrequencyState Deme Locus Allele) (deme : Deme) (inbreeding : Deme → ℝ)
    (hF0 : ∀ other, 0 ≤ inbreeding other) (hF1 : ∀ other, inbreeding other ≤ 1)
    (score outcome : FullHaplotype Locus Allele → ℝ) :
    expectedDiploidCalibrationIntercept (historyEventKernel ℓ₀ hap₀ events) x0 deme inbreeding
        hF0 hF1 (diploidSum score) (diploidSum outcome)
      = 2 * momentCalibrationIntercept ℓ₀ n deme score outcome
          (historyEventPropagator (fun _ ↦ n) events *ᵥ budgetMomentFeature (fun _ ↦ n) x0) := by
  rw [expectedDiploidCalibrationIntercept_diploidSum,
    expectedCalibrationIntercept_historyEventKernel ℓ₀ hap₀ events hn]

/-- **The additive diploid slope along a rate history**, at every budget `n ≥ 2`. -/
theorem expectedDiploidCalibrationSlope_diploidSum_rateHistoryKernel
    {rates : ℝ → NeutralRates Deme Locus Allele} {T : ℝ} (hT : 0 ≤ T)
    (hcontinuous : ∀ capacity : Locus → ℕ,
      ContinuousOn (fun t ↦ dualGenerator (rates t) capacity) (Set.Icc 0 T))
    (ℓ₀ : Locus) (hap₀ : FullHaplotype Locus Allele) {n : ℕ} (hn : 2 ≤ n)
    (x0 : FrequencyState Deme Locus Allele) (deme : Deme) (inbreeding : Deme → ℝ)
    (hF0 : ∀ other, 0 ≤ inbreeding other) (hF1 : ∀ other, inbreeding other ≤ 1)
    (score outcome : FullHaplotype Locus Allele → ℝ) :
    expectedDiploidCalibrationSlope (rateHistoryKernel rates ℓ₀ hap₀ hT hcontinuous) x0 deme
        inbreeding hF0 hF1 (diploidSum score) (diploidSum outcome)
      = momentCalibrationSlope ℓ₀ n deme score outcome
          (rateHistoryDualPropagator rates (fun _ ↦ n) T
            *ᵥ budgetMomentFeature (fun _ ↦ n) x0) := by
  rw [expectedDiploidCalibrationSlope_diploidSum,
    expectedCalibrationSlope_rateHistoryKernel hT hcontinuous ℓ₀ hap₀ hn]

/-- **The additive diploid calibration portability along a rate history**, at every budget
`n ≥ 2`. -/
theorem expectedDiploidCalibrationPortability_diploidSum_rateHistoryKernel
    {rates : ℝ → NeutralRates Deme Locus Allele} {T : ℝ} (hT : 0 ≤ T)
    (hcontinuous : ∀ capacity : Locus → ℕ,
      ContinuousOn (fun t ↦ dualGenerator (rates t) capacity) (Set.Icc 0 T))
    (ℓ₀ : Locus) (hap₀ : FullHaplotype Locus Allele) {n : ℕ} (hn : 2 ≤ n)
    (x0 : FrequencyState Deme Locus Allele) (source target : Deme) (inbreeding : Deme → ℝ)
    (hF0 : ∀ other, 0 ≤ inbreeding other) (hF1 : ∀ other, inbreeding other ≤ 1)
    (score outcome : FullHaplotype Locus Allele → ℝ) :
    expectedDiploidCalibrationPortability (rateHistoryKernel rates ℓ₀ hap₀ hT hcontinuous) x0
        source target inbreeding hF0 hF1 (diploidSum score) (diploidSum outcome)
      = momentCalibrationPortability ℓ₀ n source target score outcome
          (rateHistoryDualPropagator rates (fun _ ↦ n) T
            *ᵥ budgetMomentFeature (fun _ ↦ n) x0) := by
  rw [expectedDiploidCalibrationPortability_diploidSum,
    expectedCalibrationPortability_rateHistoryKernel hT hcontinuous ℓ₀ hap₀ hn]

/-- **The additive diploid intercept along a rate history**, twice the haploid rational intercept
at every budget `n ≥ 3`. -/
theorem expectedDiploidCalibrationIntercept_diploidSum_rateHistoryKernel
    {rates : ℝ → NeutralRates Deme Locus Allele} {T : ℝ} (hT : 0 ≤ T)
    (hcontinuous : ∀ capacity : Locus → ℕ,
      ContinuousOn (fun t ↦ dualGenerator (rates t) capacity) (Set.Icc 0 T))
    (ℓ₀ : Locus) (hap₀ : FullHaplotype Locus Allele) {n : ℕ} (hn : 3 ≤ n)
    (x0 : FrequencyState Deme Locus Allele) (deme : Deme) (inbreeding : Deme → ℝ)
    (hF0 : ∀ other, 0 ≤ inbreeding other) (hF1 : ∀ other, inbreeding other ≤ 1)
    (score outcome : FullHaplotype Locus Allele → ℝ) :
    expectedDiploidCalibrationIntercept (rateHistoryKernel rates ℓ₀ hap₀ hT hcontinuous) x0 deme
        inbreeding hF0 hF1 (diploidSum score) (diploidSum outcome)
      = 2 * momentCalibrationIntercept ℓ₀ n deme score outcome
          (rateHistoryDualPropagator rates (fun _ ↦ n) T
            *ᵥ budgetMomentFeature (fun _ ↦ n) x0) := by
  rw [expectedDiploidCalibrationIntercept_diploidSum,
    expectedCalibrationIntercept_rateHistoryKernel hT hcontinuous ℓ₀ hap₀ hn]

/-! ## Calibration accumulators of gamete-pair observables as frequency polynomials -/

/-- The mean of a gamete-pair observable in one deme, at that deme's inbreeding coefficient, as a
frequency polynomial of degree two. -/
def diploidMeanPolynomial (deme : Deme) (inbreeding : Deme → ℝ)
    (value : FullHaplotype Locus Allele × FullHaplotype Locus Allele → ℝ) :
    FrequencyPolynomial Deme Locus Allele :=
  demePolynomial deme (genotypeExpectationPolynomial (inbreeding deme) value)

/-- The covariance of two gamete-pair observables in one deme, as a frequency polynomial of degree
four. -/
def diploidCovariancePolynomial (deme : Deme) (inbreeding : Deme → ℝ)
    (first second : FullHaplotype Locus Allele × FullHaplotype Locus Allele → ℝ) :
    FrequencyPolynomial Deme Locus Allele :=
  demePolynomial deme (genotypeCovariancePolynomial (inbreeding deme) first second)

/-- The intercept accumulator `μ_Y V_S - C_SY μ_S` of gamete-pair observables in one deme, as a
frequency polynomial of degree six. -/
def diploidInterceptPolynomial (deme : Deme) (inbreeding : Deme → ℝ)
    (score outcome : FullHaplotype Locus Allele × FullHaplotype Locus Allele → ℝ) :
    FrequencyPolynomial Deme Locus Allele :=
  diploidMeanPolynomial deme inbreeding outcome * diploidCovariancePolynomial deme inbreeding score
      score
    - diploidCovariancePolynomial deme inbreeding score outcome
      * diploidMeanPolynomial deme inbreeding score

/-- At a state, the diploid mean polynomial is the expectation under the deme's gamete-pair law. -/
theorem polynomialFunction_diploidMeanPolynomial (deme : Deme) (inbreeding : Deme → ℝ)
    (hF0 : ∀ other, 0 ≤ inbreeding other) (hF1 : ∀ other, inbreeding other ≤ 1)
    (value : FullHaplotype Locus Allele × FullHaplotype Locus Allele → ℝ)
    (y : FrequencyState Deme Locus Allele) :
    polynomialFunction (diploidMeanPolynomial deme inbreeding value) y
      = (stateGenotypeLaw y deme inbreeding hF0 hF1).expectation value := by
  rw [stateGenotypeLaw, polynomialFunction_apply, diploidMeanPolynomial, eval_demePolynomial,
    eval_genotypeExpectationPolynomial (stateLaw y deme) (inbreeding deme) (hF0 deme) (hF1 deme)]

/-- At a state, the diploid covariance polynomial is the covariance under the deme's gamete-pair
law. -/
theorem polynomialFunction_diploidCovariancePolynomial (deme : Deme) (inbreeding : Deme → ℝ)
    (hF0 : ∀ other, 0 ≤ inbreeding other) (hF1 : ∀ other, inbreeding other ≤ 1)
    (first second : FullHaplotype Locus Allele × FullHaplotype Locus Allele → ℝ)
    (y : FrequencyState Deme Locus Allele) :
    polynomialFunction (diploidCovariancePolynomial deme inbreeding first second) y
      = (stateGenotypeLaw y deme inbreeding hF0 hF1).covariance first second := by
  rw [stateGenotypeLaw, polynomialFunction_apply, diploidCovariancePolynomial, eval_demePolynomial,
    eval_genotypeCovariancePolynomial (stateLaw y deme) (inbreeding deme) (hF0 deme) (hF1 deme)]

/-- At a state, the diploid covariance polynomial of an observable with itself is its variance
under the deme's gamete-pair law. -/
theorem polynomialFunction_diploidVariance (deme : Deme) (inbreeding : Deme → ℝ)
    (hF0 : ∀ other, 0 ≤ inbreeding other) (hF1 : ∀ other, inbreeding other ≤ 1)
    (value : FullHaplotype Locus Allele × FullHaplotype Locus Allele → ℝ)
    (y : FrequencyState Deme Locus Allele) :
    polynomialFunction (diploidCovariancePolynomial deme inbreeding value value) y
      = (stateGenotypeLaw y deme inbreeding hF0 hF1).variance value :=
  polynomialFunction_diploidCovariancePolynomial deme inbreeding hF0 hF1 value value y

/-- At a state, the diploid intercept polynomial is `μ_Y V_S - C_SY μ_S` of the deme's gamete-pair
law. -/
theorem polynomialFunction_diploidInterceptPolynomial (deme : Deme) (inbreeding : Deme → ℝ)
    (hF0 : ∀ other, 0 ≤ inbreeding other) (hF1 : ∀ other, inbreeding other ≤ 1)
    (score outcome : FullHaplotype Locus Allele × FullHaplotype Locus Allele → ℝ)
    (y : FrequencyState Deme Locus Allele) :
    polynomialFunction (diploidInterceptPolynomial deme inbreeding score outcome) y
      = (stateGenotypeLaw y deme inbreeding hF0 hF1).expectation outcome
          * (stateGenotypeLaw y deme inbreeding hF0 hF1).variance score
        - (stateGenotypeLaw y deme inbreeding hF0 hF1).covariance score outcome
          * (stateGenotypeLaw y deme inbreeding hF0 hF1).expectation score := by
  rw [← polynomialFunction_diploidMeanPolynomial deme inbreeding hF0 hF1 outcome y,
    ← polynomialFunction_diploidVariance deme inbreeding hF0 hF1 score y,
    ← polynomialFunction_diploidCovariancePolynomial deme inbreeding hF0 hF1 score outcome y,
    ← polynomialFunction_diploidMeanPolynomial deme inbreeding hF0 hF1 score y]
  simp only [polynomialFunction_apply, diploidInterceptPolynomial, map_sub, map_mul]

/-- The diploid mean polynomial has total degree at most two. -/
theorem totalDegree_diploidMeanPolynomial_le (deme : Deme) (inbreeding : Deme → ℝ)
    (value : FullHaplotype Locus Allele × FullHaplotype Locus Allele → ℝ) :
    (diploidMeanPolynomial deme inbreeding value).totalDegree ≤ 2 :=
  (totalDegree_rename_le _ _).trans (totalDegree_genotypeExpectationPolynomial_le _ value)

/-- The diploid covariance polynomial has total degree at most four. -/
theorem totalDegree_diploidCovariancePolynomial_le (deme : Deme) (inbreeding : Deme → ℝ)
    (first second : FullHaplotype Locus Allele × FullHaplotype Locus Allele → ℝ) :
    (diploidCovariancePolynomial deme inbreeding first second).totalDegree ≤ 4 :=
  (totalDegree_rename_le _ _).trans (totalDegree_genotypeCovariancePolynomial_le _ first second)

/-- The diploid intercept polynomial has total degree at most six. -/
theorem totalDegree_diploidInterceptPolynomial_le (deme : Deme) (inbreeding : Deme → ℝ)
    (score outcome : FullHaplotype Locus Allele × FullHaplotype Locus Allele → ℝ) :
    (diploidInterceptPolynomial deme inbreeding score outcome).totalDegree ≤ 6 := by
  have hmeanOutcome := totalDegree_diploidMeanPolynomial_le deme inbreeding outcome
  have hmeanScore := totalDegree_diploidMeanPolynomial_le deme inbreeding score
  have hvariance := totalDegree_diploidCovariancePolynomial_le deme inbreeding score score
  have hcovariance := totalDegree_diploidCovariancePolynomial_le deme inbreeding score outcome
  refine (totalDegree_sub _ _).trans (max_le ?_ ?_)
  · exact (totalDegree_mul _ _).trans (by omega)
  · exact (totalDegree_mul _ _).trans (by omega)

/-! ## The rational diploid calibration functions -/

/-- **The rational diploid calibration slope** of a budget-`n` moment vector. -/
def momentDiploidCalibrationSlope (ℓ₀ : Locus) (n : ℕ) (deme : Deme) (inbreeding : Deme → ℝ)
    (score outcome : FullHaplotype Locus Allele × FullHaplotype Locus Allele → ℝ)
    (v : BudgetConfiguration Deme Locus Allele (fun _ ↦ n) → ℝ) : ℝ :=
  (budgetCoefficients ℓ₀ (fun _ ↦ n) (diploidCovariancePolynomial deme inbreeding score outcome)
      ⬝ᵥ v)
    / (budgetCoefficients ℓ₀ (fun _ ↦ n) (diploidCovariancePolynomial deme inbreeding score score)
      ⬝ᵥ v)

/-- **The rational diploid calibration portability** of a budget-`n` moment vector. -/
def momentDiploidCalibrationPortability (ℓ₀ : Locus) (n : ℕ) (source target : Deme)
    (inbreeding : Deme → ℝ)
    (score outcome : FullHaplotype Locus Allele × FullHaplotype Locus Allele → ℝ)
    (v : BudgetConfiguration Deme Locus Allele (fun _ ↦ n) → ℝ) : ℝ :=
  momentDiploidCalibrationSlope ℓ₀ n target inbreeding score outcome v
    / momentDiploidCalibrationSlope ℓ₀ n source inbreeding score outcome v

/-- **The rational diploid calibration intercept** of a budget-`n` moment vector. -/
def momentDiploidCalibrationIntercept (ℓ₀ : Locus) (n : ℕ) (deme : Deme) (inbreeding : Deme → ℝ)
    (score outcome : FullHaplotype Locus Allele × FullHaplotype Locus Allele → ℝ)
    (v : BudgetConfiguration Deme Locus Allele (fun _ ↦ n) → ℝ) : ℝ :=
  (budgetCoefficients ℓ₀ (fun _ ↦ n) (diploidInterceptPolynomial deme inbreeding score outcome)
      ⬝ᵥ v)
    / (budgetCoefficients ℓ₀ (fun _ ↦ n) (diploidCovariancePolynomial deme inbreeding score score)
      ⬝ᵥ v)

/-! ## Integrating against a kernel with the dual moments -/

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

/-- Under a kernel with budget-`n` moments `M`, `n ≥ 4`, the diploid calibration slope of
expectations is the rational diploid slope of the propagated moments. -/
theorem expectedDiploidCalibrationSlope_eq_moment (hn : 4 ≤ n)
    (x0 : FrequencyState Deme Locus Allele) (deme : Deme) (inbreeding : Deme → ℝ)
    (hF0 : ∀ other, 0 ≤ inbreeding other) (hF1 : ∀ other, inbreeding other ≤ 1)
    (score outcome : FullHaplotype Locus Allele × FullHaplotype Locus Allele → ℝ) :
    expectedDiploidCalibrationSlope κ x0 deme inbreeding hF0 hF1 score outcome
      = momentDiploidCalibrationSlope ℓ₀ n deme inbreeding score outcome
          (M *ᵥ budgetMomentFeature (fun _ ↦ n) x0) := by
  rw [expectedDiploidCalibrationSlope, momentDiploidCalibrationSlope,
    integral_eq_dotProduct_of_totalDegree_le ℓ₀ κ M hmoment _
      ((totalDegree_diploidCovariancePolynomial_le deme inbreeding score outcome).trans hn) _
      (polynomialFunction_diploidCovariancePolynomial deme inbreeding hF0 hF1 score outcome) x0,
    integral_eq_dotProduct_of_totalDegree_le ℓ₀ κ M hmoment _
      ((totalDegree_diploidCovariancePolynomial_le deme inbreeding score score).trans hn) _
      (polynomialFunction_diploidVariance deme inbreeding hF0 hF1 score) x0]

/-- Under a kernel with budget-`n` moments `M`, `n ≥ 4`, the diploid calibration portability of
expectations is the rational diploid portability of the propagated moments. -/
theorem expectedDiploidCalibrationPortability_eq_moment (hn : 4 ≤ n)
    (x0 : FrequencyState Deme Locus Allele) (source target : Deme) (inbreeding : Deme → ℝ)
    (hF0 : ∀ other, 0 ≤ inbreeding other) (hF1 : ∀ other, inbreeding other ≤ 1)
    (score outcome : FullHaplotype Locus Allele × FullHaplotype Locus Allele → ℝ) :
    expectedDiploidCalibrationPortability κ x0 source target inbreeding hF0 hF1 score outcome
      = momentDiploidCalibrationPortability ℓ₀ n source target inbreeding score outcome
          (M *ᵥ budgetMomentFeature (fun _ ↦ n) x0) := by
  rw [expectedDiploidCalibrationPortability, momentDiploidCalibrationPortability,
    expectedDiploidCalibrationSlope_eq_moment ℓ₀ κ M hmoment hn x0 target,
    expectedDiploidCalibrationSlope_eq_moment ℓ₀ κ M hmoment hn x0 source]

/-- Under a kernel with budget-`n` moments `M`, `n ≥ 6`, the diploid calibration intercept of
expectations is the rational diploid intercept of the propagated moments. -/
theorem expectedDiploidCalibrationIntercept_eq_moment (hn : 6 ≤ n)
    (x0 : FrequencyState Deme Locus Allele) (deme : Deme) (inbreeding : Deme → ℝ)
    (hF0 : ∀ other, 0 ≤ inbreeding other) (hF1 : ∀ other, inbreeding other ≤ 1)
    (score outcome : FullHaplotype Locus Allele × FullHaplotype Locus Allele → ℝ) :
    expectedDiploidCalibrationIntercept κ x0 deme inbreeding hF0 hF1 score outcome
      = momentDiploidCalibrationIntercept ℓ₀ n deme inbreeding score outcome
          (M *ᵥ budgetMomentFeature (fun _ ↦ n) x0) := by
  rw [expectedDiploidCalibrationIntercept, momentDiploidCalibrationIntercept,
    integral_eq_dotProduct_of_totalDegree_le ℓ₀ κ M hmoment _
      ((totalDegree_diploidInterceptPolynomial_le deme inbreeding score outcome).trans hn) _
      (polynomialFunction_diploidInterceptPolynomial deme inbreeding hF0 hF1 score outcome) x0,
    integral_eq_dotProduct_of_totalDegree_le ℓ₀ κ M hmoment _
      ((totalDegree_diploidCovariancePolynomial_le deme inbreeding score score).trans
        (by omega)) _
      (polynomialFunction_diploidVariance deme inbreeding hF0 hF1 score) x0]

end MomentKernel

/-! ## The diploid calibration law along a history -/

/-- **The diploid calibration slope of expectations along a history of epochs, splits and
pulses.**  For any gamete-pair observables and every budget `n ≥ 4` it is the rational diploid
slope of the chronological propagator applied to the budget-`n` moments of `x₀`. -/
theorem expectedDiploidCalibrationSlope_historyEventKernel (ℓ₀ : Locus)
    (hap₀ : FullHaplotype Locus Allele)
    (events : List ((NeutralRates Deme Locus Allele × ℝ≥0) ⊕ PulseMatrix Deme)) {n : ℕ}
    (hn : 4 ≤ n) (x0 : FrequencyState Deme Locus Allele) (deme : Deme) (inbreeding : Deme → ℝ)
    (hF0 : ∀ other, 0 ≤ inbreeding other) (hF1 : ∀ other, inbreeding other ≤ 1)
    (score outcome : FullHaplotype Locus Allele × FullHaplotype Locus Allele → ℝ) :
    expectedDiploidCalibrationSlope (historyEventKernel ℓ₀ hap₀ events) x0 deme inbreeding hF0 hF1
        score outcome
      = momentDiploidCalibrationSlope ℓ₀ n deme inbreeding score outcome
          (historyEventPropagator (fun _ ↦ n) events *ᵥ budgetMomentFeature (fun _ ↦ n) x0) := by
  haveI := isMarkovKernel_historyEventKernel ℓ₀ hap₀ events
  exact expectedDiploidCalibrationSlope_eq_moment ℓ₀ (historyEventKernel ℓ₀ hap₀ events) _
    (integral_momentPolynomial_historyEventKernel ℓ₀ hap₀ (fun _ ↦ n) events) hn x0 deme
    inbreeding hF0 hF1 score outcome

/-- **The diploid calibration portability of expectations along a history**, at every budget
`n ≥ 4`. -/
theorem expectedDiploidCalibrationPortability_historyEventKernel (ℓ₀ : Locus)
    (hap₀ : FullHaplotype Locus Allele)
    (events : List ((NeutralRates Deme Locus Allele × ℝ≥0) ⊕ PulseMatrix Deme)) {n : ℕ}
    (hn : 4 ≤ n) (x0 : FrequencyState Deme Locus Allele) (source target : Deme)
    (inbreeding : Deme → ℝ) (hF0 : ∀ other, 0 ≤ inbreeding other)
    (hF1 : ∀ other, inbreeding other ≤ 1)
    (score outcome : FullHaplotype Locus Allele × FullHaplotype Locus Allele → ℝ) :
    expectedDiploidCalibrationPortability (historyEventKernel ℓ₀ hap₀ events) x0 source target
        inbreeding hF0 hF1 score outcome
      = momentDiploidCalibrationPortability ℓ₀ n source target inbreeding score outcome
          (historyEventPropagator (fun _ ↦ n) events *ᵥ budgetMomentFeature (fun _ ↦ n) x0) := by
  haveI := isMarkovKernel_historyEventKernel ℓ₀ hap₀ events
  exact expectedDiploidCalibrationPortability_eq_moment ℓ₀ (historyEventKernel ℓ₀ hap₀ events) _
    (integral_momentPolynomial_historyEventKernel ℓ₀ hap₀ (fun _ ↦ n) events) hn x0 source target
    inbreeding hF0 hF1 score outcome

/-- **The diploid calibration intercept of expectations along a history**, at every budget
`n ≥ 6`. -/
theorem expectedDiploidCalibrationIntercept_historyEventKernel (ℓ₀ : Locus)
    (hap₀ : FullHaplotype Locus Allele)
    (events : List ((NeutralRates Deme Locus Allele × ℝ≥0) ⊕ PulseMatrix Deme)) {n : ℕ}
    (hn : 6 ≤ n) (x0 : FrequencyState Deme Locus Allele) (deme : Deme) (inbreeding : Deme → ℝ)
    (hF0 : ∀ other, 0 ≤ inbreeding other) (hF1 : ∀ other, inbreeding other ≤ 1)
    (score outcome : FullHaplotype Locus Allele × FullHaplotype Locus Allele → ℝ) :
    expectedDiploidCalibrationIntercept (historyEventKernel ℓ₀ hap₀ events) x0 deme inbreeding
        hF0 hF1 score outcome
      = momentDiploidCalibrationIntercept ℓ₀ n deme inbreeding score outcome
          (historyEventPropagator (fun _ ↦ n) events *ᵥ budgetMomentFeature (fun _ ↦ n) x0) := by
  haveI := isMarkovKernel_historyEventKernel ℓ₀ hap₀ events
  exact expectedDiploidCalibrationIntercept_eq_moment ℓ₀ (historyEventKernel ℓ₀ hap₀ events) _
    (integral_momentPolynomial_historyEventKernel ℓ₀ hap₀ (fun _ ↦ n) events) hn x0 deme
    inbreeding hF0 hF1 score outcome

/-- **The diploid calibration slope of expectations along a rate history**, at every budget
`n ≥ 4`. -/
theorem expectedDiploidCalibrationSlope_rateHistoryKernel
    {rates : ℝ → NeutralRates Deme Locus Allele} {T : ℝ} (hT : 0 ≤ T)
    (hcontinuous : ∀ capacity : Locus → ℕ,
      ContinuousOn (fun t ↦ dualGenerator (rates t) capacity) (Set.Icc 0 T))
    (ℓ₀ : Locus) (hap₀ : FullHaplotype Locus Allele) {n : ℕ} (hn : 4 ≤ n)
    (x0 : FrequencyState Deme Locus Allele) (deme : Deme) (inbreeding : Deme → ℝ)
    (hF0 : ∀ other, 0 ≤ inbreeding other) (hF1 : ∀ other, inbreeding other ≤ 1)
    (score outcome : FullHaplotype Locus Allele × FullHaplotype Locus Allele → ℝ) :
    expectedDiploidCalibrationSlope (rateHistoryKernel rates ℓ₀ hap₀ hT hcontinuous) x0 deme
        inbreeding hF0 hF1 score outcome
      = momentDiploidCalibrationSlope ℓ₀ n deme inbreeding score outcome
          (rateHistoryDualPropagator rates (fun _ ↦ n) T
            *ᵥ budgetMomentFeature (fun _ ↦ n) x0) := by
  haveI := isMarkovKernel_rateHistoryKernel hT hcontinuous ℓ₀ hap₀
  exact expectedDiploidCalibrationSlope_eq_moment ℓ₀
    (rateHistoryKernel rates ℓ₀ hap₀ hT hcontinuous) _
    (integral_momentPolynomial_rateHistoryKernel hT hcontinuous ℓ₀ hap₀ (fun _ ↦ n)) hn x0 deme
    inbreeding hF0 hF1 score outcome

/-- **The diploid calibration portability of expectations along a rate history**, at every budget
`n ≥ 4`. -/
theorem expectedDiploidCalibrationPortability_rateHistoryKernel
    {rates : ℝ → NeutralRates Deme Locus Allele} {T : ℝ} (hT : 0 ≤ T)
    (hcontinuous : ∀ capacity : Locus → ℕ,
      ContinuousOn (fun t ↦ dualGenerator (rates t) capacity) (Set.Icc 0 T))
    (ℓ₀ : Locus) (hap₀ : FullHaplotype Locus Allele) {n : ℕ} (hn : 4 ≤ n)
    (x0 : FrequencyState Deme Locus Allele) (source target : Deme) (inbreeding : Deme → ℝ)
    (hF0 : ∀ other, 0 ≤ inbreeding other) (hF1 : ∀ other, inbreeding other ≤ 1)
    (score outcome : FullHaplotype Locus Allele × FullHaplotype Locus Allele → ℝ) :
    expectedDiploidCalibrationPortability (rateHistoryKernel rates ℓ₀ hap₀ hT hcontinuous) x0
        source target inbreeding hF0 hF1 score outcome
      = momentDiploidCalibrationPortability ℓ₀ n source target inbreeding score outcome
          (rateHistoryDualPropagator rates (fun _ ↦ n) T
            *ᵥ budgetMomentFeature (fun _ ↦ n) x0) := by
  haveI := isMarkovKernel_rateHistoryKernel hT hcontinuous ℓ₀ hap₀
  exact expectedDiploidCalibrationPortability_eq_moment ℓ₀
    (rateHistoryKernel rates ℓ₀ hap₀ hT hcontinuous) _
    (integral_momentPolynomial_rateHistoryKernel hT hcontinuous ℓ₀ hap₀ (fun _ ↦ n)) hn x0 source
    target inbreeding hF0 hF1 score outcome

/-- **The diploid calibration intercept of expectations along a rate history**, at every budget
`n ≥ 6`. -/
theorem expectedDiploidCalibrationIntercept_rateHistoryKernel
    {rates : ℝ → NeutralRates Deme Locus Allele} {T : ℝ} (hT : 0 ≤ T)
    (hcontinuous : ∀ capacity : Locus → ℕ,
      ContinuousOn (fun t ↦ dualGenerator (rates t) capacity) (Set.Icc 0 T))
    (ℓ₀ : Locus) (hap₀ : FullHaplotype Locus Allele) {n : ℕ} (hn : 6 ≤ n)
    (x0 : FrequencyState Deme Locus Allele) (deme : Deme) (inbreeding : Deme → ℝ)
    (hF0 : ∀ other, 0 ≤ inbreeding other) (hF1 : ∀ other, inbreeding other ≤ 1)
    (score outcome : FullHaplotype Locus Allele × FullHaplotype Locus Allele → ℝ) :
    expectedDiploidCalibrationIntercept (rateHistoryKernel rates ℓ₀ hap₀ hT hcontinuous) x0 deme
        inbreeding hF0 hF1 score outcome
      = momentDiploidCalibrationIntercept ℓ₀ n deme inbreeding score outcome
          (rateHistoryDualPropagator rates (fun _ ↦ n) T
            *ᵥ budgetMomentFeature (fun _ ↦ n) x0) := by
  haveI := isMarkovKernel_rateHistoryKernel hT hcontinuous ℓ₀ hap₀
  exact expectedDiploidCalibrationIntercept_eq_moment ℓ₀
    (rateHistoryKernel rates ℓ₀ hap₀ hT hcontinuous) _
    (integral_momentPolynomial_rateHistoryKernel hT hcontinuous ℓ₀ hap₀ (fun _ ↦ n)) hn x0 deme
    inbreeding hF0 hF1 score outcome

/-- **The diploid calibration slope sees the history only through finitely many moments.**  Two
histories, from two initial states, whose propagated budget-`n` moments agree, `n ≥ 4`, have equal
diploid calibration slope of expectations for every pair of gamete-pair observables. -/
theorem expectedDiploidCalibrationSlope_eq_of_moments_eq (ℓ₀ : Locus)
    (hap₀ : FullHaplotype Locus Allele)
    {first second : List ((NeutralRates Deme Locus Allele × ℝ≥0) ⊕ PulseMatrix Deme)}
    {x₁ x₂ : FrequencyState Deme Locus Allele} {n : ℕ} (hn : 4 ≤ n)
    (hmoments : historyEventPropagator (fun _ ↦ n) first *ᵥ budgetMomentFeature (fun _ ↦ n) x₁
      = historyEventPropagator (fun _ ↦ n) second *ᵥ budgetMomentFeature (fun _ ↦ n) x₂)
    (deme : Deme) (inbreeding : Deme → ℝ) (hF0 : ∀ other, 0 ≤ inbreeding other)
    (hF1 : ∀ other, inbreeding other ≤ 1)
    (score outcome : FullHaplotype Locus Allele × FullHaplotype Locus Allele → ℝ) :
    expectedDiploidCalibrationSlope (historyEventKernel ℓ₀ hap₀ first) x₁ deme inbreeding hF0 hF1
        score outcome
      = expectedDiploidCalibrationSlope (historyEventKernel ℓ₀ hap₀ second) x₂ deme inbreeding hF0
          hF1 score outcome := by
  rw [expectedDiploidCalibrationSlope_historyEventKernel ℓ₀ hap₀ first hn,
    expectedDiploidCalibrationSlope_historyEventKernel ℓ₀ hap₀ second hn, hmoments]

/-- **Diploid calibration portability sees the history only through finitely many moments**, at
every budget `n ≥ 4`. -/
theorem expectedDiploidCalibrationPortability_eq_of_moments_eq (ℓ₀ : Locus)
    (hap₀ : FullHaplotype Locus Allele)
    {first second : List ((NeutralRates Deme Locus Allele × ℝ≥0) ⊕ PulseMatrix Deme)}
    {x₁ x₂ : FrequencyState Deme Locus Allele} {n : ℕ} (hn : 4 ≤ n)
    (hmoments : historyEventPropagator (fun _ ↦ n) first *ᵥ budgetMomentFeature (fun _ ↦ n) x₁
      = historyEventPropagator (fun _ ↦ n) second *ᵥ budgetMomentFeature (fun _ ↦ n) x₂)
    (source target : Deme) (inbreeding : Deme → ℝ) (hF0 : ∀ other, 0 ≤ inbreeding other)
    (hF1 : ∀ other, inbreeding other ≤ 1)
    (score outcome : FullHaplotype Locus Allele × FullHaplotype Locus Allele → ℝ) :
    expectedDiploidCalibrationPortability (historyEventKernel ℓ₀ hap₀ first) x₁ source target
        inbreeding hF0 hF1 score outcome
      = expectedDiploidCalibrationPortability (historyEventKernel ℓ₀ hap₀ second) x₂ source target
          inbreeding hF0 hF1 score outcome := by
  rw [expectedDiploidCalibrationPortability_historyEventKernel ℓ₀ hap₀ first hn,
    expectedDiploidCalibrationPortability_historyEventKernel ℓ₀ hap₀ second hn, hmoments]

/-- **The diploid calibration intercept sees the history only through finitely many moments**, at
every budget `n ≥ 6`. -/
theorem expectedDiploidCalibrationIntercept_eq_of_moments_eq (ℓ₀ : Locus)
    (hap₀ : FullHaplotype Locus Allele)
    {first second : List ((NeutralRates Deme Locus Allele × ℝ≥0) ⊕ PulseMatrix Deme)}
    {x₁ x₂ : FrequencyState Deme Locus Allele} {n : ℕ} (hn : 6 ≤ n)
    (hmoments : historyEventPropagator (fun _ ↦ n) first *ᵥ budgetMomentFeature (fun _ ↦ n) x₁
      = historyEventPropagator (fun _ ↦ n) second *ᵥ budgetMomentFeature (fun _ ↦ n) x₂)
    (deme : Deme) (inbreeding : Deme → ℝ) (hF0 : ∀ other, 0 ≤ inbreeding other)
    (hF1 : ∀ other, inbreeding other ≤ 1)
    (score outcome : FullHaplotype Locus Allele × FullHaplotype Locus Allele → ℝ) :
    expectedDiploidCalibrationIntercept (historyEventKernel ℓ₀ hap₀ first) x₁ deme inbreeding
        hF0 hF1 score outcome
      = expectedDiploidCalibrationIntercept (historyEventKernel ℓ₀ hap₀ second) x₂ deme inbreeding
          hF0 hF1 score outcome := by
  rw [expectedDiploidCalibrationIntercept_historyEventKernel ℓ₀ hap₀ first hn,
    expectedDiploidCalibrationIntercept_historyEventKernel ℓ₀ hap₀ second hn, hmoments]

/-- **The two budgets agree on the additive slope.**  For additive score and outcome, the budget-4
diploid slope function of the budget-4 moments of a history equals the haploid budget-2 slope
function of its budget-2 moments, whatever the inbreeding coefficients. -/
theorem momentDiploidCalibrationSlope_diploidSum_historyEventKernel (ℓ₀ : Locus)
    (hap₀ : FullHaplotype Locus Allele)
    (events : List ((NeutralRates Deme Locus Allele × ℝ≥0) ⊕ PulseMatrix Deme))
    (x0 : FrequencyState Deme Locus Allele) (deme : Deme) (inbreeding : Deme → ℝ)
    (hF0 : ∀ other, 0 ≤ inbreeding other) (hF1 : ∀ other, inbreeding other ≤ 1)
    (score outcome : FullHaplotype Locus Allele → ℝ) :
    momentDiploidCalibrationSlope ℓ₀ 4 deme inbreeding (diploidSum score) (diploidSum outcome)
        (historyEventPropagator (fun _ ↦ 4) events *ᵥ budgetMomentFeature (fun _ ↦ 4) x0)
      = momentCalibrationSlope ℓ₀ 2 deme score outcome
          (historyEventPropagator (fun _ ↦ 2) events *ᵥ budgetMomentFeature (fun _ ↦ 2) x0) := by
  rw [← expectedDiploidCalibrationSlope_historyEventKernel ℓ₀ hap₀ events le_rfl x0 deme
    inbreeding hF0 hF1, expectedDiploidCalibrationSlope_diploidSum_historyEventKernel ℓ₀ hap₀ events
    le_rfl]

/-- **The two budgets agree on the additive intercept.**  For additive score and outcome, the
budget-6 diploid intercept function of the budget-6 moments of a history is twice the haploid
budget-3 intercept function of its budget-3 moments. -/
theorem momentDiploidCalibrationIntercept_diploidSum_historyEventKernel (ℓ₀ : Locus)
    (hap₀ : FullHaplotype Locus Allele)
    (events : List ((NeutralRates Deme Locus Allele × ℝ≥0) ⊕ PulseMatrix Deme))
    (x0 : FrequencyState Deme Locus Allele) (deme : Deme) (inbreeding : Deme → ℝ)
    (hF0 : ∀ other, 0 ≤ inbreeding other) (hF1 : ∀ other, inbreeding other ≤ 1)
    (score outcome : FullHaplotype Locus Allele → ℝ) :
    momentDiploidCalibrationIntercept ℓ₀ 6 deme inbreeding (diploidSum score) (diploidSum outcome)
        (historyEventPropagator (fun _ ↦ 6) events *ᵥ budgetMomentFeature (fun _ ↦ 6) x0)
      = 2 * momentCalibrationIntercept ℓ₀ 3 deme score outcome
          (historyEventPropagator (fun _ ↦ 3) events *ᵥ budgetMomentFeature (fun _ ↦ 3) x0) := by
  rw [← expectedDiploidCalibrationIntercept_historyEventKernel ℓ₀ hap₀ events le_rfl x0 deme
    inbreeding hF0 hF1,
    expectedDiploidCalibrationIntercept_diploidSum_historyEventKernel ℓ₀ hap₀ events le_rfl]

end History

/-! ## Dominance breaks the transfer of calibration -/

section Dominance

/-- **The gamete pair at one fair site.**  At allele frequency one half an observable of the pair
integrates through its four cells: independent draws with weight `1 - F`, and the two autozygous
cells with weight `F`. -/
theorem expectation_inbredMating_fairSwitch (F : ℝ) (hF0 : 0 ≤ F) (hF1 : F ≤ 1)
    (φ : Bool × Bool → ℝ) :
    (inbredMating MeiosisGameteLaw.fairSwitch F hF0 hF1).expectation φ
      = (1 - F) * ((φ (true, true) + φ (true, false) + φ (false, true) + φ (false, false)) / 4)
        + F * ((φ (true, true) + φ (false, false)) / 2) := by
  simp only [expectation_inbredMating, expectation_fairSwitch]
  ring

/-- **The recessive outcome regressed on the additive score at one site.**  At allele frequency
one half the diploid calibration slope is `1 / 2` for every inbreeding coefficient, and the
intercept `E Y - (1 / 2) E S` is `(F - 1) / 4`. -/
theorem calibrationSlope_inbredMating_diploidProduct (F : ℝ) (hF0 : 0 ≤ F) (hF1 : F ≤ 1) :
    (inbredMating MeiosisGameteLaw.fairSwitch F hF0 hF1).calibrationSlope
        (diploidSum ChronologyReportLaw.alleleValue)
        (diploidProduct ChronologyReportLaw.alleleValue) = some (1 / 2)
      ∧ (inbredMating MeiosisGameteLaw.fairSwitch F hF0 hF1).expectation
          (diploidProduct ChronologyReportLaw.alleleValue)
        - 1 / 2 * (inbredMating MeiosisGameteLaw.fairSwitch F hF0 hF1).expectation
          (diploidSum ChronologyReportLaw.alleleValue) = (F - 1) / 4 := by
  have hmean : (inbredMating MeiosisGameteLaw.fairSwitch F hF0 hF1).expectation
      (diploidSum ChronologyReportLaw.alleleValue) = 1 := by
    rw [expectation_inbredMating_diploidSum, expectation_fairSwitch]
    norm_num
  have hsquare : (inbredMating MeiosisGameteLaw.fairSwitch F hF0 hF1).expectation
      (fun pair ↦ diploidSum ChronologyReportLaw.alleleValue pair ^ 2) = (3 + F) / 2 := by
    simp only [expectation_inbredMating_fairSwitch, diploidSum,
      ChronologyReportLaw.alleleValue_true, ChronologyReportLaw.alleleValue_false]
    ring
  have houtcome : (inbredMating MeiosisGameteLaw.fairSwitch F hF0 hF1).expectation
      (diploidProduct ChronologyReportLaw.alleleValue) = (1 + F) / 4 := by
    simp only [expectation_inbredMating_fairSwitch, diploidProduct,
      ChronologyReportLaw.alleleValue_true, ChronologyReportLaw.alleleValue_false]
    ring
  have hproduct : (inbredMating MeiosisGameteLaw.fairSwitch F hF0 hF1).expectation
      (fun pair ↦ diploidSum ChronologyReportLaw.alleleValue pair
        * diploidProduct ChronologyReportLaw.alleleValue pair) = (1 + F) / 2 := by
    simp only [expectation_inbredMating_fairSwitch, diploidSum, diploidProduct,
      ChronologyReportLaw.alleleValue_true, ChronologyReportLaw.alleleValue_false]
    ring
  have hpositive : 0 < (inbredMating MeiosisGameteLaw.fairSwitch F hF0 hF1).expectation
        (fun pair ↦ diploidSum ChronologyReportLaw.alleleValue pair ^ 2)
      - (inbredMating MeiosisGameteLaw.fairSwitch F hF0 hF1).expectation
        (diploidSum ChronologyReportLaw.alleleValue) ^ 2 := by
    rw [hsquare, hmean]
    linarith
  refine ⟨?_, ?_⟩
  · rw [FiniteReportLaw.calibrationSlope_eq_rawMoments _ _ _ hpositive, hproduct, hmean, houtcome,
      hsquare]
    congr 1
    rw [div_eq_div_iff (by linarith : (0 : ℝ) < (3 + F) / 2 - 1 ^ 2).ne'
      (by norm_num : (2 : ℝ) ≠ 0)]
    ring
  · rw [houtcome, hmean]
    ring

/-- At the fair switch the allele regressed on itself in one haplotype has calibration slope
one. -/
theorem calibrationSlope_fairSwitch_alleleValue :
    MeiosisGameteLaw.fairSwitch.calibrationSlope ChronologyReportLaw.alleleValue
      ChronologyReportLaw.alleleValue = some 1 := by
  have hvariance : 0 < MeiosisGameteLaw.fairSwitch.variance ChronologyReportLaw.alleleValue := by
    simp only [FiniteReportLaw.variance_eq_rawMoments, expectation_fairSwitch,
      ChronologyReportLaw.alleleValue_true, ChronologyReportLaw.alleleValue_false]
    norm_num
  rw [FiniteReportLaw.calibrationSlope, if_pos hvariance]
  congr 1
  exact div_self hvariance.ne'

/-- **Dominance breaks the ploidy transfer of calibration.**  For the recessive outcome the diploid
calibration slope under random union is not the haploid slope of the allele on itself, although
additive lifts keep the haploid slope.  The intercept `E Y - (1 / 2) E S` under random union also
differs from the one under full autozygosity, although for additive lifts the intercept is twice
the haploid one whatever the inbreeding coefficient. -/
theorem diploidProduct_breaks_calibration_transfer :
    (FiniteReproductiveKernel.independentMating MeiosisGameteLaw.fairSwitch).calibrationSlope
        (diploidSum ChronologyReportLaw.alleleValue)
        (diploidProduct ChronologyReportLaw.alleleValue)
      ≠ MeiosisGameteLaw.fairSwitch.calibrationSlope ChronologyReportLaw.alleleValue
        ChronologyReportLaw.alleleValue ∧
    (inbredMating MeiosisGameteLaw.fairSwitch 0 le_rfl zero_le_one).expectation
        (diploidProduct ChronologyReportLaw.alleleValue)
      - 1 / 2 * (inbredMating MeiosisGameteLaw.fairSwitch 0 le_rfl zero_le_one).expectation
        (diploidSum ChronologyReportLaw.alleleValue)
      ≠ (inbredMating MeiosisGameteLaw.fairSwitch 1 zero_le_one le_rfl).expectation
          (diploidProduct ChronologyReportLaw.alleleValue)
        - 1 / 2 * (inbredMating MeiosisGameteLaw.fairSwitch 1 zero_le_one le_rfl).expectation
          (diploidSum ChronologyReportLaw.alleleValue) := by
  refine ⟨?_, ?_⟩
  · rw [← inbredMating_zero, (calibrationSlope_inbredMating_diploidProduct 0 le_rfl zero_le_one).1,
      calibrationSlope_fairSwitch_alleleValue]
    norm_num
  · rw [(calibrationSlope_inbredMating_diploidProduct 0 le_rfl zero_le_one).2,
      (calibrationSlope_inbredMating_diploidProduct 1 zero_le_one le_rfl).2]
    norm_num

end Dominance

end

end Descent.Portability.EndToEndDiploidCalibration
