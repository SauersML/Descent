/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.EndToEndPortabilityLaw
import Descent.Portability.PositiveRatioExpansion

assert_below Descent.Decision Descent.Program

/-!
# The expected squared correlation of a score along a demographic history

`EndToEndPortabilityLaw` computes the expected numerator `E N` and denominator `E D` of the
population squared correlation `r² = N / D` of NOTE2 (21) from finitely many propagated moments,
and notes that the expected squared correlation `E[N / D]` itself is not a rational function of
finitely many moments.  This module computes it exactly, as a convergent series of such
computations.

The pointwise expansion.  For a score and an outcome in the unit interval, `0 ≤ N ≤ D ≤ 1`, and
the squared correlation read as zero where it is undefined is the zero-extended ratio
(`getD_squaredCorrelation_stateLaw`).  So NOTE2 (15) applies under every Markov kernel: the
expected squared correlation is `Σₖ E[N (1 - D)ᵏ]` (`expectedSquaredCorrelation_eq_tsum`), by
`PositiveRatioExpansion.integral_ratioOnDefined_eq_tsum`.

The terms.  `N (1 - D)ᵏ` is a frequency polynomial of total degree at most `4 (k + 1)`
(`seriesTermPolynomial`, `polynomialFunction_seriesTermPolynomial`,
`totalDegree_seriesTermPolynomial_le`), so under a history kernel its expectation is its
coefficient vector dotted with the propagator applied to the budget-`4 (k + 1)` configuration
moments of `x₀` (`integral_seriesTerm_historyEventKernel`, `integral_seriesTerm_rateHistoryKernel`).

The law.  The expected squared correlation along a history of epochs, splits and pulses, or along
a rate history with continuous dual generator, is `Σₖ cₖ ⬝ (U_{4(k+1)} · H_{4(k+1)}(x₀))`
(`expectedSquaredCorrelation_historyEventKernel`, `expectedSquaredCorrelation_rateHistoryKernel`),
and two histories whose propagated moments agree at every budget `4 (k + 1)` have equal expected
squared correlation (`expectedSquaredCorrelation_eq_of_moments_eq`).

Scope.  The score and the outcome take values in the unit interval.  Truncation certificates for
the series, NOTE2 Theorem 4, are not restated here.

## Empirical status

None.  The bodies here are a pointwise geometric series, polynomial identities and integrals of
polynomials against Markov kernels, so no measurement can bear on them.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.EndToEndCorrelationSeries

open MeasureTheory ProbabilityTheory MvPolynomial Descent.Coalescent PartialHaplotypeCarrier
  PartialHaplotypeDualGenerator PartialHaplotypeDualSemigroup NeutralFellerGenerator
  NeutralPolynomialSemigroup PartialHaplotypeMicroscopicApproximation PartialHaplotypePulseKernel
  NeutralPulseHistoryKernel NeutralRateHistoryRealization NeutralRateHistoryKernel
  ReplicaMetricInstances PositiveRatioExpansion EndToEndPortabilityLaw
open scoped Matrix NNReal

noncomputable section

variable {Deme Locus : Type*} {Allele : Locus → Type*}
variable [Fintype Deme] [DecidableEq Deme] [Fintype Locus] [DecidableEq Locus]
  [∀ ℓ, Fintype (Allele ℓ)] [∀ ℓ, DecidableEq (Allele ℓ)]

/-! ## The series terms as frequency polynomials -/

/-- The `k`-th term `N (1 - D)ᵏ` of NOTE2 (15) for the squared correlation of one deme, as a
frequency polynomial. -/
def seriesTermPolynomial (deme : Deme) (score outcome : FullHaplotype Locus Allele → ℝ)
    (k : ℕ) : FrequencyPolynomial Deme Locus Allele :=
  numeratorPolynomial deme score outcome * (1 - denominatorPolynomial deme score outcome) ^ k

/-- At a state, the `k`-th series polynomial is `N (1 - D)ᵏ` of the deme's haplotype law. -/
theorem polynomialFunction_seriesTermPolynomial (deme : Deme)
    (score outcome : FullHaplotype Locus Allele → ℝ) (k : ℕ)
    (y : FrequencyState Deme Locus Allele) :
    polynomialFunction (seriesTermPolynomial deme score outcome k) y
      = correlationNumerator (stateLaw y deme) score outcome
        * (1 - correlationDenominator (stateLaw y deme) score outcome) ^ k := by
  rw [polynomialFunction_apply, seriesTermPolynomial, map_mul, map_pow, map_sub, map_one,
    ← polynomialFunction_apply, ← polynomialFunction_apply,
    polynomialFunction_numeratorPolynomial, polynomialFunction_denominatorPolynomial]

/-- The `k`-th series polynomial has total degree at most `4 (k + 1)`. -/
theorem totalDegree_seriesTermPolynomial_le (deme : Deme)
    (score outcome : FullHaplotype Locus Allele → ℝ) (k : ℕ) :
    (seriesTermPolynomial deme score outcome k).totalDegree ≤ 4 * (k + 1) := by
  have hnumerator := totalDegree_numeratorPolynomial_le deme score outcome
  have hdenominator := totalDegree_denominatorPolynomial_le deme score outcome
  have hdeficit : (1 - denominatorPolynomial deme score outcome).totalDegree ≤ 4 :=
    (totalDegree_sub _ _).trans (max_le (by rw [totalDegree_one]; omega) hdenominator)
  have hpower : ((1 - denominatorPolynomial deme score outcome) ^ k).totalDegree ≤ k * 4 :=
    (totalDegree_pow _ k).trans (Nat.mul_le_mul_left k hdeficit)
  exact (totalDegree_mul _ _).trans (by omega)

/-! ## The pointwise expansion -/

/-- **Expected squared correlation**: the population squared correlation of a deme, read as zero
where it is undefined, averaged under a kernel started at `x₀`. -/
def expectedSquaredCorrelation
    (κ : Kernel (FrequencyState Deme Locus Allele) (FrequencyState Deme Locus Allele))
    (x0 : FrequencyState Deme Locus Allele) (deme : Deme)
    (score outcome : FullHaplotype Locus Allele → ℝ) : ℝ :=
  ∫ y, ((stateLaw y deme).squaredCorrelation score outcome).getD 0 ∂(κ x0)

/-- The squared correlation of a deme, read as zero where it is undefined, is the zero-extended
ratio of the correlation numerator and denominator. -/
theorem getD_squaredCorrelation_stateLaw (deme : Deme)
    (score outcome : FullHaplotype Locus Allele → ℝ) (y : FrequencyState Deme Locus Allele) :
    ((stateLaw y deme).squaredCorrelation score outcome).getD 0
      = ratioOnDefined (fun z : FrequencyState Deme Locus Allele ↦
          correlationNumerator (stateLaw z deme) score outcome)
        (fun z ↦ correlationDenominator (stateLaw z deme) score outcome) y := by
  rw [squaredCorrelation_eq_guardedRatio]
  show _ = if 0 < correlationDenominator (stateLaw y deme) score outcome then
      correlationNumerator (stateLaw y deme) score outcome
        / correlationDenominator (stateLaw y deme) score outcome
    else 0
  split_ifs <;> rfl

/-- The correlation numerator of a deme is a measurable function of the state. -/
theorem measurable_correlationNumerator (deme : Deme)
    (score outcome : FullHaplotype Locus Allele → ℝ) :
    Measurable fun y : FrequencyState Deme Locus Allele ↦
      correlationNumerator (stateLaw y deme) score outcome := by
  have hfunction : (fun y : FrequencyState Deme Locus Allele ↦
        correlationNumerator (stateLaw y deme) score outcome)
      = ⇑(polynomialFunction (numeratorPolynomial deme score outcome)) :=
    funext fun y ↦ (polynomialFunction_numeratorPolynomial deme score outcome y).symm
  rw [hfunction]
  exact (polynomialFunction (numeratorPolynomial deme score outcome)).continuous.measurable

/-- The correlation denominator of a deme is a measurable function of the state. -/
theorem measurable_correlationDenominator (deme : Deme)
    (score outcome : FullHaplotype Locus Allele → ℝ) :
    Measurable fun y : FrequencyState Deme Locus Allele ↦
      correlationDenominator (stateLaw y deme) score outcome := by
  have hfunction : (fun y : FrequencyState Deme Locus Allele ↦
        correlationDenominator (stateLaw y deme) score outcome)
      = ⇑(polynomialFunction (denominatorPolynomial deme score outcome)) :=
    funext fun y ↦ (polynomialFunction_denominatorPolynomial deme score outcome y).symm
  rw [hfunction]
  exact (polynomialFunction (denominatorPolynomial deme score outcome)).continuous.measurable

/-- **NOTE2 (15) under a Markov kernel.**  For a score and an outcome in the unit interval, the
expected squared correlation of a deme is the series of expectations of `N (1 - D)ᵏ`. -/
theorem expectedSquaredCorrelation_eq_tsum
    (κ : Kernel (FrequencyState Deme Locus Allele) (FrequencyState Deme Locus Allele))
    [IsMarkovKernel κ] (x0 : FrequencyState Deme Locus Allele) (deme : Deme)
    (score outcome : FullHaplotype Locus Allele → ℝ)
    (hscore0 : ∀ hap, 0 ≤ score hap) (hscore1 : ∀ hap, score hap ≤ 1)
    (houtcome0 : ∀ hap, 0 ≤ outcome hap) (houtcome1 : ∀ hap, outcome hap ≤ 1) :
    expectedSquaredCorrelation κ x0 deme score outcome
      = ∑' k : ℕ, ∫ y, correlationNumerator (stateLaw y deme) score outcome
          * (1 - correlationDenominator (stateLaw y deme) score outcome) ^ k ∂(κ x0) := by
  simp only [expectedSquaredCorrelation, getD_squaredCorrelation_stateLaw]
  exact integral_ratioOnDefined_eq_tsum (κ x0) _ _
    (measurable_correlationNumerator deme score outcome)
    (measurable_correlationDenominator deme score outcome)
    (fun y ↦ correlationNumerator_nonneg _ score outcome)
    (fun y ↦ correlationNumerator_le_denominator _ score outcome)
    (fun y ↦ correlationDenominator_le_one _ score outcome hscore0 hscore1 houtcome0 houtcome1)

/-! ## The law along a history -/

/-- **The series terms along a history of epochs, splits and pulses.** -/
theorem integral_seriesTerm_historyEventKernel (ℓ₀ : Locus) (hap₀ : FullHaplotype Locus Allele)
    (events : List ((NeutralRates Deme Locus Allele × ℝ≥0) ⊕ PulseMatrix Deme))
    (x0 : FrequencyState Deme Locus Allele) (deme : Deme)
    (score outcome : FullHaplotype Locus Allele → ℝ) (k : ℕ) :
    ∫ y, correlationNumerator (stateLaw y deme) score outcome
        * (1 - correlationDenominator (stateLaw y deme) score outcome) ^ k
        ∂(historyEventKernel ℓ₀ hap₀ events x0)
      = budgetCoefficients ℓ₀ (fun _ ↦ 4 * (k + 1)) (seriesTermPolynomial deme score outcome k)
        ⬝ᵥ (historyEventPropagator (fun _ ↦ 4 * (k + 1)) events
          *ᵥ budgetMomentFeature (fun _ ↦ 4 * (k + 1)) x0) := by
  haveI := isMarkovKernel_historyEventKernel ℓ₀ hap₀ events
  have h := integral_polynomial_eq_dotProduct ℓ₀ (fun _ ↦ 4 * (k + 1))
    (historyEventKernel ℓ₀ hap₀ events) (historyEventPropagator (fun _ ↦ 4 * (k + 1)) events)
    (integral_momentPolynomial_historyEventKernel ℓ₀ hap₀ (fun _ ↦ 4 * (k + 1)) events)
    (seriesTermPolynomial deme score outcome k)
    (withinBudget_of_totalDegree_le ℓ₀ _ (totalDegree_seriesTermPolynomial_le deme score outcome k))
    x0
  simp only [polynomialFunction_seriesTermPolynomial] at h
  exact h

/-- **The expected squared correlation along a history of epochs, splits and pulses.**  For a
score and an outcome in the unit interval it is the series over `k` of the coefficient vectors of
`N (1 - D)ᵏ` dotted with the chronological propagator applied to the budget-`4 (k + 1)`
configuration moments of the initial state. -/
theorem expectedSquaredCorrelation_historyEventKernel (ℓ₀ : Locus)
    (hap₀ : FullHaplotype Locus Allele)
    (events : List ((NeutralRates Deme Locus Allele × ℝ≥0) ⊕ PulseMatrix Deme))
    (x0 : FrequencyState Deme Locus Allele) (deme : Deme)
    (score outcome : FullHaplotype Locus Allele → ℝ)
    (hscore0 : ∀ hap, 0 ≤ score hap) (hscore1 : ∀ hap, score hap ≤ 1)
    (houtcome0 : ∀ hap, 0 ≤ outcome hap) (houtcome1 : ∀ hap, outcome hap ≤ 1) :
    expectedSquaredCorrelation (historyEventKernel ℓ₀ hap₀ events) x0 deme score outcome
      = ∑' k : ℕ, budgetCoefficients ℓ₀ (fun _ ↦ 4 * (k + 1))
          (seriesTermPolynomial deme score outcome k)
        ⬝ᵥ (historyEventPropagator (fun _ ↦ 4 * (k + 1)) events
          *ᵥ budgetMomentFeature (fun _ ↦ 4 * (k + 1)) x0) := by
  haveI := isMarkovKernel_historyEventKernel ℓ₀ hap₀ events
  rw [expectedSquaredCorrelation_eq_tsum _ x0 deme score outcome hscore0 hscore1 houtcome0
    houtcome1]
  exact tsum_congr fun k ↦
    integral_seriesTerm_historyEventKernel ℓ₀ hap₀ events x0 deme score outcome k

/-- **The expected squared correlation sees the history only through propagated moments.**  Two
histories, from two initial states, whose propagated configuration moments agree at every budget
`4 (k + 1)` have equal expected squared correlation for every score and outcome in the unit
interval. -/
theorem expectedSquaredCorrelation_eq_of_moments_eq (ℓ₀ : Locus)
    (hap₀ : FullHaplotype Locus Allele)
    {first second : List ((NeutralRates Deme Locus Allele × ℝ≥0) ⊕ PulseMatrix Deme)}
    {x₁ x₂ : FrequencyState Deme Locus Allele}
    (hmoments : ∀ k : ℕ,
      historyEventPropagator (fun _ ↦ 4 * (k + 1)) first
          *ᵥ budgetMomentFeature (fun _ ↦ 4 * (k + 1)) x₁
        = historyEventPropagator (fun _ ↦ 4 * (k + 1)) second
          *ᵥ budgetMomentFeature (fun _ ↦ 4 * (k + 1)) x₂)
    (deme : Deme) (score outcome : FullHaplotype Locus Allele → ℝ)
    (hscore0 : ∀ hap, 0 ≤ score hap) (hscore1 : ∀ hap, score hap ≤ 1)
    (houtcome0 : ∀ hap, 0 ≤ outcome hap) (houtcome1 : ∀ hap, outcome hap ≤ 1) :
    expectedSquaredCorrelation (historyEventKernel ℓ₀ hap₀ first) x₁ deme score outcome
      = expectedSquaredCorrelation (historyEventKernel ℓ₀ hap₀ second) x₂ deme score outcome := by
  rw [expectedSquaredCorrelation_historyEventKernel ℓ₀ hap₀ first x₁ deme score outcome hscore0
      hscore1 houtcome0 houtcome1,
    expectedSquaredCorrelation_historyEventKernel ℓ₀ hap₀ second x₂ deme score outcome hscore0
      hscore1 houtcome0 houtcome1]
  exact tsum_congr fun k ↦ by rw [hmoments k]

/-! ## The law along a time-varying rate history -/

/-- **The series terms along a rate history.** -/
theorem integral_seriesTerm_rateHistoryKernel {rates : ℝ → NeutralRates Deme Locus Allele}
    {T : ℝ} (hT : 0 ≤ T)
    (hcontinuous : ∀ capacity : Locus → ℕ,
      ContinuousOn (fun t ↦ dualGenerator (rates t) capacity) (Set.Icc 0 T))
    (ℓ₀ : Locus) (hap₀ : FullHaplotype Locus Allele) (x0 : FrequencyState Deme Locus Allele)
    (deme : Deme) (score outcome : FullHaplotype Locus Allele → ℝ) (k : ℕ) :
    ∫ y, correlationNumerator (stateLaw y deme) score outcome
        * (1 - correlationDenominator (stateLaw y deme) score outcome) ^ k
        ∂(rateHistoryKernel rates ℓ₀ hap₀ hT hcontinuous x0)
      = budgetCoefficients ℓ₀ (fun _ ↦ 4 * (k + 1)) (seriesTermPolynomial deme score outcome k)
        ⬝ᵥ (rateHistoryDualPropagator rates (fun _ ↦ 4 * (k + 1)) T
          *ᵥ budgetMomentFeature (fun _ ↦ 4 * (k + 1)) x0) := by
  haveI := isMarkovKernel_rateHistoryKernel hT hcontinuous ℓ₀ hap₀
  have h := integral_polynomial_eq_dotProduct ℓ₀ (fun _ ↦ 4 * (k + 1))
    (rateHistoryKernel rates ℓ₀ hap₀ hT hcontinuous)
    (rateHistoryDualPropagator rates (fun _ ↦ 4 * (k + 1)) T)
    (integral_momentPolynomial_rateHistoryKernel hT hcontinuous ℓ₀ hap₀ (fun _ ↦ 4 * (k + 1)))
    (seriesTermPolynomial deme score outcome k)
    (withinBudget_of_totalDegree_le ℓ₀ _ (totalDegree_seriesTermPolynomial_le deme score outcome k))
    x0
  simp only [polynomialFunction_seriesTermPolynomial] at h
  exact h

/-- **The expected squared correlation along a time-varying rate history.** -/
theorem expectedSquaredCorrelation_rateHistoryKernel {rates : ℝ → NeutralRates Deme Locus Allele}
    {T : ℝ} (hT : 0 ≤ T)
    (hcontinuous : ∀ capacity : Locus → ℕ,
      ContinuousOn (fun t ↦ dualGenerator (rates t) capacity) (Set.Icc 0 T))
    (ℓ₀ : Locus) (hap₀ : FullHaplotype Locus Allele) (x0 : FrequencyState Deme Locus Allele)
    (deme : Deme) (score outcome : FullHaplotype Locus Allele → ℝ)
    (hscore0 : ∀ hap, 0 ≤ score hap) (hscore1 : ∀ hap, score hap ≤ 1)
    (houtcome0 : ∀ hap, 0 ≤ outcome hap) (houtcome1 : ∀ hap, outcome hap ≤ 1) :
    expectedSquaredCorrelation (rateHistoryKernel rates ℓ₀ hap₀ hT hcontinuous) x0 deme score
        outcome
      = ∑' k : ℕ, budgetCoefficients ℓ₀ (fun _ ↦ 4 * (k + 1))
          (seriesTermPolynomial deme score outcome k)
        ⬝ᵥ (rateHistoryDualPropagator rates (fun _ ↦ 4 * (k + 1)) T
          *ᵥ budgetMomentFeature (fun _ ↦ 4 * (k + 1)) x0) := by
  haveI := isMarkovKernel_rateHistoryKernel hT hcontinuous ℓ₀ hap₀
  rw [expectedSquaredCorrelation_eq_tsum _ x0 deme score outcome hscore0 hscore1 houtcome0
    houtcome1]
  exact tsum_congr fun k ↦
    integral_seriesTerm_rateHistoryKernel hT hcontinuous ℓ₀ hap₀ x0 deme score outcome k

end

end Descent.Portability.EndToEndCorrelationSeries
