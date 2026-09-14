/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.TwoTimeRatePropagator

assert_below Descent.Decision Descent.Program

/-!
# The exact sensitivity of calibration and AUC portability along time-varying rate histories

`EndToEndSensitivityRatePath` differentiates the propagator of a segment of two continuous rate
histories, `t ↦ rateSegment (first t) (second t) θ`, and with it the portability of expected
accuracies.  `EndToEndSensitivityRates` differentiates calibration and AUC portability only along
histories of segment epochs.  This module differentiates the calibration and AUC metrics along a
segment of rate histories.

Expectations.  Along the segment, each of the following expectations is a pairing with the
propagator of the segment:
- the expected score–outcome covariance and score variance of a deme, at every budget `n ≥ 2`;
- the expected intercept accumulator `E[μ_Y V_S - C_SY μ_S]`, at every budget `n ≥ 3`
  (`integral_interceptNumerator_rateHistoryKernel`);
- the expected AUC numerator and denominator, at budget 2
  (`integral_aucNumerator_rateHistoryKernel`, `integral_aucDenominator_rateHistoryKernel`).
So each has as derivative its coefficient vector paired with the sensitivity matrix
`ratePathSensitivity` applied to the initial moments (`hasDerivAt_integral_covariance_rateSegment`,
`hasDerivAt_integral_variance_rateSegment`, `hasDerivAt_integral_interceptNumerator_rateSegment`,
`hasDerivAt_integral_aucNumerator_rateSegment`, `hasDerivAt_integral_aucDenominator_rateSegment`).

The metrics.  The calibration slope and the calibration intercept of expectations have the
quotient-rule derivative wherever the expected score variance is nonzero
(`hasDerivAt_expectedCalibrationSlope_rateSegment`,
`hasDerivAt_expectedCalibrationIntercept_rateSegment`).  Calibration and AUC portability have the
cross-ratio derivative of `EndToEndSensitivityMetrics` wherever their denominators are nonzero
(`hasDerivAt_expectedCalibrationPortability_rateSegment`,
`hasDerivAt_expectedAUCPortability_rateSegment`).  None of these needs a differentiability
hypothesis.

The Duhamel form.  `TwoTimeRatePropagator.ratePathSensitivity_eq_integral` writes the sensitivity
matrix as `∫₀ᵀ U_θ₀(T, s) (Q_second - Q_first)(s) U_θ₀(s, 0) ds` (`duhamelSensitivity`,
`ratePathSensitivity_eq_duhamelSensitivity`).  Every metric derivative above therefore holds with
that integral in place of the block form (`hasDerivAt_expectedCalibrationSlope_rateSegment_duhamel`,
`hasDerivAt_expectedCalibrationPortability_rateSegment_duhamel`,
`hasDerivAt_expectedCalibrationIntercept_rateSegment_duhamel`,
`hasDerivAt_expectedAUCPortability_rateSegment_duhamel`).

The sign criterion.  With positive expectations at `θ₀`, calibration portability decreases along
the segment exactly when the relative sensitivity of the target calibration, `C_t'/C_t - V_t'/V_t`,
is below that of the source, `C_s'/C_s - V_s'/V_s`
(`deriv_expectedCalibrationPortability_rateSegment_neg_iff`).  AUC portability decreases exactly
when `N_t'/N_t - D_t'/D_t < N_s'/N_s - D_s'/D_s`
(`deriv_expectedAUCPortability_rateSegment_neg_iff`).  Both follow from
`EndToEndSensitivityMetrics.crossRatioDerivative_neg_iff_of_pos`.

Significance.  Demographic rates that change continuously in time, such as a growing population
or a gradually strengthening migration, are covered for every ratio-of-expectations metric of the
corpus, not only for the squared correlation.  The integral form says which times contribute: a
rate change at time `s` acts on the moments propagated from `0` to `s` and is carried from `s` to
`T` by the two-time propagator.

Scope.  The rate histories have continuous dual generators, as the kernel of
`NeutralRateHistoryKernel` requires.  The derivatives are two-sided at interior parameters; at the
endpoints of the segment the clamp makes them one-sided, which is not stated.  The metrics are
ratios of expectations; the expected AUC itself, a series, is not differentiated here.  The
positivity and nonvanishing hypotheses are conditions on the expectations at `θ₀`.

## Empirical status

None.  The bodies here are derivatives of pairings of coefficient vectors with the propagator of a
segment of rate histories and quotient rules for them, so no measurement can bear on them.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.EndToEndSensitivityRatePathMetrics

open MeasureTheory ProbabilityTheory MvPolynomial Descent.Coalescent PartialHaplotypeCarrier
  PartialHaplotypeDualGenerator PartialHaplotypeDualSemigroup NeutralFellerGenerator
  NeutralPolynomialSemigroup PartialHaplotypeMicroscopicApproximation PartialHaplotypePulseKernel
  NeutralPulseHistoryKernel ReplicaMetricInstances LinearFundamentalMatrix NeutralRateLipschitz
  NeutralRateHistoryRealization NeutralRateHistoryKernel EndToEndPortabilityLaw
  EndToEndCalibrationLaw EndToEndDiscriminationLaw EndToEndSensitivityMetrics
  EndToEndSensitivityRates EndToEndSensitivityRatePath TwoTimeRatePropagator
open scoped Matrix NNReal

noncomputable section

variable {Deme Locus : Type*} {Allele : Locus → Type*}
variable [Fintype Deme] [DecidableEq Deme] [Fintype Locus] [DecidableEq Locus]
  [∀ ℓ, Fintype (Allele ℓ)] [∀ ℓ, DecidableEq (Allele ℓ)]

/-! ## Propagated expectations along a rate history -/

/-- **The expected intercept accumulator along a rate history**, at every budget `n ≥ 3`. -/
theorem integral_interceptNumerator_rateHistoryKernel {rates : ℝ → NeutralRates Deme Locus Allele}
    {T : ℝ} (hT : 0 ≤ T)
    (hcontinuous : ∀ capacity : Locus → ℕ,
      ContinuousOn (fun t ↦ dualGenerator (rates t) capacity) (Set.Icc 0 T))
    (ℓ₀ : Locus) (hap₀ : FullHaplotype Locus Allele) {n : ℕ} (hn : 3 ≤ n)
    (x0 : FrequencyState Deme Locus Allele) (deme : Deme)
    (score outcome : FullHaplotype Locus Allele → ℝ) :
    ∫ y, ((stateLaw y deme).expectation outcome * (stateLaw y deme).variance score
        - (stateLaw y deme).covariance score outcome * (stateLaw y deme).expectation score)
        ∂(rateHistoryKernel rates ℓ₀ hap₀ hT hcontinuous x0)
      = budgetCoefficients ℓ₀ (fun _ ↦ n) (interceptNumeratorPolynomial deme score outcome)
        ⬝ᵥ (rateHistoryDualPropagator rates (fun _ ↦ n) T
          *ᵥ budgetMomentFeature (fun _ ↦ n) x0) := by
  haveI := isMarkovKernel_rateHistoryKernel hT hcontinuous ℓ₀ hap₀
  exact integral_eq_dotProduct_of_totalDegree_le ℓ₀
    (rateHistoryKernel rates ℓ₀ hap₀ hT hcontinuous) _
    (integral_momentPolynomial_rateHistoryKernel hT hcontinuous ℓ₀ hap₀ (fun _ ↦ n)) _
    ((totalDegree_interceptNumeratorPolynomial_le deme score outcome).trans hn) _
    (polynomialFunction_interceptNumeratorPolynomial deme score outcome) x0

/-- **The expected AUC numerator along a rate history.** -/
theorem integral_aucNumerator_rateHistoryKernel {rates : ℝ → NeutralRates Deme Locus Allele}
    {T : ℝ} (hT : 0 ≤ T)
    (hcontinuous : ∀ capacity : Locus → ℕ,
      ContinuousOn (fun t ↦ dualGenerator (rates t) capacity) (Set.Icc 0 T))
    (ℓ₀ : Locus) (hap₀ : FullHaplotype Locus Allele) (x0 : FrequencyState Deme Locus Allele)
    (deme : Deme) (score : FullHaplotype Locus Allele → ℝ)
    (outcome : FullHaplotype Locus Allele → Bool) :
    ∫ y, aucNumerator (stateLaw y deme) score outcome
        ∂(rateHistoryKernel rates ℓ₀ hap₀ hT hcontinuous x0)
      = budgetCoefficients ℓ₀ (fun _ ↦ 2)
          (demePolynomial deme (aucNumeratorPolynomial score outcome))
        ⬝ᵥ (rateHistoryDualPropagator rates (fun _ ↦ 2) T
          *ᵥ budgetMomentFeature (fun _ ↦ 2) x0) := by
  haveI := isMarkovKernel_rateHistoryKernel hT hcontinuous ℓ₀ hap₀
  exact integral_aucNumerator_eq_dotProduct ℓ₀ _ _
    (hasDualMoments_rateHistoryKernel hT hcontinuous ℓ₀ hap₀ 2) x0 deme score outcome

/-- **The expected AUC denominator along a rate history.** -/
theorem integral_aucDenominator_rateHistoryKernel {rates : ℝ → NeutralRates Deme Locus Allele}
    {T : ℝ} (hT : 0 ≤ T)
    (hcontinuous : ∀ capacity : Locus → ℕ,
      ContinuousOn (fun t ↦ dualGenerator (rates t) capacity) (Set.Icc 0 T))
    (ℓ₀ : Locus) (hap₀ : FullHaplotype Locus Allele) (x0 : FrequencyState Deme Locus Allele)
    (deme : Deme) (outcome : FullHaplotype Locus Allele → Bool) :
    ∫ y, aucDenominator (stateLaw y deme) outcome
        ∂(rateHistoryKernel rates ℓ₀ hap₀ hT hcontinuous x0)
      = budgetCoefficients ℓ₀ (fun _ ↦ 2) (demePolynomial deme (aucDenominatorPolynomial outcome))
        ⬝ᵥ (rateHistoryDualPropagator rates (fun _ ↦ 2) T
          *ᵥ budgetMomentFeature (fun _ ↦ 2) x0) := by
  haveI := isMarkovKernel_rateHistoryKernel hT hcontinuous ℓ₀ hap₀
  exact integral_aucDenominator_eq_dotProduct ℓ₀ _ _
    (hasDualMoments_rateHistoryKernel hT hcontinuous ℓ₀ hap₀ 2) x0 deme outcome

/-! ## Expectations along a segment of rate histories -/

/-- **The kernel of a segment of rate histories** at parameter `θ`: the kernel of the rate history
`t ↦ rateSegment (first t) (second t) θ`, whose dual generators are continuous by
`EndToEndSensitivityRatePath.continuousOn_dualGenerator_rateSegment`. -/
def segmentKernel {first second : ℝ → NeutralRates Deme Locus Allele} {T : ℝ} (hT : 0 ≤ T)
    (hfirst : ∀ capacity : Locus → ℕ,
      ContinuousOn (fun t ↦ dualGenerator (first t) capacity) (Set.Icc 0 T))
    (hsecond : ∀ capacity : Locus → ℕ,
      ContinuousOn (fun t ↦ dualGenerator (second t) capacity) (Set.Icc 0 T))
    (ℓ₀ : Locus) (hap₀ : FullHaplotype Locus Allele) (θ : ℝ) :
    Kernel (FrequencyState Deme Locus Allele) (FrequencyState Deme Locus Allele) :=
  rateHistoryKernel (fun t ↦ rateSegment (first t) (second t) θ) ℓ₀ hap₀ hT
    (continuousOn_dualGenerator_rateSegment hfirst hsecond θ)

/-- **The sensitivity of an expected deme covariance along a segment of rate histories**, at every
budget `n ≥ 2`. -/
theorem hasDerivAt_integral_covariance_rateSegment
    {first second : ℝ → NeutralRates Deme Locus Allele} {T : ℝ} (hT : 0 ≤ T)
    (hfirst : ∀ capacity : Locus → ℕ,
      ContinuousOn (fun t ↦ dualGenerator (first t) capacity) (Set.Icc 0 T))
    (hsecond : ∀ capacity : Locus → ℕ,
      ContinuousOn (fun t ↦ dualGenerator (second t) capacity) (Set.Icc 0 T))
    (ℓ₀ : Locus) (hap₀ : FullHaplotype Locus Allele) {n : ℕ} (hn : 2 ≤ n)
    (x0 : FrequencyState Deme Locus Allele) (deme : Deme)
    (score outcome : FullHaplotype Locus Allele → ℝ) {θ₀ : ℝ} (hθ₀ : θ₀ ∈ Set.Ioo (0 : ℝ) 1) :
    HasDerivAt (fun θ ↦ ∫ y, (stateLaw y deme).covariance score outcome
        ∂(segmentKernel hT hfirst hsecond ℓ₀ hap₀ θ x0))
      (budgetCoefficients ℓ₀ (fun _ ↦ n) (demeCovariancePolynomial deme score outcome)
        ⬝ᵥ (ratePathSensitivity first second (fun _ ↦ n) T θ₀
          *ᵥ budgetMomentFeature (fun _ ↦ n) x0)) θ₀ :=
  hasDerivAt_of_eq_dotProduct_rateSegment hT (hfirst _) (hsecond _) hθ₀ _ _ fun θ ↦
    integral_covariance_rateHistoryKernel hT
      (continuousOn_dualGenerator_rateSegment hfirst hsecond θ) ℓ₀ hap₀ hn x0 deme score outcome

/-- **The sensitivity of an expected deme score variance along a segment of rate histories**, at
every budget `n ≥ 2`. -/
theorem hasDerivAt_integral_variance_rateSegment
    {first second : ℝ → NeutralRates Deme Locus Allele} {T : ℝ} (hT : 0 ≤ T)
    (hfirst : ∀ capacity : Locus → ℕ,
      ContinuousOn (fun t ↦ dualGenerator (first t) capacity) (Set.Icc 0 T))
    (hsecond : ∀ capacity : Locus → ℕ,
      ContinuousOn (fun t ↦ dualGenerator (second t) capacity) (Set.Icc 0 T))
    (ℓ₀ : Locus) (hap₀ : FullHaplotype Locus Allele) {n : ℕ} (hn : 2 ≤ n)
    (x0 : FrequencyState Deme Locus Allele) (deme : Deme)
    (score : FullHaplotype Locus Allele → ℝ) {θ₀ : ℝ} (hθ₀ : θ₀ ∈ Set.Ioo (0 : ℝ) 1) :
    HasDerivAt (fun θ ↦ ∫ y, (stateLaw y deme).variance score
        ∂(segmentKernel hT hfirst hsecond ℓ₀ hap₀ θ x0))
      (budgetCoefficients ℓ₀ (fun _ ↦ n) (demeCovariancePolynomial deme score score)
        ⬝ᵥ (ratePathSensitivity first second (fun _ ↦ n) T θ₀
          *ᵥ budgetMomentFeature (fun _ ↦ n) x0)) θ₀ :=
  hasDerivAt_of_eq_dotProduct_rateSegment hT (hfirst _) (hsecond _) hθ₀ _ _ fun θ ↦
    integral_variance_rateHistoryKernel hT
      (continuousOn_dualGenerator_rateSegment hfirst hsecond θ) ℓ₀ hap₀ hn x0 deme score

/-- **The sensitivity of the expected intercept accumulator along a segment of rate histories**, at
every budget `n ≥ 3`. -/
theorem hasDerivAt_integral_interceptNumerator_rateSegment
    {first second : ℝ → NeutralRates Deme Locus Allele} {T : ℝ} (hT : 0 ≤ T)
    (hfirst : ∀ capacity : Locus → ℕ,
      ContinuousOn (fun t ↦ dualGenerator (first t) capacity) (Set.Icc 0 T))
    (hsecond : ∀ capacity : Locus → ℕ,
      ContinuousOn (fun t ↦ dualGenerator (second t) capacity) (Set.Icc 0 T))
    (ℓ₀ : Locus) (hap₀ : FullHaplotype Locus Allele) {n : ℕ} (hn : 3 ≤ n)
    (x0 : FrequencyState Deme Locus Allele) (deme : Deme)
    (score outcome : FullHaplotype Locus Allele → ℝ) {θ₀ : ℝ} (hθ₀ : θ₀ ∈ Set.Ioo (0 : ℝ) 1) :
    HasDerivAt (fun θ ↦ ∫ y,
        ((stateLaw y deme).expectation outcome * (stateLaw y deme).variance score
          - (stateLaw y deme).covariance score outcome * (stateLaw y deme).expectation score)
        ∂(segmentKernel hT hfirst hsecond ℓ₀ hap₀ θ x0))
      (budgetCoefficients ℓ₀ (fun _ ↦ n) (interceptNumeratorPolynomial deme score outcome)
        ⬝ᵥ (ratePathSensitivity first second (fun _ ↦ n) T θ₀
          *ᵥ budgetMomentFeature (fun _ ↦ n) x0)) θ₀ :=
  hasDerivAt_of_eq_dotProduct_rateSegment hT (hfirst _) (hsecond _) hθ₀ _ _ fun θ ↦
    integral_interceptNumerator_rateHistoryKernel hT
      (continuousOn_dualGenerator_rateSegment hfirst hsecond θ) ℓ₀ hap₀ hn x0 deme score outcome

/-- **The sensitivity of the expected AUC numerator along a segment of rate histories.** -/
theorem hasDerivAt_integral_aucNumerator_rateSegment
    {first second : ℝ → NeutralRates Deme Locus Allele} {T : ℝ} (hT : 0 ≤ T)
    (hfirst : ∀ capacity : Locus → ℕ,
      ContinuousOn (fun t ↦ dualGenerator (first t) capacity) (Set.Icc 0 T))
    (hsecond : ∀ capacity : Locus → ℕ,
      ContinuousOn (fun t ↦ dualGenerator (second t) capacity) (Set.Icc 0 T))
    (ℓ₀ : Locus) (hap₀ : FullHaplotype Locus Allele) (x0 : FrequencyState Deme Locus Allele)
    (deme : Deme) (score : FullHaplotype Locus Allele → ℝ)
    (outcome : FullHaplotype Locus Allele → Bool) {θ₀ : ℝ} (hθ₀ : θ₀ ∈ Set.Ioo (0 : ℝ) 1) :
    HasDerivAt (fun θ ↦ ∫ y, aucNumerator (stateLaw y deme) score outcome
        ∂(segmentKernel hT hfirst hsecond ℓ₀ hap₀ θ x0))
      (budgetCoefficients ℓ₀ (fun _ ↦ 2)
          (demePolynomial deme (aucNumeratorPolynomial score outcome))
        ⬝ᵥ (ratePathSensitivity first second (fun _ ↦ 2) T θ₀
          *ᵥ budgetMomentFeature (fun _ ↦ 2) x0)) θ₀ :=
  hasDerivAt_of_eq_dotProduct_rateSegment hT (hfirst _) (hsecond _) hθ₀ _ _ fun θ ↦
    integral_aucNumerator_rateHistoryKernel hT
      (continuousOn_dualGenerator_rateSegment hfirst hsecond θ) ℓ₀ hap₀ x0 deme score outcome

/-- **The sensitivity of the expected AUC denominator along a segment of rate histories.** -/
theorem hasDerivAt_integral_aucDenominator_rateSegment
    {first second : ℝ → NeutralRates Deme Locus Allele} {T : ℝ} (hT : 0 ≤ T)
    (hfirst : ∀ capacity : Locus → ℕ,
      ContinuousOn (fun t ↦ dualGenerator (first t) capacity) (Set.Icc 0 T))
    (hsecond : ∀ capacity : Locus → ℕ,
      ContinuousOn (fun t ↦ dualGenerator (second t) capacity) (Set.Icc 0 T))
    (ℓ₀ : Locus) (hap₀ : FullHaplotype Locus Allele) (x0 : FrequencyState Deme Locus Allele)
    (deme : Deme) (outcome : FullHaplotype Locus Allele → Bool) {θ₀ : ℝ}
    (hθ₀ : θ₀ ∈ Set.Ioo (0 : ℝ) 1) :
    HasDerivAt (fun θ ↦ ∫ y, aucDenominator (stateLaw y deme) outcome
        ∂(segmentKernel hT hfirst hsecond ℓ₀ hap₀ θ x0))
      (budgetCoefficients ℓ₀ (fun _ ↦ 2) (demePolynomial deme (aucDenominatorPolynomial outcome))
        ⬝ᵥ (ratePathSensitivity first second (fun _ ↦ 2) T θ₀
          *ᵥ budgetMomentFeature (fun _ ↦ 2) x0)) θ₀ :=
  hasDerivAt_of_eq_dotProduct_rateSegment hT (hfirst _) (hsecond _) hθ₀ _ _ fun θ ↦
    integral_aucDenominator_rateHistoryKernel hT
      (continuousOn_dualGenerator_rateSegment hfirst hsecond θ) ℓ₀ hap₀ x0 deme outcome

/-! ## The metrics along a segment of rate histories -/

/-- **The sensitivity of the calibration slope of expectations along a segment of rate
histories**, at every budget `n ≥ 2`, wherever the expected score variance is nonzero. -/
theorem hasDerivAt_expectedCalibrationSlope_rateSegment
    {first second : ℝ → NeutralRates Deme Locus Allele} {T : ℝ} (hT : 0 ≤ T)
    (hfirst : ∀ capacity : Locus → ℕ,
      ContinuousOn (fun t ↦ dualGenerator (first t) capacity) (Set.Icc 0 T))
    (hsecond : ∀ capacity : Locus → ℕ,
      ContinuousOn (fun t ↦ dualGenerator (second t) capacity) (Set.Icc 0 T))
    (ℓ₀ : Locus) (hap₀ : FullHaplotype Locus Allele) {n : ℕ} (hn : 2 ≤ n)
    (x0 : FrequencyState Deme Locus Allele) (deme : Deme)
    (score outcome : FullHaplotype Locus Allele → ℝ) {θ₀ : ℝ} (hθ₀ : θ₀ ∈ Set.Ioo (0 : ℝ) 1)
    (hvariance : ∫ y, (stateLaw y deme).variance score
      ∂(segmentKernel hT hfirst hsecond ℓ₀ hap₀ θ₀ x0) ≠ 0) :
    HasDerivAt (fun θ ↦ expectedCalibrationSlope (segmentKernel hT hfirst hsecond ℓ₀ hap₀ θ) x0
        deme score outcome)
      ((budgetCoefficients ℓ₀ (fun _ ↦ n) (demeCovariancePolynomial deme score outcome)
            ⬝ᵥ (ratePathSensitivity first second (fun _ ↦ n) T θ₀
              *ᵥ budgetMomentFeature (fun _ ↦ n) x0)
          * (∫ y, (stateLaw y deme).variance score
            ∂(segmentKernel hT hfirst hsecond ℓ₀ hap₀ θ₀ x0))
        - (∫ y, (stateLaw y deme).covariance score outcome
            ∂(segmentKernel hT hfirst hsecond ℓ₀ hap₀ θ₀ x0))
          * budgetCoefficients ℓ₀ (fun _ ↦ n) (demeCovariancePolynomial deme score score)
            ⬝ᵥ (ratePathSensitivity first second (fun _ ↦ n) T θ₀
              *ᵥ budgetMomentFeature (fun _ ↦ n) x0))
        / (∫ y, (stateLaw y deme).variance score
            ∂(segmentKernel hT hfirst hsecond ℓ₀ hap₀ θ₀ x0)) ^ 2) θ₀ :=
  (hasDerivAt_integral_covariance_rateSegment hT hfirst hsecond ℓ₀ hap₀ hn x0 deme score outcome
    hθ₀).fun_div
    (hasDerivAt_integral_variance_rateSegment hT hfirst hsecond ℓ₀ hap₀ hn x0 deme score hθ₀)
    hvariance

/-- **The sensitivity of calibration portability along a segment of rate histories**
`E C_t E V_s / (E V_t E C_s)`, at every budget `n ≥ 2`, wherever `E V_t E C_s ≠ 0`. -/
theorem hasDerivAt_expectedCalibrationPortability_rateSegment
    {first second : ℝ → NeutralRates Deme Locus Allele} {T : ℝ} (hT : 0 ≤ T)
    (hfirst : ∀ capacity : Locus → ℕ,
      ContinuousOn (fun t ↦ dualGenerator (first t) capacity) (Set.Icc 0 T))
    (hsecond : ∀ capacity : Locus → ℕ,
      ContinuousOn (fun t ↦ dualGenerator (second t) capacity) (Set.Icc 0 T))
    (ℓ₀ : Locus) (hap₀ : FullHaplotype Locus Allele) {n : ℕ} (hn : 2 ≤ n)
    (x0 : FrequencyState Deme Locus Allele) (source target : Deme)
    (score outcome : FullHaplotype Locus Allele → ℝ) {θ₀ : ℝ} (hθ₀ : θ₀ ∈ Set.Ioo (0 : ℝ) 1)
    (hdenominator : (∫ y, (stateLaw y target).variance score
          ∂(segmentKernel hT hfirst hsecond ℓ₀ hap₀ θ₀ x0))
        * (∫ y, (stateLaw y source).covariance score outcome
          ∂(segmentKernel hT hfirst hsecond ℓ₀ hap₀ θ₀ x0)) ≠ 0) :
    HasDerivAt (fun θ ↦ expectedCalibrationPortability
        (segmentKernel hT hfirst hsecond ℓ₀ hap₀ θ) x0 source target score outcome)
      (crossRatioDerivative
        (∫ y, (stateLaw y target).covariance score outcome
          ∂(segmentKernel hT hfirst hsecond ℓ₀ hap₀ θ₀ x0))
        (∫ y, (stateLaw y source).variance score
          ∂(segmentKernel hT hfirst hsecond ℓ₀ hap₀ θ₀ x0))
        (∫ y, (stateLaw y target).variance score
          ∂(segmentKernel hT hfirst hsecond ℓ₀ hap₀ θ₀ x0))
        (∫ y, (stateLaw y source).covariance score outcome
          ∂(segmentKernel hT hfirst hsecond ℓ₀ hap₀ θ₀ x0))
        (budgetCoefficients ℓ₀ (fun _ ↦ n) (demeCovariancePolynomial target score outcome)
          ⬝ᵥ (ratePathSensitivity first second (fun _ ↦ n) T θ₀
            *ᵥ budgetMomentFeature (fun _ ↦ n) x0))
        (budgetCoefficients ℓ₀ (fun _ ↦ n) (demeCovariancePolynomial source score score)
          ⬝ᵥ (ratePathSensitivity first second (fun _ ↦ n) T θ₀
            *ᵥ budgetMomentFeature (fun _ ↦ n) x0))
        (budgetCoefficients ℓ₀ (fun _ ↦ n) (demeCovariancePolynomial target score score)
          ⬝ᵥ (ratePathSensitivity first second (fun _ ↦ n) T θ₀
            *ᵥ budgetMomentFeature (fun _ ↦ n) x0))
        (budgetCoefficients ℓ₀ (fun _ ↦ n) (demeCovariancePolynomial source score outcome)
          ⬝ᵥ (ratePathSensitivity first second (fun _ ↦ n) T θ₀
            *ᵥ budgetMomentFeature (fun _ ↦ n) x0))) θ₀ :=
  (hasDerivAt_crossRatio
    (hasDerivAt_integral_covariance_rateSegment hT hfirst hsecond ℓ₀ hap₀ hn x0 target score
      outcome hθ₀)
    (hasDerivAt_integral_variance_rateSegment hT hfirst hsecond ℓ₀ hap₀ hn x0 source score hθ₀)
    (hasDerivAt_integral_variance_rateSegment hT hfirst hsecond ℓ₀ hap₀ hn x0 target score hθ₀)
    (hasDerivAt_integral_covariance_rateSegment hT hfirst hsecond ℓ₀ hap₀ hn x0 source score
      outcome hθ₀)
    hdenominator).congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun _ ↦
      expectedCalibrationPortability_eq_cross _ x0 source target score outcome)

/-- **The sensitivity of the calibration intercept of expectations along a segment of rate
histories**, at every budget `n ≥ 3`, wherever the expected score variance is nonzero. -/
theorem hasDerivAt_expectedCalibrationIntercept_rateSegment
    {first second : ℝ → NeutralRates Deme Locus Allele} {T : ℝ} (hT : 0 ≤ T)
    (hfirst : ∀ capacity : Locus → ℕ,
      ContinuousOn (fun t ↦ dualGenerator (first t) capacity) (Set.Icc 0 T))
    (hsecond : ∀ capacity : Locus → ℕ,
      ContinuousOn (fun t ↦ dualGenerator (second t) capacity) (Set.Icc 0 T))
    (ℓ₀ : Locus) (hap₀ : FullHaplotype Locus Allele) {n : ℕ} (hn : 3 ≤ n)
    (x0 : FrequencyState Deme Locus Allele) (deme : Deme)
    (score outcome : FullHaplotype Locus Allele → ℝ) {θ₀ : ℝ} (hθ₀ : θ₀ ∈ Set.Ioo (0 : ℝ) 1)
    (hvariance : ∫ y, (stateLaw y deme).variance score
      ∂(segmentKernel hT hfirst hsecond ℓ₀ hap₀ θ₀ x0) ≠ 0) :
    HasDerivAt (fun θ ↦ expectedCalibrationIntercept (segmentKernel hT hfirst hsecond ℓ₀ hap₀ θ)
        x0 deme score outcome)
      ((budgetCoefficients ℓ₀ (fun _ ↦ n) (interceptNumeratorPolynomial deme score outcome)
            ⬝ᵥ (ratePathSensitivity first second (fun _ ↦ n) T θ₀
              *ᵥ budgetMomentFeature (fun _ ↦ n) x0)
          * (∫ y, (stateLaw y deme).variance score
            ∂(segmentKernel hT hfirst hsecond ℓ₀ hap₀ θ₀ x0))
        - (∫ y, ((stateLaw y deme).expectation outcome * (stateLaw y deme).variance score
              - (stateLaw y deme).covariance score outcome * (stateLaw y deme).expectation score)
            ∂(segmentKernel hT hfirst hsecond ℓ₀ hap₀ θ₀ x0))
          * budgetCoefficients ℓ₀ (fun _ ↦ n) (demeCovariancePolynomial deme score score)
            ⬝ᵥ (ratePathSensitivity first second (fun _ ↦ n) T θ₀
              *ᵥ budgetMomentFeature (fun _ ↦ n) x0))
        / (∫ y, (stateLaw y deme).variance score
            ∂(segmentKernel hT hfirst hsecond ℓ₀ hap₀ θ₀ x0)) ^ 2) θ₀ :=
  (hasDerivAt_integral_interceptNumerator_rateSegment hT hfirst hsecond ℓ₀ hap₀ hn x0 deme score
    outcome hθ₀).fun_div
    (hasDerivAt_integral_variance_rateSegment (n := n) hT hfirst hsecond ℓ₀ hap₀ (by omega) x0
      deme score hθ₀)
    hvariance

/-- **The sensitivity of AUC portability along a segment of rate histories**
`E N_t E D_s / (E D_t E N_s)` of the AUC components, wherever `E D_t E N_s ≠ 0`. -/
theorem hasDerivAt_expectedAUCPortability_rateSegment
    {first second : ℝ → NeutralRates Deme Locus Allele} {T : ℝ} (hT : 0 ≤ T)
    (hfirst : ∀ capacity : Locus → ℕ,
      ContinuousOn (fun t ↦ dualGenerator (first t) capacity) (Set.Icc 0 T))
    (hsecond : ∀ capacity : Locus → ℕ,
      ContinuousOn (fun t ↦ dualGenerator (second t) capacity) (Set.Icc 0 T))
    (ℓ₀ : Locus) (hap₀ : FullHaplotype Locus Allele) (x0 : FrequencyState Deme Locus Allele)
    (source target : Deme) (score : FullHaplotype Locus Allele → ℝ)
    (outcome : FullHaplotype Locus Allele → Bool) {θ₀ : ℝ} (hθ₀ : θ₀ ∈ Set.Ioo (0 : ℝ) 1)
    (hdenominator : (∫ y, aucDenominator (stateLaw y target) outcome
          ∂(segmentKernel hT hfirst hsecond ℓ₀ hap₀ θ₀ x0))
        * (∫ y, aucNumerator (stateLaw y source) score outcome
          ∂(segmentKernel hT hfirst hsecond ℓ₀ hap₀ θ₀ x0)) ≠ 0) :
    HasDerivAt (fun θ ↦ expectedAUCPortability (segmentKernel hT hfirst hsecond ℓ₀ hap₀ θ) x0
        source target score outcome)
      (crossRatioDerivative
        (∫ y, aucNumerator (stateLaw y target) score outcome
          ∂(segmentKernel hT hfirst hsecond ℓ₀ hap₀ θ₀ x0))
        (∫ y, aucDenominator (stateLaw y source) outcome
          ∂(segmentKernel hT hfirst hsecond ℓ₀ hap₀ θ₀ x0))
        (∫ y, aucDenominator (stateLaw y target) outcome
          ∂(segmentKernel hT hfirst hsecond ℓ₀ hap₀ θ₀ x0))
        (∫ y, aucNumerator (stateLaw y source) score outcome
          ∂(segmentKernel hT hfirst hsecond ℓ₀ hap₀ θ₀ x0))
        (budgetCoefficients ℓ₀ (fun _ ↦ 2)
            (demePolynomial target (aucNumeratorPolynomial score outcome))
          ⬝ᵥ (ratePathSensitivity first second (fun _ ↦ 2) T θ₀
            *ᵥ budgetMomentFeature (fun _ ↦ 2) x0))
        (budgetCoefficients ℓ₀ (fun _ ↦ 2)
            (demePolynomial source (aucDenominatorPolynomial outcome))
          ⬝ᵥ (ratePathSensitivity first second (fun _ ↦ 2) T θ₀
            *ᵥ budgetMomentFeature (fun _ ↦ 2) x0))
        (budgetCoefficients ℓ₀ (fun _ ↦ 2)
            (demePolynomial target (aucDenominatorPolynomial outcome))
          ⬝ᵥ (ratePathSensitivity first second (fun _ ↦ 2) T θ₀
            *ᵥ budgetMomentFeature (fun _ ↦ 2) x0))
        (budgetCoefficients ℓ₀ (fun _ ↦ 2)
            (demePolynomial source (aucNumeratorPolynomial score outcome))
          ⬝ᵥ (ratePathSensitivity first second (fun _ ↦ 2) T θ₀
            *ᵥ budgetMomentFeature (fun _ ↦ 2) x0))) θ₀ :=
  hasDerivAt_crossRatio
    (hasDerivAt_integral_aucNumerator_rateSegment hT hfirst hsecond ℓ₀ hap₀ x0 target score
      outcome hθ₀)
    (hasDerivAt_integral_aucDenominator_rateSegment hT hfirst hsecond ℓ₀ hap₀ x0 source outcome
      hθ₀)
    (hasDerivAt_integral_aucDenominator_rateSegment hT hfirst hsecond ℓ₀ hap₀ x0 target outcome
      hθ₀)
    (hasDerivAt_integral_aucNumerator_rateSegment hT hfirst hsecond ℓ₀ hap₀ x0 source score
      outcome hθ₀)
    hdenominator

/-! ## The Duhamel form -/

section Duhamel

open scoped Matrix.Norms.Operator

/-- **The Duhamel sensitivity matrix of a segment of rate histories** at `θ₀`:
`∫₀ᵀ U_θ₀(T, s) (Q_second - Q_first)(s) U_θ₀(s, 0) ds`, with `U_θ₀` the two-time propagator of the
dual generator path `Q_first + θ₀ (Q_second - Q_first)` of the segment. -/
def duhamelSensitivity (first second : ℝ → NeutralRates Deme Locus Allele)
    (capacity : Locus → ℕ) (T θ₀ : ℝ) :
    Matrix (BudgetConfiguration Deme Locus Allele capacity)
      (BudgetConfiguration Deme Locus Allele capacity) ℝ :=
  ∫ s in (0 : ℝ)..T, twoTimePropagator (fun s ↦ dualGeneratorPath first capacity T s
      + θ₀ • (dualGeneratorPath second capacity T s - dualGeneratorPath first capacity T s))
      T T s
    * (dualGeneratorPath second capacity T s - dualGeneratorPath first capacity T s)
    * twoTimePropagator (fun s ↦ dualGeneratorPath first capacity T s
      + θ₀ • (dualGeneratorPath second capacity T s - dualGeneratorPath first capacity T s))
      T s 0

end Duhamel

/-- **The sensitivity matrix of a segment of rate histories is its Duhamel integral.** -/
theorem ratePathSensitivity_eq_duhamelSensitivity
    {first second : ℝ → NeutralRates Deme Locus Allele} {capacity : Locus → ℕ} {T : ℝ}
    (hT : 0 ≤ T)
    (hfirst : ContinuousOn (fun t ↦ dualGenerator (first t) capacity) (Set.Icc 0 T))
    (hsecond : ContinuousOn (fun t ↦ dualGenerator (second t) capacity) (Set.Icc 0 T))
    (θ₀ : ℝ) :
    ratePathSensitivity first second capacity T θ₀
      = duhamelSensitivity first second capacity T θ₀ :=
  ratePathSensitivity_eq_integral hT hfirst hsecond θ₀

/-- **The calibration slope along a segment of rate histories, in Duhamel form.** -/
theorem hasDerivAt_expectedCalibrationSlope_rateSegment_duhamel
    {first second : ℝ → NeutralRates Deme Locus Allele} {T : ℝ} (hT : 0 ≤ T)
    (hfirst : ∀ capacity : Locus → ℕ,
      ContinuousOn (fun t ↦ dualGenerator (first t) capacity) (Set.Icc 0 T))
    (hsecond : ∀ capacity : Locus → ℕ,
      ContinuousOn (fun t ↦ dualGenerator (second t) capacity) (Set.Icc 0 T))
    (ℓ₀ : Locus) (hap₀ : FullHaplotype Locus Allele) {n : ℕ} (hn : 2 ≤ n)
    (x0 : FrequencyState Deme Locus Allele) (deme : Deme)
    (score outcome : FullHaplotype Locus Allele → ℝ) {θ₀ : ℝ} (hθ₀ : θ₀ ∈ Set.Ioo (0 : ℝ) 1)
    (hvariance : ∫ y, (stateLaw y deme).variance score
      ∂(segmentKernel hT hfirst hsecond ℓ₀ hap₀ θ₀ x0) ≠ 0) :
    HasDerivAt (fun θ ↦ expectedCalibrationSlope (segmentKernel hT hfirst hsecond ℓ₀ hap₀ θ) x0
        deme score outcome)
      ((budgetCoefficients ℓ₀ (fun _ ↦ n) (demeCovariancePolynomial deme score outcome)
            ⬝ᵥ (duhamelSensitivity first second (fun _ ↦ n) T θ₀
              *ᵥ budgetMomentFeature (fun _ ↦ n) x0)
          * (∫ y, (stateLaw y deme).variance score
            ∂(segmentKernel hT hfirst hsecond ℓ₀ hap₀ θ₀ x0))
        - (∫ y, (stateLaw y deme).covariance score outcome
            ∂(segmentKernel hT hfirst hsecond ℓ₀ hap₀ θ₀ x0))
          * budgetCoefficients ℓ₀ (fun _ ↦ n) (demeCovariancePolynomial deme score score)
            ⬝ᵥ (duhamelSensitivity first second (fun _ ↦ n) T θ₀
              *ᵥ budgetMomentFeature (fun _ ↦ n) x0))
        / (∫ y, (stateLaw y deme).variance score
            ∂(segmentKernel hT hfirst hsecond ℓ₀ hap₀ θ₀ x0)) ^ 2) θ₀ := by
  rw [← ratePathSensitivity_eq_duhamelSensitivity hT (hfirst (fun _ ↦ n)) (hsecond (fun _ ↦ n))]
  exact hasDerivAt_expectedCalibrationSlope_rateSegment hT hfirst hsecond ℓ₀ hap₀ hn x0 deme score
    outcome hθ₀ hvariance

/-- **Calibration portability along a segment of rate histories, in Duhamel form.** -/
theorem hasDerivAt_expectedCalibrationPortability_rateSegment_duhamel
    {first second : ℝ → NeutralRates Deme Locus Allele} {T : ℝ} (hT : 0 ≤ T)
    (hfirst : ∀ capacity : Locus → ℕ,
      ContinuousOn (fun t ↦ dualGenerator (first t) capacity) (Set.Icc 0 T))
    (hsecond : ∀ capacity : Locus → ℕ,
      ContinuousOn (fun t ↦ dualGenerator (second t) capacity) (Set.Icc 0 T))
    (ℓ₀ : Locus) (hap₀ : FullHaplotype Locus Allele) {n : ℕ} (hn : 2 ≤ n)
    (x0 : FrequencyState Deme Locus Allele) (source target : Deme)
    (score outcome : FullHaplotype Locus Allele → ℝ) {θ₀ : ℝ} (hθ₀ : θ₀ ∈ Set.Ioo (0 : ℝ) 1)
    (hdenominator : (∫ y, (stateLaw y target).variance score
          ∂(segmentKernel hT hfirst hsecond ℓ₀ hap₀ θ₀ x0))
        * (∫ y, (stateLaw y source).covariance score outcome
          ∂(segmentKernel hT hfirst hsecond ℓ₀ hap₀ θ₀ x0)) ≠ 0) :
    HasDerivAt (fun θ ↦ expectedCalibrationPortability
        (segmentKernel hT hfirst hsecond ℓ₀ hap₀ θ) x0 source target score outcome)
      (crossRatioDerivative
        (∫ y, (stateLaw y target).covariance score outcome
          ∂(segmentKernel hT hfirst hsecond ℓ₀ hap₀ θ₀ x0))
        (∫ y, (stateLaw y source).variance score
          ∂(segmentKernel hT hfirst hsecond ℓ₀ hap₀ θ₀ x0))
        (∫ y, (stateLaw y target).variance score
          ∂(segmentKernel hT hfirst hsecond ℓ₀ hap₀ θ₀ x0))
        (∫ y, (stateLaw y source).covariance score outcome
          ∂(segmentKernel hT hfirst hsecond ℓ₀ hap₀ θ₀ x0))
        (budgetCoefficients ℓ₀ (fun _ ↦ n) (demeCovariancePolynomial target score outcome)
          ⬝ᵥ (duhamelSensitivity first second (fun _ ↦ n) T θ₀
            *ᵥ budgetMomentFeature (fun _ ↦ n) x0))
        (budgetCoefficients ℓ₀ (fun _ ↦ n) (demeCovariancePolynomial source score score)
          ⬝ᵥ (duhamelSensitivity first second (fun _ ↦ n) T θ₀
            *ᵥ budgetMomentFeature (fun _ ↦ n) x0))
        (budgetCoefficients ℓ₀ (fun _ ↦ n) (demeCovariancePolynomial target score score)
          ⬝ᵥ (duhamelSensitivity first second (fun _ ↦ n) T θ₀
            *ᵥ budgetMomentFeature (fun _ ↦ n) x0))
        (budgetCoefficients ℓ₀ (fun _ ↦ n) (demeCovariancePolynomial source score outcome)
          ⬝ᵥ (duhamelSensitivity first second (fun _ ↦ n) T θ₀
            *ᵥ budgetMomentFeature (fun _ ↦ n) x0))) θ₀ := by
  rw [← ratePathSensitivity_eq_duhamelSensitivity hT (hfirst (fun _ ↦ n)) (hsecond (fun _ ↦ n))]
  exact hasDerivAt_expectedCalibrationPortability_rateSegment hT hfirst hsecond ℓ₀ hap₀ hn x0
    source target score outcome hθ₀ hdenominator

/-- **The calibration intercept along a segment of rate histories, in Duhamel form.** -/
theorem hasDerivAt_expectedCalibrationIntercept_rateSegment_duhamel
    {first second : ℝ → NeutralRates Deme Locus Allele} {T : ℝ} (hT : 0 ≤ T)
    (hfirst : ∀ capacity : Locus → ℕ,
      ContinuousOn (fun t ↦ dualGenerator (first t) capacity) (Set.Icc 0 T))
    (hsecond : ∀ capacity : Locus → ℕ,
      ContinuousOn (fun t ↦ dualGenerator (second t) capacity) (Set.Icc 0 T))
    (ℓ₀ : Locus) (hap₀ : FullHaplotype Locus Allele) {n : ℕ} (hn : 3 ≤ n)
    (x0 : FrequencyState Deme Locus Allele) (deme : Deme)
    (score outcome : FullHaplotype Locus Allele → ℝ) {θ₀ : ℝ} (hθ₀ : θ₀ ∈ Set.Ioo (0 : ℝ) 1)
    (hvariance : ∫ y, (stateLaw y deme).variance score
      ∂(segmentKernel hT hfirst hsecond ℓ₀ hap₀ θ₀ x0) ≠ 0) :
    HasDerivAt (fun θ ↦ expectedCalibrationIntercept (segmentKernel hT hfirst hsecond ℓ₀ hap₀ θ)
        x0 deme score outcome)
      ((budgetCoefficients ℓ₀ (fun _ ↦ n) (interceptNumeratorPolynomial deme score outcome)
            ⬝ᵥ (duhamelSensitivity first second (fun _ ↦ n) T θ₀
              *ᵥ budgetMomentFeature (fun _ ↦ n) x0)
          * (∫ y, (stateLaw y deme).variance score
            ∂(segmentKernel hT hfirst hsecond ℓ₀ hap₀ θ₀ x0))
        - (∫ y, ((stateLaw y deme).expectation outcome * (stateLaw y deme).variance score
              - (stateLaw y deme).covariance score outcome * (stateLaw y deme).expectation score)
            ∂(segmentKernel hT hfirst hsecond ℓ₀ hap₀ θ₀ x0))
          * budgetCoefficients ℓ₀ (fun _ ↦ n) (demeCovariancePolynomial deme score score)
            ⬝ᵥ (duhamelSensitivity first second (fun _ ↦ n) T θ₀
              *ᵥ budgetMomentFeature (fun _ ↦ n) x0))
        / (∫ y, (stateLaw y deme).variance score
            ∂(segmentKernel hT hfirst hsecond ℓ₀ hap₀ θ₀ x0)) ^ 2) θ₀ := by
  rw [← ratePathSensitivity_eq_duhamelSensitivity hT (hfirst (fun _ ↦ n)) (hsecond (fun _ ↦ n))]
  exact hasDerivAt_expectedCalibrationIntercept_rateSegment hT hfirst hsecond ℓ₀ hap₀ hn x0 deme
    score outcome hθ₀ hvariance

/-- **AUC portability along a segment of rate histories, in Duhamel form.** -/
theorem hasDerivAt_expectedAUCPortability_rateSegment_duhamel
    {first second : ℝ → NeutralRates Deme Locus Allele} {T : ℝ} (hT : 0 ≤ T)
    (hfirst : ∀ capacity : Locus → ℕ,
      ContinuousOn (fun t ↦ dualGenerator (first t) capacity) (Set.Icc 0 T))
    (hsecond : ∀ capacity : Locus → ℕ,
      ContinuousOn (fun t ↦ dualGenerator (second t) capacity) (Set.Icc 0 T))
    (ℓ₀ : Locus) (hap₀ : FullHaplotype Locus Allele) (x0 : FrequencyState Deme Locus Allele)
    (source target : Deme) (score : FullHaplotype Locus Allele → ℝ)
    (outcome : FullHaplotype Locus Allele → Bool) {θ₀ : ℝ} (hθ₀ : θ₀ ∈ Set.Ioo (0 : ℝ) 1)
    (hdenominator : (∫ y, aucDenominator (stateLaw y target) outcome
          ∂(segmentKernel hT hfirst hsecond ℓ₀ hap₀ θ₀ x0))
        * (∫ y, aucNumerator (stateLaw y source) score outcome
          ∂(segmentKernel hT hfirst hsecond ℓ₀ hap₀ θ₀ x0)) ≠ 0) :
    HasDerivAt (fun θ ↦ expectedAUCPortability (segmentKernel hT hfirst hsecond ℓ₀ hap₀ θ) x0
        source target score outcome)
      (crossRatioDerivative
        (∫ y, aucNumerator (stateLaw y target) score outcome
          ∂(segmentKernel hT hfirst hsecond ℓ₀ hap₀ θ₀ x0))
        (∫ y, aucDenominator (stateLaw y source) outcome
          ∂(segmentKernel hT hfirst hsecond ℓ₀ hap₀ θ₀ x0))
        (∫ y, aucDenominator (stateLaw y target) outcome
          ∂(segmentKernel hT hfirst hsecond ℓ₀ hap₀ θ₀ x0))
        (∫ y, aucNumerator (stateLaw y source) score outcome
          ∂(segmentKernel hT hfirst hsecond ℓ₀ hap₀ θ₀ x0))
        (budgetCoefficients ℓ₀ (fun _ ↦ 2)
            (demePolynomial target (aucNumeratorPolynomial score outcome))
          ⬝ᵥ (duhamelSensitivity first second (fun _ ↦ 2) T θ₀
            *ᵥ budgetMomentFeature (fun _ ↦ 2) x0))
        (budgetCoefficients ℓ₀ (fun _ ↦ 2)
            (demePolynomial source (aucDenominatorPolynomial outcome))
          ⬝ᵥ (duhamelSensitivity first second (fun _ ↦ 2) T θ₀
            *ᵥ budgetMomentFeature (fun _ ↦ 2) x0))
        (budgetCoefficients ℓ₀ (fun _ ↦ 2)
            (demePolynomial target (aucDenominatorPolynomial outcome))
          ⬝ᵥ (duhamelSensitivity first second (fun _ ↦ 2) T θ₀
            *ᵥ budgetMomentFeature (fun _ ↦ 2) x0))
        (budgetCoefficients ℓ₀ (fun _ ↦ 2)
            (demePolynomial source (aucNumeratorPolynomial score outcome))
          ⬝ᵥ (duhamelSensitivity first second (fun _ ↦ 2) T θ₀
            *ᵥ budgetMomentFeature (fun _ ↦ 2) x0))) θ₀ := by
  rw [← ratePathSensitivity_eq_duhamelSensitivity hT (hfirst (fun _ ↦ 2)) (hsecond (fun _ ↦ 2))]
  exact hasDerivAt_expectedAUCPortability_rateSegment hT hfirst hsecond ℓ₀ hap₀ x0 source target
    score outcome hθ₀ hdenominator

/-! ## The sign criterion -/

/-- **When calibration portability decreases along a segment of rate histories.**  With positive
expected covariances and score variances at `θ₀`, calibration portability has negative derivative
exactly when the relative sensitivity of the target calibration, `C_t'/C_t - V_t'/V_t`, is below
that of the source, `C_s'/C_s - V_s'/V_s`. -/
theorem deriv_expectedCalibrationPortability_rateSegment_neg_iff
    {first second : ℝ → NeutralRates Deme Locus Allele} {T : ℝ} (hT : 0 ≤ T)
    (hfirst : ∀ capacity : Locus → ℕ,
      ContinuousOn (fun t ↦ dualGenerator (first t) capacity) (Set.Icc 0 T))
    (hsecond : ∀ capacity : Locus → ℕ,
      ContinuousOn (fun t ↦ dualGenerator (second t) capacity) (Set.Icc 0 T))
    (ℓ₀ : Locus) (hap₀ : FullHaplotype Locus Allele) {n : ℕ} (hn : 2 ≤ n)
    (x0 : FrequencyState Deme Locus Allele) (source target : Deme)
    (score outcome : FullHaplotype Locus Allele → ℝ) {θ₀ : ℝ} (hθ₀ : θ₀ ∈ Set.Ioo (0 : ℝ) 1)
    (htargetCovariance : 0 < ∫ y, (stateLaw y target).covariance score outcome
      ∂(segmentKernel hT hfirst hsecond ℓ₀ hap₀ θ₀ x0))
    (hsourceVariance : 0 < ∫ y, (stateLaw y source).variance score
      ∂(segmentKernel hT hfirst hsecond ℓ₀ hap₀ θ₀ x0))
    (htargetVariance : 0 < ∫ y, (stateLaw y target).variance score
      ∂(segmentKernel hT hfirst hsecond ℓ₀ hap₀ θ₀ x0))
    (hsourceCovariance : 0 < ∫ y, (stateLaw y source).covariance score outcome
      ∂(segmentKernel hT hfirst hsecond ℓ₀ hap₀ θ₀ x0)) :
    deriv (fun θ ↦ expectedCalibrationPortability (segmentKernel hT hfirst hsecond ℓ₀ hap₀ θ) x0
        source target score outcome) θ₀ < 0
      ↔ budgetCoefficients ℓ₀ (fun _ ↦ n) (demeCovariancePolynomial target score outcome)
            ⬝ᵥ (ratePathSensitivity first second (fun _ ↦ n) T θ₀
              *ᵥ budgetMomentFeature (fun _ ↦ n) x0)
          / (∫ y, (stateLaw y target).covariance score outcome
            ∂(segmentKernel hT hfirst hsecond ℓ₀ hap₀ θ₀ x0))
        - budgetCoefficients ℓ₀ (fun _ ↦ n) (demeCovariancePolynomial target score score)
            ⬝ᵥ (ratePathSensitivity first second (fun _ ↦ n) T θ₀
              *ᵥ budgetMomentFeature (fun _ ↦ n) x0)
          / (∫ y, (stateLaw y target).variance score
            ∂(segmentKernel hT hfirst hsecond ℓ₀ hap₀ θ₀ x0))
        < budgetCoefficients ℓ₀ (fun _ ↦ n) (demeCovariancePolynomial source score outcome)
            ⬝ᵥ (ratePathSensitivity first second (fun _ ↦ n) T θ₀
              *ᵥ budgetMomentFeature (fun _ ↦ n) x0)
          / (∫ y, (stateLaw y source).covariance score outcome
            ∂(segmentKernel hT hfirst hsecond ℓ₀ hap₀ θ₀ x0))
        - budgetCoefficients ℓ₀ (fun _ ↦ n) (demeCovariancePolynomial source score score)
            ⬝ᵥ (ratePathSensitivity first second (fun _ ↦ n) T θ₀
              *ᵥ budgetMomentFeature (fun _ ↦ n) x0)
          / (∫ y, (stateLaw y source).variance score
            ∂(segmentKernel hT hfirst hsecond ℓ₀ hap₀ θ₀ x0)) := by
  rw [(hasDerivAt_expectedCalibrationPortability_rateSegment hT hfirst hsecond ℓ₀ hap₀ hn x0
    source target score outcome hθ₀ (mul_pos htargetVariance hsourceCovariance).ne').deriv]
  exact crossRatioDerivative_neg_iff_of_pos _ _ _ _ htargetCovariance hsourceVariance
    htargetVariance hsourceCovariance

/-- **When AUC portability decreases along a segment of rate histories.**  With positive expected
AUC numerators and denominators at `θ₀`, AUC portability has negative derivative exactly when the
relative sensitivity of the target components, `N_t'/N_t - D_t'/D_t`, is below that of the source,
`N_s'/N_s - D_s'/D_s`. -/
theorem deriv_expectedAUCPortability_rateSegment_neg_iff
    {first second : ℝ → NeutralRates Deme Locus Allele} {T : ℝ} (hT : 0 ≤ T)
    (hfirst : ∀ capacity : Locus → ℕ,
      ContinuousOn (fun t ↦ dualGenerator (first t) capacity) (Set.Icc 0 T))
    (hsecond : ∀ capacity : Locus → ℕ,
      ContinuousOn (fun t ↦ dualGenerator (second t) capacity) (Set.Icc 0 T))
    (ℓ₀ : Locus) (hap₀ : FullHaplotype Locus Allele) (x0 : FrequencyState Deme Locus Allele)
    (source target : Deme) (score : FullHaplotype Locus Allele → ℝ)
    (outcome : FullHaplotype Locus Allele → Bool) {θ₀ : ℝ} (hθ₀ : θ₀ ∈ Set.Ioo (0 : ℝ) 1)
    (htargetNumerator : 0 < ∫ y, aucNumerator (stateLaw y target) score outcome
      ∂(segmentKernel hT hfirst hsecond ℓ₀ hap₀ θ₀ x0))
    (hsourceDenominator : 0 < ∫ y, aucDenominator (stateLaw y source) outcome
      ∂(segmentKernel hT hfirst hsecond ℓ₀ hap₀ θ₀ x0))
    (htargetDenominator : 0 < ∫ y, aucDenominator (stateLaw y target) outcome
      ∂(segmentKernel hT hfirst hsecond ℓ₀ hap₀ θ₀ x0))
    (hsourceNumerator : 0 < ∫ y, aucNumerator (stateLaw y source) score outcome
      ∂(segmentKernel hT hfirst hsecond ℓ₀ hap₀ θ₀ x0)) :
    deriv (fun θ ↦ expectedAUCPortability (segmentKernel hT hfirst hsecond ℓ₀ hap₀ θ) x0 source
        target score outcome) θ₀ < 0
      ↔ budgetCoefficients ℓ₀ (fun _ ↦ 2)
              (demePolynomial target (aucNumeratorPolynomial score outcome))
            ⬝ᵥ (ratePathSensitivity first second (fun _ ↦ 2) T θ₀
              *ᵥ budgetMomentFeature (fun _ ↦ 2) x0)
          / (∫ y, aucNumerator (stateLaw y target) score outcome
            ∂(segmentKernel hT hfirst hsecond ℓ₀ hap₀ θ₀ x0))
        - budgetCoefficients ℓ₀ (fun _ ↦ 2)
              (demePolynomial target (aucDenominatorPolynomial outcome))
            ⬝ᵥ (ratePathSensitivity first second (fun _ ↦ 2) T θ₀
              *ᵥ budgetMomentFeature (fun _ ↦ 2) x0)
          / (∫ y, aucDenominator (stateLaw y target) outcome
            ∂(segmentKernel hT hfirst hsecond ℓ₀ hap₀ θ₀ x0))
        < budgetCoefficients ℓ₀ (fun _ ↦ 2)
              (demePolynomial source (aucNumeratorPolynomial score outcome))
            ⬝ᵥ (ratePathSensitivity first second (fun _ ↦ 2) T θ₀
              *ᵥ budgetMomentFeature (fun _ ↦ 2) x0)
          / (∫ y, aucNumerator (stateLaw y source) score outcome
            ∂(segmentKernel hT hfirst hsecond ℓ₀ hap₀ θ₀ x0))
        - budgetCoefficients ℓ₀ (fun _ ↦ 2)
              (demePolynomial source (aucDenominatorPolynomial outcome))
            ⬝ᵥ (ratePathSensitivity first second (fun _ ↦ 2) T θ₀
              *ᵥ budgetMomentFeature (fun _ ↦ 2) x0)
          / (∫ y, aucDenominator (stateLaw y source) outcome
            ∂(segmentKernel hT hfirst hsecond ℓ₀ hap₀ θ₀ x0)) := by
  rw [(hasDerivAt_expectedAUCPortability_rateSegment hT hfirst hsecond ℓ₀ hap₀ x0 source target
    score outcome hθ₀ (mul_pos htargetDenominator hsourceNumerator).ne').deriv]
  exact crossRatioDerivative_neg_iff_of_pos _ _ _ _ htargetNumerator hsourceDenominator
    htargetDenominator hsourceNumerator

end

end Descent.Portability.EndToEndSensitivityRatePathMetrics
