/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.FundamentalMatrixParameterDerivative
import Descent.Portability.EndToEndSensitivityRates

assert_below Descent.Decision Descent.Program

/-!
# The exact sensitivity of a time-varying rate history

`NeutralRateHistoryRealization` gives a rate history `t ↦ rates t` with continuous dual generator
the propagator `rateHistoryDualPropagator`, the fundamental matrix of its dual generator path, and
`EndToEndPortabilityLaw` writes the expected metrics under its kernel as pairings with that
propagator.  This module differentiates both in a parameter moving the whole rate history.

Segments of rate histories.  Given two rate histories `first` and `second` with continuous dual
generators, the history `t ↦ rateSegment (first t) (second t) θ` interpolates them at every time.
Its dual generators are continuous (`continuousOn_dualGenerator_rateSegment`), and for `θ ∈ [0, 1]`
its dual generator path is `Q_first + θ (Q_second - Q_first)` (`dualGeneratorPath_rateSegment`), by
the additivity of the dual generator in the rates
(`EndToEndSensitivityRates.dualGenerator_rateSegment`).

The propagator.  The parameter enters that path affinely, so
`FundamentalMatrixParameterDerivative.hasDerivAt_fundamentalMatrix_affinePath` applies: at every
interior `θ₀` every entry of the propagator has derivative the lower-left block of the fundamental
matrix of `[[Q_θ₀, 0], [Q_second - Q_first, Q_θ₀]]` (`ratePathSensitivity`,
`hasDerivAt_rateHistoryDualPropagator_segment`), and `c · U(θ) v` has derivative
`c · (ratePathSensitivity) v` (`hasDerivAt_dotProduct_rateHistoryDualPropagator_segment`).

The metrics.  The expected squared-correlation numerator and denominator under the rate-history
kernel then have exact derivatives (`hasDerivAt_integral_correlationNumerator_rateSegment`,
`hasDerivAt_integral_correlationDenominator_rateSegment`), and the portability of expected
accuracies has the cross-ratio derivative of `EndToEndSensitivityMetrics`
(`hasDerivAt_expectedPortability_rateSegment`), with no differentiability hypothesis.

Scope.  The rate histories have continuous dual generators, as the kernel of
`NeutralRateHistoryKernel` requires; integrable rate histories are not covered.  The derivative is
stated in block form: the two-time propagator of the integral form `∫₀ᵀ U(T, s) Q' U(s) ds` is not
constructed in the corpus.  The endpoints of the segment, where the clamp makes the derivative
one-sided, are not stated.

## Empirical status

None.  The bodies here are derivatives of fundamental matrices of supplied generator paths and
pairings of supplied coefficient vectors with them, so no measurement can bear on them.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.EndToEndSensitivityRatePath

open MeasureTheory ProbabilityTheory MvPolynomial Descent.Coalescent PartialHaplotypeCarrier
  PartialHaplotypeDualGenerator PartialHaplotypeDualSemigroup NeutralFellerGenerator
  NeutralPolynomialSemigroup PartialHaplotypeMicroscopicApproximation PartialHaplotypePulseKernel
  NeutralPulseHistoryKernel ReplicaMetricInstances LinearFundamentalMatrix NeutralRateLipschitz
  NeutralRateHistoryRealization NeutralRateHistoryKernel EndToEndPortabilityLaw
  EndToEndSensitivityMetrics EndToEndSensitivityRates FundamentalMatrixParameterDerivative
open scoped Matrix NNReal

noncomputable section

variable {Deme Locus : Type*} {Allele : Locus → Type*}
variable [Fintype Deme] [DecidableEq Deme] [Fintype Locus] [DecidableEq Locus]
  [∀ ℓ, Fintype (Allele ℓ)] [∀ ℓ, DecidableEq (Allele ℓ)]

/-! ## Segments of rate histories -/

/-- A segment of two rate histories with continuous dual generators has continuous dual
generators at every parameter. -/
theorem continuousOn_dualGenerator_rateSegment {first second : ℝ → NeutralRates Deme Locus Allele}
    {T : ℝ}
    (hfirst : ∀ capacity : Locus → ℕ,
      ContinuousOn (fun t ↦ dualGenerator (first t) capacity) (Set.Icc 0 T))
    (hsecond : ∀ capacity : Locus → ℕ,
      ContinuousOn (fun t ↦ dualGenerator (second t) capacity) (Set.Icc 0 T))
    (θ : ℝ) : ∀ capacity : Locus → ℕ,
      ContinuousOn (fun t ↦ dualGenerator (rateSegment (first t) (second t) θ) capacity)
        (Set.Icc 0 T) := by
  intro capacity
  simp only [dualGenerator_rateSegment]
  exact ((hfirst capacity).const_smul _).add ((hsecond capacity).const_smul _)

/-- For a parameter in `[0, 1]` the dual generator path of a segment of rate histories is
`Q_first + θ (Q_second - Q_first)`. -/
theorem dualGeneratorPath_rateSegment (first second : ℝ → NeutralRates Deme Locus Allele)
    (capacity : Locus → ℕ) (T : ℝ) {θ : ℝ} (hθ : θ ∈ Set.Icc (0 : ℝ) 1) :
    dualGeneratorPath (fun t ↦ rateSegment (first t) (second t) θ) capacity T
      = fun s ↦ dualGeneratorPath first capacity T s
        + θ • (dualGeneratorPath second capacity T s - dualGeneratorPath first capacity T s) := by
  funext s
  show dualGenerator (rateSegment (first (clampTime T s)) (second (clampTime T s)) θ) capacity
    = dualGenerator (first (clampTime T s)) capacity
      + θ • (dualGenerator (second (clampTime T s)) capacity
        - dualGenerator (first (clampTime T s)) capacity)
  rw [dualGenerator_rateSegment, clampTime_of_mem hθ, sub_smul, one_smul, smul_sub]
  abel

/-- **The sensitivity matrix of a segment of rate histories** at `θ₀`: the lower-left block of the
fundamental matrix of `[[Q_θ₀, 0], [Q_second - Q_first, Q_θ₀]]` at the horizon. -/
def ratePathSensitivity (first second : ℝ → NeutralRates Deme Locus Allele)
    (capacity : Locus → ℕ) (T θ₀ : ℝ) :
    Matrix (BudgetConfiguration Deme Locus Allele capacity)
      (BudgetConfiguration Deme Locus Allele capacity) ℝ :=
  (fundamentalMatrix
    (blockPath
      (fun s ↦ dualGeneratorPath first capacity T s
        + θ₀ • (dualGeneratorPath second capacity T s - dualGeneratorPath first capacity T s))
      (fun s ↦ dualGeneratorPath second capacity T s - dualGeneratorPath first capacity T s)
      (fun s ↦ dualGeneratorPath first capacity T s
        + θ₀ • (dualGeneratorPath second capacity T s - dualGeneratorPath first capacity T s)))
    T T).toBlocks₂₁

/-- **The propagator of a segment of rate histories is differentiable** at every interior
parameter, entry by entry, with the entries of `ratePathSensitivity` as derivatives. -/
theorem hasDerivAt_rateHistoryDualPropagator_segment
    {first second : ℝ → NeutralRates Deme Locus Allele} {capacity : Locus → ℕ} {T : ℝ}
    (hT : 0 ≤ T)
    (hfirst : ContinuousOn (fun t ↦ dualGenerator (first t) capacity) (Set.Icc 0 T))
    (hsecond : ContinuousOn (fun t ↦ dualGenerator (second t) capacity) (Set.Icc 0 T))
    {θ₀ : ℝ} (hθ₀ : θ₀ ∈ Set.Ioo (0 : ℝ) 1)
    (ξ η : BudgetConfiguration Deme Locus Allele capacity) :
    HasDerivAt
      (fun θ ↦ rateHistoryDualPropagator (fun t ↦ rateSegment (first t) (second t) θ) capacity T
        ξ η)
      (ratePathSensitivity first second capacity T θ₀ ξ η) θ₀ := by
  have hA := continuous_dualGeneratorPath hT hfirst
  have hB := (continuous_dualGeneratorPath hT hsecond).sub hA
  refine (hasDerivAt_fundamentalMatrix_affinePath hA hB hT θ₀ ξ η).congr_of_eventuallyEq ?_
  filter_upwards [Ioo_mem_nhds hθ₀.1 hθ₀.2] with θ hθ
  show fundamentalMatrix (dualGeneratorPath (fun t ↦ rateSegment (first t) (second t) θ)
    capacity T) T T ξ η = _
  rw [dualGeneratorPath_rateSegment first second capacity T ⟨hθ.1.le, hθ.2.le⟩]

/-- **The pairing law along a segment of rate histories.** -/
theorem hasDerivAt_dotProduct_rateHistoryDualPropagator_segment
    {first second : ℝ → NeutralRates Deme Locus Allele} {capacity : Locus → ℕ} {T : ℝ}
    (hT : 0 ≤ T)
    (hfirst : ContinuousOn (fun t ↦ dualGenerator (first t) capacity) (Set.Icc 0 T))
    (hsecond : ContinuousOn (fun t ↦ dualGenerator (second t) capacity) (Set.Icc 0 T))
    {θ₀ : ℝ} (hθ₀ : θ₀ ∈ Set.Ioo (0 : ℝ) 1)
    (c v : BudgetConfiguration Deme Locus Allele capacity → ℝ) :
    HasDerivAt
      (fun θ ↦ c ⬝ᵥ (rateHistoryDualPropagator (fun t ↦ rateSegment (first t) (second t) θ)
        capacity T *ᵥ v))
      (c ⬝ᵥ (ratePathSensitivity first second capacity T θ₀ *ᵥ v)) θ₀ :=
  hasDerivAt_dotProduct_mulVec_of_apply
    (hasDerivAt_rateHistoryDualPropagator_segment hT hfirst hsecond hθ₀) c v

/-- A function equal at every parameter to a pairing with the propagator of a segment of rate
histories has the paired sensitivity as derivative. -/
theorem hasDerivAt_of_eq_dotProduct_rateSegment
    {first second : ℝ → NeutralRates Deme Locus Allele} {capacity : Locus → ℕ} {T : ℝ}
    (hT : 0 ≤ T)
    (hfirst : ContinuousOn (fun t ↦ dualGenerator (first t) capacity) (Set.Icc 0 T))
    (hsecond : ContinuousOn (fun t ↦ dualGenerator (second t) capacity) (Set.Icc 0 T))
    {θ₀ : ℝ} (hθ₀ : θ₀ ∈ Set.Ioo (0 : ℝ) 1) {F : ℝ → ℝ}
    (c v : BudgetConfiguration Deme Locus Allele capacity → ℝ)
    (hF : ∀ θ, F θ = c ⬝ᵥ (rateHistoryDualPropagator (fun t ↦ rateSegment (first t) (second t) θ)
      capacity T *ᵥ v)) :
    HasDerivAt F (c ⬝ᵥ (ratePathSensitivity first second capacity T θ₀ *ᵥ v)) θ₀ := by
  rw [show F = _ from funext hF]
  exact hasDerivAt_dotProduct_rateHistoryDualPropagator_segment hT hfirst hsecond hθ₀ c v

/-! ## The metrics along a segment of rate histories -/

/-- **The sensitivity of the expected squared-correlation numerator** along a segment of rate
histories. -/
theorem hasDerivAt_integral_correlationNumerator_rateSegment
    {first second : ℝ → NeutralRates Deme Locus Allele} {T : ℝ} (hT : 0 ≤ T)
    (hfirst : ∀ capacity : Locus → ℕ,
      ContinuousOn (fun t ↦ dualGenerator (first t) capacity) (Set.Icc 0 T))
    (hsecond : ∀ capacity : Locus → ℕ,
      ContinuousOn (fun t ↦ dualGenerator (second t) capacity) (Set.Icc 0 T))
    (ℓ₀ : Locus) (hap₀ : FullHaplotype Locus Allele) (x0 : FrequencyState Deme Locus Allele)
    (deme : Deme) (score outcome : FullHaplotype Locus Allele → ℝ) {θ₀ : ℝ}
    (hθ₀ : θ₀ ∈ Set.Ioo (0 : ℝ) 1) :
    HasDerivAt (fun θ ↦ ∫ y, correlationNumerator (stateLaw y deme) score outcome
        ∂(rateHistoryKernel (fun t ↦ rateSegment (first t) (second t) θ) ℓ₀ hap₀ hT
          (continuousOn_dualGenerator_rateSegment hfirst hsecond θ) x0))
      (budgetCoefficients ℓ₀ (fun _ ↦ 4) (numeratorPolynomial deme score outcome)
        ⬝ᵥ (ratePathSensitivity first second (fun _ ↦ 4) T θ₀
          *ᵥ budgetMomentFeature (fun _ ↦ 4) x0)) θ₀ :=
  hasDerivAt_of_eq_dotProduct_rateSegment hT (hfirst _) (hsecond _) hθ₀ _ _ fun θ ↦
    integral_correlationNumerator_rateHistoryKernel hT
      (continuousOn_dualGenerator_rateSegment hfirst hsecond θ) ℓ₀ hap₀ x0 deme score outcome

/-- **The sensitivity of the expected squared-correlation denominator** along a segment of rate
histories. -/
theorem hasDerivAt_integral_correlationDenominator_rateSegment
    {first second : ℝ → NeutralRates Deme Locus Allele} {T : ℝ} (hT : 0 ≤ T)
    (hfirst : ∀ capacity : Locus → ℕ,
      ContinuousOn (fun t ↦ dualGenerator (first t) capacity) (Set.Icc 0 T))
    (hsecond : ∀ capacity : Locus → ℕ,
      ContinuousOn (fun t ↦ dualGenerator (second t) capacity) (Set.Icc 0 T))
    (ℓ₀ : Locus) (hap₀ : FullHaplotype Locus Allele) (x0 : FrequencyState Deme Locus Allele)
    (deme : Deme) (score outcome : FullHaplotype Locus Allele → ℝ) {θ₀ : ℝ}
    (hθ₀ : θ₀ ∈ Set.Ioo (0 : ℝ) 1) :
    HasDerivAt (fun θ ↦ ∫ y, correlationDenominator (stateLaw y deme) score outcome
        ∂(rateHistoryKernel (fun t ↦ rateSegment (first t) (second t) θ) ℓ₀ hap₀ hT
          (continuousOn_dualGenerator_rateSegment hfirst hsecond θ) x0))
      (budgetCoefficients ℓ₀ (fun _ ↦ 4) (denominatorPolynomial deme score outcome)
        ⬝ᵥ (ratePathSensitivity first second (fun _ ↦ 4) T θ₀
          *ᵥ budgetMomentFeature (fun _ ↦ 4) x0)) θ₀ :=
  hasDerivAt_of_eq_dotProduct_rateSegment hT (hfirst _) (hsecond _) hθ₀ _ _ fun θ ↦
    integral_correlationDenominator_rateHistoryKernel hT
      (continuousOn_dualGenerator_rateSegment hfirst hsecond θ) ℓ₀ hap₀ x0 deme score outcome

/-- **The sensitivity of expected portability along a segment of rate histories**, with no
differentiability hypothesis, wherever `E D_t E N_s ≠ 0`. -/
theorem hasDerivAt_expectedPortability_rateSegment
    {first second : ℝ → NeutralRates Deme Locus Allele} {T : ℝ} (hT : 0 ≤ T)
    (hfirst : ∀ capacity : Locus → ℕ,
      ContinuousOn (fun t ↦ dualGenerator (first t) capacity) (Set.Icc 0 T))
    (hsecond : ∀ capacity : Locus → ℕ,
      ContinuousOn (fun t ↦ dualGenerator (second t) capacity) (Set.Icc 0 T))
    (ℓ₀ : Locus) (hap₀ : FullHaplotype Locus Allele) (x0 : FrequencyState Deme Locus Allele)
    (source target : Deme) (score outcome : FullHaplotype Locus Allele → ℝ) {θ₀ : ℝ}
    (hθ₀ : θ₀ ∈ Set.Ioo (0 : ℝ) 1)
    (hdenominator : (∫ y, correlationDenominator (stateLaw y target) score outcome
          ∂(rateHistoryKernel (fun t ↦ rateSegment (first t) (second t) θ₀) ℓ₀ hap₀ hT
            (continuousOn_dualGenerator_rateSegment hfirst hsecond θ₀) x0))
        * (∫ y, correlationNumerator (stateLaw y source) score outcome
          ∂(rateHistoryKernel (fun t ↦ rateSegment (first t) (second t) θ₀) ℓ₀ hap₀ hT
            (continuousOn_dualGenerator_rateSegment hfirst hsecond θ₀) x0)) ≠ 0) :
    HasDerivAt (fun θ ↦ expectedPortability
        (rateHistoryKernel (fun t ↦ rateSegment (first t) (second t) θ) ℓ₀ hap₀ hT
          (continuousOn_dualGenerator_rateSegment hfirst hsecond θ)) x0 source target score
        outcome)
      (crossRatioDerivative
        (∫ y, correlationNumerator (stateLaw y target) score outcome
          ∂(rateHistoryKernel (fun t ↦ rateSegment (first t) (second t) θ₀) ℓ₀ hap₀ hT
            (continuousOn_dualGenerator_rateSegment hfirst hsecond θ₀) x0))
        (∫ y, correlationDenominator (stateLaw y source) score outcome
          ∂(rateHistoryKernel (fun t ↦ rateSegment (first t) (second t) θ₀) ℓ₀ hap₀ hT
            (continuousOn_dualGenerator_rateSegment hfirst hsecond θ₀) x0))
        (∫ y, correlationDenominator (stateLaw y target) score outcome
          ∂(rateHistoryKernel (fun t ↦ rateSegment (first t) (second t) θ₀) ℓ₀ hap₀ hT
            (continuousOn_dualGenerator_rateSegment hfirst hsecond θ₀) x0))
        (∫ y, correlationNumerator (stateLaw y source) score outcome
          ∂(rateHistoryKernel (fun t ↦ rateSegment (first t) (second t) θ₀) ℓ₀ hap₀ hT
            (continuousOn_dualGenerator_rateSegment hfirst hsecond θ₀) x0))
        (budgetCoefficients ℓ₀ (fun _ ↦ 4) (numeratorPolynomial target score outcome)
          ⬝ᵥ (ratePathSensitivity first second (fun _ ↦ 4) T θ₀
            *ᵥ budgetMomentFeature (fun _ ↦ 4) x0))
        (budgetCoefficients ℓ₀ (fun _ ↦ 4) (denominatorPolynomial source score outcome)
          ⬝ᵥ (ratePathSensitivity first second (fun _ ↦ 4) T θ₀
            *ᵥ budgetMomentFeature (fun _ ↦ 4) x0))
        (budgetCoefficients ℓ₀ (fun _ ↦ 4) (denominatorPolynomial target score outcome)
          ⬝ᵥ (ratePathSensitivity first second (fun _ ↦ 4) T θ₀
            *ᵥ budgetMomentFeature (fun _ ↦ 4) x0))
        (budgetCoefficients ℓ₀ (fun _ ↦ 4) (numeratorPolynomial source score outcome)
          ⬝ᵥ (ratePathSensitivity first second (fun _ ↦ 4) T θ₀
            *ᵥ budgetMomentFeature (fun _ ↦ 4) x0))) θ₀ :=
  hasDerivAt_crossRatio
    (hasDerivAt_integral_correlationNumerator_rateSegment hT hfirst hsecond ℓ₀ hap₀ x0 target
      score outcome hθ₀)
    (hasDerivAt_integral_correlationDenominator_rateSegment hT hfirst hsecond ℓ₀ hap₀ x0 source
      score outcome hθ₀)
    (hasDerivAt_integral_correlationDenominator_rateSegment hT hfirst hsecond ℓ₀ hap₀ x0 target
      score outcome hθ₀)
    (hasDerivAt_integral_correlationNumerator_rateSegment hT hfirst hsecond ℓ₀ hap₀ x0 source
      score outcome hθ₀)
    hdenominator

end

end Descent.Portability.EndToEndSensitivityRatePath
