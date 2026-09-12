/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.EndToEndSensitivityMetrics
import Descent.Portability.NeutralRateLipschitz

assert_below Descent.Decision Descent.Program

/-!
# The exact sensitivity law in the demographic rates, with no differentiability hypothesis

`EndToEndSensitivityLaw` differentiates the propagator of a history of epochs, splits and pulses
in a parameter, assuming that the dual generator of each epoch is differentiable in it.  This
module removes that assumption for the rates of the neutral model.

The generator.  `NeutralRateLipschitz` proves that the partial-haplotype dual generator is additive
and homogeneous in the rate law (`dualGenerator_addNeutralRates`, `dualGenerator_scaleNeutralRates`)
and is a linear map of the signed rate coordinates
(`dualGeneratorLinearMap`, `dualGenerator_eq_dualGeneratorLinearMap`).  So along any rate path whose
coalescence, migration, recombination and mutation coordinates are differentiable, every entry of
the dual generator is differentiable with derivative the linear generator of the coordinate
derivative (`hasDerivAt_dualGenerator_apply`), and the epoch propagator has the Duhamel derivative
of that direction (`hasDerivAt_eventPropagator_ratePath`).

Segments.  Between any two rate laws `r` and `s` the segment `(1 - θ) r + θ s`, with the parameter
clamped into `[0, 1]` (`rateSegment`), is a rate law at every parameter, and its dual generator is
`(1 - θ) Q(r) + θ Q(s)` (`dualGenerator_rateSegment`).  At every interior parameter its entries have
derivative `Q(s) - Q(r)` (`hasDerivAt_dualGenerator_rateSegment`), with no hypothesis at all.  A
single rate coordinate moving from one value to another is such a segment.

Histories along segments.  A segment history lists epochs `(r, s, duration)` and pulses
(`segmentEvent`).  Every event propagator of it is differentiable at an interior parameter, an epoch
with the Duhamel derivative in the direction `Q(s) - Q(r)` and a pulse with derivative zero
(`hasDerivAt_eventPropagator_segmentEvent`, `segmentDerivative`,
`deriv_eventPropagator_segmentEvent`).  So the stagewise sensitivity law of the history holds
unconditionally (`hasDerivAt_dotProduct_segmentHistory`), and so do the derivatives of the
portability of expected accuracies, of calibration portability and of AUC portability
(`hasDerivAt_expectedPortability_segmentHistory`,
`hasDerivAt_expectedCalibrationPortability_segmentHistory`,
`hasDerivAt_expectedAUCPortability_segmentHistory`), wherever their denominators are nonzero.

Scope.  Pulses and splits are held fixed.  The derivative along a segment is two-sided at interior
parameters; at the endpoints the clamp makes it one-sided, which is not stated.  Durations are
fixed.

## Empirical status

None.  The bodies here are derivatives of linear maps of rate coordinates composed with the
propagator derivatives of `EndToEndSensitivityLaw`, so no measurement can bear on them.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.EndToEndSensitivityRates

open MeasureTheory ProbabilityTheory MvPolynomial Descent.Coalescent PartialHaplotypeCarrier
  PartialHaplotypeDualGenerator PartialHaplotypeDualSemigroup NeutralFellerGenerator
  NeutralPolynomialSemigroup PartialHaplotypeMicroscopicApproximation PartialHaplotypePulseKernel
  NeutralPulseHistoryKernel ReplicaMetricInstances LinearFundamentalMatrix NeutralRateLipschitz
  EndToEndPortabilityLaw EndToEndCalibrationLaw EndToEndDiscriminationLaw EndToEndSensitivityLaw
  EndToEndSensitivityMetrics
open scoped Matrix NNReal

noncomputable section

variable {Deme Locus : Type*} {Allele : Locus → Type*}
variable [Fintype Deme] [DecidableEq Deme] [Fintype Locus] [DecidableEq Locus]
  [∀ ℓ, Fintype (Allele ℓ)] [∀ ℓ, DecidableEq (Allele ℓ)]

/-! ## The dual generator along a rate path -/

/-- **The dual generator is differentiable in the rate coordinates.**  Along a rate path whose
coordinates have derivative `direction` at `θ₀`, every entry of the dual generator has derivative
the corresponding entry of the linear generator of `direction`. -/
theorem hasDerivAt_dualGenerator_apply {rates : ℝ → NeutralRates Deme Locus Allele}
    {direction : NeutralRateCoordinates Deme Locus Allele} {θ₀ : ℝ}
    (hrates : HasDerivAt (fun θ ↦ neutralRateCoordinates (rates θ)) direction θ₀)
    (capacity : Locus → ℕ) (ξ η : BudgetConfiguration Deme Locus Allele capacity) :
    HasDerivAt (fun θ ↦ dualGenerator (rates θ) capacity ξ η)
      (dualGeneratorLinearMap capacity direction ξ η) θ₀ := by
  have hfun : (fun θ ↦ dualGenerator (rates θ) capacity ξ η)
      = fun θ ↦ dualGeneratorLinearMap capacity (neutralRateCoordinates (rates θ)) ξ η :=
    funext fun θ ↦ by rw [dualGenerator_eq_dualGeneratorLinearMap]
  rw [hfun]
  exact (LinearMap.toContinuousLinearMap
    (({ toFun := fun N ↦ N ξ η, map_add' := fun _ _ ↦ rfl, map_smul' := fun _ _ ↦ rfl } :
      Matrix (BudgetConfiguration Deme Locus Allele capacity)
        (BudgetConfiguration Deme Locus Allele capacity) ℝ →ₗ[ℝ] ℝ).comp
      (dualGeneratorLinearMap capacity))).hasFDerivAt.comp_hasDerivAt θ₀ hrates

/-- **An epoch along a rate path has the Duhamel derivative** in the direction of the linear
generator of the coordinate derivative. -/
theorem hasDerivAt_eventPropagator_ratePath (capacity : Locus → ℕ)
    {rates : ℝ → NeutralRates Deme Locus Allele}
    {direction : NeutralRateCoordinates Deme Locus Allele} {θ₀ : ℝ}
    (hrates : HasDerivAt (fun θ ↦ neutralRateCoordinates (rates θ)) direction θ₀)
    (duration : ℝ≥0) (ξ η : BudgetConfiguration Deme Locus Allele capacity) :
    HasDerivAt (fun θ ↦ eventPropagator capacity
        (Sum.inl (rates θ, duration) : (NeutralRates Deme Locus Allele × ℝ≥0) ⊕ PulseMatrix Deme)
        ξ η)
      (duhamelDerivative (dualGenerator (rates θ₀) capacity)
        (dualGeneratorLinearMap capacity direction) duration ξ η) θ₀ :=
  hasDerivAt_eventPropagator_epoch capacity (hasDerivAt_dualGenerator_apply hrates capacity)
    duration ξ η

/-! ## Segments of rate laws -/

/-- **The segment of rate laws** from `first` to `second`: the law `(1 - θ) first + θ second`, with
the parameter clamped into `[0, 1]`, so that it is a rate law at every parameter. -/
def rateSegment (first second : NeutralRates Deme Locus Allele) (θ : ℝ) :
    NeutralRates Deme Locus Allele :=
  addNeutralRates
    (scaleNeutralRates (1 - clampTime 1 θ) (sub_nonneg.mpr (clampTime_mem zero_le_one θ).2)
      first)
    (scaleNeutralRates (clampTime 1 θ) (clampTime_mem zero_le_one θ).1 second)

/-- The dual generator along a segment of rate laws is the segment of the dual generators. -/
theorem dualGenerator_rateSegment (first second : NeutralRates Deme Locus Allele) (θ : ℝ)
    (capacity : Locus → ℕ) :
    dualGenerator (rateSegment first second θ) capacity
      = (1 - clampTime 1 θ) • dualGenerator first capacity
        + clampTime 1 θ • dualGenerator second capacity := by
  rw [rateSegment, dualGenerator_addNeutralRates, dualGenerator_scaleNeutralRates,
    dualGenerator_scaleNeutralRates]

/-- **The dual generator along a segment has derivative `Q(second) - Q(first)`** at every
interior parameter, with no hypothesis. -/
theorem hasDerivAt_dualGenerator_rateSegment (first second : NeutralRates Deme Locus Allele)
    (capacity : Locus → ℕ) {θ₀ : ℝ} (hθ₀ : θ₀ ∈ Set.Ioo (0 : ℝ) 1)
    (ξ η : BudgetConfiguration Deme Locus Allele capacity) :
    HasDerivAt (fun θ ↦ dualGenerator (rateSegment first second θ) capacity ξ η)
      ((dualGenerator second capacity - dualGenerator first capacity) ξ η) θ₀ := by
  have hline : HasDerivAt (fun θ : ℝ ↦
      (1 - θ) * dualGenerator first capacity ξ η + θ * dualGenerator second capacity ξ η)
      ((dualGenerator second capacity - dualGenerator first capacity) ξ η) θ₀ := by
    refine ((((hasDerivAt_id' (x := θ₀)).const_sub 1).mul_const
      (dualGenerator first capacity ξ η)).add
        ((hasDerivAt_id' (x := θ₀)).mul_const (dualGenerator second capacity ξ η))).congr_deriv ?_
    simp only [Matrix.sub_apply]
    ring
  refine hline.congr_of_eventuallyEq ?_
  filter_upwards [Ioo_mem_nhds hθ₀.1 hθ₀.2] with θ hθ
  rw [dualGenerator_rateSegment, clampTime_of_mem ⟨hθ.1.le, hθ.2.le⟩, Matrix.add_apply,
    Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul, smul_eq_mul]

/-! ## Histories along segments -/

/-- **The event families of a segment history**: an epoch `(first, second, duration)` runs along
the segment of rate laws from `first` to `second`, and a pulse is fixed. -/
def segmentEvent :
    (NeutralRates Deme Locus Allele × NeutralRates Deme Locus Allele × ℝ≥0) ⊕ PulseMatrix Deme →
      ℝ → (NeutralRates Deme Locus Allele × ℝ≥0) ⊕ PulseMatrix Deme
  | Sum.inl epoch, θ => Sum.inl (rateSegment epoch.1 epoch.2.1 θ, epoch.2.2)
  | Sum.inr pulse, _ => Sum.inr pulse

/-- The derivative of the propagator of a segment event at `θ₀`: the Duhamel derivative in the
direction `Q(second) - Q(first)` for an epoch, zero for a pulse. -/
def segmentDerivative (capacity : Locus → ℕ) (θ₀ : ℝ) :
    (NeutralRates Deme Locus Allele × NeutralRates Deme Locus Allele × ℝ≥0) ⊕ PulseMatrix Deme →
      Matrix (BudgetConfiguration Deme Locus Allele capacity)
        (BudgetConfiguration Deme Locus Allele capacity) ℝ
  | Sum.inl epoch =>
      duhamelDerivative (dualGenerator (rateSegment epoch.1 epoch.2.1 θ₀) capacity)
        (dualGenerator epoch.2.1 capacity - dualGenerator epoch.1 capacity) epoch.2.2
  | Sum.inr _ => 0

/-- Every event propagator of a segment history is differentiable at an interior parameter. -/
theorem hasDerivAt_eventPropagator_segmentEvent (capacity : Locus → ℕ) {θ₀ : ℝ}
    (hθ₀ : θ₀ ∈ Set.Ioo (0 : ℝ) 1) :
    ∀ (event : (NeutralRates Deme Locus Allele × NeutralRates Deme Locus Allele × ℝ≥0)
        ⊕ PulseMatrix Deme) (ξ η : BudgetConfiguration Deme Locus Allele capacity),
      HasDerivAt (fun θ ↦ eventPropagator capacity (segmentEvent event θ) ξ η)
        (segmentDerivative capacity θ₀ event ξ η) θ₀
  | Sum.inl epoch, ξ, η =>
      hasDerivAt_eventPropagator_epoch capacity
        (hasDerivAt_dualGenerator_rateSegment epoch.1 epoch.2.1 capacity hθ₀) epoch.2.2 ξ η
  | Sum.inr pulse, ξ, η => hasDerivAt_eventPropagator_pulse capacity pulse θ₀ ξ η

/-- The derivative of a segment event propagator, read by Mathlib's `deriv`. -/
theorem deriv_eventPropagator_segmentEvent (capacity : Locus → ℕ) {θ₀ : ℝ}
    (hθ₀ : θ₀ ∈ Set.Ioo (0 : ℝ) 1)
    (event : (NeutralRates Deme Locus Allele × NeutralRates Deme Locus Allele × ℝ≥0)
      ⊕ PulseMatrix Deme) (ξ η : BudgetConfiguration Deme Locus Allele capacity) :
    deriv (fun θ ↦ eventPropagator capacity (segmentEvent event θ) ξ η) θ₀
      = segmentDerivative capacity θ₀ event ξ η :=
  (hasDerivAt_eventPropagator_segmentEvent capacity hθ₀ event ξ η).deriv

/-- The event derivatives of a history of event families, read by `deriv` at `θ₀`. -/
def familyDerivative (capacity : Locus → ℕ) (θ₀ : ℝ)
    (event : ℝ → (NeutralRates Deme Locus Allele × ℝ≥0) ⊕ PulseMatrix Deme) :
    Matrix (BudgetConfiguration Deme Locus Allele capacity)
      (BudgetConfiguration Deme Locus Allele capacity) ℝ :=
  fun ξ η ↦ deriv (fun θ ↦ eventPropagator capacity (event θ) ξ η) θ₀

/-- The event families of a segment history have their `deriv` derivatives at an interior
parameter. -/
theorem hasDerivAt_familyDerivative_segmentHistory (capacity : Locus → ℕ) {θ₀ : ℝ}
    (hθ₀ : θ₀ ∈ Set.Ioo (0 : ℝ) 1)
    (history : List ((NeutralRates Deme Locus Allele × NeutralRates Deme Locus Allele × ℝ≥0)
      ⊕ PulseMatrix Deme)) :
    ∀ event ∈ history.map segmentEvent, ∀ ξ η,
      HasDerivAt (fun θ ↦ eventPropagator capacity (event θ) ξ η)
        (familyDerivative capacity θ₀ event ξ η) θ₀ := by
  intro event hevent ξ η
  obtain ⟨segment, _, rfl⟩ := List.mem_map.mp hevent
  exact (hasDerivAt_eventPropagator_segmentEvent capacity hθ₀ segment ξ η).differentiableAt
    |>.hasDerivAt

/-- **The exact sensitivity law along a segment history, with no hypothesis.**  At every interior
parameter, `c · U(θ) v` for the propagator of a history of segment epochs and fixed pulses has
derivative the stagewise sensitivity of its event derivatives. -/
theorem hasDerivAt_dotProduct_segmentHistory (capacity : Locus → ℕ) {θ₀ : ℝ}
    (hθ₀ : θ₀ ∈ Set.Ioo (0 : ℝ) 1)
    (history : List ((NeutralRates Deme Locus Allele × NeutralRates Deme Locus Allele × ℝ≥0)
      ⊕ PulseMatrix Deme))
    (c v : BudgetConfiguration Deme Locus Allele capacity → ℝ) :
    HasDerivAt (fun θ ↦ c ⬝ᵥ
        (historyEventPropagator capacity ((history.map segmentEvent).map fun event ↦ event θ)
          *ᵥ v))
      (historySensitivity capacity θ₀ (history.map segmentEvent) (familyDerivative capacity θ₀)
        c v) θ₀ :=
  hasDerivAt_dotProduct_historyEventPropagator capacity (history.map segmentEvent)
    (familyDerivative capacity θ₀) (hasDerivAt_familyDerivative_segmentHistory capacity hθ₀ history)
    c v

/-! ## The metrics along a segment history -/

/-- **The sensitivity of expected portability along a segment history**, with no differentiability
hypothesis, wherever `E D_t E N_s ≠ 0`. -/
theorem hasDerivAt_expectedPortability_segmentHistory (ℓ₀ : Locus)
    (hap₀ : FullHaplotype Locus Allele) {θ₀ : ℝ} (hθ₀ : θ₀ ∈ Set.Ioo (0 : ℝ) 1)
    (history : List ((NeutralRates Deme Locus Allele × NeutralRates Deme Locus Allele × ℝ≥0)
      ⊕ PulseMatrix Deme))
    (x0 : FrequencyState Deme Locus Allele) (source target : Deme)
    (score outcome : FullHaplotype Locus Allele → ℝ)
    (hdenominator : (∫ y, correlationDenominator (stateLaw y target) score outcome
          ∂(historyEventKernel ℓ₀ hap₀ ((history.map segmentEvent).map fun event ↦ event θ₀) x0))
        * (∫ y, correlationNumerator (stateLaw y source) score outcome
          ∂(historyEventKernel ℓ₀ hap₀ ((history.map segmentEvent).map fun event ↦ event θ₀) x0))
        ≠ 0) :
    HasDerivAt (fun θ ↦ expectedPortability
        (historyEventKernel ℓ₀ hap₀ ((history.map segmentEvent).map fun event ↦ event θ)) x0
        source target score outcome)
      (crossRatioDerivative
        (∫ y, correlationNumerator (stateLaw y target) score outcome
          ∂(historyEventKernel ℓ₀ hap₀ ((history.map segmentEvent).map fun event ↦ event θ₀) x0))
        (∫ y, correlationDenominator (stateLaw y source) score outcome
          ∂(historyEventKernel ℓ₀ hap₀ ((history.map segmentEvent).map fun event ↦ event θ₀) x0))
        (∫ y, correlationDenominator (stateLaw y target) score outcome
          ∂(historyEventKernel ℓ₀ hap₀ ((history.map segmentEvent).map fun event ↦ event θ₀) x0))
        (∫ y, correlationNumerator (stateLaw y source) score outcome
          ∂(historyEventKernel ℓ₀ hap₀ ((history.map segmentEvent).map fun event ↦ event θ₀) x0))
        (historySensitivity (fun _ ↦ 4) θ₀ (history.map segmentEvent)
          (familyDerivative (fun _ ↦ 4) θ₀)
          (budgetCoefficients ℓ₀ (fun _ ↦ 4) (numeratorPolynomial target score outcome))
          (budgetMomentFeature (fun _ ↦ 4) x0))
        (historySensitivity (fun _ ↦ 4) θ₀ (history.map segmentEvent)
          (familyDerivative (fun _ ↦ 4) θ₀)
          (budgetCoefficients ℓ₀ (fun _ ↦ 4) (denominatorPolynomial source score outcome))
          (budgetMomentFeature (fun _ ↦ 4) x0))
        (historySensitivity (fun _ ↦ 4) θ₀ (history.map segmentEvent)
          (familyDerivative (fun _ ↦ 4) θ₀)
          (budgetCoefficients ℓ₀ (fun _ ↦ 4) (denominatorPolynomial target score outcome))
          (budgetMomentFeature (fun _ ↦ 4) x0))
        (historySensitivity (fun _ ↦ 4) θ₀ (history.map segmentEvent)
          (familyDerivative (fun _ ↦ 4) θ₀)
          (budgetCoefficients ℓ₀ (fun _ ↦ 4) (numeratorPolynomial source score outcome))
          (budgetMomentFeature (fun _ ↦ 4) x0))) θ₀ :=
  hasDerivAt_expectedPortability_historyEventKernel ℓ₀ hap₀ (history.map segmentEvent)
    (familyDerivative (fun _ ↦ 4) θ₀)
    (hasDerivAt_familyDerivative_segmentHistory (fun _ ↦ 4) hθ₀ history) x0 source target score
    outcome hdenominator

/-- **The sensitivity of calibration portability along a segment history**, at every budget
`n ≥ 2`, with no differentiability hypothesis, wherever `E V_t E C_s ≠ 0`. -/
theorem hasDerivAt_expectedCalibrationPortability_segmentHistory (ℓ₀ : Locus)
    (hap₀ : FullHaplotype Locus Allele) {n : ℕ} (hn : 2 ≤ n) {θ₀ : ℝ}
    (hθ₀ : θ₀ ∈ Set.Ioo (0 : ℝ) 1)
    (history : List ((NeutralRates Deme Locus Allele × NeutralRates Deme Locus Allele × ℝ≥0)
      ⊕ PulseMatrix Deme))
    (x0 : FrequencyState Deme Locus Allele) (source target : Deme)
    (score outcome : FullHaplotype Locus Allele → ℝ)
    (hdenominator : (∫ y, (stateLaw y target).variance score
          ∂(historyEventKernel ℓ₀ hap₀ ((history.map segmentEvent).map fun event ↦ event θ₀) x0))
        * (∫ y, (stateLaw y source).covariance score outcome
          ∂(historyEventKernel ℓ₀ hap₀ ((history.map segmentEvent).map fun event ↦ event θ₀) x0))
        ≠ 0) :
    HasDerivAt (fun θ ↦ expectedCalibrationPortability
        (historyEventKernel ℓ₀ hap₀ ((history.map segmentEvent).map fun event ↦ event θ)) x0
        source target score outcome)
      (crossRatioDerivative
        (∫ y, (stateLaw y target).covariance score outcome
          ∂(historyEventKernel ℓ₀ hap₀ ((history.map segmentEvent).map fun event ↦ event θ₀) x0))
        (∫ y, (stateLaw y source).variance score
          ∂(historyEventKernel ℓ₀ hap₀ ((history.map segmentEvent).map fun event ↦ event θ₀) x0))
        (∫ y, (stateLaw y target).variance score
          ∂(historyEventKernel ℓ₀ hap₀ ((history.map segmentEvent).map fun event ↦ event θ₀) x0))
        (∫ y, (stateLaw y source).covariance score outcome
          ∂(historyEventKernel ℓ₀ hap₀ ((history.map segmentEvent).map fun event ↦ event θ₀) x0))
        (historySensitivity (fun _ ↦ n) θ₀ (history.map segmentEvent)
          (familyDerivative (fun _ ↦ n) θ₀)
          (budgetCoefficients ℓ₀ (fun _ ↦ n) (demeCovariancePolynomial target score outcome))
          (budgetMomentFeature (fun _ ↦ n) x0))
        (historySensitivity (fun _ ↦ n) θ₀ (history.map segmentEvent)
          (familyDerivative (fun _ ↦ n) θ₀)
          (budgetCoefficients ℓ₀ (fun _ ↦ n) (demeCovariancePolynomial source score score))
          (budgetMomentFeature (fun _ ↦ n) x0))
        (historySensitivity (fun _ ↦ n) θ₀ (history.map segmentEvent)
          (familyDerivative (fun _ ↦ n) θ₀)
          (budgetCoefficients ℓ₀ (fun _ ↦ n) (demeCovariancePolynomial target score score))
          (budgetMomentFeature (fun _ ↦ n) x0))
        (historySensitivity (fun _ ↦ n) θ₀ (history.map segmentEvent)
          (familyDerivative (fun _ ↦ n) θ₀)
          (budgetCoefficients ℓ₀ (fun _ ↦ n) (demeCovariancePolynomial source score outcome))
          (budgetMomentFeature (fun _ ↦ n) x0))) θ₀ :=
  hasDerivAt_expectedCalibrationPortability_historyEventKernel ℓ₀ hap₀ hn
    (history.map segmentEvent) (familyDerivative (fun _ ↦ n) θ₀)
    (hasDerivAt_familyDerivative_segmentHistory (fun _ ↦ n) hθ₀ history) x0 source target score
    outcome hdenominator

/-- **The sensitivity of AUC portability along a segment history**, with no differentiability
hypothesis, wherever `E D_t E N_s ≠ 0` for the AUC components. -/
theorem hasDerivAt_expectedAUCPortability_segmentHistory (ℓ₀ : Locus)
    (hap₀ : FullHaplotype Locus Allele) {θ₀ : ℝ} (hθ₀ : θ₀ ∈ Set.Ioo (0 : ℝ) 1)
    (history : List ((NeutralRates Deme Locus Allele × NeutralRates Deme Locus Allele × ℝ≥0)
      ⊕ PulseMatrix Deme))
    (x0 : FrequencyState Deme Locus Allele) (source target : Deme)
    (score : FullHaplotype Locus Allele → ℝ) (outcome : FullHaplotype Locus Allele → Bool)
    (hdenominator : (∫ y, aucDenominator (stateLaw y target) outcome
          ∂(historyEventKernel ℓ₀ hap₀ ((history.map segmentEvent).map fun event ↦ event θ₀) x0))
        * (∫ y, aucNumerator (stateLaw y source) score outcome
          ∂(historyEventKernel ℓ₀ hap₀ ((history.map segmentEvent).map fun event ↦ event θ₀) x0))
        ≠ 0) :
    HasDerivAt (fun θ ↦ expectedAUCPortability
        (historyEventKernel ℓ₀ hap₀ ((history.map segmentEvent).map fun event ↦ event θ)) x0
        source target score outcome)
      (crossRatioDerivative
        (∫ y, aucNumerator (stateLaw y target) score outcome
          ∂(historyEventKernel ℓ₀ hap₀ ((history.map segmentEvent).map fun event ↦ event θ₀) x0))
        (∫ y, aucDenominator (stateLaw y source) outcome
          ∂(historyEventKernel ℓ₀ hap₀ ((history.map segmentEvent).map fun event ↦ event θ₀) x0))
        (∫ y, aucDenominator (stateLaw y target) outcome
          ∂(historyEventKernel ℓ₀ hap₀ ((history.map segmentEvent).map fun event ↦ event θ₀) x0))
        (∫ y, aucNumerator (stateLaw y source) score outcome
          ∂(historyEventKernel ℓ₀ hap₀ ((history.map segmentEvent).map fun event ↦ event θ₀) x0))
        (historySensitivity (fun _ ↦ 2) θ₀ (history.map segmentEvent)
          (familyDerivative (fun _ ↦ 2) θ₀)
          (budgetCoefficients ℓ₀ (fun _ ↦ 2)
            (demePolynomial target (aucNumeratorPolynomial score outcome)))
          (budgetMomentFeature (fun _ ↦ 2) x0))
        (historySensitivity (fun _ ↦ 2) θ₀ (history.map segmentEvent)
          (familyDerivative (fun _ ↦ 2) θ₀)
          (budgetCoefficients ℓ₀ (fun _ ↦ 2)
            (demePolynomial source (aucDenominatorPolynomial outcome)))
          (budgetMomentFeature (fun _ ↦ 2) x0))
        (historySensitivity (fun _ ↦ 2) θ₀ (history.map segmentEvent)
          (familyDerivative (fun _ ↦ 2) θ₀)
          (budgetCoefficients ℓ₀ (fun _ ↦ 2)
            (demePolynomial target (aucDenominatorPolynomial outcome)))
          (budgetMomentFeature (fun _ ↦ 2) x0))
        (historySensitivity (fun _ ↦ 2) θ₀ (history.map segmentEvent)
          (familyDerivative (fun _ ↦ 2) θ₀)
          (budgetCoefficients ℓ₀ (fun _ ↦ 2)
            (demePolynomial source (aucNumeratorPolynomial score outcome)))
          (budgetMomentFeature (fun _ ↦ 2) x0))) θ₀ :=
  hasDerivAt_expectedAUCPortability_historyEventKernel ℓ₀ hap₀ (history.map segmentEvent)
    (familyDerivative (fun _ ↦ 2) θ₀)
    (hasDerivAt_familyDerivative_segmentHistory (fun _ ↦ 2) hθ₀ history) x0 source target score
    outcome hdenominator

end

end Descent.Portability.EndToEndSensitivityRates
