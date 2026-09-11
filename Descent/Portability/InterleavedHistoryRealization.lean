/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.IntegrableRateRealization
import Descent.Portability.PulseHistoryRealization

assert_below Descent.Decision Descent.Program

/-!
# Realizability under interleaved integrable rate histories, splits and pulses

NOTE1 section 2.4 lets finitely many instantaneous demographic events interleave with
time-varying rate histories, and NOTE1 Theorem 2 covers any instantaneous map whose pullback on
the features has been identified.  The ingredients are proved separately in the corpus:
`IntegrableRateHistoryRealization.propagateSegments_preserves_locusExchangeable_realization`
for rate histories with a continuous generator interleaved with splits,
`IntegrableRateRealization.integrableRateHistory_preserves_locusExchangeable_realization` for
one rate history whose rate coordinates are integrable, and
`PulseHistoryRealization.locusExchangeablePulse` for an admixture pulse.  This module composes
them.

`integrablePropagator rates hT hintegrable` is the continuous solution of the integral equation
`U(t) = 1 + ∫₀ᵗ A(s) U(s) ds` that the integrable theorem constructs, chosen once.
`integrablePropagator_eq_integral` records the equation, `integrablePropagator_unique` that every
continuous solution agrees with it on the horizon, and
`integrablePropagator_preserves_locusExchangeable_realization` the realizability readout.

`InterleavedSegment` is one segment of a piecewise history: a segment of
`IntegrableRateHistoryRealization`, that is a rate history with continuous generator or a split;
a rate history with integrable rate coordinates over its own horizon; or an admixture pulse.
`propagateInterleaved_preserves_locusExchangeable_realization` says every finite list of
segments carries a locus-exchangeably realizable stored state to a locus-exchangeably realizable
one, and `propagateInterleaved_dd_quadraticForm_nonneg` is its positive-semidefinite readout.
`InterleavedSegment.apply_segment` ties the embedded segments to `HistorySegment.apply`.

Scope.  Countably many events are not covered; NOTE1 itself says an accumulation of events needs
a separately specified convergent product.  Instantaneous maps other than splits and pulses are
not covered.

## Empirical status

None.  The bodies here compose linear maps along a finite list and read off membership in a set
of realizable states, so no measurement can bear on them.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.InterleavedHistoryRealization

open Coalescent
open MeasureTheory
open Descent.Portability.IntegrableRateHistoryRealization
open Descent.Portability.IntegrableRateRealization
open Descent.Portability.PulseHistoryRealization
open Descent.Portability.RateGeneratorLipschitz
open scoped Matrix.Norms.Operator

noncomputable section

/-! ## The propagator of an integrable rate history -/

/-- The propagator of a rate history whose rate coordinates are integrable on `[0, T]`: the
continuous solution of `U(t) = 1 + ∫₀ᵗ A(s) U(s) ds` with the corpus generator of the rate law at
each time, as constructed by the integrable-rate theorem. -/
def integrablePropagator {D : ℕ} (rates : ℝ → ManyDemeLDRates D) {T : ℝ} (hT : 0 ≤ T)
    (hintegrable : IntervalIntegrable (fun t ↦ rateCoordinates (rates t)) volume 0 T) :
    ℝ → Matrix (AffineLowOrderLDCoordinate D) (AffineLowOrderLDCoordinate D) ℝ :=
  Classical.choose
    (integrableRateHistory_preserves_locusExchangeable_realization rates hT hintegrable)

/-- The propagator of an integrable rate history is continuous. -/
theorem continuous_integrablePropagator {D : ℕ} (rates : ℝ → ManyDemeLDRates D) {T : ℝ}
    (hT : 0 ≤ T)
    (hintegrable : IntervalIntegrable (fun t ↦ rateCoordinates (rates t)) volume 0 T) :
    Continuous (integrablePropagator rates hT hintegrable) :=
  (Classical.choose_spec
    (integrableRateHistory_preserves_locusExchangeable_realization rates hT hintegrable)).1

/-- The propagator of an integrable rate history solves the integral equation on the
horizon. -/
theorem integrablePropagator_eq_integral {D : ℕ} (rates : ℝ → ManyDemeLDRates D) {T : ℝ}
    (hT : 0 ≤ T)
    (hintegrable : IntervalIntegrable (fun t ↦ rateCoordinates (rates t)) volume 0 T)
    {t : ℝ} (ht : t ∈ Set.Icc 0 T) :
    integrablePropagator rates hT hintegrable t =
      1 + ∫ s in (0 : ℝ)..t,
        augmentedLowOrderLDGenerator (rates s) * integrablePropagator rates hT hintegrable s :=
  (Classical.choose_spec
    (integrableRateHistory_preserves_locusExchangeable_realization rates hT hintegrable)).2.1 t ht

/-- Every continuous solution of the integral equation agrees with the propagator on the
horizon. -/
theorem integrablePropagator_unique {D : ℕ} (rates : ℝ → ManyDemeLDRates D) {T : ℝ}
    (hT : 0 ≤ T)
    (hintegrable : IntervalIntegrable (fun t ↦ rateCoordinates (rates t)) volume 0 T)
    (other : ℝ → Matrix (AffineLowOrderLDCoordinate D) (AffineLowOrderLDCoordinate D) ℝ)
    (hother : Continuous other)
    (hequation : ∀ t ∈ Set.Icc 0 T,
      other t = 1 + ∫ s in (0 : ℝ)..t, augmentedLowOrderLDGenerator (rates s) * other s)
    {t : ℝ} (ht : t ∈ Set.Icc 0 T) :
    other t = integrablePropagator rates hT hintegrable t :=
  (Classical.choose_spec
    (integrableRateHistory_preserves_locusExchangeable_realization rates hT hintegrable)).2.2.1
      other hother hequation t ht

/-- The propagator of an integrable rate history carries a locus-exchangeably realizable stored
state to a locus-exchangeably realizable one. -/
theorem integrablePropagator_preserves_locusExchangeable_realization {D : ℕ}
    (rates : ℝ → ManyDemeLDRates D) {T : ℝ} (hT : 0 ≤ T)
    (hintegrable : IntervalIntegrable (fun t ↦ rateCoordinates (rates t)) volume 0 T)
    {state : AffineLowOrderLDCoordinate D → ℝ}
    (realization : LocusExchangeableLowOrderLDHaplotypeRealization state) :
    Nonempty (LocusExchangeableLowOrderLDHaplotypeRealization
      ((integrablePropagator rates hT hintegrable T).mulVec state)) :=
  (Classical.choose_spec
    (integrableRateHistory_preserves_locusExchangeable_realization rates hT hintegrable)).2.2.2
      realization

/-! ## Interleaved segments -/

/-- One segment of a piecewise history: a segment of `IntegrableRateHistoryRealization`, which is
a rate history with continuous generator or a split; a rate history with integrable rate
coordinates over its own horizon; or an admixture pulse of fraction `alpha` from `source` into
`recipient`. -/
inductive InterleavedSegment (D : ℕ) where
  /-- A rate history with continuous generator, or a split. -/
  | segment (event : HistorySegment D)
  /-- A rate history whose rate coordinates are integrable over `[0, horizon]`. -/
  | integrable (rates : ℝ → ManyDemeLDRates D) (horizon : ℝ) (horizon_nonneg : 0 ≤ horizon)
      (hintegrable :
        IntervalIntegrable (fun t ↦ rateCoordinates (rates t)) volume 0 horizon)
  /-- An admixture pulse of fraction `alpha` from `source` into `recipient`. -/
  | pulse (alpha : ℝ) (alpha_nonneg : 0 ≤ alpha) (alpha_le_one : alpha ≤ 1)
      (source recipient : Fin D)

/-- The linear map one segment applies to the stored low-order state: the map of the embedded
segment, the propagator of the integrable rate history at its horizon, or the pulse matrix. -/
def InterleavedSegment.apply {D : ℕ} :
    InterleavedSegment D →
      (AffineLowOrderLDCoordinate D → ℝ) → AffineLowOrderLDCoordinate D → ℝ
  | .segment event, state => event.apply state
  | .integrable rates horizon horizon_nonneg hintegrable, state =>
      (integrablePropagator rates horizon_nonneg hintegrable horizon).mulVec state
  | .pulse alpha _ _ source recipient, state =>
      (lowOrderLDPulseTransform alpha source recipient).mulVec state

/-- A pulse of fraction zero from the first deme into itself, a segment carrying no
hypothesis. -/
def identityPulseSegment : InterleavedSegment 1 :=
  .pulse 0 le_rfl zero_le_one 0 0

/-- An embedded segment applies exactly the map of `HistorySegment.apply`. -/
theorem InterleavedSegment.apply_segment {D : ℕ} (event : HistorySegment D)
    (state : AffineLowOrderLDCoordinate D → ℝ) :
    (InterleavedSegment.segment event).apply state = event.apply state :=
  rfl

/-- **Every segment preserves locus-exchangeable realizability.**  An embedded segment is the
continuous-rate theorem or a split, an integrable rate history is the integrable-rate theorem, and
a pulse is the transformed witness. -/
theorem InterleavedSegment.preserves_locusExchangeable_realization {D : ℕ}
    (segment : InterleavedSegment D) {state : AffineLowOrderLDCoordinate D → ℝ}
    (realization : LocusExchangeableLowOrderLDHaplotypeRealization state) :
    Nonempty (LocusExchangeableLowOrderLDHaplotypeRealization (segment.apply state)) := by
  cases segment with
  | segment event =>
      exact propagateSegments_preserves_locusExchangeable_realization [event] realization
  | integrable rates horizon horizon_nonneg hintegrable =>
      exact integrablePropagator_preserves_locusExchangeable_realization rates horizon_nonneg
        hintegrable realization
  | pulse alpha alpha_nonneg alpha_le_one source recipient =>
      exact ⟨locusExchangeablePulse realization alpha alpha_nonneg alpha_le_one source
        recipient⟩

/-- The stored low-order state after a finite list of segments, applied in order. -/
def propagateInterleaved {D : ℕ} (segments : List (InterleavedSegment D))
    (state : AffineLowOrderLDCoordinate D → ℝ) : AffineLowOrderLDCoordinate D → ℝ :=
  segments.foldl (fun current segment ↦ segment.apply current) state

/-- **NOTE1 section 2.4 with integrable rates, splits and pulses.**  Every finite list of rate
histories with continuous generators, rate histories with integrable rate coordinates,
physically realized splits and admixture pulses carries a locus-exchangeably realizable stored
state to a locus-exchangeably realizable one. -/
theorem propagateInterleaved_preserves_locusExchangeable_realization {D : ℕ}
    (segments : List (InterleavedSegment D)) {state : AffineLowOrderLDCoordinate D → ℝ}
    (realization : LocusExchangeableLowOrderLDHaplotypeRealization state) :
    Nonempty (LocusExchangeableLowOrderLDHaplotypeRealization
      (propagateInterleaved segments state)) := by
  induction segments generalizing state with
  | nil => exact ⟨realization⟩
  | cons head rest ih =>
      obtain ⟨propagated⟩ := head.preserves_locusExchangeable_realization realization
      exact ih propagated

/-- After every finite list of interleaved segments the propagated `DD` block is positive
semidefinite under the common propagated haplotype law. -/
theorem propagateInterleaved_dd_quadraticForm_nonneg {D : ℕ}
    (segments : List (InterleavedSegment D)) {state : AffineLowOrderLDCoordinate D → ℝ}
    (realization : LocusExchangeableLowOrderLDHaplotypeRealization state)
    (weight : Fin D → ℝ) :
    0 ≤ ∑ first, ∑ second, weight first *
      propagateInterleaved segments state (some (.DD first second)) * weight second := by
  obtain ⟨propagated⟩ :=
    propagateInterleaved_preserves_locusExchangeable_realization segments realization
  exact propagated.toLowOrderLDHaplotypeRealization.toDDDRealization.dd_quadraticForm_nonneg
    weight

end

end Descent.Portability.InterleavedHistoryRealization
