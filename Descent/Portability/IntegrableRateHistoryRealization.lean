/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.EulerInvariantSet
import Descent.Portability.LinearFundamentalMatrix
import Descent.Portability.TwoLocusMicroscopicApproximation

assert_below Descent.Decision Descent.Program

/-!
# Locus-exchangeable realizability under time-varying rate histories

NOTE1 section 2.4 removes the restriction to piecewise-constant rates: for a finite number of
demes on a finite horizon, the fundamental matrix of the time-varying low-order system carries
every realizable state to a realizable one.  Its argument approximates the rates by nonnegative
step functions, bounds propagator differences by a constant times the `L¹` difference of the
generators, and passes body preservation to the limit.  This module carries that argument out
for rate histories whose corpus generator depends continuously on time.

`generatorPath rates T` is the corpus generator `augmentedLowOrderLDGenerator` of the rate law at
each time, with time clamped into the horizon, and `rateHistoryPropagator rates T` is its
fundamental matrix at `T` from `Descent.Portability.LinearFundamentalMatrix`.
`hasDerivWithinAt_rateHistory` is NOTE1's `U' = A(t) U` on the horizon, with `A(t)` the corpus
generator at time `t`, and `fundamentalMatrix_generatorPath_zero` is `U(0) = 1`.
`rateHistoryPropagator_const` shows that a constant history recovers the corpus epoch.

The realizability theorem.  `sampledRateEvents` lists the rate epochs of the left-endpoint
sampling of the history at step `T / n`, and `propagate_sampledRateEvents` identifies their
compiled instruction list with the sampled epoch product of the fundamental-matrix module.  Each
such list preserves locus-exchangeable realizability by NOTE1 Theorem 2,
`propagate_preserves_locusExchangeable_realization`.  `exchangeableStates` is the set of stored
states whose locus-exchangeable embedding lies in the enlarged realization body; it is closed by
the closedness of that body, and it is exactly the set of locus-exchangeably realizable states.
The sampled products converge to the propagator (`tendsto_sampledProduct`), so
`rateHistory_preserves_locusExchangeable_realization` says every initial
`LocusExchangeableLowOrderLDHaplotypeRealization` remains realizable after the whole history,
with no hypothesis beyond the continuity of the generator path.
`rateHistoryPropagator_mulVec_mem_realizationBody` and
`rateHistoryPropagator_dd_quadraticForm_nonneg` are the body and positive-semidefinite readouts.

The quantitative ingredients of NOTE1 section 2.4 are recorded at the level of rate histories.
`norm_rateHistoryPropagator_sub_le` is the variation-of-constants bound: two such histories
bounded by `K` on the horizon have propagators within `e^{2 K T}` times the `L¹` distance of their
generators.  `eventually_integral_norm_sampledGenerator_sub_le` is the step approximation: the
generators of the left-endpoint sampled rate laws, each a genuine nonnegative `ManyDemeLDRates`,
converge to the history's generator in `L¹([0, T])`.

NOTE1 section 2.4 also interleaves finite instantaneous events.  `HistorySegment` is one segment
of a piecewise history, either such a continuous rate history over its own horizon or a
physically realized split, and `propagateSegments_preserves_locusExchangeable_realization` says
every finite list of segments preserves locus-exchangeable realizability.  The rates may jump
between consecutive segments, so piecewise-continuous histories with finitely many rate changes
and splits are covered.

Scope.  Within a segment the rates are assumed to have a continuous generator on the horizon.
Measurable rates with merely integrable norm, NOTE1's full hypothesis, are not
formalized: their fundamental matrix solves the equation only almost everywhere, and neither
that Carathéodory existence theory nor the approximation of such rates by step functions is
available here.  Uniqueness of the solution of `U' = A(t) U` is not proved.

## Empirical status

None.  The bodies here are algebra and point-set topology: products of matrix exponentials, a
limit in a finite-dimensional space, and membership in a closed convex set.  No measurement can
bear on whether a closed set is carried into itself.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.IntegrableRateHistoryRealization

open Coalescent
open Descent.Portability.RealizationBody
open Descent.Portability.EnlargedLowOrderLDGenerator
open Descent.Portability.LinearFundamentalMatrix
open Descent.Portability.TwoLocusMicroscopicApproximation
open scoped Matrix.Norms.Operator

noncomputable section

/-! ## The generator path of a rate history -/

/-- The generator path of a rate history on the horizon `[0, T]`: the corpus generator of the
rate law at each time, with time clamped into the horizon. -/
def generatorPath {D : ℕ} (rates : ℝ → ManyDemeLDRates D) (T : ℝ) :
    ℝ → Matrix (AffineLowOrderLDCoordinate D) (AffineLowOrderLDCoordinate D) ℝ :=
  fun t ↦ augmentedLowOrderLDGenerator (rates (clampTime T t))

/-- Inside the horizon the generator path is the corpus generator of the rate law. -/
theorem generatorPath_of_mem {D : ℕ} (rates : ℝ → ManyDemeLDRates D) {T t : ℝ}
    (ht : t ∈ Set.Icc 0 T) :
    generatorPath rates T t = augmentedLowOrderLDGenerator (rates t) := by
  rw [generatorPath, clampTime_of_mem ht]

/-- A generator continuous on the horizon gives a continuous generator path on the line. -/
theorem continuous_generatorPath {D : ℕ} {rates : ℝ → ManyDemeLDRates D} {T : ℝ} (hT : 0 ≤ T)
    (hcontinuous :
      ContinuousOn (fun t ↦ augmentedLowOrderLDGenerator (rates t)) (Set.Icc 0 T)) :
    Continuous (generatorPath rates T) :=
  hcontinuous.comp_continuous (continuous_clampTime T) (clampTime_mem hT)

/-- A generator continuous on the compact horizon is bounded there. -/
theorem exists_generatorPath_bound {D : ℕ} {rates : ℝ → ManyDemeLDRates D} {T : ℝ}
    (hT : 0 ≤ T)
    (hcontinuous :
      ContinuousOn (fun t ↦ augmentedLowOrderLDGenerator (rates t)) (Set.Icc 0 T)) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ s ∈ Set.Icc 0 T, ‖generatorPath rates T s‖ ≤ K := by
  obtain ⟨maximizer, _, hmax⟩ := isCompact_Icc.exists_isMaxOn (Set.nonempty_Icc.mpr hT)
    (continuous_generatorPath hT hcontinuous).norm.continuousOn
  exact ⟨‖generatorPath rates T maximizer‖, norm_nonneg _, fun s hs ↦ isMaxOn_iff.mp hmax s hs⟩

/-- The propagator of a rate history over `[0, T]`: the fundamental matrix of its generator path
at the horizon. -/
def rateHistoryPropagator {D : ℕ} (rates : ℝ → ManyDemeLDRates D) (T : ℝ) :
    Matrix (AffineLowOrderLDCoordinate D) (AffineLowOrderLDCoordinate D) ℝ :=
  fundamentalMatrix (generatorPath rates T) T T

/-- The fundamental matrix of a rate history starts at the identity. -/
theorem fundamentalMatrix_generatorPath_zero {D : ℕ} (rates : ℝ → ManyDemeLDRates D) {T : ℝ}
    (hT : 0 ≤ T) : fundamentalMatrix (generatorPath rates T) T 0 = 1 :=
  fundamentalMatrix_zero _ hT

/-- **NOTE1 `U' = A(t) U` for a rate history.**  On the horizon the fundamental matrix of the
history has derivative within `[0, T]` equal to the corpus generator of the rate law at `t`
applied to it. -/
theorem hasDerivWithinAt_rateHistory {D : ℕ} {rates : ℝ → ManyDemeLDRates D} {T : ℝ}
    (hT : 0 ≤ T)
    (hcontinuous :
      ContinuousOn (fun t ↦ augmentedLowOrderLDGenerator (rates t)) (Set.Icc 0 T))
    {t : ℝ} (ht : t ∈ Set.Icc 0 T) :
    HasDerivWithinAt (fundamentalMatrix (generatorPath rates T) T)
      (augmentedLowOrderLDGenerator (rates t) * fundamentalMatrix (generatorPath rates T) T t)
      (Set.Icc 0 T) t := by
  obtain ⟨K, hK, hbound⟩ := exists_generatorPath_bound hT hcontinuous
  have hderiv := fundamentalMatrix_hasDerivWithinAt (continuous_generatorPath hT hcontinuous)
    hT hK hbound ht
  rwa [generatorPath_of_mem rates ht] at hderiv

/-- **Constant rates recover the corpus epoch.**  The propagator of the constant rate history at
a rate law over `[0, T]` is the propagator of the corpus epoch of that law, so the time-varying
propagator extends the epoch theorem rather than competing with it. -/
theorem rateHistoryPropagator_const {D : ℕ} (rates : ManyDemeLDRates D) {T : ℝ} (hT : 0 ≤ T) :
    rateHistoryPropagator (fun _ ↦ rates) T = (rates.epoch T hT).propagator :=
  fundamentalMatrix_const _ hT

/-! ## Sampled rate epochs -/

/-- The rate epochs of the left-endpoint sampling of a history at step `h`: `k` consecutive epochs
of duration `h` under the rate laws at the times `0, h, …, (k - 1) h`, clamped into the
horizon. -/
def sampledRateEvents {D : ℕ} (rates : ℝ → ManyDemeLDRates D) (T h : ℝ) (hh : 0 ≤ h) :
    ℕ → List (RateHistoryEvent D)
  | 0 => []
  | k + 1 => sampledRateEvents rates T h hh k ++
      [RateHistoryEvent.evolve (rates (clampTime T ((k : ℝ) * h))) h hh]

/-- The sampled rate epochs compile to the sampled epoch product of the generator path. -/
theorem propagate_sampledRateEvents {D : ℕ} (rates : ℝ → ManyDemeLDRates D) (T h : ℝ)
    (hh : 0 ≤ h) (state : AffineLowOrderLDCoordinate D → ℝ) :
    ∀ k : ℕ, propagateLowOrderLDInstructions
        ((sampledRateEvents rates T h hh k).map RateHistoryEvent.instruction) state =
      (sampledProduct (generatorPath rates T) h k).mulVec state
  | 0 => by
      simp [sampledRateEvents, sampledProduct, propagateLowOrderLDInstructions]
  | k + 1 => by
      rw [sampledRateEvents, List.map_append, propagateLowOrderLDInstructions_append,
        propagate_sampledRateEvents rates T h hh state k, sampledProduct,
        ← Matrix.mulVec_mulVec]
      rfl

/-! ## The closed set of locus-exchangeably realizable states -/

/-- The stored low-order states whose locus-exchangeable embedding lies in the enlarged
realization body. -/
def exchangeableStates (D : ℕ) : Set (AffineLowOrderLDCoordinate D → ℝ) :=
  {state | embedLowOrderLDState state ∈ realizationBody (enlargedLowOrderLDFeature (D := D))}

/-- The set of locus-exchangeably realizable states is closed. -/
theorem isClosed_exchangeableStates (D : ℕ) : IsClosed (exchangeableStates D) := by
  have hembed : Continuous (embedLowOrderLDState (D := D)) :=
    continuous_pi fun _ ↦ continuous_apply _
  exact (EnlargedBodyClosedness.isClosed_enlargedRealizationBody D).preimage hembed

/-- A state lies in the closed set exactly when it is locus-exchangeably realizable. -/
theorem mem_exchangeableStates_iff {D : ℕ} (state : AffineLowOrderLDCoordinate D → ℝ) :
    state ∈ exchangeableStates D ↔
      Nonempty (LocusExchangeableLowOrderLDHaplotypeRealization state) :=
  ⟨TwoLocusRealizabilityPreservation.nonempty_locusExchangeableRealization_of_embed_mem,
    fun ⟨realization⟩ ↦
      EnlargedBodyClosedness.embed_mem_enlargedRealizationBody_of_realization realization⟩

/-! ## NOTE1 section 2.4 -/

/-- **Every continuous rate history preserves locus-exchangeable realizability.**  For every
rate law depending on time with a continuous corpus generator on the horizon `[0, T]`, the
propagator of the history maps a locus-exchangeably realizable stored state to a
locus-exchangeably realizable one.  Every sampled epoch list preserves realizability by NOTE1
Theorem 2, the sampled products converge to the propagator, and the realizable states form a
closed set. -/
theorem rateHistory_preserves_locusExchangeable_realization {D : ℕ}
    (rates : ℝ → ManyDemeLDRates D) {T : ℝ} (hT : 0 ≤ T)
    (hcontinuous :
      ContinuousOn (fun t ↦ augmentedLowOrderLDGenerator (rates t)) (Set.Icc 0 T))
    {state : AffineLowOrderLDCoordinate D → ℝ}
    (realization : LocusExchangeableLowOrderLDHaplotypeRealization state) :
    Nonempty (LocusExchangeableLowOrderLDHaplotypeRealization
      ((rateHistoryPropagator rates T).mulVec state)) := by
  obtain ⟨K, hK, hbound⟩ := exists_generatorPath_bound hT hcontinuous
  have hlimit : Filter.Tendsto
      (fun n : ℕ ↦ (sampledProduct (generatorPath rates T) (T / n) n).mulVec state)
      Filter.atTop (nhds ((rateHistoryPropagator rates T).mulVec state)) :=
    ((EulerInvariantSet.mulVecMap state).continuous_of_finiteDimensional.tendsto _).comp
      (tendsto_sampledProduct (continuous_generatorPath hT hcontinuous) hT hK hbound)
  have hsampled : ∀ n : ℕ,
      (sampledProduct (generatorPath rates T) (T / n) n).mulVec state ∈ exchangeableStates D := by
    intro n
    have hstep : 0 ≤ T / n := div_nonneg hT (Nat.cast_nonneg n)
    obtain ⟨propagated⟩ := propagate_preserves_locusExchangeable_realization
      (sampledRateEvents rates T (T / n) hstep n) realization
    rw [propagate_sampledRateEvents] at propagated
    exact (mem_exchangeableStates_iff _).mpr ⟨propagated⟩
  exact (mem_exchangeableStates_iff _).mp
    ((isClosed_exchangeableStates D).mem_of_tendsto hlimit (Filter.Eventually.of_forall hsampled))

/-- The propagated state of a continuous rate history lies in the stored realization body. -/
theorem rateHistoryPropagator_mulVec_mem_realizationBody {D : ℕ}
    (rates : ℝ → ManyDemeLDRates D) {T : ℝ} (hT : 0 ≤ T)
    (hcontinuous :
      ContinuousOn (fun t ↦ augmentedLowOrderLDGenerator (rates t)) (Set.Icc 0 T))
    {state : AffineLowOrderLDCoordinate D → ℝ}
    (realization : LocusExchangeableLowOrderLDHaplotypeRealization state) :
    (rateHistoryPropagator rates T).mulVec state ∈ realizationBody (lowOrderLDFeature D) := by
  obtain ⟨propagated⟩ :=
    rateHistory_preserves_locusExchangeable_realization rates hT hcontinuous realization
  exact KernelRealizationPreservation.lowOrderLDState_mem_realizationBody_of_realization
    propagated.toLowOrderLDHaplotypeRealization

/-- The propagated `DD` block of a continuous rate history is positive semidefinite: every finite
linear combination of deme-specific linkage disequilibria has nonnegative second moment under
the common propagated haplotype law. -/
theorem rateHistoryPropagator_dd_quadraticForm_nonneg {D : ℕ}
    (rates : ℝ → ManyDemeLDRates D) {T : ℝ} (hT : 0 ≤ T)
    (hcontinuous :
      ContinuousOn (fun t ↦ augmentedLowOrderLDGenerator (rates t)) (Set.Icc 0 T))
    {state : AffineLowOrderLDCoordinate D → ℝ}
    (realization : LocusExchangeableLowOrderLDHaplotypeRealization state)
    (weight : Fin D → ℝ) :
    0 ≤ ∑ first, ∑ second, weight first *
      (rateHistoryPropagator rates T).mulVec state (some (.DD first second)) * weight second := by
  obtain ⟨propagated⟩ :=
    rateHistory_preserves_locusExchangeable_realization rates hT hcontinuous realization
  exact propagated.toLowOrderLDHaplotypeRealization.toDDDRealization.dd_quadraticForm_nonneg
    weight

/-! ## Quantitative ingredients -/

/-- **Variation of constants for rate histories.**  Two continuous rate histories whose
generators are bounded by `K` on the horizon have propagators within `e^{2 K T}` times the `L¹`
distance of their generators on `[0, T]`. -/
theorem norm_rateHistoryPropagator_sub_le {D : ℕ} {rates other : ℝ → ManyDemeLDRates D}
    {T K : ℝ} (hT : 0 ≤ T) (hK : 0 ≤ K)
    (hcontinuous :
      ContinuousOn (fun t ↦ augmentedLowOrderLDGenerator (rates t)) (Set.Icc 0 T))
    (hother : ContinuousOn (fun t ↦ augmentedLowOrderLDGenerator (other t)) (Set.Icc 0 T))
    (hbound : ∀ s ∈ Set.Icc 0 T, ‖augmentedLowOrderLDGenerator (rates s)‖ ≤ K)
    (hboundOther : ∀ s ∈ Set.Icc 0 T, ‖augmentedLowOrderLDGenerator (other s)‖ ≤ K) :
    ‖rateHistoryPropagator rates T - rateHistoryPropagator other T‖ ≤
      (∫ u in (0 : ℝ)..T,
        ‖augmentedLowOrderLDGenerator (rates u) - augmentedLowOrderLDGenerator (other u)‖) *
        Real.exp (2 * K * T) := by
  have hpathBound : ∀ s ∈ Set.Icc 0 T, ‖generatorPath rates T s‖ ≤ K := fun s hs ↦ by
    rw [generatorPath_of_mem rates hs]
    exact hbound s hs
  have hotherBound : ∀ s ∈ Set.Icc 0 T, ‖generatorPath other T s‖ ≤ K := fun s hs ↦ by
    rw [generatorPath_of_mem other hs]
    exact hboundOther s hs
  have hdistance : (∫ u in (0 : ℝ)..T, ‖generatorPath rates T u - generatorPath other T u‖) =
      ∫ u in (0 : ℝ)..T,
        ‖augmentedLowOrderLDGenerator (rates u) - augmentedLowOrderLDGenerator (other u)‖ := by
    refine intervalIntegral.integral_congr fun u hu ↦ ?_
    rw [Set.uIcc_of_le hT] at hu
    simp only [generatorPath_of_mem rates hu, generatorPath_of_mem other hu]
  rw [← hdistance]
  exact norm_fundamentalMatrix_sub_le (continuous_generatorPath hT hcontinuous)
    (continuous_generatorPath hT hother) hT hK hpathBound hotherBound

/-- **Nonnegative step approximation in `L¹`.**  For every `ε > 0`, eventually in `n`, the
generator of the rate law sampled at the left endpoint of the uniform partition of `[0, T]` into
`n` intervals, a genuine nonnegative `ManyDemeLDRates` at every time, is within `ε T` of the
history's generator in `L¹([0, T])`. -/
theorem eventually_integral_norm_sampledGenerator_sub_le {D : ℕ}
    {rates : ℝ → ManyDemeLDRates D} {T : ℝ} (hT : 0 ≤ T)
    (hcontinuous :
      ContinuousOn (fun t ↦ augmentedLowOrderLDGenerator (rates t)) (Set.Icc 0 T))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in Filter.atTop, ∫ t in (0 : ℝ)..T,
      ‖augmentedLowOrderLDGenerator (rates (clampTime T (sampleTime T n t))) -
        augmentedLowOrderLDGenerator (rates t)‖ ≤ ε * T := by
  filter_upwards [eventually_integral_norm_sample_sub_le
    (continuous_generatorPath hT hcontinuous) hT hε] with n hn
  have hsame : (∫ t in (0 : ℝ)..T,
      ‖generatorPath rates T (sampleTime T n t) - generatorPath rates T t‖) =
      ∫ t in (0 : ℝ)..T,
        ‖augmentedLowOrderLDGenerator (rates (clampTime T (sampleTime T n t))) -
          augmentedLowOrderLDGenerator (rates t)‖ := by
    refine intervalIntegral.integral_congr fun t ht ↦ ?_
    rw [Set.uIcc_of_le hT] at ht
    simp only [generatorPath_of_mem rates ht]
    rfl
  rw [← hsame]
  exact hn

/-! ## Interleaving instantaneous events -/

/-- One segment of a piecewise history of the low-order system: a rate history over its own
horizon whose corpus generator is continuous there, or a physically realized split. -/
inductive HistorySegment (D : ℕ) where
  /-- Evolution under a rate history over `[0, horizon]`. -/
  | evolve (rates : ℝ → ManyDemeLDRates D) (horizon : ℝ) (horizon_nonneg : 0 ≤ horizon)
      (continuous :
        ContinuousOn (fun t ↦ augmentedLowOrderLDGenerator (rates t)) (Set.Icc 0 horizon))
  /-- The child deme is founded as a copy of the parent deme. -/
  | split (parent child : Fin D)

/-- The linear map one segment applies to the stored low-order state: the propagator of the
rate history, or the corpus split transform. -/
def HistorySegment.apply {D : ℕ} :
    HistorySegment D → (AffineLowOrderLDCoordinate D → ℝ) → AffineLowOrderLDCoordinate D → ℝ
  | .evolve rates horizon _ _, state => (rateHistoryPropagator rates horizon).mulVec state
  | .split parent child, state => (lowOrderLDSplitTransform parent child).mulVec state

/-- A split of the first deme onto itself, a segment carrying no hypothesis. -/
def splitSegmentWitness : HistorySegment 1 :=
  .split 0 0

/-- The stored low-order state after a finite list of segments, applied in order. -/
def propagateSegments {D : ℕ} (segments : List (HistorySegment D))
    (state : AffineLowOrderLDCoordinate D → ℝ) : AffineLowOrderLDCoordinate D → ℝ :=
  segments.foldl (fun current segment ↦ segment.apply current) state

/-- **NOTE1 section 2.4 with interleaved events.**  Every finite list of rate histories with
continuous generators and physically realized splits carries a locus-exchangeably realizable
stored state to a locus-exchangeably realizable one.  Each rate history is the continuous-rate
theorem, and each split relabels the very same haplotype law. -/
theorem propagateSegments_preserves_locusExchangeable_realization {D : ℕ}
    (segments : List (HistorySegment D)) {state : AffineLowOrderLDCoordinate D → ℝ}
    (realization : LocusExchangeableLowOrderLDHaplotypeRealization state) :
    Nonempty (LocusExchangeableLowOrderLDHaplotypeRealization
      (propagateSegments segments state)) := by
  induction segments generalizing state with
  | nil => exact ⟨realization⟩
  | cons head rest ih =>
      have hhead : Nonempty (LocusExchangeableLowOrderLDHaplotypeRealization
          (head.apply state)) := by
        cases head with
        | evolve rates horizon horizon_nonneg continuous =>
            exact rateHistory_preserves_locusExchangeable_realization rates horizon_nonneg
              continuous realization
        | split parent child =>
            exact ⟨TwoLocusRealizabilityPreservation.locusExchangeableSplit realization parent
              child⟩
      obtain ⟨propagated⟩ := hhead
      exact ih propagated

/-- After every finite list of continuous rate histories and splits the propagated `DD` block is
positive semidefinite under the common propagated haplotype law. -/
theorem propagateSegments_dd_quadraticForm_nonneg {D : ℕ}
    (segments : List (HistorySegment D)) {state : AffineLowOrderLDCoordinate D → ℝ}
    (realization : LocusExchangeableLowOrderLDHaplotypeRealization state)
    (weight : Fin D → ℝ) :
    0 ≤ ∑ first, ∑ second, weight first *
      propagateSegments segments state (some (.DD first second)) * weight second := by
  obtain ⟨propagated⟩ :=
    propagateSegments_preserves_locusExchangeable_realization segments realization
  exact propagated.toLowOrderLDHaplotypeRealization.toDDDRealization.dd_quadraticForm_nonneg
    weight

end

end Descent.Portability.IntegrableRateHistoryRealization
