/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.MultinomialMicroscopicApproximation
import Descent.Portability.PulseHistoryRealization

assert_below Descent.Decision Descent.Program

/-!
# Histories of epochs, splits and pulses through multinomial resampling

NOTE1 Theorem 2 is stated for demographic histories: finite lists of rate epochs, splits and
admixture pulses. `PulseHistoryRealization` proves it with every epoch step through
`TwoLocusMicroscopicApproximation.rateEpoch_preserves_locusExchangeable_realization`, whose
microscopic approximation resamples by a single draw. This module proves the history forms with
every epoch step through `MultinomialMicroscopicApproximation`, whose drift stages draw the note's
multinomial sample of `⌈1/(c h)⌉` chromosomes, so no step of these history theorems uses the
single-draw stage.

`multinomialPulseEvent_preserves_locusExchangeable_realization` handles one event. An epoch goes
through the multinomial epoch theorem
`MultinomialMicroscopicApproximation.multinomialEpoch_preserves_locusExchangeable_realization`;
a split through `TwoLocusRealizabilityPreservation.locusExchangeableSplit`, which relabels the
realizing law; and a pulse through `PulseHistoryRealization.locusExchangeablePulse`, the
transformed witness. `multinomialPulseHistory_preserves_locusExchangeable_realization` composes
any finite list of events, `multinomialPulseHistory_present_locusExchangeable_realization` reads
it at the present of a compiled `LowOrderLDHistory`, and
`multinomialRateHistory_present_locusExchangeable_realization` is the case of rate epochs and
splits alone.

Corollary 2.1 follows at the present. The state lies in the stored realization body
(`multinomialPulseHistory_present_mem_realizationBody`), its `DD` block is positive semidefinite
(`multinomialPulseHistory_present_dd_quadraticForm_nonneg`), obeys Cauchy–Schwarz
(`multinomialPulseHistory_present_dd_cauchySchwarz`) and has a nonnegative diagonal
(`multinomialPulseHistory_present_dd_diagonal_nonneg`), and `multinomialPulseHistory_LDPairDomain`
constructs the linkage-pair domain wherever the two within-deme `DD` entries are nonzero.

Scope. Every statement takes a deme, because the multinomial stage mixture needs a stage to choose
from; with no demes there is nothing to resample. The events are exactly those of
`PulseHistoryRealization`.

## Empirical status

None. The bodies here are list induction over events whose one-step statements are proved
elsewhere, and moments of polynomial coordinates under one probability law, so no measurement can
bear on them.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.MultinomialHistoryRealization

open Coalescent
open Descent.Portability.RealizationBody
open Descent.Portability.TwoLocusMicroscopicApproximation
open Descent.Portability.PulseHistoryRealization
open Descent.Portability.MultinomialMicroscopicApproximation

noncomputable section

/-! ## NOTE1 Theorem 2 for histories, through multinomial resampling -/

/-- **Every event preserves locus-exchangeable realizability through multinomial resampling.** A
rate epoch is the multinomial epoch theorem, a split relabels the realizing law, and a pulse is
the transformed witness. -/
theorem multinomialPulseEvent_preserves_locusExchangeable_realization {D : ℕ} (deme : Fin D)
    (event : PulseHistoryEvent D) {state : AffineLowOrderLDCoordinate D → ℝ}
    (realization : LocusExchangeableLowOrderLDHaplotypeRealization state) :
    Nonempty (LocusExchangeableLowOrderLDHaplotypeRealization (event.instruction.apply state)) := by
  cases event with
  | rate event =>
      cases event with
      | evolve rates duration duration_nonneg =>
          exact multinomialEpoch_preserves_locusExchangeable_realization rates deme duration
            duration_nonneg realization
      | split parent child =>
          exact ⟨TwoLocusRealizabilityPreservation.locusExchangeableSplit realization parent child⟩
  | pulse alpha alpha_nonneg alpha_le_one source recipient =>
      exact ⟨locusExchangeablePulse realization alpha alpha_nonneg alpha_le_one source recipient⟩

/-- **NOTE1 Theorem 2 for histories with pulses, through multinomial resampling.** Composing any
finite list of rate epochs, physically realized splits and admixture pulses carries a
locus-exchangeably realizable stored state to a locus-exchangeably realizable one. -/
theorem multinomialPulseHistory_preserves_locusExchangeable_realization {D : ℕ} (deme : Fin D)
    {initial : AffineLowOrderLDCoordinate D → ℝ} (events : List (PulseHistoryEvent D))
    (realization : LocusExchangeableLowOrderLDHaplotypeRealization initial) :
    Nonempty (LocusExchangeableLowOrderLDHaplotypeRealization
      (propagateLowOrderLDInstructions (events.map PulseHistoryEvent.instruction) initial)) := by
  induction events generalizing initial with
  | nil => exact ⟨realization⟩
  | cons head rest ih =>
      obtain ⟨propagated⟩ :=
        multinomialPulseEvent_preserves_locusExchangeable_realization deme head realization
      exact ih propagated

/-! ## The present state of a compiled history -/

section Present

variable {D : ℕ} (deme : Fin D) (history : LowOrderLDHistory D)
  (events : List (PulseHistoryEvent D))
  (hcompiled : history.instructions = events.map PulseHistoryEvent.instruction)
  (realization : LocusExchangeableLowOrderLDHaplotypeRealization history.initial)

include deme hcompiled realization

/-- The present state of a history of rate epochs, splits and pulses is locus-exchangeably
realizable whenever its initial state is, with every epoch through multinomial resampling. -/
theorem multinomialPulseHistory_present_locusExchangeable_realization :
    Nonempty (LocusExchangeableLowOrderLDHaplotypeRealization history.present) := by
  rw [LowOrderLDHistory.present, hcompiled]
  exact multinomialPulseHistory_preserves_locusExchangeable_realization deme events realization

/-- The present state lies in the stored realization body. -/
theorem multinomialPulseHistory_present_mem_realizationBody :
    history.present ∈ realizationBody (lowOrderLDFeature D) := by
  obtain ⟨propagated⟩ := multinomialPulseHistory_present_locusExchangeable_realization deme
    history events hcompiled realization
  exact KernelRealizationPreservation.lowOrderLDState_mem_realizationBody_of_realization
    propagated.toLowOrderLDHaplotypeRealization

/-- **NOTE1 Corollary 2.1 through multinomial resampling: the propagated `DD` block is positive
semidefinite.** -/
theorem multinomialPulseHistory_present_dd_quadraticForm_nonneg (weight : Fin D → ℝ) :
    0 ≤ ∑ first, ∑ second,
      weight first * history.present (some (.DD first second)) * weight second := by
  obtain ⟨propagated⟩ := multinomialPulseHistory_present_locusExchangeable_realization deme
    history events hcompiled realization
  exact propagated.toLowOrderLDHaplotypeRealization.toDDDRealization.dd_quadraticForm_nonneg
    weight

/-- NOTE1 (13) through multinomial resampling: the propagated cross-deme `DD` entries obey
Cauchy–Schwarz against the propagated diagonals. -/
theorem multinomialPulseHistory_present_dd_cauchySchwarz (first second : Fin D) :
    history.present (some (.DD first second)) ^ 2 ≤
      history.present (some (.DD first first)) *
        history.present (some (.DD second second)) := by
  obtain ⟨propagated⟩ := multinomialPulseHistory_present_locusExchangeable_realization deme
    history events hcompiled realization
  exact propagated.toLowOrderLDHaplotypeRealization.toDDDRealization.dd_cauchySchwarz first
    second

/-- The propagated within-deme `DD` diagonal is nonnegative. -/
theorem multinomialPulseHistory_present_dd_diagonal_nonneg (index : Fin D) :
    0 ≤ history.present (some (.DD index index)) := by
  obtain ⟨propagated⟩ := multinomialPulseHistory_present_locusExchangeable_realization deme
    history events hcompiled realization
  exact propagated.toLowOrderLDHaplotypeRealization.toDDDRealization.dd_diagonal_nonneg index

end Present

/-- The case of rate epochs and splits alone: a history compiled from `RateHistoryEvent`s is
realizable at the present, with every epoch through multinomial resampling. -/
theorem multinomialRateHistory_present_locusExchangeable_realization {D : ℕ} (deme : Fin D)
    (history : LowOrderLDHistory D) (events : List (RateHistoryEvent D))
    (hcompiled : history.instructions = events.map RateHistoryEvent.instruction)
    (realization : LocusExchangeableLowOrderLDHaplotypeRealization history.initial) :
    Nonempty (LocusExchangeableLowOrderLDHaplotypeRealization history.present) :=
  multinomialPulseHistory_present_locusExchangeable_realization deme history
    (events.map PulseHistoryEvent.rate) (by rw [hcompiled, List.map_map]; try rfl) realization

/-- **NOTE1 Corollary 2.1 at the `EndToEndScoreLaw` endpoint, through multinomial resampling.**
For a separation-indexed family of histories of rate epochs, splits and pulses started from
locus-exchangeably realizable states, the normalized linkage-pair domain holds at every pair of
demes whose within-deme `DD` entries are nonzero. -/
theorem multinomialPulseHistory_LDPairDomain {D : ℕ} (deme : Fin D)
    (historyAt : MarkerSeparationBp → LowOrderLDHistory D) (separation : MarkerSeparationBp)
    (eventsAt : MarkerSeparationBp → List (PulseHistoryEvent D))
    (hcompiled : ∀ other, (historyAt other).instructions =
      (eventsAt other).map PulseHistoryEvent.instruction)
    (realization : LocusExchangeableLowOrderLDHaplotypeRealization (historyAt separation).initial)
    (first second : Fin D)
    (hfirst : (historyAt separation).present (some (.DD first first)) ≠ 0)
    (hsecond : (historyAt separation).present (some (.DD second second)) ≠ 0) :
    (LowOrderLDHistory.toDemographicTwoLocusMoments historyAt).LDPairDomain separation first
      second := by
  obtain ⟨propagated⟩ := multinomialPulseHistory_present_locusExchangeable_realization deme
    (historyAt separation) (eventsAt separation) (hcompiled separation) realization
  have hwitness := propagated.toLowOrderLDHaplotypeRealization.toDDDRealization
  exact hwitness.toLDPairDomain historyAt separation first second
    (lt_of_le_of_ne (hwitness.dd_diagonal_nonneg first) (Ne.symm hfirst))
    (lt_of_le_of_ne (hwitness.dd_diagonal_nonneg second) (Ne.symm hsecond))

end

end Descent.Portability.MultinomialHistoryRealization
