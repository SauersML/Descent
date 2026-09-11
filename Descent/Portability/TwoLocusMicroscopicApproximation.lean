/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.Pi2GeneratorBridges
import Descent.Portability.EnlargedBodyClosedness

assert_below Descent.Decision Descent.Program

/-!
# Low-order realizability under demographic histories, with nothing assumed

This module is NOTE1 Theorem 2 and Corollary 2.1 with no hypothesis beyond an initial
locus-exchangeable haplotype realization.  Every earlier statement of Theorem 2 in the corpus
carried the microscopic approximation of NOTE1 equation (11) as data, and some also carried
closedness of the enlarged realization body.  Both are now theorems, and this is where they
are put together.

The approximation.  `Descent.Portability.TwoLocusMicroscopicKernel` builds the stage-choosing
microscopic step of NOTE1 section 2.3 and proves its first-order expansion with an explicit
vanishing error, taking as its one hypothesis that the rate-weighted stage velocities sum to
the enlarged generator at every coordinate, and `Descent.Portability.Pi2GeneratorBridges`
proves that identification at every enlarged coordinate.  `enlargedMicroscopicApproximation`
is therefore a `MicroscopicApproximation` of `enlargedLowOrderLDGenerator rates` with nothing
assumed, for any deme count with at least one deme.  With no demes the stage set is empty, the
enlarged index set is the affine coordinate alone and the enlarged generator is zero
(`enlargedLowOrderLDGenerator_zeroDeme`), so the kernel that does nothing serves
(`zeroDemeMicroscopicApproximation`).  `enlargedLowOrderLDFeature_eq` ties the enlarged
feature map of `EnlargedLowOrderLDGenerator` to the one of `KernelRealizationPreservation`:
they are one function, so a statement about either body is a statement about both.

Theorem 2.  `rateEpoch_preserves_locusExchangeable_realization` is one epoch
`rates.epoch duration hduration` at any nonnegative rates: the propagated stored vector again
has a locus-exchangeable haplotype realization, NOTE1's invariance of the subspace (12) on the
body.  `RateHistoryEvent` names the two events Theorem 2 covers, a rate epoch and a physically
realized split, and `propagate_preserves_locusExchangeable_realization` is the theorem for any
finite list of them, read at the present of a compiled `LowOrderLDHistory` by
`history_present_locusExchangeable_realization`.  These are not phrased through
`PiecewiseConstantBodyPreservation.history_present_mem_realizationBody`, whose hypothesis is a
microscopic approximation on the stored feature map.  That hypothesis cannot be discharged once
a mutation rate is positive: the stored `pi2` mutation row reads the stored `H` column, while a
microscopic step moves `pi2` through the right-locus heterozygosity, and only a
locus-exchangeable realization licenses reading one for the other.
`history_present_mem_realizationBody_of_events` reaches that module's conclusion for compiled
histories with no approximation supplied.

Corollary 2.1.  After every compiled history the propagated `DD` block is positive
semidefinite (`history_present_dd_quadraticForm_nonneg`), obeys Cauchy--Schwarz
(`history_present_dd_cauchySchwarz`) and has a nonnegative diagonal
(`history_present_dd_diagonal_nonneg`), and `history_LDPairDomain` constructs the
`LDPairDomain` that the `EndToEndScoreLaw` contract asks for whenever the two within-deme `DD`
entries are nonzero.  What is NOT proved here: the integrable time-varying rates of NOTE1
section 2.4 beyond piecewise-constant composition, instantaneous events other than splits, and
multinomial resampling, NOTE1 equation (10), in place of which the single-draw step of NOTE1
section 2.3 is used.

## Empirical status

None.  The bodies here are algebra and point-set topology: a convex hull carried into itself by
a matrix exponential, and moments of polynomial coordinates under one probability law.  No
measurement can bear on them.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.TwoLocusMicroscopicApproximation

open Coalescent
open Descent.Portability.FiniteMixtureKernel
open Descent.Portability.RealizationBody
open Descent.Portability.PulseStageKernel
open Descent.Portability.EnlargedLowOrderLDGenerator
open Descent.Portability.TwoLocusMicroscopicKernel
open Descent.Portability.Pi2GeneratorBridges

noncomputable section

/-! ## The microscopic approximation, with nothing assumed -/

/-- **The microscopic approximation of the enlarged generator.**  The stage-choosing kernel of
NOTE1 section 2.3 advances every enlarged coordinate by the enlarged generator of NOTE1 section
2.2 applied to the feature vector, uniformly in the state, with an error that vanishes with the
step size, and the identification of the stage velocities with the generator is proved at
every coordinate rather than assumed.  The deme is data because it is what makes the stage set
nonempty. -/
def enlargedMicroscopicApproximation {D : ℕ} (rates : ManyDemeLDRates D) (deme : Fin D) :
    MicroscopicApproximation (B := Stage D × TwoLocusHaplotype)
      (enlargedLowOrderLDFeature (D := D)) (enlargedLowOrderLDGenerator rates) :=
  twoLocusMicroscopicApproximation rates deme (stage_generator_enlarged rates)

/-- With no demes the enlarged index set is the affine coordinate alone, whose generator row
is zero, so the enlarged generator is the zero matrix. -/
theorem enlargedLowOrderLDGenerator_zeroDeme (rates : ManyDemeLDRates 0) :
    enlargedLowOrderLDGenerator rates = 0 := by
  apply Matrix.ext
  intro row column
  rcases row with _ | (coordinate | pair)
  · rfl
  · rcases coordinate with
      ⟨first, _⟩ | ⟨first, _⟩ | ⟨first, _, _⟩ | ⟨first, _, _, _⟩ <;>
      exact first.elim0
  · exact pair.1.elim0

/-- The microscopic approximation with no demes: the kernel that does nothing approximates the
zero generator with no remainder. -/
def zeroDemeMicroscopicApproximation (rates : ManyDemeLDRates 0) :
    MicroscopicApproximation (B := Unit) (enlargedLowOrderLDFeature (D := 0))
      (enlargedLowOrderLDGenerator rates) :=
  (enlargedLowOrderLDGenerator_zeroDeme rates).symm ▸ trivialApproximation _

/-! ## The two enlarged feature maps -/

/-- **The enlarged feature map of `EnlargedLowOrderLDGenerator` is the enlarged feature map of
`KernelRealizationPreservation`.**  Both send the affine coordinate to one, a stored coordinate
to its corpus polynomial and a right-locus index pair to the right-locus heterozygosity; they
differ only in whether the deme count is implicit. -/
theorem enlargedLowOrderLDFeature_eq (D : ℕ) :
    enlargedLowOrderLDFeature (D := D) =
      KernelRealizationPreservation.enlargedLowOrderLDFeature D := by
  funext state coordinate
  rcases coordinate with _ | (_ | _) <;> rfl

/-! ## NOTE1 Theorem 2 -/

/-- **NOTE1 Theorem 2 for one epoch, with no hypotheses.**  For every nonnegative rate law and
every nonnegative duration, the epoch propagator of the arbitrary-deme low-order system maps a
locus-exchangeably realizable stored state to a locus-exchangeably realizable one: the
propagated vector is again the vector of all its defining polynomials under one common
probability law on the haplotype simplex, with the expected left and right heterozygosities
still equal. -/
theorem rateEpoch_preserves_locusExchangeable_realization {D : ℕ} (rates : ManyDemeLDRates D)
    (duration : ℝ) (hduration : 0 ≤ duration) {state : AffineLowOrderLDCoordinate D → ℝ}
    (realization : LocusExchangeableLowOrderLDHaplotypeRealization state) :
    Nonempty (LocusExchangeableLowOrderLDHaplotypeRealization
      ((rates.epoch duration hduration).propagator.mulVec state)) := by
  rcases Nat.eq_zero_or_pos D with hzero | hpositive
  · subst hzero
    exact EnlargedBodyClosedness.epoch_preserves_locusExchangeable_realization_of_approx rates
      (zeroDemeMicroscopicApproximation rates) duration hduration realization
  · exact EnlargedBodyClosedness.epoch_preserves_locusExchangeable_realization_of_approx rates
      (enlargedMicroscopicApproximation rates ⟨0, hpositive⟩) duration hduration realization

/-- One event of a compiled demographic history of the kind NOTE1 Theorem 2 covers: an epoch of
the arbitrary-deme low-order system at a nonnegative rate law for a nonnegative duration, or a
physically realized split of a child deme off a parent deme. -/
inductive RateHistoryEvent (D : ℕ) where
  /-- Continuous evolution under `rates` for `duration`. -/
  | evolve (rates : ManyDemeLDRates D) (duration : ℝ) (duration_nonneg : 0 ≤ duration)
  /-- The child deme is founded as a copy of the parent deme. -/
  | split (parent child : Fin D)

/-- The corpus instruction an event compiles to: the rate law's epoch, or the corpus split. -/
def RateHistoryEvent.instruction {D : ℕ} : RateHistoryEvent D → LowOrderLDInstruction D
  | .evolve rates duration duration_nonneg => .evolve (rates.epoch duration duration_nonneg)
  | .split parent child => LowOrderLDInstruction.split parent child

/-- **NOTE1 Theorem 2 for a finite history, with no hypotheses.**  Composing any finite list of
rate epochs and physically realized splits carries a locus-exchangeably realizable stored state
to a locus-exchangeably realizable one.  Each epoch is the one-epoch theorem, and each split
relabels the very same haplotype law. -/
theorem propagate_preserves_locusExchangeable_realization {D : ℕ}
    (events : List (RateHistoryEvent D)) {initial : AffineLowOrderLDCoordinate D → ℝ}
    (realization : LocusExchangeableLowOrderLDHaplotypeRealization initial) :
    Nonempty (LocusExchangeableLowOrderLDHaplotypeRealization
      (propagateLowOrderLDInstructions (events.map RateHistoryEvent.instruction) initial)) := by
  induction events generalizing initial with
  | nil => exact ⟨realization⟩
  | cons head rest ih =>
      have hhead : Nonempty (LocusExchangeableLowOrderLDHaplotypeRealization
          (head.instruction.apply initial)) := by
        cases head with
        | evolve rates duration duration_nonneg =>
            exact rateEpoch_preserves_locusExchangeable_realization rates duration
              duration_nonneg realization
        | split parent child =>
            exact ⟨TwoLocusRealizabilityPreservation.locusExchangeableSplit realization
              parent child⟩
      obtain ⟨propagated⟩ := hhead
      exact ih propagated

/-- The present state of a history compiled from rate epochs and splits is locus-exchangeably
realizable whenever its initial state is. -/
theorem history_present_locusExchangeable_realization {D : ℕ} (history : LowOrderLDHistory D)
    (events : List (RateHistoryEvent D))
    (hcompiled : history.instructions = events.map RateHistoryEvent.instruction)
    (realization : LocusExchangeableLowOrderLDHaplotypeRealization history.initial) :
    Nonempty (LocusExchangeableLowOrderLDHaplotypeRealization history.present) := by
  rw [LowOrderLDHistory.present, hcompiled]
  exact propagate_preserves_locusExchangeable_realization events realization

/-- A compiled history places its present state in the corpus realization body, the conclusion
of `PiecewiseConstantBodyPreservation.history_present_mem_realizationBody`, with no microscopic
approximation supplied. -/
theorem history_present_mem_realizationBody_of_events {D : ℕ} (history : LowOrderLDHistory D)
    (events : List (RateHistoryEvent D))
    (hcompiled : history.instructions = events.map RateHistoryEvent.instruction)
    (realization : LocusExchangeableLowOrderLDHaplotypeRealization history.initial) :
    history.present ∈ realizationBody (lowOrderLDFeature D) := by
  obtain ⟨propagated⟩ :=
    history_present_locusExchangeable_realization history events hcompiled realization
  exact KernelRealizationPreservation.lowOrderLDState_mem_realizationBody_of_realization
    propagated.toLowOrderLDHaplotypeRealization

/-! ## NOTE1 Corollary 2.1 -/

/-- **The propagated `DD` block is positive semidefinite after every compiled history.**  Every
finite linear combination of deme-specific linkage disequilibria has nonnegative second moment
under the common propagated haplotype law; the inequality is derived from the realization, not
assumed of the numbers. -/
theorem history_present_dd_quadraticForm_nonneg {D : ℕ} (history : LowOrderLDHistory D)
    (events : List (RateHistoryEvent D))
    (hcompiled : history.instructions = events.map RateHistoryEvent.instruction)
    (realization : LocusExchangeableLowOrderLDHaplotypeRealization history.initial)
    (weight : Fin D → ℝ) :
    0 ≤ ∑ first, ∑ second,
      weight first * history.present (some (.DD first second)) * weight second := by
  obtain ⟨propagated⟩ :=
    history_present_locusExchangeable_realization history events hcompiled realization
  exact propagated.toLowOrderLDHaplotypeRealization.toDDDRealization.dd_quadraticForm_nonneg
    weight

/-- NOTE1 (13) after every compiled history: the propagated cross-deme `DD` entries obey
Cauchy--Schwarz against the propagated diagonals, with no strict positivity assumed. -/
theorem history_present_dd_cauchySchwarz {D : ℕ} (history : LowOrderLDHistory D)
    (events : List (RateHistoryEvent D))
    (hcompiled : history.instructions = events.map RateHistoryEvent.instruction)
    (realization : LocusExchangeableLowOrderLDHaplotypeRealization history.initial)
    (first second : Fin D) :
    history.present (some (.DD first second)) ^ 2 ≤
      history.present (some (.DD first first)) *
        history.present (some (.DD second second)) := by
  obtain ⟨propagated⟩ :=
    history_present_locusExchangeable_realization history events hcompiled realization
  exact propagated.toLowOrderLDHaplotypeRealization.toDDDRealization.dd_cauchySchwarz first
    second

/-- The propagated within-deme `DD` diagonal is a second moment and therefore nonnegative after
every compiled history. -/
theorem history_present_dd_diagonal_nonneg {D : ℕ} (history : LowOrderLDHistory D)
    (events : List (RateHistoryEvent D))
    (hcompiled : history.instructions = events.map RateHistoryEvent.instruction)
    (realization : LocusExchangeableLowOrderLDHaplotypeRealization history.initial)
    (deme : Fin D) :
    0 ≤ history.present (some (.DD deme deme)) := by
  obtain ⟨propagated⟩ :=
    history_present_locusExchangeable_realization history events hcompiled realization
  exact propagated.toLowOrderLDHaplotypeRealization.toDDDRealization.dd_diagonal_nonneg deme

/-- **NOTE1 Corollary 2.1 at the `EndToEndScoreLaw` endpoint.**  For a separation-indexed
family of histories compiled from rate epochs and splits and started from locus-exchangeably
realizable states, the normalized linkage-pair domain holds at every pair of demes whose
within-deme `DD` entries are nonzero.  Positivity of those entries comes from the nonnegative
propagated diagonal and the Cauchy--Schwarz field from the propagated Gram witness; neither is
supplied by the caller. -/
theorem history_LDPairDomain {D : ℕ} (historyAt : MarkerSeparationBp → LowOrderLDHistory D)
    (eventsAt : MarkerSeparationBp → List (RateHistoryEvent D))
    (hcompiled : ∀ separation,
      (historyAt separation).instructions =
        (eventsAt separation).map RateHistoryEvent.instruction)
    (separation : MarkerSeparationBp) (first second : Fin D)
    (realization :
      LocusExchangeableLowOrderLDHaplotypeRealization (historyAt separation).initial)
    (first_ne : (historyAt separation).present (some (.DD first first)) ≠ 0)
    (second_ne : (historyAt separation).present (some (.DD second second)) ≠ 0) :
    (LowOrderLDHistory.toDemographicTwoLocusMoments historyAt).LDPairDomain
      separation first second := by
  obtain ⟨propagated⟩ := history_present_locusExchangeable_realization (historyAt separation)
    (eventsAt separation) (hcompiled separation) realization
  have hwitness := propagated.toLowOrderLDHaplotypeRealization.toDDDRealization
  exact hwitness.toLDPairDomain historyAt separation first second
    (lt_of_le_of_ne (hwitness.dd_diagonal_nonneg first) (Ne.symm first_ne))
    (lt_of_le_of_ne (hwitness.dd_diagonal_nonneg second) (Ne.symm second_ne))

end

end Descent.Portability.TwoLocusMicroscopicApproximation
