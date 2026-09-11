/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.AncestralHaplotypeRealization
import Descent.Portability.EndToEndScoreLaw
import Descent.Portability.TwoLocusMicroscopicApproximation

assert_below Descent.Decision Descent.Program

/-!
# The linkage-pair domain of the visible pipeline history

`Descent.Portability.EndToEndScoreLaw` compiles a visible demographic history into the corpus
low-order two-locus operator product, `PipelineDemographicHistory.twoLocusMoments`, and records
an obligation it could not discharge: a realizability corollary showing that the propagated
`DD` kernel stays positive semidefinite, thereby constructing `LDPairDomain`, with its
Cauchy--Schwarz field, whenever within-deme `DD` is nonzero.  This module discharges it, as
NOTE1 Corollary 2.1 read at the pipeline endpoint.

The compiler emits nothing but rate epochs and splits.  `compileRateHistoryEvents` mirrors
`compileLowOrderLDEvents` event by event in the vocabulary of
`TwoLocusMicroscopicApproximation.RateHistoryEvent`, and
`compileRateHistoryEvents_instructions` proves that the two emit the same instruction list for
every event sequence, starting rate state and active-deme mask.  Size, migration, mutation and
recombination changes, and the activation of a split child, only change the rate law of the
next epoch, and every rate law the pipeline builds is a genuine `ManyDemeLDRates`.  No pulse or
admixture instruction is ever emitted, so no new event kind is needed.
`lowOrderLDHistory_instructions` appends the terminal epoch.

The initial state is the unsplit ancestral boundary `commonAncestralLowOrderLDState`, whose
locus-exchangeable haplotype realization is
`AncestralHaplotypeRealization.ancestralLocusExchangeableRealization`, NOTE1 Theorem 3 copied
to every deme label of the unsplit population.  NOTE1 Theorem 2 in the form
`history_present_locusExchangeable_realization` carries it through the whole compiled history,
so `present_locusExchangeable_realization` gives the present low-order state of the pipeline at
every marker separation one common haplotype law, with no hypotheses.

The endpoint.  At every separation the `DD` kernel of `twoLocusMoments` is positive
semidefinite, obeys Cauchy--Schwarz and has a nonnegative diagonal
(`PipelineDemographicHistory.twoLocusMoments_DD_quadraticForm_nonneg`, `_DD_cauchySchwarz`,
`_DD_diagonal_nonneg`).  `PipelineDemographicHistory.ldPairDomain` constructs the linkage-pair
domain from nonzero within-deme `DD` entries alone, and
`VisiblePipelineInput.unascertainedLDCorrelationSq_some_mem_unitInterval` places every defined
input-only unascertained squared correlation in `[0,1]` with no certificate argument.

Scope.  Everything here concerns the unascertained low-order moment field.  The selected-score
linkage factor, which conditions on ascertainment, association estimates and clumping, is not
touched, and neither are the mutation-model protocol question and the simulator gate named in
`EndToEndScoreLaw`.  The realization rests on the single-draw resampling step of NOTE1 section
2.3 in place of multinomial resampling, NOTE1 equation (10).

## Empirical status

None.  The bodies here are algebra: a structural recursion over an event list, and moments of
polynomial coordinates under one probability law.  Whether a coalescent simulator realizes this
moment field is the simulator gate named in `EndToEndScoreLaw`, which these bodies cannot
answer.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.PipelineLDPairDomain

open Coalescent
open Descent.Portability.TwoLocusMicroscopicApproximation

noncomputable section

/-! ## The visible event compiler emits rate epochs and splits -/

/-- The visible event sequence compiled into rate epochs and physically realized splits: each
event evolves under the rate law of the preceding interval for its elapsed time, a split then
founds its child deme from its parent, and the rate state and active-deme mask are updated for
the suffix.  This is `compileLowOrderLDEvents` read in the vocabulary of `RateHistoryEvent`. -/
def compileRateHistoryEvents {demeCount : ℕ} (separationBp : ℝ)
    (separationBp_nonneg : 0 ≤ separationBp) :
    List (DemographicEvent demeCount) → PipelineRateState demeCount →
      (Fin demeCount → Bool) → List (RateHistoryEvent demeCount)
  | [], _, _ => []
  | event :: remaining, state, active =>
      let rates := state.toManyDemeLDRates separationBp separationBp_nonneg active
      let front : List (RateHistoryEvent demeCount) :=
        match event with
        | .split _ _ parent child _ =>
            [.evolve rates event.elapsed event.elapsed_nonneg, .split parent child]
        | _ => [.evolve rates event.elapsed event.elapsed_nonneg]
      front ++ compileRateHistoryEvents separationBp separationBp_nonneg remaining
        (event.updateRateState state) (event.updateActive active)

/-- **The pipeline compiler emits only rate epochs and splits.**  For every event sequence,
starting rate state and active-deme mask, the rate-history events compile to exactly the
instruction list that `compileLowOrderLDEvents` produces. -/
theorem compileRateHistoryEvents_instructions {demeCount : ℕ} (separationBp : ℝ)
    (separationBp_nonneg : 0 ≤ separationBp) (events : List (DemographicEvent demeCount))
    (state : PipelineRateState demeCount) (active : Fin demeCount → Bool) :
    (compileRateHistoryEvents separationBp separationBp_nonneg events state active).map
        RateHistoryEvent.instruction =
      (compileLowOrderLDEvents separationBp separationBp_nonneg events state
        active).instructions := by
  induction events generalizing state active with
  | nil => rfl
  | cons event remaining ih =>
      cases event <;>
        simp [compileRateHistoryEvents, compileLowOrderLDEvents, RateHistoryEvent.instruction,
          ih]

/-- The rate-history events of the complete visible history at one marker separation: the
compiled event sequence followed by the terminal epoch under the final rate state. -/
def rateHistoryEvents {demeCount : ℕ} (history : PipelineDemographicHistory demeCount)
    (separationBp : ℝ) (separationBp_nonneg : 0 ≤ separationBp) :
    List (RateHistoryEvent demeCount) :=
  let compiled := compileLowOrderLDEvents separationBp separationBp_nonneg history.events
    history.initialRateState (initialDemeActive history.events)
  compileRateHistoryEvents separationBp separationBp_nonneg history.events
      history.initialRateState (initialDemeActive history.events) ++
    [.evolve (compiled.finalRateState.toManyDemeLDRates separationBp separationBp_nonneg
      compiled.finalActive) history.finalElapsed history.finalElapsed_nonneg]

/-- **The pipeline's two-locus history is compiled from rate epochs and splits.**  Its
instruction list at every marker separation is the instruction list of `rateHistoryEvents`,
terminal epoch included. -/
theorem lowOrderLDHistory_instructions {demeCount : ℕ}
    (history : PipelineDemographicHistory demeCount) (separationBp : ℝ)
    (separationBp_nonneg : 0 ≤ separationBp) :
    (history.lowOrderLDHistory separationBp separationBp_nonneg).instructions =
      (rateHistoryEvents history separationBp separationBp_nonneg).map
        RateHistoryEvent.instruction := by
  have hprefix := compileRateHistoryEvents_instructions separationBp separationBp_nonneg
    history.events history.initialRateState (initialDemeActive history.events)
  simp only [rateHistoryEvents, List.map_append, hprefix]
  rfl

/-! ## NOTE1 Theorem 2 at the pipeline -/

/-- **The present low-order state of the visible pipeline history is locus-exchangeably
realizable at every marker separation, with no hypotheses.**  The unsplit ancestral boundary
carries a common haplotype law, and every compiled epoch and split preserves it. -/
theorem present_locusExchangeable_realization {demeCount : ℕ}
    (history : PipelineDemographicHistory demeCount) (separationBp : ℝ)
    (separationBp_nonneg : 0 ≤ separationBp) :
    Nonempty (LocusExchangeableLowOrderLDHaplotypeRealization
      (history.lowOrderLDHistory separationBp separationBp_nonneg).present) :=
  history_present_locusExchangeable_realization
    (history.lowOrderLDHistory separationBp separationBp_nonneg)
    (rateHistoryEvents history separationBp separationBp_nonneg)
    (lowOrderLDHistory_instructions history separationBp separationBp_nonneg)
    (AncestralHaplotypeRealization.ancestralLocusExchangeableRealization
      (history.ancestralLDRates separationBp separationBp_nonneg))

end

end Descent.Portability.PipelineLDPairDomain

namespace Descent.Portability

open Coalescent
open Descent.Portability.PipelineLDPairDomain

/-! ## NOTE1 Corollary 2.1 at the `EndToEndScoreLaw` endpoint -/

/-- **The pipeline `DD` kernel is positive semidefinite.**  At every marker separation, every
finite linear combination of deme-specific linkage disequilibria has nonnegative second moment
under the common propagated haplotype law. -/
theorem PipelineDemographicHistory.twoLocusMoments_DD_quadraticForm_nonneg {demeCount : ℕ}
    (history : PipelineDemographicHistory demeCount) (separation : MarkerSeparationBp)
    (weight : Fin demeCount → ℝ) :
    0 ≤ ∑ first, ∑ second,
      weight first * history.twoLocusMoments.DD separation first second * weight second := by
  obtain ⟨propagated⟩ := present_locusExchangeable_realization history separation.value
    separation.value_nonneg
  exact propagated.toLowOrderLDHaplotypeRealization.toDDDRealization.dd_quadraticForm_nonneg
    weight

/-- NOTE1 (13) at the pipeline endpoint: the cross-deme `DD` entries of `twoLocusMoments` obey
Cauchy--Schwarz against the within-deme entries at every marker separation. -/
theorem PipelineDemographicHistory.twoLocusMoments_DD_cauchySchwarz {demeCount : ℕ}
    (history : PipelineDemographicHistory demeCount) (separation : MarkerSeparationBp)
    (first second : Fin demeCount) :
    history.twoLocusMoments.DD separation first second ^ 2 ≤
      history.twoLocusMoments.DD separation first first *
        history.twoLocusMoments.DD separation second second := by
  obtain ⟨propagated⟩ := present_locusExchangeable_realization history separation.value
    separation.value_nonneg
  exact propagated.toLowOrderLDHaplotypeRealization.toDDDRealization.dd_cauchySchwarz first
    second

/-- The within-deme `DD` entry of `twoLocusMoments` is a second moment under the common
propagated haplotype law, and therefore nonnegative at every marker separation. -/
theorem PipelineDemographicHistory.twoLocusMoments_DD_diagonal_nonneg {demeCount : ℕ}
    (history : PipelineDemographicHistory demeCount) (separation : MarkerSeparationBp)
    (deme : Fin demeCount) :
    0 ≤ history.twoLocusMoments.DD separation deme deme := by
  obtain ⟨propagated⟩ := present_locusExchangeable_realization history separation.value
    separation.value_nonneg
  exact propagated.toLowOrderLDHaplotypeRealization.toDDDRealization.dd_diagonal_nonneg deme

/-- **The `EndToEndScoreLaw` linkage-pair obligation, discharged.**  For every visible
demographic history, marker separation and pair of demes whose within-deme `DD` entries are
nonzero, the pipeline's two-locus moments lie in the linkage-pair domain.  Positivity of the two
normalizing entries comes from their being second moments, and the Cauchy--Schwarz field from the
propagated Gram witness; neither is supplied by the caller. -/
theorem PipelineDemographicHistory.ldPairDomain {demeCount : ℕ}
    (history : PipelineDemographicHistory demeCount) (separation : MarkerSeparationBp)
    (first second : Fin demeCount)
    (first_ne : history.twoLocusMoments.DD separation first first ≠ 0)
    (second_ne : history.twoLocusMoments.DD separation second second ≠ 0) :
    history.twoLocusMoments.LDPairDomain separation first second :=
  { firstWithin_pos :=
      lt_of_le_of_ne (history.twoLocusMoments_DD_diagonal_nonneg separation first)
        (Ne.symm first_ne)
    secondWithin_pos :=
      lt_of_le_of_ne (history.twoLocusMoments_DD_diagonal_nonneg separation second)
        (Ne.symm second_ne)
    cross_sq_le := history.twoLocusMoments_DD_cauchySchwarz separation first second }

/-- **Every defined input-only unascertained squared `DD` correlation lies in `[0,1]`.**  The
readout returns a value only on the normalization domain, where the within-deme entries are
positive, and there the linkage-pair domain is constructed rather than taken as an argument. -/
theorem VisiblePipelineInput.unascertainedLDCorrelationSq_some_mem_unitInterval
    {demeCount : ℕ} (input : VisiblePipelineInput demeCount)
    (separation : MarkerSeparationBp) (target : Fin demeCount) {value : ℝ}
    (hvalue : input.unascertainedLDCorrelationSq separation target = some value) :
    value ∈ Set.Icc (0 : ℝ) 1 := by
  classical
  by_cases domain : input.demography.twoLocusMoments.LDNormalizationDomain separation
      input.studyDesign.gwasDeme target
  · exact input.unascertainedLDCorrelationSq_mem_unitInterval separation target
      (input.demography.ldPairDomain separation input.studyDesign.gwasDeme target
        domain.firstWithin_pos.ne' domain.secondWithin_pos.ne') hvalue
  · simp [VisiblePipelineInput.unascertainedLDCorrelationSq, domain] at hvalue

end Descent.Portability
