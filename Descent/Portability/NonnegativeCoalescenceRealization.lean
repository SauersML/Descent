/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.IntegrableRateHistoryRealization
import Descent.Portability.RateGeneratorLipschitz

assert_below Descent.Decision Descent.Program

/-!
# Low-order realizability at nonnegative coalescence

NOTE1 section 2.2 takes coalescence rates `c_i ≥ 0`, while the corpus rate law
`Coalescent.ManyDemeLDRates` requires `c_i > 0`, so every corpus statement of NOTE1 Theorem 2
and Corollary 2.1 excludes demes with no drift. This module removes that restriction.

`NonnegativeLDRates` is the rate law of NOTE1 section 2.2 with nonnegative coalescence, and
`NonnegativeLDRates.generator` is its low-order generator: the linear map
`RateGeneratorLipschitz.generatorLinearMap` at its rate coordinates. The definition is forced.
`generator_ofRates` shows it is the corpus `augmentedLowOrderLDGenerator` whenever coalescence is
positive, `generator_perturb` that raising every coalescence rate by `ε > 0` gives the corpus
generator of a genuine `ManyDemeLDRates` equal to it plus `ε` times the unit-coalescence
generator, and `tendsto_generator_perturb` that those corpus generators converge to it along
`ε = 1 / (n + 1)`. `coalescenceFreeRates` is a rate law with no coalescence at all, which no
corpus rate law reaches (`ofRates_ne_coalescenceFreeRates`).

Theorem 2. `NonnegativeLDRates.epoch` is the corpus `LowOrderLDEpoch` of a nonnegative rate
law, and it is the corpus epoch at positive coalescence (`epoch_ofRates`).
`tendsto_perturbedEpoch_mulVec` is continuity of the epoch propagator in the rates: the matrix
exponential is continuous, so the propagated states of the perturbed corpus epochs converge to
the propagated state of the limit epoch. Each perturbed epoch preserves locus-exchangeable
realizability by
`TwoLocusMicroscopicApproximation.rateEpoch_preserves_locusExchangeable_realization`, and the
realizable states form the closed set `IntegrableRateHistoryRealization.exchangeableStates`, so
`nonnegativeEpoch_preserves_locusExchangeable_realization` holds with no hypothesis beyond an
initial realization. `NonnegativeRateEvent` names epochs at nonnegative coalescence and splits,
`nonnegativePropagate_preserves_locusExchangeable_realization` is the theorem for any finite
list of them, and `nonnegativeHistory_present_locusExchangeable_realization` reads it at the
present of a compiled `LowOrderLDHistory`.

Corollary 2.1. After every such history the propagated `DD` block is positive semidefinite
(`nonnegativeHistory_present_dd_quadraticForm_nonneg`), obeys Cauchy–Schwarz
(`nonnegativeHistory_present_dd_cauchySchwarz`) and has a nonnegative diagonal
(`nonnegativeHistory_present_dd_diagonal_nonneg`), and `nonnegativeHistory_LDPairDomain`
constructs the `LDPairDomain` wherever the two within-deme `DD` entries are nonzero.

Scope. Rates are constant within an epoch; time-varying rates with vanishing coalescence are not
treated here. No microscopic kernel at `c_i = 0` is constructed: NOTE1 section 2.3 omits the
sampling stage there, and this module reaches the result through the limit instead.

## Empirical status

None. The bodies here are linear algebra and point-set topology: the linear extension of a
matrix-valued map, the continuity of the matrix exponential, and a limit inside a closed set, so
no measurement can bear on them.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.NonnegativeCoalescenceRealization

open Coalescent
open Filter Topology
open Descent.Portability.RealizationBody
open Descent.Portability.RateGeneratorLipschitz
open Descent.Portability.IntegrableRateHistoryRealization
open Descent.Portability.TwoLocusMicroscopicApproximation
open scoped Matrix.Norms.Operator

noncomputable section

/-! ## Rate laws with nonnegative coalescence -/

/-- **The rate law of NOTE1 section 2.2.** Coalescence, migration, mutation and recombination
rates, all nonnegative, with no self-migration. Unlike `ManyDemeLDRates`, a deme may have no
coalescence at all. -/
structure NonnegativeLDRates (D : ℕ) where
  /-- The coalescence rate of every deme. -/
  coalescence : Fin D → ℝ
  /-- The migration rate from a source deme into a target deme. -/
  migration : Fin D → Fin D → ℝ
  /-- The symmetric mutation parameter of every deme. -/
  mutation : Fin D → ℝ
  /-- The recombination parameter of every deme. -/
  recombination : Fin D → ℝ
  coalescence_nonneg : ∀ deme, 0 ≤ coalescence deme
  migration_nonneg : ∀ source target, 0 ≤ migration source target
  migration_self : ∀ deme, migration deme deme = 0
  mutation_nonneg : ∀ deme, 0 ≤ mutation deme
  recombination_nonneg : ∀ deme, 0 ≤ recombination deme

variable {D : ℕ}

/-- The rate coordinates of a nonnegative rate law. -/
def NonnegativeLDRates.coordinates (rates : NonnegativeLDRates D) : RateCoordinates D :=
  (rates.coalescence, rates.migration, rates.mutation, rates.recombination)

/-- A corpus rate law, whose coalescence is positive, read as a nonnegative rate law. -/
def NonnegativeLDRates.ofRates (rates : ManyDemeLDRates D) : NonnegativeLDRates D where
  coalescence := rates.coalescence
  migration := rates.migration
  mutation := rates.mutation
  recombination := rates.recombination
  coalescence_nonneg deme := (rates.coalescence_pos deme).le
  migration_nonneg := rates.migration_nonneg
  migration_self := rates.migration_self
  mutation_nonneg := rates.mutation_nonneg
  recombination_nonneg := rates.recombination_nonneg

/-- The corpus rate law obtained by raising every coalescence rate by a positive amount. -/
def NonnegativeLDRates.perturb (rates : NonnegativeLDRates D) (amount : ℝ) (hamount : 0 < amount) :
    ManyDemeLDRates D where
  coalescence deme := rates.coalescence deme + amount
  migration := rates.migration
  mutation := rates.mutation
  recombination := rates.recombination
  coalescence_pos deme := add_pos_of_nonneg_of_pos (rates.coalescence_nonneg deme) hamount
  migration_nonneg := rates.migration_nonneg
  migration_self := rates.migration_self
  mutation_nonneg := rates.mutation_nonneg
  recombination_nonneg := rates.recombination_nonneg

/-- **The low-order generator at nonnegative coalescence.** The corpus generator extended
linearly to signed rate coordinates, read at the rate coordinates of the law. -/
def NonnegativeLDRates.generator (rates : NonnegativeLDRates D) :
    Matrix (AffineLowOrderLDCoordinate D) (AffineLowOrderLDCoordinate D) ℝ :=
  generatorLinearMap D rates.coordinates

/-- The rate coordinates of unit coalescence in every deme and no other process. -/
def unitCoalescenceDirection (D : ℕ) : RateCoordinates D :=
  (fun _ ↦ 1, 0, 0, 0)

/-- A rate law with no coalescence at all: unit migration between distinct demes and unit
mutation and recombination parameters. It lies outside the positive-coalescence domain of the
corpus while exercising every other process. -/
def coalescenceFreeRates (D : ℕ) : NonnegativeLDRates D where
  coalescence _ := 0
  migration source target := if source = target then 0 else 1
  mutation _ := 1
  recombination _ := 1
  coalescence_nonneg _ := le_refl 0
  migration_nonneg source target := by
    split_ifs
    · exact le_refl 0
    · exact zero_le_one
  migration_self _ := if_pos rfl
  mutation_nonneg _ := zero_le_one
  recombination_nonneg _ := zero_le_one

/-- No corpus rate law reads as the coalescence-free rate law: the nonnegative rate laws strictly
extend the corpus ones. -/
theorem ofRates_ne_coalescenceFreeRates (deme : Fin D) (rates : ManyDemeLDRates D) :
    NonnegativeLDRates.ofRates rates ≠ coalescenceFreeRates D := by
  intro hequal
  have hcoalescence :=
    congrArg (fun other : NonnegativeLDRates D ↦ other.coalescence deme) hequal
  have hpositive := rates.coalescence_pos deme
  simp only [NonnegativeLDRates.ofRates, coalescenceFreeRates] at hcoalescence
  linarith

/-- **At positive coalescence the generator is the corpus generator.** -/
theorem generator_ofRates (rates : ManyDemeLDRates D) :
    (NonnegativeLDRates.ofRates rates).generator = augmentedLowOrderLDGenerator rates :=
  (augmentedLowOrderLDGenerator_eq_generatorLinearMap rates).symm

/-- **The perturbed corpus generator.** Raising every coalescence rate by `amount > 0` gives the
corpus generator of a genuine rate law, equal to the nonnegative-coalescence generator plus
`amount` times the generator of unit coalescence. -/
theorem generator_perturb (rates : NonnegativeLDRates D) (amount : ℝ) (hamount : 0 < amount) :
    augmentedLowOrderLDGenerator (rates.perturb amount hamount) =
      rates.generator + amount • generatorLinearMap D (unitCoalescenceDirection D) := by
  have hcoordinates : rateCoordinates (rates.perturb amount hamount) =
      rates.coordinates + amount • unitCoalescenceDirection D := by
    refine Prod.ext (funext fun deme ↦ ?_)
      (Prod.ext (funext fun source ↦ funext fun target ↦ ?_)
        (Prod.ext (funext fun deme ↦ ?_) (funext fun deme ↦ ?_)))
    all_goals simp [rateCoordinates, NonnegativeLDRates.perturb, NonnegativeLDRates.coordinates,
      unitCoalescence]
  rw [augmentedLowOrderLDGenerator_eq_generatorLinearMap, hcoordinates, map_add, map_smul]
  rfl

/-- **The generator is the limit of corpus generators.** Along `amount = 1 / (n + 1)` the corpus
generators of the perturbed rate laws converge to the nonnegative-coalescence generator. -/
theorem tendsto_generator_perturb (rates : NonnegativeLDRates D) :
    Tendsto (fun n : ℕ ↦ augmentedLowOrderLDGenerator
        (rates.perturb (1 / ((n : ℝ) + 1)) Nat.one_div_pos_of_nat)) atTop
      (𝓝 rates.generator) := by
  simp only [generator_perturb]
  have hlimit := (tendsto_one_div_add_atTop_nhds_zero_nat.smul_const
    (generatorLinearMap D (unitCoalescenceDirection D))).const_add rates.generator
  simpa using hlimit

/-! ## NOTE1 Theorem 2 at nonnegative coalescence -/

/-- **The epoch of a nonnegative rate law.** The corpus epoch with the nonnegative-coalescence
generator; its constant row vanishes because it does for every corpus generator. -/
def NonnegativeLDRates.epoch (rates : NonnegativeLDRates D) (duration : ℝ)
    (duration_nonneg : 0 ≤ duration) : LowOrderLDEpoch D where
  generator := rates.generator
  duration := duration
  duration_nonneg := duration_nonneg
  constant_row coordinate := by
    show (augmentedLowOrderLDGenerator (positivePartRates rates.coordinates) -
      augmentedLowOrderLDGenerator (positivePartRates (-rates.coordinates))) none coordinate = 0
    rw [Matrix.sub_apply]
    exact sub_eq_zero.mpr rfl

/-- At positive coalescence the epoch is the corpus epoch. -/
theorem epoch_ofRates (rates : ManyDemeLDRates D) (duration : ℝ) (hduration : 0 ≤ duration) :
    (NonnegativeLDRates.ofRates rates).epoch duration hduration =
      rates.epoch duration hduration := by
  unfold NonnegativeLDRates.epoch ManyDemeLDRates.epoch
  congr 1
  exact generator_ofRates rates

/-- **Continuity of the epoch propagator in the rates.** The propagated states of the perturbed
corpus epochs converge to the propagated state of the nonnegative-coalescence epoch, because the
generators converge and the matrix exponential and the action on a state are continuous. -/
theorem tendsto_perturbedEpoch_mulVec (rates : NonnegativeLDRates D) (duration : ℝ)
    (state : AffineLowOrderLDCoordinate D → ℝ) :
    Tendsto (fun n : ℕ ↦ (matrixExponential (augmentedLowOrderLDGenerator
        (rates.perturb (1 / ((n : ℝ) + 1)) Nat.one_div_pos_of_nat)) duration).mulVec state)
      atTop (𝓝 ((matrixExponential rates.generator duration).mulVec state)) := by
  have hcontinuous : Continuous (fun generator :
      Matrix (AffineLowOrderLDCoordinate D) (AffineLowOrderLDCoordinate D) ℝ ↦
        (matrixExponential generator duration).mulVec state) := by
    simp only [matrixExponential_eq_normedSpace_exp]
    exact (EulerInvariantSet.mulVecMap state).continuous_of_finiteDimensional.comp
      (NormedSpace.exp_continuous.comp (continuous_const_smul duration))
  exact (hcontinuous.tendsto _).comp (tendsto_generator_perturb rates)

/-- **NOTE1 Theorem 2 for one epoch at nonnegative coalescence.** For every nonnegative rate law,
including one in which some deme has no coalescence, and every nonnegative duration, the epoch
propagator maps a locus-exchangeably realizable stored state to a locus-exchangeably realizable
one. -/
theorem nonnegativeEpoch_preserves_locusExchangeable_realization (rates : NonnegativeLDRates D)
    (duration : ℝ) (hduration : 0 ≤ duration) {state : AffineLowOrderLDCoordinate D → ℝ}
    (realization : LocusExchangeableLowOrderLDHaplotypeRealization state) :
    Nonempty (LocusExchangeableLowOrderLDHaplotypeRealization
      ((rates.epoch duration hduration).propagator.mulVec state)) := by
  have hmember : ∀ n : ℕ, (matrixExponential (augmentedLowOrderLDGenerator
      (rates.perturb (1 / ((n : ℝ) + 1)) Nat.one_div_pos_of_nat)) duration).mulVec state ∈
        exchangeableStates D := fun n ↦
    (mem_exchangeableStates_iff _).mpr (rateEpoch_preserves_locusExchangeable_realization
      (rates.perturb (1 / ((n : ℝ) + 1)) Nat.one_div_pos_of_nat) duration hduration realization)
  exact (mem_exchangeableStates_iff _).mp ((isClosed_exchangeableStates D).mem_of_tendsto
    (tendsto_perturbedEpoch_mulVec rates duration state) (Eventually.of_forall hmember))

/-- The propagated state of one epoch at nonnegative coalescence lies in the stored realization
body. -/
theorem nonnegativeEpoch_mulVec_mem_realizationBody (rates : NonnegativeLDRates D)
    (duration : ℝ) (hduration : 0 ≤ duration) {state : AffineLowOrderLDCoordinate D → ℝ}
    (realization : LocusExchangeableLowOrderLDHaplotypeRealization state) :
    (rates.epoch duration hduration).propagator.mulVec state ∈
      realizationBody (lowOrderLDFeature D) := by
  obtain ⟨propagated⟩ :=
    nonnegativeEpoch_preserves_locusExchangeable_realization rates duration hduration realization
  exact KernelRealizationPreservation.lowOrderLDState_mem_realizationBody_of_realization
    propagated.toLowOrderLDHaplotypeRealization

/-- One event of a compiled demographic history at nonnegative coalescence: an epoch of a
nonnegative rate law for a nonnegative duration, or a physically realized split. -/
inductive NonnegativeRateEvent (D : ℕ) where
  /-- Continuous evolution under `rates` for `duration`. -/
  | evolve (rates : NonnegativeLDRates D) (duration : ℝ) (duration_nonneg : 0 ≤ duration)
  /-- The child deme is founded as a copy of the parent deme. -/
  | split (parent child : Fin D)

/-- The corpus instruction an event compiles to: the epoch of the rate law, or the corpus
split. -/
def NonnegativeRateEvent.instruction : NonnegativeRateEvent D → LowOrderLDInstruction D
  | .evolve rates duration duration_nonneg => .evolve (rates.epoch duration duration_nonneg)
  | .split parent child => LowOrderLDInstruction.split parent child

/-- A two-deme epoch of the coalescence-free rate law for unit time: an event no corpus
`RateHistoryEvent` can express. -/
def coalescenceFreeEvent : NonnegativeRateEvent 2 :=
  .evolve (coalescenceFreeRates 2) 1 zero_le_one

/-- At positive coalescence an epoch event compiles to the instruction of the corpus event. -/
theorem instruction_evolve_ofRates (rates : ManyDemeLDRates D) (duration : ℝ)
    (hduration : 0 ≤ duration) :
    (NonnegativeRateEvent.evolve (NonnegativeLDRates.ofRates rates) duration
        hduration).instruction =
      (RateHistoryEvent.evolve rates duration hduration).instruction :=
  congrArg LowOrderLDInstruction.evolve (epoch_ofRates rates duration hduration)

/-- Every event preserves locus-exchangeable realizability: an epoch by the one-epoch theorem,
and a split because it relabels the very same haplotype law. -/
theorem NonnegativeRateEvent.preserves_locusExchangeable_realization
    (event : NonnegativeRateEvent D) {state : AffineLowOrderLDCoordinate D → ℝ}
    (realization : LocusExchangeableLowOrderLDHaplotypeRealization state) :
    Nonempty (LocusExchangeableLowOrderLDHaplotypeRealization
      (event.instruction.apply state)) := by
  cases event with
  | evolve rates duration duration_nonneg =>
      exact nonnegativeEpoch_preserves_locusExchangeable_realization rates duration
        duration_nonneg realization
  | split parent child =>
      exact ⟨TwoLocusRealizabilityPreservation.locusExchangeableSplit realization parent child⟩

/-- **NOTE1 Theorem 2 for a finite history at nonnegative coalescence.** Composing any finite list
of epochs at nonnegative coalescence and physically realized splits carries a locus-exchangeably
realizable stored state to a locus-exchangeably realizable one. -/
theorem nonnegativePropagate_preserves_locusExchangeable_realization
    (events : List (NonnegativeRateEvent D)) {initial : AffineLowOrderLDCoordinate D → ℝ}
    (realization : LocusExchangeableLowOrderLDHaplotypeRealization initial) :
    Nonempty (LocusExchangeableLowOrderLDHaplotypeRealization
      (propagateLowOrderLDInstructions (events.map NonnegativeRateEvent.instruction) initial)) := by
  induction events generalizing initial with
  | nil => exact ⟨realization⟩
  | cons head rest ih =>
      obtain ⟨propagated⟩ := head.preserves_locusExchangeable_realization realization
      exact ih propagated

/-- The present state of a history compiled from epochs at nonnegative coalescence and splits is
locus-exchangeably realizable whenever its initial state is. -/
theorem nonnegativeHistory_present_locusExchangeable_realization (history : LowOrderLDHistory D)
    (events : List (NonnegativeRateEvent D))
    (hcompiled : history.instructions = events.map NonnegativeRateEvent.instruction)
    (realization : LocusExchangeableLowOrderLDHaplotypeRealization history.initial) :
    Nonempty (LocusExchangeableLowOrderLDHaplotypeRealization history.present) := by
  rw [LowOrderLDHistory.present, hcompiled]
  exact nonnegativePropagate_preserves_locusExchangeable_realization events realization

/-! ## NOTE1 Corollary 2.1 at nonnegative coalescence -/

/-- **The propagated `DD` block is positive semidefinite** after every history compiled from
epochs at nonnegative coalescence and splits. -/
theorem nonnegativeHistory_present_dd_quadraticForm_nonneg (history : LowOrderLDHistory D)
    (events : List (NonnegativeRateEvent D))
    (hcompiled : history.instructions = events.map NonnegativeRateEvent.instruction)
    (realization : LocusExchangeableLowOrderLDHaplotypeRealization history.initial)
    (weight : Fin D → ℝ) :
    0 ≤ ∑ first, ∑ second,
      weight first * history.present (some (.DD first second)) * weight second := by
  obtain ⟨propagated⟩ := nonnegativeHistory_present_locusExchangeable_realization history events
    hcompiled realization
  exact propagated.toLowOrderLDHaplotypeRealization.toDDDRealization.dd_quadraticForm_nonneg
    weight

/-- NOTE1 (13) at nonnegative coalescence: the propagated cross-deme `DD` entries obey
Cauchy–Schwarz against the propagated diagonals. -/
theorem nonnegativeHistory_present_dd_cauchySchwarz (history : LowOrderLDHistory D)
    (events : List (NonnegativeRateEvent D))
    (hcompiled : history.instructions = events.map NonnegativeRateEvent.instruction)
    (realization : LocusExchangeableLowOrderLDHaplotypeRealization history.initial)
    (first second : Fin D) :
    history.present (some (.DD first second)) ^ 2 ≤
      history.present (some (.DD first first)) *
        history.present (some (.DD second second)) := by
  obtain ⟨propagated⟩ := nonnegativeHistory_present_locusExchangeable_realization history events
    hcompiled realization
  exact propagated.toLowOrderLDHaplotypeRealization.toDDDRealization.dd_cauchySchwarz first
    second

/-- The propagated within-deme `DD` diagonal is nonnegative at nonnegative coalescence. -/
theorem nonnegativeHistory_present_dd_diagonal_nonneg (history : LowOrderLDHistory D)
    (events : List (NonnegativeRateEvent D))
    (hcompiled : history.instructions = events.map NonnegativeRateEvent.instruction)
    (realization : LocusExchangeableLowOrderLDHaplotypeRealization history.initial)
    (deme : Fin D) :
    0 ≤ history.present (some (.DD deme deme)) := by
  obtain ⟨propagated⟩ := nonnegativeHistory_present_locusExchangeable_realization history events
    hcompiled realization
  exact propagated.toLowOrderLDHaplotypeRealization.toDDDRealization.dd_diagonal_nonneg deme

/-- **NOTE1 Corollary 2.1 at the `EndToEndScoreLaw` endpoint, at nonnegative coalescence.** For
a separation-indexed family of histories compiled from epochs at nonnegative coalescence and
splits, started from locus-exchangeably realizable states, the normalized linkage-pair domain
holds at every pair of demes whose within-deme `DD` entries are nonzero. -/
theorem nonnegativeHistory_LDPairDomain (historyAt : MarkerSeparationBp → LowOrderLDHistory D)
    (eventsAt : MarkerSeparationBp → List (NonnegativeRateEvent D))
    (hcompiled : ∀ separation,
      (historyAt separation).instructions =
        (eventsAt separation).map NonnegativeRateEvent.instruction)
    (separation : MarkerSeparationBp) (first second : Fin D)
    (realization :
      LocusExchangeableLowOrderLDHaplotypeRealization (historyAt separation).initial)
    (first_ne : (historyAt separation).present (some (.DD first first)) ≠ 0)
    (second_ne : (historyAt separation).present (some (.DD second second)) ≠ 0) :
    (LowOrderLDHistory.toDemographicTwoLocusMoments historyAt).LDPairDomain
      separation first second := by
  obtain ⟨propagated⟩ := nonnegativeHistory_present_locusExchangeable_realization
    (historyAt separation) (eventsAt separation) (hcompiled separation) realization
  have hwitness := propagated.toLowOrderLDHaplotypeRealization.toDDDRealization
  exact hwitness.toLDPairDomain historyAt separation first second
    (lt_of_le_of_ne (hwitness.dd_diagonal_nonneg first) (Ne.symm first_ne))
    (lt_of_le_of_ne (hwitness.dd_diagonal_nonneg second) (Ne.symm second_ne))

end

end Descent.Portability.NonnegativeCoalescenceRealization
