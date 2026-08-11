/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Coalescent.StructuredPresentDay

assert_below Descent.Pangenome Descent.PopGen Descent.Spectral Descent.Blindness
assert_below Descent.Conditionals Descent.Portability Descent.Decision Descent.Program

namespace Descent.Coalescent

/-!
# Exact composition of a multi-deme two-locus moment history

The linkage factor between nonadjacent demes does not in general compose as a scalar power
of the adjacent-deme correlation.  Migration couples the complete closed family of `H`,
`DD`, `Dz`, and `pi2` coordinates.  The exact composition law is consequently an ordered
product of the epoch semigroups on that joint state, followed by the requested `DD` readout.

This file supplies that composition law and the concrete Wright--Fisher/diffusion generator
for the closed moment family.  Arbitrary numbers of epochs, demes, splits, migration changes,
mutation changes, and recombination changes are composed without a closure approximation or
fitted distance law.

## Empirical status

Stated once here for the generator entries and the composition machinery built from them,
following `TwoDemeLDClosedForm`'s section: they share one verdict and thirteen copies of it
would be thirteen places for it to drift.

THE GENERATOR ENTRIES ARE THE MODEL.  `lowOrderLDDrift`, `lowOrderLDMigration`,
`lowOrderLDRecombination`, `lowOrderLDMutationCoupling` and `lowOrderLDMutationForcing` are
the Ragsdale--Gravel two-locus moment generator written for an arbitrary deme count, and
`lowOrderLDBasis`, `lowOrderLDHomogeneousGenerator`, `augmentedLowOrderLDGenerator`, and
`LowOrderLDEpoch.propagator` assemble them into matrices and epoch semigroups.  Writing them
down is choosing a
reproduction, migration, mutation and recombination mechanism, not asserting anything about
a population, so no measurement can bear on an entry: what could be wrong is whether a
population is described by this generator at all, and that question is asked wherever the
composed output is compared against something.

THE COMPOSITION LAW IS DERIVED AND NOT MEASURED.  The explicit one-deme equilibrium below
is proved to solve all four stationary equations.  `commonAncestralLowOrderLDState` relabels
that equilibrium across a split, `lowOrderLDSplitTransform` is the label-replacement matrix
a split forces, and `propagateLowOrderLDInstructions` is an ordered `foldl` whose chain law
`propagateLowOrderLDInstructions_append` is proved below.  An arithmetic consequence of a
model is true of the model whatever a population does.

WHAT THIS SECTION DOES NOT COVER, named rather than left silent.  The quantity this file
exists to supply downstream is `LowOrderLDHistory.toDemographicTwoLocusMoments`, whose `DD`
readout becomes `StructuredPresentDay`'s cross-deme LD correlation.  That readout IS an
empirical claim once a demography is filled in -- a simulation can contradict its composed
prediction -- and no battery has recorded a verdict on any composed history from this file
yet.  Supplying one means integrating the same moment system numerically
(`validation/empirical/momentsld/ld_surface.py` integrates the two-deme slice) and comparing
the composed operator product against it, which is a measurement nobody has recorded here.
-/

/-- Redundant but finite carrier of the closed low-order multi-population LD family.
Keeping all ordered population indices avoids quotient bookkeeping; symmetry identities may
be proved by a concrete generator and do not alter the evolution law. -/
inductive LowOrderLDCoordinate (D : ℕ) where
  | H (first second : Fin D)
  | DD (first second : Fin D)
  | Dz (first second third : Fin D)
  | pi2 (first second third fourth : Fin D)
deriving DecidableEq, Fintype, Repr

/-- Add a constant coordinate so mutation influx and other affine source terms evolve in the
same matrix exponential as the homogeneous moments. -/
abbrev AffineLowOrderLDCoordinate (D : ℕ) := Option (LowOrderLDCoordinate D)

/-! ## The concrete arbitrary-deme generator -/

/-- Rates of the closed multi-deme `H/DD/Dz/pi2` system in one declared time scale. -/
structure ManyDemeLDRates (D : ℕ) where
  coalescence : Fin D → ℝ
  migration : Fin D → Fin D → ℝ
  mutation : Fin D → ℝ
  recombination : Fin D → ℝ
  coalescence_pos : ∀ deme, 0 < coalescence deme
  migration_nonneg : ∀ source target, 0 ≤ migration source target
  migration_self : ∀ deme, migration deme deme = 0
  mutation_nonneg : ∀ deme, 0 ≤ mutation deme
  recombination_nonneg : ∀ deme, 0 ≤ recombination deme

/-- Basis state used to read one coefficient of the concrete generator. -/
def lowOrderLDBasis {D : ℕ} (column : LowOrderLDCoordinate D) :
    LowOrderLDCoordinate D → ℝ :=
  fun coordinate ↦ if coordinate = column then 1 else 0

/-- Drift contribution to the closed low-order system.  The cases are equality patterns of
the population indices, not separate demographic assumptions. -/
noncomputable def lowOrderLDDrift {D : ℕ} (rates : ManyDemeLDRates D)
    (moment : LowOrderLDCoordinate D → ℝ) : LowOrderLDCoordinate D → ℝ
  | .H first second =>
      if first = second then -rates.coalescence first * moment (.H first second) else 0
  | .DD first second =>
      if first = second then
        rates.coalescence first *
          (-3 * moment (.DD first first) + moment (.Dz first first first) +
            moment (.pi2 first first first first))
      else
        -(rates.coalescence first + rates.coalescence second) * moment (.DD first second)
  | .Dz first second third =>
      if first = second ∧ second = third then
        rates.coalescence first *
          (4 * moment (.DD first first) - 5 * moment (.Dz first second third))
      else if first = second then
        -3 * rates.coalescence first * moment (.Dz first second third)
      else if first = third then
        -3 * rates.coalescence first * moment (.Dz first second third)
      else if second = third then
        4 * rates.coalescence second * moment (.DD first second) -
          rates.coalescence first * moment (.Dz first second third)
      else
        -rates.coalescence first * moment (.Dz first second third)
  | .pi2 first second third fourth =>
      if first = second ∧ second = third ∧ third = fourth then
        rates.coalescence first *
          (moment (.Dz first first first) - 2 * moment (.pi2 first second third fourth))
      else if first = second ∧ second = third then
        rates.coalescence first *
          (moment (.Dz first first fourth) / 2 - moment (.pi2 first second third fourth))
      else if first = second ∧ second = fourth then
        rates.coalescence first *
          (moment (.Dz first first third) / 2 - moment (.pi2 first second third fourth))
      else if first = third ∧ third = fourth then
        rates.coalescence first *
          (moment (.Dz first second first) / 2 - moment (.pi2 first second third fourth))
      else if second = third ∧ third = fourth then
        rates.coalescence second *
          (moment (.Dz second first second) / 2 - moment (.pi2 first second third fourth))
      else if first = second ∧ third = fourth then
        -(rates.coalescence first + rates.coalescence third) *
          moment (.pi2 first second third fourth)
      else if (first = third ∧ second = fourth) ∨ (first = fourth ∧ second = third) then
        rates.coalescence first / 4 * moment (.Dz first second second) +
          rates.coalescence second / 4 * moment (.Dz second first first)
      else if first = second then
        -rates.coalescence first * moment (.pi2 first second third fourth)
      else if first = third then
        rates.coalescence first / 4 * moment (.Dz first second fourth)
      else if first = fourth then
        rates.coalescence first / 4 * moment (.Dz first second third)
      else if second = third then
        rates.coalescence second / 4 * moment (.Dz second first fourth)
      else if second = fourth then
        rates.coalescence second / 4 * moment (.Dz second first third)
      else if third = fourth then
        -rates.coalescence third * moment (.pi2 first second third fourth)
      else 0

/-- Continuous migration contribution.  Each lineage index migrates separately.  The extra
`Dz` and `pi2` differences are exactly the terms created because `D` is nonlinear in
haplotype frequencies; this is where migration restores shared linkage. -/
noncomputable def lowOrderLDMigration {D : ℕ} (rates : ManyDemeLDRates D)
    (moment : LowOrderLDCoordinate D → ℝ) : LowOrderLDCoordinate D → ℝ
  | .H first second =>
      (∑ target, rates.migration first target *
        (moment (.H target second) - moment (.H first second))) +
      (∑ target, rates.migration second target *
        (moment (.H first target) - moment (.H first second)))
  | .DD first second =>
      (∑ target, rates.migration first target *
        (moment (.DD target second) - moment (.DD first second) +
          (moment (.Dz second first first) - moment (.Dz second first target) -
            moment (.Dz second target first) + moment (.Dz second target target)) / 4)) +
      (∑ target, rates.migration second target *
        (moment (.DD first target) - moment (.DD first second) +
          (moment (.Dz first second second) - moment (.Dz first second target) -
            moment (.Dz first target second) + moment (.Dz first target target)) / 4))
  | .Dz first second third =>
      (∑ target, rates.migration first target *
        (moment (.Dz target second third) - moment (.Dz first second third) +
          4 * (moment (.pi2 first second first third) -
            moment (.pi2 first second third target) -
            moment (.pi2 second target first third) +
            moment (.pi2 second target third target)))) +
      (∑ target, rates.migration second target *
        (moment (.Dz first target third) - moment (.Dz first second third))) +
      (∑ target, rates.migration third target *
        (moment (.Dz first second target) - moment (.Dz first second third)))
  | .pi2 first second third fourth =>
      (∑ target, rates.migration first target *
        (moment (.pi2 target second third fourth) -
          moment (.pi2 first second third fourth))) +
      (∑ target, rates.migration second target *
        (moment (.pi2 first target third fourth) -
          moment (.pi2 first second third fourth))) +
      (∑ target, rates.migration third target *
        (moment (.pi2 first second target fourth) -
          moment (.pi2 first second third fourth))) +
      (∑ target, rates.migration fourth target *
        (moment (.pi2 first second third target) -
          moment (.pi2 first second third fourth)))

/-- Recombination damps each `D` factor at half its deme-specific scaled rate. -/
noncomputable def lowOrderLDRecombination {D : ℕ} (rates : ManyDemeLDRates D)
    (moment : LowOrderLDCoordinate D → ℝ) : LowOrderLDCoordinate D → ℝ
  | .H _ _ => 0
  | .DD first second =>
      -(rates.recombination first + rates.recombination second) / 2 *
        moment (.DD first second)
  | .Dz first second third =>
      -rates.recombination first / 2 * moment (.Dz first second third)
  | .pi2 _ _ _ _ => 0

/-- Mutation coupling from single-locus heterozygosity into joint heterozygosity. -/
noncomputable def lowOrderLDMutationCoupling {D : ℕ} (rates : ManyDemeLDRates D)
    (moment : LowOrderLDCoordinate D → ℝ) : LowOrderLDCoordinate D → ℝ
  | .pi2 first second third fourth =>
      (rates.mutation third + rates.mutation fourth) / 8 * moment (.H first second) +
      (rates.mutation first + rates.mutation second) / 8 * moment (.H third fourth)
  | _ => 0

/-- Affine mutation influx into the heterozygosity coordinates. -/
noncomputable def lowOrderLDMutationForcing {D : ℕ} (rates : ManyDemeLDRates D) :
    LowOrderLDCoordinate D → ℝ
  | .H first second => (rates.mutation first + rates.mutation second) / 2
  | _ => 0

/-- The derived homogeneous generator for arbitrary deme count. -/
noncomputable def lowOrderLDHomogeneousGenerator {D : ℕ} (rates : ManyDemeLDRates D)
    (moment : LowOrderLDCoordinate D → ℝ) (coordinate : LowOrderLDCoordinate D) : ℝ :=
  lowOrderLDDrift rates moment coordinate + lowOrderLDMigration rates moment coordinate +
    lowOrderLDRecombination rates moment coordinate +
    lowOrderLDMutationCoupling rates moment coordinate

/-- Concrete constant-augmented matrix of the arbitrary-deme moment ODE. -/
noncomputable def augmentedLowOrderLDGenerator {D : ℕ} (rates : ManyDemeLDRates D) :
    Matrix (AffineLowOrderLDCoordinate D) (AffineLowOrderLDCoordinate D) ℝ
  | some row, some column => lowOrderLDHomogeneousGenerator rates (lowOrderLDBasis column) row
  | some row, none => lowOrderLDMutationForcing rates row
  | none, _ => 0

/-- Positive denominator of the closed one-deme stationary `DD/Dz/pi2` solve. -/
noncomputable def oneDemeLDStationaryDenominator (rates : ManyDemeLDRates 1) : ℝ :=
  18 * rates.coalescence 0 ^ 2 +
    13 * rates.coalescence 0 * rates.recombination 0 + rates.recombination 0 ^ 2

/-- The one-deme stationary denominator cannot hit a Cramer pole on the physical rate
domain. -/
theorem oneDemeLDStationaryDenominator_pos (rates : ManyDemeLDRates 1) :
    0 < oneDemeLDStationaryDenominator rates := by
  unfold oneDemeLDStationaryDenominator
  have hc := rates.coalescence_pos 0
  have hr := rates.recombination_nonneg 0
  nlinarith [sq_pos_of_pos hc, sq_nonneg (rates.recombination 0)]

/-- Closed stationary solution of the four one-deme equations.  Writing
`c = 1/(2N)`, `theta = 2u`, and `rho = 2r`, the solution is

`H = theta/c`,
`DD = theta²(10c+rho)/(4c(18c²+13c rho+rho²))`,
`Dz = 2theta²/(18c²+13c rho+rho²)`, and
`pi2 = theta²/(18c²+13c rho+rho²) + theta²/(4c²)`.

Thus the ancestral boundary has no fitted moment table and no unchecked determinant. -/
noncomputable def oneDemeStationaryLowOrderLDState (rates : ManyDemeLDRates 1) :
    AffineLowOrderLDCoordinate 1 → ℝ
  | none => 1
  | some (.H _ _) => rates.mutation 0 / rates.coalescence 0
  | some (.DD _ _) =>
      rates.mutation 0 ^ 2 *
        (10 * rates.coalescence 0 + rates.recombination 0) /
      (4 * rates.coalescence 0 * oneDemeLDStationaryDenominator rates)
  | some (.Dz _ _ _) =>
      2 * rates.mutation 0 ^ 2 / oneDemeLDStationaryDenominator rates
  | some (.pi2 _ _ _ _) =>
      rates.mutation 0 ^ 2 / oneDemeLDStationaryDenominator rates +
        rates.mutation 0 ^ 2 / (4 * rates.coalescence 0 ^ 2)

/-- The closed ancestral values solve all four stationary generator equations. -/
theorem oneDemeStationaryLowOrderLDState_equations (rates : ManyDemeLDRates 1) :
    let state := oneDemeStationaryLowOrderLDState rates
    let c := rates.coalescence 0
    let theta := rates.mutation 0
    let rho := rates.recombination 0
    theta - c * state (some (.H 0 0)) = 0 ∧
      -(3 * c + rho) * state (some (.DD 0 0)) +
          c * state (some (.Dz 0 0 0)) + c * state (some (.pi2 0 0 0 0)) = 0 ∧
      4 * c * state (some (.DD 0 0)) -
          (5 * c + rho / 2) * state (some (.Dz 0 0 0)) = 0 ∧
      c * state (some (.Dz 0 0 0)) - 2 * c * state (some (.pi2 0 0 0 0)) +
          theta / 2 * state (some (.H 0 0)) = 0 := by
  have hc : rates.coalescence 0 ≠ 0 := ne_of_gt (rates.coalescence_pos 0)
  have hden : oneDemeLDStationaryDenominator rates ≠ 0 :=
    ne_of_gt (oneDemeLDStationaryDenominator_pos rates)
  dsimp [oneDemeStationaryLowOrderLDState, oneDemeLDStationaryDenominator] at *
  have hden' : rates.coalescence 0 * rates.recombination 0 * 13 +
      rates.coalescence 0 ^ 2 * 18 + rates.recombination 0 ^ 2 ≠ 0 := by
    intro h
    exact hden (by linarith)
  constructor
  · field_simp [hc] <;> ring
  constructor
  · field_simp [hc, hden, hden']
    linear_combination (-(rates.mutation 0 ^ 2)) * mul_inv_cancel₀ hden'
  constructor
  · field_simp [hc, hden, hden'] <;> ring
  · field_simp [hc, hden, hden'] <;> ring

/-- Collapse an arbitrary-deme coordinate to the unique coordinate of a single common
ancestral deme. -/
def LowOrderLDCoordinate.collapseToOneDeme {D : ℕ} :
    LowOrderLDCoordinate D → LowOrderLDCoordinate 1
  | .H _ _ => .H 0 0
  | .DD _ _ => .DD 0 0
  | .Dz _ _ _ => .Dz 0 0 0
  | .pi2 _ _ _ _ => .pi2 0 0 0 0

/-- Lift a derived one-deme equilibrium state to the instant before the first split, where
all descendant labels denote the same ancestral population. -/
noncomputable def commonAncestralLowOrderLDState {D : ℕ}
    (ancestralRates : ManyDemeLDRates 1) : AffineLowOrderLDCoordinate D → ℝ
  | none => 1
  | some coordinate =>
      oneDemeStationaryLowOrderLDState ancestralRates (some coordinate.collapseToOneDeme)

/-- One piecewise-constant epoch of a derived low-order two-locus moment system. -/
structure LowOrderLDEpoch (D : ℕ) where
  generator : Matrix (AffineLowOrderLDCoordinate D) (AffineLowOrderLDCoordinate D) ℝ
  duration : ℝ
  duration_nonneg : 0 ≤ duration
  constant_row : ∀ coordinate, generator none coordinate = 0

/-- Build an epoch directly from the derived arbitrary-deme rate law. -/
noncomputable def ManyDemeLDRates.epoch {D : ℕ} (rates : ManyDemeLDRates D)
    (duration : ℝ) (duration_nonneg : 0 ≤ duration) : LowOrderLDEpoch D where
  generator := augmentedLowOrderLDGenerator rates
  duration := duration
  duration_nonneg := duration_nonneg
  constant_row := fun _ ↦ rfl

/-- The exactly evaluable semigroup of one epoch. -/
noncomputable def LowOrderLDEpoch.propagator {D : ℕ} (epoch : LowOrderLDEpoch D) :
    Matrix (AffineLowOrderLDCoordinate D) (AffineLowOrderLDCoordinate D) ℝ :=
  matrixExponential epoch.generator epoch.duration

/-- A demographic instruction is continuous evolution or a derived instantaneous linear map.
Splits, pulses, and admixture events are instances of `instantaneous`; none is replaced by a
scalar retention coefficient. -/
inductive LowOrderLDInstruction (D : ℕ) where
  | evolve (epoch : LowOrderLDEpoch D)
  | instantaneous
      (transform : Matrix (AffineLowOrderLDCoordinate D) (AffineLowOrderLDCoordinate D) ℝ)

/-- Replace every occurrence of a newly created child label by its parent label. -/
def LowOrderLDCoordinate.mergeSplit {D : ℕ} (parent child : Fin D) :
    LowOrderLDCoordinate D → LowOrderLDCoordinate D
  | .H first second => .H (if first = child then parent else first)
      (if second = child then parent else second)
  | .DD first second => .DD (if first = child then parent else first)
      (if second = child then parent else second)
  | .Dz first second third => .Dz (if first = child then parent else first)
      (if second = child then parent else second) (if third = child then parent else third)
  | .pi2 first second third fourth =>
      .pi2 (if first = child then parent else first)
        (if second = child then parent else second)
        (if third = child then parent else third)
        (if fourth = child then parent else fourth)

/-- Exact instantaneous split matrix: immediately after a split the child's haplotype
frequencies equal the parent's, so every new coordinate pulls back by label replacement. -/
def lowOrderLDSplitTransform {D : ℕ} (parent child : Fin D) :
    Matrix (AffineLowOrderLDCoordinate D) (AffineLowOrderLDCoordinate D) ℝ
  | none, none => 1
  | some row, some column => if row.mergeSplit parent child = column then 1 else 0
  | _, _ => 0

/-- Concrete split instruction for the arbitrary-deme history compiler. -/
def LowOrderLDInstruction.split {D : ℕ} (parent child : Fin D) :
    LowOrderLDInstruction D :=
  .instantaneous (lowOrderLDSplitTransform parent child)

/-- Apply one exact demographic instruction to the full joint moment state. -/
noncomputable def LowOrderLDInstruction.apply {D : ℕ}
    (instruction : LowOrderLDInstruction D)
    (state : AffineLowOrderLDCoordinate D → ℝ) :
    AffineLowOrderLDCoordinate D → ℝ :=
  match instruction with
  | .evolve epoch => epoch.propagator.mulVec state
  | .instantaneous transform => transform.mulVec state

/-- Ordered operator composition for an arbitrary piecewise demographic history. -/
noncomputable def propagateLowOrderLDInstructions {D : ℕ}
    (instructions : List (LowOrderLDInstruction D))
    (initial : AffineLowOrderLDCoordinate D → ℝ) :
    AffineLowOrderLDCoordinate D → ℝ :=
  instructions.foldl (fun state instruction ↦ instruction.apply state) initial

/-- Exact history composition is operator composition on the full joint state.  This is the
chain law: a suffix acts on the complete state returned by its prefix, not on the prefix's
single `DD` correlation. -/
theorem propagateLowOrderLDInstructions_append {D : ℕ}
    (front rest : List (LowOrderLDInstruction D))
    (initial : AffineLowOrderLDCoordinate D → ℝ) :
    propagateLowOrderLDInstructions (front ++ rest) initial =
      propagateLowOrderLDInstructions rest
        (propagateLowOrderLDInstructions front initial) := by
  simp [propagateLowOrderLDInstructions, List.foldl_append]

/-- A fully derived low-order history consists of its ancestral joint moments and its ordered
demographic operators.  This is the precise interface the arbitrary-deme generator must
construct from the visible history. -/
structure LowOrderLDHistory (D : ℕ) where
  initial : AffineLowOrderLDCoordinate D → ℝ
  initial_constant : initial none = 1
  instructions : List (LowOrderLDInstruction D)

/-- Present-day state after the complete ordered operator product. -/
noncomputable def LowOrderLDHistory.present {D : ℕ} (history : LowOrderLDHistory D) :
    AffineLowOrderLDCoordinate D → ℝ :=
  propagateLowOrderLDInstructions history.instructions history.initial

/-- Read the exact `DD`, `Dz`, and `pi2` family expected by portability consumers from one
composed history. -/
noncomputable def LowOrderLDHistory.toDemographicTwoLocusMoments {D : ℕ}
    (historyAt : MarkerSeparationBp → LowOrderLDHistory D) :
    DemographicTwoLocusMoments D where
  DD := fun rho first second ↦ (historyAt rho).present (some (.DD first second))
  Dz := fun rho first second third ↦ (historyAt rho).present (some (.Dz first second third))
  pi2 := fun rho first second third fourth ↦
    (historyAt rho).present (some (.pi2 first second third fourth))

/-- The bridge this module exists to supply, stated as a theorem so the two vocabularies are
tied where a contradiction could land: the `DemographicTwoLocusMoments` cross-deme `DD` entry
read at a `MarkerSeparationBp` is literally the composed history's present `DD` joint
moment, with no closure approximation between the two. -/
theorem LowOrderLDHistory.toDemographicTwoLocusMoments_DD {D : ℕ}
    (historyAt : MarkerSeparationBp → LowOrderLDHistory D)
    (rho : MarkerSeparationBp) (first second : Fin D) :
    DemographicTwoLocusMoments.DD (LowOrderLDHistory.toDemographicTwoLocusMoments historyAt)
        rho first second =
      (historyAt rho).present (some (.DD first second)) :=
  rfl

end Descent.Coalescent
