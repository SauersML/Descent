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
`propagateLowOrderLDInstructions_append` is proved below.  At positive mutation its ancestral
`DD` is proved strictly positive and its cross-deme Cauchy--Schwarz inequality is equality;
preservation of that moment realizability through the semigroup is still an explicit
downstream obligation.  An arithmetic consequence of a model is true of the model whatever
a population does.

WHAT THIS SECTION DOES NOT COVER, named rather than left silent.  The quantity this file
exists to supply downstream is `LowOrderLDHistory.toDemographicTwoLocusMoments`, whose `DD`
readout becomes `StructuredPresentDay`'s cross-deme LD correlation.  That readout IS an
empirical claim once a demography is filled in -- a simulation can contradict its composed
prediction.  `validation/empirical/momentsld/ldchain_reduction.py` now supplies an independent
exact-rational ancestral-configuration reference for stationary 2-, 3-, and 4-deme chains;
it validates the need for a full-state composition and refutes the two-deme and scalar-power
reductions.  The pre-filed 2-D comparison in `derivation/ld2d_iter.log` has now completed 4x4,
5x5, and 6x6 solves at relative residual below `1e-12`: its mechanical scoring rules out the
shared-one-dimensional-length Bessel proposal at `rho = 1` and fails it at `rho = 5, 20`.
This is evidence against another scalar reduction and for retaining the whole state; it is
not yet a coordinatewise specialization proof for this generator.  The recurrent-biallelic
damping added here also needs its own reference comparison.  Thus the operator form is
derived, while the composed readout remains scientifically ungated.
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

/-- Exact recurrent symmetric-biallelic mutation damping.

The rate coordinate is `theta = 2u`.  A centered allele contrast decays at rate `theta`,
so a within-deme linkage covariance `D` (two contrasts) decays at `2 theta`.  Counting the
contrasts in each product gives the four rows below: two `D` factors in `DD`; one `D` and two
single-locus contrasts in `Dz`; and four single-locus contrasts in `pi2`.  The `H` row is the
return-mutation correction to the affine heterozygosity influx.  This is the term absent from
the infinite-sites leading-order system. -/
noncomputable def lowOrderLDRecurrentMutationDamping {D : ℕ}
    (rates : ManyDemeLDRates D) (moment : LowOrderLDCoordinate D → ℝ) :
    LowOrderLDCoordinate D → ℝ
  | .H first second =>
      -(rates.mutation first + rates.mutation second) * moment (.H first second)
  | .DD first second =>
      -2 * (rates.mutation first + rates.mutation second) * moment (.DD first second)
  | .Dz first second third =>
      -(2 * rates.mutation first + rates.mutation second + rates.mutation third) *
        moment (.Dz first second third)
  | .pi2 first second third fourth =>
      -(rates.mutation first + rates.mutation second + rates.mutation third +
          rates.mutation fourth) * moment (.pi2 first second third fourth)

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
    lowOrderLDMutationCoupling rates moment coordinate +
    lowOrderLDRecurrentMutationDamping rates moment coordinate

/-- The homogeneous affine `H` row of the complete two-locus generator is exactly the shared
pair-divergence law, with its constant coordinate kept explicit.  Recombination and all
higher joint coordinates disappear algebraically. -/
theorem lowOrderLDAffine_H_eq_symmetricPairDivergence_affine {D : ℕ}
    (rates : ManyDemeLDRates D) (moment : LowOrderLDCoordinate D → ℝ)
    (constant : ℝ)
    (first second : Fin D) :
    lowOrderLDHomogeneousGenerator rates moment (.H first second) +
        lowOrderLDMutationForcing rates (.H first second) * constant =
      symmetricPairDivergenceAffineDerivative rates.coalescence rates.migration rates.mutation
        (fun source target ↦ moment (.H source target)) constant first second := by
  simp [lowOrderLDHomogeneousGenerator, lowOrderLDDrift, lowOrderLDMigration,
    lowOrderLDRecombination, lowOrderLDMutationCoupling,
    lowOrderLDRecurrentMutationDamping, lowOrderLDMutationForcing,
    symmetricPairDivergenceAffineDerivative] <;> ring

/-- The probability-law specialization of the affine `H`-row identity. -/
theorem lowOrderLDAffine_H_eq_symmetricPairDivergence {D : ℕ}
    (rates : ManyDemeLDRates D) (moment : LowOrderLDCoordinate D → ℝ)
    (first second : Fin D) :
    lowOrderLDHomogeneousGenerator rates moment (.H first second) +
        lowOrderLDMutationForcing rates (.H first second) =
      symmetricPairDivergenceDerivative rates.coalescence rates.migration rates.mutation
        (fun source target ↦ moment (.H source target)) first second := by
  simpa [symmetricPairDivergenceDerivative] using
    lowOrderLDAffine_H_eq_symmetricPairDivergence_affine rates moment 1 first second

/-- Concrete constant-augmented matrix of the arbitrary-deme moment ODE. -/
noncomputable def augmentedLowOrderLDGenerator {D : ℕ} (rates : ManyDemeLDRates D) :
    Matrix (AffineLowOrderLDCoordinate D) (AffineLowOrderLDCoordinate D) ℝ
  | some row, some column => lowOrderLDHomogeneousGenerator rates (lowOrderLDBasis column) row
  | some row, none => lowOrderLDMutationForcing rates row
  | none, _ => 0

/-- Linear readout retaining only the affine constant and all ordered `H` coordinates from
the complete low-order two-locus state. -/
def lowOrderLDHProjectionLinearMap {D : ℕ} :
    (AffineLowOrderLDCoordinate D → ℝ) →ₗ[ℝ]
      (AffinePairDivergenceCoordinate D → ℝ) where
  toFun state coordinate := match coordinate with
    | none => state none
    | some (first, second) => state (some (.H first second))
  map_add' := by
    intro left right
    funext coordinate
    cases coordinate <;> simp
  map_smul' := by
    intro scalar state
    funext coordinate
    cases coordinate <;> simp

/-- Rectangular matrix selecting the closed `H` subsystem from the joint state. -/
noncomputable def lowOrderLDHProjection (D : ℕ) :
    Matrix (AffinePairDivergenceCoordinate D) (AffineLowOrderLDCoordinate D) ℝ :=
  LinearMap.toMatrix' lowOrderLDHProjectionLinearMap

/-- Applying the `H` projection matrix is exact coordinate selection. -/
theorem lowOrderLDHProjection_mulVec {D : ℕ}
    (state : AffineLowOrderLDCoordinate D → ℝ) :
    (lowOrderLDHProjection D).mulVec state = lowOrderLDHProjectionLinearMap state := by
  exact LinearMap.toMatrix'_mulVec _ _

/-- Joint moment table represented by one column of the augmented low-order system. -/
def lowOrderLDAffineColumnMoment {D : ℕ}
    (column : AffineLowOrderLDCoordinate D) : LowOrderLDCoordinate D → ℝ :=
  match column with
  | none => fun _ ↦ 0
  | some coordinate => lowOrderLDBasis coordinate

/-- Constant coefficient represented by one augmented low-order column. -/
def lowOrderLDAffineColumnConstant {D : ℕ}
    (column : AffineLowOrderLDCoordinate D) : ℝ :=
  match column with
  | none => 1
  | some _ => 0

/-- A projection entry at `H(i,j)` is the `H(i,j)` value of the represented joint basis. -/
theorem lowOrderLDHProjection_apply {D : ℕ} (first second : Fin D)
    (column : AffineLowOrderLDCoordinate D) :
    lowOrderLDHProjection D (some (first, second)) column =
      lowOrderLDAffineColumnMoment column (.H first second) := by
  cases column <;>
    simp [lowOrderLDHProjection, lowOrderLDHProjectionLinearMap,
      lowOrderLDAffineColumnMoment, lowOrderLDBasis]

/-- The `H` projection passes the augmented constant coordinate. -/
theorem lowOrderLDHProjection_none {D : ℕ}
    (column : AffineLowOrderLDCoordinate D) :
    lowOrderLDHProjection D none column = lowOrderLDAffineColumnConstant column := by
  cases column <;>
    simp [lowOrderLDHProjection, lowOrderLDHProjectionLinearMap,
      lowOrderLDAffineColumnConstant]

/-- The full joint generator and its closed `H` subsystem commute exactly. -/
theorem lowOrderLDHProjection_generator_intertwines {D : ℕ}
    (rates : ManyDemeLDRates D) :
    lowOrderLDHProjection D * augmentedLowOrderLDGenerator rates =
      augmentedPairDivergenceGenerator rates.coalescence rates.migration rates.mutation *
        lowOrderLDHProjection D := by
  apply Matrix.ext
  intro row column
  change (lowOrderLDHProjection D).mulVec
      (fun source ↦ augmentedLowOrderLDGenerator rates source column) row =
    (augmentedPairDivergenceGenerator rates.coalescence rates.migration
      rates.mutation).mulVec (fun target ↦ lowOrderLDHProjection D target column) row
  rw [lowOrderLDHProjection_mulVec, augmentedPairDivergenceGenerator_mulVec]
  cases row with
  | none =>
      simp [lowOrderLDHProjectionLinearMap, pairDivergenceGeneratorLinearMap,
        augmentedLowOrderLDGenerator]
  | some pair =>
      rcases pair with ⟨first, second⟩
      change augmentedLowOrderLDGenerator rates (some (.H first second)) column =
        symmetricPairDivergenceAffineDerivative rates.coalescence rates.migration
          rates.mutation
          (fun source target ↦ lowOrderLDHProjection D (some (source, target)) column)
          (lowOrderLDHProjection D none column) first second
      rw [lowOrderLDHProjection_none]
      simp_rw [lowOrderLDHProjection_apply]
      cases column with
      | none =>
          have hzero : lowOrderLDHomogeneousGenerator rates (fun _ ↦ 0)
              (.H first second) = 0 := by
            simp [lowOrderLDHomogeneousGenerator, lowOrderLDDrift,
              lowOrderLDMigration, lowOrderLDRecombination,
              lowOrderLDMutationCoupling, lowOrderLDRecurrentMutationDamping]
          simpa [augmentedLowOrderLDGenerator, lowOrderLDAffineColumnMoment,
            lowOrderLDAffineColumnConstant, hzero] using
              lowOrderLDAffine_H_eq_symmetricPairDivergence_affine rates (fun _ ↦ 0)
                1 first second
      | some column =>
          simpa [augmentedLowOrderLDGenerator, lowOrderLDAffineColumnMoment,
            lowOrderLDAffineColumnConstant] using
            lowOrderLDAffine_H_eq_symmetricPairDivergence_affine rates
              (lowOrderLDBasis column) 0 first second

/-- The full joint epoch and the closed `H` epoch commute through their exact matrix
exponentials. -/
theorem lowOrderLDHProjection_propagator_intertwines {D : ℕ}
    (rates : ManyDemeLDRates D) (duration : ℝ) :
    lowOrderLDHProjection D * matrixExponential (augmentedLowOrderLDGenerator rates) duration =
      matrixExponential
          (augmentedPairDivergenceGenerator rates.coalescence rates.migration rates.mutation)
          duration * lowOrderLDHProjection D := by
  exact matrixExponential_intertwines _ _ _
    (lowOrderLDHProjection_generator_intertwines rates) duration

/-- Positive denominator of the recurrent-biallelic one-deme stationary `DD/Dz/pi2` solve.
It is written as an expanded positive polynomial so the physical rate domain excludes a
Cramer pole without appealing to a numerical determinant. -/
noncomputable def oneDemeLDStationaryDenominator (rates : ManyDemeLDRates 1) : ℝ :=
  let c := rates.coalescence 0
  let theta := rates.mutation 0
  let rho := rates.recombination 0
  18 * c ^ 3 + 13 * c ^ 2 * rho + 108 * c ^ 2 * theta + c * rho ^ 2 +
    38 * c * theta * rho + 160 * c * theta ^ 2 + 2 * theta * rho ^ 2 +
    24 * theta ^ 2 * rho + 64 * theta ^ 3

/-- The one-deme stationary denominator cannot hit a Cramer pole on the physical rate
domain. -/
theorem oneDemeLDStationaryDenominator_pos (rates : ManyDemeLDRates 1) :
    0 < oneDemeLDStationaryDenominator rates := by
  unfold oneDemeLDStationaryDenominator
  have hc := rates.coalescence_pos 0
  have ht := rates.mutation_nonneg 0
  have hr := rates.recombination_nonneg 0
  positivity

/-- Closed stationary solution of the four recurrent-biallelic one-deme equations.  Writing
`c = 1/(2N)`, `theta = 2u`, and `rho = 2r`, the solution is

`H = theta/(c+2theta)`,
`DD = c theta²(10c+rho+8theta)/(4(c+2theta)Q)`,
`Dz = 2c²theta²/((c+2theta)Q)`, and
`pi2 = c³theta²/((c+2theta)²Q) + theta²/(4(c+2theta)²)`,

where `Q = oneDemeLDStationaryDenominator`.  As `theta → 0`, the leading `theta²`
coefficients reduce to the former infinite-sites boundary, but this expression also retains
the return-mutation terms required by the biallelic ascertainment law.

Thus the ancestral boundary has no fitted moment table and no unchecked determinant. -/
noncomputable def oneDemeStationaryLowOrderLDState (rates : ManyDemeLDRates 1) :
    AffineLowOrderLDCoordinate 1 → ℝ
  | none => 1
  | some (.H _ _) =>
      rates.mutation 0 / (rates.coalescence 0 + 2 * rates.mutation 0)
  | some (.DD _ _) =>
      rates.coalescence 0 * rates.mutation 0 ^ 2 *
        (10 * rates.coalescence 0 + rates.recombination 0 + 8 * rates.mutation 0) /
      (4 * (rates.coalescence 0 + 2 * rates.mutation 0) *
        oneDemeLDStationaryDenominator rates)
  | some (.Dz _ _ _) =>
      2 * rates.coalescence 0 ^ 2 * rates.mutation 0 ^ 2 /
        ((rates.coalescence 0 + 2 * rates.mutation 0) *
          oneDemeLDStationaryDenominator rates)
  | some (.pi2 _ _ _ _) =>
      rates.coalescence 0 ^ 3 * rates.mutation 0 ^ 2 /
          ((rates.coalescence 0 + 2 * rates.mutation 0) ^ 2 *
            oneDemeLDStationaryDenominator rates) +
        rates.mutation 0 ^ 2 /
          (4 * (rates.coalescence 0 + 2 * rates.mutation 0) ^ 2)

/-- The closed ancestral values solve all four stationary generator equations. -/
theorem oneDemeStationaryLowOrderLDState_equations (rates : ManyDemeLDRates 1) :
    let state := oneDemeStationaryLowOrderLDState rates
    let c := rates.coalescence 0
    let theta := rates.mutation 0
    let rho := rates.recombination 0
    theta - (c + 2 * theta) * state (some (.H 0 0)) = 0 ∧
      -(3 * c + rho + 4 * theta) * state (some (.DD 0 0)) +
          c * state (some (.Dz 0 0 0)) + c * state (some (.pi2 0 0 0 0)) = 0 ∧
      4 * c * state (some (.DD 0 0)) -
          (5 * c + rho / 2 + 4 * theta) * state (some (.Dz 0 0 0)) = 0 ∧
      c * state (some (.Dz 0 0 0)) - (2 * c + 4 * theta) *
          state (some (.pi2 0 0 0 0)) +
          theta / 2 * state (some (.H 0 0)) = 0 := by
  have hscale : rates.coalescence 0 + 2 * rates.mutation 0 ≠ 0 := by
    have hc := rates.coalescence_pos 0
    have ht := rates.mutation_nonneg 0
    positivity
  have hden : oneDemeLDStationaryDenominator rates ≠ 0 :=
    ne_of_gt (oneDemeLDStationaryDenominator_pos rates)
  have hscale_comm : rates.mutation 0 * 2 + rates.coalescence 0 ≠ 0 := by
    convert hscale using 1 <;> ring
  have hscale_nf : rates.coalescence 0 + rates.mutation 0 * 2 ≠ 0 := by
    convert hscale using 1 <;> ring
  have hscale_sq :
      rates.coalescence 0 * rates.mutation 0 * 4 + rates.coalescence 0 ^ 2 +
          rates.mutation 0 ^ 2 * 4 ≠ 0 := by
    convert pow_ne_zero 2 hscale using 1 <;> ring
  have hden_comm :
      rates.coalescence 0 * rates.mutation 0 * rates.recombination 0 * 38 +
              rates.coalescence 0 * rates.mutation 0 ^ 2 * 160 +
            rates.coalescence 0 * rates.recombination 0 ^ 2 +
          rates.coalescence 0 ^ 2 * rates.mutation 0 * 108 +
        rates.coalescence 0 ^ 2 * rates.recombination 0 * 13 +
      rates.coalescence 0 ^ 3 * 18 + rates.mutation 0 * rates.recombination 0 ^ 2 * 2 +
        rates.mutation 0 ^ 2 * rates.recombination 0 * 24 +
          rates.mutation 0 ^ 3 * 64 ≠ 0 := by
    convert hden using 1 <;> unfold oneDemeLDStationaryDenominator <;> ring
  dsimp [oneDemeStationaryLowOrderLDState, oneDemeLDStationaryDenominator]
  constructor
  · field_simp [hscale, hscale_comm, hscale_nf] <;> ring
  constructor
  · field_simp [hscale, hscale_comm, hscale_nf, hscale_sq, hden, hden_comm]
    have hQcancel := mul_inv_cancel₀ hden_comm
    linear_combination
      -(rates.coalescence 0 * rates.mutation 0 ^ 2) * hQcancel
  constructor
  · field_simp [hscale, hscale_comm, hscale_nf, hscale_sq, hden, hden_comm] <;>
      field_simp [hden, hden_comm] <;> ring
  · field_simp [hscale, hscale_comm, hscale_nf, hscale_sq, hden, hden_comm] <;>
      field_simp [hden, hden_comm] <;> ring

/-- Positive recurrent mutation makes the ancestral within-deme `DD = E[D²]` strictly
positive.  This is the nondegenerate base case for the downstream normalized correlation. -/
theorem oneDemeStationaryLowOrderLDState_DD_pos (rates : ManyDemeLDRates 1)
    (mutation_pos : 0 < rates.mutation 0) :
    0 < oneDemeStationaryLowOrderLDState rates (some (.DD 0 0)) := by
  unfold oneDemeStationaryLowOrderLDState
  have hc := rates.coalescence_pos 0
  have hr := rates.recombination_nonneg 0
  have hden := oneDemeLDStationaryDenominator_pos rates
  positivity

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

/-- Every ancestral `DD(i,j)` is the same positive one-deme second moment when recurrent
mutation is positive. -/
theorem commonAncestralLowOrderLDState_DD_pos {D : ℕ}
    (ancestralRates : ManyDemeLDRates 1) (mutation_pos : 0 < ancestralRates.mutation 0)
    (first second : Fin D) :
    0 < commonAncestralLowOrderLDState ancestralRates (some (.DD first second)) := by
  exact oneDemeStationaryLowOrderLDState_DD_pos ancestralRates mutation_pos

/-- The ancestral `DD` kernel saturates Cauchy--Schwarz because every descendant label still
denotes the same unsplit population. -/
theorem commonAncestralLowOrderLDState_DD_cauchySchwarz {D : ℕ}
    (ancestralRates : ManyDemeLDRates 1) (first second : Fin D) :
    commonAncestralLowOrderLDState ancestralRates (some (.DD first second)) ^ 2 ≤
      commonAncestralLowOrderLDState ancestralRates (some (.DD first first)) *
        commonAncestralLowOrderLDState ancestralRates (some (.DD second second)) := by
  simp [commonAncestralLowOrderLDState, LowOrderLDCoordinate.collapseToOneDeme, pow_two]

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

/-- Multiplying by the split matrix is exactly coordinate relabeling.  This eliminates the
instantaneous-event half of any projection proof: there is no averaging or closure hidden in
a split, only replacement of every child label by its parent. -/
theorem lowOrderLDSplitTransform_mulVec {D : ℕ} (parent child : Fin D)
    (state : AffineLowOrderLDCoordinate D → ℝ) :
    (lowOrderLDSplitTransform parent child).mulVec state =
      fun coordinate ↦ match coordinate with
        | none => state none
        | some row => state (some (row.mergeSplit parent child)) := by
  funext coordinate
  cases coordinate with
  | none =>
      simp [Matrix.mulVec, dotProduct, lowOrderLDSplitTransform]
  | some row =>
      simp [Matrix.mulVec, dotProduct, lowOrderLDSplitTransform]

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

/-- Read the exact `H`, `DD`, `Dz`, and `pi2` family expected by portability consumers from
one composed history. -/
noncomputable def LowOrderLDHistory.toDemographicTwoLocusMoments {D : ℕ}
    (historyAt : MarkerSeparationBp → LowOrderLDHistory D) :
    DemographicTwoLocusMoments D where
  H := fun rho first second ↦ (historyAt rho).present (some (.H first second))
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

/-- The same interface exposes the marginal heterozygosity coordinate carried inside the
joint operator.  This is the coordinate that an eventual intertwining theorem identifies
with the independently propagated one-locus divergence moment. -/
theorem LowOrderLDHistory.toDemographicTwoLocusMoments_H {D : ℕ}
    (historyAt : MarkerSeparationBp → LowOrderLDHistory D)
    (rho : MarkerSeparationBp) (first second : Fin D) :
    DemographicTwoLocusMoments.H (LowOrderLDHistory.toDemographicTwoLocusMoments historyAt)
        rho first second =
      (historyAt rho).present (some (.H first second)) :=
  rfl

end Descent.Coalescent
