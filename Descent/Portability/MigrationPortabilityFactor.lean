/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.StationaryHaplotypeRealization
import Descent.Portability.TwoLocusPortabilityDecay
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

assert_below Descent.Decision Descent.Program

/-!
# The migration factor of two-locus portability

`TwoLocusPortabilityDecay` proves that after a split with no migration and no mutation the
target-to-source ratio of the expected squared correlation of a tag-locus score is `e^{-ρ̄T}`,
with `ρ̄ = (ρ_S + ρ_T)/2`.  `PortabilityDrift.PresentDayMoments` records the gap this module
works on.  Its LD kernel omits the restoration of shared LD by migration, and "the repair is a
DERIVED migration factor, which nothing here supplies".  The one migration law of cross-deme LD
in the corpus, `Coalescent.publishedTwoDemeDCorrelation`, is stationary and is not a law for
transient histories.

This module keeps the split history of `TwoLocusPortabilityDecay` and turns on symmetric
migration `m` between the two demes after the split (`withSymmetricMigration`).  Drift and
recombination are unchanged, and mutation is zero.

## Main results

- `withSymmetricMigration_DD_row`, `withSymmetricMigration_pi2_row`: the generator rows of
  `DD(S, T)` and `pi2(S, S, T, T)` are the diagonal rows of the no-migration history plus `m`
  times a migration stencil (`linkageMigrationStencil`, `heterozygosityMigrationStencil`).
  The stencils are the `DD/Dz` and `pi2` terms of `lowOrderLDMigration` at the pair.
- `migrationHistory_DD`, `migrationHistory_pi2`: variation of constants.
  `E_m[D_S D_T](T) = e^{-λ_D T} (E[D²](0) + m ∫_0^T e^{λ_D s} μ_D(s) ds)`, with
  `λ_D = c_S + c_T + ρ̄` (`crossLinkageDecayRate`), and
  `E_m[π_S π_T](T) = e^{-λ_π T} (E[π²](0) + m ∫_0^T e^{λ_π s} μ_π(s) ds)`, with
  `λ_π = c_S + c_T` (`crossHeterozygosityDecayRate`).
- `splitPortabilityRatio_withSymmetricMigration`: the portability ratio is
  `(e^{-ρ̄T} + m A_D) / (1 + m A_π)`.  Here `A_D = e^{-ρ̄T} ∫_0^T e^{λ_D s} μ_D(s) ds / E[D²](0)`
  (`linkageMigrationShare`) and `A_π = ∫_0^T e^{λ_π s} μ_π(s) ds / E[π²](0)`
  (`heterozygosityMigrationShare`).
- `splitPortabilityRatio_withSymmetricMigration_zero`: at `m = 0` the ratio is `e^{-ρ̄T}`, the
  corpus law `splitPortabilityRatio_eq`.
- `linkageMigrationStencil_migrationHistory_zero` and
  `heterozygosityMigrationStencil_migrationHistory_zero`: both stencils vanish at the split, so
  migration adds nothing until the two demes have diverged.

## The functional, and what the identity is

The functional is the one of `TwoLocusPortabilityDecay`: a ratio of expectations,
`E[D_S D_T] / E[π_S π_T]`, over its split-time value.  It is not the `Corr(D)` of
`validation/empirical/momentsld/ld_surface.py`, which divides `E[D_S D_T]` by
`√(E[D_S²] E[D_T²])`.

The identity is exact and implicit.  The stencils are read on the with-migration history
itself, a coupled system of the two-deme `DD`, `Dz` and `pi2` coordinates.  So the shares
`A_D` and `A_π` are integrals along that history, not closed forms.  Evaluating them to first
order in `m` on the no-migration history is not done here.

## Scope

Two demes of the corpus rates exchange migrants at rate `m` each way, and no other ordered pair
exchanges any.  Mutation is zero.  Drift and recombination are those of `rates`.

## Empirical status

None.  The bodies are algebra and calculus on corpus moment coordinates.  `PresentDayMoments`
records that its kernel understates shared LD by a factor between about 1.02 and 1.25.  That
figure comes from `simcov/battery_bulk55.py`, which is not in this checkout, and nothing here is
compared with it.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.MigrationPortabilityFactor

open Descent.Coalescent Descent.Portability.TwoLocusPortabilityDecay

noncomputable section

variable {D : ℕ}

/-! ## Symmetric migration between two demes -/

/-- **Symmetric migration between two demes**: rate `migration` from `parent` to `child` and from
`child` to `parent`, and zero for every other ordered pair.

Empirical status: NOT AN EMPIRICAL CLAIM.  A migration matrix supported on one pair. -/
def symmetricPairMigration (parent child : Fin D) (migration : ℝ) (source target : Fin D) : ℝ :=
  if source = parent ∧ target = child ∨ source = child ∧ target = parent then migration else 0

/-- **The rates with symmetric migration between `parent` and `child`**: the drift, mutation and
recombination of `rates`, and `symmetricPairMigration` for the migration.

Empirical status: NOT AN EMPIRICAL CLAIM.  A record update of the corpus rates. -/
def withSymmetricMigration (rates : ManyDemeLDRates D) {parent child : Fin D}
    (hne : parent ≠ child) (migration : ℝ) (hmigration : 0 ≤ migration) : ManyDemeLDRates D where
  coalescence := rates.coalescence
  migration := symmetricPairMigration parent child migration
  mutation := rates.mutation
  recombination := rates.recombination
  coalescence_pos := rates.coalescence_pos
  migration_nonneg source target := by
    unfold symmetricPairMigration
    split_ifs
    exacts [hmigration, le_rfl]
  migration_self deme := by
    unfold symmetricPairMigration
    rw [if_neg]
    rintro (⟨hparent, hchild⟩ | ⟨hchild, hparent⟩) <;> exact hne (hparent.symm.trans hchild)
  mutation_nonneg := rates.mutation_nonneg
  recombination_nonneg := rates.recombination_nonneg

/-- **The no-migration decay rate of the cross-population linkage covariance**,
`c_S + c_T + (ρ_S + ρ_T)/2`.

Empirical status: NOT AN EMPIRICAL CLAIM.  A sum of rates. -/
def crossLinkageDecayRate (rates : ManyDemeLDRates D) (parent child : Fin D) : ℝ :=
  rates.coalescence parent + rates.coalescence child
    + (rates.recombination parent + rates.recombination child) / 2

/-- **The no-migration decay rate of the cross-population heterozygosity product**, `c_S + c_T`.

Empirical status: NOT AN EMPIRICAL CLAIM.  A sum of rates. -/
def crossHeterozygosityDecayRate (rates : ManyDemeLDRates D) (parent child : Fin D) : ℝ :=
  rates.coalescence parent + rates.coalescence child

/-! ## The migration stencils -/

/-- **The migration stencil of the cross-population linkage covariance**:
`DD(T, T) + DD(S, S) - 2 DD(S, T)` plus a quarter of the two `Dz` contrasts
`Dz(T, S, S) - Dz(T, S, T) - Dz(T, T, S) + Dz(T, T, T)` and
`Dz(S, T, T) - Dz(S, T, S) - Dz(S, S, T) + Dz(S, S, S)`.  These are the terms that
`lowOrderLDMigration` adds to the `DD(S, T)` row at unit migration each way.

Empirical status: NOT AN EMPIRICAL CLAIM.  A linear combination of moment coordinates. -/
def linkageMigrationStencil (parent child : Fin D) (state : AffineLowOrderLDCoordinate D → ℝ) :
    ℝ :=
  state (some (.DD child child)) + state (some (.DD parent parent))
    - 2 * state (some (.DD parent child))
    + (state (some (.Dz child parent parent)) - state (some (.Dz child parent child))
      - state (some (.Dz child child parent)) + state (some (.Dz child child child))
      + state (some (.Dz parent child child)) - state (some (.Dz parent child parent))
      - state (some (.Dz parent parent child)) + state (some (.Dz parent parent parent))) / 4

/-- **The migration stencil of the cross-population heterozygosity product**: the four
one-index migrations of `pi2(S, S, T, T)`,
`pi2(T, S, T, T) + pi2(S, T, T, T) + pi2(S, S, S, T) + pi2(S, S, T, S) - 4 pi2(S, S, T, T)`.

Empirical status: NOT AN EMPIRICAL CLAIM.  A linear combination of moment coordinates. -/
def heterozygosityMigrationStencil (parent child : Fin D)
    (state : AffineLowOrderLDCoordinate D → ℝ) : ℝ :=
  state (some (.pi2 child parent child child)) + state (some (.pi2 parent child child child))
    + state (some (.pi2 parent parent parent child))
    + state (some (.pi2 parent parent child parent))
    - 4 * state (some (.pi2 parent parent child child))

/-- The linkage migration stencil is continuous along a continuous path. -/
theorem continuous_linkageMigrationStencil {path : ℝ → AffineLowOrderLDCoordinate D → ℝ}
    (hpath : Continuous path) (parent child : Fin D) :
    Continuous fun time ↦ linkageMigrationStencil parent child (path time) := by
  have h : ∀ coordinate, Continuous fun time ↦ path time coordinate :=
    fun coordinate ↦ (continuous_apply coordinate).comp hpath
  simp only [linkageMigrationStencil]
  first
  | fun_prop
  | exact (((h _).add (h _)).sub (continuous_const.mul (h _))).add
      (((((((((h _).sub (h _)).sub (h _)).add (h _)).add (h _)).sub (h _)).sub (h _)).add
        (h _)).div_const 4)

/-- The heterozygosity migration stencil is continuous along a continuous path. -/
theorem continuous_heterozygosityMigrationStencil
    {path : ℝ → AffineLowOrderLDCoordinate D → ℝ} (hpath : Continuous path)
    (parent child : Fin D) :
    Continuous fun time ↦ heterozygosityMigrationStencil parent child (path time) := by
  have h : ∀ coordinate, Continuous fun time ↦ path time coordinate :=
    fun coordinate ↦ (continuous_apply coordinate).comp hpath
  simp only [heterozygosityMigrationStencil]
  first
  | fun_prop
  | exact ((((h _).add (h _)).add (h _)).add (h _)).sub (continuous_const.mul (h _))

/-! ## The split history with migration -/

/-- **The moment vector of a split history with symmetric migration**, at every real time.  The
ancestral vector is split from `parent` into `child`, and the joint vector then evolves under
`withSymmetricMigration`.  At a nonnegative time it is `splitHistoryState`.

Empirical status: NOT AN EMPIRICAL CLAIM.  A matrix exponential applied to the split vector. -/
def migrationHistory (rates : ManyDemeLDRates D) {parent child : Fin D} (hne : parent ≠ child)
    (migration : ℝ) (hmigration : 0 ≤ migration) (ancestral : AffineLowOrderLDCoordinate D → ℝ)
    (time : ℝ) : AffineLowOrderLDCoordinate D → ℝ :=
  (matrixExponential
      (augmentedLowOrderLDGenerator (withSymmetricMigration rates hne migration hmigration))
      time).mulVec
    ((lowOrderLDSplitTransform parent child).mulVec ancestral)

/-- At a nonnegative time the history is the corpus split history. -/
theorem splitHistoryState_withSymmetricMigration (rates : ManyDemeLDRates D)
    {parent child : Fin D} (hne : parent ≠ child) {migration : ℝ} (hmigration : 0 ≤ migration)
    {duration : ℝ} (hduration : 0 ≤ duration) (ancestral : AffineLowOrderLDCoordinate D → ℝ) :
    splitHistoryState (withSymmetricMigration rates hne migration hmigration) parent child
        hduration ancestral
      = migrationHistory rates hne migration hmigration ancestral duration :=
  rfl

/-- At time zero the history is the split vector. -/
theorem migrationHistory_zero (rates : ManyDemeLDRates D) {parent child : Fin D}
    (hne : parent ≠ child) {migration : ℝ} (hmigration : 0 ≤ migration)
    (ancestral : AffineLowOrderLDCoordinate D → ℝ) :
    migrationHistory rates hne migration hmigration ancestral 0
      = (lowOrderLDSplitTransform parent child).mulVec ancestral := by
  rw [migrationHistory, matrixExponential_zero, Matrix.one_mulVec]

/-- The history is differentiable at every time, with derivative the generator applied to it. -/
theorem hasDerivAt_migrationHistory (rates : ManyDemeLDRates D) {parent child : Fin D}
    (hne : parent ≠ child) {migration : ℝ} (hmigration : 0 ≤ migration)
    (ancestral : AffineLowOrderLDCoordinate D → ℝ) (time : ℝ) :
    HasDerivAt (migrationHistory rates hne migration hmigration ancestral)
      ((augmentedLowOrderLDGenerator
          (withSymmetricMigration rates hne migration hmigration)).mulVec
        (migrationHistory rates hne migration hmigration ancestral time)) time :=
  StationaryHaplotypeRealization.hasDerivAt_matrixExponential_mulVec
    (augmentedLowOrderLDGenerator (withSymmetricMigration rates hne migration hmigration))
    ((lowOrderLDSplitTransform parent child).mulVec ancestral) time

/-- The history is continuous in time. -/
theorem continuous_migrationHistory (rates : ManyDemeLDRates D) {parent child : Fin D}
    (hne : parent ≠ child) {migration : ℝ} (hmigration : 0 ≤ migration)
    (ancestral : AffineLowOrderLDCoordinate D → ℝ) :
    Continuous (migrationHistory rates hne migration hmigration ancestral) :=
  continuous_iff_continuousAt.2 fun time ↦
    (hasDerivAt_migrationHistory rates hne hmigration ancestral time).continuousAt

/-! ## The generator rows with migration -/

/-- A point mass with the point on the left reads a vector at its point. -/
theorem sum_mul_pointMass_left {ι : Type*} [Fintype ι] [DecidableEq ι] (coeff : ℝ) (point : ι)
    (vector : ι → ℝ) :
    ∑ row, coeff * (if point = row then 1 else 0) * vector row = coeff * vector point := by
  simp [mul_ite, ite_mul, Finset.sum_ite_eq]

/-- **The unit point mass of a coordinate**, kept as a name so that the generator rows below
compare point masses as atoms.

Empirical status: NOT AN EMPIRICAL CLAIM.  An indicator. -/
def coordinateIndicator (point column : LowOrderLDCoordinate D) : ℝ :=
  if point = column then 1 else 0

/-- The corpus basis vector of a column reads the point mass of that column. -/
theorem lowOrderLDBasis_eq_coordinateIndicator (column point : LowOrderLDCoordinate D) :
    lowOrderLDBasis column point = coordinateIndicator point column :=
  rfl

/-- A point mass of the affine coordinates at a present coordinate is its coordinate point
mass. -/
theorem ite_some_eq_coordinateIndicator (point column : LowOrderLDCoordinate D) :
    (if (some point : AffineLowOrderLDCoordinate D) = some column then (1 : ℝ) else 0)
      = coordinateIndicator point column := by
  simp [coordinateIndicator]

set_option maxHeartbeats 800000 in
/-- **The cross-population `DD` row with symmetric migration** is the diagonal row of the
no-migration history, at rate `c_S + c_T + (ρ_S + ρ_T)/2`, plus `m` times the point masses of the
linkage migration stencil.

Assumes: no mutation and `parent ≠ child`. -/
theorem withSymmetricMigration_DD_row (rates : ManyDemeLDRates D)
    (hmutation : ∀ deme, rates.mutation deme = 0) {parent child : Fin D} (hne : parent ≠ child)
    {migration : ℝ} (hmigration : 0 ≤ migration) (column : AffineLowOrderLDCoordinate D) :
    augmentedLowOrderLDGenerator (withSymmetricMigration rates hne migration hmigration)
        (some (.DD parent child)) column
      = -crossLinkageDecayRate rates parent child
          * (if some (.DD parent child) = column then 1 else 0)
        + migration * (if some (.DD child child) = column then 1 else 0)
        + migration * (if some (.DD parent parent) = column then 1 else 0)
        - 2 * migration * (if some (.DD parent child) = column then 1 else 0)
        + migration / 4 * (if some (.Dz child parent parent) = column then 1 else 0)
        - migration / 4 * (if some (.Dz child parent child) = column then 1 else 0)
        - migration / 4 * (if some (.Dz child child parent) = column then 1 else 0)
        + migration / 4 * (if some (.Dz child child child) = column then 1 else 0)
        + migration / 4 * (if some (.Dz parent child child) = column then 1 else 0)
        - migration / 4 * (if some (.Dz parent child parent) = column then 1 else 0)
        - migration / 4 * (if some (.Dz parent parent child) = column then 1 else 0)
        + migration / 4 * (if some (.Dz parent parent parent) = column then 1 else 0) := by
  have hne' : child ≠ parent := Ne.symm hne
  cases column with
  | none => simp [augmentedLowOrderLDGenerator, lowOrderLDMutationForcing]
  | some column =>
    simp only [augmentedLowOrderLDGenerator, lowOrderLDHomogeneousGenerator, lowOrderLDDrift,
      lowOrderLDMigration, lowOrderLDRecombination, lowOrderLDMutationCoupling,
      lowOrderLDRecurrentMutationDamping, lowOrderLDBasis_eq_coordinateIndicator,
      ite_some_eq_coordinateIndicator, withSymmetricMigration, symmetricPairMigration,
      crossLinkageDecayRate, hmutation]
    simp [hne, hne', ite_mul, Finset.sum_ite_eq'] <;> ring

set_option maxHeartbeats 800000 in
/-- **The cross-population heterozygosity row with symmetric migration** is the diagonal row of
the no-migration history, at rate `c_S + c_T`, plus `m` times the point masses of the
heterozygosity migration stencil.

Assumes: no mutation and `parent ≠ child`. -/
theorem withSymmetricMigration_pi2_row (rates : ManyDemeLDRates D)
    (hmutation : ∀ deme, rates.mutation deme = 0) {parent child : Fin D} (hne : parent ≠ child)
    {migration : ℝ} (hmigration : 0 ≤ migration) (column : AffineLowOrderLDCoordinate D) :
    augmentedLowOrderLDGenerator (withSymmetricMigration rates hne migration hmigration)
        (some (.pi2 parent parent child child)) column
      = -crossHeterozygosityDecayRate rates parent child
          * (if some (.pi2 parent parent child child) = column then 1 else 0)
        + migration * (if some (.pi2 child parent child child) = column then 1 else 0)
        + migration * (if some (.pi2 parent child child child) = column then 1 else 0)
        + migration * (if some (.pi2 parent parent parent child) = column then 1 else 0)
        + migration * (if some (.pi2 parent parent child parent) = column then 1 else 0)
        - 4 * migration * (if some (.pi2 parent parent child child) = column then 1 else 0) := by
  have hne' : child ≠ parent := Ne.symm hne
  cases column with
  | none => simp [augmentedLowOrderLDGenerator, lowOrderLDMutationForcing]
  | some column =>
    simp only [augmentedLowOrderLDGenerator, lowOrderLDHomogeneousGenerator, lowOrderLDDrift,
      lowOrderLDMigration, lowOrderLDRecombination, lowOrderLDMutationCoupling,
      lowOrderLDRecurrentMutationDamping, lowOrderLDBasis_eq_coordinateIndicator,
      ite_some_eq_coordinateIndicator, withSymmetricMigration, symmetricPairMigration,
      crossHeterozygosityDecayRate, hmutation]
    simp [hne, hne', ite_mul, Finset.sum_ite_eq'] <;> ring

/-- **The linkage covariance moves at `-λ_D` times itself plus `m` times its migration
stencil.**

Assumes: no mutation and `parent ≠ child`. -/
theorem withSymmetricMigration_mulVec_DD (rates : ManyDemeLDRates D)
    (hmutation : ∀ deme, rates.mutation deme = 0) {parent child : Fin D} (hne : parent ≠ child)
    {migration : ℝ} (hmigration : 0 ≤ migration) (state : AffineLowOrderLDCoordinate D → ℝ) :
    (augmentedLowOrderLDGenerator (withSymmetricMigration rates hne migration hmigration)).mulVec
        state (some (.DD parent child))
      = -crossLinkageDecayRate rates parent child * state (some (.DD parent child))
        + migration * linkageMigrationStencil parent child state := by
  simp only [Matrix.mulVec, dotProduct,
    withSymmetricMigration_DD_row rates hmutation hne hmigration, add_mul, sub_mul,
    Finset.sum_add_distrib, Finset.sum_sub_distrib, sum_mul_pointMass_left]
  rw [linkageMigrationStencil]
  ring

/-- **The heterozygosity product moves at `-λ_π` times itself plus `m` times its migration
stencil.**

Assumes: no mutation and `parent ≠ child`. -/
theorem withSymmetricMigration_mulVec_pi2 (rates : ManyDemeLDRates D)
    (hmutation : ∀ deme, rates.mutation deme = 0) {parent child : Fin D} (hne : parent ≠ child)
    {migration : ℝ} (hmigration : 0 ≤ migration) (state : AffineLowOrderLDCoordinate D → ℝ) :
    (augmentedLowOrderLDGenerator (withSymmetricMigration rates hne migration hmigration)).mulVec
        state (some (.pi2 parent parent child child))
      = -crossHeterozygosityDecayRate rates parent child
          * state (some (.pi2 parent parent child child))
        + migration * heterozygosityMigrationStencil parent child state := by
  simp only [Matrix.mulVec, dotProduct,
    withSymmetricMigration_pi2_row rates hmutation hne hmigration, add_mul, sub_mul,
    Finset.sum_add_distrib, Finset.sum_sub_distrib, sum_mul_pointMass_left]
  rw [heterozygosityMigrationStencil]
  ring

/-! ## Variation of constants -/

/-- **Variation of constants for one coordinate.**  If `y' = -λ y + m g` at every time and `g` is
continuous, then `y(T) = e^{-λT} (y(0) + m ∫_0^T e^{λ s} g(s) ds)`.

Assumes: the derivative law at every time and a continuous source. -/
theorem eq_exp_mul_add_integral {value source : ℝ → ℝ} {rate migration : ℝ}
    (hvalue : ∀ time, HasDerivAt value (-rate * value time + migration * source time) time)
    (hsource : Continuous source) (duration : ℝ) :
    value duration = Real.exp (-rate * duration)
      * (value 0
        + migration * ∫ time in (0 : ℝ)..duration, Real.exp (rate * time) * source time) := by
  have hderiv : ∀ time ∈ Set.uIcc (0 : ℝ) duration,
      HasDerivAt (fun time ↦ Real.exp (rate * time) * value time)
        (migration * (Real.exp (rate * time) * source time)) time := fun time _ ↦
    (((hasDerivAt_id' (x := time)).const_mul rate).exp.mul (hvalue time)).congr_deriv (by ring)
  have hcontinuous : Continuous fun time ↦ migration * (Real.exp (rate * time) * source time) :=
    continuous_const.mul
      ((by fun_prop : Continuous fun time : ℝ ↦ Real.exp (rate * time)).mul hsource)
  have hintegral := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    (hcontinuous.intervalIntegrable 0 duration)
  rw [intervalIntegral.integral_const_mul, mul_zero, Real.exp_zero, one_mul] at hintegral
  have hcancel : Real.exp (-rate * duration) * Real.exp (rate * duration) = 1 := by
    rw [← Real.exp_add, show -rate * duration + rate * duration = 0 by ring, Real.exp_zero]
  calc value duration
      = Real.exp (-rate * duration) * (Real.exp (rate * duration) * value duration) := by
        rw [← mul_assoc, hcancel, one_mul]
    _ = Real.exp (-rate * duration)
      * (value 0
        + migration * ∫ time in (0 : ℝ)..duration, Real.exp (rate * time) * source time) := by
        rw [hintegral]
        ring

/-! ## The exact migration law -/

/-- **The exact migration law of the cross-population linkage covariance.**
`E_m[D_S D_T](T) = e^{-λ_D T} (E[D²](0) + m ∫_0^T e^{λ_D s} μ_D(s) ds)`, with `μ_D` the linkage
migration stencil read on the with-migration history.

Assumes: no mutation and `parent ≠ child`. -/
theorem migrationHistory_DD (rates : ManyDemeLDRates D)
    (hmutation : ∀ deme, rates.mutation deme = 0) {parent child : Fin D} (hne : parent ≠ child)
    {migration : ℝ} (hmigration : 0 ≤ migration) (ancestral : AffineLowOrderLDCoordinate D → ℝ)
    (duration : ℝ) :
    migrationHistory rates hne migration hmigration ancestral duration (some (.DD parent child))
      = Real.exp (-crossLinkageDecayRate rates parent child * duration)
        * (ancestral (some (.DD parent parent))
          + migration * ∫ time in (0 : ℝ)..duration,
            Real.exp (crossLinkageDecayRate rates parent child * time)
              * linkageMigrationStencil parent child
                (migrationHistory rates hne migration hmigration ancestral time)) := by
  have h := eq_exp_mul_add_integral (rate := crossLinkageDecayRate rates parent child)
    (migration := migration)
    (value := fun time ↦
      migrationHistory rates hne migration hmigration ancestral time (some (.DD parent child)))
    (source := fun time ↦ linkageMigrationStencil parent child
      (migrationHistory rates hne migration hmigration ancestral time))
    (fun time ↦ by
      have hcoordinate := hasDerivAt_pi.mp
        (hasDerivAt_migrationHistory rates hne hmigration ancestral time)
        (some (.DD parent child))
      rwa [withSymmetricMigration_mulVec_DD rates hmutation hne hmigration] at hcoordinate)
    (continuous_linkageMigrationStencil
      (continuous_migrationHistory rates hne hmigration ancestral) parent child)
    duration
  refine h.trans ?_
  simp only [migrationHistory_zero, splitTransform_DD hne]

/-- **The exact migration law of the cross-population heterozygosity product.**
`E_m[π_S π_T](T) = e^{-λ_π T} (E[π²](0) + m ∫_0^T e^{λ_π s} μ_π(s) ds)`, with `μ_π` the
heterozygosity migration stencil read on the with-migration history.

Assumes: no mutation and `parent ≠ child`. -/
theorem migrationHistory_pi2 (rates : ManyDemeLDRates D)
    (hmutation : ∀ deme, rates.mutation deme = 0) {parent child : Fin D} (hne : parent ≠ child)
    {migration : ℝ} (hmigration : 0 ≤ migration) (ancestral : AffineLowOrderLDCoordinate D → ℝ)
    (duration : ℝ) :
    migrationHistory rates hne migration hmigration ancestral duration
        (some (.pi2 parent parent child child))
      = Real.exp (-crossHeterozygosityDecayRate rates parent child * duration)
        * (ancestral (some (.pi2 parent parent parent parent))
          + migration * ∫ time in (0 : ℝ)..duration,
            Real.exp (crossHeterozygosityDecayRate rates parent child * time)
              * heterozygosityMigrationStencil parent child
                (migrationHistory rates hne migration hmigration ancestral time)) := by
  have h := eq_exp_mul_add_integral (rate := crossHeterozygosityDecayRate rates parent child)
    (migration := migration)
    (value := fun time ↦ migrationHistory rates hne migration hmigration ancestral time
      (some (.pi2 parent parent child child)))
    (source := fun time ↦ heterozygosityMigrationStencil parent child
      (migrationHistory rates hne migration hmigration ancestral time))
    (fun time ↦ by
      have hcoordinate := hasDerivAt_pi.mp
        (hasDerivAt_migrationHistory rates hne hmigration ancestral time)
        (some (.pi2 parent parent child child))
      rwa [withSymmetricMigration_mulVec_pi2 rates hmutation hne hmigration] at hcoordinate)
    (continuous_heterozygosityMigrationStencil
      (continuous_migrationHistory rates hne hmigration ancestral) parent child)
    duration
  refine h.trans ?_
  simp only [migrationHistory_zero, splitTransform_pi2 hne]

/-- **Migration adds nothing to the linkage covariance at the split.**  Right after the split
every coordinate of the stencil is the parent's, so the stencil vanishes.

Assumes: `parent ≠ child`. -/
theorem linkageMigrationStencil_migrationHistory_zero (rates : ManyDemeLDRates D)
    {parent child : Fin D} (hne : parent ≠ child) {migration : ℝ} (hmigration : 0 ≤ migration)
    (ancestral : AffineLowOrderLDCoordinate D → ℝ) :
    linkageMigrationStencil parent child
        (migrationHistory rates hne migration hmigration ancestral 0) = 0 := by
  rw [migrationHistory_zero, lowOrderLDSplitTransform_mulVec]
  simp [linkageMigrationStencil, LowOrderLDCoordinate.mergeSplit, hne]
  ring

/-- **Migration adds nothing to the heterozygosity product at the split.**  Right after the split
every coordinate of the stencil is the parent's, so the stencil vanishes.

Assumes: `parent ≠ child`. -/
theorem heterozygosityMigrationStencil_migrationHistory_zero (rates : ManyDemeLDRates D)
    {parent child : Fin D} (hne : parent ≠ child) {migration : ℝ} (hmigration : 0 ≤ migration)
    (ancestral : AffineLowOrderLDCoordinate D → ℝ) :
    heterozygosityMigrationStencil parent child
        (migrationHistory rates hne migration hmigration ancestral 0) = 0 := by
  rw [migrationHistory_zero, lowOrderLDSplitTransform_mulVec]
  simp [heterozygosityMigrationStencil, LowOrderLDCoordinate.mergeSplit, hne]
  ring

/-! ## The portability ratio with migration -/

/-- **The linkage migration share** `A_D = e^{-ρ̄T} ∫_0^T e^{λ_D s} μ_D(s) ds / E[D²](0)`.

Empirical status: NOT AN EMPIRICAL CLAIM.  An integral along a corpus history. -/
def linkageMigrationShare (rates : ManyDemeLDRates D) {parent child : Fin D}
    (hne : parent ≠ child) (migration : ℝ) (hmigration : 0 ≤ migration)
    (ancestral : AffineLowOrderLDCoordinate D → ℝ) (duration : ℝ) : ℝ :=
  portabilityDecay ((rates.recombination parent + rates.recombination child) / 2) duration
    * (∫ time in (0 : ℝ)..duration, Real.exp (crossLinkageDecayRate rates parent child * time)
      * linkageMigrationStencil parent child
        (migrationHistory rates hne migration hmigration ancestral time))
    / ancestral (some (.DD parent parent))

/-- **The heterozygosity migration share** `A_π = ∫_0^T e^{λ_π s} μ_π(s) ds / E[π²](0)`.

Empirical status: NOT AN EMPIRICAL CLAIM.  An integral along a corpus history. -/
def heterozygosityMigrationShare (rates : ManyDemeLDRates D) {parent child : Fin D}
    (hne : parent ≠ child) (migration : ℝ) (hmigration : 0 ≤ migration)
    (ancestral : AffineLowOrderLDCoordinate D → ℝ) (duration : ℝ) : ℝ :=
  (∫ time in (0 : ℝ)..duration,
      Real.exp (crossHeterozygosityDecayRate rates parent child * time)
        * heterozygosityMigrationStencil parent child
          (migrationHistory rates hne migration hmigration ancestral time))
    / ancestral (some (.pi2 parent parent parent parent))

/-- The ratio of two exponentially weighted moments over an ancestral ratio, with the common
exponential cancelled.

Assumes: nonzero common factor, nonzero ancestral linkage and nonzero ancestral
heterozygosity. -/
theorem ratio_eq_decay_add_div {common decay linkage heterozygosity linkageIntegral
      heterozygosityIntegral migration : ℝ} (hcommon : common ≠ 0) (hlinkage : linkage ≠ 0)
    (hheterozygosity : heterozygosity ≠ 0) :
    common * decay * (linkage + migration * linkageIntegral)
          / (common * (heterozygosity + migration * heterozygosityIntegral))
        / (linkage / heterozygosity)
      = (decay + migration * (decay * linkageIntegral / linkage))
        / (1 + migration * (heterozygosityIntegral / heterozygosity)) := by
  have hshare : 1 + migration * (heterozygosityIntegral / heterozygosity)
      = (heterozygosity + migration * heterozygosityIntegral) / heterozygosity := by
    rw [add_div, div_self hheterozygosity, mul_div_assoc]
  rcases eq_or_ne (heterozygosity + migration * heterozygosityIntegral) 0 with hzero | hzero
  · simp only [hshare, hzero, mul_zero, div_zero, zero_div]
  · rw [hshare]
    field_simp

/-- **The portability ratio with symmetric migration** is `(e^{-ρ̄T} + m A_D) / (1 + m A_π)`.
The drift factor `e^{-(c_S + c_T) T}` common to both moments cancels.

Assumes: no mutation, `parent ≠ child`, a nonzero ancestral `E[D²]` and a nonzero ancestral
heterozygosity product. -/
theorem splitPortabilityRatio_withSymmetricMigration (rates : ManyDemeLDRates D)
    (hmutation : ∀ deme, rates.mutation deme = 0) {parent child : Fin D} (hne : parent ≠ child)
    {migration : ℝ} (hmigration : 0 ≤ migration) {duration : ℝ} (hduration : 0 ≤ duration)
    (ancestral : AffineLowOrderLDCoordinate D → ℝ)
    (hlinkage : ancestral (some (.DD parent parent)) ≠ 0)
    (hheterozygosity : ancestral (some (.pi2 parent parent parent parent)) ≠ 0) :
    splitPortabilityRatio (withSymmetricMigration rates hne migration hmigration) parent child
        hduration ancestral
      = (portabilityDecay ((rates.recombination parent + rates.recombination child) / 2) duration
          + migration * linkageMigrationShare rates hne migration hmigration ancestral duration)
        / (1 + migration
          * heterozygosityMigrationShare rates hne migration hmigration ancestral duration) := by
  have hsplit : Real.exp (-crossLinkageDecayRate rates parent child * duration)
      = Real.exp (-crossHeterozygosityDecayRate rates parent child * duration)
        * portabilityDecay ((rates.recombination parent + rates.recombination child) / 2)
          duration := by
    rw [portabilityDecay, ← Real.exp_add, crossLinkageDecayRate, crossHeterozygosityDecayRate]
    congr 1
    ring
  rw [splitPortabilityRatio, crossSquaredCorrelation, ancestralSquaredCorrelation,
    splitHistoryState_withSymmetricMigration, migrationHistory_DD rates hmutation hne hmigration,
    migrationHistory_pi2 rates hmutation hne hmigration, hsplit, linkageMigrationShare,
    heterozygosityMigrationShare]
  exact ratio_eq_decay_add_div (Real.exp_pos _).ne' hlinkage hheterozygosity

/-- **Without migration the corpus law returns**: at `m = 0` the ratio is `e^{-ρ̄T}`.

Assumes: no mutation, `parent ≠ child`, and a nonzero ancestral correlation. -/
theorem splitPortabilityRatio_withSymmetricMigration_zero (rates : ManyDemeLDRates D)
    (hmutation : ∀ deme, rates.mutation deme = 0) {parent child : Fin D} (hne : parent ≠ child)
    {duration : ℝ} (hduration : 0 ≤ duration) (ancestral : AffineLowOrderLDCoordinate D → ℝ)
    (hsource : ancestralSquaredCorrelation ancestral parent ≠ 0) :
    splitPortabilityRatio (withSymmetricMigration rates hne 0 le_rfl) parent child hduration
        ancestral
      = portabilityDecay ((rates.recombination parent + rates.recombination child) / 2)
          duration :=
  splitPortabilityRatio_eq (withSymmetricMigration rates hne 0 le_rfl)
    (fun source target ↦ by simp [withSymmetricMigration, symmetricPairMigration]) hmutation hne
    hduration ancestral hsource

end

end Descent.Portability.MigrationPortabilityFactor
