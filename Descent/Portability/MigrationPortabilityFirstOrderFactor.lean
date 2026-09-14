/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.MigrationPortabilityFirstOrder
import Descent.Portability.EndToEndSensitivityLaw
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

assert_below Descent.Decision Descent.Program

/-!
# The first-order migration factor of two-locus portability

`MigrationPortabilityFactor` proves that with symmetric migration `m` between the two demes of a
split the portability ratio is `(e^{-ρ̄T} + m A_D) / (1 + m A_π)`, with shares integrated along
the with-migration history.  This module differentiates that ratio at `m = 0`.

## Main results

- `augmentedLowOrderLDGenerator_withSymmetricMigration`: the generator at rate `m` is the
  generator without migration plus `m` times `migrationDirection`, because `lowOrderLDMigration`
  is linear in the migration rates (`lowOrderLDMigration_withSymmetricMigration`).
- `duhamelDerivative_mulVec_DD`, `duhamelDerivative_mulVec_pi2`: Duhamel's formula of
  `EndToEndSensitivityLaw` read in the two cross-population rows, which are diagonal without
  migration.  The derivative of `E[D_S D_T](T)` in `m` at `0` is
  `e^{-λ_D T} ∫_0^T e^{λ_D s} μ_D(s) ds`, with `μ_D` read on the history without migration, and
  likewise for the heterozygosity product.
- `hasDerivAt_affineMigrationPortabilityRatio`,
  `hasDerivWithinAt_splitPortabilityRatio_withSymmetricMigration`: the portability ratio has
  derivative `firstOrderMigrationFactor = A_D⁰ - e^{-ρ̄T} A_π⁰` at `m = 0`, two-sided along the
  affine family of generators and one-sided for the corpus ratio on `m ≥ 0`.  So
  `ratio_m = e^{-ρ̄T} + m φ₁(T) + o(m)`.

## Empirical status

None.  The bodies are algebra and calculus on corpus moment coordinates.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.MigrationPortabilityFirstOrderFactor

open Descent.Coalescent Descent.Portability.TwoLocusPortabilityDecay
  Descent.Portability.MigrationPortabilityFactor Descent.Portability.MigrationPortabilityFirstOrder
open scoped Matrix

noncomputable section

variable {D : ℕ}

/-! ## The generator is affine in the migration rate -/

/-- The pair migration at rate `m` is `m` times the pair migration at unit rate. -/
theorem symmetricPairMigration_eq_mul (parent child : Fin D) (migration : ℝ)
    (source target : Fin D) :
    symmetricPairMigration parent child migration source target
      = migration * symmetricPairMigration parent child 1 source target := by
  unfold symmetricPairMigration
  split_ifs <;> ring

/-- **Migration enters the moment generator linearly.**  The migration part of the generator at
rate `m` is `m` times the migration part at unit rate. -/
theorem lowOrderLDMigration_withSymmetricMigration (rates : ManyDemeLDRates D)
    {parent child : Fin D} (hne : parent ≠ child) {migration : ℝ} (hmigration : 0 ≤ migration)
    (moment : LowOrderLDCoordinate D → ℝ) (coordinate : LowOrderLDCoordinate D) :
    lowOrderLDMigration (withSymmetricMigration rates hne migration hmigration) moment coordinate
      = migration
        * lowOrderLDMigration (withSymmetricMigration rates hne 1 zero_le_one) moment
          coordinate := by
  have hrate : ∀ source target,
      (withSymmetricMigration rates hne migration hmigration).migration source target
        = migration * (withSymmetricMigration rates hne 1 zero_le_one).migration source target :=
    symmetricPairMigration_eq_mul parent child migration
  cases coordinate <;> simp only [lowOrderLDMigration, hrate, mul_add, Finset.mul_sum, mul_assoc]

/-- The drift, recombination and mutation rows do not see the migration rate, so the homogeneous
generator at rate `m` is the one without migration plus `m` times the unit migration part. -/
theorem lowOrderLDHomogeneousGenerator_withSymmetricMigration (rates : ManyDemeLDRates D)
    {parent child : Fin D} (hne : parent ≠ child) {migration : ℝ} (hmigration : 0 ≤ migration)
    (moment : LowOrderLDCoordinate D → ℝ) (coordinate : LowOrderLDCoordinate D) :
    lowOrderLDHomogeneousGenerator (withSymmetricMigration rates hne migration hmigration) moment
        coordinate
      = lowOrderLDHomogeneousGenerator (withSymmetricMigration rates hne 0 le_rfl) moment
          coordinate
        + migration
          * lowOrderLDMigration (withSymmetricMigration rates hne 1 zero_le_one) moment
            coordinate := by
  have hdrift : lowOrderLDDrift (withSymmetricMigration rates hne migration hmigration) moment
      coordinate = lowOrderLDDrift (withSymmetricMigration rates hne 0 le_rfl) moment coordinate :=
    rfl
  have hrecombination :
      lowOrderLDRecombination (withSymmetricMigration rates hne migration hmigration) moment
          coordinate
        = lowOrderLDRecombination (withSymmetricMigration rates hne 0 le_rfl) moment coordinate :=
    rfl
  have hcoupling :
      lowOrderLDMutationCoupling (withSymmetricMigration rates hne migration hmigration) moment
          coordinate
        = lowOrderLDMutationCoupling (withSymmetricMigration rates hne 0 le_rfl) moment
          coordinate :=
    rfl
  have hdamping :
      lowOrderLDRecurrentMutationDamping (withSymmetricMigration rates hne migration hmigration)
          moment coordinate
        = lowOrderLDRecurrentMutationDamping (withSymmetricMigration rates hne 0 le_rfl) moment
          coordinate :=
    rfl
  rw [lowOrderLDHomogeneousGenerator, lowOrderLDHomogeneousGenerator, hdrift, hrecombination,
    hcoupling, hdamping, lowOrderLDMigration_withSymmetricMigration rates hne hmigration,
    lowOrderLDMigration_withSymmetricMigration rates hne (le_rfl : (0 : ℝ) ≤ 0)]
  ring

/-- **The migration direction of the generator**: the generator at unit migration minus the
generator without migration.

Empirical status: NOT AN EMPIRICAL CLAIM.  A difference of two corpus generators. -/
def migrationDirection (rates : ManyDemeLDRates D) {parent child : Fin D}
    (hne : parent ≠ child) :
    Matrix (AffineLowOrderLDCoordinate D) (AffineLowOrderLDCoordinate D) ℝ :=
  augmentedLowOrderLDGenerator (withSymmetricMigration rates hne 1 zero_le_one)
    - augmentedLowOrderLDGenerator (withSymmetricMigration rates hne 0 le_rfl)

/-- **The generator is affine in the migration rate**: at rate `m` it is the generator without
migration plus `m` times `migrationDirection`. -/
theorem augmentedLowOrderLDGenerator_withSymmetricMigration (rates : ManyDemeLDRates D)
    {parent child : Fin D} (hne : parent ≠ child) {migration : ℝ} (hmigration : 0 ≤ migration) :
    augmentedLowOrderLDGenerator (withSymmetricMigration rates hne migration hmigration)
      = augmentedLowOrderLDGenerator (withSymmetricMigration rates hne 0 le_rfl)
        + migration • migrationDirection rates hne := by
  have hforcing : ∀ (rate : ℝ) (hrate : 0 ≤ rate) (row : LowOrderLDCoordinate D),
      lowOrderLDMutationForcing (withSymmetricMigration rates hne rate hrate) row
        = lowOrderLDMutationForcing rates row := fun _ _ _ ↦ rfl
  ext row column
  rcases row with _ | row
  · simp [migrationDirection, augmentedLowOrderLDGenerator]
  · rcases column with _ | column
    · simp [migrationDirection, augmentedLowOrderLDGenerator, hforcing]
    · simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul,
        migrationDirection, augmentedLowOrderLDGenerator]
      rw [lowOrderLDHomogeneousGenerator_withSymmetricMigration rates hne hmigration,
        lowOrderLDHomogeneousGenerator_withSymmetricMigration rates hne zero_le_one]
      ring

/-- **The migration direction reads the linkage migration stencil** in the cross-population
linkage row.

Assumes: no mutation and `parent ≠ child`. -/
theorem migrationDirection_mulVec_DD (rates : ManyDemeLDRates D)
    (hmutation : ∀ deme, rates.mutation deme = 0) {parent child : Fin D} (hne : parent ≠ child)
    (state : AffineLowOrderLDCoordinate D → ℝ) :
    (migrationDirection rates hne).mulVec state (some (.DD parent child))
      = linkageMigrationStencil parent child state := by
  rw [migrationDirection, Matrix.sub_mulVec, Pi.sub_apply,
    withSymmetricMigration_mulVec_DD rates hmutation hne zero_le_one,
    withSymmetricMigration_mulVec_DD rates hmutation hne le_rfl]
  ring

/-- **The migration direction reads the heterozygosity migration stencil** in the
cross-population heterozygosity row.

Assumes: no mutation and `parent ≠ child`. -/
theorem migrationDirection_mulVec_pi2 (rates : ManyDemeLDRates D)
    (hmutation : ∀ deme, rates.mutation deme = 0) {parent child : Fin D} (hne : parent ≠ child)
    (state : AffineLowOrderLDCoordinate D → ℝ) :
    (migrationDirection rates hne).mulVec state (some (.pi2 parent parent child child))
      = heterozygosityMigrationStencil parent child state := by
  rw [migrationDirection, Matrix.sub_mulVec, Pi.sub_apply,
    withSymmetricMigration_mulVec_pi2 rates hmutation hne zero_le_one,
    withSymmetricMigration_mulVec_pi2 rates hmutation hne le_rfl]
  ring

/-! ## The affine family of histories -/

/-- **The affine migration history**: the split vector evolved under the generator without
migration plus `θ` times `migrationDirection`, at every real `θ`.  At `θ ≥ 0` it is
`migrationHistory`.

Empirical status: NOT AN EMPIRICAL CLAIM.  A matrix exponential applied to the split vector. -/
def affineMigrationHistory (rates : ManyDemeLDRates D) {parent child : Fin D}
    (hne : parent ≠ child) (ancestral : AffineLowOrderLDCoordinate D → ℝ) (θ time : ℝ) :
    AffineLowOrderLDCoordinate D → ℝ :=
  (matrixExponential
      (augmentedLowOrderLDGenerator (withSymmetricMigration rates hne 0 le_rfl)
        + θ • migrationDirection rates hne) time).mulVec
    ((lowOrderLDSplitTransform parent child).mulVec ancestral)

/-- At a nonnegative migration rate the affine history is the migration history. -/
theorem migrationHistory_eq_affineMigrationHistory (rates : ManyDemeLDRates D)
    {parent child : Fin D} (hne : parent ≠ child) {migration : ℝ} (hmigration : 0 ≤ migration)
    (ancestral : AffineLowOrderLDCoordinate D → ℝ) (time : ℝ) :
    migrationHistory rates hne migration hmigration ancestral time
      = affineMigrationHistory rates hne ancestral migration time := by
  rw [migrationHistory, augmentedLowOrderLDGenerator_withSymmetricMigration rates hne hmigration,
    affineMigrationHistory]

/-- At rate zero the affine history is the history without migration. -/
theorem affineMigrationHistory_zero (rates : ManyDemeLDRates D) {parent child : Fin D}
    (hne : parent ≠ child) (ancestral : AffineLowOrderLDCoordinate D → ℝ) (time : ℝ) :
    affineMigrationHistory rates hne ancestral 0 time
      = migrationHistory rates hne 0 le_rfl ancestral time := by
  rw [affineMigrationHistory, zero_smul, add_zero, migrationHistory]

/-- Every entry of the affine generator is differentiable in the rate, with derivative the entry
of `migrationDirection`. -/
theorem hasDerivAt_affineGenerator_apply (rates : ManyDemeLDRates D) {parent child : Fin D}
    (hne : parent ≠ child) (θ₀ : ℝ) (row column : AffineLowOrderLDCoordinate D) :
    HasDerivAt
      (fun θ ↦ (augmentedLowOrderLDGenerator (withSymmetricMigration rates hne 0 le_rfl)
        + θ • migrationDirection rates hne) row column)
      (migrationDirection rates hne row column) θ₀ := by
  simpa only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, one_mul] using
    ((hasDerivAt_id' (x := θ₀)).mul_const (migrationDirection rates hne row column)).const_add
      (augmentedLowOrderLDGenerator (withSymmetricMigration rates hne 0 le_rfl) row column)

/-- **The history derivative in the migration rate.**  At `θ = 0` every coordinate of the affine
history has as derivative that coordinate of the Duhamel derivative of the propagator in the
direction `migrationDirection`, applied to the split vector. -/
theorem hasDerivAt_affineMigrationHistory (rates : ManyDemeLDRates D) {parent child : Fin D}
    (hne : parent ≠ child) (ancestral : AffineLowOrderLDCoordinate D → ℝ) (time : ℝ)
    (coordinate : AffineLowOrderLDCoordinate D) :
    HasDerivAt (fun θ ↦ affineMigrationHistory rates hne ancestral θ time coordinate)
      ((EndToEndSensitivityLaw.duhamelDerivative
          (augmentedLowOrderLDGenerator (withSymmetricMigration rates hne 0 le_rfl))
          (migrationDirection rates hne) time).mulVec
        ((lowOrderLDSplitTransform parent child).mulVec ancestral) coordinate) 0 := by
  have hentry := fun column ↦
    (EndToEndSensitivityLaw.hasDerivAt_matrixExponential_apply
      (Q := fun θ ↦ augmentedLowOrderLDGenerator (withSymmetricMigration rates hne 0 le_rfl)
        + θ • migrationDirection rates hne)
      (hasDerivAt_affineGenerator_apply rates hne 0) time coordinate column).mul_const
      ((lowOrderLDSplitTransform parent child).mulVec ancestral column)
  have hsum := HasDerivAt.fun_sum (u := Finset.univ) fun column _ ↦ hentry column
  rw [zero_smul, add_zero] at hsum
  exact hsum

/-! ## Duhamel readouts in the diagonal rows -/

/-- A unit point mass on the left of a dot product reads the vector at its point. -/
theorem unitPointMass_dotProduct {ι : Type*} [Fintype ι] [DecidableEq ι] (point : ι)
    (vector : ι → ℝ) : (fun row ↦ if row = point then (1 : ℝ) else 0) ⬝ᵥ vector = vector point :=
  sum_unitPointMass_mul point vector

/-- **The forward law of a diagonal coordinate.**  If the row of `point` is `-decay` times its
unit row, the unit point mass at `point` pushed forward by the propagator reads `e^{-decay t}`
times the vector at `point`.

Assumes: the row of `point` is diagonal. -/
theorem unitPointMass_vecMul_matrixExponential_dotProduct {ι : Type*} [Fintype ι]
    [DecidableEq ι] (A : Matrix ι ι ℝ) (time : ℝ) (vector : ι → ℝ) {point : ι} {decay : ℝ}
    (hrow : ∀ column, A point column = -decay * (if column = point then 1 else 0)) :
    ((fun row ↦ if row = point then (1 : ℝ) else 0) ᵥ* matrixExponential A time) ⬝ᵥ vector
      = Real.exp (-decay * time) * vector point := by
  rw [← Matrix.dotProduct_mulVec, unitPointMass_dotProduct,
    matrixExponential_mulVec_apply_of_row_eq A time (-decay) vector point hrow, mul_comm time]

/-- **Reversing the time of a Duhamel integral.**
`∫_0^T e^{-λ s} g(T - s) ds = e^{-λ T} ∫_0^T e^{λ s} g(s) ds`. -/
theorem integral_exp_neg_mul_comp_sub (rate duration : ℝ) (source : ℝ → ℝ) :
    ∫ time in (0 : ℝ)..duration, Real.exp (-rate * time) * source (duration - time)
      = Real.exp (-rate * duration)
        * ∫ time in (0 : ℝ)..duration, Real.exp (rate * time) * source time := by
  have hshift := intervalIntegral.integral_comp_sub_left
    (f := fun time ↦ Real.exp (-rate * (duration - time)) * source time) (d := duration)
    (a := 0) (b := duration)
  simp only [sub_sub_cancel, sub_self, sub_zero] at hshift
  rw [hshift, ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr fun time _ ↦ ?_
  rw [← mul_assoc, ← Real.exp_add]
  congr 2
  ring

/-- **A Duhamel readout at a diagonal coordinate.**  If the row of `point` in `Q` is `-decay`
times its unit row, and `Q'` reads `source` in that row, then the `point` coordinate of the
Duhamel derivative applied to `v` is `e^{-decay T} ∫_0^T e^{decay s} source(e^{sQ} v) ds`.

Assumes: the row of `point` in `Q` is diagonal, and the row of `point` in `Q'` reads `source`. -/
theorem duhamelDerivative_mulVec_apply_of_diagonal_row {ι : Type*} [Fintype ι] [DecidableEq ι]
    (Q Q' : Matrix ι ι ℝ) (duration : ℝ) (vector : ι → ℝ) {point : ι} {decay : ℝ}
    (source : (ι → ℝ) → ℝ)
    (hrow : ∀ column, Q point column = -decay * (if column = point then 1 else 0))
    (hsource : ∀ state, Q'.mulVec state point = source state) :
    (EndToEndSensitivityLaw.duhamelDerivative Q Q' duration).mulVec vector point
      = Real.exp (-decay * duration)
        * ∫ time in (0 : ℝ)..duration,
          Real.exp (decay * time) * source ((matrixExponential Q time).mulVec vector) := by
  have hread := EndToEndSensitivityLaw.dotProduct_duhamelDerivative_mulVec Q Q' duration
    (fun row ↦ if row = point then (1 : ℝ) else 0) vector
  rw [unitPointMass_dotProduct] at hread
  rw [hread]
  refine (intervalIntegral.integral_congr fun time _ ↦ ?_).trans
    (integral_exp_neg_mul_comp_sub decay duration
      fun time ↦ source ((matrixExponential Q time).mulVec vector))
  rw [unitPointMass_vecMul_matrixExponential_dotProduct Q time _ hrow, hsource]

/-- **The derivative of the cross-population linkage covariance in `m` at `0`** is
`e^{-λ_D T} ∫_0^T e^{λ_D s} μ_D(s) ds`, with `μ_D` read on the history without migration.

Assumes: no mutation and `parent ≠ child`. -/
theorem duhamelDerivative_mulVec_DD (rates : ManyDemeLDRates D)
    (hmutation : ∀ deme, rates.mutation deme = 0) {parent child : Fin D} (hne : parent ≠ child)
    (ancestral : AffineLowOrderLDCoordinate D → ℝ) (duration : ℝ) :
    (EndToEndSensitivityLaw.duhamelDerivative
        (augmentedLowOrderLDGenerator (withSymmetricMigration rates hne 0 le_rfl))
        (migrationDirection rates hne) duration).mulVec
      ((lowOrderLDSplitTransform parent child).mulVec ancestral) (some (.DD parent child))
      = Real.exp (-crossLinkageDecayRate rates parent child * duration)
        * ∫ time in (0 : ℝ)..duration,
          Real.exp (crossLinkageDecayRate rates parent child * time)
            * linkageMigrationStencil parent child
              (migrationHistory rates hne 0 le_rfl ancestral time) :=
  duhamelDerivative_mulVec_apply_of_diagonal_row _ _ duration _
    (linkageMigrationStencil parent child)
    (augmentedLowOrderLDGenerator_DD_row _ (withSymmetricMigration_zero_migration rates hne)
      hmutation hne)
    (migrationDirection_mulVec_DD rates hmutation hne)

/-- **The derivative of the cross-population heterozygosity product in `m` at `0`** is
`e^{-λ_π T} ∫_0^T e^{λ_π s} μ_π(s) ds`, with `μ_π` read on the history without migration.

Assumes: no mutation and `parent ≠ child`. -/
theorem duhamelDerivative_mulVec_pi2 (rates : ManyDemeLDRates D)
    (hmutation : ∀ deme, rates.mutation deme = 0) {parent child : Fin D} (hne : parent ≠ child)
    (ancestral : AffineLowOrderLDCoordinate D → ℝ) (duration : ℝ) :
    (EndToEndSensitivityLaw.duhamelDerivative
        (augmentedLowOrderLDGenerator (withSymmetricMigration rates hne 0 le_rfl))
        (migrationDirection rates hne) duration).mulVec
      ((lowOrderLDSplitTransform parent child).mulVec ancestral)
        (some (.pi2 parent parent child child))
      = Real.exp (-crossHeterozygosityDecayRate rates parent child * duration)
        * ∫ time in (0 : ℝ)..duration,
          Real.exp (crossHeterozygosityDecayRate rates parent child * time)
            * heterozygosityMigrationStencil parent child
              (migrationHistory rates hne 0 le_rfl ancestral time) :=
  duhamelDerivative_mulVec_apply_of_diagonal_row _ _ duration _
    (heterozygosityMigrationStencil parent child)
    (augmentedLowOrderLDGenerator_pi2_row _ (withSymmetricMigration_zero_migration rates hne)
      hmutation hne)
    (migrationDirection_mulVec_pi2 rates hmutation hne)

/-! ## The elementary parts of the linkage stencil -/

/-- **The cross-population linkage covariance without migration** decays from `DD₀` at
`λ_D = c_S + c_T + (ρ_S + ρ_T)/2`.

Assumes: no mutation and `parent ≠ child`. -/
theorem noMigrationHistory_DD_cross (rates : ManyDemeLDRates D)
    (hmutation : ∀ deme, rates.mutation deme = 0) {parent child : Fin D} (hne : parent ≠ child)
    (ancestral : AffineLowOrderLDCoordinate D → ℝ) (time : ℝ) :
    migrationHistory rates hne 0 le_rfl ancestral time (some (.DD parent child))
      = Real.exp (-crossLinkageDecayRate rates parent child * time)
        * ancestral (some (.DD parent parent)) := by
  rw [migrationHistory_DD rates hmutation hne le_rfl, zero_mul, add_zero]

/-- **A fed linkage contrast.**  Without migration or mutation, along any trajectory
`Dz(i, j, j)(t) = e^{-β_i t} (Dz(i, j, j)(0) + α DD(i, j)(0)) - α e^{-λ t} DD(i, j)(0)`, with
`α = 4 c_j / β_j`, `β_i = c_i + ρ_i/2` and `λ = c_i + c_j + (ρ_i + ρ_j)/2`.

Assumes: no migration, no mutation, and `first ≠ second`. -/
theorem matrixExponential_mulVec_Dz_fed (rates : ManyDemeLDRates D)
    (hmigration : ∀ source target, rates.migration source target = 0)
    (hmutation : ∀ deme, rates.mutation deme = 0) {first second : Fin D} (hne : first ≠ second)
    (time : ℝ) (state : AffineLowOrderLDCoordinate D → ℝ) :
    (matrixExponential (augmentedLowOrderLDGenerator rates) time).mulVec state
        (some (.Dz first second second))
      = Real.exp (-linkageRate rates first * time)
          * (state (some (.Dz first second second))
            + 4 * rates.coalescence second / linkageRate rates second
              * state (some (.DD first second)))
        - 4 * rates.coalescence second / linkageRate rates second
          * Real.exp (-(rates.coalescence first + rates.coalescence second
              + (rates.recombination first + rates.recombination second) / 2) * time)
          * state (some (.DD first second)) := by
  have hcombination := matrixExponential_Dz_combination rates hmigration hmutation hne time state
  rw [matrixExponential_mulVec_apply_of_row_eq _ time _ _ _
    (augmentedLowOrderLDGenerator_DD_row rates hmigration hmutation hne), mul_comm time]
    at hcombination
  linear_combination hcombination

/-- **The child's fed contrast `Dz(T, S, S)` without migration.**

Assumes: no mutation and `parent ≠ child`. -/
theorem noMigrationHistory_Dz_childFed (rates : ManyDemeLDRates D)
    (hmutation : ∀ deme, rates.mutation deme = 0) {parent child : Fin D} (hne : parent ≠ child)
    (ancestral : AffineLowOrderLDCoordinate D → ℝ) (time : ℝ) :
    migrationHistory rates hne 0 le_rfl ancestral time (some (.Dz child parent parent))
      = Real.exp (-linkageRate rates child * time)
          * (ancestral (some (.Dz parent parent parent))
            + 4 * rates.coalescence parent / linkageRate rates parent
              * ancestral (some (.DD parent parent)))
        - 4 * rates.coalescence parent / linkageRate rates parent
          * Real.exp (-(rates.coalescence child + rates.coalescence parent
              + (rates.recombination child + rates.recombination parent) / 2) * time)
          * ancestral (some (.DD parent parent)) := by
  have h := matrixExponential_mulVec_Dz_fed _ (withSymmetricMigration_zero_migration rates hne)
    hmutation (Ne.symm hne) time ((lowOrderLDSplitTransform parent child).mulVec ancestral)
  rw [(splitTransform_block hne ancestral).2.2.1, (splitTransform_block hne ancestral).1] at h
  exact h

/-- **The parent's fed contrast `Dz(S, T, T)` without migration.**

Assumes: no mutation and `parent ≠ child`. -/
theorem noMigrationHistory_Dz_parentFed (rates : ManyDemeLDRates D)
    (hmutation : ∀ deme, rates.mutation deme = 0) {parent child : Fin D} (hne : parent ≠ child)
    (ancestral : AffineLowOrderLDCoordinate D → ℝ) (time : ℝ) :
    migrationHistory rates hne 0 le_rfl ancestral time (some (.Dz parent child child))
      = Real.exp (-linkageRate rates parent * time)
          * (ancestral (some (.Dz parent parent parent))
            + 4 * rates.coalescence child / linkageRate rates child
              * ancestral (some (.DD parent parent)))
        - 4 * rates.coalescence child / linkageRate rates child
          * Real.exp (-(rates.coalescence parent + rates.coalescence child
              + (rates.recombination parent + rates.recombination child) / 2) * time)
          * ancestral (some (.DD parent parent)) := by
  have h := matrixExponential_mulVec_Dz_fed _ (withSymmetricMigration_zero_migration rates hne)
    hmutation hne time ((lowOrderLDSplitTransform parent child).mulVec ancestral)
  rw [(splitTransform_block hne ancestral).2.1, splitTransform_DD hne] at h
  exact h

/-- **The four diagonal contrasts without migration.**  `Dz(T, S, T)`, `Dz(T, T, S)`,
`Dz(S, T, S)` and `Dz(S, S, T)` decay from `Dz₀` at `3 c_i + ρ_i/2`, `i` their first index.

Assumes: no mutation and `parent ≠ child`. -/
theorem noMigrationHistory_Dz_diagonal (rates : ManyDemeLDRates D)
    (hmutation : ∀ deme, rates.mutation deme = 0) {parent child : Fin D} (hne : parent ≠ child)
    (ancestral : AffineLowOrderLDCoordinate D → ℝ) (time : ℝ) :
    migrationHistory rates hne 0 le_rfl ancestral time (some (.Dz child parent child))
        = Real.exp (-(3 * rates.coalescence child + rates.recombination child / 2) * time)
          * ancestral (some (.Dz parent parent parent)) ∧
      migrationHistory rates hne 0 le_rfl ancestral time (some (.Dz child child parent))
        = Real.exp (-(3 * rates.coalescence child + rates.recombination child / 2) * time)
          * ancestral (some (.Dz parent parent parent)) ∧
      migrationHistory rates hne 0 le_rfl ancestral time (some (.Dz parent child parent))
        = Real.exp (-(3 * rates.coalescence parent + rates.recombination parent / 2) * time)
          * ancestral (some (.Dz parent parent parent)) ∧
      migrationHistory rates hne 0 le_rfl ancestral time (some (.Dz parent parent child))
        = Real.exp (-(3 * rates.coalescence parent + rates.recombination parent / 2) * time)
          * ancestral (some (.Dz parent parent parent)) := by
  have hmigration := withSymmetricMigration_zero_migration rates hne
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [migrationHistory] <;>
    first
    | rw [matrixExponential_mulVec_apply_of_diagonal_row _ time _
        (augmentedLowOrderLDGenerator_Dz_mixed_row _ hmigration hmutation (Ne.symm hne))]
    | rw [matrixExponential_mulVec_apply_of_diagonal_row _ time _
        (augmentedLowOrderLDGenerator_Dz_leading_row _ hmigration hmutation (Ne.symm hne))]
    | rw [matrixExponential_mulVec_apply_of_diagonal_row _ time _
        (augmentedLowOrderLDGenerator_Dz_mixed_row _ hmigration hmutation hne)]
    | rw [matrixExponential_mulVec_apply_of_diagonal_row _ time _
        (augmentedLowOrderLDGenerator_Dz_leading_row _ hmigration hmutation hne)]
  all_goals simp [lowOrderLDSplitTransform_mulVec, LowOrderLDCoordinate.mergeSplit, hne,
    withSymmetricMigration]
