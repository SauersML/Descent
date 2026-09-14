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
the with-migration history.  This module differentiates that ratio at `m = 0`, reads the linkage
stencil on the history without migration, and evaluates the factor in closed form without
recombination.

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
- The elementary parts of the linkage stencil without migration: `noMigrationHistory_DD_cross`,
  the fed contrasts `noMigrationHistory_Dz_childFed` and `noMigrationHistory_Dz_parentFed`
  (through `matrixExponential_mulVec_Dz_fed`), and `noMigrationHistory_Dz_diagonal`.
- `matrixExponential_mulVec_withinDemeCoordinate`, `noMigrationHistory_withinDemeCoordinate`: the
  within-deme coordinates `DD(i, i)`, `Dz(i, i, i)`, `pi2(i, i, i, i)` are the matrix exponential
  of the 3×3 `withinDemeBlock` applied to the parent's ancestral values (`withinDemeReadout`).
- `linkageMigrationStencil_noMigration`: at equal rates
  `μ_D = 2 w_DD + w_Dz/2 + e^{-βt} (Dz₀ + α DD₀)/2 - (2 + α/2) e^{-(2c + ρ)t} DD₀
  - e^{-(3c + ρ/2)t} Dz₀`, with `w` the within-deme readout, `β = c + ρ/2` and `α = 4c/β`.
- `heterozygosityMigrationShare_noMigration`: `A_π⁰` in closed form at equal rates.
- Without recombination, `matrixExponential_mulVec_withinDeme_slow` and
  `matrixExponential_mulVec_withinDeme_fast` give the left eigenvectors `(2, 1, 2)` at `-c` and
  `(1, 0, -1)` at `-3c` of the within-deme block.  Through them
  `linkageMigrationStencil_noMigration_zeroRecombination` reads
  `μ_D = e^{-ct} (3 DD₀ + Dz₀ + π₀) + e^{-3ct} (DD₀ - π₀ - Dz₀) - 4 e^{-2ct} DD₀`, and
  `linkageMigrationShare_noMigration_zeroRecombination` gives `A_D⁰`.
- `firstOrderMigrationFactor_zeroRecombination`:
  `φ₁(T) = 2 (cosh cT - 1) (π₀ - DD₀) (π₀ + Dz₀) / (c DD₀ π₀)`.
  `firstOrderMigrationFactor_nonneg_zeroRecombination`: `φ₁ ≥ 0` when `DD₀ ≤ π₀` and
  `π₀ + Dz₀ ≥ 0`.

## Significance

The corpus law `e^{-ρ̄T}` holds without migration.  A little migration moves portability by
`m φ₁(T)`, and `φ₁` has two parts.  Migration restores shared linkage, which raises the ratio
through `A_D⁰`, and it restores shared heterozygosity, which lowers it through `A_π⁰`.  Without
recombination the two parts combine into `2 (cosh cT - 1) (π₀ - DD₀) (π₀ + Dz₀) / (c DD₀ π₀)`.
The terms linear in `T` cancel, and the factor grows with the split time.

## Scope

Two demes of the corpus rates exchange migrants symmetrically, no other pair exchanges any, and
mutation is zero.  The derivative is taken at `m = 0`.  It does not say how large `m` may be
before the first-order reading fails, and no `O(m²)` remainder bound is proved.  The closed forms
assume equal drift and recombination in the two demes.  With recombination the linkage stencil is
left as a matrix-exponential readout of the within-deme block, and only without recombination
are the linkage share and the factor elementary.  The conditions `DD₀ ≤ π₀` and `π₀ + Dz₀ ≥ 0` of
the sign theorem are hypotheses on the ancestral moments; nothing here derives them.

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
  simp only [lowOrderLDHomogeneousGenerator]
  rw [hdrift, hrecombination, hcoupling, hdamping,
    lowOrderLDMigration_withSymmetricMigration rates hne hmigration,
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
      (fun θ : ℝ ↦ (augmentedLowOrderLDGenerator (withSymmetricMigration rates hne 0 le_rfl)
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
  simpa only [zero_smul, add_zero] using hsum

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

/-! ## The within-deme block as a matrix-exponential readout -/

/-- **The within-deme rows.**  Without migration or mutation the rows of `DD(i, i)`,
`Dz(i, i, i)` and `pi2(i, i, i, i)` read only these three coordinates:
`-(3 c + ρ) DD + c Dz + c pi2`, `4 c DD - (5 c + ρ/2) Dz` and `c Dz - 2 c pi2`.

Assumes: no migration and no mutation. -/
theorem augmentedLowOrderLDGenerator_withinDeme_rows (rates : ManyDemeLDRates D)
    (hmigration : ∀ source target, rates.migration source target = 0)
    (hmutation : ∀ deme, rates.mutation deme = 0) (deme : Fin D) :
    (∀ column, augmentedLowOrderLDGenerator rates (some (.DD deme deme)) column
      = -(3 * rates.coalescence deme + rates.recombination deme)
          * (if some (.DD deme deme) = column then 1 else 0)
        + rates.coalescence deme * (if some (.Dz deme deme deme) = column then 1 else 0)
        + rates.coalescence deme
          * (if some (.pi2 deme deme deme deme) = column then 1 else 0)) ∧
      (∀ column, augmentedLowOrderLDGenerator rates (some (.Dz deme deme deme)) column
        = 4 * rates.coalescence deme * (if some (.DD deme deme) = column then 1 else 0)
          - (5 * rates.coalescence deme + rates.recombination deme / 2)
            * (if some (.Dz deme deme deme) = column then 1 else 0)) ∧
      (∀ column, augmentedLowOrderLDGenerator rates (some (.pi2 deme deme deme deme)) column
        = rates.coalescence deme * (if some (.Dz deme deme deme) = column then 1 else 0)
          - 2 * rates.coalescence deme
            * (if some (.pi2 deme deme deme deme) = column then 1 else 0)) := by
  refine ⟨fun column ↦ ?_, fun column ↦ ?_, fun column ↦ ?_⟩ <;> rcases column with _ | column <;>
    first
    | (simp [augmentedLowOrderLDGenerator, lowOrderLDMutationForcing]; done)
    | (migration_row_entry; simp [hmigration, hmutation]; ring)

/-- **The within-deme block** of one deme's moment generator on `(DD, Dz, pi2)`:
`[[-(3c + ρ), c, c], [4c, -(5c + ρ/2), 0], [0, c, -2c]]`.

Empirical status: NOT AN EMPIRICAL CLAIM.  A matrix of rates. -/
def withinDemeBlock (rates : ManyDemeLDRates D) (deme : Fin D) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![-(3 * rates.coalescence deme + rates.recombination deme), rates.coalescence deme,
      rates.coalescence deme;
    4 * rates.coalescence deme, -(5 * rates.coalescence deme + rates.recombination deme / 2), 0;
    0, rates.coalescence deme, -(2 * rates.coalescence deme)]

/-- **The within-deme coordinates** `DD(i, i)`, `Dz(i, i, i)` and `pi2(i, i, i, i)` of one deme.

Empirical status: NOT AN EMPIRICAL CLAIM.  Three coordinate labels. -/
def withinDemeCoordinate (deme : Fin D) : Fin 3 → AffineLowOrderLDCoordinate D :=
  ![some (.DD deme deme), some (.Dz deme deme deme), some (.pi2 deme deme deme deme)]

/-- **The within-deme projection** onto the three within-deme coordinates of one deme.

Empirical status: NOT AN EMPIRICAL CLAIM.  A coordinate selection matrix. -/
def withinDemeProjection (deme : Fin D) : Matrix (Fin 3) (AffineLowOrderLDCoordinate D) ℝ :=
  fun other column ↦ if withinDemeCoordinate deme other = column then 1 else 0

/-- **The within-deme block is a matrix-exponential readout.**  Without migration or mutation the
within-deme coordinates of one deme along any trajectory are `e^{tM}` applied to their initial
values, with `M = withinDemeBlock`.

Assumes: no migration and no mutation. -/
theorem matrixExponential_mulVec_withinDemeCoordinate (rates : ManyDemeLDRates D)
    (hmigration : ∀ source target, rates.migration source target = 0)
    (hmutation : ∀ deme, rates.mutation deme = 0) (deme : Fin D) (time : ℝ)
    (state : AffineLowOrderLDCoordinate D → ℝ) (index : Fin 3) :
    (matrixExponential (augmentedLowOrderLDGenerator rates) time).mulVec state
        (withinDemeCoordinate deme index)
      = (matrixExponential (withinDemeBlock rates deme) time).mulVec
          (fun other ↦ state (withinDemeCoordinate deme other)) index := by
  have hrows := augmentedLowOrderLDGenerator_withinDeme_rows rates hmigration hmutation deme
  have hgenerator : withinDemeProjection deme * augmentedLowOrderLDGenerator rates
      = withinDemeBlock rates deme * withinDemeProjection deme := by
    ext other column
    simp only [Matrix.mul_apply, withinDemeProjection, sum_unitPointMass_left, Fin.sum_univ_three]
    fin_cases other <;>
      simp [withinDemeCoordinate, withinDemeBlock, hrows.1, hrows.2.1, hrows.2.2] <;>
      split_ifs <;> ring
  have hread : ∀ vector : AffineLowOrderLDCoordinate D → ℝ,
      (withinDemeProjection deme).mulVec vector
        = fun other ↦ vector (withinDemeCoordinate deme other) :=
    fun vector ↦ funext fun other ↦
      sum_unitPointMass_left (withinDemeCoordinate deme other) vector
  have hstate := congrArg (fun matrix ↦ matrix.mulVec state)
    (matrixExponential_intertwines (withinDemeProjection deme)
      (augmentedLowOrderLDGenerator rates) (withinDemeBlock rates deme) hgenerator time)
  simp only [← Matrix.mulVec_mulVec, hread] at hstate
  exact congrFun hstate index

/-- **The within-deme readout** `e^{tM} (DD₀, Dz₀, π₀)`: the within-deme block of `deme` applied
to the ancestral within-deme coordinates of `parent`.

Empirical status: NOT AN EMPIRICAL CLAIM.  A matrix exponential applied to three coordinates. -/
def withinDemeReadout (rates : ManyDemeLDRates D) (deme parent : Fin D)
    (ancestral : AffineLowOrderLDCoordinate D → ℝ) (time : ℝ) : Fin 3 → ℝ :=
  (matrixExponential (withinDemeBlock rates deme) time).mulVec
    fun other ↦ ancestral (withinDemeCoordinate parent other)

/-- Right after the split, the within-deme coordinates of either deme are the parent's.

Assumes: `parent ≠ child`, and `deme` is the parent or the child. -/
theorem splitTransform_withinDemeCoordinate {parent child : Fin D} (hne : parent ≠ child)
    (ancestral : AffineLowOrderLDCoordinate D → ℝ) {deme : Fin D}
    (hdeme : deme = parent ∨ deme = child) (index : Fin 3) :
    (lowOrderLDSplitTransform parent child).mulVec ancestral (withinDemeCoordinate deme index)
      = ancestral (withinDemeCoordinate parent index) := by
  rcases hdeme with rfl | rfl <;> fin_cases index <;>
    simp [withinDemeCoordinate, lowOrderLDSplitTransform_mulVec,
      LowOrderLDCoordinate.mergeSplit, hne]

/-- **The within-deme coordinates of the split history without migration**: in either deme they
are the within-deme readout of the parent's ancestral coordinates.

Assumes: no mutation, `parent ≠ child`, and `deme` is the parent or the child. -/
theorem noMigrationHistory_withinDemeCoordinate (rates : ManyDemeLDRates D)
    (hmutation : ∀ deme, rates.mutation deme = 0) {parent child : Fin D} (hne : parent ≠ child)
    (ancestral : AffineLowOrderLDCoordinate D → ℝ) (time : ℝ) {deme : Fin D}
    (hdeme : deme = parent ∨ deme = child) (index : Fin 3) :
    migrationHistory rates hne 0 le_rfl ancestral time (withinDemeCoordinate deme index)
      = withinDemeReadout rates deme parent ancestral time index := by
  have hinitial : (fun other ↦ (lowOrderLDSplitTransform parent child).mulVec ancestral
        (withinDemeCoordinate deme other))
      = fun other ↦ ancestral (withinDemeCoordinate parent other) :=
    funext fun other ↦ splitTransform_withinDemeCoordinate hne ancestral hdeme other
  have h := matrixExponential_mulVec_withinDemeCoordinate _
    (withSymmetricMigration_zero_migration rates hne) hmutation deme time
    ((lowOrderLDSplitTransform parent child).mulVec ancestral) index
  rw [hinitial] at h
  exact h

/-- **The linkage migration stencil on the history without migration, at equal rates.**  With
`w = withinDemeReadout`, `β = c + ρ/2` and `α = 4c/β`,
`μ_D(t) = 2 w_DD(t) + w_Dz(t)/2 + e^{-βt} (Dz₀ + α DD₀)/2 - (2 + α/2) e^{-(2c + ρ) t} DD₀
- e^{-(3c + ρ/2) t} Dz₀`.

Assumes: no mutation, `parent ≠ child`, and equal drift and recombination rates. -/
theorem linkageMigrationStencil_noMigration (rates : ManyDemeLDRates D)
    (hmutation : ∀ deme, rates.mutation deme = 0) {parent child : Fin D} (hne : parent ≠ child)
    (hcoal : rates.coalescence child = rates.coalescence parent)
    (hrec : rates.recombination child = rates.recombination parent)
    (ancestral : AffineLowOrderLDCoordinate D → ℝ) (time : ℝ) :
    linkageMigrationStencil parent child (migrationHistory rates hne 0 le_rfl ancestral time)
      = 2 * withinDemeReadout rates parent parent ancestral time 0
          + withinDemeReadout rates parent parent ancestral time 1 / 2
        + Real.exp (-linkageRate rates parent * time)
          * (ancestral (some (.Dz parent parent parent))
            + 4 * rates.coalescence parent / linkageRate rates parent
              * ancestral (some (.DD parent parent))) / 2
        - (2 + 2 * rates.coalescence parent / linkageRate rates parent)
          * Real.exp (-(2 * rates.coalescence parent + rates.recombination parent) * time)
          * ancestral (some (.DD parent parent))
        - Real.exp (-(3 * rates.coalescence parent + rates.recombination parent / 2) * time)
          * ancestral (some (.Dz parent parent parent)) := by
  have hβ : linkageRate rates child = linkageRate rates parent := by
    simp only [linkageRate, hcoal, hrec]
  have hreadout : ∀ source (moment : ℝ),
      withinDemeReadout rates child source ancestral moment
        = withinDemeReadout rates parent source ancestral moment := by
    intro source moment
    simp only [withinDemeReadout, withinDemeBlock, hcoal, hrec]
  have hDDc : migrationHistory rates hne 0 le_rfl ancestral time (some (.DD child child))
      = withinDemeReadout rates child parent ancestral time 0 :=
    noMigrationHistory_withinDemeCoordinate rates hmutation hne ancestral time
      (deme := child) (Or.inr rfl) 0
  have hDDp : migrationHistory rates hne 0 le_rfl ancestral time (some (.DD parent parent))
      = withinDemeReadout rates parent parent ancestral time 0 :=
    noMigrationHistory_withinDemeCoordinate rates hmutation hne ancestral time
      (deme := parent) (Or.inl rfl) 0
  have hDzc : migrationHistory rates hne 0 le_rfl ancestral time (some (.Dz child child child))
      = withinDemeReadout rates child parent ancestral time 1 :=
    noMigrationHistory_withinDemeCoordinate rates hmutation hne ancestral time
      (deme := child) (Or.inr rfl) 1
  have hDzp : migrationHistory rates hne 0 le_rfl ancestral time
        (some (.Dz parent parent parent))
      = withinDemeReadout rates parent parent ancestral time 1 :=
    noMigrationHistory_withinDemeCoordinate rates hmutation hne ancestral time
      (deme := parent) (Or.inl rfl) 1
  obtain ⟨hdiagonal₁, hdiagonal₂, hdiagonal₃, hdiagonal₄⟩ :=
    noMigrationHistory_Dz_diagonal rates hmutation hne ancestral time
  rw [linkageMigrationStencil, hDDc, hDDp, hDzc, hDzp, hdiagonal₁, hdiagonal₂, hdiagonal₃,
    hdiagonal₄, noMigrationHistory_DD_cross rates hmutation hne,
    noMigrationHistory_Dz_childFed rates hmutation hne,
    noMigrationHistory_Dz_parentFed rates hmutation hne, hreadout, crossLinkageDecayRate, hcoal,
    hrec, hβ]
  ring_nf

/-! ## The first-order factor -/

/-- **The first-order migration factor** `φ₁(T) = A_D⁰(T) - e^{-ρ̄T} A_π⁰(T)`: the linkage share
without migration minus the portability decay times the heterozygosity share without migration.

Empirical status: NOT AN EMPIRICAL CLAIM.  Two integrals along a corpus history. -/
def firstOrderMigrationFactor (rates : ManyDemeLDRates D) {parent child : Fin D}
    (hne : parent ≠ child) (ancestral : AffineLowOrderLDCoordinate D → ℝ) (duration : ℝ) : ℝ :=
  linkageMigrationShare rates hne 0 le_rfl ancestral duration
    - portabilityDecay ((rates.recombination parent + rates.recombination child) / 2) duration
      * heterozygosityMigrationShare rates hne 0 le_rfl ancestral duration

/-- **The portability ratio along the affine family of generators**, at every real rate `θ`.

Empirical status: NOT AN EMPIRICAL CLAIM.  A ratio of moment coordinates of a history. -/
def affineMigrationPortabilityRatio (rates : ManyDemeLDRates D) {parent child : Fin D}
    (hne : parent ≠ child) (ancestral : AffineLowOrderLDCoordinate D → ℝ) (duration θ : ℝ) : ℝ :=
  affineMigrationHistory rates hne ancestral θ duration (some (.DD parent child))
    / affineMigrationHistory rates hne ancestral θ duration (some (.pi2 parent parent child child))
    / ancestralSquaredCorrelation ancestral parent

/-- The linkage decay factor is the heterozygosity decay factor times the portability decay. -/
theorem exp_neg_crossLinkageDecayRate_mul (rates : ManyDemeLDRates D) (parent child : Fin D)
    (duration : ℝ) :
    Real.exp (-crossLinkageDecayRate rates parent child * duration)
      = Real.exp (-crossHeterozygosityDecayRate rates parent child * duration)
        * portabilityDecay ((rates.recombination parent + rates.recombination child) / 2)
          duration := by
  rw [portabilityDecay, ← Real.exp_add]
  congr 1
  unfold crossLinkageDecayRate crossHeterozygosityDecayRate
  ring

/-- **The portability ratio has derivative `φ₁` at `m = 0` along the affine family.**  The
quotient rule on the two Duhamel derivatives, with the drift factor `e^{-(c_S + c_T) T}` common to
both moments cancelled.

Assumes: no mutation, `parent ≠ child`, a nonzero ancestral `E[D²]` and a nonzero ancestral
heterozygosity product. -/
theorem hasDerivAt_affineMigrationPortabilityRatio (rates : ManyDemeLDRates D)
    (hmutation : ∀ deme, rates.mutation deme = 0) {parent child : Fin D} (hne : parent ≠ child)
    (ancestral : AffineLowOrderLDCoordinate D → ℝ)
    (hlinkage : ancestral (some (.DD parent parent)) ≠ 0)
    (hheterozygosity : ancestral (some (.pi2 parent parent parent parent)) ≠ 0) (duration : ℝ) :
    HasDerivAt (affineMigrationPortabilityRatio rates hne ancestral duration)
      (firstOrderMigrationFactor rates hne ancestral duration) 0 := by
  have hDD := (hasDerivAt_affineMigrationHistory rates hne ancestral duration
    (some (.DD parent child))).congr_deriv
    (duhamelDerivative_mulVec_DD rates hmutation hne ancestral duration)
  have hpi2 := (hasDerivAt_affineMigrationHistory rates hne ancestral duration
    (some (.pi2 parent parent child child))).congr_deriv
    (duhamelDerivative_mulVec_pi2 rates hmutation hne ancestral duration)
  have hvalueDD : affineMigrationHistory rates hne ancestral 0 duration (some (.DD parent child))
      = Real.exp (-crossLinkageDecayRate rates parent child * duration)
        * ancestral (some (.DD parent parent)) := by
    rw [affineMigrationHistory_zero, noMigrationHistory_DD_cross rates hmutation hne]
  have hvaluepi2 : affineMigrationHistory rates hne ancestral 0 duration
        (some (.pi2 parent parent child child))
      = Real.exp (-crossHeterozygosityDecayRate rates parent child * duration)
        * ancestral (some (.pi2 parent parent parent parent)) := by
    rw [affineMigrationHistory_zero, migrationHistory_pi2 rates hmutation hne le_rfl, zero_mul,
      add_zero]
  have hexp := (Real.exp_pos (-crossHeterozygosityDecayRate rates parent child * duration)).ne'
  have hdenominator : affineMigrationHistory rates hne ancestral 0 duration
      (some (.pi2 parent parent child child)) ≠ 0 := by
    rw [hvaluepi2]
    exact mul_ne_zero hexp hheterozygosity
  refine ((hDD.fun_div hpi2 hdenominator).div_const
    (ancestralSquaredCorrelation ancestral parent)).congr_deriv ?_
  rw [hvalueDD, hvaluepi2, firstOrderMigrationFactor, linkageMigrationShare,
    heterozygosityMigrationShare, ancestralSquaredCorrelation,
    exp_neg_crossLinkageDecayRate_mul]
  field_simp

/-- At a nonnegative rate the affine ratio is the corpus portability ratio with migration. -/
theorem splitPortabilityRatio_withSymmetricMigration_eq_affine (rates : ManyDemeLDRates D)
    {parent child : Fin D} (hne : parent ≠ child) {migration : ℝ} (hmigration : 0 ≤ migration)
    {duration : ℝ} (hduration : 0 ≤ duration) (ancestral : AffineLowOrderLDCoordinate D → ℝ) :
    splitPortabilityRatio (withSymmetricMigration rates hne migration hmigration) parent child
        hduration ancestral
      = affineMigrationPortabilityRatio rates hne ancestral duration migration := by
  rw [splitPortabilityRatio, crossSquaredCorrelation, splitHistoryState_withSymmetricMigration,
    migrationHistory_eq_affineMigrationHistory rates hne hmigration,
    affineMigrationPortabilityRatio]

/-- **The first-order migration factor of the corpus portability ratio.**  On `m ≥ 0` the ratio
`splitPortabilityRatio` with symmetric migration `m` has one-sided derivative
`firstOrderMigrationFactor` at `m = 0`: `ratio_m = e^{-ρ̄T} + m φ₁(T) + o(m)`.  The rate enters as
`max m 0`, so the function is defined at every real `m`.

Assumes: no mutation, `parent ≠ child`, a nonzero ancestral `E[D²]` and a nonzero ancestral
heterozygosity product. -/
theorem hasDerivWithinAt_splitPortabilityRatio_withSymmetricMigration (rates : ManyDemeLDRates D)
    (hmutation : ∀ deme, rates.mutation deme = 0) {parent child : Fin D} (hne : parent ≠ child)
    {duration : ℝ} (hduration : 0 ≤ duration) (ancestral : AffineLowOrderLDCoordinate D → ℝ)
    (hlinkage : ancestral (some (.DD parent parent)) ≠ 0)
    (hheterozygosity : ancestral (some (.pi2 parent parent parent parent)) ≠ 0) :
    HasDerivWithinAt
      (fun migration ↦ splitPortabilityRatio
        (withSymmetricMigration rates hne (max migration 0) (le_max_right migration 0)) parent
        child hduration ancestral)
      (firstOrderMigrationFactor rates hne ancestral duration) (Set.Ici 0) 0 := by
  refine (hasDerivAt_affineMigrationPortabilityRatio rates hmutation hne ancestral hlinkage
    hheterozygosity duration).hasDerivWithinAt.congr (fun migration hmigration ↦ ?_) ?_
  · have hnonnegative : 0 ≤ migration := hmigration
    rw [splitPortabilityRatio_withSymmetricMigration_eq_affine, max_eq_left hnonnegative]
  · rw [splitPortabilityRatio_withSymmetricMigration_eq_affine, max_self]

/-! ## Without recombination -/

/-- **The slow within-deme combination.**  Without migration or mutation, and with `ρ_i = 0`,
`2 DD(i, i) + Dz(i, i, i) + 2 pi2(i, i, i, i)` is multiplied by `e^{-c_i t}` along any trajectory.
It is the left eigenvector of the within-deme block at `-c_i`.

Assumes: no migration, no mutation, and `ρ_i = 0`. -/
theorem matrixExponential_mulVec_withinDeme_slow (rates : ManyDemeLDRates D)
    (hmigration : ∀ source target, rates.migration source target = 0)
    (hmutation : ∀ deme, rates.mutation deme = 0) {deme : Fin D}
    (hρ : rates.recombination deme = 0) (time : ℝ) (state : AffineLowOrderLDCoordinate D → ℝ) :
    2 * (matrixExponential (augmentedLowOrderLDGenerator rates) time).mulVec state
          (some (.DD deme deme))
        + (matrixExponential (augmentedLowOrderLDGenerator rates) time).mulVec state
          (some (.Dz deme deme deme))
        + 2 * (matrixExponential (augmentedLowOrderLDGenerator rates) time).mulVec state
          (some (.pi2 deme deme deme deme))
      = Real.exp (-rates.coalescence deme * time)
        * (2 * state (some (.DD deme deme)) + state (some (.Dz deme deme deme))
          + 2 * state (some (.pi2 deme deme deme deme))) := by
  obtain ⟨hDD, hDz, hpi2⟩ :=
    augmentedLowOrderLDGenerator_withinDeme_rows rates hmigration hmutation deme
  have h := sum_mul_matrixExponential_mulVec_of_left_eigen (augmentedLowOrderLDGenerator rates)
    (fun row ↦ 2 * (if some (LowOrderLDCoordinate.DD deme deme) = row then 1 else 0)
      + 1 * (if some (LowOrderLDCoordinate.Dz deme deme deme) = row then 1 else 0)
      + 2 * (if some (LowOrderLDCoordinate.pi2 deme deme deme deme) = row then 1 else 0))
    (-rates.coalescence deme) time state (fun column ↦ by
      simp only [add_mul, Finset.sum_add_distrib, sum_mul_pointMass_left, hDD, hDz, hpi2, hρ]
      ring)
  simp only [add_mul, Finset.sum_add_distrib, sum_mul_pointMass_left, one_mul,
    sum_unitPointMass_left] at h
  rw [mul_comm time] at h
  linear_combination h

/-- **The fast within-deme combination.**  Without migration or mutation, and with `ρ_i = 0`,
`DD(i, i) - pi2(i, i, i, i)` is multiplied by `e^{-3 c_i t}` along any trajectory.  It is the left
eigenvector of the within-deme block at `-3 c_i`.

Assumes: no migration, no mutation, and `ρ_i = 0`. -/
theorem matrixExponential_mulVec_withinDeme_fast (rates : ManyDemeLDRates D)
    (hmigration : ∀ source target, rates.migration source target = 0)
    (hmutation : ∀ deme, rates.mutation deme = 0) {deme : Fin D}
    (hρ : rates.recombination deme = 0) (time : ℝ) (state : AffineLowOrderLDCoordinate D → ℝ) :
    (matrixExponential (augmentedLowOrderLDGenerator rates) time).mulVec state
          (some (.DD deme deme))
        - (matrixExponential (augmentedLowOrderLDGenerator rates) time).mulVec state
          (some (.pi2 deme deme deme deme))
      = Real.exp (-(3 * rates.coalescence deme) * time)
        * (state (some (.DD deme deme)) - state (some (.pi2 deme deme deme deme))) := by
  obtain ⟨hDD, -, hpi2⟩ :=
    augmentedLowOrderLDGenerator_withinDeme_rows rates hmigration hmutation deme
  have h := sum_mul_matrixExponential_mulVec_of_left_eigen (augmentedLowOrderLDGenerator rates)
    (fun row ↦ 1 * (if some (LowOrderLDCoordinate.DD deme deme) = row then 1 else 0)
      + -1 * (if some (LowOrderLDCoordinate.pi2 deme deme deme deme) = row then 1 else 0))
    (-(3 * rates.coalescence deme)) time state (fun column ↦ by
      simp only [add_mul, Finset.sum_add_distrib, sum_mul_pointMass_left, hDD, hpi2, hρ]
      ring)
  simp only [add_mul, Finset.sum_add_distrib, sum_mul_pointMass_left, one_mul,
    sum_unitPointMass_left] at h
  rw [mul_comm time] at h
  linear_combination h

/-- **The slow combination of the split history without migration.**

Assumes: no mutation, `parent ≠ child`, `deme` is the parent or the child, and `ρ = 0` in it. -/
theorem noMigrationHistory_withinDeme_slow (rates : ManyDemeLDRates D)
    (hmutation : ∀ deme, rates.mutation deme = 0) {parent child : Fin D} (hne : parent ≠ child)
    (ancestral : AffineLowOrderLDCoordinate D → ℝ) (time : ℝ) {deme : Fin D}
    (hdeme : deme = parent ∨ deme = child) (hρ : rates.recombination deme = 0) :
    2 * migrationHistory rates hne 0 le_rfl ancestral time (some (.DD deme deme))
        + migrationHistory rates hne 0 le_rfl ancestral time (some (.Dz deme deme deme))
        + 2 * migrationHistory rates hne 0 le_rfl ancestral time (some (.pi2 deme deme deme deme))
      = Real.exp (-rates.coalescence deme * time)
        * (2 * ancestral (some (.DD parent parent)) + ancestral (some (.Dz parent parent parent))
          + 2 * ancestral (some (.pi2 parent parent parent parent))) := by
  have h := matrixExponential_mulVec_withinDeme_slow _
    (withSymmetricMigration_zero_migration rates hne) hmutation (deme := deme) hρ time
    ((lowOrderLDSplitTransform parent child).mulVec ancestral)
  have hDD : (lowOrderLDSplitTransform parent child).mulVec ancestral (some (.DD deme deme))
      = ancestral (some (.DD parent parent)) :=
    splitTransform_withinDemeCoordinate hne ancestral hdeme 0
  have hDz : (lowOrderLDSplitTransform parent child).mulVec ancestral (some (.Dz deme deme deme))
      = ancestral (some (.Dz parent parent parent)) :=
    splitTransform_withinDemeCoordinate hne ancestral hdeme 1
  have hpi2 : (lowOrderLDSplitTransform parent child).mulVec ancestral
        (some (.pi2 deme deme deme deme))
      = ancestral (some (.pi2 parent parent parent parent)) :=
    splitTransform_withinDemeCoordinate hne ancestral hdeme 2
  rw [hDD, hDz, hpi2] at h
  exact h

/-- **The fast combination of the split history without migration.**

Assumes: no mutation, `parent ≠ child`, `deme` is the parent or the child, and `ρ = 0` in it. -/
theorem noMigrationHistory_withinDeme_fast (rates : ManyDemeLDRates D)
    (hmutation : ∀ deme, rates.mutation deme = 0) {parent child : Fin D} (hne : parent ≠ child)
    (ancestral : AffineLowOrderLDCoordinate D → ℝ) (time : ℝ) {deme : Fin D}
    (hdeme : deme = parent ∨ deme = child) (hρ : rates.recombination deme = 0) :
    migrationHistory rates hne 0 le_rfl ancestral time (some (.DD deme deme))
        - migrationHistory rates hne 0 le_rfl ancestral time (some (.pi2 deme deme deme deme))
      = Real.exp (-(3 * rates.coalescence deme) * time)
        * (ancestral (some (.DD parent parent))
          - ancestral (some (.pi2 parent parent parent parent))) := by
  have h := matrixExponential_mulVec_withinDeme_fast _
    (withSymmetricMigration_zero_migration rates hne) hmutation (deme := deme) hρ time
    ((lowOrderLDSplitTransform parent child).mulVec ancestral)
  have hDD : (lowOrderLDSplitTransform parent child).mulVec ancestral (some (.DD deme deme))
      = ancestral (some (.DD parent parent)) :=
    splitTransform_withinDemeCoordinate hne ancestral hdeme 0
  have hpi2 : (lowOrderLDSplitTransform parent child).mulVec ancestral
        (some (.pi2 deme deme deme deme))
      = ancestral (some (.pi2 parent parent parent parent)) :=
    splitTransform_withinDemeCoordinate hne ancestral hdeme 2
  rw [hDD, hpi2] at h
  exact h

/-- **The linkage migration stencil without recombination, in closed form.**  At equal drift `c`
and `ρ = 0` in both demes, on the history without migration,
`μ_D(t) = e^{-ct} (3 DD₀ + Dz₀ + π₀) + e^{-3ct} (DD₀ - π₀ - Dz₀) - 4 e^{-2ct} DD₀`.

Assumes: no mutation, `parent ≠ child`, equal drift and recombination rates, and `ρ = 0`. -/
theorem linkageMigrationStencil_noMigration_zeroRecombination (rates : ManyDemeLDRates D)
    (hmutation : ∀ deme, rates.mutation deme = 0) {parent child : Fin D} (hne : parent ≠ child)
    (hcoal : rates.coalescence child = rates.coalescence parent)
    (hrec : rates.recombination child = rates.recombination parent)
    (hρ : rates.recombination parent = 0) (ancestral : AffineLowOrderLDCoordinate D → ℝ)
    (time : ℝ) :
    linkageMigrationStencil parent child (migrationHistory rates hne 0 le_rfl ancestral time)
      = Real.exp (-rates.coalescence parent * time)
          * (3 * ancestral (some (.DD parent parent)) + ancestral (some (.Dz parent parent parent))
            + ancestral (some (.pi2 parent parent parent parent)))
        + Real.exp (-(3 * rates.coalescence parent) * time)
          * (ancestral (some (.DD parent parent))
            - ancestral (some (.pi2 parent parent parent parent))
            - ancestral (some (.Dz parent parent parent)))
        - 4 * Real.exp (-(2 * rates.coalescence parent) * time)
          * ancestral (some (.DD parent parent)) := by
  have hc := (rates.coalescence_pos parent).ne'
  have hρchild : rates.recombination child = 0 := hrec.trans hρ
  have hβchild : linkageRate rates child = rates.coalescence parent := by
    rw [linkageRate, hcoal, hρchild, zero_div, add_zero]
  have hβparent : linkageRate rates parent = rates.coalescence parent := by
    rw [linkageRate, hρ, zero_div, add_zero]
  have hα : 4 * rates.coalescence parent / rates.coalescence parent = 4 := by
    rw [mul_div_assoc, div_self hc, mul_one]
  have hslowp := noMigrationHistory_withinDeme_slow rates hmutation hne ancestral time
    (deme := parent) (Or.inl rfl) hρ
  have hslowc := noMigrationHistory_withinDeme_slow rates hmutation hne ancestral time
    (deme := child) (Or.inr rfl) hρchild
  have hfastp := noMigrationHistory_withinDeme_fast rates hmutation hne ancestral time
    (deme := parent) (Or.inl rfl) hρ
  have hfastc := noMigrationHistory_withinDeme_fast rates hmutation hne ancestral time
    (deme := child) (Or.inr rfl) hρchild
  have hcross := noMigrationHistory_DD_cross rates hmutation hne ancestral time
  have hfedc := noMigrationHistory_Dz_childFed rates hmutation hne ancestral time
  have hfedp := noMigrationHistory_Dz_parentFed rates hmutation hne ancestral time
  obtain ⟨hdiagonal₁, hdiagonal₂, hdiagonal₃, hdiagonal₄⟩ :=
    noMigrationHistory_Dz_diagonal rates hmutation hne ancestral time
  rw [hcoal] at hslowc hfastc
  rw [crossLinkageDecayRate, hcoal, hrec, hρ] at hcross
  rw [hβchild, hβparent, hα, hcoal, hrec, hρ] at hfedc
  rw [hβparent, hcoal, hβchild, hα, hrec, hρ] at hfedp
  rw [hcoal, hρchild] at hdiagonal₁ hdiagonal₂
  rw [hρ] at hdiagonal₃ hdiagonal₄
  rw [linkageMigrationStencil]
  linear_combination (norm := ring_nf) hslowp / 4 + hslowc / 4 + hfastp / 2 + hfastc / 2
    - 2 * hcross + hfedc / 4 + hfedp / 4 - hdiagonal₁ / 4 - hdiagonal₂ / 4 - hdiagonal₃ / 4
    - hdiagonal₄ / 4

/-! ## The shares and the factor in closed form -/

/-- **An elementary exponential integral.**
`∫_0^T (p e^{a s} + q e^{-b s} + r) ds = p (e^{aT} - 1)/a + q (1 - e^{-bT})/b + r T`.

Assumes: `a ≠ 0` and `b ≠ 0`. -/
theorem integral_exp_add_exp_neg_add_const {a b p q r : ℝ} (ha : a ≠ 0) (hb : b ≠ 0)
    (duration : ℝ) :
    ∫ time in (0 : ℝ)..duration, (p * Real.exp (a * time) + q * Real.exp (-b * time) + r)
      = p * (Real.exp (a * duration) - 1) / a + q * (1 - Real.exp (-b * duration)) / b
        + r * duration := by
  have hderiv : ∀ time ∈ Set.uIcc (0 : ℝ) duration,
      HasDerivAt
        (fun time ↦ p * Real.exp (a * time) / a - q * Real.exp (-b * time) / b + r * time)
        (p * Real.exp (a * time) + q * Real.exp (-b * time) + r) time := by
    intro time _
    have hslow := ((hasDerivAt_id' (x := time)).const_mul a).exp
    have hfast := ((hasDerivAt_id' (x := time)).const_mul (-b)).exp
    refine ((((hslow.const_mul p).div_const a).sub ((hfast.const_mul q).div_const b)).add
      ((hasDerivAt_id' (x := time)).const_mul r)).congr_deriv ?_
    field_simp
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    ((by fun_prop : Continuous fun time : ℝ ↦
      p * Real.exp (a * time) + q * Real.exp (-b * time) + r).intervalIntegrable 0 duration)]
  simp only [mul_zero, Real.exp_zero]
  field_simp
  ring

/-- **The heterozygosity share without migration, at equal rates, in closed form.**  With
`β = c + ρ/2` and `κ = c/(4c + ρ)`,
`A_π⁰(T) = (4 π₀ ((e^{cT} - 1)/c - T) + 4 κ Dz₀ ((e^{cT} - 1)/c - (1 - e^{-βT})/β)) / π₀`.

Assumes: no mutation, `parent ≠ child`, and equal drift and recombination rates. -/
theorem heterozygosityMigrationShare_noMigration (rates : ManyDemeLDRates D)
    (hmutation : ∀ deme, rates.mutation deme = 0) {parent child : Fin D} (hne : parent ≠ child)
    (hcoal : rates.coalescence child = rates.coalescence parent)
    (hrec : rates.recombination child = rates.recombination parent)
    (ancestral : AffineLowOrderLDCoordinate D → ℝ) (duration : ℝ) :
    heterozygosityMigrationShare rates hne 0 le_rfl ancestral duration
      = (4 * ancestral (some (.pi2 parent parent parent parent))
            * ((Real.exp (rates.coalescence parent * duration) - 1) / rates.coalescence parent
              - duration)
          + 4 * fedWeight rates parent * ancestral (some (.Dz parent parent parent))
            * ((Real.exp (rates.coalescence parent * duration) - 1) / rates.coalescence parent
              - (1 - Real.exp (-linkageRate rates parent * duration)) / linkageRate rates parent))
        / ancestral (some (.pi2 parent parent parent parent)) := by
  have hintegrand : ∀ time : ℝ,
      Real.exp (crossHeterozygosityDecayRate rates parent child * time)
          * heterozygosityMigrationStencil parent child
            (migrationHistory rates hne 0 le_rfl ancestral time)
        = (4 * ancestral (some (.pi2 parent parent parent parent))
            + 4 * fedWeight rates parent * ancestral (some (.Dz parent parent parent)))
            * Real.exp (rates.coalescence parent * time)
          + -(4 * fedWeight rates parent * ancestral (some (.Dz parent parent parent)))
            * Real.exp (-linkageRate rates parent * time)
          + -(4 * ancestral (some (.pi2 parent parent parent parent))) := by
    intro time
    have hfirst : Real.exp (crossHeterozygosityDecayRate rates parent child * time)
          * Real.exp (-rates.coalescence parent * time)
        = Real.exp (rates.coalescence parent * time) := by
      rw [← Real.exp_add, crossHeterozygosityDecayRate, hcoal]
      congr 1
      ring
    have hsecond : Real.exp (crossHeterozygosityDecayRate rates parent child * time)
        * Real.exp (-(2 * rates.coalescence parent) * time) = 1 := by
      rw [← Real.exp_add, ← Real.exp_zero, crossHeterozygosityDecayRate, hcoal]
      congr 1
      ring
    have hthird : Real.exp (crossHeterozygosityDecayRate rates parent child * time)
          * Real.exp (-(3 * rates.coalescence parent + rates.recombination parent / 2) * time)
        = Real.exp (-linkageRate rates parent * time) := by
      rw [← Real.exp_add, crossHeterozygosityDecayRate, hcoal, linkageRate]
      congr 1
      ring
    rw [heterozygosityMigrationStencil_noMigration rates hmutation hne hcoal hrec]
    linear_combination (4 * ancestral (some (.pi2 parent parent parent parent))
        + 4 * fedWeight rates parent * ancestral (some (.Dz parent parent parent))) * hfirst
      - 4 * ancestral (some (.pi2 parent parent parent parent)) * hsecond
      - 4 * fedWeight rates parent * ancestral (some (.Dz parent parent parent)) * hthird
  rw [heterozygosityMigrationShare, intervalIntegral.integral_congr fun time _ ↦ hintegrand time,
    integral_exp_add_exp_neg_add_const (rates.coalescence_pos parent).ne'
      (linkageRate_pos rates parent).ne']
  ring

/-- **The linkage share without migration and without recombination, in closed form.**
`A_D⁰(T) = ((3 DD₀ + Dz₀ + π₀) (e^{cT} - 1)/c + (DD₀ - π₀ - Dz₀) (1 - e^{-cT})/c - 4 DD₀ T) / DD₀`.

Assumes: no mutation, `parent ≠ child`, equal drift and recombination rates, and `ρ = 0`. -/
theorem linkageMigrationShare_noMigration_zeroRecombination (rates : ManyDemeLDRates D)
    (hmutation : ∀ deme, rates.mutation deme = 0) {parent child : Fin D} (hne : parent ≠ child)
    (hcoal : rates.coalescence child = rates.coalescence parent)
    (hrec : rates.recombination child = rates.recombination parent)
    (hρ : rates.recombination parent = 0) (ancestral : AffineLowOrderLDCoordinate D → ℝ)
    (duration : ℝ) :
    linkageMigrationShare rates hne 0 le_rfl ancestral duration
      = ((3 * ancestral (some (.DD parent parent)) + ancestral (some (.Dz parent parent parent))
              + ancestral (some (.pi2 parent parent parent parent)))
            * (Real.exp (rates.coalescence parent * duration) - 1) / rates.coalescence parent
          + (ancestral (some (.DD parent parent))
              - ancestral (some (.pi2 parent parent parent parent))
              - ancestral (some (.Dz parent parent parent)))
            * (1 - Real.exp (-rates.coalescence parent * duration)) / rates.coalescence parent
          - 4 * ancestral (some (.DD parent parent)) * duration)
        / ancestral (some (.DD parent parent)) := by
  have hc := (rates.coalescence_pos parent).ne'
  have hintegrand : ∀ time : ℝ,
      Real.exp (crossLinkageDecayRate rates parent child * time)
          * linkageMigrationStencil parent child
            (migrationHistory rates hne 0 le_rfl ancestral time)
        = (3 * ancestral (some (.DD parent parent)) + ancestral (some (.Dz parent parent parent))
              + ancestral (some (.pi2 parent parent parent parent)))
            * Real.exp (rates.coalescence parent * time)
          + (ancestral (some (.DD parent parent))
              - ancestral (some (.pi2 parent parent parent parent))
              - ancestral (some (.Dz parent parent parent)))
            * Real.exp (-rates.coalescence parent * time)
          + -(4 * ancestral (some (.DD parent parent))) := by
    intro time
    have hfirst : Real.exp (crossLinkageDecayRate rates parent child * time)
          * Real.exp (-rates.coalescence parent * time)
        = Real.exp (rates.coalescence parent * time) := by
      rw [← Real.exp_add, crossLinkageDecayRate, hcoal, hrec, hρ]
      congr 1
      ring
    have hsecond : Real.exp (crossLinkageDecayRate rates parent child * time)
          * Real.exp (-(3 * rates.coalescence parent) * time)
        = Real.exp (-rates.coalescence parent * time) := by
      rw [← Real.exp_add, crossLinkageDecayRate, hcoal, hrec, hρ]
      congr 1
      ring
    have hthird : Real.exp (crossLinkageDecayRate rates parent child * time)
        * Real.exp (-(2 * rates.coalescence parent) * time) = 1 := by
      rw [← Real.exp_add, ← Real.exp_zero, crossLinkageDecayRate, hcoal, hrec, hρ]
      congr 1
      ring
    rw [linkageMigrationStencil_noMigration_zeroRecombination rates hmutation hne hcoal hrec hρ]
    linear_combination (3 * ancestral (some (.DD parent parent))
          + ancestral (some (.Dz parent parent parent))
          + ancestral (some (.pi2 parent parent parent parent))) * hfirst
      + (ancestral (some (.DD parent parent))
          - ancestral (some (.pi2 parent parent parent parent))
          - ancestral (some (.Dz parent parent parent))) * hsecond
      - 4 * ancestral (some (.DD parent parent)) * hthird
  rw [linkageMigrationShare, hrec, hρ, add_zero, zero_div, portabilityDecay_zero_rate,
    intervalIntegral.integral_congr fun time _ ↦ hintegrand time,
    integral_exp_add_exp_neg_add_const hc hc]
  ring

/-- **The first-order migration factor without recombination.**  At equal drift `c` and `ρ = 0`,
`φ₁(T) = 2 (cosh cT - 1) (π₀ - DD₀) (π₀ + Dz₀) / (c DD₀ π₀)`.  The terms linear in `T` of the two
shares cancel.

Assumes: no mutation, `parent ≠ child`, equal drift and recombination rates, `ρ = 0`, and nonzero
ancestral `DD` and `pi2`. -/
theorem firstOrderMigrationFactor_zeroRecombination (rates : ManyDemeLDRates D)
    (hmutation : ∀ deme, rates.mutation deme = 0) {parent child : Fin D} (hne : parent ≠ child)
    (hcoal : rates.coalescence child = rates.coalescence parent)
    (hrec : rates.recombination child = rates.recombination parent)
    (hρ : rates.recombination parent = 0) (ancestral : AffineLowOrderLDCoordinate D → ℝ)
    (hlinkage : ancestral (some (.DD parent parent)) ≠ 0)
    (hheterozygosity : ancestral (some (.pi2 parent parent parent parent)) ≠ 0) (duration : ℝ) :
    firstOrderMigrationFactor rates hne ancestral duration
      = 2 * (Real.cosh (rates.coalescence parent * duration) - 1)
          * (ancestral (some (.pi2 parent parent parent parent))
            - ancestral (some (.DD parent parent)))
          * (ancestral (some (.pi2 parent parent parent parent))
            + ancestral (some (.Dz parent parent parent)))
        / (rates.coalescence parent * ancestral (some (.DD parent parent))
          * ancestral (some (.pi2 parent parent parent parent))) := by
  have hc := (rates.coalescence_pos parent).ne'
  have hκ : fedWeight rates parent = 1 / 4 := by
    rw [fedWeight, hρ, add_zero]
    field_simp
  have hβ : linkageRate rates parent = rates.coalescence parent := by
    rw [linkageRate, hρ, zero_div, add_zero]
  have hneg : Real.exp (-(rates.coalescence parent * duration))
      = Real.exp (-rates.coalescence parent * duration) := by
    rw [neg_mul]
  rw [firstOrderMigrationFactor,
    linkageMigrationShare_noMigration_zeroRecombination rates hmutation hne hcoal hrec hρ,
    heterozygosityMigrationShare_noMigration rates hmutation hne hcoal hrec, hκ, hβ, hrec, hρ,
    add_zero, zero_div, portabilityDecay_zero_rate, Real.cosh_eq, hneg]
  field_simp
  ring

/-- **To first order, migration raises portability without recombination** when `DD₀ ≤ π₀` and
`π₀ + Dz₀ ≥ 0`: the factor `φ₁(T)` is nonnegative at every split time.

Assumes: no mutation, `parent ≠ child`, equal drift and recombination rates, `ρ = 0`, positive
ancestral `DD` and `pi2`, `DD₀ ≤ π₀`, and `0 ≤ π₀ + Dz₀`. -/
theorem firstOrderMigrationFactor_nonneg_zeroRecombination (rates : ManyDemeLDRates D)
    (hmutation : ∀ deme, rates.mutation deme = 0) {parent child : Fin D} (hne : parent ≠ child)
    (hcoal : rates.coalescence child = rates.coalescence parent)
    (hrec : rates.recombination child = rates.recombination parent)
    (hρ : rates.recombination parent = 0) (ancestral : AffineLowOrderLDCoordinate D → ℝ)
    (hlinkage : 0 < ancestral (some (.DD parent parent)))
    (hheterozygosity : 0 < ancestral (some (.pi2 parent parent parent parent)))
    (horder : ancestral (some (.DD parent parent))
      ≤ ancestral (some (.pi2 parent parent parent parent)))
    (hcontrast : 0 ≤ ancestral (some (.pi2 parent parent parent parent))
      + ancestral (some (.Dz parent parent parent))) (duration : ℝ) :
    0 ≤ firstOrderMigrationFactor rates hne ancestral duration := by
  rw [firstOrderMigrationFactor_zeroRecombination rates hmutation hne hcoal hrec hρ ancestral
    hlinkage.ne' hheterozygosity.ne']
  have hcosh := Real.one_le_cosh (rates.coalescence parent * duration)
  exact div_nonneg
    (mul_nonneg (mul_nonneg (mul_nonneg zero_le_two (sub_nonneg.mpr hcosh))
      (sub_nonneg.mpr horder)) hcontrast)
    (mul_pos (mul_pos (rates.coalescence_pos parent) hlinkage) hheterozygosity).le

end

end Descent.Portability.MigrationPortabilityFirstOrderFactor
