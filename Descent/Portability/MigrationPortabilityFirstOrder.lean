/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.MigrationPortabilityFactor

assert_below Descent.Decision Descent.Program

/-!
# The heterozygosity migration stencil on the no-migration history

`MigrationPortabilityFactor` writes the two-locus portability ratio with symmetric migration `m`
as `(e^{-ρ̄T} + m A_D) / (1 + m A_π)`.  The shares `A_D` and `A_π` integrate the migration
stencils `μ_D` and `μ_π` along the with-migration history.  To first order in `m` the stencils
are read on the no-migration history, and this module reads the heterozygosity stencil there.

## Main results

- `matrixExponential_mulVec_apply_of_diagonal_row`, `matrixExponential_mulVec_apply_of_fed_row`:
  a coordinate with a diagonal generator row decays exponentially, and a coordinate fed by one
  such coordinate is a difference of two exponentials.
- `augmentedLowOrderLDGenerator_Dz_mixed_row`, `augmentedLowOrderLDGenerator_Dz_leading_row`:
  without migration or mutation the coordinates `Dz(i, j, i)` and `Dz(i, i, j)` decay at
  `3 c_i + ρ_i/2`.
- `augmentedLowOrderLDGenerator_pi2_fed_row` and three companions: the one-index heterozygosity
  coordinates `pi2(i, j, i, i)`, `pi2(j, i, i, i)`, `pi2(i, i, i, j)` and `pi2(i, i, j, i)` read
  `c_i/2` times one of those `Dz` coordinates minus `c_i` times themselves.
- `heterozygosityMigrationStencil_noMigration`: at equal drift `c` and recombination `ρ` in the
  two demes, the stencil on the no-migration history is
  `4 π₀ (e^{-ct} - e^{-2ct}) + 4 κ Dz₀ (e^{-ct} - e^{-(3c + ρ/2) t})`, with `κ = c/(4c + ρ)`
  (`fedWeight`), `π₀ = pi2(S, S, S, S)(0)` and `Dz₀ = Dz(S, S, S)(0)`.
- `heterozygosityMigrationStencil_noMigration_nonneg`: at nonnegative times the stencil is
  nonnegative when `π₀` and `Dz₀` are, so to first order migration raises the heterozygosity
  denominator of the portability ratio.

## Scope

Two demes, no mutation, and equal drift and recombination rates in the stencil theorems.  The
linkage stencil, the integral of the heterozygosity stencil, the first-order factor and its
derivative in `m` are not in this module.

## Empirical status

None.  The bodies are algebra on corpus moment coordinates.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.MigrationPortabilityFirstOrder

open Descent.Coalescent Descent.Portability.TwoLocusPortabilityDecay
  Descent.Portability.MigrationPortabilityFactor

noncomputable section

variable {D : ℕ}

/-! ## Readouts of diagonal and fed rows -/

/-- **A coordinate with a diagonal generator row decays exponentially.**

Assumes: the row of `point` is `-decay` times its point mass. -/
theorem matrixExponential_mulVec_apply_of_diagonal_row {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (time : ℝ) (state : ι → ℝ) {point : ι} {decay : ℝ}
    (hrow : ∀ column, A point column = -decay * (if point = column then 1 else 0)) :
    (matrixExponential A time).mulVec state point = Real.exp (-decay * time) * state point := by
  have h := sum_mul_matrixExponential_mulVec_of_left_eigen A
    (fun row ↦ 1 * (if point = row then 1 else 0)) (-decay) time state
    (fun column ↦ by simp only [sum_mul_pointMass_left, hrow]; ring)
  simp only [sum_mul_pointMass_left, one_mul] at h
  rw [h, mul_comm time]

/-- **A coordinate fed by one diagonal coordinate is a difference of two exponentials.**  If the
row of `mixed` is `-decay` times its point mass, and the row of `point` is `source` times the
point mass of `mixed` minus `rate` times its own, then
`x_point(t) = e^{-rate t} (x_point(0) + α x_mixed(0)) - α e^{-decay t} x_mixed(0)`.

Assumes: the two rows, and `α (decay - rate) = source`. -/
theorem matrixExponential_mulVec_apply_of_fed_row {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (time : ℝ) (state : ι → ℝ) {point mixed : ι} {rate decay source α : ℝ}
    (hα : α * (decay - rate) = source)
    (hmixed : ∀ column, A mixed column = -decay * (if mixed = column then 1 else 0))
    (hpoint : ∀ column, A point column
      = source * (if mixed = column then 1 else 0) - rate * (if point = column then 1 else 0)) :
    (matrixExponential A time).mulVec state point
      = Real.exp (-rate * time) * (state point + α * state mixed)
        - α * Real.exp (-decay * time) * state mixed := by
  have hcombination := sum_mul_matrixExponential_mulVec_of_left_eigen A
    (fun row ↦ 1 * (if point = row then 1 else 0) + α * (if mixed = row then 1 else 0))
    (-rate) time state (fun column ↦ by
      simp only [add_mul, Finset.sum_add_distrib, sum_mul_pointMass_left, hpoint, hmixed]
      linear_combination (-(if mixed = column then (1 : ℝ) else 0)) * hα)
  simp only [add_mul, Finset.sum_add_distrib, sum_mul_pointMass_left, one_mul] at hcombination
  have hdiagonal := matrixExponential_mulVec_apply_of_diagonal_row A time state hmixed
  rw [mul_comm time] at hcombination
  linear_combination hcombination - α * hdiagonal

/-! ## Rows of the no-migration history -/

/-- Evaluates one generator entry, reading basis vectors as coordinate point masses. -/
macro "migration_row_entry" : tactic => `(tactic|
  simp only [augmentedLowOrderLDGenerator, lowOrderLDHomogeneousGenerator, lowOrderLDDrift,
    lowOrderLDMigration, lowOrderLDRecombination, lowOrderLDMutationCoupling,
    lowOrderLDRecurrentMutationDamping, lowOrderLDBasis_eq_coordinateIndicator,
    ite_some_eq_coordinateIndicator])

/-- **The mixed `Dz(i, j, i)` row** is diagonal at `3 c_i + ρ_i/2`.

Assumes: no migration, no mutation, and `first ≠ second`. -/
theorem augmentedLowOrderLDGenerator_Dz_mixed_row (rates : ManyDemeLDRates D)
    (hmigration : ∀ source target, rates.migration source target = 0)
    (hmutation : ∀ deme, rates.mutation deme = 0) {first second : Fin D} (hne : first ≠ second)
    (column : AffineLowOrderLDCoordinate D) :
    augmentedLowOrderLDGenerator rates (some (.Dz first second first)) column
      = -(3 * rates.coalescence first + rates.recombination first / 2)
        * (if some (.Dz first second first) = column then 1 else 0) := by
  cases column with
  | none => simp [augmentedLowOrderLDGenerator, lowOrderLDMutationForcing]
  | some column =>
    migration_row_entry
    simp [hmigration, hmutation, hne, Ne.symm hne] <;> ring

/-- **The leading `Dz(i, i, j)` row** is diagonal at `3 c_i + ρ_i/2`.

Assumes: no migration, no mutation, and `first ≠ second`. -/
theorem augmentedLowOrderLDGenerator_Dz_leading_row (rates : ManyDemeLDRates D)
    (hmigration : ∀ source target, rates.migration source target = 0)
    (hmutation : ∀ deme, rates.mutation deme = 0) {first second : Fin D} (hne : first ≠ second)
    (column : AffineLowOrderLDCoordinate D) :
    augmentedLowOrderLDGenerator rates (some (.Dz first first second)) column
      = -(3 * rates.coalescence first + rates.recombination first / 2)
        * (if some (.Dz first first second) = column then 1 else 0) := by
  cases column with
  | none => simp [augmentedLowOrderLDGenerator, lowOrderLDMutationForcing]
  | some column =>
    migration_row_entry
    simp [hmigration, hmutation, hne, Ne.symm hne] <;> ring

/-- **The one-index row of `pi2(i, j, i, i)`** is fed by `Dz(i, j, i)`.

Assumes: no migration, no mutation, and `first ≠ second`. -/
theorem augmentedLowOrderLDGenerator_pi2_fed_row (rates : ManyDemeLDRates D)
    (hmigration : ∀ source target, rates.migration source target = 0)
    (hmutation : ∀ deme, rates.mutation deme = 0) {first second : Fin D} (hne : first ≠ second)
    (column : AffineLowOrderLDCoordinate D) :
    augmentedLowOrderLDGenerator rates (some (.pi2 first second first first)) column
      = rates.coalescence first / 2 * (if some (.Dz first second first) = column then 1 else 0)
        - rates.coalescence first
          * (if some (.pi2 first second first first) = column then 1 else 0) := by
  cases column with
  | none => simp [augmentedLowOrderLDGenerator, lowOrderLDMutationForcing]
  | some column =>
    migration_row_entry
    simp [hmigration, hmutation, hne, Ne.symm hne] <;> ring

/-- **The one-index row of `pi2(j, i, i, i)`** is fed by `Dz(i, j, i)`.

Assumes: no migration, no mutation, and `first ≠ second`. -/
theorem augmentedLowOrderLDGenerator_pi2_fed_row_swap (rates : ManyDemeLDRates D)
    (hmigration : ∀ source target, rates.migration source target = 0)
    (hmutation : ∀ deme, rates.mutation deme = 0) {first second : Fin D} (hne : first ≠ second)
    (column : AffineLowOrderLDCoordinate D) :
    augmentedLowOrderLDGenerator rates (some (.pi2 second first first first)) column
      = rates.coalescence first / 2 * (if some (.Dz first second first) = column then 1 else 0)
        - rates.coalescence first
          * (if some (.pi2 second first first first) = column then 1 else 0) := by
  cases column with
  | none => simp [augmentedLowOrderLDGenerator, lowOrderLDMutationForcing]
  | some column =>
    migration_row_entry
    simp [hmigration, hmutation, hne, Ne.symm hne] <;> ring

/-- **The one-index row of `pi2(i, i, i, j)`** is fed by `Dz(i, i, j)`.

Assumes: no migration, no mutation, and `first ≠ second`. -/
theorem augmentedLowOrderLDGenerator_pi2_leading_row (rates : ManyDemeLDRates D)
    (hmigration : ∀ source target, rates.migration source target = 0)
    (hmutation : ∀ deme, rates.mutation deme = 0) {first second : Fin D} (hne : first ≠ second)
    (column : AffineLowOrderLDCoordinate D) :
    augmentedLowOrderLDGenerator rates (some (.pi2 first first first second)) column
      = rates.coalescence first / 2 * (if some (.Dz first first second) = column then 1 else 0)
        - rates.coalescence first
          * (if some (.pi2 first first first second) = column then 1 else 0) := by
  cases column with
  | none => simp [augmentedLowOrderLDGenerator, lowOrderLDMutationForcing]
  | some column =>
    migration_row_entry
    simp [hmigration, hmutation, hne, Ne.symm hne] <;> ring

/-- **The one-index row of `pi2(i, i, j, i)`** is fed by `Dz(i, i, j)`.

Assumes: no migration, no mutation, and `first ≠ second`. -/
theorem augmentedLowOrderLDGenerator_pi2_leading_row_swap (rates : ManyDemeLDRates D)
    (hmigration : ∀ source target, rates.migration source target = 0)
    (hmutation : ∀ deme, rates.mutation deme = 0) {first second : Fin D} (hne : first ≠ second)
    (column : AffineLowOrderLDCoordinate D) :
    augmentedLowOrderLDGenerator rates (some (.pi2 first first second first)) column
      = rates.coalescence first / 2 * (if some (.Dz first first second) = column then 1 else 0)
        - rates.coalescence first
          * (if some (.pi2 first first second first) = column then 1 else 0) := by
  cases column with
  | none => simp [augmentedLowOrderLDGenerator, lowOrderLDMutationForcing]
  | some column =>
    migration_row_entry
    simp [hmigration, hmutation, hne, Ne.symm hne] <;> ring

/-! ## The heterozygosity coordinates on the no-migration history -/

/-- The rates with migration `0` between the pair have no migration at all. -/
theorem withSymmetricMigration_zero_migration (rates : ManyDemeLDRates D) {parent child : Fin D}
    (hne : parent ≠ child) (source target : Fin D) :
    (withSymmetricMigration rates hne 0 le_rfl).migration source target = 0 := by
  simp [withSymmetricMigration, symmetricPairMigration]

/-- **The feeding weight** `κ_i = c_i/(4 c_i + ρ_i)` of a one-index heterozygosity coordinate.

Empirical status: NOT AN EMPIRICAL CLAIM.  A ratio of rates. -/
def fedWeight (rates : ManyDemeLDRates D) (deme : Fin D) : ℝ :=
  rates.coalescence deme / (4 * rates.coalescence deme + rates.recombination deme)

/-- The feeding weight times the rate gap `(3 c_i + ρ_i/2) - c_i` is `c_i/2`. -/
theorem fedWeight_mul (rates : ManyDemeLDRates D) (deme : Fin D) :
    fedWeight rates deme
        * ((3 * rates.coalescence deme + rates.recombination deme / 2) - rates.coalescence deme)
      = rates.coalescence deme / 2 := by
  have hpos : 0 < 4 * rates.coalescence deme + rates.recombination deme := by
    have := rates.coalescence_pos deme
    have := rates.recombination_nonneg deme
    linarith
  rw [fedWeight, div_mul_eq_mul_div, div_eq_iff hpos.ne']
  ring

/-- **`pi2(T, S, T, T)` on the no-migration history.**

Assumes: no mutation and `parent ≠ child`. -/
theorem noMigrationHistory_pi2_childFirst (rates : ManyDemeLDRates D)
    (hmutation : ∀ deme, rates.mutation deme = 0) {parent child : Fin D} (hne : parent ≠ child)
    (ancestral : AffineLowOrderLDCoordinate D → ℝ) (time : ℝ) :
    migrationHistory rates hne 0 le_rfl ancestral time (some (.pi2 child parent child child))
      = Real.exp (-rates.coalescence child * time)
          * (ancestral (some (.pi2 parent parent parent parent))
            + fedWeight rates child * ancestral (some (.Dz parent parent parent)))
        - fedWeight rates child
          * Real.exp (-(3 * rates.coalescence child + rates.recombination child / 2) * time)
          * ancestral (some (.Dz parent parent parent)) := by
  rw [migrationHistory, matrixExponential_mulVec_apply_of_fed_row _ time _
    (fedWeight_mul rates child)
    (augmentedLowOrderLDGenerator_Dz_mixed_row _ (withSymmetricMigration_zero_migration rates hne)
      hmutation (Ne.symm hne))
    (augmentedLowOrderLDGenerator_pi2_fed_row _ (withSymmetricMigration_zero_migration rates hne)
      hmutation (Ne.symm hne))]
  simp [lowOrderLDSplitTransform_mulVec, LowOrderLDCoordinate.mergeSplit, hne]

/-- **`pi2(S, T, T, T)` on the no-migration history.**

Assumes: no mutation and `parent ≠ child`. -/
theorem noMigrationHistory_pi2_childSecond (rates : ManyDemeLDRates D)
    (hmutation : ∀ deme, rates.mutation deme = 0) {parent child : Fin D} (hne : parent ≠ child)
    (ancestral : AffineLowOrderLDCoordinate D → ℝ) (time : ℝ) :
    migrationHistory rates hne 0 le_rfl ancestral time (some (.pi2 parent child child child))
      = Real.exp (-rates.coalescence child * time)
          * (ancestral (some (.pi2 parent parent parent parent))
            + fedWeight rates child * ancestral (some (.Dz parent parent parent)))
        - fedWeight rates child
          * Real.exp (-(3 * rates.coalescence child + rates.recombination child / 2) * time)
          * ancestral (some (.Dz parent parent parent)) := by
  rw [migrationHistory, matrixExponential_mulVec_apply_of_fed_row _ time _
    (fedWeight_mul rates child)
    (augmentedLowOrderLDGenerator_Dz_mixed_row _ (withSymmetricMigration_zero_migration rates hne)
      hmutation (Ne.symm hne))
    (augmentedLowOrderLDGenerator_pi2_fed_row_swap _
      (withSymmetricMigration_zero_migration rates hne) hmutation (Ne.symm hne))]
  simp [lowOrderLDSplitTransform_mulVec, LowOrderLDCoordinate.mergeSplit, hne]

/-- **`pi2(S, S, S, T)` on the no-migration history.**

Assumes: no mutation and `parent ≠ child`. -/
theorem noMigrationHistory_pi2_parentThird (rates : ManyDemeLDRates D)
    (hmutation : ∀ deme, rates.mutation deme = 0) {parent child : Fin D} (hne : parent ≠ child)
    (ancestral : AffineLowOrderLDCoordinate D → ℝ) (time : ℝ) :
    migrationHistory rates hne 0 le_rfl ancestral time (some (.pi2 parent parent parent child))
      = Real.exp (-rates.coalescence parent * time)
          * (ancestral (some (.pi2 parent parent parent parent))
            + fedWeight rates parent * ancestral (some (.Dz parent parent parent)))
        - fedWeight rates parent
          * Real.exp (-(3 * rates.coalescence parent + rates.recombination parent / 2) * time)
          * ancestral (some (.Dz parent parent parent)) := by
  rw [migrationHistory, matrixExponential_mulVec_apply_of_fed_row _ time _
    (fedWeight_mul rates parent)
    (augmentedLowOrderLDGenerator_Dz_leading_row _
      (withSymmetricMigration_zero_migration rates hne) hmutation hne)
    (augmentedLowOrderLDGenerator_pi2_leading_row _
      (withSymmetricMigration_zero_migration rates hne) hmutation hne)]
  simp [lowOrderLDSplitTransform_mulVec, LowOrderLDCoordinate.mergeSplit, hne]

/-- **`pi2(S, S, T, S)` on the no-migration history.**

Assumes: no mutation and `parent ≠ child`. -/
theorem noMigrationHistory_pi2_parentFourth (rates : ManyDemeLDRates D)
    (hmutation : ∀ deme, rates.mutation deme = 0) {parent child : Fin D} (hne : parent ≠ child)
    (ancestral : AffineLowOrderLDCoordinate D → ℝ) (time : ℝ) :
    migrationHistory rates hne 0 le_rfl ancestral time (some (.pi2 parent parent child parent))
      = Real.exp (-rates.coalescence parent * time)
          * (ancestral (some (.pi2 parent parent parent parent))
            + fedWeight rates parent * ancestral (some (.Dz parent parent parent)))
        - fedWeight rates parent
          * Real.exp (-(3 * rates.coalescence parent + rates.recombination parent / 2) * time)
          * ancestral (some (.Dz parent parent parent)) := by
  rw [migrationHistory, matrixExponential_mulVec_apply_of_fed_row _ time _
    (fedWeight_mul rates parent)
    (augmentedLowOrderLDGenerator_Dz_leading_row _
      (withSymmetricMigration_zero_migration rates hne) hmutation hne)
    (augmentedLowOrderLDGenerator_pi2_leading_row_swap _
      (withSymmetricMigration_zero_migration rates hne) hmutation hne)]
  simp [lowOrderLDSplitTransform_mulVec, LowOrderLDCoordinate.mergeSplit, hne]

/-- **`pi2(S, S, T, T)` on the no-migration history** decays at `c_S + c_T`.

Assumes: no mutation and `parent ≠ child`. -/
theorem noMigrationHistory_pi2_cross (rates : ManyDemeLDRates D)
    (hmutation : ∀ deme, rates.mutation deme = 0) {parent child : Fin D} (hne : parent ≠ child)
    (ancestral : AffineLowOrderLDCoordinate D → ℝ) (time : ℝ) :
    migrationHistory rates hne 0 le_rfl ancestral time (some (.pi2 parent parent child child))
      = Real.exp (-(rates.coalescence parent + rates.coalescence child) * time)
        * ancestral (some (.pi2 parent parent parent parent)) := by
  rw [migrationHistory, matrixExponential_mulVec_apply_of_row_eq _ time _ _ _
    (augmentedLowOrderLDGenerator_pi2_row _ (withSymmetricMigration_zero_migration rates hne)
      hmutation hne), mul_comm time, splitTransform_pi2 hne]
  rfl

/-! ## The heterozygosity stencil -/

/-- **The heterozygosity migration stencil on the no-migration history, at equal rates**, is
`4 π₀ (e^{-ct} - e^{-2ct}) + 4 κ Dz₀ (e^{-ct} - e^{-(3c + ρ/2) t})`.

Assumes: no mutation, `parent ≠ child`, and equal drift and recombination rates. -/
theorem heterozygosityMigrationStencil_noMigration (rates : ManyDemeLDRates D)
    (hmutation : ∀ deme, rates.mutation deme = 0) {parent child : Fin D} (hne : parent ≠ child)
    (hcoal : rates.coalescence child = rates.coalescence parent)
    (hrec : rates.recombination child = rates.recombination parent)
    (ancestral : AffineLowOrderLDCoordinate D → ℝ) (time : ℝ) :
    heterozygosityMigrationStencil parent child
        (migrationHistory rates hne 0 le_rfl ancestral time)
      = 4 * ancestral (some (.pi2 parent parent parent parent))
          * (Real.exp (-rates.coalescence parent * time)
            - Real.exp (-(2 * rates.coalescence parent) * time))
        + 4 * fedWeight rates parent * ancestral (some (.Dz parent parent parent))
          * (Real.exp (-rates.coalescence parent * time)
            - Real.exp (-(3 * rates.coalescence parent + rates.recombination parent / 2)
              * time)) := by
  have hweight : fedWeight rates child = fedWeight rates parent := by
    rw [fedWeight, fedWeight, hcoal, hrec]
  rw [heterozygosityMigrationStencil, noMigrationHistory_pi2_childFirst rates hmutation hne,
    noMigrationHistory_pi2_childSecond rates hmutation hne,
    noMigrationHistory_pi2_parentThird rates hmutation hne,
    noMigrationHistory_pi2_parentFourth rates hmutation hne,
    noMigrationHistory_pi2_cross rates hmutation hne, hweight, hcoal, hrec, ← two_mul]
  ring

/-- **To first order, migration raises the heterozygosity denominator.**  At equal rates the
heterozygosity migration stencil on the no-migration history is nonnegative at nonnegative
times.

Assumes: no mutation, `parent ≠ child`, equal drift and recombination rates, nonnegative
ancestral `pi2` and `Dz`, and `0 ≤ time`. -/
theorem heterozygosityMigrationStencil_noMigration_nonneg (rates : ManyDemeLDRates D)
    (hmutation : ∀ deme, rates.mutation deme = 0) {parent child : Fin D} (hne : parent ≠ child)
    (hcoal : rates.coalescence child = rates.coalescence parent)
    (hrec : rates.recombination child = rates.recombination parent)
    (ancestral : AffineLowOrderLDCoordinate D → ℝ)
    (hheterozygosity : 0 ≤ ancestral (some (.pi2 parent parent parent parent)))
    (hcontrast : 0 ≤ ancestral (some (.Dz parent parent parent))) {time : ℝ} (htime : 0 ≤ time) :
    0 ≤ heterozygosityMigrationStencil parent child
      (migrationHistory rates hne 0 le_rfl ancestral time) := by
  have hc := rates.coalescence_pos parent
  have hρ := rates.recombination_nonneg parent
  have hdouble : Real.exp (-(2 * rates.coalescence parent) * time)
      ≤ Real.exp (-rates.coalescence parent * time) :=
    Real.exp_le_exp.mpr (by nlinarith)
  have hmixed : Real.exp (-(3 * rates.coalescence parent + rates.recombination parent / 2) * time)
      ≤ Real.exp (-rates.coalescence parent * time) :=
    Real.exp_le_exp.mpr (by nlinarith)
  have hweight : 0 ≤ fedWeight rates parent := div_nonneg hc.le (by linarith)
  rw [heterozygosityMigrationStencil_noMigration rates hmutation hne hcoal hrec]
  exact add_nonneg
    (mul_nonneg (mul_nonneg (by norm_num) hheterozygosity) (sub_nonneg.mpr hdouble))
    (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hweight) hcontrast)
      (sub_nonneg.mpr hmixed))

end

end Descent.Portability.MigrationPortabilityFirstOrder
