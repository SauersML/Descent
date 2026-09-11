/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Coalescent.TwoLocusHistory
import Mathlib.Analysis.Matrix
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Topology.Algebra.Module.FiniteDimension

assert_below Descent.Decision Descent.Program

/-!
# The low-order generator is linear and Lipschitz in the rates

NOTE1 section 2.4 treats nonnegative measurable rates with integrable norm by approximating them
in `L¹` with nicer rates and bounding propagator differences by the `L¹` difference of the
generators.  That helps only if the generator difference is controlled by the rate difference.
This module proves it for the corpus generator `augmentedLowOrderLDGenerator`.

Every contribution to the two-locus low-order system is a rate times a fixed linear combination
of moments: coalescence in the drift, migration, recombination, and mutation in the coupling,
the recurrent damping and the affine forcing.  `addRates` adds two rate laws coordinatewise,
which is again a rate law, and `augmentedLowOrderLDGenerator_addRates` shows that the generator
of the sum is the sum of the generators.  `scaleRates` multiplies a rate law by a positive
factor, and `augmentedLowOrderLDGenerator_scaleRates` shows that the generator scales with it.

A rate law is a point of the space of signed rate coordinates `RateCoordinates`.
`positivePartRates` turns an arbitrary signed tuple into a rate law, carrying the positive parts
of its coordinates on top of unit coalescence.  `signedGenerator x` is the generator of the
positive part of `x` minus the generator of the positive part of `-x`.  Additivity on rate laws
makes it additive and homogeneous (`signedGenerator_add`, `signedGenerator_smul`), so
`generatorLinearMap` is a linear map on the finite-dimensional coordinate space, and
`augmentedLowOrderLDGenerator_eq_generatorLinearMap` shows that it agrees with the corpus
generator on every rate law.  A linear map on a finite-dimensional space is bounded, so
`exists_generator_lipschitz` gives one constant `K` with `‖A(r)‖ ≤ K ‖r‖` and
`‖A(r) - A(r')‖ ≤ K ‖r - r'‖` for all rate laws `r, r'`, in the operator norm on matrices and the
sup norm on rate coordinates.

## Empirical status

None.  The bodies here are algebra: finite sums of products of rates with moment coordinates,
and the boundedness of a linear map on a finite-dimensional space, so no measurement can bear on
them.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.RateGeneratorLipschitz

open Coalescent
open scoped Matrix.Norms.Operator

/-! ## Adding and scaling rate laws -/

/-- The sum of two rate laws: every coalescence, migration, mutation and recombination rate is
added.  Rates of independent processes acting together add, so the sum is again a rate law. -/
def addRates {D : ℕ} (first second : ManyDemeLDRates D) : ManyDemeLDRates D where
  coalescence deme := first.coalescence deme + second.coalescence deme
  migration source target := first.migration source target + second.migration source target
  mutation deme := first.mutation deme + second.mutation deme
  recombination deme := first.recombination deme + second.recombination deme
  coalescence_pos deme := add_pos (first.coalescence_pos deme) (second.coalescence_pos deme)
  migration_nonneg source target :=
    add_nonneg (first.migration_nonneg source target) (second.migration_nonneg source target)
  migration_self deme := by rw [first.migration_self deme, second.migration_self deme, add_zero]
  mutation_nonneg deme := add_nonneg (first.mutation_nonneg deme) (second.mutation_nonneg deme)
  recombination_nonneg deme :=
    add_nonneg (first.recombination_nonneg deme) (second.recombination_nonneg deme)

/-- A rate law multiplied by a positive factor: every process running `factor` times faster. -/
def scaleRates {D : ℕ} (factor : ℝ) (hfactor : 0 < factor) (rates : ManyDemeLDRates D) :
    ManyDemeLDRates D where
  coalescence deme := factor * rates.coalescence deme
  migration source target := factor * rates.migration source target
  mutation deme := factor * rates.mutation deme
  recombination deme := factor * rates.recombination deme
  coalescence_pos deme := mul_pos hfactor (rates.coalescence_pos deme)
  migration_nonneg source target := mul_nonneg hfactor.le (rates.migration_nonneg source target)
  migration_self deme := by rw [rates.migration_self deme, mul_zero]
  mutation_nonneg deme := mul_nonneg hfactor.le (rates.mutation_nonneg deme)
  recombination_nonneg deme := mul_nonneg hfactor.le (rates.recombination_nonneg deme)

/-- Two rate laws with the same coalescence, migration, mutation and recombination rates are
equal. -/
theorem rates_eq_of_coordinates {D : ℕ} {first second : ManyDemeLDRates D}
    (hcoalescence : first.coalescence = second.coalescence)
    (hmigration : first.migration = second.migration)
    (hmutation : first.mutation = second.mutation)
    (hrecombination : first.recombination = second.recombination) : first = second := by
  cases first
  cases second
  simp only [ManyDemeLDRates.mk.injEq]
  exact ⟨hcoalescence, hmigration, hmutation, hrecombination⟩

/-! ## The generator of a sum of rate laws -/

theorem lowOrderLDDrift_addRates {D : ℕ} (first second : ManyDemeLDRates D)
    (moment : LowOrderLDCoordinate D → ℝ) (coordinate : LowOrderLDCoordinate D) :
    lowOrderLDDrift (addRates first second) moment coordinate =
      lowOrderLDDrift first moment coordinate + lowOrderLDDrift second moment coordinate := by
  cases coordinate <;> simp only [lowOrderLDDrift, addRates, ite_add_ite] <;> ring_nf

theorem lowOrderLDMigration_addRates {D : ℕ} (first second : ManyDemeLDRates D)
    (moment : LowOrderLDCoordinate D → ℝ) (coordinate : LowOrderLDCoordinate D) :
    lowOrderLDMigration (addRates first second) moment coordinate =
      lowOrderLDMigration first moment coordinate +
        lowOrderLDMigration second moment coordinate := by
  cases coordinate <;>
    simp only [lowOrderLDMigration, addRates, add_mul, Finset.sum_add_distrib] <;> ring

theorem lowOrderLDRecombination_addRates {D : ℕ} (first second : ManyDemeLDRates D)
    (moment : LowOrderLDCoordinate D → ℝ) (coordinate : LowOrderLDCoordinate D) :
    lowOrderLDRecombination (addRates first second) moment coordinate =
      lowOrderLDRecombination first moment coordinate +
        lowOrderLDRecombination second moment coordinate := by
  cases coordinate <;> simp only [lowOrderLDRecombination, addRates] <;> ring

theorem lowOrderLDMutationCoupling_addRates {D : ℕ} (first second : ManyDemeLDRates D)
    (moment : LowOrderLDCoordinate D → ℝ) (coordinate : LowOrderLDCoordinate D) :
    lowOrderLDMutationCoupling (addRates first second) moment coordinate =
      lowOrderLDMutationCoupling first moment coordinate +
        lowOrderLDMutationCoupling second moment coordinate := by
  cases coordinate <;> simp only [lowOrderLDMutationCoupling, addRates] <;> ring

theorem lowOrderLDRecurrentMutationDamping_addRates {D : ℕ} (first second : ManyDemeLDRates D)
    (moment : LowOrderLDCoordinate D → ℝ) (coordinate : LowOrderLDCoordinate D) :
    lowOrderLDRecurrentMutationDamping (addRates first second) moment coordinate =
      lowOrderLDRecurrentMutationDamping first moment coordinate +
        lowOrderLDRecurrentMutationDamping second moment coordinate := by
  cases coordinate <;> simp only [lowOrderLDRecurrentMutationDamping, addRates] <;> ring

theorem lowOrderLDMutationForcing_addRates {D : ℕ} (first second : ManyDemeLDRates D)
    (coordinate : LowOrderLDCoordinate D) :
    lowOrderLDMutationForcing (addRates first second) coordinate =
      lowOrderLDMutationForcing first coordinate + lowOrderLDMutationForcing second coordinate := by
  cases coordinate <;> simp only [lowOrderLDMutationForcing, addRates] <;> ring

theorem lowOrderLDHomogeneousGenerator_addRates {D : ℕ} (first second : ManyDemeLDRates D)
    (moment : LowOrderLDCoordinate D → ℝ) (coordinate : LowOrderLDCoordinate D) :
    lowOrderLDHomogeneousGenerator (addRates first second) moment coordinate =
      lowOrderLDHomogeneousGenerator first moment coordinate +
        lowOrderLDHomogeneousGenerator second moment coordinate := by
  simp only [lowOrderLDHomogeneousGenerator, lowOrderLDDrift_addRates,
    lowOrderLDMigration_addRates, lowOrderLDRecombination_addRates,
    lowOrderLDMutationCoupling_addRates, lowOrderLDRecurrentMutationDamping_addRates]
  ring

/-- **The generator of a sum of rate laws is the sum of the generators.** -/
theorem augmentedLowOrderLDGenerator_addRates {D : ℕ} (first second : ManyDemeLDRates D) :
    augmentedLowOrderLDGenerator (addRates first second) =
      augmentedLowOrderLDGenerator first + augmentedLowOrderLDGenerator second := by
  ext row column
  rw [Matrix.add_apply]
  rcases row with _ | row
  · simp [augmentedLowOrderLDGenerator]
  · rcases column with _ | column
    · simp only [augmentedLowOrderLDGenerator]
      exact lowOrderLDMutationForcing_addRates first second row
    · simp only [augmentedLowOrderLDGenerator]
      exact lowOrderLDHomogeneousGenerator_addRates first second _ row

/-- Rate laws balancing in sum have balancing generator differences: if `first + fourth` and
`third + second` are the same rate law, then `A(first) - A(second) = A(third) - A(fourth)`. -/
theorem generator_sub_eq_of_addRates_eq {D : ℕ} {first second third fourth : ManyDemeLDRates D}
    (hbalance : addRates first fourth = addRates third second) :
    augmentedLowOrderLDGenerator first - augmentedLowOrderLDGenerator second =
      augmentedLowOrderLDGenerator third - augmentedLowOrderLDGenerator fourth := by
  have hsum := congrArg augmentedLowOrderLDGenerator hbalance
  rw [augmentedLowOrderLDGenerator_addRates, augmentedLowOrderLDGenerator_addRates] at hsum
  exact sub_eq_sub_iff_add_eq_add.mpr hsum

/-! ## The generator of a scaled rate law -/

theorem lowOrderLDDrift_scaleRates {D : ℕ} (factor : ℝ) (hfactor : 0 < factor)
    (rates : ManyDemeLDRates D) (moment : LowOrderLDCoordinate D → ℝ)
    (coordinate : LowOrderLDCoordinate D) :
    lowOrderLDDrift (scaleRates factor hfactor rates) moment coordinate =
      factor * lowOrderLDDrift rates moment coordinate := by
  cases coordinate <;> simp only [lowOrderLDDrift, scaleRates, mul_ite] <;> ring_nf

theorem lowOrderLDMigration_scaleRates {D : ℕ} (factor : ℝ) (hfactor : 0 < factor)
    (rates : ManyDemeLDRates D) (moment : LowOrderLDCoordinate D → ℝ)
    (coordinate : LowOrderLDCoordinate D) :
    lowOrderLDMigration (scaleRates factor hfactor rates) moment coordinate =
      factor * lowOrderLDMigration rates moment coordinate := by
  cases coordinate <;>
    simp only [lowOrderLDMigration, scaleRates, mul_add, Finset.mul_sum, mul_assoc]

theorem lowOrderLDRecombination_scaleRates {D : ℕ} (factor : ℝ) (hfactor : 0 < factor)
    (rates : ManyDemeLDRates D) (moment : LowOrderLDCoordinate D → ℝ)
    (coordinate : LowOrderLDCoordinate D) :
    lowOrderLDRecombination (scaleRates factor hfactor rates) moment coordinate =
      factor * lowOrderLDRecombination rates moment coordinate := by
  cases coordinate <;> simp only [lowOrderLDRecombination, scaleRates] <;> ring

theorem lowOrderLDMutationCoupling_scaleRates {D : ℕ} (factor : ℝ) (hfactor : 0 < factor)
    (rates : ManyDemeLDRates D) (moment : LowOrderLDCoordinate D → ℝ)
    (coordinate : LowOrderLDCoordinate D) :
    lowOrderLDMutationCoupling (scaleRates factor hfactor rates) moment coordinate =
      factor * lowOrderLDMutationCoupling rates moment coordinate := by
  cases coordinate <;> simp only [lowOrderLDMutationCoupling, scaleRates] <;> ring

theorem lowOrderLDRecurrentMutationDamping_scaleRates {D : ℕ} (factor : ℝ)
    (hfactor : 0 < factor) (rates : ManyDemeLDRates D) (moment : LowOrderLDCoordinate D → ℝ)
    (coordinate : LowOrderLDCoordinate D) :
    lowOrderLDRecurrentMutationDamping (scaleRates factor hfactor rates) moment coordinate =
      factor * lowOrderLDRecurrentMutationDamping rates moment coordinate := by
  cases coordinate <;> simp only [lowOrderLDRecurrentMutationDamping, scaleRates] <;> ring

theorem lowOrderLDMutationForcing_scaleRates {D : ℕ} (factor : ℝ) (hfactor : 0 < factor)
    (rates : ManyDemeLDRates D) (coordinate : LowOrderLDCoordinate D) :
    lowOrderLDMutationForcing (scaleRates factor hfactor rates) coordinate =
      factor * lowOrderLDMutationForcing rates coordinate := by
  cases coordinate <;> simp only [lowOrderLDMutationForcing, scaleRates] <;> ring

theorem lowOrderLDHomogeneousGenerator_scaleRates {D : ℕ} (factor : ℝ) (hfactor : 0 < factor)
    (rates : ManyDemeLDRates D) (moment : LowOrderLDCoordinate D → ℝ)
    (coordinate : LowOrderLDCoordinate D) :
    lowOrderLDHomogeneousGenerator (scaleRates factor hfactor rates) moment coordinate =
      factor * lowOrderLDHomogeneousGenerator rates moment coordinate := by
  simp only [lowOrderLDHomogeneousGenerator, lowOrderLDDrift_scaleRates,
    lowOrderLDMigration_scaleRates, lowOrderLDRecombination_scaleRates,
    lowOrderLDMutationCoupling_scaleRates, lowOrderLDRecurrentMutationDamping_scaleRates]
  ring

/-- **The generator of a positively scaled rate law is the scaled generator.** -/
theorem augmentedLowOrderLDGenerator_scaleRates {D : ℕ} (factor : ℝ) (hfactor : 0 < factor)
    (rates : ManyDemeLDRates D) :
    augmentedLowOrderLDGenerator (scaleRates factor hfactor rates) =
      factor • augmentedLowOrderLDGenerator rates := by
  ext row column
  rw [Matrix.smul_apply, smul_eq_mul]
  rcases row with _ | row
  · simp [augmentedLowOrderLDGenerator]
  · rcases column with _ | column
    · simp only [augmentedLowOrderLDGenerator]
      exact lowOrderLDMutationForcing_scaleRates factor hfactor rates row
    · simp only [augmentedLowOrderLDGenerator]
      exact lowOrderLDHomogeneousGenerator_scaleRates factor hfactor rates _ row

/-! ## Signed rate coordinates -/

/-- Signed rate coordinates: coalescence, migration, mutation and recombination rates as
unconstrained real tuples, with the sup norm. -/
abbrev RateCoordinates (D : ℕ) : Type :=
  (Fin D → ℝ) × (Fin D → Fin D → ℝ) × (Fin D → ℝ) × (Fin D → ℝ)

/-- The rate coordinates of a rate law. -/
def rateCoordinates {D : ℕ} (rates : ManyDemeLDRates D) : RateCoordinates D :=
  (rates.coalescence, rates.migration, rates.mutation, rates.recombination)

/-- The rate law carrying the positive parts of a signed coordinate tuple, on top of unit
coalescence and with self-migration dropped. -/
def positivePartRates {D : ℕ} (coordinates : RateCoordinates D) : ManyDemeLDRates D where
  coalescence deme := max (coordinates.1 deme) 0 + 1
  migration source target :=
    if source = target then 0 else max (coordinates.2.1 source target) 0
  mutation deme := max (coordinates.2.2.1 deme) 0
  recombination deme := max (coordinates.2.2.2 deme) 0
  coalescence_pos deme := add_pos_of_nonneg_of_pos (le_max_right _ _) one_pos
  migration_nonneg source target := by
    split_ifs
    · exact le_rfl
    · exact le_max_right _ _
  migration_self deme := if_pos rfl
  mutation_nonneg deme := le_max_right _ _
  recombination_nonneg deme := le_max_right _ _

/-- A signed rate is its positive part minus the positive part of its negation. -/
theorem rate_positivePart_sub_negativePart (a : ℝ) : max a 0 - max (-a) 0 = a := by
  rcases le_total 0 a with hnonneg | hnonpos
  · rw [max_eq_left hnonneg, max_eq_right (neg_nonpos.mpr hnonneg), sub_zero]
  · rw [max_eq_right hnonpos, max_eq_left (neg_nonneg.mpr hnonpos), zero_sub, neg_neg]

/-- The positive parts of a sum balance against the positive parts of the summands. -/
theorem addRates_positivePartRates_add {D : ℕ} (x y : RateCoordinates D) :
    addRates (positivePartRates (x + y))
        (addRates (positivePartRates (-x)) (positivePartRates (-y))) =
      addRates (addRates (positivePartRates x) (positivePartRates y))
        (positivePartRates (-(x + y))) := by
  apply rates_eq_of_coordinates
  · funext deme
    simp only [addRates, positivePartRates, Prod.fst_add, Prod.fst_neg, Pi.add_apply,
      Pi.neg_apply]
    linarith [rate_positivePart_sub_negativePart (x.1 deme),
      rate_positivePart_sub_negativePart (y.1 deme),
      rate_positivePart_sub_negativePart (x.1 deme + y.1 deme)]
  · funext source target
    simp only [addRates, positivePartRates, Prod.fst_add, Prod.snd_add, Prod.fst_neg,
      Prod.snd_neg, Pi.add_apply, Pi.neg_apply]
    split_ifs
    · ring
    · linarith [rate_positivePart_sub_negativePart (x.2.1 source target),
        rate_positivePart_sub_negativePart (y.2.1 source target),
        rate_positivePart_sub_negativePart (x.2.1 source target + y.2.1 source target)]
  · funext deme
    simp only [addRates, positivePartRates, Prod.fst_add, Prod.snd_add, Prod.fst_neg,
      Prod.snd_neg, Pi.add_apply, Pi.neg_apply]
    linarith [rate_positivePart_sub_negativePart (x.2.2.1 deme),
      rate_positivePart_sub_negativePart (y.2.2.1 deme),
      rate_positivePart_sub_negativePart (x.2.2.1 deme + y.2.2.1 deme)]
  · funext deme
    simp only [addRates, positivePartRates, Prod.snd_add, Prod.snd_neg, Pi.add_apply,
      Pi.neg_apply]
    linarith [rate_positivePart_sub_negativePart (x.2.2.2 deme),
      rate_positivePart_sub_negativePart (y.2.2.2 deme),
      rate_positivePart_sub_negativePart (x.2.2.2 deme + y.2.2.2 deme)]

/-- The positive parts of a positive multiple balance against the scaled positive parts. -/
theorem addRates_positivePartRates_smul {D : ℕ} {factor : ℝ} (hfactor : 0 < factor)
    (x : RateCoordinates D) :
    addRates (positivePartRates (factor • x))
        (scaleRates factor hfactor (positivePartRates (-x))) =
      addRates (scaleRates factor hfactor (positivePartRates x))
        (positivePartRates (-(factor • x))) := by
  apply rates_eq_of_coordinates
  · funext deme
    simp only [addRates, scaleRates, positivePartRates, Prod.smul_fst, Prod.fst_neg,
      Pi.smul_apply, Pi.neg_apply, smul_eq_mul]
    linear_combination rate_positivePart_sub_negativePart (factor * x.1 deme) -
      factor * rate_positivePart_sub_negativePart (x.1 deme)
  · funext source target
    simp only [addRates, scaleRates, positivePartRates, Prod.smul_fst, Prod.smul_snd,
      Prod.fst_neg, Prod.snd_neg, Pi.smul_apply, Pi.neg_apply, smul_eq_mul]
    split_ifs
    · ring
    · linear_combination rate_positivePart_sub_negativePart (factor * x.2.1 source target) -
        factor * rate_positivePart_sub_negativePart (x.2.1 source target)
  · funext deme
    simp only [addRates, scaleRates, positivePartRates, Prod.smul_fst, Prod.smul_snd,
      Prod.fst_neg, Prod.snd_neg, Pi.smul_apply, Pi.neg_apply, smul_eq_mul]
    linear_combination rate_positivePart_sub_negativePart (factor * x.2.2.1 deme) -
      factor * rate_positivePart_sub_negativePart (x.2.2.1 deme)
  · funext deme
    simp only [addRates, scaleRates, positivePartRates, Prod.smul_snd, Prod.snd_neg,
      Pi.smul_apply, Pi.neg_apply, smul_eq_mul]
    linear_combination rate_positivePart_sub_negativePart (factor * x.2.2.2 deme) -
      factor * rate_positivePart_sub_negativePart (x.2.2.2 deme)

/-- A rate law plus the positive part of its negated coordinates is the positive part of its
coordinates: every rate is nonnegative, so its negation contributes nothing. -/
theorem addRates_positivePartRates_neg_rateCoordinates {D : ℕ} (rates : ManyDemeLDRates D) :
    addRates rates (positivePartRates (-rateCoordinates rates)) =
      positivePartRates (rateCoordinates rates) := by
  apply rates_eq_of_coordinates
  · funext deme
    have hpositive := rates.coalescence_pos deme
    simp only [addRates, positivePartRates, rateCoordinates, Prod.fst_neg, Pi.neg_apply]
    rw [max_eq_right (neg_nonpos.mpr hpositive.le), max_eq_left hpositive.le]
    ring
  · funext source target
    simp only [addRates, positivePartRates, rateCoordinates, Prod.fst_neg, Prod.snd_neg,
      Pi.neg_apply]
    by_cases hsame : source = target
    · subst hsame
      simp [rates.migration_self]
    · have hnonnegative := rates.migration_nonneg source target
      rw [if_neg hsame, if_neg hsame, max_eq_right (neg_nonpos.mpr hnonnegative),
        max_eq_left hnonnegative, add_zero]
  · funext deme
    have hnonnegative := rates.mutation_nonneg deme
    simp only [addRates, positivePartRates, rateCoordinates, Prod.fst_neg, Prod.snd_neg,
      Pi.neg_apply]
    rw [max_eq_right (neg_nonpos.mpr hnonnegative), max_eq_left hnonnegative, add_zero]
  · funext deme
    have hnonnegative := rates.recombination_nonneg deme
    simp only [addRates, positivePartRates, rateCoordinates, Prod.snd_neg, Pi.neg_apply]
    rw [max_eq_right (neg_nonpos.mpr hnonnegative), max_eq_left hnonnegative, add_zero]

/-! ## The linear extension of the generator -/

/-- The generator extended to signed rate coordinates: the generator of the positive part of
the tuple minus the generator of the positive part of its negation. -/
noncomputable def signedGenerator {D : ℕ} (coordinates : RateCoordinates D) :
    Matrix (AffineLowOrderLDCoordinate D) (AffineLowOrderLDCoordinate D) ℝ :=
  augmentedLowOrderLDGenerator (positivePartRates coordinates) -
    augmentedLowOrderLDGenerator (positivePartRates (-coordinates))

theorem signedGenerator_add {D : ℕ} (x y : RateCoordinates D) :
    signedGenerator (x + y) = signedGenerator x + signedGenerator y := by
  have hbalance := generator_sub_eq_of_addRates_eq (addRates_positivePartRates_add x y)
  unfold signedGenerator
  rw [hbalance, augmentedLowOrderLDGenerator_addRates, augmentedLowOrderLDGenerator_addRates]
  abel

theorem signedGenerator_neg {D : ℕ} (x : RateCoordinates D) :
    signedGenerator (-x) = -signedGenerator x := by
  unfold signedGenerator
  rw [neg_neg, neg_sub]

theorem signedGenerator_smul_of_pos {D : ℕ} {factor : ℝ} (hfactor : 0 < factor)
    (x : RateCoordinates D) : signedGenerator (factor • x) = factor • signedGenerator x := by
  have hbalance := generator_sub_eq_of_addRates_eq (addRates_positivePartRates_smul hfactor x)
  unfold signedGenerator
  rw [hbalance, augmentedLowOrderLDGenerator_scaleRates, augmentedLowOrderLDGenerator_scaleRates,
    smul_sub]

theorem signedGenerator_smul {D : ℕ} (factor : ℝ) (x : RateCoordinates D) :
    signedGenerator (factor • x) = factor • signedGenerator x := by
  rcases lt_trichotomy factor 0 with hnegative | hzero | hpositive
  · have hrewrite : factor • x = (-factor) • (-x) := by rw [neg_smul, smul_neg, neg_neg]
    rw [hrewrite, signedGenerator_smul_of_pos (neg_pos.mpr hnegative), signedGenerator_neg,
      neg_smul, smul_neg, neg_neg]
  · subst hzero
    rw [zero_smul, zero_smul]
    unfold signedGenerator
    rw [neg_zero, sub_self]
  · exact signedGenerator_smul_of_pos hpositive x

/-- The generator as a linear map on signed rate coordinates. -/
noncomputable def generatorLinearMap (D : ℕ) :
    RateCoordinates D →ₗ[ℝ]
      Matrix (AffineLowOrderLDCoordinate D) (AffineLowOrderLDCoordinate D) ℝ where
  toFun := signedGenerator
  map_add' := signedGenerator_add
  map_smul' := signedGenerator_smul

/-- **The corpus generator is the linear map at the rate coordinates.** -/
theorem augmentedLowOrderLDGenerator_eq_generatorLinearMap {D : ℕ} (rates : ManyDemeLDRates D) :
    augmentedLowOrderLDGenerator rates = generatorLinearMap D (rateCoordinates rates) := by
  have hsum := congrArg augmentedLowOrderLDGenerator
    (addRates_positivePartRates_neg_rateCoordinates rates)
  rw [augmentedLowOrderLDGenerator_addRates] at hsum
  show augmentedLowOrderLDGenerator rates = signedGenerator (rateCoordinates rates)
  unfold signedGenerator
  rw [← hsum]
  abel

/-- **The generator is Lipschitz in the rates.**  One constant bounds the operator norm of the
generator by the sup norm of the rate coordinates, and the generator difference of two rate laws
by the sup norm of their coordinate difference. -/
theorem exists_generator_lipschitz (D : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧
      (∀ rates : ManyDemeLDRates D,
        ‖augmentedLowOrderLDGenerator rates‖ ≤ K * ‖rateCoordinates rates‖) ∧
      ∀ first second : ManyDemeLDRates D,
        ‖augmentedLowOrderLDGenerator first - augmentedLowOrderLDGenerator second‖ ≤
          K * ‖rateCoordinates first - rateCoordinates second‖ := by
  let bounded := LinearMap.toContinuousLinearMap (generatorLinearMap D)
  refine ⟨‖bounded‖, norm_nonneg _, fun rates ↦ ?_, fun first second ↦ ?_⟩
  · rw [augmentedLowOrderLDGenerator_eq_generatorLinearMap]
    exact bounded.le_opNorm (rateCoordinates rates)
  · rw [augmentedLowOrderLDGenerator_eq_generatorLinearMap,
      augmentedLowOrderLDGenerator_eq_generatorLinearMap, ← map_sub]
    exact bounded.le_opNorm (rateCoordinates first - rateCoordinates second)

end Descent.Portability.RateGeneratorLipschitz
