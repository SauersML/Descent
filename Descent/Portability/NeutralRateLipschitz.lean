/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.PartialHaplotypeDualSemigroup
import Descent.Portability.RateGeneratorLipschitz
import Mathlib.Analysis.Matrix
import Mathlib.Topology.Algebra.Module.FiniteDimension

assert_below Descent.Decision Descent.Program

/-!
# The partial-haplotype dual generator is additive in the rates

NOTE1 §4.2a carries the dual semigroup of (20) over to measurable rate histories with integrable
norm by the approximation of §2.4. That approximation controls propagator differences by the
`L¹` difference of the generators, so it needs the dual generator of a rate law to depend on the
law linearly. This module proves the additive and homogeneous half of that for
`PartialHaplotypeDualSemigroup.dualGenerator`.

Every dual transition of `PartialHaplotypeDualGenerator.dualTransitions` carries exactly one rate
of the law, a migration, mutation, recombination or coalescence rate, and its target does not
depend on the rates. `addNeutralRates` adds two rate laws field by field, and `scaleNeutralRates`
multiplies one by a nonnegative factor. A weighted sum over the moves of one carrier is additive and
homogeneous in the law (`sum_map_carrierMoves_add`, `sum_map_carrierMoves_scale`), and so is a
weighted sum over all dual transitions (`sum_map_dualTransitions_add`,
`sum_map_dualTransitions_scale`). The jump and exit rates are such sums
(`jumpRate_eq_sum_map`, `exitRate_eq_sum_map`), so the dual generator of a sum of laws is the sum
of the generators (`dualGenerator_addNeutralRates`) and the generator of a scaled law is the scaled
generator (`dualGenerator_scaleNeutralRates`).

The linear extension. `NeutralRateCoordinates` holds signed rate tuples, `positivePartNeutralRates`
clips a tuple at zero after symmetrizing its mutation rates, so it is a genuine rate law, and
`signedDualGenerator` is the generator of the positive part minus the generator of the positive
part of the negation. Additivity on rate laws makes it additive and homogeneous, so
`dualGeneratorLinearMap` is a linear map on the finite-dimensional coordinate space, it agrees
with `dualGenerator` on every rate law (`dualGenerator_eq_dualGeneratorLinearMap`), and
`exists_dualGenerator_lipschitz` gives one constant bounding the generator difference of two laws
by their coordinate difference.

## Empirical status

None. The bodies here are algebra: finite sums of rates against indicators of fixed targets, so no
measurement can bear on them.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.NeutralRateLipschitz

open PartialHaplotypeCarrier PartialHaplotypeDualGenerator PartialHaplotypeDualSemigroup
open RateGeneratorLipschitz (rate_positivePart_sub_negativePart)

noncomputable section

variable {Deme Locus : Type*} {Allele : Locus → Type*}

/-! ## Adding and scaling rate laws -/

/-- The sum of two neutral rate laws, field by field: independent processes acting together. -/
def addNeutralRates (first second : NeutralRates Deme Locus Allele) :
    NeutralRates Deme Locus Allele where
  coalescence i := first.coalescence i + second.coalescence i
  migration i j := first.migration i j + second.migration i j
  recombination selector := first.recombination selector + second.recombination selector
  mutation ℓ a b := first.mutation ℓ a b + second.mutation ℓ a b
  coalescence_nonneg i := add_nonneg (first.coalescence_nonneg i) (second.coalescence_nonneg i)
  migration_nonneg i j := add_nonneg (first.migration_nonneg i j) (second.migration_nonneg i j)
  recombination_nonneg selector :=
    add_nonneg (first.recombination_nonneg selector) (second.recombination_nonneg selector)
  mutation_nonneg ℓ a b := add_nonneg (first.mutation_nonneg ℓ a b) (second.mutation_nonneg ℓ a b)
  mutation_symm ℓ a b := by rw [first.mutation_symm ℓ a b, second.mutation_symm ℓ a b]

/-- A neutral rate law multiplied by a nonnegative factor: every process `factor` times as fast. -/
def scaleNeutralRates (factor : ℝ) (hfactor : 0 ≤ factor) (rates : NeutralRates Deme Locus Allele) :
    NeutralRates Deme Locus Allele where
  coalescence i := factor * rates.coalescence i
  migration i j := factor * rates.migration i j
  recombination selector := factor * rates.recombination selector
  mutation ℓ a b := factor * rates.mutation ℓ a b
  coalescence_nonneg i := mul_nonneg hfactor (rates.coalescence_nonneg i)
  migration_nonneg i j := mul_nonneg hfactor (rates.migration_nonneg i j)
  recombination_nonneg selector := mul_nonneg hfactor (rates.recombination_nonneg selector)
  mutation_nonneg ℓ a b := mul_nonneg hfactor (rates.mutation_nonneg ℓ a b)
  mutation_symm ℓ a b := by rw [rates.mutation_symm ℓ a b]

/-! ## Weighted sums of multisets -/

/-- A weighted sum over a bound multiset splits when the weighted sum over every fiber splits. -/
theorem sum_map_bind_eq_add {α β : Type*} (m : Multiset α) (F G H : α → Multiset β)
    (w : β → ℝ) (h : ∀ a ∈ m, ((F a).map w).sum = ((G a).map w).sum + ((H a).map w).sum) :
    ((m.bind F).map w).sum = ((m.bind G).map w).sum + ((m.bind H).map w).sum := by
  simp only [Multiset.map_bind, Multiset.sum_bind]
  rw [← Multiset.sum_map_add]
  exact congrArg Multiset.sum (Multiset.map_congr rfl h)

/-- A weighted sum over a bound multiset scales when the weighted sum over every fiber scales. -/
theorem sum_map_bind_eq_mul {α β : Type*} (m : Multiset α) (F G : α → Multiset β) (w : β → ℝ)
    (factor : ℝ) (h : ∀ a ∈ m, ((F a).map w).sum = factor * ((G a).map w).sum) :
    ((m.bind F).map w).sum = factor * ((m.bind G).map w).sum := by
  simp only [Multiset.map_bind, Multiset.sum_bind]
  rw [← Multiset.sum_map_mul_left]
  exact congrArg Multiset.sum (Multiset.map_congr rfl h)

/-- An `if` with a zero branch splits over a sum in the other branch. -/
theorem ite_add_zero_eq (c : Prop) [Decidable c] (a b : ℝ) :
    (if c then a + b else 0) = (if c then a else 0) + (if c then b else 0) := by
  split_ifs <;> simp

/-- A factor inside the nonzero branch of an `if` with a zero branch comes out of the `if`. -/
theorem ite_mul_zero_eq (c : Prop) [Decidable c] (factor a : ℝ) :
    (if c then factor * a else 0) = factor * (if c then a else 0) := by
  split_ifs <;> simp

variable [Fintype Deme] [DecidableEq Deme] [Fintype Locus] [DecidableEq Locus]
  [∀ ℓ, Fintype (Allele ℓ)] [∀ ℓ, DecidableEq (Allele ℓ)]

/-! ## The moves of one carrier -/

section Carrier

variable (weight : Multiset (PartialType Deme Locus Allele) → ℝ)
  (τ : PartialType Deme Locus Allele)

theorem sum_map_migrationMoves_add (first second : NeutralRates Deme Locus Allele) :
    ((migrationMoves (addNeutralRates first second) τ).map fun move ↦ move.1 * weight move.2).sum =
      ((migrationMoves first τ).map fun move ↦ move.1 * weight move.2).sum +
        ((migrationMoves second τ).map fun move ↦ move.1 * weight move.2).sum := by
  simp only [migrationMoves, Multiset.map_map, Function.comp_def, addNeutralRates, add_mul,
    Multiset.sum_map_add]

theorem sum_map_mutationMoves_add (first second : NeutralRates Deme Locus Allele) :
    ((mutationMoves (addNeutralRates first second) τ).map fun move ↦ move.1 * weight move.2).sum =
      ((mutationMoves first τ).map fun move ↦ move.1 * weight move.2).sum +
        ((mutationMoves second τ).map fun move ↦ move.1 * weight move.2).sum := by
  unfold mutationMoves
  refine sum_map_bind_eq_add _ _ _ _ _ fun ℓ _ ↦ ?_
  cases τ.allele ℓ with
  | none => simp
  | some a =>
      simp only [Option.elim, Multiset.map_map, Function.comp_def, addNeutralRates, add_mul,
        Multiset.sum_map_add]

theorem sum_map_recombinationMoves_add (first second : NeutralRates Deme Locus Allele) :
    ((recombinationMoves (addNeutralRates first second) τ).map
        fun move ↦ move.1 * weight move.2).sum =
      ((recombinationMoves first τ).map fun move ↦ move.1 * weight move.2).sum +
        ((recombinationMoves second τ).map fun move ↦ move.1 * weight move.2).sum := by
  unfold recombinationMoves
  refine sum_map_bind_eq_add _ _ _ _ _ fun selector _ ↦ ?_
  by_cases hsplit : Splits τ selector
  · simp only [dif_pos hsplit, Multiset.map_singleton, Multiset.sum_singleton, addNeutralRates,
      add_mul]
  · simp only [dif_neg hsplit, Multiset.map_zero, Multiset.sum_zero, add_zero]

/-- **One carrier's weighted moves are additive in the rate law.** -/
theorem sum_map_carrierMoves_add (first second : NeutralRates Deme Locus Allele) :
    ((carrierMoves (addNeutralRates first second) τ).map fun move ↦ move.1 * weight move.2).sum =
      ((carrierMoves first τ).map fun move ↦ move.1 * weight move.2).sum +
        ((carrierMoves second τ).map fun move ↦ move.1 * weight move.2).sum := by
  simp only [carrierMoves, Multiset.map_add, Multiset.sum_add, sum_map_migrationMoves_add,
    sum_map_mutationMoves_add, sum_map_recombinationMoves_add]
  ring

theorem sum_map_migrationMoves_scale (factor : ℝ) (hfactor : 0 ≤ factor)
    (rates : NeutralRates Deme Locus Allele) :
    ((migrationMoves (scaleNeutralRates factor hfactor rates) τ).map
        fun move ↦ move.1 * weight move.2).sum =
      factor * ((migrationMoves rates τ).map fun move ↦ move.1 * weight move.2).sum := by
  simp only [migrationMoves, Multiset.map_map, Function.comp_def, scaleNeutralRates, mul_assoc,
    Multiset.sum_map_mul_left]

theorem sum_map_mutationMoves_scale (factor : ℝ) (hfactor : 0 ≤ factor)
    (rates : NeutralRates Deme Locus Allele) :
    ((mutationMoves (scaleNeutralRates factor hfactor rates) τ).map
        fun move ↦ move.1 * weight move.2).sum =
      factor * ((mutationMoves rates τ).map fun move ↦ move.1 * weight move.2).sum := by
  unfold mutationMoves
  refine sum_map_bind_eq_mul _ _ _ _ _ fun ℓ _ ↦ ?_
  cases τ.allele ℓ with
  | none => simp
  | some a =>
      simp only [Option.elim, Multiset.map_map, Function.comp_def, scaleNeutralRates, mul_assoc,
        Multiset.sum_map_mul_left]

theorem sum_map_recombinationMoves_scale (factor : ℝ) (hfactor : 0 ≤ factor)
    (rates : NeutralRates Deme Locus Allele) :
    ((recombinationMoves (scaleNeutralRates factor hfactor rates) τ).map
        fun move ↦ move.1 * weight move.2).sum =
      factor * ((recombinationMoves rates τ).map fun move ↦ move.1 * weight move.2).sum := by
  unfold recombinationMoves
  refine sum_map_bind_eq_mul _ _ _ _ _ fun selector _ ↦ ?_
  by_cases hsplit : Splits τ selector
  · simp only [dif_pos hsplit, Multiset.map_singleton, Multiset.sum_singleton, scaleNeutralRates,
      mul_assoc]
  · simp only [dif_neg hsplit, Multiset.map_zero, Multiset.sum_zero, mul_zero]

/-- **One carrier's weighted moves scale with the rate law.** -/
theorem sum_map_carrierMoves_scale (factor : ℝ) (hfactor : 0 ≤ factor)
    (rates : NeutralRates Deme Locus Allele) :
    ((carrierMoves (scaleNeutralRates factor hfactor rates) τ).map
        fun move ↦ move.1 * weight move.2).sum =
      factor * ((carrierMoves rates τ).map fun move ↦ move.1 * weight move.2).sum := by
  simp only [carrierMoves, Multiset.map_add, Multiset.sum_add, sum_map_migrationMoves_scale,
    sum_map_mutationMoves_scale, sum_map_recombinationMoves_scale]
  ring

end Carrier

/-! ## All dual transitions -/

section Transitions

variable (ξ : Multiset (PartialType Deme Locus Allele))
  (weight : Option (Multiset (PartialType Deme Locus Allele)) → ℝ)

/-- **Weighted sums over the dual transitions are additive in the rate law.** Every transition
carries one rate of the law and a target that does not depend on the rates. -/
theorem sum_map_dualTransitions_add (first second : NeutralRates Deme Locus Allele) :
    ((dualTransitions (addNeutralRates first second) ξ).map fun t ↦ t.1 * weight t.2).sum =
      ((dualTransitions first ξ).map fun t ↦ t.1 * weight t.2).sum +
        ((dualTransitions second ξ).map fun t ↦ t.1 * weight t.2).sum := by
  unfold dualTransitions
  simp only [Multiset.map_add, Multiset.sum_add]
  have hcarrier := sum_map_bind_eq_add ξ
    (fun τ ↦ (carrierMoves (addNeutralRates first second) τ).map
      fun move ↦ (move.1, some (move.2 + ξ.erase τ)))
    (fun τ ↦ (carrierMoves first τ).map fun move ↦ (move.1, some (move.2 + ξ.erase τ)))
    (fun τ ↦ (carrierMoves second τ).map fun move ↦ (move.1, some (move.2 + ξ.erase τ)))
    (fun t ↦ t.1 * weight t.2) fun τ _ ↦ by
      simp only [Multiset.map_map, Function.comp_def]
      exact sum_map_carrierMoves_add (fun m ↦ weight (some (m + ξ.erase τ))) τ first second
  have hcoalescence := sum_map_bind_eq_add ξ
    (fun τ ↦ (ξ.erase τ).map fun σ ↦
      (if τ.deme = σ.deme then (addNeutralRates first second).coalescence τ.deme / 2 else 0,
        if Compatible τ σ then some (coalesce τ σ ::ₘ (ξ.erase τ).erase σ) else none))
    (fun τ ↦ (ξ.erase τ).map fun σ ↦
      (if τ.deme = σ.deme then first.coalescence τ.deme / 2 else 0,
        if Compatible τ σ then some (coalesce τ σ ::ₘ (ξ.erase τ).erase σ) else none))
    (fun τ ↦ (ξ.erase τ).map fun σ ↦
      (if τ.deme = σ.deme then second.coalescence τ.deme / 2 else 0,
        if Compatible τ σ then some (coalesce τ σ ::ₘ (ξ.erase τ).erase σ) else none))
    (fun t ↦ t.1 * weight t.2) fun τ _ ↦ by
      simp only [Multiset.map_map, Function.comp_def, addNeutralRates, add_div, ite_add_zero_eq,
        add_mul, Multiset.sum_map_add]
  rw [hcarrier, hcoalescence]
  ring

/-- **Weighted sums over the dual transitions scale with the rate law.** -/
theorem sum_map_dualTransitions_scale (factor : ℝ) (hfactor : 0 ≤ factor)
    (rates : NeutralRates Deme Locus Allele) :
    ((dualTransitions (scaleNeutralRates factor hfactor rates) ξ).map
        fun t ↦ t.1 * weight t.2).sum =
      factor * ((dualTransitions rates ξ).map fun t ↦ t.1 * weight t.2).sum := by
  unfold dualTransitions
  simp only [Multiset.map_add, Multiset.sum_add]
  have hcarrier := sum_map_bind_eq_mul ξ
    (fun τ ↦ (carrierMoves (scaleNeutralRates factor hfactor rates) τ).map
      fun move ↦ (move.1, some (move.2 + ξ.erase τ)))
    (fun τ ↦ (carrierMoves rates τ).map fun move ↦ (move.1, some (move.2 + ξ.erase τ)))
    (fun t ↦ t.1 * weight t.2) factor fun τ _ ↦ by
      simp only [Multiset.map_map, Function.comp_def]
      exact sum_map_carrierMoves_scale (fun m ↦ weight (some (m + ξ.erase τ))) τ factor hfactor
        rates
  have hcoalescence := sum_map_bind_eq_mul ξ
    (fun τ ↦ (ξ.erase τ).map fun σ ↦
      (if τ.deme = σ.deme then (scaleNeutralRates factor hfactor rates).coalescence τ.deme / 2
        else 0,
        if Compatible τ σ then some (coalesce τ σ ::ₘ (ξ.erase τ).erase σ) else none))
    (fun τ ↦ (ξ.erase τ).map fun σ ↦
      (if τ.deme = σ.deme then rates.coalescence τ.deme / 2 else 0,
        if Compatible τ σ then some (coalesce τ σ ::ₘ (ξ.erase τ).erase σ) else none))
    (fun t ↦ t.1 * weight t.2) factor fun τ _ ↦ by
      simp only [Multiset.map_map, Function.comp_def, scaleNeutralRates, mul_div_assoc,
        ite_mul_zero_eq, mul_assoc, Multiset.sum_map_mul_left]
  rw [hcarrier, hcoalescence]
  ring

end Transitions

/-! ## The jump and exit rates and the dual generator -/

/-- The jump rate is a weighted sum over the dual transitions, with the indicator of the target. -/
theorem jumpRate_eq_sum_map (rates : NeutralRates Deme Locus Allele)
    (ξ η : Multiset (PartialType Deme Locus Allele)) :
    jumpRate rates ξ η =
      ((dualTransitions rates ξ).map fun t ↦ t.1 * (if t.2 = some η then 1 else 0)).sum := by
  unfold jumpRate
  congr 1
  refine Multiset.map_congr rfl fun t _ ↦ ?_
  split_ifs <;> simp

/-- The exit rate is a weighted sum over the dual transitions, with unit weight. -/
theorem exitRate_eq_sum_map (rates : NeutralRates Deme Locus Allele)
    (ξ : Multiset (PartialType Deme Locus Allele)) :
    exitRate rates ξ = ((dualTransitions rates ξ).map fun t ↦ t.1 * (fun _ ↦ (1 : ℝ)) t.2).sum := by
  unfold exitRate
  simp only [mul_one]

theorem jumpRate_addNeutralRates (first second : NeutralRates Deme Locus Allele)
    (ξ η : Multiset (PartialType Deme Locus Allele)) :
    jumpRate (addNeutralRates first second) ξ η = jumpRate first ξ η + jumpRate second ξ η := by
  simp only [jumpRate_eq_sum_map]
  exact sum_map_dualTransitions_add ξ (fun target ↦ if target = some η then 1 else 0) first second

theorem exitRate_addNeutralRates (first second : NeutralRates Deme Locus Allele)
    (ξ : Multiset (PartialType Deme Locus Allele)) :
    exitRate (addNeutralRates first second) ξ = exitRate first ξ + exitRate second ξ := by
  rw [exitRate_eq_sum_map, exitRate_eq_sum_map, exitRate_eq_sum_map]
  exact sum_map_dualTransitions_add ξ (fun _ ↦ 1) first second

theorem jumpRate_scaleNeutralRates (factor : ℝ) (hfactor : 0 ≤ factor)
    (rates : NeutralRates Deme Locus Allele) (ξ η : Multiset (PartialType Deme Locus Allele)) :
    jumpRate (scaleNeutralRates factor hfactor rates) ξ η = factor * jumpRate rates ξ η := by
  simp only [jumpRate_eq_sum_map]
  exact sum_map_dualTransitions_scale ξ (fun target ↦ if target = some η then 1 else 0) factor
    hfactor rates

theorem exitRate_scaleNeutralRates (factor : ℝ) (hfactor : 0 ≤ factor)
    (rates : NeutralRates Deme Locus Allele) (ξ : Multiset (PartialType Deme Locus Allele)) :
    exitRate (scaleNeutralRates factor hfactor rates) ξ = factor * exitRate rates ξ := by
  rw [exitRate_eq_sum_map, exitRate_eq_sum_map]
  exact sum_map_dualTransitions_scale ξ (fun _ ↦ 1) factor hfactor rates

/-- **The dual generator of a sum of rate laws is the sum of the dual generators.** -/
theorem dualGenerator_addNeutralRates (first second : NeutralRates Deme Locus Allele)
    (capacity : Locus → ℕ) :
    dualGenerator (addNeutralRates first second) capacity =
      dualGenerator first capacity + dualGenerator second capacity := by
  ext ξ η
  simp only [dualGenerator, Matrix.add_apply, jumpRate_addNeutralRates, exitRate_addNeutralRates]
  split_ifs <;> ring

/-- **The dual generator of a scaled rate law is the scaled dual generator.** -/
theorem dualGenerator_scaleNeutralRates (factor : ℝ) (hfactor : 0 ≤ factor)
    (rates : NeutralRates Deme Locus Allele) (capacity : Locus → ℕ) :
    dualGenerator (scaleNeutralRates factor hfactor rates) capacity =
      factor • dualGenerator rates capacity := by
  ext ξ η
  simp only [dualGenerator, Matrix.smul_apply, smul_eq_mul, jumpRate_scaleNeutralRates,
    exitRate_scaleNeutralRates]
  split_ifs <;> ring

/-! ## The linear extension to signed rate coordinates -/

section Signed

/-- Signed rate coordinates of the neutral model: coalescence, migration, recombination and
mutation rates as unconstrained real tuples, with the sup norm. -/
abbrev NeutralRateCoordinates (Deme Locus : Type*) (Allele : Locus → Type*) :=
  (Deme → ℝ) × (Deme → Deme → ℝ) × ((Locus → Bool) → ℝ) × (∀ ℓ, Allele ℓ → Allele ℓ → ℝ)

/-- The rate coordinates of a neutral rate law. -/
def neutralRateCoordinates (rates : NeutralRates Deme Locus Allele) :
    NeutralRateCoordinates Deme Locus Allele :=
  (rates.coalescence, rates.migration, rates.recombination, rates.mutation)

/-- Two neutral rate laws with the same rate fields are equal. -/
theorem neutralRates_eq_of_fields {first second : NeutralRates Deme Locus Allele}
    (hcoalescence : first.coalescence = second.coalescence)
    (hmigration : first.migration = second.migration)
    (hrecombination : first.recombination = second.recombination)
    (hmutation : first.mutation = second.mutation) : first = second := by
  cases first
  cases second
  simp only [NeutralRates.mk.injEq]
  exact ⟨hcoalescence, hmigration, hrecombination, hmutation⟩

/-- The symmetric part of a signed mutation tuple: the average over the two orientations. -/
def symmetrizeMutation (mutation : ∀ ℓ, Allele ℓ → Allele ℓ → ℝ) :
    ∀ ℓ, Allele ℓ → Allele ℓ → ℝ :=
  fun ℓ a b ↦ (mutation ℓ a b + mutation ℓ b a) / 2

theorem symmetrizeMutation_add (first second : ∀ ℓ, Allele ℓ → Allele ℓ → ℝ) :
    symmetrizeMutation (first + second) = symmetrizeMutation first + symmetrizeMutation second := by
  funext ℓ a b
  simp only [symmetrizeMutation, Pi.add_apply]
  ring

theorem symmetrizeMutation_neg (mutation : ∀ ℓ, Allele ℓ → Allele ℓ → ℝ) :
    symmetrizeMutation (-mutation) = -symmetrizeMutation mutation := by
  funext ℓ a b
  simp only [symmetrizeMutation, Pi.neg_apply]
  ring

theorem symmetrizeMutation_smul (factor : ℝ) (mutation : ∀ ℓ, Allele ℓ → Allele ℓ → ℝ) :
    symmetrizeMutation (factor • mutation) = factor • symmetrizeMutation mutation := by
  funext ℓ a b
  simp only [symmetrizeMutation, Pi.smul_apply, smul_eq_mul]
  ring

/-- The neutral rate law carrying the positive parts of a signed tuple, every mutation rate
symmetrized over its two orientations before it is clipped at zero. -/
def positivePartNeutralRates (x : NeutralRateCoordinates Deme Locus Allele) :
    NeutralRates Deme Locus Allele where
  coalescence i := max (x.1 i) 0
  migration i j := max (x.2.1 i j) 0
  recombination selector := max (x.2.2.1 selector) 0
  mutation ℓ a b := max (symmetrizeMutation x.2.2.2 ℓ a b) 0
  coalescence_nonneg _ := le_max_right _ _
  migration_nonneg _ _ := le_max_right _ _
  recombination_nonneg _ := le_max_right _ _
  mutation_nonneg _ _ _ := le_max_right _ _
  mutation_symm ℓ a b := by simp only [symmetrizeMutation, add_comm]

/-- The positive parts of a sum balance against the positive parts of the summands. -/
theorem addNeutralRates_positivePart_add (x y : NeutralRateCoordinates Deme Locus Allele) :
    addNeutralRates (positivePartNeutralRates (x + y))
        (addNeutralRates (positivePartNeutralRates (-x)) (positivePartNeutralRates (-y))) =
      addNeutralRates (addNeutralRates (positivePartNeutralRates x) (positivePartNeutralRates y))
        (positivePartNeutralRates (-(x + y))) := by
  apply neutralRates_eq_of_fields
  · funext i
    simp only [addNeutralRates, positivePartNeutralRates, Prod.fst_add, Prod.fst_neg,
      Pi.add_apply, Pi.neg_apply]
    linarith [rate_positivePart_sub_negativePart (x.1 i),
      rate_positivePart_sub_negativePart (y.1 i),
      rate_positivePart_sub_negativePart (x.1 i + y.1 i)]
  · funext i j
    simp only [addNeutralRates, positivePartNeutralRates, Prod.fst_add, Prod.snd_add,
      Prod.fst_neg, Prod.snd_neg, Pi.add_apply, Pi.neg_apply]
    linarith [rate_positivePart_sub_negativePart (x.2.1 i j),
      rate_positivePart_sub_negativePart (y.2.1 i j),
      rate_positivePart_sub_negativePart (x.2.1 i j + y.2.1 i j)]
  · funext selector
    simp only [addNeutralRates, positivePartNeutralRates, Prod.fst_add, Prod.snd_add,
      Prod.fst_neg, Prod.snd_neg, Pi.add_apply, Pi.neg_apply]
    linarith [rate_positivePart_sub_negativePart (x.2.2.1 selector),
      rate_positivePart_sub_negativePart (y.2.2.1 selector),
      rate_positivePart_sub_negativePart (x.2.2.1 selector + y.2.2.1 selector)]
  · funext ℓ a b
    simp only [addNeutralRates, positivePartNeutralRates, Prod.snd_add, Prod.snd_neg,
      symmetrizeMutation_add, symmetrizeMutation_neg, Pi.add_apply, Pi.neg_apply]
    linarith [rate_positivePart_sub_negativePart (symmetrizeMutation x.2.2.2 ℓ a b),
      rate_positivePart_sub_negativePart (symmetrizeMutation y.2.2.2 ℓ a b),
      rate_positivePart_sub_negativePart
        (symmetrizeMutation x.2.2.2 ℓ a b + symmetrizeMutation y.2.2.2 ℓ a b)]

/-- The positive parts of a positive multiple balance against the scaled positive parts. -/
theorem addNeutralRates_positivePart_smul {factor : ℝ} (hfactor : 0 < factor)
    (x : NeutralRateCoordinates Deme Locus Allele) :
    addNeutralRates (positivePartNeutralRates (factor • x))
        (scaleNeutralRates factor hfactor.le (positivePartNeutralRates (-x))) =
      addNeutralRates (scaleNeutralRates factor hfactor.le (positivePartNeutralRates x))
        (positivePartNeutralRates (-(factor • x))) := by
  apply neutralRates_eq_of_fields
  · funext i
    simp only [addNeutralRates, scaleNeutralRates, positivePartNeutralRates, Prod.smul_fst,
      Prod.fst_neg, Pi.smul_apply, Pi.neg_apply, smul_eq_mul]
    linear_combination rate_positivePart_sub_negativePart (factor * x.1 i) -
      factor * rate_positivePart_sub_negativePart (x.1 i)
  · funext i j
    simp only [addNeutralRates, scaleNeutralRates, positivePartNeutralRates, Prod.smul_fst,
      Prod.smul_snd, Prod.fst_neg, Prod.snd_neg, Pi.smul_apply, Pi.neg_apply, smul_eq_mul]
    linear_combination rate_positivePart_sub_negativePart (factor * x.2.1 i j) -
      factor * rate_positivePart_sub_negativePart (x.2.1 i j)
  · funext selector
    simp only [addNeutralRates, scaleNeutralRates, positivePartNeutralRates, Prod.smul_fst,
      Prod.smul_snd, Prod.fst_neg, Prod.snd_neg, Pi.smul_apply, Pi.neg_apply, smul_eq_mul]
    linear_combination rate_positivePart_sub_negativePart (factor * x.2.2.1 selector) -
      factor * rate_positivePart_sub_negativePart (x.2.2.1 selector)
  · funext ℓ a b
    simp only [addNeutralRates, scaleNeutralRates, positivePartNeutralRates, Prod.smul_snd,
      Prod.snd_neg, symmetrizeMutation_smul, symmetrizeMutation_neg, Pi.smul_apply, Pi.neg_apply,
      smul_eq_mul]
    linear_combination rate_positivePart_sub_negativePart
        (factor * symmetrizeMutation x.2.2.2 ℓ a b) -
      factor * rate_positivePart_sub_negativePart (symmetrizeMutation x.2.2.2 ℓ a b)

/-- Rate laws balancing in sum have balancing dual generator differences: if `first + fourth` and
`third + second` are one law, then `Q(first) - Q(second) = Q(third) - Q(fourth)`. -/
theorem dualGenerator_sub_eq_of_add_eq (capacity : Locus → ℕ)
    {first second third fourth : NeutralRates Deme Locus Allele}
    (hbalance : addNeutralRates first fourth = addNeutralRates third second) :
    dualGenerator first capacity - dualGenerator second capacity =
      dualGenerator third capacity - dualGenerator fourth capacity := by
  have hsum := congrArg (fun rates ↦ dualGenerator rates capacity) hbalance
  simp only [dualGenerator_addNeutralRates] at hsum
  exact sub_eq_sub_iff_add_eq_add.mpr hsum

/-- The dual generator extended to signed rate coordinates: the generator of the positive part of
the tuple minus the generator of the positive part of its negation. -/
def signedDualGenerator (capacity : Locus → ℕ) (x : NeutralRateCoordinates Deme Locus Allele) :
    Matrix (BudgetConfiguration Deme Locus Allele capacity)
      (BudgetConfiguration Deme Locus Allele capacity) ℝ :=
  dualGenerator (positivePartNeutralRates x) capacity -
    dualGenerator (positivePartNeutralRates (-x)) capacity

theorem signedDualGenerator_add (capacity : Locus → ℕ)
    (x y : NeutralRateCoordinates Deme Locus Allele) :
    signedDualGenerator capacity (x + y) =
      signedDualGenerator capacity x + signedDualGenerator capacity y := by
  have hbalance := dualGenerator_sub_eq_of_add_eq capacity (addNeutralRates_positivePart_add x y)
  unfold signedDualGenerator
  rw [hbalance, dualGenerator_addNeutralRates, dualGenerator_addNeutralRates]
  abel

theorem signedDualGenerator_neg (capacity : Locus → ℕ)
    (x : NeutralRateCoordinates Deme Locus Allele) :
    signedDualGenerator capacity (-x) = -signedDualGenerator capacity x := by
  unfold signedDualGenerator
  rw [neg_neg, neg_sub]

theorem signedDualGenerator_smul_of_pos (capacity : Locus → ℕ) {factor : ℝ}
    (hfactor : 0 < factor) (x : NeutralRateCoordinates Deme Locus Allele) :
    signedDualGenerator capacity (factor • x) = factor • signedDualGenerator capacity x := by
  have hbalance := dualGenerator_sub_eq_of_add_eq capacity
    (addNeutralRates_positivePart_smul hfactor x)
  unfold signedDualGenerator
  rw [hbalance, dualGenerator_scaleNeutralRates, dualGenerator_scaleNeutralRates, smul_sub]

theorem signedDualGenerator_smul (capacity : Locus → ℕ) (factor : ℝ)
    (x : NeutralRateCoordinates Deme Locus Allele) :
    signedDualGenerator capacity (factor • x) = factor • signedDualGenerator capacity x := by
  rcases lt_trichotomy factor 0 with hbelow | hat | habove
  · have hflip : factor • x = (-factor) • (-x) := by rw [neg_smul, smul_neg, neg_neg]
    rw [hflip, signedDualGenerator_smul_of_pos capacity (neg_pos.mpr hbelow),
      signedDualGenerator_neg, neg_smul, smul_neg, neg_neg]
  · subst hat
    rw [zero_smul, zero_smul]
    unfold signedDualGenerator
    rw [neg_zero, sub_self]
  · exact signedDualGenerator_smul_of_pos capacity habove x

/-- The dual generator as a linear map on signed rate coordinates. -/
def dualGeneratorLinearMap (capacity : Locus → ℕ) :
    NeutralRateCoordinates Deme Locus Allele →ₗ[ℝ]
      Matrix (BudgetConfiguration Deme Locus Allele capacity)
        (BudgetConfiguration Deme Locus Allele capacity) ℝ where
  toFun := signedDualGenerator capacity
  map_add' := signedDualGenerator_add capacity
  map_smul' := signedDualGenerator_smul capacity

/-- The positive part of the coordinates of a rate law is the law itself. -/
theorem positivePartNeutralRates_coordinates (rates : NeutralRates Deme Locus Allele) :
    positivePartNeutralRates (neutralRateCoordinates rates) = rates := by
  apply neutralRates_eq_of_fields
  · funext i
    exact max_eq_left (rates.coalescence_nonneg i)
  · funext i j
    exact max_eq_left (rates.migration_nonneg i j)
  · funext selector
    exact max_eq_left (rates.recombination_nonneg selector)
  · funext ℓ a b
    show max ((rates.mutation ℓ a b + rates.mutation ℓ b a) / 2) 0 = rates.mutation ℓ a b
    rw [← rates.mutation_symm ℓ a b, add_self_div_two, max_eq_left (rates.mutation_nonneg ℓ a b)]

/-- The positive part of the negated coordinates of a rate law is the zero law. -/
theorem positivePartNeutralRates_neg_coordinates (rates : NeutralRates Deme Locus Allele) :
    positivePartNeutralRates (-neutralRateCoordinates rates) =
      scaleNeutralRates 0 le_rfl rates := by
  apply neutralRates_eq_of_fields
  · funext i
    show max (-rates.coalescence i) 0 = 0 * rates.coalescence i
    rw [max_eq_right (neg_nonpos.mpr (rates.coalescence_nonneg i)), zero_mul]
  · funext i j
    show max (-rates.migration i j) 0 = 0 * rates.migration i j
    rw [max_eq_right (neg_nonpos.mpr (rates.migration_nonneg i j)), zero_mul]
  · funext selector
    show max (-rates.recombination selector) 0 = 0 * rates.recombination selector
    rw [max_eq_right (neg_nonpos.mpr (rates.recombination_nonneg selector)), zero_mul]
  · funext ℓ a b
    show max ((-rates.mutation ℓ a b + -rates.mutation ℓ b a) / 2) 0 = 0 * rates.mutation ℓ a b
    rw [max_eq_right (by linarith [rates.mutation_nonneg ℓ a b, rates.mutation_nonneg ℓ b a]),
      zero_mul]

/-- **The dual generator is the linear map at the rate coordinates.** -/
theorem dualGenerator_eq_dualGeneratorLinearMap (rates : NeutralRates Deme Locus Allele)
    (capacity : Locus → ℕ) :
    dualGenerator rates capacity =
      dualGeneratorLinearMap capacity (neutralRateCoordinates rates) := by
  show dualGenerator rates capacity = signedDualGenerator capacity (neutralRateCoordinates rates)
  unfold signedDualGenerator
  rw [positivePartNeutralRates_coordinates, positivePartNeutralRates_neg_coordinates,
    dualGenerator_scaleNeutralRates, zero_smul, sub_zero]

open scoped Matrix.Norms.Operator in
/-- **The dual generator is Lipschitz in the rates.** One constant bounds the operator norm of the
dual generator difference of two rate laws by the sup norm of their rate coordinate difference. -/
theorem exists_dualGenerator_lipschitz (capacity : Locus → ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ first second : NeutralRates Deme Locus Allele,
      ‖dualGenerator first capacity - dualGenerator second capacity‖ ≤
        K * ‖neutralRateCoordinates first - neutralRateCoordinates second‖ := by
  let bounded := LinearMap.toContinuousLinearMap
    (dualGeneratorLinearMap (Deme := Deme) (Allele := Allele) capacity)
  refine ⟨‖bounded‖, norm_nonneg _, fun first second ↦ ?_⟩
  rw [dualGenerator_eq_dualGeneratorLinearMap, dualGenerator_eq_dualGeneratorLinearMap, ← map_sub]
  exact bounded.le_opNorm _

end Signed

end

end Descent.Portability.NeutralRateLipschitz
