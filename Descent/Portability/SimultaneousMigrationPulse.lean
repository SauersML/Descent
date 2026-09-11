/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.TwoLocusMicroscopicKernel

assert_below Descent.Decision Descent.Program

/-!
# The simultaneous migration stage

NOTE1 section 2.3 opens one microscopic step with a deterministic convex haplotype mixture
with migration fractions `h m_ij`: every recipient deme replaces the fraction `h m_ij` of its
haplotype vector by the haplotype vector of every source deme `j`, all recipients at once and
all from the state before the stage.  The corpus's pulse package moves one ordered pair at a
time (`PulseJetExpansion.migrationPulse`).  This module builds the simultaneous stage and
proves that its first-order velocity on every enlarged coordinate is exactly the sum of the
per-pair migration stage drifts, which is what lets it replace the per-pair stages in a
composed step.

The stage.  `migrantMixture` is the recipient's new haplotype vector, a convex combination of
all demes' vectors with weights `pulseFraction tau · m_ij / (1 + M)` (`migrationWeight`), where
`M` is the total migration rate `totalMigration`.  Dividing by `1 + M` keeps the recipient's own
weight nonnegative at every parameter in `[0, 1]`, so the stage is a genuine haplotype law with
no clamp inside the certificate range; a stage kernel runs it at rate `1 + M`, which restores
the literal fractions `h m_ij` for small `h`.  `simultaneousMigrationPulse_leftFrequency`,
`_rightFrequency` and `_linkage` are its exact laws: the marginals move linearly, and the
linkage determinant moves by the summed pair velocities plus an explicit quadratic term, which
`linkage_eq_AB_sub_marginals` makes computable.  `simultaneousMigrationCoordinateExpansion`
carries the three base certificates, each velocity written as a share-weighted sum of the
corpus's per-pair base velocities.

Velocities are linear in the base velocities.  `enlargedTreeVelocity` writes the first-order
coefficient of every enlarged coordinate as an explicit linear form in the base velocities of
the two marginals and the linkage determinant of each deme.  `enlargedPulseExpansion_velocity`
shows that the corpus's Leibniz-built certificates have exactly that velocity, and
`enlargedTreeVelocity_sum` that the form commutes with finite weighted sums.  Together they
give `simultaneousMigrationExpansion_velocity`: at rate `1 + M` the simultaneous stage advances
every enlarged coordinate by the sum over ordered pairs of the corpus's rate-weighted migration
stage drifts.

## Empirical status

None.  The bodies here are algebra: convex combinations of haplotype vectors and polynomial
identities between their coordinates, so no measurement can bear on them.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.SimultaneousMigrationPulse

open Coalescent
open Coalescent.TwoLocusHaplotypeFrequencies
open Descent.Portability.PulseJetExpansion
open Descent.Portability.PulseStageKernel
open Descent.Portability.EnlargedLowOrderLDGenerator
open Descent.Portability.TwoLocusMicroscopicKernel

noncomputable section

/-! ## Linkage in excess form -/

/-- The linkage determinant is the excess of the `AB` haplotype over the product of the two
marginal allele frequencies, because the four frequencies sum to one. -/
theorem linkage_eq_AB_sub_marginals (frequency : TwoLocusHaplotypeFrequencies) :
    frequency.linkage =
      frequency.AB - frequency.leftFrequency * frequency.rightFrequency := by
  simp only [TwoLocusHaplotypeFrequencies.linkage, TwoLocusHaplotypeFrequencies.leftFrequency,
    TwoLocusHaplotypeFrequencies.rightFrequency]
  linear_combination frequency.AB * frequency.total_eq_one

/-! ## Migration shares and weights -/

/-- The total migration rate over all ordered deme pairs. -/
def totalMigration {D : ℕ} (rates : ManyDemeLDRates D) : ℝ :=
  ∑ recipient : Fin D, ∑ source : Fin D, rates.migration recipient source

/-- The total migration rate is nonnegative. -/
theorem totalMigration_nonneg {D : ℕ} (rates : ManyDemeLDRates D) :
    0 ≤ totalMigration rates :=
  Finset.sum_nonneg fun recipient _ ↦ Finset.sum_nonneg fun source _ ↦
    rates.migration_nonneg recipient source

/-- One migration rate into `recipient` normalized by one plus the total migration rate. -/
def migrationShare {D : ℕ} (rates : ManyDemeLDRates D) (recipient source : Fin D) : ℝ :=
  rates.migration recipient source / (1 + totalMigration rates)

/-- Every share is nonnegative. -/
theorem migrationShare_nonneg {D : ℕ} (rates : ManyDemeLDRates D) (recipient source : Fin D) :
    0 ≤ migrationShare rates recipient source :=
  div_nonneg (rates.migration_nonneg recipient source) (by linarith [totalMigration_nonneg rates])

/-- The shares into one recipient sum to at most one. -/
theorem sum_migrationShare_le_one {D : ℕ} (rates : ManyDemeLDRates D) (recipient : Fin D) :
    ∑ source, migrationShare rates recipient source ≤ 1 := by
  have hpos : 0 < 1 + totalMigration rates := by linarith [totalMigration_nonneg rates]
  have hrow : ∑ source, rates.migration recipient source ≤ totalMigration rates :=
    Finset.single_le_sum (f := fun other ↦ ∑ source, rates.migration other source)
      (fun other _ ↦ Finset.sum_nonneg fun source _ ↦ rates.migration_nonneg other source)
      (Finset.mem_univ recipient)
  simp only [migrationShare, ← Finset.sum_div]
  rw [div_le_one hpos]
  linarith

/-- The shares over all ordered pairs sum to at most one. -/
theorem sum_pair_migrationShare_le_one {D : ℕ} (rates : ManyDemeLDRates D) :
    ∑ pair : Fin D × Fin D, migrationShare rates pair.2 pair.1 ≤ 1 := by
  have hpos : 0 < 1 + totalMigration rates := by linarith [totalMigration_nonneg rates]
  have htotal : ∑ pair : Fin D × Fin D, rates.migration pair.2 pair.1 = totalMigration rates := by
    rw [Fintype.sum_prod_type, Finset.sum_comm]
    rfl
  simp only [migrationShare, ← Finset.sum_div, htotal]
  rw [div_le_one hpos]
  linarith

/-- The weight a recipient takes from one deme at parameter `tau`. -/
def migrationWeight {D : ℕ} (rates : ManyDemeLDRates D) (tau : ℝ) (recipient source : Fin D) :
    ℝ :=
  pulseFraction tau * migrationShare rates recipient source

/-- Every weight is nonnegative. -/
theorem migrationWeight_nonneg {D : ℕ} (rates : ManyDemeLDRates D) (tau : ℝ)
    (recipient source : Fin D) : 0 ≤ migrationWeight rates tau recipient source :=
  mul_nonneg (pulseFraction_nonneg tau) (migrationShare_nonneg rates recipient source)

/-- The weight a recipient keeps for its own haplotype vector. -/
def retainedWeight {D : ℕ} (rates : ManyDemeLDRates D) (tau : ℝ) (recipient : Fin D) : ℝ :=
  1 - ∑ source, migrationWeight rates tau recipient source

/-- The retained weight is nonnegative. -/
theorem retainedWeight_nonneg {D : ℕ} (rates : ManyDemeLDRates D) (tau : ℝ)
    (recipient : Fin D) : 0 ≤ retainedWeight rates tau recipient := by
  have hshares := sum_migrationShare_le_one rates recipient
  have hsharesNonneg : 0 ≤ ∑ source, migrationShare rates recipient source :=
    Finset.sum_nonneg fun source _ ↦ migrationShare_nonneg rates recipient source
  have hscaled : pulseFraction tau * ∑ source, migrationShare rates recipient source ≤
      1 * ∑ source, migrationShare rates recipient source :=
    mul_le_mul_of_nonneg_right (pulseFraction_le_one tau) hsharesNonneg
  simp only [retainedWeight, migrationWeight, ← Finset.mul_sum]
  linarith

/-! ## The stage -/

/-- The haplotype vector of one recipient after the simultaneous migration stage at parameter
`tau`: it keeps its retained weight of its own vector and takes `migrationWeight` from every
deme's vector. -/
def migrantMixture {D : ℕ} (rates : ManyDemeLDRates D) (tau : ℝ)
    (state : DemeHaplotypeState D) (recipient : Fin D) : TwoLocusHaplotypeFrequencies where
  AB := retainedWeight rates tau recipient * (state recipient).AB +
    ∑ source, migrationWeight rates tau recipient source * (state source).AB
  Ab := retainedWeight rates tau recipient * (state recipient).Ab +
    ∑ source, migrationWeight rates tau recipient source * (state source).Ab
  aB := retainedWeight rates tau recipient * (state recipient).aB +
    ∑ source, migrationWeight rates tau recipient source * (state source).aB
  ab := retainedWeight rates tau recipient * (state recipient).ab +
    ∑ source, migrationWeight rates tau recipient source * (state source).ab
  AB_nonneg := add_nonneg
    (mul_nonneg (retainedWeight_nonneg rates tau recipient) (state recipient).AB_nonneg)
    (Finset.sum_nonneg fun source _ ↦
      mul_nonneg (migrationWeight_nonneg rates tau recipient source) (state source).AB_nonneg)
  Ab_nonneg := add_nonneg
    (mul_nonneg (retainedWeight_nonneg rates tau recipient) (state recipient).Ab_nonneg)
    (Finset.sum_nonneg fun source _ ↦
      mul_nonneg (migrationWeight_nonneg rates tau recipient source) (state source).Ab_nonneg)
  aB_nonneg := add_nonneg
    (mul_nonneg (retainedWeight_nonneg rates tau recipient) (state recipient).aB_nonneg)
    (Finset.sum_nonneg fun source _ ↦
      mul_nonneg (migrationWeight_nonneg rates tau recipient source) (state source).aB_nonneg)
  ab_nonneg := add_nonneg
    (mul_nonneg (retainedWeight_nonneg rates tau recipient) (state recipient).ab_nonneg)
    (Finset.sum_nonneg fun source _ ↦
      mul_nonneg (migrationWeight_nonneg rates tau recipient source) (state source).ab_nonneg)
  total_eq_one := by
    have hsum : ∑ source, migrationWeight rates tau recipient source * (state source).AB +
        ∑ source, migrationWeight rates tau recipient source * (state source).Ab +
        ∑ source, migrationWeight rates tau recipient source * (state source).aB +
        ∑ source, migrationWeight rates tau recipient source * (state source).ab =
        ∑ source, migrationWeight rates tau recipient source := by
      rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun source _ ↦ by
        linear_combination migrationWeight rates tau recipient source * (state source).total_eq_one
    simp only [retainedWeight]
    linear_combination (1 - ∑ source, migrationWeight rates tau recipient source) *
      (state recipient).total_eq_one + hsum

/-- The simultaneous migration stage of NOTE1 section 2.3 at parameter `tau`: every recipient
mixes in the vectors of all demes at once, from the state before the stage. -/
def simultaneousMigrationPulse {D : ℕ} (rates : ManyDemeLDRates D) (tau : ℝ)
    (state : DemeHaplotypeState D) : DemeHaplotypeState D :=
  fun recipient ↦ migrantMixture rates tau state recipient

/-- Keeping the rest of a unit weight and taking `weight j` of `other j` is the own value plus
the weighted differences. -/
theorem retainedMixture_eq_add_weightedDifferences {D : ℕ} (weight other : Fin D → ℝ)
    (own : ℝ) :
    (1 - ∑ source, weight source) * own + ∑ source, weight source * other source =
      own + ∑ source, weight source * (other source - own) := by
  simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul]
  ring

/-- One haplotype coordinate after the stage is the recipient's coordinate plus `tau` times the
share-weighted differences. -/
theorem migrantMixture_coordinate {D : ℕ} (rates : ManyDemeLDRates D) {tau : ℝ} (h0 : 0 ≤ tau)
    (h1 : tau ≤ 1) (coordinate : TwoLocusHaplotypeFrequencies → ℝ) (index : Fin D)
    (state : DemeHaplotypeState D) :
    retainedWeight rates tau index * coordinate (state index) +
        ∑ source, migrationWeight rates tau index source * coordinate (state source) =
      coordinate (state index) + tau * ∑ source, migrationShare rates index source *
        (coordinate (state source) - coordinate (state index)) := by
  simp only [retainedWeight]
  rw [retainedMixture_eq_add_weightedDifferences, Finset.mul_sum]
  congr 1
  exact Finset.sum_congr rfl fun source _ ↦ by
    simp only [migrationWeight, pulseFraction_eq_self h0 h1]
    ring

/-- **The left marginals move linearly** by `tau` times the share-weighted source differences. -/
theorem simultaneousMigrationPulse_leftFrequency {D : ℕ} (rates : ManyDemeLDRates D) {tau : ℝ}
    (h0 : 0 ≤ tau) (h1 : tau ≤ 1) (state : DemeHaplotypeState D) (index : Fin D) :
    (simultaneousMigrationPulse rates tau state index).leftFrequency =
      (state index).leftFrequency + tau * ∑ source, migrationShare rates index source *
        ((state source).leftFrequency - (state index).leftFrequency) := by
  have hAB := migrantMixture_coordinate rates h0 h1 TwoLocusHaplotypeFrequencies.AB index state
  have hAb := migrantMixture_coordinate rates h0 h1 TwoLocusHaplotypeFrequencies.Ab index state
  have hsum : ∑ source, migrationShare rates index source *
        ((state source).AB - (state index).AB) +
      ∑ source, migrationShare rates index source * ((state source).Ab - (state index).Ab) =
      ∑ source, migrationShare rates index source *
        ((state source).leftFrequency - (state index).leftFrequency) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun source _ ↦ by
      simp only [TwoLocusHaplotypeFrequencies.leftFrequency]
      ring
  simp only [simultaneousMigrationPulse, migrantMixture, TwoLocusHaplotypeFrequencies.leftFrequency]
  simp only [TwoLocusHaplotypeFrequencies.leftFrequency] at hsum
  linear_combination hAB + hAb + tau * hsum

/-- **The right marginals move linearly** by `tau` times the share-weighted source
differences. -/
theorem simultaneousMigrationPulse_rightFrequency {D : ℕ} (rates : ManyDemeLDRates D)
    {tau : ℝ} (h0 : 0 ≤ tau) (h1 : tau ≤ 1) (state : DemeHaplotypeState D) (index : Fin D) :
    (simultaneousMigrationPulse rates tau state index).rightFrequency =
      (state index).rightFrequency + tau * ∑ source, migrationShare rates index source *
        ((state source).rightFrequency - (state index).rightFrequency) := by
  have hAB := migrantMixture_coordinate rates h0 h1 TwoLocusHaplotypeFrequencies.AB index state
  have haB := migrantMixture_coordinate rates h0 h1 TwoLocusHaplotypeFrequencies.aB index state
  have hsum : ∑ source, migrationShare rates index source *
        ((state source).AB - (state index).AB) +
      ∑ source, migrationShare rates index source * ((state source).aB - (state index).aB) =
      ∑ source, migrationShare rates index source *
        ((state source).rightFrequency - (state index).rightFrequency) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun source _ ↦ by
      simp only [TwoLocusHaplotypeFrequencies.rightFrequency]
      ring
  simp only [simultaneousMigrationPulse, migrantMixture,
    TwoLocusHaplotypeFrequencies.rightFrequency]
  simp only [TwoLocusHaplotypeFrequencies.rightFrequency] at hsum
  linear_combination hAB + haB + tau * hsum

/-- **The linkage determinant moves by the summed pair velocities** plus the product of the two
marginal displacements, a term of order `tau²`. -/
theorem simultaneousMigrationPulse_linkage {D : ℕ} (rates : ManyDemeLDRates D) {tau : ℝ}
    (h0 : 0 ≤ tau) (h1 : tau ≤ 1) (state : DemeHaplotypeState D) (index : Fin D) :
    (simultaneousMigrationPulse rates tau state index).linkage =
      (state index).linkage +
        tau * ∑ source, migrationShare rates index source *
          migrationLinkageVelocity (state source) (state index) -
        tau ^ 2 * (∑ source, migrationShare rates index source *
            ((state source).leftFrequency - (state index).leftFrequency)) *
          (∑ source, migrationShare rates index source *
            ((state source).rightFrequency - (state index).rightFrequency)) := by
  have hleft := simultaneousMigrationPulse_leftFrequency rates h0 h1 state index
  have hright := simultaneousMigrationPulse_rightFrequency rates h0 h1 state index
  have hAB : (simultaneousMigrationPulse rates tau state index).AB =
      (state index).AB + tau * ∑ source, migrationShare rates index source *
        ((state source).AB - (state index).AB) :=
    migrantMixture_coordinate rates h0 h1 TwoLocusHaplotypeFrequencies.AB index state
  have hterm : ∑ source, migrationShare rates index source *
        ((state source).AB - (state index).AB) -
      (state index).leftFrequency * ∑ source, migrationShare rates index source *
        ((state source).rightFrequency - (state index).rightFrequency) -
      (state index).rightFrequency * ∑ source, migrationShare rates index source *
        ((state source).leftFrequency - (state index).leftFrequency) =
      ∑ source, migrationShare rates index source *
        migrationLinkageVelocity (state source) (state index) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun source _ ↦ ?_
    simp only [TwoLocusHaplotypeFrequencies.migrationLinkageVelocity]
    rw [linkage_eq_AB_sub_marginals (state source), linkage_eq_AB_sub_marginals (state index)]
    ring
  rw [linkage_eq_AB_sub_marginals (simultaneousMigrationPulse rates tau state index), hAB, hleft,
    hright, linkage_eq_AB_sub_marginals (state index)]
  linear_combination tau * hterm

/-! ## Base certificates -/

/-- A share-weighted sum over ordered pairs of an increment that only the recipient carries is
the share-weighted sum over sources into that recipient. -/
theorem sum_pair_recipient {D : ℕ} (weight increment : Fin D → Fin D → ℝ) (index : Fin D) :
    ∑ pair : Fin D × Fin D,
        weight pair.2 pair.1 * (if index = pair.2 then increment pair.1 pair.2 else 0) =
      ∑ source, weight index source * increment source index := by
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun source _ ↦ ?_
  simp only [mul_ite, mul_zero]
  rw [Finset.sum_ite_eq]
  simp

/-- A share-weighted sum over pairs of uniformly bounded terms is bounded by the same constant. -/
theorem abs_pairShareSum_le {D : ℕ} (rates : ManyDemeLDRates D) (term : Fin D × Fin D → ℝ)
    (bound : ℝ) (hboundNonneg : 0 ≤ bound) (hterm : ∀ pair, |term pair| ≤ bound) :
    |∑ pair : Fin D × Fin D, migrationShare rates pair.2 pair.1 * term pair| ≤ bound := by
  calc |∑ pair : Fin D × Fin D, migrationShare rates pair.2 pair.1 * term pair|
      ≤ ∑ pair : Fin D × Fin D, |migrationShare rates pair.2 pair.1 * term pair| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ pair : Fin D × Fin D, migrationShare rates pair.2 pair.1 * bound :=
        Finset.sum_le_sum fun pair _ ↦ by
          rw [abs_mul, abs_of_nonneg (migrationShare_nonneg rates pair.2 pair.1)]
          exact mul_le_mul_of_nonneg_left (hterm pair) (migrationShare_nonneg rates _ _)
    _ = (∑ pair : Fin D × Fin D, migrationShare rates pair.2 pair.1) * bound := by
        rw [Finset.sum_mul]
    _ ≤ 1 * bound := mul_le_mul_of_nonneg_right (sum_pair_migrationShare_le_one rates)
        hboundNonneg
    _ = bound := one_mul bound

/-- A share-weighted sum over the sources into one recipient of terms of size at most one has
size at most one. -/
theorem abs_recipientShareSum_le_one {D : ℕ} (rates : ManyDemeLDRates D) (index : Fin D)
    (term : Fin D → ℝ) (hterm : ∀ source, |term source| ≤ 1) :
    |∑ source, migrationShare rates index source * term source| ≤ 1 := by
  calc |∑ source, migrationShare rates index source * term source|
      ≤ ∑ source, |migrationShare rates index source * term source| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ source, migrationShare rates index source * 1 :=
        Finset.sum_le_sum fun source _ ↦ by
          rw [abs_mul, abs_of_nonneg (migrationShare_nonneg rates index source)]
          exact mul_le_mul_of_nonneg_left (hterm source) (migrationShare_nonneg rates _ _)
    _ = ∑ source, migrationShare rates index source := by simp
    _ ≤ 1 := sum_migrationShare_le_one rates index

/-- The left marginal under the simultaneous stage: velocity the share-weighted sum of the
corpus's per-pair left velocities, no remainder. -/
def simultaneousMigrationLeftExpansion {D : ℕ} (rates : ManyDemeLDRates D) (index : Fin D) :
    PulseExpansion (simultaneousMigrationPulse rates)
      (fun state ↦ (state index).leftFrequency) where
  velocity state := ∑ pair : Fin D × Fin D, migrationShare rates pair.2 pair.1 *
    (migrationLeftExpansion pair.1 pair.2 index).velocity state
  valueBound := 1
  velocityBound := 1
  remainder := 0
  value_abs_le state :=
    abs_le.mpr ⟨by linarith [(state index).leftFrequency_nonneg],
      (state index).leftFrequency_le_one⟩
  velocity_abs_le state := abs_pairShareSum_le rates _ 1 zero_le_one fun pair ↦
    (migrationLeftExpansion pair.1 pair.2 index).velocity_abs_le state
  expansion tau h0 h1 state := by
    have hcollapse : ∑ pair : Fin D × Fin D, migrationShare rates pair.2 pair.1 *
        (migrationLeftExpansion pair.1 pair.2 index).velocity state =
        ∑ source, migrationShare rates index source *
          ((state source).leftFrequency - (state index).leftFrequency) :=
      sum_pair_recipient (migrationShare rates)
        (fun source recipient ↦ (state source).leftFrequency - (state recipient).leftFrequency)
        index
    rw [simultaneousMigrationPulse_leftFrequency rates h0 h1 state index, hcollapse]
    calc _ = |(0 : ℝ)| := by congr 1; ring
      _ ≤ 0 * tau ^ 2 := by simp

/-- The right marginal under the simultaneous stage: velocity the share-weighted sum of the
corpus's per-pair right velocities, no remainder. -/
def simultaneousMigrationRightExpansion {D : ℕ} (rates : ManyDemeLDRates D) (index : Fin D) :
    PulseExpansion (simultaneousMigrationPulse rates)
      (fun state ↦ (state index).rightFrequency) where
  velocity state := ∑ pair : Fin D × Fin D, migrationShare rates pair.2 pair.1 *
    (migrationRightExpansion pair.1 pair.2 index).velocity state
  valueBound := 1
  velocityBound := 1
  remainder := 0
  value_abs_le state :=
    abs_le.mpr ⟨by linarith [(state index).rightFrequency_nonneg],
      (state index).rightFrequency_le_one⟩
  velocity_abs_le state := abs_pairShareSum_le rates _ 1 zero_le_one fun pair ↦
    (migrationRightExpansion pair.1 pair.2 index).velocity_abs_le state
  expansion tau h0 h1 state := by
    have hcollapse : ∑ pair : Fin D × Fin D, migrationShare rates pair.2 pair.1 *
        (migrationRightExpansion pair.1 pair.2 index).velocity state =
        ∑ source, migrationShare rates index source *
          ((state source).rightFrequency - (state index).rightFrequency) :=
      sum_pair_recipient (migrationShare rates)
        (fun source recipient ↦ (state source).rightFrequency - (state recipient).rightFrequency)
        index
    rw [simultaneousMigrationPulse_rightFrequency rates h0 h1 state index, hcollapse]
    calc _ = |(0 : ℝ)| := by congr 1; ring
      _ ≤ 0 * tau ^ 2 := by simp

/-- The linkage determinant under the simultaneous stage: velocity the share-weighted sum of the
corpus's per-pair linkage velocities, quadratic remainder one. -/
def simultaneousMigrationLinkageExpansion {D : ℕ} (rates : ManyDemeLDRates D) (index : Fin D) :
    PulseExpansion (simultaneousMigrationPulse rates) (fun state ↦ (state index).linkage) where
  velocity state := ∑ pair : Fin D × Fin D, migrationShare rates pair.2 pair.1 *
    (migrationLinkageExpansion pair.1 pair.2 index).velocity state
  valueBound := 1 / 4
  velocityBound := 2
  remainder := 1
  value_abs_le state := (state index).linkage_abs_le_quarter
  velocity_abs_le state := abs_pairShareSum_le rates _ 2 (by norm_num) fun pair ↦
    (migrationLinkageExpansion pair.1 pair.2 index).velocity_abs_le state
  expansion tau h0 h1 state := by
    have hcollapse : ∑ pair : Fin D × Fin D, migrationShare rates pair.2 pair.1 *
        (migrationLinkageExpansion pair.1 pair.2 index).velocity state =
        ∑ source, migrationShare rates index source *
          migrationLinkageVelocity (state source) (state index) :=
      sum_pair_recipient (migrationShare rates)
        (fun source recipient ↦ migrationLinkageVelocity (state source) (state recipient))
        index
    have hleftSum := abs_recipientShareSum_le_one rates index
      (fun source ↦ (state source).leftFrequency - (state index).leftFrequency)
      fun source ↦ abs_le.mpr
        ⟨by linarith [(state source).leftFrequency_nonneg, (state index).leftFrequency_le_one],
          by linarith [(state source).leftFrequency_le_one, (state index).leftFrequency_nonneg]⟩
    have hrightSum := abs_recipientShareSum_le_one rates index
      (fun source ↦ (state source).rightFrequency - (state index).rightFrequency)
      fun source ↦ abs_le.mpr
        ⟨by linarith [(state source).rightFrequency_nonneg, (state index).rightFrequency_le_one],
          by linarith [(state source).rightFrequency_le_one, (state index).rightFrequency_nonneg]⟩
    have hproduct : |(∑ source, migrationShare rates index source *
          ((state source).leftFrequency - (state index).leftFrequency)) *
        (∑ source, migrationShare rates index source *
          ((state source).rightFrequency - (state index).rightFrequency))| ≤ 1 := by
      rw [abs_mul]
      calc _ ≤ 1 * |∑ source, migrationShare rates index source *
            ((state source).rightFrequency - (state index).rightFrequency)| :=
          mul_le_mul_of_nonneg_right hleftSum (abs_nonneg _)
        _ ≤ 1 := by rw [one_mul]; exact hrightSum
    rw [simultaneousMigrationPulse_linkage rates h0 h1 state index, hcollapse]
    calc _ = |tau ^ 2 * ((∑ source, migrationShare rates index source *
            ((state source).leftFrequency - (state index).leftFrequency)) *
          (∑ source, migrationShare rates index source *
            ((state source).rightFrequency - (state index).rightFrequency)))| := by
          rw [← abs_neg]
          congr 1
          ring
      _ = tau ^ 2 * |(∑ source, migrationShare rates index source *
            ((state source).leftFrequency - (state index).leftFrequency)) *
          (∑ source, migrationShare rates index source *
            ((state source).rightFrequency - (state index).rightFrequency))| := by
          rw [abs_mul, abs_of_nonneg (by positivity)]
      _ ≤ tau ^ 2 * 1 := mul_le_mul_of_nonneg_left hproduct (by positivity)
      _ = 1 * tau ^ 2 := by ring

/-- The base coordinate expansions of the simultaneous migration stage. -/
def simultaneousMigrationCoordinateExpansion {D : ℕ} (rates : ManyDemeLDRates D) :
    PulseCoordinateExpansion (simultaneousMigrationPulse rates) where
  leftMarginal := simultaneousMigrationLeftExpansion rates
  rightMarginal := simultaneousMigrationRightExpansion rates
  linkageDeterminant := simultaneousMigrationLinkageExpansion rates

/-! ## Velocities are linear in the base velocities -/

/-- The first-order coefficient of every enlarged coordinate as a linear form in the base
velocities of the two marginals and the linkage determinant of each deme: the product rule
applied to the corpus polynomial behind the coordinate. -/
def enlargedTreeVelocity {D : ℕ}
    (leftVelocity rightVelocity linkageVelocity : Fin D → DemeHaplotypeState D → ℝ) :
    AffineEnlargedCoordinate D → DemeHaplotypeState D → ℝ
  | none => fun _ ↦ 0
  | some (.inl (.H first second)) => fun state ↦
      (1 - 2 * (state second).leftFrequency) * leftVelocity first state +
        (1 - 2 * (state first).leftFrequency) * leftVelocity second state
  | some (.inl (.DD first second)) => fun state ↦
      (state first).linkage * linkageVelocity second state +
        (state second).linkage * linkageVelocity first state
  | some (.inl (.Dz first second third)) => fun state ↦
      (1 - 2 * (state second).leftFrequency) * (1 - 2 * (state third).rightFrequency) *
          linkageVelocity first state +
        -2 * (state first).linkage * (1 - 2 * (state third).rightFrequency) *
          leftVelocity second state +
        -2 * (state first).linkage * (1 - 2 * (state second).leftFrequency) *
          rightVelocity third state
  | some (.inl (.pi2 first second third fourth)) => fun state ↦
      1 / 4 * (twoLocusRightHJet third fourth).value state *
          (1 - 2 * (state second).leftFrequency) * leftVelocity first state +
        1 / 4 * (twoLocusRightHJet third fourth).value state *
          (1 - 2 * (state first).leftFrequency) * leftVelocity second state +
        1 / 4 * (twoLocusHJet first second).value state *
          (1 - 2 * (state fourth).rightFrequency) * rightVelocity third state +
        1 / 4 * (twoLocusHJet first second).value state *
          (1 - 2 * (state third).rightFrequency) * rightVelocity fourth state
  | some (.inr pair) => fun state ↦
      (1 - 2 * (state pair.2).rightFrequency) * rightVelocity pair.1 state +
        (1 - 2 * (state pair.1).rightFrequency) * rightVelocity pair.2 state

/-- The pulse expansion of every enlarged coordinate assembled from the base expansions of one
pulse family. -/
def enlargedPulseExpansion {D : ℕ} {pulse : ℝ → DemeHaplotypeState D → DemeHaplotypeState D}
    (base : PulseCoordinateExpansion pulse) :
    (coordinate : AffineEnlargedCoordinate D) →
      PulseExpansion pulse (enlargedCoordinateJet coordinate).value
  | none => PulseExpansion.const D pulse 1
  | some (.inl feature) => base.coordinate feature
  | some (.inr pair) => base.rightHeterozygosity pair.1 pair.2

/-- **The corpus certificates have the linear-form velocity.**  The velocity of every enlarged
coordinate's Leibniz-built certificate is `enlargedTreeVelocity` of the base velocities. -/
theorem enlargedPulseExpansion_velocity {D : ℕ}
    {pulse : ℝ → DemeHaplotypeState D → DemeHaplotypeState D}
    (base : PulseCoordinateExpansion pulse) (coordinate : AffineEnlargedCoordinate D)
    (state : DemeHaplotypeState D) :
    (enlargedPulseExpansion base coordinate).velocity state =
      enlargedTreeVelocity (fun index ↦ (base.leftMarginal index).velocity)
        (fun index ↦ (base.rightMarginal index).velocity)
        (fun index ↦ (base.linkageDeterminant index).velocity) coordinate state := by
  rcases coordinate with _ | ((⟨first, second⟩ | ⟨first, second⟩ | ⟨first, second, third⟩ |
    ⟨first, second, third, fourth⟩) | ⟨first, second⟩)
  · simp [enlargedPulseExpansion, enlargedTreeVelocity, PulseExpansion.const]
  all_goals
    simp only [enlargedPulseExpansion, enlargedTreeVelocity, PulseCoordinateExpansion.coordinate,
      PulseCoordinateExpansion.leftHeterozygosity, PulseCoordinateExpansion.rightHeterozygosity,
      PulseCoordinateExpansion.linkageProduct, PulseCoordinateExpansion.dzObservable,
      PulseCoordinateExpansion.jointHeterozygosity, PulseExpansion.ofEq, PulseExpansion.add,
      PulseExpansion.smul, PulseExpansion.mul, PulseExpansion.const] <;>
    ring

/-- **The linear form commutes with finite weighted sums of base velocities.** -/
theorem enlargedTreeVelocity_sum {D : ℕ} {K : Type*} [Fintype K] (coefficient : K → ℝ)
    (leftVelocity rightVelocity linkageVelocity : K → Fin D → DemeHaplotypeState D → ℝ)
    (coordinate : AffineEnlargedCoordinate D) (state : DemeHaplotypeState D) :
    enlargedTreeVelocity (fun index y ↦ ∑ k, coefficient k * leftVelocity k index y)
        (fun index y ↦ ∑ k, coefficient k * rightVelocity k index y)
        (fun index y ↦ ∑ k, coefficient k * linkageVelocity k index y) coordinate state =
      ∑ k, coefficient k *
        enlargedTreeVelocity (leftVelocity k) (rightVelocity k) (linkageVelocity k)
          coordinate state := by
  rcases coordinate with _ | ((⟨first, second⟩ | ⟨first, second⟩ | ⟨first, second, third⟩ |
    ⟨first, second, third, fourth⟩) | ⟨first, second⟩)
  · simp [enlargedTreeVelocity]
  all_goals
    simp only [enlargedTreeVelocity, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun k _ ↦ by ring

/-- The corpus migration stage certificate of an enlarged coordinate is the assembled pulse
expansion of the per-pair migration family. -/
theorem enlargedStageExpansion_migration_velocity {D : ℕ}
    (coordinate : AffineEnlargedCoordinate D) (source recipient : Fin D)
    (state : DemeHaplotypeState D) :
    ((enlargedStageExpansion coordinate).migration source recipient).velocity state =
      (enlargedPulseExpansion (migrationCoordinateExpansion source recipient) coordinate).velocity
        state := by
  rcases coordinate with _ | (feature | pair) <;> rfl

/-- The simultaneous migration stage's expansion of every enlarged coordinate. -/
def simultaneousMigrationExpansion {D : ℕ} (rates : ManyDemeLDRates D)
    (coordinate : AffineEnlargedCoordinate D) :
    PulseExpansion (simultaneousMigrationPulse rates) (enlargedCoordinateJet coordinate).value :=
  enlargedPulseExpansion (simultaneousMigrationCoordinateExpansion rates) coordinate

/-- **At rate `1 + M` the simultaneous stage carries the summed per-pair migration drift.**  Its
rate-weighted velocity on every enlarged coordinate is the sum over ordered pairs of the corpus's
migration stage drifts. -/
theorem simultaneousMigrationExpansion_velocity {D : ℕ} (rates : ManyDemeLDRates D)
    (coordinate : AffineEnlargedCoordinate D) (state : DemeHaplotypeState D) :
    (1 + totalMigration rates) * (simultaneousMigrationExpansion rates coordinate).velocity state =
      ∑ pair : Fin D × Fin D,
        stageDrift rates (enlargedStageExpansion coordinate) (.migration pair.1 pair.2) state := by
  have hne : 1 + totalMigration rates ≠ 0 := by linarith [totalMigration_nonneg rates]
  have hlinear := enlargedTreeVelocity_sum
    (fun pair : Fin D × Fin D ↦ migrationShare rates pair.2 pair.1)
    (fun pair index ↦ ((migrationCoordinateExpansion pair.1 pair.2).leftMarginal index).velocity)
    (fun pair index ↦ ((migrationCoordinateExpansion pair.1 pair.2).rightMarginal index).velocity)
    (fun pair index ↦
      ((migrationCoordinateExpansion pair.1 pair.2).linkageDeterminant index).velocity)
    coordinate state
  beta_reduce at hlinear
  have hvelocity : (simultaneousMigrationExpansion rates coordinate).velocity state =
      ∑ pair : Fin D × Fin D, migrationShare rates pair.2 pair.1 *
        ((enlargedStageExpansion coordinate).migration pair.1 pair.2).velocity state := by
    rw [simultaneousMigrationExpansion, enlargedPulseExpansion_velocity]
    refine hlinear.trans (Finset.sum_congr rfl fun pair _ ↦ ?_)
    rw [enlargedStageExpansion_migration_velocity, enlargedPulseExpansion_velocity]
  rw [hvelocity, Finset.mul_sum]
  refine Finset.sum_congr rfl fun pair _ ↦ ?_
  have hcancel : (1 + totalMigration rates) *
      (rates.migration pair.2 pair.1 / (1 + totalMigration rates)) =
      rates.migration pair.2 pair.1 := by
    field_simp
  simp only [stageDrift, stageRate, stageVelocity, migrationShare]
  rw [← mul_assoc, hcancel]

end

end Descent.Portability.SimultaneousMigrationPulse
