/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.TwoLocusMicroscopicKernel

assert_below Descent.Decision Descent.Program

/-!
# The joint-heterozygosity row of the enlarged generator

NOTE1 section 2.3 builds one microscopic step out of resampling, migration, recombination and
two allele-flip pulses, and its equation (11) asks that the rate-weighted first-order stage
velocities sum to the enlarged generator of section 2.2 on every coordinate of the family (6).
`Descent.Portability.TwoLocusMicroscopicKernel` proves that identification on the constant,
`H`, `H^R`, `DD` and `Dz` coordinates, and on the joint heterozygosity
`pi2(i,j;k,l) = H^L_ij H^R_kl / 4` it proves only the drift and recombination stage sums.  This
module supplies the migration and mutation families of `pi2`, assembles the `pi2` row, and
collects every row into `stage_generator_enlarged`, which is the identification hypothesis of
`twoLocusMicroscopicApproximation` discharged at every enlarged coordinate.

The two families follow from the Leibniz rule.  The pulse certificate of `pi2` is a quarter of
the product certificate of one left and one right heterozygosity, so
`jointHeterozygosity_velocity_leibniz` reads the velocity of `pi2` off the two heterozygosity
velocities for any pulse family, and each pulse then acts only through heterozygosity bridges
that are already proved.  A migration pulse replaces each lineage argument sitting in the
recipient deme by the source deme's lineage (`migrationJointHeterozygosity_velocity`), and
summed against the migration rates this is the corpus row `lowOrderLDMigration` at `pi2`
(`migrationStage_sum_jointHeterozygosity`).  A left-locus allele-flip pulse moves `pi2` by the
corpus's `twoLocusPi2LeftMutationVelocity` per left lineage in the mutating deme, and a
right-locus pulse by `twoLocusPi2RightMutationVelocity` per right lineage
(`leftMutationJointHeterozygosity_velocity`, `rightMutationJointHeterozygosity_velocity`).

The mutation row is where the enlargement of NOTE1 equation (6) is used.  Summed over demes,
the left-locus pulses put the weight `(theta_i + theta_j) / 8` on the right-locus
heterozygosity `H^R_kl`, while the corpus coupling `lowOrderLDMutationCoupling` puts it on the
stored `H_kl` column.  The enlarged generator moves that weight to the `H^R` column through
`rightHeterozygosityMutationCoupling`, and
`rightHeterozygosityRedirect_sum_jointHeterozygosity` shows that the redirect reads exactly
that one column.  So `mutationStage_sum_jointHeterozygosity` matches the two mutation families
against the corpus coupling, damping and forcing rows plus the redirect, and the
identification `H^L = H^R` is made nowhere.  `stage_generator_jointHeterozygosity` is the
assembled `pi2` row, stated in the form of the kernel module's `stage_generator_dzObservable`.

Scope.  Only velocities are identified here.  The hypothesis-free microscopic approximation,
the propagation through epochs, and NOTE1 Theorem 2 and Corollary 2.1 belong to the assembly
module.  Multinomial resampling, NOTE1 equation (10), is not formalized; the single-draw
resampling stage of NOTE1 section 2.3 is used throughout.

## Empirical status

None.  The bodies here are algebra: identities between polynomials in haplotype frequencies,
summed against the rate coordinates of `ManyDemeLDRates`, so no measurement can bear on them.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.Pi2GeneratorBridges

open Coalescent
open Descent.Portability.PulseJetExpansion
open Descent.Portability.PulseStageKernel
open Descent.Portability.EnlargedLowOrderLDGenerator
open Descent.Portability.TwoLocusMicroscopicKernel

/-! ## The Leibniz rule for the joint heterozygosity -/

/-- **The pulse velocity of the joint heterozygosity is the Leibniz rule.**  Under any pulse
family, `pi2(i,j;k,l) = H^L_ij H^R_kl / 4` moves at a quarter of
`H^L_ij v(H^R_kl) + H^R_kl v(H^L_ij)`, where `v` is the velocity assembled from the same base
coordinate expansions. -/
theorem jointHeterozygosity_velocity_leibniz {D : ℕ}
    {pulse : ℝ → DemeHaplotypeState D → DemeHaplotypeState D}
    (base : PulseCoordinateExpansion pulse) (first second third fourth : Fin D)
    (state : DemeHaplotypeState D) :
    (base.jointHeterozygosity first second third fourth).velocity state =
      1 / 4 * ((twoLocusHJet first second).value state *
          (base.rightHeterozygosity third fourth).velocity state +
        (twoLocusRightHJet third fourth).value state *
          (base.leftHeterozygosity first second).velocity state) := rfl

/-! ## The migration stages reproduce the corpus `pi2` migration row -/

/-- **A migration pulse replaces one lineage of the joint heterozygosity at a time.**  The
pulse from `source` into `recipient` moves `pi2(i,j;k,l)` by the source-minus-recipient
replacement at each of its four lineage arguments sitting in the recipient deme, whether that
lineage is read at the left locus or at the right. -/
theorem migrationJointHeterozygosity_velocity {D : ℕ}
    (source recipient first second third fourth : Fin D) (state : DemeHaplotypeState D) :
    ((migrationCoordinateExpansion source recipient).jointHeterozygosity first second third
        fourth).velocity state =
      (if first = recipient then
        (twoLocusPi2Jet source second third fourth).value state -
          (twoLocusPi2Jet first second third fourth).value state else 0) +
      (if second = recipient then
        (twoLocusPi2Jet first source third fourth).value state -
          (twoLocusPi2Jet first second third fourth).value state else 0) +
      (if third = recipient then
        (twoLocusPi2Jet first second source fourth).value state -
          (twoLocusPi2Jet first second third fourth).value state else 0) +
      (if fourth = recipient then
        (twoLocusPi2Jet first second third source).value state -
          (twoLocusPi2Jet first second third fourth).value state else 0) := by
  rw [jointHeterozygosity_velocity_leibniz, migrationLeftHeterozygosity_velocity,
    migrationRightHeterozygosity_velocity]
  simp only [twoLocusPi2Jet_value, twoLocusHJet_value, twoLocusRightHJet_value,
    twoLocusJointHeterozygosity]
  split_ifs <;> ring

/-- **The migration stages sum to the corpus `pi2` migration row.**  Each ordered deme pair
contributes at every lineage argument sitting in its recipient, and summing the replacement
stencil against the migration rates is `lowOrderLDMigration` at `pi2`, term by term. -/
theorem migrationStage_sum_jointHeterozygosity {D : ℕ} (rates : ManyDemeLDRates D)
    (first second third fourth : Fin D) (state : DemeHaplotypeState D) :
    ∑ pair : Fin D × Fin D, stageRate rates (Stage.migration pair.1 pair.2) *
        stageVelocity
          (enlargedStageExpansion (some (.inl (.pi2 first second third fourth))))
          (Stage.migration pair.1 pair.2) state =
      lowOrderLDMigration rates (twoLocusJetMoment state) (.pi2 first second third fourth) := by
  have hvelocity : ∀ pair : Fin D × Fin D,
      stageRate rates (Stage.migration pair.1 pair.2) *
        stageVelocity
          (enlargedStageExpansion (some (.inl (.pi2 first second third fourth))))
          (Stage.migration pair.1 pair.2) state =
      rates.migration pair.2 pair.1 *
        ((if first = pair.2 then
            (twoLocusPi2Jet pair.1 second third fourth).value state -
              (twoLocusPi2Jet first second third fourth).value state else 0) +
          (if second = pair.2 then
            (twoLocusPi2Jet first pair.1 third fourth).value state -
              (twoLocusPi2Jet first second third fourth).value state else 0) +
          (if third = pair.2 then
            (twoLocusPi2Jet first second pair.1 fourth).value state -
              (twoLocusPi2Jet first second third fourth).value state else 0) +
          (if fourth = pair.2 then
            (twoLocusPi2Jet first second third pair.1).value state -
              (twoLocusPi2Jet first second third fourth).value state else 0)) := by
    intro pair
    show rates.migration pair.2 pair.1 *
        ((migrationCoordinateExpansion pair.1 pair.2).jointHeterozygosity first second third
          fourth).velocity state = _
    rw [migrationJointHeterozygosity_velocity]
  have hmoment : ∀ leftFirst leftSecond rightFirst rightSecond : Fin D,
      twoLocusJetMoment state (.pi2 leftFirst leftSecond rightFirst rightSecond) =
        (twoLocusPi2Jet leftFirst leftSecond rightFirst rightSecond).value state :=
    fun _ _ _ _ ↦ rfl
  rw [Finset.sum_congr rfl fun pair _ ↦ hvelocity pair]
  simp only [hmoment, Fintype.sum_prod_type, lowOrderLDMigration, mul_add,
    Finset.sum_add_distrib, mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]

/-! ## The mutation stages reproduce the enlarged `pi2` mutation row -/

/-- **A left-locus allele-flip pulse moves the joint heterozygosity by the corpus left-channel
velocity.**  Only the left heterozygosity factor moves, so the velocity is twice the number of
left lineages sitting in the mutating deme times `twoLocusPi2LeftMutationVelocity`, the exact
`H^R / 8 - pi2` coupling. -/
theorem leftMutationJointHeterozygosity_velocity {D : ℕ}
    (target first second third fourth : Fin D) (state : DemeHaplotypeState D) :
    ((leftMutationCoordinateExpansion target).jointHeterozygosity first second third
        fourth).velocity state =
      2 * ((if first = target then (1 : ℝ) else 0) +
          (if second = target then (1 : ℝ) else 0)) *
        twoLocusPi2LeftMutationVelocity (state first) (state second) (state third)
          (state fourth) := by
  rw [jointHeterozygosity_velocity_leibniz, leftMutationRightHeterozygosity_velocity,
    leftMutationLeftHeterozygosity_velocity, twoLocusRightHJet_value]
  simp only [twoLocusPi2LeftMutationVelocity, twoLocusHMutationVelocity,
    twoLocusRightHeterozygosity_eq_contrasts]
  ring

/-- **A right-locus allele-flip pulse moves the joint heterozygosity by the corpus
right-channel velocity.**  Only the right heterozygosity factor moves, so the velocity is twice
the number of right lineages sitting in the mutating deme times
`twoLocusPi2RightMutationVelocity`, the exact `H^L / 8 - pi2` coupling. -/
theorem rightMutationJointHeterozygosity_velocity {D : ℕ}
    (target first second third fourth : Fin D) (state : DemeHaplotypeState D) :
    ((rightMutationCoordinateExpansion target).jointHeterozygosity first second third
        fourth).velocity state =
      2 * ((if third = target then (1 : ℝ) else 0) +
          (if fourth = target then (1 : ℝ) else 0)) *
        twoLocusPi2RightMutationVelocity (state first) (state second) (state third)
          (state fourth) := by
  rw [jointHeterozygosity_velocity_leibniz, rightMutationRightHeterozygosity_velocity,
    rightMutationLeftHeterozygosity_velocity, twoLocusHJet_value]
  simp only [twoLocusPi2RightMutationVelocity, twoLocusLeftHeterozygosity_eq_contrasts,
    twoLocusRightHeterozygosity_eq_contrasts]
  ring

/-- **The right-locus redirect of a `pi2` row reads one column.**  Over the right-locus
heterozygosity columns, the coefficient `rightHeterozygosityMutationCoupling` of the row
`pi2(i,j;k,l)` is supported on the single pair `(k,l)`, where it carries the left-index
mutation rates over eight. -/
theorem rightHeterozygosityRedirect_sum_jointHeterozygosity {D : ℕ}
    (rates : ManyDemeLDRates D) (first second third fourth : Fin D)
    (vector : AffineEnlargedCoordinate D → ℝ) :
    ∑ pair : Fin D × Fin D,
        rightHeterozygosityMutationCoupling rates (.pi2 first second third fourth)
            pair.1 pair.2 *
          (vector (some (.inr pair)) - vector (some (.inl (.H pair.1 pair.2)))) =
      (rates.mutation first + rates.mutation second) / 8 *
        (vector (some (.inr (third, fourth))) - vector (some (.inl (.H third fourth)))) := by
  have hhit : rightHeterozygosityMutationCoupling rates (.pi2 first second third fourth)
      third fourth = (rates.mutation first + rates.mutation second) / 8 := by
    show (if third = third ∧ fourth = fourth then
      (rates.mutation first + rates.mutation second) / 8 else 0) = _
    exact if_pos ⟨rfl, rfl⟩
  rw [Finset.sum_eq_single (third, fourth)]
  · exact congrArg (fun coefficient ↦ coefficient *
      (vector (some (.inr (third, fourth))) - vector (some (.inl (.H third fourth))))) hhit
  · intro pair _ hpair
    have hmiss : ¬(third = pair.1 ∧ fourth = pair.2) := by
      rintro ⟨hthird, hfourth⟩
      subst hthird hfourth
      exact hpair rfl
    have hzero : rightHeterozygosityMutationCoupling rates (.pi2 first second third fourth)
        pair.1 pair.2 = 0 := by
      show (if third = pair.1 ∧ fourth = pair.2 then
        (rates.mutation first + rates.mutation second) / 8 else 0) = 0
      exact if_neg hmiss
    rw [hzero, zero_mul]
  · intro hmember
    exact absurd (Finset.mem_univ _) hmember

/-- **The two mutation stage families sum to the enlarged `pi2` mutation row.**  The
left-locus pulses contribute the left-channel velocity at the two left lineages and the
right-locus pulses the right-channel velocity at the two right lineages.  Against the corpus
rows this is the coupling, the recurrent damping and the vanishing forcing, plus the redirect
that moves the left-channel weight from the stored heterozygosity column onto the right-locus
one. -/
theorem mutationStage_sum_jointHeterozygosity {D : ℕ} (rates : ManyDemeLDRates D)
    (first second third fourth : Fin D) (state : DemeHaplotypeState D) :
    mutationStageDrift rates (some (.inl (.pi2 first second third fourth))) state =
      lowOrderLDMutationCoupling rates (twoLocusJetMoment state)
          (.pi2 first second third fourth) +
        lowOrderLDRecurrentMutationDamping rates (twoLocusJetMoment state)
          (.pi2 first second third fourth) +
        lowOrderLDMutationForcing rates (.pi2 first second third fourth) +
        ∑ pair : Fin D × Fin D,
          rightHeterozygosityMutationCoupling rates (.pi2 first second third fourth)
              pair.1 pair.2 *
            (enlargedLowOrderLDFeature state (some (.inr pair)) -
              enlargedLowOrderLDFeature state (some (.inl (.H pair.1 pair.2)))) := by
  have hleft : ∀ deme : Fin D,
      stageRate rates (Stage.mutationLeft deme) *
        stageVelocity
          (enlargedStageExpansion (some (.inl (.pi2 first second third fourth))))
          (Stage.mutationLeft deme) state =
      twoLocusPi2LeftMutationVelocity (state first) (state second) (state third)
          (state fourth) * (rates.mutation deme * (if first = deme then (1 : ℝ) else 0)) +
        twoLocusPi2LeftMutationVelocity (state first) (state second) (state third)
          (state fourth) * (rates.mutation deme * (if second = deme then (1 : ℝ) else 0)) :=
    fun deme ↦ mutationStage_drift_of_velocity rates _ (.mutationLeft deme) deme rfl state
      (leftMutationJointHeterozygosity_velocity deme first second third fourth state) (by ring)
  have hright : ∀ deme : Fin D,
      stageRate rates (Stage.mutationRight deme) *
        stageVelocity
          (enlargedStageExpansion (some (.inl (.pi2 first second third fourth))))
          (Stage.mutationRight deme) state =
      twoLocusPi2RightMutationVelocity (state first) (state second) (state third)
          (state fourth) * (rates.mutation deme * (if third = deme then (1 : ℝ) else 0)) +
        twoLocusPi2RightMutationVelocity (state first) (state second) (state third)
          (state fourth) * (rates.mutation deme * (if fourth = deme then (1 : ℝ) else 0)) :=
    fun deme ↦ mutationStage_drift_of_velocity rates _ (.mutationRight deme) deme rfl state
      (rightMutationJointHeterozygosity_velocity deme first second third fourth state) (by ring)
  have hforcing : lowOrderLDMutationForcing rates (.pi2 first second third fourth) = 0 := rfl
  rw [mutationStageDrift, (Finset.sum_congr rfl fun deme _ ↦ hleft deme),
    (Finset.sum_congr rfl fun deme _ ↦ hright deme),
    rightHeterozygosityRedirect_sum_jointHeterozygosity rates first second third fourth
      (enlargedLowOrderLDFeature state), hforcing]
  simp only [Finset.sum_add_distrib, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq,
    Finset.mem_univ, if_true]
  simp only [lowOrderLDMutationCoupling, lowOrderLDRecurrentMutationDamping,
    enlargedLowOrderLDFeature, twoLocusJetMoment, twoLocusCoordinateJet, twoLocusHJet_value,
    twoLocusPi2Jet_value, twoLocusPi2LeftMutationVelocity_eq,
    twoLocusPi2RightMutationVelocity_eq]
  ring

/-! ## The assembled rows -/

/-- **The stage velocities reproduce the enlarged generator on the joint-heterozygosity
coordinate.**  Drift supplies the corpus coalescence row, migration the four-lineage
replacement stencil, recombination nothing, and the two mutation families the coupling and
damping rows with the left-channel weight read off the right-locus heterozygosity.  This is
the last coordinate family of NOTE1 equation (11). -/
theorem stage_generator_jointHeterozygosity {D : ℕ} (rates : ManyDemeLDRates D)
    (first second third fourth : Fin D) (state : DemeHaplotypeState D) :
    (enlargedLowOrderLDGenerator rates).mulVec (enlargedLowOrderLDFeature state)
        (some (.inl (.pi2 first second third fourth))) =
      ∑ stage : Stage D,
        stageDrift rates
          (enlargedStageExpansion (some (.inl (.pi2 first second third fourth)))) stage
          state := by
  have hmutation := mutationStage_sum_jointHeterozygosity rates first second third fourth state
  rw [mutationStageDrift] at hmutation
  have hstored : (fun coordinate ↦ enlargedLowOrderLDFeature state (some (.inl coordinate))) =
      twoLocusJetMoment state := rfl
  have hone : enlargedLowOrderLDFeature state (none : AffineEnlargedCoordinate D) = 1 := rfl
  rw [enlargedGenerator_mulVec_stored, sum_stage, hstored, hone]
  simp only [stageDrift, lowOrderLDHomogeneousGenerator]
  rw [driftStage_sum_stored, migrationStage_sum_jointHeterozygosity,
    recombinationStage_sum_stored]
  linarith [hmutation]

/-- **The stage velocities reproduce the enlarged generator on every stored coordinate.**  The
four stored families `H`, `DD`, `Dz` and `pi2` are each matched by their own row theorem. -/
theorem stage_generator_stored {D : ℕ} (rates : ManyDemeLDRates D)
    (feature : LowOrderLDCoordinate D) (state : DemeHaplotypeState D) :
    (enlargedLowOrderLDGenerator rates).mulVec (enlargedLowOrderLDFeature state)
        (some (.inl feature)) =
      ∑ stage : Stage D,
        stageDrift rates (enlargedStageExpansion (some (.inl feature))) stage state := by
  cases feature with
  | H first second => exact stage_generator_leftHeterozygosity rates first second state
  | DD first second => exact stage_generator_linkageProduct rates first second state
  | Dz first second third =>
      exact stage_generator_dzObservable rates first second third state
  | pi2 first second third fourth =>
      exact stage_generator_jointHeterozygosity rates first second third fourth state

/-- **The stage velocities reproduce the enlarged generator at every enlarged coordinate.**
This is the `stage_generator` hypothesis of `twoLocusMicroscopicApproximation`, with nothing
left to assume: the constant row, the four stored families and the right-locus heterozygosity
row are all matched. -/
theorem stage_generator_enlarged {D : ℕ} (rates : ManyDemeLDRates D)
    (state : DemeHaplotypeState D) (coordinate : AffineEnlargedCoordinate D) :
    (enlargedLowOrderLDGenerator rates).mulVec (enlargedLowOrderLDFeature state) coordinate =
      ∑ stage : Stage D, stageDrift rates (enlargedStageExpansion coordinate) stage state := by
  rcases coordinate with _ | (feature | ⟨first, second⟩)
  · exact stage_generator_constant rates state
  · exact stage_generator_stored rates feature state
  · exact stage_generator_rightHeterozygosity rates first second state

end Descent.Portability.Pi2GeneratorBridges
