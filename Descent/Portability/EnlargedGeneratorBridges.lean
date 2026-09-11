/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.TwoLocusMicroscopicKernel

assert_below Descent.Decision Descent.Program

/-!
# The right-locus heterozygosity row of the enlarged generator, stage by stage

`EnlargedLowOrderLDGenerator` builds the enlarged family of NOTE 1 (6) and reads its generator
back in row form; `PulseStageKernel` puts the five microscopic stages under one index and
proves that each expands to first order with its own rate and velocity.  Between them sits the
identification of the SUM over stages of `stageRate * stageVelocity` with the matching
generator row.  `TwoLocusMicroscopicKernel` proves that identification row by row.  This
module reads one row, the right-locus heterozygosity row `H^R_ij`, one stage family at a
time, with every family matched against a single corpus channel.

The row has five stage contributions.  The resampling block is the corpus coalescence channel
`lowOrderLDDrift`, and the migration block, written as a double sum over source and recipient,
is the corpus channel `lowOrderLDMigration`; both are the kernel's stage sums.  The
recombination block is the corpus recombination row, which vanishes on a heterozygosity.  The
two mutation families are kept apart, which the kernel does not do: the left-locus mutation
block is the corpus coupling row, zero on a heterozygosity, and the right-locus mutation block
carries the whole affine mutation law, the recurrent damping together with the constant
influx.  The asymmetry between those two blocks is why NOTE 1 (6) enlarges the stored family.

`sum_stage` splits a sum over `Stage D` into its five blocks in the nested form the blocks
use, from the kernel's split.  `enlargedGenerator_mulVec_constant` says the constant row of the
enlarged generator annihilates every vector, not only a feature vector, and
`stageSum_constant` is the kernel's constant-row identification read from the stage side.
`stageSum_rightHeterozygosity` is the bridge itself: the rate-weighted stage velocities of
`twoLocusRightHJet first second` add up to exactly the enlarged generator applied to the
enlarged feature vector at `H^R (first, second)`, assembled from the five blocks through
`enlargedGenerator_mulVec_rightHeterozygosity`.  It is the claim of
`TwoLocusMicroscopicKernel.stage_generator_rightHeterozygosity`, reached block by block.

The three pulse velocities the row needs are the kernel's lemmas, restated under this
module's names and proved from the kernel's: recombination and left-locus mutation move no
right marginal and have velocity zero, and the right-locus mutation velocity is twice the
number of the coordinate's lineages sitting in the mutating deme times `1/2 - H^R`.

Scope.  Only the constant row and the `H^R` row are read here.  The stored rows `H`, `DD` and
`Dz` are identified in `TwoLocusMicroscopicKernel`, and the `pi2` row, whose right-locus
dependence the generator routes through `rightHeterozygosityMutationCoupling`, in
`Pi2GeneratorBridges`.  Nothing here assembles a `MicroscopicApproximation` or takes a limit.

## Empirical status

None.  The bodies here are algebra: an index bijection, and polynomial identities between
pulse velocities and generator entries on the probability simplex.  No measurement can bear on
them.  Whether a population's step is this list of stages is asked wherever a composed
prediction meets data, not here.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.EnlargedGeneratorBridges

open Coalescent PulseJetExpansion PulseStageKernel EnlargedLowOrderLDGenerator
open TwoLocusMicroscopicKernel

noncomputable section

/-! ## Splitting a sum over the stage index -/

/-- The five stage kinds presented as an iterated sum type, which is the kernel's
`stageStructure`.  It exists only so that a sum over `Stage D` can be split into its five
blocks. -/
def sumStageEquiv (D : ℕ) :
    Fin D ⊕ (Fin D × Fin D) ⊕ Fin D ⊕ Fin D ⊕ Fin D ≃ Stage D :=
  stageStructure D

/-- The stage bijection of this module is the kernel's. -/
theorem sumStageEquiv_eq_stageStructure (D : ℕ) : sumStageEquiv D = stageStructure D := rfl

/-- A sum over the five stages splits into the resampling block, the ordered migration pairs,
and the three single-deme pulse blocks.  This is the kernel's `sum_stage` with the migration
block written as a double sum and the blocks nested to the right. -/
theorem sum_stage {D : ℕ} (score : Stage D → ℝ) :
    ∑ stage : Stage D, score stage =
      (∑ deme, score (.drift deme)) +
        ((∑ source, ∑ recipient, score (.migration source recipient)) +
          ((∑ deme, score (.recombination deme)) +
            ((∑ deme, score (.mutationLeft deme)) +
              ∑ deme, score (.mutationRight deme)))) := by
  rw [TwoLocusMicroscopicKernel.sum_stage score]
  simp only [Fintype.sum_prod_type]
  ring

/-! ## The three right-locus heterozygosity velocities -/

/-- A recombination pulse redraws haplotypes from the product of the deme's own marginals, so
it moves no marginal allele frequency and no right-locus heterozygosity. -/
theorem recombinationRightHeterozygosity_velocity {D : ℕ} (target first second : Fin D)
    (state : DemeHaplotypeState D) :
    ((recombinationCoordinateExpansion target).rightHeterozygosity first second).velocity
      state = 0 :=
  TwoLocusMicroscopicKernel.recombinationRightHeterozygosity_velocity target first second state

/-- A left-locus mutation pulse leaves every right marginal alone, so it moves no right-locus
heterozygosity.  This is the asymmetry that makes the enlargement of NOTE 1 (6) necessary:
the left and right families are driven by different stages. -/
theorem leftMutationRightHeterozygosity_velocity {D : ℕ} (target first second : Fin D)
    (state : DemeHaplotypeState D) :
    ((leftMutationCoordinateExpansion target).rightHeterozygosity first second).velocity
      state = 0 :=
  TwoLocusMicroscopicKernel.leftMutationRightHeterozygosity_velocity target first second state

/-- The right-locus mutation velocity of a right-locus heterozygosity is the mirror of the
corpus's left-locus law: twice the number of the coordinate's lineages sitting in the mutating
deme, times the affine contrast-decay velocity `1/2 - H^R`.  The factor two is the conversion
between an allele-flip probability and the repository's mutation rate coordinate, exactly as
in `leftMutationLeftHeterozygosity_velocity`. -/
theorem rightMutationRightHeterozygosity_velocity {D : ℕ} (target first second : Fin D)
    (state : DemeHaplotypeState D) :
    ((rightMutationCoordinateExpansion target).rightHeterozygosity first second).velocity
        state =
      2 * ((if first = target then 1 else 0) + (if second = target then 1 else 0)) *
        (1 / 2 - twoLocusRightHeterozygosity (state first) (state second)) :=
  TwoLocusMicroscopicKernel.rightMutationRightHeterozygosity_velocity target first second state

/-! ## The constant row -/

/-- The constant row of the enlarged generator is zero, so a constant observable is fixed. -/
theorem enlargedGenerator_mulVec_constant {D : ℕ} (rates : ManyDemeLDRates D)
    (vector : AffineEnlargedCoordinate D → ℝ) :
    (enlargedLowOrderLDGenerator rates).mulVec vector none = 0 := by
  have hsum : (enlargedLowOrderLDGenerator rates).mulVec vector none =
      ∑ entry, enlargedLowOrderLDGenerator rates none entry * vector entry := rfl
  rw [hsum]
  exact Finset.sum_eq_zero fun entry _ ↦ by
    rw [show enlargedLowOrderLDGenerator rates none entry = 0 from rfl, zero_mul]

/-- The constant coordinate of the enlarged family carries the five stage certificates: no
stage moves a constant.  These are the kernel's certificates for the affine coordinate. -/
def constantStageExpansion (D : ℕ) :
    StageExpansion (TwoLocusDiffusionJet.const (1 : ℝ) : TwoLocusDiffusionJet D) :=
  TwoLocusMicroscopicKernel.constantStageExpansion

/-- **The constant row of the enlarged generator is the sum of its stage velocities.**  Both
sides are zero: every stage is a probability kernel and so fixes the constant observable, and
the enlarged generator's constant row vanishes.  This is the kernel's
`stage_generator_constant` read from the stage side. -/
theorem stageSum_constant {D : ℕ} (rates : ManyDemeLDRates D)
    (state : DemeHaplotypeState D) :
    (∑ stage : Stage D, stageDrift rates (constantStageExpansion D) stage state) =
      (enlargedLowOrderLDGenerator rates).mulVec (enlargedLowOrderLDFeature state) none :=
  (stage_generator_constant rates state).symm

/-! ## The five stage blocks of the right-locus heterozygosity row -/

/-- The resampling block of the row is the corpus drift channel: a right-locus heterozygosity
decays at the coalescence rate exactly when both its lineages sit in the drifting deme. -/
theorem driftBlock_rightHeterozygosity {D : ℕ} (rates : ManyDemeLDRates D)
    (first second : Fin D) (state : DemeHaplotypeState D) :
    (∑ deme, stageDrift rates (rightHeterozygosityStageExpansion first second)
        (.drift deme) state) =
      lowOrderLDDrift rates
        (rightHeterozygosityMoment (enlargedLowOrderLDFeature state)) (.H first second) :=
  driftStage_sum_rightHeterozygosity rates first second state

/-- The migration block of the row is the corpus migration channel: each lineage sitting in
the recipient deme is replaced by the source deme's lineage. -/
theorem migrationBlock_rightHeterozygosity {D : ℕ} (rates : ManyDemeLDRates D)
    (first second : Fin D) (state : DemeHaplotypeState D) :
    (∑ source, ∑ recipient,
        stageDrift rates (rightHeterozygosityStageExpansion first second)
          (.migration source recipient) state) =
      lowOrderLDMigration rates
        (rightHeterozygosityMoment (enlargedLowOrderLDFeature state)) (.H first second) := by
  rw [← migrationStage_sum_rightHeterozygosity rates first second state, Fintype.sum_prod_type]
  rfl

/-- The recombination block of the row vanishes, matching the corpus's zero recombination row
at a heterozygosity: a recombination pulse moves no marginal allele frequency. -/
theorem recombinationBlock_rightHeterozygosity {D : ℕ} (rates : ManyDemeLDRates D)
    (first second : Fin D) (state : DemeHaplotypeState D) :
    (∑ deme, stageDrift rates (rightHeterozygosityStageExpansion first second)
        (.recombination deme) state) =
      lowOrderLDRecombination rates
        (rightHeterozygosityMoment (enlargedLowOrderLDFeature state)) (.H first second) :=
  (recombinationStage_sum_rightHeterozygosity rates first second state).trans
    (lowOrderLDRecombination_H_eq_zero rates _ first second).symm

/-- The left-locus mutation block of the row vanishes, matching the corpus's zero mutation
coupling row at a heterozygosity.  This is the asymmetry NOTE 1 (6) is about: the right-locus
family is not driven by the left-locus mutation stage. -/
theorem leftMutationBlock_rightHeterozygosity {D : ℕ} (rates : ManyDemeLDRates D)
    (first second : Fin D) (state : DemeHaplotypeState D) :
    (∑ deme, stageDrift rates (rightHeterozygosityStageExpansion first second)
        (.mutationLeft deme) state) =
      lowOrderLDMutationCoupling rates
        (rightHeterozygosityMoment (enlargedLowOrderLDFeature state)) (.H first second) := by
  have hzero : ∀ deme ∈ (Finset.univ : Finset (Fin D)),
      stageDrift rates (rightHeterozygosityStageExpansion first second)
        (.mutationLeft deme) state = 0 := by
    intro deme _
    simp only [stageDrift, stageVelocity, rightHeterozygosityStageExpansion,
      leftMutationRightHeterozygosity_velocity, mul_zero]
  rw [Finset.sum_eq_zero hzero]
  simp only [lowOrderLDMutationCoupling]

/-- The right-locus mutation block of the row carries both affine mutation terms: the
recurrent damping and the constant influx.  Their sum is the exact contrast-decay velocity
`(theta_first + theta_second) * (1/2 - H^R)`. -/
theorem rightMutationBlock_rightHeterozygosity {D : ℕ} (rates : ManyDemeLDRates D)
    (first second : Fin D) (state : DemeHaplotypeState D) :
    (∑ deme, stageDrift rates (rightHeterozygosityStageExpansion first second)
        (.mutationRight deme) state) =
      lowOrderLDRecurrentMutationDamping rates
          (rightHeterozygosityMoment (enlargedLowOrderLDFeature state)) (.H first second) +
        lowOrderLDMutationForcing rates (.H first second) *
          enlargedLowOrderLDFeature state none := by
  have hterm : ∀ deme : Fin D,
      stageDrift rates (rightHeterozygosityStageExpansion first second)
          (.mutationRight deme) state =
        (if first = deme then
          rates.mutation deme *
            (1 / 2 - twoLocusRightHeterozygosity (state first) (state second)) else 0) +
        (if second = deme then
          rates.mutation deme *
            (1 / 2 - twoLocusRightHeterozygosity (state first) (state second)) else 0) := by
    intro deme
    simp only [stageDrift, stageRate, stageVelocity, rightHeterozygosityStageExpansion,
      rightMutationRightHeterozygosity_velocity]
    by_cases hfirst : first = deme <;> by_cases hsecond : second = deme <;>
      simp [hfirst, hsecond] <;> ring
  rw [Finset.sum_congr rfl (fun deme _ ↦ hterm deme), Finset.sum_add_distrib,
    Finset.sum_ite_eq, Finset.sum_ite_eq]
  simp only [Finset.mem_univ, if_true, lowOrderLDRecurrentMutationDamping,
    lowOrderLDMutationForcing, rightHeterozygosityMoment, enlargedLowOrderLDFeature]
  ring

/-- **The right-locus heterozygosity row of the enlarged generator is the sum of its stage
velocities.**  Adding the five rate-weighted stage velocities of `twoLocusRightHJet` over the
stage index reproduces exactly the enlarged generator applied to the enlarged feature vector
at that coordinate.  This is the row the stored corpus generator does not carry, and the one
NOTE 1 (6) adds; with it, the `H^R` block of a `MicroscopicApproximation` of
`enlargedLowOrderLDGenerator` is available from `apply_uniformStageMixture`. -/
theorem stageSum_rightHeterozygosity {D : ℕ} (rates : ManyDemeLDRates D)
    (first second : Fin D) (state : DemeHaplotypeState D) :
    (∑ stage : Stage D,
        stageDrift rates (rightHeterozygosityStageExpansion first second) stage state) =
      (enlargedLowOrderLDGenerator rates).mulVec (enlargedLowOrderLDFeature state)
        (some (.inr (first, second))) := by
  rw [sum_stage, enlargedGenerator_mulVec_rightHeterozygosity]
  simp only [lowOrderLDHomogeneousGenerator, driftBlock_rightHeterozygosity,
    migrationBlock_rightHeterozygosity, recombinationBlock_rightHeterozygosity,
    leftMutationBlock_rightHeterozygosity, rightMutationBlock_rightHeterozygosity]
  ring

end

end Descent.Portability.EnlargedGeneratorBridges
