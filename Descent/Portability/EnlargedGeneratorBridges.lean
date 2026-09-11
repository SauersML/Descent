/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.EnlargedLowOrderLDGenerator
import Descent.Portability.PulseStageKernel

assert_below Descent.Decision Descent.Program

/-!
# The right-locus heterozygosity row of the enlarged generator, stage by stage

`EnlargedLowOrderLDGenerator` builds the enlarged family of NOTE 1 (6) and reads its generator
back in row form; `PulseStageKernel` puts the five microscopic stages under one index and
proves that each expands to first order with its own rate and velocity.  What is still missing
between them is the identification of the SUM over stages of `stageRate * stageVelocity` with
the matching generator row.  This module supplies that identification for the row the corpus
cannot supply on its own: the right-locus heterozygosity row `H^R_ij`.

The row has five stage contributions and only two existed before.  The resampling stage is the
corpus's `twoLocusRightHJet_driftAt`, which decays a right-locus heterozygosity at the
coalescence rate exactly when both its lineages sit in the drifting deme.  The migration stage
is `PulseJetExpansion.migrationRightHeterozygosity_velocity`.  The three proved here are the
recombination stage and the left-locus mutation stage, both of which move no right marginal
and so have velocity identically zero, and the right-locus mutation stage, whose velocity is
the mirror of the corpus's left-locus law: twice the number of the coordinate's lineages
sitting in the mutating deme, times the affine contrast-decay velocity `1/2 - H^R`.  That last
one is stated against `1 / 2 - twoLocusRightHeterozygosity` rather than against a new named
velocity, because the corpus names such a velocity only at the left locus and this module does
not extend the corpus's vocabulary.

`sum_stage` splits a sum over `Stage D` into its five blocks through an explicit equivalence
with a sum type; it is bookkeeping, but nothing else can turn the per-stage expansion into a
row.  `stageSum_constant` disposes of the constant coordinate, where both sides vanish because
a probability kernel fixes constants.  `stageSum_rightHeterozygosity` is the bridge itself:
the rate-weighted stage velocities of `twoLocusRightHJet first second` add up to exactly the
enlarged generator applied to the enlarged feature vector at `H^R (first, second)`, which by
`enlargedGenerator_mulVec_rightHeterozygosity` is the corpus `H` row read at right-locus
indices together with its affine mutation forcing.

Scope.  Only the constant row and the `H^R` row are proved here.  The stored rows `H`, `DD`,
`Dz` and `pi2` need the same treatment and are NOT done: of their twenty stage cells the
corpus and `PulseJetExpansion` supply eight, and the rest belong to the pulse package.  In
particular the `pi2` row is the one whose right-locus dependence the generator routes through
`rightHeterozygosityMutationCoupling`, so its bridge must read `H^R` off the enlarged vector
rather than off the stored `H` column.  Nothing here assembles a `MicroscopicApproximation` or
takes a limit.

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

noncomputable section

/-! ## Splitting a sum over the stage index -/

/-- The five stage kinds presented as an iterated sum type.  It exists only so that a sum over
`Stage D` can be split into its five blocks. -/
def sumStageEquiv (D : ℕ) :
    Fin D ⊕ (Fin D × Fin D) ⊕ Fin D ⊕ Fin D ⊕ Fin D ≃ Stage D where
  toFun
    | .inl deme => .drift deme
    | .inr (.inl pair) => .migration pair.1 pair.2
    | .inr (.inr (.inl deme)) => .recombination deme
    | .inr (.inr (.inr (.inl deme))) => .mutationLeft deme
    | .inr (.inr (.inr (.inr deme))) => .mutationRight deme
  invFun
    | .drift deme => .inl deme
    | .migration source recipient => .inr (.inl (source, recipient))
    | .recombination deme => .inr (.inr (.inl deme))
    | .mutationLeft deme => .inr (.inr (.inr (.inl deme)))
    | .mutationRight deme => .inr (.inr (.inr (.inr deme)))
  left_inv := by
    rintro (deme | pair | deme | deme | deme) <;> rfl
  right_inv := by
    intro stage
    cases stage <;> rfl

/-- A sum over the five stages splits into the resampling block, the ordered migration pairs,
and the three single-deme pulse blocks. -/
theorem sum_stage {D : ℕ} (score : Stage D → ℝ) :
    ∑ stage : Stage D, score stage =
      (∑ deme, score (.drift deme)) +
        ((∑ source, ∑ recipient, score (.migration source recipient)) +
          ((∑ deme, score (.recombination deme)) +
            ((∑ deme, score (.mutationLeft deme)) +
              ∑ deme, score (.mutationRight deme)))) := by
  rw [← Fintype.sum_equiv (sumStageEquiv D)
    (fun value ↦ score (sumStageEquiv D value)) score (fun _ ↦ rfl)]
  simp [Fintype.sum_sum_type, Fintype.sum_prod_type, sumStageEquiv]

/-! ## The three missing right-locus heterozygosity velocities -/

/-- A recombination pulse redraws haplotypes from the product of the deme's own marginals, so
it moves no marginal allele frequency and no right-locus heterozygosity. -/
theorem recombinationRightHeterozygosity_velocity {D : ℕ} (target first second : Fin D)
    (state : DemeHaplotypeState D) :
    ((recombinationCoordinateExpansion target).rightHeterozygosity first second).velocity
      state = 0 := by
  simp [PulseCoordinateExpansion.rightHeterozygosity, PulseExpansion.ofEq,
    PulseExpansion.add, PulseExpansion.mul, PulseExpansion.smul, PulseExpansion.const,
    recombinationCoordinateExpansion, recombinationRightExpansion]

/-- A left-locus mutation pulse leaves every right marginal alone, so it moves no right-locus
heterozygosity.  This is the asymmetry that makes the enlargement of NOTE 1 (6) necessary:
the left and right families are driven by different stages. -/
theorem leftMutationRightHeterozygosity_velocity {D : ℕ} (target first second : Fin D)
    (state : DemeHaplotypeState D) :
    ((leftMutationCoordinateExpansion target).rightHeterozygosity first second).velocity
      state = 0 := by
  simp [PulseCoordinateExpansion.rightHeterozygosity, PulseExpansion.ofEq,
    PulseExpansion.add, PulseExpansion.mul, PulseExpansion.smul, PulseExpansion.const,
    leftMutationCoordinateExpansion, leftMutationRightExpansion]

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
        (1 / 2 - twoLocusRightHeterozygosity (state first) (state second)) := by
  by_cases hfirst : first = target <;> by_cases hsecond : second = target <;>
    simp [PulseCoordinateExpansion.rightHeterozygosity, PulseExpansion.ofEq,
      PulseExpansion.add, PulseExpansion.mul, PulseExpansion.smul, PulseExpansion.const,
      rightMutationCoordinateExpansion, rightMutationRightExpansion,
      twoLocusRightHeterozygosity, TwoLocusHaplotypeFrequencies.rightContrast,
      hfirst, hsecond] <;> ring

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
stage moves a constant. -/
def constantStageExpansion (D : ℕ) :
    StageExpansion (TwoLocusDiffusionJet.const (1 : ℝ) : TwoLocusDiffusionJet D) where
  drift := resamplingExpansionConst 1
  migration source recipient :=
    PulseExpansion.const D (migrationPulse source recipient) 1
  recombination deme := PulseExpansion.const D (recombinationPulseAt deme) 1
  mutationLeft deme := PulseExpansion.const D (leftMutationPulseAt deme) 1
  mutationRight deme := PulseExpansion.const D (rightMutationPulseAt deme) 1

/-- **The constant row of the enlarged generator is the sum of its stage velocities.**  Both
sides are zero: every stage is a probability kernel and so fixes the constant observable, and
the enlarged generator's constant row vanishes. -/
theorem stageSum_constant {D : ℕ} (rates : ManyDemeLDRates D)
    (state : DemeHaplotypeState D) :
    (∑ stage : Stage D, stageDrift rates (constantStageExpansion D) stage state) =
      (enlargedLowOrderLDGenerator rates).mulVec (enlargedLowOrderLDFeature state) none := by
  rw [enlargedGenerator_mulVec_constant]
  refine Finset.sum_eq_zero fun stage _ ↦ ?_
  cases stage <;>
    simp [stageDrift, stageVelocity, constantStageExpansion, TwoLocusDiffusionJet.const,
      PulseExpansion.const]

/-! ## The five stage blocks of the right-locus heterozygosity row -/

/-- The enlarged feature vector reads a right-locus heterozygosity coordinate as the value of
the corresponding corpus jet. -/
theorem rightHeterozygosityMoment_heterozygosity {D : ℕ} (state : DemeHaplotypeState D)
    (first second : Fin D) :
    rightHeterozygosityMoment (enlargedLowOrderLDFeature state) (.H first second) =
      (twoLocusRightHJet first second).value state := by
  rw [twoLocusRightHJet_value]
  rfl

/-- The resampling block of the row is the corpus drift channel: a right-locus heterozygosity
decays at the coalescence rate exactly when both its lineages sit in the drifting deme. -/
theorem driftBlock_rightHeterozygosity {D : ℕ} (rates : ManyDemeLDRates D)
    (first second : Fin D) (state : DemeHaplotypeState D) :
    (∑ deme, stageDrift rates (rightHeterozygosityStageExpansion first second)
        (.drift deme) state) =
      lowOrderLDDrift rates
        (rightHeterozygosityMoment (enlargedLowOrderLDFeature state)) (.H first second) := by
  have hterm : ∀ deme : Fin D,
      stageDrift rates (rightHeterozygosityStageExpansion first second)
          (.drift deme) state =
        rates.coalescence deme *
          (if first = deme ∧ second = deme then
            -(twoLocusRightHJet first second).value state else 0) := by
    intro deme
    simp only [stageDrift, stageRate, stageVelocity, rightHeterozygosityStageExpansion]
    rw [twoLocusRightHJet_driftAt]
  rw [Finset.sum_congr rfl (fun deme _ ↦ hterm deme)]
  by_cases hpair : first = second
  · subst hpair
    rw [Finset.sum_eq_single first]
    · simp only [lowOrderLDDrift, if_pos rfl, and_self,
        rightHeterozygosityMoment_heterozygosity]
      ring
    · intro other _ hother
      rw [if_neg (fun hcondition ↦ hother hcondition.1.symm), mul_zero]
    · intro hnotmem
      exact absurd (Finset.mem_univ first) hnotmem
  · have hzero : ∀ deme ∈ (Finset.univ : Finset (Fin D)),
        rates.coalescence deme *
          (if first = deme ∧ second = deme then
            -(twoLocusRightHJet first second).value state else 0) = 0 := by
      intro deme _
      have hcondition : ¬(first = deme ∧ second = deme) := by
        rintro ⟨hleft, hright⟩
        exact hpair (hleft.trans hright.symm)
      rw [if_neg hcondition, mul_zero]
    rw [Finset.sum_eq_zero hzero]
    simp only [lowOrderLDDrift, if_neg hpair]

/-- The migration block of the row is the corpus migration channel: each lineage sitting in
the recipient deme is replaced by the source deme's lineage. -/
theorem migrationBlock_rightHeterozygosity {D : ℕ} (rates : ManyDemeLDRates D)
    (first second : Fin D) (state : DemeHaplotypeState D) :
    (∑ source, ∑ recipient,
        stageDrift rates (rightHeterozygosityStageExpansion first second)
          (.migration source recipient) state) =
      lowOrderLDMigration rates
        (rightHeterozygosityMoment (enlargedLowOrderLDFeature state)) (.H first second) := by
  have hterm : ∀ source recipient : Fin D,
      stageDrift rates (rightHeterozygosityStageExpansion first second)
          (.migration source recipient) state =
        (if first = recipient then
          rates.migration recipient source *
            ((twoLocusRightHJet source second).value state -
              (twoLocusRightHJet first second).value state) else 0) +
        (if second = recipient then
          rates.migration recipient source *
            ((twoLocusRightHJet first source).value state -
              (twoLocusRightHJet first second).value state) else 0) := by
    intro source recipient
    simp only [stageDrift, stageRate, stageVelocity, rightHeterozygosityStageExpansion,
      migrationRightHeterozygosity_velocity]
    by_cases hfirst : first = recipient <;> by_cases hsecond : second = recipient <;>
      simp [hfirst, hsecond] <;> ring
  have hinner : ∀ source : Fin D,
      (∑ recipient, stageDrift rates (rightHeterozygosityStageExpansion first second)
          (.migration source recipient) state) =
        rates.migration first source *
            ((twoLocusRightHJet source second).value state -
              (twoLocusRightHJet first second).value state) +
          rates.migration second source *
            ((twoLocusRightHJet first source).value state -
              (twoLocusRightHJet first second).value state) := by
    intro source
    rw [Finset.sum_congr rfl (fun recipient _ ↦ hterm source recipient),
      Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.sum_ite_eq]
    simp
  rw [Finset.sum_congr rfl (fun source _ ↦ hinner source), Finset.sum_add_distrib]
  simp only [lowOrderLDMigration, rightHeterozygosityMoment_heterozygosity]

/-- The recombination block of the row vanishes, matching the corpus's zero recombination row
at a heterozygosity: a recombination pulse moves no marginal allele frequency. -/
theorem recombinationBlock_rightHeterozygosity {D : ℕ} (rates : ManyDemeLDRates D)
    (first second : Fin D) (state : DemeHaplotypeState D) :
    (∑ deme, stageDrift rates (rightHeterozygosityStageExpansion first second)
        (.recombination deme) state) =
      lowOrderLDRecombination rates
        (rightHeterozygosityMoment (enlargedLowOrderLDFeature state)) (.H first second) := by
  have hzero : ∀ deme ∈ (Finset.univ : Finset (Fin D)),
      stageDrift rates (rightHeterozygosityStageExpansion first second)
        (.recombination deme) state = 0 := by
    intro deme _
    simp only [stageDrift, stageVelocity, rightHeterozygosityStageExpansion,
      recombinationRightHeterozygosity_velocity, mul_zero]
  rw [Finset.sum_eq_zero hzero]
  simp only [lowOrderLDRecombination]

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
    lowOrderLDMutationForcing, enlargedLowOrderLDFeature,
    rightHeterozygosityMoment_heterozygosity, twoLocusRightHJet_value]
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
