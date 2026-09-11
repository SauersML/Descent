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
row.  `stageSum_rightHeterozygosity` is the bridge itself: the rate-weighted stage velocities
of `twoLocusRightHJet first second` add up to exactly the enlarged generator applied to the
enlarged feature vector at the coordinate `H^R (first, second)`, which by
`enlargedGenerator_mulVec_rightHeterozygosity` is the corpus `H` row read at right-locus
indices together with its affine mutation forcing.

Scope.  Only the `H^R` row is proved here.  The stored rows `H`, `DD`, `Dz` and `pi2` need the
same treatment and are NOT done: of their twenty stage cells the corpus and
`PulseJetExpansion` supply eight, and the rest belong to the pulse package.  In particular the
`pi2` row is the one whose right-locus dependence the enlarged generator routes through
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

end

end Descent.Portability.EnlargedGeneratorBridges
