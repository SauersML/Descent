/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Coalescent.StructuredPresentDay
import Descent.Foundations.TransportIdentities

assert_below Descent.Pangenome Descent.PopGen Descent.Spectral Descent.Blindness
assert_below Descent.Conditionals Descent.Portability Descent.Decision Descent.Program

namespace Descent.Coalescent

/-!
# Exact composition of a multi-deme two-locus moment history

The linkage factor between nonadjacent demes does not in general compose as a scalar power
of the adjacent-deme correlation.  Migration couples the complete closed family of `H`,
`DD`, `Dz`, and `pi2` coordinates.  The exact composition law is consequently an ordered
product of the epoch semigroups on that joint state, followed by the requested `DD` readout.

This file supplies that composition law and the concrete Wright--Fisher/diffusion generator
for the closed moment family.  Arbitrary numbers of epochs, demes, splits, migration changes,
mutation changes, and recombination changes are composed without a closure approximation or
fitted distance law.

## Empirical status

Stated once here for the generator entries and the composition machinery built from them,
following `TwoDemeLDClosedForm`'s section: they share one verdict and thirteen copies of it
would be thirteen places for it to drift.

THE GENERATOR ENTRIES ARE THE MODEL.  `lowOrderLDDrift`, `lowOrderLDMigration`,
`lowOrderLDRecombination`, `lowOrderLDMutationCoupling` and `lowOrderLDMutationForcing` are
the Ragsdale--Gravel two-locus moment generator written for an arbitrary deme count, and
`lowOrderLDBasis`, `lowOrderLDHomogeneousGenerator`, `augmentedLowOrderLDGenerator`, and
`LowOrderLDEpoch.propagator` assemble them into matrices and epoch semigroups.  Writing them
down is choosing a
reproduction, migration, mutation and recombination mechanism, not asserting anything about
a population, so no measurement can bear on an entry: what could be wrong is whether a
population is described by this generator at all, and that question is asked wherever the
composed output is compared against something.

THE COMPOSITION LAW IS DERIVED AND NOT MEASURED.  The explicit one-deme equilibrium below
is proved to solve all four stationary equations.  `commonAncestralLowOrderLDState` relabels
that equilibrium across a split, `lowOrderLDSplitTransform` is the label-replacement matrix
a split forces, and `propagateLowOrderLDInstructions` is an ordered `foldl` whose chain law
`propagateLowOrderLDInstructions_append` is proved below.  At positive mutation its ancestral
`DD` is proved strictly positive and its cross-deme Cauchy--Schwarz inequality is equality;
preservation of that moment realizability through the semigroup is still an explicit
downstream obligation.  An arithmetic consequence of a model is true of the model whatever
a population does.

WHAT THIS SECTION DOES NOT COVER, named rather than left silent.  The quantity this file
exists to supply downstream is `LowOrderLDHistory.toDemographicTwoLocusMoments`, whose `DD`
readout becomes `StructuredPresentDay`'s cross-deme LD correlation.  That readout IS an
empirical claim once a demography is filled in -- a simulation can contradict its composed
prediction.  `validation/empirical/momentsld/ldchain_reduction.py` now supplies an independent
exact-rational ancestral-configuration reference for stationary 2-, 3-, and 4-deme chains;
it validates the need for a full-state composition and refutes the two-deme and scalar-power
reductions.  The pre-filed 2-D comparison in `derivation/ld2d_iter.log` has now completed 4x4,
5x5, and 6x6 solves at relative residual below `1e-12`: its mechanical scoring rules out the
shared-one-dimensional-length Bessel proposal at `rho = 1` and fails it at `rho = 5, 20`.
This is evidence against another scalar reduction and for retaining the whole state; it is
not yet a coordinatewise specialization proof for this generator.  The recurrent-biallelic
damping added here also needs its own reference comparison.  Thus the operator form is
derived, while the composed readout remains scientifically ungated.
-/

/-- Redundant but finite carrier of the closed low-order multi-population LD family.
Keeping all ordered population indices avoids quotient bookkeeping; symmetry identities may
be proved by a concrete generator and do not alter the evolution law. -/
inductive LowOrderLDCoordinate (D : ℕ) where
  | H (first second : Fin D)
  | DD (first second : Fin D)
  | Dz (first second third : Fin D)
  | pi2 (first second third fourth : Fin D)
deriving DecidableEq, Fintype, Repr

/-- The four allelic states at a pair of biallelic loci, used as coordinates of the
haplotype-frequency Wright--Fisher simplex. -/
inductive TwoLocusHaplotype where
  | AB
  | Ab
  | aB
  | ab
deriving DecidableEq, Fintype, Repr

/-- Add a constant coordinate so mutation influx and other affine source terms evolve in the
same matrix exponential as the homogeneous moments. -/
abbrev AffineLowOrderLDCoordinate (D : ℕ) := Option (LowOrderLDCoordinate D)

/-- Four nonnegative two-locus haplotype frequencies on the probability simplex.
The names record alleles at the left (`A/a`) and right (`B/b`) loci. -/
structure TwoLocusHaplotypeFrequencies where
  AB : ℝ
  Ab : ℝ
  aB : ℝ
  ab : ℝ
  AB_nonneg : 0 ≤ AB
  Ab_nonneg : 0 ≤ Ab
  aB_nonneg : 0 ≤ aB
  ab_nonneg : 0 ≤ ab
  total_eq_one : AB + Ab + aB + ab = 1

namespace TwoLocusHaplotypeFrequencies

/-- Frequency of allele `A` at the left locus. -/
def leftFrequency (frequency : TwoLocusHaplotypeFrequencies) : ℝ :=
  frequency.AB + frequency.Ab

/-- Frequency of allele `B` at the right locus. -/
def rightFrequency (frequency : TwoLocusHaplotypeFrequencies) : ℝ :=
  frequency.AB + frequency.aB

/-- Centered left-locus allele-frequency contrast used by the Hill--Robertson `Dz` basis. -/
def leftContrast (frequency : TwoLocusHaplotypeFrequencies) : ℝ :=
  1 - 2 * frequency.leftFrequency

/-- Centered right-locus allele-frequency contrast used by the Hill--Robertson `Dz` basis. -/
def rightContrast (frequency : TwoLocusHaplotypeFrequencies) : ℝ :=
  1 - 2 * frequency.rightFrequency

/-- Linkage disequilibrium in determinant form. -/
def linkage (frequency : TwoLocusHaplotypeFrequencies) : ℝ :=
  frequency.AB * frequency.ab - frequency.Ab * frequency.aB

theorem leftFrequency_nonneg (frequency : TwoLocusHaplotypeFrequencies) :
    0 ≤ frequency.leftFrequency := by
  exact add_nonneg frequency.AB_nonneg frequency.Ab_nonneg

theorem leftFrequency_le_one (frequency : TwoLocusHaplotypeFrequencies) :
    frequency.leftFrequency ≤ 1 := by
  dsimp [leftFrequency]
  linarith [frequency.aB_nonneg, frequency.ab_nonneg, frequency.total_eq_one]

theorem rightFrequency_nonneg (frequency : TwoLocusHaplotypeFrequencies) :
    0 ≤ frequency.rightFrequency := by
  exact add_nonneg frequency.AB_nonneg frequency.aB_nonneg

theorem rightFrequency_le_one (frequency : TwoLocusHaplotypeFrequencies) :
    frequency.rightFrequency ≤ 1 := by
  dsimp [rightFrequency]
  linarith [frequency.Ab_nonneg, frequency.ab_nonneg, frequency.total_eq_one]

/-- Haplotype-wise migration/admixture with source fraction `alpha`.  Unlike a formula
written only for marginal allele frequencies, this operation retains arbitrary linkage in
both the source and recipient populations. -/
noncomputable def mixture (alpha : ℝ) (alpha_nonneg : 0 ≤ alpha) (alpha_le_one : alpha ≤ 1)
    (source recipient : TwoLocusHaplotypeFrequencies) : TwoLocusHaplotypeFrequencies where
  AB := alpha * source.AB + (1 - alpha) * recipient.AB
  Ab := alpha * source.Ab + (1 - alpha) * recipient.Ab
  aB := alpha * source.aB + (1 - alpha) * recipient.aB
  ab := alpha * source.ab + (1 - alpha) * recipient.ab
  AB_nonneg := add_nonneg (mul_nonneg alpha_nonneg source.AB_nonneg)
    (mul_nonneg (sub_nonneg.mpr alpha_le_one) recipient.AB_nonneg)
  Ab_nonneg := add_nonneg (mul_nonneg alpha_nonneg source.Ab_nonneg)
    (mul_nonneg (sub_nonneg.mpr alpha_le_one) recipient.Ab_nonneg)
  aB_nonneg := add_nonneg (mul_nonneg alpha_nonneg source.aB_nonneg)
    (mul_nonneg (sub_nonneg.mpr alpha_le_one) recipient.aB_nonneg)
  ab_nonneg := add_nonneg (mul_nonneg alpha_nonneg source.ab_nonneg)
    (mul_nonneg (sub_nonneg.mpr alpha_le_one) recipient.ab_nonneg)
  total_eq_one := by
    linear_combination
      alpha * source.total_eq_one + (1 - alpha) * recipient.total_eq_one

/-- Marginalization commutes exactly with haplotype mixture at the left locus. -/
theorem mixture_leftFrequency (alpha : ℝ) (alpha_nonneg : 0 ≤ alpha)
    (alpha_le_one : alpha ≤ 1) (source recipient : TwoLocusHaplotypeFrequencies) :
    (mixture alpha alpha_nonneg alpha_le_one source recipient).leftFrequency =
      alpha * source.leftFrequency + (1 - alpha) * recipient.leftFrequency := by
  simp only [mixture, leftFrequency]
  ring

/-- Marginalization commutes exactly with haplotype mixture at the right locus. -/
theorem mixture_rightFrequency (alpha : ℝ) (alpha_nonneg : 0 ≤ alpha)
    (alpha_le_one : alpha ≤ 1) (source recipient : TwoLocusHaplotypeFrequencies) :
    (mixture alpha alpha_nonneg alpha_le_one source recipient).rightFrequency =
      alpha * source.rightFrequency + (1 - alpha) * recipient.rightFrequency := by
  simp only [mixture, rightFrequency]
  ring

/-- Centered left contrasts mix linearly, so their migration velocity is simply source
minus recipient contrast. -/
theorem mixture_leftContrast (alpha : ℝ) (alpha_nonneg : 0 ≤ alpha)
    (alpha_le_one : alpha ≤ 1) (source recipient : TwoLocusHaplotypeFrequencies) :
    (mixture alpha alpha_nonneg alpha_le_one source recipient).leftContrast =
      alpha * source.leftContrast + (1 - alpha) * recipient.leftContrast := by
  rw [leftContrast, mixture_leftFrequency]
  simp only [leftContrast]
  ring

/-- Centered right contrasts obey the same exact mixture law. -/
theorem mixture_rightContrast (alpha : ℝ) (alpha_nonneg : 0 ≤ alpha)
    (alpha_le_one : alpha ≤ 1) (source recipient : TwoLocusHaplotypeFrequencies) :
    (mixture alpha alpha_nonneg alpha_le_one source recipient).rightContrast =
      alpha * source.rightContrast + (1 - alpha) * recipient.rightContrast := by
  rw [rightContrast, mixture_rightFrequency]
  simp only [rightContrast]
  ring

/-- **Exact migration-restoration identity.**  Mixing retains the two parental linkage
terms and creates an additional joint channel from simultaneous differentiation at the two
loci.  No linkage-equilibrium assumption or fitted restoration coefficient is present. -/
theorem mixture_linkage (alpha : ℝ) (alpha_nonneg : 0 ≤ alpha)
    (alpha_le_one : alpha ≤ 1) (source recipient : TwoLocusHaplotypeFrequencies) :
    (mixture alpha alpha_nonneg alpha_le_one source recipient).linkage =
      alpha * source.linkage + (1 - alpha) * recipient.linkage +
        alpha * (1 - alpha) * (source.leftFrequency - recipient.leftFrequency) *
          (source.rightFrequency - recipient.rightFrequency) := by
  have source_ab : source.ab = 1 - source.AB - source.Ab - source.aB := by
    linarith [source.total_eq_one]
  have recipient_ab : recipient.ab = 1 - recipient.AB - recipient.Ab - recipient.aB := by
    linarith [recipient.total_eq_one]
  simp only [mixture, linkage, leftFrequency, rightFrequency]
  rw [source_ab, recipient_ab]
  ring

/-- The same law separated into its exact first-order migration term and quadratic pulse
correction.  The coefficient of `alpha` is the infinitesimal restoration term consumed by
the continuous migration generator. -/
theorem mixture_linkage_firstOrder (alpha : ℝ) (alpha_nonneg : 0 ≤ alpha)
    (alpha_le_one : alpha ≤ 1) (source recipient : TwoLocusHaplotypeFrequencies) :
    (mixture alpha alpha_nonneg alpha_le_one source recipient).linkage =
      recipient.linkage + alpha *
        (source.linkage - recipient.linkage +
          (source.leftFrequency - recipient.leftFrequency) *
            (source.rightFrequency - recipient.rightFrequency)) -
        alpha ^ 2 * (source.leftFrequency - recipient.leftFrequency) *
          (source.rightFrequency - recipient.rightFrequency) := by
  rw [mixture_linkage]
  ring

/-- Infinitesimal change of recipient linkage under haplotype migration from `source`. -/
def migrationLinkageVelocity
    (source recipient : TwoLocusHaplotypeFrequencies) : ℝ :=
  source.linkage - recipient.linkage +
    (source.leftFrequency - recipient.leftFrequency) *
      (source.rightFrequency - recipient.rightFrequency)

/-- The infinitesimal restoration term in the centered contrast coordinates used by the
closed low-order moment system. -/
theorem migrationLinkageVelocity_eq_contrasts
    (source recipient : TwoLocusHaplotypeFrequencies) :
    migrationLinkageVelocity source recipient =
      source.linkage - recipient.linkage +
        (recipient.leftContrast - source.leftContrast) *
          (recipient.rightContrast - source.rightContrast) / 4 := by
  simp only [migrationLinkageVelocity, leftContrast, rightContrast]
  ring

/-- The exact pulse law is recipient linkage plus a first-order migration velocity and the
finite-pulse quadratic correction. -/
theorem mixture_linkage_eq_velocity (alpha : ℝ) (alpha_nonneg : 0 ≤ alpha)
    (alpha_le_one : alpha ≤ 1) (source recipient : TwoLocusHaplotypeFrequencies) :
    (mixture alpha alpha_nonneg alpha_le_one source recipient).linkage =
      recipient.linkage + alpha * migrationLinkageVelocity source recipient -
        alpha ^ 2 * (source.leftFrequency - recipient.leftFrequency) *
          (source.rightFrequency - recipient.rightFrequency) := by
  rw [mixture_linkage_firstOrder]
  rfl

/-- The linkage-equilibrium haplotype distribution with exactly the same two marginal
allele frequencies as `frequency`. -/
noncomputable def linkageEquilibrium
    (frequency : TwoLocusHaplotypeFrequencies) : TwoLocusHaplotypeFrequencies where
  AB := frequency.leftFrequency * frequency.rightFrequency
  Ab := frequency.leftFrequency * (1 - frequency.rightFrequency)
  aB := (1 - frequency.leftFrequency) * frequency.rightFrequency
  ab := (1 - frequency.leftFrequency) * (1 - frequency.rightFrequency)
  AB_nonneg := mul_nonneg frequency.leftFrequency_nonneg frequency.rightFrequency_nonneg
  Ab_nonneg := mul_nonneg frequency.leftFrequency_nonneg
    (sub_nonneg.mpr frequency.rightFrequency_le_one)
  aB_nonneg := mul_nonneg (sub_nonneg.mpr frequency.leftFrequency_le_one)
    frequency.rightFrequency_nonneg
  ab_nonneg := mul_nonneg (sub_nonneg.mpr frequency.leftFrequency_le_one)
    (sub_nonneg.mpr frequency.rightFrequency_le_one)
  total_eq_one := by ring

/-- Linkage equilibrium preserves the left marginal exactly. -/
theorem linkageEquilibrium_leftFrequency
    (frequency : TwoLocusHaplotypeFrequencies) :
    (linkageEquilibrium frequency).leftFrequency = frequency.leftFrequency := by
  simp only [linkageEquilibrium, leftFrequency]
  ring

/-- Linkage equilibrium preserves the right marginal exactly. -/
theorem linkageEquilibrium_rightFrequency
    (frequency : TwoLocusHaplotypeFrequencies) :
    (linkageEquilibrium frequency).rightFrequency = frequency.rightFrequency := by
  simp only [linkageEquilibrium, rightFrequency]
  ring

/-- The product-of-marginals construction has identically zero linkage. -/
theorem linkageEquilibrium_linkage
    (frequency : TwoLocusHaplotypeFrequencies) :
    (linkageEquilibrium frequency).linkage = 0 := by
  simp only [linkageEquilibrium, linkage]
  ring

/-- An exact recombination pulse: an `alpha` fraction is redrawn from the product of the
current marginals and the remainder retains the parental haplotype.  Convexity proves that
the result remains on the haplotype simplex. -/
noncomputable def recombinationPulse
    (alpha : ℝ) (alpha_nonneg : 0 ≤ alpha) (alpha_le_one : alpha ≤ 1)
    (frequency : TwoLocusHaplotypeFrequencies) : TwoLocusHaplotypeFrequencies :=
  mixture alpha alpha_nonneg alpha_le_one (linkageEquilibrium frequency) frequency

/-- Recombination changes no left-locus allele frequency. -/
theorem recombinationPulse_leftFrequency
    (alpha : ℝ) (alpha_nonneg : 0 ≤ alpha) (alpha_le_one : alpha ≤ 1)
    (frequency : TwoLocusHaplotypeFrequencies) :
    (recombinationPulse alpha alpha_nonneg alpha_le_one frequency).leftFrequency =
      frequency.leftFrequency := by
  rw [recombinationPulse, mixture_leftFrequency, linkageEquilibrium_leftFrequency]
  ring

/-- Recombination changes no right-locus allele frequency. -/
theorem recombinationPulse_rightFrequency
    (alpha : ℝ) (alpha_nonneg : 0 ≤ alpha) (alpha_le_one : alpha ≤ 1)
    (frequency : TwoLocusHaplotypeFrequencies) :
    (recombinationPulse alpha alpha_nonneg alpha_le_one frequency).rightFrequency =
      frequency.rightFrequency := by
  rw [recombinationPulse, mixture_rightFrequency, linkageEquilibrium_rightFrequency]
  ring

/-- Recombination preserves the centered left contrast. -/
theorem recombinationPulse_leftContrast
    (alpha : ℝ) (alpha_nonneg : 0 ≤ alpha) (alpha_le_one : alpha ≤ 1)
    (frequency : TwoLocusHaplotypeFrequencies) :
    (recombinationPulse alpha alpha_nonneg alpha_le_one frequency).leftContrast =
      frequency.leftContrast := by
  simp only [leftContrast, recombinationPulse_leftFrequency]

/-- Recombination preserves the centered right contrast. -/
theorem recombinationPulse_rightContrast
    (alpha : ℝ) (alpha_nonneg : 0 ≤ alpha) (alpha_le_one : alpha ≤ 1)
    (frequency : TwoLocusHaplotypeFrequencies) :
    (recombinationPulse alpha alpha_nonneg alpha_le_one frequency).rightContrast =
      frequency.rightContrast := by
  simp only [rightContrast, recombinationPulse_rightFrequency]

/-- **Exact recombination law.**  A pulse retaining fraction `1-alpha` of parental
haplotypes retains exactly that fraction of linkage disequilibrium. -/
theorem recombinationPulse_linkage
    (alpha : ℝ) (alpha_nonneg : 0 ≤ alpha) (alpha_le_one : alpha ≤ 1)
    (frequency : TwoLocusHaplotypeFrequencies) :
    (recombinationPulse alpha alpha_nonneg alpha_le_one frequency).linkage =
      (1 - alpha) * frequency.linkage := by
  rw [recombinationPulse, mixture_linkage, linkageEquilibrium_linkage,
    linkageEquilibrium_leftFrequency, linkageEquilibrium_rightFrequency]
  ring

/-- Infinitesimal linkage velocity generated by recombination. -/
def recombinationLinkageVelocity (frequency : TwoLocusHaplotypeFrequencies) : ℝ :=
  -frequency.linkage

/-- The exact pulse is the initial linkage plus pulse size times its recombination velocity. -/
theorem recombinationPulse_linkage_eq_velocity
    (alpha : ℝ) (alpha_nonneg : 0 ≤ alpha) (alpha_le_one : alpha ≤ 1)
    (frequency : TwoLocusHaplotypeFrequencies) :
    (recombinationPulse alpha alpha_nonneg alpha_le_one frequency).linkage =
      frequency.linkage + alpha * frequency.recombinationLinkageVelocity := by
  rw [recombinationPulse_linkage]
  simp only [recombinationLinkageVelocity]
  ring

/-- Complement the allele at the left locus while leaving the right allele unchanged. -/
def leftAlleleFlip
    (frequency : TwoLocusHaplotypeFrequencies) : TwoLocusHaplotypeFrequencies where
  AB := frequency.aB
  Ab := frequency.ab
  aB := frequency.AB
  ab := frequency.Ab
  AB_nonneg := frequency.aB_nonneg
  Ab_nonneg := frequency.ab_nonneg
  aB_nonneg := frequency.AB_nonneg
  ab_nonneg := frequency.Ab_nonneg
  total_eq_one := by linarith [frequency.total_eq_one]

/-- Complementing the left allele sends its marginal frequency to `1-p`. -/
theorem leftAlleleFlip_leftFrequency (frequency : TwoLocusHaplotypeFrequencies) :
    (leftAlleleFlip frequency).leftFrequency = 1 - frequency.leftFrequency := by
  simp only [leftAlleleFlip, leftFrequency]
  linarith [frequency.total_eq_one]

/-- Complementing the left allele preserves the right marginal. -/
theorem leftAlleleFlip_rightFrequency (frequency : TwoLocusHaplotypeFrequencies) :
    (leftAlleleFlip frequency).rightFrequency = frequency.rightFrequency := by
  simp only [leftAlleleFlip, rightFrequency]
  ring

/-- Complementing either allele reverses linkage phase. -/
theorem leftAlleleFlip_linkage (frequency : TwoLocusHaplotypeFrequencies) :
    (leftAlleleFlip frequency).linkage = -frequency.linkage := by
  simp only [leftAlleleFlip, linkage]
  ring

/-- Complement the allele at the right locus while leaving the left allele unchanged. -/
def rightAlleleFlip
    (frequency : TwoLocusHaplotypeFrequencies) : TwoLocusHaplotypeFrequencies where
  AB := frequency.Ab
  Ab := frequency.AB
  aB := frequency.ab
  ab := frequency.aB
  AB_nonneg := frequency.Ab_nonneg
  Ab_nonneg := frequency.AB_nonneg
  aB_nonneg := frequency.ab_nonneg
  ab_nonneg := frequency.aB_nonneg
  total_eq_one := by linarith [frequency.total_eq_one]

/-- Complementing the right allele preserves the left marginal. -/
theorem rightAlleleFlip_leftFrequency (frequency : TwoLocusHaplotypeFrequencies) :
    (rightAlleleFlip frequency).leftFrequency = frequency.leftFrequency := by
  simp only [rightAlleleFlip, leftFrequency]
  ring

/-- Complementing the right allele sends its marginal frequency to `1-q`. -/
theorem rightAlleleFlip_rightFrequency (frequency : TwoLocusHaplotypeFrequencies) :
    (rightAlleleFlip frequency).rightFrequency = 1 - frequency.rightFrequency := by
  simp only [rightAlleleFlip, rightFrequency]
  linarith [frequency.total_eq_one]

/-- Complementing the right allele also reverses linkage phase. -/
theorem rightAlleleFlip_linkage (frequency : TwoLocusHaplotypeFrequencies) :
    (rightAlleleFlip frequency).linkage = -frequency.linkage := by
  simp only [rightAlleleFlip, linkage]
  ring

/-- Exact symmetric-biallelic mutation pulse at the left locus: flip the left allele of an
`epsilon` fraction of haplotypes. -/
noncomputable def leftMutationPulse
    (epsilon : ℝ) (epsilon_nonneg : 0 ≤ epsilon) (epsilon_le_one : epsilon ≤ 1)
    (frequency : TwoLocusHaplotypeFrequencies) : TwoLocusHaplotypeFrequencies :=
  mixture epsilon epsilon_nonneg epsilon_le_one (leftAlleleFlip frequency) frequency

/-- A left-locus mutation pulse multiplies the centered left contrast by `1-2 epsilon`. -/
theorem leftMutationPulse_leftContrast
    (epsilon : ℝ) (epsilon_nonneg : 0 ≤ epsilon) (epsilon_le_one : epsilon ≤ 1)
    (frequency : TwoLocusHaplotypeFrequencies) :
    (leftMutationPulse epsilon epsilon_nonneg epsilon_le_one frequency).leftContrast =
      (1 - 2 * epsilon) * frequency.leftContrast := by
  rw [leftContrast, leftMutationPulse, mixture_leftFrequency,
    leftAlleleFlip_leftFrequency]
  simp only [leftContrast]
  ring

/-- A left-locus mutation pulse preserves the right contrast. -/
theorem leftMutationPulse_rightContrast
    (epsilon : ℝ) (epsilon_nonneg : 0 ≤ epsilon) (epsilon_le_one : epsilon ≤ 1)
    (frequency : TwoLocusHaplotypeFrequencies) :
    (leftMutationPulse epsilon epsilon_nonneg epsilon_le_one frequency).rightContrast =
      frequency.rightContrast := by
  rw [rightContrast, leftMutationPulse, mixture_rightFrequency,
    leftAlleleFlip_rightFrequency]
  simp only [rightContrast]
  ring

/-- A left-locus mutation pulse retains exactly `1-2 epsilon` of linkage. -/
theorem leftMutationPulse_linkage
    (epsilon : ℝ) (epsilon_nonneg : 0 ≤ epsilon) (epsilon_le_one : epsilon ≤ 1)
    (frequency : TwoLocusHaplotypeFrequencies) :
    (leftMutationPulse epsilon epsilon_nonneg epsilon_le_one frequency).linkage =
      (1 - 2 * epsilon) * frequency.linkage := by
  rw [leftMutationPulse, mixture_linkage, leftAlleleFlip_linkage,
    leftAlleleFlip_leftFrequency, leftAlleleFlip_rightFrequency]
  ring

/-- Exact symmetric-biallelic mutation pulse at the right locus. -/
noncomputable def rightMutationPulse
    (epsilon : ℝ) (epsilon_nonneg : 0 ≤ epsilon) (epsilon_le_one : epsilon ≤ 1)
    (frequency : TwoLocusHaplotypeFrequencies) : TwoLocusHaplotypeFrequencies :=
  mixture epsilon epsilon_nonneg epsilon_le_one (rightAlleleFlip frequency) frequency

/-- A right-locus mutation pulse preserves the left contrast. -/
theorem rightMutationPulse_leftContrast
    (epsilon : ℝ) (epsilon_nonneg : 0 ≤ epsilon) (epsilon_le_one : epsilon ≤ 1)
    (frequency : TwoLocusHaplotypeFrequencies) :
    (rightMutationPulse epsilon epsilon_nonneg epsilon_le_one frequency).leftContrast =
      frequency.leftContrast := by
  rw [leftContrast, rightMutationPulse, mixture_leftFrequency,
    rightAlleleFlip_leftFrequency]
  simp only [leftContrast]
  ring

/-- A right-locus mutation pulse multiplies the centered right contrast by `1-2 epsilon`. -/
theorem rightMutationPulse_rightContrast
    (epsilon : ℝ) (epsilon_nonneg : 0 ≤ epsilon) (epsilon_le_one : epsilon ≤ 1)
    (frequency : TwoLocusHaplotypeFrequencies) :
    (rightMutationPulse epsilon epsilon_nonneg epsilon_le_one frequency).rightContrast =
      (1 - 2 * epsilon) * frequency.rightContrast := by
  rw [rightContrast, rightMutationPulse, mixture_rightFrequency,
    rightAlleleFlip_rightFrequency]
  simp only [rightContrast]
  ring

/-- A right-locus mutation pulse retains exactly `1-2 epsilon` of linkage. -/
theorem rightMutationPulse_linkage
    (epsilon : ℝ) (epsilon_nonneg : 0 ≤ epsilon) (epsilon_le_one : epsilon ≤ 1)
    (frequency : TwoLocusHaplotypeFrequencies) :
    (rightMutationPulse epsilon epsilon_nonneg epsilon_le_one frequency).linkage =
      (1 - 2 * epsilon) * frequency.linkage := by
  rw [rightMutationPulse, mixture_linkage, rightAlleleFlip_linkage,
    rightAlleleFlip_leftFrequency, rightAlleleFlip_rightFrequency]
  ring

/-- Independent symmetric mutation pulses at both loci, implemented as the composition of
the two exact simplex-preserving allele-flip channels. -/
noncomputable def twoLocusMutationPulse
    (epsilonLeft : ℝ) (epsilonLeft_nonneg : 0 ≤ epsilonLeft)
    (epsilonLeft_le_one : epsilonLeft ≤ 1)
    (epsilonRight : ℝ) (epsilonRight_nonneg : 0 ≤ epsilonRight)
    (epsilonRight_le_one : epsilonRight ≤ 1)
    (frequency : TwoLocusHaplotypeFrequencies) : TwoLocusHaplotypeFrequencies :=
  rightMutationPulse epsilonRight epsilonRight_nonneg epsilonRight_le_one
    (leftMutationPulse epsilonLeft epsilonLeft_nonneg epsilonLeft_le_one frequency)

/-- The two-locus mutation pulse scales the left contrast only by its left-channel
retention. -/
theorem twoLocusMutationPulse_leftContrast
    (epsilonLeft : ℝ) (epsilonLeft_nonneg : 0 ≤ epsilonLeft)
    (epsilonLeft_le_one : epsilonLeft ≤ 1)
    (epsilonRight : ℝ) (epsilonRight_nonneg : 0 ≤ epsilonRight)
    (epsilonRight_le_one : epsilonRight ≤ 1)
    (frequency : TwoLocusHaplotypeFrequencies) :
    (twoLocusMutationPulse epsilonLeft epsilonLeft_nonneg epsilonLeft_le_one
      epsilonRight epsilonRight_nonneg epsilonRight_le_one frequency).leftContrast =
      (1 - 2 * epsilonLeft) * frequency.leftContrast := by
  rw [twoLocusMutationPulse, rightMutationPulse_leftContrast,
    leftMutationPulse_leftContrast]

/-- The two-locus mutation pulse scales the right contrast only by its right-channel
retention. -/
theorem twoLocusMutationPulse_rightContrast
    (epsilonLeft : ℝ) (epsilonLeft_nonneg : 0 ≤ epsilonLeft)
    (epsilonLeft_le_one : epsilonLeft ≤ 1)
    (epsilonRight : ℝ) (epsilonRight_nonneg : 0 ≤ epsilonRight)
    (epsilonRight_le_one : epsilonRight ≤ 1)
    (frequency : TwoLocusHaplotypeFrequencies) :
    (twoLocusMutationPulse epsilonLeft epsilonLeft_nonneg epsilonLeft_le_one
      epsilonRight epsilonRight_nonneg epsilonRight_le_one frequency).rightContrast =
      (1 - 2 * epsilonRight) * frequency.rightContrast := by
  rw [twoLocusMutationPulse, rightMutationPulse_rightContrast,
    leftMutationPulse_rightContrast]

/-- **Exact two-locus symmetric-mutation linkage law.**  The linkage retention is the
product of the two single-locus contrast retentions. -/
theorem twoLocusMutationPulse_linkage
    (epsilonLeft : ℝ) (epsilonLeft_nonneg : 0 ≤ epsilonLeft)
    (epsilonLeft_le_one : epsilonLeft ≤ 1)
    (epsilonRight : ℝ) (epsilonRight_nonneg : 0 ≤ epsilonRight)
    (epsilonRight_le_one : epsilonRight ≤ 1)
    (frequency : TwoLocusHaplotypeFrequencies) :
    (twoLocusMutationPulse epsilonLeft epsilonLeft_nonneg epsilonLeft_le_one
      epsilonRight epsilonRight_nonneg epsilonRight_le_one frequency).linkage =
      (1 - 2 * epsilonLeft) * (1 - 2 * epsilonRight) * frequency.linkage := by
  rw [twoLocusMutationPulse, rightMutationPulse_linkage, leftMutationPulse_linkage]
  ring

/-- Scaled symmetric-mutation velocity of the left centered contrast when the rate
coordinate is `theta = 2u`. -/
def scaledMutationLeftContrastVelocity
    (frequency : TwoLocusHaplotypeFrequencies) : ℝ :=
  -frequency.leftContrast

/-- Scaled symmetric-mutation velocity of the right centered contrast. -/
def scaledMutationRightContrastVelocity
    (frequency : TwoLocusHaplotypeFrequencies) : ℝ :=
  -frequency.rightContrast

/-- Scaled symmetric-mutation velocity of linkage.  Both loci mutate, so the two contrast
decay channels add and give `-2D`. -/
def scaledMutationLinkageVelocity
    (frequency : TwoLocusHaplotypeFrequencies) : ℝ :=
  -2 * frequency.linkage

/-- The exact one-locus mutation pulse exposes the scaled left-contrast velocity with pulse
coordinate `2 epsilon`. -/
theorem leftMutationPulse_leftContrast_eq_velocity
    (epsilon : ℝ) (epsilon_nonneg : 0 ≤ epsilon) (epsilon_le_one : epsilon ≤ 1)
    (frequency : TwoLocusHaplotypeFrequencies) :
    (leftMutationPulse epsilon epsilon_nonneg epsilon_le_one frequency).leftContrast =
      frequency.leftContrast +
        (2 * epsilon) * frequency.scaledMutationLeftContrastVelocity := by
  rw [leftMutationPulse_leftContrast]
  simp only [scaledMutationLeftContrastVelocity]
  ring

/-- The exact right-locus pulse exposes the analogous scaled velocity. -/
theorem rightMutationPulse_rightContrast_eq_velocity
    (epsilon : ℝ) (epsilon_nonneg : 0 ≤ epsilon) (epsilon_le_one : epsilon ≤ 1)
    (frequency : TwoLocusHaplotypeFrequencies) :
    (rightMutationPulse epsilon epsilon_nonneg epsilon_le_one frequency).rightContrast =
      frequency.rightContrast +
        (2 * epsilon) * frequency.scaledMutationRightContrastVelocity := by
  rw [rightMutationPulse_rightContrast]
  simp only [scaledMutationRightContrastVelocity]
  ring

/-- With equal mutation at both loci, the exact finite pulse is its first-order scaled
linkage velocity plus the explicit second-order two-mutation correction. -/
theorem twoLocusMutationPulse_linkage_eq_velocity
    (epsilon : ℝ) (epsilon_nonneg : 0 ≤ epsilon) (epsilon_le_one : epsilon ≤ 1)
    (frequency : TwoLocusHaplotypeFrequencies) :
    (twoLocusMutationPulse epsilon epsilon_nonneg epsilon_le_one
      epsilon epsilon_nonneg epsilon_le_one frequency).linkage =
      frequency.linkage + (2 * epsilon) * frequency.scaledMutationLinkageVelocity +
        (2 * epsilon) ^ 2 * frequency.linkage := by
  rw [twoLocusMutationPulse_linkage]
  simp only [scaledMutationLinkageVelocity]
  ring

/-- The older linkage-equilibrium admixture law is the zero-parental-linkage specialization
of the general identity, rather than a separate mechanism. -/
theorem mixture_linkage_of_parental_linkage_zero (alpha : ℝ)
    (alpha_nonneg : 0 ≤ alpha) (alpha_le_one : alpha ≤ 1)
    (source recipient : TwoLocusHaplotypeFrequencies)
    (source_unlinked : source.linkage = 0) (recipient_unlinked : recipient.linkage = 0) :
    (mixture alpha alpha_nonneg alpha_le_one source recipient).linkage =
      alpha * (1 - alpha) * (source.leftFrequency - recipient.leftFrequency) *
        (source.rightFrequency - recipient.rightFrequency) := by
  rw [mixture_linkage, source_unlinked, recipient_unlinked]
  ring

/-- The determinant definition and the probability simplex give the sharp universal
linkage bound `|D| ≤ 1/4`.  Equality is attained by a half-`AB`, half-`ab` population (or
the corresponding repulsion-phase population). -/
theorem linkage_abs_le_quarter (frequency : TwoLocusHaplotypeFrequencies) :
    |frequency.linkage| ≤ 1 / 4 := by
  have hABab_sum_nonneg : 0 ≤ frequency.AB + frequency.ab :=
    add_nonneg frequency.AB_nonneg frequency.ab_nonneg
  have hABab_sum_le_one : frequency.AB + frequency.ab ≤ 1 := by
    linarith [frequency.Ab_nonneg, frequency.aB_nonneg, frequency.total_eq_one]
  have hABab_product_le : frequency.AB * frequency.ab ≤ 1 / 4 := by
    have hinside : 0 ≤ (frequency.AB + frequency.ab) *
        (1 - (frequency.AB + frequency.ab)) :=
      mul_nonneg hABab_sum_nonneg (sub_nonneg.mpr hABab_sum_le_one)
    nlinarith [sq_nonneg (frequency.AB - frequency.ab)]
  have hAbaB_sum_nonneg : 0 ≤ frequency.Ab + frequency.aB :=
    add_nonneg frequency.Ab_nonneg frequency.aB_nonneg
  have hAbaB_sum_le_one : frequency.Ab + frequency.aB ≤ 1 := by
    linarith [frequency.AB_nonneg, frequency.ab_nonneg, frequency.total_eq_one]
  have hAbaB_product_le : frequency.Ab * frequency.aB ≤ 1 / 4 := by
    have hinside : 0 ≤ (frequency.Ab + frequency.aB) *
        (1 - (frequency.Ab + frequency.aB)) :=
      mul_nonneg hAbaB_sum_nonneg (sub_nonneg.mpr hAbaB_sum_le_one)
    nlinarith [sq_nonneg (frequency.Ab - frequency.aB)]
  rw [abs_le]
  constructor <;> dsimp [linkage] <;>
    nlinarith [mul_nonneg frequency.AB_nonneg frequency.ab_nonneg,
      mul_nonneg frequency.Ab_nonneg frequency.aB_nonneg]

/-- A simplex point attaining the positive endpoint of the universal linkage interval. -/
noncomputable def maximalCoupling : TwoLocusHaplotypeFrequencies where
  AB := 1 / 2
  Ab := 0
  aB := 0
  ab := 1 / 2
  AB_nonneg := by norm_num
  Ab_nonneg := by norm_num
  aB_nonneg := by norm_num
  ab_nonneg := by norm_num
  total_eq_one := by norm_num

/-- The `1/4` linkage bound is attained, so it cannot be uniformly improved. -/
theorem maximalCoupling_linkage : maximalCoupling.linkage = 1 / 4 := by
  norm_num [maximalCoupling, linkage]

end TwoLocusHaplotypeFrequencies

/-! ## Primitive multinomial covariance laws -/

/-- Mean of a score on the four haplotypes under one haplotype-frequency simplex point. -/
def twoLocusHaplotypeMean (frequency : TwoLocusHaplotypeFrequencies)
    (score : TwoLocusHaplotype → ℝ) : ℝ :=
  frequency.AB * score .AB + frequency.Ab * score .Ab +
    frequency.aB * score .aB + frequency.ab * score .ab

/-- Exact covariance of two haplotype scores under one multinomial draw. -/
def twoLocusHaplotypeCovariance (frequency : TwoLocusHaplotypeFrequencies)
    (firstScore secondScore : TwoLocusHaplotype → ℝ) : ℝ :=
  twoLocusHaplotypeMean frequency (fun haplotype ↦
      firstScore haplotype * secondScore haplotype) -
    twoLocusHaplotypeMean frequency firstScore *
      twoLocusHaplotypeMean frequency secondScore

/-- Indicator that a haplotype carries `A` at the left locus. -/
def twoLocusLeftAlleleIndicator : TwoLocusHaplotype → ℝ
  | .AB | .Ab => 1
  | .aB | .ab => 0

/-- Indicator that a haplotype carries `B` at the right locus. -/
def twoLocusRightAlleleIndicator : TwoLocusHaplotype → ℝ
  | .AB | .aB => 1
  | .Ab | .ab => 0

/-- Gradient of the haplotype determinant `AB*ab - Ab*aB`. -/
def twoLocusLinkageGradient (frequency : TwoLocusHaplotypeFrequencies) :
    TwoLocusHaplotype → ℝ
  | .AB => frequency.ab
  | .Ab => -frequency.aB
  | .aB => -frequency.Ab
  | .ab => frequency.AB

/-- The multinomial mean of the left indicator is the left marginal frequency. -/
theorem twoLocusHaplotypeMean_leftIndicator
    (frequency : TwoLocusHaplotypeFrequencies) :
    twoLocusHaplotypeMean frequency twoLocusLeftAlleleIndicator =
      frequency.leftFrequency := by
  simp [twoLocusHaplotypeMean, twoLocusLeftAlleleIndicator,
    TwoLocusHaplotypeFrequencies.leftFrequency]

/-- The multinomial mean of the right indicator is the right marginal frequency. -/
theorem twoLocusHaplotypeMean_rightIndicator
    (frequency : TwoLocusHaplotypeFrequencies) :
    twoLocusHaplotypeMean frequency twoLocusRightAlleleIndicator =
      frequency.rightFrequency := by
  simp [twoLocusHaplotypeMean, twoLocusRightAlleleIndicator,
    TwoLocusHaplotypeFrequencies.rightFrequency]

/-- Left marginal quadratic variation is the Bernoulli variance. -/
theorem twoLocusHaplotypeCovariance_left_left
    (frequency : TwoLocusHaplotypeFrequencies) :
    twoLocusHaplotypeCovariance frequency twoLocusLeftAlleleIndicator
        twoLocusLeftAlleleIndicator =
      frequency.leftFrequency * (1 - frequency.leftFrequency) := by
  simp [twoLocusHaplotypeCovariance, twoLocusHaplotypeMean,
    twoLocusLeftAlleleIndicator, TwoLocusHaplotypeFrequencies.leftFrequency]
  ring

/-- Right marginal quadratic variation is the Bernoulli variance. -/
theorem twoLocusHaplotypeCovariance_right_right
    (frequency : TwoLocusHaplotypeFrequencies) :
    twoLocusHaplotypeCovariance frequency twoLocusRightAlleleIndicator
        twoLocusRightAlleleIndicator =
      frequency.rightFrequency * (1 - frequency.rightFrequency) := by
  simp [twoLocusHaplotypeCovariance, twoLocusHaplotypeMean,
    twoLocusRightAlleleIndicator, TwoLocusHaplotypeFrequencies.rightFrequency]
  ring

/-- Cross-locus marginal quadratic covariation is exactly linkage disequilibrium `D`. -/
theorem twoLocusHaplotypeCovariance_left_right
    (frequency : TwoLocusHaplotypeFrequencies) :
    twoLocusHaplotypeCovariance frequency twoLocusLeftAlleleIndicator
        twoLocusRightAlleleIndicator = frequency.linkage := by
  have hab : frequency.ab = 1 - frequency.AB - frequency.Ab - frequency.aB := by
    linarith [frequency.total_eq_one]
  simp [twoLocusHaplotypeCovariance, twoLocusHaplotypeMean,
    twoLocusLeftAlleleIndicator, twoLocusRightAlleleIndicator,
    TwoLocusHaplotypeFrequencies.linkage]
  rw [hab]
  ring

/-- Bilinear scaling of the cross-locus marginal covariance.  This is the exact quadratic
covariation used when composite heterozygosity gradients share a drifting deme. -/
theorem twoLocusHaplotypeCovariance_scaled_left_right
    (frequency : TwoLocusHaplotypeFrequencies) (leftScale rightScale : ℝ) :
    twoLocusHaplotypeCovariance frequency
        (fun haplotype ↦ leftScale * twoLocusLeftAlleleIndicator haplotype)
        (fun haplotype ↦ rightScale * twoLocusRightAlleleIndicator haplotype) =
      leftScale * rightScale * frequency.linkage := by
  have hab : frequency.ab = 1 - frequency.AB - frequency.Ab - frequency.aB := by
    linarith [frequency.total_eq_one]
  simp [twoLocusHaplotypeCovariance, twoLocusHaplotypeMean,
    twoLocusLeftAlleleIndicator, twoLocusRightAlleleIndicator,
    TwoLocusHaplotypeFrequencies.linkage]
  rw [hab]
  ring

/-- Linkage/marginal covariation at the left locus is `D (1-2p)`. -/
theorem twoLocusHaplotypeCovariance_linkage_left
    (frequency : TwoLocusHaplotypeFrequencies) :
    twoLocusHaplotypeCovariance frequency (twoLocusLinkageGradient frequency)
        twoLocusLeftAlleleIndicator =
      frequency.linkage * frequency.leftContrast := by
  have hab : frequency.ab = 1 - frequency.AB - frequency.Ab - frequency.aB := by
    linarith [frequency.total_eq_one]
  simp [twoLocusHaplotypeCovariance, twoLocusHaplotypeMean,
    twoLocusLinkageGradient, twoLocusLeftAlleleIndicator,
    TwoLocusHaplotypeFrequencies.linkage,
    TwoLocusHaplotypeFrequencies.leftContrast,
    TwoLocusHaplotypeFrequencies.leftFrequency]
  rw [hab]
  ring

/-- Linkage/marginal covariation at the right locus is `D (1-2q)`. -/
theorem twoLocusHaplotypeCovariance_linkage_right
    (frequency : TwoLocusHaplotypeFrequencies) :
    twoLocusHaplotypeCovariance frequency (twoLocusLinkageGradient frequency)
        twoLocusRightAlleleIndicator =
      frequency.linkage * frequency.rightContrast := by
  have hab : frequency.ab = 1 - frequency.AB - frequency.Ab - frequency.aB := by
    linarith [frequency.total_eq_one]
  simp [twoLocusHaplotypeCovariance, twoLocusHaplotypeMean,
    twoLocusLinkageGradient, twoLocusRightAlleleIndicator,
    TwoLocusHaplotypeFrequencies.linkage,
    TwoLocusHaplotypeFrequencies.rightContrast,
    TwoLocusHaplotypeFrequencies.rightFrequency]
  rw [hab]
  ring

/-- Exact linkage quadratic variation.  This single identity produces the three terms in
the same-deme `DD` drift row: `-D² + D z w + p(1-p)q(1-q)`. -/
theorem twoLocusHaplotypeCovariance_linkage_linkage
    (frequency : TwoLocusHaplotypeFrequencies) :
    twoLocusHaplotypeCovariance frequency (twoLocusLinkageGradient frequency)
        (twoLocusLinkageGradient frequency) =
      -frequency.linkage ^ 2 +
        frequency.linkage * frequency.leftContrast * frequency.rightContrast +
        frequency.leftFrequency * (1 - frequency.leftFrequency) *
          (frequency.rightFrequency * (1 - frequency.rightFrequency)) := by
  have hab : frequency.ab = 1 - frequency.AB - frequency.Ab - frequency.aB := by
    linarith [frequency.total_eq_one]
  simp [twoLocusHaplotypeCovariance, twoLocusHaplotypeMean,
    twoLocusLinkageGradient, TwoLocusHaplotypeFrequencies.linkage,
    TwoLocusHaplotypeFrequencies.leftContrast,
    TwoLocusHaplotypeFrequencies.rightContrast,
    TwoLocusHaplotypeFrequencies.leftFrequency,
    TwoLocusHaplotypeFrequencies.rightFrequency]
  rw [hab]
  ring

/-- Indicator score for one named haplotype. -/
def twoLocusHaplotypeIndicator (target observed : TwoLocusHaplotype) : ℝ :=
  if observed = target then 1 else 0

/-- The second-order Wright--Fisher generator applied to the haplotype determinant.  The
two mixed derivatives are the covariances of the opposite haplotype pairs. -/
def twoLocusLinkageDrift (frequency : TwoLocusHaplotypeFrequencies) : ℝ :=
  twoLocusHaplotypeCovariance frequency
      (twoLocusHaplotypeIndicator .AB) (twoLocusHaplotypeIndicator .ab) -
    twoLocusHaplotypeCovariance frequency
      (twoLocusHaplotypeIndicator .Ab) (twoLocusHaplotypeIndicator .aB)

/-- Linkage disequilibrium decays at exactly one unit under unit-coalescence neutral drift.
This is derived directly from the four-category multinomial covariance, not postulated as a
row coefficient. -/
theorem twoLocusLinkageDrift_eq_neg_linkage
    (frequency : TwoLocusHaplotypeFrequencies) :
    twoLocusLinkageDrift frequency = -frequency.linkage := by
  simp [twoLocusLinkageDrift, twoLocusHaplotypeCovariance,
    twoLocusHaplotypeMean, twoLocusHaplotypeIndicator,
    TwoLocusHaplotypeFrequencies.linkage]
  ring

/-- Pointwise observable whose expectation is `Dz(i,j,k)`. -/
def twoLocusDzObservable
    (linkageDeme leftDeme rightDeme : TwoLocusHaplotypeFrequencies) : ℝ :=
  linkageDeme.linkage * leftDeme.leftContrast * rightDeme.rightContrast

/-- Multiplying the exact linkage migration velocity by any other deme's linkage produces
exactly the `DD` difference plus the four-`Dz` stencil used by the arbitrary-deme migration
generator. -/
theorem migrationLinkageVelocity_mul_linkage_eq_DD_Dz
    (source recipient other : TwoLocusHaplotypeFrequencies) :
    source.migrationLinkageVelocity recipient * other.linkage =
      source.linkage * other.linkage - recipient.linkage * other.linkage +
        (twoLocusDzObservable other recipient recipient -
          twoLocusDzObservable other recipient source -
          twoLocusDzObservable other source recipient +
          twoLocusDzObservable other source source) / 4 := by
  rw [TwoLocusHaplotypeFrequencies.migrationLinkageVelocity_eq_contrasts]
  simp only [twoLocusDzObservable]
  ring

/-- Symmetric cross-deme heterozygosity at the left locus.  At one deme this is
`2 p (1-p)`, the usual haploid heterozygosity. -/
def twoLocusLeftHeterozygosity
    (first second : TwoLocusHaplotypeFrequencies) : ℝ :=
  first.leftFrequency * (1 - second.leftFrequency) +
    second.leftFrequency * (1 - first.leftFrequency)

/-- Symmetric cross-deme heterozygosity at the right locus. -/
def twoLocusRightHeterozygosity
    (first second : TwoLocusHaplotypeFrequencies) : ℝ :=
  first.rightFrequency * (1 - second.rightFrequency) +
    second.rightFrequency * (1 - first.rightFrequency)

/-- Cross-deme left heterozygosity in centered contrast coordinates. -/
theorem twoLocusLeftHeterozygosity_eq_contrasts
    (first second : TwoLocusHaplotypeFrequencies) :
    twoLocusLeftHeterozygosity first second =
      (1 - first.leftContrast * second.leftContrast) / 2 := by
  simp only [twoLocusLeftHeterozygosity, TwoLocusHaplotypeFrequencies.leftContrast]
  ring

/-- Cross-deme right heterozygosity in centered contrast coordinates. -/
theorem twoLocusRightHeterozygosity_eq_contrasts
    (first second : TwoLocusHaplotypeFrequencies) :
    twoLocusRightHeterozygosity first second =
      (1 - first.rightContrast * second.rightContrast) / 2 := by
  simp only [twoLocusRightHeterozygosity, TwoLocusHaplotypeFrequencies.rightContrast]
  ring

/-- The exact generalized joint-heterozygosity coordinate of the multi-population
Hill--Robertson system:

`pi2(i,j;k,l) = H_left(i,j) H_right(k,l) / 4`.

The factor `1/4` is forced by the four-lineage sampling definition and makes the
within-deme specialization exactly `p(1-p)q(1-q)`. -/
noncomputable def twoLocusJointHeterozygosity
    (leftFirst leftSecond rightFirst rightSecond : TwoLocusHaplotypeFrequencies) : ℝ :=
  twoLocusLeftHeterozygosity leftFirst leftSecond *
    twoLocusRightHeterozygosity rightFirst rightSecond / 4

/-! ## Exact local diffusion jets -/

/-- A function of every deme's haplotype simplex together with its exact local neutral-drift
velocity and gradient.  The gradient is retained because the product rule couples factors
through the multinomial covariance. -/
structure TwoLocusDiffusionJet (D : ℕ) where
  value : (Fin D → TwoLocusHaplotypeFrequencies) → ℝ
  driftAt : Fin D → (Fin D → TwoLocusHaplotypeFrequencies) → ℝ
  gradientAt : Fin D → (Fin D → TwoLocusHaplotypeFrequencies) →
    TwoLocusHaplotype → ℝ

namespace TwoLocusDiffusionJet

/-- Constant observable. -/
def const {D : ℕ} (constant : ℝ) : TwoLocusDiffusionJet D where
  value _ := constant
  driftAt _ _ := 0
  gradientAt _ _ _ := 0

/-- Addition of diffusion jets. -/
def add {D : ℕ} (first second : TwoLocusDiffusionJet D) : TwoLocusDiffusionJet D where
  value state := first.value state + second.value state
  driftAt deme state := first.driftAt deme state + second.driftAt deme state
  gradientAt deme state haplotype :=
    first.gradientAt deme state haplotype + second.gradientAt deme state haplotype

/-- Scalar multiplication of diffusion jets. -/
def smul {D : ℕ} (scalar : ℝ) (observable : TwoLocusDiffusionJet D) :
    TwoLocusDiffusionJet D where
  value state := scalar * observable.value state
  driftAt deme state := scalar * observable.driftAt deme state
  gradientAt deme state haplotype :=
    scalar * observable.gradientAt deme state haplotype

/-- Exact Wright--Fisher diffusion product rule.  The cross term is the multinomial
covariance of the two gradients in the drifting deme. -/
def mul {D : ℕ} (first second : TwoLocusDiffusionJet D) : TwoLocusDiffusionJet D where
  value state := first.value state * second.value state
  driftAt deme state :=
    first.value state * second.driftAt deme state +
      second.value state * first.driftAt deme state +
      twoLocusHaplotypeCovariance (state deme)
        (first.gradientAt deme state) (second.gradientAt deme state)
  gradientAt deme state haplotype :=
    first.value state * second.gradientAt deme state haplotype +
      second.value state * first.gradientAt deme state haplotype

end TwoLocusDiffusionJet

/-- Left marginal frequency in one named deme. -/
def twoLocusLeftFrequencyJet {D : ℕ} (index : Fin D) : TwoLocusDiffusionJet D where
  value state := (state index).leftFrequency
  driftAt _ _ := 0
  gradientAt deme _ haplotype :=
    if deme = index then twoLocusLeftAlleleIndicator haplotype else 0

/-- Right marginal frequency in one named deme. -/
def twoLocusRightFrequencyJet {D : ℕ} (index : Fin D) : TwoLocusDiffusionJet D where
  value state := (state index).rightFrequency
  driftAt _ _ := 0
  gradientAt deme _ haplotype :=
    if deme = index then twoLocusRightAlleleIndicator haplotype else 0

/-- Linkage determinant in one named deme, with its drift obtained from
`twoLocusLinkageDrift_eq_neg_linkage`. -/
def twoLocusLinkageJet {D : ℕ} (index : Fin D) : TwoLocusDiffusionJet D where
  value state := (state index).linkage
  driftAt deme state := if deme = index then twoLocusLinkageDrift (state index) else 0
  gradientAt deme state haplotype :=
    if deme = index then twoLocusLinkageGradient (state index) haplotype else 0

/-- Centered left marginal contrast. -/
def twoLocusLeftContrastJet {D : ℕ} (index : Fin D) : TwoLocusDiffusionJet D :=
  .add (.const 1) (.smul (-2) (twoLocusLeftFrequencyJet index))

/-- Centered right marginal contrast. -/
def twoLocusRightContrastJet {D : ℕ} (index : Fin D) : TwoLocusDiffusionJet D :=
  .add (.const 1) (.smul (-2) (twoLocusRightFrequencyJet index))

/-- Cross-deme left heterozygosity. -/
def twoLocusHJet {D : ℕ} (first second : Fin D) : TwoLocusDiffusionJet D :=
  .add
    (.mul (twoLocusLeftFrequencyJet first)
      (.add (.const 1) (.smul (-1) (twoLocusLeftFrequencyJet second))))
    (.mul (twoLocusLeftFrequencyJet second)
      (.add (.const 1) (.smul (-1) (twoLocusLeftFrequencyJet first))))

/-- Cross-deme right-locus heterozygosity. -/
def twoLocusRightHJet {D : ℕ} (first second : Fin D) : TwoLocusDiffusionJet D :=
  .add
    (.mul (twoLocusRightFrequencyJet first)
      (.add (.const 1) (.smul (-1) (twoLocusRightFrequencyJet second))))
    (.mul (twoLocusRightFrequencyJet second)
      (.add (.const 1) (.smul (-1) (twoLocusRightFrequencyJet first))))

/-- Cross-deme product of linkage determinants. -/
def twoLocusDDJet {D : ℕ} (first second : Fin D) : TwoLocusDiffusionJet D :=
  .mul (twoLocusLinkageJet first) (twoLocusLinkageJet second)

/-- Generalized `Dz` observable. -/
def twoLocusDzJet {D : ℕ} (first second third : Fin D) : TwoLocusDiffusionJet D :=
  .mul (.mul (twoLocusLinkageJet first) (twoLocusLeftContrastJet second))
    (twoLocusRightContrastJet third)

/-- Generalized four-deme joint heterozygosity. -/
noncomputable def twoLocusPi2Jet {D : ℕ} (first second third fourth : Fin D) :
    TwoLocusDiffusionJet D :=
  .smul (1 / 4)
    (.mul (twoLocusHJet first second) (twoLocusRightHJet third fourth))

/-- The `H` jet reads exactly the biological heterozygosity observable. -/
theorem twoLocusHJet_value {D : ℕ}
    (state : Fin D → TwoLocusHaplotypeFrequencies) (first second : Fin D) :
    (twoLocusHJet first second).value state =
      twoLocusLeftHeterozygosity (state first) (state second) := by
  simp [twoLocusHJet, TwoLocusDiffusionJet.add, TwoLocusDiffusionJet.mul,
    TwoLocusDiffusionJet.const, TwoLocusDiffusionJet.smul,
    twoLocusLeftFrequencyJet, twoLocusLeftHeterozygosity]
  ring

/-- The right-locus heterozygosity jet reads its biological observable. -/
theorem twoLocusRightHJet_value {D : ℕ}
    (state : Fin D → TwoLocusHaplotypeFrequencies) (first second : Fin D) :
    (twoLocusRightHJet first second).value state =
      twoLocusRightHeterozygosity (state first) (state second) := by
  simp [twoLocusRightHJet, TwoLocusDiffusionJet.add, TwoLocusDiffusionJet.mul,
    TwoLocusDiffusionJet.const, TwoLocusDiffusionJet.smul,
    twoLocusRightFrequencyJet, twoLocusRightHeterozygosity]
  ring

/-- The `DD` jet reads exactly the linkage product. -/
theorem twoLocusDDJet_value {D : ℕ}
    (state : Fin D → TwoLocusHaplotypeFrequencies) (first second : Fin D) :
    (twoLocusDDJet first second).value state =
      (state first).linkage * (state second).linkage := by
  rfl

/-- The `Dz` jet reads exactly the generalized `Dz` observable. -/
theorem twoLocusDzJet_value {D : ℕ}
    (state : Fin D → TwoLocusHaplotypeFrequencies)
    (first second third : Fin D) :
    (twoLocusDzJet first second third).value state =
      twoLocusDzObservable (state first) (state second) (state third) := by
  simp [twoLocusDzJet, TwoLocusDiffusionJet.mul, twoLocusLinkageJet,
    twoLocusLeftContrastJet, twoLocusRightContrastJet,
    TwoLocusDiffusionJet.add, TwoLocusDiffusionJet.smul,
    TwoLocusDiffusionJet.const, twoLocusLeftFrequencyJet,
    twoLocusRightFrequencyJet, twoLocusDzObservable,
    TwoLocusHaplotypeFrequencies.leftContrast,
    TwoLocusHaplotypeFrequencies.rightContrast]
  ring

/-- The `pi2` jet reads exactly the generalized joint heterozygosity observable. -/
theorem twoLocusPi2Jet_value {D : ℕ}
    (state : Fin D → TwoLocusHaplotypeFrequencies)
    (first second third fourth : Fin D) :
    (twoLocusPi2Jet first second third fourth).value state =
      twoLocusJointHeterozygosity
        (state first) (state second) (state third) (state fourth) := by
  simp [twoLocusPi2Jet, twoLocusHJet, twoLocusRightHJet,
    TwoLocusDiffusionJet.mul,
    TwoLocusDiffusionJet.add, TwoLocusDiffusionJet.smul,
    TwoLocusDiffusionJet.const, twoLocusLeftFrequencyJet,
    twoLocusRightFrequencyJet, twoLocusJointHeterozygosity,
    twoLocusLeftHeterozygosity, twoLocusRightHeterozygosity]
  ring

/-- Exact local drift of cross-deme heterozygosity.  It is affected only when both sampled
lineages occupy the drifting deme, in which case it decays at unit coalescence rate. -/
theorem twoLocusHJet_driftAt {D : ℕ}
    (state : Fin D → TwoLocusHaplotypeFrequencies)
    (deme first second : Fin D) :
    (twoLocusHJet first second).driftAt deme state =
      if first = deme ∧ second = deme then
        -(twoLocusHJet first second).value state
      else 0 := by
  by_cases hfirst : deme = first
  · subst first
    by_cases hsecond : deme = second
    · subst second
      simp [twoLocusHJet, TwoLocusDiffusionJet.add, TwoLocusDiffusionJet.mul,
        TwoLocusDiffusionJet.const, TwoLocusDiffusionJet.smul,
        twoLocusLeftFrequencyJet, twoLocusHaplotypeCovariance,
        twoLocusHaplotypeMean, twoLocusLeftAlleleIndicator,
        TwoLocusHaplotypeFrequencies.leftFrequency]
      ring
    · simp [twoLocusHJet, TwoLocusDiffusionJet.add, TwoLocusDiffusionJet.mul,
        TwoLocusDiffusionJet.const, TwoLocusDiffusionJet.smul,
        twoLocusLeftFrequencyJet, twoLocusHaplotypeCovariance,
        twoLocusHaplotypeMean, twoLocusLeftAlleleIndicator, hsecond,
        Ne.symm hsecond]
  · by_cases hsecond : deme = second
    · subst second
      simp [twoLocusHJet, TwoLocusDiffusionJet.add, TwoLocusDiffusionJet.mul,
        TwoLocusDiffusionJet.const, TwoLocusDiffusionJet.smul,
        twoLocusLeftFrequencyJet, twoLocusHaplotypeCovariance,
        twoLocusHaplotypeMean, twoLocusLeftAlleleIndicator, hfirst,
        Ne.symm hfirst]
    · simp [twoLocusHJet, TwoLocusDiffusionJet.add, TwoLocusDiffusionJet.mul,
        TwoLocusDiffusionJet.const, TwoLocusDiffusionJet.smul,
        twoLocusLeftFrequencyJet, twoLocusHaplotypeCovariance,
        twoLocusHaplotypeMean, twoLocusLeftAlleleIndicator, hfirst, hsecond,
        Ne.symm hfirst, Ne.symm hsecond]

/-- The exact left-heterozygosity gradient in one deme.  Each matching lineage contributes
the centered allele-frequency contrast of the other lineage. -/
theorem twoLocusHJet_gradientAt {D : ℕ}
    (state : Fin D → TwoLocusHaplotypeFrequencies)
    (deme first second : Fin D) (haplotype : TwoLocusHaplotype) :
    (twoLocusHJet first second).gradientAt deme state haplotype =
      ((if deme = first then (state second).leftContrast else 0) +
        (if deme = second then (state first).leftContrast else 0)) *
          twoLocusLeftAlleleIndicator haplotype := by
  by_cases hfirst : deme = first
  · subst first
    by_cases hsecond : deme = second
    · subst second
      simp [twoLocusHJet, TwoLocusDiffusionJet.add, TwoLocusDiffusionJet.mul,
        TwoLocusDiffusionJet.const, TwoLocusDiffusionJet.smul,
        twoLocusLeftFrequencyJet,
        TwoLocusHaplotypeFrequencies.leftContrast]
      ring
    · simp [twoLocusHJet, TwoLocusDiffusionJet.add, TwoLocusDiffusionJet.mul,
        TwoLocusDiffusionJet.const, TwoLocusDiffusionJet.smul,
        twoLocusLeftFrequencyJet,
        TwoLocusHaplotypeFrequencies.leftContrast, hsecond]
      ring
  · by_cases hsecond : deme = second
    · subst second
      simp [twoLocusHJet, TwoLocusDiffusionJet.add, TwoLocusDiffusionJet.mul,
        TwoLocusDiffusionJet.const, TwoLocusDiffusionJet.smul,
        twoLocusLeftFrequencyJet,
        TwoLocusHaplotypeFrequencies.leftContrast, hfirst]
      ring
    · simp [twoLocusHJet, TwoLocusDiffusionJet.add, TwoLocusDiffusionJet.mul,
        TwoLocusDiffusionJet.const, TwoLocusDiffusionJet.smul,
        twoLocusLeftFrequencyJet, hfirst, hsecond]

/-- Exact local drift of right-locus cross-deme heterozygosity. -/
theorem twoLocusRightHJet_driftAt {D : ℕ}
    (state : Fin D → TwoLocusHaplotypeFrequencies)
    (deme first second : Fin D) :
    (twoLocusRightHJet first second).driftAt deme state =
      if first = deme ∧ second = deme then
        -(twoLocusRightHJet first second).value state
      else 0 := by
  by_cases hfirst : deme = first
  · subst first
    by_cases hsecond : deme = second
    · subst second
      simp [twoLocusRightHJet, TwoLocusDiffusionJet.add,
        TwoLocusDiffusionJet.mul, TwoLocusDiffusionJet.const,
        TwoLocusDiffusionJet.smul, twoLocusRightFrequencyJet,
        twoLocusHaplotypeCovariance, twoLocusHaplotypeMean,
        twoLocusRightAlleleIndicator,
        TwoLocusHaplotypeFrequencies.rightFrequency]
      ring
    · simp [twoLocusRightHJet, TwoLocusDiffusionJet.add,
        TwoLocusDiffusionJet.mul, TwoLocusDiffusionJet.const,
        TwoLocusDiffusionJet.smul, twoLocusRightFrequencyJet,
        twoLocusHaplotypeCovariance, twoLocusHaplotypeMean,
        twoLocusRightAlleleIndicator, hsecond, Ne.symm hsecond]
  · by_cases hsecond : deme = second
    · subst second
      simp [twoLocusRightHJet, TwoLocusDiffusionJet.add,
        TwoLocusDiffusionJet.mul, TwoLocusDiffusionJet.const,
        TwoLocusDiffusionJet.smul, twoLocusRightFrequencyJet,
        twoLocusHaplotypeCovariance, twoLocusHaplotypeMean,
        twoLocusRightAlleleIndicator, hfirst, Ne.symm hfirst]
    · simp [twoLocusRightHJet, TwoLocusDiffusionJet.add,
        TwoLocusDiffusionJet.mul, TwoLocusDiffusionJet.const,
        TwoLocusDiffusionJet.smul, twoLocusRightFrequencyJet,
        twoLocusHaplotypeCovariance, twoLocusHaplotypeMean,
        twoLocusRightAlleleIndicator, hfirst, hsecond,
        Ne.symm hfirst, Ne.symm hsecond]

/-- The right-heterozygosity gradient has the symmetric contrast-coefficient law. -/
theorem twoLocusRightHJet_gradientAt {D : ℕ}
    (state : Fin D → TwoLocusHaplotypeFrequencies)
    (deme first second : Fin D) (haplotype : TwoLocusHaplotype) :
    (twoLocusRightHJet first second).gradientAt deme state haplotype =
      ((if deme = first then (state second).rightContrast else 0) +
        (if deme = second then (state first).rightContrast else 0)) *
          twoLocusRightAlleleIndicator haplotype := by
  by_cases hfirst : deme = first
  · subst first
    by_cases hsecond : deme = second
    · subst second
      simp [twoLocusRightHJet, TwoLocusDiffusionJet.add,
        TwoLocusDiffusionJet.mul, TwoLocusDiffusionJet.const,
        TwoLocusDiffusionJet.smul, twoLocusRightFrequencyJet,
        TwoLocusHaplotypeFrequencies.rightContrast]
      ring
    · simp [twoLocusRightHJet, TwoLocusDiffusionJet.add,
        TwoLocusDiffusionJet.mul, TwoLocusDiffusionJet.const,
        TwoLocusDiffusionJet.smul, twoLocusRightFrequencyJet,
        TwoLocusHaplotypeFrequencies.rightContrast, hsecond]
      ring
  · by_cases hsecond : deme = second
    · subst second
      simp [twoLocusRightHJet, TwoLocusDiffusionJet.add,
        TwoLocusDiffusionJet.mul, TwoLocusDiffusionJet.const,
        TwoLocusDiffusionJet.smul, twoLocusRightFrequencyJet,
        TwoLocusHaplotypeFrequencies.rightContrast, hfirst]
      ring
    · simp [twoLocusRightHJet, TwoLocusDiffusionJet.add,
        TwoLocusDiffusionJet.mul, TwoLocusDiffusionJet.const,
        TwoLocusDiffusionJet.smul, twoLocusRightFrequencyJet,
        hfirst, hsecond]

/-- Exact local drift of a cross-deme linkage product.  The same-deme branch is the
Hill--Robertson `-3 DD + Dz + pi2` row, derived from the exact linkage drift and linkage
quadratic variation.  A single matching index contributes `-DD`; no matching index
contributes zero. -/
theorem twoLocusDDJet_driftAt {D : ℕ}
    (state : Fin D → TwoLocusHaplotypeFrequencies)
    (deme first second : Fin D) :
    (twoLocusDDJet first second).driftAt deme state =
      if first = deme ∧ second = deme then
        -3 * (twoLocusDDJet first second).value state +
          (twoLocusDzJet deme deme deme).value state +
          (twoLocusPi2Jet deme deme deme deme).value state
      else if first = deme ∨ second = deme then
        -(twoLocusDDJet first second).value state
      else 0 := by
  by_cases hfirst : deme = first
  · subst first
    by_cases hsecond : deme = second
    · subst second
      simp [twoLocusDDJet, twoLocusDzJet, twoLocusPi2Jet, twoLocusHJet,
        twoLocusRightHJet,
        TwoLocusDiffusionJet.mul, TwoLocusDiffusionJet.add,
        TwoLocusDiffusionJet.smul, TwoLocusDiffusionJet.const,
        twoLocusLinkageJet, twoLocusLeftContrastJet,
        twoLocusRightContrastJet, twoLocusLeftFrequencyJet,
        twoLocusRightFrequencyJet,
        twoLocusLinkageDrift_eq_neg_linkage,
        twoLocusHaplotypeCovariance_linkage_linkage,
        TwoLocusHaplotypeFrequencies.leftContrast,
        TwoLocusHaplotypeFrequencies.rightContrast,
        TwoLocusHaplotypeFrequencies.leftFrequency,
        TwoLocusHaplotypeFrequencies.rightFrequency]
      ring
    · simp [twoLocusDDJet, TwoLocusDiffusionJet.mul, twoLocusLinkageJet,
        twoLocusLinkageDrift_eq_neg_linkage, twoLocusHaplotypeCovariance,
        twoLocusHaplotypeMean, twoLocusLinkageGradient, hsecond,
        Ne.symm hsecond]
      ring
  · by_cases hsecond : deme = second
    · subst second
      simp [twoLocusDDJet, TwoLocusDiffusionJet.mul, twoLocusLinkageJet,
        twoLocusLinkageDrift_eq_neg_linkage, twoLocusHaplotypeCovariance,
        twoLocusHaplotypeMean, twoLocusLinkageGradient, hfirst,
        Ne.symm hfirst]
    · simp [twoLocusDDJet, TwoLocusDiffusionJet.mul, twoLocusLinkageJet,
        twoLocusHaplotypeCovariance, twoLocusHaplotypeMean,
        twoLocusLinkageGradient, hfirst, hsecond,
        Ne.symm hfirst, Ne.symm hsecond]

/-- Exact local drift of the generalized `Dz(first,second,third)` observable.  The five
branches are forced by which of its linkage, left-contrast, and right-contrast arguments
occupy the drifting deme.  In particular the same-deme branch is the Hill--Robertson
`4 DD - 5 Dz` row, and joint drift of the two contrast arguments restores `4 DD` even
when their linkage argument lies in another deme. -/
theorem twoLocusDzJet_driftAt {D : ℕ}
    (state : Fin D → TwoLocusHaplotypeFrequencies)
    (deme first second third : Fin D) :
    (twoLocusDzJet first second third).driftAt deme state =
      if first = deme ∧ second = deme ∧ third = deme then
        4 * (twoLocusDDJet deme deme).value state -
          5 * (twoLocusDzJet first second third).value state
      else if first = deme ∧ second = deme then
        -3 * (twoLocusDzJet first second third).value state
      else if first = deme ∧ third = deme then
        -3 * (twoLocusDzJet first second third).value state
      else if second = deme ∧ third = deme then
        4 * (twoLocusDDJet first deme).value state
      else if first = deme then
        -(twoLocusDzJet first second third).value state
      else 0 := by
  have hab : (state deme).ab =
      1 - (state deme).AB - (state deme).Ab - (state deme).aB := by
    linarith [(state deme).total_eq_one]
  by_cases hfirst : deme = first
  · subst first
    by_cases hsecond : deme = second
    · subst second
      by_cases hthird : deme = third
      · subst third
        simp [twoLocusDzJet, twoLocusDDJet, TwoLocusDiffusionJet.mul,
          TwoLocusDiffusionJet.add, TwoLocusDiffusionJet.smul,
          TwoLocusDiffusionJet.const, twoLocusLinkageJet,
          twoLocusLeftContrastJet, twoLocusRightContrastJet,
          twoLocusLeftFrequencyJet, twoLocusRightFrequencyJet,
          twoLocusLinkageDrift_eq_neg_linkage,
          twoLocusHaplotypeCovariance_linkage_left,
          twoLocusHaplotypeCovariance_linkage_right,
          twoLocusHaplotypeCovariance_left_right,
          twoLocusHaplotypeCovariance, twoLocusHaplotypeMean,
          twoLocusLinkageGradient, twoLocusLeftAlleleIndicator,
          twoLocusRightAlleleIndicator,
          TwoLocusHaplotypeFrequencies.linkage,
          TwoLocusHaplotypeFrequencies.leftFrequency,
          TwoLocusHaplotypeFrequencies.rightFrequency,
          TwoLocusHaplotypeFrequencies.leftContrast,
          TwoLocusHaplotypeFrequencies.rightContrast]
        rw [hab]
        ring
      · simp [twoLocusDzJet, TwoLocusDiffusionJet.mul,
          TwoLocusDiffusionJet.add, TwoLocusDiffusionJet.smul,
          TwoLocusDiffusionJet.const, twoLocusLinkageJet,
          twoLocusLeftContrastJet, twoLocusRightContrastJet,
          twoLocusLeftFrequencyJet, twoLocusRightFrequencyJet,
          twoLocusLinkageDrift_eq_neg_linkage,
          twoLocusHaplotypeCovariance_linkage_left,
          twoLocusHaplotypeCovariance, twoLocusHaplotypeMean,
          twoLocusLinkageGradient, twoLocusLeftAlleleIndicator,
          TwoLocusHaplotypeFrequencies.linkage,
          TwoLocusHaplotypeFrequencies.leftFrequency,
          TwoLocusHaplotypeFrequencies.leftContrast,
          hthird, Ne.symm hthird]
        rw [hab]
        ring
    · by_cases hthird : deme = third
      · subst third
        simp [twoLocusDzJet, TwoLocusDiffusionJet.mul,
          TwoLocusDiffusionJet.add, TwoLocusDiffusionJet.smul,
          TwoLocusDiffusionJet.const, twoLocusLinkageJet,
          twoLocusLeftContrastJet, twoLocusRightContrastJet,
          twoLocusLeftFrequencyJet, twoLocusRightFrequencyJet,
          twoLocusLinkageDrift_eq_neg_linkage,
          twoLocusHaplotypeCovariance_linkage_right,
          twoLocusHaplotypeCovariance, twoLocusHaplotypeMean,
          twoLocusLinkageGradient, twoLocusRightAlleleIndicator,
          TwoLocusHaplotypeFrequencies.linkage,
          TwoLocusHaplotypeFrequencies.rightFrequency,
          TwoLocusHaplotypeFrequencies.rightContrast,
          hsecond, Ne.symm hsecond]
        rw [hab]
        ring
      · simp [twoLocusDzJet, TwoLocusDiffusionJet.mul,
          TwoLocusDiffusionJet.add, TwoLocusDiffusionJet.smul,
          TwoLocusDiffusionJet.const, twoLocusLinkageJet,
          twoLocusLeftContrastJet, twoLocusRightContrastJet,
          twoLocusLeftFrequencyJet, twoLocusRightFrequencyJet,
          twoLocusLinkageDrift_eq_neg_linkage,
          twoLocusHaplotypeCovariance, twoLocusHaplotypeMean,
          twoLocusLinkageGradient,
          TwoLocusHaplotypeFrequencies.linkage,
          hsecond, hthird, Ne.symm hsecond, Ne.symm hthird]
        rw [hab]
        ring
  · by_cases hsecond : deme = second
    · subst second
      by_cases hthird : deme = third
      · subst third
        simp [twoLocusDzJet, twoLocusDDJet, TwoLocusDiffusionJet.mul,
          TwoLocusDiffusionJet.add, TwoLocusDiffusionJet.smul,
          TwoLocusDiffusionJet.const, twoLocusLinkageJet,
          twoLocusLeftContrastJet, twoLocusRightContrastJet,
          twoLocusLeftFrequencyJet, twoLocusRightFrequencyJet,
          twoLocusHaplotypeCovariance_left_right,
          twoLocusHaplotypeCovariance, twoLocusHaplotypeMean,
          twoLocusLeftAlleleIndicator, twoLocusRightAlleleIndicator,
          TwoLocusHaplotypeFrequencies.linkage,
          TwoLocusHaplotypeFrequencies.leftFrequency,
          TwoLocusHaplotypeFrequencies.rightFrequency,
          hfirst, Ne.symm hfirst]
        rw [hab]
        ring
      · simp [twoLocusDzJet, TwoLocusDiffusionJet.mul,
          TwoLocusDiffusionJet.add, TwoLocusDiffusionJet.smul,
          TwoLocusDiffusionJet.const, twoLocusLinkageJet,
          twoLocusLeftContrastJet, twoLocusRightContrastJet,
          twoLocusLeftFrequencyJet, twoLocusRightFrequencyJet,
          twoLocusHaplotypeCovariance, twoLocusHaplotypeMean,
          twoLocusLeftAlleleIndicator,
          hfirst, hthird, Ne.symm hfirst, Ne.symm hthird]
    · by_cases hthird : deme = third
      · subst third
        simp [twoLocusDzJet, TwoLocusDiffusionJet.mul,
          TwoLocusDiffusionJet.add, TwoLocusDiffusionJet.smul,
          TwoLocusDiffusionJet.const, twoLocusLinkageJet,
          twoLocusLeftContrastJet, twoLocusRightContrastJet,
          twoLocusLeftFrequencyJet, twoLocusRightFrequencyJet,
          twoLocusHaplotypeCovariance, twoLocusHaplotypeMean,
          twoLocusRightAlleleIndicator,
          hfirst, hsecond, Ne.symm hfirst, Ne.symm hsecond]
      · simp [twoLocusDzJet, TwoLocusDiffusionJet.mul,
          TwoLocusDiffusionJet.add, TwoLocusDiffusionJet.smul,
          TwoLocusDiffusionJet.const, twoLocusLinkageJet,
          twoLocusLeftContrastJet, twoLocusRightContrastJet,
          twoLocusLeftFrequencyJet, twoLocusRightFrequencyJet,
          twoLocusHaplotypeCovariance, twoLocusHaplotypeMean,
          hfirst, hsecond, hthird,
          Ne.symm hfirst, Ne.symm hsecond, Ne.symm hthird]

/-- Exact local drift of generalized joint heterozygosity.  This factorized statement
contains every equality-pattern branch of the `pi2` Hill--Robertson row: within-locus
coalescence supplies the two loss terms, while shared-deme cross-locus quadratic variation
is local linkage times the two exact heterozygosity-gradient coefficients. -/
theorem twoLocusPi2Jet_driftAt {D : ℕ}
    (state : Fin D → TwoLocusHaplotypeFrequencies)
    (deme first second third fourth : Fin D) :
    (twoLocusPi2Jet first second third fourth).driftAt deme state =
      -(if first = deme ∧ second = deme then
          (twoLocusPi2Jet first second third fourth).value state else 0) -
        (if third = deme ∧ fourth = deme then
          (twoLocusPi2Jet first second third fourth).value state else 0) +
        (state deme).linkage *
          ((if deme = first then (state second).leftContrast else 0) +
            (if deme = second then (state first).leftContrast else 0)) *
          ((if deme = third then (state fourth).rightContrast else 0) +
            (if deme = fourth then (state third).rightContrast else 0)) / 4 := by
  have hleftGradient :
      (twoLocusHJet first second).gradientAt deme state =
        fun haplotype ↦
          ((if deme = first then (state second).leftContrast else 0) +
            (if deme = second then (state first).leftContrast else 0)) *
              twoLocusLeftAlleleIndicator haplotype := by
    funext haplotype
    exact twoLocusHJet_gradientAt state deme first second haplotype
  have hrightGradient :
      (twoLocusRightHJet third fourth).gradientAt deme state =
        fun haplotype ↦
          ((if deme = third then (state fourth).rightContrast else 0) +
            (if deme = fourth then (state third).rightContrast else 0)) *
              twoLocusRightAlleleIndicator haplotype := by
    funext haplotype
    exact twoLocusRightHJet_gradientAt state deme third fourth haplotype
  simp only [twoLocusPi2Jet, TwoLocusDiffusionJet.smul,
    TwoLocusDiffusionJet.mul]
  rw [twoLocusHJet_driftAt, twoLocusRightHJet_driftAt]
  rw [hleftGradient, hrightGradient]
  rw [twoLocusHaplotypeCovariance_scaled_left_right]
  split_ifs <;> ring

/-- The generalized four-deme `pi2` observable in centered contrast form. -/
theorem twoLocusJointHeterozygosity_eq_contrasts
    (leftFirst leftSecond rightFirst rightSecond : TwoLocusHaplotypeFrequencies) :
    twoLocusJointHeterozygosity leftFirst leftSecond rightFirst rightSecond =
      (1 - leftFirst.leftContrast * leftSecond.leftContrast) *
        (1 - rightFirst.rightContrast * rightSecond.rightContrast) / 16 := by
  rw [twoLocusJointHeterozygosity,
    twoLocusLeftHeterozygosity_eq_contrasts,
    twoLocusRightHeterozygosity_eq_contrasts]
  ring

/-- Per-unit-scaled-mutation velocity of cross-deme left heterozygosity when mutation acts
on either one of its two lineage arguments. -/
noncomputable def twoLocusHMutationVelocity
    (first second : TwoLocusHaplotypeFrequencies) : ℝ :=
  first.leftContrast * second.leftContrast / 2

/-- The heterozygosity mutation velocity is exactly the affine forcing `1/2` minus the
current heterozygosity. -/
theorem twoLocusHMutationVelocity_eq
    (first second : TwoLocusHaplotypeFrequencies) :
    twoLocusHMutationVelocity first second =
      1 / 2 - twoLocusLeftHeterozygosity first second := by
  rw [twoLocusHMutationVelocity, twoLocusLeftHeterozygosity_eq_contrasts]
  ring

/-- Per-unit-scaled-mutation velocity of generalized `pi2` when mutation acts on either
left-locus lineage argument. -/
noncomputable def twoLocusPi2LeftMutationVelocity
    (leftFirst leftSecond rightFirst rightSecond : TwoLocusHaplotypeFrequencies) : ℝ :=
  leftFirst.leftContrast * leftSecond.leftContrast *
    (1 - rightFirst.rightContrast * rightSecond.rightContrast) / 16

/-- The left-channel `pi2` velocity is the exact `H/8 - pi2` coupling appearing in the
closed moment system. -/
theorem twoLocusPi2LeftMutationVelocity_eq
    (leftFirst leftSecond rightFirst rightSecond : TwoLocusHaplotypeFrequencies) :
    twoLocusPi2LeftMutationVelocity leftFirst leftSecond rightFirst rightSecond =
      twoLocusRightHeterozygosity rightFirst rightSecond / 8 -
        twoLocusJointHeterozygosity leftFirst leftSecond rightFirst rightSecond := by
  rw [twoLocusPi2LeftMutationVelocity,
    twoLocusRightHeterozygosity_eq_contrasts,
    twoLocusJointHeterozygosity_eq_contrasts]
  ring

/-- Per-unit-scaled-mutation velocity of generalized `pi2` when mutation acts on either
right-locus lineage argument. -/
noncomputable def twoLocusPi2RightMutationVelocity
    (leftFirst leftSecond rightFirst rightSecond : TwoLocusHaplotypeFrequencies) : ℝ :=
  (1 - leftFirst.leftContrast * leftSecond.leftContrast) *
    rightFirst.rightContrast * rightSecond.rightContrast / 16

/-- The right-channel velocity is the symmetric `H/8 - pi2` coupling. -/
theorem twoLocusPi2RightMutationVelocity_eq
    (leftFirst leftSecond rightFirst rightSecond : TwoLocusHaplotypeFrequencies) :
    twoLocusPi2RightMutationVelocity leftFirst leftSecond rightFirst rightSecond =
      twoLocusLeftHeterozygosity leftFirst leftSecond / 8 -
        twoLocusJointHeterozygosity leftFirst leftSecond rightFirst rightSecond := by
  rw [twoLocusPi2RightMutationVelocity,
    twoLocusLeftHeterozygosity_eq_contrasts,
    twoLocusJointHeterozygosity_eq_contrasts]
  ring

/-- Left-locus heterozygosity is affine in its first haplotype argument under an exact
migration pulse.  Consequently its infinitesimal migration coefficient is the source-minus-
recipient coordinate replacement, with no closure assumption. -/
theorem twoLocusLeftHeterozygosity_mixture_first
    (alpha : ℝ) (alpha_nonneg : 0 ≤ alpha) (alpha_le_one : alpha ≤ 1)
    (source recipient other : TwoLocusHaplotypeFrequencies) :
    twoLocusLeftHeterozygosity
        (TwoLocusHaplotypeFrequencies.mixture alpha alpha_nonneg alpha_le_one
          source recipient) other =
      alpha * twoLocusLeftHeterozygosity source other +
        (1 - alpha) * twoLocusLeftHeterozygosity recipient other := by
  simp only [twoLocusLeftHeterozygosity,
    TwoLocusHaplotypeFrequencies.mixture_leftFrequency]
  ring

/-- Right-locus heterozygosity is likewise affine in its first haplotype argument. -/
theorem twoLocusRightHeterozygosity_mixture_first
    (alpha : ℝ) (alpha_nonneg : 0 ≤ alpha) (alpha_le_one : alpha ≤ 1)
    (source recipient other : TwoLocusHaplotypeFrequencies) :
    twoLocusRightHeterozygosity
        (TwoLocusHaplotypeFrequencies.mixture alpha alpha_nonneg alpha_le_one
          source recipient) other =
      alpha * twoLocusRightHeterozygosity source other +
        (1 - alpha) * twoLocusRightHeterozygosity recipient other := by
  simp only [twoLocusRightHeterozygosity,
    TwoLocusHaplotypeFrequencies.mixture_rightFrequency]
  ring

/-- Generalized `pi2` is affine under a pulse in its first left-locus index. -/
theorem twoLocusJointHeterozygosity_mixture_leftFirst
    (alpha : ℝ) (alpha_nonneg : 0 ≤ alpha) (alpha_le_one : alpha ≤ 1)
    (source recipient leftSecond rightFirst rightSecond :
      TwoLocusHaplotypeFrequencies) :
    twoLocusJointHeterozygosity
        (TwoLocusHaplotypeFrequencies.mixture alpha alpha_nonneg alpha_le_one
          source recipient) leftSecond rightFirst rightSecond =
      alpha * twoLocusJointHeterozygosity source leftSecond rightFirst rightSecond +
        (1 - alpha) *
          twoLocusJointHeterozygosity recipient leftSecond rightFirst rightSecond := by
  rw [twoLocusJointHeterozygosity, twoLocusLeftHeterozygosity_mixture_first]
  simp only [twoLocusJointHeterozygosity]
  ring

/-- Generalized `pi2` is affine under a pulse in its second left-locus index. -/
theorem twoLocusJointHeterozygosity_mixture_leftSecond
    (alpha : ℝ) (alpha_nonneg : 0 ≤ alpha) (alpha_le_one : alpha ≤ 1)
    (leftFirst source recipient rightFirst rightSecond :
      TwoLocusHaplotypeFrequencies) :
    twoLocusJointHeterozygosity leftFirst
        (TwoLocusHaplotypeFrequencies.mixture alpha alpha_nonneg alpha_le_one
          source recipient) rightFirst rightSecond =
      alpha * twoLocusJointHeterozygosity leftFirst source rightFirst rightSecond +
        (1 - alpha) *
          twoLocusJointHeterozygosity leftFirst recipient rightFirst rightSecond := by
  rw [twoLocusJointHeterozygosity]
  have symmetry : ∀ first second,
      twoLocusLeftHeterozygosity first second =
        twoLocusLeftHeterozygosity second first := by
    intro first second
    simp only [twoLocusLeftHeterozygosity]
    ring
  rw [symmetry leftFirst, twoLocusLeftHeterozygosity_mixture_first]
  simp only [twoLocusJointHeterozygosity]
  rw [symmetry source leftFirst, symmetry recipient leftFirst]
  ring

/-- Generalized `pi2` is affine under a pulse in its first right-locus index. -/
theorem twoLocusJointHeterozygosity_mixture_rightFirst
    (alpha : ℝ) (alpha_nonneg : 0 ≤ alpha) (alpha_le_one : alpha ≤ 1)
    (leftFirst leftSecond source recipient rightSecond :
      TwoLocusHaplotypeFrequencies) :
    twoLocusJointHeterozygosity leftFirst leftSecond
        (TwoLocusHaplotypeFrequencies.mixture alpha alpha_nonneg alpha_le_one
          source recipient) rightSecond =
      alpha * twoLocusJointHeterozygosity leftFirst leftSecond source rightSecond +
        (1 - alpha) *
          twoLocusJointHeterozygosity leftFirst leftSecond recipient rightSecond := by
  rw [twoLocusJointHeterozygosity, twoLocusRightHeterozygosity_mixture_first]
  simp only [twoLocusJointHeterozygosity]
  ring

/-- Generalized `pi2` is affine under a pulse in its second right-locus index. -/
theorem twoLocusJointHeterozygosity_mixture_rightSecond
    (alpha : ℝ) (alpha_nonneg : 0 ≤ alpha) (alpha_le_one : alpha ≤ 1)
    (leftFirst leftSecond rightFirst source recipient :
      TwoLocusHaplotypeFrequencies) :
    twoLocusJointHeterozygosity leftFirst leftSecond rightFirst
        (TwoLocusHaplotypeFrequencies.mixture alpha alpha_nonneg alpha_le_one
          source recipient) =
      alpha * twoLocusJointHeterozygosity leftFirst leftSecond rightFirst source +
        (1 - alpha) *
          twoLocusJointHeterozygosity leftFirst leftSecond rightFirst recipient := by
  rw [twoLocusJointHeterozygosity]
  have symmetry : ∀ first second,
      twoLocusRightHeterozygosity first second =
        twoLocusRightHeterozygosity second first := by
    intro first second
    simp only [twoLocusRightHeterozygosity]
    ring
  rw [symmetry rightFirst, twoLocusRightHeterozygosity_mixture_first]
  simp only [twoLocusJointHeterozygosity]
  rw [symmetry source rightFirst, symmetry recipient rightFirst]
  ring

/-- Recombination pulses at both endpoints leave cross-deme left heterozygosity unchanged,
because they preserve both marginal allele frequencies exactly. -/
theorem twoLocusLeftHeterozygosity_recombinationPulse
    (alphaFirst alphaSecond : ℝ)
    (alphaFirst_nonneg : 0 ≤ alphaFirst) (alphaFirst_le_one : alphaFirst ≤ 1)
    (alphaSecond_nonneg : 0 ≤ alphaSecond) (alphaSecond_le_one : alphaSecond ≤ 1)
    (first second : TwoLocusHaplotypeFrequencies) :
    twoLocusLeftHeterozygosity
        (TwoLocusHaplotypeFrequencies.recombinationPulse
          alphaFirst alphaFirst_nonneg alphaFirst_le_one first)
        (TwoLocusHaplotypeFrequencies.recombinationPulse
          alphaSecond alphaSecond_nonneg alphaSecond_le_one second) =
      twoLocusLeftHeterozygosity first second := by
  simp only [twoLocusLeftHeterozygosity,
    TwoLocusHaplotypeFrequencies.recombinationPulse_leftFrequency]

/-- Generalized `pi2` is invariant under arbitrary recombination pulses at all four
arguments: it depends only on the two marginal-frequency pairs. -/
theorem twoLocusJointHeterozygosity_recombinationPulse
    (alphaLeftFirst alphaLeftSecond alphaRightFirst alphaRightSecond : ℝ)
    (hLeftFirst0 : 0 ≤ alphaLeftFirst) (hLeftFirst1 : alphaLeftFirst ≤ 1)
    (hLeftSecond0 : 0 ≤ alphaLeftSecond) (hLeftSecond1 : alphaLeftSecond ≤ 1)
    (hRightFirst0 : 0 ≤ alphaRightFirst) (hRightFirst1 : alphaRightFirst ≤ 1)
    (hRightSecond0 : 0 ≤ alphaRightSecond) (hRightSecond1 : alphaRightSecond ≤ 1)
    (leftFirst leftSecond rightFirst rightSecond : TwoLocusHaplotypeFrequencies) :
    twoLocusJointHeterozygosity
        (TwoLocusHaplotypeFrequencies.recombinationPulse
          alphaLeftFirst hLeftFirst0 hLeftFirst1 leftFirst)
        (TwoLocusHaplotypeFrequencies.recombinationPulse
          alphaLeftSecond hLeftSecond0 hLeftSecond1 leftSecond)
        (TwoLocusHaplotypeFrequencies.recombinationPulse
          alphaRightFirst hRightFirst0 hRightFirst1 rightFirst)
        (TwoLocusHaplotypeFrequencies.recombinationPulse
          alphaRightSecond hRightSecond0 hRightSecond1 rightSecond) =
      twoLocusJointHeterozygosity leftFirst leftSecond rightFirst rightSecond := by
  simp only [twoLocusJointHeterozygosity, twoLocusLeftHeterozygosity,
    twoLocusRightHeterozygosity,
    TwoLocusHaplotypeFrequencies.recombinationPulse_leftFrequency,
    TwoLocusHaplotypeFrequencies.recombinationPulse_rightFrequency]

/-- A recombination pulse at the linkage-bearing argument scales `Dz` by exactly the
parental-linkage retention `1-alpha`. -/
theorem twoLocusDzObservable_recombinationPulse
    (alpha : ℝ) (alpha_nonneg : 0 ≤ alpha) (alpha_le_one : alpha ≤ 1)
    (linkageDeme leftDeme rightDeme : TwoLocusHaplotypeFrequencies) :
    twoLocusDzObservable
        (TwoLocusHaplotypeFrequencies.recombinationPulse
          alpha alpha_nonneg alpha_le_one linkageDeme)
        leftDeme rightDeme =
      (1 - alpha) * twoLocusDzObservable linkageDeme leftDeme rightDeme := by
  simp only [twoLocusDzObservable,
    TwoLocusHaplotypeFrequencies.recombinationPulse_linkage]
  ring

/-- Multiplying linkage migration velocity by the two contrasts in `Dz` produces exactly
the `Dz` replacement difference plus the four-`pi2` restoration stencil. -/
theorem migrationLinkageVelocity_mul_contrasts_eq_Dz_pi2
    (source recipient left right : TwoLocusHaplotypeFrequencies) :
    source.migrationLinkageVelocity recipient * left.leftContrast * right.rightContrast =
      twoLocusDzObservable source left right - twoLocusDzObservable recipient left right +
        4 * (twoLocusJointHeterozygosity recipient left recipient right -
          twoLocusJointHeterozygosity recipient left right source -
          twoLocusJointHeterozygosity left source recipient right +
          twoLocusJointHeterozygosity left source right source) := by
  rw [TwoLocusHaplotypeFrequencies.migrationLinkageVelocity_eq_contrasts]
  simp only [twoLocusDzObservable, twoLocusJointHeterozygosity_eq_contrasts]
  ring

/-- Migration of the left contrast index in `Dz` is a pure coordinate replacement. -/
theorem linkage_mul_leftContrastVelocity_mul_rightContrast
    (linkageDeme source recipient right : TwoLocusHaplotypeFrequencies) :
    linkageDeme.linkage * (source.leftContrast - recipient.leftContrast) *
        right.rightContrast =
      twoLocusDzObservable linkageDeme source right -
        twoLocusDzObservable linkageDeme recipient right := by
  simp only [twoLocusDzObservable]
  ring

/-- Migration of the right contrast index in `Dz` is also a pure replacement. -/
theorem linkage_mul_leftContrast_mul_rightContrastVelocity
    (linkageDeme left source recipient : TwoLocusHaplotypeFrequencies) :
    linkageDeme.linkage * left.leftContrast *
        (source.rightContrast - recipient.rightContrast) =
      twoLocusDzObservable linkageDeme left source -
        twoLocusDzObservable linkageDeme left recipient := by
  simp only [twoLocusDzObservable]
  ring

/-- A full low-order state is haplotype-realizable when all of its coordinates are
expectations of the defining polynomials under one common probability law on the
multi-deme haplotype-frequency simplex.  `H` is represented at the left locus here.  The
closed mutation row additionally identifies the analogous right-locus expectation; that
scientifically substantive locus-exchangeability condition is carried by the extension
`LocusExchangeableLowOrderLDHaplotypeRealization` below rather than silently assumed here.
This is the semantic cone whose preservation by the continuous Wright--Fisher semigroup
remains to be proved. -/
structure LowOrderLDHaplotypeRealization {D : ℕ}
    (state : AffineLowOrderLDCoordinate D → ℝ) where
  sampleSpace : Type
  expectation : Foundations.ExpFunctional sampleSpace
  haplotype : sampleSpace → Fin D → TwoLocusHaplotypeFrequencies
  constant_eq : state none = 1
  H_eq : ∀ first second,
    state (some (.H first second)) = expectation (fun outcome ↦
      twoLocusLeftHeterozygosity (haplotype outcome first) (haplotype outcome second))
  DD_eq : ∀ first second,
    state (some (.DD first second)) = expectation (fun outcome ↦
      (haplotype outcome first).linkage * (haplotype outcome second).linkage)
  Dz_eq : ∀ first second third,
    state (some (.Dz first second third)) = expectation (fun outcome ↦
      twoLocusDzObservable (haplotype outcome first) (haplotype outcome second)
        (haplotype outcome third))
  pi2_eq : ∀ first second third fourth,
    state (some (.pi2 first second third fourth)) = expectation (fun outcome ↦
      twoLocusJointHeterozygosity (haplotype outcome first) (haplotype outcome second)
        (haplotype outcome third) (haplotype outcome fourth))

/-- Haplotype realization in the locus-exchangeable model used by the closed mutation
system.  The extra field is exactly what licenses the same `H(i,j)` coordinate to appear as
either a left- or right-locus marginal in the `pi2` mutation row. -/
structure LocusExchangeableLowOrderLDHaplotypeRealization {D : ℕ}
    (state : AffineLowOrderLDCoordinate D → ℝ)
    extends LowOrderLDHaplotypeRealization state where
  H_right_eq : ∀ first second,
    state (some (.H first second)) = expectation (fun outcome ↦
      twoLocusRightHeterozygosity (haplotype outcome first) (haplotype outcome second))

/-- Evaluate the complete low-order polynomial family under a positive normalized
expectation.  This is the forward semantic map from an actual haplotype law to the finite
moment vector used by the demographic operator. -/
noncomputable def haplotypeLowOrderLDState {D : ℕ} {sampleSpace : Type}
    (expectation : Foundations.ExpFunctional sampleSpace)
    (haplotype : sampleSpace → Fin D → TwoLocusHaplotypeFrequencies) :
    AffineLowOrderLDCoordinate D → ℝ
  | none => 1
  | some (.H first second) => expectation (fun outcome ↦
      twoLocusLeftHeterozygosity (haplotype outcome first) (haplotype outcome second))
  | some (.DD first second) => expectation (fun outcome ↦
      (haplotype outcome first).linkage * (haplotype outcome second).linkage)
  | some (.Dz first second third) => expectation (fun outcome ↦
      twoLocusDzObservable (haplotype outcome first) (haplotype outcome second)
        (haplotype outcome third))
  | some (.pi2 first second third fourth) => expectation (fun outcome ↦
      twoLocusJointHeterozygosity (haplotype outcome first) (haplotype outcome second)
        (haplotype outcome third) (haplotype outcome fourth))

/-- The semantic moment map is realizable by construction, so the cone is inhabited by
every genuine law rather than merely constrained by a list of equations. -/
def haplotypeLowOrderLDState_realization {D : ℕ} {sampleSpace : Type}
    (expectation : Foundations.ExpFunctional sampleSpace)
    (haplotype : sampleSpace → Fin D → TwoLocusHaplotypeFrequencies) :
    LowOrderLDHaplotypeRealization (haplotypeLowOrderLDState expectation haplotype) where
  sampleSpace := sampleSpace
  expectation := expectation
  haplotype := haplotype
  constant_eq := rfl
  H_eq _ _ := rfl
  DD_eq _ _ := rfl
  Dz_eq _ _ _ := rfl
  pi2_eq _ _ _ _ := rfl

/-- A concrete haplotype law whose expected left and right heterozygosities agree supplies
the stronger locus-exchangeable realization required by the mutation generator. -/
def haplotypeLowOrderLDState_locusExchangeableRealization
    {D : ℕ} {sampleSpace : Type}
    (expectation : Foundations.ExpFunctional sampleSpace)
    (haplotype : sampleSpace → Fin D → TwoLocusHaplotypeFrequencies)
    (locus_exchangeable : ∀ first second,
      expectation (fun outcome ↦
        twoLocusLeftHeterozygosity (haplotype outcome first) (haplotype outcome second)) =
      expectation (fun outcome ↦
        twoLocusRightHeterozygosity (haplotype outcome first) (haplotype outcome second))) :
    LocusExchangeableLowOrderLDHaplotypeRealization
      (haplotypeLowOrderLDState expectation haplotype) where
  toLowOrderLDHaplotypeRealization :=
    haplotypeLowOrderLDState_realization expectation haplotype
  H_right_eq first second := locus_exchangeable first second

/-- Apply one exact deterministic migration pulse to the underlying haplotype random
variables.  Only the recipient changes; its four haplotype frequencies are mixed before any
moment is read. -/
noncomputable def LowOrderLDHaplotypeRealization.pulseHaplotype {D : ℕ}
    {state : AffineLowOrderLDCoordinate D → ℝ}
    (realization : LowOrderLDHaplotypeRealization state)
    (alpha : ℝ) (alpha_nonneg : 0 ≤ alpha) (alpha_le_one : alpha ≤ 1)
    (source recipient : Fin D) :
    realization.sampleSpace → Fin D → TwoLocusHaplotypeFrequencies :=
  fun outcome deme ↦
    if deme = recipient then
      TwoLocusHaplotypeFrequencies.mixture alpha alpha_nonneg alpha_le_one
        (realization.haplotype outcome source) (realization.haplotype outcome recipient)
    else
      realization.haplotype outcome deme

/-- The complete low-order moment vector immediately after a migration pulse, evaluated
from the transformed haplotype law rather than from an assumed scalar retention factor. -/
noncomputable def LowOrderLDHaplotypeRealization.pulseState {D : ℕ}
    {state : AffineLowOrderLDCoordinate D → ℝ}
    (realization : LowOrderLDHaplotypeRealization state)
    (alpha : ℝ) (alpha_nonneg : 0 ≤ alpha) (alpha_le_one : alpha ≤ 1)
    (source recipient : Fin D) : AffineLowOrderLDCoordinate D → ℝ :=
  haplotypeLowOrderLDState realization.expectation
    (realization.pulseHaplotype alpha alpha_nonneg alpha_le_one source recipient)

/-- A deterministic migration pulse preserves the full haplotype-realizable cone by an
explicit transformed witness. -/
noncomputable def LowOrderLDHaplotypeRealization.pulse {D : ℕ}
    {state : AffineLowOrderLDCoordinate D → ℝ}
    (realization : LowOrderLDHaplotypeRealization state)
    (alpha : ℝ) (alpha_nonneg : 0 ≤ alpha) (alpha_le_one : alpha ≤ 1)
    (source recipient : Fin D) :
    LowOrderLDHaplotypeRealization
      (realization.pulseState alpha alpha_nonneg alpha_le_one source recipient) :=
  haplotypeLowOrderLDState_realization realization.expectation
    (realization.pulseHaplotype alpha alpha_nonneg alpha_le_one source recipient)

/-- At the recipient, the pulse witness obeys the exact restoration identity pointwise. -/
theorem LowOrderLDHaplotypeRealization.pulseHaplotype_recipient_linkage {D : ℕ}
    {state : AffineLowOrderLDCoordinate D → ℝ}
    (realization : LowOrderLDHaplotypeRealization state)
    (alpha : ℝ) (alpha_nonneg : 0 ≤ alpha) (alpha_le_one : alpha ≤ 1)
    (source recipient : Fin D) (outcome : realization.sampleSpace) :
    (realization.pulseHaplotype alpha alpha_nonneg alpha_le_one source recipient
        outcome recipient).linkage =
      alpha * (realization.haplotype outcome source).linkage +
        (1 - alpha) * (realization.haplotype outcome recipient).linkage +
        alpha * (1 - alpha) *
          ((realization.haplotype outcome source).leftFrequency -
            (realization.haplotype outcome recipient).leftFrequency) *
          ((realization.haplotype outcome source).rightFrequency -
            (realization.haplotype outcome recipient).rightFrequency) := by
  rw [LowOrderLDHaplotypeRealization.pulseHaplotype]
  simp only [if_pos]
  exact TwoLocusHaplotypeFrequencies.mixture_linkage _ _ _ _ _

/-- Every non-recipient deme is unchanged by the pulse witness. -/
theorem LowOrderLDHaplotypeRealization.pulseHaplotype_of_ne {D : ℕ}
    {state : AffineLowOrderLDCoordinate D → ℝ}
    (realization : LowOrderLDHaplotypeRealization state)
    (alpha : ℝ) (alpha_nonneg : 0 ≤ alpha) (alpha_le_one : alpha ≤ 1)
    (source recipient deme : Fin D) (distinct : deme ≠ recipient)
    (outcome : realization.sampleSpace) :
    realization.pulseHaplotype alpha alpha_nonneg alpha_le_one source recipient outcome deme =
      realization.haplotype outcome deme := by
  simp [LowOrderLDHaplotypeRealization.pulseHaplotype, distinct]

/-- A low-order state is `DD`-realizable when its complete `DD(i,j)` block is the Gram
kernel of actual linkage observables under one positive normalized linear expectation.

This is stronger than storing pairwise Cauchy--Schwarz inequalities: one common witness
simultaneously realizes every deme pair and therefore supplies symmetry, diagonal
nonnegativity, all finite quadratic-form inequalities, and Cauchy--Schwarz from the same law.
The remaining epoch theorem must show that the two-locus diffusion semigroup preserves this
witness class; deterministic split preservation is proved below. -/
structure LowOrderLDDDRealization {D : ℕ}
    (state : AffineLowOrderLDCoordinate D → ℝ) where
  sampleSpace : Type
  expectation : Foundations.ExpFunctional sampleSpace
  linkage : sampleSpace → Fin D → ℝ
  dd_eq : ∀ first second,
    state (some (.DD first second)) =
      expectation (fun outcome ↦ linkage outcome first * linkage outcome second)

namespace LowOrderLDHaplotypeRealization

/-- Forgetting allele frequencies retains a single Gram witness for the complete `DD`
block.  Thus every haplotype-realizable state automatically satisfies all PSD consequences
proved below. -/
def toDDDRealization {D : ℕ} {state : AffineLowOrderLDCoordinate D → ℝ}
    (realization : LowOrderLDHaplotypeRealization state) :
    LowOrderLDDDRealization state where
  sampleSpace := realization.sampleSpace
  expectation := realization.expectation
  linkage := fun outcome deme ↦ (realization.haplotype outcome deme).linkage
  dd_eq := realization.DD_eq

/-- Expected infinitesimal change of `DD(recipient,other)` under one directed migration
channel is exactly the `DD/Dz` stencil appearing in `lowOrderLDMigration`.  This derives the
row from the haplotype mixture law and the common expectation, rather than postulating its
four `Dz` signs. -/
theorem migrationLinkageVelocity_mul_linkage_expectation {D : ℕ}
    {state : AffineLowOrderLDCoordinate D → ℝ}
    (realization : LowOrderLDHaplotypeRealization state)
    (source recipient other : Fin D) :
    realization.expectation (fun outcome ↦
      (realization.haplotype outcome source).migrationLinkageVelocity
          (realization.haplotype outcome recipient) *
        (realization.haplotype outcome other).linkage) =
      state (some (.DD source other)) - state (some (.DD recipient other)) +
        (state (some (.Dz other recipient recipient)) -
          state (some (.Dz other recipient source)) -
          state (some (.Dz other source recipient)) +
          state (some (.Dz other source source))) / 4 := by
  have pointwise :
      (fun outcome ↦
        (realization.haplotype outcome source).migrationLinkageVelocity
            (realization.haplotype outcome recipient) *
          (realization.haplotype outcome other).linkage) =
        (fun outcome ↦
          (realization.haplotype outcome source).linkage *
            (realization.haplotype outcome other).linkage) -
        (fun outcome ↦
          (realization.haplotype outcome recipient).linkage *
            (realization.haplotype outcome other).linkage) +
        (1 / 4 : ℝ) •
          ((fun outcome ↦ twoLocusDzObservable
              (realization.haplotype outcome other)
              (realization.haplotype outcome recipient)
              (realization.haplotype outcome recipient)) -
            (fun outcome ↦ twoLocusDzObservable
              (realization.haplotype outcome other)
              (realization.haplotype outcome recipient)
              (realization.haplotype outcome source)) -
            (fun outcome ↦ twoLocusDzObservable
              (realization.haplotype outcome other)
              (realization.haplotype outcome source)
              (realization.haplotype outcome recipient)) +
            (fun outcome ↦ twoLocusDzObservable
              (realization.haplotype outcome other)
              (realization.haplotype outcome source)
              (realization.haplotype outcome source))) := by
    funext outcome
    simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [migrationLinkageVelocity_mul_linkage_eq_DD_Dz]
    ring
  rw [pointwise, realization.expectation.add_eval, realization.expectation.eval_sub,
    realization.expectation.smul_eval, realization.expectation.add_eval,
    realization.expectation.eval_sub, realization.expectation.eval_sub]
  rw [← realization.DD_eq source other, ← realization.DD_eq recipient other,
    ← realization.Dz_eq other recipient recipient,
    ← realization.Dz_eq other recipient source,
    ← realization.Dz_eq other source recipient,
    ← realization.Dz_eq other source source]
  ring

/-- The first endpoint stencil of a `DD(first,second)` migration row is precisely the
expected linkage velocity at `first` times the unchanged linkage at `second`. -/
theorem firstEndpointDDMigrationStencil_eq_expectation {D : ℕ}
    {state : AffineLowOrderLDCoordinate D → ℝ}
    (realization : LowOrderLDHaplotypeRealization state)
    (target first second : Fin D) :
    state (some (.DD target second)) - state (some (.DD first second)) +
        (state (some (.Dz second first first)) -
          state (some (.Dz second first target)) -
          state (some (.Dz second target first)) +
          state (some (.Dz second target target))) / 4 =
      realization.expectation (fun outcome ↦
        (realization.haplotype outcome target).migrationLinkageVelocity
            (realization.haplotype outcome first) *
          (realization.haplotype outcome second).linkage) := by
  symm
  exact realization.migrationLinkageVelocity_mul_linkage_expectation target first second

/-- The second endpoint stencil is the same product-rule term with the two `DD` factors
interchanged. -/
theorem secondEndpointDDMigrationStencil_eq_expectation {D : ℕ}
    {state : AffineLowOrderLDCoordinate D → ℝ}
    (realization : LowOrderLDHaplotypeRealization state)
    (target first second : Fin D) :
    state (some (.DD first target)) - state (some (.DD first second)) +
        (state (some (.Dz first second second)) -
          state (some (.Dz first second target)) -
          state (some (.Dz first target second)) +
          state (some (.Dz first target target))) / 4 =
      realization.expectation (fun outcome ↦
        (realization.haplotype outcome first).linkage *
          (realization.haplotype outcome target).migrationLinkageVelocity
            (realization.haplotype outcome second)) := by
  have target_symm :
      state (some (.DD first target)) = state (some (.DD target first)) := by
    rw [realization.DD_eq first target, realization.DD_eq target first]
    congr 1
    funext outcome
    ring
  have second_symm :
      state (some (.DD first second)) = state (some (.DD second first)) := by
    rw [realization.DD_eq first second, realization.DD_eq second first]
    congr 1
    funext outcome
    ring
  calc
    _ = realization.expectation (fun outcome ↦
        (realization.haplotype outcome target).migrationLinkageVelocity
            (realization.haplotype outcome second) *
          (realization.haplotype outcome first).linkage) := by
      rw [realization.migrationLinkageVelocity_mul_linkage_expectation target second first]
      rw [target_symm, second_symm]
    _ = _ := by
      congr 1
      funext outcome
      ring

/-- The linkage-index migration stencil of `Dz(first,second,third)` is the expected linkage
velocity at `first` multiplied by the two unchanged centered contrasts. -/
theorem linkageIndexDzMigrationStencil_eq_expectation {D : ℕ}
    {state : AffineLowOrderLDCoordinate D → ℝ}
    (realization : LowOrderLDHaplotypeRealization state)
    (target first second third : Fin D) :
    state (some (.Dz target second third)) - state (some (.Dz first second third)) +
        4 * (state (some (.pi2 first second first third)) -
          state (some (.pi2 first second third target)) -
          state (some (.pi2 second target first third)) +
          state (some (.pi2 second target third target))) =
      realization.expectation (fun outcome ↦
        (realization.haplotype outcome target).migrationLinkageVelocity
            (realization.haplotype outcome first) *
          (realization.haplotype outcome second).leftContrast *
          (realization.haplotype outcome third).rightContrast) := by
  have pointwise := migrationLinkageVelocity_mul_contrasts_eq_Dz_pi2
  symm
  calc
    _ = realization.expectation (fun outcome ↦
        twoLocusDzObservable (realization.haplotype outcome target)
            (realization.haplotype outcome second) (realization.haplotype outcome third) -
          twoLocusDzObservable (realization.haplotype outcome first)
            (realization.haplotype outcome second) (realization.haplotype outcome third) +
          4 * (twoLocusJointHeterozygosity (realization.haplotype outcome first)
              (realization.haplotype outcome second) (realization.haplotype outcome first)
              (realization.haplotype outcome third) -
            twoLocusJointHeterozygosity (realization.haplotype outcome first)
              (realization.haplotype outcome second) (realization.haplotype outcome third)
              (realization.haplotype outcome target) -
            twoLocusJointHeterozygosity (realization.haplotype outcome second)
              (realization.haplotype outcome target) (realization.haplotype outcome first)
              (realization.haplotype outcome third) +
            twoLocusJointHeterozygosity (realization.haplotype outcome second)
              (realization.haplotype outcome target) (realization.haplotype outcome third)
              (realization.haplotype outcome target))) := by
      congr 1
      funext outcome
      exact pointwise (realization.haplotype outcome target)
        (realization.haplotype outcome first) (realization.haplotype outcome second)
        (realization.haplotype outcome third)
    _ = _ := by
      have split_four : (fun outcome ↦
          4 * (twoLocusJointHeterozygosity (realization.haplotype outcome first)
              (realization.haplotype outcome second) (realization.haplotype outcome first)
              (realization.haplotype outcome third) -
            twoLocusJointHeterozygosity (realization.haplotype outcome first)
              (realization.haplotype outcome second) (realization.haplotype outcome third)
              (realization.haplotype outcome target) -
            twoLocusJointHeterozygosity (realization.haplotype outcome second)
              (realization.haplotype outcome target) (realization.haplotype outcome first)
              (realization.haplotype outcome third) +
            twoLocusJointHeterozygosity (realization.haplotype outcome second)
              (realization.haplotype outcome target) (realization.haplotype outcome third)
              (realization.haplotype outcome target))) =
          (4 : ℝ) • ((fun outcome ↦ twoLocusJointHeterozygosity
              (realization.haplotype outcome first) (realization.haplotype outcome second)
              (realization.haplotype outcome first) (realization.haplotype outcome third)) -
            (fun outcome ↦ twoLocusJointHeterozygosity
              (realization.haplotype outcome first) (realization.haplotype outcome second)
              (realization.haplotype outcome third) (realization.haplotype outcome target)) -
            (fun outcome ↦ twoLocusJointHeterozygosity
              (realization.haplotype outcome second) (realization.haplotype outcome target)
              (realization.haplotype outcome first) (realization.haplotype outcome third)) +
            (fun outcome ↦ twoLocusJointHeterozygosity
              (realization.haplotype outcome second) (realization.haplotype outcome target)
              (realization.haplotype outcome third) (realization.haplotype outcome target))) := by
        funext outcome
        simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      rw [show (fun outcome ↦
          twoLocusDzObservable (realization.haplotype outcome target)
              (realization.haplotype outcome second) (realization.haplotype outcome third) -
            twoLocusDzObservable (realization.haplotype outcome first)
              (realization.haplotype outcome second) (realization.haplotype outcome third) +
            4 * (twoLocusJointHeterozygosity (realization.haplotype outcome first)
                (realization.haplotype outcome second) (realization.haplotype outcome first)
                (realization.haplotype outcome third) -
              twoLocusJointHeterozygosity (realization.haplotype outcome first)
                (realization.haplotype outcome second) (realization.haplotype outcome third)
                (realization.haplotype outcome target) -
              twoLocusJointHeterozygosity (realization.haplotype outcome second)
                (realization.haplotype outcome target) (realization.haplotype outcome first)
                (realization.haplotype outcome third) +
              twoLocusJointHeterozygosity (realization.haplotype outcome second)
                (realization.haplotype outcome target) (realization.haplotype outcome third)
                (realization.haplotype outcome target))) =
          (fun outcome ↦ twoLocusDzObservable (realization.haplotype outcome target)
              (realization.haplotype outcome second) (realization.haplotype outcome third)) -
            (fun outcome ↦ twoLocusDzObservable (realization.haplotype outcome first)
              (realization.haplotype outcome second) (realization.haplotype outcome third)) +
            (fun outcome ↦ 4 * (twoLocusJointHeterozygosity
              (realization.haplotype outcome first) (realization.haplotype outcome second)
              (realization.haplotype outcome first) (realization.haplotype outcome third) -
              twoLocusJointHeterozygosity (realization.haplotype outcome first)
                (realization.haplotype outcome second) (realization.haplotype outcome third)
                (realization.haplotype outcome target) -
              twoLocusJointHeterozygosity (realization.haplotype outcome second)
                (realization.haplotype outcome target) (realization.haplotype outcome first)
                (realization.haplotype outcome third) +
              twoLocusJointHeterozygosity (realization.haplotype outcome second)
                (realization.haplotype outcome target) (realization.haplotype outcome third)
                (realization.haplotype outcome target))) by rfl]
      rw [realization.expectation.add_eval, realization.expectation.eval_sub, split_four,
        realization.expectation.smul_eval, realization.expectation.add_eval,
        realization.expectation.eval_sub, realization.expectation.eval_sub]
      rw [← realization.Dz_eq target second third, ← realization.Dz_eq first second third,
        ← realization.pi2_eq first second first third,
        ← realization.pi2_eq first second third target,
        ← realization.pi2_eq second target first third,
        ← realization.pi2_eq second target third target]

/-- The left-contrast index migration stencil is the expected left-contrast velocity. -/
theorem leftIndexDzMigrationStencil_eq_expectation {D : ℕ}
    {state : AffineLowOrderLDCoordinate D → ℝ}
    (realization : LowOrderLDHaplotypeRealization state)
    (target first second third : Fin D) :
    state (some (.Dz first target third)) - state (some (.Dz first second third)) =
      realization.expectation (fun outcome ↦
        (realization.haplotype outcome first).linkage *
          ((realization.haplotype outcome target).leftContrast -
            (realization.haplotype outcome second).leftContrast) *
          (realization.haplotype outcome third).rightContrast) := by
  symm
  calc
    _ = realization.expectation (fun outcome ↦
        twoLocusDzObservable (realization.haplotype outcome first)
            (realization.haplotype outcome target) (realization.haplotype outcome third) -
          twoLocusDzObservable (realization.haplotype outcome first)
            (realization.haplotype outcome second) (realization.haplotype outcome third)) := by
      congr 1
      funext outcome
      exact linkage_mul_leftContrastVelocity_mul_rightContrast _ _ _ _
    _ = _ := by
      rw [show (fun outcome ↦
          twoLocusDzObservable (realization.haplotype outcome first)
              (realization.haplotype outcome target) (realization.haplotype outcome third) -
            twoLocusDzObservable (realization.haplotype outcome first)
              (realization.haplotype outcome second) (realization.haplotype outcome third)) =
          (fun outcome ↦ twoLocusDzObservable (realization.haplotype outcome first)
            (realization.haplotype outcome target) (realization.haplotype outcome third)) -
          (fun outcome ↦ twoLocusDzObservable (realization.haplotype outcome first)
            (realization.haplotype outcome second) (realization.haplotype outcome third)) by rfl]
      rw [realization.expectation.eval_sub, ← realization.Dz_eq first target third,
        ← realization.Dz_eq first second third]

/-- The right-contrast index migration stencil is the expected right-contrast velocity. -/
theorem rightIndexDzMigrationStencil_eq_expectation {D : ℕ}
    {state : AffineLowOrderLDCoordinate D → ℝ}
    (realization : LowOrderLDHaplotypeRealization state)
    (target first second third : Fin D) :
    state (some (.Dz first second target)) - state (some (.Dz first second third)) =
      realization.expectation (fun outcome ↦
        (realization.haplotype outcome first).linkage *
          (realization.haplotype outcome second).leftContrast *
          ((realization.haplotype outcome target).rightContrast -
            (realization.haplotype outcome third).rightContrast)) := by
  symm
  calc
    _ = realization.expectation (fun outcome ↦
        twoLocusDzObservable (realization.haplotype outcome first)
            (realization.haplotype outcome second) (realization.haplotype outcome target) -
          twoLocusDzObservable (realization.haplotype outcome first)
            (realization.haplotype outcome second) (realization.haplotype outcome third)) := by
      congr 1
      funext outcome
      exact linkage_mul_leftContrast_mul_rightContrastVelocity _ _ _ _
    _ = _ := by
      rw [show (fun outcome ↦
          twoLocusDzObservable (realization.haplotype outcome first)
              (realization.haplotype outcome second) (realization.haplotype outcome target) -
            twoLocusDzObservable (realization.haplotype outcome first)
              (realization.haplotype outcome second) (realization.haplotype outcome third)) =
          (fun outcome ↦ twoLocusDzObservable (realization.haplotype outcome first)
            (realization.haplotype outcome second) (realization.haplotype outcome target)) -
          (fun outcome ↦ twoLocusDzObservable (realization.haplotype outcome first)
            (realization.haplotype outcome second) (realization.haplotype outcome third)) by rfl]
      rw [realization.expectation.eval_sub, ← realization.Dz_eq first second target,
        ← realization.Dz_eq first second third]

/-- Any `H` coordinate replacement is the expectation of the corresponding exact
cross-deme heterozygosity replacement. -/
theorem HReplacementStencil_eq_expectation {D : ℕ}
    {state : AffineLowOrderLDCoordinate D → ℝ}
    (realization : LowOrderLDHaplotypeRealization state)
    (first second newFirst newSecond : Fin D) :
    state (some (.H newFirst newSecond)) - state (some (.H first second)) =
      realization.expectation (fun outcome ↦
        twoLocusLeftHeterozygosity
            (realization.haplotype outcome newFirst)
            (realization.haplotype outcome newSecond) -
          twoLocusLeftHeterozygosity
            (realization.haplotype outcome first)
            (realization.haplotype outcome second)) := by
  rw [show (fun outcome ↦
      twoLocusLeftHeterozygosity
          (realization.haplotype outcome newFirst)
          (realization.haplotype outcome newSecond) -
        twoLocusLeftHeterozygosity
          (realization.haplotype outcome first)
          (realization.haplotype outcome second)) =
      (fun outcome ↦ twoLocusLeftHeterozygosity
        (realization.haplotype outcome newFirst)
        (realization.haplotype outcome newSecond)) -
      (fun outcome ↦ twoLocusLeftHeterozygosity
        (realization.haplotype outcome first)
        (realization.haplotype outcome second)) by rfl]
  rw [realization.expectation.eval_sub,
    ← realization.H_eq newFirst newSecond, ← realization.H_eq first second]

/-- Any generalized-`pi2` coordinate-replacement stencil is the expectation of the
corresponding haplotype-observable replacement.  The four migration channels below are its
one-index specializations, whose exact finite-pulse laws were proved above. -/
theorem pi2ReplacementStencil_eq_expectation {D : ℕ}
    {state : AffineLowOrderLDCoordinate D → ℝ}
    (realization : LowOrderLDHaplotypeRealization state)
    (leftFirst leftSecond rightFirst rightSecond
      newLeftFirst newLeftSecond newRightFirst newRightSecond : Fin D) :
    state (some (.pi2 newLeftFirst newLeftSecond newRightFirst newRightSecond)) -
        state (some (.pi2 leftFirst leftSecond rightFirst rightSecond)) =
      realization.expectation (fun outcome ↦
        twoLocusJointHeterozygosity
            (realization.haplotype outcome newLeftFirst)
            (realization.haplotype outcome newLeftSecond)
            (realization.haplotype outcome newRightFirst)
            (realization.haplotype outcome newRightSecond) -
          twoLocusJointHeterozygosity
            (realization.haplotype outcome leftFirst)
            (realization.haplotype outcome leftSecond)
            (realization.haplotype outcome rightFirst)
            (realization.haplotype outcome rightSecond)) := by
  rw [show (fun outcome ↦
      twoLocusJointHeterozygosity
          (realization.haplotype outcome newLeftFirst)
          (realization.haplotype outcome newLeftSecond)
          (realization.haplotype outcome newRightFirst)
          (realization.haplotype outcome newRightSecond) -
        twoLocusJointHeterozygosity
          (realization.haplotype outcome leftFirst)
          (realization.haplotype outcome leftSecond)
          (realization.haplotype outcome rightFirst)
          (realization.haplotype outcome rightSecond)) =
      (fun outcome ↦ twoLocusJointHeterozygosity
        (realization.haplotype outcome newLeftFirst)
        (realization.haplotype outcome newLeftSecond)
        (realization.haplotype outcome newRightFirst)
        (realization.haplotype outcome newRightSecond)) -
      (fun outcome ↦ twoLocusJointHeterozygosity
        (realization.haplotype outcome leftFirst)
        (realization.haplotype outcome leftSecond)
        (realization.haplotype outcome rightFirst)
        (realization.haplotype outcome rightSecond)) by rfl]
  rw [realization.expectation.eval_sub,
    ← realization.pi2_eq newLeftFirst newLeftSecond newRightFirst newRightSecond,
    ← realization.pi2_eq leftFirst leftSecond rightFirst rightSecond]

/-- `H(i,j)` is symmetric because its defining cross-deme heterozygosity polynomial is. -/
theorem H_symm {D : ℕ} {state : AffineLowOrderLDCoordinate D → ℝ}
    (realization : LowOrderLDHaplotypeRealization state) (first second : Fin D) :
    state (some (.H first second)) = state (some (.H second first)) := by
  rw [realization.H_eq first second, realization.H_eq second first]
  congr 1
  funext outcome
  simp only [twoLocusLeftHeterozygosity]
  ring

/-- Cross-deme heterozygosity is nonnegative on the haplotype simplex. -/
theorem H_nonneg {D : ℕ} {state : AffineLowOrderLDCoordinate D → ℝ}
    (realization : LowOrderLDHaplotypeRealization state) (first second : Fin D) :
    0 ≤ state (some (.H first second)) := by
  rw [realization.H_eq first second]
  apply realization.expectation.nonneg_eval
  intro outcome
  apply add_nonneg
  · exact mul_nonneg (realization.haplotype outcome first).leftFrequency_nonneg
      (sub_nonneg.mpr (realization.haplotype outcome second).leftFrequency_le_one)
  · exact mul_nonneg (realization.haplotype outcome second).leftFrequency_nonneg
      (sub_nonneg.mpr (realization.haplotype outcome first).leftFrequency_le_one)

/-- Generalized `pi2` is nonnegative because it is one quarter of a product of two
nonnegative cross-deme heterozygosities. -/
theorem pi2_nonneg {D : ℕ} {state : AffineLowOrderLDCoordinate D → ℝ}
    (realization : LowOrderLDHaplotypeRealization state)
    (first second third fourth : Fin D) :
    0 ≤ state (some (.pi2 first second third fourth)) := by
  rw [realization.pi2_eq first second third fourth]
  apply realization.expectation.nonneg_eval
  intro outcome
  apply div_nonneg
  · apply mul_nonneg
    · apply add_nonneg
      · exact mul_nonneg (realization.haplotype outcome first).leftFrequency_nonneg
          (sub_nonneg.mpr (realization.haplotype outcome second).leftFrequency_le_one)
      · exact mul_nonneg (realization.haplotype outcome second).leftFrequency_nonneg
          (sub_nonneg.mpr (realization.haplotype outcome first).leftFrequency_le_one)
    · apply add_nonneg
      · exact mul_nonneg (realization.haplotype outcome third).rightFrequency_nonneg
          (sub_nonneg.mpr (realization.haplotype outcome fourth).rightFrequency_le_one)
      · exact mul_nonneg (realization.haplotype outcome fourth).rightFrequency_nonneg
          (sub_nonneg.mpr (realization.haplotype outcome third).rightFrequency_le_one)
  · norm_num

/-- Every cross-deme `DD(i,j)=E[DᵢDⱼ]` coordinate obeys the sharp simplex scale
`|DD(i,j)| ≤ 1/16`.  This is independent of demography: history changes the law on the
simplex, while positivity of expectation preserves the pathwise determinant bound. -/
theorem DD_abs_le_sixteenth {D : ℕ}
    {state : AffineLowOrderLDCoordinate D → ℝ}
    (realization : LowOrderLDHaplotypeRealization state) (first second : Fin D) :
    |state (some (.DD first second))| ≤ 1 / 16 := by
  rw [realization.DD_eq first second, abs_le]
  constructor
  · calc
      -(1 / 16 : ℝ) = realization.expectation (fun _ ↦ -(1 / 16 : ℝ)) := by
        rw [realization.expectation.eval_const]
      _ ≤ realization.expectation (fun outcome ↦
          (realization.haplotype outcome first).linkage *
            (realization.haplotype outcome second).linkage) := by
        apply realization.expectation.eval_mono
        intro outcome
        have hfirst := (realization.haplotype outcome first).linkage_abs_le_quarter
        have hsecond := (realization.haplotype outcome second).linkage_abs_le_quarter
        have habs : |(realization.haplotype outcome first).linkage *
            (realization.haplotype outcome second).linkage| ≤ 1 / 16 := by
          rw [abs_mul]
          nlinarith [mul_nonneg (abs_nonneg
            (realization.haplotype outcome first).linkage)
            (sub_nonneg.mpr hsecond),
            mul_nonneg (sub_nonneg.mpr hfirst) (by norm_num : (0 : ℝ) ≤ 1 / 4)]
        exact (neg_le_of_abs_le habs)
  · calc
      realization.expectation (fun outcome ↦
          (realization.haplotype outcome first).linkage *
            (realization.haplotype outcome second).linkage) ≤
          realization.expectation (fun _ ↦ (1 / 16 : ℝ)) := by
        apply realization.expectation.eval_mono
        intro outcome
        have hfirst := (realization.haplotype outcome first).linkage_abs_le_quarter
        have hsecond := (realization.haplotype outcome second).linkage_abs_le_quarter
        have habs : |(realization.haplotype outcome first).linkage *
            (realization.haplotype outcome second).linkage| ≤ 1 / 16 := by
          rw [abs_mul]
          nlinarith [mul_nonneg (abs_nonneg
            (realization.haplotype outcome first).linkage)
            (sub_nonneg.mpr hsecond),
            mul_nonneg (sub_nonneg.mpr hfirst) (by norm_num : (0 : ℝ) ≤ 1 / 4)]
        exact (le_of_abs_le habs)
      _ = 1 / 16 := realization.expectation.eval_const _

/-- The `1/16` cross-moment bound is attained when all requested demes share the maximal
coupling simplex point. -/
theorem DD_sixteenth_attained {D : ℕ} (first second : Fin D) :
    haplotypeLowOrderLDState (Foundations.ExpFunctional.evalAt ())
        (fun _ (_ : Fin D) ↦ TwoLocusHaplotypeFrequencies.maximalCoupling)
        (some (.DD first second)) = 1 / 16 := by
  simp only [haplotypeLowOrderLDState, Foundations.ExpFunctional.evalAt]
  rw [TwoLocusHaplotypeFrequencies.maximalCoupling_linkage]
  norm_num

/-- Expected per-index mutation velocity of `H` is exactly its affine pull toward `1/2`. -/
theorem HMutationVelocity_expectation {D : ℕ}
    {state : AffineLowOrderLDCoordinate D → ℝ}
    (realization : LowOrderLDHaplotypeRealization state) (first second : Fin D) :
    realization.expectation (fun outcome ↦
      twoLocusHMutationVelocity (realization.haplotype outcome first)
        (realization.haplotype outcome second)) =
      1 / 2 - state (some (.H first second)) := by
  have pointwise : (fun outcome ↦
      twoLocusHMutationVelocity (realization.haplotype outcome first)
        (realization.haplotype outcome second)) =
      (fun _ ↦ (1 / 2 : ℝ)) - (fun outcome ↦
        twoLocusLeftHeterozygosity (realization.haplotype outcome first)
          (realization.haplotype outcome second)) := by
    funext outcome
    simp only [Pi.sub_apply]
    exact twoLocusHMutationVelocity_eq _ _
  rw [pointwise, realization.expectation.eval_sub,
    realization.expectation.eval_const, ← realization.H_eq first second]

end LowOrderLDHaplotypeRealization

namespace LocusExchangeableLowOrderLDHaplotypeRealization

/-- Expected left-channel `pi2` mutation velocity is exactly `H_right/8 - pi2`; locus
exchangeability identifies that right marginal with the stored `H` coordinate. -/
theorem pi2LeftMutationVelocity_expectation {D : ℕ}
    {state : AffineLowOrderLDCoordinate D → ℝ}
    (realization : LocusExchangeableLowOrderLDHaplotypeRealization state)
    (first second third fourth : Fin D) :
    realization.expectation (fun outcome ↦
      twoLocusPi2LeftMutationVelocity
        (realization.haplotype outcome first) (realization.haplotype outcome second)
        (realization.haplotype outcome third) (realization.haplotype outcome fourth)) =
      state (some (.H third fourth)) / 8 -
        state (some (.pi2 first second third fourth)) := by
  have pointwise : (fun outcome ↦
      twoLocusPi2LeftMutationVelocity
        (realization.haplotype outcome first) (realization.haplotype outcome second)
        (realization.haplotype outcome third) (realization.haplotype outcome fourth)) =
      (1 / 8 : ℝ) • (fun outcome ↦
        twoLocusRightHeterozygosity (realization.haplotype outcome third)
          (realization.haplotype outcome fourth)) -
      (fun outcome ↦ twoLocusJointHeterozygosity
        (realization.haplotype outcome first) (realization.haplotype outcome second)
        (realization.haplotype outcome third) (realization.haplotype outcome fourth)) := by
    funext outcome
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    rw [twoLocusPi2LeftMutationVelocity_eq]
    ring
  rw [pointwise, realization.expectation.eval_sub,
    realization.expectation.smul_eval,
    ← realization.H_right_eq third fourth,
    ← realization.pi2_eq first second third fourth]
  ring

/-- Expected right-channel `pi2` mutation velocity is exactly `H_left/8 - pi2`. -/
theorem pi2RightMutationVelocity_expectation {D : ℕ}
    {state : AffineLowOrderLDCoordinate D → ℝ}
    (realization : LocusExchangeableLowOrderLDHaplotypeRealization state)
    (first second third fourth : Fin D) :
    realization.expectation (fun outcome ↦
      twoLocusPi2RightMutationVelocity
        (realization.haplotype outcome first) (realization.haplotype outcome second)
        (realization.haplotype outcome third) (realization.haplotype outcome fourth)) =
      state (some (.H first second)) / 8 -
        state (some (.pi2 first second third fourth)) := by
  have pointwise : (fun outcome ↦
      twoLocusPi2RightMutationVelocity
        (realization.haplotype outcome first) (realization.haplotype outcome second)
        (realization.haplotype outcome third) (realization.haplotype outcome fourth)) =
      (1 / 8 : ℝ) • (fun outcome ↦
        twoLocusLeftHeterozygosity (realization.haplotype outcome first)
          (realization.haplotype outcome second)) -
      (fun outcome ↦ twoLocusJointHeterozygosity
        (realization.haplotype outcome first) (realization.haplotype outcome second)
        (realization.haplotype outcome third) (realization.haplotype outcome fourth)) := by
    funext outcome
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    rw [twoLocusPi2RightMutationVelocity_eq]
    ring
  rw [pointwise, realization.expectation.eval_sub,
    realization.expectation.smul_eval,
    ← realization.H_eq first second,
    ← realization.pi2_eq first second third fourth]
  ring

end LocusExchangeableLowOrderLDHaplotypeRealization

/-- The four-term generalized definition has exactly the classical within-deme
specialization; the normalization contains no fitted or conventional scale factor. -/
theorem twoLocusJointHeterozygosity_self
    (frequency : TwoLocusHaplotypeFrequencies) :
    twoLocusJointHeterozygosity frequency frequency frequency frequency =
      frequency.leftFrequency * (1 - frequency.leftFrequency) *
        frequency.rightFrequency * (1 - frequency.rightFrequency) := by
  simp only [twoLocusJointHeterozygosity, twoLocusLeftHeterozygosity,
    twoLocusRightHeterozygosity]
  ring

namespace LowOrderLDDDRealization

/-- Every realizable `DD` block is symmetric. -/
theorem dd_symm {D : ℕ} {state : AffineLowOrderLDCoordinate D → ℝ}
    (realization : LowOrderLDDDRealization state) (first second : Fin D) :
    state (some (.DD first second)) = state (some (.DD second first)) := by
  rw [realization.dd_eq first second, realization.dd_eq second first]
  congr 1
  funext outcome
  ring

/-- Every diagonal `DD(i,i) = E[Dᵢ²]` of a realizable state is nonnegative. -/
theorem dd_diagonal_nonneg {D : ℕ}
    {state : AffineLowOrderLDCoordinate D → ℝ}
    (realization : LowOrderLDDDRealization state) (deme : Fin D) :
    0 ≤ state (some (.DD deme deme)) := by
  rw [realization.dd_eq deme deme]
  exact realization.expectation.nonneg_eval _ fun outcome ↦
    mul_self_nonneg (realization.linkage outcome deme)

/-- A realizable `DD` block is positive semidefinite in the population-genetic form: every
finite linear combination of deme-specific linkage disequilibria has nonnegative second
moment. -/
theorem dd_quadraticForm_nonneg {D : ℕ}
    {state : AffineLowOrderLDCoordinate D → ℝ}
    (realization : LowOrderLDDDRealization state) (weight : Fin D → ℝ) :
    0 ≤ ∑ first, ∑ second,
      weight first * state (some (.DD first second)) * weight second := by
  simp_rw [realization.dd_eq]
  have square_nonneg : 0 ≤ realization.expectation (fun outcome ↦
      (∑ deme, weight deme * realization.linkage outcome deme) ^ 2) :=
    realization.expectation.nonneg_eval _ fun outcome ↦ sq_nonneg _
  have expectation_expand :
      realization.expectation (fun outcome ↦
          (∑ deme, weight deme * realization.linkage outcome deme) ^ 2) =
        ∑ first, ∑ second,
          weight first * realization.expectation (fun outcome ↦
            realization.linkage outcome first * realization.linkage outcome second) *
              weight second := by
    have pointwise : (fun outcome ↦
        (∑ deme, weight deme * realization.linkage outcome deme) ^ 2) =
      ∑ first, ∑ second, (weight first * weight second) •
        (fun outcome ↦ realization.linkage outcome first *
          realization.linkage outcome second) := by
      funext outcome
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      rw [pow_two, Finset.sum_mul_sum]
      apply Finset.sum_congr rfl
      intro first _
      apply Finset.sum_congr rfl
      intro second _
      ring
    rw [pointwise]
    simp_rw [Foundations.ExpFunctional.eval_sum, realization.expectation.smul_eval]
    apply Finset.sum_congr rfl
    intro first _
    apply Finset.sum_congr rfl
    intro second _
    ring
  rw [expectation_expand] at square_nonneg
  exact square_nonneg

/-- Pairwise Cauchy--Schwarz is a consequence of the common realization, not an independent
field attached to each requested pair. -/
theorem dd_cauchySchwarz {D : ℕ}
    {state : AffineLowOrderLDCoordinate D → ℝ}
    (realization : LowOrderLDDDRealization state) (first second : Fin D) :
    state (some (.DD first second)) ^ 2 ≤
      state (some (.DD first first)) * state (some (.DD second second)) := by
  rw [realization.dd_eq first second, realization.dd_eq first first,
    realization.dd_eq second second]
  simpa [pow_two] using realization.expectation.cauchy_schwarz
    (fun outcome ↦ realization.linkage outcome first)
    (fun outcome ↦ realization.linkage outcome second)

end LowOrderLDDDRealization

/-! ## The concrete arbitrary-deme generator -/

/-- Rates of the closed multi-deme `H/DD/Dz/pi2` system in one declared time scale. -/
structure ManyDemeLDRates (D : ℕ) where
  coalescence : Fin D → ℝ
  migration : Fin D → Fin D → ℝ
  mutation : Fin D → ℝ
  recombination : Fin D → ℝ
  coalescence_pos : ∀ deme, 0 < coalescence deme
  migration_nonneg : ∀ source target, 0 ≤ migration source target
  migration_self : ∀ deme, migration deme deme = 0
  mutation_nonneg : ∀ deme, 0 ≤ mutation deme
  recombination_nonneg : ∀ deme, 0 ≤ recombination deme

/-- Basis state used to read one coefficient of the concrete generator. -/
def lowOrderLDBasis {D : ℕ} (column : LowOrderLDCoordinate D) :
    LowOrderLDCoordinate D → ℝ :=
  fun coordinate ↦ if coordinate = column then 1 else 0

/-- Drift contribution to the closed low-order system.  The cases are equality patterns of
the population indices, not separate demographic assumptions. -/
noncomputable def lowOrderLDDrift {D : ℕ} (rates : ManyDemeLDRates D)
    (moment : LowOrderLDCoordinate D → ℝ) : LowOrderLDCoordinate D → ℝ
  | .H first second =>
      if first = second then -rates.coalescence first * moment (.H first second) else 0
  | .DD first second =>
      if first = second then
        rates.coalescence first *
          (-3 * moment (.DD first first) + moment (.Dz first first first) +
            moment (.pi2 first first first first))
      else
        -(rates.coalescence first + rates.coalescence second) * moment (.DD first second)
  | .Dz first second third =>
      if first = second ∧ second = third then
        rates.coalescence first *
          (4 * moment (.DD first first) - 5 * moment (.Dz first second third))
      else if first = second then
        -3 * rates.coalescence first * moment (.Dz first second third)
      else if first = third then
        -3 * rates.coalescence first * moment (.Dz first second third)
      else if second = third then
        4 * rates.coalescence second * moment (.DD first second) -
          rates.coalescence first * moment (.Dz first second third)
      else
        -rates.coalescence first * moment (.Dz first second third)
  | .pi2 first second third fourth =>
      if first = second ∧ second = third ∧ third = fourth then
        rates.coalescence first *
          (moment (.Dz first first first) - 2 * moment (.pi2 first second third fourth))
      else if first = second ∧ second = third then
        rates.coalescence first *
          (moment (.Dz first first fourth) / 2 - moment (.pi2 first second third fourth))
      else if first = second ∧ second = fourth then
        rates.coalescence first *
          (moment (.Dz first first third) / 2 - moment (.pi2 first second third fourth))
      else if first = third ∧ third = fourth then
        rates.coalescence first *
          (moment (.Dz first second first) / 2 - moment (.pi2 first second third fourth))
      else if second = third ∧ third = fourth then
        rates.coalescence second *
          (moment (.Dz second first second) / 2 - moment (.pi2 first second third fourth))
      else if first = second ∧ third = fourth then
        -(rates.coalescence first + rates.coalescence third) *
          moment (.pi2 first second third fourth)
      else if (first = third ∧ second = fourth) ∨ (first = fourth ∧ second = third) then
        rates.coalescence first / 4 * moment (.Dz first second second) +
          rates.coalescence second / 4 * moment (.Dz second first first)
      else if first = second then
        -rates.coalescence first * moment (.pi2 first second third fourth)
      else if first = third then
        rates.coalescence first / 4 * moment (.Dz first second fourth)
      else if first = fourth then
        rates.coalescence first / 4 * moment (.Dz first second third)
      else if second = third then
        rates.coalescence second / 4 * moment (.Dz second first fourth)
      else if second = fourth then
        rates.coalescence second / 4 * moment (.Dz second first third)
      else if third = fourth then
        -rates.coalescence third * moment (.pi2 first second third fourth)
      else 0

/-- Continuous migration contribution.  Each lineage index migrates separately.  The extra
`Dz` and `pi2` differences are exactly the terms created because `D` is nonlinear in
haplotype frequencies; this is where migration restores shared linkage. -/
noncomputable def lowOrderLDMigration {D : ℕ} (rates : ManyDemeLDRates D)
    (moment : LowOrderLDCoordinate D → ℝ) : LowOrderLDCoordinate D → ℝ
  | .H first second =>
      (∑ target, rates.migration first target *
        (moment (.H target second) - moment (.H first second))) +
      (∑ target, rates.migration second target *
        (moment (.H first target) - moment (.H first second)))
  | .DD first second =>
      (∑ target, rates.migration first target *
        (moment (.DD target second) - moment (.DD first second) +
          (moment (.Dz second first first) - moment (.Dz second first target) -
            moment (.Dz second target first) + moment (.Dz second target target)) / 4)) +
      (∑ target, rates.migration second target *
        (moment (.DD first target) - moment (.DD first second) +
          (moment (.Dz first second second) - moment (.Dz first second target) -
            moment (.Dz first target second) + moment (.Dz first target target)) / 4))
  | .Dz first second third =>
      (∑ target, rates.migration first target *
        (moment (.Dz target second third) - moment (.Dz first second third) +
          4 * (moment (.pi2 first second first third) -
            moment (.pi2 first second third target) -
            moment (.pi2 second target first third) +
            moment (.pi2 second target third target)))) +
      (∑ target, rates.migration second target *
        (moment (.Dz first target third) - moment (.Dz first second third))) +
      (∑ target, rates.migration third target *
        (moment (.Dz first second target) - moment (.Dz first second third)))
  | .pi2 first second third fourth =>
      (∑ target, rates.migration first target *
        (moment (.pi2 target second third fourth) -
          moment (.pi2 first second third fourth))) +
      (∑ target, rates.migration second target *
        (moment (.pi2 first target third fourth) -
          moment (.pi2 first second third fourth))) +
      (∑ target, rates.migration third target *
        (moment (.pi2 first second target fourth) -
          moment (.pi2 first second third fourth))) +
      (∑ target, rates.migration fourth target *
        (moment (.pi2 first second third target) -
          moment (.pi2 first second third fourth)))

/-- **The complete `H` migration row is the two-factor product rule.**  Each lineage
channel is the derivative of the exact affine heterozygosity pulse law. -/
theorem lowOrderLDMigration_H_eq_haplotypeVelocity {D : ℕ}
    (rates : ManyDemeLDRates D)
    {state : AffineLowOrderLDCoordinate D → ℝ}
    (realization : LowOrderLDHaplotypeRealization state)
    (first second : Fin D) :
    lowOrderLDMigration rates (fun coordinate ↦ state (some coordinate)) (.H first second) =
      (∑ target, rates.migration first target *
        realization.expectation (fun outcome ↦
          twoLocusLeftHeterozygosity
              (realization.haplotype outcome target)
              (realization.haplotype outcome second) -
            twoLocusLeftHeterozygosity
              (realization.haplotype outcome first)
              (realization.haplotype outcome second))) +
      (∑ target, rates.migration second target *
        realization.expectation (fun outcome ↦
          twoLocusLeftHeterozygosity
              (realization.haplotype outcome first)
              (realization.haplotype outcome target) -
            twoLocusLeftHeterozygosity
              (realization.haplotype outcome first)
              (realization.haplotype outcome second))) := by
  simp only [lowOrderLDMigration]
  congr 1
  · apply Finset.sum_congr rfl
    intro target _
    rw [realization.HReplacementStencil_eq_expectation
      first second target second]
  · apply Finset.sum_congr rfl
    intro target _
    rw [realization.HReplacementStencil_eq_expectation
      first second first target]

/-- **The complete `DD` migration row is the expectation-level product rule for the exact
haplotype-mixture velocity.**  Each directed channel acts at one endpoint, and the two
endpoint sums are exactly the two terms obtained by differentiating `E[D_first D_second]`.
This is the formal migration-restoration bridge for the linkage covariance block. -/
theorem lowOrderLDMigration_DD_eq_haplotypeVelocity {D : ℕ}
    (rates : ManyDemeLDRates D)
    {state : AffineLowOrderLDCoordinate D → ℝ}
    (realization : LowOrderLDHaplotypeRealization state)
    (first second : Fin D) :
    lowOrderLDMigration rates (fun coordinate ↦ state (some coordinate)) (.DD first second) =
      (∑ target, rates.migration first target *
        realization.expectation (fun outcome ↦
          (realization.haplotype outcome target).migrationLinkageVelocity
              (realization.haplotype outcome first) *
            (realization.haplotype outcome second).linkage)) +
      (∑ target, rates.migration second target *
        realization.expectation (fun outcome ↦
          (realization.haplotype outcome first).linkage *
            (realization.haplotype outcome target).migrationLinkageVelocity
              (realization.haplotype outcome second))) := by
  simp only [lowOrderLDMigration]
  congr 1
  · apply Finset.sum_congr rfl
    intro target _
    rw [realization.firstEndpointDDMigrationStencil_eq_expectation target first second]
  · apply Finset.sum_congr rfl
    intro target _
    rw [realization.secondEndpointDDMigrationStencil_eq_expectation target first second]

/-- **The complete `Dz` migration row is the three-factor product rule.**  Migration at
the linkage index uses the exact restored-linkage velocity, including its differentiation
term; migration at either marginal index replaces the corresponding centered contrast.
Thus every correction in the generator's `Dz` row is forced by haplotype mixture. -/
theorem lowOrderLDMigration_Dz_eq_haplotypeVelocity {D : ℕ}
    (rates : ManyDemeLDRates D)
    {state : AffineLowOrderLDCoordinate D → ℝ}
    (realization : LowOrderLDHaplotypeRealization state)
    (first second third : Fin D) :
    lowOrderLDMigration rates (fun coordinate ↦ state (some coordinate))
        (.Dz first second third) =
      (∑ target, rates.migration first target *
        realization.expectation (fun outcome ↦
          (realization.haplotype outcome target).migrationLinkageVelocity
              (realization.haplotype outcome first) *
            (realization.haplotype outcome second).leftContrast *
            (realization.haplotype outcome third).rightContrast)) +
      (∑ target, rates.migration second target *
        realization.expectation (fun outcome ↦
          (realization.haplotype outcome first).linkage *
            ((realization.haplotype outcome target).leftContrast -
              (realization.haplotype outcome second).leftContrast) *
            (realization.haplotype outcome third).rightContrast)) +
      (∑ target, rates.migration third target *
        realization.expectation (fun outcome ↦
          (realization.haplotype outcome first).linkage *
            (realization.haplotype outcome second).leftContrast *
            ((realization.haplotype outcome target).rightContrast -
              (realization.haplotype outcome third).rightContrast))) := by
  simp only [lowOrderLDMigration]
  congr 1
  · congr 1
    · apply Finset.sum_congr rfl
      intro target _
      rw [realization.linkageIndexDzMigrationStencil_eq_expectation target first second third]
    · apply Finset.sum_congr rfl
      intro target _
      rw [realization.leftIndexDzMigrationStencil_eq_expectation target first second third]
  · apply Finset.sum_congr rfl
    intro target _
    rw [realization.rightIndexDzMigrationStencil_eq_expectation target first second third]

/-- **The complete generalized-`pi2` migration row is the four-factor product rule.**
Each lineage channel is the source-minus-recipient derivative of the exact affine pulse law
for that haplotype argument.  This closes the migration correspondence for all four
low-order coordinate families. -/
theorem lowOrderLDMigration_pi2_eq_haplotypeVelocity {D : ℕ}
    (rates : ManyDemeLDRates D)
    {state : AffineLowOrderLDCoordinate D → ℝ}
    (realization : LowOrderLDHaplotypeRealization state)
    (first second third fourth : Fin D) :
    lowOrderLDMigration rates (fun coordinate ↦ state (some coordinate))
        (.pi2 first second third fourth) =
      (∑ target, rates.migration first target *
        realization.expectation (fun outcome ↦
          twoLocusJointHeterozygosity
              (realization.haplotype outcome target)
              (realization.haplotype outcome second)
              (realization.haplotype outcome third)
              (realization.haplotype outcome fourth) -
            twoLocusJointHeterozygosity
              (realization.haplotype outcome first)
              (realization.haplotype outcome second)
              (realization.haplotype outcome third)
              (realization.haplotype outcome fourth))) +
      (∑ target, rates.migration second target *
        realization.expectation (fun outcome ↦
          twoLocusJointHeterozygosity
              (realization.haplotype outcome first)
              (realization.haplotype outcome target)
              (realization.haplotype outcome third)
              (realization.haplotype outcome fourth) -
            twoLocusJointHeterozygosity
              (realization.haplotype outcome first)
              (realization.haplotype outcome second)
              (realization.haplotype outcome third)
              (realization.haplotype outcome fourth))) +
      (∑ target, rates.migration third target *
        realization.expectation (fun outcome ↦
          twoLocusJointHeterozygosity
              (realization.haplotype outcome first)
              (realization.haplotype outcome second)
              (realization.haplotype outcome target)
              (realization.haplotype outcome fourth) -
            twoLocusJointHeterozygosity
              (realization.haplotype outcome first)
              (realization.haplotype outcome second)
              (realization.haplotype outcome third)
              (realization.haplotype outcome fourth))) +
      (∑ target, rates.migration fourth target *
        realization.expectation (fun outcome ↦
          twoLocusJointHeterozygosity
              (realization.haplotype outcome first)
              (realization.haplotype outcome second)
              (realization.haplotype outcome third)
              (realization.haplotype outcome target) -
            twoLocusJointHeterozygosity
              (realization.haplotype outcome first)
              (realization.haplotype outcome second)
              (realization.haplotype outcome third)
              (realization.haplotype outcome fourth))) := by
  simp only [lowOrderLDMigration]
  congr 1
  · congr 1
    · congr 1
      · apply Finset.sum_congr rfl
        intro target _
        rw [realization.pi2ReplacementStencil_eq_expectation
          first second third fourth target second third fourth]
      · apply Finset.sum_congr rfl
        intro target _
        rw [realization.pi2ReplacementStencil_eq_expectation
          first second third fourth first target third fourth]
    · apply Finset.sum_congr rfl
      intro target _
      rw [realization.pi2ReplacementStencil_eq_expectation
        first second third fourth first second target fourth]
  · apply Finset.sum_congr rfl
    intro target _
    rw [realization.pi2ReplacementStencil_eq_expectation
      first second third fourth first second third target]

/-- Recombination damps each `D` factor at half its deme-specific scaled rate. -/
noncomputable def lowOrderLDRecombination {D : ℕ} (rates : ManyDemeLDRates D)
    (moment : LowOrderLDCoordinate D → ℝ) : LowOrderLDCoordinate D → ℝ
  | .H _ _ => 0
  | .DD first second =>
      -(rates.recombination first + rates.recombination second) / 2 *
        moment (.DD first second)
  | .Dz first second third =>
      -rates.recombination first / 2 * moment (.Dz first second third)
  | .pi2 _ _ _ _ => 0

/-- The `H` recombination row vanishes, as forced by exact marginal preservation under the
haplotype recombination pulse. -/
theorem lowOrderLDRecombination_H_eq_zero {D : ℕ}
    (rates : ManyDemeLDRates D) (moment : LowOrderLDCoordinate D → ℝ)
    (first second : Fin D) :
    lowOrderLDRecombination rates moment (.H first second) = 0 := by
  rfl

/-- **The complete `DD` recombination row is the two-factor product rule for the exact
linkage velocity `-D`.**  The factor `1/2` converts each deme's scaled recombination
coordinate `rho = 4 N_ref r` to its per-lineage event rate after time is rescaled by
`2 N_ref`, matching the Ragsdale--Gravel diffusion convention. -/
theorem lowOrderLDRecombination_DD_eq_haplotypeVelocity {D : ℕ}
    (rates : ManyDemeLDRates D)
    {state : AffineLowOrderLDCoordinate D → ℝ}
    (realization : LowOrderLDHaplotypeRealization state)
    (first second : Fin D) :
    lowOrderLDRecombination rates (fun coordinate ↦ state (some coordinate))
        (.DD first second) =
      rates.recombination first / 2 *
        realization.expectation (fun outcome ↦
          (realization.haplotype outcome first).recombinationLinkageVelocity *
            (realization.haplotype outcome second).linkage) +
      rates.recombination second / 2 *
        realization.expectation (fun outcome ↦
          (realization.haplotype outcome first).linkage *
            (realization.haplotype outcome second).recombinationLinkageVelocity) := by
  have first_velocity : (fun outcome ↦
      (realization.haplotype outcome first).recombinationLinkageVelocity *
        (realization.haplotype outcome second).linkage) =
      (-1 : ℝ) • (fun outcome ↦
        (realization.haplotype outcome first).linkage *
          (realization.haplotype outcome second).linkage) := by
    funext outcome
    simp only [TwoLocusHaplotypeFrequencies.recombinationLinkageVelocity,
      Pi.smul_apply, smul_eq_mul]
    ring
  have second_velocity : (fun outcome ↦
      (realization.haplotype outcome first).linkage *
        (realization.haplotype outcome second).recombinationLinkageVelocity) =
      (-1 : ℝ) • (fun outcome ↦
        (realization.haplotype outcome first).linkage *
          (realization.haplotype outcome second).linkage) := by
    funext outcome
    simp only [TwoLocusHaplotypeFrequencies.recombinationLinkageVelocity,
      Pi.smul_apply, smul_eq_mul]
    ring
  simp only [lowOrderLDRecombination]
  rw [first_velocity, second_velocity, realization.expectation.smul_eval,
    ← realization.DD_eq first second]
  ring

/-- **The complete `Dz` recombination row is the exact linkage derivative times its two
unchanged marginal contrasts.** -/
theorem lowOrderLDRecombination_Dz_eq_haplotypeVelocity {D : ℕ}
    (rates : ManyDemeLDRates D)
    {state : AffineLowOrderLDCoordinate D → ℝ}
    (realization : LowOrderLDHaplotypeRealization state)
    (first second third : Fin D) :
    lowOrderLDRecombination rates (fun coordinate ↦ state (some coordinate))
        (.Dz first second third) =
      rates.recombination first / 2 *
        realization.expectation (fun outcome ↦
          (realization.haplotype outcome first).recombinationLinkageVelocity *
            (realization.haplotype outcome second).leftContrast *
            (realization.haplotype outcome third).rightContrast) := by
  have velocity : (fun outcome ↦
      (realization.haplotype outcome first).recombinationLinkageVelocity *
        (realization.haplotype outcome second).leftContrast *
        (realization.haplotype outcome third).rightContrast) =
      (-1 : ℝ) • (fun outcome ↦
        twoLocusDzObservable (realization.haplotype outcome first)
          (realization.haplotype outcome second)
          (realization.haplotype outcome third)) := by
    funext outcome
    simp only [TwoLocusHaplotypeFrequencies.recombinationLinkageVelocity,
      twoLocusDzObservable, Pi.smul_apply, smul_eq_mul]
    ring
  simp only [lowOrderLDRecombination]
  rw [velocity, realization.expectation.smul_eval,
    ← realization.Dz_eq first second third]
  ring

/-- The generalized-`pi2` recombination row vanishes, as forced by exact preservation of
both marginal-frequency pairs under recombination. -/
theorem lowOrderLDRecombination_pi2_eq_zero {D : ℕ}
    (rates : ManyDemeLDRates D) (moment : LowOrderLDCoordinate D → ℝ)
    (first second third fourth : Fin D) :
    lowOrderLDRecombination rates moment (.pi2 first second third fourth) = 0 := by
  rfl

/-- Mutation coupling from single-locus heterozygosity into joint heterozygosity. -/
noncomputable def lowOrderLDMutationCoupling {D : ℕ} (rates : ManyDemeLDRates D)
    (moment : LowOrderLDCoordinate D → ℝ) : LowOrderLDCoordinate D → ℝ
  | .pi2 first second third fourth =>
      (rates.mutation third + rates.mutation fourth) / 8 * moment (.H first second) +
      (rates.mutation first + rates.mutation second) / 8 * moment (.H third fourth)
  | _ => 0

/-- Exact recurrent symmetric-biallelic mutation damping.

The rate coordinate is `theta = 2u`.  A centered allele contrast decays at rate `theta`,
so a within-deme linkage covariance `D` (two contrasts) decays at `2 theta`.  Counting the
contrasts in each product gives the four rows below: two `D` factors in `DD`; one `D` and two
single-locus contrasts in `Dz`; and four single-locus contrasts in `pi2`.  The `H` row is the
return-mutation correction to the affine heterozygosity influx.  This is the term absent from
the infinite-sites leading-order system. -/
noncomputable def lowOrderLDRecurrentMutationDamping {D : ℕ}
    (rates : ManyDemeLDRates D) (moment : LowOrderLDCoordinate D → ℝ) :
    LowOrderLDCoordinate D → ℝ
  | .H first second =>
      -(rates.mutation first + rates.mutation second) * moment (.H first second)
  | .DD first second =>
      -2 * (rates.mutation first + rates.mutation second) * moment (.DD first second)
  | .Dz first second third =>
      -(2 * rates.mutation first + rates.mutation second + rates.mutation third) *
        moment (.Dz first second third)
  | .pi2 first second third fourth =>
      -(rates.mutation first + rates.mutation second + rates.mutation third +
          rates.mutation fourth) * moment (.pi2 first second third fourth)

/-- Affine mutation influx into the heterozygosity coordinates. -/
noncomputable def lowOrderLDMutationForcing {D : ℕ} (rates : ManyDemeLDRates D) :
    LowOrderLDCoordinate D → ℝ
  | .H first second => (rates.mutation first + rates.mutation second) / 2
  | _ => 0

/-- **The complete affine `H` mutation row is the expected contrast-decay velocity.**
The apparently separate constant forcing and recurrent damping are the expansion of the
single exact law `theta * E[z_first z_second / 2]` at each lineage index. -/
theorem lowOrderLDMutation_H_eq_haplotypeVelocity {D : ℕ}
    (rates : ManyDemeLDRates D)
    {state : AffineLowOrderLDCoordinate D → ℝ}
    (realization : LowOrderLDHaplotypeRealization state)
    (first second : Fin D) :
    lowOrderLDMutationCoupling rates (fun coordinate ↦ state (some coordinate))
          (.H first second) +
        lowOrderLDRecurrentMutationDamping rates
          (fun coordinate ↦ state (some coordinate)) (.H first second) +
        lowOrderLDMutationForcing rates (.H first second) * state none =
      rates.mutation first * realization.expectation (fun outcome ↦
        twoLocusHMutationVelocity (realization.haplotype outcome first)
          (realization.haplotype outcome second)) +
      rates.mutation second * realization.expectation (fun outcome ↦
        twoLocusHMutationVelocity (realization.haplotype outcome first)
          (realization.haplotype outcome second)) := by
  simp only [lowOrderLDMutationCoupling, lowOrderLDRecurrentMutationDamping,
    lowOrderLDMutationForcing]
  rw [realization.constant_eq,
    realization.HMutationVelocity_expectation first second]
  ring

/-- **The complete `DD` mutation row is the two-factor product rule for the exact scaled
linkage velocity `-2D`.** -/
theorem lowOrderLDMutation_DD_eq_haplotypeVelocity {D : ℕ}
    (rates : ManyDemeLDRates D)
    {state : AffineLowOrderLDCoordinate D → ℝ}
    (realization : LowOrderLDHaplotypeRealization state)
    (first second : Fin D) :
    lowOrderLDMutationCoupling rates (fun coordinate ↦ state (some coordinate))
          (.DD first second) +
        lowOrderLDRecurrentMutationDamping rates
          (fun coordinate ↦ state (some coordinate)) (.DD first second) +
        lowOrderLDMutationForcing rates (.DD first second) * state none =
      rates.mutation first * realization.expectation (fun outcome ↦
        (realization.haplotype outcome first).scaledMutationLinkageVelocity *
          (realization.haplotype outcome second).linkage) +
      rates.mutation second * realization.expectation (fun outcome ↦
        (realization.haplotype outcome first).linkage *
          (realization.haplotype outcome second).scaledMutationLinkageVelocity) := by
  have first_velocity : (fun outcome ↦
      (realization.haplotype outcome first).scaledMutationLinkageVelocity *
        (realization.haplotype outcome second).linkage) =
      (-2 : ℝ) • (fun outcome ↦
        (realization.haplotype outcome first).linkage *
          (realization.haplotype outcome second).linkage) := by
    funext outcome
    simp only [TwoLocusHaplotypeFrequencies.scaledMutationLinkageVelocity,
      Pi.smul_apply, smul_eq_mul]
    ring
  have second_velocity : (fun outcome ↦
      (realization.haplotype outcome first).linkage *
        (realization.haplotype outcome second).scaledMutationLinkageVelocity) =
      (-2 : ℝ) • (fun outcome ↦
        (realization.haplotype outcome first).linkage *
          (realization.haplotype outcome second).linkage) := by
    funext outcome
    simp only [TwoLocusHaplotypeFrequencies.scaledMutationLinkageVelocity,
      Pi.smul_apply, smul_eq_mul]
    ring
  simp only [lowOrderLDMutationCoupling, lowOrderLDRecurrentMutationDamping,
    lowOrderLDMutationForcing]
  rw [first_velocity, second_velocity, realization.expectation.smul_eval,
    ← realization.DD_eq first second]
  ring

/-- **The complete `Dz` mutation row is the three-factor product rule.**  Its linkage
factor contributes two contrast-decay channels and its two marginal contrasts contribute
one each. -/
theorem lowOrderLDMutation_Dz_eq_haplotypeVelocity {D : ℕ}
    (rates : ManyDemeLDRates D)
    {state : AffineLowOrderLDCoordinate D → ℝ}
    (realization : LowOrderLDHaplotypeRealization state)
    (first second third : Fin D) :
    lowOrderLDMutationCoupling rates (fun coordinate ↦ state (some coordinate))
          (.Dz first second third) +
        lowOrderLDRecurrentMutationDamping rates
          (fun coordinate ↦ state (some coordinate)) (.Dz first second third) +
        lowOrderLDMutationForcing rates (.Dz first second third) * state none =
      rates.mutation first * realization.expectation (fun outcome ↦
        (realization.haplotype outcome first).scaledMutationLinkageVelocity *
          (realization.haplotype outcome second).leftContrast *
          (realization.haplotype outcome third).rightContrast) +
      rates.mutation second * realization.expectation (fun outcome ↦
        (realization.haplotype outcome first).linkage *
          (realization.haplotype outcome second).scaledMutationLeftContrastVelocity *
          (realization.haplotype outcome third).rightContrast) +
      rates.mutation third * realization.expectation (fun outcome ↦
        (realization.haplotype outcome first).linkage *
          (realization.haplotype outcome second).leftContrast *
          (realization.haplotype outcome third).scaledMutationRightContrastVelocity) := by
  have linkage_velocity : (fun outcome ↦
      (realization.haplotype outcome first).scaledMutationLinkageVelocity *
        (realization.haplotype outcome second).leftContrast *
        (realization.haplotype outcome third).rightContrast) =
      (-2 : ℝ) • (fun outcome ↦
        twoLocusDzObservable (realization.haplotype outcome first)
          (realization.haplotype outcome second)
          (realization.haplotype outcome third)) := by
    funext outcome
    simp only [TwoLocusHaplotypeFrequencies.scaledMutationLinkageVelocity,
      twoLocusDzObservable, Pi.smul_apply, smul_eq_mul]
    ring
  have left_velocity : (fun outcome ↦
      (realization.haplotype outcome first).linkage *
        (realization.haplotype outcome second).scaledMutationLeftContrastVelocity *
        (realization.haplotype outcome third).rightContrast) =
      (-1 : ℝ) • (fun outcome ↦
        twoLocusDzObservable (realization.haplotype outcome first)
          (realization.haplotype outcome second)
          (realization.haplotype outcome third)) := by
    funext outcome
    simp only [TwoLocusHaplotypeFrequencies.scaledMutationLeftContrastVelocity,
      twoLocusDzObservable, Pi.smul_apply, smul_eq_mul]
    ring
  have right_velocity : (fun outcome ↦
      (realization.haplotype outcome first).linkage *
        (realization.haplotype outcome second).leftContrast *
        (realization.haplotype outcome third).scaledMutationRightContrastVelocity) =
      (-1 : ℝ) • (fun outcome ↦
        twoLocusDzObservable (realization.haplotype outcome first)
          (realization.haplotype outcome second)
          (realization.haplotype outcome third)) := by
    funext outcome
    simp only [TwoLocusHaplotypeFrequencies.scaledMutationRightContrastVelocity,
      twoLocusDzObservable, Pi.smul_apply, smul_eq_mul]
    ring
  simp only [lowOrderLDMutationCoupling, lowOrderLDRecurrentMutationDamping,
    lowOrderLDMutationForcing]
  rw [linkage_velocity, left_velocity, right_velocity]
  simp only [realization.expectation.smul_eval]
  rw [← realization.Dz_eq first second third]
  ring

/-- **The complete generalized-`pi2` mutation row is the four-factor product rule.**
Its two `H/8` coupling terms and four damping terms are therefore derived consequences of
the exact symmetric allele-flip channel.  Locus exchangeability is explicit in the type. -/
theorem lowOrderLDMutation_pi2_eq_haplotypeVelocity {D : ℕ}
    (rates : ManyDemeLDRates D)
    {state : AffineLowOrderLDCoordinate D → ℝ}
    (realization : LocusExchangeableLowOrderLDHaplotypeRealization state)
    (first second third fourth : Fin D) :
    lowOrderLDMutationCoupling rates (fun coordinate ↦ state (some coordinate))
          (.pi2 first second third fourth) +
        lowOrderLDRecurrentMutationDamping rates
          (fun coordinate ↦ state (some coordinate)) (.pi2 first second third fourth) +
        lowOrderLDMutationForcing rates (.pi2 first second third fourth) * state none =
      rates.mutation first * realization.expectation (fun outcome ↦
        twoLocusPi2LeftMutationVelocity
          (realization.haplotype outcome first) (realization.haplotype outcome second)
          (realization.haplotype outcome third) (realization.haplotype outcome fourth)) +
      rates.mutation second * realization.expectation (fun outcome ↦
        twoLocusPi2LeftMutationVelocity
          (realization.haplotype outcome first) (realization.haplotype outcome second)
          (realization.haplotype outcome third) (realization.haplotype outcome fourth)) +
      rates.mutation third * realization.expectation (fun outcome ↦
        twoLocusPi2RightMutationVelocity
          (realization.haplotype outcome first) (realization.haplotype outcome second)
          (realization.haplotype outcome third) (realization.haplotype outcome fourth)) +
      rates.mutation fourth * realization.expectation (fun outcome ↦
        twoLocusPi2RightMutationVelocity
          (realization.haplotype outcome first) (realization.haplotype outcome second)
          (realization.haplotype outcome third) (realization.haplotype outcome fourth)) := by
  simp only [lowOrderLDMutationCoupling, lowOrderLDRecurrentMutationDamping,
    lowOrderLDMutationForcing]
  rw [realization.pi2LeftMutationVelocity_expectation first second third fourth,
    realization.pi2RightMutationVelocity_expectation first second third fourth]
  ring

/-- The derived homogeneous generator for arbitrary deme count. -/
noncomputable def lowOrderLDHomogeneousGenerator {D : ℕ} (rates : ManyDemeLDRates D)
    (moment : LowOrderLDCoordinate D → ℝ) (coordinate : LowOrderLDCoordinate D) : ℝ :=
  lowOrderLDDrift rates moment coordinate + lowOrderLDMigration rates moment coordinate +
    lowOrderLDRecombination rates moment coordinate +
    lowOrderLDMutationCoupling rates moment coordinate +
    lowOrderLDRecurrentMutationDamping rates moment coordinate

/-- The homogeneous affine `H` row of the complete two-locus generator is exactly the shared
pair-divergence law, with its constant coordinate kept explicit.  Recombination and all
higher joint coordinates disappear algebraically. -/
theorem lowOrderLDAffine_H_eq_symmetricPairDivergence_affine {D : ℕ}
    (rates : ManyDemeLDRates D) (moment : LowOrderLDCoordinate D → ℝ)
    (constant : ℝ)
    (first second : Fin D) :
    lowOrderLDHomogeneousGenerator rates moment (.H first second) +
        lowOrderLDMutationForcing rates (.H first second) * constant =
      symmetricPairDivergenceAffineDerivative rates.coalescence rates.migration rates.mutation
        (fun source target ↦ moment (.H source target)) constant first second := by
  simp [lowOrderLDHomogeneousGenerator, lowOrderLDDrift, lowOrderLDMigration,
    lowOrderLDRecombination, lowOrderLDMutationCoupling,
    lowOrderLDRecurrentMutationDamping, lowOrderLDMutationForcing,
    symmetricPairDivergenceAffineDerivative] <;> ring

/-- The probability-law specialization of the affine `H`-row identity. -/
theorem lowOrderLDAffine_H_eq_symmetricPairDivergence {D : ℕ}
    (rates : ManyDemeLDRates D) (moment : LowOrderLDCoordinate D → ℝ)
    (first second : Fin D) :
    lowOrderLDHomogeneousGenerator rates moment (.H first second) +
        lowOrderLDMutationForcing rates (.H first second) =
      symmetricPairDivergenceDerivative rates.coalescence rates.migration rates.mutation
        (fun source target ↦ moment (.H source target)) first second := by
  simpa [symmetricPairDivergenceDerivative] using
    lowOrderLDAffine_H_eq_symmetricPairDivergence_affine rates moment 1 first second

/-- Concrete constant-augmented matrix of the arbitrary-deme moment ODE. -/
noncomputable def augmentedLowOrderLDGenerator {D : ℕ} (rates : ManyDemeLDRates D) :
    Matrix (AffineLowOrderLDCoordinate D) (AffineLowOrderLDCoordinate D) ℝ
  | some row, some column => lowOrderLDHomogeneousGenerator rates (lowOrderLDBasis column) row
  | some row, none => lowOrderLDMutationForcing rates row
  | none, _ => 0

/-- Linear readout retaining only the affine constant and all ordered `H` coordinates from
the complete low-order two-locus state. -/
def lowOrderLDHProjectionLinearMap {D : ℕ} :
    (AffineLowOrderLDCoordinate D → ℝ) →ₗ[ℝ]
      (AffinePairDivergenceCoordinate D → ℝ) where
  toFun state coordinate := match coordinate with
    | none => state none
    | some (first, second) => state (some (.H first second))
  map_add' := by
    intro left right
    funext coordinate
    cases coordinate <;> simp
  map_smul' := by
    intro scalar state
    funext coordinate
    cases coordinate <;> simp

/-- Rectangular matrix selecting the closed `H` subsystem from the joint state. -/
noncomputable def lowOrderLDHProjection (D : ℕ) :
    Matrix (AffinePairDivergenceCoordinate D) (AffineLowOrderLDCoordinate D) ℝ :=
  LinearMap.toMatrix' lowOrderLDHProjectionLinearMap

/-- Applying the `H` projection matrix is exact coordinate selection. -/
theorem lowOrderLDHProjection_mulVec {D : ℕ}
    (state : AffineLowOrderLDCoordinate D → ℝ) :
    (lowOrderLDHProjection D).mulVec state = lowOrderLDHProjectionLinearMap state := by
  exact LinearMap.toMatrix'_mulVec _ _

/-- Joint moment table represented by one column of the augmented low-order system. -/
def lowOrderLDAffineColumnMoment {D : ℕ}
    (column : AffineLowOrderLDCoordinate D) : LowOrderLDCoordinate D → ℝ :=
  match column with
  | none => fun _ ↦ 0
  | some coordinate => lowOrderLDBasis coordinate

/-- Constant coefficient represented by one augmented low-order column. -/
def lowOrderLDAffineColumnConstant {D : ℕ}
    (column : AffineLowOrderLDCoordinate D) : ℝ :=
  match column with
  | none => 1
  | some _ => 0

/-- A projection entry at `H(i,j)` is the `H(i,j)` value of the represented joint basis. -/
theorem lowOrderLDHProjection_apply {D : ℕ} (first second : Fin D)
    (column : AffineLowOrderLDCoordinate D) :
    lowOrderLDHProjection D (some (first, second)) column =
      lowOrderLDAffineColumnMoment column (.H first second) := by
  cases column <;>
    simp [lowOrderLDHProjection, lowOrderLDHProjectionLinearMap,
      lowOrderLDAffineColumnMoment, lowOrderLDBasis]

/-- The `H` projection passes the augmented constant coordinate. -/
theorem lowOrderLDHProjection_none {D : ℕ}
    (column : AffineLowOrderLDCoordinate D) :
    lowOrderLDHProjection D none column = lowOrderLDAffineColumnConstant column := by
  cases column <;>
    simp [lowOrderLDHProjection, lowOrderLDHProjectionLinearMap,
      lowOrderLDAffineColumnConstant]

/-- The full joint generator and its closed `H` subsystem commute exactly. -/
theorem lowOrderLDHProjection_generator_intertwines {D : ℕ}
    (rates : ManyDemeLDRates D) :
    lowOrderLDHProjection D * augmentedLowOrderLDGenerator rates =
      augmentedPairDivergenceGenerator rates.coalescence rates.migration rates.mutation *
        lowOrderLDHProjection D := by
  apply Matrix.ext
  intro row column
  change (lowOrderLDHProjection D).mulVec
      (fun source ↦ augmentedLowOrderLDGenerator rates source column) row =
    (augmentedPairDivergenceGenerator rates.coalescence rates.migration
      rates.mutation).mulVec (fun target ↦ lowOrderLDHProjection D target column) row
  rw [lowOrderLDHProjection_mulVec, augmentedPairDivergenceGenerator_mulVec]
  cases row with
  | none =>
      simp [lowOrderLDHProjectionLinearMap, pairDivergenceGeneratorLinearMap,
        augmentedLowOrderLDGenerator]
  | some pair =>
      rcases pair with ⟨first, second⟩
      change augmentedLowOrderLDGenerator rates (some (.H first second)) column =
        symmetricPairDivergenceAffineDerivative rates.coalescence rates.migration
          rates.mutation
          (fun source target ↦ lowOrderLDHProjection D (some (source, target)) column)
          (lowOrderLDHProjection D none column) first second
      rw [lowOrderLDHProjection_none]
      simp_rw [lowOrderLDHProjection_apply]
      cases column with
      | none =>
          have hzero : lowOrderLDHomogeneousGenerator rates (fun _ ↦ 0)
              (.H first second) = 0 := by
            simp [lowOrderLDHomogeneousGenerator, lowOrderLDDrift,
              lowOrderLDMigration, lowOrderLDRecombination,
              lowOrderLDMutationCoupling, lowOrderLDRecurrentMutationDamping]
          simpa [augmentedLowOrderLDGenerator, lowOrderLDAffineColumnMoment,
            lowOrderLDAffineColumnConstant, hzero] using
              lowOrderLDAffine_H_eq_symmetricPairDivergence_affine rates (fun _ ↦ 0)
                1 first second
      | some column =>
          simpa [augmentedLowOrderLDGenerator, lowOrderLDAffineColumnMoment,
            lowOrderLDAffineColumnConstant] using
            lowOrderLDAffine_H_eq_symmetricPairDivergence_affine rates
              (lowOrderLDBasis column) 0 first second

/-- The full joint epoch and the closed `H` epoch commute through their exact matrix
exponentials. -/
theorem lowOrderLDHProjection_propagator_intertwines {D : ℕ}
    (rates : ManyDemeLDRates D) (duration : ℝ) :
    lowOrderLDHProjection D * matrixExponential (augmentedLowOrderLDGenerator rates) duration =
      matrixExponential
          (augmentedPairDivergenceGenerator rates.coalescence rates.migration rates.mutation)
          duration * lowOrderLDHProjection D := by
  exact matrixExponential_intertwines _ _ _
    (lowOrderLDHProjection_generator_intertwines rates) duration

/-- Positive denominator of the recurrent-biallelic one-deme stationary `DD/Dz/pi2` solve.
It is written as an expanded positive polynomial so the physical rate domain excludes a
Cramer pole without appealing to a numerical determinant. -/
noncomputable def oneDemeLDStationaryDenominator (rates : ManyDemeLDRates 1) : ℝ :=
  let c := rates.coalescence 0
  let theta := rates.mutation 0
  let rho := rates.recombination 0
  18 * c ^ 3 + 13 * c ^ 2 * rho + 108 * c ^ 2 * theta + c * rho ^ 2 +
    38 * c * theta * rho + 160 * c * theta ^ 2 + 2 * theta * rho ^ 2 +
    24 * theta ^ 2 * rho + 64 * theta ^ 3

/-- The one-deme stationary denominator cannot hit a Cramer pole on the physical rate
domain. -/
theorem oneDemeLDStationaryDenominator_pos (rates : ManyDemeLDRates 1) :
    0 < oneDemeLDStationaryDenominator rates := by
  unfold oneDemeLDStationaryDenominator
  have hc := rates.coalescence_pos 0
  have ht := rates.mutation_nonneg 0
  have hr := rates.recombination_nonneg 0
  positivity

/-- Closed stationary solution of the four recurrent-biallelic one-deme equations.  Writing
`c = 1/(2N)`, `theta = 2u`, and `rho = 2r`, the solution is

`H = theta/(c+2theta)`,
`DD = c theta²(10c+rho+8theta)/(4(c+2theta)Q)`,
`Dz = 2c²theta²/((c+2theta)Q)`, and
`pi2 = c³theta²/((c+2theta)²Q) + theta²/(4(c+2theta)²)`,

where `Q = oneDemeLDStationaryDenominator`.  As `theta → 0`, the leading `theta²`
coefficients reduce to the former infinite-sites boundary, but this expression also retains
the return-mutation terms required by the biallelic ascertainment law.

Thus the ancestral boundary has no fitted moment table and no unchecked determinant. -/
noncomputable def oneDemeStationaryLowOrderLDState (rates : ManyDemeLDRates 1) :
    AffineLowOrderLDCoordinate 1 → ℝ
  | none => 1
  | some (.H _ _) =>
      rates.mutation 0 / (rates.coalescence 0 + 2 * rates.mutation 0)
  | some (.DD _ _) =>
      rates.coalescence 0 * rates.mutation 0 ^ 2 *
        (10 * rates.coalescence 0 + rates.recombination 0 + 8 * rates.mutation 0) /
      (4 * (rates.coalescence 0 + 2 * rates.mutation 0) *
        oneDemeLDStationaryDenominator rates)
  | some (.Dz _ _ _) =>
      2 * rates.coalescence 0 ^ 2 * rates.mutation 0 ^ 2 /
        ((rates.coalescence 0 + 2 * rates.mutation 0) *
          oneDemeLDStationaryDenominator rates)
  | some (.pi2 _ _ _ _) =>
      rates.coalescence 0 ^ 3 * rates.mutation 0 ^ 2 /
          ((rates.coalescence 0 + 2 * rates.mutation 0) ^ 2 *
            oneDemeLDStationaryDenominator rates) +
        rates.mutation 0 ^ 2 /
          (4 * (rates.coalescence 0 + 2 * rates.mutation 0) ^ 2)

/-- The closed ancestral values solve all four stationary generator equations. -/
theorem oneDemeStationaryLowOrderLDState_equations (rates : ManyDemeLDRates 1) :
    let state := oneDemeStationaryLowOrderLDState rates
    let c := rates.coalescence 0
    let theta := rates.mutation 0
    let rho := rates.recombination 0
    theta - (c + 2 * theta) * state (some (.H 0 0)) = 0 ∧
      -(3 * c + rho + 4 * theta) * state (some (.DD 0 0)) +
          c * state (some (.Dz 0 0 0)) + c * state (some (.pi2 0 0 0 0)) = 0 ∧
      4 * c * state (some (.DD 0 0)) -
          (5 * c + rho / 2 + 4 * theta) * state (some (.Dz 0 0 0)) = 0 ∧
      c * state (some (.Dz 0 0 0)) - (2 * c + 4 * theta) *
          state (some (.pi2 0 0 0 0)) +
          theta / 2 * state (some (.H 0 0)) = 0 := by
  have hscale : rates.coalescence 0 + 2 * rates.mutation 0 ≠ 0 := by
    have hc := rates.coalescence_pos 0
    have ht := rates.mutation_nonneg 0
    positivity
  have hden : oneDemeLDStationaryDenominator rates ≠ 0 :=
    ne_of_gt (oneDemeLDStationaryDenominator_pos rates)
  have hscale_comm : rates.mutation 0 * 2 + rates.coalescence 0 ≠ 0 := by
    convert hscale using 1 <;> ring
  have hscale_nf : rates.coalescence 0 + rates.mutation 0 * 2 ≠ 0 := by
    convert hscale using 1 <;> ring
  have hscale_sq :
      rates.coalescence 0 * rates.mutation 0 * 4 + rates.coalescence 0 ^ 2 +
          rates.mutation 0 ^ 2 * 4 ≠ 0 := by
    convert pow_ne_zero 2 hscale using 1 <;> ring
  have hden_comm :
      rates.coalescence 0 * rates.mutation 0 * rates.recombination 0 * 38 +
              rates.coalescence 0 * rates.mutation 0 ^ 2 * 160 +
            rates.coalescence 0 * rates.recombination 0 ^ 2 +
          rates.coalescence 0 ^ 2 * rates.mutation 0 * 108 +
        rates.coalescence 0 ^ 2 * rates.recombination 0 * 13 +
      rates.coalescence 0 ^ 3 * 18 + rates.mutation 0 * rates.recombination 0 ^ 2 * 2 +
        rates.mutation 0 ^ 2 * rates.recombination 0 * 24 +
          rates.mutation 0 ^ 3 * 64 ≠ 0 := by
    convert hden using 1 <;> unfold oneDemeLDStationaryDenominator <;> ring
  dsimp [oneDemeStationaryLowOrderLDState, oneDemeLDStationaryDenominator]
  constructor
  · field_simp [hscale, hscale_comm, hscale_nf] <;> ring
  constructor
  · field_simp [hscale, hscale_comm, hscale_nf, hscale_sq, hden, hden_comm]
    have hQcancel := mul_inv_cancel₀ hden_comm
    linear_combination
      -(rates.coalescence 0 * rates.mutation 0 ^ 2) * hQcancel
  constructor
  · field_simp [hscale, hscale_comm, hscale_nf, hscale_sq, hden, hden_comm] <;>
      field_simp [hden, hden_comm] <;> ring
  · field_simp [hscale, hscale_comm, hscale_nf, hscale_sq, hden, hden_comm] <;>
      field_simp [hden, hden_comm] <;> ring

/-- Positive recurrent mutation makes the ancestral within-deme `DD = E[D²]` strictly
positive.  This is the nondegenerate base case for the downstream normalized correlation. -/
theorem oneDemeStationaryLowOrderLDState_DD_pos (rates : ManyDemeLDRates 1)
    (mutation_pos : 0 < rates.mutation 0) :
    0 < oneDemeStationaryLowOrderLDState rates (some (.DD 0 0)) := by
  unfold oneDemeStationaryLowOrderLDState
  have hc := rates.coalescence_pos 0
  have hr := rates.recombination_nonneg 0
  have hden := oneDemeLDStationaryDenominator_pos rates
  positivity

/-- The stationary ancestral `DD` is nonnegative even on the zero-mutation boundary. -/
theorem oneDemeStationaryLowOrderLDState_DD_nonneg (rates : ManyDemeLDRates 1) :
    0 ≤ oneDemeStationaryLowOrderLDState rates (some (.DD 0 0)) := by
  unfold oneDemeStationaryLowOrderLDState
  have hc := rates.coalescence_pos 0
  have ht := rates.mutation_nonneg 0
  have hr := rates.recombination_nonneg 0
  have hden := oneDemeLDStationaryDenominator_pos rates
  positivity

/-- Collapse an arbitrary-deme coordinate to the unique coordinate of a single common
ancestral deme. -/
def LowOrderLDCoordinate.collapseToOneDeme {D : ℕ} :
    LowOrderLDCoordinate D → LowOrderLDCoordinate 1
  | .H _ _ => .H 0 0
  | .DD _ _ => .DD 0 0
  | .Dz _ _ _ => .Dz 0 0 0
  | .pi2 _ _ _ _ => .pi2 0 0 0 0

/-- Lift a derived one-deme equilibrium state to the instant before the first split, where
all descendant labels denote the same ancestral population. -/
noncomputable def commonAncestralLowOrderLDState {D : ℕ}
    (ancestralRates : ManyDemeLDRates 1) : AffineLowOrderLDCoordinate D → ℝ
  | none => 1
  | some coordinate =>
      oneDemeStationaryLowOrderLDState ancestralRates (some coordinate.collapseToOneDeme)

/-- Selecting the ancestral `H` subsystem yields one normalized affine coordinate and the
same one-deme stationary heterozygosity for every ordered descendant pair. -/
theorem lowOrderLDHProjection_commonAncestral {D : ℕ}
    (ancestralRates : ManyDemeLDRates 1) :
    (lowOrderLDHProjection D).mulVec (commonAncestralLowOrderLDState ancestralRates) =
      fun coordinate ↦ match coordinate with
        | none => 1
        | some _ => oneDemeStationaryLowOrderLDState ancestralRates (some (.H 0 0)) := by
  rw [lowOrderLDHProjection_mulVec]
  funext coordinate
  cases coordinate with
  | none => rfl
  | some pair =>
      rcases pair with ⟨first, second⟩
      rfl

/-- Every ancestral `DD(i,j)` is the same positive one-deme second moment when recurrent
mutation is positive. -/
theorem commonAncestralLowOrderLDState_DD_pos {D : ℕ}
    (ancestralRates : ManyDemeLDRates 1) (mutation_pos : 0 < ancestralRates.mutation 0)
    (first second : Fin D) :
    0 < commonAncestralLowOrderLDState ancestralRates (some (.DD first second)) := by
  exact oneDemeStationaryLowOrderLDState_DD_pos ancestralRates mutation_pos

/-- The entire unsplit ancestral `DD` block has one explicit Gram realization: every deme
label reads the same constant linkage observable whose square is the stationary `DD` value.
This includes the zero-mutation boundary, where that observable is zero. -/
noncomputable def commonAncestralLowOrderLDDDRealization {D : ℕ}
    (ancestralRates : ManyDemeLDRates 1) :
    LowOrderLDDDRealization (commonAncestralLowOrderLDState (D := D) ancestralRates) where
  sampleSpace := Unit
  expectation := Foundations.ExpFunctional.evalAt ()
  linkage := fun _ _ ↦
    Real.sqrt (oneDemeStationaryLowOrderLDState ancestralRates (some (.DD 0 0)))
  dd_eq := by
    intro first second
    change oneDemeStationaryLowOrderLDState ancestralRates (some (.DD 0 0)) =
      Real.sqrt (oneDemeStationaryLowOrderLDState ancestralRates (some (.DD 0 0))) *
        Real.sqrt (oneDemeStationaryLowOrderLDState ancestralRates (some (.DD 0 0)))
    rw [← pow_two, Real.sq_sqrt (oneDemeStationaryLowOrderLDState_DD_nonneg ancestralRates)]

/-- The ancestral `DD` kernel saturates Cauchy--Schwarz because every descendant label still
denotes the same unsplit population. -/
theorem commonAncestralLowOrderLDState_DD_cauchySchwarz {D : ℕ}
    (ancestralRates : ManyDemeLDRates 1) (first second : Fin D) :
    commonAncestralLowOrderLDState ancestralRates (some (.DD first second)) ^ 2 ≤
      commonAncestralLowOrderLDState ancestralRates (some (.DD first first)) *
        commonAncestralLowOrderLDState ancestralRates (some (.DD second second)) := by
  exact (commonAncestralLowOrderLDDDRealization (D := D) ancestralRates).dd_cauchySchwarz
    first second

/-- One piecewise-constant epoch of a derived low-order two-locus moment system. -/
structure LowOrderLDEpoch (D : ℕ) where
  generator : Matrix (AffineLowOrderLDCoordinate D) (AffineLowOrderLDCoordinate D) ℝ
  duration : ℝ
  duration_nonneg : 0 ≤ duration
  constant_row : ∀ coordinate, generator none coordinate = 0

/-- Build an epoch directly from the derived arbitrary-deme rate law. -/
noncomputable def ManyDemeLDRates.epoch {D : ℕ} (rates : ManyDemeLDRates D)
    (duration : ℝ) (duration_nonneg : 0 ≤ duration) : LowOrderLDEpoch D where
  generator := augmentedLowOrderLDGenerator rates
  duration := duration
  duration_nonneg := duration_nonneg
  constant_row := fun _ ↦ rfl

/-- The exactly evaluable semigroup of one epoch. -/
noncomputable def LowOrderLDEpoch.propagator {D : ℕ} (epoch : LowOrderLDEpoch D) :
    Matrix (AffineLowOrderLDCoordinate D) (AffineLowOrderLDCoordinate D) ℝ :=
  matrixExponential epoch.generator epoch.duration

/-- The homogeneous affine coordinate remains exactly constant through every joint epoch. -/
theorem LowOrderLDEpoch.propagator_none {D : ℕ} (epoch : LowOrderLDEpoch D)
    (state : AffineLowOrderLDCoordinate D → ℝ) :
    epoch.propagator.mulVec state none = state none := by
  apply matrixExponential_mulVec_apply_of_row_zero
  intro column
  exact epoch.constant_row column

/-- A demographic instruction is continuous evolution or a derived instantaneous linear map.
Splits, pulses, and admixture events are instances of `instantaneous`; none is replaced by a
scalar retention coefficient. -/
inductive LowOrderLDInstruction (D : ℕ) where
  | evolve (epoch : LowOrderLDEpoch D)
  | instantaneous
      (transform : Matrix (AffineLowOrderLDCoordinate D) (AffineLowOrderLDCoordinate D) ℝ)

/-- Replace every occurrence of a newly created child label by its parent label. -/
def LowOrderLDCoordinate.mergeSplit {D : ℕ} (parent child : Fin D) :
    LowOrderLDCoordinate D → LowOrderLDCoordinate D
  | .H first second => .H (if first = child then parent else first)
      (if second = child then parent else second)
  | .DD first second => .DD (if first = child then parent else first)
      (if second = child then parent else second)
  | .Dz first second third => .Dz (if first = child then parent else first)
      (if second = child then parent else second) (if third = child then parent else third)
  | .pi2 first second third fourth =>
      .pi2 (if first = child then parent else first)
        (if second = child then parent else second)
        (if third = child then parent else third)
        (if fourth = child then parent else fourth)

/-- Exact instantaneous split matrix: immediately after a split the child's haplotype
frequencies equal the parent's, so every new coordinate pulls back by label replacement. -/
def lowOrderLDSplitTransform {D : ℕ} (parent child : Fin D) :
    Matrix (AffineLowOrderLDCoordinate D) (AffineLowOrderLDCoordinate D) ℝ
  | none, none => 1
  | some row, some column => if row.mergeSplit parent child = column then 1 else 0
  | _, _ => 0

/-- Multiplying by the split matrix is exactly coordinate relabeling.  This eliminates the
instantaneous-event half of any projection proof: there is no averaging or closure hidden in
a split, only replacement of every child label by its parent. -/
theorem lowOrderLDSplitTransform_mulVec {D : ℕ} (parent child : Fin D)
    (state : AffineLowOrderLDCoordinate D → ℝ) :
    (lowOrderLDSplitTransform parent child).mulVec state =
      fun coordinate ↦ match coordinate with
        | none => state none
        | some row => state (some (row.mergeSplit parent child)) := by
  funext coordinate
  cases coordinate with
  | none =>
      simp [Matrix.mulVec, dotProduct, lowOrderLDSplitTransform]
  | some row =>
      simp [Matrix.mulVec, dotProduct, lowOrderLDSplitTransform]

/-- Deterministic population splitting preserves one common Gram realization of the entire
`DD` block: the child's linkage observable is exactly the parent's pre-split observable and
every other observable is unchanged. -/
noncomputable def LowOrderLDDDRealization.split {D : ℕ}
    {state : AffineLowOrderLDCoordinate D → ℝ}
    (realization : LowOrderLDDDRealization state) (parent child : Fin D) :
    LowOrderLDDDRealization ((lowOrderLDSplitTransform parent child).mulVec state) where
  sampleSpace := realization.sampleSpace
  expectation := realization.expectation
  linkage := fun outcome deme ↦
    realization.linkage outcome (if deme = child then parent else deme)
  dd_eq := by
    intro first second
    rw [lowOrderLDSplitTransform_mulVec]
    change state (some (.DD (if first = child then parent else first)
      (if second = child then parent else second))) = _
    exact realization.dd_eq _ _

/-- A deterministic split preserves the full haplotype semantic cone, not only its `DD`
projection: every coordinate is obtained by replacing the child haplotype-frequency random
variable with the parent's random variable. -/
noncomputable def LowOrderLDHaplotypeRealization.split {D : ℕ}
    {state : AffineLowOrderLDCoordinate D → ℝ}
    (realization : LowOrderLDHaplotypeRealization state) (parent child : Fin D) :
    LowOrderLDHaplotypeRealization
      ((lowOrderLDSplitTransform parent child).mulVec state) where
  sampleSpace := realization.sampleSpace
  expectation := realization.expectation
  haplotype := fun outcome deme ↦
    realization.haplotype outcome (if deme = child then parent else deme)
  constant_eq := by
    rw [lowOrderLDSplitTransform_mulVec]
    exact realization.constant_eq
  H_eq := by
    intro first second
    rw [lowOrderLDSplitTransform_mulVec]
    change state (some (.H (if first = child then parent else first)
      (if second = child then parent else second))) = _
    exact realization.H_eq _ _
  DD_eq := by
    intro first second
    rw [lowOrderLDSplitTransform_mulVec]
    change state (some (.DD (if first = child then parent else first)
      (if second = child then parent else second))) = _
    exact realization.DD_eq _ _
  Dz_eq := by
    intro first second third
    rw [lowOrderLDSplitTransform_mulVec]
    change state (some (.Dz (if first = child then parent else first)
      (if second = child then parent else second)
      (if third = child then parent else third))) = _
    exact realization.Dz_eq _ _ _
  pi2_eq := by
    intro first second third fourth
    rw [lowOrderLDSplitTransform_mulVec]
    change state (some (.pi2 (if first = child then parent else first)
      (if second = child then parent else second)
      (if third = child then parent else third)
      (if fourth = child then parent else fourth))) = _
    exact realization.pi2_eq _ _ _ _

/-- The exact split transform preserves the joint state's affine constant. -/
theorem lowOrderLDSplitTransform_none {D : ℕ} (parent child : Fin D)
    (state : AffineLowOrderLDCoordinate D → ℝ) :
    (lowOrderLDSplitTransform parent child).mulVec state none = state none := by
  rw [lowOrderLDSplitTransform_mulVec]

/-- The instantaneous split map on the full joint state commutes exactly with selection of
the closed `H` subsystem.  The affine coordinate is fixed at one on reachable states, while
every deme label in `H(i,j)` is pulled back through the same child-to-parent relabeling as the
one-locus pair-divergence state. -/
theorem lowOrderLDHProjection_split {D : ℕ} (parent child : Fin D)
    (state : AffineLowOrderLDCoordinate D → ℝ) (hconstant : state none = 1) :
    (lowOrderLDHProjection D).mulVec
        ((lowOrderLDSplitTransform parent child).mulVec state) =
      splitPairDivergenceState parent child
        ((lowOrderLDHProjection D).mulVec state) := by
  rw [lowOrderLDSplitTransform_mulVec, lowOrderLDHProjection_mulVec,
    lowOrderLDHProjection_mulVec]
  funext coordinate
  cases coordinate with
  | none =>
      simp [lowOrderLDHProjectionLinearMap, splitPairDivergenceState, hconstant]
  | some pair =>
      rcases pair with ⟨first, second⟩
      simp [lowOrderLDHProjectionLinearMap, splitPairDivergenceState,
        LowOrderLDCoordinate.mergeSplit, mergeSplitDemeLabel]

/-- Concrete split instruction for the arbitrary-deme history compiler. -/
def LowOrderLDInstruction.split {D : ℕ} (parent child : Fin D) :
    LowOrderLDInstruction D :=
  .instantaneous (lowOrderLDSplitTransform parent child)

/-- Apply one exact demographic instruction to the full joint moment state. -/
noncomputable def LowOrderLDInstruction.apply {D : ℕ}
    (instruction : LowOrderLDInstruction D)
    (state : AffineLowOrderLDCoordinate D → ℝ) :
    AffineLowOrderLDCoordinate D → ℝ :=
  match instruction with
  | .evolve epoch => epoch.propagator.mulVec state
  | .instantaneous transform => transform.mulVec state

/-- Ordered operator composition for an arbitrary piecewise demographic history. -/
noncomputable def propagateLowOrderLDInstructions {D : ℕ}
    (instructions : List (LowOrderLDInstruction D))
    (initial : AffineLowOrderLDCoordinate D → ℝ) :
    AffineLowOrderLDCoordinate D → ℝ :=
  instructions.foldl (fun state instruction ↦ instruction.apply state) initial

/-- Exact history composition is operator composition on the full joint state.  This is the
chain law: a suffix acts on the complete state returned by its prefix, not on the prefix's
single `DD` correlation. -/
theorem propagateLowOrderLDInstructions_append {D : ℕ}
    (front rest : List (LowOrderLDInstruction D))
    (initial : AffineLowOrderLDCoordinate D → ℝ) :
    propagateLowOrderLDInstructions (front ++ rest) initial =
      propagateLowOrderLDInstructions rest
        (propagateLowOrderLDInstructions front initial) := by
  simp [propagateLowOrderLDInstructions, List.foldl_append]

/-- A fully derived low-order history consists of its ancestral joint moments and its ordered
demographic operators.  This is the precise interface the arbitrary-deme generator must
construct from the visible history. -/
structure LowOrderLDHistory (D : ℕ) where
  initial : AffineLowOrderLDCoordinate D → ℝ
  initial_constant : initial none = 1
  instructions : List (LowOrderLDInstruction D)

/-- Present-day state after the complete ordered operator product. -/
noncomputable def LowOrderLDHistory.present {D : ℕ} (history : LowOrderLDHistory D) :
    AffineLowOrderLDCoordinate D → ℝ :=
  propagateLowOrderLDInstructions history.instructions history.initial

/-- Read the exact `H`, `DD`, `Dz`, and `pi2` family expected by portability consumers from
one composed history. -/
noncomputable def LowOrderLDHistory.toDemographicTwoLocusMoments {D : ℕ}
    (historyAt : MarkerSeparationBp → LowOrderLDHistory D) :
    DemographicTwoLocusMoments D where
  H := fun rho first second ↦ (historyAt rho).present (some (.H first second))
  DD := fun rho first second ↦ (historyAt rho).present (some (.DD first second))
  Dz := fun rho first second third ↦ (historyAt rho).present (some (.Dz first second third))
  pi2 := fun rho first second third fourth ↦
    (historyAt rho).present (some (.pi2 first second third fourth))

/-- The bridge this module exists to supply, stated as a theorem so the two vocabularies are
tied where a contradiction could land: the `DemographicTwoLocusMoments` cross-deme `DD` entry
read at a `MarkerSeparationBp` is literally the composed history's present `DD` joint
moment, with no closure approximation between the two. -/
theorem LowOrderLDHistory.toDemographicTwoLocusMoments_DD {D : ℕ}
    (historyAt : MarkerSeparationBp → LowOrderLDHistory D)
    (rho : MarkerSeparationBp) (first second : Fin D) :
    DemographicTwoLocusMoments.DD (LowOrderLDHistory.toDemographicTwoLocusMoments historyAt)
        rho first second =
    (historyAt rho).present (some (.DD first second)) :=
  rfl

/-- A common Gram realization of the composed present state supplies the exact
`LDPairDomain` consumed by the normalized portability law.  Only strict positivity of the
two normalization diagonals remains separate; Cauchy--Schwarz is derived from the witness. -/
def LowOrderLDDDRealization.toLDPairDomain {D : ℕ}
    (historyAt : MarkerSeparationBp → LowOrderLDHistory D)
    (rho : MarkerSeparationBp) (first second : Fin D)
    (realization : LowOrderLDDDRealization (historyAt rho).present)
    (first_pos : 0 < (historyAt rho).present (some (.DD first first)))
    (second_pos : 0 < (historyAt rho).present (some (.DD second second))) :
    (LowOrderLDHistory.toDemographicTwoLocusMoments historyAt).LDPairDomain
      rho first second where
  firstWithin_pos := first_pos
  secondWithin_pos := second_pos
  cross_sq_le := realization.dd_cauchySchwarz first second

/-- A full haplotype realization reaches the portability domain through its derived Gram
witness; no pairwise linkage inequality is supplied independently. -/
def LowOrderLDHaplotypeRealization.toLDPairDomain {D : ℕ}
    (historyAt : MarkerSeparationBp → LowOrderLDHistory D)
    (rho : MarkerSeparationBp) (first second : Fin D)
    (realization : LowOrderLDHaplotypeRealization (historyAt rho).present)
    (first_pos : 0 < (historyAt rho).present (some (.DD first first)))
    (second_pos : 0 < (historyAt rho).present (some (.DD second second))) :
    (LowOrderLDHistory.toDemographicTwoLocusMoments historyAt).LDPairDomain
      rho first second :=
  realization.toDDDRealization.toLDPairDomain historyAt rho first second first_pos second_pos

/-- The same interface exposes the marginal heterozygosity coordinate carried inside the
joint operator.  This is the coordinate that an eventual intertwining theorem identifies
with the independently propagated one-locus divergence moment. -/
theorem LowOrderLDHistory.toDemographicTwoLocusMoments_H {D : ℕ}
    (historyAt : MarkerSeparationBp → LowOrderLDHistory D)
    (rho : MarkerSeparationBp) (first second : Fin D) :
    DemographicTwoLocusMoments.H (LowOrderLDHistory.toDemographicTwoLocusMoments historyAt)
        rho first second =
      (historyAt rho).present (some (.H first second)) :=
  rfl

end Descent.Coalescent
