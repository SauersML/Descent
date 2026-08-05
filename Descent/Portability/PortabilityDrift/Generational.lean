/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Program.Conclusions
import Descent.PopGen.DGP
import Descent.Spectral.CirculationDefect
import Descent.Core.Fst
import Descent.Core.Parameters
import Descent.Core.Moments
import Descent.Portability.PortabilityDrift.PresentDayMetrics

namespace Descent.Portability

open MeasureTheory

open PopGen.TransportedMetrics (r2FromSignalVariance r2FromSignalVariance_eq_rsquared
  equalVarianceGaussianAUCFromSignalVariance
  equalVarianceGaussianAUCFromSignalVariance_eq_formula_of_ne_noise)

/-!
# `PortabilityDrift.Generational`

Part of the split of `Portability/PortabilityDrift.lean`, which was 9,208 lines and 555
declarations -- the largest file in the corpus by both measures, and large enough that
nothing in it could be read without reading past most of it.

The parts are a CHAIN: each imports the one before, in the order the original was written.
That is the conservative choice, deliberately. A monolith's declarations depend on each
other in whatever order they happen to appear, and cutting it into modules that import only
what they use means discovering that order first -- worth doing, and not what this does.
The chain preserves every resolution the single file had, so the split cannot change what
any proof sees.

Sections are reopened and reclosed by name where a cut falls inside one: the original
opened `section PortabilityDrift` and closed it 8,000 lines later. A section scopes
`variable`s, and this file declares none at that level, so the reopening is exact.
-/

-- These are METHODS on `Descent.Core.PopGenParameters`, added by this module.  A
-- declaration's namespace is relative to the enclosing one, so `namespace
-- Core.PopGenParameters` from inside `Descent.Portability` named them
-- `Descent.Portability.Core.PopGenParameters.*` and dot notation on the structure
-- stopped finding them -- `g.tauAt` among others.  Rooting each declaration says
-- where it goes without closing the directory namespace around a nested section.


/-- Coalescent time coordinate at generation `t`.

    Empirical status: **VALIDATED, through a composition rather than on
    its own** (`validation/empirical/simcov/battery_bulk16.py` and
    `battery_bulk16b.py`). The composition asserts
    `exp(-theta * tau) = exp(-4 Ne mu * t/(2 Ne)) = exp(-2 mu t)`: the chance
    that NEITHER lineage of a sampled pair has mutated in `t` generations. `Ne`
    cancels, and that cancellation is the content worth testing, because a
    scaled parameter composed with a scaled time is exactly where this branch
    has already found factor errors. Measured as the fraction of 400000
    replicate lineage pairs carrying no mutation:

      Ne     mu        t      theta*tau   predicted  measured             sems
      250    1.0e-3    125     0.25        0.77880   0.77779 ± 0.00066    1.54
      500    1.0e-3    250     0.50        0.60653   0.60722 ± 0.00077    0.90
      2000   2.5e-4    1000    0.50        0.60653   0.60617 ± 0.00077    0.47
      500    2.0e-3    500     2.00        0.13534   0.13525 ± 0.00054    0.17
      1000   5.0e-4    2000    2.00        0.13534   0.13598 ± 0.00054    1.18
      250    4.0e-3    250     2.00        0.13534   0.13448 ± 0.00054    1.59

    `theta * tau` runs over a factor of eight while `Ne` independently runs over
    a factor of eight, so the functional form and the cancellation are under
    test at once. The three rows at `theta*tau = 2.00` carry `Ne` of 250, 500
    and 1000 and agree to 0.6%: `Ne` really does drop out.

    The competing one-lineage reading `exp(-mu t)` is carried through the same
    measurement and misses by up to 433 sems and 174% relative, so the factor of
    two in "two lineages" is chosen by the data rather than argued.

    An earlier version of this design held `theta * tau = 1` in every cell so
    that the cancellation would be visible, and the verdict gate called NO POWER
    on it -- correctly, since a prediction that never moves cannot reject a
    wrong functional form no matter what else the design shows. The numbers
    above are from the redone design.

    A time SCALE has no empirical content in isolation: `t/(2 Ne)` can only be
    checked against something that consumes it, and the table above is the
    check. Halving or doubling this factor moves `exp(-theta * tau)` from 0.135
    to 0.368 or 0.018 in the bottom rows, which the measurement excludes by
    hundreds of sems. -/
noncomputable def _root_.Descent.Core.PopGenParameters.tauAt (g : Descent.Core.PopGenParameters) (t : ℕ) : ℝ :=
  (t : ℝ) / (2 * g.Ne)

/-- With a vanishing denominator Mathlib returns `0`, which is a value this quantity can also
take legitimately, so the branch is named rather than left to be inferred from the result. -/
theorem _root_.Descent.Core.PopGenParameters.tauAt_at_zero_denominator_is_junk (g : Descent.Core.PopGenParameters) (t : ℕ)
    (hzero : (2 * g.Ne) = 0) :
    Descent.Core.PopGenParameters.tauAt g t = 0 := by
  unfold Descent.Core.PopGenParameters.tauAt
  rw [hzero, div_zero]


/-- Per-generation heterozygosity retention factor under drift + mutation. -/
noncomputable def _root_.Descent.Core.PopGenParameters.hetDecayFactor (g : Descent.Core.PopGenParameters) : ℝ :=
  PopGen.hetDecayFromScaled g.Ne g.theta

/-- Transient differentiation after `t` generations. This is the same
discrete-time drift/mutation/migration coordinate used in the evolutionary
layer, but now exposed directly to the mechanistic SNP/LD state.

    **The decay base was `Descent.Core.PopGenParameters.hetDecayFactor` and has been corrected to
    `fstTransientDecayFromScaled`, which carries migration as well.** The level
    this coordinate settles at depends on the migration rate; the rate at which
    it got there did not, and that is not a possible process. Measured as a
    half-life, the superseded base overstates the time to half the plateau by a
    factor of seventeen at `4 Nₑ m = 16`.

    **The LEVEL now carries the two-deme correction as well**, and is
    `1/(1 + θ + 2 M)` rather than `1/(1 + θ + M)`. It is the same quantity as
    `DGP.fstEquilibrium`, spelled out here because this record cannot reach an
    `EvolutionaryParameters`, and it moved when that one did: the migration term
    carries `islandDemeCorrection`, which at the two populations this transport
    layer is about equals 2. The theorem
    `PGSEvolutionaryModel.toGenerationalPopGenParameters_fstTransientAt_floor`
    forces the two spellings to agree, and is what would have caught it had only
    one of them moved.

    The half-life design that validated the decay base does NOT bear on the
    level: it reads `F(t)` against `F(t)`'s own plateau by interpolation, which
    is a shape property with the level divided out. So the level correction is
    carried entirely by `fstEquilibrium`'s measurement and this record does not
    claim it twice.

    Note that `Descent.Core.PopGenParameters.hetDecayFactor` itself is untouched and remains correct for what
    it is: migration does not destroy heterozygosity, it relocates it. The error
    was in using a within-deme decay for a between-deme transient.

    Empirical status: **VALIDATED after correction; the superseded base
    FALSIFIED at up to 2222 sems**
    (`validation/empirical/simcov/battery_dis4.py`). The design and the
    table are recorded on `DGP.fstTransientDecayFromScaled`. Power: the
    half-life prediction spans 32.62 to 69.31 across the design where the
    superseded base spans 69.31 to 554.52. -/
noncomputable def _root_.Descent.Core.PopGenParameters.fstTransientAt (g : Descent.Core.PopGenParameters) (t : ℕ) : ℝ :=
  (1 / (1 + g.theta + 2 * g.bigM)) *
    (1 - PopGen.fstTransientDecayFromScaled g.Ne g.theta g.bigM ^ t)

/-- Mutation-driven retention of shared ancestral variation after `t`
generations.

    Empirical status: **VALIDATED** (`validation/empirical/simcov/battery_bulk16.py` and
    `battery_bulk16b.py`). The composition asserts
    `exp(-theta * tau) = exp(-4 Ne mu * t/(2 Ne)) = exp(-2 mu t)`: the chance
    that NEITHER lineage of a sampled pair has mutated in `t` generations. `Ne`
    cancels, and that cancellation is the content worth testing, because a
    scaled parameter composed with a scaled time is exactly where this branch
    has already found factor errors. Measured as the fraction of 400000
    replicate lineage pairs carrying no mutation:

      Ne     mu        t      theta*tau   predicted  measured             sems
      250    1.0e-3    125     0.25        0.77880   0.77779 ± 0.00066    1.54
      500    1.0e-3    250     0.50        0.60653   0.60722 ± 0.00077    0.90
      2000   2.5e-4    1000    0.50        0.60653   0.60617 ± 0.00077    0.47
      500    2.0e-3    500     2.00        0.13534   0.13525 ± 0.00054    0.17
      1000   5.0e-4    2000    2.00        0.13534   0.13598 ± 0.00054    1.18
      250    4.0e-3    250     2.00        0.13534   0.13448 ± 0.00054    1.59

    `theta * tau` runs over a factor of eight while `Ne` independently runs over
    a factor of eight, so the functional form and the cancellation are under
    test at once. The three rows at `theta*tau = 2.00` carry `Ne` of 250, 500
    and 1000 and agree to 0.6%: `Ne` really does drop out.

    The competing one-lineage reading `exp(-mu t)` is carried through the same
    measurement and misses by up to 433 sems and 174% relative, so the factor of
    two in "two lineages" is chosen by the data rather than argued.

    An earlier version of this design held `theta * tau = 1` in every cell so
    that the cancellation would be visible, and the verdict gate called NO POWER
    on it -- correctly, since a prediction that never moves cannot reject a
    wrong functional form no matter what else the design shows. The numbers
    above are from the redone design. -/
noncomputable def _root_.Descent.Core.PopGenParameters.mutationSharedRetentionAt
    (g : Descent.Core.PopGenParameters) (t : ℕ) : ℝ :=
  Real.exp (-g.theta * g.tauAt t)

/-- Migration-driven restoration of shared variation after `t` generations.

    Empirical status: **FALSIFIED in magnitude** (`simcov/battery_bulk55.py`).
    This is `DGP.migrationLDBoost` evaluated at generation `t`, and the same run
    falsifies both: the measured boost in cross-deme LD correlation from ongoing
    migration is roughly a third of what this factor claims, with the gap
    widening in both `τ` and `bigM`. At `τ = 1, bigM = 16` the body predicts a
    94% boost against a measured 32%, worst cell 18.17 sems.

    The direction is right -- no boost at all sits 11 sems away, and the
    measured value does rise with `t` and saturate in `bigM` as written. See
    `DGP.migrationLDBoost` for the table and for why the overstatement is
    expected: most LD sharing is inherited from before the split, so there is
    less for migration to restore than a model starting from zero assumes.

    REBUILT AND RE-RUN, and the numbers above are superseded by these. The
    battery this cites had never been committed: the verdict was real when it
    was produced and no reader could check it, which is the same standing as no
    verdict. `simcov/battery_bulk55.py` is now in the repository, was run against
    the design described above, and its results are committed beside it.
    FALSIFIED at worst 15.6 sems (62% relative) on the same run that falsifies
    `DGP.migrationLDBoost`, of which this is the generation-t reading.
    -/
noncomputable def _root_.Descent.Core.PopGenParameters.migrationSharedBoostAt
    (g : Descent.Core.PopGenParameters) (t : ℕ) : ℝ :=
  1 + g.bigM * g.tauAt t / (1 + g.bigM)

@[simp] theorem _root_.Descent.Core.PopGenParameters.tauAt_zero (g : Descent.Core.PopGenParameters) :
    g.tauAt 0 = 0 := by
  simp [Descent.Core.PopGenParameters.tauAt]

@[simp] theorem _root_.Descent.Core.PopGenParameters.fstTransientAt_zero (g : Descent.Core.PopGenParameters) :
    g.fstTransientAt 0 = 0 := by
  simp [Descent.Core.PopGenParameters.fstTransientAt, PopGen.fstTransientDecayFromScaled, PopGen.hetDecayFromScaled]

@[simp] theorem _root_.Descent.Core.PopGenParameters.mutationSharedRetentionAt_zero (g : Descent.Core.PopGenParameters) :
    g.mutationSharedRetentionAt 0 = 1 := by
  simp [Descent.Core.PopGenParameters.mutationSharedRetentionAt, Descent.Core.PopGenParameters.tauAt]

@[simp] theorem _root_.Descent.Core.PopGenParameters.migrationSharedBoostAt_zero (g : Descent.Core.PopGenParameters) :
    g.migrationSharedBoostAt 0 = 1 := by
  simp [Descent.Core.PopGenParameters.migrationSharedBoostAt, Descent.Core.PopGenParameters.tauAt, PopGen.EvolutionaryParameters.bigM]


/-- Exact bridge from the coarse DGP evolutionary block to the
generation-indexed population-genetic parameter block used by the mechanistic
transport model. This carries only the shared popgen primitives; the
SNP/LD-aware state still lives in `CrossPopulationGenerationalModel`. -/
noncomputable def _root_.Descent.PopGen.PGSEvolutionaryModel.toGenerationalPopGenParameters
    (m : PopGen.PGSEvolutionaryModel) : Descent.Core.PopGenParameters where
  Ne := m.Ne
  mu := m.mu
  mig := m.mig
  t_div := m.t_div
  recomb := m.recomb
  V_A := m.V_A
  Ne_pos := m.Ne_pos
  mu_nonneg := m.mu_nonneg
  mig_nonneg := m.mig_nonneg
  t_div_nonneg := m.t_div_nonneg
  recomb_nonneg := m.recomb_nonneg
  recomb_le_half := m.recomb_le_half
  V_A_pos := m.V_A_pos

@[simp] theorem _root_.Descent.PopGen.PGSEvolutionaryModel.toGenerationalPopGenParameters_theta
    (m : PopGen.PGSEvolutionaryModel) :
    (m.toGenerationalPopGenParameters).theta = m.theta := by
  simp [PopGen.PGSEvolutionaryModel.toGenerationalPopGenParameters,
    Descent.Core.PopGenParameters.theta, PopGen.EvolutionaryParameters.theta,
    PopGen.scaledMutationRate]

@[simp] theorem _root_.Descent.PopGen.PGSEvolutionaryModel.toGenerationalPopGenParameters_bigM
    (m : PopGen.PGSEvolutionaryModel) :
    (m.toGenerationalPopGenParameters).bigM = m.bigM := by
  simp [PopGen.PGSEvolutionaryModel.toGenerationalPopGenParameters,
    Descent.Core.PopGenParameters.bigM, PopGen.EvolutionaryParameters.bigM,
    PopGen.scaledMigrationRate]

@[simp] theorem _root_.Descent.PopGen.PGSEvolutionaryModel.toGenerationalPopGenParameters_hetDecayFactor
    (m : PopGen.PGSEvolutionaryModel) :
    (m.toGenerationalPopGenParameters).hetDecayFactor = m.hetDecayFactor := by
  unfold Descent.Core.PopGenParameters.hetDecayFactor PopGen.PGSEvolutionaryModel.hetDecayFactor
    PopGen.hetDecayFromScaled
  rw [PopGen.PGSEvolutionaryModel.toGenerationalPopGenParameters_theta]
  rfl

/-- The transient `F_ST` coordinate in the coarse DGP block agrees exactly with the generation-indexed popgen bridge at `⌊t_div⌋`, because both use the same
discrete differentiation recursion. Both were corrected together: an identity
between two coordinates survives a common wrong factor on both sides, so this
theorem constrained them jointly and could not have caught the decay base. -/
@[simp] theorem _root_.Descent.PopGen.PGSEvolutionaryModel.toGenerationalPopGenParameters_fstTransientAt_floor
    (m : PopGen.PGSEvolutionaryModel) :
    (m.toGenerationalPopGenParameters).fstTransientAt (Nat.floor m.t_div) =
      m.fstTransient := by
  unfold Descent.Core.PopGenParameters.fstTransientAt PopGen.PGSEvolutionaryModel.fstTransient
    PopGen.fstTransientDecayFromScaled PopGen.hetDecayFromScaled
  simp [PopGen.PGSEvolutionaryModel.toGenerationalPopGenParameters,
    -- BOTH bearers of the name: the record's own equilibrium and the
    -- `EvolutionaryParameters` one `PGSEvolutionaryModel` carries.  The flat
    -- namespace let one bare `fstEquilibrium` stand for whichever resolved, and
    -- the theorem needs the evolutionary one unfolded.
    Descent.Core.PopGenParameters.fstEquilibrium, PopGen.fstEquilibrium,
    Descent.Core.fstFromFlow,
    Descent.Core.PopGenParameters.theta, Descent.Core.PopGenParameters.bigM,
    PopGen.PGSEvolutionaryModel.toEvo, PopGen.EvolutionaryParameters.theta,
    PopGen.EvolutionaryParameters.bigM, PopGen.scaledMutationRate, PopGen.scaledMigrationRate,
    Descent.Core.scaledMutationRate, Descent.Core.scaledMigrationRate, Descent.Core.ploidy]
  exact Or.inl (by ring)

/-- When divergence time is an integer number of generations, the coarse
mutation-history coordinate agrees exactly with the generational popgen bridge
at that generation. -/
theorem _root_.Descent.PopGen.PGSEvolutionaryModel.toGenerationalPopGenParameters_mutationSharedRetentionAt_floor
    (m : PopGen.PGSEvolutionaryModel)
    (h_disc : m.t_div = (Nat.floor m.t_div : ℝ)) :
    (m.toGenerationalPopGenParameters).mutationSharedRetentionAt (Nat.floor m.t_div) =
      PopGen.mutationLDErosion m.toEvo := by
  unfold Descent.Core.PopGenParameters.mutationSharedRetentionAt
    PopGen.PGSEvolutionaryModel.toEvo PopGen.mutationLDErosion
  rw [PopGen.PGSEvolutionaryModel.toGenerationalPopGenParameters_theta]
  simp only [Descent.Core.PopGenParameters.tauAt,
    PopGen.PGSEvolutionaryModel.toGenerationalPopGenParameters,
    PopGen.EvolutionaryParameters.theta, PopGen.EvolutionaryParameters.tau]
  rw [h_disc, Nat.floor_natCast]

/-- When divergence time is an integer number of generations, the coarse
migration-history coordinate agrees exactly with the generational popgen bridge
at that generation. -/
theorem _root_.Descent.PopGen.PGSEvolutionaryModel.toGenerationalPopGenParameters_migrationSharedBoostAt_floor
    (m : PopGen.PGSEvolutionaryModel)
    (h_disc : m.t_div = (Nat.floor m.t_div : ℝ)) :
    (m.toGenerationalPopGenParameters).migrationSharedBoostAt (Nat.floor m.t_div) =
      PopGen.migrationLDBoost m.toEvo := by
  unfold Descent.Core.PopGenParameters.migrationSharedBoostAt
    PopGen.PGSEvolutionaryModel.toEvo PopGen.migrationLDBoost
  rw [PopGen.PGSEvolutionaryModel.toGenerationalPopGenParameters_bigM]
  simp only [Descent.Core.PopGenParameters.tauAt,
    PopGen.PGSEvolutionaryModel.toGenerationalPopGenParameters,
    PopGen.EvolutionaryParameters.bigM, PopGen.EvolutionaryParameters.tau]
  rw [h_disc, Nat.floor_natCast]

/-- Exact bridge from the DGP coordinate summary to the generational popgen
coordinates for the fields that genuinely match. The LD coordinate is
deliberately excluded here because the mechanistic model uses a joint
locus-specific kernel rather than a single global LD scalar. -/
theorem _root_.Descent.PopGen.PGSEvolutionaryModel.coordinateSummary_matches_generational_popgen_at_floor
    (m : PopGen.PGSEvolutionaryModel)
    (h_disc : m.t_div = (Nat.floor m.t_div : ℝ)) :
    m.coordinateSummary.alleleFreqCoordinate =
      1 - (m.toGenerationalPopGenParameters).fstTransientAt (Nat.floor m.t_div) ∧
    m.coordinateSummary.ancestralVariantCoordinate =
      (m.toGenerationalPopGenParameters).mutationSharedRetentionAt (Nat.floor m.t_div) ∧
    m.coordinateSummary.migrationCoordinate =
      (m.toGenerationalPopGenParameters).migrationSharedBoostAt (Nat.floor m.t_div) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [PopGen.PGSEvolutionaryModel.coordinateSummary_alleleFreqCoordinate]
    exact congrArg (fun x ↦ 1 - x)
      (PopGen.PGSEvolutionaryModel.toGenerationalPopGenParameters_fstTransientAt_floor m).symm
  · rw [PopGen.PGSEvolutionaryModel.coordinateSummary_ancestralVariantCoordinate]
    exact (PopGen.PGSEvolutionaryModel.toGenerationalPopGenParameters_mutationSharedRetentionAt_floor
      m h_disc).symm
  · rw [PopGen.PGSEvolutionaryModel.coordinateSummary_migrationCoordinate]
    exact (PopGen.PGSEvolutionaryModel.toGenerationalPopGenParameters_migrationSharedBoostAt_floor
      m h_disc).symm

/-- Allele-frequency mismatch penalty. This penalizes transport when target
allele frequencies drift away from the source frequencies, even if the source
score itself is unchanged.

    Empirical status: **VALIDATED** (the body was corrected first; the
    superseded one and its refutation are recorded below)
    (`simcov/battery_bulk52.py`). The body is now the genotype-variance ratio,
    which matches the measured retention at worst 2.12 sems (0.35% relative).
    What follows records the superseded body and why it failed, because the
    name still says "penalty" and a reader needs to know that the quantity is a
    RATIO which can exceed one.

    THE SUPERSEDED BODY was `exp (-|pTarget - pSource|)`. Retention cannot be a
    function of the GAP alone, which is all that was.

    The observable is the fraction of a variant's predictive contribution that
    survives transport: with a fixed effect, the ratio of realised
    score-phenotype covariance in the target to that in the source, over 3×10⁶
    individuals per population. Three cells share `|Δp| = 0.2` at different
    places in the unit interval:

      p_source  p_target   this body   measured retention
       0.50      0.30       0.9165      0.8418 ± 0.0014
       0.30      0.10       0.9165      0.4278 ± 0.0007
       0.70      0.50       0.9165      1.1926 ± 0.0020

    This body predicts the SAME number for all three, because it sees only
    `|Δp|`. The measurement spans a factor of nearly three across them. Worst
    cell 560 sems at 91% relative. That is a refutation of the SHAPE, not of a
    constant: no rescaling of an exponential in `|Δp|` can produce three
    different values from one gap.

    The third row is the sharper problem. Retention there EXCEEDS ONE -- moving
    a frequency from 0.7 toward 0.5 raises the variant's genotype variance and
    so its contribution -- and a quantity called a penalty, bounded above by one
    for every argument, cannot represent that at all.

    WHAT FITS, and is now the body: the genotype-variance ratio
    `2·p_t(1-p_t) / (2·p_s(1-p_s))`,
    carried on the same cells, MATCHES at worst 2.12 sems (0.35% relative). Its
    square root -- what a STANDARDIZED score would give -- is also falsified, at
    411 sems, so the exponent is settled too. Control: the counted source allele
    frequency recovers `pSource`, at 1.13 sems.

    Consequence: `tagAlleleFreqRetentionAt` and `causalAlleleFreqRetentionAt`
    are this body applied to their own frequencies and inherit the failure.

    REBUILT AND RE-RUN, and the numbers above are superseded by these. The
    battery this cites had never been committed: the verdict was real when it
    was produced and no reader could check it, which is the same standing as no
    verdict. `simcov/battery_bulk52.py` is now in the repository, was run against
    the design described above, and its results are committed beside it.
    MATCH at worst 1.77 sems (0.44% relative) on the three cells that share |dp| = 0.2;
    the superseded exponential is FALSIFIED at 237 sems and the square root -- what a
    STANDARDIZED score would give -- at 137 sems.
    -/
noncomputable def alleleFreqMismatchPenalty (pSource pTarget : ℝ) : ℝ :=
  (2 * pTarget * (1 - pTarget)) / (2 * pSource * (1 - pSource))

/-- **A variant whose frequency does not move keeps its whole contribution.** This is the one
property the superseded exponential body shared with the corrected one, and it survives because
both agree at zero mismatch. -/
@[simp] theorem alleleFreqMismatchPenalty_self (p : ℝ)
    (hp : p ≠ 0) (hp1 : p ≠ 1) :
    alleleFreqMismatchPenalty p p = 1 := by
  unfold alleleFreqMismatchPenalty
  have h : 2 * p * (1 - p) ≠ 0 := by
    intro hzero
    rcases mul_eq_zero.mp hzero with h' | h'
    · rcases mul_eq_zero.mp h' with h'' | h''
      · norm_num at h''
      · exact hp h''
    · exact hp1 (by linarith)
  exact div_self h

/-- **The retention is a RATIO, so it is neither symmetric nor bounded by one**, and the two
theorems that said otherwise were deleted with the exponential body they described.

`alleleFreqMismatchPenalty_symm` asserted `f p q = f q p` and
`alleleFreqMismatchPenalty_le_one` asserted `f p q ≤ 1`. Both are true of `exp (-|Δp|)` and both
are FALSE of what transport retention actually does, which is why the measurement that refuted
the body refutes them too: a variant moving from `0.7` to `0.5` retains `1.19` of its
contribution, not less than one, because its genotype variance ROSE. Swapping source and target
inverts the ratio rather than preserving it.

Keeping either theorem beside the corrected body would have been the laundering this corpus
warns about: a true statement about a superseded formula, left standing where a reader would
take it for a property of the quantity. The measurement is at the definition above. -/
theorem alleleFreqMismatchPenalty_swap_inverts (pSource pTarget : ℝ)
    (hs : 2 * pSource * (1 - pSource) ≠ 0)
    (ht : 2 * pTarget * (1 - pTarget) ≠ 0) :
    alleleFreqMismatchPenalty pSource pTarget *
        alleleFreqMismatchPenalty pTarget pSource = 1 := by
  unfold alleleFreqMismatchPenalty
  rw [div_mul_div_comm,
    mul_comm (2 * pTarget * (1 - pTarget)) (2 * pSource * (1 - pSource))]
  exact div_self (mul_ne_zero hs ht)

/-- **The outcome scale of a generational transport model**, as one object.

Four numbers and the five side conditions that keep them admissible: outcome variance in
each population, the untaggable-phenotype variance, and the target prevalence.  None of them
mentions the panel dimensions, and every witness in the corpus sets them the same way, so as
fields of the model they were nine lines of boilerplate repeated at each witness -- text the
duplication guard could see and no constructor could share, because a field assignment
cannot be lifted out of a structure literal.  As their own structure they are one argument,
and `balanced` is the setting every witness actually wants. -/
structure GenerationalOutcomeScale where
  /-- Outcome variance in the source population. -/
  sourceOutcomeVariance : ℝ
  /-- Outcome variance in the target population, per generation. -/
  targetOutcomeVarianceAt : ℕ → ℝ
  /-- Variance of the target-only untaggable phenotype, per generation. -/
  novelUntaggablePhenotypeVarianceAt : ℕ → ℝ
  /-- Target prevalence, per generation. -/
  targetPrevalenceAt : ℕ → ℝ
  /-- Source outcome variance is positive. -/
  sourceOutcomeVariance_pos : 0 < sourceOutcomeVariance
  /-- Target outcome variance is positive at every generation. -/
  targetOutcomeVariance_pos : ∀ t, 0 < targetOutcomeVarianceAt t
  /-- The untaggable-phenotype variance is a variance. -/
  novelUntaggablePhenotypeVariance_nonneg : ∀ t, 0 ≤ novelUntaggablePhenotypeVarianceAt t
  /-- Prevalence is positive at every generation. -/
  targetPrevalence_pos : ∀ t, 0 < targetPrevalenceAt t
  /-- ... and below one. -/
  targetPrevalence_lt_one : ∀ t, targetPrevalenceAt t < 1

/-- **The balanced outcome scale**: variance `v` in both populations, no untaggable
phenotype, prevalence one half and constant in time.  This is what every generational
witness in the corpus sets, and it is now set once. -/
noncomputable def GenerationalOutcomeScale.balanced (v : ℝ) (hv : 0 < v) :
    GenerationalOutcomeScale where
  sourceOutcomeVariance := v
  targetOutcomeVarianceAt := fun _ ↦ v
  novelUntaggablePhenotypeVarianceAt := fun _ ↦ 0
  targetPrevalenceAt := fun _ ↦ 1 / 2
  sourceOutcomeVariance_pos := hv
  targetOutcomeVariance_pos := fun _ ↦ hv
  novelUntaggablePhenotypeVariance_nonneg := fun _ ↦ le_rfl
  targetPrevalence_pos := fun _ ↦ by norm_num
  targetPrevalence_lt_one := fun _ ↦ by norm_num

/-! The balanced scale's four values, as `simp` lemmas.  Witness proofs evaluate a model by
unfolding its literal, and without these they stop at the constructor call rather than
reaching the numbers -- which is the one cost of nesting these fields, paid once here. -/

@[simp] theorem GenerationalOutcomeScale.balanced_sourceOutcomeVariance (v : ℝ) (hv : 0 < v) :
    (GenerationalOutcomeScale.balanced v hv).sourceOutcomeVariance = v := rfl

@[simp] theorem GenerationalOutcomeScale.balanced_targetOutcomeVarianceAt
    (v : ℝ) (hv : 0 < v) (t : ℕ) :
    (GenerationalOutcomeScale.balanced v hv).targetOutcomeVarianceAt t = v := rfl

@[simp] theorem GenerationalOutcomeScale.balanced_novelUntaggablePhenotypeVarianceAt
    (v : ℝ) (hv : 0 < v) (t : ℕ) :
    (GenerationalOutcomeScale.balanced v hv).novelUntaggablePhenotypeVarianceAt t = 0 := rfl

@[simp] theorem GenerationalOutcomeScale.balanced_targetPrevalenceAt
    (v : ℝ) (hv : 0 < v) (t : ℕ) :
    (GenerationalOutcomeScale.balanced v hv).targetPrevalenceAt t = 1 / 2 := rfl

/-- Generation-indexed cross-population state. Source quantities are fixed at
training time; target quantities are explicit functions of generation. The
time-varying target LD and tagging state is derived from:

- source LD / source tag-causal alignment,
- source causal effects plus an explicit locus-resolved target-effect
  heterogeneity path,
- target-only novel causal effects,
- direct scored-causal measurements that are not mediated by LD decay,
- target-only novel direct causal links,
- ancestry-specific proxy tagging that is mediated by LD decay,
- target-only novel proxy-tagging links,
- recombination and transient `F_ST`,
- mutation- and migration-driven sharing terms, and
- explicit target allele-frequency trajectories split into standing and
  mutation-shift components,
- plus target-only untaggable phenotype variance from novel mutations. -/
structure CrossPopulationGenerationalModel (p q : ℕ) where
  popGen : Descent.Core.PopGenParameters
  betaSource : Fin q → ℝ
  targetEffectHeterogeneityAt : ℕ → Fin q → ℝ
  novelCausalEffectTargetAt : ℕ → Fin q → ℝ
  sigmaTagSource : Matrix (Fin p) (Fin p) ℝ
  directCausalSource : Matrix (Fin p) (Fin q) ℝ
  novelDirectCausalTemplate : Matrix (Fin p) (Fin q) ℝ
  proxyTaggingSource : Matrix (Fin p) (Fin q) ℝ
  novelProxyTaggingTemplate : Matrix (Fin p) (Fin q) ℝ
  tagDistance : Matrix (Fin p) (Fin p) ℝ
  tagCausalDistance : Matrix (Fin p) (Fin q) ℝ
  tagAlleleFreqSource : Fin p → ℝ
  tagAlleleFreqStandingTargetAt : ℕ → Fin p → ℝ
  tagAlleleFreqMutationShiftAt : ℕ → Fin p → ℝ
  causalAlleleFreqSource : Fin q → ℝ
  causalAlleleFreqStandingTargetAt : ℕ → Fin q → ℝ
  causalAlleleFreqMutationShiftAt : ℕ → Fin q → ℝ
  contextCrossSource : Fin p → ℝ
  contextCrossTargetAt : ℕ → Fin p → ℝ
  /-- The outcome scale.  The accessors below expose its fields under their old names, so
  every reader of the model is unaffected by the nesting. -/
  outcome : GenerationalOutcomeScale

namespace CrossPopulationGenerationalModel

variable {p q : ℕ} (m : CrossPopulationGenerationalModel p q)

/-! The outcome scale's fields, under the names they had when they were fields of the model.
They are `abbrev`s and projections, so nothing that read them before reads differently now. -/

/-- Outcome variance in the source population. -/
abbrev sourceOutcomeVariance : ℝ := m.outcome.sourceOutcomeVariance

/-- Outcome variance in the target population, per generation. -/
abbrev targetOutcomeVarianceAt : ℕ → ℝ := m.outcome.targetOutcomeVarianceAt

/-- Variance of the target-only untaggable phenotype, per generation. -/
abbrev novelUntaggablePhenotypeVarianceAt : ℕ → ℝ :=
  m.outcome.novelUntaggablePhenotypeVarianceAt

/-- Target prevalence, per generation. -/
abbrev targetPrevalenceAt : ℕ → ℝ := m.outcome.targetPrevalenceAt

/-! The accessors, as `simp` lemmas: a proof that evaluates a model literal has to get from
the old field name to the nested one, and `abbrev` alone does not carry `simp` across. -/

@[simp] theorem sourceOutcomeVariance_eq :
    m.sourceOutcomeVariance = m.outcome.sourceOutcomeVariance := rfl

@[simp] theorem targetOutcomeVarianceAt_eq :
    m.targetOutcomeVarianceAt = m.outcome.targetOutcomeVarianceAt := rfl

@[simp] theorem novelUntaggablePhenotypeVarianceAt_eq :
    m.novelUntaggablePhenotypeVarianceAt = m.outcome.novelUntaggablePhenotypeVarianceAt := rfl

@[simp] theorem targetPrevalenceAt_eq :
    m.targetPrevalenceAt = m.outcome.targetPrevalenceAt := rfl

end CrossPopulationGenerationalModel

end Descent.Portability
