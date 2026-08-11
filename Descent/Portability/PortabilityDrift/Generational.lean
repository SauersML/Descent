/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Core.Parameters
import Descent.Core.Scaling
import Descent.PopGen.DGP

assert_below Descent.Decision Descent.Program

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

The parts are a FAN, not a chain. The head carries the definitions and every import the
subsystem draws on from outside it; each other part imports the head and whichever siblings
actually declare the names it uses. The split first laid the parts out as a chain, each
importing the one before in the order the original was written, which made every part
transitively downstream of everything written earlier -- so the depth of the corpus was a
function of the length of a file rather than of what depends on what. The order here was
recovered by resolving each name a part references back to the sibling that declares it.

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
    hundreds of sems.

    Power: the composed prediction spans 0.13534 to 0.77880 across the design,
    `theta*tau` running over a factor of eight while `Ne` runs independently over
    a factor of eight, so the form and the `Ne` cancellation are on trial at
    once. Halving or doubling this time scale moves the bottom rows to 0.368 or
    0.018, and the competing one-lineage reading `exp(-mu t)` misses by up to
    433 sems and 174 percent. -/
noncomputable def _root_.Descent.Core.PopGenParameters.tauAt (g : Descent.Core.PopGenParameters)
    (t : ℕ) : Descent.Core.Tau :=
  Descent.Core.Tau.ofGenerations (t : ℝ) g.Ne

/-- **The `2 Nₑ` in `tauAt` is the coalescent time scale.**  The denominator is
`ploidy · Nₑ`, the mean pairwise coalescence time, and not an independently chosen two.
Stated here, beside the definition, rather than in the audit layer at the top of the
graph. -/
theorem _root_.Descent.Core.PopGenParameters.tauAt_uses_timeScale (g :
  Descent.Core.PopGenParameters) (t : ℕ) :
    (Descent.Core.PopGenParameters.tauAt g t).value
      = (t : ℝ) / Descent.Core.coalescentTimeScale g.Ne := by
  unfold Descent.Core.PopGenParameters.tauAt
  rw [Descent.Core.Tau.value_ofGenerations, Descent.Core.coalescentTimeScale_eq]


/-- With a vanishing denominator Mathlib returns `0`, which is a value this quantity can also
take legitimately, so the branch is named rather than left to be inferred from the result. -/
theorem _root_.Descent.Core.PopGenParameters.tauAt_at_zero_denominator_is_junk (g :
  Descent.Core.PopGenParameters) (t : ℕ)
    (hzero : (2 * g.Ne) = 0) :
    (Descent.Core.PopGenParameters.tauAt g t).value = 0 := by
  unfold Descent.Core.PopGenParameters.tauAt
  rw [Descent.Core.Tau.value_ofGenerations, hzero, div_zero]


/-- Per-generation heterozygosity retention factor under drift + mutation. -/
noncomputable def _root_.Descent.Core.PopGenParameters.hetDecayFactor (g :
  Descent.Core.PopGenParameters) : ℝ :=
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

    **THE LEVEL IS NOT THIS RECORD'S OWN, and the record is not general.** This
    body is `PopGen.fstConnectedPairAt` evaluated at `mTot = bigM / (2 Nₑ)`,
    which is `2m`: the total emigration rate of a deme with exactly TWO
    neighbours. That is the geometry this transport layer is about, and it is
    the only one this record can express -- `bigM` carries a per-neighbour rate
    and a `PopGenParameters` has no field saying how many neighbours there are.
    The level it produces, `1/(1 + θ + 2·bigM)`, agrees with the general law on
    a chain interior and is 86% high on a square lattice, where `mTot` is `4m`.
    A caller whose demes have some other degree must use `fstConnectedPairAt`
    with its own row sum; reading this coordinate there is a scope error, not a
    numerical approximation.

    Regime: an interior deme with two neighbours. Boundary demes are outside
    the general law's reach as well, measured up to 16% high.

    The half-life design that validated the decay base does NOT bear on the
    level: it reads `F(t)` against `F(t)`'s own plateau by interpolation, which
    is a shape property with the level divided out. So the level is carried
    entirely by `fstConnectedPairAt`'s record and this one does not claim it
    twice.

    Note that `Descent.Core.PopGenParameters.hetDecayFactor` itself is untouched and remains correct
    for what
    it is: migration does not destroy heterozygosity, it relocates it. The error
    was in using a within-deme decay for a between-deme transient.

    Empirical status: **VALIDATED after correction; the superseded base
    FALSIFIED at up to 2222 sems**
    (`validation/empirical/simcov/battery_dis4.py`). The design and the
    table are recorded on `DGP.fstTransientDecayFromScaled`. Power: the
    half-life prediction spans 32.62 to 69.31 across the design where the
    superseded base spans 69.31 to 554.52. -/
noncomputable def _root_.Descent.Core.PopGenParameters.fstTransientAt (g :
  Descent.Core.PopGenParameters) (t : ℕ) : ℝ :=
  PopGen.fstConnectedPairAt g.Ne g.theta (g.bigM.value / (2 * g.Ne)) t

/-- **The divisor turning a scaled rate back into a per-generation one is the coalescent time
scale**, not a loose two: `bigM` is `2 · ploidy · Nₑ · m` and dividing by `2 Nₑ` returns `2m`,
the total emigration of a deme with two neighbours. -/
theorem _root_.Descent.Core.PopGenParameters.fstTransientAt_uses_coalescentTimeScale
    (g : Descent.Core.PopGenParameters) (t : ℕ) :
    g.fstTransientAt t =
      PopGen.fstConnectedPairAt g.Ne g.theta
        (g.bigM.value / Descent.Core.coalescentTimeScale g.Ne) t := by
  unfold Descent.Core.PopGenParameters.fstTransientAt
  rw [Descent.Core.coalescentTimeScale_eq]

/-- **The record's own spelling of the coordinate**, recovered from the general law at the
two-neighbour total emigration rate. `4 · Nₑ · (bigM / (2 Nₑ))` is `2 · bigM` whenever the
effective size is nonzero, which is where the superseded hardcoded level came from; at
`Nₑ = 0` the record's `bigM` is junk and the two spellings part, so the hypothesis is real. -/
theorem _root_.Descent.Core.PopGenParameters.fstTransientAt_eq_explicit
    (g : Descent.Core.PopGenParameters) (hNe : g.Ne ≠ 0) (t : ℕ) :
    g.fstTransientAt t =
      (1 / (1 + g.theta.value + 2 * g.bigM.value)) *
        (1 - PopGen.fstTransientDecayFromScaled g.Ne g.theta g.bigM ^ t) := by
  unfold Descent.Core.PopGenParameters.fstTransientAt PopGen.fstConnectedPairAt
    PopGen.fstTransientDecayFromScaled
  have hlevel : 4 * g.Ne * (g.bigM.value / (2 * g.Ne)) = 2 * g.bigM.value := by
    field_simp
    ring
  rw [hlevel]

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
    above are from the redone design.

    Power: the prediction spans 0.13534 to 0.77880 across the design, with
    `theta*tau` running over a factor of eight and `Ne` independently over a
    factor of eight, and the competing one-lineage reading `exp(-mu t)` misses by
    up to 433 sems and 174 percent on the same measurement. -/
noncomputable def _root_.Descent.Core.PopGenParameters.mutationSharedRetentionAt
    (g : Descent.Core.PopGenParameters) (t : ℕ) : ℝ :=
  Real.exp (-g.theta.value * (g.tauAt t).value)

@[simp] theorem _root_.Descent.Core.PopGenParameters.tauAt_zero (g : Descent.Core.PopGenParameters)
  :
    (g.tauAt 0).value = 0 := by
  simp [Descent.Core.PopGenParameters.tauAt]

@[simp] theorem _root_.Descent.Core.PopGenParameters.fstTransientAt_zero (g :
  Descent.Core.PopGenParameters) :
    g.fstTransientAt 0 = 0 := by
  simp [Descent.Core.PopGenParameters.fstTransientAt, PopGen.fstTransientDecayFromScaled,
    PopGen.hetDecayFromScaled]

@[simp] theorem _root_.Descent.Core.PopGenParameters.mutationSharedRetentionAt_zero (g :
  Descent.Core.PopGenParameters) :
    g.mutationSharedRetentionAt 0 = 1 := by
  simp [Descent.Core.PopGenParameters.mutationSharedRetentionAt,
    Descent.Core.PopGenParameters.tauAt]


/-- Exact bridge from the coarse DGP evolutionary block to the
generation-indexed population-genetic parameter block used by the mechanistic
transport model. This carries only the shared popgen primitives; the
SNP/LD-aware state still lives in `CrossPopulationGenerationalModel`. -/
noncomputable def _root_.Descent.PopGen.PGSEvolutionaryModel.toGenerationalPopGenParameters
    (m : PopGen.PGSEvolutionaryModel) : Descent.Core.PopGenParameters where
  Ne := m.Ne
  mu := m.mu
  mig := m.mig
  -- `EvolutionaryParameters` carries no deme count, and the quantity it computes is
  -- `DGP.fstEquilibrium`'s `1/(1 + θ + 2M)`, whose migration coefficient IS
  -- `islandDemeCorrection 2`.  So two is the count that record already assumes, and
  -- writing it here states the assumption rather than inheriting it: this bridge is
  -- about a two-population split and says so.
  nDemes := 2
  t_div := m.t_div
  recomb := m.recomb
  V_A := m.V_A
  Ne_pos := m.Ne_pos
  mu_nonneg := m.mu_nonneg
  mig_nonneg := m.mig_nonneg
  nDemes_ge_two := by norm_num
  t_div_nonneg := m.t_div_nonneg
  recomb_nonneg := m.recomb_nonneg
  recomb_le_half := m.recomb_le_half
  V_A_pos := m.V_A_pos

@[simp] theorem _root_.Descent.PopGen.PGSEvolutionaryModel.toGenerationalPopGenParameters_theta
    (m : PopGen.PGSEvolutionaryModel) :
    (m.toGenerationalPopGenParameters).theta.value = m.theta := by
  simp [PopGen.PGSEvolutionaryModel.toGenerationalPopGenParameters,
    Descent.Core.PopGenParameters.theta, PopGen.EvolutionaryParameters.theta,
    Descent.Core.Theta.ofRate, Descent.Core.scalingConstant, Descent.Core.scaledMutationRate]

@[simp] theorem _root_.Descent.PopGen.PGSEvolutionaryModel.toGenerationalPopGenParameters_bigM
    (m : PopGen.PGSEvolutionaryModel) :
    (m.toGenerationalPopGenParameters).bigM.value = m.bigM := by
  simp [PopGen.PGSEvolutionaryModel.toGenerationalPopGenParameters,
    Descent.Core.PopGenParameters.bigM, PopGen.EvolutionaryParameters.bigM,
    Descent.Core.BigM.ofRate, Descent.Core.scalingConstant, Descent.Core.scaledMigrationRate]

@[simp] theorem
  _root_.Descent.PopGen.PGSEvolutionaryModel.toGenerationalPopGenParameters_hetDecayFactor
    (m : PopGen.PGSEvolutionaryModel) :
    (m.toGenerationalPopGenParameters).hetDecayFactor = m.hetDecayFactor := by
  unfold Descent.Core.PopGenParameters.hetDecayFactor PopGen.PGSEvolutionaryModel.hetDecayFactor
    PopGen.hetDecayFromScaled
  rw [PopGen.PGSEvolutionaryModel.toGenerationalPopGenParameters_theta]
  rfl

/-- The transient `F_ST` coordinate in the coarse DGP block agrees exactly with the
generation-indexed popgen bridge at `⌊t_div⌋`, because both use the same
discrete differentiation recursion. Both were corrected together: an identity
between two coordinates survives a common wrong factor on both sides, so this
theorem constrained them jointly and could not have caught the decay base. -/
@[simp] theorem
  _root_.Descent.PopGen.PGSEvolutionaryModel.toGenerationalPopGenParameters_fstTransientAt_floor
    (m : PopGen.PGSEvolutionaryModel) :
    (m.toGenerationalPopGenParameters).fstTransientAt (Nat.floor m.t_div) =
      m.fstTransient := by
  rw [Descent.Core.PopGenParameters.fstTransientAt_eq_explicit _
    (by simp [PopGen.PGSEvolutionaryModel.toGenerationalPopGenParameters]; exact ne_of_gt m.Ne_pos)]
  unfold PopGen.PGSEvolutionaryModel.fstTransient
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
    PopGen.EvolutionaryParameters.bigM, Descent.Core.scaledMutationRate,
      Descent.Core.scaledMigrationRate,
    Descent.Core.Theta.ofRate, Descent.Core.BigM.ofRate, Descent.Core.Tau.ofGenerations,
    Descent.Core.scalingConstant, Descent.Core.ratio,
    Descent.Core.scaledMutationRate, Descent.Core.scaledMigrationRate,
    Descent.Core.Theta.ofRate, Descent.Core.BigM.ofRate, Descent.Core.Tau.ofGenerations,
    Descent.Core.scalingConstant, Descent.Core.ratio, Descent.Core.ploidy]
  exact Or.inl (by ring)

/-- When divergence time is an integer number of generations, the coarse
mutation-history coordinate agrees exactly with the generational popgen bridge
at that generation. -/
theorem _root_.Descent.PopGen.PGSEvolutionaryModel.toGenerational_mutationSharedRetentionAt_floor
    (m : PopGen.PGSEvolutionaryModel)
    (h_disc : m.t_div = (Nat.floor m.t_div : ℝ)) :
    (m.toGenerationalPopGenParameters).mutationSharedRetentionAt (Nat.floor m.t_div) =
      PopGen.mutationLDErosion m.toEvo := by
  unfold Descent.Core.PopGenParameters.mutationSharedRetentionAt
    PopGen.PGSEvolutionaryModel.toEvo PopGen.mutationLDErosion
  rw [PopGen.PGSEvolutionaryModel.toGenerationalPopGenParameters_theta]
  simp only [Descent.Core.PopGenParameters.tauAt, Descent.Core.Tau.value_ofGenerations,
    PopGen.PGSEvolutionaryModel.toGenerationalPopGenParameters,
    PopGen.EvolutionaryParameters.theta, PopGen.EvolutionaryParameters.tau]
  rw [h_disc, Nat.floor_natCast]

/-- Exact bridge from the DGP coordinate summary to the generational popgen
coordinates for the fields that genuinely match. The LD coordinate is
deliberately excluded here because the mechanistic model uses a joint
locus-specific kernel rather than a single global LD scalar. -/
theorem
  _root_.Descent.PopGen.PGSEvolutionaryModel.coordinateSummary_matches_generational_popgen_at_floor
    (m : PopGen.PGSEvolutionaryModel)
    (h_disc : m.t_div = (Nat.floor m.t_div : ℝ)) :
    m.coordinateSummary.alleleFreqCoordinate =
      1 - (m.toGenerationalPopGenParameters).fstTransientAt (Nat.floor m.t_div) ∧
    m.coordinateSummary.ancestralVariantCoordinate =
      (m.toGenerationalPopGenParameters).mutationSharedRetentionAt (Nat.floor m.t_div) := by
  refine ⟨?_, ?_⟩
  · rw [PopGen.PGSEvolutionaryModel.coordinateSummary_alleleFreqCoordinate]
    exact congrArg (fun x ↦ 1 - x)
      (PopGen.PGSEvolutionaryModel.toGenerationalPopGenParameters_fstTransientAt_floor m).symm
  · rw [PopGen.PGSEvolutionaryModel.coordinateSummary_ancestralVariantCoordinate]
    exact
      (PopGen.PGSEvolutionaryModel.toGenerational_mutationSharedRetentionAt_floor
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

    Power: measured retention runs from 0.4278 to 1.1926 -- one cell above one --
    across three cells that all share `|Δp| = 0.2`, which is exactly the set any
    gap-only shape must give a single number to. On the committed re-run this
    body MATCHES at worst 1.77 sems while the superseded exponential is
    FALSIFIED at 237 sems and its square root at 137.
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
- a SUPPLIED LD-retention surface, read at a tag separation and a generation,
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
  /-- **The LD-retention surface**: the fraction of the source population's between-locus
  LD correlation that survives in the target, read at a tag separation and a generation.

  IT IS AN INPUT AND IT ASSERTS NOTHING.  Any surface whatever satisfies this field, so no
  measurement can disagree with it, and the field carries no hypothesis -- not monotonicity
  in separation, not a rate multiplying separation, and in particular not the value `1` at
  zero separation.  What IS claimed is claimed by the kernels that read it
  (`jointTagLDKernelAt` and the two proxy kernels): that this factor enters MULTIPLICATIVELY
  beside mutation retention and the allele-frequency retentions.  A construction site fills
  this slot with a stipulation or a measurement and says which; a site that filled it
  silently would be a deleted body with extra steps.

  ONE THING A CONSTRUCTION SITE OWES THE REST OF THE CHAPTER, and it is about the time
  index rather than about LD: at generation `0` the target IS the source, so retention there
  is `1` at every separation and every kernel is exactly `1`.  The closed form this slot
  replaced got that free, through a transient `F_ST` of zero at `t = 0`; a supplied surface
  has to say it, and a site that did not would be claiming the two populations differ before
  they have diverged.  It is stated here rather than carried as a hypothesis field for the
  same reason the allele-frequency paths carry none: the structure lets a construction be
  wrong and the theorems about each construction are what pin it.

  THE SLOT IS EMPTY BECAUSE THE CLOSED FORM IS OWED, NOT BECAUSE NONE EXISTS.  The exact
  machinery is published and installed: the Ragsdale-Gravel two-locus moment system computes
  the cross-deme second moments of `D` directly for a stated demography, so the surface can
  be evaluated numerically today (`validation/empirical/momentsld/ld_surface.py`) and a
  derivation has something exact to be checked against.  What the corpus lacks is a closed
  form for it, which is a derivation owed rather than an open question.  When that lands it
  becomes a computed instance of this field and no consumer changes.

  WHAT RETIRED INTO THIS SLOT, carried as a rival record rather than as prose about the
  past.  The field replaces `ldCorrelationDecay`, `exp(-(lambda * √fstGap * distance))`,
  and every part of that body is refuted:

  * the SHAPE in separation, at `validation/empirical/popgensel/ldshapecell.py` cell `I` --
    χ²/point 28.49 and 79.66 for the exponential against 4.16 and 1.95 for a hyperbolic, on
    a fitter that prefers the exponential 168- and 197-fold when handed a true one;
  * the RATE's divergence dependence, at `simcov/battery_bulk54.py` -- the `√fstGap` reading
    FALSIFIED at 4.31 sems, the superseded linear `fstGap` at 8.04 and a rate independent of
    divergence at 25.48, over a 240-fold sweep in `4·Nₑ·m`;
  * the RATE SLOT itself, at `simcov/battery_rate22.py` -- read as `4·Nₑ·c` under this
    shape, FALSIFIED at 1099.66 sems over six cells crossing `Nₑ` against realised `F_ST`;
  * the AMPLITUDE.  Both this body and the hyperbolic successor deleted beside it force the
    surface to `1` at zero separation.  The measurement puts it at 0.91-0.98 and tracking
    `F_ST` rather than `Nₑ`, and the moment system agrees from a separate code path
    (0.9111 at `F_ST` 0.048, 0.6926 at 0.200).  A theorem needing `retention 0 = 1` would
    inherit that refutation, so nothing in this chapter states one.

  The one reading `battery_rate22` did NOT refute is the rate VARIABLE: in `ρ = 4·Nₑ·c`
  units the cross-deme curve is free of `Nₑ`, which is the coordinate the owed derivation
  should be written in. -/
  ldRetentionAt : ℕ → ℝ → ℝ
  tagAlleleFreqSource : Fin p → ℝ
  tagAlleleFreqStandingTargetAt : ℕ → Fin p → ℝ
  tagAlleleFreqMutationShiftAt : ℕ → Fin p → ℝ
  causalAlleleFreqSource : Fin q → ℝ
  causalAlleleFreqStandingTargetAt : ℕ → Fin q → ℝ
  causalAlleleFreqMutationShiftAt : ℕ → Fin q → ℝ
  contextCrossSource : Fin p → ℝ
  contextCrossTargetAt : ℕ → Fin p → ℝ
  /-- The outcome scale: the four quantities that carry the phenotype's units, grouped so
  that the hypotheses constraining them (`targetPrevalence_pos` and its companions) travel
  with the fields they constrain.  Read its fields through `outcome`; there is no flattened
  spelling. -/
  outcome : GenerationalOutcomeScale

end Descent.Portability
