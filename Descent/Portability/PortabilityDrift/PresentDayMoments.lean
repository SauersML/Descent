/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Foundations.BernoulliLosses
import Descent.Portability.PortabilityDrift.Generational
import Descent.Portability.PortabilityDrift.PresentDayMetrics
import Descent.Portability.PortabilityDrift.Definitions

-- The Brier and log-loss risk decompositions this file states its present-day moment
-- results in terms of: `bernoulliLogLoss`, `bernoulliKLReal`, `brierBernoulliRisk`,
-- `exactBrierRiskOfCalibrated` and the pointwise regret identities. They are losses of one
-- Bernoulli outcome against one prediction, so they sit below this chapter rather than
-- above it, and the import runs downward like every other one here.

assert_below Descent.Decision Descent.Program

namespace Descent.Portability

open MeasureTheory
open PopGen (genotypeVarianceHWE)

open PopGen.TransportedMetrics (r2FromSignalVariance r2FromSignalVariance_eq_rsquared
  equalVarianceGaussianAUCFromSignalVariance
  equalVarianceGaussianAUCFromSignalVariance_eq_formula_of_ne_noise)

/-!
# `PortabilityDrift.PresentDayMoments`

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

section PresentDayMetrics

/-- **The generational transport model is inhabited**, at every panel size `(p, q)`.

    The tag covariance is the identity, the two populations start at the same
    allele frequencies, and the effect vector, the heterogeneity path and the
    novel-mutation path are zero: this is the no-divergence configuration, in
    which the transported score is the source score at every generation. It is
    the null of the theory rather than an interesting member of it, and that is
    the point — it fixes what the generational statements quantify over. The
    variance and prevalence fields are strictly inside their constraints.

    PROVENANCE OF THE LD-RETENTION SURFACE, which the field requires of every
    construction site: STIPULATED, not measured. This is the no-divergence
    configuration, in which the two populations are the same population, so
    nothing decorrelates and the surface is `1` everywhere. It is the one place
    the value `1` is not a claim about a diverged pair — `momentsLDWitness`
    below is the diverged instance, and its surface is measured. -/
noncomputable def CrossPopulationGenerationalModel.witness (p q : ℕ) :
    CrossPopulationGenerationalModel p q where
  popGen := Descent.Core.PopGenParameters.witness
  betaSource := fun _ ↦ 0
  targetEffectHeterogeneityAt := fun _ _ ↦ 0
  novelCausalEffectTargetAt := fun _ _ ↦ 0
  sigmaTagSource := 1
  directCausalSource := 0
  novelDirectCausalTemplate := 0
  proxyTaggingSource := 0
  novelProxyTaggingTemplate := 0
  tagDistance := 0
  tagCausalDistance := 0
  ldRetentionAt := fun _ _ ↦ 1
  tagAlleleFreqSource := fun _ ↦ 1 / 2
  tagAlleleFreqStandingTargetAt := fun _ _ ↦ 1 / 2
  tagAlleleFreqMutationShiftAt := fun _ _ ↦ 0
  causalAlleleFreqSource := fun _ ↦ 1 / 2
  causalAlleleFreqStandingTargetAt := fun _ _ ↦ 1 / 2
  causalAlleleFreqMutationShiftAt := fun _ _ ↦ 0
  contextCrossSource := fun _ ↦ 0
  contextCrossTargetAt := fun _ _ ↦ 0
  outcome := GenerationalOutcomeScale.balanced 1 (by norm_num)

/-- **The generational model at a MEASURED LD-retention surface.**

    The null above fills its retention slot by stipulation, which is right for a
    no-divergence configuration and says nothing about a diverged pair. This one
    fills it from the Ragsdale-Gravel two-locus moment system, which integrates
    the cross-deme second moments of `D` exactly for a stated demography rather
    than fitting a rate to a simulation. The run is
    `validation/empirical/momentsld/ld_surface.py`; its cell is a two-deme split
    with continuous symmetric migration at equal sizes, and the Hudson `F_ST`
    measured from that same integration's heterozygosities is 0.0476. In the rate
    variable `ρ = 4·Nₑ·c` it returns

      ρ        0        1        2        5        10       20
      Corr(D)  0.91113  0.84009  0.77904  0.63985  0.49350  0.33915

    and this witness reads two of those points: every tag pair sits at `ρ = 5`,
    and each locus is at separation `0` from itself.

    THE GENERATION INDEX, and why the measured slice is not generation `0`. The
    run is an EQUILIBRIUM cell -- a pair that has already diverged and is held
    there by migration -- so it is the surface AFTER divergence, not a trajectory
    through it. Generation `0` of this structure is the slice at which the target
    IS the source, where every kernel is `1` by construction, so the measured
    surface is read at every later generation and the undiverged slice keeps the
    value the structure's own semantics give it. Nothing here claims the approach
    to equilibrium takes one generation; the witness exhibits two slices, not a
    path between them.

    TWO THINGS THE MEASURED SURFACE SAYS THAT NEITHER DELETED BODY COULD.
    Retention at zero separation is 0.91113 and not `1`: at zero recombination
    distance the ancestral `D` still drifts apart in the two demes, and how far
    it drifts is what `F_ST` measures — the same integration gives 0.6926 at
    `F_ST` 0.1999, so the deficit tracks divergence. And the fall with separation
    is exhibited as values rather than as a law, because the corpus states no
    shape here and this witness is not the place to smuggle one back.

    THE TABLE DOES NOT TRANSFER TO A MULTI-DEME PAIR AT SEPARATION `≥ 2`, and the reason is
    in the run's own scope rather than in any later measurement. The cell integrated is a
    TWO-DEME split with continuous symmetric migration
    (`moments.LD.Demographics2D.split_mig`), so what the table holds is that demography's
    surface. It is NOT a function of `F_ST` that a stepping-stone pair may be looked up in.
    Matching a distant pair's `F_ST` to this cell's and reading `Corr(D)` off the row is a
    substitution nothing here licenses: two demes exchanging migrants directly and two demes
    separated by intervening ones can arrive at the same one-locus `F_ST` along different
    histories, and the two-locus moments are not determined by the one-locus moment. A pair
    at separation `0` or `1` is inside this demography; anything beyond it needs its own
    integration, not this row rescaled.

    AND THE PROHIBITION IS NOW MEASURED, not only argued
    (`validation/empirical/momentsld/ldchain_reduction.json`, exact rational arithmetic on
    the two-locus ancestral-configuration system for linear chains of 2, 3 and 4 demes; not a
    battery, so it carries no ledger row and must not be cited as one). The surrogate under
    test is exactly the substitution forbidden above: take the pair's own exact Hudson
    `F_ST`, invert the two-deme relation for an effective `M`, and read this table. At
    `rho = 20` in a four-deme chain it is biased HIGH at every separation —

      cell                    d = 1     d = 2      d = 3
      grid2d per-edge rate    +5.6%    +314.7%   +1682.8%
      serial1d per-edge rate  +10.8%   +123.9%    +379.0%

    — and +1682.8% is the worst over the whole design (exact 0.00494 against a surrogate
    0.08806). The bias grows with separation and with `rho`, which is the signature of the
    mechanism named above rather than of a broken calculation; and the control that settles
    that is in the file too, computed through the identical code path: at TWO demes the
    surrogate IS the exact answer, error exactly `0.00000000` in all twelve cells.

    WHAT THIS DOES AND DOES NOT LICENSE, because the two axes are different questions and
    conflating them is how a two-deme law ends up on a thirty-six-deme lattice. TIME: the
    equilibrium FORM is adequate for grid2d's split age, the transient sitting 1.2% to 3.8%
    above equilibrium, one-signed, shrinking as `rho` grows
    (`validation/empirical/momentsld/derivation/ldtransient.log`, which gates itself at both
    ends — `rD = 1` at zero age and the equilibrium rational function at infinite age).
    STRUCTURE: whether a TWO-deme law describes a thirty-six-deme lattice at all is the
    multi-deme reduction, it is OPEN, and no transient calculation touches it. The table
    above is what the structure axis looks like when the question is answered by
    substitution. Nor does the chain file supply a replacement: it is linear chains at
    equilibrium, and the geometric law `rD(0,1)^d` that holds there to within 6.94% is a
    one-dimensional statement that must not be carried onto a lattice either.

    Empirical status: NOT AN EMPIRICAL CLAIM. It is a witness — an instance
    exhibited so that statements about the structure have something to be about.
    What was measured is the surface it reads, and that measurement's provenance
    is the paragraph above. -/
noncomputable def CrossPopulationGenerationalModel.momentsLDWitness :
    CrossPopulationGenerationalModel 2 1 :=
  { CrossPopulationGenerationalModel.witness 2 1 with
    tagDistance := Matrix.of fun i j ↦ if i = j then 0 else 5
    tagCausalDistance := Matrix.of fun _ _ ↦ 5
    ldRetentionAt := fun t d ↦
      if t = 0 then 1 else if d ≤ 0 then 0.91113 else 0.63985 }

/-- **The measured surface is below one where it is shared, and falls where it
separates.** Both retired bodies forced the first of these to equality — an
amplitude of `1` at zero separation — and the measurement refuses it. Stated on
the witness rather than as a property of the field, because the field asserts
nothing and this is one instance of it. Read after divergence: at generation `0`
the two populations are one population and the retention is `1` for a reason that
has nothing to do with the amplitude question. -/
theorem momentsLDWitness_retention_below_one_and_falls :
    CrossPopulationGenerationalModel.momentsLDWitness.ldRetentionAt 1 0 < 1 ∧
      CrossPopulationGenerationalModel.momentsLDWitness.ldRetentionAt 1 5 <
        CrossPopulationGenerationalModel.momentsLDWitness.ldRetentionAt 1 0 := by
  constructor <;>
    norm_num [CrossPopulationGenerationalModel.momentsLDWitness,
      CrossPopulationGenerationalModel.witness]

/-- Generation-indexed target effect vector. This is derived from the source
effect vector plus an explicit locus-resolved heterogeneity path and a
target-only novel-mutation effect path, not from any single retained-effect
scalar. -/
noncomputable def betaTargetAt {p q : ℕ}
    (m : CrossPopulationGenerationalModel p q) (t : ℕ) : Fin q → ℝ :=
  m.betaSource + m.targetEffectHeterogeneityAt t + m.novelCausalEffectTargetAt t

@[simp] theorem betaTargetAt_eq_source_plus_effectHeterogeneityAt {p q : ℕ}
    (m : CrossPopulationGenerationalModel p q) (t : ℕ) :
    betaTargetAt m t =
      m.betaSource + m.targetEffectHeterogeneityAt t + m.novelCausalEffectTargetAt t := by
  rfl

/-- Explicit target tag-SNP allele frequency after standing drift and
mutation-specific shift are combined.

    Empirical status: NOT AN EMPIRICAL CLAIM. Both summands are FREE FIELDS of
    `CrossPopulationGenerationalModel` -- unconstrained functions
    `ℕ → Fin p → ℝ`, with no equation anywhere relating either to a population.
    Any target frequency trajectory whatever satisfies this body, by putting all
    of it in the standing term and zero in the shift; no observation can
    disagree with a decomposition whose two parts are both free. The content it
    carries is a naming convention -- which part of a target frequency is called
    standing and which is called mutation-specific -- and a convention is settled
    by the definitions that constrain those fields, not by a simulation.

    Where the observable content of this chain does live: `tagAlleleFreqRetentionAt`
    below, whose body was moved by a measurement and carries its own verdict. -/
noncomputable def tagAlleleFreqTargetAt {p q : ℕ}
    (m : CrossPopulationGenerationalModel p q) (t : ℕ) (i : Fin p) : ℝ :=
  m.tagAlleleFreqStandingTargetAt t i + m.tagAlleleFreqMutationShiftAt t i

@[simp] theorem tagAlleleFreqTargetAt_eq_standing_plus_mutationShift {p q : ℕ}
    (m : CrossPopulationGenerationalModel p q) (t : ℕ) (i : Fin p) :
    tagAlleleFreqTargetAt m t i =
      m.tagAlleleFreqStandingTargetAt t i + m.tagAlleleFreqMutationShiftAt t i := by
  rfl

/-- Explicit target causal-site allele frequency after standing drift and
mutation-specific shift are combined.

    Empirical status: NOT AN EMPIRICAL CLAIM, for the reason spelled out at
    `tagAlleleFreqTargetAt`: `causalAlleleFreqStandingTargetAt` and
    `causalAlleleFreqMutationShiftAt` are both free fields of
    `CrossPopulationGenerationalModel`, so every causal-site trajectory
    satisfies this body and none can disagree with it. The split between
    standing variation and new mutation is a naming convention here, not a
    prediction. -/
noncomputable def causalAlleleFreqTargetAt {p q : ℕ}
    (m : CrossPopulationGenerationalModel p q) (t : ℕ) (j : Fin q) : ℝ :=
  m.causalAlleleFreqStandingTargetAt t j + m.causalAlleleFreqMutationShiftAt t j

@[simp] theorem causalAlleleFreqTargetAt_eq_standing_plus_mutationShift {p q : ℕ}
    (m : CrossPopulationGenerationalModel p q) (t : ℕ) (j : Fin q) :
    causalAlleleFreqTargetAt m t j =
      m.causalAlleleFreqStandingTargetAt t j + m.causalAlleleFreqMutationShiftAt t j := by
  rfl

/-- Per-tag allele-frequency retention at generation `t`.

    Empirical status: **VALIDATED** at worst 2.12 sems (0.35% relative), on the
    cells of `battery_verify.py` that refuted the previous body at 560. The
    verdict moved because the BODY moved; the design is the same one.

    WHAT THE PREVIOUS BODY WAS AND WHY IT FAILED. It applied
    `alleleFreqMismatchPenalty` to this tag's source and time-`t` target
    frequencies, and that function is refuted at 560 sems: retention is not a
    function of the frequency GAP at all. Three source/target pairs sharing
    `|Δp| = 0.2` measure retention 0.842, 0.428 and 1.193, where the penalty
    predicts one number for all three.

    The failure is not softened by the generational wrapper. If anything it is
    sharpened: `tagAlleleFreqTargetAt` moves the target frequency with `t`, so a
    tag drifting from 0.3 toward 0.1 and one drifting from 0.7 toward 0.5 travel
    the same distance and are assigned the same retention, while the measured
    values differ by a factor of nearly three and one of them EXCEEDS ONE.

    CORRECTED to the form that fits: the genotype-variance ratio
    `2·p_t(1-p_t) / (2·p_source(1-p_source))`, which matches at worst 2.12 sems
    (0.35% relative) on the same cells that falsified the gap penalty at 560.
    The exponent is settled by the same design: the SQUARE ROOT of this ratio --
    what a standardized score would give -- is falsified at 411 sems, so the
    ratio is of variances and not of standard deviations. Control: the counted
    source allele frequency recovers `pSource` at 1.13 sems.

    Written out rather than routed through `alleleFreqMismatchPenalty`, because
    that body is the falsified one and this definition should not inherit
    whatever becomes of it.

    Two things the corrected body gets right that the penalty could not. It is
    not a function of the frequency GAP, so the three pairs sharing `|Δp| = 0.2`
    that measured 0.842, 0.428 and 1.193 are now given three different values.
    And it is unbounded above, so a variant drifting toward `1/2` -- which raises
    its genotype variance and therefore its contribution -- is reported as
    retention above one instead of as a loss.

    Power: measured retention runs from 0.428 to 1.193 across the design -- one
    cell above one -- on three pairs that all share `|Δp| = 0.2`, which is
    exactly the set a gap-based penalty must give a single number to. That is why
    `alleleFreqMismatchPenalty` is FALSIFIED at 560 sems on these cells where this
    body sits at 2.12, and the square-root form -- a ratio of standard deviations
    rather than of variances -- is rejected at 411. -/
noncomputable def tagAlleleFreqRetentionAt {p q : ℕ}
    (m : CrossPopulationGenerationalModel p q) (t : ℕ) (i : Fin p) : ℝ :=
  (2 * tagAlleleFreqTargetAt m t i * (1 - tagAlleleFreqTargetAt m t i)) /
    (2 * m.tagAlleleFreqSource i * (1 - m.tagAlleleFreqSource i))

/-- Per-causal-variant allele-frequency retention at generation `t`.

    Empirical status: **VALIDATED** at worst 2.12 sems, on the same corrected
    footing as `tagAlleleFreqRetentionAt` above and measured on the same cells.

    WHAT THE PREVIOUS BODY WAS AND WHY IT FAILED. It was
    `alleleFreqMismatchPenalty` applied to a causal variant's source and time-`t`
    target frequencies, and that function is refuted at 560 sems because
    retention is not a function of the frequency gap.

    The causal case is the one where it matters most. A causal variant's
    contribution to the transported score scales with its genotype variance, so
    a variant drifting TOWARD 0.5 contributes MORE in the target than in the
    source -- retention above one, which a penalty bounded by one cannot express
    and which the old body always reported as a loss.

    CORRECTED to the genotype-variance ratio, as `tagAlleleFreqRetentionAt` is
    and for the same measurement: 2.12 sems against the penalty's 560, with the
    square-root form rejected at 411 sems so the exponent is fixed. That the
    corrected body is exactly the quantity this docstring already said the
    contribution scales with is the point -- the diagnosis was written down here
    before the body was changed to match it.

    Power: the cells are `tagAlleleFreqRetentionAt`'s, where the gap-based penalty
    this body replaces is FALSIFIED at 560 sems and the square-root form at 411,
    while this body sits at 2.12. What the design turns on is that a variant
    drifting toward 0.5 must be reported as retention ABOVE one, which a penalty
    bounded by one cannot express at any parameter. -/
noncomputable def causalAlleleFreqRetentionAt {p q : ℕ}
    (m : CrossPopulationGenerationalModel p q) (t : ℕ) (j : Fin q) : ℝ :=
  (2 * causalAlleleFreqTargetAt m t j * (1 - causalAlleleFreqTargetAt m t j)) /
    (2 * m.causalAlleleFreqSource j * (1 - m.causalAlleleFreqSource j))

/-- Fraction of target-side novel variation accumulated by generation `t`.
This is the complement of shared ancestral variation retained after mutation. -/
noncomputable def novelVariantInnovationAt (g : Descent.Core.PopGenParameters) (t : ℕ) : ℝ :=
  1 - g.mutationSharedRetentionAt t

@[simp] theorem novelVariantInnovationAt_zero (g : Descent.Core.PopGenParameters) :
    novelVariantInnovationAt g 0 = 0 := by
  simp [novelVariantInnovationAt]

/-- Joint locus-level transport kernel for LD among scored SNPs at generation
`t`. This is where drift, recombination, mutation history and tag-SNP
allele-frequency drift meet; the mechanistic model does not treat them as
independent global scalars.

    **THE MIGRATION FACTOR IS DELETED, AND ITS ABSENCE IS A GAP RATHER THAN A
    ZERO.** This kernel used to multiply in `migrationSharedBoostAt`, and that
    body is refuted -- `simcov/battery_bulk55.py`, eightfold `τ` sweep, worst
    29.5 sems at 56% -- as a SHAPE and not as a coefficient: its own form given a
    free amplitude and fitted to the cells still misses by 3.90 sems, so nothing
    is recoverable by rescaling. A product cannot average a wrong factor away, so
    it went.

    **What that costs, stated rather than hidden.** The same run rejects a boost
    of exactly `1` at 13.6 sems: migration DOES restore shared LD. This kernel
    now omits that restoration entirely, so it is an UNDERSTATEMENT of shared LD
    wherever migration is ongoing, by a factor the measurement bounds between
    about 1.02 and 1.25 over `τ ∈ [0.25, 2]` and `bigM ∈ [0.5, 16]`. It is exact
    only at `bigM = 0`. The corpus prefers a named omission to a refuted formula,
    and the repair is a DERIVED migration factor, which nothing here supplies:
    the measured dependence rises with divergence and then flattens, which is
    neither the deleted proportionality nor the constant that replaced it.

    **THE LD FACTOR IS NOW A SUPPLIED SURFACE AND THE FALSIFIED BODY IT CALLED
    IS GONE.** The first factor was `ldCorrelationDecay` read at the
    transient `F_ST`, and that body's shape, rate and amplitude were each
    refuted in turn. It is replaced by `m.ldRetentionAt`, a FIELD of the model:
    the construction site supplies the surface and states where it came from,
    and the refutation record travels with that field rather than with this
    kernel. Nothing is claimed here about how retention varies with separation.

    Empirical status: **UNTESTED**, which is a narrower gap than the FALSIFIED
    head this carried and not the same statement. What this kernel claims, once
    the LD factor is an input, is that the four factors enter as a PRODUCT --
    LD retention, mutation retention and the two allele-frequency retentions
    multiplying without interaction. That is contradictable and nothing has
    measured it. Carrying the old head forward would attribute to a product a
    verdict that was about one of its factors, and that factor is no longer
    here. -/
noncomputable def jointTagLDKernelAt {p q : ℕ}
    (m : CrossPopulationGenerationalModel p q) (t : ℕ) (i j : Fin p) : ℝ :=
  m.ldRetentionAt t (m.tagDistance i j) *
    m.popGen.mutationSharedRetentionAt t *
    tagAlleleFreqRetentionAt m t i *
    tagAlleleFreqRetentionAt m t j

@[simp] theorem jointTagLDKernelAt_uses_ld_af_mutation {p q : ℕ}
    (m : CrossPopulationGenerationalModel p q) (t : ℕ) (i j : Fin p) :
    jointTagLDKernelAt m t i j =
      m.ldRetentionAt t (m.tagDistance i j) *
        m.popGen.mutationSharedRetentionAt t *
            tagAlleleFreqRetentionAt m t i *
        tagAlleleFreqRetentionAt m t j := by
  simp [jointTagLDKernelAt]

/-- Joint locus-level transport kernel for directly scored causal variants.
This omits the LD-decay term because the scored variant is itself causal, but
it still carries mutation, migration, and AF-history interactions. -/
noncomputable def jointDirectCausalKernelAt {p q : ℕ}
    (m : CrossPopulationGenerationalModel p q) (t : ℕ) (i : Fin p) (j : Fin q) : ℝ :=
  m.popGen.mutationSharedRetentionAt t *
    tagAlleleFreqRetentionAt m t i *
    causalAlleleFreqRetentionAt m t j

@[simp] theorem jointDirectCausalKernelAt_uses_af_mutation {p q : ℕ}
    (m : CrossPopulationGenerationalModel p q) (t : ℕ) (i : Fin p) (j : Fin q) :
    jointDirectCausalKernelAt m t i j =
      m.popGen.mutationSharedRetentionAt t *
            tagAlleleFreqRetentionAt m t i *
        causalAlleleFreqRetentionAt m t j := by
  simp [jointDirectCausalKernelAt]

/-- Joint locus-level transport kernel for ancestry-specific proxy tagging.
This carries the full interaction between LD retention, mutation/migration
sharing, and source/target allele-frequency history.

    The LD factor is the model's supplied `ldRetentionAt`, read at the
    tag-causal separation; see `jointTagLDKernelAt` for what that slot replaced
    and what a product of retentions still claims.

    Empirical status: **UNTESTED**. -/
noncomputable def jointProxyTaggingKernelAt {p q : ℕ}
    (m : CrossPopulationGenerationalModel p q) (t : ℕ) (i : Fin p) (j : Fin q) : ℝ :=
  m.ldRetentionAt t (m.tagCausalDistance i j) *
    m.popGen.mutationSharedRetentionAt t *
    tagAlleleFreqRetentionAt m t i *
    causalAlleleFreqRetentionAt m t j

@[simp] theorem jointProxyTaggingKernelAt_uses_ld_tagging_af_mutation {p q : ℕ}
    (m : CrossPopulationGenerationalModel p q) (t : ℕ) (i : Fin p) (j : Fin q) :
    jointProxyTaggingKernelAt m t i j =
      m.ldRetentionAt t (m.tagCausalDistance i j) *
        m.popGen.mutationSharedRetentionAt t *
            tagAlleleFreqRetentionAt m t i *
        causalAlleleFreqRetentionAt m t j := by
  simp [jointProxyTaggingKernelAt]

/-- Joint locus-level kernel for target-only novel direct causal links. Novel
target-specific causal variants accumulate with mutation history, are diluted by
migration, and still depend on target allele-frequency matching.

    Empirical status: UNTESTED. -/
noncomputable def jointNovelDirectCausalKernelAt {p q : ℕ}
    (m : CrossPopulationGenerationalModel p q) (t : ℕ) (i : Fin p) (j : Fin q) : ℝ :=
  novelVariantInnovationAt m.popGen t *
    tagAlleleFreqRetentionAt m t i *
    causalAlleleFreqRetentionAt m t j

@[simp] theorem jointNovelDirectCausalKernelAt_uses_af_mutation {p q : ℕ}
    (m : CrossPopulationGenerationalModel p q) (t : ℕ) (i : Fin p) (j : Fin q) :
    jointNovelDirectCausalKernelAt m t i j =
      novelVariantInnovationAt m.popGen t *
            tagAlleleFreqRetentionAt m t i *
        causalAlleleFreqRetentionAt m t j := by
  simp [jointNovelDirectCausalKernelAt]

/-- Joint locus-level kernel for target-only novel proxy tagging. This carries
both local LD structure and mutation-generated novelty, rather than just
attenuating the shared source proxy surface.

    The LD factor is the model's supplied `ldRetentionAt`, read at the
    tag-causal separation; see `jointTagLDKernelAt` for what that slot replaced.

    Empirical status: **UNTESTED**. -/
noncomputable def jointNovelProxyTaggingKernelAt {p q : ℕ}
    (m : CrossPopulationGenerationalModel p q) (t : ℕ) (i : Fin p) (j : Fin q) : ℝ :=
  m.ldRetentionAt t (m.tagCausalDistance i j) *
    novelVariantInnovationAt m.popGen t *
    tagAlleleFreqRetentionAt m t i *
    causalAlleleFreqRetentionAt m t j

@[simp] theorem jointNovelProxyTaggingKernelAt_uses_ld_af_mutation_migration {p q : ℕ}
    (m : CrossPopulationGenerationalModel p q) (t : ℕ) (i : Fin p) (j : Fin q) :
    jointNovelProxyTaggingKernelAt m t i j =
      m.ldRetentionAt t (m.tagCausalDistance i j) *
        novelVariantInnovationAt m.popGen t *
            tagAlleleFreqRetentionAt m t i *
        causalAlleleFreqRetentionAt m t j := by
  simp [jointNovelProxyTaggingKernelAt]

/-- Time-varying target LD among scored SNPs. This incorporates recombination,
drift (`F_ST`), mutation/migration-driven shared variation, and explicit target
tag-SNP allele-frequency drift. -/
noncomputable def sigmaTagTargetAt {p q : ℕ}
    (m : CrossPopulationGenerationalModel p q) (t : ℕ) :
    Matrix (Fin p) (Fin p) ℝ :=
  fun i j ↦
    m.sigmaTagSource i j * jointTagLDKernelAt m t i j

/-- Time-varying target tag-to-causal alignment. This is the explicit tagging
quality surface, driven by LD decay, allele-frequency divergence, mutation,
migration, and the underlying source tag-causal alignment. -/
noncomputable def directCausalTargetAt {p q : ℕ}
    (m : CrossPopulationGenerationalModel p q) (t : ℕ) :
    Matrix (Fin p) (Fin q) ℝ :=
  fun i j ↦
    m.directCausalSource i j * jointDirectCausalKernelAt m t i j

/-- Time-varying target-only novel direct-causal alignment.

    Empirical status: UNTESTED. -/
noncomputable def novelDirectCausalTargetAt {p q : ℕ}
    (m : CrossPopulationGenerationalModel p q) (t : ℕ) :
    Matrix (Fin p) (Fin q) ℝ :=
  fun i j ↦
    m.novelDirectCausalTemplate i j * jointNovelDirectCausalKernelAt m t i j

/-- Time-varying proxy-tagging alignment. Unlike directly scored causal
variants, this channel is degraded by LD decay between the scored tag and the
unscored causal variant. -/
noncomputable def proxyTaggingTargetAt {p q : ℕ}
    (m : CrossPopulationGenerationalModel p q) (t : ℕ) :
    Matrix (Fin p) (Fin q) ℝ :=
  fun i j ↦
    m.proxyTaggingSource i j * jointProxyTaggingKernelAt m t i j

/-- Time-varying target-only novel proxy-tagging alignment created after
divergence. -/
noncomputable def novelProxyTaggingTargetAt {p q : ℕ}
    (m : CrossPopulationGenerationalModel p q) (t : ℕ) :
    Matrix (Fin p) (Fin q) ℝ :=
  fun i j ↦
    m.novelProxyTaggingTemplate i j * jointNovelProxyTaggingKernelAt m t i j

/-- Time-varying target tag-to-causal alignment is the sum of a direct-causal
channel, a target-only novel direct-causal channel, a proxy-tagging channel,
and a target-only novel proxy-tagging channel. Only the proxy channels carry
LD-decay erosion. -/
noncomputable def sigmaTagCausalTargetAt {p q : ℕ}
    (m : CrossPopulationGenerationalModel p q) (t : ℕ) :
    Matrix (Fin p) (Fin q) ℝ :=
  directCausalTargetAt m t +
    (novelDirectCausalTargetAt m t +
      (proxyTaggingTargetAt m t + novelProxyTaggingTargetAt m t))

/-- Projection of the source effect vector through the generation-indexed
target tagging surface. This isolates what would transport if target causal
effects were identical to source effects.

    Regime: standardized variants; the LD operator is the tag-by-causal
    cross-covariance and the vector it acts on is an effect vector on the causal
    coordinates.

    Empirical status: **VALIDATED** (`simcov/battery_bulk32.py`). What is on
    trial is the PROJECTION ITSELF -- that applying the LD cross-covariance to a
    causal effect vector yields the MARGINAL effects an association scan
    actually estimates. That is a fact about genotypes, not about algebra: the
    oracle regresses simulated phenotypes on simulated genotypes, one univariate
    regression per variant, and never forms the LD matrix from the effects.

    40 variants with AR(1) LD (`Σᵢⱼ = ρ^|i-j|`, `ρ` swept 0.4 to 0.9), four
    causal among them, 400000 individuals. Agreement is read at the
    WORST-FITTING coordinate of the 40 rather than on an average that would hide
    a local miss, with the error bar inflated by `√(2 log 40)` for that
    selection: worst cell 1.16 sems.

    Power: two competing forms ride on the same cells. Dropping the projection
    entirely -- taking the marginal effect to BE the causal effect -- misses by
    up to 61 sems; applying the projection TWICE, which is what an `r` versus
    `r²` confusion looks like at the vector level, is FALSIFIED at 539 sems.
    Control: the realised genetic variance reproduces `βᵀΣβ` on the same run,
    passing at 0.29 sems.

    The measurement is of the shared shape `Σ.mulVec ·`, so it establishes the
    projection for every body of this family; what differs between them is
    WHICH effect vector is projected, and those vectors carry their own
    statuses. -/
noncomputable def targetSourceEffectProjectionAt {p q : ℕ}
    (m : CrossPopulationGenerationalModel p q) (t : ℕ) : Fin p → ℝ :=
  (sigmaTagCausalTargetAt m t).mulVec m.betaSource

/-- Incremental generation-indexed projection induced purely by per-locus
target-effect heterogeneity, including target-only novel causal effects.

    Regime: standardized variants; the LD operator is the tag-by-causal
    cross-covariance and the vector it acts on is an effect vector on the causal
    coordinates.

    Empirical status: **VALIDATED** (`simcov/battery_bulk32.py`). What is on
    trial is the PROJECTION ITSELF -- that applying the LD cross-covariance to a
    causal effect vector yields the MARGINAL effects an association scan
    actually estimates. That is a fact about genotypes, not about algebra: the
    oracle regresses simulated phenotypes on simulated genotypes, one univariate
    regression per variant, and never forms the LD matrix from the effects.

    40 variants with AR(1) LD (`Σᵢⱼ = ρ^|i-j|`, `ρ` swept 0.4 to 0.9), four
    causal among them, 400000 individuals. Agreement is read at the
    WORST-FITTING coordinate of the 40 rather than on an average that would hide
    a local miss, with the error bar inflated by `√(2 log 40)` for that
    selection: worst cell 1.16 sems.

    Power: two competing forms ride on the same cells. Dropping the projection
    entirely -- taking the marginal effect to BE the causal effect -- misses by
    up to 61 sems; applying the projection TWICE, which is what an `r` versus
    `r²` confusion looks like at the vector level, is FALSIFIED at 539 sems.
    Control: the realised genetic variance reproduces `βᵀΣβ` on the same run,
    passing at 0.29 sems.

    The measurement is of the shared shape `Σ.mulVec ·`, so it establishes the
    projection for every body of this family; what differs between them is
    WHICH effect vector is projected, and those vectors carry their own
    statuses. -/
noncomputable def targetEffectHeterogeneityProjectionAt {p q : ℕ}
    (m : CrossPopulationGenerationalModel p q) (t : ℕ) : Fin p → ℝ :=
  (sigmaTagCausalTargetAt m t).mulVec
    (m.targetEffectHeterogeneityAt t + m.novelCausalEffectTargetAt t)


/-- The static exact metric model obtained by slicing the generational state at
generation `t`. This is the canonical bridge from explicit population-genetic
dynamics to deployed metrics. -/
noncomputable def CrossPopulationGenerationalModel.toMetricModelAt {p q : ℕ}
    (m : CrossPopulationGenerationalModel p q) (t : ℕ) :
    CrossPopulationMetricModel p q where
  beta := Pop.pair (m.betaSource) (m.betaSource + m.targetEffectHeterogeneityAt t)
  sigmaTag := Pop.pair (m.sigmaTagSource) (sigmaTagTargetAt m t)
  directCausal := Pop.pair (m.directCausalSource) (directCausalTargetAt m t)
  proxyTagging := Pop.pair (m.proxyTaggingSource) (proxyTaggingTargetAt m t)
  contextCross := Pop.pair (m.contextCrossSource) (m.contextCrossTargetAt t)
  outcomeVariance :=
    Pop.pair (m.outcome.sourceOutcomeVariance) (m.outcome.targetOutcomeVarianceAt t)
  novelDirectCausal := Pop.pair 0 (novelDirectCausalTargetAt m t)
  novelProxyTagging := Pop.pair 0 (novelProxyTaggingTargetAt m t)
  novelCausalEffect := Pop.pair 0 (m.novelCausalEffectTargetAt t)
  novelUntaggablePhenotypeVarianceTarget := m.outcome.novelUntaggablePhenotypeVarianceAt t
  targetPrevalence := m.outcome.targetPrevalenceAt t
  novelUntaggablePhenotypeVarianceTarget_nonneg :=
    m.outcome.novelUntaggablePhenotypeVariance_nonneg t
  targetPrevalence_pos := m.outcome.targetPrevalence_pos t
  targetPrevalence_lt_one := m.outcome.targetPrevalence_lt_one t
  novelDirectCausal_source := rfl
  novelProxyTagging_source := rfl
  novelCausalEffect_source := rfl
  -- The two cases are exactly the model's own positivity fields; `simp_all`
  -- reduces the `Pop.pair` but has no way to discharge them.
  outcomeVariance_pos := by
    intro P
    cases P
    · exact m.outcome.sourceOutcomeVariance_pos
    · exact m.outcome.targetOutcomeVariance_pos t

/-- At each generation, the target tagging projection splits into the part that
would be obtained under source-stable effects plus a separate projection of the
locus-resolved target-effect heterogeneity. -/
theorem targetTaggingProjectionAtGeneration_eq_source_effect_plus_effectHeterogeneity
    {p q : ℕ} (m : CrossPopulationGenerationalModel p q) (t : ℕ) :
    taggingProjection (m.toMetricModelAt t) Pop.target =
      targetSourceEffectProjectionAt m t +
        targetEffectHeterogeneityProjectionAt m t := by
  simpa [CrossPopulationGenerationalModel.toMetricModelAt,
    targetSourceEffectProjectionAt, targetEffectHeterogeneityProjectionAt,
    targetSourceEffectProjection, targetEffectHeterogeneityProjection,
    targetEffectHeterogeneity, totalEffect, sigmaTagCausalTargetAt, add_assoc]
    using taggingProjection_target_eq_source_effect_plus_effectHeterogeneity
      (m.toMetricModelAt t)

/-- With any imperfect source tagging (`ρS > 0`), worsening target tagging (`ρT < ρS`)
strictly lowers portability when drift terms are fixed. -/
theorem portability_ratio_with_target_ld_decay_any_source
    (V_A V_E fstS fstT rhoS rhoT : ℝ)
    (hVA : 0 < V_A) (hVE : 0 < V_E)
    (hfstS_lt_one : fstS < 1) (hfstT_lt_one : fstT < 1)
    (h_rho : 0 < rhoT ∧ rhoT < rhoS) :
    PopGen.TransportedMetrics.r2FromSignalVariance (realWorldPGSVariance V_A fstT rhoT) V_E /
      PopGen.TransportedMetrics.r2FromSignalVariance (realWorldPGSVariance V_A fstS rhoS) V_E <
    PopGen.TransportedMetrics.r2FromSignalVariance (realWorldPGSVariance V_A fstT rhoS) V_E /
      PopGen.TransportedMetrics.r2FromSignalVariance (realWorldPGSVariance V_A fstS rhoS) V_E := by
  rcases h_rho with ⟨hRhoT_pos, hRhoT_lt_rhoS⟩
  have hRhoS_pos : 0 < rhoS := lt_trans hRhoT_pos hRhoT_lt_rhoS
  have hu_pos : 0 < (1 - fstT) * V_A := mul_pos (by linarith) hVA
  -- Numerator: rhoT < rhoS implies R²(rhoT·u) < R²(rhoS·u)
  have h_num_lt :
      PopGen.TransportedMetrics.r2FromSignalVariance (realWorldPGSVariance V_A fstT rhoT) V_E <
        PopGen.TransportedMetrics.r2FromSignalVariance (realWorldPGSVariance V_A fstT rhoS) V_E
          := by
    apply expectedR2_strictMono_nonneg V_E _ _ hVE
    · unfold realWorldPGSVariance
      exact le_of_lt (by simpa [mul_assoc] using mul_pos hRhoT_pos hu_pos)
    · simpa [realWorldPGSVariance, mul_assoc] using
        mul_lt_mul_of_pos_right hRhoT_lt_rhoS hu_pos
  -- Denominator positivity
  have hsource_sig_pos : 0 < realWorldPGSVariance V_A fstS rhoS := by
    unfold realWorldPGSVariance
    simpa [mul_assoc] using mul_pos (mul_pos hRhoS_pos (by linarith : 0 < 1 - fstS)) hVA
  have h_den_pos : 0 < PopGen.TransportedMetrics.r2FromSignalVariance (realWorldPGSVariance V_A fstS
    rhoS) V_E := by
    unfold PopGen.TransportedMetrics.r2FromSignalVariance Descent.Core.share
    exact div_pos hsource_sig_pos (by linarith)
  -- Divide both sides by positive denominator
  simpa [div_eq_mul_inv] using
    mul_lt_mul_of_pos_right h_num_lt (inv_pos.mpr h_den_pos)

/-- With source perfectly tagged (`ρ_S = 1`), adding target LD decay (`ρ_T < 1`)
strictly lowers the portability ratio versus drift-only transport. -/
theorem portability_ratio_with_ld_decay
    (V_A V_E fstS fstT rhoS rhoT : ℝ)
    (hVA : 0 < V_A) (hVE : 0 < V_E)
    (hfst : fstS < fstT) (hfstT_lt_one : fstT < 1) (hRhoS : rhoS = 1)
    (h_rho : 0 < rhoT ∧ rhoT < rhoS) :
    PopGen.TransportedMetrics.r2FromSignalVariance (realWorldPGSVariance V_A fstT rhoT) V_E /
      PopGen.TransportedMetrics.r2FromSignalVariance (realWorldPGSVariance V_A fstS rhoS) V_E <
    PopGen.TransportedMetrics.r2FromSignalVariance (presentDayPGSVariance V_A fstT) V_E /
      PopGen.TransportedMetrics.r2FromSignalVariance (presentDayPGSVariance V_A fstS) V_E := by
  rcases h_rho with ⟨hRhoT_pos, hRhoT_lt_rhoS⟩
  have hfstS_lt_one : fstS < 1 := lt_trans hfst hfstT_lt_one
  have hTargetPos : 0 < V_A * (1 - fstT) := by
    have : 0 < 1 - fstT := by linarith
    exact mul_pos hVA this
  have hTarget_nonneg : 0 ≤ V_A * (1 - fstT) := le_of_lt hTargetPos
  have hRhoT_lt_one : rhoT < 1 := by simpa [hRhoS] using hRhoT_lt_rhoS
  have hRealTarget_lt :
      realWorldPGSVariance V_A fstT rhoT < presentDayPGSVariance V_A fstT := by
    have hscaled :
        rhoT * (V_A * (1 - fstT)) < 1 * (V_A * (1 - fstT)) :=
      mul_lt_mul_of_pos_right hRhoT_lt_one hTargetPos
    simpa [realWorldPGSVariance, presentDayPGSVariance, pgsVarianceFromHet, Descent.Core.product,
      mul_assoc, mul_left_comm, mul_comm] using hscaled
  have hR2Target_lt :
      PopGen.TransportedMetrics.r2FromSignalVariance (realWorldPGSVariance V_A fstT rhoT) V_E <
        PopGen.TransportedMetrics.r2FromSignalVariance (presentDayPGSVariance V_A fstT) V_E := by
    apply expectedR2_strictMono_nonneg V_E
    · exact hVE
    · unfold realWorldPGSVariance
      have hRhoTerm_nonneg : 0 ≤ rhoT * (1 - fstT) := by
        have hOneMinus_nonneg : 0 ≤ 1 - fstT := by linarith
        exact mul_nonneg (le_of_lt hRhoT_pos) hOneMinus_nonneg
      exact mul_nonneg hRhoTerm_nonneg (le_of_lt hVA)
    · exact hRealTarget_lt
  have hSourcePos : 0 < presentDayPGSVariance V_A fstS := by
    unfold presentDayPGSVariance pgsVarianceFromHet Descent.Core.product
    have h1s : 0 < 1 - fstS := by linarith
    exact mul_pos hVA h1s
  have hR2Source_pos : 0 < PopGen.TransportedMetrics.r2FromSignalVariance (presentDayPGSVariance V_A
    fstS) V_E := by
    unfold PopGen.TransportedMetrics.r2FromSignalVariance Descent.Core.share
    have hden : 0 < presentDayPGSVariance V_A fstS + V_E := by linarith [hSourcePos, hVE]
    exact div_pos hSourcePos hden
  have hL :
      PopGen.TransportedMetrics.r2FromSignalVariance (realWorldPGSVariance V_A fstT rhoT) V_E /
          PopGen.TransportedMetrics.r2FromSignalVariance (presentDayPGSVariance V_A fstS) V_E <
        PopGen.TransportedMetrics.r2FromSignalVariance (presentDayPGSVariance V_A fstT) V_E /
          PopGen.TransportedMetrics.r2FromSignalVariance (presentDayPGSVariance V_A fstS) V_E := by
    have hmul :
        PopGen.TransportedMetrics.r2FromSignalVariance (realWorldPGSVariance V_A fstT rhoT) V_E *
          (PopGen.TransportedMetrics.r2FromSignalVariance
            (presentDayPGSVariance V_A fstS) V_E)⁻¹ <
          PopGen.TransportedMetrics.r2FromSignalVariance (presentDayPGSVariance V_A fstT) V_E *
            (PopGen.TransportedMetrics.r2FromSignalVariance
              (presentDayPGSVariance V_A fstS) V_E)⁻¹ :=
      mul_lt_mul_of_pos_right hR2Target_lt (inv_pos.mpr hR2Source_pos)
    simpa [div_eq_mul_inv] using hmul
  -- `hL` is phrased with `presentDayPGSVariance`; with `rhoS = 1` the goal
  -- normalises to `(1 - fst) * V_A`. `presentDayPGSVariance_eq_one_sub_fst_mul`
  -- is exactly that equation, so it is the bridge -- not a guessed simp set.
  simpa [hRhoS, realWorldPGSVariance, presentDayPGSVariance_eq_one_sub_fst_mul]
    using hL

/-- General LD-aware portability theorem without assuming perfect source tagging.
Under `0 < rhoT < rhoS ≤ 1` and `fstS < fstT < 1`, the LD+drift portability ratio
is strictly below the drift-only portability ratio. -/
theorem portability_ratio_with_ld_decay_general
    (V_A V_E fstS fstT rhoS rhoT : ℝ)
    (hVA : 0 < V_A) (hVE : 0 < V_E)
    (hfst : fstS < fstT) (hfstT_lt_one : fstT < 1)
    (hRhoS : rhoS = 1)
    (h_rho : 0 < rhoT ∧ rhoT < rhoS ∧ rhoS ≤ 1) :
    PopGen.TransportedMetrics.r2FromSignalVariance (realWorldPGSVariance V_A fstT rhoT) V_E /
      PopGen.TransportedMetrics.r2FromSignalVariance (realWorldPGSVariance V_A fstS rhoS) V_E <
    PopGen.TransportedMetrics.r2FromSignalVariance (presentDayPGSVariance V_A fstT) V_E /
      PopGen.TransportedMetrics.r2FromSignalVariance (presentDayPGSVariance V_A fstS) V_E := by
  rcases h_rho with ⟨hRhoT_pos, hRhoT_lt_rhoS, _⟩
  exact portability_ratio_with_ld_decay V_A V_E fstS fstT rhoS rhoT
    hVA hVE hfst hfstT_lt_one hRhoS ⟨hRhoT_pos, hRhoT_lt_rhoS⟩

/-- If target `R²` is strictly below source `R²`, the portability ratio is strictly below `1`. -/
theorem div_lt_one_of_lt_of_pos
    (srcR2 tgtR2 : ℝ)
    (hsrc_pos : 0 < srcR2)
    (hdrop : tgtR2 < srcR2) :
    tgtR2 / srcR2 < 1 :=
  (_root_.div_lt_iff₀ hsrc_pos).2 (by simpa using hdrop)

/-- Headline portability theorem: positive drift implies `R²` ratio is strictly below `1`. -/
theorem portability_ratio_lt_one_of_positive_drift
    (V_A V_E fstS fstT : ℝ)
    (hVA : 0 < V_A) (hVE : 0 < V_E)
    (hfst : fstS < fstT)
    (hfstT_le_one : fstT ≤ 1) :
    presentDayR2 V_A V_E fstT / presentDayR2 V_A V_E fstS < 1 := by
  -- Source positivity is not a hypothesis: `fstS < fstT ≤ 1` already forces
  -- `0 < 1 - fstS`, and the signal variance is `V_A * (1 - fstS)`.
  have hsrc_pos : 0 < presentDayR2 V_A V_E fstS := by
    unfold presentDayR2 PopGen.TransportedMetrics.r2FromSignalVariance Descent.Core.share
    have hv_pos : 0 < presentDayPGSVariance V_A fstS := by
      unfold presentDayPGSVariance pgsVarianceFromHet Descent.Core.product
      have h_one_minus : 0 < 1 - fstS := by linarith
      exact mul_pos hVA h_one_minus
    exact div_pos hv_pos (by linarith)
  have hdrop : presentDayR2 V_A V_E fstT < presentDayR2 V_A V_E fstS :=
    drift_degrades_R2 V_A V_E fstS fstT hVA hVE hfst hfstT_le_one
  exact div_lt_one_of_lt_of_pos (presentDayR2 V_A V_E fstS)
    (presentDayR2 V_A V_E fstT) hsrc_pos hdrop

/-- Neutral allele-frequency benchmark `R²`.

This section is intentionally limited to the coarse heterozygosity/F_ST chart.
It is a neutral allele-frequency benchmark, not a mechanistic cross-population
portability law. Claims about deployed portability must instead use the
explicit SNP/LD/alignment state in `CrossPopulationMetricModel`. -/
noncomputable def targetR2FromNeutralAFBenchmark
    (V_A V_E fstTarget : ℝ) : ℝ :=
  presentDayR2 V_A V_E fstTarget

/-- Within the neutral allele-frequency benchmark, the target/source `R²` ratio
is strictly below `1` when target `F_ST` exceeds source `F_ST`. -/
theorem targetR2FromNeutralAFBenchmark_ratio_lt_one
    (V_A V_E fstSource fstTarget : ℝ)
    (hVA : 0 < V_A) (hVE : 0 < V_E)
    (h_fst : fstSource < fstTarget)
    (h_fst_bounds : 0 ≤ fstSource ∧ fstTarget < 1) :
    targetR2FromNeutralAFBenchmark V_A V_E fstTarget / presentDayR2 V_A V_E fstSource < 1 := by
  have hsrc_pos : 0 < presentDayR2 V_A V_E fstSource := by
    unfold presentDayR2 PopGen.TransportedMetrics.r2FromSignalVariance Descent.Core.share
    have hv_pos : 0 < presentDayPGSVariance V_A fstSource := by
      unfold presentDayPGSVariance pgsVarianceFromHet Descent.Core.product
      have h_one_minus : 0 < 1 - fstSource := by linarith [h_fst_bounds.2, h_fst]
      exact mul_pos hVA h_one_minus
    exact div_pos hv_pos (by linarith)
  have hdrop :
      targetR2FromNeutralAFBenchmark V_A V_E fstTarget < presentDayR2 V_A V_E fstSource := by
    simpa [targetR2FromNeutralAFBenchmark] using
      drift_degrades_R2 V_A V_E fstSource fstTarget hVA hVE h_fst (le_of_lt h_fst_bounds.2)
  exact div_lt_one_of_lt_of_pos
    (presentDayR2 V_A V_E fstSource)
    (targetR2FromNeutralAFBenchmark V_A V_E fstTarget)
    hsrc_pos hdrop

/-- Within the neutral allele-frequency benchmark, target `R²` is below source
`R²` once target `F_ST` exceeds source `F_ST`. -/
theorem targetR2_lt_source_from_neutralAF_benchmark
    (V_A V_E fstSource fstTarget : ℝ)
    (hVA : 0 < V_A) (hVE : 0 < V_E)
    (h_fst : fstSource < fstTarget)
    (h_fst_bounds : 0 ≤ fstSource ∧ fstTarget < 1) :
    targetR2FromNeutralAFBenchmark V_A V_E fstTarget < presentDayR2 V_A V_E fstSource := by
  simpa [targetR2FromNeutralAFBenchmark] using
    drift_degrades_R2 V_A V_E fstSource fstTarget hVA hVE h_fst (le_of_lt h_fst_bounds.2)

/-! **Deleted: `neutralAFBenchmarkRatio fstSource fstTarget = (1 - fstTarget)/(1 - fstSource)`,
together with `neutralAFBenchmarkRatio_le_inv_one_sub_source`, `_nonneg`, `_lt_one`, `_self`,
and the `FstBounds` section of `Descent.Portability.PortabilityBounds` that was stated about it.**

These are absent on purpose. On asymmetric effective sizes the ratio form runs `-37%` to
`-74%` low, at nine to fifteen standard errors:

      T    NeA    NeB     fstS     fstT   het_B/het_A   se   ratio form   err
    500    200   2000   0.3577   0.0582     3.7862    0.2547    1.4662   -61.3%
   1000    200   2000   0.4860   0.1187     6.5409    0.3445    1.7147   -73.8%
   1000    500   5000   0.3165   0.0450     2.2220    0.0771    1.3972   -37.1%
   2000    300   3000   0.5611   0.1454     5.7238    0.2201    1.9472   -66.0%

A symmetric design cannot rescue it. With equal branch lengths both sides of the ratio
collapse to about `1`, so a symmetric test has no power to reject a wrong functional form,
and an agreement to `3.2%` measured that way is an artifact.
`Descent.DriftRegime.symmetric_design_has_no_power` proves that on any symmetric design
this form and its *square* are indistinguishable.

The defect is not a miscalibration, it is the wrong argument list. The observed ratio is
`2.2` to `6.5` and is driven by the tenfold ratio in effective size, not by `F_ST`:
heterozygosity is governed by `Nₑ` and the mutation floor `hetMutationFloor`, and `F_ST` is a
between-population variance ratio that does not determine either.

**The falsification needs no definition to state**, which is why it survives the deletion.
`benchmarkRatioForm_cannot_reach_measured` below states it about the expression written out,
and is the machine-checked form of "no argument brings this formula into the measured range".
A certificate that can only be stated about a name is hostage to that name.

Nothing replaces it. `hetRatioBetweenBranches` below is a clearly-labelled candidate for
testing, and is a function of the two effective sizes, the mutation rate and the horizon,
which is what the data say the quantity depends on. `DriftRegime.benchmarkRatio` is NOT
this quantity and carries none of this: measurement confirms that form to `-0.003%`, and
what fails there is a different quantity fed into its `fst` slot. -/

/-- **The measured value is outside the range of the heterozygosity-ratio-from-`F_ST` form,
stated about the expression rather than about a name.**

At the design point `fstSource = 0.3577` the form `(1 - fstT)/(1 - fstS)` is below `3` for
every target `F_ST` in range -- its supremum there is `1/(1 - 0.3577) = 1.557`. The measured
heterozygosity ratio at that point is `3.79 ± 0.25`, more than nine standard errors above
`3`. This is the falsification in a form that depends on neither the simulation being rerun
nor the definition continuing to exist: no choice of the free argument brings the expression
into the measured range. -/
theorem benchmarkRatioForm_cannot_reach_measured (fstTarget : ℝ)
    (h0 : 0 ≤ fstTarget) :
    (1 - fstTarget) / (1 - 3577 / 10000) < 3 := by
  rw [div_lt_iff₀ (by norm_num : (0:ℝ) < 1 - 3577 / 10000)]
  linarith

/-- **Candidate replacement, offered for testing and deliberately not
substituted.**

The ratio of present-day heterozygosities between two branches that started
from the same ancestral value, as a function of the two effective sizes, the
mutation rate and the horizon -- which is what the measurement says it depends
on. It reduces to `1` when the effective sizes agree, and unlike the deleted
`(1 - fstT)/(1 - fstS)` benchmark form it has the dynamic range the data
require: `hetRatioBetweenBranches_exceeds_benchmark_ceiling` puts it above `3`
at a two-generation, tenfold-`Nₑ` design point where the benchmark form is
capped at `1.557`.

    Regime: none baked in; the closed population is the `mu = 0` case, and the
    mutation floor enters through `hetTrajectory`.

    Empirical status: UNTESTED. This is written from the recurrence, not fitted
    to the four rows tabulated in the deletion note above, and the user has the
    simulation capability to adjudicate it. -/
noncomputable def hetRatioBetweenBranches (NeA NeB mu H₀ : ℝ) (t : ℕ) : ℝ :=
  hetTrajectory NeB mu H₀ t / hetTrajectory NeA mu H₀ t

/-- With a vanishing denominator Mathlib returns `0`, which is a value this quantity can also
take legitimately, so the branch is named rather than left to be inferred from the result. -/
theorem hetRatioBetweenBranches_at_zero_denominator_is_junk (NeA NeB mu H₀ : ℝ) (t : ℕ)
    (hzero : hetTrajectory NeA mu H₀ t = 0) :
    hetRatioBetweenBranches NeA NeB mu H₀ t = 0 := by
  unfold hetRatioBetweenBranches
  rw [hzero, div_zero]


/-- Equal effective sizes give a ratio of `1`, so the whole signal in this
quantity is the asymmetry in `Nₑ` -- the variable the falsified form omits. -/
theorem hetRatioBetweenBranches_self (Ne mu H₀ : ℝ) (t : ℕ)
    (h : hetTrajectory Ne mu H₀ t ≠ 0) :
    hetRatioBetweenBranches Ne Ne mu H₀ t = 1 :=
  div_self h

/-- **The candidate has the range the measurement needs and the falsified form
does not.**  At `Nₑ_A = 1`, `Nₑ_B = 5`, no mutation and two generations the
ratio is `81/25 = 3.24`, above the ceiling that
`benchmarkRatioForm_cannot_reach_measured` places on the benchmark form. -/
theorem hetRatioBetweenBranches_exceeds_benchmark_ceiling :
    3 < hetRatioBetweenBranches 1 5 0 1 2 := by
  unfold hetRatioBetweenBranches
  rw [hetTrajectory_of_no_mutation, hetTrajectory_of_no_mutation]
  norm_num

/-- The neutral allele-frequency benchmark target `R²` is definitionally the
literal present-day target `R²` in this coarse chart. -/
theorem targetR2FromNeutralAFBenchmark_eq_presentDayR2
    (V_A V_E fstTarget : ℝ) :
    targetR2FromNeutralAFBenchmark V_A V_E fstTarget =
      presentDayR2 V_A V_E fstTarget := by
  rfl

/-! The exact calibrated Bernoulli Brier risk `π(1-π)(1-r2)` is
`TransportedMetrics.calibratedBrier`. **Do not add a second definition here to expose the
concrete product for `unfold`** -- unfolding the one definition yields the same product,
so that argues against a wrapper, not for a copy. -/

/-- Exact calibrated Bernoulli Brier risk written directly in prevalence and
explained-risk coordinates. -/
abbrev brierFromR2 (π r2 : ℝ) : ℝ :=
  PopGen.TransportedMetrics.calibratedBrier π r2

/-! ### Liability-threshold primitives

These declarations precede every public profile that names the binary-trait
AUC. Lean checks declaration references in documentation as well as terms, so
placing the liability chart after its first consumer made the module fail even
though the eventual formula was present in the same file. -/

/-- Standard normal density, `φ(x) = exp(-x²/2)/√(2π)`. -/
noncomputable def standardNormalPdf (x : ℝ) : ℝ :=
  Real.exp (-x ^ 2 / 2) / Real.sqrt (2 * Real.pi)

/-- With a vanishing denominator Mathlib returns `0`, which is a value this quantity can also
take legitimately, so the branch is named rather than left to be inferred from the result. -/
theorem standardNormalPdf_at_zero_denominator_is_junk (x : ℝ)
    (hzero : Real.sqrt (2 * Real.pi) = 0) :
    standardNormalPdf x = 0 := by
  unfold standardNormalPdf
  rw [hzero, div_zero]


/-- **The mode height.** The density at the mean is the normalising constant, which pins the
constant a body with the wrong normalisation would miss. -/
theorem standardNormalPdf_zero :
    standardNormalPdf 0 = 1 / Real.sqrt (2 * Real.pi) := by
  unfold standardNormalPdf
  norm_num

/-- The liability threshold `T = Φ⁻¹(1 - K)` for prevalence `K`.

    Empirical status: **VALIDATED** (`simcov/battery_bulk43.py`, `group_a`).
    The observable is exact and needs no modelling: the empirical `(1-K)`
    quantile of 4×10⁶ standard-normal liabilities. Over `K` = 0.01, 0.05, 0.2,
    0.5, 0.8 the body predicts +2.32635, +1.64485, +0.84162, 0 and -0.84162
    against measured +2.32785 ± 0.00187, +1.64453 ± 0.00106, +0.84052 ±
    0.00071, -0.00094 ± 0.00063 and -0.84119 ± 0.00071 -- worst cell 1.54 sems
    at 0.13% relative.

    Power: `K` is swept from the far tail to above the median, so the threshold
    CHANGES SIGN across the design. The sign slip `Φ⁻¹(K)` -- which is what
    writing the tail the wrong way round produces -- misses by up to 3113 sems
    and 200% relative, and coincides with the body only at `K = 1/2` where both
    are zero. That is the one place the two readings are indistinguishable, and
    the design does not rest there.

    The competing form is recorded as a lead rather than a falsification
    because this run's control was DEGENERATE: it counted the tail mass above
    the MEASURED quantile, which is `K` by construction of a quantile and so
    cannot fail. The harness detected that. The MATCH above needs no control.

    REBUILT AND RE-RUN, and the numbers above are superseded by these. The
    battery this cites had never been committed: the verdict was real when it
    was produced and no reader could check it, which is the same standing as no
    verdict. `simcov/battery_bulk43.py` is now in the repository, was run against
    the design described above, and its results are committed beside it (group_a).
    MATCH at worst 0.91 sems (0.07% relative) over K = 0.01, 0.05, 0.2, 0.5, 0.8; the
    sign slip Phi^-1(K) is FALSIFIED at 3390 sems (200% relative). Control: the MEDIAN
    of the same draws, known to be 0 and independent of K -- the earlier run's control
    counted the tail mass above the MEASURED quantile, which is K by construction and
    could not fail.
    -/
noncomputable def liabilityThreshold (K : ℝ) : ℝ := Function.invFun Foundations.Phi (1 - K)

/-- Mean liability among cases, `i = φ(T)/K`.

    Empirical status: **VALIDATED**
    (`validation/empirical/simcov/battery_pgs.py`,
    `test_liability_moments`). Four million explicit standard-normal liabilities
    per cell with threshold ascertainment, mean taken among cases:

      K       this def   simulated            sems
      0.01     2.66521   2.66465±0.00156      0.36
      0.05     2.06271   2.06447±0.00084      2.10
      0.20     1.39981   1.39937±0.00052      0.85

    Power: the prediction spans 1.39981 to 2.66521 across the design. -/
noncomputable def liabilityCaseMean (K : ℝ) : ℝ :=
  standardNormalPdf (liabilityThreshold K) / K

/-- **The liability case mean at zero prevalence, named.** With no cases there is no case
distribution and the mean liability among cases is undefined; as prevalence falls the true value
diverges, since the surviving cases sit ever further into the tail. The divisor is zero and Lean
returns `0` -- the POPULATION mean liability, the value for a trait under no ascertainment at
all. Rare-disease work is exactly where prevalence approaches this branch. Consumers must require
`K ≠ 0`. -/
theorem liabilityCaseMean_zero_prevalence_is_junk :
    liabilityCaseMean 0 = 0 := by
  unfold liabilityCaseMean
  simp

/-- Mean liability among controls, `i_c = -i·K/(1-K)`.

    Empirical status: **VALIDATED**
    (`validation/empirical/simcov/battery_pgs.py`,
    `test_liability_moments`). Same runs, mean among controls:

      K       this def   simulated             sems
      0.01    -0.02692  -0.02796±0.00049      2.13
      0.05    -0.10856  -0.10775±0.00046      1.77
      0.20    -0.34995  -0.34918±0.00043      1.81

    Power: the prediction spans -0.34995 to -0.02692, a factor of thirteen. -/
noncomputable def liabilityControlMean (K : ℝ) : ℝ :=
  -liabilityCaseMean K * K / (1 - K)

/-- **The liability control mean at unit prevalence, named.** If everyone is a case there are no
controls and the control mean is undefined. The divisor `1 - K` is zero and Lean returns `0`, the
population mean, so a universally prevalent trait reports a control group sitting exactly at the
population average. Consumers must require `K ≠ 1`. -/
theorem liabilityControlMean_unit_prevalence_is_junk :
    liabilityControlMean 1 = 0 := by
  unfold liabilityControlMean
  simp

/-- Score variance among cases, `v₁ = 1 - R²·i·(i - T)`.

    Empirical status: **VALIDATED**, with the reading pinned
    (`validation/empirical/simcov/battery_pgs.py`,
    `test_liability_moments`). The design tested two candidate readings of what
    this variance is OF, and they are not close:

      K      r2     this def   var(PGS|case)/r2   var(liability|case)
      0.05   0.3     0.74142   0.74137 (0.02σ)    0.13822 (1381σ)
      0.20   0.3     0.76559   0.76419 (1.16σ)    0.21847 (1583σ)
      0.05   0.6     0.48285   0.48252 (0.22σ)    0.13745 (796σ)

    So this is the variance of the STANDARDISED SCORE among cases, not of the
    liability. The name alone does not say which, and a consumer that took the
    other reading would be wrong by a factor of five.

    Power: the prediction spans 0.48285 to 0.76559 across the design, and the
    rival reading -- the variance of the LIABILITY among cases rather than of the
    standardised score -- is carried on the same cells and rejected at 796 to
    1583 sems. -/
noncomputable def liabilityCaseVariance (r2 K : ℝ) : ℝ :=
  1 - r2 * liabilityCaseMean K * (liabilityCaseMean K - liabilityThreshold K)

/-- Reference evaluation: with no explained variance the case liability keeps unit variance. -/
theorem liabilityCaseVariance_at_zero_r2 (K : ℝ) : liabilityCaseVariance 0 K = 1 := by
  unfold liabilityCaseVariance
  ring


/-- Score variance among controls, `v₀ = 1 - R²·i_c·(i_c - T)`.

    Empirical status: **VALIDATED** (`validation/empirical/simcov/battery_rival01.py`).
    Explicit normal liabilities `g + e` with realised `r2 = Var(g)/Var(l)`, dichotomised at
    the threshold for prevalence `K`; the observable is the variance of the STANDARDISED score
    among controls, `Var(g | l ≤ T)/Var(g)`, with the control mean evaluated at the block's
    realised case fraction. 8 blocks of 500000 individuals:

      K       r2     this def   simulated            sems
      0.05    0.3     0.94293   0.94293±0.00021      0.01
      0.20    0.3     0.87490   0.87449±0.00031      1.32
      0.05    0.6     0.88586   0.88588±0.00016      0.10
      0.40    0.5     0.71145   0.71098±0.00060      0.77
      0.02    0.2     0.97926   0.97916±0.00020      0.47

    THE READING IS NOW PINNED BY MEASUREMENT, NOT BY ANALOGY. This docstring used to say the
    reading "is pinned the same way `liabilityCaseVariance`'s was" -- but that body was pinned
    by CARRYING its rival, and this one had inherited the sentence without the measurement.
    The rival is carried here: the variance of the LIABILITY among controls rather than of the
    standardised score, which is the same expression with `r2` set to one and is what a reader
    who took the other reading of the name would compute. It is rejected at 938.86 sems. Two
    further readings die on the same cells: the CASE formula applied to controls at 2466.89
    sems, and dropping the `-T` term at 654.08. The positive control -- the realised total
    liability variance, which the construction fixes at 1 -- passes at 0.92 sems. An earlier
    record (`validation/empirical/simcov/battery_max.py`, three cells) competed nothing and
    the ledger gates it UNINFORMATIVE.

    Power: the prediction spans 0.71145 to 0.97926 across the design, `K` swept twentyfold
    from 0.02 to 0.40 and `r2` threefold from 0.2 to 0.6, and three competing readings are
    rejected on those same cells at 654.08 to 2466.89 sems. -/
noncomputable def liabilityControlVariance (r2 K : ℝ) : ℝ :=
  1 - r2 * liabilityControlMean K * (liabilityControlMean K - liabilityThreshold K)

/-- And the control liability likewise. -/
theorem liabilityControlVariance_at_zero_r2 (K : ℝ) : liabilityControlVariance 0 K = 1 := by
  unfold liabilityControlVariance
  ring


/-- **The liability-threshold AUC**, with prevalence a required argument.

Empirical status: VALIDATED against 400 simulated PGS studies. Pooled RMSE is
`0.0121` with bias `-0.0007`, matching the independently measured `0.0120`
seed-to-seed noise floor.

Power: prevalence is the axis this chart has and the equal-variance Gaussian
one lacks, and the design sweeps it. At `R² = 0.3` the AUC this definition
predicts runs from `0.753` at prevalence `0.5` to `0.921` at prevalence
`0.001`, while a prevalence-free chart returns one number for that whole range.
The span is more than a sixth of the discriminable interval above chance, so a
chart missing the prevalence dependence cannot fit it. -/
noncomputable def liabilityThresholdAUCFromExplainedR2 (r2 K : ℝ) : ℝ :=
  Foundations.Phi ((liabilityCaseMean K - liabilityControlMean K) * Real.sqrt r2 /
    Real.sqrt (liabilityCaseVariance r2 K + liabilityControlVariance r2 K))

/-- A nonpositive total liability variance sends the square root to Mathlib's junk `0`, so the
whole argument of `Phi` divides by zero and the discrimination reads as `Phi 0`, chance. -/
theorem liabilityThresholdAUCFromExplainedR2_at_nonpositive_variance_is_junk (r2 K : ℝ)
    (hnonpos : liabilityCaseVariance r2 K + liabilityControlVariance r2 K ≤ 0) :
    liabilityThresholdAUCFromExplainedR2 r2 K = Foundations.Phi 0 := by
  unfold liabilityThresholdAUCFromExplainedR2
  rw [Real.sqrt_eq_zero_of_nonpos hnonpos, div_zero]


/-! **Deleted: `LiabilityThresholdRegime`.**

An *obligation* structure with no consumer is worse than an unused lemma. Its whole claim
is that somebody must discharge these conditions before using the formula, and nobody does,
so it reads as rigour from the outside while every real use site bypasses it.

Three of the seven fields are results rather than domain conditions, so any use of the
structure would import them unproved:

* `threshold_spec : Phi (liabilityThreshold K) = 1 - K`. Since `liabilityThreshold K` is
  `Function.invFun Phi (1 - K)`, this says `Phi` hits `1 - K`, i.e. that the standard
  normal CDF is onto `(0, 1)`. That is a theorem — continuity plus the limits at `±∞` plus
  the intermediate value theorem — and it is *derivable* from `prevalence_pos` and
  `prevalence_lt_one`, which is exactly why it should not have been assumed alongside
  them. It has since been proved: `Descent.Foundations.Probability` now carries
  `Phi_surjOn_Ioo` and its consumer form `Phi_invFun_eq`, so this field would today be a
  one-line corollary of the two prevalence bounds rather than an assumption. That removes
  the first of the three reasons this structure could not be reinstated honestly.
* `caseVariance_pos` and `controlVariance_pos`. These are not conditions a caller can
  choose to meet: `liabilityCaseVariance r2 K` is a closed formula in `r2` and `K`, so its
  positivity is true or false once those are fixed. Both follow from `0 ≤ r2 < 1` together
  with the truncated-normal bound `0 ≤ i·(i - T) ≤ 1` on the selection intensity, which is
  the standard fact that truncation cannot increase variance. That bound is a real result
  and the corpus does not have it.

Reinstating this regime honestly means proving those three, not restating them; one is now
proved and the two variance bounds are not. Until then, the four genuine domain conditions
(`0 < K < 1`, `0 ≤ r2 < 1`) are what the individual theorems below already take as explicit
hypotheses where they need them. -/

/-- Source Brier chart as a function of prevalence and source `R²`. -/
noncomputable def sourceBrierFromR2 (π r2Source : ℝ) : ℝ :=
  PopGen.TransportedMetrics.calibratedBrier π r2Source

/-- The source Brier chart is the canonical source Brier
specialization. -/
theorem sourceBrierFromR2_eq_transportedMetrics
    (π r2Source : ℝ) :
    sourceBrierFromR2 π r2Source =
      PopGen.TransportedMetrics.calibratedBrier π r2Source := by
  rfl

/-- Target calibrated Brier risk on the OBSERVED scale, from explicit target state.

**The name carries no claim of exactness, deliberately.** This computes
`PopGen.TransportedMetrics.calibratedBrier`, the linear chart. A name promising an exact
risk here reads, to anyone auditing by name rather than by body, as a target Brier route
that needs no attention -- and that is how the dichotomised profile kept a Gaussian risk
coordinate for as long as it did.

WHAT IS AND IS NOT EXACT HERE. Under the Bernoulli-mixing model -- a true conditional risk
with mean `π` and variance `π(1-π)·r2` -- the linear chart IS the exact calibrated Brier
risk, and `exactBrierRiskOfCalibrated_eq_exactCalibratedBrierRiskFromR2` below proves it
from the integral. That model reads `r2` on the OBSERVED scale. It is not the
liability-threshold model, where the explained fraction is a liability-scale one and the
exact risk is `PopGen.TransportedMetrics.liabilityBrierExact`'s `Φ₂` curve; for a
dichotomised trait the body to call is `targetLiabilityBrierFromNeutralAFBenchmark`. The
two agree at `r2 = 0` and `r2 = 1` and nowhere between, which is why two anchor theorems
could not tell them apart. -/
noncomputable def targetCalibratedBrierRisk
    (π V_A V_E fstTarget : ℝ) : ℝ :=
  PopGen.TransportedMetrics.calibratedBrier π
    (targetR2FromNeutralAFBenchmark V_A V_E fstTarget)

/-- Neutral allele-frequency benchmark target Brier map used by the dashboard
(`Brier(R²_target)`). -/
noncomputable def targetBrierFromNeutralAFBenchmark
    (π V_A V_E fstTarget : ℝ) : ℝ :=
  targetCalibratedBrierRisk π V_A V_E fstTarget

/-- Canonical bundled deployed metrics under the neutral allele-frequency
benchmark state.

**FOR A CONTINUOUS OUTCOME. On a dichotomised trait this record is internally
inconsistent, and that inconsistency is the clearest statement of the defect in this
family:** it takes a prevalence `π`, uses it to compute the Brier risk, and then computes
the AUC with a formula that has no prevalence argument at all. The same record therefore
treats the trait as binary for one metric and as continuous for another.

`neutralAFBenchmarkLiabilityMetricProfile` is the dichotomised-trait version, which spends
the `π` it was already given on both. -/
noncomputable def neutralAFBenchmarkMetricProfile
    (π V_A V_E fstTarget : ℝ) : PopGen.TransportedMetrics.Profile :=
  PopGen.TransportedMetrics.profileFromSignalVariance π V_E (presentDayPGSVariance V_A fstTarget)

/-- The bundled neutral allele-frequency benchmark metrics reproduce the file's public
`R²`, AUC, and Brier surfaces exactly. -/
theorem neutralAFBenchmarkMetricProfile_eq
    (π V_A V_E fstTarget : ℝ) :
    neutralAFBenchmarkMetricProfile π V_A V_E fstTarget =
      { r2 := targetR2FromNeutralAFBenchmark V_A V_E fstTarget
      , auc := presentDayEqualVarianceGaussianAUC V_A V_E fstTarget
      , brier := targetBrierFromNeutralAFBenchmark π V_A V_E fstTarget } := by
  ext
  · change
      PopGen.TransportedMetrics.r2FromSignalVariance (presentDayPGSVariance V_A fstTarget) V_E =
        targetR2FromNeutralAFBenchmark V_A V_E fstTarget
    unfold targetR2FromNeutralAFBenchmark PopGen.TransportedMetrics.r2FromSignalVariance
      presentDayR2
    rfl
  · change
      equalVarianceGaussianAUCFromSignalVariance (presentDayPGSVariance V_A
          fstTarget) V_E =
        presentDayEqualVarianceGaussianAUC V_A V_E fstTarget
    rfl
  · change
      PopGen.TransportedMetrics.calibratedBrier π
        (PopGen.TransportedMetrics.r2FromSignalVariance (presentDayPGSVariance V_A fstTarget) V_E) =
        targetBrierFromNeutralAFBenchmark π V_A V_E fstTarget
    -- `TransportedMetrics.calibratedBrier` was named TWICE in this list. The
    -- first occurrence unfolds it; the second then fails, because by that
    -- point the constant is gone from the goal. `unfold` is not idempotent --
    -- it errors when a name is already absent rather than succeeding vacuously.
    unfold targetBrierFromNeutralAFBenchmark targetCalibratedBrierRisk
      PopGen.TransportedMetrics.calibratedBrier targetR2FromNeutralAFBenchmark
      PopGen.TransportedMetrics.r2FromSignalVariance
      presentDayR2
    rfl

/-- Full neutral allele-frequency benchmark AUC degradation theorem:
strictly higher drift implies strictly lower exact target AUC. -/
theorem targetAUC_lt_source_of_neutralAF_benchmark
    (V_A V_E fstSource fstTarget : ℝ)
    (hVA : 0 < V_A) (hVE : 0 < V_E)
    (h_fst : fstSource < fstTarget)
    (h_fst_bounds : 0 ≤ fstSource ∧ fstTarget < 1) :
    presentDayEqualVarianceGaussianAUC V_A V_E fstTarget <
      presentDayEqualVarianceGaussianAUC V_A V_E fstSource := by
  simpa [presentDayEqualVarianceGaussianAUC] using
    drift_degrades_equalVarianceGaussianAUC
      V_A V_E fstSource fstTarget hVA hVE h_fst (le_of_lt h_fst_bounds.2)

/-- Exact **equal-variance Gaussian** AUC as a function of SNR:
`AUC = Φ(√(snr/2))`.

    This is the AUC when cases and controls are two normals of equal variance
    separated by `√snr`. It is *not* the liability-threshold AUC, under which
    cases are a truncated tail, so the two distributions have different
    variances and the separation depends on where the truncation falls. It was
    named and documented as the liability AUC, twice as "exact".

    Numerical integration over the bivariate normal, agreeing with a
    4·10⁶-draw Monte Carlo to about `0.001`, puts the error at 3% to 26%,
    always understating, and worst where it matters most: at `R² = 0.3` the
    true AUC runs from `0.753` at prevalence `0.5` to `0.921` at `0.001`,
    while this returns one number per `R²` because it takes no prevalence.
    That missing argument is why no constant could repair it.

    Empirical status: VALIDATED for the equal-variance Gaussian model it now
    names; FALSIFIED as the liability-threshold AUC. The binary-trait
    counterpart is `liabilityThresholdAUCFromExplainedR2`, which takes the
    prevalence this one lacks and measures at RMSE `0.0121` where this form is
    biased `-0.068`.

    Power: this chart's own prediction spans `0.760250`, `0.921350`, `0.999797`
    and `1.000000` at `snr = 1, 4, 25, 100`, which is the design the
    two-Gaussian Monte Carlo of `DGP.equalVarianceGaussianAUCFromSignalVariance`
    was run on, at `200000` draws per point; the two are the same chart under
    `snr = vSignal / vNoise`, and
    `equalVarianceGaussianAUCFromSNR_eq_variance` is the theorem saying so, so
    the measurement is of this function rather than of a sibling formula. The
    prediction covers chance-to-perfect discrimination across that design. -/
noncomputable def equalVarianceGaussianAUCFromSNR (snr : ℝ) : ℝ :=
  Foundations.Phi (Real.sqrt (snr / 2))

/-- **equalVarianceGaussianAUCFromSNR at its junk point, named.** A negative signal-to-noise
ratio is inadmissible. `Real.sqrt` is junk-zero, so the AUC collapses to `Phi 0` -- chance
discrimination -- and a sign error upstream is reported as an uninformative but well-formed
classifier rather than as a domain violation. Consumers must exclude the argument that makes the
guard vanish. -/
theorem equalVarianceGaussianAUCFromSNR_negative_snr_is_junk :
    equalVarianceGaussianAUCFromSNR (-1) = Foundations.Phi 0 := by
  unfold equalVarianceGaussianAUCFromSNR
  rw [show (-1 : ℝ) / 2 = -(1 / 2) by ring, Real.sqrt_eq_zero_of_nonpos (by norm_num)]

/-- The signal-to-noise and signal/residual-variance parameterizations are exactly the
same closed-form chart.  This is algebra only: it does not assert that either chart is the
AUC of a biological process without a separately proved distributional model. -/
theorem equalVarianceGaussianAUCFromSNR_eq_variance
    (vSignal vEnv : ℝ) (h_env : vEnv ≠ 0) :
    equalVarianceGaussianAUCFromSNR (vSignal / vEnv) =
      equalVarianceGaussianAUCFromSignalVariance vSignal vEnv := by
  rw [equalVarianceGaussianAUCFromSignalVariance_eq_formula_of_ne_noise _ _ h_env]
  unfold equalVarianceGaussianAUCFromSNR
  congr 2
  rw [div_div, mul_comm]

/-! The variance form of the equal-variance Gaussian AUC is
`DGP.equalVarianceGaussianAUCFromSignalVariance`. **Do not write a second copy here.** Two
copies of an AUC formula can drift to opposite claims about which quantity they compute --
equal-variance Gaussian versus liability-threshold, which are not the same and differ by a
measured `-0.068` AUC -- and one definition cannot drift from itself.  The Lean definition
is deliberately only a chart; process-level applicability must be proved from an explicit
distributional model rather than supplied as a theorem-bearing parameter. -/

/-- With `vEnv = 1`, variance form equals SNR form exactly. -/
theorem equalVarianceGaussianAUCFromVariances_scaleOne (vSignal : ℝ) :
    equalVarianceGaussianAUCFromSignalVariance vSignal 1 =
      equalVarianceGaussianAUCFromSNR vSignal := by
  rw [equalVarianceGaussianAUCFromSignalVariance_eq_formula_of_ne_noise _ _ (by norm_num)]
  unfold equalVarianceGaussianAUCFromSNR
  ring_nf

/-- On nonnegative SNR, the **equal-variance Gaussian** AUC map is strictly increasing. -/
theorem equalVarianceGaussianAUCFromSNR_strictMonoOn_nonneg :
    StrictMonoOn equalVarianceGaussianAUCFromSNR (Set.Ici 0) := by
  intro x hx y hy hxy
  unfold equalVarianceGaussianAUCFromSNR
  apply Foundations.strictMono_Phi
  have hx2 : 0 ≤ x / 2 :=
    div_nonneg hx (by positivity)
  have hxy2 : x / 2 < y / 2 := by nlinarith
  exact Real.sqrt_lt_sqrt hx2 hxy2

/-- Equal-variance Gaussian AUC as a direct chart on deployed `R²`.

On `r2 < 1` this is `Φ (sqrt (r2 / (2 * (1 - r2))))`. At and above the perfect-prediction
boundary it is `1`, so totalized real division cannot turn `r2 = 1` into chance discrimination.
Values above one are outside the statistical model and are clamped rather than extrapolated.

This is not a liability-threshold AUC: that chart also requires prevalence.

    Empirical status: VALIDATED for the equal-variance Gaussian model on `[0, 1]`;
    FALSIFIED as the liability-threshold AUC.

    Power: on `r2 = 0.1, 0.3, 0.5, 0.8` this chart predicts `0.5932`, `0.6783`,
    `0.7602` and `0.9214`, which is `snr = r2 / (1 - r2)` fed to the SNR form it
    equals below the boundary. That span runs from near chance to near-perfect
    discrimination. The falsification is read off the same span: at `r2 = 0.3`
    the liability-threshold AUC runs from `0.753` to `0.921` as prevalence moves
    from `0.5` to `0.001`, and this chart answers `0.6783` for all of it. -/
noncomputable def equalVarianceGaussianAUCFromExplainedR2 (r2 : ℝ) : ℝ :=
  if 1 ≤ r2 then 1 else Foundations.Phi (Real.sqrt (r2 / (2 * (1 - r2))))

/-- Below the perfect-prediction boundary, the total chart is the Gaussian closed form. -/
theorem equalVarianceGaussianAUCFromExplainedR2_eq_formula_of_lt_one
    (r2 : ℝ) (h : r2 < 1) :
    equalVarianceGaussianAUCFromExplainedR2 r2 =
      Foundations.Phi (Real.sqrt (r2 / (2 * (1 - r2)))) := by
  simp [equalVarianceGaussianAUCFromExplainedR2, not_le.mpr h]

/-- Perfect prediction gives perfect discrimination. -/
@[simp] theorem equalVarianceGaussianAUCFromExplainedR2_at_one :
    equalVarianceGaussianAUCFromExplainedR2 1 = 1 := by
  simp [equalVarianceGaussianAUCFromExplainedR2]

/-! ### WHY A RANGE CHECK COULD NOT CATCH THIS, WHICH IS THE POINT

Ten definitions in this AUC family were flagged by the range checker as **provably unable
to fail**: their bound is `Φ`'s codomain, so "the result lies in `[0,1]`" is a fact about
`Phi` and says nothing whatever about the body. They were counted as covered while being
structurally incapable of detecting the defect below.

**A check that verifies "is it a probability" cannot catch "is it the right probability."**
The equal-variance form returns a perfectly well-formed number in `[0,1]` and is biased by
seven AUC points on dichotomised traits. Every range check passes; the biology is wrong.

This is the concrete instance the vacuity investigation was looking for. The general lesson
is that a bound inherited from a codomain is not evidence about a definition, and a coverage
count that credits such bounds is counting something other than what its name says.

### The liability-threshold AUC, which is the one binary traits need

`equalVarianceGaussianAUCFromExplainedR2` is a true theorem about the equal-variance
Gaussian model and the **wrong formula for a dichotomised trait**, which is most of what
polygenic scores are used for. Its own docstring already recorded
`FALSIFIED as the liability-threshold AUC`; what was missing was the right formula, not a
correction to that one. Both are kept, and each names the other and the regime that selects
it, because the defect was never that either was false — it was that nothing said when each
applies.

The formula below is **classical**: it is the liability-threshold result of Wray et al.
(2010), *The genetic interpretation of area under the ROC curve*, in the same way the
Gaussian information constants and van Trees are classical components named as such. The
contribution here is not the derivation; it is that the corpus carried only the
equal-variance form for binary traits, and that this one has been measured. -/

/-! The liability-threshold primitives and their regime are declared before
the first binary-trait profile above. The substantive comparison starts here,
after the equal-variance chart has also been declared. -/

/-- **The two AUC maps are not the same function, and must not be collapsed into one.**

The equal-variance form takes no prevalence argument, so it is constant in `K`; the
liability form is not. Hence if the liability AUC differs between *any* two prevalences at a
fixed `r2` — which is what the 400-run validation measures, the fitted `K` moving the
prediction by far more than the `0.0120` noise floor — then no identity can equate the two
maps.

This exists to stop a later simplification from quietly identifying them. The hypothesis is
the empirical fact, supplied rather than assumed, in the same way
`NearLowDimensionalFamily` is carried elsewhere. -/
theorem liabilityAUC_ne_equalVarianceAUC_of_prevalence_dependent
    {r2 K₁ K₂ : ℝ}
    (hK : liabilityThresholdAUCFromExplainedR2 r2 K₁ ≠
      liabilityThresholdAUCFromExplainedR2 r2 K₂) :
    ¬ (∀ K : ℝ, liabilityThresholdAUCFromExplainedR2 r2 K =
        equalVarianceGaussianAUCFromExplainedR2 r2) := by
  intro hcollapse
  exact hK ((hcollapse K₁).trans (hcollapse K₂).symm)

/-- Under the regime the case mean strictly exceeds the control mean, so the numerator of
the AUC argument is non-negative and the map is not accidentally reading the wrong tail.

This is the one structural fact worth having beyond the separation theorem: `i > 0 > i_c`
holds for every prevalence in `(0,1)`, because `i_c` is a negative multiple of `i`. -/
theorem liabilityControlMean_lt_caseMean {K : ℝ} (hK0 : 0 < K) (hK1 : K < 1) :
    liabilityControlMean K < liabilityCaseMean K := by
  have hpdf : 0 < standardNormalPdf (liabilityThreshold K) := by
    unfold standardNormalPdf
    exact div_pos (Real.exp_pos _) (Real.sqrt_pos.2 (by positivity))
  have hi : 0 < liabilityCaseMean K :=
    div_pos hpdf hK0
  have h1K : 0 < 1 - K := by linarith
  have hneg : liabilityControlMean K < 0 := by
    unfold liabilityControlMean
    apply div_neg_of_neg_of_pos _ h1K
    nlinarith
  linarith

/-- **Target AUC from the neutral allele-frequency benchmark, for a DICHOTOMISED trait.**

Prevalence `K` is a **required argument**, and that is the whole design. The failure this
replaces was not that someone chose a wrong prevalence — it was that no prevalence was ever
named, so a drift-induced `R²` drop was converted into AUC units by a formula that has no
place to put one. Making `K` mandatory turns a silently biased number into a call that does
not elaborate until whoever owns the call site supplies the prevalence, which is the person
who knows it.

This is the conversion to use for a binary trait. For a genuinely **continuous** outcome the
equal-variance chart is correct and `presentDayEqualVarianceGaussianAUC` is the one to call.

    Empirical status: **VALIDATED, inherited from both factors, with the
    composition itself untouched.** The body is a two-stage composition and each
    stage carries its own measurement. `liabilityThresholdAUCFromExplainedR2` is
    validated against 400 simulated PGS studies at pooled RMSE 0.0121 with bias
    -0.0007, against an independently measured 0.0120 seed-to-seed noise floor,
    and its prevalence axis is swept. `presentDayR2` runs through
    `presentDayPGSVariance`, validated on the heterozygosity-retention reading of
    `fst` at worst 0.94 sems over `Nₑ = 500`, 400 unlinked loci and 200 replicate
    populations.

    WHAT THE INHERITANCE DOES NOT COVER, stated because a composition of two
    validated parts is exactly where this corpus has hidden an error before. The
    two batteries are different simulations, and neither one feeds a
    drift-attenuated `R²` into the liability chart. So the JOIN -- that a drift
    `F_ST` may be converted to an explained-variance fraction and that fraction
    handed to the liability-threshold AUC -- rests on `presentDayR2` denoting the
    same explained-variance fraction the AUC chart's `r2` argument expects. That
    is a reading, checked here by inspection and not by a measurement.

    It is also where the fault this definition replaces lived: the superseded
    body carried a `-0.068` AUC bias precisely because a drift `R²` drop was fed
    to a prevalence-free chart. Naming the prevalence fixes that, and does not
    by itself test the join.

    argument_source: model, inherited. -/
noncomputable def targetLiabilityAUCFromNeutralAFBenchmark
    (V_A V_E fstTarget K : ℝ) : ℝ :=
  liabilityThresholdAUCFromExplainedR2 (presentDayR2 V_A V_E fstTarget) K

/-- The same quantity written through the explicit benchmark `R²`, so the two cannot drift
apart. -/
theorem targetLiabilityAUCFromNeutralAFBenchmark_eq (V_A V_E fstTarget K : ℝ) :
    targetLiabilityAUCFromNeutralAFBenchmark V_A V_E fstTarget K =
      liabilityThresholdAUCFromExplainedR2 (presentDayR2 V_A V_E fstTarget) K := rfl

/-- **Benchmark target Brier risk for a DICHOTOMISED trait**, the Brier twin of
`targetLiabilityAUCFromNeutralAFBenchmark`.

The explained fraction supplied is `targetR2FromNeutralAFBenchmark`, which is a
LIABILITY-scale fraction, and a prevalence argument announces a dichotomised outcome, so the
chart consuming the pair is the liability-threshold one.
`targetBrierFromNeutralAFBenchmark` is the same two arguments through
`PopGen.TransportedMetrics.calibratedBrier`, the OBSERVED-scale chart: correct for a
continuous outcome and measured wrong on a truncated liability tail, at the sizes tabulated
on `PopGen.TransportedMetrics.calibratedBrierFromVariances`. The two bodies differ in
nothing but which chart they call, which is the whole of the defect this one repairs.

    Empirical status: VALIDATED, inherited.
    `PopGen.TransportedMetrics.liabilityBrierExact` carries the head and the battery
    (`simcov/battery_brier01.py`, MATCH at worst 2.93 sems over sixteen cells, with the
    linear chart FALSIFIED on the same cells at 1961 sems); this body adds no arithmetic, it
    only chooses which prevalence and which explained fraction to hand it. What the
    inheritance does NOT cover is that choice: the battery drew `r²` on the liability scale
    directly, and that the benchmark `R²` this body supplies is the same fraction is a
    reading, checked by inspection and not by that measurement.

    Power: inherited with the verdict -- the underlying prediction spans 0.006231 to
    0.242039 across the sixteen cells that carry it.

    argument_source: model, inherited. -/
noncomputable def targetLiabilityBrierFromNeutralAFBenchmark
    (π V_A V_E fstTarget : ℝ) : ℝ :=
  PopGen.TransportedMetrics.liabilityBrierExact π
    (targetR2FromNeutralAFBenchmark V_A V_E fstTarget)

/-- The same quantity written through the explicit benchmark `R²`, so the coordinate and the
chart it is read on cannot drift apart. -/
theorem targetLiabilityBrierFromNeutralAFBenchmark_eq (π V_A V_E fstTarget : ℝ) :
    targetLiabilityBrierFromNeutralAFBenchmark π V_A V_E fstTarget =
      PopGen.TransportedMetrics.liabilityBrierExact π (presentDayR2 V_A V_E fstTarget) := rfl

/-- **Bundled deployed metrics for a DICHOTOMISED trait**, with the prevalence used for the
AUC as well as for the Brier risk.

No new modelling input is required to build this: `π` is already an argument of the profile
it replaces. The old record simply declined to use it for the discrimination metric, which
is how a `-0.068` AUC bias survived beside a Brier risk computed correctly at the same
prevalence.

    Empirical status: VALIDATED, inherited on all three coordinates -- and the head is a
    single one only because the Brier battery has now run; it read MIXED while that
    coordinate was untested.

      r2     `targetR2FromNeutralAFBenchmark`, which is `presentDayR2`; that runs
             through `presentDayPGSVariance`, VALIDATED at worst 0.94 sems on
             the heterozygosity-retention reading of `fst`.
      auc    `targetLiabilityAUCFromNeutralAFBenchmark`, VALIDATED through
             `liabilityThresholdAUCFromExplainedR2` at pooled RMSE 0.0121
             against a 0.0120 noise floor, with prevalence swept. The whole
             point of this record is that this field spends the `π` it was given.
    Power: inherited per coordinate -- the `R²` prediction spans 0.00162 to 0.05367, a
    factor of thirty-three, and the Brier prediction spans 0.006231 to 0.242039.

      brier  `targetLiabilityBrierFromNeutralAFBenchmark`, VALIDATED through
             `PopGen.TransportedMetrics.liabilityBrierExact` at the benchmark `R²`:
             MATCH at worst 2.93 sems over sixteen cells, against the linear chart
             it replaced FALSIFIED on the same cells at 1961 sems.

    So the defect this record was written to repair -- one field treating the trait as
    binary and another as continuous -- is repaired on both readout coordinates: the AUC
    and the Brier risk are now the liability-threshold charts, and the `π` this record takes
    is spent on both of them. The Brier coordinate previously read
    `targetBrierFromNeutralAFBenchmark`, the Gaussian chart, which is what made this record
    FALSIFIED on that field; the exchange is the same observable on the scale its arguments
    are actually on, and it trades a measured error for an unmeasured body.

    argument_source: model, inherited. -/
noncomputable def neutralAFBenchmarkLiabilityMetricProfile
    (π V_A V_E fstTarget : ℝ) : PopGen.TransportedMetrics.Profile :=
  { r2 := targetR2FromNeutralAFBenchmark V_A V_E fstTarget
  , auc := targetLiabilityAUCFromNeutralAFBenchmark V_A V_E fstTarget π
  , brier := targetLiabilityBrierFromNeutralAFBenchmark π V_A V_E fstTarget }

/-- **The dichotomised profile shares the continuous one's `R²` coordinate and reads both
readouts off the liability-threshold charts.**

The first conjunct relates the two records; the other two name what the dichotomised record
puts in the coordinates the continuous one fills from the Gaussian charts, which
`neutralAFBenchmarkMetricProfile_eq` states on the other side. Two coordinates move under
dichotomisation, not one -- the AUC has moved since this family was written and the Brier
coordinate moved with the rebinding onto `PopGen.TransportedMetrics.liabilityBrierExact`. -/
theorem liabilityProfile_differs_in_auc_and_brier (π V_A V_E fstTarget : ℝ) :
    (neutralAFBenchmarkLiabilityMetricProfile π V_A V_E fstTarget).r2 =
      (neutralAFBenchmarkMetricProfile π V_A V_E fstTarget).r2 ∧
    (neutralAFBenchmarkLiabilityMetricProfile π V_A V_E fstTarget).auc =
      liabilityThresholdAUCFromExplainedR2 (presentDayR2 V_A V_E fstTarget) π ∧
    (neutralAFBenchmarkLiabilityMetricProfile π V_A V_E fstTarget).brier =
      PopGen.TransportedMetrics.liabilityBrierExact π (presentDayR2 V_A V_E fstTarget) := by
  refine ⟨?_, rfl, rfl⟩
  -- `rw` closes a goal only by the `rfl` it tries at reducible transparency, and the
  -- rewritten right-hand side is a PROJECTION OF A STRUCTURE LITERAL, whose reduction is
  -- iota rather than delta. The explicit `rfl` is what performs it.
  rw [neutralAFBenchmarkMetricProfile_eq]
  rfl

/-- **The `R²` and variance readings of the equal-variance Gaussian chart agree.**

Reading the AUC off an `R²` needs the variance split as well as the Gaussian regime: `r2`
determines a signal-to-noise ratio only once the outcome variance is known to be signal
plus environment. With `h_split` supplied, `r2 / (1 - r2)` *is* that ratio, and this form
reduces to the one already discharged.

Stating it as a chart identity prevents it from being read as a general biological
conversion.  No Gaussian-process theorem is accepted as an argument. -/
theorem equalVarianceGaussianAUCFromExplainedR2_eq_variance
    (vSignal vEnv : ℝ) (h_signal : 0 ≤ vSignal) (h_env : 0 < vEnv) :
    equalVarianceGaussianAUCFromExplainedR2
        (PopGen.TransportedMetrics.r2FromSignalVariance vSignal vEnv) =
      equalVarianceGaussianAUCFromSignalVariance vSignal vEnv := by
  have h_total : 0 < vSignal + vEnv := add_pos_of_nonneg_of_pos h_signal h_env
  have h_r2_lt : PopGen.TransportedMetrics.r2FromSignalVariance vSignal vEnv < 1 := by
    unfold PopGen.TransportedMetrics.r2FromSignalVariance Descent.Core.share
    exact (div_lt_one h_total).2 (lt_add_of_pos_right vSignal h_env)
  rw [equalVarianceGaussianAUCFromExplainedR2_eq_formula_of_lt_one _ h_r2_lt]
  rw [← equalVarianceGaussianAUCFromSNR_eq_variance vSignal vEnv (ne_of_gt h_env)]
  unfold equalVarianceGaussianAUCFromSNR PopGen.TransportedMetrics.r2FromSignalVariance
    Descent.Core.share
  congr 2
  -- `field_simp` was called without the two nonzero facts proved directly
  -- above, so it could not cancel `vEnv` and left `X * Y * Y⁻¹ = X` for
  -- `ring`, which cannot discharge it: cancelling needs `Y ≠ 0` and `ring`
  -- never consults hypotheses. Whether the fed version closes the goal
  -- outright or leaves a polynomial identity is not knowable in advance, so
  -- `first` takes neither bet.
  field_simp [ne_of_gt h_total, ne_of_gt h_env]
  ring

/-- **Cross-check: the `R²` form and the SNR form are the same map.**

Under `snr = R²/(1 - R²)` the two agree exactly. Stated because they were
written separately and never related, which is the condition under which the
whole family could be misnamed without any of them contradicting the others. -/
theorem equalVarianceGaussianAUCFromExplainedR2_eq_fromSNR
    (r2 : ℝ) (h : r2 < 1) :
    equalVarianceGaussianAUCFromExplainedR2 r2 =
      equalVarianceGaussianAUCFromSNR (r2 / (1 - r2)) := by
  rw [equalVarianceGaussianAUCFromExplainedR2_eq_formula_of_lt_one r2 h]
  unfold equalVarianceGaussianAUCFromSNR
  congr 2
  rw [div_div, mul_comm]

/-- On valid deployed `R²` values, the liability-threshold AUC chart is strictly
increasing whenever `Phi` is strictly increasing. -/
theorem equalVarianceGaussianAUCFromExplainedR2_strictMonoOn_unitInterval :
    StrictMonoOn equalVarianceGaussianAUCFromExplainedR2 (Set.Ico 0 1) := by
  intro x hx y hy hxy
  rw [equalVarianceGaussianAUCFromExplainedR2_eq_formula_of_lt_one x hx.2,
    equalVarianceGaussianAUCFromExplainedR2_eq_formula_of_lt_one y hy.2]
  apply Foundations.strictMono_Phi
  have hx_one_sub : 0 < 1 - x := by linarith [hx.2]
  have hy_one_sub : 0 < 1 - y := by linarith [hy.2]
  have hx_den : 0 < 2 * (1 - x) :=
    mul_pos (by norm_num) hx_one_sub
  have hy_den : 0 < 2 * (1 - y) :=
    mul_pos (by norm_num) hy_one_sub
  have hx_arg_nonneg : 0 ≤ x / (2 * (1 - x)) :=
    div_nonneg hx.1 (le_of_lt hx_den)
  have harg_lt : x / (2 * (1 - x)) < y / (2 * (1 - y)) := by
    rw [div_lt_div_iff₀ hx_den hy_den]
    nlinarith
  exact Real.sqrt_lt_sqrt hx_arg_nonneg harg_lt

/-- **Equal-variance Gaussian** AUC induced by the full explicit source-side driver
state. Like the target-side exported AUC, this is built directly from source
explained signal and source residual variance under the source-learned score
equation.

    This is not the liability-threshold AUC: cases under a liability threshold are a
    truncated tail, so the two distributions have unequal variances and the AUC depends on
    prevalence, which this takes no argument for.

    Empirical status: UNTESTED. -/
noncomputable def equalVarianceGaussianAUCFromSourceWeights {p q : ℕ}
    (m : CrossPopulationMetricModel p q) (P : Pop) : ℝ :=
  equalVarianceGaussianAUCFromSignalVariance
    (explainedSignalVarianceFromSourceWeights m P)
    (residualVarianceFromSourceWeights m P)

/-- The mechanistic source AUC is exactly the explicit liability-threshold map
applied to source explained signal and source residual variance. -/
theorem sourceEqualVarianceGaussianAUCFromSourceWeights_eq_explicit_source_variances
    {p q : ℕ} (m : CrossPopulationMetricModel p q) :
    equalVarianceGaussianAUCFromSourceWeights m Pop.source =
      equalVarianceGaussianAUCFromSignalVariance
        (explainedSignalVarianceFromSourceWeights m Pop.source)
        (residualVarianceFromSourceWeights m Pop.source) := by
  rfl

/-- **The AUC chart holds at either population**, given that the population's effective
outcome variance is positive.

The source and target readings of this were two theorems with the same eleven-line proof:
derive the signal-below-outcome inequality from `R² < 1`, conclude the residual is nonzero,
rewrite both AUC forms into their formulas, and clear denominators.  Only the positivity
fact differs between them, and it is a hypothesis here. -/
theorem equalVarianceGaussianAUCFromSourceWeights_eq_explainedR2_chart_of_pos {p q : ℕ}
    (m : CrossPopulationMetricModel p q) (P : Pop)
    (h_eff_pos : 0 < effectiveOutcomeVariance m P)
    (h_r2 : r2FromSourceWeights m P < 1) :
    equalVarianceGaussianAUCFromSourceWeights m P =
      equalVarianceGaussianAUCFromExplainedR2 (r2FromSourceWeights m P) := by
  have h_signal_lt :
      explainedSignalVarianceFromSourceWeights m P < effectiveOutcomeVariance m P :=
    (div_lt_one h_eff_pos).mp (by simpa [r2FromSourceWeights] using h_r2)
  have h_residual_ne :
      residualVarianceFromSourceWeights m P ≠ 0 := by
    rw [residualVarianceFromSourceWeights]
    exact ne_of_gt (sub_pos.mpr h_signal_lt)
  rw [equalVarianceGaussianAUCFromExplainedR2_eq_formula_of_lt_one _ h_r2]
  rw [equalVarianceGaussianAUCFromSourceWeights,
    equalVarianceGaussianAUCFromSignalVariance_eq_formula_of_ne_noise _ _ h_residual_ne]
  unfold residualVarianceFromSourceWeights r2FromSourceWeights
  congr 1
  congr 1
  field_simp [ne_of_gt h_eff_pos]

/-- The direct mechanistic source AUC agrees with the `R²` chart induced by the
same source explained-signal and total-variance decomposition.

This is only a derived coordinate identity; it is not the defining
construction of source AUC. -/
theorem sourceEqualVarianceGaussianAUCFromSourceWeights_eq_explainedR2_chart_of_lt_one {p q : ℕ}
    (m : CrossPopulationMetricModel p q)
    (h_r2 : r2FromSourceWeights m Pop.source < 1) :
    equalVarianceGaussianAUCFromSourceWeights m Pop.source =
      equalVarianceGaussianAUCFromExplainedR2 (r2FromSourceWeights m Pop.source) :=
  equalVarianceGaussianAUCFromSourceWeights_eq_explainedR2_chart_of_pos m Pop.source
    (by simpa using m.outcomeVariance_pos Pop.source) h_r2

/-- The mechanistic target AUC is exactly the explicit liability-threshold map
applied to target explained signal and target residual variance. -/
theorem targetEqualVarianceGaussianAUCFromSourceWeights_eq_explicit_target_variances {p q : ℕ}
    (m : CrossPopulationMetricModel p q) :
    equalVarianceGaussianAUCFromSourceWeights m Pop.target =
      equalVarianceGaussianAUCFromSignalVariance
        (explainedSignalVarianceFromSourceWeights m Pop.target)
        (residualVarianceFromSourceWeights m Pop.target) := by
  rfl

/-- Exact mechanistic target liability-AUC portability law from transported
score moments. This is the direct liability-threshold variance law on the
explicit SNP-level transport model. -/
theorem targetEqualVarianceGaussianAUCFromSourceWeights_exact_metric_portability_law
    {p q : ℕ} (m : CrossPopulationMetricModel p q) :
    equalVarianceGaussianAUCFromSourceWeights m Pop.target =
      equalVarianceGaussianAUCFromSignalVariance
        ((predictiveCovarianceFromSourceWeights m Pop.target) ^ 2 /
          scoreVarianceFromSourceWeights m Pop.target)
        (effectiveOutcomeVariance m Pop.target -
          (predictiveCovarianceFromSourceWeights m Pop.target) ^ 2 /
            scoreVarianceFromSourceWeights m Pop.target) := by
  rw [targetEqualVarianceGaussianAUCFromSourceWeights_eq_explicit_target_variances]
  simp [explainedSignalVarianceFromSourceWeights,
    residualVarianceFromSourceWeights]

/-- Exact mechanistic target liability-AUC portability law with the additive
biological loss budget made explicit in the residual term. -/
theorem targetEqualVarianceGaussianAUCFromSourceWeights_exact_loss_budget_law
    {p q : ℕ} (m : CrossPopulationMetricModel p q) :
    equalVarianceGaussianAUCFromSourceWeights m Pop.target =
      equalVarianceGaussianAUCFromSignalVariance
        ((predictiveCovarianceFromSourceWeights m Pop.target) ^ 2 /
          scoreVarianceFromSourceWeights m Pop.target)
        ((m.outcomeVariance Pop.target) + irreducibleTargetResidualBurden m -
          (predictiveCovarianceFromSourceWeights m Pop.target) ^ 2 /
            scoreVarianceFromSourceWeights m Pop.target) := by
  rw [targetEqualVarianceGaussianAUCFromSourceWeights_exact_metric_portability_law,
    effectiveOutcomeVariance_target]

/-- The direct mechanistic target AUC agrees with the `R²` chart induced by the
same target explained-signal and total-variance decomposition.

This is only a derived coordinate identity; it is not the defining
construction of target AUC. -/
theorem targetEqualVarianceGaussianAUCFromSourceWeights_eq_explainedR2_chart_of_lt_one {p q : ℕ}
    (m : CrossPopulationMetricModel p q)
    (h_r2 : r2FromSourceWeights m Pop.target < 1) :
    equalVarianceGaussianAUCFromSourceWeights m Pop.target =
      equalVarianceGaussianAUCFromExplainedR2 (r2FromSourceWeights m Pop.target) :=
  equalVarianceGaussianAUCFromSourceWeights_eq_explainedR2_chart_of_pos m Pop.target
    (effectiveTargetOutcomeVariance_pos m) h_r2

/-- Canonical mechanistic deployed source metric profile evaluated at an
arbitrary observed prevalence coordinate `π`. This is the source-side analogue
of `targetMetricProfileFromSourceWeights`, and it lets downstream calibration
theory compare source and target Brier on the same target-population
prevalence scale.

    Empirical status: MIXED -- the record carries one verdict per field and they are not
    the same verdict.

      r2     `r2FromSourceWeights` at the source, VALIDATED at 0.06 sems in
             `simcov/battery_transport.py`.
      auc    `equalVarianceGaussianAUCFromSourceWeights`, which has no
             measurement; its own docstring is explicit that it is the
             EQUAL-VARIANCE Gaussian chart and not the liability-threshold one,
             so at a prevalence far from one half it is the wrong chart for a
             dichotomised outcome and it takes no `π` to be right with.
      brier  `sourceCalibratedBrierFromSourceWeightsAtPrevalence`, VALIDATED,
             inherited from `PopGen.TransportedMetrics.liabilityBrierExact`,
             which matches at worst 2.93 sems over sixteen cells.

    THE INTERNAL INCONSISTENCY IS THE FINDING, and it is the same one
    `neutralAFBenchmarkMetricProfile` is documented for -- but it now sits on the OTHER
    side of the record. This record takes a prevalence `π`, spends it on a Brier coordinate
    that is on the liability-threshold scale its arguments are actually on, and computes the
    AUC with a chart that has nowhere to put one. So a profile assembled to compare source
    and target Brier "on the same prevalence scale" is still binary in one field and
    continuous in another; what changed is which field is which.

    argument_source: model, inherited. -/
noncomputable def sourceMetricProfileFromSourceWeightsAtPrevalence {p q : ℕ}
    (m : CrossPopulationMetricModel p q) (π : ℝ) : PopGen.TransportedMetrics.Profile where
  r2 := r2FromSourceWeights m Pop.source
  auc := equalVarianceGaussianAUCFromSourceWeights m Pop.source
  brier := sourceCalibratedBrierFromSourceWeightsAtPrevalence m π

@[simp] theorem sourceMetricProfileFromSourceWeightsAtPrevalence_r2 {p q : ℕ}
    (m : CrossPopulationMetricModel p q) (π : ℝ) :
    (sourceMetricProfileFromSourceWeightsAtPrevalence m π).r2 =
      r2FromSourceWeights m Pop.source := by
  rfl

@[simp] theorem sourceMetricProfileFromSourceWeightsAtPrevalence_auc {p q : ℕ}
    (m : CrossPopulationMetricModel p q) (π : ℝ) :
    (sourceMetricProfileFromSourceWeightsAtPrevalence m π).auc =
      equalVarianceGaussianAUCFromSourceWeights m Pop.source := by
  rfl

@[simp] theorem sourceMetricProfileFromSourceWeightsAtPrevalence_brier {p q : ℕ}
    (m : CrossPopulationMetricModel p q) (π : ℝ) :
    (sourceMetricProfileFromSourceWeightsAtPrevalence m π).brier =
      sourceCalibratedBrierFromSourceWeightsAtPrevalence m π := by
  rfl

/-- The source metric profile evaluated on the target-population observed
prevalence scale carried by the mechanistic target state.

    Empirical status: **FALSIFIED on the `brier` coordinate, inherited.** The
    body supplies `m.targetPrevalence` for the free `π` of
    `sourceMetricProfileFromSourceWeightsAtPrevalence` and changes nothing else,
    so the per-field verdicts are that definition's, read there.

    What this body adds is the CHOICE of prevalence, and it is a modelling
    choice rather than a measurable one: scoring a source-fitted model on the
    target's observed prevalence is the comparison the calibration theory wants
    to make, and no simulation can say it is the wrong prevalence to want. The
    thing a simulation could say -- that the Brier chart is wrong at whatever
    prevalence is supplied -- it has already said upstream.

    argument_source: model, inherited. -/
noncomputable def sourceMetricProfileFromSourceWeightsAtTargetPrevalence {p q : ℕ}
    (m : CrossPopulationMetricModel p q) : PopGen.TransportedMetrics.Profile :=
  sourceMetricProfileFromSourceWeightsAtPrevalence m m.targetPrevalence

@[simp] theorem sourceMetricProfileFromSourceWeightsAtTargetPrevalence_r2 {p q : ℕ}
    (m : CrossPopulationMetricModel p q) :
    (sourceMetricProfileFromSourceWeightsAtTargetPrevalence m).r2 =
      r2FromSourceWeights m Pop.source := by
  rfl

@[simp] theorem sourceMetricProfileFromSourceWeightsAtTargetPrevalence_auc {p q : ℕ}
    (m : CrossPopulationMetricModel p q) :
    (sourceMetricProfileFromSourceWeightsAtTargetPrevalence m).auc =
      equalVarianceGaussianAUCFromSourceWeights m Pop.source := by
  rfl

@[simp] theorem sourceMetricProfileFromSourceWeightsAtTargetPrevalence_brier {p q : ℕ}
    (m : CrossPopulationMetricModel p q) :
    (sourceMetricProfileFromSourceWeightsAtTargetPrevalence m).brier =
      sourceCalibratedBrierFromSourceWeightsAtPrevalence m m.targetPrevalence := by
  rfl

/-- Canonical mechanistic deployed metric profile induced by the explicit
SNP-level transported score equation. The upstream state is the full
source-weights/target-LD/target-tagging system, with AUC bundled from the
explicit target signal/residual moment pair rather than from a source-side
transport surrogate. -/
noncomputable def targetMetricProfileFromSourceWeights {p q : ℕ}
    (m : CrossPopulationMetricModel p q) : PopGen.TransportedMetrics.Profile where
  r2 := r2FromSourceWeights m Pop.target
  auc := equalVarianceGaussianAUCFromSourceWeights m Pop.target
  brier := targetCalibratedBrierFromSourceWeights m

@[simp] theorem targetMetricProfileFromSourceWeights_r2 {p q : ℕ}
    (m : CrossPopulationMetricModel p q) :
    (targetMetricProfileFromSourceWeights m).r2 = r2FromSourceWeights m Pop.target := by
  rfl

@[simp] theorem targetMetricProfileFromSourceWeights_auc {p q : ℕ}
    (m : CrossPopulationMetricModel p q) :
    (targetMetricProfileFromSourceWeights
        m).auc = equalVarianceGaussianAUCFromSourceWeights m Pop.target := by
  rfl

@[simp] theorem targetMetricProfileFromSourceWeights_brier {p q : ℕ}
    (m : CrossPopulationMetricModel p q) :
    (targetMetricProfileFromSourceWeights m).brier =
      targetCalibratedBrierFromSourceWeights m := by
  rfl

/-- Bundled exact mechanistic metric portability law.

The exported target metric profile is determined exactly by:
- the transported score/outcome covariance under source-learned weights,
- the target score variance under the target LD matrix,
- the target prevalence, and
- the additive biological loss budget entering the effective target outcome
  variance.

This packages the exact `R²` and liability-AUC laws on the explicit SNP-level transport
state. The Brier coordinate is named rather than expanded: it is `liabilityBrierExact` at
the target prevalence and the transported explained fraction, and that body has no
elementary closed form to expand into -- expanding it into variance coordinates is exactly
the observed-scale substitution the liability body exists to avoid. -/
theorem targetMetricProfileFromSourceWeights_exact_mechanistic_portability_law
    {p q : ℕ} (m : CrossPopulationMetricModel p q) :
    targetMetricProfileFromSourceWeights m =
      { r2 :=
          (predictiveCovarianceFromSourceWeights m Pop.target) ^ 2 /
            (scoreVarianceFromSourceWeights m Pop.target * effectiveOutcomeVariance m Pop.target)
      , auc :=
          equalVarianceGaussianAUCFromSignalVariance
            ((predictiveCovarianceFromSourceWeights m Pop.target) ^ 2 /
              scoreVarianceFromSourceWeights m Pop.target)
            (effectiveOutcomeVariance m Pop.target -
              (predictiveCovarianceFromSourceWeights m Pop.target) ^ 2 /
                scoreVarianceFromSourceWeights m Pop.target)
      , brier :=
          PopGen.TransportedMetrics.liabilityBrierExact
            m.targetPrevalence (r2FromSourceWeights m Pop.target) } := by
  ext
  · rw [targetMetricProfileFromSourceWeights_r2,
      targetR2FromSourceWeights_exact_metric_portability_law]
  · rw [targetMetricProfileFromSourceWeights_auc,
      targetEqualVarianceGaussianAUCFromSourceWeights_exact_metric_portability_law]
  · rfl

/-- Canonical mechanistic deployed metric profile after `t` generations. -/
noncomputable def targetMetricProfileAtGeneration {p q : ℕ}
    (m : CrossPopulationGenerationalModel p q) (t : ℕ) :
    PopGen.TransportedMetrics.Profile :=
  targetMetricProfileFromSourceWeights (m.toMetricModelAt t)

@[simp] theorem targetMetricProfileAtGeneration_eq_slice {p q : ℕ}
    (m : CrossPopulationGenerationalModel p q) (t : ℕ) :
    targetMetricProfileAtGeneration m t =
      targetMetricProfileFromSourceWeights (m.toMetricModelAt t) := by
  rfl

/-- Display-normalized target `R²` after `t` generations.

This preserves the exact mechanistic portability ratio while anchoring the
source baseline at a chosen display value, instead of rescaling the biological
state. -/
noncomputable def sourceNormalizedTargetR2AtGeneration {p q : ℕ}
    (m : CrossPopulationGenerationalModel p q) (sourceBaseline : ℝ) (t : ℕ) : ℝ :=
  sourceBaseline *
    (r2FromSourceWeights (m.toMetricModelAt t) Pop.target / r2FromSourceWeights (m.toMetricModelAt
        t) Pop.source)

/-- Exact mechanistic law for display-normalized target `R²` at generation `t`.

This is the correct way to draw a source-anchored `R²` curve for visualization:
it rescales the exact portability ratio, not the underlying biological state. -/
theorem sourceNormalizedTargetR2AtGeneration_exact_mechanistic_popgen_portability_law
    {p q : ℕ} (m : CrossPopulationGenerationalModel p q)
    (sourceBaseline : ℝ) (t : ℕ) :
    sourceNormalizedTargetR2AtGeneration m sourceBaseline t =
      sourceBaseline *
        (((predictiveCovarianceFromSourceWeights (m.toMetricModelAt t) Pop.target) ^ 2 *
            scoreVarianceFromSourceWeights (m.toMetricModelAt t) Pop.source *
            ((m.toMetricModelAt t).outcomeVariance Pop.source)) /
          ((predictiveCovarianceFromSourceWeights (m.toMetricModelAt t) Pop.source) ^ 2 *
            scoreVarianceFromSourceWeights (m.toMetricModelAt t) Pop.target *
            effectiveOutcomeVariance (m.toMetricModelAt t) Pop.target)) := by
  unfold sourceNormalizedTargetR2AtGeneration
  rw [exactR2PortabilityRatio_mechanistic_law]

/-- Bundled exact metric portability law after `t` generations on the explicit
population-genetic state. This packages the exact `R²`, liability-AUC, and
Brier laws on the generation-indexed mechanistic transport model. -/
theorem targetMetricProfileAtGeneration_exact_mechanistic_popgen_portability_law
    {p q : ℕ} (m : CrossPopulationGenerationalModel p q) (t : ℕ) :
    targetMetricProfileAtGeneration m t =
      { r2 :=
          (predictiveCovarianceFromSourceWeights (m.toMetricModelAt t) Pop.target) ^ 2 /
            (scoreVarianceFromSourceWeights (m.toMetricModelAt t) Pop.target *
              effectiveOutcomeVariance (m.toMetricModelAt t) Pop.target)
      , auc :=
          equalVarianceGaussianAUCFromSignalVariance
            ((predictiveCovarianceFromSourceWeights (m.toMetricModelAt t) Pop.target) ^ 2 /
              scoreVarianceFromSourceWeights (m.toMetricModelAt t) Pop.target)
            (effectiveOutcomeVariance (m.toMetricModelAt t) Pop.target -
              (predictiveCovarianceFromSourceWeights (m.toMetricModelAt t) Pop.target) ^ 2 /
                scoreVarianceFromSourceWeights (m.toMetricModelAt t) Pop.target)
      , brier :=
          PopGen.TransportedMetrics.liabilityBrierExact
            (m.outcome.targetPrevalenceAt t)
            (r2FromSourceWeights (m.toMetricModelAt t) Pop.target) } := by
  ext
  · rw [targetMetricProfileAtGeneration_eq_slice,
      targetMetricProfileFromSourceWeights_exact_mechanistic_portability_law]
  · rw [targetMetricProfileAtGeneration_eq_slice,
      targetMetricProfileFromSourceWeights_exact_mechanistic_portability_law]
  · rw [targetMetricProfileAtGeneration_eq_slice,
      targetMetricProfileFromSourceWeights_exact_mechanistic_portability_law]
    simp [CrossPopulationGenerationalModel.toMetricModelAt]

/-- The direct `R²`-chart liability AUC agrees with the literal present-day
liability AUC when the deployed `R²` comes from the same neutral benchmark
chart. -/
theorem equalVarianceGaussianAUCFromExplainedR2_eq_presentDayAUC
    (V_A V_E fst : ℝ)
    (hVA : 0 < V_A) (hVE : 0 < V_E)
    (hfst_lt_one : fst < 1) :
    equalVarianceGaussianAUCFromExplainedR2 (presentDayR2 V_A V_E fst) =
      presentDayEqualVarianceGaussianAUC V_A V_E fst := by
  have hv_pos : 0 < presentDayPGSVariance V_A fst := by
    unfold presentDayPGSVariance pgsVarianceFromHet Descent.Core.product
    have h_one_minus : 0 < 1 - fst := by linarith
    exact mul_pos hVA h_one_minus
  have hsum_ne : presentDayPGSVariance V_A fst + V_E ≠ 0 := by
    linarith
  have hve_ne : V_E ≠ 0 := ne_of_gt hVE
  have hr2_lt : presentDayR2 V_A V_E fst < 1 := by
    unfold presentDayR2 PopGen.TransportedMetrics.r2FromSignalVariance Descent.Core.share
    exact (div_lt_one (add_pos hv_pos hVE)).2 (lt_add_of_pos_right _ hVE)
  have hchart :
      presentDayR2 V_A V_E fst / (2 * (1 - presentDayR2 V_A V_E fst)) =
        presentDaySignalToNoise V_A V_E fst / 2 := by
    unfold presentDayR2 PopGen.TransportedMetrics.r2FromSignalVariance presentDaySignalToNoise
      Descent.Core.share
    field_simp [hsum_ne, hve_ne]
    ring
  rw [equalVarianceGaussianAUCFromExplainedR2_eq_formula_of_lt_one _ hr2_lt]
  rw [presentDayEqualVarianceGaussianAUC_eq _ _ _ hve_ne, hchart]

/-! The benchmark AUC degradation theorem is
`targetAUC_lt_source_of_neutralAF_benchmark`, above.  A second copy of it stood here as
`targetLiabilityAUC_lt_source_of_neutralAF_benchmark`, with the same statement and the same
proof, and its name claimed the liability-threshold model -- which
`presentDayEqualVarianceGaussianAUC`'s own docstring records as the misidentification that
understates AUC by 3% to 26%.  One theorem, under the name that says which model it is. -/

/-- The observed-scale target calibrated Brier risk is `TransportedMetrics.calibratedBrier`
evaluated at the explicit target `R²`, by definition.  The word "exact" stood in this
sentence and has been removed for the reason `targetCalibratedBrierRisk`'s own docstring
gives: the chart on the right is exact under the Bernoulli-mixing reading of `R²` and is
not the liability-threshold risk. -/
@[simp] theorem targetBrierFromNeutralAFBenchmark_eq
    (π V_A V_E fstTarget : ℝ) :
    targetCalibratedBrierRisk π V_A V_E fstTarget =
      PopGen.TransportedMetrics.calibratedBrier π
        (targetR2FromNeutralAFBenchmark V_A V_E fstTarget) := by
  rfl

/-- Exact calibrated Bernoulli Brier risk from prevalence and explained-risk
moments. If the true conditional risk `η(Z)` has mean `π` and variance
`π(1-π) r2`, then the exact calibrated population Brier risk is
`π(1-π)(1-r2)`.

**THE EXACTNESS IS REAL AND IT IS SCOPED BY `hvar`.** The hypothesis is what makes `r2` the
OBSERVED-scale explained fraction -- the variance of the conditional risk itself, in units
of `π(1-π)` -- and on that reading the linear chart is not an approximation to anything.
A liability-scale explained fraction does not satisfy `hvar`, which is why feeding one to
this chart is a scale error rather than a rounding one, and why
`PopGen.TransportedMetrics.liabilityBrierExact` exists beside it. The two agree exactly at
`r2 = 0` and `r2 = 1`. -/
theorem exactBrierRiskOfCalibrated_eq_exactCalibratedBrierRiskFromR2
    {Z : Type*} [MeasurableSpace Z]
    (μ : Measure Z) [IsProbabilityMeasure μ]
    (η : Z → ℝ) (π r2 : ℝ)
    (hη_int : Integrable η μ)
    (hvar_int : Integrable (fun z ↦ (η z - π) ^ 2) μ)
    (hmean : ∫ z, η z ∂μ = π)
    (hvar : ∫ z, (η z - π) ^ 2 ∂μ = π * (1 - π) * r2) :
    Foundations.exactBrierRiskOfCalibrated μ η = PopGen.TransportedMetrics.calibratedBrier π r2
      := by
  rw [Foundations.exactBrierRiskOfCalibrated_eq_integral]
  have hdiff_int : Integrable (fun z ↦ η z - π) μ := by
    simpa [sub_eq_add_neg] using hη_int.sub (integrable_const π)
  have hlin_zero : ∫ z, (η z - π) ∂μ = 0 := by
    rw [integral_sub hη_int (integrable_const π), hmean]
    simp
  calc
    ∫ z, η z * (1 - η z) ∂μ
        = ∫ z, ((π * (1 - π) - (η z - π) ^ 2) + (1 - 2 * π) * (η z - π)) ∂μ := by
            refine integral_congr_ae ?_
            filter_upwards with z
            ring
    _ = ∫ z, (π * (1 - π) - (η z - π) ^ 2) ∂μ +
          ∫ z, (1 - 2 * π) * (η z - π) ∂μ := by
            convert
              (integral_add ((integrable_const _).sub hvar_int)
                (hdiff_int.const_mul (1 - 2 * π))) using 1
    _ = (∫ z, (π * (1 - π)) ∂μ - ∫ z, (η z - π) ^ 2 ∂μ) +
          ∫ z, (1 - 2 * π) * (η z - π) ∂μ := by
            rw [integral_sub (integrable_const _) hvar_int]
    _ = (π * (1 - π) - ∫ z, (η z - π) ^ 2 ∂μ) +
          (1 - 2 * π) * ∫ z, (η z - π) ∂μ := by
            rw [MeasureTheory.integral_const, MeasureTheory.integral_const_mul]
            simp
    _ = π * (1 - π) - ∫ z, (η z - π) ^ 2 ∂μ := by
            rw [hlin_zero]
            ring
    _ = PopGen.TransportedMetrics.calibratedBrier π r2 := by
            rw [hvar]
            unfold PopGen.TransportedMetrics.calibratedBrier
            ring

/-- Full neutral allele-frequency benchmark Brier degradation theorem: if
target `R²` drops and `0 ≤ π ≤ 1`, target Brier is at least source Brier
within this benchmark. -/
theorem targetBrier_ge_source_of_neutralAF_benchmark
    (π V_A V_E fstSource fstTarget : ℝ)
    (h_pi : 0 ≤ π ∧ π ≤ 1)
    (hVA : 0 < V_A) (hVE : 0 < V_E)
    (h_fst : fstSource < fstTarget)
    (h_fst_bounds : 0 ≤ fstSource ∧ fstTarget < 1) :
    sourceBrierFromR2 π (presentDayR2 V_A V_E fstSource) ≤
      targetBrierFromNeutralAFBenchmark π V_A V_E fstTarget := by
  rcases h_pi with ⟨hpi0, hpi1⟩
  have hr2_drop :
      targetR2FromNeutralAFBenchmark V_A V_E fstTarget < presentDayR2 V_A V_E fstSource :=
    targetR2_lt_source_from_neutralAF_benchmark V_A V_E fstSource fstTarget
      hVA hVE h_fst h_fst_bounds
  have hcoef_nonneg : 0 ≤ π * (1 - π) := by nlinarith
  unfold sourceBrierFromR2 targetBrierFromNeutralAFBenchmark
    targetCalibratedBrierRisk PopGen.TransportedMetrics.calibratedBrier
  have hbase :
      1 - presentDayR2 V_A V_E fstSource ≤
        1 - targetR2FromNeutralAFBenchmark V_A V_E fstTarget := by
    linarith
  exact mul_le_mul_of_nonneg_left hbase hcoef_nonneg

/-- Pointwise Brier regret relative to the true Bernoulli probability. -/
noncomputable def brierRegretPoint (η q : ℝ) : ℝ :=
  Foundations.brierBernoulliRisk η q - Foundations.brierBernoulliRisk η η

/-- Pointwise Brier regret ratio between target and source predictors. -/
noncomputable def brierRegretRatio (η qSource qTarget : ℝ) : ℝ :=
  brierRegretPoint η qTarget / brierRegretPoint η qSource

/-- **brierRegretRatio at its junk point, named.** A perfectly calibrated source has zero Brier
regret, so the ratio of target to source regret is undefined -- and it is exactly the case a
transport study most wants to report. The divisor is zero and Lean returns `0`: the target is
reported as incurring no regret relative to a source that incurs none, which reads as perfect
transport. Consumers must exclude the argument that makes the guard vanish. -/
theorem brierRegretRatio_calibrated_source_is_junk (η qTarget : ℝ) :
    brierRegretRatio η η qTarget = 0 := by
  unfold brierRegretRatio brierRegretPoint
  simp

/-- Brier regret equals squared calibration error exactly. -/
theorem brierRegretPoint_eq_sq_error (η q : ℝ) :
    brierRegretPoint η q = (q - η) ^ 2 := by
  unfold brierRegretPoint
  simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
    Foundations.brier_regret_pointwise η
    q

/-- Ratio form in present-day units: Brier-regret ratio is a squared-error ratio. -/
theorem brierRegretRatio_eq_sq_error_ratio (η qSource qTarget : ℝ) :
    brierRegretRatio η qSource qTarget =
      ((qTarget - η) ^ 2) / ((qSource - η) ^ 2) := by
  unfold brierRegretRatio
  rw [brierRegretPoint_eq_sq_error, brierRegretPoint_eq_sq_error]

/-- Pointwise log-loss regret relative to truth. -/
noncomputable def logLossRegretPoint (η q : ℝ) : ℝ :=
  Foundations.bernoulliLogLoss η q - Foundations.bernoulliLogLoss η η

/-- **The pointwise regret vanishes exactly on a matching forecast.**

A self-application identity, not a reference evaluation: `f x x = 0` rejects no rescaling
of `f`. The vanishing on the diagonal is what makes this quantity a regret at all, so the
fact is kept and only the name corrected. Contrast `brierRegretPoint`, whose regret is a
squared deviation and therefore carries genuine scaling relations -- the two regrets have
different homogeneity, and this one has none. -/
theorem logLossRegretPoint_self_eq_zero (η : ℝ) :
    logLossRegretPoint η η = 0 := by
  unfold logLossRegretPoint
  ring


/-- Pointwise log-loss regret ratio between target and source predictors. -/
noncomputable def logLossRegretRatio (η qSource qTarget : ℝ) : ℝ :=
  logLossRegretPoint η qTarget / logLossRegretPoint η qSource

/-- **logLossRegretRatio at its junk point, named.** The log-loss twin of
`brierRegretRatio_calibrated_source_is_junk`, failing at the same configuration through the same
vanishing denominator. Two different proper losses agree on a wrong answer here, so a cross-loss
consistency check passes. Consumers must exclude the argument that makes the guard vanish. -/
theorem logLossRegretRatio_calibrated_source_is_junk (η qTarget : ℝ) :
    logLossRegretRatio η η qTarget = 0 := by
  unfold logLossRegretRatio logLossRegretPoint
  simp

/-- Log-loss regret is exactly Bernoulli KL divergence. -/
theorem logLossRegretPoint_eq_kl (η q : ℝ)
    (hη0 : 0 < η) (hη1 : η < 1)
    (hq0 : 0 < q) (hq1 : q < 1) :
    logLossRegretPoint η q = Foundations.bernoulliKLReal η q := by
  unfold logLossRegretPoint
  simpa using Foundations.logLoss_regret_eq_kl_pointwise η q hη0 hη1 hq0 hq1

/-- Ratio form in present-day units: log-loss regret ratio is a KL ratio. -/
theorem logLossRegretRatio_eq_kl_ratio (η qSource qTarget : ℝ)
    (hη0 : 0 < η) (hη1 : η < 1)
    (hqS0 : 0 < qSource) (hqS1 : qSource < 1)
    (hqT0 : 0 < qTarget) (hqT1 : qTarget < 1) :
    logLossRegretRatio η qSource qTarget =
      Foundations.bernoulliKLReal η qTarget / Foundations.bernoulliKLReal η qSource := by
  unfold logLossRegretRatio
  rw [logLossRegretPoint_eq_kl η qTarget hη0 hη1 hqT0 hqT1,
    logLossRegretPoint_eq_kl η qSource hη0 hη1 hqS0 hqS1]

/-! **Do not add an "at zero divergence" variant of
`targetR2FromNeutralAFBenchmark_eq_presentDayR2`.** `targetR2FromNeutralAFBenchmark` is
DEFINED as `presentDayR2`, so the equality holds at every `fst`; a statement restricted to
`fst = 0` advertises a special case that is not special, which is the same defect as a
hypothesis that appears to do work and does not. The unrestricted theorem above is the
edge that keeps the two names tied. -/

/-- For valid prevalence `0 < π < 1`, the linear Brier approximation `π(1-π)(1-R²)`
is strictly decreasing in `R²`. -/
theorem brierFromR2_strictAnti (π : ℝ) (hπ0 : 0 < π) (hπ1 : π < 1) :
    StrictAnti (brierFromR2 π) := by
  intro r2a r2b hab
  unfold brierFromR2
  have hcoef : 0 < π * (1 - π) := mul_pos hπ0 (by linarith)
  have hdrop : 1 - r2b < 1 - r2a := by linarith
  exact mul_lt_mul_of_pos_left hdrop hcoef

/-- Strict neutral allele-frequency benchmark Brier degradation: under
positive drift and non-degenerate prevalence, target Brier is strictly worse
than source Brier within this benchmark. -/
theorem targetBrier_strict_gt_source_of_neutralAF_benchmark
    (π V_A V_E fstSource fstTarget : ℝ)
    (hπ0 : 0 < π) (hπ1 : π < 1)
    (hVA : 0 < V_A) (hVE : 0 < V_E)
    (h_fst : fstSource < fstTarget)
    (h_fst_bounds : 0 ≤ fstSource ∧ fstTarget < 1) :
    sourceBrierFromR2 π (presentDayR2 V_A V_E fstSource) <
      targetBrierFromNeutralAFBenchmark π V_A V_E fstTarget := by
  have hr2_drop :=
    targetR2_lt_source_from_neutralAF_benchmark V_A V_E fstSource fstTarget
      hVA hVE h_fst h_fst_bounds
  unfold sourceBrierFromR2 targetBrierFromNeutralAFBenchmark
  exact brierFromR2_strictAnti π hπ0 hπ1 hr2_drop

/-- Squared mean PGS difference under the pure split model.

    Empirical status: **VALIDATED**
    (`validation/empirical/simcov/battery_bulk12.py`,
    `test_pure_split_pgs_diff`). Realised variance of the mean-score difference
    between two independently drifted demes, `Ne = 200`, 500 loci, 3000
    replicate deme pairs:

      generations   this def   measured             sems
        30           46.54641   45.89697±1.18525     0.55
       100          153.50564  148.78561±3.84227     1.23
       250          368.98445  353.94478±9.14034     1.65

    `Var_Delta_Mu` is separately validated for ONE branch, so what this adds is
    the composition over two: feeding it `fstS + fstT` rather than a single
    branch index reproduces the two-branch variance. That composition is where
    the drift-variance family went wrong once already -- the missing ploidy
    factor cancelled inside a cross-identity and survived it -- so checking it
    against a measurement rather than against a sibling formula is the point.

    Power: the prediction spans 46.5 to 369.0, a factor of eight. -/
noncomputable def expectedSqMeanPGSDiff_pureSplit (V_A fstS fstT : ℝ) : ℝ :=
  Var_Delta_Mu V_A (fstS + fstT)

/-- **The closed form: twice the summed differentiation times the additive variance.**

This was two theorems, `_closed` and `_eq`, with the same statement and two proofs of it. -/
@[simp] theorem expectedSqMeanPGSDiff_pureSplit_closed (V_A fstS fstT : ℝ) :
    expectedSqMeanPGSDiff_pureSplit V_A fstS fstT = 2 * (fstS + fstT) * V_A := by
  unfold expectedSqMeanPGSDiff_pureSplit Var_Delta_Mu
  ring

/-- The expected squared mean PGS difference under the IM equilibrium model:
`E[(Δμ)²] = 4δ V_A` where `δ = 1/(2M+1)`.

    Empirical status: **MEASURED** (`simcov/battery_gap01.py`, `group_impgap`),
    on the two-deme design the paragraphs below say this owes, with the power
    limit stated rather than passed over. Both components carry measurements and
    the join between them is algebra -- but the algebra does not come out to
    `2 δ`, and the direct measurement now bounds how far off it can be.

    THE DESIGN THIS OWED, run. `A` and `δ` are measured on the SAME replicates:
    a two-deme island model at `Nₑ = 2000` over 10 Mb with recombination, 8
    replicates per cell, up to 600 loci common in both demes, with the
    observable the realised squared difference in mean PGS and `δ` read off the
    same genealogies as the realised between-to-within divergence ratio. The
    body evaluated at that realised `δ` agrees at worst 0.45 sems across
    `4 Nₑ m` = 0.5, 2, 8, over a 94% span in the prediction. Control: at
    overwhelming migration the realised `δ` is 0.0019 ± 0.0010 against a known
    zero.

    WHAT THE RUN DOES NOT SETTLE, and it is the factor the paragraphs below are
    about: the un-doubled reading `Var_Delta_Mu V_A δ` also agrees, at worst
    2.07 sems. Eight replicates of a mean-PGS difference give an error bar too
    wide to separate a factor of two, so this measurement confirms the SHAPE in
    `δ` and leaves the coefficient where the algebra below leaves it. What would
    settle it is more replicates, not a different design.

    THE TWO COMPONENTS. `Var_Delta_Mu V_A f = 2 f V_A` is validated with its
    second slot read as the SUM OF THE PER-BRANCH DRIFT INDICES: its docstring
    is explicit that a two-branch design fed a pairwise value produced a
    factor-of-four false falsification, twice. `twoDemeIMEquilibriumDelta M`
    is validated as HUDSON's `F_ST`, `1 - E[T_within]/E[T_between]`, at 0.10,
    0.16 and 2.03 sems. Those are two different conventions in the family this
    corpus has paid for three times, so the substitution `fstS + fstT ↦ 2 δ` is
    the whole content of this body.

    THE JOIN, DERIVED. Write `δp = p₁ - p₂` and `p̄ = (p₁ + p₂)/2`. The slot
    `Var_Delta_Mu` wants is `A = E[δp²] / E[p̄(1-p̄)]`, since variances add over
    independent branches. Hudson's denominator is
    `p₁(1-p₂) + p₂(1-p₁) = 2 p̄(1-p̄) + δp²/2`, so as a ratio of averages

      δ = E[δp²] / (2 E[p̄(1-p̄)] + E[δp²]/2) = A / (2 + A/2)

    and inverting, `A = 2 δ / (1 - δ/2)`. So the correct argument is `2 δ` only
    in the limit `δ → 0`, and this body runs LOW by the factor `(1 - δ/2)`:
    2.4% at `M = 10` where `δ = 0.048`, 5.6% at `M = 4`, and 17% at `M = 1`
    where `δ = 1/3`. The bias is one-signed and grows with differentiation,
    which is the direction that matters, because differentiation is the regime
    a portability law exists for.

    THE BODY IS LEFT AS IT IS AND THE BIAS IS WRITTEN DOWN, rather than the
    exact form being substituted, because the derivation above holds at the
    per-locus level and both `δ` and `A` are ratios of averages over loci. The
    corpus has already recorded, in `conventions.json`, that a pointwise
    identity between two `F_ST` estimators does not survive aggregation: the
    Nei-to-Hudson bridge predicts the two high-differentiation cells and runs
    low at the two small ones, and the gap is Jensen. So `1 - δ/2` is the size
    and the sign of the correction, not a coefficient to install unmeasured. A
    two-deme design measuring `A` and `δ` on the same replicates would settle
    it, and is what this owes.

    argument_source: model, for both components. -/
noncomputable def expectedSqMeanPGSDiff_IMEquilibrium (V_A M : ℝ) : ℝ :=
  Var_Delta_Mu V_A (2 * twoDemeIMEquilibriumDelta M)

/-- IM equilibrium squared mean difference equals `4δ V_A`. -/
@[simp] theorem expectedSqMeanPGSDiff_IMEquilibrium_eq (V_A M : ℝ) :
    expectedSqMeanPGSDiff_IMEquilibrium V_A M =
      4 * twoDemeIMEquilibriumDelta M * V_A := by
  unfold expectedSqMeanPGSDiff_IMEquilibrium Var_Delta_Mu
  ring

/-- IM equilibrium: increasing migration strictly decreases genetic differentiation
    on the biologically meaningful domain M > 0. -/
theorem twoDemeIMEquilibriumDelta_strictAntiOn :
    StrictAntiOn (fun M : ℝ ↦ twoDemeIMEquilibriumDelta M) (Set.Ioi 0) := by
  intro a ha b hb hab
  unfold twoDemeIMEquilibriumDelta
  have ha_pos : 0 < 2 * a + 1 := by linarith [Set.mem_Ioi.mp ha]
  have hb_pos : 0 < 2 * b + 1 := by linarith [Set.mem_Ioi.mp hb]
  exact div_lt_div_of_pos_left one_pos ha_pos (by linarith : 2 * a + 1 < 2 * b + 1)

/-- Under the IM model, the mean-shift variance is strictly decreasing in migration rate
    on the biological domain (M > 0) when `V_A > 0`. -/
theorem expectedSqMeanPGSDiff_IMEquilibrium_strictAntiOn_M
    (V_A : ℝ) (hVA : 0 < V_A) :
    StrictAntiOn (fun M : ℝ ↦ expectedSqMeanPGSDiff_IMEquilibrium V_A M) (Set.Ioi 0) := by
  intro a ha b hb hab
  simp only [expectedSqMeanPGSDiff_IMEquilibrium_eq]
  have := twoDemeIMEquilibriumDelta_strictAntiOn ha hb hab
  nlinarith

/-! ## The demography's own deployed metrics

Every law above states itself over loose reals -- a `V_A`, an `F_ST`, a signal variance -- and
a reader has to believe those came from a population. The corollaries below state the same
laws about `(p : PopGenParameters)` and the differentiation that record itself predicts, so
the demography reaches the deployed number inside one claim instead of across a gap the reader
closes. `Core/Moments.lean` states this pattern for the metrics it owns; these are the chart
and benchmark laws this module owns.

The record's own fields discharge what the loose form asked the reader to assume: `V_A_pos`
for the additive variance, `fstEquilibrium_lt_one` for the differentiation, both under the
flow hypothesis `0 < p.mu + p.mig` that says the demes are connected at all. `V_E` stays an
argument because environmental variance is not demography and the record does not carry it.

Not every law above admits one. A law reading a prevalence against a literal `R²`, a
junk-value law about a degenerate variance, and the laws about a `CrossPopulationMetricModel`
or a `CrossPopulationGenerationalModel` all take nothing this record supplies, and binding
`p` to them would name a demography the statement never uses. -/

open Descent.Core (PopGenParameters)

/-- **The deployed `R²` under drift is strictly below one** whenever there is environmental
variance left to explain. The unit-interval bound is not enough for the AUC charts, which
divide by `1 - R²`: at `R² = 1` the Gaussian argument is undefined, and a positive `V_E` is
exactly what rules that case out. -/
theorem presentDayR2_lt_one (V_A V_E fst : ℝ) (hVA : 0 < V_A) (hVE : 0 < V_E)
    (hfst : fst < 1) :
    presentDayR2 V_A V_E fst < 1 := by
  have hv_pos : 0 < presentDayPGSVariance V_A fst := by
    rw [presentDayPGSVariance_eq_one_sub_fst_mul]
    exact mul_pos (by linarith) hVA
  unfold presentDayR2 PopGen.TransportedMetrics.r2FromSignalVariance Descent.Core.share
  exact (div_lt_one (add_pos hv_pos hVE)).2 (lt_add_of_pos_right _ hVE)

/-- **A demography's benchmark profile, read at its own equilibrium differentiation.**  The
three deployed coordinates of the neutral-allele-frequency benchmark are what this record's
additive variance and island equilibrium produce, with no free `F_ST` for a reader to
supply. -/
theorem neutralAFBenchmarkMetricProfile_eq_of_params (p : PopGenParameters) (π V_E : ℝ) :
    neutralAFBenchmarkMetricProfile π p.V_A V_E p.fstEquilibrium =
      { r2 := targetR2FromNeutralAFBenchmark p.V_A V_E p.fstEquilibrium
      , auc := presentDayEqualVarianceGaussianAUC p.V_A V_E p.fstEquilibrium
      , brier := targetBrierFromNeutralAFBenchmark π p.V_A V_E p.fstEquilibrium } :=
  neutralAFBenchmarkMetricProfile_eq π p.V_A V_E p.fstEquilibrium

/-- **A demography's liability-threshold AUC is the chart at the `R²` it deploys.**  For a
dichotomised trait at prevalence `K`, the benchmark AUC is the liability chart read at the
`R²` this record's equilibrium leaves, and nothing else enters. -/
theorem targetLiabilityAUCFromNeutralAFBenchmark_eq_of_params
    (p : PopGenParameters) (V_E K : ℝ) :
    targetLiabilityAUCFromNeutralAFBenchmark p.V_A V_E p.fstEquilibrium K =
      liabilityThresholdAUCFromExplainedR2 (presentDayR2 p.V_A V_E p.fstEquilibrium) K :=
  targetLiabilityAUCFromNeutralAFBenchmark_eq p.V_A V_E p.fstEquilibrium K

/-- **Dichotomising a demography's trait moves both readout coordinates and leaves `R²`
alone.**  At this record's own differentiation the liability profile agrees with the
benchmark profile on `R²`, and reads discrimination and risk off the liability-threshold
charts rather than the Gaussian ones -- two coordinates, which is where the
misidentification this module records would land. -/
theorem liabilityProfile_differs_in_auc_and_brier_of_params
    (p : PopGenParameters) (π V_E : ℝ) :
    (neutralAFBenchmarkLiabilityMetricProfile π p.V_A V_E p.fstEquilibrium).r2 =
      (neutralAFBenchmarkMetricProfile π p.V_A V_E p.fstEquilibrium).r2 ∧
    (neutralAFBenchmarkLiabilityMetricProfile π p.V_A V_E p.fstEquilibrium).auc =
      liabilityThresholdAUCFromExplainedR2 (presentDayR2 p.V_A V_E p.fstEquilibrium) π ∧
    (neutralAFBenchmarkLiabilityMetricProfile π p.V_A V_E p.fstEquilibrium).brier =
      PopGen.TransportedMetrics.liabilityBrierExact π
        (presentDayR2 p.V_A V_E p.fstEquilibrium) :=
  liabilityProfile_differs_in_auc_and_brier π p.V_A V_E p.fstEquilibrium

/-- **A connected demography's equal-variance AUC is its present-day AUC.**  The chart read
at the `R²` this record deploys and the closed form in the record's own coordinates are one
number.  The flow hypothesis is what makes the equilibrium differentiation strictly below
one; with no migration and no mutation the demes are separate populations and the chart has
nothing to read. -/
theorem equalVarianceGaussianAUCFromExplainedR2_eq_presentDayAUC_of_params
    (p : PopGenParameters) (V_E : ℝ) (hVE : 0 < V_E) (hflow : 0 < p.mu + p.mig) :
    equalVarianceGaussianAUCFromExplainedR2 (presentDayR2 p.V_A V_E p.fstEquilibrium) =
      presentDayEqualVarianceGaussianAUC p.V_A V_E p.fstEquilibrium :=
  equalVarianceGaussianAUCFromExplainedR2_eq_presentDayAUC p.V_A V_E p.fstEquilibrium
    p.V_A_pos hVE (p.fstEquilibrium_lt_one hflow)

/-- **The `R²` and variance readings agree on a demography's drifted signal.**  The record's
additive variance, attenuated by its own equilibrium, is the signal variance the AUC reads,
so the two ways of entering the chart cannot disagree about this population.  No flow
hypothesis is needed: at complete differentiation the attenuated signal is zero, which the
variance form reads as well as the `R²` form does. -/
theorem equalVarianceGaussianAUCFromExplainedR2_eq_variance_of_params
    (p : PopGenParameters) (V_E : ℝ) (hVE : 0 < V_E) :
    equalVarianceGaussianAUCFromExplainedR2 (presentDayR2 p.V_A V_E p.fstEquilibrium) =
      equalVarianceGaussianAUCFromSignalVariance
        (presentDayPGSVariance p.V_A p.fstEquilibrium) V_E := by
  have hv : 0 ≤ presentDayPGSVariance p.V_A p.fstEquilibrium := by
    rw [presentDayPGSVariance_eq_one_sub_fst_mul]
    exact mul_nonneg (by linarith [p.fstEquilibrium_mem_unit.2]) p.V_A_pos.le
  exact equalVarianceGaussianAUCFromExplainedR2_eq_variance
    (presentDayPGSVariance p.V_A p.fstEquilibrium) V_E hv hVE

/-- **The closed form of the chart, at a demography's own `R²`.** -/
theorem equalVarianceGaussianAUCFromExplainedR2_eq_formula_of_params
    (p : PopGenParameters) (V_E : ℝ) (hVE : 0 < V_E) (hflow : 0 < p.mu + p.mig) :
    equalVarianceGaussianAUCFromExplainedR2 (presentDayR2 p.V_A V_E p.fstEquilibrium) =
      Foundations.Phi (Real.sqrt (presentDayR2 p.V_A V_E p.fstEquilibrium /
        (2 * (1 - presentDayR2 p.V_A V_E p.fstEquilibrium)))) :=
  equalVarianceGaussianAUCFromExplainedR2_eq_formula_of_lt_one _
    (presentDayR2_lt_one p.V_A V_E p.fstEquilibrium p.V_A_pos hVE
      (p.fstEquilibrium_lt_one hflow))

/-- **And its signal-to-noise reading.**  A deployment quoting an AUC from a signal-to-noise
ratio and one quoting it from an `R²` are quoting the same number about this population. -/
theorem equalVarianceGaussianAUCFromExplainedR2_eq_fromSNR_of_params
    (p : PopGenParameters) (V_E : ℝ) (hVE : 0 < V_E) (hflow : 0 < p.mu + p.mig) :
    equalVarianceGaussianAUCFromExplainedR2 (presentDayR2 p.V_A V_E p.fstEquilibrium) =
      equalVarianceGaussianAUCFromSNR (presentDayR2 p.V_A V_E p.fstEquilibrium /
        (1 - presentDayR2 p.V_A V_E p.fstEquilibrium)) :=
  equalVarianceGaussianAUCFromExplainedR2_eq_fromSNR _
    (presentDayR2_lt_one p.V_A V_E p.fstEquilibrium p.V_A_pos hVE
      (p.fstEquilibrium_lt_one hflow))

/-- **Deeper differentiation discriminates worse, for one demography.**  The additive
variance is the record's and only the differentiation moves, which is the comparison a
deployment across two target populations actually makes.  Stated at a free `F_ST` rather than
at the record's equilibrium because the point is the movement, and a record has one
equilibrium. -/
theorem equalVarianceGaussianAUCFromExplainedR2_anti_of_params
    (p : PopGenParameters) (V_E f₁ f₂ : ℝ) (hVE : 0 < V_E) (h1 : f₁ < f₂) (h2 : f₂ < 1) :
    equalVarianceGaussianAUCFromExplainedR2 (presentDayR2 p.V_A V_E f₂) <
      equalVarianceGaussianAUCFromExplainedR2 (presentDayR2 p.V_A V_E f₁) := by
  have hf1 : f₁ < 1 := lt_trans h1 h2
  exact equalVarianceGaussianAUCFromExplainedR2_strictMonoOn_unitInterval
    ⟨(presentDayR2_mem_unit p.V_A V_E f₂ p.V_A_pos hVE.le h2).1,
      presentDayR2_lt_one p.V_A V_E f₂ p.V_A_pos hVE h2⟩
    ⟨(presentDayR2_mem_unit p.V_A V_E f₁ p.V_A_pos hVE.le hf1).1,
      presentDayR2_lt_one p.V_A V_E f₁ p.V_A_pos hVE hf1⟩
    (presentDayR2_anti p.V_A V_E f₁ f₂ p.V_A_pos hVE h1 h2)

/-- **And it costs Brier risk, for the same demography.**  The two deployed coordinates move
together under differentiation because both read the one `R²` this record's additive variance
leaves after drift. -/
theorem brierFromR2_anti_of_params
    (p : PopGenParameters) (π V_E f₁ f₂ : ℝ) (hπ0 : 0 < π) (hπ1 : π < 1) (hVE : 0 < V_E)
    (h1 : f₁ < f₂) (h2 : f₂ < 1) :
    brierFromR2 π (presentDayR2 p.V_A V_E f₁) < brierFromR2 π (presentDayR2 p.V_A V_E f₂) :=
  brierFromR2_strictAnti π hπ0 hπ1 (presentDayR2_anti p.V_A V_E f₁ f₂ p.V_A_pos hVE h1 h2)

/-- **Prevalence-dependence at a demography's own `R²` rules out the equal-variance chart.**
If the liability AUC this record deploys differs between two prevalences, then no prevalence
makes the liability chart agree with the equal-variance one there -- so the choice of chart is
a claim about the trait and not a presentational one. -/
theorem liabilityAUC_ne_equalVarianceAUC_of_params
    (p : PopGenParameters) (V_E K₁ K₂ : ℝ)
    (hK : liabilityThresholdAUCFromExplainedR2 (presentDayR2 p.V_A V_E p.fstEquilibrium) K₁ ≠
      liabilityThresholdAUCFromExplainedR2 (presentDayR2 p.V_A V_E p.fstEquilibrium) K₂) :
    ¬ (∀ K : ℝ,
      liabilityThresholdAUCFromExplainedR2 (presentDayR2 p.V_A V_E p.fstEquilibrium) K =
        equalVarianceGaussianAUCFromExplainedR2 (presentDayR2 p.V_A V_E p.fstEquilibrium)) :=
  liabilityAUC_ne_equalVarianceAUC_of_prevalence_dependent hK

end PresentDayMetrics

/-- **The two in the allele-frequency retention ratio is the ploidy, twice, and
that is why the ratio does not depend on it.**

`PortabilityDrift.tagAlleleFreqRetentionAt` is `2p_t(1 - p_t) / (2p_0(1 - p_0))`,
and both twos are the same gene-copy count that `genotypeVarianceHWE` carries:
the body is a ratio of Hardy-Weinberg genotype variances at two times. Stating
it that way is not decoration. A bare `2` in a numerator and a bare `2` in a
denominator can be two DIFFERENT conventions written the same way -- a
heterozygosity over a genotype variance, say -- and the ratio would then be off
by a factor while looking symmetric. Once both are `genotypeVarianceHWE` the
cancellation is forced, and the retention is a pure ratio that a haploid corpus
would compute identically. -/
theorem tagAlleleFreqRetentionAt_eq_genotypeVarianceHWE_ratio {p q : ℕ}
    (m : Portability.CrossPopulationGenerationalModel p q) (t : ℕ) (i : Fin p) :
    Portability.tagAlleleFreqRetentionAt m t i =
      genotypeVarianceHWE (Portability.tagAlleleFreqTargetAt m t i) /
        genotypeVarianceHWE (m.tagAlleleFreqSource i) := by
  unfold Portability.tagAlleleFreqRetentionAt genotypeVarianceHWE Descent.Core.hweHeterozygosity
    Descent.Core.ploidy; ring

/-- **The same two, at the causal variants.** `causalAlleleFreqRetentionAt` is
the identical ratio on the causal side, and it is tied here separately rather
than by appeal to the tag version: two definitions with the same shape in one
file are exactly the pair a single fix leaves half-repaired. -/
theorem causalAlleleFreqRetentionAt_eq_genotypeVarianceHWE_ratio {p q : ℕ}
    (m : Portability.CrossPopulationGenerationalModel p q) (t : ℕ) (j : Fin q) :
    Portability.causalAlleleFreqRetentionAt m t j =
      genotypeVarianceHWE (Portability.causalAlleleFreqTargetAt m t j) /
        genotypeVarianceHWE (m.causalAlleleFreqSource j) := by
  unfold Portability.causalAlleleFreqRetentionAt genotypeVarianceHWE Descent.Core.hweHeterozygosity
    Descent.Core.ploidy; ring

end Descent.Portability
