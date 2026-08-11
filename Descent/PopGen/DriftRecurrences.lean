/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Core.Fst
import Descent.Core.Parameters
import Descent.Core.Ratios
import Descent.Core.Scaling
import Descent.Layer

assert_below Descent.Spectral Descent.Blindness Descent.Conditionals
assert_below Descent.Portability Descent.Decision Descent.Program

namespace Descent.PopGen

/-!
# Drift recurrences

The identity-by-descent recurrence, the island-model `F_ST` step and its equilibrium, the
mutation-drift heterozygosity floor, Hudson's `F_ST` from coalescence times, and pairwise
`F_ST` off a tree.

Every one of these is a statement about ONE population's allele frequencies over
generations. No score is carried anywhere in any of them, and no body reaches anything in
`Descent.Portability` -- which is why they are here rather than in the drift chapter, where
they had been housed for the reason the chapter was written there first. Six cross-layer
edges into `Portability.PortabilityDrift` were the cost of that, and they are the edges
this module retires.
-/

/-- `F_ST` after `t` generations of drift at effective size `Nₑ`, obtained by
rescaling to coalescent time and applying `fstFromTau`.

    Regime: a clean two-population split with no migration and equal sizes;
    `F_ST` is the pairwise Hudson estimator as a ratio of averages, which is the
    convention every `F_ST` in this corpus is written for.

    Empirical status: **VALIDATED** (`simcov/battery_bulk20.py`, `group_a`).
    The composition, not either half alone, is what is measured: `τ` is never
    read off, only `t` and `Nₑ` go in. Over `τ` = 0.125, 0.25, 1, 2, 4 the body
    predicts 0.11111, 0.20000, 0.50000, 0.66667 and 0.80000 against measured
    0.11708 ± 0.00264, 0.19851 ± 0.00511, 0.50095 ± 0.00770, 0.66607 ± 0.00624
    and 0.80065 ± 0.00317, worst cell 2.26 sems at 5.1% relative. Power: the
    prediction spans 86% of the unit interval and crosses the whole saturating
    curve, so a form linear in `τ`, or one saturating at another rate, separates
    on the grid rather than only at its ends. Simulated with recombination
    (8 Mb at 1e-8): at zero recombination one genealogy per replicate makes the
    error bar honest but far too wide to decide anything. -/
noncomputable def fstFromGenerations (t Ne : ℝ) : ℝ :=
  Descent.Core.fstFromTau (Descent.Core.Tau.ofGenerations t Ne)


theorem fst_from_tau_nonneg_of_nonneg (tau : ℝ) (htau : 0 ≤ tau) :
    0 ≤ Descent.Core.fstFromTau (Descent.Core.Tau.ofScaled tau) := by
  unfold Descent.Core.fstFromTau Descent.Core.saturation
  simp only [Descent.Core.Tau.value_ofScaled]
  exact div_nonneg htau (by linarith)


theorem fst_from_tau_lt_one (tau : ℝ) (htau : 0 ≤ tau) :
    Descent.Core.fstFromTau (Descent.Core.Tau.ofScaled tau) < 1 := by
  unfold Descent.Core.fstFromTau Descent.Core.saturation
  simp only [Descent.Core.Tau.value_ofScaled]
  rw [div_lt_one (by linarith)]
  linarith


/-- Hudson's `F_ST` estimator from mean coalescence times: one minus the ratio
of the within-population time to the total time.

    Regime: a clean two-population split, no migration, equal sizes.

    Empirical status: **VALIDATED** (`simcov/battery_bulk20.py`, `group_a`).
    This body claims that the GENEALOGICAL quantity computes the FREQUENCY one,
    so the two sides are taken from two engines that share no code: `ETss` and
    `ETst` come from branch-mode diversity and divergence over the tree
    sequence, and the value they are compared against is the site-frequency
    Hudson estimator over mutations dropped on that same tree, as a ratio of
    averages. Agreement is therefore evidence and not a transcription checked
    against itself. Over `τ` = 0.125, 0.25, 1, 2, 4 the branch-time reading
    gives 0.11571, 0.19622, 0.49809, 0.66453 and 0.79992 against the
    frequency-based 0.11708 ± 0.00372, 0.19851 ± 0.00711, 0.50095 ± 0.01057,
    0.66607 ± 0.00875 and 0.80065 ± 0.00447, worst cell 0.37 sems over a
    prediction spanning 86%. -/
noncomputable def hudsonFstFromCoalescenceTimes (ETss ETst : ℝ) : ℝ :=
  Descent.Core.proportionalReduction ETss ETst


/-- **Branchwise-to-pairwise `F_ST` map under independent drift from a common
ancestor.**

    Regime: small divergence, `F_ST` below about `0.05`. Multiplicative
    composition is the right shape -- additive composition `fstS + fstT` is 53%
    high at `T = 4000` -- and this map is within simulation error at the shortest
    branch tested, but it degrades monotonically as divergence grows, and the
    degradation is one-sided, always too high:

        T      fstS     fstT   pairwise obs      se      this map    err
      200    0.0461   0.0500     0.09314      0.00612    0.09366    +0.6%
     1000    0.1867   0.1895     0.31845      0.00941    0.34075    +7.0%
     2000    0.3374   0.3234     0.48780      0.01002    0.55098   +13.0%
     4000    0.5029   0.4987     0.65365      0.00801    0.74948   +14.7%

    Twelve to eighteen standard errors on the last two rows. Not an estimator
    artifact: under Nei's estimator the same rows give -1.4%, +3.3%, +10.0%,
    +14.2%.

    The mechanism is derivable rather than empirical, and
    `pairwiseFstFromBranches_eq_fstFromTau_add_mul` states it: composing
    multiplicatively in `F_ST` is the same as composing *additively in coalescent
    time* after inserting a spurious `tauS * tauT` of extra divergence time.
    Coalescence times add along a path; `F_ST` values do not. At `tau` near `1`,
    which is where `T = 4000` sits, that spurious term doubles the divergence
    time, which is the sign and the size of the error above.
    `pairwiseFstFromBranchTaus` is the same composition without it.

    Empirical status: CONDITIONALLY VALID. -/
noncomputable def pairwiseFstFromBranches (fstS fstT : ℝ) : ℝ :=
  Descent.Core.complementaryComposition fstS fstT


/-- **The heterozygosity floor that mutation holds.**

`theta / (1 + theta)` with `theta = 4 Nₑ mu`: the level at which mutational
input balances drift loss. Below it the recurrence gains heterozygosity, above
it the recurrence loses heterozygosity, and it is never crossed from above.
This is the number the closed-population model sets to zero.

    Regime: none. Its `mu = 0` value is `0`, which is the closed-population
    assumption itself, and is why that model predicts unbounded loss.

    Empirical status: **VALIDATED** (`simcov/battery_bulk20b.py`). The
    saturation is an INFINITE-ALLELES statement, and reading it under infinite
    sites is what an earlier attempt got wrong: per-site heterozygosity there is
    approximately `θ` and the `1 / (1 + θ)` denominator never shows. Measured on
    a single locus under `msprime`'s `InfiniteAlleles` model at `Nₑ = 1000` with 100 sampled
    chromosomes and 40 independent replicates, with heterozygosity
    taken as the unbiased `1 - ∑ pᵢ²` over the WHOLE sample -- never conditioned
    on the locus being polymorphic, which inflates it exactly where `θ` is
    small. Over `θ` = 0.1, 0.5, 1, 3, 10 the body predicts 0.09091, 0.33333,
    0.50000, 0.75000 and 0.90909 against measured 0.11943 ± 0.02958, 0.37403 ±
    0.03421, 0.49994 ± 0.03388, 0.76355 ± 0.01782 and 0.91824 ± 0.00421, worst
    cell 2.17 sems at 1.0% relative, over a prediction spanning 90%.

    Control: Ewens' sampling formula for the expected number of distinct
    alleles, `∑ᵢ θ/(θ+i-1)`, evaluated on the same samples. It shares no algebra
    with the body and passed at worst 1.10 sems (1.50/1.53, 3.28/3.45,
    5.19/5.38, 11.12/11.40, 24.44/25.05). It earned its place: on the first run
    the control returned exactly 2 alleles in every cell, which the sampling
    formula cannot produce, and it voided a design whose heterozygosity cells
    would otherwise have been read as a 21-sem falsification of this body.

    The observation the body explains is measured too: at demographic
    equilibrium the retention stays at `1.025 ± 0.020` out to `T = 4000` where
    the floorless model predicts `0.135`.

    INDEPENDENTLY CONFIRMED, and with the competitor gate the run above lacks
    (`simcov/battery_ia02.py`). 200 replicates rather than 40, same regime, and
    two competing readings carried on the same cells: `θ/(1+2θ)` misses by up to
    182 sems and `2θ/(1+2θ)` by 18, while the body sits at worst 0.68 sems. The
    Ewens control tracks `E[K]` from 1.5 to 24.4 alleles across the hundredfold
    sweep at 0.09 to 1.45 sems. A validation with no rejected competitor is
    arithmetic; this one is not.

    THE SAME TRAP HAS NOW BITTEN THIS DEFINITION THREE TIMES, in three
    directions, and it is worth naming so it stops. `msprime.InfiniteAlleles()`
    requires a DISCRETE genome. Under `discrete_genome=False` each mutation
    lands at its own real-valued position, so one locus carrying `k` mutations
    is reported as `k` biallelic SITES instead of one site with `k+1` allelic
    states -- and a design reading the FIRST variant then sees two alleles
    however large `θ` is. That produced a 21-sem falsification once, a VOID in
    `battery_bulk20.py` `group_b` once, and correct numbers only when
    `sequence_length = 1` is used with msprime's default discrete genome. The
    Ewens control is what caught it every time, because `∑ᵢ θ/(θ+i-1)` cannot
    return 2 for every `θ`. Do not drop that control. -/
noncomputable def hetMutationFloor (Ne mu : ℝ) : ℝ :=
  4 * Ne * mu / (1 + 4 * Ne * mu)


/-- **Arithmetic mean of the two directional migration rates.**

    **The docstring here said "harmonic mean" and the body is the arithmetic mean.** They
    are different numbers whenever the two rates differ, and the disagreement is
    one-sided: AM ≥ HM always, with equality only at `m₁₂ = m₂₁`
    (`harmonicMigrationMean_le_effectiveSymmetricMigration` below). So the stated
    quantity systematically *overstates* gene flow relative to the quantity the docstring
    named.

    That error does not stop at the mean. `fstMigrationDriftEquilibrium` is decreasing in
    the migration rate, so an overstated rate yields an understated `F_ST`, which
    `presentDayR2` turns into an *overstated* `R²` in the target population — the
    optimistic direction, and the direction that matters for a user being told how well a
    score transfers. `effectiveSymmetricMigration_fst_le_harmonic_fst` states that
    consequence.

    This is the same failure shape the corpus already records for `hudsonFst` computing
    Nei's `G_ST`: a name and docstring asserting one estimator over a body computing
    another, with the discrepancy landing in the direction that flatters the result. The
    name and docstring are corrected here rather than the body, because the body is what
    two other files already depend on — `Conventions.lean` ties it to `meanAlleleFreq`
    (an arithmetic mean, so that identity is only true of the current body), and
    `PopulationGeneticsFoundations.lean` proves the betweenness and idempotence facts
    against it. Changing the body to a harmonic mean would falsify both. Which of the two
    means is the right effective rate for asymmetric migration is not settled anywhere in
    this corpus, and nothing here should be read as settling it.
    nothing about the harmonic mean.

    Empirical status: **VALIDATED as a constancy claim**
    (`validation/empirical/simcov/battery_bulk13.py`). The claim is that
    an asymmetric pair behaves like a symmetric one at the ARITHMETIC MEAN rate,
    so the test holds that mean fixed and varies the asymmetry: if anything
    beyond the mean mattered, the measured `F_ST` would move and the prediction
    would not.

      m12       m21      mean rate   predicted   measured             sems
      1.0e-3    1.0e-3    1.0e-3      0.11111    0.11480±0.00589      0.63
      1.5e-3    5.0e-4    1.0e-3      0.11111    0.11538±0.00640      0.67
      1.8e-3    2.0e-4    1.0e-3      0.11111    0.10918±0.00521      0.37

    The asymmetry ratio runs from 1 to 9 across those rows and the measurement
    moves by 0.006, within its own error. The prediction is constant BY
    CONSTRUCTION here, which is why the verdict machinery reports no span; the
    power of this design is in the measured values not moving, not in the
    predicted ones moving.

    Fed to the deme-corrected two-deme form. The uncorrected
    `1/(1 + 4 Ne m_eff)` would miss every row by 14 sems, which is the separate
    defect recorded on `asymmetricFst`. A test of this quantity tests the arithmetic
    mean and says -/
noncomputable def effectiveSymmetricMigration (m₁₂ m₂₁ : ℝ) : ℝ :=
  Descent.Core.midpoint m₁₂ m₂₁


/-- **One generation of the identity-by-descent recurrence.**

A lineage pair coalesces this generation with probability `1/(2 Nₑ)`; failing
that it is identical only if it already was. Independently, the pair survives
the disrupting event -- whatever separates the two lineages -- with probability
`(1 - rate)²`, one chance per lineage.

    Denotes: the recurrence itself, not either quantity that satisfies it. Read
    with `rate = m` it is the island-model single-locus IBD recursion; read with
    `rate = c` it is Sved's two-locus IBD recursion for `E[r²]`. Those are
    different quantities obeying one map, so the map is named for the map and
    for neither of them.

Composition convention: the disrupting event acts on the offspring generation
*after* reproduction, and the two events multiply rather than add. This is the
difference from `ibdFlowStep`, which linearises `(1 - rate)² (1 - 1/(2 Nₑ))` to
`1 - 2 rate - 1/(2 Nₑ)` and therefore has a different fixed point.

    Empirical status: **VALIDATED**
    (`validation/empirical/simcov/battery_bulk1.py`,
    `test_one_step_maps`). Explicit island model, 40 demes of `2 Ne` gametes,
    3000 loci, migration then drift then two-way mutation each generation,
    `F_ST` read as `Var_between(p) / (pbar (1 - pbar))`. Tested as a ONE-STEP
    map: predict `F_{t+1}` from the measured `F_t` at each of 350 generations
    past the transient, then compare against the measured `F_{t+1}`.

      Ne     m        this def   simulated            sems
      200    0.002     0.27083   0.27079±0.00365      0.01
      200    0.010     0.10530   0.10530±0.00042      0.01
      500    0.005     0.07603   0.07602±0.00069      0.02

    A map tested only at its own fixed point cannot tell a wrong slope from a
    right one, which is why the prediction is made from the measured state at
    every generation rather than from the plateau.

    Power: the prediction spans 0.07603 to 0.27083 across the design. -/
noncomputable def ibdRecurrenceStep (Ne rate x : ℝ) : ℝ :=
  Descent.Core.survivalWeightedMix Ne rate x


/-- **The rest point of the identity-by-descent recurrence.**

Solving `x = (1 - rate)² (a + (1 - a) x)` with `a = 1/(2 Nₑ)` gives
`x* = (1 - rate)² a / (1 - (1 - rate)² (1 - a))`, and clearing `a` writes it as
the form below. Both readings of `ibdRecurrenceStep` inherit it: with `rate = m`
it is the island-model equilibrium `F_ST`, with `rate = c` it is Sved's `E[r²]`.

    Denotes: the rest point of the recurrence, under either reading.

    Empirical status: **VALIDATED** on the island reading
    (`validation/empirical/simcov/battery_pd1.py`), where it is
    reached through `fstIslandMultiplicativeEquilibrium`. Explicit
    Wright-Fisher symmetric island model, 200 demes, migration then
    reproduction with the census read POST-migration -- the composition
    convention `ibdRecurrenceStep` declares, and the one that matters, because
    the other ordering has a fixed point differing by `(1 - m)²`, a factor of
    four at `m = 0.5`. `F_ST` is the identity-probability convention on DISTINCT
    pairs, as a ratio of averages over loci; ten independent replicate
    metapopulations per cell.

      Nₑ    m        this def   simulated            rel
      200   0.0100    0.10963    0.10897 ± 0.00005    0.61%
      50    0.0100    0.32999    0.32714 ± 0.00009    0.87%
      13    0.1538    0.08839    0.08769 ± 0.00001    0.80%
      4     0.5000    0.04000    0.03936 ± 0.00001    1.63%
      2     0.2500    0.24324    0.23978 ± 0.00001    1.44%

    WHAT MAKES THIS A MEASUREMENT AND NOT THE THIRD UNINFORMATIVE MATCH. The
    rival closed form `1/(1 + 4 Nₑ m)` is carried on the SAME cells and is
    rejected there: 1.7%, 1.9%, 26%, 182%, 39%. The two forms differ in `m` and
    not in `4 Nₑ m`, so the earlier runs (`battery_bulk1`, `battery_bulk20`),
    which swept the compound parameter, could not tell them apart and passed
    both. Here `m` is swept 50-fold at fixed `4 Nₑ m` by SHRINKING `Nₑ`, and
    `4 Nₑ m` is swept 4-fold besides so the rival has a prediction span at all
    -- a constant prediction scores NO POWER and rejects nothing.

    Positive control: a panmictic pool split into 200 labelled demes reads
    `F_ST = -0.000000 ± 0.000007`, 0.05 sems from zero. That control is the one
    that matters here, because the with-replacement reading of the estimator
    returns `1/(2 Nₑ)` on the same design, which at `Nₑ = 2` is 0.25 against a
    signal of 0.24.

    The 0.6-1.6% residual is the finite-deme term the body is blind to. Repeating
    at 500 demes shrinks it in every cell -- 0.39%, 0.74%, 0.48%, 0.83%, 1.09% --
    by a factor of 1.2 to 2.0 against the 2.5 a pure `1/d` term would give, so a
    second correction of order `1/(2 Nₑ)` survives at the smallest deme sizes.
    Two further controls are recorded rather than gated, both agreeing to the
    percent that the discrete model differs from its diffusion limit: Wright's
    law with Latter's finite-deme factor at the small-`m` cell (1.1% high), and
    the Beta`(4Nμ, 4Nμ)` stationary variance in one population (2.0% and 0.7%
    high). Neither is a code fault; both are the size of the diffusion
    approximation at `2 Nₑ = 50`.

    argument_source: model. `Nₑ` and `m` are the simulation's own setup
    parameters, written into the update rule, never estimated from the
    replicates the oracle measures. -/
noncomputable def ibdRecurrenceFixedPoint (Ne rate : ℝ) : ℝ :=
  (1 - rate) ^ 2 / ((1 - rate) ^ 2 + 2 * Ne * rate * (2 - rate))


/-- **The island-model reading of the recurrence.**  Migration is the disrupting
event: the pair is identical only if neither lineage is a migrant, probability
`(1 - m)²`, and the parental copies either coalesced in the deme or were already
identical.

    Regime: the many-deme symmetric island model. The deme count is not a
    parameter here, and at small deme counts it must be: at fixed `4 Ne m`
    the simulated `F_ST` runs 0.117 at two demes to 0.186 at twenty, against
    a deme-blind 0.200. See `fstIslandEquilibriumFiniteDemes`.

    Empirical status: **VALIDATED**, including the
    argument forwarding (`validation/empirical/simcov/battery_bulk14.py`).
    Island-model Wright-Fisher, 40 demes, 3000 loci, run 220 generations past
    the transient and then tested as a one-step map at each of 120 further
    generations, `F_ST` read as `Var_between(p) / mean(pbar (1 - pbar))`:

      Ne     m        this def   simulated            sems
      200    0.002     0.32536   0.32563 ± 0.00195     0.14
      200    0.010     0.10990   0.10967 ± 0.00066     0.35
      500    0.005     0.08848   0.08860 ± 0.00053     0.23

    (worst of the 120 generations in each row)

    What this adds over the already-validated `ibdRecurrenceStep` it forwards to
    is the FORWARDING. A wrapper that delegates correctly and one that transposes
    its arguments are the same source text to a reading eye, so the battery calls
    this definition at its own declared signature `(Ne m F)` with `Ne` and `m`
    five orders of magnitude apart. A transposed forwarding would return
    6.7e+06, 1.8e+06 and 2.3e+07 in the three rows against a measurement near
    0.1: the check has a margin of seven orders of magnitude, rather than the
    few percent a same-scale design would have given it.

    Power: the prediction spans 0.088 to 0.325 across the design. -/
noncomputable def islandFstMultiplicativeStep (Ne m F : ℝ) : ℝ :=
  ibdRecurrenceStep Ne m F


/-- **Fixed point of the island-model recursion.**

`F* = (1-m)² / ((1-m)² + 2 Nₑ m (2 - m))`.  Expanding the denominator gives
`(1-m)² + 4 Nₑ m − 2 Nₑ m²`, so this reduces to `1/(1 + 4 Nₑ m)` only after
dropping terms of order `m²` and `m/Nₑ`; the two closed forms are never equal
for `m > 0`, which `ibdRecurrenceFixedPoint_lt_linearisation` proves in general
and `fstIslandMultiplicativeEquilibrium_ne_fstMigrationDriftEquilibrium`
witnesses at a point.

    Regime: the many-deme symmetric island model. The deme count is not a
    parameter here, and at small deme counts it must be: at fixed `4 Ne m`
    the simulated `F_ST` runs 0.117 at two demes to 0.186 at twenty, against
    a deme-blind 0.200. See `fstIslandEquilibriumFiniteDemes`.

    Empirical status: **VALIDATED**
    (`validation/empirical/simcov/battery_pd1.py`). This is the
    definition the battery actually calls, so the table and the design are the
    ones written out at `ibdRecurrenceFixedPoint`: explicit Wright-Fisher island
    model at 200 demes, `m` swept 50-fold at fixed `4 Nₑ m`, agreement within
    1.6% relative across the sweep while the rival `1/(1 + 4 Nₑ m)` misses by up
    to 182% on the same cells, panmictic control 0.05 sems from zero.

    The regime declared above is what the design respects and it is not
    decoration: 200 demes, not two. At two demes this body is wrong by roughly
    the factor its own regime paragraph records, and `battery_bulk40` measured
    exactly that -- 0.199 predicted against 0.104 simulated -- on a two-deme
    design that had no business testing a many-deme law.

    argument_source: model. -/
noncomputable def fstIslandMultiplicativeEquilibrium (Ne m : ℝ) : ℝ :=
  ibdRecurrenceFixedPoint Ne m


/-- **Island model equilibrium Fst under migration-drift balance.**
    Fst_eq = 1 / (1 + 4Nm) where N is effective size and m is migration rate.
    This is the classical Wright (1931) result.

    Regime: the infinite-island limit. `Descent.Core.islandDemeCorrection` carries the
    finite-deme factor this drops, and the identity below places this body inside
    `Descent.Core.fstIslandEquilibrium` so the discrepancy is a substitution rather than a
    comparison of two independent formulas. Simulation puts the law within 2% at 40
    demes, but +17% at 10, +31% at 5 and +95% at 2. The two-deme case is the
    two-ancestry comparison this development is mostly about, so the law is off
    by roughly twofold in its primary application. The finite-deme correction
    `1/(1 + 4 Nₑ m (d/(d-1))²)` repairs the 5-to-10 deme range and overshoots at
    `d = 2` by −40%.

    Empirical status: CONDITIONALLY VALID. Accurate in the limit it was derived
    for; frequently violated in use. Neither validated nor falsified. -/
noncomputable def fstMigrationDriftEquilibrium (Ne m : ℝ) : ℝ :=
  Descent.Core.fstFromFlow (4 * Ne * m)

/-- **The equilibrium decreases when the migration-drift product rises.**

Both monotonicities are this one fact: the equilibrium is `1 / (1 + 4 Ne m)`, so it falls
whenever `Ne * m` rises, and whether that happened by moving `m` or by moving `Ne` is the
caller's business.  Stated separately, each carried the same three-line proof. -/
theorem fstMigrationDriftEquilibrium_strictAnti_product (Ne₁ m₁ Ne₂ m₂ : ℝ)
    (h_pos : 0 < Ne₁ * m₁) (h_more : Ne₁ * m₁ < Ne₂ * m₂) :
    fstMigrationDriftEquilibrium Ne₂ m₂ < fstMigrationDriftEquilibrium Ne₁ m₁ := by
  unfold fstMigrationDriftEquilibrium Descent.Core.fstFromFlow
  apply div_lt_div_of_pos_left one_pos (by nlinarith) (by nlinarith)

/-- **Equilibrium Fst decreases with migration rate** (Ne fixed).
    More migration → more gene flow → less differentiation. -/
theorem fstMigrationDriftEquilibrium_decreases_with_m (Ne m₁ m₂ : ℝ)
    (hNe : 0 < Ne) (hm₁ : 0 < m₁) (h_more : m₁ < m₂) :
    fstMigrationDriftEquilibrium Ne m₂ < fstMigrationDriftEquilibrium Ne m₁ :=
  fstMigrationDriftEquilibrium_strictAnti_product Ne m₁ Ne m₂
    (by positivity) (by nlinarith)

/-- **One generation of the identity-by-descent balance.**

`F` is the probability that two gene copies drawn from the same subpopulation
are identical by descent (equivalently, `F_ST` measured against a total
population in which that probability is zero).  In one generation:

* drift makes a pair identical with probability `1/(2 Nₑ)` among the pairs that
  are not already identical, contributing `+(1 - F)/(2 Nₑ)`;
* each of the two lineages independently escapes the local identity class at
  rate `rate` -- by mutating away from its ancestral allelic state, or by being
  replaced by a migrant -- contributing `-2 · rate · F`.

`rate` is therefore whichever homogenising force is in play: `μ` for
mutation-drift balance, `m` for migration-drift balance, `μ + m` for both.
That the two forces enter identically is the whole content of
`islandModelFst_eq_mutationForm`.

Composition convention: this is the first-order (weak-force, large-`Nₑ`)
recursion, in which drift and the homogenising force are *added*, so their
within-generation ordering does not matter.  The unlinearised discrete-generation
recursion multiplies them instead -- see `islandFstMultiplicativeStep` -- and its fixed
point differs from this one at O(rate², rate/Nₑ).

    Empirical status: **VALIDATED**
    (`validation/empirical/simcov/battery_max.py`, `test_ibd_flow_step`).
    Wright-Fisher forward simulation, 4000 loci, 300 replicate populations, one
    generation of drift plus gene flow from a fixed source pool, `F` read as
    `1 - H/H_ancestral`:

      Ne     rate     this def   simulated            sems
      200    0.000     0.07459   0.07452±0.00030      0.22
      200    0.002     0.07018   0.07015±0.00028      0.09
      500    0.005     0.02596   0.02592±0.00010      0.43

    Power: the prediction spans 0.02596 to 0.07459 across the design. -/
noncomputable def ibdFlowStep (Ne rate F : ℝ) : ℝ :=
  F + (1 - F) / (2 * Ne) - 2 * rate * F

/-- **ibdFlowStep where its denominator vanishes, named.** The guard `2 * Ne` is zero at `Ne = 0`.
Lean returns `F - 2 * rate * F` there rather than the value the modelled quantity takes, and no
type error marks the point. Consumers must require `2 * Ne ≠ 0`. -/
theorem ibdFlowStep_at_ne0_is_junk (rate : ℝ) (F : ℝ) :
    ibdFlowStep 0 rate F = F - 2 * rate * F := by
  unfold ibdFlowStep
  norm_num

/-- **`1/(1 + 4 Nₑ · rate)` is the fixed point of the identity balance.**
Setting `(1 - F)/(2 Nₑ) = 2 · rate · F` gives `1 - F = 4 Nₑ · rate · F`, hence
`F = 1/(1 + 4 Nₑ · rate)`.  This single lemma is what pins every `1/(1 + θ)`
and `1/(1 + 4 N m)` in the development; none of them is stipulated. -/
theorem ibdFlowStep_fixedPoint (Ne rate : ℝ) (hNe : 0 < Ne) (hrate : 0 ≤ rate) :
    ibdFlowStep Ne rate (1 / (1 + 4 * Ne * rate)) = 1 / (1 + 4 * Ne * rate) := by
  have hprod : (0 : ℝ) ≤ 4 * Ne * rate := by positivity
  have hd : (0 : ℝ) < 1 + 4 * Ne * rate := by linarith
  have hd' : (1 : ℝ) + 4 * Ne * rate ≠ 0 := ne_of_gt hd
  have hNe' : Ne ≠ 0 := ne_of_gt hNe
  unfold ibdFlowStep
  field_simp
  ring

/-- **Complete fixation is a boundary the balance attains.**  With no
homogenising force the only fixed point is `F = 1`: drift runs to completion.
The closed form takes that value exactly, rather than approaching it. -/
@[simp] theorem ibdFlowStep_one_of_no_flow (Ne : ℝ) :
    ibdFlowStep Ne 0 1 = 1 := by
  unfold ibdFlowStep
  simp

/-- **Both twos in the identity-flow step are the ploidy.** Identity is created at
`1 / (ploidy · Nₑ)` per generation, and destroyed at `ploidy · rate` because either of the
two lineages of a sampled pair can be hit by the homogenising force. That second two is
what makes the fixed point `1 / (1 + 4 Nₑ · rate)` rather than `1 / (1 + 2 Nₑ · rate)`, so
it is the one a reader most needs pinned. -/
theorem ibdFlowStep_uses_coalescentTimeScale (Ne rate F : ℝ) :
    ibdFlowStep Ne rate F
      = F + (1 - F) / Descent.Core.coalescentTimeScale Ne - Descent.Core.ploidy * rate * F := by
  unfold ibdFlowStep Descent.Core.ploidy; rw [Descent.Core.coalescentTimeScale_eq]

end Descent.PopGen
