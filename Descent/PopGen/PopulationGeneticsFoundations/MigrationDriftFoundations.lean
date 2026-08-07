/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.PopGen.PopulationGeneticsFoundations.MutationDriftBalance
-- `Portability.effectiveSymmetricMigration` and `Portability.fstMigrationDriftEquilibrium`
-- are named below.
import Descent.Portability.PortabilityDrift

assert_below Descent.Blindness Descent.Conditionals Descent.Decision

-- LAYER DEBT. This file cannot yet assert it is below `Descent.Portability`, `Descent.Spectral`:
--   Spectral: reaches 2 module(s) -- `Descent.Spectral.CirculationDefect`,
--   `Descent.Spectral.SpectralDegradation`
--   Portability: reaches 10 module(s) -- `Descent.Portability.PortabilityDrift`,
--   `Descent.Portability.PortabilityDrift.ClosedPopulationRegime`,
--   `Descent.Portability.PortabilityDrift.Definitions` and 7 more
-- The repair is to move what it reaches for DOWN, not to move this file up.

namespace Descent.PopGen

open MeasureTheory

/-!
# `PopulationGeneticsFoundations.MigrationDriftFoundations`

Part of the split of `Descent/PopGen/PopulationGeneticsFoundations.lean`, which was 2,740 lines.

The parts are a FAN: each imports the parts that declare the symbols it names, and nothing
else. The split first made them a CHAIN -- each importing the one before, in the order the
original text ran -- which preserved every resolution the single file had and charged every
part a dependency on everything written above it, used or not. Recovering the real order is
the work that chain deferred: each part's identifiers were resolved against its siblings'
declarations, and the imports above are the answer, so what a part rests on is readable
from its header instead of inherited from its position in a file that no longer exists.

Where a cut falls inside a section, the section is reopened and reclosed by name. A section
scopes `variable`s and this file declares none at that level, so the reopening is exact.
-/

/-!
## Migration-Drift Balance: Population Genetics Foundations

The island model of migration-drift balance is a cornerstone of population genetics.
When populations exchange migrants at rate m per generation, drift and migration
reach an equilibrium Fst = 1/(1 + 4Nm). This section provides the pure population
genetics foundations for migration effects, independent of PGS portability.

Key results:
1. Island model Fst equilibrium and monotonicity properties
2. Stepping-stone model and isolation by distance
3. Migration homogenizes allele frequencies and LD
4. Admixture (recent migration pulses) and transient LD
5. Asymmetric migration and effective migration rates
-/

section MigrationDriftFoundations

/-! ### Island Model Equilibrium

**REGIME, stated once for everything in this section.** `1/(1 + 4·Nₑ·m)` is the
INFINITE-ISLAND LIMIT. It is the `d → ∞` case of the finite-island result

  `F_ST = 1 / (1 + 4·Nₑ·m·d/(d-1))`

for `d` demes, and it is not the finite-`d` answer. **This header used to quote
the SQUARED correction `(d/(d-1))²` here while `islandFstFiniteDemes` -- twenty
lines below, in this same section -- states the linear one, and the measurement
recorded on `islandDemeCorrection` excludes the square at 9.04 sems.** The two
were a straight contradiction inside one section. The linear form is the one
this corpus's `F_ST` convention has: see the attribution note on
`islandFstFiniteDemes` for which published statistic each form belongs to.

The correction factor `d/(d-1)` is `2` at `d = 2` and `1.5` at `d = 3`, so with two demes the limit
understates the migration pressure by a factor of two in
the scaled rate and overstates `F_ST` correspondingly. Nothing about the
expression `1/(1+4Nm)`
announces this, which is why every theorem below is a theorem about the limit
and not about a two-deme system. `islandFstFiniteDemes` states the finite form,
`islandFstFiniteDemes_lt_islandLimit` proves the limit is an overstatement at
every finite `d`, and `islandDemeCorrection_tendsto_one` proves the two agree
only in the limit.

The reason this matters here specifically: two-population comparisons are the
common case in this corpus, and `d = 2` is exactly where the limit is worst. -/

/-! **`islandDemeCorrection` is deleted here.**  It was
`Descent.Core.islandDemeCorrection` under a second name, and every reference now
calls the kernel.  The deme correction `d/(d-1)` is one quantity; two names for it is how a
factor-of-two disagreement survives unnoticed. -/

/-- Reference evaluation; see `Descent.Core.Ratios` for what these pin and why. -/
theorem islandDemeCorrection_at_reference_point :
    Descent.Core.islandDemeCorrection (1 / 2) = -1 := by
  unfold Descent.Core.islandDemeCorrection Descent.Core.ratio
  norm_num

/-- **The deme correction's junk branch, named.** At a single deme the correction diverges and
Lean returns `0`. Consumers must require `d ≠ 1`, and `islandFstFiniteDemes_one_deme_is_junk`
shows what the `0` does downstream. -/
theorem islandDemeCorrection_one_deme_is_junk : Descent.Core.islandDemeCorrection 1 = 0 := by
  unfold Descent.Core.islandDemeCorrection; exact Descent.Core.islandDemeCorrection_one_is_junk

/-- **Finite-island `F_ST` for `d` demes**, `F_ST = 1/(1 + 4·Nₑ·m·d/(d-1))`.

    **Attribution, corrected -- this is not Nei's.** The docstring used to cite
    "(Wright; Nei)". The form with the deme factor SQUARED,
    `1/(1 + 4·Nₑ·m·(d/(d-1))²)`, is Crow and Aoki (1984) for Nei's `G_ST` and is
    what Whitlock and McCauley (1999), Heredity 82:117--125, quote; naming Nei on
    the LINEAR form credits him with the form this corpus measured against his.

    The linear form is the ratio-of-coalescence-times statistic, Slatkin (1991),
    *Inbreeding coefficients and coalescence times*, Genetics Research
    58:167--175, which finds `F_ST` in the finite island model by that route. The
    derivation is short enough to check here: in the symmetric island model
    `E[T_within] = 2·Nₑ·d` and `E[T_between] = 2·Nₑ·d + (d-1)/(2·m)`, so
    `1 - E[T_within]/E[T_between] = 1/(1 + 4·Nₑ·m·d/(d-1))`, which is this body.

    **So the two forms are two STATISTICS, not two guesses at one number**, and
    the FALSIFIED verdict on the square recorded at `islandDemeCorrection` should
    be read that way: the measurement read `F_ST` as `1 - E[T_w]/E[T_b]` off the
    genealogies, which is exactly the quantity the linear form computes, so the
    square was on trial under a convention that is not its own. It is not
    evidence that Crow and Aoki are wrong about `G_ST`. What the corpus is
    entitled to say is that under ITS `F_ST` convention -- the Hudson
    ratio-of-averages one every `F_ST` here is written for -- the correction is
    linear. (At `d = 2` the two happen to coincide once the corpus's own
    two-population `Hudson = 2G/(1 + G)` bridge is applied: `G = 1/(1 + 4M)`
    maps to `1/(1 + 2M)`, which is the linear form there. That coincidence does
    NOT extend to `d > 2`, where the two-subpopulation bridge does not apply,
    and no `d > 2` conversion is claimed here.)

    Regime: `d` demes of equal size `Nₑ`, symmetric migration at rate `m`,
    mutation negligible relative to migration, and `F_ST` in the Hudson
    coalescence-time convention. This is the finite-`d`
    statement; `fstMigrationDriftEquilibrium` is its `d → ∞` limit.

    Empirical status: VALIDATED -- matches `validation/differential/refs.island_fst_finite_demes`,
    against which the differential check `islandModelFst-finite-demes` measures
    the corpus's limit form. This body is checked by
    `islandFstFiniteDemes-is-the-finite-form`, 12 cells, verdict FORMULA.

Power: across those 12 cells the predicted `F_ST` spans 0.0123 to 0.7091, a factor of 57, so
the correction is exercised over its whole range rather than at one deme count. The check
detects `scale x1.05`, `scale x0.5` and `transpose first two args`. The discriminating rival
is the limit form itself: `islandModelFst-finite-demes` evaluates `1/(1 + 4Nm)` on the
IDENTICAL grid, deliberately shared so the comparison is exact, and is off by up to 0.7454
relative. `d = 2` carries that separation -- the correction factor is 4 there -- and the
same grid restricted to large `d` could not have failed, since at `d = 40` the correction is
5% and at `d → ∞` it vanishes. -/
noncomputable def islandFstFiniteDemes (Ne m d : ℝ) : ℝ :=
  1 / (1 + 4 * Ne * m * Descent.Core.islandDemeCorrection d)

/-- **This is the master island law at zero mutation**, which is where it sits in the
lattice.

`Core.fstIslandEquilibrium Ne m mu d` is `1/(1 + 4·Ne·m·correction(d) + 4·Ne·mu)`. Setting
`mu = 0` leaves exactly this body, so the finite-deme migration-drift equilibrium is not a
separate law that happens to resemble the island one -- it is the island one with the
mutation channel switched off, which is one of the specialisations the master exists to
support.

Stating it here rather than trusting the shapes to match is the point: the two `4`s in this
body are inlined, and the master's come from `scaledMigrationRate`, where the ploidy
convention fixes them in a single place. Without this theorem an edit to that convention
would silently stop reaching this definition. -/
theorem islandFstFiniteDemes_eq_islandEquilibrium_no_mutation (Ne m d : ℝ) :
    islandFstFiniteDemes Ne m d
      = Descent.Core.fstIslandEquilibrium (Descent.Core.BigM.ofRate Ne m)
          (Descent.Core.Theta.ofRate Ne 0) d := by
  rw [Descent.Core.fstIslandEquilibrium_eq]
  unfold islandFstFiniteDemes
  ring_nf

/-- **The junk value here is not merely wrong, it is inverted.**

    At a single deme the correction is Lean's `0` rather than divergent, so the whole
    denominator collapses to `1` and this reports `F_ST = 1`: complete differentiation, at the
    one configuration where there is nothing to differentiate from and the true value is `0`.
    That is the difference between a harmless artifact and a wrong answer inside the domain, and
    it is why `d ≠ 1` is a condition on the quantity existing rather than a modelling choice. -/
theorem islandFstFiniteDemes_one_deme_is_junk (Ne m : ℝ) :
    islandFstFiniteDemes Ne m 1 = 1 := by
  unfold islandFstFiniteDemes
  rw [islandDemeCorrection_one_deme_is_junk]
  norm_num

/-- At two demes the correction is exactly `2`: the scaled migration rate is
`8·Nₑ·m`, not `4·Nₑ·m`. Stated as an equation because `d = 2` is the case the
corpus actually uses, and it is where the measurement separates the candidates
most sharply -- simulated `0.09743 ± 0.00432` against `0.11111` here and
`0.05882` for the superseded square. -/
theorem islandDemeCorrection_at_two : Descent.Core.islandDemeCorrection 2 = 2 :=
  Descent.Core.islandDemeCorrection_two

/-- The correction is strictly above `1` at every finite number of demes, so
the limit is never exact for a real population. -/
theorem one_lt_islandDemeCorrection (d : ℝ) (hd : 1 < d) :
    1 < Descent.Core.islandDemeCorrection d := by
  unfold Descent.Core.islandDemeCorrection Descent.Core.ratio
  have hpos : 0 < d - 1 := by linarith
  rw [lt_div_iff₀ hpos]; linarith

/-- **The infinite-island limit overstates `F_ST` at every finite `d`.** This is
the claim the section header makes, made machine-checked: a definition that is
correct in its regime and silent about the regime is still a defect, and this
is what stops the limit from being read as the general answer. -/
theorem islandFstFiniteDemes_lt_islandLimit (Ne m d : ℝ)
    (hNe : 0 < Ne) (hm : 0 < m) (hd : 1 < d) :
    islandFstFiniteDemes Ne m d < Portability.fstMigrationDriftEquilibrium Ne m := by
  unfold islandFstFiniteDemes Portability.fstMigrationDriftEquilibrium Descent.Core.fstFromFlow
  have hc : 1 < Descent.Core.islandDemeCorrection d := one_lt_islandDemeCorrection d hd
  have hNm : 0 < 4 * Ne * m := by positivity
  apply div_lt_div_of_pos_left one_pos (by nlinarith)
  nlinarith

/-- **And the two agree only in the limit.** Without this the phrase
"infinite-island limit" is prose; with it, the regime is a proved property of
the definition rather than a claim in a comment.

The limit is proved once, on the kernel, and this is the wrapper's inheritance of
it. `Descent.Core.islandDemeCorrection_sub_one` carries the sharper statement the proof of
the limit throws away: the correction exceeds one by exactly `1/(d-1)`, which is
what a reader deciding whether the many-deme form is usable at a given `d` actually
needs. -/
theorem islandDemeCorrection_tendsto_one :
    Filter.Tendsto Descent.Core.islandDemeCorrection Filter.atTop (nhds 1) :=
  Descent.Core.islandDemeCorrection_tendsto_one

/-- Island model Fst is the reciprocal of (1 + 4Nm). -/
theorem islandModelFst_eq_inv (Ne m : ℝ) :
    Portability.fstMigrationDriftEquilibrium Ne m = (1 + 4 * Ne * m)⁻¹ := by
  unfold Portability.fstMigrationDriftEquilibrium Descent.Core.fstFromFlow
  rw [one_div]

/-- **Island model Fst is strictly decreasing in migration rate.**
    The function m ↦ 1/(1 + 4Nm) is strictly anti-monotone for positive Ne. -/
theorem islandModelFst_strictAnti_m (Ne a b : ℝ) (hNe : 0 < Ne)
    (ha : 0 ≤ a) (hab : a < b) :
    Portability.fstMigrationDriftEquilibrium Ne b < Portability.fstMigrationDriftEquilibrium Ne a
      := by
  unfold Portability.fstMigrationDriftEquilibrium Descent.Core.fstFromFlow
  have hden_pos : 0 < 1 + 4 * Ne * a := by nlinarith
  have hden_lt : 1 + 4 * Ne * a < 1 + 4 * Ne * b := by nlinarith
  exact div_lt_div_of_pos_left one_pos hden_pos hden_lt

/-- **Island model Fst is strictly decreasing in Ne.**
    Larger populations have more effective migrants per generation. -/
theorem islandModelFst_strictAnti_Ne (m a b : ℝ) (hm : 0 < m)
    (ha : 0 ≤ a) (hab : a < b) :
    Portability.fstMigrationDriftEquilibrium b m < Portability.fstMigrationDriftEquilibrium a m
      := by
  unfold Portability.fstMigrationDriftEquilibrium Descent.Core.fstFromFlow
  have hden_pos : 0 < 1 + 4 * a * m := by nlinarith
  have hden_lt : 1 + 4 * a * m < 1 + 4 * b * m := by nlinarith
  exact div_lt_div_of_pos_left one_pos hden_pos hden_lt

/-- **When 4Nm > 1, Fst < 1/2** (one-migrant-per-generation rule).
    This is Wright's classical threshold: even one migrant per generation
    (Nm = 0.25, so 4Nm = 1) is enough to prevent substantial differentiation. -/
theorem islandModelFst_lt_half_of_one_migrant (Ne m : ℝ)
    (h_threshold : 1 < 4 * Ne * m) :
    Portability.fstMigrationDriftEquilibrium Ne m < 1 / 2 := by
  unfold Portability.fstMigrationDriftEquilibrium Descent.Core.fstFromFlow
  rw [div_lt_div_iff₀ (by nlinarith : 0 < 1 + 4 * Ne * m) (by norm_num : (0:ℝ) < 2)]
  linarith

/-- **When 4Nm ≫ 1, Fst ≈ 0.** Specifically, 4Nm > k implies Fst < 1/(1+k). -/
theorem islandModelFst_small_of_large_migration (Ne m k : ℝ)
    (hk : 0 < k)
    (h_large : k < 4 * Ne * m) :
    Portability.fstMigrationDriftEquilibrium Ne m < 1 / (1 + k) := by
  unfold Portability.fstMigrationDriftEquilibrium Descent.Core.fstFromFlow
  apply div_lt_div_of_pos_left one_pos (by linarith) (by nlinarith)

/-! ### Relationship between Migration and Mutation Effects on Fst -/

/-- **Migration-mutation equivalence for Fst.**
    Under the island model, the equilibrium Fst has the same functional form
    whether the homogenizing force is migration or mutation:
    Fst_migration = 1/(1+4Nm), Fst_mutation = 1/(1+4Neμ).
    The key parameter is the scaled rate 4N × (rate). -/
theorem islandModelFst_eq_mutationForm (Ne m : ℝ) :
    Portability.fstMigrationDriftEquilibrium Ne m
      = Descent.Core.fstFromFlow (4 * Ne * m) := by
  unfold Portability.fstMigrationDriftEquilibrium Descent.Core.fstFromFlow
  ring

/-- **Combined migration and mutation reduce Fst below either alone.**
    When both migration (m) and mutation (μ) act, the equilibrium Fst
    is 1/(1 + 4Nm + 4Neμ), which is below either individual equilibrium.

    **The deme count is missing from the signature, and the quantity depends on
    it.** Measured against msprime's symmetric island model at equilibrium
    (`validation/empirical/simcov/battery_verify.py`,
    `test_island_deme_count`), `Ne = 1000`, total emigration rate `m = 1e-3` so
    that `4*Ne*m = 4.0` is held FIXED, `mu = 1e-8`, Hudson `F_ST`, 24 replicates
    of 4 Mb, 40 diploids from each of two sampled demes:

      demes    this def    simulated F_ST
        2        0.2000    0.09314±0.01311     8.2 sems, +115 percent
        4        0.2000    0.16469±0.02700     1.3 sems
        8        0.2000    0.15502±0.01987     2.3 sems
       20        0.2000    0.14347±0.01971     2.9 sems

    The scaled rate `4*Ne*m` is identical in every row, so a formula in
    `(Ne, m, mu)` alone must return one number for all four; the measurement
    does not. The two-deme row is decisive on its own.

    Empirical status: **CONDITIONALLY VALID** -- exact in the many-deme limit it
    is now named for, and exact at no finite deme count. The correction
    `d/(d-1)` shrinks with `d` and never vanishes, so the measurements below,
    which reject this body at two demes and at twenty, are what a limit looks
    like when it is evaluated where the limit has not been taken. They are
    retained in full: they are the evidence for the restriction, not a defect
    report on the body.

    A consumer at finite `d` wants `fstIslandEquilibriumFiniteDemes`, which
    carries `nDemes` explicitly and is VALIDATED at `d = 2`. This body is the
    limit that one converges to.

    The FALSIFIED marker this replaces was earned by an earlier NAME. Called
    `fstMigrationMutationEquilibrium` it asserted it was the island-model
    equilibrium, which is false at small deme count; the repair recorded below
    was to rename rather than to edit, because a signature of `(Ne, m, mu)`
    cannot express a deme count and so no edit to the body could have fixed the
    claim. The marker outlived that repair.

    AT TWENTY DEMES (`simcov/battery_falsrepair_c2.py`). msprime symmetric
    island model, 20 demes of `Ne = 1000`, total emigration rate `m` spread over
    the 19 other demes, `mu = 1e-8`, 2 Mb at recombination `1e-8` so each
    replicate averages many genealogies, Hudson `F_ST` between demes 0 and 1,
    48 replicates, with `4 Ne m` swept sixteenfold:

      4Nem   this body   measured             sems   finite-deme (20/19)
       1.0    0.50000    0.51926 ± 0.01301    1.48     0.48717  (2.47)
       2.0    0.33333    0.31746 ± 0.00862    1.84     0.32203  (0.53)
       4.0    0.20000    0.19950 ± 0.00517    0.10     0.19192  (1.47)
       8.0    0.11111    0.10727 ± 0.00285    1.35     0.10614  (0.39)
      16.0    0.05882    0.05203 ± 0.00173    3.92     0.05605  (2.32)

    Worst 3.92 sems against the finite-deme form's 2.47. Control: the same
    engine at TWO demes and `4 Ne m = 4` reproduces the two-deme value at 0.91
    sems, and the two-deme form is excluded across the twenty-deme cells at up
    to 17.11 sems -- so the design can see a deme-count factor of two and does
    not see one here, while still rejecting this body.

    Power: the prediction spans 0.50000 to 0.05882 across the design, a factor
    of eight and a half. The superseded record had none: it held `4 Ne m` fixed
    and swept the deme count, so this body was constant at 0.2000 by
    construction.

    **A FIRST, LOOSER RUN OF THIS DESIGN SAID MATCH, AND THE DIFFERENCE WAS THE
    ERROR BARS.** `battery_falsrepair.py`'s `group_c` used 24 replicates with recombination switched
    off -- one genealogy per replicate -- and got sems
    five times wider, on which this body passed at 1.57 sems and the record
    above was nearly written as CONDITIONALLY VALID. The point estimates agree
    between the two runs; only the resolution changed. A verdict that flips on
    replicate count was never a verdict.

    WHAT THIS RUN DOES NOT SETTLE. At the two extreme cells the measurement
    deviates from BOTH candidate forms in OPPOSITE directions -- above both at
    `4 Ne m = 1`, below both at 16 -- which is the signature of an estimator
    systematic rather than of a wrong formula, Hudson `F_ST` being a
    ratio-of-averages read against a per-site parametric prediction. So the 3.92
    is an upper bound on this body's own error and the finite-deme form's 2.47
    is not a clean win over it. What would settle it is a design whose `F_ST`
    estimator is the same functional as the prediction. That is a reason this
    record does not claim the finite-deme form is validated HERE -- it is
    validated separately, on `fstIslandEquilibriumFiniteDemes`, at a design
    built for it.
    **The name was corrected, because the name was the falsity.** This body
    cannot express a deme-count factor -- its signature is `(Ne, m, mu)` and
    nothing else -- so no edit to the body can fix what the measurement above
    found. What could be fixed is the CLAIM: called
    `fstMigrationMutationEquilibrium`, it asserts it is the island-model
    equilibrium, which is false at small deme count; called
    `...ManyDemes`, it asserts it is the many-deme limit of one, and the limit
    it is the limit OF is now a definition in this file --
    `fstIslandEquilibriumFiniteDemes`, which carries `nDemes` explicitly and
    whose `islandDemeCorrection = d/(d - 1)` has since been measured and
    validated at `d = 2`.

    This is the whole content of the repair. A consumer at two or three demes
    now has to read a name that says the body does not apply to them, rather
    than a name that says it does. Documenting the restriction in prose while
    leaving the name unqualified is what let the two-deme error stand, and the
    same pattern was recorded on `asymmetricFst` in `PortabilityDrift`, whose
    name commits it to exactly two demes and which therefore could not be
    repaired this way at all. That one was repaired the other way instead: it
    now takes BOTH migration rates and returns the two-deme value at their sum,
    which is validated to 2.03 sems where the single-rate body it replaced was
    excluded at 79.9.
-/
noncomputable def fstMigrationMutationEquilibriumManyDemes (Ne m μ : ℝ) : ℝ :=
  Descent.Core.fstFromFlow (4 * Ne * m + 4 * Ne * μ)

/-- **The island-model equilibrium with the deme count carried explicitly.**

    `1 / (1 + 4 Ne m n/(n-1) + 4 Ne mu)`. The homogenising force a deme feels is
    not the emigration rate but the rate at which it receives lineages from the
    other `n - 1` demes, and at small `n` those differ by a factor that no value
    of `m` absorbs: at two demes the correction is 2, at forty it is 1.026.

    Empirical status: **VALIDATED**
    (`validation/empirical/simcov/battery_correct.py`,
    `correct_island_deme_count`). msprime symmetric island model at equilibrium,
    `Ne = 1000`, TOTAL emigration rate `m = 1e-3` held fixed so `4 Ne m = 4.0` is
    identical in every row, `mu = 1e-8`, Hudson `F_ST`, 40 replicates of 20 Mb:

      demes   limit form   this def   simulated          sems (this def)
        2         0.20000    0.11111  0.11698±0.01017     0.6
        3         0.20000    0.14286  0.13273±0.01669     0.6
        4         0.20000    0.15789  0.12658±0.01764     1.7
        6         0.20000    0.17241  0.17579±0.02036     0.2
       10         0.20000    0.18367  0.14297±0.01752     2.3
       20         0.20000    0.19194  0.18580±0.01879     0.3
       40         0.20000    0.19608  0.17114±0.01809     1.4

    Worst cell 2.3 sems against the limit form's 8.2 at two demes. The squared
    correction `(n/(n-1))^2` was also tried and is excluded: it gives 0.05882 at
    two demes, 5.7 sems low, where this form sits at 0.6.

    Power: at fixed `4 Ne m` the prediction spans 0.11111 to 0.19608 across the
    deme counts while the limit form is constant at 0.20000, so the design
    separates them by construction. -/
noncomputable def fstIslandEquilibriumFiniteDemes (Ne m μ nDemes : ℝ) : ℝ :=
  Descent.Core.fstFromFlow (4 * Ne * m * Descent.Core.islandDemeCorrection nDemes + 4 * Ne * μ)

/-- **This body and `Core.fstIslandEquilibrium` are the same function.**

Not a resemblance. The master is `fstFromFlow (scaledMigrationRate·correction +
scaledMutationRate)`, and each scaled rate is `2 · ploidy · Nₑ · rate`, which at the
diploid convention is the `4` written out here twice. Expanding the master gives this body
character for character.

The wrapper was tried and reverted when this module was split out of the monolith, and
the convention edges have since been written against the inlined form, so the bodies stay
as they are and the identity is stated instead. That is enough for the purpose: an edit to
`Core.ploidy` that this body failed to follow would now break THIS theorem, which is the
protection the wrapper would have given.

It was rediscovered numerically before it was written down --
`validation/empirical/extract/semantic_duplicates.py` reports the two agreeing at every one
of 200 sampled points, from the values alone. -/
theorem fstIslandEquilibriumFiniteDemes_eq_master (Ne m μ nDemes : ℝ) :
    fstIslandEquilibriumFiniteDemes Ne m μ nDemes
      = Descent.Core.fstIslandEquilibrium (Descent.Core.BigM.ofRate Ne m)
          (Descent.Core.Theta.ofRate Ne μ) nDemes := by
  rw [Descent.Core.fstIslandEquilibrium_eq]
  unfold fstIslandEquilibriumFiniteDemes Descent.Core.fstFromFlow
  ring_nf

/-- **fstIslandEquilibriumFiniteDemes at a single deme, named.** The finite-deme correction is
`nDemes / (nDemes - 1)`, whose divisor vanishes at one deme. The migration term is junk-zero
there, so the equilibrium reduces to the mutation-only form -- a single population reported as
differentiated from itself at the mutation-drift level, where in fact there is nothing to
differentiate from. Consumers must exclude it by hypothesis. -/
theorem fstIslandEquilibriumFiniteDemes_single_deme_is_junk (Ne m μ : ℝ) :
    fstIslandEquilibriumFiniteDemes Ne m μ 1 = 1 / (1 + 4 * Ne * μ) := by
  unfold fstIslandEquilibriumFiniteDemes Descent.Core.fstFromFlow
  rw [islandDemeCorrection_one_deme_is_junk]
  norm_num

/-- **The finite-deme equilibrium is the fixed point of the same identity balance**,
at the deme-corrected scaled rate. The correction multiplies the migration term and
nothing else, so the balance that produced the limit form produces this one at
`4 Nₑ m n/(n-1) + 4 Nₑ μ`. Without this the definition would be an equilibrium
stipulated as a closed form, which is the defect `EQUILIBRIUM_BUDGET` names. -/
theorem fstIslandEquilibriumFiniteDemes_isFixedPoint (Ne m μ nDemes : ℝ)
    (hNe : 0 < Ne) (hm : 0 ≤ m) (hμ : 0 ≤ μ)
    (hcorr : 0 ≤ Descent.Core.islandDemeCorrection nDemes) :
    scaledIdentityStep (4 * Ne * m * Descent.Core.islandDemeCorrection nDemes + 4 * Ne * μ)
        (fstIslandEquilibriumFiniteDemes Ne m μ nDemes) =
      fstIslandEquilibriumFiniteDemes Ne m μ nDemes := by
  have h4 : (0 : ℝ) ≤ 4 * Ne := by linarith
  have h : (0 : ℝ) ≤ 4 * Ne * m * Descent.Core.islandDemeCorrection nDemes + 4 * Ne * μ :=
    add_nonneg (mul_nonneg (mul_nonneg h4 hm) hcorr) (mul_nonneg h4 hμ)
  have hbody : fstIslandEquilibriumFiniteDemes Ne m μ nDemes =
      1 / (1 + (4 * Ne * m * Descent.Core.islandDemeCorrection nDemes + 4 * Ne * μ)) := by
    unfold fstIslandEquilibriumFiniteDemes Descent.Core.fstFromFlow
    ring
  rw [hbody]
  exact scaledIdentityStep_fixedPoint _ h

/-- **The many-deme limit is the deme-blind formula.** At `nDemes / (nDemes - 1) = 1`
the finite-deme equilibrium is exactly `fstMigrationMutationEquilibriumManyDemes`, which is
the precise sense in which the older definition is a limit rather than a law. -/
theorem fstIslandEquilibriumFiniteDemes_eq_limit_of_unit_correction
    (Ne m μ nDemes : ℝ) (h : Descent.Core.islandDemeCorrection nDemes = 1) :
    fstIslandEquilibriumFiniteDemes Ne m μ nDemes
      = fstMigrationMutationEquilibriumManyDemes Ne m μ := by
  unfold fstIslandEquilibriumFiniteDemes fstMigrationMutationEquilibriumManyDemes
    Descent.Core.fstFromFlow
  rw [h]; ring_nf

/-- **`fstMigrationMutationEquilibriumManyDemes` at the denominator, named.**
Migration and mutation enter the divisor additively, so an inadmissible negative migration rate
can cancel the leading one even with mutation absent. The equilibrium is reported as zero -- no
differentiation -- where the formula has no value at all. Consumers must exclude it by
hypothesis. -/
theorem fstMigrationMutationEquilibriumManyDemes_cancelling_terms_is_junk :
    fstMigrationMutationEquilibriumManyDemes 1 (-(1/4)) 0 = 0 := by
  unfold fstMigrationMutationEquilibriumManyDemes Descent.Core.fstFromFlow
  norm_num

/-- **The migration term's coefficient, pinned.**
`fstMigrationMutationEquilibriumManyDemes_isFixedPoint` is invariant under exactly the rescaling
it should exclude. At `4 Ne m = 1` with no mutation the equilibrium `Fst` is one half, which fixes
the factor four on the migration term. -/
theorem fstMigrationMutationEquilibriumManyDemes_migration_only :
    fstMigrationMutationEquilibriumManyDemes 1 (1 / 4) 0 = 1 / 2 := by
  unfold fstMigrationMutationEquilibriumManyDemes Descent.Core.fstFromFlow
  norm_num

/-- **The mutation term enters with the same coefficient, pinned.** Mutation and migration are
interchangeable at this order: `4 Ne mu = 1` with no migration gives the same equilibrium as
`4 Ne m = 1` with no mutation. Fixing the migration coefficient alone would leave the mutation
coefficient free. -/
theorem fstMigrationMutationEquilibriumManyDemes_mutation_only :
    fstMigrationMutationEquilibriumManyDemes 1 0 (1 / 4) = 1 / 2 := by
  unfold fstMigrationMutationEquilibriumManyDemes Descent.Core.fstFromFlow
  norm_num

/-- **The combined equilibrium is the rest point of the scaled identity balance
at the summed scaled rate.**  This is where the additivity of `θ` and `M` comes
from: one balance, one rate, and that rate is `4 Nₑ (m + μ)`. -/
theorem fstMigrationMutationEquilibriumManyDemes_isFixedPoint (Ne m μ : ℝ)
    (hNe : 0 < Ne) (hm : 0 ≤ m) (hμ : 0 ≤ μ) :
    scaledIdentityStep (4 * Ne * m + 4 * Ne * μ)
        (fstMigrationMutationEquilibriumManyDemes Ne m μ) =
      fstMigrationMutationEquilibriumManyDemes Ne m μ := by
  have h4 : (0 : ℝ) ≤ 4 * Ne := by linarith
  have h : (0 : ℝ) ≤ 4 * Ne * m + 4 * Ne * μ :=
    add_nonneg (mul_nonneg h4 hm) (mul_nonneg h4 hμ)
  have hbody : fstMigrationMutationEquilibriumManyDemes Ne m μ =
      1 / (1 + (4 * Ne * m + 4 * Ne * μ)) := by
    unfold fstMigrationMutationEquilibriumManyDemes Descent.Core.fstFromFlow
    ring
  rw [hbody]
  exact scaledIdentityStep_fixedPoint _ h

/-- Combined Fst is below migration-only Fst. -/
theorem fstMigrationMutation_lt_migrationOnly (Ne m μ : ℝ)
    (hNe : 0 < Ne) (hm : 0 < m) (hμ : 0 < μ) :
    fstMigrationMutationEquilibriumManyDemes Ne m μ < Portability.fstMigrationDriftEquilibrium Ne m
      := by
  unfold fstMigrationMutationEquilibriumManyDemes Portability.fstMigrationDriftEquilibrium
    Descent.Core.fstFromFlow
  apply div_lt_div_of_pos_left one_pos (by nlinarith) (by nlinarith)

/-- Combined Fst is below mutation-only Fst. -/
theorem fstMigrationMutation_lt_mutationOnly (Ne m μ : ℝ)
    (hNe : 0 < Ne) (hm : 0 < m) (hμ : 0 < μ) :
    fstMigrationMutationEquilibriumManyDemes Ne m μ
      < Descent.Core.fstFromFlow (4 * Ne * μ) := by
  unfold fstMigrationMutationEquilibriumManyDemes Descent.Core.fstFromFlow
  apply div_lt_div_of_pos_left one_pos (by nlinarith) (by nlinarith)

/-! ### Stepping-Stone Model Foundations -/

/-- **Characteristic length of one-dimensional isolation by distance.**
    `L = √(m·σ² / (2·μ))`, in units of the deme spacing. This is the Malécot /
    Kimura-Weiss decay scale: in an infinite linear array of demes with nearest-neighbour migration
    rate `m`, dispersal variance `σ²` and mutation
    rate `μ`, the probability that two genes sampled `d` demes apart are
    identical by descent falls off as `exp(-d/L)`.

    It is the balance point of two rates. At unit dispersal variance a lineage
    crosses a stretch of `L` demes in time `L²/m`, while mutation destroys
    identity in the two lineages at rate `2·μ`. Setting `L²/m = 1/(2·μ)` gives
    this body, and
    `steppingStoneCharacteristicLength_balances_mutation` states exactly that.

    **The mutation rate is mandatory and the deme size does not enter.** The
    form `√(2·Nₑ·m)` carries the deme size and no mutation rate. That is not a
    mis-set constant, it is the wrong function. `√(2·Nₑ·m)` is not even a
    length: `Nₑ` is a count of individuals, so the expression has units of
    √individuals, while `m/(2μ)` is a ratio of two per-generation rates and is
    dimensionless, as a squared deme count must be. The two forms disagree on
    both axes that matter. `√(2·Nₑ·m)` is constant in `μ` where the true scale
    goes as `μ^(-1/2)`, and grows as `√Nₑ` where the true scale does not depend
    on `Nₑ` at all. `validation/differential/heavy/h1_stepping_stone_length.py`
    measures those two exponents and is the standing check on this definition.

    **The dispersal variance is an explicit argument, and it is load-bearing.**
    `L` scales as `σ`, so a habitat with `σ² = 4` has a decay length twice that
    of one with `σ² = 1` -- a factor, not a rounding. A body that fixes `σ² = 1`
    has no argument with which to state the assumption, so every caller makes it
    and none writes it down.

    Regime: mutation-limited, i.e. distances comparable to `L`. Below `L`,
    isolation by distance is governed instead by the mutation-free coalescent
    result `DemographicHistory.demoSteppingStoneFst`, which is a different
    function and is derived separately.

    Measured on every axis that separates this body from `√(2·Nₑ·m)`:
    `d log L / d log μ = -0.502` against that form's `0`,
    `d log L / d log Nₑ = -0.000` against its `+1/2`, and
    `d log L / d log m = +0.510`. This body is confirmed and `√(2·Nₑ·m)` is
    excluded on two independent axes rather than one.

    Empirical status: MEASURED on all three axes above, and the body is the
    published Kimura-Weiss result. The dispersal-variance axis is MEASURED too:
    `d log L / d log σ² = +0.475` against `0` for a body without `σ²`, and the
    error from omitting `σ²` is `-26.9%` at `σ² = 2` and `-49.3%` at `σ² = 4`.

    Why an exponent is the decisive measurement here. A convention difference --
    infinite-alleles versus infinite-sites, say -- multiplies `μ` by a constant,
    which rescales every `L` UNIFORMLY AND CANNOT MOVE AN EXPONENT. A
    constant-factor discrepancy on this definition, of the +44% size seen here,
    therefore admits a convention artefact as its whole explanation and settles
    nothing. An exponent is immune to that entire class of explanation, which is
    why the `σ²` axis settles the question and is worth waiting for rather than
    estimating. The measured `+0.475` is the diffusion balance's `+1/2`.

    Signature consistency: both siblings carry a dispersal variance --
    `DemographicHistory.demoSteppingStoneFst (d Ne m σ_sq)` and
    `DemographicHistory.steppingStoneDiffusionTimescale (d σ_sq m)` -- so this
    signature matches the family. -/
noncomputable def steppingStoneCharacteristicLength (m σ_sq μ : ℝ) : ℝ :=
  Real.sqrt (m * σ_sq / (2 * μ))

/-- **steppingStoneCharacteristicLength at its junk point, named.** Without mutation there is no
scale at which isolation by distance saturates, so the characteristic length is unbounded. The
divisor is zero, the radicand is junk-zero, and the length is `0`: complete local isolation, the
opposite limit. Consumers must exclude the argument that makes the guard vanish. -/
theorem steppingStoneCharacteristicLength_no_mutation_is_junk (m σ_sq : ℝ) :
    steppingStoneCharacteristicLength m σ_sq 0 = 0 := by
  unfold steppingStoneCharacteristicLength
  simp

/-- The characteristic length scale is positive for positive migration,
    dispersal and mutation rates. -/
theorem steppingStoneCharacteristicLength_pos (m σ_sq μ : ℝ)
    (hm : 0 < m) (hσ : 0 < σ_sq) (hμ : 0 < μ) :
    0 < steppingStoneCharacteristicLength m σ_sq μ := by
  unfold steppingStoneCharacteristicLength
  exact Real.sqrt_pos.mpr (by positivity)

/-- **What the definition claims: the migration/mutation balance.**
    `L² · (2·μ) = m·σ²`, i.e. the time `L²/(m·σ²)` a lineage takes to diffuse
    `L` demes is exactly the time `1/(2·μ)` in which mutation destroys identity
    between two lineages. Stating it as an equation is what stops the body from
    drifting back to something containing `Nₑ`, and now also what pins the
    `σ²` scaling: no expression lacking `σ²` can satisfy it. -/
theorem steppingStoneCharacteristicLength_balances_mutation (m σ_sq μ : ℝ)
    (hm : 0 ≤ m) (hσ : 0 ≤ σ_sq) (hμ : 0 < μ) :
    steppingStoneCharacteristicLength m σ_sq μ ^ 2 * (2 * μ) = m * σ_sq := by
  unfold steppingStoneCharacteristicLength
  rw [Real.sq_sqrt (by positivity)]
  field_simp

/-- **The `σ² = 1` slice.** Anything stated about `√(m/(2μ))` is the unit-dispersal
    case of this, and not a different quantity. -/
theorem steppingStoneCharacteristicLength_at_unit_dispersal (m μ : ℝ) :
    steppingStoneCharacteristicLength m 1 μ = Real.sqrt (m / (2 * μ)) := by
  unfold steppingStoneCharacteristicLength
  norm_num

/-- **The decay scale grows with dispersal variance.** This is the axis that
    was just measured at `+0.475`, and on which a body without `σ²` is pinned
    at `0` and cannot move. -/
theorem steppingStoneCharacteristicLength_strictMono_dispersal
    (m σ₁ σ₂ μ : ℝ) (hm : 0 < m) (hσ₁ : 0 ≤ σ₁) (hμ : 0 < μ) (h : σ₁ < σ₂) :
    steppingStoneCharacteristicLength m σ₁ μ
      < steppingStoneCharacteristicLength m σ₂ μ := by
  unfold steppingStoneCharacteristicLength
  apply Real.sqrt_lt_sqrt (by positivity)
  apply div_lt_div_of_pos_right _ (by positivity)
  exact (mul_lt_mul_iff_right₀ hm).mpr h

/-- **The decay scale shrinks as mutation gets faster.**
    This is the axis on which the `√(2·Nₑ·m)` body was falsified: it is
    constant in `μ`, so it could not move here at all. -/
theorem steppingStoneCharacteristicLength_strictAnti_mutation (m σ_sq μ₁ μ₂ : ℝ)
    (hm : 0 < m) (hσ : 0 < σ_sq) (hμ₁ : 0 < μ₁) (h : μ₁ < μ₂) :
    steppingStoneCharacteristicLength m σ_sq μ₂
      < steppingStoneCharacteristicLength m σ_sq μ₁ := by
  unfold steppingStoneCharacteristicLength
  have hμ₂ : 0 < μ₂ := lt_trans hμ₁ h
  apply Real.sqrt_lt_sqrt
    (div_nonneg (mul_nonneg hm.le hσ.le) (mul_nonneg (by norm_num) hμ₂.le))
  exact div_lt_div_of_pos_left (by positivity) (by linarith) (by linarith)

/-- The decay scale grows with the migration rate. -/
theorem steppingStoneCharacteristicLength_strictMono_migration
    (m₁ m₂ σ_sq μ : ℝ) (hm₁ : 0 ≤ m₁) (hσ : 0 < σ_sq) (hμ : 0 < μ) (h : m₁ < m₂) :
    steppingStoneCharacteristicLength m₁ σ_sq μ
      < steppingStoneCharacteristicLength m₂ σ_sq μ := by
  unfold steppingStoneCharacteristicLength
  apply Real.sqrt_lt_sqrt (by positivity)
  apply div_lt_div_of_pos_right _ (by positivity)
  exact (mul_lt_mul_iff_left₀ hσ).mpr h

/-! ### `continuousSteppingStoneFst` has been deleted

The corpus carried a second stepping-stone F_ST,
`continuousSteppingStoneFst L d = 1 - exp(-d/L)`, evaluated at
`L = steppingStoneCharacteristicLength`. It contradicted
`DemographicHistory.demoSteppingStoneFst d Nₑ m σ² = d/(d + 4·Nₑ·m·σ²)` by up
to 878% on the differential grid, so at most one of the two could be right.

The contradiction is decidable without simulation, and it is decided against
the exponential. `demoSteppingStoneFst` is derived from the coalescent in
`DemographicHistory`: the meeting time of two lineages `d` demes apart is
linear in `d`, `T(d) = d/(2σ²m)`, and `F_ST = T/(T + 2Nₑ)` then gives the
hyperbolic `d/(d + 4Nₑσ²m)` exactly, with `steppingStoneFst_from_coalescence_time` proving that
equality. A linear
meeting time under the `T/(T+2Nₑ)` map cannot produce `1 - exp(-d/L)` for any
`L`: the two agree only to first order in `d`, and there they agree only if
`L = 4·Nₑ·m·σ²`, which is not the scale the corpus passed and is not a
mutation scale at all. The exponential had no derivation anywhere in the
corpus and no theorem tying it to anything.

Its three theorems -- `continuousSteppingStoneFst_nonneg`, `_increases` and
`_decreases_with_L` -- are absent with it, and their absence carries the
lesson. All three are monotonicity and sign facts, true of the exponential body
as written, and `d/(d + 4Nₑmσ²)` satisfies them equally. Facts of that shape
cannot detect a wrong functional form. Callers wanting a stepping-stone F_ST
should use `demoSteppingStoneFst`. -/

/-! ### Allele Frequency Homogenization by Migration -/

/-- **Allele frequency convergence under migration.**
    Starting from initial frequency p₀ in a deme, the frequency after t
    generations of migration at rate m toward a continent with frequency p_c is:
    p(t) = p_c + (p₀ - p_c) × (1-m)^t.
    The deviation from the continental frequency decays geometrically.

    Empirical status: **VALIDATED**
    (`validation/empirical/simcov/battery_bulk16.py`). Wright-Fisher with migration toward a fixed
    continent, `N = 40000` so drift stays far below the
    deterministic signal, 400 replicates, four times per parameter set:

      m        p0     p_c    worst of t in {5,15,30,60}     rel err
      0.010    0.8    0.2     1.95 sems                     0.03%
      0.050    0.9    0.3     under 2 sems                  under 0.03%
      0.002    0.1    0.6     under 2 sems                  under 0.03%

    Twelve cells at 0.03% relative, with the sign of `p0 - p_c` reversed in the
    third set so the approach is tested from both directions.

    Read a second way, `log |p_t - p_c|` is linear in `t` with slope
    `log (1 - m)`; the fitted slopes come out 0.21% steep, at 10.14 sems. That
    residual is an artifact of the readout and not of this body. `log` of a
    noisy quantity is biased downward by Jensen, and the bias grows as
    `|p_t - p_c|` shrinks toward the replicate noise, which steepens a fitted
    slope; the effect is largest in the `m = 0.05` set whose tail decays
    furthest. The trajectory reading, which involves no logarithm, agrees at
    0.03% across all twelve cells, and it is the one that carries the status.
    Both are reported because a 10-sem disagreement that is understood is worth
    more on the record than one that is dropped. -/
noncomputable def alleleFreqAfterMigration (p₀ p_c m : ℝ) (t : ℕ) : ℝ :=
  p_c + (p₀ - p_c) * (1 - m) ^ t

/-- After 0 generations of migration, frequency is unchanged. -/
theorem alleleFreqAfterMigration_at_zero (p₀ p_c m : ℝ) :
    alleleFreqAfterMigration p₀ p_c m 0 = p₀ := by
  unfold alleleFreqAfterMigration
  simp

/-- **Allele frequency converges toward continental frequency.**
    The deviation |p(t) - p_c| decreases with each generation of migration. -/
theorem alleleFreq_deviation_decreases (p₀ p_c m : ℝ) (t₁ t₂ : ℕ)
    (hm : 0 < m) (hm1 : m < 1)
    (hne : p₀ ≠ p_c) (ht : t₁ < t₂) :
    |alleleFreqAfterMigration p₀ p_c m t₂ - p_c| <
    |alleleFreqAfterMigration p₀ p_c m t₁ - p_c| := by
  unfold alleleFreqAfterMigration
  simp only [add_sub_cancel_left]
  rw [abs_mul, abs_mul]
  apply mul_lt_mul_of_pos_left
  · rw [abs_of_nonneg (pow_nonneg (by linarith) _),
        abs_of_nonneg (pow_nonneg (by linarith) _)]
    have h_base_pos : 0 < 1 - m := by linarith
    have h_base_lt : 1 - m < 1 := by linarith
    exact pow_lt_pow_right_of_lt_one₀ h_base_pos h_base_lt ht
  · exact abs_pos.mpr (sub_ne_zero.mpr hne)

/-! ### Effective Migration Rate -/

/-! **Effective migration is between the two directional rates** is
`effectiveSymmetricMigration_between`, stated beside `effectiveSymmetricMigration` itself in
`Descent.Portability.PortabilityDrift`, which this module imports.  It was restated here as
`effectiveMigration_bounds` with the same statement and the same two-line proof. -/

/-- Effective migration equals both rates when migration is symmetric. -/
theorem effectiveMigration_symmetric (m : ℝ) :
    Portability.effectiveSymmetricMigration m m = m := by
  unfold Portability.effectiveSymmetricMigration Descent.Core.midpoint
  ring

/-- **Asymmetric migration yields asymmetric Fst.**
    The population receiving more migrants has lower Fst (from its perspective).
    We prove the Fst difference is proportional to the migration asymmetry. -/
theorem asymmetric_fst_difference_sign (Ne m₁₂ m₂₁ : ℝ)
    (hNe : 0 < Ne) (hm₂₁ : 0 < m₂₁)
    (h_asym : m₂₁ < m₁₂) :
    Portability.fstMigrationDriftEquilibrium Ne m₁₂ < Portability.fstMigrationDriftEquilibrium Ne
      m₂₁ := by
  exact islandModelFst_strictAnti_m Ne m₂₁ m₁₂ hNe (le_of_lt hm₂₁) h_asym

/-! ### Migration and LD Homogenization -/

/-- **LD similarity between populations under migration.**
    Populations exchanging migrants share more similar LD patterns.
    We model the LD correlation as a function of scaled migration rate:
    LD_correlation(M) = M² / (1 + M)² (proportion of LD that is shared).
    This accounts for both allele frequency sharing and haplotype sharing.

    **This is a stipulation, not a derivation, and the name says so.** No source is
    cited, nothing derives this shape from a migration process, and no theorem here
    constrains it beyond monotonicity and range. Do not rename it to assert a derivation
    unless one is supplied.

    Empirical status: **FALSIFIED** (`simcov/battery_bulk51.py`, `group_a`).
    The comparison the paragraph above says nobody had made has now been made,
    and the ansatz does not survive it.

    Two-deme island model at `Nₑ = 1000` over 5 Mb with recombination; the
    observable is the cross-deme correlation of signed LD `r` across SNP pairs
    common in BOTH demes -- the quantity this body names -- with `4·Nₑ·m` swept a
    hundredfold:

      4Nₑm    measured LD correlation   this ansatz   M/(1+M)
      0.4     0.8908 ± 0.0196           0.0816        0.2857
      2.0     0.9414 ± 0.0057           0.4444        0.6667
      8.0     0.9747 ± 0.0027           0.7901        0.8889
      40      0.9898 ± 0.0004           0.9518        0.9756

    Worst cell 87 sems at 53% relative. The failure is worst at LOW migration,
    where the ansatz predicts almost no shared LD and the simulation finds
    nearly complete sharing. The unsquared `M/(1+M)` is carried alongside and is
    also FALSIFIED, at 48 sems -- so this is not a matter of one power too many.
    Both forms decay with migration; the measured correlation does not.

    Why: LD structure between two demes is set largely by the recombination
    history they SHARED before separating, and that persists long after
    migration has stopped homogenising allele frequencies. Neither form has a
    term for it. `PortabilityDrift.sharedLD_from_equilibrium` records the same
    finding from the other direction.

    Control: one panmictic population split into two arbitrary halves, through
    the same estimators and filters, gives `F_ST` indistinguishable from zero
    (0.41 sems).

    REBUILT AND RE-RUN, and the numbers above are superseded by these. The
    battery this cites had never been committed: the verdict was real when it
    was produced and no reader could check it, which is the same standing as no
    verdict. `simcov/battery_bulk51.py` is now in the repository, was run against
    the design described above, and its results are committed beside it (group_a).
    FALSIFIED at worst 102 sems (53% relative), and the unsquared `M/(1+M)` with it at
    61 sems -- so this is not a matter of one power too many. The measured cross-deme LD
    correlation does not fall with migration the way either form requires. The estimator
    is SPLIT-HALF: the naive correlation of r between demes is attenuated by the
    sampling noise in r itself, and the panmictic control detected that at twelve sems
    before the repair. It now passes at 1.0047 against a known 1.
    -/
noncomputable def ldCorrelationMigrationAnsatz (M : ℝ) : ℝ :=
  M ^ 2 / (1 + M) ^ 2

/-- **ldCorrelationMigrationAnsatz at `M = -1`, named.** The squared divisor `(1 + M) ^ 2`
vanishes at `M = -1`, and the ansatz returns zero correlation where it diverges. Squaring the
divisor makes the branch quadratically flat around the singularity, so sampling near it gives no
warning. Consumers must exclude it by hypothesis. -/
theorem ldCorrelationMigrationAnsatz_negative_unit_migration_is_junk :
    ldCorrelationMigrationAnsatz (-1) = 0 := by
  unfold ldCorrelationMigrationAnsatz
  norm_num

/-- LD correlation from migration is nonneg. -/
theorem ldCorrelationFromMigration_nonneg (M : ℝ) :
    0 ≤ ldCorrelationMigrationAnsatz M := by
  unfold ldCorrelationMigrationAnsatz
  exact div_nonneg (sq_nonneg M) (sq_nonneg (1 + M))

/-- LD correlation from migration is at most 1. -/
theorem ldCorrelationFromMigration_le_one (M : ℝ) (hM : 0 ≤ M) :
    ldCorrelationMigrationAnsatz M ≤ 1 := by
  unfold ldCorrelationMigrationAnsatz
  rw [div_le_one (sq_pos_of_pos (by linarith : 0 < 1 + M))]
  exact sq_le_sq' (by linarith) (by linarith)

/-- **LD correlation increases with migration rate.** -/
theorem ldCorrelationFromMigration_increases (M₁ M₂ : ℝ)
    (hM₁ : 0 < M₁) (h_more : M₁ < M₂) :
    ldCorrelationMigrationAnsatz M₁ < ldCorrelationMigrationAnsatz M₂ := by
  unfold ldCorrelationMigrationAnsatz
  have h1M₁ : 0 < 1 + M₁ := by linarith
  have h1M₂ : 0 < 1 + M₂ := by linarith
  have h_ratio : M₁ / (1 + M₁) < M₂ / (1 + M₂) := by
    rw [div_lt_div_iff₀ h1M₁ h1M₂]
    nlinarith
  have h_sq :
      (M₁ / (1 + M₁)) ^ 2 < (M₂ / (1 + M₂)) ^ 2 := by
    nlinarith [h_ratio, div_pos hM₁ h1M₁, div_pos (lt_trans hM₁ h_more) h1M₂]
  simpa [div_pow] using h_sq

end MigrationDriftFoundations

theorem fstMigrationMutationEquilibriumManyDemes_eq_scaled (Ne m μ : ℝ) :
    PopGen.fstMigrationMutationEquilibriumManyDemes Ne m μ
      = 1 / (1 + Descent.Core.scaledMigrationRate Ne m + Descent.Core.scaledMutationRate Ne μ) := by
  unfold PopGen.fstMigrationMutationEquilibriumManyDemes Descent.Core.fstFromFlow
  rw [Descent.Core.scaledMigrationRate_eq_ploidy_form,
    Descent.Core.scaledMutationRate_eq_ploidy_form]
  unfold Descent.Core.ploidy; ring_nf

/-- **The finite-deme island equilibrium carries the same two scaled rates.** Its
`4 Nₑ m` is `scaledMigrationRate` and its `4 Nₑ μ` is `scaledMutationRate`, exactly as in
the deme-blind limit form; the deme correction multiplies the migration rate and does not
touch either constant. Without this the `4` would be a third inlined ploidy convention. -/
theorem fstIslandEquilibriumFiniteDemes_eq_scaled (Ne m μ nDemes : ℝ) :
    PopGen.fstIslandEquilibriumFiniteDemes Ne m μ nDemes
      = 1 / (1 + Descent.Core.scaledMigrationRate Ne m * Descent.Core.islandDemeCorrection nDemes
              + Descent.Core.scaledMutationRate Ne μ) := by
  -- The bridge this used to go through, `fstIslandEquilibriumFiniteDemes_eq`, was
  -- deleted when the body was repointed at `Core.fstFromFlow`, which is `1/(1+x)`
  -- and needs no normalisation lemma of its own. What is left to say is that the
  -- two `4`s in the flow are the two scaled rates and not a third inlined ploidy
  -- convention, which is exactly what the two `_eq_ploidy_form` rewrites state.
  unfold PopGen.fstIslandEquilibriumFiniteDemes Descent.Core.fstFromFlow
  rw [Descent.Core.scaledMigrationRate_eq_ploidy_form,
    Descent.Core.scaledMutationRate_eq_ploidy_form]
  unfold Descent.Core.ploidy; ring_nf

/-- **The `2 μ` in the stepping-stone characteristic length counts the two lineages of a
sampled pair.** Mutation destroys the identity of a pair at rate `ploidy · μ`, so
`1 / (ploidy · μ)` is the time available to the diffusion and `L² = m σ² / (ploidy · μ)`
is the balance. Written inline the two read as arbitrary; it is the same two that
`Descent.Core.coalescentTimeScale` puts in front of `Nₑ`. -/
theorem steppingStoneCharacteristicLength_uses_ploidy (m σ_sq μ : ℝ) :
    PopGen.steppingStoneCharacteristicLength m σ_sq μ = Real.sqrt (m * σ_sq / (Descent.Core.ploidy *
      μ)) := by
  unfold PopGen.steppingStoneCharacteristicLength Descent.Core.ploidy; ring

end Descent.PopGen
