/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.PopGen.PopulationGeneticsFoundations
import Descent.PopGen.LDDecayTheory
import Descent.Core.Fst
import Descent.Layer

assert_below Descent.Blindness Descent.Conditionals Descent.Decision

-- LAYER DEBT. This file cannot yet assert it is below `Descent.Spectral`, `Descent.Portability`, `Descent.Program`:
--   Spectral: reaches 2 module(s) -- `Descent.Spectral.CirculationDefect`, `Descent.Spectral.SpectralDegradation`
--   Portability: reaches 10 module(s) -- `Descent.Portability.PortabilityDrift`, `Descent.Portability.PortabilityDrift.ClosedPopulationRegime`, `Descent.Portability.PortabilityDrift.Definitions` and 7 more
--   Program: reaches 1 module(s) -- `Descent.Program.Conclusions`
-- The repair is to move what it reaches for DOWN, not to move this file up.

namespace Descent.PopGen

open MeasureTheory

/-!
# Demographic History Models and PGS Portability

Formalizes how demographic histories (migration, admixture, bottlenecks,
expansion) affect PGS portability through their effects on F_ST and LD.

Provenance: derived here, not imported. Wang et al. (2026), Nature Communications 17:942,
substantiates nothing below. It is an empirical study of the polygenic-score portability
gap and does not treat island, admixture or bottleneck demographic models. Sources for
individual results, where they exist, are cited at those results.
-/


section IslandModel

/-! Island model equilibrium F_ST: `1 / (1 + 4·Ne·m)`.

    Empirical status: CONDITIONALLY VALID. A simulation check was attempted and was
    invalid, because the migration parameter was supplied per pair of demes, so
    total immigration scaled with the number of demes rather than being held
    fixed. The result of that run says nothing about this formula in either
    direction and must not be cited as support.

    Regime: this is the infinite-island limit. Simulation puts it within 2% at
    40 demes, but +17% at 10, +31% at 5 and +95% at 2. The two-deme case is
    in the infinite-island limit the two-ancestry comparison this development is about, so the law
    is off by roughly twofold in its primary application. The finite-deme
    correction `1/(1 + 4 Nₑ m (d/(d-1))²)` repairs the 5-to-10 deme range and
    overshoots at `d = 2` by −40%. No copy of this formula documented the
    assumption, and there are four of them in four files.

    Empirical status: CONDITIONALLY VALID. Accurate in the limit it was derived
    for; frequently violated in use. Neither validated nor falsified.

The theorems below are stated about `fstMigrationDriftEquilibrium` from
`Descent.PopGen.PopulationGeneticsFoundations`, which this file imports. Do not restate
`1/(1 + 4 Nₑ m)` here; the regime caveats above belong to that one definition. -/

/-- More migration → lower equilibrium F_ST.  The demographic reading of
`fstMigrationDriftEquilibrium_decreases_with_m`, which `Descent.Portability.PortabilityDrift`
proves:
this file names the consequence it uses rather than reproving it. -/
theorem more_migration_lower_fst (Ne m₁ m₂ : ℝ)
    (hNe : 0 < Ne) (hm₁ : 0 < m₁)
    (h_more : m₁ < m₂) :
    Portability.fstMigrationDriftEquilibrium Ne m₂ < Portability.fstMigrationDriftEquilibrium Ne m₁ :=
  Portability.fstMigrationDriftEquilibrium_decreases_with_m Ne m₁ m₂ hNe hm₁ h_more

/-! The island-model `F_ST` has one definition, `fstMigrationDriftEquilibrium`. A second
spelling in this module would need its own theorem tying it to that one, which is a
reason not to add it.

The constant is derived, not stipulated. `PortabilityDrift` defines a one-generation
migration-drift map, and `fstMigrationDriftEquilibrium_isFixedPoint` proves the constant is
a fixed point of that map. Without such a theorem the constant would rate only "unverified
but probably true". -/

end IslandModel


section SteppingStone

/-- **The hyperbolic stepping-stone `F_ST`, `d/(d + 4·Ne·m·σ²)` — VERIFIED by simulation.**

    The corpus decided this form against a deleted exponential rival by *derivation*, not
    measurement. Direct two-lineage stepping-stone simulation (circle `D = 64`, `Ne = 25`,
    `m = 0.2`, `σ² = 1`; lineages walk and coalesce with probability `1/(2Ne)` when
    co-located; `F_ST = 1 - T_within/T_between`) now confirms it independently:

    * in its own stated `d ≪ D` regime, RMS relative error **`0.058`**;
    * the best-fitted exponential `1 - exp(-d/L)`, with `L` fitted **freely to the
      measurement**, gives `0.103` — `1.8×` worse in the corpus form's own regime. The
      deletion of `continuousSteppingStoneFst` is corroborated by measurement, not only by
      derivation.

    **A better form exists that the corpus does not carry.** Replacing `d` by `d(D-d)/D` — the
    same coalescent derivation without the `d ≪ D` truncation — drops the RMS error across the
    whole range `d ≤ D/2` from `0.172` to **`0.061`**, removing essentially all of the
    far-field error. Per-`d` relative error of the current form runs `-0.10, -0.02, -0.01,
    +0.05, +0.18, +0.36` at `d = 1, 2, 4, 8, 16, 32`; the untruncated form stays flat.

    **The two compensating omissions this file documents are confirmed quantitatively.**
    Measured `T_within = 3136.9 = 2·D·Ne`, not the per-deme `2·Ne = 50` that `coalFst` is
    handed — a factor of `D = 64`. It cancels against the `(D-d) ≈ D` dropped from the meeting
    time, which is exactly why this definition is right anyway.

    Empirical status: **VALIDATED in its stated regime**
    (`validation/empirical/coalescent_diff/`),
    with the untruncated `d(D-d)/D` form recorded as the available improvement. -/
noncomputable def demoSteppingStoneFst (d Ne m σ_sq : ℝ) : ℝ :=
  d / (d + 4 * Ne * m * σ_sq)

/-- **demoSteppingStoneFst where its denominator vanishes, named.** The guard `d + 4 * Ne * m *
σ_sq` is zero at `d = 0`, `Ne = 0`, `m = 0`, `σ_sq = 0`. Lean returns `0` there rather than the
value the modelled quantity takes, and no type error marks the point. Consumers must require `d
+ 4 * Ne * m * σ_sq ≠ 0`. -/
theorem demoSteppingStoneFst_at_d0ne0m0sq0_is_junk :
    demoSteppingStoneFst 0 0 0 0 = 0 := by
  unfold demoSteppingStoneFst
  norm_num

/-- **The functional form the previous derivation produced**, retained so that the
indistinguishability recorded in the note above can be stated rather than asserted.

**DO NOT "CORRECT" THIS BODY. THE FALSIFICATION IS THE RESULT.** This is a
deliberate foil; the full statement of why, and of the two theorems that depend
on it, is at the end of this docstring. A directive to fix every falsified
definition does not reach this one.

    Empirical status: **FALSIFIED**
    (`validation/empirical/simcov/battery_verify.py`,
    `test_stepping_slope_tight`). Both this form and `demoSteppingStoneFst` have
    the shape `d / (d + K)`, so they cannot be told apart by any choice of
    `σ_sq` -- picking a value for an unstated convention moved the answer by two
    orders of magnitude, and a test whose verdict is set by a convention
    measures the convention. What no `σ_sq` can change is an EXPONENT.

    Fit `K = d (1 - F) / F` from a 16-deme 1D stepping stone, `Ne = 500`,
    interior demes 5 and 8 so no boundary reflection enters, recombining,
    30 replicates of 10 Mb, and read the log-log slope of `K` against `m`:

      m         F_ST                K
      0.005     0.21051±0.00383    11.251
      0.010     0.12634±0.00301    20.746
      0.020     0.06689±0.00202    41.853
      0.040     0.03552±0.00121    81.450
      0.080     0.01870±0.00078   157.447

      slope = 0.959 ± 0.010

    This form has `K` proportional to `m^2` and so predicts slope 2; the linear
    sibling `demoSteppingStoneFst` has `K` proportional to `m` and predicts
    slope 1. The measurement sits 101 sems from 2 and 4.0 sems from 1. The
    residual 4 sems from exactly 1 is a finite-lattice effect and is not the
    difference between the two candidates.

    This is the evidence `demoSteppingStoneFst_indistinguishable_from_quadratic`
    demands and no earlier measurement supplied. That theorem proves the two
    forms are indistinguishable while `σ²` is free, and states the consequence
    as a requirement: evidence for the FUNCTIONAL FORM needs `σ²` held at an
    independently determined dispersal scale while `m` varies. On a
    nearest-neighbour lattice the dispersal scale is fixed by the geometry and
    cannot move with `m`, so the design above satisfies exactly that condition
    and the tie is broken. The definition is kept, because stating the
    indistinguishability requires naming the rejected form.

    Power: `K` spans 11.251 to 157.447, a factor of fourteen, across the design;
    the two candidate exponents predict a factor of 16 and a factor of 256 over
    that same range of `m`. 
    **Independently reconfirmed** (`validation/empirical/simcov/battery_bulk17.py`).
    A separate 20-deme lattice realisation, `Ne = 500`, separation `d = 4`, four
    migration rates spanning a factor of eight, `K = d(1 - F)/F` read off at each
    and the exponent taken as the log-log slope of `K` against `m`:

      m        F_ST                K = d(1-F)/F
      0.004    0.30906 ± 0.01070    8.943
      0.008    0.20305 ± 0.00687   15.700
      0.016    0.11095 ± 0.00556   32.051
      0.032    0.05641 ± 0.00220   66.913

      fitted exponent  0.974 ± 0.042

    The linear form predicts 1 and this body predicts 2: the measurement sits
    0.62 sems from linear and 24.4 sems from quadratic. Same conclusion as the
    run recorded above, on different seeds and a different separation.

    An error in the first pass of that battery is worth recording, since it
    inverted a verdict. The comparison cells were signed backwards -- `K` GROWS
    with `m`, so the linear form predicts a slope of `+1`, not `-1` -- and the
    harness duly reported both candidates as failing by tens of sems. The
    measured number 0.974 was correct throughout; only the two predictions it
    was compared against carried the wrong sign.

    **A third, convention-free confirmation that needs no simulation at all: the
    body is not dimensionally homogeneous.** `Ne` enters population genetics only
    as a number of generations (`2 * Ne` is the coalescent time scale) and `m` is
    a per-generation rate, so `4 * Ne * m` is dimensionless and `4 * Ne * m * σ_sq`
    — the sibling `demoSteppingStoneFst`'s denominator term — carries exactly the
    units of `σ_sq`, which are the units `d` is counted in. Replacing `m * σ_sq`
    by `σ_sq ^ 2 * m ^ 2` multiplies that term by one extra factor of `m`, leaving
    a per-generation rate added to a distance. No choice of units for `d` or
    `σ_sq` can rescue it: whatever convention makes `demoSteppingStoneFst`
    homogeneous makes this body inhomogeneous by one power of time. That argument
    is exact, costs nothing, commits to no `F_ST` convention, and reaches the same
    verdict the two log-log slope measurements above reached — which is the point
    of recording it: three instruments that could each have said no, and none of
    them did.

    **DO NOT "CORRECT" THIS BODY. THE FALSIFICATION IS THE RESULT.**

    This definition is a FOIL, not a candidate law that failed. Its role is to be
    the wrong exponent, held next to the right one, so that a theorem can say what
    the data cannot distinguish. Two theorems in this file depend on it being
    exactly what it is:

    * `demoSteppingStoneFst_indistinguishable_from_quadratic` proves
      `demoSteppingStoneFst d Nₑ m σ² = steppingStoneFstQuadratic d Nₑ m √(σ²/m)`.
    * `steppingStoneCoalescenceTime_indistinguishable_through_coalFst` carries the
      same identity through the meeting time.

    Together they are a NON-IDENTIFIABILITY result: with `σ²` free, no amount of
    `F_ST` data separates the linear form from the quadratic one, so a fit
    constrains the product `m·σ²` and nothing else. That is the whole content, and
    it is why the regime note on `demoSteppingStoneFst` demands `σ²` be held at an
    independently measured dispersal variance.

    Replacing this body with `d / (d + 4·Nₑ·m·σ_sq)` makes it literally
    `demoSteppingStoneFst`. Both theorems above collapse to `x = x`, and the
    identifiability result is gone — deleted, not repaired. The three falsifying
    instruments recorded above are the DEMONSTRATION that this exponent is wrong;
    they are what the foil is for, not evidence against keeping it.

    A directive to fix every falsified definition does not reach this one. The
    alternative here is not "fix it"; the alternative is destroying a theorem. -/
noncomputable def steppingStoneFstQuadratic (d Ne m σ_sq : ℝ) : ℝ :=
  d / (d + 4 * Ne * σ_sq ^ 2 * m ^ 2)

/-- **steppingStoneFstQuadratic where its denominator vanishes, named.** The guard `d + 4 * Ne *
σ_sq ^ 2 * m ^ 2` is zero at `d = 0`, `Ne = 0`, `m = 0`, `σ_sq = 0`. Lean returns `0` there
rather than the value the modelled quantity takes, and no type error marks the point. Consumers
must require `d + 4 * Ne * σ_sq ^ 2 * m ^ 2 ≠ 0`. -/
theorem steppingStoneFstQuadratic_at_d0ne0m0sq0_is_junk :
    steppingStoneFstQuadratic 0 0 0 0 = 0 := by
  unfold steppingStoneFstQuadratic
  norm_num

/-- **A freely fitted dispersal variance cannot tell the two forms apart.**

The note on `demoSteppingStoneFst` says a refitted `σ²` absorbs the extra power exactly,
and that the fit therefore constrains the product `m·σ²` and nothing else. This is that
claim, proved: at `σ' = √(σ²/m)` the quadratic form takes the same value everywhere, so no
amount of `F_ST` data with `σ²` free can distinguish them.

The consequence is the regime, and it is now enforceable: evidence for the *functional
form* requires `σ²` held at an independently measured dispersal variance while `m` varies.
Evidence gathered with `σ²` free is evidence about `m·σ²`, whatever the fit quality — the
±11% agreement quoted in the note included. -/
theorem demoSteppingStoneFst_indistinguishable_from_quadratic
    (d Ne m σ_sq : ℝ) (hm : 0 < m) (hσ : 0 ≤ σ_sq) :
    demoSteppingStoneFst d Ne m σ_sq
      = steppingStoneFstQuadratic d Ne m (Real.sqrt (σ_sq / m)) := by
  unfold demoSteppingStoneFst steppingStoneFstQuadratic
  have hnn : (0 : ℝ) ≤ σ_sq / m := div_nonneg hσ (le_of_lt hm)
  rw [Real.sq_sqrt hnn]
  have hm' : m ≠ 0 := ne_of_gt hm
  congr 2
  field_simp

/-- Stepping-stone F_ST increases with geographic distance. -/
theorem stepping_stone_fst_increasing (d₁ d₂ Ne m σ_sq : ℝ)
    (hNe : 0 < Ne) (hm : 0 < m) (hσ : 0 < σ_sq)
    (hd₁ : 0 < d₁) (h_farther : d₁ < d₂) :
    demoSteppingStoneFst d₁ Ne m σ_sq < demoSteppingStoneFst d₂ Ne m σ_sq := by
  unfold demoSteppingStoneFst
  have h_C := mul_pos (mul_pos (mul_pos (by norm_num : (0:ℝ) < 4) hNe) hm) hσ
  rw [div_lt_div_iff₀ (by linarith) (by linarith)]
  nlinarith

/-- Stepping-stone F_ST saturates below 1 at any finite distance. -/
theorem stepping_stone_fst_saturates (d Ne m σ_sq : ℝ)
    (hNe : 0 < Ne) (hm : 0 < m) (hσ : 0 < σ_sq)
    (hd : 0 < d) :
    demoSteppingStoneFst d Ne m σ_sq < 1 := by
  unfold demoSteppingStoneFst
  rw [div_lt_one (by nlinarith [mul_pos (mul_pos hNe hm) hσ])]
  linarith [mul_pos (mul_pos (mul_pos (by norm_num : (0:ℝ) < 4) hNe) hm) hσ]

/-! ### Derivation of stepping-stone Fst from the coalescent

In a one-dimensional stepping-stone model with demes of effective size Ne,
migration rate m between adjacent demes, and dispersal variance σ², two
lineages separated by d demes must first meet before they can coalesce. Both
lineages move, so their separation diffuses at twice the single-lineage
coefficient m·σ², and the expected extra time to meet is

  T(d) = d / (2 · σ² · m)

Once in the same deme, coalescence takes an expected 2·Ne generations, so

  Fst(d) = T(d) / (T(d) + 2·Ne)                                     [`coalFst`]
         = [d/(2σ²m)] / ([d/(2σ²m)] + 2·Ne)
         = d / (d + 4·Ne·σ²·m)

which is `demoSteppingStoneFst d Ne m σ_sq`, and is what
`steppingStoneFst_from_coalescence_time` proves. Equivalently
Fst/(1 - Fst) = d/(4·Ne·m·σ²), the standard Malécot/Rousset linear
isolation-by-distance relation in one dimension.

Writing T(d) = d/(σ²·m) drops the factor 2 from the relative diffusion, and
recovering the factor 4 by passing `2·Ne·σ²·m` as the effective size to
`coalFst` -- which is not an effective size -- gives
d/(d + 4·Ne·σ⁴·m²), a different function of the parameters from the definition
it claimed to derive, and no theorem related the two. The 1/2 belongs in the
meeting time and the effective size argument is Ne.

Cross-check against the island model, which uses the same `T/(T + 2Ne)` map:
two lineages in different demes each migrate at rate m, so they meet at rate
2m, giving T = 1/(2m) and Fst = [1/(2m)]/([1/(2m)] + 2Ne) = 1/(1 + 4·Ne·m),
Wright's result. The factor 4 in both formulas comes from that meeting rate
being 2m (or 2·m·σ²), not from any separate diploid doubling.
-/

/-- **Meeting time at distance d in the stepping-stone model.**
    T(d) = d / (2 · σ² · m), the expected extra time for lineages separated by
    d demes to first occupy the same deme. The 2 is the relative diffusion of
    two independently moving lineages; omitting it was the error in the
    previous derivation (see the block comment above).

    **REGIME: this is a PER-DEME meeting time, not the meeting time.** On a
    finite lattice of `D` demes the expected time for two lineages `d` demes
    apart to first share a deme is `d·(D-d)/(2·σ²·m)`. This body omits the
    factor `(D-d)` entirely, and the omission is not small: at `d = 1`,
    `D = 256` this expression gives `5.0` where the measured meeting time is
    `1344.2`. Read as a standalone number of generations it is wrong by that
    factor. `steppingStoneMeetingTimeOnLattice` states the lattice quantity and
    `steppingStoneMeetingTime_eq_scaled` proves the exact relation between
    them, so the missing factor is now visible rather than implicit.

    **Why no consumer-level check could have caught this, which is the reason
    it survived.** The only thing this feeds is `coalFst _ Ne`, and `coalFst`
    is handed the PER-DEME size `Ne` rather than the metapopulation size
    `D·Ne`. The lattice size therefore cancels between the two arguments, and
    `demoSteppingStoneFst` comes out right to 4.4% despite the meeting time
    being off by `(D-d)`. Two compensating omissions in a ratio look exactly
    like a correct ratio from outside. Anything that consumes this value on its
    own, or pairs it with a metapopulation-scale `Ne`, will be wrong by
    `(D-d)`; that pairing is a load-bearing convention and not an incidental
    choice of argument.

    **This is a diffusion timescale, not a coalescence time.** As the note above
    records, it is MEASURED off by exactly `(D-d)` as a standalone meeting time, and it
    yields a correct `demoSteppingStoneFst` only because that error cancels against a
    per-deme `Nₑ`.

    Empirical status: MEASURED and off by exactly `(D-d)` as a standalone
    meeting time. Its consequence `demoSteppingStoneFst` is CONDITIONALLY
    VALID -- RMS relative error 0.044 with σ² SET rather than fitted, against
    0.622 for a quadratic, 0.335 for a linear and 0.163 for a freely fitted
    exponential form. Note that this is the σ²-held-fixed comparison the
    docstring on `demoSteppingStoneFst` records as not yet done; it has now
    been done and the derived form wins. -/
noncomputable def steppingStoneDiffusionTimescale (d σ_sq m : ℝ) : ℝ :=
  d / (2 * σ_sq * m)

/-- **steppingStoneDiffusionTimescale at zero σ_sq, named.** With no dispersal variance a lineage
never moves between demes and the diffusion timescale is infinite. Lean returns `0`: instantaneous
mixing across the lattice, the opposite regime. Consumers must require `σ_sq ≠ 0`. -/
theorem steppingStoneDiffusionTimescale_zero_sigmasq_is_junk (d : ℝ) (m : ℝ) :
    steppingStoneDiffusionTimescale d 0 m = 0 := by
  unfold steppingStoneDiffusionTimescale
  simp

/-- **Expected meeting time on a lattice of `D` demes**, `d·(D-d)/(2·σ²·m)`:
    the quantity `steppingStoneDiffusionTimescale` is a per-deme rescaling of.
    Stated so that the corpus contains the lattice-level time under a name,
    rather than only the rescaled one under a name that does not say it is
    rescaled.

    Denotes: `d` is the lattice separation between the two sampled demes and
    `demeCount` is `D`, the total number of demes, with `0 ≤ d ≤ demeCount`. The
    two are not interchangeable and the formula is not symmetric in them —
    swapping them flips the sign whenever `d < demeCount`, as the guard below
    measures. -/
noncomputable def steppingStoneMeetingTimeOnLattice
    (d demeCount σ_sq m : ℝ) : ℝ :=
  d * (demeCount - d) / (2 * σ_sq * m)

/-- **steppingStoneMeetingTimeOnLattice at zero σ_sq, named.** The same zero-dispersal branch as
the diffusion timescale, with the same reversal: lineages that can never move are reported as
meeting immediately. Consumers must require `σ_sq ≠ 0`. -/
theorem steppingStoneMeetingTimeOnLattice_zero_sigmasq_is_junk (d : ℝ) (demeCount : ℝ) (m : ℝ) :
    steppingStoneMeetingTimeOnLattice d demeCount 0 m = 0 := by
  unfold steppingStoneMeetingTimeOnLattice
  simp

/-- **The guard against the argument swap.**

    A meeting time is nonnegative on the admissible range `0 ≤ d ≤ D`. The omission of such a
    fact has teeth here, because the `d`/`D` arguments differ
    only in case, and a swap **always flips the sign** when `d < D`, so it returns a *negative
    expected time*. In exact rationals at `D = 256`: `d = 1` gives `1275` correct against
    `-326400` swapped, `d = 8` gives `9920` against `-317440`, `d = 128` gives `81920` against
    `-163840`. Nothing catches that unless something asserts the sign, which is what this
    theorem does.

    Verified numerically at `D = 64`: measured over predicted is `1.026, 1.027, 1.006, 1.004`
    at `d = 4, 8, 16, 32`.

    **A worse collision remains, and no theorem can guard it.** `σ_sq` and `m` enter only
    through the product `2·σ_sq·m`, so a `σ_sq ↔ m` swap is *exactly invisible* — no test,
    simulation or theorem can detect it — and the three siblings in this file order them
    inconsistently: `demoSteppingStoneFst (d Ne m σ_sq)`, `steppingStoneDiffusionTimescale
    (d σ_sq m)`, and this one `(d D σ_sq m)`. `demoSteppingStoneFst` is symmetric in the two
    as well. That hazard is documentation-only by construction. -/
theorem steppingStoneMeetingTimeOnLattice_nonneg (d demeCount σ_sq m : ℝ)
    (hd : 0 ≤ d) (hdD : d ≤ demeCount) (hσ : 0 < σ_sq) (hm : 0 < m) :
    0 ≤ steppingStoneMeetingTimeOnLattice d demeCount σ_sq m := by
  unfold steppingStoneMeetingTimeOnLattice
  have hden : 0 < 2 * σ_sq * m := by positivity
  apply div_nonneg _ (le_of_lt hden)
  exact mul_nonneg hd (by linarith)

/-- **The exact factor between the two**, which is `(D - d)` and nothing else.
    Proving it as an equation is what stops the per-deme convention from being
    reintroduced silently: any future body for either one that does not differ
    by exactly this factor stops compiling. -/
theorem steppingStoneMeetingTime_eq_scaled (d demeCount σ_sq m : ℝ) :
    steppingStoneMeetingTimeOnLattice d demeCount σ_sq m
      = (demeCount - d) * steppingStoneDiffusionTimescale d σ_sq m := by
  unfold steppingStoneMeetingTimeOnLattice steppingStoneDiffusionTimescale
  ring

/-- **The two agree only when `D - d = 1`**, i.e. essentially never for a
    lattice worth modelling. Stated as the contrapositive of the regime: if a
    reader takes `steppingStoneDiffusionTimescale` for the meeting time, this is
    the assumption they have made without writing it down. -/
theorem steppingStoneMeetingTime_eq_perDeme_iff (d demeCount σ_sq m : ℝ)
    (hd : 0 < d) (hσ : 0 < σ_sq) (hm : 0 < m) :
    steppingStoneMeetingTimeOnLattice d demeCount σ_sq m
      = steppingStoneDiffusionTimescale d σ_sq m ↔ demeCount - d = 1 := by
  rw [steppingStoneMeetingTime_eq_scaled]
  constructor
  · intro h
    have hpos : 0 < steppingStoneDiffusionTimescale d σ_sq m := by
      unfold steppingStoneDiffusionTimescale
      apply div_pos hd; have := mul_pos hσ hm; linarith
    have := mul_right_cancel₀ (ne_of_gt hpos) (by linarith :
      (demeCount - d) * steppingStoneDiffusionTimescale d σ_sq m =
        1 * steppingStoneDiffusionTimescale d σ_sq m)
    linarith
  · intro h; rw [h, one_mul]

/-! **Fst from coalescence time ratio**: `Fst = T/(T + 2Ne)`. This is `coalFst` from
`Descent.PopGen.PopulationGeneticsFoundations`; use it rather than restating it here. -/

/-- **Derivation, and the theorem that pins the definition.**
    With T(d) = d/(2·σ²·m) and effective size Ne:

      Fst = T/(T + 2·Ne) = [d/(2σ²m)] / ([d/(2σ²m)] + 2·Ne)

    Multiplying numerator and denominator by 2·σ²·m:

      = d / (d + 4·Ne·σ²·m)

    which is exactly `demoSteppingStoneFst d Ne m σ_sq`. Stating the conclusion
    as an equation between the derivation and the definition -- rather than as
    a free-standing closed form, which lets the two disagree -- means a
    replacement body for either one stops typechecking.

    A conclusion of `d / (d + 4·Ne·σ⁴·m²)` from `coalFst _ (2·Ne·σ²·m)` feeds a
    non-effective-size into the effective-size slot and compensates for a
    missing 1/2 in the meeting time. That is a different function from the
    definition, and no theorem equates them. -/
theorem steppingStoneFst_from_coalescence_time (d Ne m σ_sq : ℝ)
    (hd : 0 < d) (hNe : 0 < Ne) (hm : 0 < m) (hσ : 0 < σ_sq) :
    coalFst (steppingStoneDiffusionTimescale d σ_sq m) Ne =
      demoSteppingStoneFst d Ne m σ_sq := by
  unfold coalFst steppingStoneDiffusionTimescale demoSteppingStoneFst Descent.Core.oddsLike
  have hσm : (0 : ℝ) < 2 * σ_sq * m := by
    have h := mul_pos hσ hm; linarith
  have hσm' : (2 : ℝ) * σ_sq * m ≠ 0 := ne_of_gt hσm
  have hT : (0 : ℝ) < d / (2 * σ_sq * m) := div_pos hd hσm
  have hTden : d / (2 * σ_sq * m) + 2 * Ne ≠ 0 :=
    ne_of_gt (by linarith)
  have hden : d + 4 * Ne * m * σ_sq ≠ 0 := by
    have h4 : (0 : ℝ) < 4 * Ne * m * σ_sq :=
      mul_pos (mul_pos (mul_pos (by norm_num : (0:ℝ) < 4) hNe) hm) hσ
    exact ne_of_gt (by linarith)
  field_simp
  ring


/-- **The meeting time inherits the indistinguishability of the `F_ST` it produces.**

`steppingStoneDiffusionTimescale` is the only route by which `demoSteppingStoneFst` acquires
its dispersal variance, so the freedom that makes the `F_ST` unidentifiable is freedom in
this quantity. Stated so the meeting time carries the regime rather than borrowing it
silently from a theorem three declarations away: a refitted `σ²` changes the meeting time
and leaves the observable `F_ST` fixed, which is what it means for the data to constrain
`m·σ²` and not the dispersal variance itself. -/
theorem steppingStoneCoalescenceTime_indistinguishable_through_coalFst
    (d Ne m σ_sq : ℝ) (hd : 0 < d) (hNe : 0 < Ne) (hm : 0 < m) (hσ : 0 < σ_sq) :
    coalFst (steppingStoneDiffusionTimescale d σ_sq m) Ne =
      steppingStoneFstQuadratic d Ne m (Real.sqrt (σ_sq / m)) := by
  rw [steppingStoneFst_from_coalescence_time d Ne m σ_sq hd hNe hm hσ]
  exact demoSteppingStoneFst_indistinguishable_from_quadratic d Ne m σ_sq hm (le_of_lt hσ)

/-- The coalescence time is positive for positive distance and dispersal. -/
theorem steppingStoneCoalescenceTime_pos (d σ_sq m : ℝ)
    (hd : 0 < d) (hσ : 0 < σ_sq) (hm : 0 < m) :
    0 < steppingStoneDiffusionTimescale d σ_sq m := by
  unfold steppingStoneDiffusionTimescale
  positivity

/-- Fst from coalescence time is in (0, 1) for positive parameters. -/
theorem fstFromCoalescenceTime_in_unit (T Ne : ℝ)
    (hT : 0 < T) (hNe : 0 < Ne) :
    0 < coalFst T Ne ∧ coalFst T Ne < 1 := by
  unfold coalFst Descent.Core.oddsLike
  constructor
  · positivity
  · rw [div_lt_one (by linarith)]; linarith

end SteppingStone


section AdmixtureModels

/-- Two-way admixed F_ST: (1-α)² × F_ST(A,B).

    **REGIME: the numerator only.** `F_ST` is a ratio, and the derivation
    below computes the NUMERATOR ratio correctly -- simulation confirms it is
    exactly `(1-α)²`, so the algebra in this file survives intact -- and then
    divides by `p̄(1-p̄)` as though the DENOMINATOR were the same for the
    (admixed, A) pair as for the (A, B) pair. It is not. The admixed population
    has its own mean allele frequency, so its heterozygosity term differs, and
    the measured denominator ratio runs from `0.978` at `α = 0.1` down to
    `0.428` at `α = 0.9`. This body assumes that ratio is `1`.

    The consequence is a one-sided bias, never a wash: measured error
    `-2.2%` to `-19.9%` across `α = 0.1 … 0.9` at `F_ST = 0.222`, and `-6.4%`
    to `-57.2%` at `F_ST = 0.633`. It is always NEGATIVE -- this body
    understates admixed `F_ST` -- and `admixedFst_le_exact` below proves that
    sign rather than leaving it as an observation, since a bias whose direction
    is known is a different object from one that merely happened to be negative
    in the runs performed.

    Second, separate assumption: NO POST-ADMIXTURE DRIFT. With 20 generations
    of drift after the admixture event the error reaches `-82.8%`. Nothing in
    the expression carries a time since admixture, so this is an assumption the
    body cannot even express.

    Empirical status: MIXED -- NUMERATOR VALIDATED (exactly `(1-α)²`), DENOMINATOR
    OMITTED, and **FALSIFIED as a whole `F_ST`** at 14.16 sems
    (`simcov/battery_max.py`, logged in `simcov/ledger.json` under battery `max`),
    which is the omitted denominator measured rather than argued. Use
    `admixedFstExact` when the heterozygosity ratio is available.

    The number is worth carrying next to the body and not only in the ledger,
    because it is the smaller of a pair and the pair is the finding: on the same
    design `admixedFstExact` with the ratio applied UPSIDE DOWN reached 21.3 sems,
    so a correction made the answer worse than omitting it. That comparison is
    recorded on `admixedFstExact` below and is what fixes the ratio's orientation.
    A reader who meets only this definition's 14.16 would take it for the cost of
    the missing denominator; it is the cost of the missing denominator only when
    the present one points the right way. -/
noncomputable def admixedFst (α fst_AB : ℝ) : ℝ :=
  (1 - α) ^ 2 * fst_AB

/-- **Two-way admixed F_ST with the heterozygosity ratio carried**, rather than
    assumed to be one:

      `F_ST(adm, A) = (1-α)² · F_ST(A,B) / hetRatio`

    where `hetRatio = p̄_adm(1-p̄_adm) / p̄_AB(1-p̄_AB)` is the ratio of the
    denominator heterozygosity of the (admixed, A) pair to that of the (A, B)
    pair. This is the quantity `admixedFst` computes when that ratio is `1`.

    Empirical status: **EXACT BY CONSTRUCTION in the orientation stated above,
    and therefore not an empirical claim.**
    (`validation/empirical/simcov/battery_dis1.py`). Simulated one-pulse
    admixture with no post-admixture drift, Nei `G_ST` as a ratio of averages
    over 40000 loci: this body reproduces the measured `F_ST(adm, A)` to machine
    precision at `α = 0.2, 0.5, 0.8`, and the harness returns SELF-TEST. That is
    the right answer and not a disappointing one -- the numerator ratio being
    exactly `(1-α)²` is a real measured fact, recorded on `admixedFst` above, and
    once it holds this definition is that fact times an identity.

    What the ratio's ORIENTATION is, however, is empirical, and getting it
    backwards is a real error rather than a convention: `battery_max.py`
    reported this body FALSIFIED at 21.3 sems while `admixedFst`, which assumes
    the ratio is `1`, missed by only 14.2 -- a correction that made the answer
    worse, which is the signature of a divisor applied upside down. Divide by
    `p̄_adm(1-p̄_adm) / p̄_AB(1-p̄_AB)` and not by its reciprocal.

    Still assumed, and not repaired by carrying the ratio: NO POST-ADMIXTURE
    DRIFT, as recorded on `admixedFst`. Nothing in this expression carries a time
    since admixture either. -/
noncomputable def admixedFstExact (α fst_AB hetRatio : ℝ) : ℝ :=
  (1 - α) ^ 2 * fst_AB / hetRatio

/-- **admixedFstExact at zero hetRatio, named.** A heterozygosity ratio of zero means the admixed
population carries no heterozygosity to normalise against, and the corrected `Fst` is undefined.
Lean returns `0`, reporting no differentiation, which is what a freely interbreeding pair of
populations also gives. Consumers must require `hetRatio ≠ 0`. -/
theorem admixedFstExact_zero_hetratio_is_junk (α : ℝ) (fst_AB : ℝ) :
    admixedFstExact α fst_AB 0 = 0 := by
  unfold admixedFstExact
  simp

/-- **The regime, made checkable.** `admixedFst` is exactly the `hetRatio = 1`
    case. A future edit that changes either body without preserving this stops
    compiling. -/
theorem admixedFstExact_at_one (α fst_AB : ℝ) :
    admixedFstExact α fst_AB 1 = admixedFst α fst_AB := by
  unfold admixedFstExact admixedFst
  ring

/-- **The heterozygosity correction enters as a divisor, pinned.** `admixedFstExact_at_one`
identifies the exact form with `admixedFst` when the heterozygosity ratio is one, which
constrains the two definitions jointly and says nothing about how the ratio enters away from
one. Doubling the admixed heterozygosity halves the differentiation. -/
theorem admixedFstExact_double_heterozygosity (fst_AB : ℝ) :
    admixedFstExact 0 fst_AB 2 = fst_AB / 2 := by
  unfold admixedFstExact
  ring

/-- **The sign of the bias is forced, not observed.** The measured
    heterozygosity ratio is below one at every admixture proportion tested, and
    whenever it is, `admixedFst` understates the true admixed `F_ST`. This is
    why every measured error is negative; it is a property of the omission, not
    a fact about which parameter values happened to be simulated. -/
theorem admixedFst_le_exact (α fst_AB hetRatio : ℝ)
    (hfst : 0 ≤ fst_AB) (hpos : 0 < hetRatio) (hle : hetRatio ≤ 1) :
    admixedFst α fst_AB ≤ admixedFstExact α fst_AB hetRatio := by
  unfold admixedFst admixedFstExact
  rw [le_div_iff₀ hpos]
  nlinarith [sq_nonneg (1 - α), mul_nonneg (sq_nonneg (1 - α)) hfst]

/-- Admixed F_ST < parent F_ST for any admixture proportion α ∈ (0,1). -/
theorem admixed_fst_smaller (α fst_AB : ℝ)
    (hα : 0 < α) (hα1 : α < 1) (h_fst : 0 < fst_AB) :
    admixedFst α fst_AB < fst_AB := by
  unfold admixedFst
  have h1 : (1 - α) ^ 2 < 1 := by
    apply (sq_lt_one_iff_abs_lt_one _).mpr
    rw [abs_of_nonneg (by linarith)]; linarith
  calc (1 - α) ^ 2 * fst_AB < 1 * fst_AB := mul_lt_mul_of_pos_right h1 h_fst
    _ = fst_AB := one_mul _

/-- **PGS trained in parent population has intermediate portability to admixed.**
    Better than to the other parent, worse than to itself.
    Model: R² to admixed = α · R²(A→A) + (1-α) · R²(A→B) for admixture
    proportion α from population A. Since R²(A→B) < R²(A→A) and 0 < α < 1,
    the weighted average is strictly between the two parent values. -/
theorem convexCombination_strictly_between
    (r2_AA r2_AB α : ℝ)
    (h_gap : r2_AB < r2_AA)
    (hα : 0 < α) (hα1 : α < 1) :
    r2_AB < α * r2_AA + (1 - α) * r2_AB ∧
      α * r2_AA + (1 - α) * r2_AB < r2_AA := by
  constructor
  · -- r2_AB = 0 · r2_AA + 1 · r2_AB < α · r2_AA + (1-α) · r2_AB
    nlinarith
  · -- α · r2_AA + (1-α) · r2_AB < α · r2_AA + (1-α) · r2_AA = r2_AA
    nlinarith

/-- Optimal admixed PGS (convex combination) is between the two parent values. -/
theorem min_le_convexCombination_le_max
    (pgs_A pgs_B α : ℝ)
    (hα : 0 ≤ α) (hα1 : α ≤ 1) :
    min pgs_A pgs_B ≤ α * pgs_A + (1 - α) * pgs_B ∧
      α * pgs_A + (1 - α) * pgs_B ≤ max pgs_A pgs_B := by
  constructor
  · by_cases h : pgs_A ≤ pgs_B
    · simp [min_eq_left h]; nlinarith
    · push_neg at h; simp [min_eq_right (le_of_lt h)]; nlinarith
  · by_cases h : pgs_A ≤ pgs_B
    · simp [max_eq_right h]; nlinarith
    · push_neg at h; simp [max_eq_left (le_of_lt h)]; nlinarith

/-! ### Derivation of admixed Fst from allele frequency mixing

Consider an admixed population formed as a mixture of population A (proportion α)
and population B (proportion 1-α). The admixed allele frequency is:

  p_adm = α · p_A + (1-α) · p_B

The Fst between the admixed population and its source population A is
defined via the variance of allele frequency differences:

  Fst(adm, A) = Var(p_adm - p_A) / [p̄(1-p̄)]

where p̄ is the mean allele frequency. Computing the numerator:

  p_adm - p_A = α · p_A + (1-α) · p_B - p_A
              = (1-α) · (p_B - p_A)

Therefore:

  Var(p_adm - p_A) = (1-α)² · Var(p_B - p_A)
                    = (1-α)² · Fst(A, B) · p̄(1-p̄)

Dividing by p̄(1-p̄):

  Fst(adm, A) = (1-α)² · Fst(A, B)

This is `admixedFst α fst_AB`.
-/

/-- **Allele frequency in the admixed population.**
    p_adm = α · p_A + (1-α) · p_B.

    Regime: generation zero of a single pulse, ancestry assigned per
    individual. This is the frequency in the MIXTURE, so it needs no assumption
    about mating or linkage.

    Empirical status: **VALIDATED** (`simcov/battery_bulk30.py`). Measured as
    the realised allele frequency in a simulated admixed sample of 6×10⁶
    individuals whose ancestry is drawn at rate `α` and whose alleles are then
    drawn from the assigned ancestry's frequency. Worst cell 0.91 sems at 0.02%
    relative, with `α` swept 0.2 to 0.8 and the ancestral frequencies differing
    by up to 0.8.

    The companion `LDDecayTheory.admixtureLD` is measured on the SAME draws and
    is where the power lives: three competing forms of the mixing weight are
    falsified there at up to 1627 sems. That matters here because both bodies
    read `α` as the same mixing proportion, so a design that fixed the weight
    for one fixes the reading for the other. -/
noncomputable def admixedAlleleFreq (α p_A p_B : ℝ) : ℝ :=
  Descent.Core.convexCombination α p_A p_B

/-- Reference evaluation; see `Descent.Core.Ratios` for what these pin and why. -/
theorem admixedAlleleFreq_at_reference_point :
    admixedAlleleFreq 1 1 1 = 1 := by
  norm_num [admixedAlleleFreq, Descent.Core.convexCombination]


/-- **Key algebraic identity**: the difference between admixed and source A
    allele frequencies is (1-α) times the parental difference.
    This is the core of the (1-α)² derivation. -/
theorem admixed_freq_diff (α p_A p_B : ℝ) :
    admixedAlleleFreq α p_A p_B - p_A = (1 - α) * (p_B - p_A) := by
  unfold admixedAlleleFreq Descent.Core.convexCombination
  ring

/-- **Derivation**: If variance of allele frequency differences satisfies
    Var(p_adm - p_A) = (1-α)² · Var(p_B - p_A), and Fst(A,B) is defined as
    Var(p_B - p_A) / [p̄(1-p̄)], then Fst(adm, A) = (1-α)² · Fst(A,B).

    We express this as: for any set of loci, the mean squared frequency
    difference between admixed and source is (1-α)² times the mean squared
    frequency difference between parents. -/
theorem admixedFst_from_freq_variance (α : ℝ) (var_parent pbar_term : ℝ) :
    (1 - α) ^ 2 * var_parent / pbar_term =
      admixedFst α (var_parent / pbar_term) := by
  unfold admixedFst
  ring

/-- **No admixture, no reduction.** `admixedFst_le_exact` bounds this above and
`admixedFst_from_freq_variance` ties it to the frequency variance, and a body carrying `α ^ 2`
in place of `(1 - α) ^ 2` satisfies both. At `α = 0` the recipient population has received no
ancestry from the donor and its differentiation from the donor is unchanged; the swapped body
returns zero here. -/
theorem admixedFst_no_admixture (fst_AB : ℝ) :
    admixedFst 0 fst_AB = fst_AB := by
  unfold admixedFst
  ring

/-- **The exponent on the admixture fraction, pinned.** `admixedFst_no_admixture` fixes the
orientation and leaves the exponent free: `(1 - α) * fst` agrees with it at `α = 0`. Half
ancestry from the donor quarters the differentiation, not halves it -- the square is what makes
admixture cost differentiation faster than it costs ancestry. -/
theorem admixedFst_at_half_admixture (fst_AB : ℝ) :
    admixedFst (1 / 2) fst_AB = fst_AB / 4 := by
  unfold admixedFst
  ring

/-- **Per-locus derivation**: at a single locus with parental frequencies p_A and p_B,
    the squared frequency difference between admixed and source is (1-α)² times the
    squared parental difference. Summing over loci gives the Fst relationship. -/
theorem admixed_squared_diff (α p_A p_B : ℝ) :
    (admixedAlleleFreq α p_A p_B - p_A) ^ 2 = (1 - α) ^ 2 * (p_B - p_A) ^ 2 := by
  rw [admixed_freq_diff]
  ring

end AdmixtureModels


/-!
### Recent expansion and the singleton spectrum

Removed.  This section defined `singletonProportion N₀ N₁ = 1 - log N₀ / log N₁`
and proved monotonicity and endpoint results about it.  Coalescent simulation
falsifies the identification decisively: the formula does not track the
singleton proportion under exponential growth.  The theorems were correct about
the formula and wrong about the quantity it was named for, which is the failure
this development is trying to eliminate, so they are deleted rather than
weakened.
-/


section ArchaicIntrogression

/-- **Cumulative introgressed variants.**
    Given an ancestral variant mass `N₀` and a constant introgression rate `r`,
    the cumulative introgressed contribution after time `t` is
    `N₀ * (1 - exp(-r * t))`. -/
noncomputable def introgressionVariants (N₀ introgressionRate t : ℝ) : ℝ :=
  N₀ * (1 - Real.exp (-introgressionRate * t))

/-- Reference evaluation; see `Descent.Core.Ratios` for what these pin and why. -/
theorem introgressionVariants_at_reference_point :
    introgressionVariants 1 1 1 = 1 - Real.exp (-1) := by
  norm_num [introgressionVariants]



/-- **Differential introgression creates population-specific variants.**
    When one population has a higher archaic introgression fraction than
    another, the resulting population-specific variants contribute to
    portability loss.

    Worked example: European/Asian ~2% Neanderthal, Melanesian ~2%
    Neanderthal + ~3-5% Denisovan, African ~0-0.3% archaic. -/
theorem introgression_creates_population_specific_variants
    (N₀ t rHigh rLow : ℝ)
    (hN : 0 < N₀)
    (ht : 0 < t)
    (h_diff : rLow < rHigh) :
    introgressionVariants N₀ rLow t < introgressionVariants N₀ rHigh t := by
  unfold introgressionVariants
  have h_exp_arg : -rHigh * t < -rLow * t := by
    nlinarith
  have h_exp_lt : Real.exp (-rHigh * t) < Real.exp (-rLow * t) := by
    exact Real.exp_lt_exp.mpr h_exp_arg
  have h_inner : 1 - Real.exp (-rLow * t) < 1 - Real.exp (-rHigh * t) := by
    linarith
  exact mul_lt_mul_of_pos_left h_inner hN

/-- **Introgression fraction of heritability is bounded.**
    When introgressed heritability is at most a fraction δ of total
    heritability, the introgression share is bounded by δ.

    Worked example: For most traits, introgression contributes < 1%
    of total heritability. -/
theorem introgression_gap_bounded
    (h2_total h2_intro δ : ℝ)
    (h_total : 0 < h2_total)
    (h_small : h2_intro ≤ δ * h2_total) :
    h2_intro / h2_total ≤ δ := by
  exact (div_le_iff₀ h_total).mpr h_small

end ArchaicIntrogression


section FounderEffects

/-- **Within-population heterozygosity loss after `t` generations in a founding
    population of size `k`**: `1 - (1 - 1/(2k))^t`.

    **This is NOT between-population `F_ST`, and the gap is not a convention fork or a
    factor of two -- they are different quantities with different limits.** At
    `Nₑ = 1000`, `t = 4000` this expression's retention factor gives `0.135` against a
    measured `1.025 ± 0.020`, and the `F_ST` its cluster reports is approximately zero
    where the measurable between-population `F_ST` at that design point is `0.50`.
    Reading this as a differentiation measure is not slightly off; it is the wrong axis.

    **For between-population `F_ST` after a split use
    `PopulationGeneticsFoundations.coalFst t Ne = t / (t + 2 Nₑ)`**, which coalescent
    simulation in branch mode -- which removes mutational noise analytically -- finds
    unbiased across the tested grid.

    `heterozygosityLossFromDrift` in
    `PopulationGeneticsFoundations` are this same quantity.

    Regime: closed population, no mutation. `founderHeterozygosityLoss_eq_derived`
    below pins it to the `θ = 0` slice of the general transient, which is what makes
    the no-mutation premise explicit rather than implied.

    Empirical status: MIXED -- correct for what it says; FALSIFIED as an `F_ST`. -/
noncomputable def founderHeterozygosityLoss (k : ℕ) (t : ℕ) : ℝ :=
  1 - (1 - 1 / (2 * (k : ℝ))) ^ t

/-- **founderHeterozygosityLoss at its junk point, named.** A founding population of zero loses all
heterozygosity at once. The per-generation retention is junk-one, so the loss is `0` at every
generation count: no founder effect whatsoever, reported for the most extreme founder event
possible. Consumers must exclude the argument that makes the guard vanish. -/
theorem founderHeterozygosityLoss_zero_founders_is_junk (t : ℕ) :
    founderHeterozygosityLoss 0 t = 0 := by
  unfold founderHeterozygosityLoss
  simp

/-- Smaller founding population → larger heterozygosity loss (more drift). -/
theorem smaller_founder_larger_heterozygosity_loss
    (k₁ k₂ : ℕ) (t : ℕ)
    (hk₂ : 2 < k₂)
    (h_smaller : k₂ < k₁) (ht : 0 < t) :
    founderHeterozygosityLoss k₁ t < founderHeterozygosityLoss k₂ t := by
  unfold founderHeterozygosityLoss
  have h_base : 1 - 1 / (2 * (k₂ : ℝ)) < 1 - 1 / (2 * (k₁ : ℝ)) := by
    rw [sub_lt_sub_iff_left]
    apply div_lt_div_of_pos_left one_pos
    · exact Nat.cast_pos.mpr (by omega) |> (fun h ↦ mul_pos (by norm_num : (0:ℝ) < 2) h)
    · exact mul_lt_mul_of_pos_left (Nat.cast_lt.mpr h_smaller) (by norm_num : (0:ℝ) < 2)
  have h_nn : 0 ≤ 1 - 1 / (2 * (k₂ : ℝ)) := by
    rw [sub_nonneg, div_le_one (by positivity)]
    have : (2 : ℝ) ≤ k₂ := by exact Nat.ofNat_le_cast.mpr (by omega)
    linarith
  linarith [pow_lt_pow_left₀ h_base h_nn (by omega : t ≠ 0)]

/-- **Connection to derived formula**: `founderHeterozygosityLoss` equals the pure-drift
    specialization of `fstMutationDriftTransientDiscrete` from
    `PopulationGeneticsFoundations.lean`.

    When θ = 0 (no mutation), the transient Fst formula reduces to:
    - `fstMutationDriftEquilibrium 0 = 1/(1+0) = 1`
    - `hetDecayFactor k 0 = (1 - 1/(2k)) · (1 - 0) = 1 - 1/(2k)`
    - `fstMutationDriftTransientDiscrete 0 k t = 1 · (1 - (1 - 1/(2k))^t)`
                                                = 1 - (1 - 1/(2k))^t

    This is exactly `founderHeterozygosityLoss k t`, confirming that the founder effect
    formula is the pure-drift case of the general heterozygosity recurrence
    derived in `PopulationGeneticsFoundations`. -/
theorem founderHeterozygosityLoss_eq_derived (k : ℕ) (t : ℕ) :
    founderHeterozygosityLoss k t = fstMutationDriftTransientDiscrete 0 (k : ℝ) t := by
  -- `simp only` rather than `unfold`: two declarations bear the name
  -- `hetDecayFactor` -- this module's `(Ne θ : ℝ)` one and the method on
  -- `Core.PopGenParameters` -- and `unfold` fails outright when the name it is
  -- handed is not the one the term carries, where `simp only` just does not fire.
  simp only [founderHeterozygosityLoss, fstMutationDriftTransientDiscrete,
    fstMutationDriftEquilibrium, Descent.Core.fstFromFlow,
    Descent.PopGen.hetDecayFactor, hetDecayFromScaled]
  simp

end FounderEffects


/-!
## Heterozygosity Loss Under Variable Population Size

When Ne changes over time, the drift-accumulated loss of within-population
heterozygosity is
  L(T) = 1 - exp(-Σ_{t=0}^{T-1} 1/(2·Ne(t)))
replacing the constant-size form L = 1 - exp(-T/(2·Ne)).

**This is heterozygosity loss, not between-population `F_ST`.** See the note on
`founderHeterozygosityLoss` above for the measurement that separates them, and use
`PopulationGeneticsFoundations.coalFst` if differentiation after a split is wanted.
Note that the constant-size form `1 - exp(-T/(2·Ne))` named above is the same
falsified expression, so neither the constant-size nor the variable-`Nₑ` form is an
`F_ST`.
-/

section VariableNeFst

/-- **Cumulative drift** under variable Ne: Σ 1/(2·Ne(t)).

    This is the accumulated drift EXPONENT, not the heterozygosity loss itself:
    the loss is `1 - exp(-cumulativeDrift)`, as the note above states. Read as
    the loss directly it is wrong by 22 sems in deep drift, and the first
    measurement of it made exactly that misreading before the note was
    consulted; the sum and the loss agree only to first order.

    Empirical status: **VALIDATED** in the stated form
    (`validation/empirical/simcov/battery_verify.py`,
    `test_cumulative_drift_stated`). Wright-Fisher forward simulation, 2000
    replicates of 2000 loci, realised loss taken as `1 - H_T/H_0`:

      schedule              1 - exp(-Σ)   simulated             sems
      Ne=500, 20 gens          0.01980    0.01983±0.00030      0.10
      Ne=200, 50 gens          0.11750    0.11769±0.00177      0.10
      Ne=50, 60 gens           0.45119    0.45291±0.00679      0.25
      1000/30/1000 bottleneck  0.16194    0.16316±0.00245      0.50

    The same runs give the exact Wright-Fisher product `1 - Π(1 - 1/(2 Ne_i))`
    at 0.01 to 0.06 sems, so the exponential form carries a real second-order
    error -- 0.37 percent at the deepest cell, low every time -- that this
    design detects in sign but not yet at significance. Read as the loss
    directly, the bare sum errs +0.57, +4.1, +21.7 and +5.5 sems on those four
    rows, which is what fixes the exponent reading as the intended one.

    Power: the prediction spans 0.01980 to 0.45119 across the schedules, a
    factor of twenty-three. 
    **A retraction** (`validation/empirical/simcov/battery_bulk17.py`).
    That battery reported this body FALSIFIED at 78 sems against the realised
    `F = 1 - H/H_ancestral`, and proposed replacing it with `1 - prod (1 - 1/(2 Ne_i))`. The report
    is withdrawn. It tested the bare sum
    AS the heterozygosity loss, which is a reading this docstring already
    disowns: the sum is consumed as an EXPONENT, by
    `heterozygosityLossVariableNe = 1 - exp(-cumulativeDrift)`, and the table
    above already records that the bare sum read as the loss errs by up to 21.7
    sems. Re-deriving a known and documented failure of a disowned reading is
    not a new finding.

    What the new run does add is confirmation on deeper schedules than the
    original: over four schedules reaching `F = 0.55`, including twelve
    consecutive epochs at `Ne = 20`, the exact product `1 - prod (1 - 1/(2 Ne_i))`
    tracks the simulation to 1.77 sems and 3.8% relative. That strengthens the
    note above -- the product is the exact law and the exponential is a very good
    approximation to it -- without changing what this definition says.
-/
noncomputable def cumulativeDrift {T : ℕ} (Ne : Fin T → ℝ) : ℝ :=
  ∑ i, 1 / (2 * Ne i)

/-- **cumulativeDrift at every epoch at zero effective size, named.** Each term divides by `2 *
Ne i`, so an epoch of zero effective size contributes junk-zero rather than diverging. A history
of nothing but total bottlenecks accumulates NO drift at all -- and because the terms are summed,
one such epoch is silently dropped from an otherwise sound history rather than making the total
infinite. Consumers must exclude it by hypothesis. -/
theorem cumulativeDrift_zero_sizes_is_junk {T : ℕ} :
    cumulativeDrift (fun _ : Fin T ↦ (0 : ℝ)) = 0 := by
  unfold cumulativeDrift
  simp

/-- **Within-population heterozygosity loss under variable Nₑ**:
    `1 - exp(-Σ 1/(2·Nₑ(t)))`.

    The continuous-time form of `founderHeterozygosityLoss`; see that docstring for
    the measurement showing this family is **not** between-population `F_ST` (`≈ 0`
    here against a measured `0.50` at `Nₑ = 1000`, `t = 4000`) and for
    `coalFst t Ne = t / (t + 2 Nₑ)`, which is the between-population quantity.

    `validation/popgen_defs/battery2.py` checks this body against
    `truth = 1 - H_t/H_0`, drift-only heterozygosity loss, which is what it computes.

    Empirical status: MIXED -- correct for what it now says; FALSIFIED as an `F_ST`. -/
noncomputable def heterozygosityLossVariableNe {T : ℕ} (Ne : Fin T → ℝ) : ℝ :=
  1 - Real.exp (-(cumulativeDrift Ne))

/-- Reference evaluation: with no cumulative drift no heterozygosity is lost. -/
theorem heterozygosityLossVariableNe_of_no_cumulative_drift {T : ℕ} (Ne : Fin T → ℝ)
    (hzero : cumulativeDrift Ne = 0) :
    heterozygosityLossVariableNe Ne = 0 := by
  unfold heterozygosityLossVariableNe
  rw [hzero]
  simp


/-- Heterozygosity loss under variable Nₑ is nonneg when all Nₑ are positive. -/
theorem heterozygosityLossVariableNe_nonneg {T : ℕ}
    (Ne : Fin T → ℝ) (hNe : ∀ i, 0 < Ne i) :
    0 ≤ heterozygosityLossVariableNe Ne := by
  unfold heterozygosityLossVariableNe
  rw [sub_nonneg, ← Real.exp_zero]
  apply Real.exp_le_exp.mpr
  have hcum_nonneg : 0 ≤ cumulativeDrift Ne := by
    unfold cumulativeDrift
    apply Finset.sum_nonneg
    intro i _
    exact le_of_lt (div_pos one_pos (by linarith [hNe i]))
  simpa using hcum_nonneg

/-- Heterozygosity loss under variable Nₑ is strictly less than 1. -/
theorem heterozygosityLossVariableNe_lt_one {T : ℕ} (Ne : Fin T → ℝ) :
    heterozygosityLossVariableNe Ne < 1 := by
  unfold heterozygosityLossVariableNe
  linarith [Real.exp_pos (-(cumulativeDrift Ne))]

/-- Larger cumulative drift yields higher heterozygosity loss. -/
theorem more_drift_higher_heterozygosity_loss {T : ℕ}
    (Ne₁ Ne₂ : Fin T → ℝ)
    (h_more_drift : cumulativeDrift Ne₁ < cumulativeDrift Ne₂) :
    heterozygosityLossVariableNe Ne₁ < heterozygosityLossVariableNe Ne₂ := by
  unfold heterozygosityLossVariableNe
  -- Need: 1 - exp(-d₁) < 1 - exp(-d₂) ↔ exp(-d₂) < exp(-d₁) ↔ -d₂ < -d₁ ↔ d₁ < d₂ ✓
  have h_exp : Real.exp (-(cumulativeDrift Ne₂)) < Real.exp (-(cumulativeDrift Ne₁)) := by
    apply Real.exp_lt_exp.mpr
    linarith
  linarith

/-- Population with uniformly smaller Ne accumulates more drift. -/
theorem smaller_ne_more_drift {T : ℕ} (hT : 0 < T)
    (Ne₁ Ne₂ : Fin T → ℝ)
    (hNe₂ : ∀ i, 0 < Ne₂ i)
    (h_smaller : ∀ i, Ne₂ i < Ne₁ i) :
    cumulativeDrift Ne₁ < cumulativeDrift Ne₂ := by
  unfold cumulativeDrift
  apply Finset.sum_lt_sum
  · intro i _
    have h_pos : 0 < Ne₂ i := hNe₂ i
    have h_lt : Ne₂ i < Ne₁ i := h_smaller i
    exact le_of_lt (div_lt_div_of_pos_left one_pos (by linarith) (by linarith))
  · let j : Fin T := ⟨0, hT⟩
    exact ⟨j, Finset.mem_univ j,
      div_lt_div_of_pos_left one_pos (by linarith [hNe₂ j]) (by linarith [h_smaller j])⟩

/-- **`1/(2x)` is decreasing in `x` on the positives.**

    The per-generation term of `cumulativeDrift` above, isolated. Read as
    genetics it says a bottleneck generation contributes more drift than a
    normal-sized one, but that reading needs the per-generation drift to BE
    `1/(2Nₑ)`, which is the definition's business and not this statement's:
    here there are two positive reals and no population. -/
theorem one_div_two_mul_lt_one_div_two_mul_of_lt (x y : ℝ)
    (hx : 0 < x)
    (hxy : x < y) :
    1 / (2 * y) < 1 / (2 * x) :=
  div_lt_div_of_pos_left one_pos (by linarith) (by linarith)

end VariableNeFst


/-!
## Portability Implications of Demographic History

Populations with different demographic histories have different LD structures
even at the same Fst. This leads to different PGS portability properties:
a bottlenecked population has more long-range LD (from drift during the
bottleneck) compared to a stably-sized population at the same Fst.
-/

section BottleneckExcessLD_Derivation

/-!
## Excess LD from a bottleneck

**Do not derive a bottleneck LD excess from additive drift accounting.** That route --
LD created at rate `1/(2 Ne)` per generation, excess creation rate
`1/(2 Ne_b) - 1/(2 Ne_stable)`, cumulative excess the geometric sum under drift-only
decay -- is internally consistent and gives the wrong function. It carries no
recombination rate, so the level rises without bound toward `1` instead of saturating
at the drift-recombination equilibrium. Simulation puts the same defect at up to
3.3-fold high, and no constant repairs a missing argument.

Any closed form of the shape
`(1 - (1-1/(2 Ne_b))^t_b) - (1 - (1-1/(2 Ne_stable))^t_b)` has that error in its first
term. Use `excessLDAfterBottleneck`, which runs the two-locus recurrence and therefore
carries `c`.

Deleted with it: `excessDriftRate`, `cumulativeExcessLD`, `geom_sum_drift`,
`cumulativeExcessLD_eq_closedForm`, and `derivation_matches_bottleneckExcessLD`.
The last of these deserves its own note. It was stated as

    (1 - a) - (1 - b) = b - a

proved `by ring`, under a docstring claiming it confirmed that the drift
derivation produces the `bottleneckExcessLD` formula. It mentions neither
`cumulativeExcessLD` nor `excessDriftRate`; it is a tautology about two real
numbers and connects nothing. A theorem named "derivation matches" that relates
no two things is worse than no theorem, because its name is read as evidence.

`driftLDCreationRate` is retained below because `Conventions.lean` relates it to
the coalescent time scale, and because it is a correct statement about drift in
isolation. It is not a model of LD.

The replacement lives in `LDDecayTheory.lean`: `driftLDStep` (the Sved
drift-recombination recurrence, which does take `c`), `driftLDEquilibrium` with
`driftLDEquilibrium_isFixedPoint`, and `driftLDTrajectory` with
`driftLDTrajectory_closedForm`. `bottleneckExcessLD` below is now defined as a
trajectory of that process and its closed form is proved, not asserted.
-/

/-- **Drift LD creation rate**: In a population of effective size Ne,
    genetic drift creates new LD at rate 1/(2·Ne) per generation.
    This arises from Cov(Δpᵢ, Δpⱼ) for linked loci under drift.

    This is a creation rate only. Accumulating it without a recombination rate
    is what produced the falsified `bottleneckExcessLD` formula deleted above;
    the honest accumulation is `driftLDStep` in `LDDecayTheory.lean`, in which
    this rate appears multiplied by the non-recombinant fraction `(1-c)²`.

    **Identical twin of `LDDecayTheory.driftRatePerGen`**, which was named
    `ldDecayRatePerGen` until its LD reading was FALSIFIED at up to 201x
    (`validation/empirical/coalescent_diff/`): `1/(2Ne)` is not the fraction of LD lost per
    generation, because recombination dominates it. The same caution applies to any LD
    reading of this body -- the `LD` in this name is about where the rate is *used*, not
    about what it measures. As a bare drift rate it stands.

    Empirical status: **VALIDATED as a drift rate**
    (`validation/empirical/popgensel/`, cell A); the LD reading of the shared formula
    remains FALSIFIED at the twin.

    A per-generation drift rate is the per-generation probability that two gene copies
    coalesce, whose reciprocal is the mean pairwise coalescence time. Measured under
    msprime's `DiscreteTimeWrightFisher` model -- a different engine and a different code
    path from the recursion this body was derived from -- with 40000 replicates per cell:

    | `Nₑ` | mean pairwise `T` | rate `1/T` | this body `1/(2Nₑ)` | sems |
    |---|---|---|---|---|
    | 10 | 20.024 ± 0.098 | 0.049940 ± 0.000243 | 0.05000 | 0.25 |
    | 25 | 49.864 ± 0.244 | 0.020054 ± 0.000098 | 0.02000 | -0.55 |
    | 60 | 119.118 ± 0.591 | 0.008395 ± 0.000042 | 0.008333 | -1.48 |

    The competitors carried on the same cells are rejected: `1/(4Nₑ)` at 102 sems and
    `1/Nₑ` at 199 to 206 sems, so the measurement fixes the factor of two rather than
    tolerating any `1/(kNₑ)`. The `PLANTED` control `1.4/(2Nₑ)` is rejected at 79 to 82
    sems. Ne was scaled down so the whole cell runs in seconds.

    Denotes: a per-generation rate. Other definitions share this formula under names from a
    different concept family; the formula does not fix which is meant. -/
noncomputable def driftLDCreationRate (Ne : ℝ) : ℝ :=
  driftRatePerGen Ne

/-- **driftLDCreationRate at zero Ne, named.** An empty population creates linkage disequilibrium
instantly and the rate diverges. Lean returns `0`, reporting a population in which drift generates
no disequilibrium at all. Consumers must require `Ne ≠ 0`. -/
theorem driftLDCreationRate_zero_ne_is_junk :
    driftLDCreationRate 0 = 0 := by
  unfold driftLDCreationRate driftRatePerGen alleleFreqDivergenceRate
  simp

/-- **Cross-check: this is the same per-generation drift rate that
`LDDecayTheory` calls `driftRatePerGen`.** One rate under two names.

The "fraction of LD lost per generation" reading is FALSIFIED — recombination dominates
`1/(2Ne)`, by up to 201x — so this equality ties two names for a drift rate, not two
readings of an LD rate. It is worth keeping precisely because the two
names sit in different concept families and identical magnitudes are where a divergence
goes unnoticed. -/
theorem driftLDCreationRate_eq_driftRatePerGen (Ne : ℝ) :
    driftLDCreationRate Ne = driftRatePerGen Ne := by
  unfold driftLDCreationRate driftRatePerGen; ring

end BottleneckExcessLD_Derivation


section DemographicPortability

/-- **LD mismatch from demographic differences.**
    Two populations can reach the same Fst via different paths:
    one through a bottleneck (high LD) and one through stable drift (lower LD).
    The bottlenecked population has additional drift-generated LD of order
    1/(2·N_b) per bottleneck generation.

    We model: pop A has stable Ne_A, pop B had a bottleneck to Ne_b < Ne_A
    for t_b generations then recovered to Ne_A. Even if their Fst values
    match, pop B has excess LD.

    **Derived from the drift-recombination process** in `LDDecayTheory.lean`:
    a population sitting at the equilibrium LD level for its stable size
    `Ne_stable` is bottlenecked to `Ne_b` for `t_b` generations, and this is how
    far above the stable level it ends up.

    The previous body was
    `(1 - (1-1/(2 Ne_b))^t_b) - (1 - (1-1/(2 Ne_stable))^t_b)`, whose first term
    is `bottleneckLDAmplification` verbatim -- the formula deleted from
    `LDDecayTheory.lean` for taking no recombination rate and therefore rising
    to `1` with time rather than saturating at the drift-recombination
    equilibrium (simulation: up to 3.3-fold overstatement). The same objection
    applied here unchanged, so this is now a trajectory of a process that does
    take `c`, and `bottleneckExcessLD_eq_closedForm` proves the closed form
    rather than asserting it.

    Empirical status: **VALIDATED** (`validation/empirical/popgensel/`,
    cell B), and the predecessor it replaced is rejected by the same cells.

    Simulated with a labelled-ancestry individual-based two-locus Wright-Fisher:
    each gamete carries one id for its INTACT two-locus haplotype and a
    recombinant offspring gets a fresh id, because its two loci no longer descend
    together. `Q` is then the probability that two distinct gametes share an id.
    (Without the fresh id on recombination the ids fix, `Q` goes to `1` and the
    excess reads a flat `0.000` -- that is the identity-by-descent-with-no-reset
    trap, and it is what the first run of this cell reported.) 800 replicates per
    cell, burn-in at `Nₑ_stable`, then `t_b` generations at `Nₑ_b`:

    | `Nₑ_s` | `Nₑ_b` | `c` | `t_b` | measured excess | this def | sems |
    |---|---|---|---|---|---|---|
    | 50 | 10 | 0.02 | 8 | 0.18712 ± 0.00605 | 0.18342 | -0.61 |
    | 50 | 5 | 0.05 | 5 | 0.24194 ± 0.00606 | 0.25598 | 2.32 |
    | 80 | 20 | 0.01 | 12 | 0.13245 ± 0.00556 | 0.13297 | 0.09 |

    The deleted predecessor `(1-(1-1/(2Nₑ_b))^t_b) - (1-(1-1/(2Nₑ_s))^t_b)` is
    rejected at 10.3, 19.6 and 10.3 sems on the same rows, and a variant keeping
    the trajectory but dropping the `(1-c)²` recombination factor at 12.2, 21.9
    and 13.8 sems. The `PLANTED` control at `1.4x` this body is rejected at 9.7
    to 19.2 sems.

    The positive control is the pre-bottleneck level against
    `driftLDEquilibrium`, which the simulation reaches independently: measured
    `0.19926 ± 0.00312`, `0.08451 ± 0.00115`, `0.23359 ± 0.00372` against
    `0.19519`, `0.08472`, `0.23537`, worst 1.30 sems.

    Argument source: the simulation is an individual-based realisation of the
    same Wright-Fisher model the recursion describes, so what it establishes is
    that the closed form is the right function OF THAT MODEL -- the
    discrimination that carries information is the rejection of the predecessor
    and of the no-recombination variant, which are different functions of it. It
    is not independent evidence that a real bottlenecked population has this much
    excess. -/
noncomputable def bottleneckExcessLD (Ne_b Ne_stable c : ℝ) (t_b : ℕ) : ℝ :=
  driftLDTrajectory Ne_b c (driftLDEquilibrium Ne_stable c) t_b -
    driftLDEquilibrium Ne_stable c

/-- **Closed form of the bottleneck excess**, proved from the recurrence: the
    gap between the two equilibria, approached geometrically over the
    bottleneck. This is the theorem the deleted `derivation_matches_bottleneckExcessLD`
    was named for and did not state. -/
theorem bottleneckExcessLD_eq_closedForm (Ne_b Ne_stable c : ℝ) (t_b : ℕ)
    (hNb : 1 ≤ Ne_b) (hc : 0 ≤ c) (hc1 : c ≤ 1) :
    bottleneckExcessLD Ne_b Ne_stable c t_b =
      (driftLDEquilibrium Ne_b c - driftLDEquilibrium Ne_stable c) *
        (1 - driftLDRetention Ne_b c ^ t_b) := by
  unfold bottleneckExcessLD
  rw [driftLDTrajectory_closedForm Ne_b c _ hNb hc hc1 t_b]
  ring

/-- **One quantity, one definition**: the bottleneck excess is the zero-recovery
    case of `excessLDAfterBottleneck` in `LDDecayTheory.lean`. Stated so the two
    copies of this construction cannot drift apart the way the two copies of the
    deleted formula did. -/
theorem bottleneckExcessLD_eq_excessLDAfterBottleneck
    (Ne_b Ne_stable c : ℝ) (t_b : ℕ) :
    bottleneckExcessLD Ne_b Ne_stable c t_b =
      excessLDAfterBottleneck Ne_b Ne_stable c t_b 0 := by
  unfold bottleneckExcessLD excessLDAfterBottleneck
  rw [driftLDTrajectory_zero]

/-- The bottlenecked population has strictly more LD than the stable population
    over the same number of generations when bottleneck Ne is smaller.

    The recombination rate must be strictly between 0 and 1: at `c = 0` both
    populations equilibrate at `1` and the excess is zero, and at `c = 1` both
    equilibrate at `0`. The old statement, which had no `c`, reported a strictly
    positive excess in both of those regimes. -/
theorem bottleneck_excess_ld_pos (Ne_b Ne_stable c : ℝ) (t_b : ℕ)
    (hNb : 1 ≤ Ne_b) (h_bottle : Ne_b < Ne_stable)
    (hc : 0 < c) (hc1 : c < 1)
    (ht : 0 < t_b) :
    0 < bottleneckExcessLD Ne_b Ne_stable c t_b := by
  rw [bottleneckExcessLD_eq_closedForm Ne_b Ne_stable c t_b hNb (le_of_lt hc) (le_of_lt hc1)]
  exact bottleneckExcessFactor_pos Ne_b Ne_stable c t_b hNb h_bottle hc hc1 ht

/-- **A bottleneck adds mismatch on top of whatever `F_ST` already contributes.**

    The content is `bottleneck_excess_ld_pos` above, which is where the demography is: it proves
    the excess linkage disequilibrium a bottleneck leaves is strictly positive. This composes it
    with the fact that adding a positive quantity increases a total, so two source-target pairs
    at the same `F_ST` are not interchangeable when one target was bottlenecked.

    The hypothesis `0 ≤ fst_mismatch` was doing no work — a positive addend raises any total —
    and is removed, so what is left in the signature is exactly what
    `bottleneck_excess_ld_pos` needs. -/
theorem bottleneck_worsens_portability
    (Ne_b Ne_stable c : ℝ) (t_b : ℕ)
    (hNb : 1 ≤ Ne_b) (h_bottle : Ne_b < Ne_stable)
    (hc : 0 < c) (hc1 : c < 1)
    (ht : 0 < t_b) (fst_mismatch : ℝ) :
    fst_mismatch < fst_mismatch + bottleneckExcessLD Ne_b Ne_stable c t_b := by
  linarith [bottleneck_excess_ld_pos Ne_b Ne_stable c t_b hNb h_bottle hc hc1 ht]

/-- **Portability ratio under bottleneck** is strictly worse than under stable demography.
    Derived: portability ∝ (1 - Fst) for stable populations. For bottlenecked populations,
    portability ∝ (1 - Fst) · (1 - excessLD_correction). Since bottleneckExcessLD > 0,
    the correction factor is < 1, reducing the portability ratio.
    We model: R²_bottleneck = R²_source · ((1-Fst) - excessLD) where
    excessLD = bottleneckExcessLD Ne_b Ne_stable c t_b. -/
theorem bottleneck_reduces_portability_ratio
    (R2_source Ne_b Ne_stable c : ℝ) (t_b : ℕ) (fst : ℝ)
    (hR2 : 0 < R2_source)
    (hNb : 1 ≤ Ne_b) (h_bottle : Ne_b < Ne_stable)
    (hc : 0 < c) (hc1 : c < 1)
    (ht : 0 < t_b) :
    R2_source * ((1 - fst) - bottleneckExcessLD Ne_b Ne_stable c t_b) <
    R2_source * (1 - fst) := by
  apply mul_lt_mul_of_pos_left _ hR2
  linarith [bottleneck_excess_ld_pos Ne_b Ne_stable c t_b hNb h_bottle hc hc1 ht]

/-- Populations that experienced expansion retain more pre-existing LD,
    meaning their LD structure is closer to the source population's LD
    (since both have large modern Ne). We show that if the expanded population
    has LD retention factor closer to the source, the LD distance is smaller.

    Formally: if |ρ_exp - ρ_src| < |ρ_small - ρ_src| where ρ is the LD
    retention, then the PGS accuracy loss (proportional to LD mismatch²)
    is smaller for the expanded population. -/
theorem mul_sq_lt_mul_sq_of_lt_of_nonneg
    (ld_mismatch_exp ld_mismatch_small accuracy_coeff : ℝ)
    (h_coeff_pos : 0 < accuracy_coeff)
    (h_mismatch_exp_nn : 0 ≤ ld_mismatch_exp)
    (h_exp_less : ld_mismatch_exp < ld_mismatch_small) :
    accuracy_coeff * ld_mismatch_exp ^ 2 < accuracy_coeff * ld_mismatch_small ^ 2 := by
  apply mul_lt_mul_of_pos_left _ h_coeff_pos
  exact sq_lt_sq' (by linarith) h_exp_less

end DemographicPortability

theorem driftLDCreationRate_eq_inv_timeScale (Ne : ℝ) :
    PopGen.driftLDCreationRate Ne = 1 / Descent.Core.coalescentTimeScale Ne := by
  unfold PopGen.driftLDCreationRate PopGen.driftRatePerGen PopGen.alleleFreqDivergenceRate
  rw [Descent.Core.coalescentTimeScale_eq]

/-- Wright's compounding identity: one minus the product of retentions. It is
written once for the two branches of a split and once for the two levels of
the `F`-statistic hierarchy. -/
theorem pairwiseFstFromBranches_eq_wrightFIT (a b : ℝ) :
    Portability.pairwiseFstFromBranches a b = PopGen.wrightFIT a b := by
  unfold Portability.pairwiseFstFromBranches PopGen.wrightFIT Descent.Core.complementaryComposition; ring_nf

theorem cumulativeDrift_uses_timeScale {T : ℕ} (Ne : Fin T → ℝ) :
    PopGen.cumulativeDrift Ne = ∑ i, 1 / Descent.Core.coalescentTimeScale (Ne i) := by
  unfold PopGen.cumulativeDrift
  simp only [Descent.Core.coalescentTimeScale_eq]

theorem demoSteppingStoneFst_eq_scaled (d Ne m σ_sq : ℝ) :
    PopGen.demoSteppingStoneFst d Ne m σ_sq
      = d / (d + Descent.Core.scaledMigrationRate Ne m * σ_sq) := by
  unfold PopGen.demoSteppingStoneFst
  rw [Descent.Core.scaledMigrationRate_eq_ploidy_form]; unfold Descent.Core.ploidy; ring_nf

theorem fstMutationDriftTransient_uses_timeScale (θ t Ne : ℝ) :
    PopGen.fstMutationDriftTransient θ t Ne
      = PopGen.fstMutationDriftEquilibrium θ *
          (1 - Real.exp (-(1 + θ) * t / Descent.Core.coalescentTimeScale Ne)) := by
  unfold PopGen.fstMutationDriftTransient; rw [Descent.Core.coalescentTimeScale_eq]

/-- **Slatkin's identity**: `1 - H_w/H_b = 1 - E[T_w]/E[T_b]`.

The heterozygosity reading of `F_ST` and the coalescence-time reading are the same number
whenever the two RATIOS agree -- which is the content, and it is a premise here rather than
a theorem. Under the infinite-sites limit expected heterozygosity is proportional to
expected coalescence time, so the constant cancels in the ratio; away from that limit it
does not, and this statement correctly says nothing.

What the corpus gets from it is a lattice edge. `fstFromHetRatio` and
`hudsonFstFromCoalescenceTimes` are both `Core.proportionalReduction`, so at EQUAL
arguments they agree by `rfl` and that is what
`pcTargetAxisEfficacy_eq_proportionalReduction` above records. This says the harder thing:
at DIFFERENT arguments -- heterozygosities on one side, coalescence times on the other --
they still agree, provided the population genetics that relates those arguments holds. Both
are Hudson-convention readings, so the edge is inside one convention and needs no bridge.

    Empirical status: NOT AN EMPIRICAL CLAIM -- the algebra is `rw [h]`. The premise
    `H_w/H_b = E[T_w]/E[T_b]` is where all the biology is, and it is supplied by the
    caller, not established here. -/
theorem slatkin_hetRatio_eq_coalescenceRatio
    (Hw Hb ETw ETb : ℝ) (h : Hw / Hb = ETw / ETb) :
    PopGen.fstFromHetRatio Hw Hb = Portability.hudsonFstFromCoalescenceTimes ETw ETb := by
  unfold PopGen.fstFromHetRatio Portability.hudsonFstFromCoalescenceTimes
    Descent.Core.proportionalReduction
  rw [h]

/-- **The four in the quadratic stepping-stone form is twice the ploidy**, the same
`4 Nₑ` scaling as every other migration-drift denominator in the corpus. Only the powers of
`m` and `σ²` distinguish this form from `demoSteppingStoneFst`; the constant does not. -/
theorem steppingStoneFstQuadratic_uses_ploidy (d Ne m σ_sq : ℝ) :
    PopGen.steppingStoneFstQuadratic d Ne m σ_sq
      = d / (d + 2 * Descent.Core.ploidy * Ne * σ_sq ^ 2 * m ^ 2) := by
  unfold PopGen.steppingStoneFstQuadratic Descent.Core.ploidy; ring

/-- **The finite-deme island `F_ST` is the identity fraction at the deme-corrected scaled
migration rate.** Its `4 Nₑ m` is `scaledMigrationRate`, which
`scaledMigrationRate_eq_ploidy_form` already forces to `2 · ploidy · Nₑ · m`; the deme
correction multiplies that rate and does not touch the constant. This is the second
consumer of the one bridge, so the finite-`d` form and its `d → ∞` limit cannot acquire
different conventions. -/
theorem islandFstFiniteDemes_eq_scaled (Ne m d : ℝ) :
    PopGen.islandFstFiniteDemes Ne m d
      = PopGen.fstMutationDriftEquilibrium (Descent.Core.scaledMigrationRate Ne m * Descent.Core.islandDemeCorrection d) := by
  unfold PopGen.islandFstFiniteDemes PopGen.fstMutationDriftEquilibrium Descent.Core.scaledMigrationRate Descent.Core.fstFromFlow
    Descent.Core.islandDemeCorrection Descent.Core.ratio Descent.Core.ploidy
  ring

end Descent.PopGen
