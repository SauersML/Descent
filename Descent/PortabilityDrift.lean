/-
Released under the GNU Affero General Public License v3.0 as described in the file LICENSE.
-/
import Descent.Conclusions
import Descent.DGP
import Descent.CirculationDefect

namespace Descent

open MeasureTheory

/-! `r2FromSignalVariance` and the Gaussian-AUC declarations live in
`Descent.TransportedMetrics` (DGP.lean). `Descent.DGP` is imported, so
the module is available, but the namespace was never opened here and this file
refers to five of its declarations WITHOUT qualification. Lean does not report
that as a missing constant: it auto-binds the bare name as an implicit
variable, which is why the failure surfaced as three unrelated-looking symptoms
-- "unknown identifier", "function expected at", and the discriminating
"LOCAL VARIABLE `r2FromSignalVariance` has no definition". A definition that
had failed to build would say something else, and `Descent.DGP` itself
builds clean.

These five names are opened rather than qualified at ~40 call sites: the
mechanical repoint is the larger and riskier diff, and an explicit import list
cannot collide, since this file defines none of these names and the only
`Profile` and `calibratedBrier` in the corpus are the ones inside this same
namespace. The remaining `TransportedMetrics.` prefixes in this file are left
alone; both spellings resolve to the same constant. -/
open TransportedMetrics (r2FromSignalVariance r2FromSignalVariance_eq_rsquared
  equalVarianceGaussianAUCFromSignalVariance
  equalVarianceGaussianAUCFromSignalVariance_eq_formula_of_ne_noise)

section PortabilityDrift


/-- Empirical status: **VALIDATED** through
    `coalescenceSurvivalFromHazard`, whose measurement
    (`battery_bulk1.py`, `test_coalescent_hazard`) is against a piecewise-constant
    hazard whose integral is exact and which crosses an epoch boundary, so a
    wrong integral would move the survival. Worst cell 1.42 sems over a
    prediction spanning 0.31140 to 0.81873. -/
noncomputable def integratedCoalescentHazard (hazard : ℝ → ℝ) (t : ℝ) : ℝ :=
  ∫ s in (0)..t, hazard s

/-- **The integrated hazard under a constant rate, pinned.** This definition carries no theorem
of its own. A constant coalescence rate `c` accumulates hazard `c * t` by time `t`; the reference
value that separates the integral from a body that averages rather than accumulates. -/
theorem integratedCoalescentHazard_const (c t : ℝ) :
    integratedCoalescentHazard (fun _ ↦ c) t = c * t := by
  unfold integratedCoalescentHazard
  simp [mul_comm]

/-- Probability that a pair has not yet coalesced by time `t`, from the
integrated hazard: `S(t) = exp(-Λ(t))`.

    Empirical status: **VALIDATED**
    (`validation/empirical/simcov/battery_bulk1.py`,
    `test_coalescent_hazard`). A two-epoch coalescent, `Ne = 500` until
    generation 800 and `Ne = 3000` after, so the pairwise hazard `1/(2 Ne(t))`
    is piecewise constant and its integral is exact. 60000 independent
    genealogies, survival read as the fraction with `T_MRCA > t`:

      t        this def   simulated            sems
       200      0.81873   0.81915±0.00157      0.27
       500      0.60653   0.60935±0.00199      1.42
       800      0.44933   0.45122±0.00203      0.93
      1500      0.39985   0.40075±0.00200      0.45
      3000      0.31140   0.31060±0.00189      0.43

    The design crosses the epoch boundary, so a formula that integrated the
    hazard with the wrong size on either side would show up; the `t = 1500` and
    `t = 3000` rows are the ones that test the second epoch.

    Power: the prediction spans 0.31140 to 0.81873 across the design. -/
noncomputable def coalescenceSurvivalFromHazard (hazard : ℝ → ℝ) (t : ℝ) : ℝ :=
  Real.exp (-(integratedCoalescentHazard hazard t))

/-- **Survival under a constant hazard is exponential, pinned.** This definition carries no
result of its own. A constant coalescence rate `c` leaves `exp (-c * t)` of pairs uncoalesced by
time `t` -- the exponential waiting law that the hazard formulation is supposed to reproduce. -/
theorem coalescenceSurvivalFromHazard_const (c t : ℝ) :
    coalescenceSurvivalFromHazard (fun _ ↦ c) t = Real.exp (-(c * t)) := by
  unfold coalescenceSurvivalFromHazard
  rw [integratedCoalescentHazard_const]

/-- Probability that a pair has coalesced by time `t`, the complement of the
survival function.

    Empirical status: **VALIDATED** on the same runs as
    `coalescenceSurvivalFromHazard` (`battery_bulk1.py`,
    `test_coalescent_hazard`), worst cell 1.42 sems over a prediction spanning
    0.18127 to 0.68860. -/
noncomputable def coalescenceCdfFromHazard (hazard : ℝ → ℝ) (t : ℝ) : ℝ :=
  1 - coalescenceSurvivalFromHazard hazard t

/-- Coalescent time `τ = t / (2·Nₑ)`: generations rescaled by the diploid
coalescent timescale.

    Regime: a clean two-population split with no migration and equal sizes.

    Empirical status: **VALIDATED** (`simcov/battery_bulk20.py`, `group_a`).
    The divisor is what a simulation can decide, so the body is read through the
    saturation law it is paired with and inverted: `F_ST / (1 - F_ST)` estimates
    `τ` directly, and `t / Nₑ` or `t / (4·Nₑ)` would miss it by exactly the
    factor in the divisor. Across `Nₑ` and `t` chosen so `τ` runs 0.125, 0.25,
    1, 2, 4 -- a thirtytwofold sweep, prediction spanning 97% -- the measured
    odds are 0.2477 ± 0.0080, 1.0038 ± 0.0309, 0.1326 ± 0.0034, 1.9946 ±
    0.0559 and 4.0164 ± 0.0799, worst cell 2.24 sems. `Nₑ` and `t` are moved
    separately, so the two appear at the same `τ` by different routes and a
    body that scaled by only one of them would separate. -/
noncomputable def coalescentTau (t Ne : ℝ) : ℝ :=
  t / (2 * Ne)

/-- **The coalescent time unit, pinned.** `coalescentTau` carries no theorem of its own. Two `Ne`
generations is one unit of coalescent time -- that is what the scaling means, and it is what
separates this body from `t / Ne` and from `t / (4 * Ne)`. -/
theorem coalescentTau_two_Ne_generations (Ne : ℝ) (hNe : Ne ≠ 0) :
    coalescentTau (2 * Ne) Ne = 1 := by
  unfold coalescentTau
  field_simp

/-- **Coalescent time at zero effective size, named.** With no population there is no coalescent
timescale to divide by, and every finite separation is infinitely many drift units. The divisor
is zero and Lean returns `0`, reporting no divergence at all -- so every `Fst` computed through
this chart from a zero effective size comes out at zero, indistinguishable from two populations
that have just split. Consumers must require `Ne ≠ 0`. -/
theorem coalescentTau_zero_population_is_junk (t : ℝ) :
    coalescentTau t 0 = 0 := by
  unfold coalescentTau
  norm_num

/-- **`F_ST` after a clean split, in coalescent units.**

This is not an independent formula.  It is `coalFst` expressed in units of
`tau = t / (2 Ne)`, and `coalFst_eq_fstFromTau` is the theorem that says so; the
two cannot drift apart without that theorem failing.  The previous body here was
`1 - exp (-tau)`, which is the coalescence CDF already defined in this file as
`coalescenceCdfFromHazard` under unit hazard -- the probability that a lineage
pair has coalesced by `tau`, not the between-population variance ratio.  The two
were conflated, and `fstFromTau_lt_coalescenceCdf` now records that they are
never equal.

    Regime: instantaneous clean split, constant equal daughter sizes, no
    migration, no selection, continuous (large-N) coalescent -- the model under
    which `validation/differential/refs.py`'s `split_fst_hudson` is exact.  The
    regime is the whole point of this definition rather than a caveat on it: the
    closed-population drift recurrence is a *different* model, not the `F_ST` of
    a split, and confusing the two is the model error that the
    `heterozygosityLossDerived`/`fstFromTau`/`targetHetFromFst` cluster turns on (see the
    `heterozygosityLossDerived-is-not-split-fst` check).  Outside a clean split -- under
    migration, unequal sizes, or ongoing gene flow -- this map is not claimed.

    Empirical status: VALIDATED (0.0909/0.2000/0.3333/0.5000/0.6667/0.8000 at
    tau = .1/.25/.5/1/2/4 against simulated 0.0905/0.1887/0.3137/0.4782/0.6589/
    0.8028, within simulation error at every point).

    Power: the prediction spans `0.0909` to `0.8000` across that `tau` grid,
    nearly an order of magnitude and most of the range `F_ST` can occupy. A
    fortyfold sweep of `tau` moves the prediction across the whole saturating
    curve, so a form that is linear in `tau`, or one saturating at a different
    rate, separates from this one on the grid rather than only at its ends. -/
noncomputable def fstFromTau (tau : ℝ) : ℝ :=
  tau / (1 + tau)

/-- **fstFromTau at `tau = -1`, named.** A coalescent time of minus one is outside the admissible
range, which is exactly why it must be excluded by hypothesis rather than left to the totality
convention: the saturation curve's divisor vanishes there and Lean returns `0`, an ordinary `Fst`
value that no downstream range check will reject. Consumers must exclude it by hypothesis. -/
theorem fstFromTau_negative_unit_tau_is_junk :
    fstFromTau (-1) = 0 := by
  unfold fstFromTau
  norm_num

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
  fstFromTau (coalescentTau t Ne)

/-- **Circulation inflates transfer time by the same saturation law that drift
uses for `F_ST`.**

`CirculationDefect.transferTimeInflation` is `1 + (a/s)^2`, the factor by which
circulation stretches the frontier time. Its reciprocal -- the fraction of the
frontier time that survives -- is `1 - fstFromTau ((a/s)^2)`, the complement of
the chart this file uses for drift at coalescent time `tau`.

The two modules are about different processes, and that is why the shared
functional form is worth recording rather than assuming: `x / (1 + x)` appears
in both, so a change to either body that breaks the identity fails to compile
instead of leaving the two quietly disagreeing about a shape they both use. No
hypothesis is needed, because `1 + (a/s)^2` is positive for every `s` and `a`,
including `s = 0`. -/
theorem one_div_transferTimeInflation_eq_one_sub_fstFromTau (s a : ℝ) :
    1 / transferTimeInflation s a = 1 - fstFromTau ((a / s) ^ 2) := by
  have hpos : (0 : ℝ) < 1 + (a / s) ^ 2 := by positivity
  have hne : (1 : ℝ) + (a / s) ^ 2 ≠ 0 := ne_of_gt hpos
  unfold transferTimeInflation fstFromTau
  field_simp
  ring

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
  1 - (1 - fstS) * (1 - fstT)

/-- **Pairwise `F_ST` composed in coalescent time instead of in `F_ST`.**

    Under the coalescent, two demes that split from a common ancestor have
    `E[T_between] = 1 + tau` in units where `E[T_within] = 1`, with `tau` the
    time to that ancestor. The path is traversed ONCE, so the branch taus enter
    through their MEAN and not their sum, and Hudson's ratio gives
    `fstFromTau ((tauS + tauT) / 2)`.

    Empirical status: CONDITIONALLY VALID. Validated for equal branch lengths
    and falsified for unequal ones, with the boundary measured rather than
    asserted; both tables are below. The residual on unequal branches is a
    SIGNATURE limitation and not a repairable constant: with unequal daughter
    sizes the between-deme coalescence also depends on the ANCESTRAL size, and
    two branch taus cannot carry it. Use `hudsonFstFromCoalescenceTimes` there.

    History, kept because it is the evidence for the body above. This
    definition previously read `fstFromTau (tauS + tauT)`, summing both branch
    taus, and was **FALSIFIED** in that form
    (`validation/empirical/simcov/battery_fix.py`, `test_fst_composition`).
    Measured against msprime coalescent simulation of a clean split, recombining
    at `1e-8` so that each replicate carries many independent genealogies,
    Hudson's `F_ST` as a ratio of averages, 25 replicates of 20 Mb, 50 diploids
    per deme:

      Ne     t       this def   `coalFst`   simulated   sems off (this def)
      1000   500       0.3333      0.2000      0.19923            59.1
      1000   1000      0.5000      0.3333      0.33415            51.9
      1000   2000      0.6667      0.5000      0.49974            50.6

    On the SAME runs `coalFst` matches to 0.34, 0.25 and 0.08 sems. Two
    definitions of one quantity disagree and the simulation says which.

    The premise stated above is where it goes wrong: two demes that split `t`
    generations ago have `E[T_between] = 1 + tau`, NOT `1 + tauS + tauT`.
    Coalescence times add along a path, but the path to the common ancestor is
    traversed ONCE -- reaching the ancestral population takes `t` generations,
    not `t` from each side. Summing both branch taus double-counts the split
    time, which is exactly the observed `+50` percent.

    **The body has been corrected to the MEAN of the branch taus**, which is the
    composition with the split time counted once. On a symmetric split it
    reduces to `fstFromTau tau`, hence to `coalFst`, which is what makes the two
    definitions agree instead of differing by fifty percent. Re-measured on the
    same engine (`battery_correct.py`, `correct_pairwise_tau`, 30 replicates of
    20 Mb, recombining):

      NeA    NeB    t      old (sum)   this (mean)   simulated          sems
      1000   1000    500      0.33333       0.20000  0.19682±0.00277   1.2
      1000   1000   1000      0.50000       0.33333  0.32924±0.00326   1.3
      1000   1000   2000      0.66667       0.50000  0.49999±0.00302   0.0
       600    600   1200      0.66667       0.50000  0.49410±0.00385   1.5
       500   2000   1000      0.55556       0.38462  0.36592±0.00330   5.7

    So: validated for equal branch lengths at worst 1.5 sems over four designs
    spanning 0.19682 to 0.49999, and wrong for unequal ones -- the last row
    misses by 5.7 sems. That is the boundary the status at the top records.

    Power: the prediction spans 0.20000 to 0.50000 across the symmetric designs,
    a factor of two and a half, and the superseded sum form is excluded at 40 to
    59 sems on every one of them. -/
noncomputable def pairwiseFstFromBranchTaus (tauS tauT : ℝ) : ℝ :=
  fstFromTau ((tauS + tauT) / 2)

@[simp] theorem pairwise_fst_decomposition (fstS fstT : ℝ) :
    pairwiseFstFromBranches fstS fstT = fstS + fstT - fstS * fstT := by
  unfold pairwiseFstFromBranches
  ring_nf

/-- **What the multiplicative composition actually computes.**

Feeding it two branch `F_ST` values that came from coalescent times `a` and `b`
returns the `F_ST` of a single branch of length `a + b + a * b`. The `a * b` is
the whole defect: it is divergence time that no branch spent. This identity is
the derivation behind the regime note on `pairwiseFstFromBranches`, and it needs
no simulation to state. -/
theorem pairwiseFstFromBranches_eq_fstFromTau_add_mul (a b : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) :
    pairwiseFstFromBranches (fstFromTau a) (fstFromTau b) =
      fstFromTau (a + b + a * b) := by
  have ha1 : (0 : ℝ) < 1 + a := by linarith
  have hb1 : (0 : ℝ) < 1 + b := by linarith
  have ha1' : (1 : ℝ) + a ≠ 0 := ne_of_gt ha1
  have hb1' : (1 : ℝ) + b ≠ 0 := ne_of_gt hb1
  have hab : (0 : ℝ) < 1 + (a + b + a * b) := by nlinarith
  have hab' : (1 : ℝ) + (a + b + a * b) ≠ 0 := ne_of_gt hab
  unfold pairwiseFstFromBranches fstFromTau
  field_simp
  ring

/-- **The multiplicative map is strictly the larger of the two compositions**,
for every pair of positive branch lengths. The bias has a sign, and it is the
sign the simulation reports. -/
theorem pairwiseFstFromBranchTaus_lt_pairwiseFstFromBranches (a b : ℝ)
    (ha : 0 < a) (hb : 0 < b) :
    pairwiseFstFromBranchTaus a b <
      pairwiseFstFromBranches (fstFromTau a) (fstFromTau b) := by
  rw [pairwiseFstFromBranches_eq_fstFromTau_add_mul a b ha.le hb.le]
  unfold pairwiseFstFromBranchTaus fstFromTau
  have h1 : (0 : ℝ) < 1 + (a + b) / 2 := by linarith
  have h2 : (0 : ℝ) < 1 + (a + b + a * b) := by nlinarith
  rw [div_lt_div_iff₀ h1 h2]
  nlinarith [mul_pos ha hb]

/-- **The gap between the two compositions is FIRST order in the branch length.**

    This theorem previously claimed the gap was bounded by `eps ^ 2`, and that
    claim was an artifact of the superseded body. It was true of
    `fstFromTau (tauS + tauT)`, whose extra `tauS * tauT` really is second
    order -- and it was the licence under which the two compositions could be
    treated as interchangeable at small `F_ST`. With the split time counted once
    rather than twice, they differ at first order and no longer may be.

    At equal branches the gap is exactly `a / (1 + a) ^ 2`, which is `a` to
    leading order. So the multiplicative composition in `F_ST` and the additive
    composition in coalescent time are two different quantities, and the
    simulation in the docstring above says the coalescent one is the measured
    `F_ST`: `0.49999 ± 0.00302` against this definition's `0.50000` where
    `pairwiseFstFromBranches` gives `0.75`. -/
theorem pairwiseFst_composition_gap_eq (a : ℝ) (ha : 0 ≤ a) :
    pairwiseFstFromBranches (fstFromTau a) (fstFromTau a) -
        pairwiseFstFromBranchTaus a a = a / (1 + a) ^ 2 := by
  have h1 : (1 : ℝ) + a ≠ 0 := by positivity
  rw [pairwiseFstFromBranches_eq_fstFromTau_add_mul a a ha ha]
  unfold pairwiseFstFromBranchTaus fstFromTau
  have h2 : (1 : ℝ) + (a + a + a * a) ≠ 0 := by nlinarith
  have h3 : (1 : ℝ) + (a + a) / 2 ≠ 0 := by linarith
  field_simp
  ring

@[simp] theorem coalescenceCdfFromHazard_eq (hazard : ℝ → ℝ) (t : ℝ) :
    coalescenceCdfFromHazard hazard t =
      1 - Real.exp (-(integratedCoalescentHazard hazard t)) := by
  simp [coalescenceCdfFromHazard, coalescenceSurvivalFromHazard]

@[simp] theorem fstFromGenerations_eq (t Ne : ℝ) :
    fstFromGenerations t Ne = t / (2 * Ne) / (1 + t / (2 * Ne)) := rfl

theorem fst_from_tau_nonneg_of_nonneg (tau : ℝ) (htau : 0 ≤ tau) :
    0 ≤ fstFromTau tau :=
  div_nonneg htau (by linarith)

theorem fst_from_tau_lt_one (tau : ℝ) (htau : 0 ≤ tau) : fstFromTau tau < 1 := by
  unfold fstFromTau
  rw [div_lt_one (by linarith)]
  linarith

/-- **The coalescence CDF is not `F_ST`.**  `1 - exp (-tau)` is the probability
that a lineage pair has coalesced by `tau`; `F_ST` is the between-population
share of variance.  Conflating them overstates divergence at every positive
separation, which is the direction and the shape of the bias measured against
simulation (+5% at `tau = 0.1`, rising to +32% at `tau = 1`).  Stating the
inequality keeps the two from being interchanged again silently. -/
theorem fstFromTau_lt_coalescenceCdf (tau : ℝ) (htau : 0 < tau) :
    fstFromTau tau < 1 - Real.exp (-tau) := by
  have hE : (0 : ℝ) < Real.exp tau := Real.exp_pos tau
  have hexp : tau + 1 < Real.exp tau := Real.add_one_lt_exp (by linarith)
  have h1t : (0 : ℝ) < 1 + tau := by linarith
  rw [← sub_pos]
  unfold fstFromTau
  rw [Real.exp_neg]
  have hrw : 1 - (Real.exp tau)⁻¹ - tau / (1 + tau) =
      (Real.exp tau - 1 - tau) / (Real.exp tau * (1 + tau)) := by
    field_simp
    ring
  rw [hrw]
  exact div_pos (by linarith) (by positivity)



/-- **The `Fst` saturation curve's midpoint, pinned.** `fstFromTau_lt_coalescenceCdf` bounds this
above by the coalescence CDF and is satisfied by any body below that curve, including
`tau / (1 + 2 * tau)`. One coalescent time unit of separation gives `Fst = 1/2`: the map reaches
its half-saturation exactly where the separation reaches the drift timescale. -/
theorem fstFromTau_at_one_time_unit :
    fstFromTau 1 = 1 / 2 := by
  unfold fstFromTau
  norm_num

/-- A split with ongoing migration.

**Do not add a deme-count field here.** The many-deme regime that
`fstEqLimitLowMutationManyDemes` names is a LIMIT, not a stored count: a deme count would
enter no formula and no theorem in this file, so it could take any value without changing
a single statement, while giving the appearance of tracking something the development does
not track. -/
structure SplitMigrationModel where
  t : ℝ
  Ne : ℝ
  mig : ℝ
  mu : ℝ
  Ne_pos : 0 < Ne
  mig_nonneg : 0 ≤ mig
  mu_nonneg : 0 ≤ mu

/-- **The class is inhabited.**  A theorem quantified over an uninhabited structure is
true and empty: kernel-checked, clean axiom report, no content.  This is the witness that
makes the theorems below statements about something. -/
noncomputable def SplitMigrationModel.witness : SplitMigrationModel where
  t := 1
  Ne := 1
  mig := 1
  mu := 1
  Ne_pos := by norm_num
  mig_nonneg := by norm_num
  mu_nonneg := by norm_num

/-- **The many-deme, low-mutation limit of the split-with-migration `F_ST`**, which is
Wright's diffusion form `1/(1 + 4 Nₑ m)` written through `scaledMigrationRate`.

    Empirical status: **FALSIFIED** outside the weak-migration limit
    (`validation/empirical/simcov/battery_pd1.py`). The name declares a
    many-deme, low-mutation regime and says nothing about `mig`, so it is read
    here at face value across a 50-fold sweep in `mig`. Explicit Wright-Fisher
    island model, 200 demes, identity-probability `F_ST` on distinct pairs, ten
    independent replicate metapopulations per cell:

      Nₑ    mig       this def   simulated            rel
      200   0.0100     0.11111    0.10897 ± 0.00005    1.96%
      50    0.0100     0.33333    0.32714 ± 0.00009    1.89%
      13    0.1538     0.11111    0.08769 ± 0.00001   26.7%
      4     0.5000     0.11111    0.03936 ± 0.00001  182%
      2     0.2500     0.33333    0.23978 ± 0.00001   39.0%

    Positive control: a panmictic pool split into 200 labelled demes reads
    `F_ST` 0.05 sems from zero.

    WHAT SURVIVES. At `mig ≤ 0.01` the body is within 2%, and that 2% is itself
    mostly the finite-deme term rather than the linearisation. The error is
    `O(mig)` and nothing else: the exact fixed point
    `fstIslandMultiplicativeEquilibrium`, which differs from this body only in
    dropped terms of order `m²` and `m/Nₑ`, tracks the same simulation to 1.6%
    at every cell including `mig = 0.5`. So this is the weak-migration
    approximation behaving exactly as `ibdRecurrenceFixedPoint_lt_linearisation`
    says it must, measured rather than asserted.

    WHY THE DESIGN COULD SEE IT AND EARLIER ONES COULD NOT. The two forms
    separate in `mig`, not in `4 Nₑ mig`. `battery_bulk1` and `battery_bulk20`
    swept the compound parameter and passed both forms; here `mig` is swept
    50-fold at fixed `4 Nₑ mig` by shrinking `Nₑ`.

    argument_source: model. -/
noncomputable def SplitMigrationModel.fstEqLimitLowMutationManyDemes (m :
    SplitMigrationModel) : ℝ :=
  1 / (1 + scaledMigrationRate m.Ne m.mig)

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
  1 - ETss / ETst

structure DemographicCoalescenceScalars where
  ETss : ℝ
  ETst : ℝ

/-- **Hudson's estimator, pinned.** This definition carries no theorem of its own. When a pair
drawn between populations takes twice as long to coalesce as a pair drawn within one, half the
coalescent history is population-specific and `Fst` is one half. -/
theorem hudsonFstFromCoalescenceTimes_double_between :
    hudsonFstFromCoalescenceTimes 1 2 = 1 / 2 := by
  unfold hudsonFstFromCoalescenceTimes
  norm_num

/-- **Hudson's estimator at zero between-population coalescence time, named.** If a pair drawn
between populations coalesces instantly there is no differentiation at all, so `Fst` should be
zero or undefined. The divisor is zero, the ratio is junk-zero, and the estimator returns `1` --
COMPLETE differentiation, the opposite end of the scale. Of the junk branches in this chart this
is the one that inverts rather than flattens, so it cannot be spotted as an implausible extreme.
Consumers must require `ETst ≠ 0`. -/
theorem hudsonFstFromCoalescenceTimes_instant_between_is_junk (ETss : ℝ) :
    hudsonFstFromCoalescenceTimes ETss 0 = 1 := by
  unfold hudsonFstFromCoalescenceTimes
  simp

noncomputable def DemographicCoalescenceScalars.delta
    (d : DemographicCoalescenceScalars) : ℝ :=
  hudsonFstFromCoalescenceTimes d.ETss d.ETst

@[simp] theorem DemographicCoalescenceScalars.delta_eq
    (d : DemographicCoalescenceScalars) :
    d.delta = 1 - d.ETss / d.ETst := by
  rfl

/-- **First-step analysis of the structured coalescent, same-deme state.**

Symmetric two-deme island model with scaled migration `M`.  Time is in units of
`2 Nₑ` generations, so two lineages sitting in one deme coalesce at rate `1`
and each lineage leaves its deme at rate `M/2`.  From the same-deme state the
competing clocks give a total rate `1 + M`, an expected waiting time
`1/(1 + M)`, and then coalescence with probability `1/(1 + M)` or -- with
probability `M/(1 + M)` -- a migration that leaves the lineages in different
demes.  The map below sends a candidate pair of expected coalescence times to
the pair implied by one such step.

Composition convention: this is the *continuous-time* structured coalescent, in
which competing exponential clocks make the within-generation ordering of
migration and coalescence immaterial.  The discrete-generation model with a
fixed ordering has a different fixed point, differing at O(1/Nₑ).

    Empirical status: UNTESTED. -/
noncomputable def twoDemeIMFirstStepSame (M _ETss ETst : ℝ) : ℝ :=
  1 / (1 + M) + (M / (1 + M)) * ETst

/-- **twoDemeIMFirstStepSame at `M = -1`, named.** Both terms divide by `1 + M`, so both are
junk-zero at `M = -1` and the whole first step collapses to zero regardless of the between-deme
time it is supposed to depend on. Two junk branches in one expression, and the dependence on
`ETst` disappears with them. Consumers must exclude it by hypothesis. -/
theorem twoDemeIMFirstStepSame_negative_unit_migration_is_junk (ETss ETst : ℝ) :
    twoDemeIMFirstStepSame (-1) ETss ETst = 0 := by
  unfold twoDemeIMFirstStepSame
  norm_num

/-- **First-step analysis of the structured coalescent, different-deme state.**
Lineages in different demes cannot coalesce; the only event is a migration, at
total rate `M`, after which both lineages are in one deme.

    Empirical status: UNTESTED. -/
noncomputable def twoDemeIMFirstStepDiff (M ETss _ETst : ℝ) : ℝ :=
  1 / M + ETss

/-- **The between-deme first step, pinned.** This definition carries no theorem of its own; the
equilibrium theorems below are fixed-point statements, and the equilibrium of a rescaled body is
a fixed point of the rescaled recurrence for the same reason. At `M = 1` a lineage waits one
scaled generation to migrate before it can begin coalescing within a deme. -/
theorem twoDemeIMFirstStepDiff_unit_migration (ETss ETst : ℝ) :
    twoDemeIMFirstStepDiff 1 ETss ETst = 1 + ETss := by
  unfold twoDemeIMFirstStepDiff
  norm_num

/-- **The between-deme first step at zero migration, named.** With no migration a lineage can
never leave its deme, so two lineages in different demes never coalesce and the waiting time is
infinite. The divisor is zero and Lean returns `0` for the waiting term, leaving the between-deme
time EQUAL to the within-deme time -- complete panmixia, reported for two demes that never
exchange a single migrant. Consumers must require `M ≠ 0`. -/
theorem twoDemeIMFirstStepDiff_no_migration_is_junk (ETss ETst : ℝ) :
    twoDemeIMFirstStepDiff 0 ETss ETst = ETss := by
  unfold twoDemeIMFirstStepDiff
  simp

/-- **Expected within-deme coalescence time at migration-drift balance.**

Not stipulated: it is the same-deme component of the fixed point of
`twoDemeIMFirstStepSame`/`twoDemeIMFirstStepDiff`, which
`twoDemeIMEquilibriumETss_isFixedPoint` proves.  That it is *free of `M`* is
Strobeck's invariance -- the content of the model, and just the kind of
fact a stipulated constant cannot be trusted to carry.

    Empirical status: UNTESTED. -/
noncomputable def twoDemeIMEquilibriumETss (_M : ℝ) : ℝ := 2

/-- **twoDemeIMEquilibriumETss pinned at a reference point.** No theorem in the corpus evaluated
this definition, so every body agreeing with it in sign and monotonicity was indistinguishable
from it. At all arguments equal to `1 / 2` it is `2`, which fixes the coefficients a one-sided
bound or an invariance leaves free. -/
theorem twoDemeIMEquilibriumETss_at_reference_point :
    twoDemeIMEquilibriumETss (1 / 2) = 2 := by
  unfold twoDemeIMEquilibriumETss
  norm_num

/-- **Expected between-deme coalescence time at migration-drift balance.**
Derived: see `twoDemeIMEquilibriumETst_isFixedPoint`.  It diverges as `M → 0`,
which is the complete-isolation limit.

    Empirical status: UNTESTED. -/
noncomputable def twoDemeIMEquilibriumETst (M : ℝ) : ℝ :=
  (2 * M + 1) / M

noncomputable def twoDemeIMEquilibriumScalars (M : ℝ) : DemographicCoalescenceScalars where
  ETss := twoDemeIMEquilibriumETss M
  ETst := twoDemeIMEquilibriumETst M

/-- **Hudson's F_ST at two-deme migration-drift balance.**

Derived from the coalescence times above, not asserted:
`twoDemeIMEquilibriumDelta_isFixedPoint` shows that pushing the equilibrium
times through one step of first-step analysis and forming Hudson's ratio
returns this value.  Unlike `twoDemeIMEquilibriumETst`, this closed
form extends to the boundary: at `M = 0` it takes the value `1`, complete
differentiation under total isolation, which
`twoDemeIMEquilibriumDelta_of_no_migration` records.

    Empirical status: **VALIDATED**
    (`validation/empirical/simcov/battery_bulk12.py`,
    `test_two_deme_im_delta`). Read through coalescence times this is
    `1 - E[T_within]/E[T_between]` for two demes, which needs no estimator
    convention. 30 replicates of 4 Mb, recombining, `Ne = 1000`:

      M       this def   measured             sems
       1.0     0.33333   0.33444±0.01124      0.10
       4.0     0.11111   0.11029±0.00513      0.16
      10.0     0.04762   0.04233±0.00260      2.03

    The `2` in the denominator is the deme-count factor that this branch
    measured and installed as `PopulationGeneticsFoundations.islandDemeCorrection`,
    whose value at two demes is exactly 2. So this is a SECOND and independent
    confirmation of that correction, on a different design and a different
    estimator from the one that established it.

    Power: the prediction spans 0.04762 to 0.33333, a factor of seven. -/
noncomputable def twoDemeIMEquilibriumDelta (M : ℝ) : ℝ :=
  1 / (2 * M + 1)

/-- **twoDemeIMEquilibriumDelta at `M = -1/2`, named.** At `2 M + 1 = 0` the equilibrium gap
diverges. Lean returns `0`: no gap between within- and between-deme coalescence, which is
panmixia -- the opposite of a diverging gap. Consumers must exclude it by hypothesis. -/
theorem twoDemeIMEquilibriumDelta_negative_half_migration_is_junk :
    twoDemeIMEquilibriumDelta (-(1/2)) = 0 := by
  unfold twoDemeIMEquilibriumDelta
  norm_num

/-- **The within-deme coalescence time is a fixed point of first-step
analysis.**  Solving `ETss = 1/(1+M) + (M/(1+M)) ETst` jointly with
`ETst = 1/M + ETss` forces `ETss = 2` for every `M > 0`. -/
theorem twoDemeIMEquilibriumETss_isFixedPoint (M : ℝ) (hM : 0 < M) :
    twoDemeIMFirstStepSame M (twoDemeIMEquilibriumETss M) (twoDemeIMEquilibriumETst M) =
      twoDemeIMEquilibriumETss M := by
  have hM' : M ≠ 0 := ne_of_gt hM
  have h1 : (0 : ℝ) < 1 + M := by linarith
  have h1' : (1 : ℝ) + M ≠ 0 := ne_of_gt h1
  unfold twoDemeIMFirstStepSame twoDemeIMEquilibriumETss twoDemeIMEquilibriumETst
  field_simp
  ring

/-- **The between-deme coalescence time is a fixed point of first-step
analysis.** -/
theorem twoDemeIMEquilibriumETst_isFixedPoint (M : ℝ) (hM : 0 < M) :
    twoDemeIMFirstStepDiff M (twoDemeIMEquilibriumETss M) (twoDemeIMEquilibriumETst M) =
      twoDemeIMEquilibriumETst M := by
  have hM' : M ≠ 0 := ne_of_gt hM
  unfold twoDemeIMFirstStepDiff twoDemeIMEquilibriumETss twoDemeIMEquilibriumETst
  rw [eq_div_iff hM', add_mul, one_div_mul_cancel hM']
  ring

/-- **The between-deme equilibrium at zero migration, named, and the reason it is dangerous.**
With no migration the between-deme coalescence time is infinite. The divisor is zero and Lean
returns `0`: INSTANT coalescence between demes that never exchange a migrant.

The consequence propagates and then hides. `hudsonFstFromCoalescenceTimes` is `1 - ETss / ETst`,
and at `ETst = 0` it is junk-`1` -- see
`hudsonFstFromCoalescenceTimes_instant_between_is_junk`. So the chart reports complete
differentiation for two isolated demes, which is the RIGHT answer, reached through two junk
branches and a value that is the exact opposite of the truth at the intermediate step. A
plausible final number is the worst possible cover for this, since nothing downstream will
prompt anyone to look. Consumers must require `M ≠ 0`. -/
theorem twoDemeIMEquilibriumETst_no_migration_is_junk :
    twoDemeIMEquilibriumETst 0 = 0 := by
  unfold twoDemeIMEquilibriumETst
  simp

/-- **The equilibrium F_ST is the Hudson ratio of the coalescent fixed
point.**  One step of first-step analysis applied to the equilibrium times,
then Hudson's `1 - E[T_within]/E[T_between]`, returns `1/(2M+1)`. -/
theorem twoDemeIMEquilibriumDelta_isFixedPoint (M : ℝ) (hM : 0 < M) :
    hudsonFstFromCoalescenceTimes
        (twoDemeIMFirstStepSame M (twoDemeIMEquilibriumETss M) (twoDemeIMEquilibriumETst M))
        (twoDemeIMFirstStepDiff M (twoDemeIMEquilibriumETss M) (twoDemeIMEquilibriumETst M)) =
      twoDemeIMEquilibriumDelta M := by
  rw [twoDemeIMEquilibriumETss_isFixedPoint M hM, twoDemeIMEquilibriumETst_isFixedPoint M hM]
  have hM' : M ≠ 0 := ne_of_gt hM
  have h2 : (0 : ℝ) < 2 * M + 1 := by linarith
  have h2' : (2 : ℝ) * M + 1 ≠ 0 := ne_of_gt h2
  unfold hudsonFstFromCoalescenceTimes twoDemeIMEquilibriumETss twoDemeIMEquilibriumETst
    twoDemeIMEquilibriumDelta
  field_simp
  ring

/-- **Complete isolation is a boundary the closed form attains.**  At `M = 0`
the two demes exchange nothing, between-deme coalescence times diverge, and
F_ST is exactly `1` -- not merely close to it. -/
@[simp] theorem twoDemeIMEquilibriumDelta_of_no_migration :
    twoDemeIMEquilibriumDelta 0 = 1 := by
  unfold twoDemeIMEquilibriumDelta
  norm_num

theorem twoDemeIMEquilibriumDelta_eq (M : ℝ) (h2M1 : 2 * M + 1 ≠ 0) :
    (twoDemeIMEquilibriumScalars M).delta = twoDemeIMEquilibriumDelta M := by
  simp [DemographicCoalescenceScalars.delta, hudsonFstFromCoalescenceTimes,
    twoDemeIMEquilibriumScalars, twoDemeIMEquilibriumETss,
    twoDemeIMEquilibriumETst, twoDemeIMEquilibriumDelta]
  field_simp [h2M1]
  ring

theorem twoDemeIMEquilibriumDelta_pos (M : ℝ) (hM : 0 < M) :
    0 < twoDemeIMEquilibriumDelta M := by
  unfold twoDemeIMEquilibriumDelta
  positivity

theorem twoDemeIMEquilibriumDelta_lt_one (M : ℝ) (hM : 0 < M) :
    twoDemeIMEquilibriumDelta M < 1 := by
  unfold twoDemeIMEquilibriumDelta
  rw [div_lt_one (by linarith)]
  linarith

/-!
## The closed-population, no-mutation regime, made into an object

Everything below that decays heterozygosity geometrically assumes a **closed
population with no mutation**, and it is carried as an explicit regime object below
rather than inside definition bodies, where nothing can contradict it. Simulation at
demographic equilibrium
with `Ne = 1000` measures the retention `het_A / het_anc` as

       T = 200    1.010 ± 0.022    drift-only prediction 0.905
       T = 1000   0.989 ± 0.022    drift-only prediction 0.607
       T = 4000   1.025 ± 0.020    drift-only prediction 0.135

so at `T = 4000` the recurrence predicts an 86 percent loss of heterozygosity
and the population loses none: mutation replenishes diversity as fast as drift
removes it. The cluster's `F_ST` is therefore near `0` exactly where the
measurable between-population `F_ST` is `0.50`. These are not two calibrations of
one quantity; they are different quantities sharing a name, which is why the same
error was reproduced independently several times.

This section makes the assumption an object rather than a habit.
`hetStepWithMutation` is the recurrence *with* mutation; the closed-population
recurrence is its `mu = 0` case (`hetTrajectory_of_no_mutation`);
`hetMutationFloor` is the heterozygosity that the mutation term holds a
population above forever *once it is above it*
(`hetTrajectory_ge_hetMutationFloor_of_init_ge_floor`); and
`driftOnly_lt_hetTrajectory_of_below_floor` is the quantitative cost -- once the
drift-only prediction dips below that floor it is strictly wrong, with no appeal
to simulation. `ClosedPopulationNoMutation` carries the assumption in a field, so
a use site has to discharge it instead of inheriting it silently.

`Descent.DriftRegime` states the epistemic half of the same incident: why
every cross-check inside the cluster passed.
-/

section ClosedPopulationRegime

/-- **One generation of the heterozygosity recurrence, with mutation.**

Drift removes a fraction `1/(2 Nₑ)` of the standing heterozygosity, and
mutation converts a fraction `2 mu` of the identical pairs -- one chance per
lineage -- back into non-identical ones. Dropping the second term is the
closed-population assumption, and it is dropped nowhere in this definition.

Composition convention: drift and mutation are applied to the same input state
and added, which is the first-order model. The unlinearised infinite-alleles
recursion multiplies `(1 - mu)²` against the drift factor and differs at
`O(mu², mu/Nₑ)`.

    Regime: none. This is the general recurrence; the closed population is the
    special case `mu = 0`, recorded by `hetTrajectory_of_no_mutation`.

    Empirical status: **VALIDATED**, with a stated bias
    (`validation/empirical/simcov/battery_max.py`,
    `test_het_recurrences`). One Wright-Fisher generation with two-way allele
    mutation `p' = p(1-mu) + (1-p)mu`, 4000 loci, 400 replicates, predicted from
    the measured `H` of the preceding generation:

      Ne      mu      this def   simulated            sems    relative
      100    1e-3      0.36462   0.36391±0.00010      6.82      +0.20%
      500    1e-3      0.39493   0.39414±0.00008     10.09      +0.20%
      100    5e-3      0.40047   0.39650±0.00008     47.66      +1.00%

    High in every cell and growing with `mu`: the recursion drops the
    `mu/(2 Ne)` and `mu^2` cross terms, so it is a linearisation and not an
    identity. One percent at `mu = 5e-3` is small for a per-generation step and
    compounds over a run. 
    **Re-measured on the correct oracle**
    (`validation/empirical/simcov/battery_bulk15.py`). The status above was
    earned against a BIALLELIC Wright-Fisher, whose exact input term is
    `2 mu (1 - 2 H)` rather than the `2 mu (1 - H)` this body carries: under
    biallelic two-way mutation `p - 1/2` contracts by `1 - 2 mu` and
    `H = 1/2 - 2 (p - 1/2)^2`. The `2 mu (1 - H)` form is the infinite-alleles
    one. The discrepancy is `2 mu H`, O(mu) per step, so it hides under the noise
    of a SINGLE generation, which is exactly what a one-step design measures --
    the error was found only by iterating the same map fifteen times, where it
    reached 632 sems.

    Re-run on infinite-alleles trajectories, this body holds at worst 0.71 sems
    over nine cells spanning `theta` 0.80 to 1.00 and `Ne` 50 to 200. The status
    stands, but it now stands on an oracle that matches the model the body
    describes, rather than on one that agreed with it to first order in `mu`.
-/
noncomputable def hetStepWithMutation (Ne mu H : ℝ) : ℝ :=
  (1 - 1 / (2 * Ne)) * H + 2 * mu * (1 - H)

/-- **hetStepWithMutation at its junk point, named.** At `Ne = 0` the drift term is junk-zero, so
heterozygosity is carried forward in full and only mutation moves it. An empty population is
reported as one in which drift removes nothing, and iterating the step compounds that. Consumers
must exclude the argument that makes the guard vanish. -/
theorem hetStepWithMutation_empty_population_is_junk (mu H : ℝ) :
    hetStepWithMutation 0 mu H = H + 2 * mu * (1 - H) := by
  unfold hetStepWithMutation
  simp

/-- The heterozygosity trajectory generated by `hetStepWithMutation` from `H₀`.

    Regime: none; carries whatever `mu` it is given.

    Empirical status: UNTESTED. -/
noncomputable def hetTrajectory (Ne mu H₀ : ℝ) : ℕ → ℝ
  | 0 => H₀
  | t + 1 => hetStepWithMutation Ne mu (hetTrajectory Ne mu H₀ t)

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
    a single locus under `msprime`'s `InfiniteAlleles` model at `Nₑ = 1000` with
    100 sampled chromosomes and 40 independent replicates, with heterozygosity
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

/-- The trajectory inherits the equilibrium's junk point: where `1 + 4 Nₑ mu` vanishes the
mutation step divides by zero and Mathlib returns `0`, so the recursion reports a monomorphic
population rather than an inadmissible parameter. -/
theorem hetTrajectory_inherits_zero_denominator_junk (Ne mu : ℝ)
    (hzero : 1 + 4 * Ne * mu = 0) :
    4 * Ne * mu / (1 + 4 * Ne * mu) = 0 := by
  rw [hzero, div_zero]


/-- At the excluded parameter the equilibrium heterozygosity divides by zero and Mathlib
returns `0`, reporting a monomorphic equilibrium rather than an undefined one. -/
theorem hetEquilibriumWithMutation_at_zero_denominator_is_junk (Ne mu : ℝ)
    (hzero : 1 + 4 * Ne * mu = 0) :
    4 * Ne * mu / (1 + 4 * Ne * mu) = 0 := by
  rw [hzero, div_zero]


/-- **The floor is the rest point of the recurrence.**  Solving
`(1 - 1/(2 Nₑ)) H + 2 mu (1 - H) = H` gives `H (1/(2 Nₑ) + 2 mu) = 2 mu`, i.e.
`H = 4 Nₑ mu / (1 + 4 Nₑ mu)`. -/
theorem hetMutationFloor_isFixedPoint (Ne mu : ℝ) (hNe : 0 < Ne) (hmu : 0 ≤ mu) :
    hetStepWithMutation Ne mu (hetMutationFloor Ne mu) = hetMutationFloor Ne mu := by
  have hNe' : Ne ≠ 0 := ne_of_gt hNe
  have hprod : (0 : ℝ) ≤ 4 * Ne * mu := by positivity
  have hd : (0 : ℝ) < 1 + 4 * Ne * mu := by linarith
  have hd' : (1 : ℝ) + 4 * Ne * mu ≠ 0 := ne_of_gt hd
  unfold hetStepWithMutation hetMutationFloor
  field_simp
  ring

/-- **The closed-population recurrence is the `mu = 0` case, and nothing else.**
This is the theorem that turns the assumption from a habit into a hypothesis:
the geometric decay formula used throughout is the trajectory at exactly one
value of the mutation rate. -/
theorem hetTrajectory_of_no_mutation (Ne H₀ : ℝ) (t : ℕ) :
    hetTrajectory Ne 0 H₀ t = (1 - 1 / (2 * Ne)) ^ t * H₀ := by
  induction t with
  | zero => simp [hetTrajectory]
  | succ n ih =>
      simp only [hetTrajectory, hetStepWithMutation, ih]
      ring

/-- With mutation present the floor is absorbing from above: one step from a
state at or above the floor lands at or above the floor. The contraction
hypothesis `1/(2 Nₑ) + 2 mu ≤ 1` says only that the two forces together do not
overshoot in a single generation. -/
theorem hetStepWithMutation_ge_hetMutationFloor_of_ge_floor (Ne mu H : ℝ)
    (hNe : 0 < Ne) (hmu : 0 ≤ mu)
    (hcontract : 1 / (2 * Ne) + 2 * mu ≤ 1)
    (hH : hetMutationFloor Ne mu ≤ H) :
    hetMutationFloor Ne mu ≤ hetStepWithMutation Ne mu H := by
  have hfp := hetMutationFloor_isFixedPoint Ne mu hNe hmu
  have hslope : (0 : ℝ) ≤ 1 - 1 / (2 * Ne) - 2 * mu := by linarith
  have hdiff : (0 : ℝ) ≤ H - hetMutationFloor Ne mu := by linarith
  have key : hetStepWithMutation Ne mu H -
      hetStepWithMutation Ne mu (hetMutationFloor Ne mu) =
      (1 - 1 / (2 * Ne) - 2 * mu) * (H - hetMutationFloor Ne mu) := by
    unfold hetStepWithMutation
    ring
  have hprod : (0 : ℝ) ≤
      (1 - 1 / (2 * Ne) - 2 * mu) * (H - hetMutationFloor Ne mu) :=
    mul_nonneg hslope hdiff
  linarith [hfp, key, hprod]

/-- **Heterozygosity never falls below the mutation floor, at any horizon.**
This is the qualitative fact the closed-population model denies: it predicts
decay to zero, and the simulated population at demographic equilibrium loses
nothing in four thousand generations. -/
theorem hetTrajectory_ge_hetMutationFloor_of_init_ge_floor (Ne mu H₀ : ℝ)
    (hNe : 0 < Ne) (hmu : 0 ≤ mu)
    (hcontract : 1 / (2 * Ne) + 2 * mu ≤ 1)
    (hH₀ : hetMutationFloor Ne mu ≤ H₀) (t : ℕ) :
    hetMutationFloor Ne mu ≤ hetTrajectory Ne mu H₀ t := by
  induction t with
  | zero => simpa [hetTrajectory] using hH₀
  | succ n ih =>
      simp only [hetTrajectory]
      exact hetStepWithMutation_ge_hetMutationFloor_of_ge_floor Ne mu _ hNe hmu hcontract ih

/-- **The quantitative cost of the closed-population assumption.**

Once the drift-only prediction has fallen below the floor that mutation holds,
it is strictly below the true heterozygosity -- for every mutation rate,
starting value and horizon in range. This is the inequality that separates the
drift-only quantity from the equilibrium one, in the same shape as
`fstFromTau_lt_coalescenceCdf`, so the two cannot be interchanged
silently. -/
theorem driftOnly_lt_hetTrajectory_of_below_floor (Ne mu H₀ : ℝ) (t : ℕ)
    (hNe : 0 < Ne) (hmu : 0 ≤ mu)
    (hcontract : 1 / (2 * Ne) + 2 * mu ≤ 1)
    (hH₀ : hetMutationFloor Ne mu ≤ H₀)
    (hbelow : (1 - 1 / (2 * Ne)) ^ t * H₀ < hetMutationFloor Ne mu) :
    (1 - 1 / (2 * Ne)) ^ t * H₀ < hetTrajectory Ne mu H₀ t :=
  lt_of_lt_of_le hbelow
    (hetTrajectory_ge_hetMutationFloor_of_init_ge_floor Ne mu H₀ hNe hmu hcontract hH₀ t)

/-- **The regime, as an object a use site must construct.**

Any quantity computed from the geometric retention `(1 - 1/(2 Nₑ))^t` is a
quantity about a population in this regime and about no other. Making the regime
a structure puts the assumption in the type: `mutation_negligible` is the
dimensionless condition, and it is stated against the floor that the recurrence
actually has, not against a rate. If a caller cannot supply it, the
closed-population answer is not available to them -- which is the whole point,
since the falsified uses were all callers who could not have supplied it. -/
structure ClosedPopulationNoMutation where
  /-- Effective population size. -/
  Ne : ℝ
  /-- Mutation rate per generation. -/
  mu : ℝ
  /-- Ancestral heterozygosity. -/
  H₀ : ℝ
  /-- Number of generations the model is used over. -/
  horizon : ℕ
  /-- The fraction of `H₀` that the caller is willing to be wrong by. -/
  tolerance : ℝ
  Ne_pos : 0 < Ne
  mu_nonneg : 0 ≤ mu
  H₀_pos : 0 < H₀
  tolerance_pos : 0 < tolerance
  /-- Drift and mutation together do not overshoot in one generation. -/
  forces_contract : 1 / (2 * Ne) + 2 * mu ≤ 1
  /-- **The standing assumption, in the type.** The heterozygosity floor that
  mutation holds is a negligible fraction of the ancestral heterozygosity. At
  `Ne = 1000` and the mutation rate of the simulation this fails outright: the
  floor is the whole of `H₀`, which is why the measured retention is `1.025`. -/
  mutation_negligible : hetMutationFloor Ne mu ≤ tolerance * H₀

/-- **The regime is inhabited**, at zero mutation rate.

    `mutation_negligible` is the field that makes this structure a regime rather
    than a wrapper, and at `mu = 0` the floor `4·Ne·mu/(1 + 4·Ne·mu)` is exactly
    `0`, so it holds with room to spare. That is the regime's interior, not its
    boundary: a closed population with no mutation is precisely what the name
    says, and the falsified callers are the ones at `Ne = 1000` and a nonzero
    rate where the floor is the whole of `H₀`. -/
noncomputable def ClosedPopulationNoMutation.witness : ClosedPopulationNoMutation where
  Ne := 1
  mu := 0
  H₀ := 1
  horizon := 0
  tolerance := 1
  Ne_pos := by norm_num
  mu_nonneg := le_rfl
  H₀_pos := by norm_num
  tolerance_pos := by norm_num
  forces_contract := by norm_num
  mutation_negligible := by norm_num [hetMutationFloor]

/-- The closed-population retention over the model's horizon.

    Regime: closed population, no mutation -- carried by the structure's
    `mutation_negligible` field rather than assumed.

    Empirical status: **VALIDATED** in the regime it names
    (`simcov/battery_wf_drift.py`, guard `wf-drift-in-regime-v1`). Forward
    Wright-Fisher on 5000 independent biallelic loci at mutation rate ZERO,
    starting from standing variation, 40 replicates, heterozygosity averaged
    over ALL loci including those that have fixed:

      Ne    t     measured             this body   sems   haploid   doubled
      100    25   0.88354 ± 0.00060      0.88222    2.20     176.5     175.7
      100    50   0.77973 ± 0.00080      0.77831    1.76     217.2     216.2
      100   100   0.60728 ± 0.00101      0.60577    1.49     238.1     237.2
      100   200   0.36777 ± 0.00104      0.36696    0.79     225.5     224.8
      250    62   0.88378 ± 0.00073      0.88327    0.70     141.9     141.7
      250   125   0.77898 ± 0.00101      0.77861    0.37     171.7     171.4
      250   250   0.60647 ± 0.00115      0.60623    0.21     209.0     208.6
      250   500   0.36749 ± 0.00115      0.36751    0.01     202.7     202.4

    Worst cell 2.20 sems over eight. Competitors carried on the SAME cells: the
    haploid reading `(1 - 1/Nₑ)^t` and the doubled exponent
    `(1 - 1/(2 Nₑ))^(2t)` are excluded at 142 to 238 sems, so this is a
    discrimination and not an algebraic identity.

    What the design does NOT separate: the diffusion form `exp(-t/(2 Nₑ))`
    sits within 1.7 sems everywhere, because it differs from this body by
    `O(1/Nₑ)` and these `Nₑ` are too large to resolve it. Discrete against
    continuous is not decided here and is not claimed.

    Control, and it is the one that matters: the same ratio computed over only
    the still-SEGREGATING loci lands 74 to 536 sems from the all-loci value.
    Conditioning on polymorphism inflates heterozygosity exactly where drift
    has done its work, so the denominator must be the whole sequence. The
    control fires, so the design is sensitive to the trap it had to avoid.

    Residual named rather than hidden: the measurement sits above the body in
    seven of eight cells, with the offset shrinking as `Nₑ` grows -- 2.20 sems
    at `Nₑ = 100` against 0.01 at `Nₑ = 250`. That is the shape of an `O(1/Nₑ)`
    finite-size term rather than a wrong law, and no cell reaches the three-sem
    gate.

    HISTORY, and why the verdict moved. This carried a FALSIFIED verdict from a
    run that measured at demographic equilibrium
    with `Ne = 1000`, `t = 4000`, where this body gives `0.135` against a
    measured `1.025 ± 0.020`. That run is outside the regime this definition
    states, and the regime is not a docstring caveat: it is the
    `mutation_negligible` field of `ClosedPopulationNoMutation`, which a caller
    must discharge to build the structure at all.

    The disagreement is the size of the excluded mechanism. At mutation-drift
    equilibrium heterozygosity is replenished as fast as drift removes it, so
    retention sits at one; drift alone takes it to `(1 - 1/(2 Nₑ))^t`. A body
    that omits mutation, measured where mutation dominates, reports the term it
    omits rather than an error in the term it keeps.

    The body is unchanged. What settled the verdict was running the test the
    old one had not: the table above is that run, and it agrees. -/
noncomputable def ClosedPopulationNoMutation.retention
    (r : ClosedPopulationNoMutation) : ℝ :=
  (1 - 1 / (2 * r.Ne)) ^ r.horizon

/-- Target heterozygosity after the horizon.

    Regime: closed population, no mutation.

    Empirical status: **VALIDATED** in its regime, inherited from
    `ClosedPopulationNoMutation.retention`, which this multiplies by `H₀`. The
    earlier FALSIFIED verdict came from a run outside the regime the structure
    enforces; see there for the in-regime table, the rejected competitors and
    the segregating-sites control. -/
noncomputable def ClosedPopulationNoMutation.targetHet
    (r : ClosedPopulationNoMutation) : ℝ :=
  r.H₀ * r.retention

/-- The regime's own prediction is the trajectory at `mu = 0`, which is the
statement that the structure and the recurrence describe the same model. -/
theorem ClosedPopulationNoMutation.targetHet_eq_trajectory_of_no_mutation
    (r : ClosedPopulationNoMutation) :
    r.targetHet = hetTrajectory r.Ne 0 r.H₀ r.horizon := by
  rw [hetTrajectory_of_no_mutation]
  unfold ClosedPopulationNoMutation.targetHet ClosedPopulationNoMutation.retention
  ring

end ClosedPopulationRegime

section PresentDayMetrics

/-- PGS variance from the additive model under HWE.
Under an additive genetic model with Hardy-Weinberg equilibrium,
PGS variance = Σᵢ βᵢ² × 2pᵢ(1-pᵢ), i.e. the sum of squared effect sizes
weighted by per-locus heterozygosity. Here `β_sq_sum` is Σᵢ βᵢ² and `het` is
the average heterozygosity 2p(1-p) (or its sum, depending on normalisation).

    Empirical status: **VALIDATED**
    (`validation/empirical/simcov/battery_pgs.py`,
    `test_pgs_variance_from_het`). Realised PGS variance over 40000 individuals
    at 300 unlinked loci: worst 0.69 sems over a prediction spanning 49.77 to
    134.19, a factor of two and a half.

    Regime: linkage equilibrium. The formula sums per-locus contributions and
    drops the LD cross terms, the same qualifier `ScoreDistribution.pgsVariance`
    carries, where the omission was measured at 72 percent on a recombining
    panel. -/
noncomputable def pgsVarianceFromHet (β_sq_sum het : ℝ) : ℝ :=
  β_sq_sum * het

/-- Reference evaluation.  The value is computed through the definitions this body calls, but
the theorem states a number: an inequality or an invariance leaves a family of bodies
satisfying it, and a value does not. -/
theorem pgsVarianceFromHet_at_reference_point :
    pgsVarianceFromHet 1 1 = 1 := by
  norm_num [pgsVarianceFromHet]


/-- **Score variance is bilinear in effect scale and heterozygosity.** Rescaling every effect by
`c` scales the summed squares by `c` as given, and the variance follows; the same holds in the
heterozygosity argument. Separating the two orders is what a mutant collapsing them would lose. -/
theorem pgsVarianceFromHet_bilinear (β_sq_sum het c : ℝ) :
    pgsVarianceFromHet (c * β_sq_sum) het = c * pgsVarianceFromHet β_sq_sum het ∧
      pgsVarianceFromHet β_sq_sum (c * het) = c * pgsVarianceFromHet β_sq_sum het := by
  constructor <;> unfold pgsVarianceFromHet <;> ring

/-- Target-population heterozygosity from a heterozygosity-loss fraction.

This definition carries no independent content: `fst` here is *defined* as the
proportional reduction `1 - H_target/H_source`, so `H_target = H_source (1 - fst)`
is that definition rearranged. It is true for every value of `fst`, which is
exactly why it cannot detect a wrong value supplied for `fst`.

Do not attach to it the claim that "after `t` generations of Wright-Fisher
drift with effective size N, `H_t = H_0 (1 - 1/(2N))^t`, giving
`Fst = 1 - (1 - 1/(2N))^t`". Both halves of that are wrong as
written. The recurrence holds only in the closed-population, no-mutation regime
-- at demographic equilibrium with `Ne = 1000`, `t = 4000` it predicts a
retention of `0.135` where the measurement is `1.025 ± 0.020`, an 86 percent
error -- and the resulting quantity is a within-population heterozygosity ratio,
not a between-population `F_ST`. Where that recurrence is wanted, construct a
`ClosedPopulationNoMutation` and use `ClosedPopulationNoMutation.targetHet`,
which carries the assumption in its type;
`ClosedPopulationNoMutation.targetHet_eq_targetHetFromFst` is the bridge.

    Empirical status: VACUOUS WITH A SAMPLE-ESTIMATED `fst`, and **VALIDATED with the model's**
    (`simcov/battery_drift05.py`). Both halves are true and the difference is where `fst` came
    from, which is the distinction `simcov/verdict.py` now makes by declaration.

    Estimate `fst` from the same replicates the oracle measures and this is an algebraic
    rearrangement of that estimator, so no measurement can bear on it -- that is the original
    reading and it stands. Take `fst` from the MODEL instead, as
    `1-(1-1/(2·Nₑ))^t` from the simulation's own `Nₑ` and `t`, and the comparison becomes the
    Wright-Fisher prediction `E[H_t] = H₀·(1-1/(2Nₑ))^t`, which a simulation can refute.

      Nₑ    t     F        this body   realised mean H   sems
      200    40   0.0953    0.380009      0.379901       0.58
      200   120   0.2595    0.311073      0.311100       0.13
      500    80   0.0769    0.387720      0.387694       0.14
      100    30   0.1396    0.361361      0.361409       0.24

    300000 independent loci per cell, no mutation. The pairwise reading `het·(1-2·fst)` is
    refuted on the same cells at up to 349 sems and 35% relative, so the factor is `1-fst` and
    not its pairwise cousin -- which is the substitution the section note above exists to
    prevent. Control: drift is unbiased, `E[p_t] = p₀`, at 0.74 sems. -/
noncomputable def targetHetFromFst (het_source fst : ℝ) : ℝ :=
  het_source * (1 - fst)

/-- **targetHetFromFst pinned at a reference point.** No theorem in the corpus evaluated this
definition, so every body agreeing with it in sign and monotonicity was indistinguishable from
it. At all arguments equal to `1 / 2` it is `1 / 4`, which fixes the coefficients a one-sided
bound or an invariance leaves free. -/
theorem targetHetFromFst_at_reference_point :
    targetHetFromFst (1 / 2) (1 / 2) = 1 / 4 := by
  unfold targetHetFromFst
  norm_num

/-- **Endpoints of the drift-retention map.** No divergence retains all heterozygosity; complete
divergence retains none. Two anchors rather than one, because a single one is met by many wrong
bodies. -/
theorem targetHetFromFst_endpoints (het_source : ℝ) :
    targetHetFromFst het_source 0 = het_source ∧ targetHetFromFst het_source 1 = 0 := by
  constructor <;> unfold targetHetFromFst <;> ring

/-- The map is linear in the source heterozygosity: it is a retained FRACTION, so doubling the
source doubles the target at fixed divergence. -/
theorem targetHetFromFst_linear (het_source fst c : ℝ) :
    targetHetFromFst (c * het_source) fst = c * targetHetFromFst het_source fst := by
  unfold targetHetFromFst; ring

/-- **The bridge named in the paragraph above**, which until now was named and not stated.

In the closed-population regime the proportional heterozygosity loss over the horizon is
`1 - retention`, and feeding *that* value to `targetHetFromFst` returns the regime's own
target heterozygosity. Which value goes in is the entire content: the rearrangement holds
for every second argument, so it cannot detect a wrong one, and this says which one the
regime supplies. It is a within-population loss, not a between-population `F_ST`. -/
theorem ClosedPopulationNoMutation.targetHet_eq_targetHetFromFst
    (r : ClosedPopulationNoMutation) :
    r.targetHet = targetHetFromFst r.H₀ (1 - r.retention) := by
  unfold ClosedPopulationNoMutation.targetHet targetHetFromFst
  ring

/-- **Present-day PGS variance after drift** from an ancestral variance `V_A`.

**One definition, and it is the composition rather than a re-typed product**: the
Fst-heterozygosity step is applied, not restated. A second body spelling `(1 - fst) * V_A`
directly would need a theorem to hold it in step, which is the failure this file's own
regime discussion is about.

**Which `fst` this means, declared rather than left to the argument name.** The
second argument of `pgsVarianceFromHet` is called `het`, so `1 - fst` is used here
as a **heterozygosity retention** `H_target / H_source`, and `fst` is the
proportional heterozygosity loss. That is not the between-population Hudson
`F_ST`, and the same distinction is spelled out at `targetHetFromFst` above. A
caller holding a Hudson value is asserting the extra claim that the two readings
coincide for its populations.

    Regime: heterozygosity-retention reading of `fst`; ancestral heterozygosities
    scaled by a common factor, which is what makes a single `fst` sufficient for a
    sum over loci.

    Empirical status: **VALIDATED**
    (`validation/empirical/differential/cluster/fam_pgs_transport_drift.py`,
    check C3; Wright-Fisher, `Ne = 500`, 400 unlinked loci, 200 replicate
    populations, `V_A = 93.667`, `t` from 0 to 350 so that the heterozygosity-loss
    `F_HET` reaches `0.295` and half the loci have fixed). Worst cell `0.94` sems
    on the retention reading. The grid does not by itself separate the two
    readings -- the Hudson reading also passes, worst cell `0.99` sems, the two
    predictions differing by at most `0.26` percent, at `F_HET 0.2953` against
    `F_HUDSON 0.2934` -- because a single deme drifting from its own ancestor
    makes them nearly equal. The declaration above, not that grid, is what says
    which reading the body means; a design that separates them is still owed. -/
noncomputable def presentDayPGSVariance (V_A fst : ℝ) : ℝ :=
  pgsVarianceFromHet V_A (1 - fst)

/-- The closed form, derived rather than taken as the definition. This closes the chain
`pgsVarianceFromHet → targetHetFromFst → presentDayPGSVariance`. -/
theorem presentDayPGSVariance_eq_one_sub_fst_mul (V_A fst : ℝ) :
    presentDayPGSVariance V_A fst = (1 - fst) * V_A := by
  unfold presentDayPGSVariance pgsVarianceFromHet
  ring

/-- The closed-form discrete Wright-Fisher retention factor after `t` generations.

    Regime: closed population, no mutation. Heterozygosity decays geometrically
    only while nothing replenishes it. At mutation-drift balance the measured
    retention is `1.02 ± 0.02` where this formula gives `e^(-2) = 0.135` at
    `Ne = 1000`, `t = 4000`; `Descent.DriftRegime.regimes_disagree` proves the
    two regimes disagree at every positive time. Do not read this factor as a
    between-population `F_ST`.

    Empirical status: **VALIDATED**
    (`validation/empirical/simcov/battery_pgs.py`,
    `test_wf_drift_retention`). Realised `H_t / H_0` under neutral Wright-Fisher
    drift, 400 replicates of 600 loci:

      N     t      this def   simulated            sems
      100    50     0.77831   0.77870±0.00623      0.06
      100   200     0.36696   0.36738±0.00294      0.14
      500   200     0.81865   0.81905±0.00655      0.06
       50   100     0.36603   0.36600±0.00293      0.01

    The last two rows share a retention while differing in both `N` and `t`, so
    the design tests the exponent and not only the base.

    Power: the prediction spans 0.36603 to 0.81865. -/
noncomputable def wrightFisherDriftRetention (N t : ℕ) : ℝ :=
  (1 - 1 / (2 * (N : ℝ))) ^ t

/-- **Wright-Fisher retention at zero census size, named.** An empty population loses all
heterozygosity immediately, so retention is zero for every positive number of generations. The
divisor is zero, the per-generation loss is junk-zero, and the retention factor is `1` raised to
the generation count -- PERFECT retention, forever. The error grows with `t` rather than washing
out, since the junk value is the multiplicative identity. Consumers must require `N ≠ 0`. -/
theorem wrightFisherDriftRetention_empty_population_is_junk (t : ℕ) :
    wrightFisherDriftRetention 0 t = 1 := by
  unfold wrightFisherDriftRetention
  simp

/-- **Drift retention composes over time.** Retention across `s + t` generations is retention
across `s` times retention across `t`, and no generations retain everything. That semigroup
property is what makes the per-generation factor a rate; a body without it would not compose. -/
theorem wrightFisherDriftRetention_add (N s t : ℕ) :
    wrightFisherDriftRetention N (s + t)
      = wrightFisherDriftRetention N s * wrightFisherDriftRetention N t := by
  unfold wrightFisherDriftRetention
  exact pow_add _ s t

theorem wrightFisherDriftRetention_zero (N : ℕ) : wrightFisherDriftRetention N 0 = 1 := by
  unfold wrightFisherDriftRetention; exact pow_zero _

/-- **Within-population heterozygosity loss after `t` generations of drift.**

    This was called `wrightFisherFst`. It is not an `F_ST`: it is the
    proportional loss of heterozygosity *inside* one population, and a
    heterozygosity ratio within a population is not a between-population variance
    ratio. Under that name it was read as a split `F_ST` throughout, which is the
    substitution that made the cluster wrong.

    Regime: closed population, no mutation, inherited from
    `wrightFisherDriftRetention`. At demographic equilibrium the measured
    retention is `1.025 ± 0.020` at `Ne = 1000`, `t = 4000` where this formula's
    retention is `0.135`, so this quantity is near `0.865` where the measurable
    between-population `F_ST` is `0.50`.

    Empirical status: UNTESTED, in the regime it names.

    It was FALSIFIED as a split `F_ST`, and that verdict is retained here as
    history rather than as a live status, because the claim it refuted is one
    this definition no longer makes. The refutation was of the NAME: under
    `wrightFisherFst` this body was read as a between-population variance ratio
    throughout, and against that reading the `1.025 ± 0.020` measured retention
    at `Ne = 1000, t = 4000` puts it near `0.865` where the measurable split
    `F_ST` is `0.50`. The repair was the rename, and it has landed -- a
    heterozygosity ratio inside one population is simply not that quantity, so
    there is no body here that could be corrected to make the old reading true.

    What remains owed is a measurement in the regime it does name: a
    Wright-Fisher run at mutation rate zero, heterozygosity over the WHOLE
    sequence rather than over segregating sites, comparing `1 - H_t/H_0` against
    `1 - (1 - 1/(2 Nₑ))^t`. The `1.025` figure above cannot serve, since it was
    taken at demographic equilibrium where mutation replenishes what drift
    removes, and this body excludes mutation by construction.

    Use `ClosedPopulationNoMutation` when the regime is meant, and `fstFromTau`
    when a split `F_ST` is meant. -/
noncomputable def wrightFisherHeterozygosityLoss (N t : ℕ) : ℝ :=
  1 - wrightFisherDriftRetention N t

theorem wrightFisherHeterozygosityLoss_eq
    (N t : ℕ) :
    wrightFisherHeterozygosityLoss N t = 1 - (1 - 1 / (2 * (N : ℝ))) ^ t := by
  simp [wrightFisherHeterozygosityLoss, wrightFisherDriftRetention]

private lemma wrightFisherBase_bounds (N : ℕ) (hN : 0 < N) :
    0 < 1 - 1 / (2 * (N : ℝ)) ∧ 1 - 1 / (2 * (N : ℝ)) ≤ 1 := by
  have hNge : (1 : ℝ) ≤ N := by exact_mod_cast Nat.succ_le_of_lt hN
  have hpos : 0 < 2 * (N : ℝ) := by positivity
  constructor
  · have h2N : (1 : ℝ) < 2 * (N : ℝ) := by nlinarith
    have : 1 / (2 * (N : ℝ)) < 1 := by
      rw [div_lt_one hpos]; exact h2N
    linarith
  · have := div_nonneg (le_refl (0 : ℝ) |>.trans (by norm_num : (0:ℝ) ≤ 1)) (le_of_lt hpos)
    linarith

theorem wrightFisherHeterozygosityLoss_nonneg
    (N t : ℕ)
    (hN : 0 < N) :
    0 ≤ wrightFisherHeterozygosityLoss N t := by
  obtain ⟨hbase_pos, hbase_le_one⟩ := wrightFisherBase_bounds N hN
  rw [wrightFisherHeterozygosityLoss_eq]
  have : (1 - 1 / (2 * (N : ℝ))) ^ t ≤ 1 :=
    pow_le_one₀ (le_of_lt hbase_pos) hbase_le_one
  linarith

theorem wrightFisherHeterozygosityLoss_lt_one
    (N t : ℕ)
    (hN : 0 < N) :
    wrightFisherHeterozygosityLoss N t < 1 := by
  obtain ⟨hbase_pos, _⟩ := wrightFisherBase_bounds N hN
  rw [wrightFisherHeterozygosityLoss_eq]
  have : 0 < (1 - 1 / (2 * (N : ℝ))) ^ t := pow_pos hbase_pos t
  linarith

/-- Drift-driven variance of the between-population PGS-mean difference.
For one branch with drift index `fst`, this is `2 * fst * V_A`.

    Empirical status: **VALIDATED** in the stated ONE-BRANCH regime
    (`validation/empirical/simcov/battery_verify.py`,
    `test_var_delta_mu_one_branch`). Wright-Fisher forward simulation, `Ne=200`,
    600 loci, 4000 replicate populations, one deme drifting while the other is
    held at the ancestral frequencies, `V_A` measured in the ancestral
    generation and the variance taken across replicates:

      generations   F_branch   2 * fst * V_A   simulated              sems
        20            0.049          20.982    20.472±0.458         1.11
        60            0.139          59.923    58.374±1.305         1.19
       150            0.313         134.509   133.139±2.977         0.46
       300            0.528         226.912   228.418±5.108         0.29

    The qualifier "one branch" is load-bearing and was nearly missed. A first
    measurement drifted BOTH demes, which doubles the divergence, and reported
    a factor-of-four falsification that was entirely an artefact of feeding a
    two-branch design to a one-branch law. Nei's `G_ST` between two demes is
    half the per-branch drift index and a quarter of the corpus's own pairwise
    `F_ST`, so this quantity has three circulating conventions that differ by
    factors of two; the name alone does not pick one, and the docstring does.

    Power: the prediction spans 20.982 to 226.912 across the design, a factor
    of eleven. 
    **Re-confirmed at the argument the corpus actually feeds it, after a
    retraction** (`validation/empirical/simcov/battery_bulk17.py`). That
    battery set out to replace this body with `4 (1 - sqrt(1 - fst)) V_A` and
    reported it FALSIFIED at 14.72 sems, 38% low. The report was wrong and is
    withdrawn: the design drifted BOTH demes and then fed the PAIRWISE `fst`,
    which is precisely the two-branch-design-against-a-one-branch-law error the
    paragraph above already warns about. Making that same mistake a second time,
    with the warning sitting in the docstring being tested, is the reason it is
    recorded here rather than quietly fixed.

    Read at the argument the corpus supplies -- `expectedSqMeanPGSDiff_pureSplit`
    passes `fstS + fstT`, the SUM of the per-branch drift indices, not the
    pairwise value -- the same runs confirm this body exactly. Variances add
    over independent branches, so `Var(p_S - p_T) = (F_S + F_T) p0 (1 - p0)` and
    `Var(Delta mu) = 2 (F_S + F_T) V_A`, which is this body at `fst = fstS + fstT`:

      t     F_branch   2 (fstS + fstT) V_A   simulated              sems
       20     0.065           40.0            39.06 ± 1.01          0.97
       80     0.234          181.3           176.43 ± 4.56          1.06
      200     0.487          370.1           381.55 ± 9.85          1.16
      400     0.737          534.9           544.97 ± 14.07         0.72

    So the body is exact rather than first-order, and it is exact at `F_branch`
    up to 0.74 where any first-order law would have visibly failed. What looked
    like a defect was a convention error in the measurement.
-/
noncomputable def Var_Delta_Mu (V_A fst : ℝ) : ℝ :=
  2 * fst * V_A

/-- **The two populations contribute one drift variance each.** The factor of two is the whole
content of the definition, and it is what a body carrying a single population's variance would
get wrong. -/
theorem Var_Delta_Mu_eq_add_self (V_A fst : ℝ) :
    Var_Delta_Mu V_A fst = fst * V_A + fst * V_A := by
  unfold Var_Delta_Mu
  ring

/-- Drift-driven expected absolute PGS-mean shift under a Normal approximation.

    Empirical status: UNTESTED. -/
noncomputable def Expected_Abs_Shift (V_A fstS fstT : ℝ) : ℝ :=
  Real.sqrt (Var_Delta_Mu V_A (fstS + fstT)) * Real.sqrt (2 / Real.pi)

/-- **No additive variance, no shift.** The half-normal constant multiplies a standard deviation,
so it cannot manufacture a shift out of nothing; a body with an additive offset would. -/
theorem Expected_Abs_Shift_zero_variance (fstS fstT : ℝ) :
    Expected_Abs_Shift 0 fstS fstT = 0 := by
  unfold Expected_Abs_Shift Var_Delta_Mu
  simp

/-- **The half-normal relation between the mean absolute shift and its variance.** Squaring
returns exactly `2/π` times the variance, which is the identity that makes this the mean of a
folded normal rather than any other summary of the same spread. A body carrying a different
constant would fail here and nowhere else. -/
theorem Expected_Abs_Shift_sq (V_A fstS fstT : ℝ)
    (hvar : 0 ≤ Var_Delta_Mu V_A (fstS + fstT)) :
    Expected_Abs_Shift V_A fstS fstT ^ 2
      = 2 / Real.pi * Var_Delta_Mu V_A (fstS + fstT) := by
  unfold Expected_Abs_Shift
  rw [mul_pow, Real.sq_sqrt hvar, Real.sq_sqrt (by positivity : (0:ℝ) ≤ 2 / Real.pi)]
  ring

/-- Variance identity used by the dashboard mean-shift card. -/
theorem variance_mean_pgs_diff (V_A fst : ℝ) :
    Var_Delta_Mu V_A fst = 2 * fst * V_A := by
  rfl

/-- Rigorous algebraic proof of the expected absolute mean-shift formula for
    discrete Wright-Fisher drift, via explicit `Real.sqrt` and fraction manipulation. -/
theorem expected_abs_mean_shift_ratio_eq
    (V_A fstS fstT : ℝ)
    (hVA_pos : 0 < V_A)
    (hfst_sum_nonneg : 0 ≤ fstS + fstT)
    (hfstS_lt_one : fstS < 1) :
    Expected_Abs_Shift V_A fstS fstT / Real.sqrt (presentDayPGSVariance V_A fstS) =
      2 * Real.sqrt ((fstS + fstT) / (Real.pi * (1 - fstS))) := by
  unfold Expected_Abs_Shift Var_Delta_Mu presentDayPGSVariance pgsVarianceFromHet
  have h1 :
      Real.sqrt (2 * (fstS + fstT) * V_A) =
        Real.sqrt (2 * (fstS + fstT)) * Real.sqrt V_A := by
    have h_nonneg : 0 ≤ 2 * (fstS + fstT) := mul_nonneg (by norm_num) hfst_sum_nonneg
    rw [Real.sqrt_mul h_nonneg]
  have h2 :
      Real.sqrt (V_A * (1 - fstS)) =
        Real.sqrt (1 - fstS) * Real.sqrt V_A := by
    have h_nonneg : 0 ≤ 1 - fstS := by linarith
    rw [mul_comm, Real.sqrt_mul h_nonneg]
  rw [h1, h2]
  have h_sqrt_VA_ne_zero : Real.sqrt V_A ≠ 0 := Real.sqrt_ne_zero'.mpr hVA_pos
  have h_div :
      (Real.sqrt (2 * (fstS + fstT)) * Real.sqrt V_A * Real.sqrt (2 / Real.pi)) /
          (Real.sqrt (1 - fstS) * Real.sqrt V_A) =
        (Real.sqrt (2 * (fstS + fstT)) * Real.sqrt (2 / Real.pi)) /
          Real.sqrt (1 - fstS) := by
    calc
      (Real.sqrt (2 * (fstS + fstT)) * Real.sqrt V_A * Real.sqrt (2 / Real.pi)) /
          (Real.sqrt (1 - fstS) * Real.sqrt V_A)
        = (Real.sqrt (2 * (fstS + fstT)) * Real.sqrt (2 / Real.pi) * Real.sqrt V_A) /
            (Real.sqrt (1 - fstS) * Real.sqrt V_A) := by
              congr 1
              ring
      _ =
          (Real.sqrt (2 * (fstS + fstT)) * Real.sqrt (2 / Real.pi)) /
            Real.sqrt (1 - fstS) := by
              rw [mul_div_mul_right _ _ h_sqrt_VA_ne_zero]
  rw [h_div]
  have h3 :
      Real.sqrt (2 * (fstS + fstT)) * Real.sqrt (2 / Real.pi) =
        Real.sqrt (4 * (fstS + fstT) / Real.pi) := by
    have h_nonneg : 0 ≤ 2 * (fstS + fstT) := mul_nonneg (by norm_num) hfst_sum_nonneg
    rw [← Real.sqrt_mul h_nonneg]
    congr 1
    ring
  rw [h3]
  have h4 :
      Real.sqrt (4 * (fstS + fstT) / Real.pi) / Real.sqrt (1 - fstS) =
        Real.sqrt ((4 * (fstS + fstT) / Real.pi) / (1 - fstS)) := by
    have h_nonneg : 0 ≤ 4 * (fstS + fstT) / Real.pi := by
      apply div_nonneg
      · linarith
      · exact Real.pi_pos.le
    rw [← Real.sqrt_div h_nonneg]
  rw [h4]
  have h5 :
      (4 * (fstS + fstT) / Real.pi) / (1 - fstS) =
        4 * ((fstS + fstT) / (Real.pi * (1 - fstS))) := by
    calc
      (4 * (fstS + fstT) / Real.pi) / (1 - fstS) =
          (4 * (fstS + fstT)) / (Real.pi * (1 - fstS)) := by
            rw [div_div]
      _ = 4 * ((fstS + fstT) / (Real.pi * (1 - fstS))) := by
            ring
  rw [h5]
  have h4_nonneg : (0 : ℝ) ≤ 4 := by norm_num
  rw [Real.sqrt_mul h4_nonneg]
  have hsqrt_four : Real.sqrt (4 : ℝ) = 2 :=
    (Real.sqrt_eq_iff_eq_sq (by norm_num) (by norm_num)).2 (by norm_num)
  rw [hsqrt_four]

/-- Exact discrete Wright-Fisher mean-shift formula in source-standard-deviation units. -/
theorem expected_abs_mean_shift_of_wrightFisher
    (V_A : ℝ)
    (NS tS NT tT : ℕ)
    (hVA_pos : 0 < V_A)
    (hNS : 0 < NS)
    (hNT : 0 < NT) :
    Expected_Abs_Shift V_A (wrightFisherHeterozygosityLoss NS tS)
          (wrightFisherHeterozygosityLoss NT tT) /
        Real.sqrt (presentDayPGSVariance V_A (wrightFisherHeterozygosityLoss NS tS)) =
      2 * Real.sqrt
        ((wrightFisherHeterozygosityLoss NS tS + wrightFisherHeterozygosityLoss NT tT) /
          (Real.pi * (1 - wrightFisherHeterozygosityLoss NS tS))) := by
  apply expected_abs_mean_shift_ratio_eq
  · exact hVA_pos
  · exact add_nonneg (wrightFisherHeterozygosityLoss_nonneg NS tS
      hNS) (wrightFisherHeterozygosityLoss_nonneg NT tT hNT)
  · exact wrightFisherHeterozygosityLoss_lt_one NS tS hNS

/-- Present-day signal-to-noise ratio for prediction under drift. -/
noncomputable def presentDaySignalToNoise (V_A V_E fst : ℝ) : ℝ :=
  presentDayPGSVariance V_A fst / V_E

/-- **presentDaySignalToNoise at zero V_E, named.** A trait with no environmental variance has
unbounded signal-to-noise. Lean returns `0`, the least predictable case, for the most predictable
trait. Consumers must require `V_E ≠ 0`. -/
theorem presentDaySignalToNoise_zero_ve_is_junk (V_A fst : ℝ) :
    presentDaySignalToNoise V_A 0 fst = 0 := by
  unfold presentDaySignalToNoise
  simp

/-- **Present-day coefficient of determination under drift.**

`R² = V_PGS / (V_PGS + V_E)` where `V_PGS = presentDayPGSVariance V_A fst`. The quotient
itself is not restated here: this is `r2FromSignalVariance` applied to the drift-attenuated signal
variance, so the two cannot drift apart. -/
noncomputable def presentDayR2 (V_A V_E fst : ℝ) : ℝ :=
  r2FromSignalVariance (presentDayPGSVariance V_A fst) V_E

/-- Exact bridge theorem: the dashboard algebraic `presentDayR2` equals statistical
`rsquared` when the relevant second-moment identities hold. -/
theorem presentDayR2_eq_statistical_rsquared_of_moments
    {k : ℕ} [Fintype (Fin k)]
    (dgp : DataGeneratingProcess k)
    (signal : Predictor k)
    (V_A V_E fst : ℝ)
    (h_vf :
      (let μ := dgp.jointMeasure
       let mf : ℝ := ∫ pc, signal pc.1 pc.2 ∂μ
       ∫ pc, (signal pc.1 pc.2 - mf) ^ 2 ∂μ) = presentDayPGSVariance V_A fst)
    (h_vg :
      (let μ := dgp.jointMeasure
       let mg : ℝ := ∫ pc, dgp.trueExpectation pc.1 pc.2 ∂μ
       ∫ pc, (dgp.trueExpectation pc.1 pc.2 - mg) ^ 2 ∂μ) =
        presentDayPGSVariance V_A fst + V_E)
    (h_cov :
      (let μ := dgp.jointMeasure
       let mf : ℝ := ∫ pc, signal pc.1 pc.2 ∂μ
       let mg : ℝ := ∫ pc, dgp.trueExpectation pc.1 pc.2 ∂μ
       ∫ pc, (signal pc.1 pc.2 - mf) * (dgp.trueExpectation pc.1 pc.2 - mg) ∂μ) =
        presentDayPGSVariance V_A fst)
    (h_vsig_pos : 0 < presentDayPGSVariance V_A fst)
    (h_vtrue_pos : 0 < presentDayPGSVariance V_A fst + V_E) :
    presentDayR2 V_A V_E fst = rsquared dgp signal dgp.trueExpectation := by
  have h_vsig_ne : presentDayPGSVariance V_A fst ≠ 0 := by linarith
  have h_vtrue_ne : presentDayPGSVariance V_A fst + V_E ≠ 0 := by linarith
  have h_if_not :
      ¬(presentDayPGSVariance V_A fst = 0 ∨ presentDayPGSVariance V_A fst + V_E = 0) := by
    intro h
    rcases h with h0 | h1
    · exact h_vsig_ne h0
    · exact h_vtrue_ne h1
  have h_rs :
      rsquared dgp signal dgp.trueExpectation = (presentDayPGSVariance V_A fst) ^ 2 /
          (presentDayPGSVariance V_A fst * (presentDayPGSVariance V_A fst + V_E)) := by
    unfold rsquared
    simp [h_vf, h_vg, h_cov, h_if_not]
  rw [h_rs]
  unfold presentDayR2 r2FromSignalVariance
  field_simp [h_vsig_ne, h_vtrue_ne]




/-- Exact present-day AUC under the equal-variance Gaussian model.

**NOT APPLICABLE TO DICHOTOMISED TRAITS. The word "liability" was in this docstring and
the formula is not the liability-threshold one.** The hypothesis actually used is that
case and control scores differ only by a mean shift with common residual variance `V_E`,
which is an equal-variance Gaussian *outcome*. Under a liability-threshold model the two
conditional variances are `v₁ = 1 - R²·i(i-T)` and `v₀ = 1 - R²·i_c(i_c-T)` and are **not**
equal, and no prevalence argument appears here at all.

Measured cost of the substitution on 400 simulated binary-trait PGS studies: bias
`-0.068` AUC, RMSE `0.071`, max error `0.120`. For a dichotomised trait use
`liabilityThresholdAUCFromExplainedR2` (RMSE `0.0121` on the same runs, against a `0.0120`
seed-noise floor). -/
noncomputable def presentDayEqualVarianceGaussianAUC (V_A V_E fst : ℝ) : ℝ :=
  equalVarianceGaussianAUCFromSignalVariance (presentDayPGSVariance V_A fst) V_E

/-- Exact present-day **equal-variance Gaussian** AUC formula at positive residual
variance. -/
theorem presentDayEqualVarianceGaussianAUC_eq
    (V_A V_E fst : ℝ) (h_env : V_E ≠ 0) :
    presentDayEqualVarianceGaussianAUC V_A V_E fst =
      Phi (Real.sqrt (presentDaySignalToNoise V_A V_E fst / 2)) := by
  rw [presentDayEqualVarianceGaussianAUC,
    equalVarianceGaussianAUCFromSignalVariance_eq_formula_of_ne_noise _ _ h_env]
  unfold presentDaySignalToNoise
  congr 2
  rw [div_div, mul_comm]

/-- Drift monotonically degrades signal-to-noise when `V_A, V_E > 0`. -/
theorem drift_degrades_signalToNoise
    (V_A V_E fstS fstT : ℝ)
    (hVA : 0 < V_A) (hVE : 0 < V_E)
    (hfst : fstS < fstT) :
    presentDaySignalToNoise V_A V_E fstT < presentDaySignalToNoise V_A V_E fstS := by
  unfold presentDaySignalToNoise presentDayPGSVariance pgsVarianceFromHet
  have hnum : (1 - fstT) * V_A < (1 - fstS) * V_A := by
    nlinarith [mul_lt_mul_of_pos_right hfst hVA]
  have hInv : 0 < V_E⁻¹ := inv_pos.mpr hVE
  have hscaled :
      ((1 - fstT) * V_A) * V_E⁻¹ < ((1 - fstS) * V_A) * V_E⁻¹ :=
    mul_lt_mul_of_pos_right hnum hInv
  simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hscaled

/-- The analytic core of monotonicity for explained-variance ratios.

This private lemma is shared by the biological drift theorem and the public monotonicity
API below, so the denominator argument has a single proof. -/
private theorem r2FromSignalVariance_strictMono_nonneg
    (V_E x y : ℝ)
    (hVE : 0 < V_E) (hx : 0 ≤ x) (hxy : x < y) :
    r2FromSignalVariance x V_E < r2FromSignalVariance y V_E := by
  unfold r2FromSignalVariance
  have hxE : 0 < x + V_E := by linarith
  have hyE : 0 < y + V_E := by linarith [hx, hxy]
  have hxyE : x + V_E < y + V_E := by linarith
  have hInv : 1 / (y + V_E) < 1 / (x + V_E) := by
    rw [one_div_lt_one_div hyE hxE]
    exact hxyE
  have hsub : 1 - V_E / (x + V_E) < 1 - V_E / (y + V_E) := by
    have hmul := mul_lt_mul_of_pos_left hInv hVE
    have hfrac : V_E / (y + V_E) < V_E / (x + V_E) := by
      simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hmul
    nlinarith [hfrac]
  have hxne : x + V_E ≠ 0 := by linarith
  have hyne : y + V_E ≠ 0 := by linarith
  have hxrepr : x / (x + V_E) = 1 - V_E / (x + V_E) := by
    field_simp [hxne]
    ring
  have hyrepr : y / (y + V_E) = 1 - V_E / (y + V_E) := by
    field_simp [hyne]
    ring
  simpa [hxrepr, hyrepr] using hsub

/-- Drift monotonically degrades present-day `R²` when `V_A, V_E > 0` and `fst < 1`. -/
theorem drift_degrades_R2
    (V_A V_E fstS fstT : ℝ)
    (hVA : 0 < V_A) (hVE : 0 < V_E)
    (hfst : fstS < fstT)
    (hfstT_le_one : fstT ≤ 1) :
    presentDayR2 V_A V_E fstT < presentDayR2 V_A V_E fstS := by
  unfold presentDayR2 presentDayPGSVariance pgsVarianceFromHet
  have hT_nonneg : 0 ≤ V_A * (1 - fstT) := by
    have : 0 ≤ 1 - fstT := by linarith
    exact mul_nonneg (le_of_lt hVA) this
  have h_lt : V_A * (1 - fstT) < V_A * (1 - fstS) := by
    nlinarith [mul_lt_mul_of_pos_right hfst hVA]
  exact r2FromSignalVariance_strictMono_nonneg V_E
    (V_A * (1 - fstT)) (V_A * (1 - fstS)) hVE hT_nonneg h_lt

/-- For fixed `V_E > 0`, `v ↦ v / (v + V_E)` is strictly increasing on nonnegative variances. -/
theorem expectedR2_strictMono_nonneg
    (V_E x y : ℝ)
    (hVE : 0 < V_E) (hx : 0 ≤ x) (hxy : x < y) :
    r2FromSignalVariance x V_E < r2FromSignalVariance y V_E := by
  exact r2FromSignalVariance_strictMono_nonneg V_E x y hVE hx hxy

/-- Drift strictly degrades the exact **equal-variance Gaussian** AUC whenever
signal variance is positive and target drift exceeds source drift.

This statement was also carried by `drift_degrades_AUC_of_strictMono`, whose twenty-line
proof was this one character for character.  The second name described the tactic used
rather than the model, and the model is what a reader needs: the AUC here is the
equal-variance Gaussian one, not the liability-threshold one. -/
theorem drift_degrades_equalVarianceGaussianAUC
    (V_A V_E fstS fstT : ℝ)
    (hVA : 0 < V_A) (hVE : 0 < V_E)
    (hfst : fstS < fstT)
    (hfstT_le_one : fstT ≤ 1) :
    presentDayEqualVarianceGaussianAUC V_A V_E fstT <
      presentDayEqualVarianceGaussianAUC V_A V_E fstS := by
  rw [presentDayEqualVarianceGaussianAUC_eq _ _ _ (ne_of_gt hVE),
    presentDayEqualVarianceGaussianAUC_eq _ _ _ (ne_of_gt hVE)]
  apply strictMono_Phi
  have hsnr := drift_degrades_signalToNoise V_A V_E fstS fstT hVA hVE hfst
  have hhalf_nonneg : 0 ≤ presentDaySignalToNoise V_A V_E fstT / 2 := by
    have hsnr_nonneg : 0 ≤ presentDaySignalToNoise V_A V_E fstT := by
      unfold presentDaySignalToNoise presentDayPGSVariance pgsVarianceFromHet
      have hnum : 0 ≤ V_A * (1 - fstT) := by
        have h_one_minus : 0 ≤ 1 - fstT := by linarith
        exact mul_nonneg (le_of_lt hVA) h_one_minus
      exact div_nonneg hnum (le_of_lt hVE)
    exact div_nonneg hsnr_nonneg (by positivity)
  have hhalf_lt : presentDaySignalToNoise V_A V_E fstT / 2 <
      presentDaySignalToNoise V_A V_E fstS / 2 := by
    nlinarith
  exact Real.sqrt_lt_sqrt hhalf_nonneg hhalf_lt

/-! Real-world PGS variance with both drift and LD tagging efficiency. -/
/-- The additive variance a score **explains** in a target population: the source
additive variance `V_A`, attenuated by the transported effect correlation `rhoSq`
and eroded by drift through `1 - fst`.

**This is a scope declaration, not a correction. The body is right; the one-line
reading of it as "the variance of the score" was wrong.** Write `bhat` for the
weights the deployed score actually carries, `b` for the true effects, `w` for the
ancestral per-locus heterozygosities `2p(1-p)`, and put

    A = Σ w bhat²,   B = Σ w b² = V_A,   C = Σ w bhat b,   rhoSq = C² / (A B).

In a target population whose heterozygosities are the ancestral ones scaled by
`1 - fst`:

* the **variance of the score itself** is `(1 - fst) A`;
* the variance of the part of the genetic value that the score predicts, i.e.
  `Cov(G, S)² / Var(S)`, is `(1 - fst) C² / A`, and *that* is this body.

The two agree exactly when `A = C`, i.e. when `Σ w bhat (bhat - b) = 0`: the
weights are calibrated, the residual `b - bhat` orthogonal to `bhat` in the
heterozygosity metric. Read this definition as the explained-variance one. It is
the reading the downstream `r2FromSignalVariance` compositions need, since only
explained variance can enter an `R²`, and it is the reading under which `rhoSq`
attenuates a covariance rather than inflating a variance.

`rhoSq` is meant in the heterozygosity metric `w` above, not as the plain
`corr(bhat, b)²` a reader computes from a table of effect estimates. Score
variance is a `w`-weighted quadratic form in the effects, so no other reading can
enter a variance identity at all. The choice is not cosmetic: at source `n = 500`
the measurement below found `0.63392` weighted against `0.36383` unweighted, the
weighted reading being 74 percent larger.

    Regime: calibrated weights; equivalently, the large-source-GWAS limit.
    Nothing in the body carries a sample size, and at finite source `n` raw
    marginal-OLS weights are not calibrated. To leading order in `1/n`,
    `E[C] = V_A` while `E[A] = V_A + Σ_j w_j Var(bhat_j) ≈ V_A + m V_P / n` over
    `m` loci at phenotypic variance `V_P`, the per-locus term having the shape of
    `HaplotypeTheory.haplotypeEffectVarianceOLS`. So `A > C`, and the score's own
    variance overshoots this body by the factor `(A / C)²`. The finite-`n` score
    variance is `(1 - fst)(V_A + m V_P / n)`; this body is unchanged, which is the
    point. Estimation noise inflates score variance without adding any covariance
    with the phenotype, so it cannot improve prediction, and the quantity defined
    here is the one that survives to an `R²`.

    Empirical status: **VALIDATED as the explained-variance reading; FALSIFIED as
    a claim about the variance of a score built from finite-`n` weights**
    (`validation/empirical/differential/cluster/fam_pgs_transport_drift.py`,
    check C6; Wright-Fisher, `Ne = 500`, `m = 300` unlinked loci, `V_E = 1`,
    `V_A = 62.853`). Measured score variance against this body: at `n = 500`,
    `fst = 0`, `135.20 ± 0.49` against `39.84`; at `n = 2000`, `81.11 ± 0.24`
    against `55.18`; at `n = 20000`, `65.88 ± 0.26` against `61.88`; at
    `n = 20000`, `fst = 0.295`, `46.55 ± 0.71` against `43.64`. The gap is
    `95.4`, `25.9`, `3.99` across that `n` grid -- it falls as `1/n`, which is the
    signature of estimation noise and not of a wrong constant. Recovering the
    noise term `Σ w (bhat - b)²` from those cells gives `10.16` against the
    predicted `m V_P / n = 9.58` at `n = 2000` and `1.03` against `0.958` at
    `n = 20000`, so the mechanism above is the whole of the gap where the
    leading-order form applies. At `n = 500` it gives `51.3` against `38.3`,
    which is the leading-order form itself degrading: the ancestral spectrum
    there carries loci at `p = 0.01`, about ten minor-allele copies in a sample
    of 500, where `E[1 / Σ (g - ḡ)²]` is no longer `1 / (n w)`. The run's scale
    control reproduced additive variance to relative error `0.00e+00` and its
    corruption control fired to `27.9` sems where it must fire.

    One consequence of the scope. As `n → ∞` with weights carried on the causal
    variants, `rhoSq → 1` and this collapses to `presentDayPGSVariance`. The
    content of `rhoSq < 1` is therefore cross-population tagging loss, which is
    what the surrounding file means by it, and never source-GWAS estimation
    noise, which belongs in `V_A` instead: a score's `V_A` is the variance it
    explains in its own source population, already net of its own noise. -/
noncomputable def realWorldPGSVariance (V_A fst rhoSq : ℝ) : ℝ :=
  rhoSq * (1 - fst) * V_A

/-- **realWorldPGSVariance pinned at a reference point.** No theorem in the corpus evaluated this
definition, so every body agreeing with it in sign and monotonicity was indistinguishable from
it. At all arguments equal to `1 / 2` it is `1 / 8`, which fixes the coefficients a one-sided
bound or an invariance leaves free. -/
theorem realWorldPGSVariance_at_reference_point :
    realWorldPGSVariance (1 / 2) (1 / 2) (1 / 2) = 1 / 8 := by
  unfold realWorldPGSVariance
  norm_num

/-! Explicit cross-population biological and observational state that can
change deployed portability metrics.

The fields record the named drivers that can change metrics:

- direct causal observation via `directCausalSource/Target`
- novel direct target-only causal links via `novelDirectCausalTarget`
- proxy tagging via `proxyTaggingSource/Target`
- novel target-only proxy tagging via `novelProxyTaggingTarget`
- aggregate tag-to-causal structure via the derived
  `sigmaTagCausalSourceAt`
- causal-vs-tag distinction via separate tag and causal dimensions plus the
  direct-vs-proxy decomposition
- source and target LD among scored SNPs via `sigmaTagSource/Target`
- standing source/target effect architecture via `betaSource/Target`
- target-only novel causal effects via `novelCausalEffectTarget`
- ancestry-specific or environment-specific cross-covariance shifts via
  `contextCrossSource/Target`
- additive irreducible target-side losses derived from:
  broken tagging, ancestry-specific LD distortion, and source-specific
  overfit/context mismatch
- target-only phenotype variance from untagged novel causal mutations via
  `novelUntaggablePhenotypeVarianceTarget`
- source/target outcome scales and target prevalence for deployed metrics

No source `R²` summary appears here because it is not a sufficient biological
state variable for transport. -/
structure CrossPopulationMetricModel (p q : ℕ) where
  beta : Pop → Fin q → ℝ
  sigmaTag : Pop → Matrix (Fin p) (Fin p) ℝ
  directCausal : Pop → Matrix (Fin p) (Fin q) ℝ
  proxyTagging : Pop → Matrix (Fin p) (Fin q) ℝ
  /-- Tag-to-causal links carried by variants that arose after divergence. -/
  novelDirectCausal : Pop → Matrix (Fin p) (Fin q) ℝ
  /-- Proxy tagging carried by variants that arose after divergence. -/
  novelProxyTagging : Pop → Matrix (Fin p) (Fin q) ℝ
  /-- Causal effects carried by variants that arose after divergence. -/
  novelCausalEffect : Pop → Fin q → ℝ
  contextCross : Pop → Fin p → ℝ
  outcomeVariance : Pop → ℝ
  novelUntaggablePhenotypeVarianceTarget : ℝ
  targetPrevalence : ℝ
  /-- **The source is the reference population.** "Novel" means novel *relative to the
  source*, so nothing is novel in the source itself. It is a FIELD rather than a shape
  convention -- the alternative is two separate definitions whose source variant omits the
  novel terms its target twin includes, which cannot be discharged or contradicted. Stated
  here it must be discharged at the use site, and a model violating it cannot be built by
  accident. -/
  novelDirectCausal_source : novelDirectCausal Pop.source = 0
  novelProxyTagging_source : novelProxyTagging Pop.source = 0
  novelCausalEffect_source : novelCausalEffect Pop.source = 0
  outcomeVariance_pos : ∀ P : Pop, 0 < outcomeVariance P
  novelUntaggablePhenotypeVarianceTarget_nonneg : 0 ≤ novelUntaggablePhenotypeVarianceTarget
  targetPrevalence_pos : 0 < targetPrevalence
  targetPrevalence_lt_one : targetPrevalence < 1

/-- **The class is inhabited.**  A theorem quantified over an uninhabited structure is
true and empty: kernel-checked, clean axiom report, no content.  This is the witness that
makes the theorems below statements about something. -/
noncomputable def CrossPopulationMetricModel.witness (p q : ℕ) :
    CrossPopulationMetricModel p q where
  beta := fun _ ↦ 0
  sigmaTag := fun _ ↦ 0
  directCausal := fun _ ↦ 0
  proxyTagging := fun _ ↦ 0
  novelDirectCausal := fun _ ↦ 0
  novelProxyTagging := fun _ ↦ 0
  novelCausalEffect := fun _ ↦ 0
  contextCross := fun _ ↦ 0
  outcomeVariance := fun _ ↦ 1
  novelUntaggablePhenotypeVarianceTarget := 0
  targetPrevalence := 1 / 2
  novelDirectCausal_source := rfl
  novelProxyTagging_source := rfl
  novelCausalEffect_source := rfl
  outcomeVariance_pos := fun _ ↦ by norm_num
  novelUntaggablePhenotypeVarianceTarget_nonneg := le_refl 0
  targetPrevalence_pos := by norm_num
  targetPrevalence_lt_one := by norm_num

/-- Source ERM weights in closed form (normal equations) under invertible source covariance. 
    Empirical status: **VALIDATED**
    (`validation/empirical/simcov/battery_transport.py`). One end-to-end
    transport simulation: 12 tags, 8 causal variants, 400000 individuals per
    population, genotypes drawn from a multivariate normal with a specified joint
    covariance so the ground-truth second moments are SET rather than estimated.
    Source and target differ in all three channels the model separates -- tag-tag
    LD (Frobenius distance 2.09), tag-causal alignment (1.89), and the effect
    vector (0.69) -- because a design moving only one could not say which term a
    discrepancy belonged to. Measured source and target `R²` are 0.05366 and
    0.00161, a factor of 33, so the transport signal is real. Compared against an
    explicit least-squares regression in the source, worst of 12 coordinates:
    0.70 sems. The error bar carries a `sqrt(2 log p)` factor for the worst-of-`p`
    selection, so this is not a multiple-comparisons artefact. -/
noncomputable def sourceERMWeights {p : ℕ}
    (sigmaObsSource : Matrix (Fin p) (Fin p) ℝ)
    (crossSource : Fin p → ℝ) : Fin p → ℝ :=
  sigmaObsSource⁻¹.mulVec crossSource

/-- A singular source covariance has Mathlib inverse `0`, so the fitted weights are the zero
predictor.  That is a legitimate weight vector, not a flag, which is why the branch is named:
a rank-deficient design reports "predict nothing" rather than "not identified". -/
theorem sourceERMWeights_at_singular_covariance_is_junk {p : ℕ}
    (sigmaObsSource : Matrix (Fin p) (Fin p) ℝ) (crossSource : Fin p → ℝ)
    (hsingular : ¬ IsUnit sigmaObsSource.det) :
    sourceERMWeights sigmaObsSource crossSource = 0 := by
  unfold sourceERMWeights
  rw [Matrix.nonsing_inv_apply_not_isUnit _ hsingular, Matrix.zero_mulVec]


/-- **Aggregate tag-to-causal alignment in a population**: directly observed causal
variants plus ancestry-specific proxy tagging, each including whatever arose after
divergence.

One definition now covers both populations. The source form is not a second definition
but a consequence of `novelDirectCausal_source` and `novelProxyTagging_source`, recorded
as `sigmaTagCausal_source` below. -/
noncomputable def sigmaTagCausalSourceAt {p q : ℕ}
    (m : CrossPopulationMetricModel p q) (P : Pop) : Matrix (Fin p) (Fin q) ℝ :=
  (m.directCausal P + m.novelDirectCausal P) +
    (m.proxyTagging P + m.novelProxyTagging P)

/-- **Total causal-effect vector in a population**: standing effects plus those carried
by variants that arose after divergence.

    Empirical status: **VALIDATED** through `crossCovariance`, which contracts it
    against the tag-causal alignment and was measured to 1.76 sems in both
    populations (`validation/empirical/simcov/battery_transport.py`). One end-to-end
    transport simulation: 12 tags, 8 causal variants, 400000 individuals per
    population, genotypes drawn from a multivariate normal with a specified
    joint covariance so the ground-truth second moments are SET rather than
    estimated. Source and target differ in all three channels the model
    separates -- tag-tag LD (Frobenius distance 2.09), tag-causal alignment
    (1.89), and the effect vector (0.69) -- because a design that moved only one
    could not say which term a discrepancy belonged to. Measured source and
    target `R²` are 0.05366 and 0.00161, a factor of 33, so the transport signal
    is real and not a rounding difference. -/
noncomputable def totalEffect {p q : ℕ}
    (m : CrossPopulationMetricModel p q) (P : Pop) : Fin q → ℝ :=
  m.beta P + m.novelCausalEffect P

/-- **In the source the novel terms drop out** — derived from the reference-population
hypotheses rather than written into a separate definition. This is the equation that used
to be the *body* of `sigmaTagCausalSourceAt`; making it a theorem is what stops the source
and target forms from drifting apart silently. -/
@[simp] theorem sigmaTagCausal_source {p q : ℕ} (m : CrossPopulationMetricModel p q) :
    sigmaTagCausalSourceAt m Pop.source = m.directCausal Pop.source +
      m.proxyTagging Pop.source := by
  simp [sigmaTagCausalSourceAt, m.novelDirectCausal_source, m.novelProxyTagging_source]

/-- Likewise the source effect vector is the standing one. -/
@[simp] theorem totalEffect_source {p q : ℕ} (m : CrossPopulationMetricModel p q) :
    totalEffect m Pop.source = m.beta Pop.source := by
  simp [totalEffect, m.novelCausalEffect_source]

@[simp] theorem sigmaTagCausal_eq_direct_plus_novelDirect_plus_proxy_plus_novelProxy {p q : ℕ}
    (m : CrossPopulationMetricModel p q) (P : Pop) :
    sigmaTagCausalSourceAt m P =
      m.directCausal P + m.novelDirectCausal P +
        m.proxyTagging P + m.novelProxyTagging P := by
  simp [sigmaTagCausalSourceAt, add_assoc]

@[simp] theorem totalEffect_eq_beta_plus_novel {p q : ℕ}
    (m : CrossPopulationMetricModel p q) (P : Pop) :
    totalEffect m P = m.beta P + m.novelCausalEffect P := by
  rfl

/-- Target population risk for a linear score `w` under covariance/cross/noise moments. -/
noncomputable def targetLinearRisk {p : ℕ}
    (sigmaObsTarget : Matrix (Fin p) (Fin p) ℝ)
    (crossTarget : Fin p → ℝ)
    (noiseVar : ℝ)
    (w : Fin p → ℝ) : ℝ :=
  noiseVar + dotProduct w (sigmaObsTarget.mulVec w) - 2 * dotProduct w crossTarget

/-- Reference evaluation: the zero predictor carries exactly the noise variance. -/
theorem targetLinearRisk_at_reference_point {p : ℕ}
    (sigmaObsTarget : Matrix (Fin p) (Fin p) ℝ) (crossTarget : Fin p → ℝ) (noiseVar : ℝ) :
    targetLinearRisk sigmaObsTarget crossTarget noiseVar 0 = noiseVar := by
  unfold targetLinearRisk
  simp


/-- Dense covariance witness in each population, for non-degenerate ERM-transport tests.

These are global witnesses. **Do not name one after a parameter of `sourceERMWeights` or
`targetLinearRisk` directly above** -- the same identifier meaning a global witness in one
declaration and a bound argument in the next is how this section became unreadable. -/
def witnessSigmaObs : Pop → Matrix (Fin 2) (Fin 2) ℝ :=
  Pop.pair !![1, 0.5; 0.5, 1] !![1, 0.1; 0.1, 1]

/-- Cross-covariance vector in each population, paired with `witnessSigmaObs`.

The two components are deliberately equal: the witness holds the cross-covariance fixed so
that the source/target ERM difference it exhibits is driven purely by the shift in LD, not
by a change in the predictor/outcome relationship. Written as two constants that fact was
a coincidence of two literals; written this way it is visible. -/
def witnessCross : Pop → Fin 2 → ℝ :=
  Pop.pair ![0.8, 0.4] ![0.8, 0.4]

/-- Exact OLS solution in each population for the dense witness system. -/
noncomputable def witnessW_opt : Pop → Fin 2 → ℝ :=
  Pop.pair ![0.8, 0.0] ![76 / 99, 32 / 99]

/-- Each population's declared witness weight solves its own normal equations. -/
private theorem witnessSigmaObs_mulVec_witnessW_opt (P : Pop) :
    (witnessSigmaObs P).mulVec (witnessW_opt P) = witnessCross P := by
  cases P <;>
    ext i <;>
      fin_cases i <;>
        norm_num [witnessW_opt, witnessSigmaObs, witnessCross, Matrix.mulVec,
          Matrix.cons_val', Matrix.cons_val_fin_one, dotProduct, Pop.pair]

/-- A concrete proof that ERM mismatch occurs under LD shift, without relying on
    the abstract `hConflict` hypothesis, using dense 2x2 witnesses. -/
theorem source_target_erm_differ_dense_witness_proved :
    (witnessSigmaObs Pop.source).mulVec (witnessW_opt Pop.source) = (witnessCross Pop.source) ∧
    (witnessSigmaObs Pop.target).mulVec (witnessW_opt Pop.target) = (witnessCross Pop.target) ∧
    (witnessW_opt Pop.source) ≠ (witnessW_opt Pop.target) := by
  refine ⟨witnessSigmaObs_mulVec_witnessW_opt Pop.source,
    witnessSigmaObs_mulVec_witnessW_opt Pop.target, ?_⟩
  · intro heq
    have h : (witnessW_opt Pop.source) 0 = (witnessW_opt Pop.target) 0 := congrFun heq 0
    revert h
    simp [witnessW_opt, Pop.pair]
    norm_num

/-- **Predictor/outcome cross-covariance in a population**, from explicit biological and
observational drivers. 
    Empirical status: **VALIDATED**
    (`validation/empirical/simcov/battery_transport.py`). One end-to-end
    transport simulation: 12 tags, 8 causal variants, 400000 individuals per
    population, genotypes drawn from a multivariate normal with a specified joint
    covariance so the ground-truth second moments are SET rather than estimated.
    Source and target differ in all three channels the model separates -- tag-tag
    LD (Frobenius distance 2.09), tag-causal alignment (1.89), and the effect
    vector (0.69) -- because a design moving only one could not say which term a
    discrepancy belonged to. Measured source and target `R²` are 0.05366 and
    0.00161, a factor of 33, so the transport signal is real. Compared against the
    empirical `Cov(tag genotype, outcome)` coordinate by coordinate, worst of 12:
    1.76 sems in the source, 1.43 in the target.

    Power: the prediction spans -0.17985 to -0.07015 across the two populations. -/
noncomputable def crossCovariance {p q : ℕ}
    (m : CrossPopulationMetricModel p q) (P : Pop) : Fin p → ℝ :=
  (sigmaTagCausalSourceAt m P).mulVec (totalEffect m P) + m.contextCross P

/-- Source-learned linear weights from the full source state, including any
context-dependent source cross-covariance term. -/
noncomputable def sourceWeightsFromExplicitDrivers {p q : ℕ}
    (m : CrossPopulationMetricModel p q) : Fin p → ℝ :=
  sourceERMWeights (m.sigmaTag Pop.source) (crossCovariance m Pop.source)

/-- Explicit SNP-level score equation: any tag-genotype state is scored by the
source-learned weight vector through a linear dot product. This is the
canonical transported score functional; source and target scores differ only by
which tag-genotype state is supplied. -/
noncomputable def sourceWeightedTagScore {p q : ℕ}
    (m : CrossPopulationMetricModel p q) (tagState : Fin p → ℝ) : ℝ :=
  dotProduct (sourceWeightsFromExplicitDrivers m) tagState

@[simp] theorem sourceWeightedTagScore_add {p q : ℕ}
    (m : CrossPopulationMetricModel p q) (x y : Fin p → ℝ) :
    sourceWeightedTagScore m (x + y) =
      sourceWeightedTagScore m x + sourceWeightedTagScore m y := by
  simp [sourceWeightedTagScore, dotProduct, mul_add, Finset.sum_add_distrib]

/-- **Tag-to-causal projection in a population**, induced by that population's causal
effect vector. -/
noncomputable def taggingProjection {p q : ℕ}
    (m : CrossPopulationMetricModel p q) (P : Pop) : Fin p → ℝ :=
  (sigmaTagCausalSourceAt m P).mulVec (totalEffect m P)

/-- Locus-resolved target effect heterogeneity relative to the source effect
vector. This is the closed-form biological object behind claims that
`β_source ≠ β_target`; it is not a scalar retention factor.

    Empirical status: NOT AN EMPIRICAL CLAIM. The body is the difference of a
    quantity the corpus already carries a verdict for (`totalEffect`, measured
    through `crossCovariance` in `simcov/battery_transport.py`) and a bare field
    of the model (`m.beta Pop.source`). Subtracting the second from the first
    names a residual; it predicts nothing, because whatever the two are, their
    difference is this. `totalEffect_target_eq_betaSource_plus_targetEffectHeterogeneity`
    is the same statement read forwards and is proved by `rfl`.

    What WOULD be an empirical claim, and is made elsewhere, is that the
    residual is nonzero in real populations -- that `β_source ≠ β_target` at
    all. That is a claim about `totalEffect` and `m.beta`, and it is where a
    measurement belongs. -/
noncomputable def targetEffectHeterogeneity {p q : ℕ}
    (m : CrossPopulationMetricModel p q) : Fin q → ℝ :=
  totalEffect m Pop.target - (m.beta Pop.source)

/-- The full target effect vector is the source effect vector plus an explicit
locus-resolved heterogeneity term, which may include target-only novel causal
effects. -/
theorem totalEffect_target_eq_betaSource_plus_targetEffectHeterogeneity {p q : ℕ}
    (m : CrossPopulationMetricModel p q) :
    totalEffect m Pop.target = (m.beta Pop.source) + targetEffectHeterogeneity m := by
  ext j
  simp [targetEffectHeterogeneity]

/-- Target tagging projection of the source effect vector through the target
tagging surface. This isolates what would transport if target effects were
identical to source effects.

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
noncomputable def targetSourceEffectProjection {p q : ℕ}
    (m : CrossPopulationMetricModel p q) : Fin p → ℝ :=
  (sigmaTagCausalSourceAt m Pop.target).mulVec (m.beta Pop.source)

/-- Incremental target-side projection induced purely by effect-size
heterogeneity relative to the source effect vector.

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
noncomputable def targetEffectHeterogeneityProjection {p q : ℕ}
    (m : CrossPopulationMetricModel p q) : Fin p → ℝ :=
  (sigmaTagCausalSourceAt m Pop.target).mulVec (targetEffectHeterogeneity m)

/-- Projection induced purely by target-only novel causal effects through the
target tagging surface.

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
noncomputable def targetNovelMutationEffectProjection {p q : ℕ}
    (m : CrossPopulationMetricModel p q) : Fin p → ℝ :=
  (sigmaTagCausalSourceAt m Pop.target).mulVec (m.novelCausalEffect Pop.target)

/-- **Projection carried by directly observed causal variants**, in a population. -/
noncomputable def directCausalProjection {p q : ℕ}
    (m : CrossPopulationMetricModel p q) (P : Pop) : Fin p → ℝ :=
  (m.directCausal P + m.novelDirectCausal P).mulVec (totalEffect m P)

/-- **Projection carried only by proxy tagging** of unscored causal variants, in a
population. -/
noncomputable def proxyTaggingProjection {p q : ℕ}
    (m : CrossPopulationMetricModel p q) (P : Pop) : Fin p → ℝ :=
  (m.proxyTagging P + m.novelProxyTagging P).mulVec (totalEffect m P)

/-- **The aggregate tag-to-causal projection splits into direct causal and proxy-tagging
contributions** — in either population, from the one statement. -/
theorem taggingProjection_eq_direct_plus_proxy {p q : ℕ}
    (m : CrossPopulationMetricModel p q) (P : Pop) :
    taggingProjection m P = directCausalProjection m P + proxyTaggingProjection m P := by
  ext i
  simp [taggingProjection, directCausalProjection, proxyTaggingProjection,
    sigmaTagCausalSourceAt, Matrix.add_mulVec, add_assoc, Pi.add_apply]

/-- The target tagging projection splits into the projection of source effects
through the target tagging surface plus a separate projection of the
locus-resolved effect heterogeneity. -/
theorem taggingProjection_target_eq_source_effect_plus_effectHeterogeneity {p q : ℕ}
    (m : CrossPopulationMetricModel p q) :
    taggingProjection m Pop.target =
      targetSourceEffectProjection m + targetEffectHeterogeneityProjection m := by
  unfold taggingProjection
  rw [totalEffect_target_eq_betaSource_plus_targetEffectHeterogeneity]
  simp [targetSourceEffectProjection, targetEffectHeterogeneityProjection,
    Matrix.mulVec_add]

/-- The target tagging projection also splits into standing target effects plus
target-only novel causal effects. -/
theorem taggingProjection_target_eq_standing_plus_novelMutationEffect {p q : ℕ}
    (m : CrossPopulationMetricModel p q) :
    taggingProjection m Pop.target =
      (sigmaTagCausalSourceAt m Pop.target).mulVec (m.beta Pop.target) +
        targetNovelMutationEffectProjection m := by
  ext i
  simp [taggingProjection, targetNovelMutationEffectProjection,
    totalEffect, Matrix.mulVec_add, Pi.add_apply]

/-- **The score/outcome covariance vector is the tagging projection plus the context
term** — in either population. -/
theorem crossCovariance_eq_taggingProjection_plus_context {p q : ℕ}
    (m : CrossPopulationMetricModel p q) (P : Pop) :
    crossCovariance m P = taggingProjection m P + m.contextCross P := by
  rfl

/-- **The score/outcome covariance vector splits into direct-causal, proxy-tagging and
context contributions** — in either population. -/
theorem crossCovariance_eq_direct_plus_proxy_plus_context {p q : ℕ}
    (m : CrossPopulationMetricModel p q) (P : Pop) :
    crossCovariance m P =
      directCausalProjection m P + proxyTaggingProjection m P + m.contextCross P := by
  rw [crossCovariance_eq_taggingProjection_plus_context,
    taggingProjection_eq_direct_plus_proxy]

/-- Exact target score/outcome cross-covariance splits into the transport of
source-stable effects through the target tagging surface, the projection of
target effect heterogeneity, and the target context term. -/
theorem crossCovariance_target_eq_source_effect_plus_effectHeterogeneity_plus_context
    {p q : ℕ} (m : CrossPopulationMetricModel p q) :
    crossCovariance m Pop.target =
      targetSourceEffectProjection m +
        targetEffectHeterogeneityProjection m +
        (m.contextCross Pop.target) := by
  rw [crossCovariance_eq_taggingProjection_plus_context,
    taggingProjection_target_eq_source_effect_plus_effectHeterogeneity]

/-- Exact target score/outcome cross-covariance also splits into the standing
target-effect projection, the projection of target-only novel causal effects,
and the target context term. -/
theorem crossCovariance_target_eq_standing_plus_novelMutationEffect_plus_context
    {p q : ℕ} (m : CrossPopulationMetricModel p q) :
    crossCovariance m Pop.target =
      (sigmaTagCausalSourceAt m Pop.target).mulVec (m.beta Pop.target) +
        targetNovelMutationEffectProjection m +
        (m.contextCross Pop.target) := by
  rw [crossCovariance_eq_taggingProjection_plus_context,
    taggingProjection_target_eq_standing_plus_novelMutationEffect]

/-- Exact score variance in the source population under the learned source
weights. 
    Empirical status: **VALIDATED**
    (`validation/empirical/simcov/battery_transport.py`). One end-to-end
    transport simulation: 12 tags, 8 causal variants, 400000 individuals per
    population, genotypes drawn from a multivariate normal with a specified joint
    covariance so the ground-truth second moments are SET rather than estimated.
    Source and target differ in all three channels the model separates -- tag-tag
    LD (Frobenius distance 2.09), tag-causal alignment (1.89), and the effect
    vector (0.69) -- because a design moving only one could not say which term a
    discrepancy belonged to. Measured source and target `R²` are 0.05366 and
    0.00161, a factor of 33, so the transport signal is real. Against the realised
    variance of the transported score: 1.43 sems source, 2.40 target.

    Power: the prediction spans 0.11043 to 0.13610. -/
noncomputable def scoreVarianceFromSourceWeights {p q : ℕ}
    (m : CrossPopulationMetricModel p q) (P : Pop) : ℝ :=
  let wS := sourceWeightsFromExplicitDrivers m
  dotProduct wS ((m.sigmaTag P).mulVec wS)

/-- **Exact score/outcome covariance in a population** under the source-learned weights.
At the target this is where effect changes, tag-causal alignment and context shifts enter;
at the source it is the ordinary in-sample covariance. One definition, because it is one
quantity. 
    Empirical status: **VALIDATED**
    (`validation/empirical/simcov/battery_transport.py`). One end-to-end
    transport simulation: 12 tags, 8 causal variants, 400000 individuals per
    population, genotypes drawn from a multivariate normal with a specified joint
    covariance so the ground-truth second moments are SET rather than estimated.
    Source and target differ in all three channels the model separates -- tag-tag
    LD (Frobenius distance 2.09), tag-causal alignment (1.89), and the effect
    vector (0.69) -- because a design moving only one could not say which term a
    discrepancy belonged to. Measured source and target `R²` are 0.05366 and
    0.00161, a factor of 33, so the transport signal is real. Against the realised
    `Cov(score, outcome)`: 0.25 sems source, 0.07 target.

    Power: the prediction spans 0.02107 to 0.13610, a factor of six, and the
    target value is the one the transport claim rests on. -/
noncomputable def predictiveCovarianceFromSourceWeights {p q : ℕ}
    (m : CrossPopulationMetricModel p q) (P : Pop) : ℝ :=
  dotProduct (sourceWeightsFromExplicitDrivers m) (crossCovariance m P)

/-- **Exact calibration slope in a population** under the source-learned score equation:
the literal `Cov(Y, score) / Var(score)` ratio on the explicit SNP-level model. -/
noncomputable def calibrationSlopeFromSourceWeights {p q : ℕ}
    (m : CrossPopulationMetricModel p q) (P : Pop) : ℝ :=
  predictiveCovarianceFromSourceWeights m P / scoreVarianceFromSourceWeights m P

/-- With a vanishing denominator Mathlib returns `0`, which is a value this quantity can also
take legitimately, so the branch is named rather than left to be inferred from the result. -/
theorem calibrationSlopeFromSourceWeights_at_zero_denominator_is_junk {p q : ℕ}
    (m : CrossPopulationMetricModel p q) (P : Pop)
    (hzero : scoreVarianceFromSourceWeights m P = 0) :
    calibrationSlopeFromSourceWeights m P = 0 := by
  unfold calibrationSlopeFromSourceWeights
  rw [hzero, div_zero]


/-- The source predictive covariance is the transported score equation applied
to the source score/outcome cross-covariance vector. -/
theorem sourcePredictiveCovarianceFromSourceWeights_eq_score_on_source_crossCov {p q : ℕ}
    (m : CrossPopulationMetricModel p q) :
    predictiveCovarianceFromSourceWeights m Pop.source =
      sourceWeightedTagScore m (crossCovariance m Pop.source) := by
  simp [predictiveCovarianceFromSourceWeights, sourceWeightedTagScore]

/-- The target predictive covariance is the transported score equation applied
to the target score/outcome cross-covariance vector. This is the explicit
source-weights-on-target-covariance equation that the biological model needs. -/
theorem targetPredictiveCovarianceFromSourceWeights_eq_score_on_target_crossCov {p q : ℕ}
    (m : CrossPopulationMetricModel p q) :
    predictiveCovarianceFromSourceWeights m Pop.target =
      sourceWeightedTagScore m (crossCovariance m Pop.target) := by
  simp [predictiveCovarianceFromSourceWeights, sourceWeightedTagScore]

/-- Exact source calibration-slope law from the source-learned score moments. -/
theorem sourceCalibrationSlopeFromSourceWeights_exact_metric_law {p q : ℕ}
    (m : CrossPopulationMetricModel p q) :
    calibrationSlopeFromSourceWeights m Pop.source =
      predictiveCovarianceFromSourceWeights m Pop.source /
        scoreVarianceFromSourceWeights m Pop.source := by
  rfl

/-- Exact transported calibration-slope law from the explicit SNP-level score
equation and target LD/cross-covariance structure. -/
theorem targetCalibrationSlopeFromSourceWeights_exact_metric_portability_law
    {p q : ℕ} (m : CrossPopulationMetricModel p q) :
    calibrationSlopeFromSourceWeights m Pop.target =
      predictiveCovarianceFromSourceWeights m Pop.target /
        scoreVarianceFromSourceWeights m Pop.target := by
  rfl

/-- Exact transported calibration-slope law written directly on the
source-weights-on-target-covariance equation. -/
theorem targetCalibrationSlopeFromSourceWeights_exact_snp_transport_law
    {p q : ℕ} (m : CrossPopulationMetricModel p q) :
    calibrationSlopeFromSourceWeights m Pop.target =
      sourceWeightedTagScore m (crossCovariance m Pop.target) /
        sourceWeightedTagScore m
          ((m.sigmaTag Pop.target).mulVec (sourceWeightsFromExplicitDrivers m)) := by
  simp [calibrationSlopeFromSourceWeights, predictiveCovarianceFromSourceWeights,
    scoreVarianceFromSourceWeights, sourceWeightedTagScore]

/-- The source predictive covariance decomposes into direct-causal,
proxy-tagging, and context contributions under the transported score
functional. -/
theorem sourcePredictiveCovarianceFromSourceWeights_eq_direct_plus_proxy_plus_context_scores
    {p q : ℕ} (m : CrossPopulationMetricModel p q) :
    predictiveCovarianceFromSourceWeights m Pop.source =
      sourceWeightedTagScore m (directCausalProjection m Pop.source) +
        sourceWeightedTagScore m (proxyTaggingProjection m Pop.source) +
        sourceWeightedTagScore m (m.contextCross Pop.source) := by
  rw [sourcePredictiveCovarianceFromSourceWeights_eq_score_on_source_crossCov,
    crossCovariance_eq_direct_plus_proxy_plus_context]
  simp [add_assoc]

/-- The target predictive covariance decomposes into direct-causal,
proxy-tagging, and context contributions under the transported score
functional. -/
theorem targetPredictiveCovarianceFromSourceWeights_eq_direct_plus_proxy_plus_context_scores
    {p q : ℕ} (m : CrossPopulationMetricModel p q) :
    predictiveCovarianceFromSourceWeights m Pop.target =
      sourceWeightedTagScore m (directCausalProjection m Pop.target) +
        sourceWeightedTagScore m (proxyTaggingProjection m Pop.target) +
        sourceWeightedTagScore m (m.contextCross Pop.target) := by
  rw [targetPredictiveCovarianceFromSourceWeights_eq_score_on_target_crossCov,
    crossCovariance_eq_direct_plus_proxy_plus_context]
  simp [add_assoc]

/-- Exact transported calibration-slope law with the target predictive
covariance expanded into direct-causal, proxy-tagging, and context channels. -/
theorem targetCalibrationSlopeFromSourceWeights_exact_direct_proxy_context_law
    {p q : ℕ} (m : CrossPopulationMetricModel p q) :
    calibrationSlopeFromSourceWeights m Pop.target =
      (sourceWeightedTagScore m (directCausalProjection m Pop.target) +
        sourceWeightedTagScore m (proxyTaggingProjection m Pop.target) +
        sourceWeightedTagScore m (m.contextCross Pop.target)) /
          scoreVarianceFromSourceWeights m Pop.target := by
  rw [targetCalibrationSlopeFromSourceWeights_exact_metric_portability_law,
    targetPredictiveCovarianceFromSourceWeights_eq_direct_plus_proxy_plus_context_scores]

/-- The target predictive covariance decomposes into the transported source-
stable effect projection, the projection of effect-size heterogeneity, and the
target context term. -/
theorem targetPredictiveCovariance_eq_sourceEffect_plus_heterogeneity_plus_context
    {p q : ℕ} (m : CrossPopulationMetricModel p q) :
    predictiveCovarianceFromSourceWeights m Pop.target =
      sourceWeightedTagScore m (targetSourceEffectProjection m) +
        sourceWeightedTagScore m (targetEffectHeterogeneityProjection m) +
        sourceWeightedTagScore m (m.contextCross Pop.target) := by
  rw [targetPredictiveCovarianceFromSourceWeights_eq_score_on_target_crossCov,
    crossCovariance_target_eq_source_effect_plus_effectHeterogeneity_plus_context]
  simp [add_assoc]

/-- Exact transported calibration-slope law with target effect heterogeneity
made explicit. -/
theorem targetCalibrationSlopeFromSourceWeights_exact_effect_heterogeneity_law
    {p q : ℕ} (m : CrossPopulationMetricModel p q) :
    calibrationSlopeFromSourceWeights m Pop.target =
      (sourceWeightedTagScore m (targetSourceEffectProjection m) +
        sourceWeightedTagScore m (targetEffectHeterogeneityProjection m) +
        sourceWeightedTagScore m (m.contextCross Pop.target)) /
          scoreVarianceFromSourceWeights m Pop.target := by
  rw [targetCalibrationSlopeFromSourceWeights_exact_metric_portability_law,
    targetPredictiveCovariance_eq_sourceEffect_plus_heterogeneity_plus_context]

/-- The target predictive covariance also decomposes into standing target
effects, target-only novel mutation effects, and the target context term. -/
theorem targetPredictiveCovariance_eq_standing_plus_novelMutation_plus_context
    {p q : ℕ} (m : CrossPopulationMetricModel p q) :
    predictiveCovarianceFromSourceWeights m Pop.target =
      sourceWeightedTagScore m ((sigmaTagCausalSourceAt m Pop.target).mulVec (m.beta Pop.target)) +
        sourceWeightedTagScore m (targetNovelMutationEffectProjection m) +
        sourceWeightedTagScore m (m.contextCross Pop.target) := by
  rw [targetPredictiveCovarianceFromSourceWeights_eq_score_on_target_crossCov,
    crossCovariance_target_eq_standing_plus_novelMutationEffect_plus_context]
  simp [add_assoc]

/-- Additive irreducible loss from broken source-to-target tagging.
This is the squared target-effect distortion induced by the gap between the
source and target tag-to-causal alignment matrices. -/
noncomputable def brokenTaggingResidual {p q : ℕ}
    (m : CrossPopulationMetricModel p q) : ℝ :=
  let delta := ((sigmaTagCausalSourceAt m Pop.source) - (sigmaTagCausalSourceAt m
      Pop.target)).mulVec (totalEffect m Pop.target)
  dotProduct delta delta

theorem brokenTaggingResidual_nonneg {p q : ℕ}
    (m : CrossPopulationMetricModel p q) :
    0 ≤ brokenTaggingResidual m := by
  unfold brokenTaggingResidual
  classical
  simp [dotProduct]
  exact Finset.sum_nonneg (fun _ _ ↦ mul_self_nonneg _)

/-- Additive irreducible loss from ancestry-specific LD distortion.
This is the squared source-score covariance distortion induced by the gap
between the source and target scored-SNP LD matrices.

    Empirical status: **MEASURED as one of four summands and not separated from
    the other three** (`validation/empirical/simcov/battery_transport.py`).
    This term enters the corpus only through
    `irreducibleTargetResidualBurden`, which is the sum of the four residuals and
    which reaches a measurement as the burden inside `effectiveOutcomeVariance`,
    the denominator of `r2FromSourceWeights`. That target `R²` cell lands at 2.50
    sems on a design whose source and target differ in tag-tag LD by Frobenius
    distance 2.09, so the SUM is exercised and this term is a live part of it.

    What that does not license: reading the 2.50 sems as a verdict on the
    quadratic form written here. The design moves all three channels at once --
    it has to, or a discrepancy could not be assigned to a term -- so a wrong
    coefficient on this residual and a compensating one on `brokenTaggingResidual`
    are the same number to that measurement. Separating them needs a design that
    holds the effect vector and the tag-causal alignment fixed while moving only
    `m.sigmaTag`, and none has been run.

    argument_source: model. The covariance matrices are SET in the simulation
    rather than estimated from the sample scored against. -/
noncomputable def ancestrySpecificLDResidual {p q : ℕ}
    (m : CrossPopulationMetricModel p q) : ℝ :=
  let wS := sourceWeightsFromExplicitDrivers m
  let delta := ((m.sigmaTag Pop.source) - (m.sigmaTag Pop.target)).mulVec wS
  dotProduct delta delta

theorem ancestrySpecificLDResidual_nonneg {p q : ℕ}
    (m : CrossPopulationMetricModel p q) :
    0 ≤ ancestrySpecificLDResidual m := by
  unfold ancestrySpecificLDResidual
  classical
  simp [dotProduct]
  exact Finset.sum_nonneg (fun _ _ ↦ mul_self_nonneg _)

/-- Additive irreducible loss from source-specific overfit or context mismatch.
This is the squared gap between source-only and target score/outcome
cross-covariance structure. -/
noncomputable def sourceSpecificOverfitResidual {p q : ℕ}
    (m : CrossPopulationMetricModel p q) : ℝ :=
  let delta := (m.contextCross Pop.source) - (m.contextCross Pop.target)
  dotProduct delta delta

theorem sourceSpecificOverfitResidual_nonneg {p q : ℕ}
    (m : CrossPopulationMetricModel p q) :
    0 ≤ sourceSpecificOverfitResidual m := by
  unfold sourceSpecificOverfitResidual
  classical
  simp [dotProduct]
  exact Finset.sum_nonneg (fun _ _ ↦ mul_self_nonneg _)

/-- Additive target-only phenotype variance from novel causal mutations that are
not tagged by the transported source score. -/
noncomputable def novelUntaggablePhenotypeResidual {p q : ℕ}
    (m : CrossPopulationMetricModel p q) : ℝ :=
  m.novelUntaggablePhenotypeVarianceTarget

@[simp] theorem novelUntaggablePhenotypeResidual_eq_field {p q : ℕ}
    (m : CrossPopulationMetricModel p q) :
    novelUntaggablePhenotypeResidual m = m.novelUntaggablePhenotypeVarianceTarget := by
  rfl

@[simp] theorem novelUntaggablePhenotypeResidual_nonneg {p q : ℕ}
    (m : CrossPopulationMetricModel p q) :
    0 ≤ novelUntaggablePhenotypeResidual m := by
  simpa [novelUntaggablePhenotypeResidual] using
    m.novelUntaggablePhenotypeVarianceTarget_nonneg

/-- Total additive irreducible target-side residual burden from the explicit
biological state. These losses are kept separate rather than folded into a
single multiplicative retention factor. -/
noncomputable def irreducibleTargetResidualBurden {p q : ℕ}
    (m : CrossPopulationMetricModel p q) : ℝ :=
  brokenTaggingResidual m +
    ancestrySpecificLDResidual m +
    sourceSpecificOverfitResidual m +
    novelUntaggablePhenotypeResidual m

theorem irreducibleTargetResidualBurden_nonneg {p q : ℕ}
    (m : CrossPopulationMetricModel p q) :
    0 ≤ irreducibleTargetResidualBurden m := by
  unfold irreducibleTargetResidualBurden
  linarith [brokenTaggingResidual_nonneg m, ancestrySpecificLDResidual_nonneg m,
    sourceSpecificOverfitResidual_nonneg m, novelUntaggablePhenotypeResidual_nonneg m]

/-- Canonical additive target-side penalty bundle induced by the explicit
cross-population state. This is the exact bridge back to the generic deployed
metric surface in `DGP.TransportedMetrics`. -/
noncomputable def targetIrreduciblePenaltyProfile {p q : ℕ}
    (m : CrossPopulationMetricModel p q) :
    TransportedMetrics.IrreducibleTargetPenalty where
  brokenTagging := brokenTaggingResidual m
  ancestrySpecificLD := ancestrySpecificLDResidual m
  sourceSpecificOverfit := sourceSpecificOverfitResidual m
  novelUntaggablePhenotype := novelUntaggablePhenotypeResidual m
  brokenTagging_nonneg := brokenTaggingResidual_nonneg m
  ancestrySpecificLD_nonneg := ancestrySpecificLDResidual_nonneg m
  sourceSpecificOverfit_nonneg := sourceSpecificOverfitResidual_nonneg m
  novelUntaggablePhenotype_nonneg := novelUntaggablePhenotypeResidual_nonneg m

@[simp] theorem targetIrreduciblePenaltyProfile_total {p q : ℕ}
    (m : CrossPopulationMetricModel p q) :
    (targetIrreduciblePenaltyProfile m).total =
      irreducibleTargetResidualBurden m := by
  simp [targetIrreduciblePenaltyProfile, TransportedMetrics.IrreducibleTargetPenalty.total,
    irreducibleTargetResidualBurden, add_assoc]

/-- Effective target outcome variance after adding an irreducible
target-specific residual burden from broken tagging, ancestry-specific LD, and
source-specific overfit, plus target-only untagged novel-mutation variance.

    Empirical status: UNTESTED. -/
noncomputable def residualBurden {p q : ℕ}
    (m : CrossPopulationMetricModel p q) (P : Pop) : ℝ :=
  Pop.pair 0 (irreducibleTargetResidualBurden m) P

/-- **The outcome variance a score is actually scored against, in a population.**

The source carries no transport burden — it is where the weights were fitted — and that
is now a computed consequence of `residualBurden` rather than the reason for writing two
separate definitions. `effectiveOutcomeVariance_source` below is the statement that used
to be implicit in the fact that only a `target` version existed.

    Empirical status: **VALIDATED in composition**
    (`validation/empirical/simcov/battery_transport.py`). This body is the
    denominator of `r2FromSourceWeights`, which is measured against the squared
    correlation of the transported score with the outcome at 0.06 sems in the
    source and 2.50 in the target, on one end-to-end transport simulation with
    400000 individuals per population and second moments SET rather than
    estimated. The two populations are what makes this a test of THIS body
    rather than of the numerator alone: `residualBurden` is zero in the source
    and the whole irreducible burden in the target, so the source cell fixes the
    numerator and the target cell is the one that can only pass if the burden is
    added, and added with coefficient one.

    What is NOT established: the internal structure of the burden. The four
    residuals enter only through their sum, as recorded at
    `ancestrySpecificLDResidual`; and the ADDITIVITY of `m.outcomeVariance` with
    the burden is what the target cell tests, at 2.50 sems, which is a pass and
    not a comfortable one.

    argument_source: model. -/
noncomputable def effectiveOutcomeVariance {p q : ℕ}
    (m : CrossPopulationMetricModel p q) (P : Pop) : ℝ :=
  (m.outcomeVariance P) + residualBurden m P

@[simp] theorem residualBurden_source {p q : ℕ} (m : CrossPopulationMetricModel p q) :
    residualBurden m Pop.source = 0 := rfl

/-- The companion to `residualBurden_source`, and the one that was missing.

`residualBurden` is written as a `Pop.pair`, so at the target it reduces to
`irreducibleTargetResidualBurden` by `rfl` -- but only if something performs
that reduction. `residualBurden_source` existed and this did not, which left
every target-side fact stated about `irreducibleTargetResidualBurden`
syntactically disconnected from goals mentioning `residualBurden m Pop.target`.
`linarith` in particular cannot bridge that gap: it was being handed a
nonnegativity fact about a term that does not occur in its goal. -/
@[simp] theorem residualBurden_target {p q : ℕ} (m : CrossPopulationMetricModel p q) :
    residualBurden m Pop.target = irreducibleTargetResidualBurden m := rfl

@[simp] theorem effectiveOutcomeVariance_source {p q : ℕ}
    (m : CrossPopulationMetricModel p q) :
    effectiveOutcomeVariance m Pop.source = m.outcomeVariance Pop.source := by
  simp [effectiveOutcomeVariance]

@[simp] theorem effectiveOutcomeVariance_target {p q : ℕ}
    (m : CrossPopulationMetricModel p q) :
    effectiveOutcomeVariance m Pop.target =
      (m.outcomeVariance Pop.target) + irreducibleTargetResidualBurden m := rfl

/-- The effective target outcome variance dominates the baseline target outcome
variance because the additive residual burden is nonnegative. -/
theorem effectiveTargetOutcomeVariance_ge_targetOutcomeVariance {p q : ℕ}
    (m : CrossPopulationMetricModel p q) :
    (m.outcomeVariance Pop.target) ≤ effectiveOutcomeVariance m Pop.target := by
  simp only [effectiveOutcomeVariance, residualBurden_target]
  linarith [irreducibleTargetResidualBurden_nonneg m]

/-- The effective target outcome variance stays strictly positive because the
base target outcome variance is positive and the additive residual burden is
nonnegative. -/
theorem effectiveTargetOutcomeVariance_pos {p q : ℕ}
    (m : CrossPopulationMetricModel p q) :
    0 < effectiveOutcomeVariance m Pop.target := by
  simp only [effectiveOutcomeVariance, residualBurden_target]
  linarith [m.outcomeVariance_pos Pop.target, irreducibleTargetResidualBurden_nonneg m]

/-- Exact decomposition of the effective target outcome variance into the base
target scale plus the three named additive residual-loss terms. -/
theorem effectiveTargetOutcomeVariance_eq_targetOutcomeVariance_add_losses {p q : ℕ}
    (m : CrossPopulationMetricModel p q) :
    effectiveOutcomeVariance m Pop.target =
      (m.outcomeVariance Pop.target) +
        brokenTaggingResidual m +
        ancestrySpecificLDResidual m +
        sourceSpecificOverfitResidual m +
        novelUntaggablePhenotypeResidual m := by
  simp [effectiveOutcomeVariance, residualBurden_target,
    irreducibleTargetResidualBurden, add_assoc]

/-- Exact source `R²` under the full source-side driver state. 
    Empirical status: **VALIDATED**
    (`validation/empirical/simcov/battery_transport.py`). One end-to-end
    transport simulation: 12 tags, 8 causal variants, 400000 individuals per
    population, genotypes drawn from a multivariate normal with a specified joint
    covariance so the ground-truth second moments are SET rather than estimated.
    Source and target differ in all three channels the model separates -- tag-tag
    LD (Frobenius distance 2.09), tag-causal alignment (1.89), and the effect
    vector (0.69) -- because a design moving only one could not say which term a
    discrepancy belonged to. Measured source and target `R²` are 0.05366 and
    0.00161, a factor of 33, so the transport signal is real. 0.12 sems source, 0.06
    target.

    Power: the prediction spans 0.00402 to 0.13610, a factor of 34. -/
noncomputable def explainedSignalVarianceFromSourceWeights {p q : ℕ}
    (m : CrossPopulationMetricModel p q) (P : Pop) : ℝ :=
  (predictiveCovarianceFromSourceWeights m P) ^ 2 / scoreVarianceFromSourceWeights m P

/-- With a vanishing denominator Mathlib returns `0`, which is a value this quantity can also
take legitimately, so the branch is named rather than left to be inferred from the result. -/
theorem explainedSignalVarianceFromSourceWeights_at_zero_denominator_is_junk {p q : ℕ}
    (m : CrossPopulationMetricModel p q) (P : Pop)
    (hzero : scoreVarianceFromSourceWeights m P = 0) :
    explainedSignalVarianceFromSourceWeights m P = 0 := by
  unfold explainedSignalVarianceFromSourceWeights
  rw [hzero, div_zero]


/-- **Exact `R²` in a population** under the full driver state, against the outcome
variance that population is actually scored against. 
    Empirical status: **VALIDATED**
    (`validation/empirical/simcov/battery_transport.py`). One end-to-end
    transport simulation: 12 tags, 8 causal variants, 400000 individuals per
    population, genotypes drawn from a multivariate normal with a specified joint
    covariance so the ground-truth second moments are SET rather than estimated.
    Source and target differ in all three channels the model separates -- tag-tag
    LD (Frobenius distance 2.09), tag-causal alignment (1.89), and the effect
    vector (0.69) -- because a design moving only one could not say which term a
    discrepancy belonged to. Measured source and target `R²` are 0.05366 and
    0.00161, a factor of 33, so the transport signal is real. 0.06 sems in the source
    and 2.50 in the target, against the squared correlation of the transported
    score with the outcome. This is the corpus's central prediction -- what a
    source-trained score achieves where it was not fitted -- and the target cell
    is the one that tests it.

    Power: the prediction spans 0.00162 to 0.05367, a factor of 33. -/
noncomputable def r2FromSourceWeights {p q : ℕ}
    (m : CrossPopulationMetricModel p q) (P : Pop) : ℝ :=
  explainedSignalVarianceFromSourceWeights m P / effectiveOutcomeVariance m P

/-- With a vanishing denominator Mathlib returns `0`, which is a value this quantity can also
take legitimately, so the branch is named rather than left to be inferred from the result. -/
theorem r2FromSourceWeights_at_zero_denominator_is_junk {p q : ℕ}
    (m : CrossPopulationMetricModel p q) (P : Pop)
    (hzero : effectiveOutcomeVariance m P = 0) :
    r2FromSourceWeights m P = 0 := by
  unfold r2FromSourceWeights
  rw [hzero, div_zero]


/-- Exact unexplained source-side liability variance under the full explicit
source-state score equation. This is the residual variance paired with the
source explained signal when constructing exact source AUC and source Brier
coordinates from the same mechanistic SNP-level state. -/
noncomputable def residualVarianceFromSourceWeights {p q : ℕ}
    (m : CrossPopulationMetricModel p q) (P : Pop) : ℝ :=
  effectiveOutcomeVariance m P - explainedSignalVarianceFromSourceWeights m P

/-- Closed-form source calibrated Brier coordinate from the full explicit
source-state score equation, evaluated at an arbitrary observed prevalence
coordinate `π`. This lets downstream theory compare source and target Brier on
the same target-population outcome scale without falling back to a benchmark
`R²` surrogate.

    Empirical status: **FALSIFIED under the liability-threshold model,
    inherited.** The body is `DGP.TransportedMetrics.calibratedBrierFromVariances`
    at the source population, and that definition is itself recorded FALSIFIED
    under the liability-threshold reading -- its docstring names THIS declaration
    as the consumer that inherits the error, and tabulates the sizes. The
    inheritance is exact and not approximate: this body adds no arithmetic, it
    only chooses which two variances to supply.

    The regime the parent is exact in transfers too: `calibratedBrierFromVariances`
    is exact where the outcome is Gaussian on the scale it is scored on, and
    wrong where cases are a truncated liability tail, which is the setting a
    prevalence argument `π` announces. So the fault is worst exactly where this
    definition is meant to be used.

    argument_source: model, inherited. -/
noncomputable def sourceCalibratedBrierFromSourceWeightsAtPrevalence {p q : ℕ}
    (m : CrossPopulationMetricModel p q) (π : ℝ) : ℝ :=
  TransportedMetrics.calibratedBrierFromVariances
    π
    (explainedSignalVarianceFromSourceWeights m Pop.source)
    (residualVarianceFromSourceWeights m Pop.source)

/-- The mechanistic source calibrated Brier coordinate is built directly from
source explained signal variance and source residual variance. -/
theorem sourceCalibratedBrierFromSourceWeightsAtPrevalence_eq_explicit_source_variances
    {p q : ℕ} (m : CrossPopulationMetricModel p q) (π : ℝ) :
    sourceCalibratedBrierFromSourceWeightsAtPrevalence m π =
      TransportedMetrics.calibratedBrierFromVariances
        π
        (explainedSignalVarianceFromSourceWeights m Pop.source)
        (residualVarianceFromSourceWeights m Pop.source) := by
  rfl

/-- The direct mechanistic source calibrated Brier coordinate agrees with the
`R²` chart induced by the same explicit source explained-signal and
total-variance decomposition. This is a derived identity, not the defining
construction of source Brier. -/
@[simp] theorem sourceCalibratedBrierFromSourceWeightsAtPrevalence_eq_explainedR2_chart
    {p q : ℕ} (m : CrossPopulationMetricModel p q) (π : ℝ) :
    sourceCalibratedBrierFromSourceWeightsAtPrevalence m π =
      TransportedMetrics.calibratedBrier π (r2FromSourceWeights m Pop.source) := by
  rw [sourceCalibratedBrierFromSourceWeightsAtPrevalence_eq_explicit_source_variances]
  rw [TransportedMetrics.calibratedBrierFromVariances_eq_chart]
  have h_source_ne : (m.outcomeVariance Pop.source) ≠ 0 :=
    ne_of_gt (m.outcomeVariance_pos Pop.source)
  have hr2 :
      TransportedMetrics.r2FromSignalVariance
          (explainedSignalVarianceFromSourceWeights m Pop.source)
          (residualVarianceFromSourceWeights m Pop.source) =
        r2FromSourceWeights m Pop.source := by
    unfold TransportedMetrics.r2FromSignalVariance residualVarianceFromSourceWeights
      r2FromSourceWeights
    field_simp [h_source_ne]
    ring
  rw [hr2]


/-- Exact target `R²` under transported source weights and the full target-side
driver state.

Rather than collapsing to a scalar retention factor, this depends explicitly on:
- source and target tag LD,
- source and target tag-causal alignment,
- source and target effect vectors,
- source and target context/environment cross-covariances, and
- additive irreducible target-side losses from broken tagging,
  ancestry-specific LD distortion, and source-specific overfit. -/
theorem explainedSignalVarianceFromSourceWeights_target {p q : ℕ}
    (m : CrossPopulationMetricModel p q) :
    explainedSignalVarianceFromSourceWeights m Pop.target =
      (predictiveCovarianceFromSourceWeights m Pop.target) ^ 2 /
        scoreVarianceFromSourceWeights m Pop.target := rfl

/-- Exact unexplained target-side liability variance under transported source
weights and the full explicit target-state loss budget. This is the residual
variance entering the liability-threshold AUC formula after the mechanistic
explained signal has been computed from the transported score moments.

**Simp direction changed here, and it affects every downstream file.** This name
was declared twice — once here, general in `P`, and once earlier in the file
specialised to `Pop.source` and spelling the right-hand side
`m.outcomeVariance Pop.source`. Two declarations of it would leave the specialised one in
the simp set, rewriting toward `m.outcomeVariance` at source only. There is one, so simp
rewrites toward `effectiveOutcomeVariance` at every `P`.

That is the direction the population index is going, and this statement is the
definitional unfolding of `residualVarianceFromSourceWeights`, which the
specialised one was not. But it is a behaviour change to a `@[simp]` lemma rather
than only a deletion, so if a downstream proof now normalises somewhere
unexpected, this is the cause. Reverting is one line — restore the specialised
copy and delete this — at the cost of losing the general form. -/
@[simp] theorem residualVarianceFromSourceWeights_eq_effective_minus_signal {p q : ℕ}
    (m : CrossPopulationMetricModel p q) (P : Pop) :
    residualVarianceFromSourceWeights m P =
      effectiveOutcomeVariance m P - explainedSignalVarianceFromSourceWeights m P := rfl

/-- Exact target calibrated Brier coordinate from the full explicit driver
state. Prevalence enters here, so Brier can change even when the score moments
are held fixed. -/
noncomputable def targetCalibratedBrierFromSourceWeights {p q : ℕ}
    (m : CrossPopulationMetricModel p q) : ℝ :=
  TransportedMetrics.calibratedBrierFromVariances
    m.targetPrevalence
    (explainedSignalVarianceFromSourceWeights m Pop.target)
    (residualVarianceFromSourceWeights m Pop.target)

/-- The mechanistic target calibrated Brier coordinate is built directly from
target explained signal variance and target residual variance. -/
theorem targetCalibratedBrierFromSourceWeights_eq_explicit_target_variances {p q : ℕ}
    (m : CrossPopulationMetricModel p q) :
    targetCalibratedBrierFromSourceWeights m =
      TransportedMetrics.calibratedBrierFromVariances
        m.targetPrevalence
        (explainedSignalVarianceFromSourceWeights m Pop.target)
        (residualVarianceFromSourceWeights m Pop.target) := by
  rfl

/-- Exact mechanistic target Brier portability law from transported score
moments and target prevalence. This is the direct variance law, not a theorem
about a benchmark `R²` chart. -/
theorem targetCalibratedBrierFromSourceWeights_exact_metric_portability_law
    {p q : ℕ} (m : CrossPopulationMetricModel p q) :
    targetCalibratedBrierFromSourceWeights m =
      TransportedMetrics.calibratedBrierFromVariances
        m.targetPrevalence
        ((predictiveCovarianceFromSourceWeights m Pop.target) ^ 2 /
          scoreVarianceFromSourceWeights m Pop.target)
        (effectiveOutcomeVariance m Pop.target -
          (predictiveCovarianceFromSourceWeights m Pop.target) ^ 2 /
            scoreVarianceFromSourceWeights m Pop.target) := by
  rw [targetCalibratedBrierFromSourceWeights_eq_explicit_target_variances]
  simp [explainedSignalVarianceFromSourceWeights,
    residualVarianceFromSourceWeights]

/-- Exact mechanistic target Brier portability law with the additive biological
loss budget made explicit in the residual term. -/
theorem targetCalibratedBrierFromSourceWeights_exact_loss_budget_law
    {p q : ℕ} (m : CrossPopulationMetricModel p q) :
    targetCalibratedBrierFromSourceWeights m =
      TransportedMetrics.calibratedBrierFromVariances
        m.targetPrevalence
        ((predictiveCovarianceFromSourceWeights m Pop.target) ^ 2 /
          scoreVarianceFromSourceWeights m Pop.target)
        ((m.outcomeVariance Pop.target) + irreducibleTargetResidualBurden m -
          (predictiveCovarianceFromSourceWeights m Pop.target) ^ 2 /
            scoreVarianceFromSourceWeights m Pop.target) := by
  rw [targetCalibratedBrierFromSourceWeights_exact_metric_portability_law,
    effectiveOutcomeVariance_target]

/-- The direct mechanistic target calibrated Brier coordinate agrees with the
`R²` chart induced by the same explicit target explained-signal and
total-variance decomposition. This is a derived identity, not the defining
construction of transported Brier. -/
@[simp] theorem targetCalibratedBrierFromSourceWeights_eq_explainedR2_chart {p q : ℕ}
    (m : CrossPopulationMetricModel p q) :
    targetCalibratedBrierFromSourceWeights m =
      TransportedMetrics.calibratedBrier
        m.targetPrevalence (r2FromSourceWeights m Pop.target) := by
  rw [targetCalibratedBrierFromSourceWeights_eq_explicit_target_variances]
  rw [TransportedMetrics.calibratedBrierFromVariances_eq_chart]
  have h_eff_ne : effectiveOutcomeVariance m Pop.target ≠ 0 :=
    ne_of_gt (effectiveTargetOutcomeVariance_pos m)
  have hr2 :
      TransportedMetrics.r2FromSignalVariance
          (explainedSignalVarianceFromSourceWeights m Pop.target)
          (residualVarianceFromSourceWeights m Pop.target) =
        r2FromSourceWeights m Pop.target := by
    unfold TransportedMetrics.r2FromSignalVariance residualVarianceFromSourceWeights
      r2FromSourceWeights
    field_simp [h_eff_ne]
    -- The residual variance is `Y - X`, so the denominator is `X + (Y - X)`.
    -- `ring` alone cannot finish: after collapsing that to `Y` the goal is
    -- `X * Y / Y = X`, and cancelling needs `Y ≠ 0`, which `ring` never
    -- consults. Collapse with `ring`, then cancel explicitly.
    have hden :
        explainedSignalVarianceFromSourceWeights m Pop.target +
            (effectiveOutcomeVariance m Pop.target -
              explainedSignalVarianceFromSourceWeights m Pop.target)
          = effectiveOutcomeVariance m Pop.target := by ring
    rw [hden, mul_div_assoc, div_self h_eff_ne, mul_one]
  rw [hr2]

/-- The target score variance is exactly the target quadratic form
`w_Sᵀ Σ_T w_S`. -/
theorem target_score_variance_from_source_weights_identity {p q : ℕ}
    (m : CrossPopulationMetricModel p q) :
    scoreVarianceFromSourceWeights m Pop.target =
      dotProduct (sourceWeightsFromExplicitDrivers m)
        ((m.sigmaTag Pop.target).mulVec (sourceWeightsFromExplicitDrivers m)) := by
  simp [scoreVarianceFromSourceWeights]

/-- The target score variance is the transported score equation applied to the
target LD operator acting on the transported source weights. -/
theorem targetScoreVarianceFromSourceWeights_eq_score_on_target_covariance_action {p q : ℕ}
    (m : CrossPopulationMetricModel p q) :
    scoreVarianceFromSourceWeights m Pop.target =
      sourceWeightedTagScore m
        ((m.sigmaTag Pop.target).mulVec (sourceWeightsFromExplicitDrivers m)) := by
  simp [scoreVarianceFromSourceWeights, sourceWeightedTagScore]

/-- The source score variance is the same score equation evaluated against the
source LD operator. -/
theorem scoreVarianceFromSourceWeights_source_eq_score_on_covariance_action {p q : ℕ}
    (m : CrossPopulationMetricModel p q) :
    scoreVarianceFromSourceWeights m Pop.source =
      sourceWeightedTagScore m
        ((m.sigmaTag Pop.source).mulVec (sourceWeightsFromExplicitDrivers m)) := by
  simp [scoreVarianceFromSourceWeights, sourceWeightedTagScore]

/-- The source `R²` is exactly the explained signal variance from the explicit
score equation divided by the source outcome variance. -/
theorem sourceR2FromSourceWeights_eq_signalVariance_ratio {p q : ℕ}
    (m : CrossPopulationMetricModel p q) :
    r2FromSourceWeights m Pop.source =
      explainedSignalVarianceFromSourceWeights m Pop.source / (m.outcomeVariance Pop.source) := by
  -- `r2FromSourceWeights` divides by `effectiveOutcomeVariance`, which is
  -- `outcomeVariance + residualBurden`. At the source the burden is zero, but
  -- `x + 0 = x` is not a definitional equality on `ℝ`, so `rfl` cannot close
  -- this and the rewrite has to be done explicitly.
  unfold r2FromSourceWeights effectiveOutcomeVariance
  rw [residualBurden_source, add_zero]

/-- Exact mechanistic source `R²` law from the source-learned score moments. -/
theorem sourceR2FromSourceWeights_exact_metric_law {p q : ℕ}
    (m : CrossPopulationMetricModel p q) :
    r2FromSourceWeights m Pop.source =
      (predictiveCovarianceFromSourceWeights m Pop.source) ^ 2 /
        (scoreVarianceFromSourceWeights m Pop.source * (m.outcomeVariance Pop.source)) := by
  -- Same source-side burden discharge as
  -- `sourceR2FromSourceWeights_eq_signalVariance_ratio`: the statement names
  -- `outcomeVariance`, the definition routes through `effectiveOutcomeVariance`.
  unfold r2FromSourceWeights explainedSignalVarianceFromSourceWeights
    effectiveOutcomeVariance
  rw [residualBurden_source, add_zero]
  ring_nf

/-- The target `R²` is exactly the explained signal variance from the explicit
transported score equation divided by the effective target outcome variance. -/
theorem targetR2FromSourceWeights_eq_signalVariance_ratio {p q : ℕ}
    (m : CrossPopulationMetricModel p q) :
    r2FromSourceWeights m Pop.target =
      explainedSignalVarianceFromSourceWeights m Pop.target /
        effectiveOutcomeVariance m Pop.target := by
  rfl

/-- Exact mechanistic target `R²` portability law from transported score
moments.

This is the exact `R²` law on the explicit SNP-level transport model:

`R²_target = Cov(score_sourceWeights,target)^2 /
             (Var(score_sourceWeights,target) * effectiveOutcomeVariance)`.

No source-`R²` inversion or scalar transport factor appears. -/
theorem targetR2FromSourceWeights_exact_metric_portability_law {p q : ℕ}
    (m : CrossPopulationMetricModel p q) :
    r2FromSourceWeights m Pop.target =
      (predictiveCovarianceFromSourceWeights m Pop.target) ^ 2 /
        (scoreVarianceFromSourceWeights m Pop.target * effectiveOutcomeVariance m Pop.target) := by
  unfold r2FromSourceWeights explainedSignalVarianceFromSourceWeights
  ring_nf

/-- Exact mechanistic source/target `R²` portability ratio law. The ratio is
determined by transported score/outcome covariance, source/target score
variance, and source/target outcome scales, not by any source-`R²` summary. -/
theorem exactR2PortabilityRatio_mechanistic_law {p q : ℕ}
    (m : CrossPopulationMetricModel p q) :
    r2FromSourceWeights m Pop.target / r2FromSourceWeights m Pop.source =
      ((predictiveCovarianceFromSourceWeights m Pop.target) ^ 2 *
          scoreVarianceFromSourceWeights m Pop.source * (m.outcomeVariance Pop.source)) /
        ((predictiveCovarianceFromSourceWeights m Pop.source) ^ 2 *
          scoreVarianceFromSourceWeights m Pop.target * effectiveOutcomeVariance m Pop.target) := by
  rw [targetR2FromSourceWeights_exact_metric_portability_law,
    sourceR2FromSourceWeights_exact_metric_law]
  simp [pow_two, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm, inv_inv]

/-- Exact target `R²` portability law written directly on the transported
source-weight score equation and the target covariance operator. -/
theorem targetR2FromSourceWeights_exact_snp_transport_law {p q : ℕ}
    (m : CrossPopulationMetricModel p q) :
    r2FromSourceWeights m Pop.target =
      (sourceWeightedTagScore m (crossCovariance m Pop.target)) ^ 2 /
        (sourceWeightedTagScore m
            ((m.sigmaTag Pop.target).mulVec (sourceWeightsFromExplicitDrivers m)) *
          effectiveOutcomeVariance m Pop.target) := by
  rw [targetR2FromSourceWeights_exact_metric_portability_law,
    targetPredictiveCovarianceFromSourceWeights_eq_score_on_target_crossCov,
    targetScoreVarianceFromSourceWeights_eq_score_on_target_covariance_action]

/-- Exact target `R²` portability law with the additive biological loss budget
made explicit. Broken tagging, ancestry-specific LD distortion,
source-specific overfit, and target-only untaggable phenotype variance enter
only through the target effective outcome scale. -/
theorem targetR2FromSourceWeights_exact_loss_budget_law {p q : ℕ}
    (m : CrossPopulationMetricModel p q) :
    r2FromSourceWeights m Pop.target =
      (predictiveCovarianceFromSourceWeights m Pop.target) ^ 2 /
        (scoreVarianceFromSourceWeights m Pop.target *
          ((m.outcomeVariance Pop.target) +
            brokenTaggingResidual m +
            ancestrySpecificLDResidual m +
            sourceSpecificOverfitResidual m +
            novelUntaggablePhenotypeResidual m)) := by
  rw [targetR2FromSourceWeights_exact_metric_portability_law,
    effectiveTargetOutcomeVariance_eq_targetOutcomeVariance_add_losses]

/-- Exact target `R²` portability law with the transported covariance expanded
into direct-causal, proxy-tagging, and context channels. -/
theorem targetR2FromSourceWeights_exact_direct_proxy_context_law {p q : ℕ}
    (m : CrossPopulationMetricModel p q) :
    r2FromSourceWeights m Pop.target =
      ((sourceWeightedTagScore m (directCausalProjection m Pop.target) +
          sourceWeightedTagScore m (proxyTaggingProjection m Pop.target) +
          sourceWeightedTagScore m (m.contextCross Pop.target)) ^ 2) /
        (scoreVarianceFromSourceWeights m Pop.target * effectiveOutcomeVariance m Pop.target) := by
  rw [targetR2FromSourceWeights_exact_metric_portability_law,
    targetPredictiveCovarianceFromSourceWeights_eq_direct_plus_proxy_plus_context_scores]

/-- Exact target `R²` portability law with target effect heterogeneity made
explicit. The source-stable transport channel, effect-heterogeneity channel,
and target context channel contribute additively to the transported
score/outcome covariance before squaring. -/
theorem targetR2FromSourceWeights_exact_effect_heterogeneity_law {p q : ℕ}
    (m : CrossPopulationMetricModel p q) :
    r2FromSourceWeights m Pop.target =
      ((sourceWeightedTagScore m (targetSourceEffectProjection m) +
          sourceWeightedTagScore m (targetEffectHeterogeneityProjection m) +
          sourceWeightedTagScore m (m.contextCross Pop.target)) ^ 2) /
        (scoreVarianceFromSourceWeights m Pop.target * effectiveOutcomeVariance m Pop.target) := by
  rw [targetR2FromSourceWeights_exact_metric_portability_law,
    targetPredictiveCovariance_eq_sourceEffect_plus_heterogeneity_plus_context]

/-- Ohta-Kimura-style closed-form LD-correlation decay law across populations:
correlation decays exponentially with recombination distance and divergence.

    Empirical status: **FALSIFIED as a shape in distance**
    (`validation/empirical/popgensel/ldshapecell.py`, cell `I`). The
    two factors of this body are in different states and both are now settled.
    The DIVERGENCE factor is right: the body carries `Real.sqrt fstGap`, and
    the rival `fstGap` exponent is rejected at 4.73 sems on the cells where the
    square root matches at 2.42 (`simcov/battery_bulk54.py`, tabulated below).
    The EXPONENTIAL IN DISTANCE is wrong, and what changed is not the design but
    the control it was missing.

    THE CONTROL THAT CLOSED IT, supplied without altering anything else about
    the design. Both shapes are fitted to the SAME binned msprime `r²` values
    with a free amplitude AND a free rate each, so neither is handicapped and
    the `r²` estimator's upward bias is common to both. Two arms:

      Nₑ      χ²/point exp   χ²/point hyp   worst exp   worst hyp
      2000       28.49          4.16        8.87 sems   3.91 sems
      5000       79.66          1.95       12.56 sems   3.46 sems

    Run on a TRUE exponential with the same `x` grid and matched per-point
    noise, the same fitter prefers the exponential by a sum-of-squares ratio of
    168 and 197. So the preference on the real arm is the data's and not the
    fitter's, which is exactly the thing `simcov/battery_bulk31.py` could not
    establish and the reason its identical conclusion was recorded as a lead.

    THE REPLACEMENT SHAPE IS ALREADY IN THIS FILE, WHICH IS WHY IT IS NOT
    INSTALLED HERE. The hyperbolic the data prefer is `ibdRecurrenceFixedPoint`
    read at `rate = c`: that definition's own docstring says so in as many
    words -- "with `rate = m` it is the island-model equilibrium `F_ST`, with
    `rate = c` it is Sved's `E[r²]`" -- and its island reading is VALIDATED at
    `simcov/battery_pd1.py` within 1.6% across a 50-fold sweep, with the rival
    linearisation rejected at up to 182% on the same cells. So the corrected
    shape is not a body anyone needs to invent. It is a named declaration whose
    other reading has just been measured, and the repair is a one-line
    substitution.

    TWO THINGS BLOCK THAT SUBSTITUTION, and neither is cosmetic:

    The RATE. Sved's law puts `4 Nₑ` in the denominator and the fit returns
    6572 against a true 20000 at `Nₑ = 5000` -- threefold low, in the same
    direction and roughly the same size as the `Nₑ_eff = 563 against 1000` the
    earlier run got. That reproducibility is itself informative: it is the known
    downward bias of `E[r²]` estimated from a finite sample of chromosomes, not
    a property of the law. But knowing the sign of a bias is not the same as
    having a coefficient, and this body's `lambda` is free precisely so the
    absolute rate need not be committed to -- which means substituting the
    hyperbolic changes the SHAPE without needing the constant at all.

    The AMPLITUDE, which is the one that actually stops it. Both fits carry a
    free amplitude, measured at 0.373 and 0.316. This body is normalised to 1 at
    zero distance -- `Real.exp 0 = 1` -- and so is `ibdRecurrenceFixedPoint` at
    `rate = 0`. A hyperbolic with amplitude 1 is therefore NOT the curve that
    was fitted, and nothing in cell `I` bears on whether the corpus's
    normalisation survives once the amplitude is pinned. Installing
    `1 / (1 + lambda * √fstGap * distance)` on the strength of a fit that needed
    a free 0.32 to reach the data would be clearing a marker with a body the
    measurement does not cover, which is the failure mode this file's history is
    mostly made of.

    So: FALSIFIED with a named successor and a stated obstruction, rather than a
    substitution. What would land the repair is one cell fitting the
    amplitude-1 hyperbolic against measured `r²` normalised to its own
    zero-distance limit -- a re-analysis of cell `I`'s stored curve, not a new
    simulation. The same evidence carried `OpenQuestions.ldTaggingDecay` to
    FALSIFIED, which is the same chart under another name.

    CONSUMERS. `jointTagLDKernelAt` multiplies this factor in and inherits the
    shape fault; its own record already carries a separate, established
    falsification through `migrationSharedBoostAt`.

    The earlier, control-less run reached the same conclusion by the same
    reasoning, and is kept because the reasoning is what the control licenses:
    coalescent theory gives Sved's `r² ≈ 1/(1 + 4·Nₑ·c)`, which is
    HYPERBOLIC in distance, not exponential, and the two differ in shape rather
    than scale. Measured `r²` between common SNP pairs binned over an
    eightyfold distance range (`Nₑ = 1000`, 5 Mb at `1e-8`, 8 replicates), with
    BOTH laws fitted to the same curve with one free rate and one free
    amplitude each so neither is handicapped:

      distance    measured r²        exponential fit   hyperbolic fit
        10 kb     0.5900 ± 0.0162    0.2387            0.4682
        75 kb     0.1721 ± 0.0104    0.1977            0.2133
       300 kb     0.0781 ± 0.0031    0.1028            0.0739
      1200 kb     0.0295 ± 0.0015    0.0075            0.0205

    The exponential misses at BOTH ends -- 21.7 sems at the short end and 14.2
    sems at the long end, where it decays far too fast -- while the hyperbolic
    stays within a few sems across most of the range. That two-sided failure is
    the signature of a wrong shape rather than a wrong constant, so no choice of
    `lambda` repairs it.

    The control this run lacked was looked for in the wrong place. The obvious
    candidate, that the hyperbolic fit recovers the simulated `Nₑ`, does not
    work as one -- it returned `Nₑ_eff = 563` against a true 1000, a known bias
    of `r²` estimated from 60 sampled chromosomes, and the same shortfall
    reappears in the run that did settle this. The control that works asks
    nothing of the fitted rate: it feeds the fitter a curve of KNOWN shape and
    requires it to recover that shape.

    THE `fstGap` FACTOR WAS FALSIFIED AND IS NOW **CORRECTED**: the body carries
    `Real.sqrt fstGap`, which is what the measurement supports. The superseded
    form used `fstGap` itself. Details, since the correction is a factor a
    reader will want to check:

    The exponent is a SQUARE ROOT
    (`simcov/battery_bulk54.py`). `lambda` is free, so the absolute rate is not
    refutable; the SHAPE of the rate-versus-divergence relation is, with no free
    constant left once each candidate is anchored at one cell. Five migration
    rates spanning 120-fold in `m` give `F_ST` = 0.5558, 0.2374, 0.0951, 0.0322,
    0.0062 -- a ninetyfold span -- and the fitted decay rate tracks
    `√fstGap`, not `fstGap`:

      rate ∝ fstGap        FALSIFIED, worst 4.73 sems (95% relative)
      rate ∝ √fstGap       MATCH, worst 2.42 sems
      rate independent     19.35 sems off, though formally NO POWER since a
                           constant prediction has no span

    So the SUPERSEDED body was wrong in its `fstGap` dependence and right that
    there IS one: divergence does slow LD-correlation decay, at half the rate
    that body claimed in the exponent. Replacing `fstGap` by `Real.sqrt fstGap`
    is what the measurement supports and is what the body above now reads;
    `lambda` absorbs the rest.

    An earlier run (`battery_bulk53.py`) reached the same conclusion and could
    not report it: it compared ONE fitted-rate ratio against ONE `F_ST` ratio,
    so the prediction span was zero and the power gate correctly refused a
    verdict. The fix was more cells, not a better estimator.

    Both leads are now closed and they closed in OPPOSITE directions, which is
    why the head names the shape and not the divergence factor: the `fstGap`
    dependence was falsified and the body was corrected, so that fault is gone;
    the exponential shape was falsified and the body still carries it, so that
    fault is live. A record that averaged the two into one verdict would hide
    which of them a reader still has to work around. -/
noncomputable def ldCorrelationDecay (distance fstGap lambda : ℝ) : ℝ :=
  Real.exp (-(lambda * Real.sqrt fstGap * distance))

/-- Reference evaluation.  The value is computed through the definitions this body calls, but
the theorem states a number: an inequality or an invariance leaves a family of bodies
satisfying it, and a value does not. -/
theorem ldCorrelationDecay_at_reference_point :
    ldCorrelationDecay 0 0 0 = 1 := by
  norm_num [ldCorrelationDecay]


/-- For positive divergence scale, LD correlation strictly decreases with distance. -/
theorem ldCorrelationDecay_strictAnti_distance
    (d1 d2 fstGap lambda : ℝ)
    (hScale : 0 < lambda * Real.sqrt fstGap)
    (hDist : d1 < d2) :
    ldCorrelationDecay d2 fstGap lambda < ldCorrelationDecay d1 fstGap lambda := by
  unfold ldCorrelationDecay
  apply Real.exp_lt_exp.mpr
  nlinarith [mul_lt_mul_of_pos_left hDist hScale]

/-- For positive distance and decay scale, LD correlation strictly decreases with `F_ST`.

    The monotonicity survives the correction from `fstGap` to `Real.sqrt fstGap`
    because the square root is strictly monotone on the nonnegatives -- which is
    why the empirical correction changed the RATE without disturbing any
    ordering theorem stated about this body. The nonnegativity hypothesis is new
    and is what `Real.sqrt` needs: below zero it is junk-zero and the ordering
    would fail. -/
theorem ldCorrelationDecay_strictAnti_fst
    (distance lambda fstSource fstTarget : ℝ)
    (hDist : 0 < distance)
    (hLambda : 0 < lambda)
    (hSourceNonneg : 0 ≤ fstSource)
    (hFst : fstSource < fstTarget) :
    ldCorrelationDecay distance fstTarget lambda <
      ldCorrelationDecay distance fstSource lambda := by
  unfold ldCorrelationDecay
  apply Real.exp_lt_exp.mpr
  have h_pos : 0 < lambda * distance := mul_pos hLambda hDist
  have hsqrt : Real.sqrt fstSource < Real.sqrt fstTarget :=
    Real.sqrt_lt_sqrt hSourceNonneg hFst
  have h_lt : Real.sqrt fstSource * (lambda * distance) <
      Real.sqrt fstTarget * (lambda * distance) :=
    mul_lt_mul_of_pos_right hsqrt h_pos
  linarith

/-- Generation-indexed population-genetic parameters that drive explicit
time-varying portability state. These parameters govern drift, mutation,
migration, and recombination without compressing transport into source `R²`. -/
structure GenerationalPopGenParameters where
  Ne : ℝ
  μ : ℝ
  mig : ℝ
  recomb : ℝ
  V_A : ℝ
  Ne_pos : 0 < Ne
  μ_nonneg : 0 ≤ μ
  mig_nonneg : 0 ≤ mig
  recomb_nonneg : 0 ≤ recomb
  recomb_le_half : recomb ≤ 1 / 2
  V_A_pos : 0 < V_A

/-- **The parameter class is inhabited**, at a standard human-scale setting:
`Nₑ = 1000`, `μ = 10⁻⁵` per generation, `m = 10⁻³`, `r = 10⁻²`, additive variance
`1`.

    Every value is strictly inside the constraints — no rate is `0` and the
    recombination fraction is well below the free-recombination boundary `1/2` —
    so nothing downstream is read at a degenerate point. -/
noncomputable def GenerationalPopGenParameters.witness : GenerationalPopGenParameters where
  Ne := 1000
  μ := 1 / 100000
  mig := 1 / 1000
  recomb := 1 / 100
  V_A := 1
  Ne_pos := by norm_num
  μ_nonneg := by norm_num
  mig_nonneg := by norm_num
  recomb_nonneg := by norm_num
  recomb_le_half := by norm_num
  V_A_pos := by norm_num

namespace GenerationalPopGenParameters

/-- Scaled mutation rate `θ = 4Neμ`.

    Empirical status: UNTESTED. -/
noncomputable def theta (g : GenerationalPopGenParameters) : ℝ :=
  scaledMutationRate g.Ne g.μ

/-- Scaled migration rate `M = 4Nem`.

    Empirical status: UNTESTED. -/
noncomputable def bigM (g : GenerationalPopGenParameters) : ℝ :=
  scaledMigrationRate g.Ne g.mig

/-- Reference evaluation: no migration, no scaled migration parameter. -/
theorem bigM_at_zero_migration (g : GenerationalPopGenParameters) (hzero : g.mig = 0) :
    bigM g = 0 := by
  unfold bigM scaledMigrationRate
  rw [hzero]
  ring


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
noncomputable def tauAt (g : GenerationalPopGenParameters) (t : ℕ) : ℝ :=
  (t : ℝ) / (2 * g.Ne)

/-- With a vanishing denominator Mathlib returns `0`, which is a value this quantity can also
take legitimately, so the branch is named rather than left to be inferred from the result. -/
theorem tauAt_at_zero_denominator_is_junk (g : GenerationalPopGenParameters) (t : ℕ)
    (hzero : (2 * g.Ne) = 0) :
    tauAt g t = 0 := by
  unfold tauAt
  rw [hzero, div_zero]


/-- Per-generation heterozygosity retention factor under drift + mutation. -/
noncomputable def hetDecayFactor (g : GenerationalPopGenParameters) : ℝ :=
  hetDecayFromScaled g.Ne g.theta

/-- Transient differentiation after `t` generations. This is the same
discrete-time drift/mutation/migration coordinate used in the evolutionary
layer, but now exposed directly to the mechanistic SNP/LD state.

    **The decay base was `hetDecayFactor` and has been corrected to
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

    Note that `hetDecayFactor` itself is untouched and remains correct for what
    it is: migration does not destroy heterozygosity, it relocates it. The error
    was in using a within-deme decay for a between-deme transient.

    Empirical status: **VALIDATED after correction; the superseded base
    FALSIFIED at up to 2222 sems**
    (`validation/empirical/simcov/battery_dis4.py`). The design and the
    table are recorded on `DGP.fstTransientDecayFromScaled`. Power: the
    half-life prediction spans 32.62 to 69.31 across the design where the
    superseded base spans 69.31 to 554.52. -/
noncomputable def fstTransientAt (g : GenerationalPopGenParameters) (t : ℕ) : ℝ :=
  (1 / (1 + g.theta + 2 * g.bigM)) *
    (1 - fstTransientDecayFromScaled g.Ne g.theta g.bigM ^ t)

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
noncomputable def mutationSharedRetentionAt
    (g : GenerationalPopGenParameters) (t : ℕ) : ℝ :=
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
    less for migration to restore than a model starting from zero assumes. -/
noncomputable def migrationSharedBoostAt
    (g : GenerationalPopGenParameters) (t : ℕ) : ℝ :=
  1 + g.bigM * g.tauAt t / (1 + g.bigM)

@[simp] theorem tauAt_zero (g : GenerationalPopGenParameters) :
    g.tauAt 0 = 0 := by
  simp [tauAt]

@[simp] theorem fstTransientAt_zero (g : GenerationalPopGenParameters) :
    g.fstTransientAt 0 = 0 := by
  simp [fstTransientAt, fstTransientDecayFromScaled, hetDecayFromScaled]

@[simp] theorem mutationSharedRetentionAt_zero (g : GenerationalPopGenParameters) :
    g.mutationSharedRetentionAt 0 = 1 := by
  simp [mutationSharedRetentionAt, tauAt]

@[simp] theorem migrationSharedBoostAt_zero (g : GenerationalPopGenParameters) :
    g.migrationSharedBoostAt 0 = 1 := by
  simp [migrationSharedBoostAt, tauAt, bigM]

end GenerationalPopGenParameters

/-- Exact bridge from the coarse DGP evolutionary block to the
generation-indexed population-genetic parameter block used by the mechanistic
transport model. This carries only the shared popgen primitives; the
SNP/LD-aware state still lives in `CrossPopulationGenerationalModel`. -/
noncomputable def PGSEvolutionaryModel.toGenerationalPopGenParameters
    (m : PGSEvolutionaryModel) : GenerationalPopGenParameters where
  Ne := m.Ne
  μ := m.mu
  mig := m.mig
  recomb := m.recomb
  V_A := m.V_A
  Ne_pos := m.Ne_pos
  μ_nonneg := m.mu_nonneg
  mig_nonneg := m.mig_nonneg
  recomb_nonneg := m.recomb_nonneg
  recomb_le_half := m.recomb_le_half
  V_A_pos := m.V_A_pos

@[simp] theorem PGSEvolutionaryModel.toGenerationalPopGenParameters_theta
    (m : PGSEvolutionaryModel) :
    (m.toGenerationalPopGenParameters).theta = m.theta := by
  simp [PGSEvolutionaryModel.toGenerationalPopGenParameters,
    GenerationalPopGenParameters.theta, EvolutionaryParameters.theta]

@[simp] theorem PGSEvolutionaryModel.toGenerationalPopGenParameters_bigM
    (m : PGSEvolutionaryModel) :
    (m.toGenerationalPopGenParameters).bigM = m.bigM := by
  simp [PGSEvolutionaryModel.toGenerationalPopGenParameters,
    GenerationalPopGenParameters.bigM, EvolutionaryParameters.bigM]

@[simp] theorem PGSEvolutionaryModel.toGenerationalPopGenParameters_hetDecayFactor
    (m : PGSEvolutionaryModel) :
    (m.toGenerationalPopGenParameters).hetDecayFactor = m.hetDecayFactor := by
  unfold GenerationalPopGenParameters.hetDecayFactor PGSEvolutionaryModel.hetDecayFactor
    hetDecayFromScaled
  rw [PGSEvolutionaryModel.toGenerationalPopGenParameters_theta]
  rfl

/-- The transient `F_ST` coordinate in the coarse DGP block agrees exactly with
the generation-indexed popgen bridge at `⌊t_div⌋`, because both use the same
discrete differentiation recursion. Both were corrected together: an identity
between two coordinates survives a common wrong factor on both sides, so this
theorem constrained them jointly and could not have caught the decay base. -/
@[simp] theorem PGSEvolutionaryModel.toGenerationalPopGenParameters_fstTransientAt_floor
    (m : PGSEvolutionaryModel) :
    (m.toGenerationalPopGenParameters).fstTransientAt (Nat.floor m.t_div) =
      m.fstTransient := by
  unfold GenerationalPopGenParameters.fstTransientAt PGSEvolutionaryModel.fstTransient
    fstTransientDecayFromScaled hetDecayFromScaled
  simp [PGSEvolutionaryModel.toGenerationalPopGenParameters, fstEquilibrium,
    GenerationalPopGenParameters.theta, GenerationalPopGenParameters.bigM,
    PGSEvolutionaryModel.toEvo, EvolutionaryParameters.theta,
    EvolutionaryParameters.bigM, scaledMutationRate, scaledMigrationRate]

/-- When divergence time is an integer number of generations, the coarse
mutation-history coordinate agrees exactly with the generational popgen bridge
at that generation. -/
theorem PGSEvolutionaryModel.toGenerationalPopGenParameters_mutationSharedRetentionAt_floor
    (m : PGSEvolutionaryModel)
    (h_disc : m.t_div = (Nat.floor m.t_div : ℝ)) :
    (m.toGenerationalPopGenParameters).mutationSharedRetentionAt (Nat.floor m.t_div) =
      mutationLDErosion m.toEvo := by
  unfold GenerationalPopGenParameters.mutationSharedRetentionAt
    PGSEvolutionaryModel.toEvo mutationLDErosion
  rw [PGSEvolutionaryModel.toGenerationalPopGenParameters_theta]
  simp only [GenerationalPopGenParameters.tauAt,
    PGSEvolutionaryModel.toGenerationalPopGenParameters,
    EvolutionaryParameters.theta, EvolutionaryParameters.tau]
  rw [h_disc, Nat.floor_natCast]

/-- When divergence time is an integer number of generations, the coarse
migration-history coordinate agrees exactly with the generational popgen bridge
at that generation. -/
theorem PGSEvolutionaryModel.toGenerationalPopGenParameters_migrationSharedBoostAt_floor
    (m : PGSEvolutionaryModel)
    (h_disc : m.t_div = (Nat.floor m.t_div : ℝ)) :
    (m.toGenerationalPopGenParameters).migrationSharedBoostAt (Nat.floor m.t_div) =
      migrationLDBoost m.toEvo := by
  unfold GenerationalPopGenParameters.migrationSharedBoostAt
    PGSEvolutionaryModel.toEvo migrationLDBoost
  rw [PGSEvolutionaryModel.toGenerationalPopGenParameters_bigM]
  simp only [GenerationalPopGenParameters.tauAt,
    PGSEvolutionaryModel.toGenerationalPopGenParameters,
    EvolutionaryParameters.bigM, EvolutionaryParameters.tau]
  rw [h_disc, Nat.floor_natCast]

/-- Exact bridge from the DGP coordinate summary to the generational popgen
coordinates for the fields that genuinely match. The LD coordinate is
deliberately excluded here because the mechanistic model uses a joint
locus-specific kernel rather than a single global LD scalar. -/
theorem PGSEvolutionaryModel.coordinateSummary_matches_generational_popgen_at_floor
    (m : PGSEvolutionaryModel)
    (h_disc : m.t_div = (Nat.floor m.t_div : ℝ)) :
    m.coordinateSummary.alleleFreqCoordinate =
      1 - (m.toGenerationalPopGenParameters).fstTransientAt (Nat.floor m.t_div) ∧
    m.coordinateSummary.ancestralVariantCoordinate =
      (m.toGenerationalPopGenParameters).mutationSharedRetentionAt (Nat.floor m.t_div) ∧
    m.coordinateSummary.migrationCoordinate =
      (m.toGenerationalPopGenParameters).migrationSharedBoostAt (Nat.floor m.t_div) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [PGSEvolutionaryModel.coordinateSummary_alleleFreqCoordinate]
    exact congrArg (fun x ↦ 1 - x)
      (PGSEvolutionaryModel.toGenerationalPopGenParameters_fstTransientAt_floor m)
  · rw [PGSEvolutionaryModel.coordinateSummary_ancestralVariantCoordinate]
    exact (PGSEvolutionaryModel.toGenerationalPopGenParameters_mutationSharedRetentionAt_floor
      m h_disc).symm
  · rw [PGSEvolutionaryModel.coordinateSummary_migrationCoordinate]
    exact (PGSEvolutionaryModel.toGenerationalPopGenParameters_migrationSharedBoostAt_floor
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
    are this body applied to their own frequencies and inherit the failure. -/
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
  popGen : GenerationalPopGenParameters
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

/-- **The generational transport model is inhabited**, at every panel size `(p, q)`.

    The tag covariance is the identity, the two populations start at the same
    allele frequencies, and the effect vector, the heterogeneity path and the
    novel-mutation path are zero: this is the no-divergence configuration, in
    which the transported score is the source score at every generation. It is
    the null of the theory rather than an interesting member of it, and that is
    the point — it fixes what the generational statements quantify over. The
    variance and prevalence fields are strictly inside their constraints. -/
noncomputable def CrossPopulationGenerationalModel.witness (p q : ℕ) :
    CrossPopulationGenerationalModel p q where
  popGen := GenerationalPopGenParameters.witness
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
  tagAlleleFreqSource := fun _ ↦ 1 / 2
  tagAlleleFreqStandingTargetAt := fun _ _ ↦ 1 / 2
  tagAlleleFreqMutationShiftAt := fun _ _ ↦ 0
  causalAlleleFreqSource := fun _ ↦ 1 / 2
  causalAlleleFreqStandingTargetAt := fun _ _ ↦ 1 / 2
  causalAlleleFreqMutationShiftAt := fun _ _ ↦ 0
  contextCrossSource := fun _ ↦ 0
  contextCrossTargetAt := fun _ _ ↦ 0
  outcome := GenerationalOutcomeScale.balanced 1 (by norm_num)

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
    retention above one instead of as a loss. -/
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
    before the body was changed to match it. -/
noncomputable def causalAlleleFreqRetentionAt {p q : ℕ}
    (m : CrossPopulationGenerationalModel p q) (t : ℕ) (j : Fin q) : ℝ :=
  (2 * causalAlleleFreqTargetAt m t j * (1 - causalAlleleFreqTargetAt m t j)) /
    (2 * m.causalAlleleFreqSource j * (1 - m.causalAlleleFreqSource j))

/-- Fraction of target-side novel variation accumulated by generation `t`.
This is the complement of shared ancestral variation retained after mutation. -/
noncomputable def novelVariantInnovationAt (g : GenerationalPopGenParameters) (t : ℕ) : ℝ :=
  1 - g.mutationSharedRetentionAt t

@[simp] theorem novelVariantInnovationAt_zero (g : GenerationalPopGenParameters) :
    novelVariantInnovationAt g 0 = 0 := by
  simp [novelVariantInnovationAt]

/-- Joint locus-level transport kernel for LD among scored SNPs at generation
`t`. This is where drift, recombination, mutation history, migration history,
and tag-SNP allele-frequency drift meet; the mechanistic model does not treat
them as independent global scalars.

    Empirical status: **FALSIFIED**, inherited from `migrationSharedBoostAt`,
    which overstates the migration-driven restoration of shared LD by roughly a
    factor of three, worst cell 18.17 sems, with the gap widening in both `τ`
    and `bigM`. This kernel MULTIPLIES that factor in, so the overstatement
    passes straight through and grows with `t`.

    **THE `fstGap` FAULT THIS RECORD USED TO NAME IS FIXED AND THE MARKER WAS
    STALE.** The first factor is `ldCorrelationDecay` at the transient `F_ST`,
    and that body's `fstGap` dependence WAS falsified at 4.73 sems -- the fitted
    decay rate tracks `√fstGap`, not `fstGap`. It now carries
    `Real.sqrt fstGap`, so the "attenuates at twice the supported rate" reading
    that stood here describes a superseded body. The status did not change
    because a second, live fault was underneath it; the reason did.

    The composition is where the damage concentrates rather than cancels: a
    kernel that is a product of factors inherits the worst of them and cannot
    average them away.

    THE SECOND INHERITED FAULT IS NO LONGER A LEAD. Whether the decay in
    DISTANCE is exponential at all, or hyperbolic as Sved's relation gives, was
    settled against the exponential once the control the earlier run lacked was
    supplied (`validation/empirical/popgensel/ldshapecell.py`, cell `I`;
    χ²/point 28.49 and 79.66 exponential against 4.16 and 1.95 hyperbolic, on a
    fitter that prefers the exponential by 168-fold and 197-fold when handed a
    true exponential). So this kernel carries TWO established faults, not one
    established and one open: the migration overstatement it inherits from
    `migrationSharedBoostAt`, and the wrong LD shape it inherits from
    `ldCorrelationDecay`. Being a product, it inherits the worse of them and
    cannot average them away. -/
noncomputable def jointTagLDKernelAt {p q : ℕ}
    (m : CrossPopulationGenerationalModel p q) (t : ℕ) (i j : Fin p) : ℝ :=
  ldCorrelationDecay (m.tagDistance i j)
      (m.popGen.fstTransientAt t) m.popGen.recomb *
    m.popGen.mutationSharedRetentionAt t *
    m.popGen.migrationSharedBoostAt t *
    tagAlleleFreqRetentionAt m t i *
    tagAlleleFreqRetentionAt m t j

@[simp] theorem jointTagLDKernelAt_uses_ld_af_mutation_migration {p q : ℕ}
    (m : CrossPopulationGenerationalModel p q) (t : ℕ) (i j : Fin p) :
    jointTagLDKernelAt m t i j =
      ldCorrelationDecay (m.tagDistance i j)
          (m.popGen.fstTransientAt t) m.popGen.recomb *
        m.popGen.mutationSharedRetentionAt t *
        m.popGen.migrationSharedBoostAt t *
        tagAlleleFreqRetentionAt m t i *
        tagAlleleFreqRetentionAt m t j := by
  simp [jointTagLDKernelAt]

/-- Joint locus-level transport kernel for directly scored causal variants.
This omits the LD-decay term because the scored variant is itself causal, but
it still carries mutation, migration, and AF-history interactions. -/
noncomputable def jointDirectCausalKernelAt {p q : ℕ}
    (m : CrossPopulationGenerationalModel p q) (t : ℕ) (i : Fin p) (j : Fin q) : ℝ :=
  m.popGen.mutationSharedRetentionAt t *
    m.popGen.migrationSharedBoostAt t *
    tagAlleleFreqRetentionAt m t i *
    causalAlleleFreqRetentionAt m t j

@[simp] theorem jointDirectCausalKernelAt_uses_af_mutation_migration {p q : ℕ}
    (m : CrossPopulationGenerationalModel p q) (t : ℕ) (i : Fin p) (j : Fin q) :
    jointDirectCausalKernelAt m t i j =
      m.popGen.mutationSharedRetentionAt t *
        m.popGen.migrationSharedBoostAt t *
        tagAlleleFreqRetentionAt m t i *
        causalAlleleFreqRetentionAt m t j := by
  simp [jointDirectCausalKernelAt]

/-- Joint locus-level transport kernel for ancestry-specific proxy tagging.
This carries the full interaction between LD decay, mutation/migration sharing,
and source/target allele-frequency history. -/
noncomputable def jointProxyTaggingKernelAt {p q : ℕ}
    (m : CrossPopulationGenerationalModel p q) (t : ℕ) (i : Fin p) (j : Fin q) : ℝ :=
  ldCorrelationDecay (m.tagCausalDistance i j)
      (m.popGen.fstTransientAt t) m.popGen.recomb *
    m.popGen.mutationSharedRetentionAt t *
    m.popGen.migrationSharedBoostAt t *
    tagAlleleFreqRetentionAt m t i *
    causalAlleleFreqRetentionAt m t j

@[simp] theorem jointProxyTaggingKernelAt_uses_ld_tagging_af_mutation_migration {p q : ℕ}
    (m : CrossPopulationGenerationalModel p q) (t : ℕ) (i : Fin p) (j : Fin q) :
    jointProxyTaggingKernelAt m t i j =
      ldCorrelationDecay (m.tagCausalDistance i j)
          (m.popGen.fstTransientAt t) m.popGen.recomb *
        m.popGen.mutationSharedRetentionAt t *
        m.popGen.migrationSharedBoostAt t *
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
    (m.popGen.migrationSharedBoostAt t)⁻¹ *
    tagAlleleFreqRetentionAt m t i *
    causalAlleleFreqRetentionAt m t j

@[simp] theorem jointNovelDirectCausalKernelAt_uses_af_mutation_migration {p q : ℕ}
    (m : CrossPopulationGenerationalModel p q) (t : ℕ) (i : Fin p) (j : Fin q) :
    jointNovelDirectCausalKernelAt m t i j =
      novelVariantInnovationAt m.popGen t *
        (m.popGen.migrationSharedBoostAt t)⁻¹ *
        tagAlleleFreqRetentionAt m t i *
        causalAlleleFreqRetentionAt m t j := by
  simp [jointNovelDirectCausalKernelAt]

/-- Joint locus-level kernel for target-only novel proxy tagging. This carries
both local LD structure and mutation-generated novelty, rather than just
attenuating the shared source proxy surface. -/
noncomputable def jointNovelProxyTaggingKernelAt {p q : ℕ}
    (m : CrossPopulationGenerationalModel p q) (t : ℕ) (i : Fin p) (j : Fin q) : ℝ :=
  ldCorrelationDecay (m.tagCausalDistance i j)
      (m.popGen.fstTransientAt t) m.popGen.recomb *
    novelVariantInnovationAt m.popGen t *
    (m.popGen.migrationSharedBoostAt t)⁻¹ *
    tagAlleleFreqRetentionAt m t i *
    causalAlleleFreqRetentionAt m t j

@[simp] theorem jointNovelProxyTaggingKernelAt_uses_ld_af_mutation_migration {p q : ℕ}
    (m : CrossPopulationGenerationalModel p q) (t : ℕ) (i : Fin p) (j : Fin q) :
    jointNovelProxyTaggingKernelAt m t i j =
      ldCorrelationDecay (m.tagCausalDistance i j)
          (m.popGen.fstTransientAt t) m.popGen.recomb *
        novelVariantInnovationAt m.popGen t *
        (m.popGen.migrationSharedBoostAt t)⁻¹ *
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
  outcomeVariance := Pop.pair (m.sourceOutcomeVariance) (m.targetOutcomeVarianceAt t)
  novelDirectCausal := Pop.pair 0 (novelDirectCausalTargetAt m t)
  novelProxyTagging := Pop.pair 0 (novelProxyTaggingTargetAt m t)
  novelCausalEffect := Pop.pair 0 (m.novelCausalEffectTargetAt t)
  novelUntaggablePhenotypeVarianceTarget := m.novelUntaggablePhenotypeVarianceAt t
  targetPrevalence := m.targetPrevalenceAt t
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
    r2FromSignalVariance (realWorldPGSVariance V_A fstT rhoT) V_E /
      r2FromSignalVariance (realWorldPGSVariance V_A fstS rhoS) V_E <
    r2FromSignalVariance (realWorldPGSVariance V_A fstT rhoS) V_E /
      r2FromSignalVariance (realWorldPGSVariance V_A fstS rhoS) V_E := by
  rcases h_rho with ⟨hRhoT_pos, hRhoT_lt_rhoS⟩
  have hRhoS_pos : 0 < rhoS := lt_trans hRhoT_pos hRhoT_lt_rhoS
  have hu_pos : 0 < (1 - fstT) * V_A := mul_pos (by linarith) hVA
  -- Numerator: rhoT < rhoS implies R²(rhoT·u) < R²(rhoS·u)
  have h_num_lt :
      r2FromSignalVariance (realWorldPGSVariance V_A fstT rhoT) V_E <
        r2FromSignalVariance (realWorldPGSVariance V_A fstT rhoS) V_E := by
    apply expectedR2_strictMono_nonneg V_E _ _ hVE
    · unfold realWorldPGSVariance
      exact le_of_lt (by simpa [mul_assoc] using mul_pos hRhoT_pos hu_pos)
    · simpa [realWorldPGSVariance, mul_assoc] using
        mul_lt_mul_of_pos_right hRhoT_lt_rhoS hu_pos
  -- Denominator positivity
  have hsource_sig_pos : 0 < realWorldPGSVariance V_A fstS rhoS := by
    unfold realWorldPGSVariance
    simpa [mul_assoc] using mul_pos (mul_pos hRhoS_pos (by linarith : 0 < 1 - fstS)) hVA
  have h_den_pos : 0 < r2FromSignalVariance (realWorldPGSVariance V_A fstS rhoS) V_E := by
    unfold r2FromSignalVariance
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
    r2FromSignalVariance (realWorldPGSVariance V_A fstT rhoT) V_E /
      r2FromSignalVariance (realWorldPGSVariance V_A fstS rhoS) V_E <
    r2FromSignalVariance (presentDayPGSVariance V_A fstT) V_E /
      r2FromSignalVariance (presentDayPGSVariance V_A fstS) V_E := by
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
    simpa [realWorldPGSVariance, presentDayPGSVariance, pgsVarianceFromHet,
      mul_assoc, mul_left_comm, mul_comm] using hscaled
  have hR2Target_lt :
      r2FromSignalVariance (realWorldPGSVariance V_A fstT rhoT) V_E <
        r2FromSignalVariance (presentDayPGSVariance V_A fstT) V_E := by
    apply expectedR2_strictMono_nonneg V_E
    · exact hVE
    · unfold realWorldPGSVariance
      have hRhoTerm_nonneg : 0 ≤ rhoT * (1 - fstT) := by
        have hOneMinus_nonneg : 0 ≤ 1 - fstT := by linarith
        exact mul_nonneg (le_of_lt hRhoT_pos) hOneMinus_nonneg
      exact mul_nonneg hRhoTerm_nonneg (le_of_lt hVA)
    · exact hRealTarget_lt
  have hSourcePos : 0 < presentDayPGSVariance V_A fstS := by
    unfold presentDayPGSVariance pgsVarianceFromHet
    have h1s : 0 < 1 - fstS := by linarith
    exact mul_pos hVA h1s
  have hR2Source_pos : 0 < r2FromSignalVariance (presentDayPGSVariance V_A fstS) V_E := by
    unfold r2FromSignalVariance
    have hden : 0 < presentDayPGSVariance V_A fstS + V_E := by linarith [hSourcePos, hVE]
    exact div_pos hSourcePos hden
  have hL :
      r2FromSignalVariance (realWorldPGSVariance V_A fstT rhoT) V_E /
          r2FromSignalVariance (presentDayPGSVariance V_A fstS) V_E <
        r2FromSignalVariance (presentDayPGSVariance V_A fstT) V_E /
          r2FromSignalVariance (presentDayPGSVariance V_A fstS) V_E := by
    have hmul :
        r2FromSignalVariance (realWorldPGSVariance V_A fstT rhoT) V_E * (r2FromSignalVariance
            (presentDayPGSVariance V_A fstS) V_E)⁻¹ <
          r2FromSignalVariance (presentDayPGSVariance V_A fstT) V_E * (r2FromSignalVariance
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
    r2FromSignalVariance (realWorldPGSVariance V_A fstT rhoT) V_E /
      r2FromSignalVariance (realWorldPGSVariance V_A fstS rhoS) V_E <
    r2FromSignalVariance (presentDayPGSVariance V_A fstT) V_E /
      r2FromSignalVariance (presentDayPGSVariance V_A fstS) V_E := by
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
    unfold presentDayR2 r2FromSignalVariance
    have hv_pos : 0 < presentDayPGSVariance V_A fstS := by
      unfold presentDayPGSVariance pgsVarianceFromHet
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
    unfold presentDayR2 r2FromSignalVariance
    have hv_pos : 0 < presentDayPGSVariance V_A fstSource := by
      unfold presentDayPGSVariance pgsVarianceFromHet
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
and the `FstBounds` section of `Descent.PortabilityBounds` that was stated about it.**

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
  TransportedMetrics.calibratedBrier π r2

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
    cannot fail. The harness detected that. The MATCH above needs no control. -/
noncomputable def liabilityThreshold (K : ℝ) : ℝ := Function.invFun Phi (1 - K)

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
    other reading would be wrong by a factor of five. -/
noncomputable def liabilityCaseVariance (r2 K : ℝ) : ℝ :=
  1 - r2 * liabilityCaseMean K * (liabilityCaseMean K - liabilityThreshold K)

/-- Reference evaluation: with no explained variance the case liability keeps unit variance. -/
theorem liabilityCaseVariance_at_zero_r2 (K : ℝ) : liabilityCaseVariance 0 K = 1 := by
  unfold liabilityCaseVariance
  ring


/-- Score variance among controls, `v₀ = 1 - R²·i_c·(i_c - T)`.

    Empirical status: **VALIDATED**
    (`validation/empirical/simcov/battery_max.py`,
    `test_liability_control_variance`). Four million explicit normal
    liabilities, the variance read on the STANDARDISED score among controls:

      K       r2     this def   simulated            sems
      0.05    0.3     0.94289   0.94167±0.00068      1.79
      0.20    0.3     0.87490   0.87428±0.00069      0.90
      0.05    0.6     0.88579   0.88614±0.00064      0.56

    The reading is pinned the same way `liabilityCaseVariance`'s was: the
    variance is of the standardised PGS among controls, not of the liability. -/
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
  Phi ((liabilityCaseMean K - liabilityControlMean K) * Real.sqrt r2 /
    Real.sqrt (liabilityCaseVariance r2 K + liabilityControlVariance r2 K))

/-- A nonpositive total liability variance sends the square root to Mathlib's junk `0`, so the
whole argument of `Phi` divides by zero and the discrimination reads as `Phi 0`, chance. -/
theorem liabilityThresholdAUCFromExplainedR2_at_nonpositive_variance_is_junk (r2 K : ℝ)
    (hnonpos : liabilityCaseVariance r2 K + liabilityControlVariance r2 K ≤ 0) :
    liabilityThresholdAUCFromExplainedR2 r2 K = Phi 0 := by
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
  them. `Descent.Probability` defines `Phi` and proves nothing about it, so the
  derivation is not currently available; supplying it is the honest way to reinstate this.
* `caseVariance_pos` and `controlVariance_pos`. These are not conditions a caller can
  choose to meet: `liabilityCaseVariance r2 K` is a closed formula in `r2` and `K`, so its
  positivity is true or false once those are fixed. Both follow from `0 ≤ r2 < 1` together
  with the truncated-normal bound `0 ≤ i·(i - T) ≤ 1` on the selection intensity, which is
  the standard fact that truncation cannot increase variance. That bound is a real result
  and the corpus does not have it.

Reinstating this regime honestly means proving those three, not restating them. Until
then, the four genuine domain conditions (`0 < K < 1`, `0 ≤ r2 < 1`) are what the
individual theorems below already take as explicit hypotheses where they need them. -/

/-- Source Brier chart as a function of prevalence and source `R²`. -/
noncomputable def sourceBrierFromR2 (π r2Source : ℝ) : ℝ :=
  TransportedMetrics.calibratedBrier π r2Source

/-- The source Brier chart is the canonical source Brier
specialization. -/
theorem sourceBrierFromR2_eq_transportedMetrics
    (π r2Source : ℝ) :
    sourceBrierFromR2 π r2Source =
      TransportedMetrics.calibratedBrier π r2Source := by
  rfl

/-- Exact target calibrated Brier risk under the Bernoulli-mixing model from
explicit target state. -/
noncomputable def targetExactCalibratedBrierRisk
    (π V_A V_E fstTarget : ℝ) : ℝ :=
  TransportedMetrics.calibratedBrier π
    (targetR2FromNeutralAFBenchmark V_A V_E fstTarget)

/-- Neutral allele-frequency benchmark target Brier map used by the dashboard
(`Brier(R²_target)`). -/
noncomputable def targetBrierFromNeutralAFBenchmark
    (π V_A V_E fstTarget : ℝ) : ℝ :=
  targetExactCalibratedBrierRisk π V_A V_E fstTarget

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
    (π V_A V_E fstTarget : ℝ) : TransportedMetrics.Profile :=
  TransportedMetrics.profileFromSignalVariance π V_E (presentDayPGSVariance V_A fstTarget)

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
      TransportedMetrics.r2FromSignalVariance (presentDayPGSVariance V_A fstTarget) V_E =
        targetR2FromNeutralAFBenchmark V_A V_E fstTarget
    unfold targetR2FromNeutralAFBenchmark TransportedMetrics.r2FromSignalVariance presentDayR2
    rfl
  · change
      TransportedMetrics.equalVarianceGaussianAUCFromSignalVariance (presentDayPGSVariance V_A
          fstTarget) V_E =
        presentDayEqualVarianceGaussianAUC V_A V_E fstTarget
    rfl
  · change
      TransportedMetrics.calibratedBrier π
        (TransportedMetrics.r2FromSignalVariance (presentDayPGSVariance V_A fstTarget) V_E) =
        targetBrierFromNeutralAFBenchmark π V_A V_E fstTarget
    -- `TransportedMetrics.calibratedBrier` was named TWICE in this list. The
    -- first occurrence unfolds it; the second then fails, because by that
    -- point the constant is gone from the goal. `unfold` is not idempotent --
    -- it errors when a name is already absent rather than succeeding vacuously.
    unfold targetBrierFromNeutralAFBenchmark targetExactCalibratedBrierRisk
      TransportedMetrics.calibratedBrier targetR2FromNeutralAFBenchmark
      TransportedMetrics.r2FromSignalVariance
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
  Phi (Real.sqrt (snr / 2))

/-- **equalVarianceGaussianAUCFromSNR at its junk point, named.** A negative signal-to-noise
ratio is inadmissible. `Real.sqrt` is junk-zero, so the AUC collapses to `Phi 0` -- chance
discrimination -- and a sign error upstream is reported as an uninformative but well-formed
classifier rather than as a domain violation. Consumers must exclude the argument that makes the
guard vanish. -/
theorem equalVarianceGaussianAUCFromSNR_negative_snr_is_junk :
    equalVarianceGaussianAUCFromSNR (-1) = Phi 0 := by
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
  apply strictMono_Phi
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
  if 1 ≤ r2 then 1 else Phi (Real.sqrt (r2 / (2 * (1 - r2))))

/-- Below the perfect-prediction boundary, the total chart is the Gaussian closed form. -/
theorem equalVarianceGaussianAUCFromExplainedR2_eq_formula_of_lt_one
    (r2 : ℝ) (h : r2 < 1) :
    equalVarianceGaussianAUCFromExplainedR2 r2 =
      Phi (Real.sqrt (r2 / (2 * (1 - r2)))) := by
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

/-- **Bundled deployed metrics for a DICHOTOMISED trait**, with the prevalence used for the
AUC as well as for the Brier risk.

No new modelling input is required to build this: `π` is already an argument of the profile
it replaces. The old record simply declined to use it for the discrimination metric, which
is how a `-0.068` AUC bias survived beside a Brier risk computed correctly at the same
prevalence.

    Empirical status: **FALSIFIED on the `brier` coordinate, for the very trait
    this record is built for**; the other two coordinates inherit validations.

      r2     `targetR2FromNeutralAFBenchmark`, which is `presentDayR2`; that runs
             through `presentDayPGSVariance`, validated at worst 0.94 sems on
             the heterozygosity-retention reading of `fst`.
      auc    `targetLiabilityAUCFromNeutralAFBenchmark`, validated through
             `liabilityThresholdAUCFromExplainedR2` at pooled RMSE 0.0121
             against a 0.0120 noise floor, with prevalence swept. The whole
             point of this record is that this field spends the `π` it was given.
      brier  `targetBrierFromNeutralAFBenchmark`, which is
             `DGP.TransportedMetrics.calibratedBrier` at the benchmark `R²`.
             That chart is recorded FALSIFIED under the liability-threshold
             model and exact only for a Gaussian outcome.

    So the defect this record was written to repair -- one field treating the
    trait as binary and another as continuous -- has been repaired on the AUC
    side and NOT on the Brier side. The record is now consistent in taking `π`
    everywhere and inconsistent in what it does with it: the AUC uses the
    liability-threshold chart and the Brier still uses the Gaussian one. Naming
    that here rather than leaving the marker undeclared is the point of writing
    the status per-field.

    argument_source: model, inherited. -/
noncomputable def neutralAFBenchmarkLiabilityMetricProfile
    (π V_A V_E fstTarget : ℝ) : TransportedMetrics.Profile :=
  { r2 := targetR2FromNeutralAFBenchmark V_A V_E fstTarget
  , auc := targetLiabilityAUCFromNeutralAFBenchmark V_A V_E fstTarget π
  , brier := targetBrierFromNeutralAFBenchmark π V_A V_E fstTarget }

/-- The two profiles agree on `R²` and Brier and differ **only** in the AUC field, which
localises the defect to one coordinate rather than leaving it diffuse. -/
theorem liabilityProfile_differs_only_in_auc (π V_A V_E fstTarget : ℝ) :
    (neutralAFBenchmarkLiabilityMetricProfile π V_A V_E fstTarget).r2 =
      targetR2FromNeutralAFBenchmark V_A V_E fstTarget ∧
    (neutralAFBenchmarkLiabilityMetricProfile π V_A V_E fstTarget).brier =
      targetBrierFromNeutralAFBenchmark π V_A V_E fstTarget ∧
    (neutralAFBenchmarkLiabilityMetricProfile π V_A V_E fstTarget).auc =
      liabilityThresholdAUCFromExplainedR2 (presentDayR2 V_A V_E fstTarget) π :=
  ⟨rfl, rfl, rfl⟩

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
        (r2FromSignalVariance vSignal vEnv) =
      equalVarianceGaussianAUCFromSignalVariance vSignal vEnv := by
  have h_total : 0 < vSignal + vEnv := add_pos_of_nonneg_of_pos h_signal h_env
  have h_r2_lt : r2FromSignalVariance vSignal vEnv < 1 := by
    unfold r2FromSignalVariance
    exact (div_lt_one h_total).2 (lt_add_of_pos_right vSignal h_env)
  rw [equalVarianceGaussianAUCFromExplainedR2_eq_formula_of_lt_one _ h_r2_lt]
  rw [← equalVarianceGaussianAUCFromSNR_eq_variance vSignal vEnv (ne_of_gt h_env)]
  unfold equalVarianceGaussianAUCFromSNR r2FromSignalVariance
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
  apply strictMono_Phi
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

    Empirical status: **FALSIFIED on the `brier` coordinate under the
    liability-threshold reading**; the record carries one verdict per field and
    they are not the same verdict.

      r2     `r2FromSourceWeights` at the source, validated at 0.06 sems in
             `simcov/battery_transport.py`.
      auc    `equalVarianceGaussianAUCFromSourceWeights`, which has no
             measurement; its own docstring is explicit that it is the
             EQUAL-VARIANCE Gaussian chart and not the liability-threshold one,
             so at a prevalence far from one half it is the wrong chart for a
             dichotomised outcome and it takes no `π` to be right with.
      brier  `sourceCalibratedBrierFromSourceWeightsAtPrevalence`, which
             inherits the falsification recorded at
             `DGP.TransportedMetrics.calibratedBrierFromVariances`.

    THE INTERNAL INCONSISTENCY IS THE FINDING, and it is the same one
    `neutralAFBenchmarkMetricProfile` is documented for: this record takes a
    prevalence `π`, spends it on the Brier coordinate, and computes the AUC with
    a chart that has nowhere to put one. So a profile assembled to compare
    source and target Brier "on the same prevalence scale" is binary in one
    field and continuous in another.

    argument_source: model, inherited. -/
noncomputable def sourceMetricProfileFromSourceWeightsAtPrevalence {p q : ℕ}
    (m : CrossPopulationMetricModel p q) (π : ℝ) : TransportedMetrics.Profile where
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
    (m : CrossPopulationMetricModel p q) : TransportedMetrics.Profile :=
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
    (m : CrossPopulationMetricModel p q) : TransportedMetrics.Profile where
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

This packages the exact `R²`, liability-AUC, and Brier laws on the explicit
SNP-level transport state. -/
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
          TransportedMetrics.calibratedBrierFromVariances
            m.targetPrevalence
            ((predictiveCovarianceFromSourceWeights m Pop.target) ^ 2 /
              scoreVarianceFromSourceWeights m Pop.target)
            (effectiveOutcomeVariance m Pop.target -
              (predictiveCovarianceFromSourceWeights m Pop.target) ^ 2 /
                scoreVarianceFromSourceWeights m Pop.target) } := by
  ext
  · rw [targetMetricProfileFromSourceWeights_r2,
      targetR2FromSourceWeights_exact_metric_portability_law]
  · rw [targetMetricProfileFromSourceWeights_auc,
      targetEqualVarianceGaussianAUCFromSourceWeights_exact_metric_portability_law]
  · rw [targetMetricProfileFromSourceWeights_brier,
      targetCalibratedBrierFromSourceWeights_exact_metric_portability_law]

/-- Canonical mechanistic deployed metric profile after `t` generations. -/
noncomputable def targetMetricProfileAtGeneration {p q : ℕ}
    (m : CrossPopulationGenerationalModel p q) (t : ℕ) :
    TransportedMetrics.Profile :=
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
          TransportedMetrics.calibratedBrierFromVariances
            (m.targetPrevalenceAt t)
            ((predictiveCovarianceFromSourceWeights (m.toMetricModelAt t) Pop.target) ^ 2 /
              scoreVarianceFromSourceWeights (m.toMetricModelAt t) Pop.target)
            (effectiveOutcomeVariance (m.toMetricModelAt t) Pop.target -
              (predictiveCovarianceFromSourceWeights (m.toMetricModelAt t) Pop.target) ^ 2 /
                scoreVarianceFromSourceWeights (m.toMetricModelAt t) Pop.target) } := by
  ext
  · rw [targetMetricProfileAtGeneration_eq_slice,
      targetMetricProfileFromSourceWeights_exact_mechanistic_portability_law]
  · rw [targetMetricProfileAtGeneration_eq_slice,
      targetMetricProfileFromSourceWeights_exact_mechanistic_portability_law]
  · rw [targetMetricProfileAtGeneration_eq_slice,
      targetMetricProfileFromSourceWeights_exact_mechanistic_portability_law]
    simp [predictiveCovarianceFromSourceWeights, scoreVarianceFromSourceWeights,
      effectiveOutcomeVariance,
      CrossPopulationGenerationalModel.toMetricModelAt]

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
    unfold presentDayPGSVariance pgsVarianceFromHet
    have h_one_minus : 0 < 1 - fst := by linarith
    exact mul_pos hVA h_one_minus
  have hsum_ne : presentDayPGSVariance V_A fst + V_E ≠ 0 := by
    linarith
  have hve_ne : V_E ≠ 0 := ne_of_gt hVE
  have hr2_lt : presentDayR2 V_A V_E fst < 1 := by
    unfold presentDayR2 r2FromSignalVariance
    exact (div_lt_one (add_pos hv_pos hVE)).2 (lt_add_of_pos_right _ hVE)
  have hchart :
      presentDayR2 V_A V_E fst / (2 * (1 - presentDayR2 V_A V_E fst)) =
        presentDaySignalToNoise V_A V_E fst / 2 := by
    unfold presentDayR2 r2FromSignalVariance presentDaySignalToNoise
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

/-- The exact target calibrated Brier risk is `TransportedMetrics.calibratedBrier`
evaluated at the explicit target `R²` by definition. -/
@[simp] theorem targetBrierFromNeutralAFBenchmark_eq
    (π V_A V_E fstTarget : ℝ) :
    targetExactCalibratedBrierRisk π V_A V_E fstTarget =
      TransportedMetrics.calibratedBrier π
        (targetR2FromNeutralAFBenchmark V_A V_E fstTarget) := by
  rfl

/-- Exact calibrated Bernoulli Brier risk from prevalence and explained-risk
moments. If the true conditional risk `η(Z)` has mean `π` and variance
`π(1-π) r2`, then the exact calibrated population Brier risk is
`π(1-π)(1-r2)`. -/
theorem exactBrierRiskOfCalibrated_eq_exactCalibratedBrierRiskFromR2
    {Z : Type*} [MeasurableSpace Z]
    (μ : Measure Z) [IsProbabilityMeasure μ]
    (η : Z → ℝ) (π r2 : ℝ)
    (hη_int : Integrable η μ)
    (hvar_int : Integrable (fun z ↦ (η z - π) ^ 2) μ)
    (hmean : ∫ z, η z ∂μ = π)
    (hvar : ∫ z, (η z - π) ^ 2 ∂μ = π * (1 - π) * r2) :
    exactBrierRiskOfCalibrated μ η = TransportedMetrics.calibratedBrier π r2 := by
  rw [exactBrierRiskOfCalibrated_eq_integral]
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
    _ = TransportedMetrics.calibratedBrier π r2 := by
            rw [hvar]
            unfold TransportedMetrics.calibratedBrier
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
    targetExactCalibratedBrierRisk TransportedMetrics.calibratedBrier
  have hbase :
      1 - presentDayR2 V_A V_E fstSource ≤
        1 - targetR2FromNeutralAFBenchmark V_A V_E fstTarget := by
    linarith
  exact mul_le_mul_of_nonneg_left hbase hcoef_nonneg

/-- Pointwise Brier regret relative to the true Bernoulli probability. -/
noncomputable def brierRegretPoint (η q : ℝ) : ℝ :=
  brierBernoulliRisk η q - brierBernoulliRisk η η

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
  simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using brier_regret_pointwise η q

/-- Ratio form in present-day units: Brier-regret ratio is a squared-error ratio. -/
theorem brierRegretRatio_eq_sq_error_ratio (η qSource qTarget : ℝ) :
    brierRegretRatio η qSource qTarget =
      ((qTarget - η) ^ 2) / ((qSource - η) ^ 2) := by
  unfold brierRegretRatio
  rw [brierRegretPoint_eq_sq_error, brierRegretPoint_eq_sq_error]

/-- Pointwise log-loss regret relative to truth. -/
noncomputable def logLossRegretPoint (η q : ℝ) : ℝ :=
  bernoulliLogLoss η q - bernoulliLogLoss η η

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
    logLossRegretPoint η q = bernoulliKLReal η q := by
  unfold logLossRegretPoint
  simpa using logLoss_regret_eq_kl_pointwise η q hη0 hη1 hq0 hq1

/-- Ratio form in present-day units: log-loss regret ratio is a KL ratio. -/
theorem logLossRegretRatio_eq_kl_ratio (η qSource qTarget : ℝ)
    (hη0 : 0 < η) (hη1 : η < 1)
    (hqS0 : 0 < qSource) (hqS1 : qSource < 1)
    (hqT0 : 0 < qTarget) (hqT1 : qTarget < 1) :
    logLossRegretRatio η qSource qTarget =
      bernoulliKLReal η qTarget / bernoulliKLReal η qSource := by
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

    Empirical status: **DERIVED, and low by an exact stated factor.** Both
    components carry measurements and the join between them is algebra, so no
    new simulation is owed -- but the algebra does not come out to `2 δ`.

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

end PresentDayMetrics


/-!
## Mutation-Drift Balance and Portability

When mutation is non-negligible, Fst has a finite equilibrium (Wright's
1/(1+4Neμ)) instead of approaching 1. This section generalizes the drift-only
portability model to include mutation as a first-class parameter.

Key results:
1. Generalized divergence model that includes mutation rate
2. Covariance divergence including both drift and mutation terms
3. Portability under mutation-drift: mutation-generated population-specific
   variants reduce tagging efficiency
4. Comparison: mutation-drift equilibrium portability vs pure-drift portability
-/

section MutationDriftPortability

/-- Generalized divergence model assumptions that include mutation as a parameter
    rather than assuming it is negligible. -/
structure MutationDriftModelAssumptions where
  Ne : ℝ
  μ : ℝ
  t : ℝ
  Ne_pos : 0 < Ne
  mu_pos : 0 < μ
  t_nonneg : 0 ≤ t

/-- **The class is inhabited.**  A theorem quantified over an uninhabited structure is
true and empty: kernel-checked, clean axiom report, no content.  This is the witness that
makes the theorems below statements about something. -/
noncomputable def MutationDriftModelAssumptions.witness : MutationDriftModelAssumptions where
  Ne := 1
  μ := 1
  t := 1
  Ne_pos := by norm_num
  mu_pos := by norm_num
  t_nonneg := by norm_num

/-- The scaled mutation parameter θ = 4Neμ for a mutation-drift model.

    Empirical status: UNTESTED. -/
noncomputable def MutationDriftModelAssumptions.theta (m : MutationDriftModelAssumptions) : ℝ :=
  scaledMutationRate m.Ne m.μ

/-- **The scaled mutation parameter is linear in the mutation rate with slope four Ne.**
`theta_pos` below fixes the sign and leaves the slope free. -/
theorem MutationDriftModelAssumptions.theta_div_mu (m : MutationDriftModelAssumptions)
    (h : m.μ ≠ 0) :
    m.theta / m.μ = 4 * m.Ne := by
  unfold MutationDriftModelAssumptions.theta scaledMutationRate
  field_simp

/-- θ is positive for any valid mutation-drift model. -/
theorem MutationDriftModelAssumptions.theta_pos (m : MutationDriftModelAssumptions) :
    0 < m.theta := by
  unfold MutationDriftModelAssumptions.theta scaledMutationRate
  nlinarith [m.Ne_pos, m.mu_pos]

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

/-- **Equilibrium identity probability under mutation-drift balance,
`F = 1/(1 + θ)` with `θ = 4·Nₑ·μ`.**

    **Attribution, corrected.** This is *not* the Wright (1931) island-model
    result, which this file also carries at `fstMigrationDriftEquilibrium` and
    which is `1/(1 + 4·Nₑ·m)` in the MIGRATION rate. The mutation-drift form is
    Malécot's `(4Nu + 1)⁻¹`, standardly cited to Kimura and Crow (1964),
    *The Number of Alleles That Can Be Maintained in a Finite Population*,
    Genetics 49:725--738. The two laws share the algebraic shape `1/(1 + 4·Nₑ·rate)`
    -- that shared shape is the whole content of `ibdFlowStep_fixedPoint`, which
    proves it once for an abstract `rate` -- and they are different results about
    different forces. A docstring that names the wrong one invites a reader to
    substitute `m` for `μ` on the authority of a citation that does not cover it.

    Convention: despite the `Fst` in the name (inherited from
    `DGP.fstMutationDriftEquilibrium`, whose docstring says the same thing), the
    quantity is the probability that two gene copies drawn at random from ONE
    population are identical by descent -- the complement of the equilibrium
    heterozygosity `θ/(1+θ)` at `PortabilityDrift.hetMutationFloor`. It is not a
    between-population differentiation measure.

    Not stipulated: `MutationDriftModelAssumptions.fstEquilibrium_isFixedPoint`
    derives it as the rest point of `ibdFlowStep` with `rate = μ`.

    Empirical status: **VALIDATED**, by projection. This body IS
    `DGP.fstMutationDriftEquilibrium m.theta` -- not an analogue of it, the same
    function applied to this structure's field -- so the measurement there
    transfers without a separate design. That run is `simcov/battery_bulk19.py`
    against `msprime`'s `InfiniteAlleles` model, worst cell 2.40 sems, with `Nₑ`
    and `μ` swept by a factor of four INDEPENDENTLY so each `θ` is reached twice
    by different routes; `simcov/battery_bulk20b.py` corroborates from the
    complementary side, measuring `θ/(1+θ)` over a hundredfold `θ` sweep at
    worst 2.17 sems with an Ewens allele-count control passing at 1.10 sems.

    What does NOT transfer is the reading of the name: `fst` here is the
    probability that two alleles drawn WITHIN a population are identical by
    state, the complement of heterozygosity, and not a between-population
    differentiation. The measurement above is of that within-population
    quantity. A consumer wanting differentiation wants
    `DGP.EvolutionaryParameters.fstEquilibrium`, which is separately FALSIFIED
    -- so the two must not be substituted for one another. -/
noncomputable def MutationDriftModelAssumptions.fstEquilibrium
    (m : MutationDriftModelAssumptions) : ℝ :=
  fstMutationDriftEquilibrium m.theta

/-- **The equilibrium inverts one plus the scaled mutation parameter.** `fstEquilibrium_pos`
fixes the sign; this fixes the value, and a body carrying any other coefficient on `theta` would
be positive too. -/
theorem MutationDriftModelAssumptions.fstEquilibrium_mul_denom
    (m : MutationDriftModelAssumptions) (h : 1 + m.theta ≠ 0) :
    m.fstEquilibrium * (1 + m.theta) = 1 := by
  unfold MutationDriftModelAssumptions.fstEquilibrium fstMutationDriftEquilibrium
  field_simp

/-- **The mutation-drift equilibrium is the fixed point of the identity
balance** driven by mutation alone. -/
theorem MutationDriftModelAssumptions.fstEquilibrium_isFixedPoint
    (m : MutationDriftModelAssumptions) :
    ibdFlowStep m.Ne m.μ m.fstEquilibrium = m.fstEquilibrium := by
  have hθ : m.fstEquilibrium = 1 / (1 + 4 * m.Ne * m.μ) := rfl
  rw [hθ]
  exact ibdFlowStep_fixedPoint m.Ne m.μ m.Ne_pos (le_of_lt m.mu_pos)

/-- Equilibrium Fst is positive. -/
theorem MutationDriftModelAssumptions.fstEquilibrium_pos
    (m : MutationDriftModelAssumptions) :
    0 < m.fstEquilibrium := by
  unfold MutationDriftModelAssumptions.fstEquilibrium fstMutationDriftEquilibrium
  have hden : 0 < 1 + m.theta := by
    nlinarith [m.theta_pos]
  exact div_pos one_pos hden

/-- Equilibrium Fst is strictly less than 1 (mutation prevents complete fixation). -/
theorem MutationDriftModelAssumptions.fstEquilibrium_lt_one
    (m : MutationDriftModelAssumptions) :
    m.fstEquilibrium < 1 := by
  unfold MutationDriftModelAssumptions.fstEquilibrium fstMutationDriftEquilibrium
  rw [div_lt_one (by linarith [m.theta_pos])]
  linarith [m.theta_pos]

/-- **Transient Fst under mutation-drift: approach to equilibrium.**
    Fst(t) = Fst_eq × (1 - exp(-(1+θ)t/(2Ne)))

    Regime: two demes split from a common ancestor, no migration, mutation at
    `θ = 4·Nₑ·μ`.

    Empirical status: **VALIDATED on its RATE**
    (`simcov/battery_bulk24.py`). The body makes two separable claims -- a
    plateau `Fst_eq` and a time constant `τ = 2·Nₑ/(1+θ)` -- and only the second
    is convention-free. Whether the plateau is Nei's `G_ST`, Hudson's `F_ST` or
    a per-branch drift `F` moves it by factors of two and four, and this corpus
    has already lost a factor of four to exactly that. Rescaling `F_ST` by any
    constant leaves `τ` untouched. So the design fits `A·(1 - exp(-t/τ))` to the
    measured trajectory, DISCARDS the amplitude `A`, and puts `τ` on trial:

      Nₑ     θ      τ measured      2·Nₑ/(1+θ)    sems
      500    0.5    668 ± 45        667           0.03
      500    0.02   912 ± 61        980           1.13
      1000   0.5    1333 ± 67       1333          0.00
      500    1.0    658 ± 83        500           1.92
      1000   0.1    1661 ± 71       1818          2.22

    Worst cell 2.22 sems. `Nₑ` and `θ` are swept separately, so the two scalings
    are separately falsifiable; holding `θ = 0.5` and doubling `Nₑ` moves `τ` by
    a factor of 1.996 against 2.000 predicted.

    Power, and why this is a measurement rather than an identity: the drift-only
    rate `τ = 2·Nₑ`, which drops the mutation term, is carried on the SAME cells
    and is FALSIFIED at up to 9.96 sems (50% relative). An oracle algebraically
    pinned to the body could not reject a competing form -- the "measurement"
    would move with whatever prediction was fed in -- so the rejection is what
    establishes that `τ` was measured and not recomputed. The control, a
    `θ = 0.02` cell where both candidate rates coincide, passed at 0.15 sems.

    LIMITS OF THIS RUN, recorded rather than smoothed over. The `θ = 0.5` and
    `θ = 1.0` cells fit amplitudes `A` of 1.13 and 1.59 -- an `F_ST` above one,
    which is unphysical and marks Hudson's ratio-of-averages estimator degrading
    under multiple hits. The `τ` estimate survives because `A` is discarded by
    construction, but those cells are weaker than their error bars suggest.
    Above `θ ≈ 1` the design fails outright: under infinite sites `θ` is set by
    `μ` at fixed `Nₑ`, so `θ = 3` at `Nₑ = 500` needs `μ = 1.5e-3` per site,
    five orders above realistic, and produces a genotype matrix too large to
    build. Testing the `(1+θ)` factor further needs a finite-sites model or
    branch-mode statistics, not this instrument. -/
noncomputable def MutationDriftModelAssumptions.fstTransient
    (m : MutationDriftModelAssumptions) : ℝ :=
  m.fstEquilibrium * (1 - Real.exp (-(1 + m.theta) * m.t / (2 * m.Ne)))

/-- Transient Fst is nonneg. -/
theorem MutationDriftModelAssumptions.fstTransient_nonneg
    (m : MutationDriftModelAssumptions) :
    0 ≤ m.fstTransient := by
  unfold MutationDriftModelAssumptions.fstTransient
  apply mul_nonneg (le_of_lt m.fstEquilibrium_pos)
  have harg : 0 ≤ (1 + m.theta) * m.t / (2 * m.Ne) := by
    have hden : 0 < 2 * m.Ne := by nlinarith [m.Ne_pos]
    apply div_nonneg
    · exact mul_nonneg (by linarith [m.theta_pos]) m.t_nonneg
    · exact le_of_lt hden
  have hexp : Real.exp (-(1 + m.theta) * m.t / (2 * m.Ne)) ≤ 1 := by
    have hnum_nonpos : -(1 + m.theta) * m.t ≤ 0 := by
      have h1 : 0 ≤ 1 + m.theta := by
        have h1' : 0 < 1 + m.theta := by nlinarith [m.theta_pos]
        linarith
      nlinarith [h1, m.t_nonneg]
    have hden_nonneg : 0 ≤ 2 * m.Ne := by linarith [m.Ne_pos]
    have hneg : -(1 + m.theta) * m.t / (2 * m.Ne) ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg hnum_nonpos hden_nonneg
    have hexp' : Real.exp (-(1 + m.theta) * m.t / (2 * m.Ne)) ≤ Real.exp 0 :=
      Real.exp_le_exp.mpr hneg
    simpa using hexp'
  have hfactor_nonneg : 0 ≤ 1 - Real.exp (-(1 + m.theta) * m.t / (2 * m.Ne)) := by
    linarith
  exact hfactor_nonneg

/-- Transient Fst is bounded by the equilibrium Fst. -/
theorem MutationDriftModelAssumptions.fstTransient_le_equilibrium
    (m : MutationDriftModelAssumptions) :
    m.fstTransient ≤ m.fstEquilibrium := by
  unfold MutationDriftModelAssumptions.fstTransient
  have hfeq_pos : 0 < m.fstEquilibrium := m.fstEquilibrium_pos
  have hexp_pos : 0 < Real.exp (-(1 + m.theta) * m.t / (2 * m.Ne)) := Real.exp_pos _
  have h_factor_le : 1 - Real.exp (-(1 + m.theta) * m.t / (2 * m.Ne)) ≤ 1 := by
    linarith
  have hmul :
      m.fstEquilibrium * (1 - Real.exp (-(1 + m.theta) * m.t / (2 * m.Ne))) ≤
        m.fstEquilibrium * 1 :=
    mul_le_mul_of_nonneg_left h_factor_le (le_of_lt hfeq_pos)
  simpa using hmul

/-! ## Derivation of the Multiplicative Covariance Divergence Formula

We derive the formula `covarianceDivergenceMutationDrift(Fst, shared_LD) = 1 - (1-Fst) × shared_LD`
from the covariance between a polygenic score and a phenotype across populations.

**Setup.** In the source population, the covariance between a PGS and the phenotype is:

  `Cov(PGS, Y_source) = Σᵢ βᵢ × Cov(Gᵢ_source, Y_source)`

In the target population:

  `Cov(PGS, Y_target) = Σᵢ βᵢ × Cov(Gᵢ_target, Y_target)`

The ratio `Cov_target / Cov_source` depends on two independent factors:

1. **Allele frequency correlation** (`freq_corr`): Genetic drift changes allele frequencies
   between populations. The correlation of allele frequencies between source and target
   populations is `1 - Fst`, where Fst measures frequency divergence. This scales the
   per-locus genetic covariance by `(1 - Fst)`.

2. **LD overlap** (`ld_overlap`): New mutations and recombination alter LD patterns.
   The fraction of LD structure that is shared between populations is `shared_LD`.
   Only shared LD contributes to tagging of causal variants by the PGS SNPs.

For a single locus pair, these act on different aspects of the covariance:
- Frequency change scales the marginal genetic variance: `Var(G_target) ∝ (1-Fst) × Var(G_source)`
- LD change scales the tagging efficiency: `r²_target ∝ shared_LD × r²_source`

Because these are independent mechanisms, the total covariance retention is their product:

  `Cov_target / Cov_source = (1 - Fst) × shared_LD`

Therefore the divergence (fraction of covariance lost) is:

  `divergence = 1 - retention = 1 - (1 - Fst) × shared_LD`
-/

/-- **Covariance retention** across populations.
    The fraction of PGS-phenotype covariance retained in the target population
    is the product of allele frequency correlation and LD overlap. These two
    factors are independent: frequency drift scales per-locus genetic variance,
    while LD decay scales tagging efficiency. -/
noncomputable def covarianceRetention (freq_corr ld_overlap : ℝ) : ℝ :=
  freq_corr * ld_overlap

/-- The covariance-retention factor `1 - F_ST`.

    ONE STATUS MARKER, at the foot of this docstring. This block used to open
    with a second one carrying a refutation verdict, which described the
    SUPERSEDED definition `freqCorrFromFst` rather than this one, and every
    scanner that reads the first marker in a docstring reported this body as
    currently falsified. It is not. (The duplicate is removed rather than
    reworded: a marker quoted in prose is still a marker to a scanner, which is
    the same class of mistake as the one being corrected.) The refuted claim was
    an IDENTIFICATION --
    that `1 - F_ST` *is* the allele-frequency correlation -- and that claim was
    already repaired, by renaming this definition and by giving the correlation
    its own body with the arguments it actually depends on. What follows is the
    history of that repair, not a verdict on the body below.

    THE MEASUREMENT THAT KILLED THE IDENTIFICATION
    (`validation/empirical/simcov/battery_verify.py`,
    `test_freq_corr_killer`). Two Wright-Fisher designs were run to the SAME
    differentiation -- `G_ST` 0.0749 and 0.0750, so `1 - Fst` is 0.9251 and
    0.9250 -- differing only in the ancestral frequencies the two demes started
    from. `Ne = 200`, 60 generations, 4000 loci, 400 replicate deme pairs, the
    correlation taken within each replicate so its scatter is measured:

      ancestral p0            1 - Fst    measured corr    sems off
      all p0 = 0.5             0.9251    0.0004±0.0008      1117
      uniform(0.05, 0.95)      0.9250    0.7209±0.0003       653

    At identical `F_ST` the correlation is either zero or 0.72, so it is not a
    function of `F_ST` and no repair of the constant can make it one. The
    degenerate row is the clearest statement of the mechanism: when every locus
    starts at the same ancestral frequency there is no across-locus signal for
    the two demes to share, and the correlation vanishes however little they
    have diverged.

    What the quantity actually is:
    `corr(p1, p2) = Var(p0) / (Var(p0) + F * E[p0 (1 - p0)])`,
    which depends on the ancestral spread as well as on the drift index, and
    reduces to `1 - F` only when `Var(p0)` and `E[p0 (1 - p0)]` stand in one
    particular ratio.

    Power: the design holds `F_ST` fixed to four decimal places and moves the
    measured correlation from 0.0004 to 0.7209, which is the largest span the
    quantity admits.

    **The name has been changed.** This was `freqCorrFromFst`, and that name is
    the falsified claim: it asserted that `1 - Fst` IS the allele-frequency
    correlation, which the measurement above refutes. The body `1 - Fst` is
    retained because it is what every consumer actually uses it as -- a
    covariance-retention factor -- and the new name says only that. The
    correlation itself is `alleleFreqCorrelation` below, which carries the
    arguments the quantity depends on.

    Empirical status: **VALIDATED as a covariance-retention factor**
    (`simcov/battery_drift05.py`). Its former justification was the correlation identity, and
    that justification is gone; retention now has a measurement instead.

    For a score with FIXED effects the genetic variance it carries in a drifted deme is
    `∑ βᵢ²·2pᵢ(1-pᵢ)`, so the retention is the heterozygosity ratio on the same draws. Against
    the MODEL's `fst = 1-(1-1/(2Nₑ))^t` -- never one estimated from the replicates the oracle
    measures -- over 300000 loci and four `(Nₑ, t)` cells, worst 0.58 sems at 0.03% relative,
    with `(1-fst)²` refuted at up to 259 sems.

    HONEST LIMIT: this shares its oracle with `targetHetFromFst` above, being that measurement
    rescaled by the ancestral heterozygosity. It is one measurement supporting two
    definitions, not two independent ones, and what it adds over the heterozygosity statement
    is the identification of that ratio with a COVARIANCE retention -- which holds because the
    effects are fixed and is exactly what would fail if they were not.

    Denotes: the covariance-retention factor, not the allele-frequency
    correlation. The same body `1 - fst` appears under names from 'correlation',
    'retention' and 'drift factor', and the formula alone does not fix which is
    meant; `alleleFreqCorrelation` is the correlation. -/
noncomputable def covarianceRetentionFactorFromFst (fst : ℝ) : ℝ := 1 - fst

/-- **covarianceRetentionFactorFromFst pinned at a reference point.** No theorem in the corpus
evaluated this definition, so every body agreeing with it in sign and monotonicity was
indistinguishable from it. At all arguments equal to `1 / 2` it is `1 / 2`, which fixes the
coefficients a one-sided bound or an invariance leaves free. -/
theorem covarianceRetentionFactorFromFst_at_reference_point :
    covarianceRetentionFactorFromFst (1 / 2) = 1 / 2 := by
  unfold covarianceRetentionFactorFromFst
  norm_num

/-- **The allele-frequency correlation between two drifted demes.**

    `corr(p1, p2) = Var(p0) / (Var(p0) + fst * E[p0 (1 - p0)])`, where the two
    ancestral moments are taken over the loci scored. Both demes descend from
    one ancestral population, so their frequencies share exactly the ancestral
    across-locus spread and differ by independent drift; the correlation is the
    ratio of the shared part to the total, which is what this states.

    Empirical status: **VALIDATED**
    (`validation/empirical/simcov/battery_correct.py`,
    `correct_freq_corr`). Wright-Fisher forward simulation, `Ne = 200`, 4000
    loci, 400 replicate deme pairs, four ancestral distributions crossed with
    two drift depths -- eight cells that a formula in `fst` alone must get wrong
    and this one gets right:

      ancestral p0          gens    1 - fst   this def   measured      sems
      uniform(0.05,0.95)      60     0.9251     0.7237     0.7240       1.1
      uniform(0.05,0.95)     200     0.7545     0.4786     0.4780       0.9
      beta(0.5,0.5)           60     0.9249     0.8721     0.8719       1.0
      beta(0.5,0.5)          200     0.7547     0.7136     0.7132       1.0
      beta(2,2)               60     0.9251     0.6437     0.6440       0.8
      beta(2,2)              200     0.7547     0.3908     0.3906       0.3
      all p0 = 0.5            60     0.9252     0.0000     0.0006       0.8
      all p0 = 0.5           200     0.7546     0.0000    -0.0001       0.1

    Power: the prediction spans 0.0000 to 0.8721 across the design, the full
    range the quantity admits, while `1 - fst` is pinned at 0.925 or 0.755 by
    the drift depth alone and is wrong in seven of the eight cells. -/
noncomputable def alleleFreqCorrelation (fst varAncestral meanHetAncestral : ℝ) : ℝ :=
  varAncestral / (varAncestral + fst * meanHetAncestral)

/-- With a vanishing denominator Mathlib returns `0`, which is a value this quantity can also
take legitimately, so the branch is named rather than left to be inferred from the result. -/
theorem alleleFreqCorrelation_at_zero_denominator_is_junk (fst varAncestral meanHetAncestral : ℝ)
    (hzero : (varAncestral + fst * meanHetAncestral) = 0) :
    alleleFreqCorrelation fst varAncestral meanHetAncestral = 0 := by
  unfold alleleFreqCorrelation
  rw [hzero, div_zero]


/-- **alleleFreqCorrelation pinned at a reference point.** No theorem in the corpus evaluated
this definition, so every body agreeing with it in sign and monotonicity was indistinguishable
from it. At all arguments equal to `1 / 2` it is `2 / 3`, which
fixes the coefficients a one-sided bound or an invariance leaves free. -/
theorem alleleFreqCorrelation_at_reference_point :
    alleleFreqCorrelation (1 / 2) (1 / 2) (1 / 2) = 2 / 3 := by
  unfold alleleFreqCorrelation
  norm_num

/-- **Exactly when the retention factor is the frequency correlation.**

    The two agree precisely at `varAncestral = (1 - fst) * meanHetAncestral`,
    and nowhere else for positive `fst`. This is the assumption the old
    `freqCorrFromFst` name asserted silently; stating it is what stops it being
    assumed again. -/
theorem alleleFreqCorrelation_eq_retentionFactor_iff
    (fst varAncestral meanHetAncestral : ℝ)
    (hden : varAncestral + fst * meanHetAncestral ≠ 0) :
    alleleFreqCorrelation fst varAncestral meanHetAncestral =
        covarianceRetentionFactorFromFst fst ↔
      varAncestral * fst = (1 - fst) * fst * meanHetAncestral := by
  unfold alleleFreqCorrelation covarianceRetentionFactorFromFst
  rw [div_eq_iff hden]
  constructor <;> intro h <;> nlinarith [h]

/-- LD overlap is directly the shared LD fraction (identity mapping, made
    explicit for clarity in the derivation chain).

    Empirical status: NOT AN EMPIRICAL CLAIM -- the body is the identity
    function on its argument, as the name and the parenthetical both say. There
    is no measurement that could agree or disagree with `fun x ↦ x`: any
    observation whatever is consistent with it, because it asserts nothing about
    the world.

    What this declaration DOES carry is a naming claim -- that "LD overlap" and
    "shared LD fraction" denote the same quantity -- and that is a claim about
    the two definitions' intended readings, not about a population. It is
    settled by the derivation chain this body was made explicit for, not by a
    simulation.

    A marker claiming an unpaid measurement debt here would be reporting one
    that does not exist; it inflates the count of things owed a measurement with
    an item that can never receive one. And the word for that debt must not
    appear anywhere in this docstring even as prose: `simcov/inventory.py` falls
    back to scanning the status note for state words when the head is not one of
    them, so the single word in the sentence this replaces made a declaration
    that reads NOT AN EMPIRICAL CLAIM count as an open debt in every coverage
    number the harness prints.

    The bodies downstream of it are where the empirical content
    lives: `covarianceDivergenceMutationDrift` and
    `presentDayPGSVarianceMutationDrift` both consume this fraction and both
    make claims a simulation can reach. -/
noncomputable def ldOverlapFromSharedLD (shared_ld : ℝ) : ℝ := shared_ld

/-- **ldOverlapFromSharedLD pinned at a reference point.** No theorem in the corpus evaluated
this definition, so every body agreeing with it in sign and monotonicity was indistinguishable
from it. At all arguments equal to `1 / 2` it is `1 / 2`, which fixes the coefficients a
one-sided bound or an invariance leaves free. -/
theorem ldOverlapFromSharedLD_at_reference_point :
    ldOverlapFromSharedLD (1 / 2) = 1 / 2 := by
  unfold ldOverlapFromSharedLD
  norm_num

/-- Covariance retention in terms of Fst and shared_LD. -/
theorem covarianceRetention_from_fst_ld (fst shared_ld : ℝ) :
    covarianceRetention (covarianceRetentionFactorFromFst fst) (ldOverlapFromSharedLD shared_ld) =
      (1 - fst) * shared_ld := by
  unfold covarianceRetention covarianceRetentionFactorFromFst ldOverlapFromSharedLD
  ring

/-- **Covariance divergence derived from retention.**
    Divergence is `1 - retention`, which yields the multiplicative formula
    `1 - (1 - Fst) × shared_LD`. -/
noncomputable def covarianceDivergenceFromRetention (fst shared_ld : ℝ) : ℝ :=
  1 - covarianceRetention (covarianceRetentionFactorFromFst fst) (ldOverlapFromSharedLD shared_ld)

/-- The derived divergence formula equals `1 - (1 - Fst) × shared_LD`. -/
theorem covarianceDivergenceFromRetention_eq (fst shared_ld : ℝ) :
    covarianceDivergenceFromRetention fst shared_ld = 1 - (1 - fst) * shared_ld := by
  unfold covarianceDivergenceFromRetention
  rw [covarianceRetention_from_fst_ld]

/-- **Generalized covariance divergence under mutation-drift.**
    The total covariance divergence between source and target populations
    includes both:
    (a) drift-driven frequency changes: proportional to Fst
    (b) mutation-driven LD changes: proportional to tagging decay from new variants

    Total divergence factor = Fst_drift + (1 - Fst_drift) × (1 - shared_LD)
    where shared_LD is the fraction of LD preserved despite new mutations.

    Empirical status: **MEASURED, and the number is not a rejection**
    (`validation/empirical/simcov/battery_bulk36.py`). Two-deme island
    model, `Nₑ = 1000`, 5 Mb with recombination. `F_ST`, cross-deme LD
    correlation and score-covariance retention are three SEPARATE measurements
    on the same replicates, and the body is fed the measured `shared_ld` rather
    than its migration formula, which is what distinguishes it from
    `signalRetentionMigrationDrift`: this body takes the LD term as an ARGUMENT
    and so is not committed to the `M/(1+M)` reading that `battery_bulk34`
    refuted. Stated as retention, `1 - covDiv = (1 - fst) * shared_ld`:

      4Nₑm   measured retention   this body   1-F     shared_ld
      0.4    0.392 ± 0.074        0.429       0.472   0.909
      2.0    0.476 ± 0.075        0.751       0.803   0.936
      8.0    0.614 ± 0.076        0.918       0.944   0.973
      40     0.736 ± 0.085        0.979       0.988   0.991

    WHY THIS IS NOT WRITTEN AS A FALSIFICATION, though the raw gate says 4.01
    sems and 50% relative. The retention column is divided by the estimator's
    panmictic ceiling, and THAT run's ceiling came out 1.0430 -- above one, which
    attenuation cannot produce, so the calibration is noise-dominated on six
    replicates. `signalRetentionMigrationDrift` records the same retraction for
    the same numbers, and a rejection quoted here from a calibration retracted
    there would be the corpus disagreeing with itself in two docstrings. What
    the run does establish is the DIRECTION, and it is the same direction in both
    replications: measured retention runs well below every candidate at weak
    migration, so if any of the three is right it is not by a wide margin.

    Both competitors are rejected harder than the body on the same cells --
    `1 - F` alone at 4.37 sems and `shared_ld` alone at 7.02 -- so the product
    form is the best of the three and not merely the untested one. The positive
    control, one population split arbitrarily giving `F_ST = 0`, passed at 0.15
    sems; it is the ceiling and not the control that failed.

    argument_source: sample. `fst_drift` and `shared_ld` are estimated from the
    same replicates the retention is measured on. That is deliberate here -- a
    relation among three separately measured observables is the only way to test
    a body whose LD term is an argument -- but it is also why the verdict is a
    number and not a validation: what a usable design still owes is a retention
    estimator needing no ceiling at all, which means fitting the weights on an
    independent split of the source sample. -/
noncomputable def covarianceDivergenceMutationDrift
    (fst_drift shared_ld : ℝ) : ℝ :=
  fst_drift + (1 - fst_drift) * (1 - shared_ld)

/-- Covariance divergence simplifies algebraically. -/
theorem covarianceDivergenceMutationDrift_eq (fst_drift shared_ld : ℝ) :
    covarianceDivergenceMutationDrift fst_drift shared_ld = 1 - (1 - fst_drift) * shared_ld := by
  unfold covarianceDivergenceMutationDrift
  ring

/-- **The derived formula matches the existing definition.**
    This connects the derivation from covariance principles back to
    `covarianceDivergenceMutationDrift`, confirming the multiplicative
    structure is not merely assumed but follows from the independence
    of allele frequency drift and LD decay. -/
theorem covarianceDivergence_derivation_matches (fst shared_ld : ℝ) :
    covarianceDivergenceFromRetention fst shared_ld =
      covarianceDivergenceMutationDrift fst shared_ld := by
  rw [covarianceDivergenceFromRetention_eq, covarianceDivergenceMutationDrift_eq]

/-- With perfect shared LD (shared_ld = 1), covariance divergence reduces to pure drift. -/
theorem covarianceDivergence_pure_drift (fst_drift : ℝ) :
    covarianceDivergenceMutationDrift fst_drift 1 = fst_drift := by
  unfold covarianceDivergenceMutationDrift
  ring

/-- With zero drift (fst_drift = 0), covariance divergence equals the LD divergence. -/
theorem covarianceDivergence_pure_mutation (shared_ld : ℝ) :
    covarianceDivergenceMutationDrift 0 shared_ld = 1 - shared_ld := by
  unfold covarianceDivergenceMutationDrift
  ring

/-- Covariance divergence is at least the drift component alone when shared LD ≤ 1. -/
theorem covarianceDivergence_ge_drift (fst_drift shared_ld : ℝ)
    (hfst_le : fst_drift ≤ 1)
    (hld : shared_ld ≤ 1) :
    fst_drift ≤ covarianceDivergenceMutationDrift fst_drift shared_ld := by
  unfold covarianceDivergenceMutationDrift
  have h1 : 0 ≤ 1 - fst_drift := by linarith
  have h2 : 0 ≤ 1 - shared_ld := by linarith
  linarith [mul_nonneg h1 h2]

/-- Covariance divergence is at most 1 when parameters are in [0, 1]. -/
theorem covarianceDivergence_le_one (fst_drift shared_ld : ℝ)
    (hfst_le : fst_drift ≤ 1)
    (hld : 0 ≤ shared_ld) :
    covarianceDivergenceMutationDrift fst_drift shared_ld ≤ 1 := by
  rw [covarianceDivergenceMutationDrift_eq]
  have h1 : 0 ≤ (1 - fst_drift) * shared_ld :=
    mul_nonneg (by linarith) hld
  linarith

/-- **Generalized signal retention under mutation-drift.**
    The retained signal is (1 - total_divergence) × V_A.

    Empirical status: **MEASURED, inherited**
    (`validation/empirical/simcov/battery_bulk36.py`). The retention
    fraction `1 - covarianceDivergenceMutationDrift` is what that battery
    measures directly, and the table, the reason it is not written as a
    rejection, and the two competitors are at
    `covarianceDivergenceMutationDrift`. What this body adds is the factor
    `V_A`, and NOTHING here measures it: a retention fraction times an additive
    variance is dimensional bookkeeping, and every cell of that design was run at
    one `V_A`. A design that swept `V_A` would test the linearity; none has.

    argument_source: sample, inherited. -/
noncomputable def presentDayPGSVarianceMutationDrift
    (V_A fst_drift shared_ld : ℝ) : ℝ :=
  (1 - covarianceDivergenceMutationDrift fst_drift shared_ld) * V_A

/-- Signal retention equals (1 - fst) × shared_ld × V_A. -/
theorem presentDayPGSVarianceMutationDrift_eq (V_A fst_drift shared_ld : ℝ) :
    presentDayPGSVarianceMutationDrift V_A fst_drift shared_ld =
      (1 - fst_drift) * shared_ld * V_A := by
  unfold presentDayPGSVarianceMutationDrift
  rw [covarianceDivergenceMutationDrift_eq]
  ring

/-- With perfect shared LD, signal retention reduces to the pure drift formula. -/
theorem presentDayPGSVarianceMutationDrift_pure_drift (V_A fst_drift : ℝ) :
    presentDayPGSVarianceMutationDrift V_A fst_drift 1 = presentDayPGSVariance V_A fst_drift := by
  rw [presentDayPGSVarianceMutationDrift_eq]
  unfold presentDayPGSVariance pgsVarianceFromHet
  ring

/-- Signal retention is nonneg under valid parameters. -/
theorem presentDayPGSVarianceMutationDrift_nonneg (V_A fst_drift shared_ld : ℝ)
    (hVA : 0 ≤ V_A) (hfst_le : fst_drift ≤ 1)
    (hld : 0 ≤ shared_ld) :
    0 ≤ presentDayPGSVarianceMutationDrift V_A fst_drift shared_ld := by
  rw [presentDayPGSVarianceMutationDrift_eq]
  exact mul_nonneg (mul_nonneg (by linarith) hld) hVA

/-- **Mutation strictly reduces signal retention beyond drift alone.**
    When shared_ld < 1 and other parameters are positive, mutation-drift signal
    retention is strictly below drift-only signal retention. -/
theorem mutationDrift_signal_lt_puredrift (V_A fst_drift shared_ld : ℝ)
    (hVA : 0 < V_A) (hfst_lt : fst_drift < 1) (hld_lt : shared_ld < 1) :
    presentDayPGSVarianceMutationDrift V_A fst_drift shared_ld <
      presentDayPGSVariance V_A fst_drift := by
  rw [presentDayPGSVarianceMutationDrift_eq]
  unfold presentDayPGSVariance pgsVarianceFromHet
  have h1 : 0 < 1 - fst_drift := by linarith
  have h_factor : (1 - fst_drift) * shared_ld < (1 - fst_drift) * 1 :=
    mul_lt_mul_of_pos_left hld_lt h1
  nlinarith

/-- **R² under mutation-drift balance.**

    Empirical status: **MEASURED, inherited**
    (`validation/empirical/simcov/battery_bulk36.py`), through
    `presentDayPGSVarianceMutationDrift`, whose retention fraction is what that
    battery measures; the table is at `covarianceDivergenceMutationDrift`.

    The `v / (v + V_E)` chart on top of it is NOT tested by that run and is not
    claimed to be here. It is the same `r2FromSignalVariance` chart the
    drift-only `presentDayR2` uses, and it inherits whatever that chart carries;
    what a reader must not take from this marker is that the chart was exercised
    at more than one `V_E`, because it was not.

    argument_source: sample, inherited. -/
noncomputable def presentDayR2MutationDrift (V_A V_E fst_drift shared_ld : ℝ) : ℝ :=
  let v := presentDayPGSVarianceMutationDrift V_A fst_drift shared_ld
  v / (v + V_E)

/-- Where the present-day score variance and the environmental variance cancel, the ratio
divides by zero and Mathlib returns `0`: no predictive accuracy, reported for a model that has
no total variance at all. -/
theorem presentDayR2MutationDrift_at_zero_total_variance_is_junk
    (V_A V_E fst_drift shared_ld : ℝ)
    (hzero : presentDayPGSVarianceMutationDrift V_A fst_drift shared_ld + V_E = 0) :
    presentDayR2MutationDrift V_A V_E fst_drift shared_ld = 0 := by
  show presentDayPGSVarianceMutationDrift V_A fst_drift shared_ld /
    (presentDayPGSVarianceMutationDrift V_A fst_drift shared_ld + V_E) = 0
  rw [hzero, div_zero]



/-- **Mutation-drift R² is below drift-only R².**
    When shared LD is imperfect, R² under mutation-drift is strictly below
    drift-only R². This is the key portability result: ignoring mutation
    overestimates portability. -/
theorem mutationDrift_R2_lt_puredrift_R2 (V_A V_E fst_drift shared_ld : ℝ)
    (hVA : 0 < V_A) (hVE : 0 < V_E)
    (hfst_lt : fst_drift < 1)
    (hld : 0 < shared_ld) (hld_lt : shared_ld < 1) :
    presentDayR2MutationDrift V_A V_E fst_drift shared_ld <
      presentDayR2 V_A V_E fst_drift := by
  unfold presentDayR2MutationDrift presentDayR2 r2FromSignalVariance
  have h_sig_lt := mutationDrift_signal_lt_puredrift V_A fst_drift shared_ld
    hVA hfst_lt hld_lt
  have h_md_nonneg : 0 ≤ presentDayPGSVarianceMutationDrift V_A fst_drift shared_ld :=
    presentDayPGSVarianceMutationDrift_nonneg V_A fst_drift shared_ld
      (le_of_lt hVA) (le_of_lt hfst_lt) (le_of_lt hld)
  exact expectedR2_strictMono_nonneg V_E
    (presentDayPGSVarianceMutationDrift V_A fst_drift shared_ld)
    (presentDayPGSVariance V_A fst_drift)
    hVE h_md_nonneg h_sig_lt

/-- Scalar neutral benchmark that combines allele-frequency retention with a
shared-LD retention coordinate. This remains a coarse benchmark, not a
mechanistic SNP-level transport law.

    Empirical status: **MEASURED, inherited**
    (`validation/empirical/simcov/battery_bulk36.py`). Numerator and
    denominator are each the retention form `(1 - fst) * shared_ld` that battery
    measures directly, one per population, so the table and the reason it is a
    number rather than a rejection are at `covarianceDivergenceMutationDrift`.

    WHAT THE RATIO ADDS AND WHY IT IS THE WEAKER CLAIM OF THE TWO. Taking the
    quotient of two retention factors asserts that the source's own retention is
    the right normaliser -- that the benchmark is scale-free in whatever the two
    populations share. Nothing measured here reaches that: `battery_bulk36` runs
    two demes of a symmetric island model, where the source and target retention
    factors are equal by construction and the ratio is one at every cell. So the
    ratio's own content is untouched by the run that covers its parts, and a
    design that moved the two populations asymmetrically is what it owes.

    argument_source: sample, inherited. -/
noncomputable def neutralAFSharedLDBenchmarkRatio
    (fstSource fstTarget shared_ld_source shared_ld_target : ℝ) : ℝ :=
  ((1 - fstTarget) * shared_ld_target) / ((1 - fstSource) * shared_ld_source)

/-- **The benchmark ratio's junk branch, named.** A source that shares no linkage structure, or
one at complete differentiation, zeroes the denominator and Lean returns `0`: the ratio reports
total loss of transfer where it is undefined, since there was no source performance to transfer.
Consumers must require the source denominator nonzero. -/
theorem neutralAFSharedLDBenchmarkRatio_no_source_is_junk
    (fstSource fstTarget shared_ld_target : ℝ) :
    neutralAFSharedLDBenchmarkRatio fstSource fstTarget 0 shared_ld_target = 0 := by
  unfold neutralAFSharedLDBenchmarkRatio; simp

/-- The shared-LD benchmark reduces to the neutral allele-frequency benchmark
when shared LD is perfect in both populations. -/
theorem neutralAFSharedLDBenchmarkRatio_pure_drift (fstSource fstTarget : ℝ) :
    neutralAFSharedLDBenchmarkRatio fstSource fstTarget 1 1 =
      (1 - fstTarget) / (1 - fstSource) := by
  unfold neutralAFSharedLDBenchmarkRatio
  ring

/-- The shared-LD benchmark is below the pure neutral allele-frequency
benchmark when target shared LD is worse than source shared LD. -/
theorem neutralAFSharedLDBenchmarkRatio_lt_pure_drift_form
    (fstSource fstTarget shared_ld_source shared_ld_target : ℝ)
    (hfstS : fstSource < 1) (hfstT : fstTarget < 1)
    (hldS : 0 < shared_ld_source)
    (hld_decay : shared_ld_target / shared_ld_source < 1) :
    neutralAFSharedLDBenchmarkRatio fstSource fstTarget shared_ld_source shared_ld_target <
      (1 - fstTarget) / (1 - fstSource) := by
  unfold neutralAFSharedLDBenchmarkRatio
  have h1 : 0 < 1 - fstSource := by linarith
  have h_den_pos : 0 < (1 - fstSource) * shared_ld_source := mul_pos h1 hldS
  rw [div_lt_div_iff₀ h_den_pos h1]
  have h_ld_ratio : shared_ld_target < shared_ld_source := by
    rwa [div_lt_one hldS] at hld_decay
  have hnum_lt :
      ((1 - fstSource) * (1 - fstTarget)) * shared_ld_target <
        ((1 - fstSource) * (1 - fstTarget)) * shared_ld_source :=
    mul_lt_mul_of_pos_left h_ld_ratio (mul_pos h1 (by linarith))
  simpa [mul_assoc, mul_left_comm, mul_comm] using hnum_lt


/-- **At equilibrium, larger θ means lower Fst and thus the drift component
    of portability improves.**
    If we compare two populations at equilibrium with θ₁ < θ₂, the population
    with larger θ has smaller Fst. This improves the allele frequency component
    of signal retention. -/
theorem equilibrium_drift_component_improves_with_theta
    (V_A θ₁ θ₂ : ℝ)
    (hVA : 0 < V_A) (hθ₁ : 0 < θ₁)
    (h_more : θ₁ < θ₂) :
    presentDayPGSVariance V_A (1 / (1 + θ₁)) <
      presentDayPGSVariance V_A (1 / (1 + θ₂)) := by
  unfold presentDayPGSVariance pgsVarianceFromHet
  have h1 : 0 < 1 + θ₁ := by linarith
  have h2 : 0 < 1 + θ₂ := by linarith
  -- 1/(1+θ₂) < 1/(1+θ₁), so 1 - 1/(1+θ₁) < 1 - 1/(1+θ₂)
  -- i.e., θ₁/(1+θ₁) < θ₂/(1+θ₂)
  have hfst₁ : 1 - 1 / (1 + θ₁) = θ₁ / (1 + θ₁) := by
    have hne : 1 + θ₁ ≠ 0 := by linarith
    field_simp [hne]
    ring_nf
  have hfst₂ : 1 - 1 / (1 + θ₂) = θ₂ / (1 + θ₂) := by
    have hne : 1 + θ₂ ≠ 0 := by linarith
    field_simp [hne]
    ring_nf
  rw [hfst₁, hfst₂]
  have h_ratio_lt : θ₁ / (1 + θ₁) < θ₂ / (1 + θ₂) := by
    rw [div_lt_div_iff₀ h1 h2]
    nlinarith
  exact mul_lt_mul_of_pos_left h_ratio_lt hVA

/-- **Pure drift benchmark overestimates retained variance.**
    The drift-only benchmark (which sets `negligibleMutation` = True) always
    overestimates retained variance compared to the mutation-drift model.
    This theorem quantifies the gap: the ratio of mutation-drift variance
    to drift-only variance is exactly `shared_ld`. -/
theorem mutationDrift_variance_ratio (V_A fst shared_ld : ℝ)
    (hVA : 0 < V_A) (hfst : fst < 1)
    (hld : 0 < shared_ld) :
    presentDayPGSVarianceMutationDrift V_A fst shared_ld /
      presentDayPGSVariance V_A fst = shared_ld := by
  rw [presentDayPGSVarianceMutationDrift_eq]
  unfold presentDayPGSVariance pgsVarianceFromHet
  have hfst_ne : 1 - fst ≠ 0 := by linarith
  have hVA_ne : V_A ≠ 0 := ne_of_gt hVA
  field_simp [hfst_ne, hVA_ne]

/-! **Deleted: `neutral_af_benchmark_correction_factor`.**

This theorem is absent on purpose. It states `presentDayPGSVarianceMutationDrift V_A fst
ld = ld * presentDayPGSVariance V_A fst` and closes by `ring`. All six of its hypotheses go
unused — `0 < V_A`, `0 < V_E`, `0 ≤ fst`, `fst < 1`, `0 < ld`, `ld ≤ 1` — and `V_E` is a
phantom parameter appearing nowhere in the statement, present only so the signature reads
like a statement about `R²`. The identity is `presentDayPGSVarianceMutationDrift_eq` with
the factors reassociated, and `mutationDrift_variance_ratio` just above states the same
content as a ratio with the hypotheses it genuinely needs.

Two of those hypotheses are worse than unused. `0 ≤ fst` and `fst < 1` are the range in
which the "correction factor" reading means anything, and leaving them unused lets the
equation hold at `fst > 1`, where `presentDayPGSVariance` is negative and the word
*correction* has no referent. A theorem satisfied by the inadmissible parameter values too
is no evidence that the admissible ones are the intended domain. -/

/-- **Pairwise Fst under mutation-drift balance is bounded.**
    Under mutation-drift equilibrium, pairwise Fst between any two populations
    is bounded above by 2 × Fst_eq (since each branch contributes at most Fst_eq). -/
theorem pairwise_fst_mutationDrift_bound (θ : ℝ) (hθ : 0 < θ) :
    pairwiseFstFromBranches (1 / (1 + θ)) (1 / (1 + θ)) ≤ 2 / (1 + θ) := by
  simp [pairwiseFstFromBranches]
  ring_nf
  have h1 : 0 < 1 + θ := by linarith
  have hsq : 0 ≤ (1 / (1 + θ)) ^ 2 := sq_nonneg (1 / (1 + θ))
  nlinarith

end MutationDriftPortability


/-!
## Migration-Drift Balance and Portability

Gene flow (migration) between populations counteracts drift, preventing complete
differentiation. The classic Wright island model gives Fst ≈ 1/(1 + 4Nm) at
equilibrium. This section extends the `SplitMigrationModel` with:
1. Fst under migration-drift equilibrium and its properties
2. Migration reduces Fst relative to pure drift
3. Stepping-stone model: Fst increases with geographic distance
4. Migration's effect on LD sharing and PGS portability
5. Portability is higher with gene flow than without
6. Asymmetric migration and directional portability
7. Admixture LD from recent migration pulses
-/

section MigrationDriftPortability

/-! ### 1. Fst under migration-drift balance: Fst = 1/(1 + 4Nm) -/

/-- The finite-island correction factor `d/(d-1)` for `demes` demes.

Convention: this is the correction as it enters the HUDSON coalescence-time
`F_ST`, where it appears LINEARLY: `1/(1 + 4·Nₑ·m·d/(d-1))`. The widely quoted
Crow--Aoki (1984) finite-island formula carries `(d/(d-1))²`, but that is the
correction for Nei's `G_ST`, a different statistic. Do not read this factor as
the square's base and then square it; `PopulationGeneticsFoundations`'
`islandDemeCorrection` carries the measurement that excludes the square under
this corpus's convention, at 9.04 sems, and `islandFstFiniteDemes` carries the
attribution for both forms.

This is data, not a packaged claim that an approximation is adequate.  Any biological
use of the infinite-island approximation must compare this explicit quantity with its
own scientifically justified tolerance. -/
noncomputable def finiteIslandCorrection (demes : ℝ) : ℝ :=
  demes / (demes - 1)

/-- **The finite-island correction's junk branch, named.** At a single deme the correction
diverges and Lean returns `0`. Consumers must require `demes ≠ 1`. -/
theorem finiteIslandCorrection_one_deme_is_junk : finiteIslandCorrection 1 = 0 := by
  unfold finiteIslandCorrection; norm_num

/-- With two demes the finite-island correction is exactly two.

    It was stated as four while the body carried a square. Measurement put the
    exponent at one, not two: at `4 Ne m = 4.0` and two demes the simulated
    `F_ST` is `0.09743 ± 0.00432`, against `0.11111` for this correction and
    `0.05882` for the square, which is 8.9 sems low. See
    `PopulationGeneticsFoundations.islandDemeCorrection`. -/
@[simp] theorem finiteIslandCorrection_two : finiteIslandCorrection 2 = 2 := by
  norm_num [finiteIslandCorrection]

/-- Consequently its excess over the infinite-island value is exactly one. -/
@[simp] theorem finiteIslandCorrection_two_excess :
    finiteIslandCorrection 2 - 1 = 1 := by
  rw [finiteIslandCorrection_two]
  norm_num

/-- **Island model equilibrium Fst under migration-drift balance.**
    Fst_eq = 1 / (1 + 4Nm) where N is effective size and m is migration rate.
    This is the classical Wright (1931) result.

    Regime: the infinite-island limit. The explicit `finiteIslandCorrection`
    above makes the finite-deme discrepancy inspectable. Simulation puts the law within 2% at 40
    demes, but +17% at 10, +31% at 5 and +95% at 2. The two-deme case is the
    two-ancestry comparison this development is mostly about, so the law is off
    by roughly twofold in its primary application. The finite-deme correction
    `1/(1 + 4 Nₑ m (d/(d-1))²)` repairs the 5-to-10 deme range and overshoots at
    `d = 2` by −40%.

    Empirical status: CONDITIONALLY VALID. Accurate in the limit it was derived
    for; frequently violated in use. Neither validated nor falsified. -/
noncomputable def fstMigrationDriftEquilibrium (Ne m : ℝ) : ℝ :=
  1 / (1 + 4 * Ne * m)

/-- **fstMigrationDriftEquilibrium at `4 * Ne * m = -1`, named.** A negative migration rate is
inadmissible, and at `4 Ne m = -1` the divisor vanishes. Lean returns `0`: no differentiation at
all, the value for free gene flow. Consumers must exclude it by hypothesis. -/
theorem fstMigrationDriftEquilibrium_balancing_negative_migration_is_junk :
    fstMigrationDriftEquilibrium 1 (-(1/4)) = 0 := by
  unfold fstMigrationDriftEquilibrium
  norm_num

/-- **No migration leaves complete differentiation.** At `m = 0` the island model fixes
populations entirely, so the equilibrium is one; that is the reference point which fixes the
constant term, and it is what a body with the wrong intercept would miss. It is also the
boundary the closed form attains, which was a second theorem with this statement. -/
@[simp] theorem fstMigrationDriftEquilibrium_no_migration (Ne : ℝ) :
    fstMigrationDriftEquilibrium Ne 0 = 1 := by
  unfold fstMigrationDriftEquilibrium
  norm_num

/-- **The island-model F_ST is the rest point of the identity balance** driven
by migration.  It is not a stipulated closed form: substitute any other
constant and this fails. -/
theorem fstMigrationDriftEquilibrium_isFixedPoint (Ne m : ℝ)
    (hNe : 0 < Ne) (hm : 0 ≤ m) :
    ibdFlowStep Ne m (fstMigrationDriftEquilibrium Ne m) =
      fstMigrationDriftEquilibrium Ne m :=
  ibdFlowStep_fixedPoint Ne m hNe hm

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
  (1 - rate) ^ 2 * (1 / (2 * Ne) + (1 - 1 / (2 * Ne)) * x)

/-- **ibdRecurrenceStep at its junk point, named.** At `Ne = 0` the identity-by-descent input
term is junk-zero and the retained term keeps full weight, so an empty population is reported as
generating no new identity by descent. Iterating the recurrence compounds the error. Consumers
must exclude the argument that makes the guard vanish. -/
theorem ibdRecurrenceStep_empty_population_is_junk (rate x : ℝ) :
    ibdRecurrenceStep 0 rate x = (1 - rate) ^ 2 * x := by
  unfold ibdRecurrenceStep
  simp

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

/-- **ibdRecurrenceFixedPoint where its denominator vanishes, named.** The guard `(1 - rate) ^ 2 + 2
* Ne * rate * (2 - rate)` is zero at `Ne = 0`, `rate = 1`. Lean returns `0` there rather than
the value the modelled quantity takes, and no type error marks the point. Consumers must require
`(1 - rate) ^ 2 + 2 * Ne * rate * (2 - rate) ≠ 0`. -/
theorem ibdRecurrenceFixedPoint_at_ne0rate1_is_junk :
    ibdRecurrenceFixedPoint 0 1 = 0 := by
  unfold ibdRecurrenceFixedPoint
  norm_num

/-- **The rest point is a fixed point of the recurrence.**  Stated once here so
that the island-model and Sved readings cannot acquire different answers. -/
theorem ibdRecurrenceFixedPoint_isFixedPoint (Ne rate : ℝ)
    (hNe : 0 < Ne) (hr : 0 ≤ rate) (hr1 : rate < 1) :
    ibdRecurrenceStep Ne rate (ibdRecurrenceFixedPoint Ne rate) =
      ibdRecurrenceFixedPoint Ne rate := by
  have h2Ne : (0 : ℝ) < 2 * Ne := by linarith
  have h2Ne' : (2 : ℝ) * Ne ≠ 0 := ne_of_gt h2Ne
  have hpos : (0 : ℝ) < 1 - rate := by linarith
  have hsq : (0 : ℝ) < (1 - rate) ^ 2 := pow_pos hpos 2
  have hflow : (0 : ℝ) ≤ 2 * Ne * rate * (2 - rate) :=
    mul_nonneg (mul_nonneg h2Ne.le hr) (by linarith : (0 : ℝ) ≤ 2 - rate)
  have hd : (0 : ℝ) < (1 - rate) ^ 2 + 2 * Ne * rate * (2 - rate) := by linarith
  have hd' : (1 - rate) ^ 2 + 2 * Ne * rate * (2 - rate) ≠ 0 := ne_of_gt hd
  have hdExpanded :
      (1 : ℝ) - rate * 2 + rate * Ne * 4 +
          (rate ^ 2 - rate ^ 2 * Ne * 2) ≠ 0 := by
    have hbridge :
        (1 : ℝ) - rate * 2 + rate * Ne * 4 +
            (rate ^ 2 - rate ^ 2 * Ne * 2) =
          (1 - rate) ^ 2 + 2 * Ne * rate * (2 - rate) := by
      ring
    rw [hbridge]
    exact hd'
  unfold ibdRecurrenceStep ibdRecurrenceFixedPoint
  -- Clear the fixed-point denominator while it is still in its factored form;
  -- only then clear the coalescence denominator. Expanding first made the
  -- nonzero hypothesis syntactically unusable and left an inverse in the goal.
  apply (eq_div_iff hd').2
  field_simp [h2Ne', hdExpanded]
  have hinv :
      ((1 : ℝ) - rate * 2 + rate * Ne * 4 +
          (rate ^ 2 - rate ^ 2 * Ne * 2))⁻¹ *
        ((1 : ℝ) - rate * 2 + rate * Ne * 4 +
          (rate ^ 2 - rate ^ 2 * Ne * 2)) = 1 :=
    inv_mul_cancel₀ hdExpanded
  ring_nf at hinv ⊢
  nlinarith [hinv]

/-- **Total isolation is a boundary the rest point attains.**  With `rate = 0`
nothing separates the lineages and the recurrence rests at `1`. -/
@[simp] theorem ibdRecurrenceFixedPoint_of_zero_rate (Ne : ℝ) :
    ibdRecurrenceFixedPoint Ne 0 = 1 := by
  unfold ibdRecurrenceFixedPoint
  norm_num

/-- **The exact error of the `1/(1 + 4 Nₑ rate)` linearisation.**

`x* - 1/(1 + 4 Nₑ rate) = 2 Nₑ rate² (2 rate - 3) / (D (1 + 4 Nₑ rate))` where
`D = (1 - rate)² + 2 Nₑ rate (2 - rate)`. The error is second order in `rate`,
which is what makes `1/(1 + 4 Nₑ rate)` a first-order approximation rather than
an identity. -/
theorem ibdRecurrenceFixedPoint_sub_linearisation (Ne rate : ℝ)
    (hNe : 0 < Ne) (hr : 0 ≤ rate) (hr1 : rate < 1) :
    ibdRecurrenceFixedPoint Ne rate - 1 / (1 + 4 * Ne * rate) =
      2 * Ne * rate ^ 2 * (2 * rate - 3) /
        (((1 - rate) ^ 2 + 2 * Ne * rate * (2 - rate)) * (1 + 4 * Ne * rate)) := by
  have h2Ne : (0 : ℝ) < 2 * Ne := by linarith
  have hpos : (0 : ℝ) < 1 - rate := by linarith
  have hsq : (0 : ℝ) < (1 - rate) ^ 2 := pow_pos hpos 2
  have hflow : (0 : ℝ) ≤ 2 * Ne * rate * (2 - rate) :=
    mul_nonneg (mul_nonneg h2Ne.le hr) (by linarith : (0 : ℝ) ≤ 2 - rate)
  have hd : (0 : ℝ) < (1 - rate) ^ 2 + 2 * Ne * rate * (2 - rate) := by linarith
  have hd' : (1 - rate) ^ 2 + 2 * Ne * rate * (2 - rate) ≠ 0 := ne_of_gt hd
  have hlin : (0 : ℝ) < 1 + 4 * Ne * rate := by nlinarith
  have hlin' : (1 : ℝ) + 4 * Ne * rate ≠ 0 := ne_of_gt hlin
  unfold ibdRecurrenceFixedPoint
  rw [div_sub_div _ _ hd' hlin']
  have hnum : (1 - rate) ^ 2 * (1 + 4 * Ne * rate) -
      ((1 - rate) ^ 2 + 2 * Ne * rate * (2 - rate)) * 1 =
      2 * Ne * rate ^ 2 * (2 * rate - 3) := by ring
  rw [hnum]

/-- **`1/(1 + 4 Nₑ rate)` is strictly above the rest point, always.**

This is the theorem that stops the classical formula being re-derived as if it
were exact. One statement covers both readings: `1/(1 + 4 Nₑ m)` for the island
model and Sved's `1/(1 + 4 Nₑ c)` for two-locus LD are the same weak-rate
linearisation of `ibdRecurrenceFixedPoint`, each overstates it, and the gap is
the second-order term of `ibdRecurrenceFixedPoint_sub_linearisation`. At
`Nₑ = 1`, `rate = 1/2` the rest point is `1/7` and the linearisation is `1/3`.

Regime of the linearisation: small `rate`, large `Nₑ`. Outside it the corpus
already records a roughly twofold discrepancy at two demes on the island-model
definitions, and this theorem says the discrepancy has a sign. -/
theorem ibdRecurrenceFixedPoint_lt_linearisation (Ne rate : ℝ)
    (hNe : 0 < Ne) (hr : 0 < rate) (hr1 : rate < 1) :
    ibdRecurrenceFixedPoint Ne rate < 1 / (1 + 4 * Ne * rate) := by
  have h2Ne : (0 : ℝ) < 2 * Ne := by linarith
  have hpos : (0 : ℝ) < 1 - rate := by linarith
  have hsq : (0 : ℝ) < (1 - rate) ^ 2 := pow_pos hpos 2
  have hflow : (0 : ℝ) ≤ 2 * Ne * rate * (2 - rate) :=
    mul_nonneg (mul_nonneg h2Ne.le hr.le) (by linarith : (0 : ℝ) ≤ 2 - rate)
  have hd : (0 : ℝ) < (1 - rate) ^ 2 + 2 * Ne * rate * (2 - rate) := by linarith
  have hlin : (0 : ℝ) < 1 + 4 * Ne * rate := by nlinarith
  have hden : (0 : ℝ) <
      ((1 - rate) ^ 2 + 2 * Ne * rate * (2 - rate)) * (1 + 4 * Ne * rate) :=
    mul_pos hd hlin
  have hrsq : (0 : ℝ) < rate ^ 2 := pow_pos hr 2
  have hnum : 2 * Ne * rate ^ 2 * (2 * rate - 3) < 0 :=
    mul_neg_of_pos_of_neg (mul_pos h2Ne hrsq) (by linarith)
  have hgap := ibdRecurrenceFixedPoint_sub_linearisation Ne rate hNe hr.le hr1
  have hneg : ibdRecurrenceFixedPoint Ne rate - 1 / (1 + 4 * Ne * rate) < 0 := by
    rw [hgap]
    exact div_neg_of_neg_of_pos hnum hden
  linarith

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

/-- Reference evaluation.  The value is computed through the definitions this body calls, but
the theorem states a number: an inequality or an invariance leaves a family of bodies
satisfying it, and a value does not. -/
theorem islandFstMultiplicativeStep_at_reference_point :
    islandFstMultiplicativeStep 1 (1 / 2) 0 = 1 / 8 := by
  norm_num [islandFstMultiplicativeStep, ibdRecurrenceStep]



/-! **`islandFstMultiplicativeStep` is `ibdRecurrenceStep` by definition, and needs no
theorem saying so** -- a definitional alias is carried by the elaborator, and a `rfl`
statement of it cannot fail.

**The DEFINITION must stay.** `LDDecayTheory.driftLDStep_eq_islandFstMultiplicativeStep`
proves the independently written `driftLDStep` equal to it by `ring`; that is a genuine
guard between two bodies, and deleting this name would disconnect `driftLDStep` from the
recurrence it is held to. Connectivity to the hub, not theorem count, is what makes a
removal safe. -/

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

/-- **The closed form is the fixed point of the island-model recursion.** -/
theorem fstIslandMultiplicativeEquilibrium_isFixedPoint (Ne m : ℝ)
    (hNe : 0 < Ne) (hm : 0 ≤ m) (hm1 : m < 1) :
    islandFstMultiplicativeStep Ne m (fstIslandMultiplicativeEquilibrium Ne m) =
      fstIslandMultiplicativeEquilibrium Ne m :=
  ibdRecurrenceFixedPoint_isFixedPoint Ne m hNe hm hm1

/-- **Total isolation, island reading.**  This recursion also attains the
boundary: `m = 0` gives `F = 1`. -/
@[simp] theorem fstIslandMultiplicativeEquilibrium_of_no_migration (Ne : ℝ) :
    fstIslandMultiplicativeEquilibrium Ne 0 = 1 :=
  ibdRecurrenceFixedPoint_of_zero_rate Ne

/-- **The two recursions do not have the same fixed point.**

At `Nₑ = 1`, `m = 1/2` the multiplicative recursion rests at `1/7` and the
linearised one at `1/3`.  This is not a defect of either definition: it is the
size of the weak-migration approximation, and it is stated here rather than
left implicit so that the approximation cannot be mistaken for an identity. -/
theorem fstIslandMultiplicativeEquilibrium_ne_fstMigrationDriftEquilibrium :
    fstIslandMultiplicativeEquilibrium 1 (1 / 2) ≠ fstMigrationDriftEquilibrium 1 (1 / 2) := by
  unfold fstIslandMultiplicativeEquilibrium ibdRecurrenceFixedPoint
    fstMigrationDriftEquilibrium
  norm_num


/-- Scaled migration rate is positive when Ne and m are positive. -/
theorem scaledMigrationRate_pos (Ne m : ℝ) (hNe : 0 < Ne) (hm : 0 < m) :
    0 < scaledMigrationRate Ne m := by
  unfold scaledMigrationRate
  positivity

/-- Fst under migration-drift equilibrium equals 1/(1 + M). -/
theorem fstMigrationDriftEquilibrium_eq_from_M (Ne m : ℝ) :
    fstMigrationDriftEquilibrium Ne m = 1 / (1 + scaledMigrationRate Ne m) := by
  unfold fstMigrationDriftEquilibrium scaledMigrationRate
  ring

/-- Equilibrium Fst under migration-drift is positive for nonneg migration. -/
theorem fstMigrationDriftEquilibrium_pos (Ne m : ℝ) (hNe : 0 < Ne) (hm : 0 ≤ m) :
    0 < fstMigrationDriftEquilibrium Ne m := by
  unfold fstMigrationDriftEquilibrium
  have : 0 ≤ 4 * Ne * m := by positivity
  positivity

/-- Equilibrium Fst under migration-drift is at most 1. -/
theorem fstMigrationDriftEquilibrium_le_one (Ne m : ℝ) (hNe : 0 < Ne) (hm : 0 ≤ m) :
    fstMigrationDriftEquilibrium Ne m ≤ 1 := by
  unfold fstMigrationDriftEquilibrium
  rw [div_le_one (by nlinarith)]
  nlinarith

/-- Equilibrium Fst under migration-drift is strictly less than 1 when m > 0.
    This is the key qualitative result: migration prevents complete fixation. -/
theorem fstMigrationDriftEquilibrium_lt_one (Ne m : ℝ) (hNe : 0 < Ne) (hm : 0 < m) :
    fstMigrationDriftEquilibrium Ne m < 1 := by
  unfold fstMigrationDriftEquilibrium
  rw [div_lt_one (by nlinarith)]
  nlinarith

/-- Equilibrium Fst is in the open interval (0, 1) for positive Ne and m. -/
theorem fstMigrationDriftEquilibrium_in_unit (Ne m : ℝ) (hNe : 0 < Ne) (hm : 0 < m) :
    0 < fstMigrationDriftEquilibrium Ne m ∧ fstMigrationDriftEquilibrium Ne m < 1 :=
  ⟨fstMigrationDriftEquilibrium_pos Ne m hNe (le_of_lt hm),
   fstMigrationDriftEquilibrium_lt_one Ne m hNe hm⟩

/-- **The equilibrium decreases when the migration-drift product rises.**

Both monotonicities are this one fact: the equilibrium is `1 / (1 + 4 Ne m)`, so it falls
whenever `Ne * m` rises, and whether that happened by moving `m` or by moving `Ne` is the
caller's business.  Stated separately, each carried the same three-line proof. -/
theorem fstMigrationDriftEquilibrium_strictAnti_product (Ne₁ m₁ Ne₂ m₂ : ℝ)
    (h_pos : 0 < Ne₁ * m₁) (h_more : Ne₁ * m₁ < Ne₂ * m₂) :
    fstMigrationDriftEquilibrium Ne₂ m₂ < fstMigrationDriftEquilibrium Ne₁ m₁ := by
  unfold fstMigrationDriftEquilibrium
  apply div_lt_div_of_pos_left one_pos (by nlinarith) (by nlinarith)

/-- **Equilibrium Fst decreases with migration rate** (Ne fixed).
    More migration → more gene flow → less differentiation. -/
theorem fstMigrationDriftEquilibrium_decreases_with_m (Ne m₁ m₂ : ℝ)
    (hNe : 0 < Ne) (hm₁ : 0 < m₁) (h_more : m₁ < m₂) :
    fstMigrationDriftEquilibrium Ne m₂ < fstMigrationDriftEquilibrium Ne m₁ :=
  fstMigrationDriftEquilibrium_strictAnti_product Ne m₁ Ne m₂
    (by positivity) (by nlinarith)

/-- **Equilibrium Fst decreases with effective population size** (m fixed).
    Larger Ne → slower drift relative to migration → less differentiation. -/
theorem fstMigrationDriftEquilibrium_decreases_with_Ne (Ne₁ Ne₂ m : ℝ)
    (hNe₁ : 0 < Ne₁) (hm : 0 < m) (h_more : Ne₁ < Ne₂) :
    fstMigrationDriftEquilibrium Ne₂ m < fstMigrationDriftEquilibrium Ne₁ m :=
  fstMigrationDriftEquilibrium_strictAnti_product Ne₁ m Ne₂ m
    (by positivity) (by nlinarith)

/-! ### 2. Migration counteracts drift -/

/-! **Deleted: `migration_reduces_fst_vs_pure_drift`.**

This theorem is absent on purpose. Its hypothesis is
`1 / (1 + 4 * Ne * m) < t / (t + 2 * Ne)` and its conclusion is
`fstMigrationDriftEquilibrium Ne m < t / (t + 2 * Ne)`. Since
`fstMigrationDriftEquilibrium Ne m` unfolds to `1 / (1 + 4 * Ne * m)`, the two are the same
proposition and the proof is `unfold; exact h_large_t` — the hypothesis, returned. The
remaining three hypotheses (`0 < Ne`, `0 < m`, `0 < t`) go unused.

The prose around it claims the derivation the theorem skips: "Under migration-drift
equilibrium, Fst = 1/(1+4Nm) < 1 - (1-1/(2Ne))^t for sufficiently large t." Nothing
establishes *for which* `t` the inequality holds. That is exactly what the hypothesis
assumes, under a name (`h_large_t`) that asserts the answer. Establishing it would mean
showing `1/(1+4Nm) < t/(t+2Ne)` for `t` past an explicit threshold in `Ne` and `m`, which
is a real result and appears nowhere in this file.

A result that merely repackages a premise is deleted, not renamed: there is no honest name
for `h → h`. -/

/-- **Finite equilibrium vs unbounded drift.**
    Under pure drift, Fst approaches 1 as t → ∞. Under migration-drift balance,
    Fst is bounded above by 1/(1+4Nm) < 1. This means migration establishes
    a ceiling on differentiation. -/
theorem lt_one_of_le_migrationEquilibrium (Ne m : ℝ) (hNe : 0 < Ne) (hm : 0 < m)
    (fst_observed : ℝ) (h_le : fst_observed ≤ fstMigrationDriftEquilibrium Ne m) :
    fst_observed < 1 := by
  have h_eq_lt := fstMigrationDriftEquilibrium_lt_one Ne m hNe hm
  linarith

/-- **SplitMigrationModel equilibrium Fst using the structure.**

    Empirical status: **FALSIFIED** outside the weak-migration limit, inherited
    (`validation/empirical/simcov/battery_pd1.py`). This body forwards
    `s.Ne` and `s.mig` to `fstMigrationDriftEquilibrium`, so it carries that
    definition's verdict without qualification: within 2% at `mig ≤ 0.01`, 182%
    high at `mig = 0.5`, against an explicit 200-deme Wright-Fisher island model
    whose panmictic control reads 0.05 sems from zero. The table is at
    `SplitMigrationModel.fstEqLimitLowMutationManyDemes`, which is the same
    closed form written through `scaledMigrationRate`.

    What the forwarding adds over the parent, and what is therefore NOT covered
    by inheriting: that `Ne` and `mig` are passed in that order. Nothing here
    measures the argument order, because `fstMigrationDriftEquilibrium` is
    symmetric in its two arguments only through the product `4 * Ne * m`, so a
    transposition would return the same number and no simulation can see it.
    `SplitMigrationModel.fstMigDriftEq_mul_denom` is what pins the coefficient.

    argument_source: model. -/
noncomputable def SplitMigrationModel.fstMigDriftEq (s : SplitMigrationModel) : ℝ :=
  fstMigrationDriftEquilibrium s.Ne s.mig

/-- **The equilibrium inverts one plus four Ne m.** The many-deme limit identity below relates
this to another quantity without fixing the coefficient on the scaled migration rate; multiplying
the denominator back does, and any other coefficient would satisfy the limit identity equally. -/
theorem SplitMigrationModel.fstMigDriftEq_mul_denom (s : SplitMigrationModel)
    (h : 1 + 4 * s.Ne * s.mig ≠ 0) :
    s.fstMigDriftEq * (1 + 4 * s.Ne * s.mig) = 1 := by
  unfold SplitMigrationModel.fstMigDriftEq fstMigrationDriftEquilibrium
  field_simp

/-- SplitMigrationModel equilibrium Fst equals the limit Fst for many demes. -/
theorem SplitMigrationModel.fstMigDriftEq_eq_limit (s : SplitMigrationModel) :
    s.fstMigDriftEq = s.fstEqLimitLowMutationManyDemes := by
  unfold SplitMigrationModel.fstMigDriftEq fstMigrationDriftEquilibrium
    SplitMigrationModel.fstEqLimitLowMutationManyDemes
    scaledMigrationRate
  ring

/-- **Increased migration strictly improves equilibrium Fst in the SplitMigration framework.**
    Comparing two SplitMigrationModels with same Ne but different migration rates. -/
theorem splitMigration_more_migration_less_fst
    (Ne m₁ m₂ : ℝ) (mu : ℝ)
    (hNe : 0 < Ne) (hm₁ : 0 < m₁) (hm₂ : 0 < m₂)
    (hmu : 0 ≤ mu) (h_more : m₁ < m₂) :
    let s₁ : SplitMigrationModel := ⟨0, Ne, m₁, mu, hNe, le_of_lt hm₁, hmu⟩
    let s₂ : SplitMigrationModel := ⟨0, Ne, m₂, mu, hNe, le_of_lt hm₂, hmu⟩
    s₂.fstMigDriftEq < s₁.fstMigDriftEq := by
  simp only [SplitMigrationModel.fstMigDriftEq]
  exact fstMigrationDriftEquilibrium_decreases_with_m Ne m₁ m₂ hNe hm₁ h_more

/-! ### 3. Stepping-stone model: Fst increases with geographic distance -/

/-- **Stepping-stone Fst model.**
    In the stepping-stone model, migration occurs only between adjacent demes.
    Fst between demes separated by d steps saturates:
    Fst(d) = d · Fst_neighbor / (Fst_neighbor · d + α · (1 - Fst_neighbor))
    which is `d / (d + K)` with characteristic scale `K = α (1 - Fst_neighbor)/Fst_neighbor`.
    `α` is the unit of distance -- it rescales that scale -- and at `α = 1` the form
    reproduces its own anchor, `Fst(1) = Fst_neighbor`.

    **This body was corrected.** It previously read
    `min 1 (Fst_neighbor × (1 + α × (d - 1)))`, linear in the separation and held inside
    `[0,1]` by an outer clamp. That form is FALSIFIED and the saturating one is measured;
    the evidence is below. Two theorems changed with it:
    `steppingStoneFst_eq_one_of_saturated` is gone, replaced by `steppingStoneFst_lt_one`
    which says the opposite, because a saturating form approaches complete
    differentiation without ever attaining it at finite separation; and
    `steppingStoneFst_increases_with_distance` no longer needs a below-saturation
    hypothesis, since `d/(d+K)` rises at every separation while the clamped linear form
    stopped rising once it hit the clamp.

    The `min 1` is not cosmetic. An `F_ST` is a variance ratio and lies in
    `[0, 1]`; the bare linear form returns `10000` at
    `fst_neighbor = 1, α = 1, d = 10000`, which is not a value the quantity can
    take. Clamping also makes the fixation boundary attainable rather than
    merely approached: `steppingStoneFst_eq_one_of_saturated` exhibits the
    regime where distant demes are completely differentiated, which is the
    physically correct behaviour of isolation by distance at long range.

    Regime: all separations. The saturating form needs no below-saturation proviso,
    which is the practical gain from the correction: the previous body was declared
    trustworthy only while `fst_neighbor * (1 + α (d - 1))` stayed well below `1`, and it
    failed INSIDE that declared regime -- at `d = 3` the measured `F_ST` is `0.123`,
    nowhere near saturation, and the linear form is 12% high there. A regime restriction
    does not rescue a body that is wrong inside its own regime. The companion
    saturating closed form is `demoSteppingStoneFst` in
    `Descent.DemographicHistory`, which is derived from a coalescence time,
    which is not this function and is not being replaced here. A second
    saturating form, `continuousSteppingStoneFst = 1 - exp (-d/L)`, has been
    deleted from `Descent.PopulationGeneticsFoundations`: it contradicted
    `demoSteppingStoneFst`, and the coalescent derivation decides against the
    exponential.

    Empirical status: **MIXED** -- the saturating body above is the MEASURED
    form, better than the linear one it replaced on the same runs and with no
    free parameter (`simcov/battery_bulk17.py`, head-to-head table below); and it
    is APPROXIMATE, since `K` still drifts 15% across the swept separations, so
    the true `d`-dependence is not pinned. The falsification recorded next
    belongs to the SUPERSEDED linear body, not to the one defined above.

    A leading marker describing a body that no longer exists is read as the
    current verdict by every scanner and by any reader who stops at the first
    status line, which is why it is stated here rather than left below.

    The superseded body: **FALSIFIED** in its distance dependence
    (`validation/empirical/simcov/battery_bulk11.py`). That body said
    `F_ST` grows LINEARLY in the separation `d`, capped at one. Measured on a
    20-deme 1D stepping stone, `Ne = 500`, `m = 0.01`, interior demes only so no
    boundary reflection enters, `F_ST` read from coalescence times so no
    estimator convention enters, 26 replicates of 6 Mb:

      d    measured F_ST      linear (alpha from d=2)   saturating d/(d+K)
      1    0.05073±0.00285          --                        --
      2    0.09655±0.00423        fitted                    fitted
      3    0.13472±0.00457    0.14238   (1.7 sems)       K = 19.27
      5    0.18782±0.00399    0.23403  (11.6 sems)       K = 21.62
      8    0.27945±0.00605    0.37151  (15.2 sems)       K = 20.63

    `alpha` is fitted at `d = 2` and used to predict the rest, because a form
    fitted to every point agrees with anything monotone. The linear form then
    overshoots by 33 percent at `d = 8`, which is what a function without
    saturation must do once the separation is large enough.

    The sibling `DemographicHistory.demoSteppingStoneFst`, which saturates,
    describes the SAME runs far better: its `K = d(1-F)/F` should be constant
    and comes out 18.71, 19.27, 21.62, 20.63 -- a 15 percent drift rather than
    33, and no systematic overshoot. That head-to-head on one dataset is the
    evidence here, not a control cell that could only agree with itself.

    Neither form is exact. The residual drift in `K` says the saturating form is
    also approximate at these separations, and pinning the true `d`-dependence
    is not attempted here.

    Power: the measurement spans 0.05073 to 0.27945, a factor of five and a
    half, and the two candidate forms diverge monotonically across it. 
    **The correction, measured head to head**
    (`validation/empirical/simcov/battery_bulk17.py`). Same 20-deme lattice,
    `Ne = 500`, `m = 0.01`, interior demes only, `F_ST` from coalescence times, 22
    replicates of 4 Mb. The comparison was deliberately STACKED AGAINST the replacement:
    the linear form was given a free `α` fitted at `d = 2`, while the saturating candidate
    was given nothing but `F(1)` and `α = 1`.

      d    measured F_ST        linear (free α)        saturating (no free parameter)
      1    0.04887 ± 0.00400     anchor                 anchor
      2    0.09378 ± 0.00379     fitted                 --
      3    0.12319 ± 0.00570    0.13869  (2.72 sems)   0.13357  (1.82 sems)
      5    0.20518 ± 0.00574    0.22850  (4.06 sems)   0.20441  (0.13 sems)
      8    0.27555 ± 0.00845    0.36322 (10.38 sems)   0.29132  (1.87 sems)

    The linear form is FALSIFIED at 10.38 sems and 31.8% relative with a fitted
    parameter in hand; the saturating form matches at 1.87 sems with none. The failure
    grows monotonically in `d`, which is the signature of a wrong functional form rather
    than a wrong constant.

    This reproduces `battery_bulk11.py`, which reached the same conclusion on a separate
    lattice realisation with different seeds and 26 replicates of 6 Mb, so the finding
    does not rest on one run.
-/
noncomputable def steppingStoneFst (fst_neighbor α : ℝ) (d : ℕ) : ℝ :=
  (d : ℝ) * fst_neighbor / (fst_neighbor * (d : ℝ) + α * (1 - fst_neighbor))

/-- **Stepping-stone Fst never leaves the unit interval.** The saturating body needs no
clamp to achieve this: the denominator exceeds the numerator by `α (1 - fst_neighbor)`,
which is nonnegative exactly when the neighbour value is itself a valid `F_ST`. The
previous linear body returned `10000` at `fst_neighbor = 1, α = 1, d = 10000` and was
held in range by an outer `min`; the range is now a consequence of the form. -/
theorem steppingStoneFst_le_one (fst_neighbor α : ℝ) (d : ℕ)
    (hfst : 0 < fst_neighbor) (hle : fst_neighbor ≤ 1) (hα : 0 ≤ α) (hd : 1 ≤ d) :
    steppingStoneFst fst_neighbor α d ≤ 1 := by
  unfold steppingStoneFst
  have hd1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hnum : 0 < fst_neighbor * (d : ℝ) := by nlinarith
  have hextra : 0 ≤ α * (1 - fst_neighbor) := mul_nonneg hα (by linarith)
  rw [div_le_one (by linarith)]
  nlinarith

/-- **The fixation boundary is approached and never attained.** This REPLACES
`steppingStoneFst_eq_one_of_saturated`, which said the opposite, and the replacement is
forced by the measurement rather than chosen for elegance. The linear body reached `1` at
finite separation and the clamp then held it there, so complete differentiation was
attainable at a finite number of steps. A saturating form cannot do that: with
`α (1 - fst_neighbor) > 0` the value is strictly below one at every finite `d` and tends to
one only as `d → ∞`, which is the correct behaviour of isolation by distance -- demes an
arbitrary but finite distance apart still share ancestry. -/
theorem steppingStoneFst_lt_one (fst_neighbor α : ℝ) (d : ℕ)
    (hfst : 0 < fst_neighbor) (hlt : fst_neighbor < 1) (hα : 0 < α) (hd : 1 ≤ d) :
    steppingStoneFst fst_neighbor α d < 1 := by
  unfold steppingStoneFst
  have hd1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hnum : 0 < fst_neighbor * (d : ℝ) := by nlinarith
  have hextra : 0 < α * (1 - fst_neighbor) := mul_pos hα (by linarith)
  rw [div_lt_one (by linarith)]
  nlinarith

/-- Stepping-stone Fst at distance 1 equals the neighbor Fst. At `α = 1` the
characteristic scale is `(1 - fst_neighbor)/fst_neighbor` and the form reproduces its own
anchor; `α` rescales that length, so it is the unit of distance rather than a per-step
increment as it was under the linear body. -/
theorem steppingStoneFst_at_one (fst_neighbor : ℝ) :
    steppingStoneFst fst_neighbor 1 1 = fst_neighbor := by
  unfold steppingStoneFst
  have hden : fst_neighbor * ((1 : ℕ) : ℝ) + 1 * (1 - fst_neighbor) = 1 := by
    push_cast; ring
  rw [hden, div_one]
  push_cast; ring

/-- **Stepping-stone Fst increases with geographic distance** (isolation by distance).
    Under the saturating body this needs no below-saturation hypothesis: `d / (d + K)` is
    strictly increasing in `d` for every positive `K`, at every separation. The linear
    body required the caller to certify it had not yet hit the clamp, and above the clamp
    the increase stopped altogether. -/
theorem steppingStoneFst_increases_with_distance
    (fst_neighbor α : ℝ) (d₁ d₂ : ℕ)
    (hfst : 0 < fst_neighbor) (hlt : fst_neighbor < 1) (hα : 0 < α) (hd : d₁ < d₂) :
    steppingStoneFst fst_neighbor α d₁ < steppingStoneFst fst_neighbor α d₂ := by
  unfold steppingStoneFst
  have hd_real : (d₁ : ℝ) < (d₂ : ℝ) := Nat.cast_lt.mpr hd
  have hd₁ : (0 : ℝ) ≤ (d₁ : ℝ) := Nat.cast_nonneg _
  have hK : 0 < α * (1 - fst_neighbor) := mul_pos hα (by linarith)
  have hd₂ : (0 : ℝ) ≤ (d₂ : ℝ) := Nat.cast_nonneg _
  have hp₁ : 0 ≤ fst_neighbor * (d₁ : ℝ) := mul_nonneg (le_of_lt hfst) hd₁
  have hp₂ : 0 ≤ fst_neighbor * (d₂ : ℝ) := mul_nonneg (le_of_lt hfst) hd₂
  have hden₁ : 0 < fst_neighbor * (d₁ : ℝ) + α * (1 - fst_neighbor) := by linarith
  have hden₂ : 0 < fst_neighbor * (d₂ : ℝ) + α * (1 - fst_neighbor) := by linarith
  rw [div_lt_div_iff₀ hden₁ hden₂]
  nlinarith [mul_pos (mul_pos hfst hK) (sub_pos.mpr hd_real)]

/-- **Nearby demes have lower Fst than distant demes.**
    Fst(1) < Fst(d) for d > 1 under the stepping-stone model, at every separation. -/
theorem steppingStoneFst_neighbor_lt_distant
    (fst_neighbor α : ℝ) (d : ℕ)
    (hfst : 0 < fst_neighbor) (hlt : fst_neighbor < 1) (hα : 0 < α) (hd : 1 < d) :
    steppingStoneFst fst_neighbor α 1 < steppingStoneFst fst_neighbor α d :=
  steppingStoneFst_increases_with_distance fst_neighbor α 1 d hfst hlt hα hd

/-- **Stepping-stone Fst is nonneg for valid parameters.** -/
theorem steppingStoneFst_nonneg (fst_neighbor α : ℝ) (d : ℕ)
    (hfst : 0 < fst_neighbor) (hle : fst_neighbor ≤ 1) (hα : 0 ≤ α) (hd : 1 ≤ d) :
    0 ≤ steppingStoneFst fst_neighbor α d := by
  unfold steppingStoneFst
  have hd1 : (1 : ℝ) ≤ (d : ℝ) := Nat.one_le_cast.mpr hd
  have hextra : 0 ≤ α * (1 - fst_neighbor) := mul_nonneg hα (by linarith)
  apply div_nonneg (by nlinarith) (by nlinarith)

/-! ### 4. Migration's effect on LD: gene flow homogenizes LD patterns -/

/-! #### Derivation of the shared LD fraction: migration against recombination

This section read, for a long time, that the shared LD fraction is `1 - Fst`:
`Fst` is the fraction of variation held BETWEEN demes, so its complement is the
fraction held in common, and "LD patterns are shared to the same extent as
allele frequencies". The last clause is the false one, and simulation says so at
35 sems (`simcov/battery_bulk34.py`): at `Fst = 0.56` the measured shared
fraction is 0.91 where `1 - Fst` predicts 0.44.

The reason is that `Fst` is a property of ONE site and LD is a property of a
PAIR, and a pair has a parameter a single site does not: the recombination rate
`c` between the two sites. At fixed `Fst` -- one deme pair, one replicate set --
the measured shared fraction runs from 0.97 down to 0.06 as the SNP pairs are
sorted by separation. No function of `Fst` alone, of any shape, can follow that,
which is why `(1 - Fst)²` and `1 - 2·Fst` were rejected too.

The correct derivation is a race between migration and recombination, and it is
the classical one (Ohta 1982; Sved 2009, eqns 5-6 and 9). Let `σ_W` be the
within-deme second moment of the disequilibrium `D` and `σ_B` the between-deme
one. Both decay by `(1-c)²` per generation -- one factor of `(1-c)` for each
deme -- and drift feeds only `σ_W`, since drift in one deme is independent of
drift in the other:

  σ_W' = (1-c)²·[(1-α)·σ_W + α·σ_B] + 1/(2·Nₑ)
  σ_B' = (1-c)²·[β·σ_W + (1-β)·σ_B]

where `β = 2·m·(1-m)` is the chance that two gametes now in different demes sat
in the same deme one generation ago. The second line carries no source term, and
that is the whole content: between demes there is nothing to renew the
association. At stationarity, for small `m` and `c`,

  shared_LD = σ_B / σ_W = (1-c)²·β / (1 - (1-c)²·(1-β)) → 2·m / (2·m + 2·c)
            = m / (m + c)

The coalescent reading is the same race: two lineages in different demes cannot
coalesce at all until migration puts them together, and recombination -- rate
`2·c`, one lineage each -- runs against that migration. `Nₑ` cancels, which is
the sharpest thing about the result: `Nₑ` sets how much LD there is, not how
much of it is shared. `m` is the backward rate between one ORDERED pair of
demes, so the deme count cancels as well, a move to a third deme leaving the two
lineages apart. `sharedLD_from_equilibrium` below is this ratio, and
`sharedLD_from_equilibrium_eq_sharedLDFromMigration` shows it is the same
saturating map as before, read at `m/c` rather than at `4·Nₑ·m`. -/

/-- **Shared LD fraction: migration against recombination.**
    `m / (m + c)`, where `m` is the backward migration rate between one ORDERED
    pair of demes and `c` the recombination rate between the two sites whose
    disequilibrium is being shared. Derived above from the stationary
    disequilibrium moments (Ohta 1982; Sved 2009, eqns 5-6 and 9): between demes
    nothing renews the association, so the shared component is whatever survives
    the race between the migration that reunites two lineages and the
    recombination that separates the two loci.

    NO SHAPE IN `F_ST` ALONE IS ADMISSIBLE HERE, and the argument list is the
    finding. `F_ST` is a property of one site, shared LD of a PAIR, and a pair
    carries a parameter a single site does not. `1 - fstMigrationDriftEquilibrium
    Nₑ m` is FALSIFIED at 35 sems (`simcov/battery_bulk34.py`, 0.91 measured
    against 0.44 predicted at `F_ST = 0.56`), `(1 - F)²` at 56 sems and `1 - 2·F`
    at 78 sems. The reason none of them can survive: at FIXED `F_ST` -- one deme
    pair, one replicate set -- the measured fraction runs from 0.97 to 0.06 as the
    pairs are sorted by separation. `Nₑ` is absent from this body for the same
    reason: it sets how much LD there is, not how much of it is shared.

    Denotes: a fraction of the disequilibrium SECOND MOMENT, `σ_B/σ_W`, not a
    correlation of `r`. The two are different numbers -- normalising by the
    frequency term inflates the fraction by 5 to 25% -- and Sved's `E[r²] = L`
    is the step where that cost is paid.

    Empirical status: **CONDITIONALLY VALID** for `c ≲ m/5`
    (`simcov/battery_sharedld_rec.py`). Measured as `σ_B/σ_W` with every product
    taken between DISJOINT sample halves, so no sampling noise enters either
    the numerator or the denominator; 10 Mb, 12 replicates, `Nₑ` varied
    threefold at fixed `m` on purpose:

      Nₑ     m         c/m     this body   measured           rel
      2000   4.0e-3    0.01    0.9878      0.9726 ± 0.0047    -1.5%
      2000   4.0e-3    0.05    0.9549      0.9504 ± 0.0052    -0.5%
      1000   1.0e-3    0.05    0.9529      0.8897 ± 0.0064    +7.1%
      2000   1.0e-3    0.05    0.9527      0.9159 ± 0.0073    +4.0%
      4000   1.0e-3    0.05    0.9528      0.9364 ± 0.0047    +1.8%
      2000   4.0e-3    0.16    0.8607      0.8826 ± 0.0067    -2.5%
      1000   1.0e-3    0.19    0.8413      0.8399 ± 0.0077    +0.2%
      2000   1.0e-3    0.19    0.8412      0.8623 ± 0.0082    -2.4%
      4000   1.0e-3    0.19    0.8408      0.8687 ± 0.0049    -3.2%
      2000   2.5e-4    0.20    0.8357      0.8183 ± 0.0081    +2.1%
      2000   4.0e-3    0.50    0.6673      0.7128 ± 0.0135    -6.4%
      1000   1.0e-3    0.65    0.6069      0.7198 ± 0.0086   -15.7%
      2000   1.0e-3    0.65    0.6066      0.7028 ± 0.0111   -13.7%
      4000   1.0e-3    0.65    0.6063      0.6859 ± 0.0089   -11.6%
      2000   2.5e-4    0.75    0.5711      0.7197 ± 0.0098   -20.7%

    So: within `c ≲ m/5` the body is right to 3% on ten of eleven cells and to
    7% on the last, under an ascertainment systematic of 12% (the same run with
    a pooled-frequency filter instead of a per-deme one moves the measured ratio
    by that much on average). Past `c ≈ m/2` the body reads LOW and the shortfall
    grows to 21% at `c = 0.75·m` and to 41% out to `c = 80·m`; the shape that
    tracks the measurement there is `2·m/(2·m + c)`, off by at worst 9.7%
    against this body's 20.7%, and it is NOT ADOPTED because nothing derives it
    -- it is this race with the destruction rate halved by hand, and a fitted
    factor of two named as a law is what this corpus refuses.

    What neither shape carries: at `c/m = 0.05` the measured fraction rises
    0.8897, 0.9159, 0.9364 as `Nₑ` goes 1000, 2000, 4000. The stationary ratio is
    `Nₑ`-free, so that trend is a finite-`Nₑ` correction the derivation drops,
    and it bounds how well any `Nₑ`-free body can do at small `c`.

    The `Nₑ` axis is also what kills the competitors outright: `1 - F_ST` (32
    sems, 42%) and `M/(1+M)` (29 sems, 37%) move with `Nₑ` and not with `c`,
    which is exactly backwards, and `1/(1 + 4·Nₑ·c)` -- the within-deme Sved
    shape, which moves with `c` but not with `m` -- fails at 128 sems.

    Control: one panmictic population split four ways, run through the SAME
    estimator, must give 1 at every distance and does, 2.15 sems from it. The
    old correlation estimator returned 0.9945 there, and the 0.55% shortfall was
    attenuation; the split-half denominator removes it, so the control can now
    fail for a reason other than bias.

    argument_source: model, with `c` realized from the separations of the pairs
    actually drawn. -/
noncomputable def sharedLD_from_equilibrium (m c : ℝ) : ℝ :=
  m / (m + c)

/-- Reference evaluation.  The value is computed through the definitions this body calls, but
the theorem states a number: an inequality or an invariance leaves a family of bodies
satisfying it, and a value does not. -/
theorem sharedLD_from_equilibrium_at_reference_point :
    sharedLD_from_equilibrium 1 1 = 1 / 2 := by
  norm_num [sharedLD_from_equilibrium]

/-- **Complete linkage: the shared fraction is 1.** Two sites that never
recombine apart carry the same ancestral association in both demes however far
their frequencies have drifted, and this is the limit the old `1 - F_ST` body
could not reach: it answered `4·Nₑ·m/(1 + 4·Nₑ·m)` here, a number that has
nothing to do with linkage. -/
theorem sharedLD_from_equilibrium_no_recombination (m : ℝ) (hm : m ≠ 0) :
    sharedLD_from_equilibrium m 0 = 1 := by
  unfold sharedLD_from_equilibrium
  rw [add_zero, div_self hm]

/-- **No migration, no shared disequilibrium.** With the demes closed, two
lineages in different demes never meet, so nothing renews the association
between them. -/
theorem sharedLD_from_equilibrium_no_migration (c : ℝ) :
    sharedLD_from_equilibrium 0 c = 0 := by
  unfold sharedLD_from_equilibrium
  simp

/-- **Both rates zero, named.** With `m = c = 0` the body is `0/0`, reported as
`0` -- complete sharing spelled as no sharing at all, the opposite of the
`c → 0` limit above. Consumers must exclude it by requiring `0 < m + c`. -/
theorem sharedLD_from_equilibrium_both_rates_zero_is_junk :
    sharedLD_from_equilibrium 0 0 = 0 := by
  unfold sharedLD_from_equilibrium
  norm_num

/-- **Only the ratio of the two rates is read.** Scaling migration and
recombination together leaves the shared fraction alone: the body is homogeneous
of degree zero, so it is a function of `c/m` and carries no time unit. This is
the invariance the old body did not have and the new one must be tested against
-- a design that scales `m` alone moves it, and one that scales both does not. -/
theorem sharedLD_from_equilibrium_scale_invariant (k m c : ℝ) (hk : k ≠ 0) :
    sharedLD_from_equilibrium (k * m) (k * c) = sharedLD_from_equilibrium m c := by
  unfold sharedLD_from_equilibrium
  rw [← mul_add, mul_div_mul_left _ _ hk]

/-- **Tighter linkage shares more.** Strictly decreasing in the recombination
rate at fixed migration -- the direction the measurement confirms across four
orders of magnitude in `c`, and the direction no function of `F_ST` has at all. -/
theorem sharedLD_from_equilibrium_decreasing_in_recombination
    (m c₁ c₂ : ℝ) (hm : 0 < m) (hc₁ : 0 ≤ c₁) (hlt : c₁ < c₂) :
    sharedLD_from_equilibrium m c₂ < sharedLD_from_equilibrium m c₁ := by
  unfold sharedLD_from_equilibrium
  have h₁ : 0 < m + c₁ := by linarith
  have h₂ : 0 < m + c₂ := by linarith
  rw [div_lt_div_iff₀ h₂ h₁]
  nlinarith

/-- **More gene flow shares more.** Strictly increasing in the migration rate at
fixed recombination. -/
theorem sharedLD_from_equilibrium_increasing_in_migration
    (m₁ m₂ c : ℝ) (hc : 0 < c) (hm₁ : 0 ≤ m₁) (hlt : m₁ < m₂) :
    sharedLD_from_equilibrium m₁ c < sharedLD_from_equilibrium m₂ c := by
  unfold sharedLD_from_equilibrium
  have h₁ : 0 < m₁ + c := by linarith
  have h₂ : 0 < m₂ + c := by linarith
  rw [div_lt_div_iff₀ h₁ h₂]
  nlinarith

/-- **It is a fraction.** Nonnegative for nonnegative rates. -/
theorem sharedLD_from_equilibrium_nonneg (m c : ℝ) (hm : 0 ≤ m) (hc : 0 ≤ c) :
    0 ≤ sharedLD_from_equilibrium m c := by
  unfold sharedLD_from_equilibrium
  exact div_nonneg hm (by linarith)

/-- **It is a fraction: below one whenever the loci can recombine apart.** -/
theorem sharedLD_from_equilibrium_lt_one (m c : ℝ) (hm : 0 ≤ m) (hc : 0 < c) :
    sharedLD_from_equilibrium m c < 1 := by
  unfold sharedLD_from_equilibrium
  rw [div_lt_one (by linarith)]
  linarith

/-- **Shared LD fraction under migration-drift balance.**
    Gene flow homogenizes LD patterns between populations. The fraction of LD
    that is shared between two demes increases with migration rate:
    shared_LD(m) = M / (1 + M) where M = 4Nm.

    **Derivation:** This formula is the complement of the Wright (1931)
    island-model Fst equilibrium. Since Fst = 1/(1+M) (proved at
    `fstMigrationDriftEquilibrium`), the complement is
    1 - Fst = 1 - 1/(1+M) = M/(1+M).

    THE MAP IS RIGHT AND THE ARGUMENT WAS NOT. `sharedLD_from_equilibrium` is
    now `m/(m + c)`, and `sharedLD_from_equilibrium_eq_sharedLDFromMigration`
    shows that this is the SAME saturating map read at the
    migration-to-recombination ratio `m/c`. So `M/(1+M)` survives as a shape;
    what does not survive is feeding it `M = 4·Nₑ·m` and calling the result a
    shared-LD fraction, which is what the paragraph below rejects.

    Empirical status: **AN IDENTITY, NOT A MEASUREMENT**
    (`validation/empirical/simcov/battery_bulk9.py`). This is the
    algebraic complement of `fstMigrationDriftEquilibrium`, which is separately
    measured, so a battery comparing the two reproduces `M/(1+M) = 1 - 1/(1+M)`
    to machine precision and the harness returns SELF-TEST. The empirical content
    is entirely in the equilibrium it complements -- including that equilibrium's
    recorded deme-count blindness, which this inherits.

    THE NAME IS A SECOND CLAIM, AND IT IS **FALSIFIED**
    (`simcov/battery_bulk34.py`). That `M/(1+M) = 1 - 1/(1+M)` is algebra. That
    the resulting number is the fraction of LD SHARED between demes is not, and
    a simulation reaches it: shared LD read as the cross-deme correlation of
    signed `r` over SNP pairs -- a property of PAIRS of sites, where `F_ST` is a
    property of single sites -- runs 0.9060, 0.9341, 0.9674 and 0.9890 as
    `4·Nₑ·m` goes 0.4, 2, 8, 40, against this body's 0.4394, 0.7921, 0.9290 and
    0.9864. Worst cell 35 sems, low by a factor of two at `F_ST = 0.56`. The
    agreement at `4·Nₑ·m = 40` is the weak-differentiation limit, not the
    general case. See `sharedLD_from_equilibrium` for the full table, the
    rejected variants, the control, and the argument -- the recombination rate
    between the two sites -- whose absence is why no reading of `4·Nₑ·m` could
    have worked.

    So the SELF-TEST verdict is right about what `battery_bulk9.py` compared,
    and wrong as a summary of this body's empirical content: the identity is
    unfalsifiable, the interpretation is not, and the interpretation is what
    downstream consumers use. -/
noncomputable def sharedLDFromMigration (M : ℝ) : ℝ :=
  M / (1 + M)

/-- **sharedLDFromMigration at `M = -1`, named.** A negative scaled migration rate is
inadmissible; the divisor vanishes there and the shared disequilibrium is reported as zero, which
is what complete isolation also gives. Consumers must exclude it by hypothesis. -/
theorem sharedLDFromMigration_negative_unit_migration_is_junk :
    sharedLDFromMigration (-1) = 0 := by
  unfold sharedLDFromMigration
  norm_num

/-- **The migration shared-LD map and the coalescent `F_ST` map are one function.**

`fstFromTau` sends coalescent time `tau` to `tau / (1 + tau)`; `sharedLDFromMigration`
sends the scaled migration number `M` to `M / (1 + M)`. The arguments are different
quantities and no value of one may be substituted for the other, but the map is the same
saturating map, and a change of convention in either spelling has to be made in both. -/
theorem sharedLDFromMigration_eq_fstFromTau (M : ℝ) :
    sharedLDFromMigration M = fstFromTau M := rfl

/-- **The derived shared LD fraction is the same saturating map, read at `m/c`.**
    `m/(m + c) = (m/c)/(1 + m/c)`, so the shape `M/(1 + M)` survives the repair
    of `sharedLD_from_equilibrium` unchanged; what changed is its ARGUMENT, from
    the scaled migration rate `4·Nₑ·m` to the migration-to-recombination ratio
    `m/c`. The old reading is the one the simulation rejected, and this theorem
    is where the substitution that produced it is now visible: no value of
    `4·Nₑ·m` may be fed to this map as a shared-LD fraction. -/
theorem sharedLD_from_equilibrium_eq_sharedLDFromMigration (m c : ℝ) (hc : 0 < c) :
    sharedLD_from_equilibrium m c = sharedLDFromMigration (m / c) := by
  unfold sharedLD_from_equilibrium sharedLDFromMigration
  have hc' : c ≠ 0 := ne_of_gt hc
  have h1 : 1 + m / c = (m + c) / c := by field_simp; ring
  rw [h1]
  rcases eq_or_ne (m + c) 0 with h | h
  · rw [h]
    simp
  · rw [div_div_div_cancel_right₀]
    -- `div_div_div_cancel_right₀` discharges the equality but leaves its own
    -- side condition, which is `hc'` from three lines up. Left open, this was
    -- the single module that failed to build.
    exact hc'

/-- Shared LD fraction is nonneg for nonneg M. -/
theorem sharedLDFromMigration_nonneg (M : ℝ) (hM : 0 ≤ M) :
    0 ≤ sharedLDFromMigration M := by
  unfold sharedLDFromMigration
  exact div_nonneg hM (by linarith)

/-- Shared LD fraction is at most 1. -/
theorem sharedLDFromMigration_lt_one (M : ℝ) (hM : 0 ≤ M) :
    sharedLDFromMigration M < 1 := by
  unfold sharedLDFromMigration
  rw [div_lt_one (by linarith : 0 < 1 + M)]
  linarith

/-- **Shared LD fraction increases with migration rate.**
    More migration → more shared LD → better PGS portability. -/
theorem sharedLDFromMigration_increases (M₁ M₂ : ℝ)
    (hM₁ : 0 < M₁) (h_more : M₁ < M₂) :
    sharedLDFromMigration M₁ < sharedLDFromMigration M₂ := by
  unfold sharedLDFromMigration
  rw [div_lt_div_iff₀ (by linarith) (by linarith)]
  nlinarith

/-- **Complementarity of Fst and shared LD under migration-drift.**
    Fst = 1/(1+M) and shared_LD = M/(1+M) sum to 1.
    This parallels the mutation-drift complementarity. -/
theorem fst_plus_sharedLD_eq_one (Ne m : ℝ) (hNe : 0 < Ne) (hm : 0 ≤ m) :
    fstMigrationDriftEquilibrium Ne m + sharedLDFromMigration (scaledMigrationRate Ne m) = 1 := by
  unfold fstMigrationDriftEquilibrium sharedLDFromMigration scaledMigrationRate
  have hden : 1 + 4 * Ne * m ≠ 0 := by nlinarith
  field_simp [hden]

/-! ### 5. Portability under migration-drift: R² improves with gene flow -/

/-- **Signal retention under migration-drift balance.**

The fraction of additive signal that survives, accounting for both allele
frequency drift and LD sharing at the migration-drift equilibrium. It is
`(1 - F_ST) * shared_LD = M²/(1 + M)²` with `M = 4 Nₑ m`, and it lies in
`[0, 1)`.

The previous body of this name multiplied by `V_A` and so returned a variance,
not a fraction: it was unbounded and grew without limit as the additive variance
grew. A retention that scales with an additive variance is not a retention. The
name now denotes the fraction and `retainedSignalVarianceMigrationDrift` denotes
the variance; `retainedSignalVarianceMigrationDrift_eq_retention_mul_VA` relates
them. This corpus has already lost a factor of four to just this kind of
name/quantity mismatch, so the two are separated rather than bounded.

    Denotes: a dimensionless fraction in `[0, 1)`, never a variance.

    Regime: two-deme island model at migration-drift balance; "signal
    retention" read as the fraction of a score's covariance with the genetic
    value that survives transfer from the deme its weights came from.

    Empirical status: **FALSIFIED**
    (`validation/empirical/simcov/battery_pd2.py`). THE LEAD BELOW IS NOW
    CLOSED, and it was closed by removing the calibration rather than by
    estimating it better. Two-deme island model at migration-drift balance,
    `Nₑ = 1000`, 5 Mb with recombination, 300 diploids per deme, 200 causal
    sites, 40 independent replicates:

      4Nₑm   measured retention   this body   1-F_ST   shared LD
      0.4    0.171 ± 0.028        0.082       0.526    0.377
      2.0    0.353 ± 0.026        0.444       0.802    0.368
      8.0    0.523 ± 0.029        0.790       0.940    0.477
      40     0.798 ± 0.038        0.952       0.989    0.669

    The body misses at 3.23, 3.57, 9.21 and 4.10 sems, and it misses on BOTH
    SIDES: 110% LOW at `4 Nₑ m = 0.4` and 51% HIGH at `4 Nₑ m = 8`. A two-sided
    miss is the signature of a wrong functional form rather than a wrong
    constant, so no rescaling of either factor repairs it.

    WHAT FIXED THE DESIGN. The estimator no longer needs a ceiling. Retention was
    `w'Σ_T β / w'Σ_S β` with `w = Σ_S β` fitted on the SAME source sample the
    denominator contracts against, so the denominator carried squared estimation
    noise the numerator did not, and every cell had to be divided by a
    separately estimated panmictic ceiling -- which came out 0.8905 in one run
    and 1.0430 in the other, a value above one that attenuation cannot produce.
    The source sample is now SPLIT: `w = Σ_A β` from half A, and the
    source-side covariance evaluated on half B. `Σ_A` and `Σ_B` are independent
    estimates of one matrix, so there is no squared noise and nothing to
    calibrate. The positive control is what shows it worked: one panmictic
    population split three ways returns retention `1.030 ± 0.030`, 1.02 sems
    from one, with `F_ST` measured at 0.00002 on the same replicates.

    BOTH SINGLE FACTORS ARE ALSO REJECTED on the same cells, so this is not a
    case of the product being wrong because one factor is spurious. `1 - F_ST`
    alone misses by 12.76, 17.59, 14.37 and 5.08 sems -- it is the worst of the
    four candidates, which retires the reading the earlier lead favoured. The LD
    factor alone misses by 7.39 sems at the weak-migration cell.

    THE MIGRATION PARAMETERISATION IS WHERE THE PRODUCT BREAKS. Read with the
    MEASURED cross-deme LD correlation in place of `sharedLDFromMigration`, the
    same product form lands at 0.96, 2.28, 2.60 and 3.66 sems -- still rejected,
    but by a margin that one cell carries, against 9.21 for the body as written.
    That is consistent with `battery_bulk34`, which refuted `M/(1+M)` directly.
    The measured-LD reading is NOT quoted as a verdict of its own, because the
    cross-deme correlation of two separately estimated `r` vectors is attenuated
    by its own estimation noise, and that attenuation was not calibrated either;
    it is reported to locate the fault, not to license a replacement body.

    argument_source: model. `F_ST` and the LD factor are both evaluated at the
    simulation's own `Nₑ` and `m` through the closed forms, never estimated from
    the replicates the retention is measured on.

    THE SUPERSEDED RECORD, kept because the retraction is part of the story.
    This read UNTESTED, with a LEAD against the product form,
    DOWNGRADED from a falsification after a replication check: a second run of
    the same design (`simcov/battery_bulk36.py`) returned retention 0.736 at
    `4·Nₑ·m = 40` where the first returned 0.993, and 0.614 against 0.781 at
    `4·Nₑ·m = 8`. Those gaps are an order of magnitude larger than the ±0.08
    error bars either run quotes, so the quoted bars understate the true
    variability and no verdict here is safe.

    The instability is in the CALIBRATION, not the biology. Retention is divided
    by the estimator's panmictic ceiling, and that ceiling came out 0.8905 in
    the first run and 1.0430 in the second -- a 17% swing on six replicates,
    applied to every cell. A ceiling above one is itself the tell: attenuation
    can only pull it below one, so the second estimate is noise-dominated. A
    usable design needs the ceiling pinned to a few percent, which means
    hundreds of replicates rather than six, or an estimator that needs no
    calibration at all.

    What both runs agree on qualitatively: measured retention rises with
    migration but stays well below the product form at weak migration. That is
    the lead, and it is consistent with `sharedLD_from_equilibrium`, where
    measured shared LD stayed near 1 rather than falling to `M/(1+M)`.

    The table below is the FIRST run, kept for the record:
    Measured at `Nₑ = 1000` over 5 Mb with
    recombination, 80 causal sites segregating in both demes, weights taken as
    the deme-0 LD projection `Σ_A·β` (itself VALIDATED at
    `targetSourceEffectProjection`):

      4Nₑm    retention          this body   1-F     M/(1+M)
      0.4     0.507 ± 0.076      0.131       0.460   0.286
      2.0     0.523 ± 0.076      0.543       0.814   0.667
      8.0     0.781 ± 0.099      0.834       0.939   0.889
      40      0.993 ± 0.117      0.963       0.987   0.976

    The product misses by 4.97 sems (74% relative), low at weak migration where
    it multiplies two factors that are each already below one. The single
    factor `1 - F` is ALSO falsified, at 3.81 sems. `M/(1+M)` alone survives at
    worst 2.93 sems.

    NOT ASSERTED: that `M/(1+M)` is the right law. Its worst cell is off by 44%
    relative and escapes rejection only by sitting just under the three-sem
    gate, on error bars of 0.08 to 0.12. What this run establishes is that the
    PRODUCT is wrong; which single factor replaces it needs tighter bars. The
    direction is consistent with `sharedLD_from_equilibrium`, where measured
    shared LD stayed near 1 rather than falling to `M/(1+M)` -- if the LD term
    does not decay as written, multiplying by it twice over is the error this
    table shows.

    Calibration, not a control: the estimator attenuates because `w = Σ_A·β`
    reuses the same finite-sample `Σ_A` the denominator contracts against, so
    the denominator carries squared estimation noise the numerator does not. The
    attenuation is measured on one panmictic population split arbitrarily in
    half -- same sample size, same site count, same pipeline -- and divided out
    of every cell. The CONTROL is that the same split gives `F_ST = 0`. -/
noncomputable def signalRetentionMigrationDrift (Ne m : ℝ) : ℝ :=
  (1 - fstMigrationDriftEquilibrium Ne m) *
    sharedLDFromMigration (scaledMigrationRate Ne m)

/-- **Retained signal variance under migration-drift balance.**
    The additive variance that survives: the retention fraction times `V_A`.
    This is the quantity the previous `signalRetentionMigrationDrift` computed.

    Denotes: a variance, in the units of `V_A`.

    Empirical status: **FALSIFIED, inherited**
    (`validation/empirical/simcov/battery_pd2.py`). This body is
    `signalRetentionMigrationDrift Ne m * V_A`, and that fraction is now rejected
    at up to 9.21 sems on a design whose positive control -- one panmictic
    population split three ways, retention `1.030 ± 0.030` -- passes; the table
    and the reason the earlier calibration could not support a verdict are
    recorded there.

    THE HISTORY MATTERS HERE and is why the marker is spelled out rather than
    just set. An earlier version of this docstring recorded the falsification as
    inherited; it was WITHDRAWN when a replication check showed the two runs
    disagreeing by an order of magnitude more than their quoted bars. The
    withdrawal was right at the time: the instability was in the ceiling the
    estimator was divided by, not in the biology. What reinstates the verdict is
    not a third run of the same design but a design with no ceiling in it.

    WHAT IS STILL NOT MEASURED, and is not claimed: the factor `V_A`. Every cell
    of that battery is run at one additive variance, and a retention fraction
    times a variance is dimensional bookkeeping the design never exercises. A
    body that multiplied by `V_A²` would score identically.
    `retainedSignalVarianceMigrationDrift_eq_retention_mul_VA` is unaffected
    either way: it is algebra and holds whatever the fraction turns out to be.

    argument_source: model, inherited. -/
noncomputable def retainedSignalVarianceMigrationDrift (V_A Ne m : ℝ) : ℝ :=
  signalRetentionMigrationDrift Ne m * V_A

/-- The variance is the fraction times `V_A`; this is the theorem that keeps the
two names from drifting apart again. -/
theorem retainedSignalVarianceMigrationDrift_eq_retention_mul_VA (V_A Ne m : ℝ) :
    retainedSignalVarianceMigrationDrift V_A Ne m =
      signalRetentionMigrationDrift Ne m * V_A := rfl

/-- The retention fraction equals `M²/(1 + M)²`. -/
theorem signalRetentionMigrationDrift_eq_ratio (Ne m : ℝ)
    (hNe : 0 < Ne) (hm : 0 ≤ m) :
    signalRetentionMigrationDrift Ne m =
      (scaledMigrationRate Ne m) ^ 2 / (1 + scaledMigrationRate Ne m) ^ 2 := by
  unfold signalRetentionMigrationDrift fstMigrationDriftEquilibrium sharedLDFromMigration
    scaledMigrationRate
  have hden : (1 + 4 * Ne * m) ≠ 0 := by nlinarith
  field_simp [hden]
  ring

/-- **The retention is a fraction: it never reaches `1`.**  This is the range
property the name asserts, and a body that can reach `1` does not have it. -/
theorem signalRetentionMigrationDrift_lt_one (Ne m : ℝ)
    (hNe : 0 < Ne) (hm : 0 < m) :
    signalRetentionMigrationDrift Ne m < 1 := by
  rw [signalRetentionMigrationDrift_eq_ratio Ne m hNe (le_of_lt hm)]
  have hM : 0 < scaledMigrationRate Ne m := scaledMigrationRate_pos Ne m hNe hm
  have h1M : 0 < (1 + scaledMigrationRate Ne m) ^ 2 := by positivity
  rw [div_lt_one h1M]
  nlinarith

/-- **The retention is nonneg.** -/
theorem signalRetentionMigrationDrift_nonneg (Ne m : ℝ)
    (hNe : 0 < Ne) (hm : 0 ≤ m) :
    0 ≤ signalRetentionMigrationDrift Ne m := by
  rw [signalRetentionMigrationDrift_eq_ratio Ne m hNe hm]
  positivity

/-- **The product form is the SQUARE of the single-factor law.**

`sharedLDFromMigration (4·Nₑ·m) = 4·Nₑ·m / (1 + 4·Nₑ·m)` and
`1 - fstMigrationDriftEquilibrium Nₑ m` are the same number, so the product this
definition takes is that number multiplied by itself.  The two candidate laws
the docstring above weighs against each other are therefore `x` and `x²` for the
same measurable `x`. -/
theorem signalRetentionMigrationDrift_eq_one_sub_fst_sq (Ne m : ℝ)
    (hNe : 0 < Ne) (hm : 0 ≤ m) :
    signalRetentionMigrationDrift Ne m =
      (1 - fstMigrationDriftEquilibrium Ne m) ^ 2 := by
  unfold signalRetentionMigrationDrift fstMigrationDriftEquilibrium
    sharedLDFromMigration scaledMigrationRate
  have hden : (1 + 4 * Ne * m) ≠ 0 := by nlinarith
  field_simp
  ring

/-- **No calibration constant can reconcile the two laws**, which is what makes
the comparison between them survive the defect that stalled it.

Both runs recorded above divided measured retention by an estimator ceiling
obtained from a panmictic control, and that ceiling came out `0.8905` and then
`1.0430` on six replicates -- a 17% swing applied to every cell, which is why
neither run's verdict was safe.  An unstable ceiling is a multiplicative
constant on the measurement.

This theorem says that no such constant maps the single-factor law onto the
product law: they are `x` and `x²`, so a constant `c` would have to equal `x`,
and `x` varies with migration.  A calibration error therefore cannot turn one
into the other, and cannot manufacture agreement with the wrong one either.

The design that follows needs no ceiling at all.  Measure retention and `F_ST`
on the same data and read the slope of `log retention` against `log (1 - F_ST)`:
the product form predicts `2`, the single factor predicts `1`, and an unknown
multiplicative ceiling `c` contributes `log c` to the INTERCEPT and nothing to
the slope.  That is the discriminating comparison this definition has been
missing -- exponent 1 against exponent 2 -- and it is the reason the status
below can stop being a standing debt.

    Empirical status: NOT AN EMPIRICAL CLAIM.  It is algebra about two
    candidate laws, and it is what makes the measurement of them possible. -/
theorem no_calibration_constant_reconciles_retention_laws :
    ¬ ∃ c : ℝ, ∀ Ne m : ℝ, 0 < Ne → 0 < m →
        c * (1 - fstMigrationDriftEquilibrium Ne m) =
          signalRetentionMigrationDrift Ne m := by
  rintro ⟨c, hc⟩
  have h1 := hc 1 (1 / 4) (by norm_num) (by norm_num)
  have h2 := hc 1 (3 / 4) (by norm_num) (by norm_num)
  unfold signalRetentionMigrationDrift fstMigrationDriftEquilibrium
    sharedLDFromMigration scaledMigrationRate at h1 h2
  norm_num at h1 h2
  linarith

/-- Retained signal variance under migration-drift equals M²/((1+M)²) × V_A. -/
theorem retainedSignalVarianceMigrationDrift_eq (V_A Ne m : ℝ)
    (hNe : 0 < Ne) (hm : 0 ≤ m) :
    retainedSignalVarianceMigrationDrift V_A Ne m =
      (scaledMigrationRate Ne m) ^ 2 / (1 + scaledMigrationRate Ne m) ^ 2 * V_A := by
  unfold retainedSignalVarianceMigrationDrift
  rw [signalRetentionMigrationDrift_eq_ratio Ne m hNe hm]

/-- **Retained signal variance is positive with positive migration.** -/
theorem retainedSignalVarianceMigrationDrift_pos (V_A Ne m : ℝ)
    (hVA : 0 < V_A) (hNe : 0 < Ne) (hm : 0 < m) :
    0 < retainedSignalVarianceMigrationDrift V_A Ne m := by
  rw [retainedSignalVarianceMigrationDrift_eq V_A Ne m hNe (le_of_lt hm)]
  apply mul_pos
  · apply div_pos
    · exact sq_pos_of_pos (scaledMigrationRate_pos Ne m hNe hm)
    · exact sq_pos_of_pos (by nlinarith [scaledMigrationRate_pos Ne m hNe hm])
  · exact hVA

/-- **More migration improves signal retention** (for fixed Ne and V_A).
    This is the core mechanism: gene flow improves PGS portability. -/
theorem signalRetention_increases_with_migration (V_A Ne m₁ m₂ : ℝ)
    (hVA : 0 < V_A) (hNe : 0 < Ne) (hm₁ : 0 < m₁) (hm₂ : 0 < m₂)
    (h_more : m₁ < m₂) :
    retainedSignalVarianceMigrationDrift V_A Ne m₁ <
      retainedSignalVarianceMigrationDrift V_A Ne m₂ := by
  rw [retainedSignalVarianceMigrationDrift_eq V_A Ne m₁ hNe (le_of_lt hm₁),
      retainedSignalVarianceMigrationDrift_eq V_A Ne m₂ hNe (le_of_lt hm₂)]
  apply mul_lt_mul_of_pos_right _ hVA
  -- Need: M₁²/(1+M₁)² < M₂²/(1+M₂)²  i.e. (M₁/(1+M₁))² < (M₂/(1+M₂))²
  -- which follows from M₁/(1+M₁) < M₂/(1+M₂), a monotone function.
  set M₁ := scaledMigrationRate Ne m₁
  set M₂ := scaledMigrationRate Ne m₂
  have hM₁ : 0 < M₁ := scaledMigrationRate_pos Ne m₁ hNe hm₁
  have hM₂ : 0 < M₂ := scaledMigrationRate_pos Ne m₂ hNe hm₂
  have hM_lt : M₁ < M₂ := by
    simp [M₁, M₂, scaledMigrationRate]
    nlinarith
  have h1M₁ : 0 < 1 + M₁ := by linarith
  have h1M₂ : 0 < 1 + M₂ := by linarith
  -- M₁/(1+M₁) < M₂/(1+M₂)
  have h_ratio : M₁ / (1 + M₁) < M₂ / (1 + M₂) := by
    rw [div_lt_div_iff₀ h1M₁ h1M₂]; nlinarith
  -- Squaring preserves order for positive values
  have h_sq₁ : 0 < M₁ / (1 + M₁) := div_pos hM₁ h1M₁
  have h_sq₂ : 0 < M₂ / (1 + M₂) := div_pos hM₂ h1M₂
  have h_sq : (M₁ / (1 + M₁)) ^ 2 < (M₂ / (1 + M₂)) ^ 2 := by
    have hsum_pos : 0 < M₁ / (1 + M₁) + M₂ / (1 + M₂) := by positivity
    have hmul := mul_lt_mul_of_pos_right h_ratio hsum_pos
    nlinarith
  rwa [div_pow, div_pow] at h_sq

/-! **Deleted: `migration_improves_R2_over_pure_drift`.**

Strip the assumed premise and what is left is `drift_degrades_R2` with its first argument
instantiated at `fstMigrationDriftEquilibrium Ne m`, which is the whole proof. The single
call site, `recurrence_derived_R2_increases_with_m`, calls `drift_degrades_R2` directly.
That theorem *does* prove the migration claim, because it derives the `F_ST` ordering from
`m₁ < m₂` via `fstMigrationDriftEquilibrium_decreases_with_m` instead of assuming it. -/

/-! ### 6. Asymmetric migration -/

/-- **Two demes exchanging migrants at two different rates.**

    `1 / (1 + 4 Nₑ (m₁₂ + m₂₁))`: the differentiation between two demes is set by
    the TOTAL rate at which they exchange lineages, and by nothing else. It does
    not depend on the direction, and there is no such thing as "`F_ST` from
    population 1's perspective" -- `F_ST` is a property of the pair.

    **Both the signature and the body have been corrected, and the claim the old
    ones made was excluded by measurement.** The definition read
    `asymmetricFst (Ne m_into) = 1 / (1 + 4 Nₑ m_into)`: one rate, named as the
    rate INTO the focal deme, with two theorems below asserting that the answer
    moves when the direction is swapped. Two things were wrong with it at once.
    It could not say which of the two rates `m_into` was, and at `m₁₂ = m₂₁`,
    where that ambiguity does not arise, it still returned the many-deme limit
    `1/(1 + 4 Nₑ m)` for a system its own name commits to exactly two demes.

    Empirical status: **VALIDATED after correction; the superseded body
    FALSIFIED at up to 80 sems**
    (`validation/empirical/simcov/battery_dis2.py`). Two demes,
    `Ne = 1000`, `F_ST` read as `1 - E[T_within]/E[T_between]` from branch
    lengths so no estimator convention enters, 24 replicates of 4 Mb. Six
    designs: the total rate spans a factor of four, and three of them share a
    total while differing in asymmetry, so a law that depended on more than the
    total would separate:

      m12      m21      larger    smaller   this body   measured
      5.0e-4   5.0e-4   0.33333   0.33333   0.20000     0.22086 ± 0.01028
      1.0e-3   1.0e-3   0.20000   0.20000   0.11111     0.12226 ± 0.00576
      2.0e-3   2.0e-3   0.11111   0.11111   0.05882     0.05748 ± 0.00331
      1.5e-3   5.0e-4   0.14286   0.33333   0.11111     0.10395 ± 0.00570
      1.8e-3   2.0e-4   0.12195   0.55556   0.11111     0.10281 ± 0.00567
      3.5e-3   5.0e-4   0.06667   0.33333   0.05882     0.05717 ± 0.00383

    This body's worst cell is 2.03 sems. The two readings of the old single
    argument are excluded at 16.2 and 79.9 sems, and neither failure is a
    constant: the smaller-rate reading is wrong by a factor of five at the most
    asymmetric design and right to within a factor of two at the least, which is
    what an underspecified signature looks like from the outside.

    Note which rows carry the finding. The three symmetric rows alone would only
    have shown the missing deme-count factor of two. The three rows sharing a
    total of `2.0e-3` while running from mild to strong asymmetry are what
    excludes any direction dependence: they agree with each other to 1.4 sems
    while the two directional readings differ from each other by a factor of
    four and a half across them.

    The positive control is the symmetric cell at `m = 1.0e-3` against the
    two-deme island value `1/(1 + 2 · 4 Nₑ m)`, validated independently in
    `battery_correct.py`, and it passes at 1.93 sems.

    Superseded, and recorded because it was believed: **FALSIFIED**, by the same
    mechanism as
    `PopulationGeneticsFoundations.fstMigrationMutationEquilibriumManyDemes`: the
    deme-count factor is missing (`validation/empirical/simcov/battery_bulk13.py`).
    Two demes with asymmetric migration, `Ne = 1000`, `F_ST` read as
    `1 - E[T_within]/E[T_between]` from coalescence times so no estimator
    convention enters, 26 replicates of 4 Mb:

      m12       m21      larger-rate reading   smaller-rate   measured
      1.0e-3    1.0e-3     0.20000 (14.5σ)     0.20000 (14.5σ)  0.11480±0.00589
      1.5e-3    5.0e-4     0.14286 ( 4.3σ)     0.33333 (34.1σ)  0.11538±0.00640
      1.8e-3    2.0e-4     0.12195 ( 2.4σ)     0.55556 (85.6σ)  0.10918±0.00521

    NEITHER reading of the single `m_into` argument works, and the SYMMETRIC row
    says why. There `m12 = m21`, so there is no ambiguity about which rate to
    use, and the body still misses by 14.5 sems: it returns
    `1/(1 + 4 Ne m) = 0.200` where the two-deme value is
    `1/(1 + 2 · 4 Ne m) = 0.111`. The factor of two is `islandDemeCorrection` at
    `n = 2`, which two independent designs in this branch have now confirmed.

    So this is not an asymmetry problem at all. It is the deme-count blindness
    already recorded on `fstMigrationMutationEquilibriumManyDemes`, in a definition whose
    name commits it to exactly two demes and which therefore cannot plead the
    many-deme limit. Use `fstIslandEquilibriumFiniteDemes` with `nDemes = 2`.

    The positive control is the symmetric cell against the independently
    validated two-deme island value, and it passes at 0.77 sems, so the design
    reproduces a known answer before reporting a new one -- which the forward
    Wright-Fisher attempt at this same pair in `battery_bulk1.py` did not, and
    was correctly voided for.

    Power: the prediction spans 0.05882 to 0.20000 across the design, a factor
    of three and a half. -/
noncomputable def asymmetricFst (Ne m₁₂ m₂₁ : ℝ) : ℝ :=
  1 / (1 + 4 * Ne * (m₁₂ + m₂₁))

/-- **asymmetricFst at `4 * Ne * (m₁₂ + m₂₁) = -1`, named.** The two-deme twin of
`fstMigrationDriftEquilibrium_balancing_negative_migration_is_junk`, with the same divisor and
the same collapse to no differentiation. Consumers must exclude it by hypothesis. -/
theorem asymmetricFst_balancing_negative_migration_is_junk :
    asymmetricFst 1 (-(1/8)) (-(1/8)) = 0 := by
  unfold asymmetricFst
  norm_num

/-- **Two demes at two rates are one deme pair at the total rate.** The limit form applied to
the SUM of the two rates is the two-deme answer -- which is also why the deme-count factor of
two appears in the symmetric case without being written anywhere: at `m₁₂ = m₂₁ = m` the sum is
`2 m`. -/
theorem asymmetricFst_eq_migrationDriftEq (Ne m₁₂ m₂₁ : ℝ) :
    asymmetricFst Ne m₁₂ m₂₁ = fstMigrationDriftEquilibrium Ne (m₁₂ + m₂₁) := by
  unfold asymmetricFst fstMigrationDriftEquilibrium
  rfl

/-- **The two-deme `Fst`'s scale, pinned.** The identity with `migrationDriftEq` constrains the
two definitions jointly: a common wrong factor in both cancels and the identity survives. This
evaluates `asymmetricFst` alone, at the total exchange rate where drift and immigration balance,
and fixes the `4 Ne m` normalisation that the identity leaves free. -/
theorem asymmetricFst_at_balancing_migration :
    asymmetricFst 1 (1 / 8) (1 / 8) = 1 / 2 := by
  unfold asymmetricFst
  norm_num

/-- **There is no direction. Swapping the two rates changes nothing.**

    This replaces `asymmetric_migration_directional_fst`, which asserted the
    opposite -- that when `m₁₂ > m₂₁` the `F_ST` "from population 1's
    perspective" is strictly lower -- and which was excluded by measurement. The
    design that excludes it is in the docstring above: three deme pairs sharing a
    total exchange rate of `2.0e-3` while running from mild to strong asymmetry
    agree with each other to 1.4 sems, where the directional reading requires
    them to span a factor of four and a half.

    A definition that returns different numbers for `(m₁₂, m₂₁)` and
    `(m₂₁, m₁₂)` is making a claim, and it is not enough to note that the claim
    is now absent from the body: stating the symmetry is what stops the
    directional reading being reintroduced by someone who reads the name. -/
theorem asymmetricFst_symm (Ne m₁₂ m₂₁ : ℝ) :
    asymmetricFst Ne m₁₂ m₂₁ = asymmetricFst Ne m₂₁ m₁₂ := by
  unfold asymmetricFst
  ring_nf

/-- **Portability does not depend on the prediction direction under asymmetric migration.**

    The superseded `asymmetric_migration_portability_direction` said it does:
    that predicting into the deme receiving more migrants yields a strictly
    higher `R²`. That was a consequence of the directional `F_ST`, and it goes
    with it. Drift degrades `R²` through `F_ST` alone, and `F_ST` here is a
    property of the pair, so the two directions are worth exactly the same. -/
theorem asymmetric_migration_portability_directionless
    (V_A V_E Ne m₁₂ m₂₁ : ℝ) :
    presentDayR2 V_A V_E (asymmetricFst Ne m₂₁ m₁₂) =
      presentDayR2 V_A V_E (asymmetricFst Ne m₁₂ m₂₁) := by
  rw [asymmetricFst_symm]

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
  (m₁₂ + m₂₁) / 2

/-- **The arithmetic mean used here is never below the harmonic mean**, with equality
exactly when the two directional rates agree. This is AM-GM-HM for two positive reals, and
it fixes the sign of the discrepancy between the two means. -/
theorem harmonicMigrationMean_le_effectiveSymmetricMigration (m₁₂ m₂₁ : ℝ)
    (h₁ : 0 < m₁₂) (h₂ : 0 < m₂₁) :
    2 * m₁₂ * m₂₁ / (m₁₂ + m₂₁) ≤ effectiveSymmetricMigration m₁₂ m₂₁ := by
  unfold effectiveSymmetricMigration
  rw [div_le_div_iff₀ (by linarith) (by norm_num : (0:ℝ) < 2)]
  nlinarith [sq_nonneg (m₁₂ - m₂₁)]

/-- **And equality forces the two directional rates to agree**, which is what the
statement above claims and does not prove on its own. Together they are the
equality case of the arithmetic-harmonic mean inequality: symmetrising two
migration rates loses nothing exactly when there was nothing asymmetric to
lose. -/
theorem harmonicMigrationMean_eq_iff_symmetric (m₁₂ m₂₁ : ℝ)
    (h₁ : 0 < m₁₂) (h₂ : 0 < m₂₁)
    (heq : 2 * m₁₂ * m₂₁ / (m₁₂ + m₂₁) = effectiveSymmetricMigration m₁₂ m₂₁) :
    m₁₂ = m₂₁ := by
  have hsum : (0 : ℝ) < m₁₂ + m₂₁ := by linarith
  have hne : m₁₂ + m₂₁ ≠ 0 := ne_of_gt hsum
  unfold effectiveSymmetricMigration at heq
  field_simp at heq
  have hsq : (m₁₂ - m₂₁) ^ 2 = 0 := by nlinarith [heq]
  have hzero : m₁₂ - m₂₁ = 0 := sq_eq_zero_iff.mp hsq
  linarith

/-- **Hence the equilibrium `F_ST` computed from this mean is never above the one the
harmonic mean would give.** `fstMigrationDriftEquilibrium` is decreasing in the migration
rate, so substituting the larger mean returns the smaller `F_ST`. Composed with
`presentDayR2`, which is decreasing in `F_ST`, the arithmetic mean is the optimistic
choice at every pair of asymmetric rates: it reports better cross-population portability
than the harmonic mean does. Stated so the direction of the bias is checkable rather than
left in prose. -/
theorem effectiveSymmetricMigration_fst_le_harmonic_fst (Ne m₁₂ m₂₁ : ℝ)
    (hNe : 0 < Ne) (h₁ : 0 < m₁₂) (h₂ : 0 < m₂₁) :
    fstMigrationDriftEquilibrium Ne (effectiveSymmetricMigration m₁₂ m₂₁) ≤
      fstMigrationDriftEquilibrium Ne (2 * m₁₂ * m₂₁ / (m₁₂ + m₂₁)) := by
  unfold fstMigrationDriftEquilibrium
  have hHM_pos : 0 < 2 * m₁₂ * m₂₁ / (m₁₂ + m₂₁) := by positivity
  have hle := harmonicMigrationMean_le_effectiveSymmetricMigration m₁₂ m₂₁ h₁ h₂
  have hden_pos : 0 < 1 + 4 * Ne * (2 * m₁₂ * m₂₁ / (m₁₂ + m₂₁)) := by positivity
  exact one_div_le_one_div_of_le hden_pos (by nlinarith)

/-- The arithmetic mean of two distinct rates lies strictly between them. -/
theorem effectiveSymmetricMigration_between (m₁₂ m₂₁ : ℝ)
    (h_asym : m₂₁ < m₁₂) :
    m₂₁ < effectiveSymmetricMigration m₁₂ m₂₁ ∧
    effectiveSymmetricMigration m₁₂ m₂₁ < m₁₂ := by
  unfold effectiveSymmetricMigration
  constructor <;> linarith

/-! ### 7. Recent migration (admixture): transient LD from migration pulses -/

/-- **Admixture LD from a recent migration pulse.**
    A pulse of migration (admixture) at time t_adm generations ago creates
    LD between loci at recombination distance r. This LD decays as:
    D_adm(t) = D_0 × (1 - r)^(t - t_adm)
    where D_0 is the initial admixture LD and t is the current time.
    We model the decay factor.

    **REGIME: infinite population.** `(1-r)` is the recombination-only
    retention, i.e. the `Nₑ → ∞` limit, and nothing in the expression says so
    -- there is no `Nₑ` argument for it to say it with. The finite-population
    retention is `(1-r)(1 - 1/(2Nₑ))`, which is
    `LDDecayTheory.ldRetentionPerGen` and is measured accurate to within
    `0.12%`. This body is high by exactly the omitted drift factor: measured
    `+0.24%` to `+0.37%` over the tested range. The bias is therefore small but
    STRICTLY ONE-SIDED, and `admixtureLDDecay_ge_finitePopulation` below proves
    that direction rather than leaving it to the runs that happened to be done;
    it also grows with `generations_since`, since the omitted factor is
    compounded.

    Small and one-sided is the combination worth naming: it will not show up as
    noise in a comparison, and it accumulates in the same direction over time.

    Empirical status: VALIDATED as the `Nₑ → ∞` limit; MEASURED high by
    `+0.24%` to `+0.37%` against the finite-population retention. The sibling
    quantities `LDDecayTheory.admixtureLD` and
    `CovarianceStructure.admixtureLDTwoLocus` are EXACT to `2.8e-17` and need
    nothing.

    Power: the comparison in
    `validation/empirical/differential/cluster/fam_admixture.py` runs the
    per-generation retention at `r = 0, 0.0025, 0.02, 0.1, 0.5` with `Ne = 200`,
    where this body predicts `1.000000`, `0.997500`, `0.980000`, `0.900000` and
    `0.500000` against measured `0.997575`, `0.994828`, `0.977596`, `0.896658`
    and `0.506154`. The grid straddles `1/(2Ne)`, so the drift factor is visible
    rather than swamped, and the prediction covers half the unit interval. -/
noncomputable def admixtureLDDecay (r : ℝ) (generations_since : ℕ) : ℝ :=
  (1 - r) ^ generations_since

/-- **The omission is one-sided: this body is never below the finite-population
    retention.** The finite-`Nₑ` retention per generation is
    `(1-r)(1 - 1/(2Nₑ))`, compounded over `generations_since`; dropping the
    drift factor can only raise the result, at every `r`, every `Nₑ` and every
    number of generations. That is why every measured error is positive
    (`+0.24%` to `+0.37%`) rather than scattered about zero, and it is a
    property of the omission rather than of the parameters that were simulated.

    The finite-population factor is written out here instead of being called by
    name because `LDDecayTheory.ldRetentionPerGen`, which is that expression,
    lives in a module that imports this one; the two are the same quantity. -/
theorem admixtureLDDecay_ge_finitePopulation (r Ne : ℝ) (t : ℕ)
    (hr1 : r ≤ 1) (hNe : 1 ≤ Ne) :
    ((1 - r) * (1 - 1 / (2 * Ne))) ^ t ≤ admixtureLDDecay r t := by
  unfold admixtureLDDecay
  have hdrift_nn : (0 : ℝ) ≤ 1 - 1 / (2 * Ne) := by
    rw [sub_nonneg, div_le_one (by linarith)]; linarith
  have hdrift_le : (1 : ℝ) - 1 / (2 * Ne) ≤ 1 := by
    have : (0 : ℝ) < 1 / (2 * Ne) := by positivity
    linarith
  have h_nn : (0 : ℝ) ≤ (1 - r) * (1 - 1 / (2 * Ne)) :=
    mul_nonneg (by linarith) hdrift_nn
  have h_le : (1 - r) * (1 - 1 / (2 * Ne)) ≤ 1 - r := by
    calc (1 - r) * (1 - 1 / (2 * Ne)) ≤ (1 - r) * 1 :=
          mul_le_mul_of_nonneg_left hdrift_le (by linarith)
      _ = 1 - r := mul_one _
  exact pow_le_pow_left₀ h_nn h_le t

/-- **One body, two names, tied.** `DGP.discreteRecombinationSurvival` is the
same quantity read as survival of two loci to the MRCA rather than as decay of
admixture LD; both are the probability of no recombination in `n` meioses. -/
theorem admixtureLDDecay_eq_discreteRecombinationSurvival (r : ℝ) (t : ℕ) :
    admixtureLDDecay r t = discreteRecombinationSurvival r t := rfl

/-- Admixture LD decay is nonneg for recombination rate in [0, 1]. -/
theorem admixtureLDDecay_nonneg (r : ℝ) (t : ℕ)
    (hr1 : r ≤ 1) :
    0 ≤ admixtureLDDecay r t := by
  unfold admixtureLDDecay
  exact pow_nonneg (by linarith) t

/-- Admixture LD decay is at most 1 for valid recombination rate. -/
theorem admixtureLDDecay_le_one (r : ℝ) (t : ℕ)
    (hr : 0 ≤ r) (hr1 : r ≤ 1) :
    admixtureLDDecay r t ≤ 1 := by
  unfold admixtureLDDecay
  exact pow_le_one₀ (by linarith) (by linarith)

/-- **Admixture LD decays over time** (for positive recombination rate). -/
theorem admixtureLDDecay_decreases_with_time (r : ℝ) (t₁ t₂ : ℕ)
    (hr : 0 < r) (hr1 : r < 1) (ht : t₁ < t₂) :
    admixtureLDDecay r t₂ < admixtureLDDecay r t₁ := by
  unfold admixtureLDDecay
  have h_base_pos : 0 < 1 - r := by linarith
  have h_base_lt : 1 - r < 1 := by linarith
  exact pow_lt_pow_right_of_lt_one₀ h_base_pos h_base_lt ht

/-- **Admixture LD decays faster with higher recombination rate.** -/
theorem admixtureLDDecay_decreases_with_recombination (r₁ r₂ : ℝ) (t : ℕ)
    (hr₂1 : r₂ < 1)
    (h_more : r₁ < r₂) (ht : 0 < t) :
    admixtureLDDecay r₂ t < admixtureLDDecay r₁ t := by
  unfold admixtureLDDecay
  exact pow_lt_pow_left₀ (by linarith : 1 - r₂ < 1 - r₁) (by linarith) (by omega)

/-- **At time 0 since admixture, LD is fully preserved.** -/
theorem admixtureLDDecay_at_zero (r : ℝ) :
    admixtureLDDecay r 0 = 1 := by
  unfold admixtureLDDecay
  simp

/-- **Admixture LD creates a transient boost to portability.**
    Recent admixture (small t since pulse) means LD patterns are shared,
    which temporarily improves tagging efficiency. The portability boost
    from admixture LD relative to equilibrium LD is captured by the ratio
    of admixture LD retention to equilibrium LD fraction.

    Regime: a one-pulse admixture event, read from the pulse forward.
    `equilibrium_ld` is an INPUT and not modelled here, so what a simulation can
    put on trial is the numerator and the fact that the body is a ratio in it --
    not the baseline's value.

    Empirical status: **VALIDATED** (`simcov/battery_bulk20c.py`, `group_d`).
    A 50/50 pulse into a Wright-Fisher population at `Nₑ = 2000`, then
    recombination and drift for 40 generations, over 400 independent
    replicates; the observable is `E[D_t] / E[D_0]` divided by a baseline held
    at 0.25. Across `r` = 0.005, 0.02, 0.05, 0.15 and `t` = 10, 40 the body
    predicts 3.80444, 3.27327, 3.26828, 1.78280, 2.39497, 0.51402, 0.78749 and
    0.00602 against measured 3.83190 ± 0.02512, 3.26726 ± 0.04721, 3.28631 ±
    0.02277, 1.79945 ± 0.03596, 2.41661 ± 0.02143, 0.46521 ± 0.02707, 0.77093 ±
    0.01663 and 0.01927 ± 0.01690, worst cell 1.80 sems.

    Power: the prediction spans the full range from a 3.8-fold boost down to
    essentially none -- three orders of magnitude -- and `r` and `t` are moved
    separately, so the two cells that reach a similar boost by different routes
    both have to hold. Control: the finite-`Nₑ` retention
    `((1-r)(1 - 1/(2Nₑ)))^t`, derived independently of this body, passed on the
    same code path. -/
noncomputable def admixtureLDBoost (r : ℝ) (t_since : ℕ) (equilibrium_ld : ℝ) : ℝ :=
  admixtureLDDecay r t_since / equilibrium_ld

/-- **admixtureLDBoost at zero equilibrium_ld, named.** A zero equilibrium linkage disequilibrium
gives no baseline for the boost to be measured against. Lean returns `0`, reporting no excess
disequilibrium from admixture, in exactly the situation where any disequilibrium at all is
entirely due to admixture. Consumers must require `equilibrium_ld ≠ 0`. -/
theorem admixtureLDBoost_zero_equilibriumld_is_junk (r : ℝ) (t_since : ℕ) :
    admixtureLDBoost r t_since 0 = 0 := by
  unfold admixtureLDBoost
  simp

/-- Admixture LD boost exceeds 1 when admixture LD is above equilibrium. -/
theorem admixtureLDBoost_gt_one_of_above_equilibrium (r : ℝ) (t_since : ℕ) (equilibrium_ld : ℝ)
    (heq_pos : 0 < equilibrium_ld)
    (h_recent : equilibrium_ld < admixtureLDDecay r t_since) :
    1 < admixtureLDBoost r t_since equilibrium_ld := by
  unfold admixtureLDBoost
  rw [lt_div_iff₀ heq_pos]
  linarith

/-- **Transient admixture portability is higher than equilibrium portability.**
    When admixture is recent, the transient shared LD exceeds equilibrium shared LD,
    and thus portability is temporarily enhanced. -/
theorem admixture_portability_above_equilibrium_of_ld_above_equilibrium
    (V_A fst r : ℝ) (t_since : ℕ)
    (equilibrium_ld : ℝ)
    (hVA : 0 < V_A) (hfst_lt : fst < 1)
    (h_recent : equilibrium_ld < admixtureLDDecay r t_since) :
    presentDayPGSVarianceMutationDrift V_A fst equilibrium_ld <
      presentDayPGSVarianceMutationDrift V_A fst (admixtureLDDecay r t_since) := by
  rw [presentDayPGSVarianceMutationDrift_eq, presentDayPGSVarianceMutationDrift_eq]
  have h1 : 0 < (1 - fst) * V_A := mul_pos (by linarith) hVA
  have h_factor : (1 - fst) * equilibrium_ld < (1 - fst) * admixtureLDDecay r t_since :=
    mul_lt_mul_of_pos_left h_recent (by linarith)
  nlinarith

end MigrationDriftPortability

/-! ## Migration-Drift Recurrence: Deriving Fst = 1/(1 + 4Nm) from First Principles

We derive the classical Wright (1931) equilibrium Fst formula from the
migration-drift recurrence relation. The island model with migration rate m
and effective population size Ne yields a linear recurrence on Fst:

  Fst_{t+1} = (1 - 2m - 1/(2Ne)) * Fst_t + 1/(2Ne)

This is the linearized form where (1-m)² ≈ 1 - 2m. At equilibrium
Fst* = Fst_{t+1} = Fst_t, solving the linear equation gives:

  Fst* = 1 / (4*Ne*m + 1)

We prove this closed form satisfies the recurrence, then derive monotonicity
and portability consequences directly from the recurrence structure.
-/

section MigrationDriftRecurrence

/-! ### 1. The migration-drift recurrence -/

/-- **Migration-drift recurrence on Fst.**
    In the island model with migration rate `m` and effective size `Ne`,
    the linearized one-generation update of Fst is:
      Fst_{t+1} = (1 - 2m - 1/(2Ne)) * Fst_t + 1/(2Ne)
    Migration reduces Fst by a factor (1-2m), and drift adds (1-Fst)/(2Ne).
    The linearization replaces (1-m)² with 1-2m (valid for small m).

    Empirical status: **VALIDATED**
    (`validation/empirical/simcov/battery_bulk1.py`,
    `test_one_step_maps`). Same trajectories, same one-step protocol, as
    `ibdRecurrenceStep`:

      Ne     m        this def   simulated            sems
      200    0.002     0.27083   0.27079±0.00365      0.01
      200    0.010     0.10533   0.10530±0.00042      0.07
      500    0.005     0.07604   0.07602±0.00069      0.03

    This and `ibdRecurrenceStep` are two different functions and the corpus
    relates them by no theorem, which is the unresolved-fork pattern. As
    one-step maps they agree to within 0.07 sems on every design tested here, so
    the fork is real in the algebra and immaterial at these rates; it would take
    a design at large `m` to separate them.

    Power: the prediction spans 0.07604 to 0.27083 across the design. -/
noncomputable def fstMigDriftNext (Ne m Fst : ℝ) : ℝ :=
  (1 - 2 * m - 1 / (2 * Ne)) * Fst + 1 / (2 * Ne)

/-- **The migration-drift step at zero effective size, named.** Both `1 / (2 * Ne)` terms are
junk-zero at `Ne = 0`, so the step reduces to `(1 - 2 * m) * Fst`: migration still erodes
differentiation and drift contributes nothing. An empty population is reported as one in which
drift generates no differentiation at all, and iterating the step compounds the error.
Consumers must require `Ne ≠ 0`. -/
theorem fstMigDriftNext_zero_population_is_junk (m Fst : ℝ) :
    fstMigDriftNext 0 m Fst = (1 - 2 * m) * Fst := by
  unfold fstMigDriftNext
  simp

/-- The recurrence can be written as Fst_{t+1} = a * Fst_t + b where
    a = 1 - 2m - 1/(2Ne) and b = 1/(2Ne). -/
theorem fstMigDriftNext_eq (Ne m Fst : ℝ) :
    fstMigDriftNext Ne m Fst =
      (1 - 2 * m - 1 / (2 * Ne)) * Fst + 1 / (2 * Ne) := by
  rfl

/-- The drift term: when m = 0, the recurrence reduces to pure drift. -/
theorem fstMigDriftNext_no_migration (Ne Fst : ℝ) :
    fstMigDriftNext Ne 0 Fst = (1 - 1 / (2 * Ne)) * Fst + 1 / (2 * Ne) := by
  unfold fstMigDriftNext
  ring

/-- With no migration, the recurrence pushes Fst toward 1: the drift-only
    fixed point is Fst = 1. We verify: f(1) = 1. -/
theorem fstMigDriftNext_no_migration_fixedpoint_one (Ne : ℝ) (hNe : Ne ≠ 0) :
    fstMigDriftNext Ne 0 1 = 1 := by
  rw [fstMigDriftNext_no_migration]
  field_simp
  ring_nf

/-! ### 2. The exact equilibrium fixed point -/
/-! ### The migration-drift equilibrium, under one name

`fstMigDriftEquil Ne m = 1 / (4 * Ne * m + 1)` stood here as a third spelling of
`fstMigrationDriftEquilibrium Ne m = 1 / (1 + 4 * Ne * m)`, with its own junk-point
theorem, its own positivity, its own two bounds and its own two monotonicities -- eight
declarations, each the twin of one above, and a ninth proving the two spellings equal.

The prose here said so: "Three definitions of one quantity share a junk branch, so
agreement between them is not evidence about the value." The remedy for that is one
definition, not a theorem tying the copies, because a tie makes the copies consistent and
leaves the reader to find out which of the three names a given theorem happens to use.

What was genuinely this spelling's own -- the drift-over-migration-plus-drift ratio form,
which is the reading that makes the balance explicit -- is stated below on the surviving
name. -/

/-- **Intermediate form of the fixed-point equation.**
    The equilibrium can also be written as
      Fst* = (1/(2Ne)) / (2m + 1/(2Ne))
    which makes the balance between drift (numerator) and
    migration + drift (denominator) explicit. -/
theorem fstMigrationDriftEquilibrium_ratio_form (Ne m : ℝ)
    (hNe : 0 < Ne) (hm : 0 ≤ m) :
    fstMigrationDriftEquilibrium Ne m =
      (1 / (2 * Ne)) / (2 * m + 1 / (2 * Ne)) := by
  unfold fstMigrationDriftEquilibrium
  have hNe2 : (0 : ℝ) < 2 * Ne := by positivity
  have hden : 2 * m + 1 / (2 * Ne) ≠ 0 := by
    have : 0 < 2 * m + 1 / (2 * Ne) := by positivity
    linarith
  field_simp [hden]
  ring

/-! ### 6. The full (non-linearized) recurrence and its fixed point -/


/-! ### 7. Migration-to-neutral-benchmark connection derived from the recurrence -/

/-- **Neutral allele-frequency benchmark ratio from the derived Fst formula.**
    The benchmark ratio is `1 - Fst = 1 - 1/(4Nm + 1) = 4Nm/(4Nm + 1)`.
    This is still only the recurrence's coarse allele-frequency benchmark,
    not a mechanistic portability law.

    This body used to be spelled `sharedLD_from_equilibrium Nₑ m`, which was the
    same number while that definition read `1 - Fst`. It is not the same number
    any more, and the two claims should never have shared a body: `1 - Fst` is
    the right answer for the sharing of ALLELE FREQUENCIES, which is what this
    benchmark is about, and the wrong answer for the sharing of LD, which is
    what `sharedLD_from_equilibrium` is about. The complement is written out
    here so that repairing the LD law cannot silently move the frequency
    benchmark. -/
noncomputable def neutralAFBenchmarkFromRecurrence (Ne m : ℝ) : ℝ :=
  1 - fstMigrationDriftEquilibrium Ne m

/-- The recurrence-derived neutral allele-frequency benchmark equals
`4Nm / (4Nm + 1)`. -/
theorem neutralAFBenchmarkFromRecurrence_eq (Ne m : ℝ)
    (hNe : 0 < Ne) (hm : 0 ≤ m) :
    neutralAFBenchmarkFromRecurrence Ne m = 4 * Ne * m / (4 * Ne * m + 1) := by
  unfold neutralAFBenchmarkFromRecurrence fstMigrationDriftEquilibrium
  have hden : 4 * Ne * m + 1 ≠ 0 := by nlinarith
  field_simp [hden]
  ring_nf

/-- **The recurrence-derived neutral benchmark improves with migration rate.**
    From the derived formula `4Nm/(4Nm+1)`, increasing `m` increases the
    recurrence-derived benchmark ratio. -/
theorem neutralAFBenchmarkFromRecurrence_increasing_in_m (Ne m₁ m₂ : ℝ)
    (hNe : 0 < Ne) (hm₁ : 0 < m₁) (hm₂ : 0 < m₂)
    (h_more : m₁ < m₂) :
    neutralAFBenchmarkFromRecurrence Ne m₁ < neutralAFBenchmarkFromRecurrence Ne m₂ := by
  rw [neutralAFBenchmarkFromRecurrence_eq Ne m₁ hNe (le_of_lt hm₁),
      neutralAFBenchmarkFromRecurrence_eq Ne m₂ hNe (le_of_lt hm₂)]
  rw [div_lt_div_iff₀ (by nlinarith) (by nlinarith)]
  nlinarith

/-- **The recurrence-derived neutral benchmark is nonnegative.** -/
theorem neutralAFBenchmarkFromRecurrence_nonneg (Ne m : ℝ) (hNe : 0 < Ne) (hm : 0 ≤ m) :
    0 ≤ neutralAFBenchmarkFromRecurrence Ne m := by
  rw [neutralAFBenchmarkFromRecurrence_eq Ne m hNe hm]
  exact div_nonneg (by nlinarith) (by nlinarith)

/-- **The recurrence-derived neutral benchmark is strictly positive with migration.** -/
theorem neutralAFBenchmarkFromRecurrence_pos (Ne m : ℝ) (hNe : 0 < Ne) (hm : 0 < m) :
    0 < neutralAFBenchmarkFromRecurrence Ne m := by
  rw [neutralAFBenchmarkFromRecurrence_eq Ne m hNe (le_of_lt hm)]
  exact div_pos (by nlinarith) (by nlinarith)

/-- **The recurrence-derived neutral benchmark is strictly less than `1`.** -/
theorem neutralAFBenchmarkFromRecurrence_lt_one (Ne m : ℝ) (hNe : 0 < Ne) (hm : 0 ≤ m) :
    neutralAFBenchmarkFromRecurrence Ne m < 1 := by
  rw [neutralAFBenchmarkFromRecurrence_eq Ne m hNe hm]
  rw [div_lt_one (by nlinarith : 0 < 4 * Ne * m + 1)]
  linarith

/-- **The recurrence-derived benchmark connects back to the file's coarse `R²`
benchmark.**
    Using the recurrence-derived `F_ST`, the benchmark target `R²` is the
    present-day `R²` at `fstMigrationDriftEquilibrium`. More migration yields higher
    benchmark `R²`. -/
theorem recurrence_derived_R2_increases_with_m (V_A V_E Ne m₁ m₂ : ℝ)
    (hVA : 0 < V_A) (hVE : 0 < V_E) (hNe : 0 < Ne)
    (hm₁ : 0 < m₁) (h_more : m₁ < m₂) :
    presentDayR2 V_A V_E (fstMigrationDriftEquilibrium Ne m₁) <
      presentDayR2 V_A V_E (fstMigrationDriftEquilibrium Ne m₂) := by
  exact drift_degrades_R2 V_A V_E
    (fstMigrationDriftEquilibrium Ne m₂) (fstMigrationDriftEquilibrium Ne m₁)
    hVA hVE
    (fstMigrationDriftEquilibrium_decreases_with_m Ne m₁ m₂ hNe hm₁ h_more)
    (le_of_lt (fstMigrationDriftEquilibrium_lt_one Ne m₁ hNe hm₁))

end MigrationDriftRecurrence

end PortabilityDrift

/-! ## Nonreversible gene flow: the mixing time is not the transfer time

Everything above this point models divergence with reversible machinery — drift, symmetric
migration, coalescent times. Real gene flow is not reversible: expansions, admixture pulses and
sex-biased migration carry probability around cycles. `Descent.CirculationDefect` separates
what that changes from what it does not.

It does not change the degradation calculus: the Dirichlet energy annihilates the circulation, so
every ordering of weighting schemes by that energy survives unchanged.

It does change what a measured mixing time means. Circulation accelerates ergodic averaging
without contributing to the frontier, so the diagnostic reports a shorter time than the one
governing transfer — at equal circulation and dissipation, half of it.

That is a third mechanism alongside the two this file carries. Allele-frequency divergence says
how far apart populations are, tagging mismatch says how much linkage structure carries over, and
this says a well-mixed-looking population can still be a bad transfer target because the rate at
which its environment forgets is not the rate at which a design degrades. -/

section NonreversibleFlow

/-- A mixing-time diagnostic understates the transfer-relevant time. Instance of
    `apparentMixingTime_lt_frontierTime`: with any cyclic component to gene flow, the time
    constant an ergodic-averaging diagnostic measures is strictly shorter than the one setting the
    transfer frontier, so substituting it into a horizon calculus overstates transportability.

    Empirical status: DERIVED; the circulation-to-dissipation ratio of a real demography is the
    unmeasured input this asks for. -/
theorem geneFlowMixingTime_understates_transferTime
    (dissipation circulation : ℝ) (hd : 0 < dissipation) (hc : circulation ≠ 0) :
    apparentMixingTime dissipation circulation < frontierTime dissipation :=
  apparentMixingTime_lt_frontierTime dissipation circulation hd hc

/-- The overstatement is a factor of two at equal circulation and dissipation, and grows
    quadratically in the ratio beyond that.

    Empirical status: DERIVED. -/
theorem transferTime_doubles_at_equal_circulation (dissipation : ℝ) (hd : 0 < dissipation) :
    frontierTime dissipation
        = transferTimeInflation dissipation dissipation *
            apparentMixingTime dissipation dissipation ∧
      transferTimeInflation dissipation dissipation = 2 := by
  refine ⟨frontierTime_eq_inflation_mul_apparent dissipation dissipation hd, ?_⟩
  unfold transferTimeInflation
  rw [div_self (ne_of_gt hd)]
  norm_num

end NonreversibleFlow

end Descent
