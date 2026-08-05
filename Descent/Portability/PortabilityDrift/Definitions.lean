/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Program.Conclusions
import Descent.PopGen.DGP
import Descent.Spectral.CirculationDefect
import Descent.Core.Fst
import Descent.Core.Parameters
import Descent.Core.Moments

namespace Descent.Portability

open MeasureTheory

open PopGen.TransportedMetrics (r2FromSignalVariance r2FromSignalVariance_eq_rsquared
  equalVarianceGaussianAUCFromSignalVariance
  equalVarianceGaussianAUCFromSignalVariance_eq_formula_of_ne_noise)

/-!
# `PortabilityDrift.Definitions`

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


/-! `r2FromSignalVariance` and the Gaussian-AUC declarations live in
`Descent.TransportedMetrics` (DGP.lean). `Descent.PopGen.DGP` is imported, so
the module is available, but the namespace was never opened here and this file
refers to five of its declarations WITHOUT qualification. Lean does not report
that as a missing constant: it auto-binds the bare name as an implicit
variable, which is why the failure surfaced as three unrelated-looking symptoms
-- "unknown identifier", "function expected at", and the discriminating
"LOCAL VARIABLE `r2FromSignalVariance` has no definition". A definition that
had failed to build would say something else, and `Descent.PopGen.DGP` itself
builds clean.

These five names are opened rather than qualified at ~40 call sites: the
mechanical repoint is the larger and riskier diff, and an explicit import list
cannot collide, since this file defines none of these names and the only
`Profile` and `calibratedBrier` in the corpus are the ones inside this same
namespace. The remaining `TransportedMetrics.` prefixes in this file are left
alone; both spellings resolve to the same constant. -/

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

/-! **`fstFromTau` is deleted here.**  It was
`Descent.Core.fstFromTau` under a second name, and every reference now
calls the kernel.  `Core.fstFromTau` is the split law `tau/(1+tau)`; the wrapper added a second
place for the convention to be got wrong. -/


/-- **fstFromTau at `tau = -1`, named.** A coalescent time of minus one is outside the admissible
range, which is exactly why it must be excluded by hypothesis rather than left to the totality
convention: the saturation curve's divisor vanishes there and Lean returns `0`, an ordinary `Fst`
value that no downstream range check will reject. Consumers must exclude it by hypothesis. -/
theorem fstFromTau_negative_unit_tau_is_junk :
    Descent.Core.fstFromTau (-1) = 0 := by
  unfold Descent.Core.fstFromTau Descent.Core.saturation
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
  Descent.Core.fstFromTau (coalescentTau t Ne)

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
    1 / Spectral.transferTimeInflation s a = 1 - Descent.Core.fstFromTau ((a / s) ^ 2) := by
  have hpos : (0 : ℝ) < 1 + (a / s) ^ 2 := by positivity
  have hne : (1 : ℝ) + (a / s) ^ 2 ≠ 0 := ne_of_gt hpos
  unfold Spectral.transferTimeInflation Descent.Core.fstFromTau Descent.Core.saturation
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
  Descent.Core.complementaryComposition fstS fstT

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
  Descent.Core.fstFromTau ((tauS + tauT) / 2)

@[simp] theorem pairwise_fst_decomposition (fstS fstT : ℝ) :
    pairwiseFstFromBranches fstS fstT = fstS + fstT - fstS * fstT := by
  unfold pairwiseFstFromBranches Descent.Core.complementaryComposition
  ring_nf

/-- **What the multiplicative composition actually computes.**

Feeding it two branch `F_ST` values that came from coalescent times `a` and `b`
returns the `F_ST` of a single branch of length `a + b + a * b`. The `a * b` is
the whole defect: it is divergence time that no branch spent. This identity is
the derivation behind the regime note on `pairwiseFstFromBranches`, and it needs
no simulation to state. -/
theorem pairwiseFstFromBranches_eq_fstFromTau_add_mul (a b : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) :
    pairwiseFstFromBranches (Descent.Core.fstFromTau a) (Descent.Core.fstFromTau b) =
      Descent.Core.fstFromTau (a + b + a * b) := by
  have ha1 : (0 : ℝ) < 1 + a := by linarith
  have hb1 : (0 : ℝ) < 1 + b := by linarith
  have ha1' : (1 : ℝ) + a ≠ 0 := ne_of_gt ha1
  have hb1' : (1 : ℝ) + b ≠ 0 := ne_of_gt hb1
  have hab : (0 : ℝ) < 1 + (a + b + a * b) := by nlinarith
  have hab' : (1 : ℝ) + (a + b + a * b) ≠ 0 := ne_of_gt hab
  unfold pairwiseFstFromBranches Descent.Core.fstFromTau Descent.Core.saturation Descent.Core.complementaryComposition
  field_simp
  ring

/-- **The multiplicative map is strictly the larger of the two compositions**,
for every pair of positive branch lengths. The bias has a sign, and it is the
sign the simulation reports. -/
theorem pairwiseFstFromBranchTaus_lt_pairwiseFstFromBranches (a b : ℝ)
    (ha : 0 < a) (hb : 0 < b) :
    pairwiseFstFromBranchTaus a b <
      pairwiseFstFromBranches (Descent.Core.fstFromTau a) (Descent.Core.fstFromTau b) := by
  rw [pairwiseFstFromBranches_eq_fstFromTau_add_mul a b ha.le hb.le]
  unfold pairwiseFstFromBranchTaus Descent.Core.fstFromTau Descent.Core.saturation
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
    pairwiseFstFromBranches (Descent.Core.fstFromTau a) (Descent.Core.fstFromTau a) -
        pairwiseFstFromBranchTaus a a = a / (1 + a) ^ 2 := by
  have h1 : (1 : ℝ) + a ≠ 0 := by positivity
  rw [pairwiseFstFromBranches_eq_fstFromTau_add_mul a a ha ha]
  unfold pairwiseFstFromBranchTaus Descent.Core.fstFromTau Descent.Core.saturation
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
    0 ≤ Descent.Core.fstFromTau tau :=
  div_nonneg htau (by linarith)

theorem fst_from_tau_lt_one (tau : ℝ) (htau : 0 ≤ tau) : Descent.Core.fstFromTau tau < 1 := by
  unfold Descent.Core.fstFromTau Descent.Core.saturation
  rw [div_lt_one (by linarith)]
  linarith

/-- **The coalescence CDF is not `F_ST`.**  `1 - exp (-tau)` is the probability
that a lineage pair has coalesced by `tau`; `F_ST` is the between-population
share of variance.  Conflating them overstates divergence at every positive
separation, which is the direction and the shape of the bias measured against
simulation (+5% at `tau = 0.1`, rising to +32% at `tau = 1`).  Stating the
inequality keeps the two from being interchanged again silently. -/
theorem fstFromTau_lt_coalescenceCdf (tau : ℝ) (htau : 0 < tau) :
    Descent.Core.fstFromTau tau < 1 - Real.exp (-tau) := by
  have hE : (0 : ℝ) < Real.exp tau := Real.exp_pos tau
  have hexp : tau + 1 < Real.exp tau := Real.add_one_lt_exp (by linarith)
  have h1t : (0 : ℝ) < 1 + tau := by linarith
  rw [← sub_pos]
  unfold Descent.Core.fstFromTau Descent.Core.saturation
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
    Descent.Core.fstFromTau 1 = 1 / 2 := by
  unfold Descent.Core.fstFromTau Descent.Core.saturation
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
  1 / (1 + Descent.Core.scaledMigrationRate m.Ne m.mig)

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

structure DemographicCoalescenceScalars where
  ETss : ℝ
  ETst : ℝ

/-- **Hudson's estimator, pinned.** This definition carries no theorem of its own. When a pair
drawn between populations takes twice as long to coalesce as a pair drawn within one, half the
coalescent history is population-specific and `Fst` is one half. -/
theorem hudsonFstFromCoalescenceTimes_double_between :
    hudsonFstFromCoalescenceTimes 1 2 = 1 / 2 := by
  unfold hudsonFstFromCoalescenceTimes Descent.Core.proportionalReduction
  norm_num

/-- **Hudson's estimator at zero between-population coalescence time, named.** If a pair drawn
between populations coalesces instantly there is no differentiation at all, so `Fst` should be
zero or undefined. The divisor is zero, the ratio is junk-zero, and the estimator returns `1` --
COMPLETE differentiation, the opposite end of the scale. Of the junk branches in this chart this
is the one that inverts rather than flattens, so it cannot be spotted as an implausible extreme.
Consumers must require `ETst ≠ 0`. -/
theorem hudsonFstFromCoalescenceTimes_instant_between_is_junk (ETss : ℝ) :
    hudsonFstFromCoalescenceTimes ETss 0 = 1 := by
  unfold hudsonFstFromCoalescenceTimes Descent.Core.proportionalReduction
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

/-- Reference evaluation; see `Descent.Core.Ratios` for what these pin and why. -/
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
analysis.**  Solving `ETss = 1/(1+M) + (M/(1+M)) ETst` jointly with `ETst = 1/M + ETss` forces `ETss
= 2` for every `M > 0`. -/
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
  unfold hudsonFstFromCoalescenceTimes twoDemeIMEquilibriumETss twoDemeIMEquilibriumETst Descent.Core.proportionalReduction
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
    twoDemeIMEquilibriumETst, twoDemeIMEquilibriumDelta, Descent.Core.proportionalReduction]
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

`Descent.PopGen.DriftRegime` states the epistemic half of the same incident: why
every cross-check inside the cluster passed.
-/

end PortabilityDrift

/-- **Cross-check: the within-deme coalescence time carries the same two.**
`PortabilityDrift.twoDemeIMEquilibriumETss` is `2` in units of `Nₑ`
generations, and that two is the ploidy: `E[T_within] = ploidy · Nₑ`
generations is `Descent.Core.coalescentTimeScale`, which is `2 Nₑ`. Writing the constant
without saying so left a bare numeral in an equilibrium; this theorem says
which two it is. -/
theorem twoDemeIMEquilibriumETss_eq_ploidy (M : ℝ) :
    Portability.twoDemeIMEquilibriumETss M = Descent.Core.ploidy := by
  unfold Portability.twoDemeIMEquilibriumETss Descent.Core.ploidy; ring

theorem coalescentTau_uses_timeScale (t Ne : ℝ) :
    Portability.coalescentTau t Ne = t / Descent.Core.coalescentTimeScale Ne := by
  unfold Portability.coalescentTau; rw [Descent.Core.coalescentTimeScale_eq]

theorem SplitMigrationModel_scaledMigration_eq_ploidy_form
    (m : Portability.SplitMigrationModel) :
    Descent.Core.scaledMigrationRate m.Ne m.mig = 2 * Descent.Core.ploidy * m.Ne * m.mig := by
  unfold Descent.Core.scaledMigrationRate Descent.Core.ploidy Descent.Core.scaledMigrationRate Descent.Core.ploidy; ring

end Descent.Portability
