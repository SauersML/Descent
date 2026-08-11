/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.PortabilityDrift.ClosedPopulationRegime
import Descent.PopGen.AssortativeMatingPGS
import Descent.PopGen.LDDecayTheory
import Descent.PopGen.PolygenicAdaptation
import Descent.Core.Moments

assert_below Descent.Decision Descent.Program

namespace Descent.Portability

open MeasureTheory

open PopGen.TransportedMetrics (r2FromSignalVariance r2FromSignalVariance_eq_rsquared
  equalVarianceGaussianAUCFromSignalVariance
  equalVarianceGaussianAUCFromSignalVariance_eq_formula_of_ne_noise)

/-!
# `PortabilityDrift.PresentDayMetrics`

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
  Descent.Core.product β_sq_sum het

/-- Reference evaluation; see `Descent.Core.Ratios` for what these pin and why. -/
theorem pgsVarianceFromHet_at_reference_point :
    pgsVarianceFromHet 1 1 = 1 := by
  norm_num [pgsVarianceFromHet, Descent.Core.product]


/-- **Score variance is bilinear in effect scale and heterozygosity.** Rescaling every effect by
`c` scales the summed squares by `c` as given, and the variance follows; the same holds in the
heterozygosity argument. Separating the two orders is what a mutant collapsing them would lose. -/
theorem pgsVarianceFromHet_bilinear (β_sq_sum het c : ℝ) :
    pgsVarianceFromHet (c * β_sq_sum) het = c * pgsVarianceFromHet β_sq_sum het ∧
      pgsVarianceFromHet β_sq_sum (c * het) = c * pgsVarianceFromHet β_sq_sum het := by
  constructor <;> unfold pgsVarianceFromHet Descent.Core.product <;> ring

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

    Empirical status: **MIXED** -- VACUOUS with a sample-estimated `fst`, and VALIDATED with
    the model's (`simcov/battery_drift05.py`). Both halves are true and the difference is where
    `fst` came from, which is the distinction `simcov/verdict.py` now makes by declaration.
    The head is `MIXED` because that is the closed-vocabulary term for a definition whose parts
    carry different verdicts; it read `VACUOUS ...` before, and a scanner takes the first word
    of a status line as the verdict, so the half of this definition that IS measured -- the
    table below, with a competitor refuted at 349 sems and a control that passes -- was being
    counted as unmeasured.

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
  Descent.Core.retainedFraction fst het_source

/-- Reference evaluation; see `Descent.Core.Ratios` for what these pin and why. -/
theorem targetHetFromFst_at_reference_point :
    targetHetFromFst (1 / 2) (1 / 2) = 1 / 4 := by
  unfold targetHetFromFst Descent.Core.retainedFraction
  norm_num

/-- **Endpoints of the drift-retention map.** No divergence retains all heterozygosity; complete
divergence retains none. Two anchors rather than one, because a single one is met by many wrong
bodies. -/
theorem targetHetFromFst_endpoints (het_source : ℝ) :
    targetHetFromFst het_source 0 = het_source ∧ targetHetFromFst het_source 1 = 0 := by
  constructor <;> unfold targetHetFromFst Descent.Core.retainedFraction <;> ring

/-- The map is linear in the source heterozygosity: it is a retained FRACTION, so doubling the
source doubles the target at fixed divergence. -/
theorem targetHetFromFst_linear (het_source fst c : ℝ) :
    targetHetFromFst (c * het_source) fst = c * targetHetFromFst het_source fst := by
  unfold targetHetFromFst Descent.Core.retainedFraction; ring

/-- **The bridge named in the paragraph above**, which until now was named and not stated.

In the closed-population regime the proportional heterozygosity loss over the horizon is
`1 - retention`, and feeding *that* value to `targetHetFromFst` returns the regime's own
target heterozygosity. Which value goes in is the entire content: the rearrangement holds
for every second argument, so it cannot detect a wrong one, and this says which one the
regime supplies. It is a within-population loss, not a between-population `F_ST`. -/
theorem ClosedPopulationNoMutation.targetHet_eq_targetHetFromFst
    (r : ClosedPopulationNoMutation) :
    r.targetHet = targetHetFromFst r.H₀ (1 - r.retention) := by
  unfold ClosedPopulationNoMutation.targetHet targetHetFromFst Descent.Core.retainedFraction
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
  unfold presentDayPGSVariance pgsVarianceFromHet Descent.Core.product
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

    **A third design makes the same convention error measurable rather than
    argued** (`validation/empirical/simcov/battery_pgsdrift01.py`). That run
    reports BOTH `F_ST` conventions in every cell, so the gap between them is a
    number and not a warning: per-branch 0.1829 against pairwise 0.1007, and
    0.1407 against 0.0757 -- the pairwise value is `(F_b/2)/(1 - F_b/2)`, about
    half. Fed the per-branch index against one population's score variance this
    body matches at worst 1.92 sems, with `fst · V_A` rejected at 23 sems and
    `4 · fst · V_A` at 47 on the same cells. Fed a pairwise `F_ST` against the
    variance of the DIFFERENCE -- the pairing `battery_pgs` used, and the one
    this declaration's NAME invites -- it is FALSIFIED at 22.08 sems and 73%.

    That falsification is the one standing in the ledger against this
    declaration, and `adjudications.json` now records it as a true result about
    a pairing the corpus does not use rather than as a verdict on the body. The
    name is left alone: it is load-bearing at every call site, and a rename is
    not a measurement.
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
    Descent.Core.product
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
  PopGen.TransportedMetrics.r2FromSignalVariance (presentDayPGSVariance V_A fst) V_E

/-- **The free `F_ST` here has a derivation, and this is it.**

`presentDayR2` takes `fst` as a parameter, which is right: the metric is a function of
differentiation however that differentiation arose. But the corpus also DERIVES an `F_ST`
from raw demography, and nothing in this module said the two compose. Supplying the island
equilibrium of a parameter record for the parameter gives exactly
`Core.ScoreMoments.deployedR2`, the composition that runs `(Nₑ, m, μ, d)` to a deployed
metric.

It used to give `Core.ScoreMoments.deployedR2FromIsland`, a SECOND composition taking six
raw reals, which existed only because the parameter record carried no deme count and so
`deployedR2` could express the two-deme case alone. `nDemes` is a field of that record
now, the raw-real composition is deleted, and this edge lands on the one route.

The `fst` parameter is deliberately not replaced. A metric that only accepted a derived
`F_ST` would be unable to state what happens at a MEASURED one, which is most of what this
module is for. What was missing was the edge, not the generality: with it, a reader can
see which `F_ST`s in this file have a demographic origin and follow it, and the ones that
do not are the ones with no such theorem. -/
theorem presentDayR2_at_island_eq_deployedR2
    (p : Descent.Core.PopGenParameters) (V_E : ℝ) :
    presentDayR2 p.V_A V_E
        (Descent.Core.fstIslandEquilibrium p.bigM p.theta p.nDemes)
      = Descent.Core.ScoreMoments.deployedR2 p V_E := by
  unfold presentDayR2 Descent.Core.ScoreMoments.deployedR2 presentDayPGSVariance
    pgsVarianceFromHet Descent.Core.product
    PopGen.TransportedMetrics.r2FromSignalVariance
    Descent.Core.ScoreMoments.r2 Descent.Core.ScoreMoments.momentsUnderDrift
    Descent.Core.share Descent.Core.retainedFraction
    Descent.Core.PopGenParameters.fstEquilibrium
  -- The two sides write the retained variance in opposite orders, `V_A * (1 - F)` against
  -- `(1 - F) * V_A`, so the zero case has to be rewritten on both.
  by_cases h :
      (1 - Descent.Core.fstIslandEquilibrium p.bigM p.theta p.nDemes) * p.V_A = 0
  · have h' :
        p.V_A * (1 - Descent.Core.fstIslandEquilibrium p.bigM p.theta p.nDemes) = 0 := by
      rw [mul_comm]; exact h
    rw [h, h']; simp
  · field_simp

/-! ### The drift model produces a moment tuple

`PortabilityMasterTheorem` declares that the interface between the population-genetic
layer and the deployed-metric layer is a moment tuple. This section is the PopGen side of
that interface: a drift model with additive variance `V_A`, environmental variance `V_E`
and differentiation `F_ST` produces a `Core.ScoreMoments`, and the metrics below are that
tuple read through the Core metric laws rather than through a second set of formulas.

Before this, `presentDayR2` and the master theorem's `r2` were two expressions with the
same shape in two modules with nothing relating them, and the layer contract was a
sentence in a docstring. -/

/-- **The drift model's moment tuple.** What this module hands the metric layer.

Empirical status: DERIVED, and the derivation is the three theorems immediately below.
`driftMoments_scoreVariance`, `driftMoments_predictiveCovariance` and
`driftMoments_outcomeVariance` each identify one field of the tuple with a quantity this
module already computes -- `presentDayPGSVariance`, and that quantity plus `V_E` -- so
the tuple is a repackaging and not a fourth model with its own content.  It carries no
measurement of its own for the same reason: what a simulation could reject is
`presentDayPGSVariance`, and `presentDayR2_eq_deployedR2` is the theorem that makes a
rejection there a rejection here. -/
noncomputable def driftMoments (V_A V_E fst : ℝ) : Descent.Core.ScoreMoments :=
  Descent.Core.ScoreMoments.momentsUnderDrift V_A V_E fst

/-- **The tuple's score variance IS `presentDayPGSVariance`.** The first of three
component identities; together they say the tuple is not a fourth model but a repackaging
of the three quantities this module already computes. -/
theorem driftMoments_scoreVariance (V_A V_E fst : ℝ) :
    (driftMoments V_A V_E fst).scoreVariance = presentDayPGSVariance V_A fst := by
  unfold driftMoments Descent.Core.ScoreMoments.momentsUnderDrift presentDayPGSVariance
    pgsVarianceFromHet Descent.Core.product Descent.Core.retainedFraction
  simp only [Descent.Core.product]
  ring

/-- **The predictive covariance is the same retained variance.** Under drift with no
effect turnover the score's covariance with the outcome equals its own variance -- which
is exactly why the calibration slope does not move, and why a deployment judged only by
calibration reports no problem. -/
theorem driftMoments_predictiveCovariance (V_A V_E fst : ℝ) :
    (driftMoments V_A V_E fst).predictiveCovariance = presentDayPGSVariance V_A fst :=
  driftMoments_scoreVariance V_A V_E fst

/-- **The outcome variance carries the SAME erosion.** The target's own additive variance
is eroded by drift too, so the denominator is `V_A(1-F) + V_E`, not `V_A + V_E`. Using the
ancestral additive variance here understates the deployed `R²`. -/
theorem driftMoments_outcomeVariance (V_A V_E fst : ℝ) :
    (driftMoments V_A V_E fst).outcomeVariance = presentDayPGSVariance V_A fst + V_E :=
  congrArg (· + V_E) (driftMoments_scoreVariance V_A V_E fst)

/-- **`presentDayR2` IS the Core metric law on this module's tuple.**

The composition the corpus's layer contract asserted and could not state. Both sides are
`V_A(1-F) / (V_A(1-F) + V_E)`; what the equality buys is the dependency, so a change to
either the drift model or the metric law reaches the other. -/
theorem presentDayR2_eq_core (V_A V_E fst : ℝ) :
    presentDayR2 V_A V_E fst = (driftMoments V_A V_E fst).r2 := by
  unfold presentDayR2 driftMoments Descent.Core.ScoreMoments.momentsUnderDrift
    Descent.Core.ScoreMoments.r2 PopGen.TransportedMetrics.r2FromSignalVariance
    presentDayPGSVariance pgsVarianceFromHet Descent.Core.product
    Descent.Core.share
    Descent.Core.retainedFraction
  have e1 : V_A * (1 - fst) = (1 - fst) * V_A := by ring
  rw [e1]
  rcases eq_or_ne ((1 - fst) * V_A) 0 with hz | hz
  · rw [hz]; simp
  · rw [pow_two, mul_div_mul_left _ _ hz]

/-- **The calibration slope of a drift-attenuated score is one at every `F_ST`.**

Read off the tuple rather than derived again: drift erodes the score variance and the
predictive covariance by the same factor. A polygenic score that has lost most of its
`R²` in a target population can be perfectly calibrated there, and a deployment audited
on calibration alone would find nothing. -/
theorem driftMoments_calibrationSlope (V_A V_E fst : ℝ) (hV : 0 < V_A) (hf : fst < 1) :
    (driftMoments V_A V_E fst).calibrationSlope = 1 :=
  Descent.Core.ScoreMoments.calibrationSlope_momentsUnderDrift V_A V_E fst hV hf

/-- **The deployed `R²` under drift lies in the unit interval**, inherited from the Core
bound rather than re-proved. -/
theorem presentDayR2_mem_unit (V_A V_E fst : ℝ) (hV : 0 < V_A) (hE : 0 ≤ V_E)
    (hf : fst < 1) :
    0 ≤ presentDayR2 V_A V_E fst ∧ presentDayR2 V_A V_E fst ≤ 1 := by
  have hr : 0 < (1 - fst) * V_A := by nlinarith
  rw [presentDayR2_eq_core]
  refine (driftMoments V_A V_E fst).r2_mem_unit ?_
  refine { scoreVariance_pos := ?_, outcomeVariance_pos := ?_, cauchy_schwarz := ?_ } <;>
    unfold driftMoments Descent.Core.ScoreMoments.momentsUnderDrift
      Descent.Core.retainedFraction <;> simp
  · linarith
  · linarith
  · nlinarith [sq_nonneg ((1 - fst) * V_A), mul_nonneg (le_of_lt hV) hE]

/-- **More differentiation, less deployed `R²`** -- this module's own statement of the
law, now a consequence of the Core one rather than a parallel derivation. -/
theorem presentDayR2_anti (V_A V_E f₁ f₂ : ℝ) (hV : 0 < V_A) (hE : 0 < V_E)
    (h1 : f₁ < f₂) (h2 : f₂ < 1) :
    presentDayR2 V_A V_E f₂ < presentDayR2 V_A V_E f₁ := by
  rw [presentDayR2_eq_core, presentDayR2_eq_core]
  exact Descent.Core.ScoreMoments.r2_momentsUnderDrift_anti V_A V_E f₁ f₂ hV hE h1 h2

/-- **`fst` is a free real here, and this is what pins it.**

Every metric in this section takes `fst` as an argument, which severs it from the
population genetics meant to produce it. `Core.PopGenParameters.fstEquilibrium` is that
production, and this theorem is the join: the deployed metric of a demographic history is
this module's metric at the equilibrium that history reaches.

Where `fst` remains free below, it is because the module means an ARBITRARY
differentiation -- a measured `F_ST` from data, a differentiation produced by selection
rather than drift, or a sensitivity sweep -- and not because a derivation was unavailable. -/
theorem presentDayR2_at_equilibrium (p : Descent.Core.PopGenParameters) (V_E : ℝ) :
    presentDayR2 p.V_A V_E p.fstEquilibrium
      = Descent.Core.ScoreMoments.deployedR2 p V_E := by
  rw [presentDayR2_eq_core]
  rfl

/-- **And the end-to-end law, in this module's vocabulary**: raise the migration rate in
the demographic parameters and `presentDayR2` rises. Every step -- equilibrium, moment
tuple, metric -- is a named map. -/
theorem presentDayR2_mono_in_migration (p q : Descent.Core.PopGenParameters) (V_E : ℝ)
    (hE : 0 < V_E) (hNe : p.Ne = q.Ne) (hmu : p.mu = q.mu) (hd : p.nDemes = q.nDemes)
    (hV : p.V_A = q.V_A) (hlt : p.mig < q.mig) (hflow : 0 < p.mu + p.mig) :
    presentDayR2 p.V_A V_E p.fstEquilibrium < presentDayR2 q.V_A V_E q.fstEquilibrium := by
  rw [presentDayR2_at_equilibrium, presentDayR2_at_equilibrium]
  exact Descent.Core.ScoreMoments.deployedR2_mono_in_migration p q V_E hE hNe hmu hd hV
    hlt hflow

/-! ### The rest of the deployment report, at an equilibrium

`presentDayR2` is one number a deployment reports. These carry the same demographic
history into the others, so a report cannot quietly use a different `F_ST` for its
calibration slope than for its `R²`. -/

/-- **The deployed calibration slope at an equilibrium is one.** Stated in this module
because this is where a deployment report is assembled, and the warning belongs next to
the metrics it is about: no demographic history under pure drift produces a miscalibrated
score, so a deployment audited on calibration finds nothing while `R²` falls. -/
theorem deployedSlope_at_equilibrium_eq_one (p : Descent.Core.PopGenParameters) (V_E : ℝ)
    (hflow : 0 < p.mu + p.mig) :
    (driftMoments p.V_A V_E p.fstEquilibrium).calibrationSlope = 1 :=
  Descent.Core.ScoreMoments.calibrationSlope_momentsUnderDrift p.V_A V_E _ p.V_A_pos
    (p.fstEquilibrium_lt_one hflow)

/-- **The deployed mean squared error at an equilibrium is the environmental variance**,
whatever the history. The second flat metric. -/
theorem deployedMse_at_equilibrium (p : Descent.Core.PopGenParameters) (V_E : ℝ) :
    (driftMoments p.V_A V_E p.fstEquilibrium).mse = V_E :=
  Descent.Core.ScoreMoments.mse_momentsUnderDrift p.V_A V_E _

/-- **The deployed Brier score at an equilibrium**, as this module's report would carry
it. -/
noncomputable def deployedBrierAtEquilibrium (π : ℝ)
    (p : Descent.Core.PopGenParameters) (V_E : ℝ) : ℝ :=
  Descent.Core.ScoreMoments.brier π (driftMoments p.V_A V_E p.fstEquilibrium)

/-- **More migration, better deployed Brier score.** -/
theorem deployedBrierAtEquilibrium_mono_in_migration (π : ℝ)
    (p q : Descent.Core.PopGenParameters) (V_E : ℝ) (hπ : 0 < π) (hπ1 : π < 1)
    (hE : 0 < V_E) (hNe : p.Ne = q.Ne) (hmu : p.mu = q.mu) (hd : p.nDemes = q.nDemes)
    (hV : p.V_A = q.V_A) (hlt : p.mig < q.mig) (hflow : 0 < p.mu + p.mig) :
    deployedBrierAtEquilibrium π q V_E < deployedBrierAtEquilibrium π p V_E := by
  unfold deployedBrierAtEquilibrium driftMoments
  rw [hV]
  exact Descent.Core.ScoreMoments.brier_anti_in_r2 π _ _ hπ hπ1
    (Descent.Core.ScoreMoments.r2_momentsUnderDrift_anti q.V_A V_E q.fstEquilibrium
      p.fstEquilibrium q.V_A_pos hE
      (Descent.Core.PopGenParameters.fstEquilibrium_lt_of_mig_lt p q hNe hmu hd hlt)
      (p.fstEquilibrium_lt_one hflow))

/-- **The deployed AUC argument at an equilibrium falls with differentiation.** Carried by
the argument rather than a closed form for `Φ`, which this corpus has no Mathlib form
for -- the same discipline `calibratedBrierFromVariances` records for the liability
scale. -/
theorem deployedAucArgument_mono_in_migration (p q : Descent.Core.PopGenParameters)
    (V_E : ℝ) (hE : 0 < V_E) (hNe : p.Ne = q.Ne) (hmu : p.mu = q.mu)
    (hd : p.nDemes = q.nDemes) (hV : p.V_A = q.V_A)
    (hlt : p.mig < q.mig) (hflow : 0 < p.mu + p.mig) (hflowq : 0 < q.mu + q.mig) :
    Descent.Core.ScoreMoments.aucArgument (driftMoments p.V_A V_E p.fstEquilibrium)
      < Descent.Core.ScoreMoments.aucArgument (driftMoments q.V_A V_E q.fstEquilibrium) := by
  unfold driftMoments
  rw [hV]
  exact Descent.Core.ScoreMoments.aucArgument_momentsUnderDrift_anti q.V_A V_E
    q.fstEquilibrium p.fstEquilibrium q.V_A_pos hE
    (Descent.Core.PopGenParameters.fstEquilibrium_lt_of_mig_lt p q hNe hmu hd hlt)
    (p.fstEquilibrium_lt_one hflow) q.fstEquilibrium_mem_unit.1

/-- **The deployed report is bounded by the heritability at every history.** The ceiling
in this module's vocabulary: no demography makes a score explain more of the target's
variance than the trait's heritability. -/
theorem presentDayR2_at_equilibrium_le_heritability (p : Descent.Core.PopGenParameters)
    (V_E : ℝ) (hE : 0 ≤ V_E) (hflow : 0 < p.mu + p.mig) :
    presentDayR2 p.V_A V_E p.fstEquilibrium ≤ Descent.Core.share p.V_A V_E := by
  rw [presentDayR2_at_equilibrium]
  exact Descent.Core.ScoreMoments.deployedR2_le_heritability p V_E hE hflow

/-- **And it is in the unit interval at every history.** -/
theorem presentDayR2_at_equilibrium_mem_unit (p : Descent.Core.PopGenParameters)
    (V_E : ℝ) (hE : 0 ≤ V_E) (hflow : 0 < p.mu + p.mig) :
    0 ≤ presentDayR2 p.V_A V_E p.fstEquilibrium ∧
      presentDayR2 p.V_A V_E p.fstEquilibrium ≤ 1 := by
  rw [presentDayR2_at_equilibrium]
  exact Descent.Core.ScoreMoments.deployedR2_mem_unit p V_E hE hflow

/-- Exact bridge theorem: the dashboard algebraic `presentDayR2` equals statistical
`rsquared` when the relevant second-moment identities hold. -/
theorem presentDayR2_eq_statistical_rsquared_of_moments
    {k : ℕ} [Fintype (Fin k)]
    (dgp : Foundations.DataGeneratingProcess k)
    (signal : Foundations.Predictor k)
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
    presentDayR2 V_A V_E fst = PopGen.rsquared dgp signal dgp.trueExpectation := by
  have h_vsig_ne : presentDayPGSVariance V_A fst ≠ 0 := by linarith
  have h_vtrue_ne : presentDayPGSVariance V_A fst + V_E ≠ 0 := by linarith
  have h_if_not :
      ¬(presentDayPGSVariance V_A fst = 0 ∨ presentDayPGSVariance V_A fst + V_E = 0) := by
    intro h
    rcases h with h0 | h1
    · exact h_vsig_ne h0
    · exact h_vtrue_ne h1
  have h_rs :
      PopGen.rsquared dgp signal dgp.trueExpectation = (presentDayPGSVariance V_A fst) ^ 2 /
          (presentDayPGSVariance V_A fst * (presentDayPGSVariance V_A fst + V_E)) := by
    unfold PopGen.rsquared
    simp [h_vf, h_vg, h_cov, h_if_not]
  rw [h_rs]
  unfold presentDayR2 PopGen.TransportedMetrics.r2FromSignalVariance Descent.Core.share
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
      Foundations.Phi (Real.sqrt (presentDaySignalToNoise V_A V_E fst / 2)) := by
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
  unfold presentDaySignalToNoise presentDayPGSVariance pgsVarianceFromHet Descent.Core.product
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
    PopGen.TransportedMetrics.r2FromSignalVariance x V_E <
      PopGen.TransportedMetrics.r2FromSignalVariance y V_E := by
  unfold PopGen.TransportedMetrics.r2FromSignalVariance Descent.Core.share
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
  unfold presentDayR2 presentDayPGSVariance pgsVarianceFromHet Descent.Core.product
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
    PopGen.TransportedMetrics.r2FromSignalVariance x V_E <
      PopGen.TransportedMetrics.r2FromSignalVariance y V_E := by
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
  apply Foundations.strictMono_Phi
  have hsnr := drift_degrades_signalToNoise V_A V_E fstS fstT hVA hVE hfst
  have hhalf_nonneg : 0 ≤ presentDaySignalToNoise V_A V_E fstT / 2 := by
    have hsnr_nonneg : 0 ≤ presentDaySignalToNoise V_A V_E fstT := by
      unfold presentDaySignalToNoise presentDayPGSVariance pgsVarianceFromHet Descent.Core.product
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

/-- Reference evaluation; see `Descent.Core.Ratios` for what these pin and why. -/
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
    PopGen.TransportedMetrics.IrreducibleTargetPenalty where
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
  simp [targetIrreduciblePenaltyProfile, PopGen.TransportedMetrics.IrreducibleTargetPenalty.total,
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
    source and 2.50 in the target, on one end-to-end transport simulation with 400000 individuals
    per population and second moments SET rather than
    estimated. The two populations are what makes this a test of THIS body
    rather than of the numerator alone: `residualBurden` is zero in the source
    and the whole irreducible burden in the target, so the source cell fixes the
    numerator and the target cell is the one that can only pass if the burden is
    added, and added with coefficient one.

    What is NOT established: the internal structure of the burden. The four
    residuals enter only through their sum, as recorded at
    `ancestrySpecificLDResidual`; and the ADDITIVITY of `m.outcomeVariance` with the burden is what
    the target cell tests, at 2.50 sems, which is a pass and
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

/-- Source calibrated Brier coordinate from the full explicit source-state score equation,
evaluated at an arbitrary observed prevalence coordinate `π`. This lets downstream theory
compare source and target Brier on the same target-population outcome scale without falling
back to a benchmark `R²` surrogate.

    **THE SCALE OF THE EXPLAINED FRACTION IS THE WHOLE OF WHAT THIS BODY HAS TO GET RIGHT.**
    `r2FromSourceWeights` is a LIABILITY-scale fraction and a prevalence argument announces a
    dichotomised outcome, so the Brier body it is fed to must be the liability-threshold one.
    `calibratedBrierFromVariances` is not: it is the OBSERVED-scale body, right on that scale
    and measured wrong by 9% to 47%, at up to 299 sems, on a truncated liability tail.

    Empirical status: UNTESTED, inherited. `liabilityBrierExact` carries the head and the
    queued battery; this body adds no arithmetic, it only chooses which prevalence and which
    explained fraction to supply.

    argument_source: model, inherited. -/
noncomputable def sourceCalibratedBrierFromSourceWeightsAtPrevalence {p q : ℕ}
    (m : CrossPopulationMetricModel p q) (π : ℝ) : ℝ :=
  PopGen.TransportedMetrics.liabilityBrierExact π (r2FromSourceWeights m Pop.source)

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

/-- Target calibrated Brier coordinate from the full explicit driver state. Prevalence enters
here, so Brier can change even when the score moments are held fixed.

    It is the target-side twin of `sourceCalibratedBrierFromSourceWeightsAtPrevalence` and
    carries the same requirement for the same reason: the explained fraction is on the
    liability scale, the prevalence announces a dichotomised outcome, so the Brier body is the
    liability-threshold one. A twin that took the observed-scale chart while its partner took
    the liability one would put the two coordinates on different scales and let a comparison
    between them read as a portability loss.

    Empirical status: UNTESTED, inherited from `liabilityBrierExact`, which carries the head
    and the queued battery. -/
noncomputable def targetCalibratedBrierFromSourceWeights {p q : ℕ}
    (m : CrossPopulationMetricModel p q) : ℝ :=
  PopGen.TransportedMetrics.liabilityBrierExact
    m.targetPrevalence (r2FromSourceWeights m Pop.target)

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
    simulation. The same evidence condemned the identical chart carried under
    another name in `Program/OpenQuestions.lean`, which is why the combined
    portability there now multiplies in `ohtaKimuraSigmaDSq` instead.

    CONSUMERS. `jointTagLDKernelAt` multiplies this factor in and inherits the
    shape fault, and it is now the ONLY fault that kernel carries: the migration
    factor it used to inherit a second falsification through has been deleted
    outright.

    The earlier, control-less run reached the same conclusion by the same
    reasoning, and is kept because the reasoning is what the control licenses:
    coalescent theory gives Sved's `r² ≈ 1/(1 + 4·Nₑ·c)`, which is
    HYPERBOLIC in distance, not exponential, and the two differ in shape rather
    than scale. Measured `r²` between common SNP pairs binned over an
    eightyfold distance range (`Nₑ = 1000`, 5 Mb at `1e-8`, 8 replicates), with BOTH laws fitted to
    the same curve with one free rate and one free
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
    which of them a reader still has to work around.

    **THE SUCCESSOR IS ALREADY IN THE CORPUS, and it is
    `PopGen.LDDecayTheory.ohtaKimuraSigmaDSq`.** Every previous refutation of
    the exponential came from ONE simulator and one fitting procedure --
    binned `r²` off msprime -- so the shape was rejected without a replacement
    a consumer could move to, which leaves the falsified shape in use.
    `simcov/battery_sved01.py` puts the question to a forward two-locus
    Wright-Fisher engine instead, a different model class with a different
    estimator and no binning, and measures `σ_d² = E[D²]/E[pq p'q']` over
    `ρ = 4·Nₑ·c` from 0.5 to 20:

    | shape | worst cell |
    |---|---|
    | `ohtaKimuraSigmaDSq`, `(10+ρ)/((2+ρ)(11+ρ))` | **1.85 sems** |
    | this body's shape, `A·exp(-k·ρ)` | 6.29 sems (36% relative) |
    | Sved's `1/(1+ρ)` | 17.6 sems (86% relative) |

    The exponential there is FITTED BY LEAST SQUARES TO THE VERY CURVE IT IS
    BEING JUDGED ON, with a free amplitude AND a free rate, while the two
    hyperbolic forms are given no fitted constant at all. It still loses, which
    is the strongest form the claim can take: the failure cannot be a badly
    chosen `lambda`, because `lambda` was chosen optimally and the shape still
    does not fit. The control -- with recombination off, `E[D]` must decay by
    exactly `1 - 1/(2Nₑ)` per generation -- passed at 0.01 sems.

    What that battery did NOT do is add Sved's `E[r²] = 1/(1+4Nₑc)` as the
    successor, which is what it was written to do. `E[r²]` has no mutation-free
    equilibrium to measure: at a mutation rate low enough to leave the
    drift-recombination equilibrium intact the loci fix and the average is over
    the remnant nearest to fixation, and at one high enough to keep them
    polymorphic the measured `σ_d²` falls to 0.143 against Ohta-Kimura's 0.365.
    The ratio of expectations survives both; the expectation of the ratio does
    not. -/
noncomputable def ldCorrelationDecay (distance fstGap lambda : ℝ) : ℝ :=
  Real.exp (-(lambda * Real.sqrt fstGap * distance))

/-- Reference evaluation; see `Descent.Core.Ratios` for what these pin and why. -/
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

/-- **The hyperbolic candidate the falsification record names, written down so a battery can
    race it against the body it would replace.** `ldCorrelationDecay` is FALSIFIED as a shape
    in distance and its docstring names the successor — `ohtaKimuraSigmaDSq`, the
    Ohta-Kimura `(10 + ρ)/((2 + ρ)(11 + ρ))` — while stating an obstruction that stops the
    substitution. This declaration is that successor written at the falsified body's
    signature, with the `√fstGap` divergence factor carried over unchanged, so the two are
    functions of the same three arguments and one simulation can fit both.

    THE SHAPE IS NORMALISED TO ONE AT ZERO DISTANCE, by dividing through by
    `ohtaKimuraSigmaDSq` at `ρ = 0`, which is `10/22`. That keeps the boundary behaviour
    `ldCorrelationDecay` has — `Real.exp 0 = 1` — so a consumer swapping one for the other
    does not silently acquire a different value at zero separation.

    **NORMALISING DOES NOT CLEAR THE OBSTRUCTION, and this declaration does not claim it
    does.** Read the falsified body's docstring closely: the difficulty is not that the
    hyperbolic fails to reach one at zero distance — the naive
    `1/(1 + λ·√fstGap·d)` already does. It is that the fits which chose the hyperbolic over
    the exponential carried a FREE amplitude and measured it at 0.373 and 0.316, so an
    amplitude-one curve is not the curve that was fitted, and cell `I` bears on the shape
    only. Normalising to one is therefore how this candidate lands squarely on the object the
    measurement does not yet cover, rather than a way around it. What would settle it is the
    re-analysis that docstring already specifies: one cell fitting the amplitude-one
    hyperbolic against measured `r²` normalised to its own zero-distance limit. That is a
    re-analysis of a stored curve, not a new simulation.

    NOTHING HERE DISTURBS THE STANDING RECORDS. `ldCorrelationDecay` keeps its body and its
    FALSIFIED marker, and `jointTagLDKernelAt` keeps the shape fault it inherits through it.
    A candidate sitting beside a falsified body is not a repair of it; the marker moves when
    a battery moves it and not before.

    Empirical status: **MEASURED** (`validation/empirical/simcov/battery_ldshape01.py`). THE
    AMPLITUDE OBSTRUCTION IS CLEARED; THE SHAPE IS NOT SEPARATED FROM THE NAIVE HYPERBOLA. The
    re-analysis `ldCorrelationDecay`'s falsification record specifies has now been run, on the
    terms that record sets: one cell fitting the amplitude-1 hyperbolic against measured `r²`
    normalised to its own zero-distance limit, a re-analysis of cell `I`'s two stored curves
    and no new simulation.

    WHAT THE OBSTRUCTION WAS. That record refuses to install an amplitude-1 body because
    cell `I`'s fits "carry a free amplitude, measured at 0.373 and 0.316", so an amplitude-1
    curve "is NOT the curve that was fitted". The re-analysis measures each curve's OWN
    zero-distance limit from its three shortest bins alone — with the candidate's droop across
    them divided out — and finds 0.3798 ± 0.0244 and 0.3803 ± 0.0243. The free amplitudes the
    record objects to ARE those limits, to within one and two sems respectively:

      curve             A from the whole curve   A from the shortest bins   ratio
      Ne=2000, 4 Mb            0.3202                0.3798 ± 0.0244        0.843
      Ne=5000, 2 Mb            0.3826                0.3803 ± 0.0243        1.006

    So the free 0.32 was never a constant pulling away from the data; it was the data's own
    plateau. That the two curves agree on that plateau to 0.1% across a 2.5-fold change in
    `Nₑ` is the check that it is a real quantity: under the theory it is set by the shared
    sample size and MAF filter and not by `Nₑ`, and it behaves that way.

    WITH THE AMPLITUDE PINNED AT 1 AND ONLY THE RATE FREE — one parameter where cell `I`
    allowed two — this body matches the normalised curves at worst 2.57 sems, and the
    exponential shape `ldCorrelationDecay` carries is FALSIFIED at 12.05 sems and 78%
    relative on the same 26 cells. Power: the prediction spans 0.998 down to 0.020, a factor
    of 51.

    WHY THIS IS `MEASURED` AND NOT `VALIDATED`, and why `ldCorrelationDecay`'s marker has NOT
    moved. Three things the run does not deliver:

    * The naive amplitude-1 hyperbola `1/(1 + ρ)` matches at 2.58 sems — indistinguishable
      from this body's 2.57. THESE CURVES CANNOT CHOOSE BETWEEN THE TWO HYPERBOLAS, and the
      margin was measured three ways rather than asserted. On the anchor-normalised cells it
      is 2.57 against 2.58. On cell `I`'s own statistic — each shape given a free amplitude
      AND a free rate, χ² per point against the measurement sems with no anchor anywhere —
      it is 3.687 against 4.160 on one curve and 1.975 against 1.948 on the other, so the two
      shapes SPLIT one curve each at 1.1x, against the 7x and 40x that statistic returned when
      it rejected the exponential. A free rate reparametrises one hyperbola into the other
      across this range, which is why.

      Pinning the rate at its theoretical `4·Nₑ` — no free parameter left in either shape —
      does separate them, 14.0 against 286.7 and 140.3 against 901.7 in χ² per point. That
      comparison is NOT admissible here and is recorded so no one re-derives it as though it
      were: `ldCorrelationDecay`'s own record already established that this estimator's `Nₑ`
      recovery carries a large known downward bias, 563 against a true 1000, so the pinned
      rate is known to be wrong for BOTH shapes and the contest is between two handicapped
      curves. The implied `Nₑ_eff` bears that out — a consistent 70% and 72% of truth for this
      body and a consistent 33% for the naive one, each internally consistent across a
      2.5-fold change in `Nₑ`, which is what a reparametrisation looks like and not what a
      discrimination looks like.

      WHAT DOES BREAK THE TIE IS ALREADY IN THE CORPUS, on the estimator where `ρ` is exact by
      construction rather than fitted: `battery_sved01` measures `σ_d²` on a forward two-locus
      Wright-Fisher engine at known `ρ = 4·Nₑ·c` with no free constant, and there
      `ohtaKimuraSigmaDSq` matches at 1.85 sems while Sved's `1/(1 + ρ)` — the naive hyperbola
      — is FALSIFIED at 17.6 sems and 86% relative. So the shape this body is built from is
      preferred to its rival by a measurement, and by one this file's curves are too biased to
      make. The inference is CROSS-BATTERY and is flagged as such: it carries the assumption
      that the shape settled in `σ_d²` is the shape a normalised `E[r²]` decay follows, which
      is the same scale mismatch the third bullet below declines to discharge.
    * The residuals are large in absolute terms, 27% relative at the worst cell, because the
      anchor's own 6% uncertainty is carried into every bar. A match at that width is a weak
      constraint even where it holds.
    * The scale mismatch is untouched. These curves are binned `E[r²]`, the expectation of the
      ratio, while `ohtaKimuraSigmaDSq` is a closed form for `σ_d²`, the ratio of
      expectations, and `battery_sved01` established those are different numbers. Normalising
      each curve to its own zero limit is what makes this a comparison of SHAPES; the mismatch
      is not known to cancel exactly, so this record licenses the shape and the amplitude-1
      normalisation and does NOT license reading this body as a `σ_d²`.

    The control is what makes the amplitude number usable, and it failed first: fed synthetic
    curves of known amplitude 1, an earlier anchor that did not divide out the droop returned
    1.0400 ± 0.0031, a 4% bias at 12.8 sems — larger than the effect being reported. Corrected,
    it returns 0.998814 ± 0.002886. The bias was found by the control and not by a reading of
    the verdict.

    WHAT THIS RECORD RECOMMENDS, since the re-analysis it discharges was commissioned to
    decide replace-versus-delete for `ldCorrelationDecay`. The obstruction that record names
    is an amplitude obstruction and only that, and it is cleared: the amplitude-1 curve is the
    curve that was fitted. On those stated terms the exponential should be REPLACED by this
    shape rather than deleted, and the evidence for the replacement is four separate
    measurements — the exponential refuted here at 12.05 sems and by 8x to 270x in χ² per
    point, the amplitude-1 normalisation covered at 0.380 against free amplitudes of 0.316 and
    0.373, the Ohta-Kimura shape preferred to Sved's at 1.85 against 17.6 sems in
    `battery_sved01`, and the `√fstGap` exponent at 2.42 against 4.73 sems in
    `battery_bulk54`.

    TWO THINGS A SUBSTITUTION MUST HANDLE, neither of them an argument against it. The
    monotonicity theorems on the falsified body are proved through `Real.exp_lt_exp` and hold
    for every real distance; this shape has a pole at `ρ = -2`, so both need a nonnegativity
    hypothesis on the distance, which is a signature change consumers must absorb. And the
    composition — that `ρ` may be read as `λ·√fstGap·distance` in a CROSS-population setting —
    stays untested either way: these curves are within-population `r²` against genetic
    distance, so `fstGap` is never exercised. That gap is not a reason to keep the exponential,
    which carries the identical untested composition on top of a refuted shape.

    The `√fstGap` factor is the one part carried over already measured, at 2.42 sems against
    4.73 for the un-rooted rival, and nothing in this run bears on it: these curves are
    within-population `r²` against genetic distance, so `fstGap` is not exercised and `ρ` is
    read as a bare rate times distance. That `ρ` may be read as `λ·√fstGap·distance` remains
    untested. -/
noncomputable def ldCorrelationDecayHyperbolic (distance fstGap lambda : ℝ) : ℝ :=
  PopGen.ohtaKimuraSigmaDSq (1 / 4) (lambda * Real.sqrt fstGap * distance) /
    PopGen.ohtaKimuraSigmaDSq (1 / 4) 0

/-- The candidate agrees with `ldCorrelationDecay` at zero distance, which is the boundary
    condition the normalisation exists to preserve. Both are `1`. -/
theorem ldCorrelationDecayHyperbolic_at_reference_point :
    ldCorrelationDecayHyperbolic 0 0 0 = 1 := by
  unfold ldCorrelationDecayHyperbolic PopGen.ohtaKimuraSigmaDSq
  norm_num

/-- **The normalisation is the `10/22` the docstring names.** Stated separately so the
    amplitude this candidate commits to is a theorem rather than a constant buried in a
    body — it is the number the outstanding re-analysis has to bear on. -/
theorem ldCorrelationDecayHyperbolic_normalizer :
    PopGen.ohtaKimuraSigmaDSq (1 / 4) 0 = 10 / 22 := by
  unfold PopGen.ohtaKimuraSigmaDSq
  norm_num

/-- **The candidate in closed form**, with `ρ = λ·√fstGap·distance` cleared of the
    normalisation. Written so a fitter has the expression without unfolding two definitions,
    and so a replacement body that is not this curve cannot pass as it. The nonnegativity
    hypothesis is what keeps the Ohta-Kimura denominator off its pole at `ρ = -2`, which
    `ohtaKimuraSigmaDSq_cancelling_scaled_recombination_is_junk` names; every use of a decay
    law in distance supplies it. -/
theorem ldCorrelationDecayHyperbolic_closed (distance fstGap lambda : ℝ)
    (hrho : 0 ≤ lambda * Real.sqrt fstGap * distance) :
    ldCorrelationDecayHyperbolic distance fstGap lambda =
      22 * (10 + lambda * Real.sqrt fstGap * distance) /
        (10 * ((2 + lambda * Real.sqrt fstGap * distance) *
          (11 + lambda * Real.sqrt fstGap * distance))) := by
  have h2 : (2 : ℝ) + lambda * Real.sqrt fstGap * distance ≠ 0 := by positivity
  have h11 : (11 : ℝ) + lambda * Real.sqrt fstGap * distance ≠ 0 := by positivity
  unfold ldCorrelationDecayHyperbolic PopGen.ohtaKimuraSigmaDSq
  norm_num
  field_simp
  ring

/-- **The candidate is a decay: it is strictly below one at any positive scaled distance.**
    A shape normalised to one at the origin that failed this would be predicting that
    separation can strengthen an LD correlation. -/
theorem ldCorrelationDecayHyperbolic_lt_one (distance fstGap lambda : ℝ)
    (hpos : 0 < lambda * Real.sqrt fstGap * distance) :
    ldCorrelationDecayHyperbolic distance fstGap lambda < 1 := by
  rw [ldCorrelationDecayHyperbolic_closed distance fstGap lambda hpos.le]
  set r := lambda * Real.sqrt fstGap * distance with hr
  have h2 : 0 < 2 + r := by linarith
  have h11 : 0 < 11 + r := by linarith
  rw [div_lt_one (by positivity)]
  nlinarith [mul_pos h2 h11, sq_nonneg r]

/-! ### Generation-indexed population-genetic parameters

The record itself is `Core.PopGenParameters`, and this module writes out no second copy of
it. A local record with the same fields and the same positivity proofs as
`DGP.EvolutionaryParameters`, differing only in spelling `μ` for `mu` and in dropping the
divergence time, would mean a constraint tightened on one reaches the other only if someone
noticed. The accessors below are the generation-indexed laws this module adds to the shared
record, not a second record.
-/
end PresentDayMetrics

theorem wrightFisherDriftRetention_uses_timeScale (N : ℕ) (t : ℕ) :
    Portability.wrightFisherDriftRetention N t
      = (1 - 1 / Descent.Core.coalescentTimeScale (N : ℝ)) ^ t := by
  unfold Portability.wrightFisherDriftRetention; rw [Descent.Core.coalescentTimeScale_eq]

/-- **The between-population variance of the mean breeding value is
`ploidy · F_ST · V_A`.**

Two independently drifting populations each contribute `F_ST V_A`, so the
variance of their difference carries the ploidy factor. Writing `2` here is
the same convention as everywhere else and is now tied to it. -/
theorem Var_Delta_Mu_eq_ploidy_form (V_A fst : ℝ) :
    Portability.Var_Delta_Mu V_A fst = Descent.Core.ploidy * fst * V_A := by
  unfold Portability.Var_Delta_Mu Descent.Core.ploidy; ring

/-- **The transport name and the population-genetics name are one quantity.**

`PopGen.pgsDriftVariance_one_pop` is the drift variance of one population's mean breeding
value and `Var_Delta_Mu` is the same number under the name transport theory calls it by.
The two were previously joined by an alias that ran from PopGen UP into this file, which
made a population-genetics body unreadable without the transport layer; they are now
declared where each belongs and tied here, where both are in scope. -/
theorem Var_Delta_Mu_eq_pgsDriftVariance_one_pop (V_A fst : ℝ) :
    Portability.Var_Delta_Mu V_A fst = PopGen.pgsDriftVariance_one_pop V_A fst := by
  unfold Portability.Var_Delta_Mu PopGen.pgsDriftVariance_one_pop Descent.Core.ploidy; ring

/-- **Present-day PGS variance is a retained fraction of the ancestral variance.**
`presentDayPGSVariance` is not a wrapper over the kernel -- it routes through
`pgsVarianceFromHet` -- so this is a real identity and not a restatement of a body. -/
theorem presentDayPGSVariance_eq_retainedFraction (V_A fst : ℝ) :
    Portability.presentDayPGSVariance V_A fst = Descent.Core.retainedFraction fst V_A := by
  unfold Portability.presentDayPGSVariance Portability.pgsVarianceFromHet Descent.Core.product
    Descent.Core.retainedFraction
  ring

/-- **The realised target PGS variance is a retained fraction, scaled by transport.**
`PortabilityDrift.realWorldPGSVariance` erodes the additive variance by `1 - F_ST` and then
by the transported correlation. The first factor is `Core.retainedFraction`, the same
`(1 - loss) · total` map as the ascertainment survivor and the neutral portability ratio.
Those two now CALL the kernel and so need no theorem here; this one does not, because it
routes through a transported correlation as well, which is why it survives the deletion of
its four siblings. -/
theorem realWorldPGSVariance_eq_retainedFraction (V_A fst rhoSq : ℝ) :
    Portability.realWorldPGSVariance V_A fst rhoSq = rhoSq * Descent.Core.retainedFraction fst V_A
      := by
  unfold Portability.realWorldPGSVariance Descent.Core.retainedFraction; ring

/-- **Cross-check spanning the mating and drift modules: assortative mating and
drift act multiplicatively on the additive variance.**

`amEquilibriumVariance` inflates by `1/(1 - r h²)` and `presentDayPGSVariance`
deflates by `(1 - F_ST)`, and composing them gives the product. Stated because
the two modules described the same variance and were never related, which is
the condition under which a falsified companion of `amEquilibriumVariance`
survived. -/
theorem amEquilibrium_then_drift (V_A r h2 fst : ℝ) :
    Portability.presentDayPGSVariance (PopGen.amEquilibriumVariance V_A r h2) fst =
      (1 - fst) * (V_A / (1 - r * h2)) := by
  unfold Portability.presentDayPGSVariance Portability.pgsVarianceFromHet Descent.Core.product
    PopGen.amEquilibriumVariance
  ring

end Descent.Portability
