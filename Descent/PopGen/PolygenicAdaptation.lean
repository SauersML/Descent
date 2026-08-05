/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.PopGen.PopulationGeneticsFoundations
import Descent.Core.Fst

namespace Descent

open MeasureTheory
open scoped BigOperators

/-!
# Polygenic Adaptation and PGS Portability

This file formalizes how polygenic adaptation — coordinated allele
frequency changes across many loci under selection — affects PGS
portability. Polygenic adaptation is subtle but can systematically
bias PGS predictions across populations.

Key results:
1. QST-FST test for polygenic selection
2. Polygenic score overdispersion under selection
3. Directional selection on PGS-relevant traits
4. Stabilizing vs directional selection effects
5. Detecting adaptation from GWAS summary statistics

Provenance: derived here, not imported. Wang et al. (2026), Nature Communications 17:942,
substantiates nothing below. It is an empirical study of the polygenic-score portability
gap and does not treat the QST-FST test or score overdispersion under selection. Sources
for individual results, where they exist, are cited at those results.
-/


/-!
## QST-FST Comparison

QST measures phenotypic differentiation between populations for
quantitative traits. Comparing QST to FST detects selection:
QST > FST → directional selection, QST < FST → stabilizing selection.
-/

section QSTFSTTest

/-- **QST definition.**
    QST = V_between / (V_between + 2 × V_within)
    where V_between and V_within are between- and within-population
    additive genetic variance components.

    Empirical status: UNTESTED. -/
noncomputable def qst (V_between V_within : ℝ) : ℝ :=
  Descent.Core.oddsLike V_between V_within

/-- **qst pinned at a reference point.** No theorem in the corpus evaluated this definition, so
every body agreeing with it in sign and monotonicity was indistinguishable from it. At all
arguments equal to `1 / 2` it is `1 / 3`, which fixes the
coefficients a one-sided bound or an invariance leaves free. -/
theorem qst_at_reference_point :
    qst (1 / 2) (1 / 2) = 1 / 3 := by
  unfold qst Descent.Core.oddsLike
  norm_num

/-- **qst where its denominator vanishes, named.** The guard `V_between + 2 * V_within` is zero at
`V_between = 0`, `V_within = 0`. With neither between- nor within-population variance there is
no differentiation to quantify. Lean returns `0` there rather than the value the modelled
quantity takes, and no type error marks the point. Consumers must require `V_between + 2 *
V_within ≠ 0`. -/
theorem qst_at_vbetween0vwithin0_is_junk :
    qst 0 0 = 0 := by
  unfold qst Descent.Core.oddsLike
  norm_num

/-- **No within-population variance makes the statistic one.**

The cross-check below identifies `Q_ST` with the coalescent `F_ST` as one map applied to two
different pairs, which constrains the two together and neither alone. This endpoint fixes the
factor of two: at zero within-population variance the ratio is one for every coefficient on
`V_within`, but the map only reaches one *there*, and a body with the factor elsewhere -- inside
the numerator, or on `V_between` -- fails. It is also the reading that makes `Q_ST` a proportion:
all of the additive variation is between populations exactly when none is within. -/
theorem qst_no_within (V_between : ℝ) (h : V_between ≠ 0) :
    qst V_between 0 = 1 := by
  unfold qst Descent.Core.oddsLike
  norm_num
  exact div_self h

/-- **Cross-check: `Q_ST` and the coalescent `F_ST` are one map applied to two
different pairs of quantities.** `PopulationGeneticsFoundations.coalFst` sends
`(t, Nₑ)` to `t / (t + 2 Nₑ)`; `qst` sends `(V_b, V_w)` to
`V_b / (V_b + 2 V_w)`. The whole point of the `Q_ST` versus `F_ST` comparison
is that these two numbers are compared on the same scale, which requires the
factor of two to be the same factor of two in both. This theorem makes a
divergence between them a failed proof rather than a silent recalibration. -/
theorem qst_eq_coalFst_form (V_between V_within : ℝ) :
    qst V_between V_within = coalFst V_between V_within := by
  unfold qst coalFst Descent.Core.oddsLike; ring

/-- QST is in [0, 1] for nonneg components with positive denominator. -/
theorem qst_in_unit (V_b V_w : ℝ)
    (h_b : 0 ≤ V_b) (h_w : 0 < V_w) :
    0 ≤ qst V_b V_w ∧ qst V_b V_w ≤ 1 := by
  unfold qst Descent.Core.oddsLike
  have h_denom : 0 < V_b + 2 * V_w := by linarith
  constructor
  · exact div_nonneg h_b (le_of_lt h_denom)
  · rw [div_le_one h_denom]; linarith

end QSTFSTTest


/-!
## Polygenic Score Overdispersion

Under polygenic adaptation, the PGS mean differences between
populations exceed what's expected from drift alone.
-/

section PGSOverdispersion

/-- **PGS drift variance in a single population.**

    **Derivation from drift theory:**
    - PGS = Σᵢ βᵢ × Gᵢ, so under drift E[ΔPGS] = Σᵢ βᵢ × E[Δpᵢ] = 0
      (drift is unbiased on allele frequencies).
    - Var(ΔPGS) = Σᵢ (ploidy·βᵢ)² × Var(Δpᵢ)     (independent loci)
                = Σᵢ 4βᵢ² × pᵢ(1-pᵢ) × Fst
                = 2·Fst × Σᵢ 2pᵢ(1-pᵢ)βᵢ²
                = 2·Fst × V_A            (definition of additive genetic variance)

    This gives the variance of PGS change in one population due to drift.

    **The ploidy factor was missing and the body has been corrected.** The chain
    above previously read `Var(ΔPGS) = Σᵢ βᵢ² × Var(Δpᵢ)`, dropping the `ploidy`
    that the score itself carries: a PGS is `Σᵢ βᵢ·Gᵢ` with `Gᵢ` a DOSAGE, so its
    mean is `Σᵢ βᵢ·2pᵢ` and a frequency change of `Δpᵢ` moves it by `2βᵢΔpᵢ`. The
    square of that is `4βᵢ²`, not `βᵢ²`, and the two factors of two collapse to
    one against the `2pᵢ(1-pᵢ)` inside `V_A`.

    Measured (`validation/empirical/simcov/battery_bulk3.py`,
    `test_drift_variance_family`): Wright-Fisher, `Ne = 200`, 600 loci, 4000
    replicate populations, variance of one population's mean score about the
    ancestral mean.

      generations   F       old (fst·V_A)   this (2·fst·V_A)   simulated
        30          0.072        30.39           60.79         60.98±1.36
       100          0.221        91.56          183.12        185.13±4.14
       250          0.465       186.38          372.76        366.22±8.19

    The superseded body is 50.7 percent low at 22.7 sems in every cell. The
    corrected value is what `PortabilityDrift.Var_Delta_Mu` already states for
    this same quantity, and that definition was validated on the same engine at
    0.29 to 1.19 sems -- so the two agreed only after this correction.

    The docstring below on `expectedPGSDiffVariance` predicted precisely this
    failure: a common wrong factor built into both sides of a cross-identity
    cancels and the identity survives. It did, for three definitions at once.

    Empirical status: **VALIDATED** after correction; the superseded body
    **FALSIFIED** at 22.7 sems.

    Power: the prediction spans 60.79 to 372.76 across the design. -/
noncomputable def pgsDriftVariance_one_pop (V_A fst : ℝ) : ℝ :=
  Var_Delta_Mu V_A fst

/-- **pgsDriftVariance_one_pop pinned at a reference point.** No theorem in the corpus evaluated
this definition, so every body agreeing with it in sign and monotonicity was indistinguishable
from it. At all arguments equal to `1 / 2` it is `1 / 2`, which fixes the coefficients a
one-sided bound or an invariance leaves free. It was `1 / 4` while the body was missing
its ploidy factor, and this line is what pins the correction to a number. -/
theorem pgsDriftVariance_one_pop_at_reference_point :
    pgsDriftVariance_one_pop (1 / 2) (1 / 2) = 1 / 2 := by
  unfold pgsDriftVariance_one_pop Var_Delta_Mu
  norm_num

/-- Single-population PGS drift variance is nonneg. -/
theorem pgsDriftVariance_one_pop_nonneg (V_A fst : ℝ)
    (h_VA : 0 ≤ V_A) (h_fst : 0 ≤ fst) :
    0 ≤ pgsDriftVariance_one_pop V_A fst := by
  unfold pgsDriftVariance_one_pop Var_Delta_Mu
  positivity

/-- **The same drift variance, as a sum over loci.**

The derivation quoted in the docstring above lived only in that docstring: the
closed form `fst × V_A` was a definition, and no object in this file was the
locus-wise process it was supposed to summarise. This is that process, on the
standardized scale where each locus contributes drift variance `fst` per unit
squared effect:

  `Var(ΔPGS) = 2 Σᵢ fst × βᵢ²`.

**That displayed equation carried no factor of two and has been corrected.** It
read `Var(ΔPGS) = Σᵢ fst × βᵢ²`, which is this body itself, and so said that this
sum IS the drift variance. The theorem immediately below says it is HALF of it,
and the paragraph after that explains why. The three could not all be right, and
the docstring's own displayed equation was the one that was wrong -- which is
worth recording rather than quietly fixing, because a definition whose summary
line contradicts the theorem underneath it is exactly the shape a reader trusts
and does not check.

Measured (`validation/empirical/simcov/battery_dis1.py`): Wright-Fisher,
`Ne = 200`, 400 loci, 2500 replicate populations, variance of ONE population's
mean score about the ancestral mean, with the effects drawn on the standardized
scale this docstring declares so that `Σ βᵢ²` is `V_A`:

  generations   F       Σ fst βᵢ²    2 Σ fst βᵢ²   simulated
     30         0.072      25.98        51.97      51.55 ± 1.46
    100         0.221      91.79       183.58     181.14 ± 5.12
    250         0.465     210.88       421.76     427.79 ± 12.10

The sum alone is 50 percent low at up to 17.9 sems; twice the sum is within 0.5
sems in every cell. The positive control is `pgsDriftVariance_one_pop = 2 fst
V_A`, validated independently on this engine in `battery_bulk3.py`.

`pgsDriftVarianceFromLoci_eq_closedForm` is the theorem that the sum and the
closed form agree, so the closed form can now be contradicted by changing either
one. It carries an explicit factor of two, and that factor is the whole content
of the scale difference: this sum is on the STANDARDIZED scale, where each
locus already carries its `2p(1-p)` inside `beta`, while
`pgsDriftVariance_one_pop` is on the DOSAGE scale, where the score is
`sum beta * G` with `G` counting alleles and the ploidy is still explicit. The
two are the same quantity written in two units, and writing the identity without
the factor -- as it stood -- asserted that the units agree.

    Empirical status: **VALIDATED as half the one-branch drift variance** (worst
    0.5 sems), and the reading its own summary line invited -- that the sum is
    that variance -- **FALSIFIED at 17.9 sems**. -/
noncomputable def pgsDriftVarianceFromLoci {n : ℕ} (fst : ℝ) (β : Fin n → ℝ) : ℝ :=
  ∑ i : Fin n, fst * β i ^ 2

/-- **The locus sum equals the closed form.** This is the step that was carried
in prose. -/
theorem pgsDriftVarianceFromLoci_eq_closedForm {n : ℕ} (fst : ℝ) (β : Fin n → ℝ) :
    2 * pgsDriftVarianceFromLoci fst β =
      pgsDriftVariance_one_pop (∑ i : Fin n, β i ^ 2) fst := by
  unfold pgsDriftVarianceFromLoci pgsDriftVariance_one_pop Var_Delta_Mu
  rw [Finset.mul_sum, Finset.mul_sum]
  exact Finset.sum_congr rfl (fun i _ ↦ by ring)

/-- **PGS difference variance between two independently drifting populations.**

    For two populations that diverged from a common ancestor and drifted
    independently:
    - Var(PGS₁ - PGS₂) = Var(PGS₁) + Var(PGS₂)  (independence of drift)
                        = 2·Fst × V_A + 2·Fst × V_A
                        = 4 × Fst × V_A
                        = 2 × pgsDriftVariance_one_pop(V_A, Fst)

    The factor of 2 arises because both populations drift independently
    from their common ancestor, analogous to the factor of 2 in
    expectedFreqDiffSq for allele frequency differences.

    Empirical status: **VALIDATED** after the ploidy correction
    (`validation/empirical/simcov/battery_bulk3.py`,
    `test_drift_variance_family`). Variance of the mean-score difference between
    two independently drifted populations, 4000 replicates. Before the
    correction to `pgsDriftVariance_one_pop` this definition inherited that
    body's missing ploidy factor and read 50.5 percent low at 22.6 sems; it is
    `2 * pgsDriftVariance_one_pop` and so was corrected with it. -/
noncomputable def pgsDiffVariance_two_pop (V_A fst : ℝ) : ℝ :=
  2 * pgsDriftVariance_one_pop V_A fst

/-- Two-population PGS difference variance decomposes as sum of
    independent single-population drift variances. -/
theorem pgsDiffVariance_two_pop_eq_sum (V_A fst : ℝ) :
    pgsDiffVariance_two_pop V_A fst =
      pgsDriftVariance_one_pop V_A fst + pgsDriftVariance_one_pop V_A fst := by
  unfold pgsDiffVariance_two_pop; ring

/-- **Expected PGS mean difference under drift.**
    Under pure drift, the PGS mean difference has variance:
    Var(ΔPGS) = V_A × 4FST.
    The expected |ΔPGS| ∝ √(V_A × FST).

    **Corrected with `pgsDriftVariance_one_pop`**, whose missing ploidy factor
    this definition inherited. Measured on the two-branch design of
    `battery_bulk3.py`: the superseded `V_A × 2FST` is 50.5 percent low at 22.6
    sems in every cell.

    Empirical status: **VALIDATED** after correction; the superseded body
    **FALSIFIED** at 22.6 sems. -/
noncomputable def expectedPGSDiffVariance (V_A fst : ℝ) : ℝ :=
  V_A * 4 * fst

/-- **At complete differentiation the difference variance is twice the additive variance.**

The agreement with `pgsDiffVariance_two_pop` recorded below is a cross-identity: both sides are
built from `pgsDriftVariance_one_pop`, so a common wrong factor cancels and the identity survives
it. Evaluating at `F_ST = 1` does not. Two populations that share no ancestry contribute one
additive variance each, so the difference carries exactly two, and that is the only reading under
which the factor is a count of populations rather than a fitted constant. -/
theorem expectedPGSDiffVariance_complete_differentiation (V_A : ℝ) :
    expectedPGSDiffVariance V_A 1 = 4 * V_A := by
  unfold expectedPGSDiffVariance
  ring

/-- **The two-population PGS difference variance equals expectedPGSDiffVariance.**

    This connects the step-by-step derivation to the original definition:
    pgsDiffVariance_two_pop V_A fst
      = 2 × (fst × V_A)          (unfolding pgsDriftVariance_one_pop)
      = V_A × 2 × fst            (commutativity of multiplication)
      = expectedPGSDiffVariance V_A fst -/
theorem pgsDiffVariance_eq_expected (V_A fst : ℝ) :
    pgsDiffVariance_two_pop V_A fst = expectedPGSDiffVariance V_A fst := by
  unfold pgsDiffVariance_two_pop pgsDriftVariance_one_pop Var_Delta_Mu
    expectedPGSDiffVariance
  ring

/-- **And the two-population difference variance is the sum of two independent
copies of the locus sum**, which is the content the factor of two was standing
for. Chained with `pgsDiffVariance_eq_expected`, this ties
`expectedPGSDiffVariance` back to a process over loci rather than to a
restatement of itself. -/
theorem pgsDiffVariance_two_pop_eq_lociSum {n : ℕ} (fst : ℝ) (β : Fin n → ℝ) :
    pgsDiffVariance_two_pop (∑ i : Fin n, β i ^ 2) fst =
      2 * (pgsDriftVarianceFromLoci fst β + pgsDriftVarianceFromLoci fst β) := by
  unfold pgsDiffVariance_two_pop pgsDriftVarianceFromLoci pgsDriftVariance_one_pop
    Var_Delta_Mu
  rw [Finset.mul_sum, Finset.mul_sum]
  rw [← Finset.sum_add_distrib, Finset.mul_sum]
  exact Finset.sum_congr rfl (fun i _ ↦ by ring)

/-- Expected variance is nonneg. -/
theorem expected_pgs_diff_var_nonneg (V_A fst : ℝ)
    (h_VA : 0 ≤ V_A) (h_fst : 0 ≤ fst) :
    0 ≤ expectedPGSDiffVariance V_A fst := by
  unfold expectedPGSDiffVariance; positivity


/-- **Population stratification confounds overdispersion tests.**
    Cryptic stratification in the GWAS discovery sample can
    create spurious PGS differences that look like adaptation.

    We prove the substantive claim: stratification bias can make a
    non-significant true signal appear significant. Specifically, if
    the true χ² statistic (delta_true² / drift_var) does not exceed
    the critical value, but the confounded signal (delta_true + bias)²
    is large enough, then the confounded χ² *does* exceed the critical
    value — a false positive for polygenic adaptation. -/
theorem stratification_confounds_overdispersion
    (delta_true strat_bias drift_var critical : ℝ)
    (h_drift_pos : 0 < drift_var)
    (h_not_sig : delta_true ^ 2 / drift_var ≤ critical)
    (h_confounded_sig : critical * drift_var < (delta_true + strat_bias) ^ 2) :
    delta_true ^ 2 / drift_var ≤ critical ∧
      critical < (delta_true + strat_bias) ^ 2 / drift_var := by
  exact ⟨h_not_sig, by rwa [lt_div_iff₀ h_drift_pos]⟩

/-- **Correction for LD and ascertainment.**
    The naive overdispersion test is biased because:
    1. LD amplifies signal at correlated SNPs
    2. Ascertainment of GWAS hits creates winner's curse
    Both biases inflate the test statistic.

    We prove the substantive claim: after subtracting positive LD and
    ascertainment biases from the naive statistic, the corrected value
    is strictly smaller than the naive value AND still positive (when
    the biases are less than the naive statistic). -/
theorem corrections_reduce_signal
    (stat_naive ld_bias ascertainment_bias : ℝ)
    (h_ld : 0 < ld_bias) (h_asc : 0 < ascertainment_bias)
    (h_partial : ld_bias + ascertainment_bias < stat_naive) :
    let stat_corrected := stat_naive - ld_bias - ascertainment_bias
    0 < stat_corrected ∧ stat_corrected < stat_naive := by
  simp only
  exact ⟨by linarith, by linarith⟩

end PGSOverdispersion


/-!
## Directional vs Stabilizing Selection

The type of selection determines how genetic architecture
changes across populations.
-/

section SelectionTypes

/-- **Directional selection shifts allele frequencies.**
    Under directional selection for higher trait values,
    alleles that increase the trait become more common.
    A nonzero selection coefficient s on a trait with additive
    genetic variance V_A shifts the PGS mean by s × V_A per generation;
    after t generations the mean differs from neutral. -/
theorem directional_selection_shifts_pgs
    (pgs_mean_neutral s V_A : ℝ) (t : ℕ)
    (h_s : s ≠ 0) (h_VA : 0 < V_A) (h_t : 0 < t) :
    pgs_mean_neutral ≠ pgs_mean_neutral + s * V_A * t := by
  have : s * V_A * t ≠ 0 := by
    apply mul_ne_zero (mul_ne_zero h_s (ne_of_gt h_VA))
    exact Nat.cast_ne_zero.mpr (by omega)
  intro h_eq
  have h_zero : s * V_A * t = 0 := by linarith
  exact this h_zero

/-!
### The effect-correlation family

**Do not write these correlations inline in theorem statements, and do not describe the
stabilizing model as `ρ = 1 - drift/(drift + selection)`.** That expression is
`1 - 1/(1 + s·N)` once `selection = d·s·N`, which is NOT the `1 - d/(1 + s·N)` computed
here; stating one and proving about the other is what named definitions prevent. The
definitions below are the
ones the theorems use, and the docstrings now describe them.

The fluctuating correlation is additionally clamped at `-1`. Unclamped,
`1 - d(1 + f·N)` leaves `[-1, 1]` as soon as `d(1 + f·N) > 2`, which is an
ordinary parameter regime, and the previous statement of
`fluctuating_selection_worst_portability` excluded it by a hypothesis assuming
the answer stayed in range. The clamp is the same absorbing-boundary device as
the `max 0` in `Descent.PopulationGeneticsFoundations.selectionMigrationEquilibrium`,
and with it the ordering theorem needs no range hypothesis at all.
-/

/-- **Effect correlation under stabilizing selection.** Neutral drift
decorrelates effects by `d`; stabilizing selection toward a shared optimum damps
that decorrelation by the factor `1 / (1 + s·N)`, where `s` is the selection
strength and `N` the effective population size.

    Empirical status: **FALSIFIED, including in sign**
    (`validation/empirical/popgensel/fluctcell.py`, cell F). Forward,
    individual-based Wright-Fisher with Gaussian stabilizing selection toward a
    SHARED optimum -- the setting this docstring describes -- 60 unlinked causal
    loci, two populations split from one ancestor for 20 generations, 150
    replicates per cell. `d` is fed REALIZED from a neutral arm run on the same
    loci, seeds and divergence time, not from a nominal parameter, because the
    predicted effect IS the gap between the neutral and selected arms.

    | `N` | `s` | `s·N` | realized `d` | measured `ρ` | this body | sems |
    |---|---|---|---|---|---|---|
    | 30 | 0.1 | 3 | 0.7305 | 0.2464 ± 0.0127 | 0.8174 | 45.0 |
    | 30 | 0.5 | 15 | 0.7305 | 0.2121 ± 0.0145 | 0.9543 | 51.3 |
    | 30 | 2.0 | 60 | 0.7305 | 0.1427 ± 0.0184 | 0.9880 | 45.8 |
    | 60 | 0.5 | 30 | 0.4618 | 0.4143 ± 0.0114 | 0.9851 | 49.9 |
    | 60 | 2.0 | 120 | 0.4618 | 0.3545 ± 0.0152 | 0.9962 | 42.1 |

    The damping has the wrong SIGN. This body is increasing in `s·N` -- stronger
    selection, better-preserved effects, rising to 0.996 -- while the measurement
    falls monotonically, because a shared optimum is reachable by different
    allelic routes and stronger selection lets the two populations take different
    ones faster. Neutral drift is not damped by stabilizing selection; it is
    accelerated by it.

    The positive control is the `s = 0` arm, where this body returns exactly the
    measured neutral correlation by construction, so the instrument agrees where
    it must; and the sweep moves 22 sems along the selection axis, so the
    disagreement is the measurement rather than the design's blindness.

    What survives is the ORDERING against `effectCorrelationFluctuating`: at
    matched strength the fluctuating arm decorrelates further than the
    stabilizing one (0.0844 against 0.3545 at `N = 60`, `s = 2`), which is what
    `fluctuating_selection_worst_portability` orders. The magnitudes
    are not to be read off either body. -/
noncomputable def effectCorrelationStabilizingDriftSelection (d s N : ℝ) : ℝ :=
  1 - d / (1 + s * N)

/-- **effectCorrelationStabilizingDriftSelection at its junk point, named.** When `1 + s * N`
vanishes the drift-to-selection ratio diverges and the effect correlation is undefined. The
divisor is zero, the ratio is junk-zero, and the correlation is `1`: PERFECTLY preserved effects,
the strongest portability claim available, at the parameter combination where the model breaks
down. Consumers must exclude the argument that makes the guard vanish. -/
theorem effectCorrelationStabilizingDriftSelection_balanced_is_junk (d : ℝ) :
    effectCorrelationStabilizingDriftSelection d 1 (-1) = 1 := by
  unfold effectCorrelationStabilizingDriftSelection
  norm_num

/-- **The decorrelation is the divergence divided by the selection-drift balance.** Membership in
`[-1, 1]` is shared by every rescaling of the second term; this fixes the scale. -/
theorem effectCorrelationStabilizingDriftSelection_gap (d s N : ℝ) (h : 1 + s * N ≠ 0) :
    (1 - effectCorrelationStabilizingDriftSelection d s N) * (1 + s * N) = d := by
  unfold effectCorrelationStabilizingDriftSelection
  field_simp
  ring

/-- **Effect correlation under fluctuating selection**, clamped to the correlation
range. Fluctuating selection accelerates decorrelation by the factor
`(1 + f·N)`; the clamp at `-1` is what keeps the quantity a correlation for every
parameter value rather than only on the range the ordering theorem wants.

    Empirical status: **FALSIFIED, and the clamp is where it fails**
    (`validation/empirical/popgensel/fluctcell.py`, cell F). Measured on a
    fluctuating-selection arm: the same forward Wright-Fisher as
    `effectCorrelationStabilizingDriftSelection`, except the optimum is a fresh
    `N(0, V_g)` draw every generation and INDEPENDENTLY in each population, which
    is what fluctuating selection is. `d` is fed REALIZED from the neutral arm of
    that same sweep.

    | `N` | `f` | `f·N` | realized `d` | measured `ρ` | this body | sems |
    |---|---|---|---|---|---|---|
    | 30 | 0.1 | 3 | 0.7377 | 0.2306 ± 0.0116 | -1 (clamped) | 106.5 |
    | 30 | 0.5 | 15 | 0.7377 | 0.1525 ± 0.0157 | -1 (clamped) | 73.6 |
    | 60 | 0.1 | 6 | 0.4411 | 0.5442 ± 0.0090 | -1 (clamped) | 171.8 |
    | 60 | 0.5 | 30 | 0.4411 | 0.3953 ± 0.0125 | -1 (clamped) | 111.4 |
    | 60 | 2.0 | 120 | 0.4411 | 0.0844 ± 0.0224 | -1 (clamped) | 48.4 |

    The clamp binds on EVERY cell with `f > 0`, because `d·(1 + f·N) > 2` as soon
    as `f·N > 1.7` at these realized `d`, and the docstring above already names
    that as "an ordinary parameter regime". So across the whole swept range this
    body returns the boundary value `-1` while the measurement sits between 0.08
    and 0.54 -- perfect anticorrelation predicted where a positive correlation is
    observed, at 48 to 172 sems. The clamp does keep the output inside `[-1, 1]`;
    what it does not do is make it right. It converts a formula that leaves the
    correlation range into one that is wrong while inside it, which is harder to
    notice.

    The positive control is the `f = 0` arm, where this body returns the measured
    neutral correlation exactly; and the sweep moves 21 sems along the selection
    axis, so the design can see fluctuating selection acting.

    What survives is the ORDERING: fluctuating selection does decorrelate further
    than stabilizing at matched strength (0.0844 against 0.3545 at `N = 60`,
    strength 2), which is the direction
    `fluctuating_selection_worst_portability` orders. The multiplicative
    form `(1 + f·N)` and the clamped value are not supported. -/
noncomputable def effectCorrelationFluctuating (d f N : ℝ) : ℝ :=
  max (-1) (1 - d * (1 + f * N))

/-- **Away from the clamp the correlation is exactly the linear expression.** The clamp is the
only nonlinearity, which is what the range theorem alone does not say. -/
theorem effectCorrelationFluctuating_unclamped (d f N : ℝ)
    (h : (-1 : ℝ) ≤ 1 - d * (1 + f * N)) :
    effectCorrelationFluctuating d f N = 1 - d * (1 + f * N) := by
  unfold effectCorrelationFluctuating
  exact max_eq_right h

/-- Both selected correlations are in `[-1, 1]` by construction, for any
decorrelation `0 ≤ d ≤ 1` and nonnegative scaled selection. **Do not supply this
bound as a hypothesis**; it is a theorem, and assuming it would let a model set it
inconsistently. -/
theorem effectCorrelation_mem_range
    (d s f N : ℝ)
    (h_d_nonneg : 0 ≤ d) (h_d_le : d ≤ 1)
    (h_sN : 0 ≤ s * N) (h_fN : 0 ≤ f * N) :
    (-1 ≤ effectCorrelationStabilizingDriftSelection d s N ∧
      effectCorrelationStabilizingDriftSelection d s N ≤ 1) ∧
    (-1 ≤ effectCorrelationFluctuating d f N ∧
      effectCorrelationFluctuating d f N ≤ 1) := by
  have h_denom_pos : (0 : ℝ) < 1 + s * N := by linarith
  have h_frac_nonneg : 0 ≤ d / (1 + s * N) := div_nonneg h_d_nonneg h_denom_pos.le
  have h_frac_le : d / (1 + s * N) ≤ 1 := by
    rw [div_le_one h_denom_pos]
    linarith
  have h_prod_nonneg : 0 ≤ d * (1 + f * N) := by nlinarith
  unfold effectCorrelationStabilizingDriftSelection effectCorrelationFluctuating
  refine ⟨⟨?_, ?_⟩, ⟨le_max_left _ _, ?_⟩⟩
  · linarith
  · linarith
  · apply max_le
    · norm_num
    · linarith

/-- **Stabilizing selection maintains architecture.**
    Under stabilizing selection toward the same optimum, extreme-effect
    alleles are removed in all populations. The remaining architecture
    is similar, yielding better portability.

    The model is the one `effectCorrelationStabilizingDriftSelection` states: neutral drift
    decorrelates by `d`, and stabilizing selection damps the decorrelation to
    `d / (1 + s·N)`, so `ρ_stab = 1 - d/(1 + s·N) > 1 - d = ρ_neutral`. -/
theorem stabilizing_maintains_architecture
    (d s N : ℝ)
    (h_d_pos : 0 < d)
    (h_s : 0 < s) (h_N : 0 < N) :
    1 - d < effectCorrelationStabilizingDriftSelection d s N := by
  unfold effectCorrelationStabilizingDriftSelection
  have h_sN : 0 < s * N := mul_pos h_s h_N
  have h_denom_pos : (0 : ℝ) < 1 + s * N := by linarith
  have h_frac_lt : d / (1 + s * N) < d := by
    rw [div_lt_iff₀ h_denom_pos]
    nlinarith
  linarith

/-- **Fluctuating selection is worst for portability.**
    Under the drift-selection model:
    - Stabilizing selection: ρ = 1 - d/(1 + s·N)  (selection restores correlation)
    - Neutral drift:         ρ = 1 - d              (no restoration)
    - Fluctuating selection: ρ = max (-1) (1 - d·(1 + f·N))  (selection
      accelerates divergence, clamped at the end of the correlation range)

    where d is the drift parameter, s is stabilizing selection strength,
    f is the fluctuation intensity, and N is effective population size.
    We derive the full ordering: ρ_fluctuating < ρ_neutral < ρ_stabilizing.

    **Status change.** The previous statement carried the hypothesis
    `d * (1 + f * N) < 1`, which assumed the unclamped fluctuating correlation
    stayed inside the correlation range — that is, it assumed away the regime in
    which the definition was ill-formed. With the clamp the ordering holds for
    every `0 < d ≤ 1` and positive `s, f, N`, so the headline claim is now
    strictly stronger rather than weaker. -/
theorem fluctuating_selection_worst_portability
    (d s f N : ℝ)
    (h_d_pos : 0 < d) (h_d_le : d ≤ 1)
    (h_s : 0 < s) (h_f : 0 < f) (h_N : 0 < N) :
    effectCorrelationFluctuating d f N < 1 - d ∧
      1 - d < effectCorrelationStabilizingDriftSelection d s N := by
  have h_fN : 0 < f * N := mul_pos h_f h_N
  refine ⟨?_, stabilizing_maintains_architecture d s N h_d_pos h_s h_N⟩
  unfold effectCorrelationFluctuating
  apply max_lt
  · linarith
  · -- 1 - d(1 + fN) < 1 - d, since d(1 + fN) > d
    nlinarith [mul_pos h_d_pos h_fN]

/-- **The weak and strong selection regimes are disjoint.**

    If `s < ne_inv` and `ne_inv * 10 < s` both held we would have `ne_inv * 10 < ne_inv`, which
    a positive `ne_inv` forbids. That is the whole content: two thresholds on one number cannot
    both be met.

    The portability reading — that near-neutral alleles transfer and strongly selected ones are
    population-specific — is why one would draw the boundary at `1/(2Nₑ)`, and it is not derived
    here. No allele, no population and no portability quantity appears below, so this cannot be
    cited as showing that selection strength determines portability. -/
theorem selection_strength_determines_portability
    (s ne_inv : ℝ) -- s = selection coefficient, ne_inv = 1/(2Ne)
    (h_ne_inv_pos : 0 < ne_inv) :
    ¬(s < ne_inv ∧ ne_inv * 10 < s) := by
  intro ⟨h1, h2⟩; linarith

end SelectionTypes


/-!
## Detecting Adaptation from GWAS Summary Statistics

Modern methods detect polygenic adaptation directly from
GWAS effect sizes and allele frequencies.
-/

section DetectingAdaptation

/-- **The height adaptation signal partially confounded.**
    Sohail et al. (2019) showed that much of the apparent height
    adaptation signal was due to residual stratification in UKBiobank.
    After correction, the signal was greatly reduced. -/
theorem stratification_reduces_adaptation_signal
    (signal_raw strat_bias : ℝ)
    (h_bias_pos : 0 < strat_bias)
    (h_partial : strat_bias < signal_raw) :
    -- After removing stratification bias, signal is reduced but not eliminated
    0 < signal_raw - strat_bias ∧ signal_raw - strat_bias < signal_raw := by
  exact ⟨by linarith, by linarith⟩


end DetectingAdaptation

end Descent
