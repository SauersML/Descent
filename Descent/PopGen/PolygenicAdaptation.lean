/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Core.Scaling
import Descent.PopGen.AssortativeMatingPGS
import Descent.PopGen.PopulationGeneticsFoundations.CoalescentTheory

assert_below Descent.Blindness Descent.Conditionals Descent.Decision

namespace Descent.PopGen

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
4. The weak and strong selection-strength regimes are disjoint
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

/-- Reference evaluation; see `Descent.Core.Ratios` for what these pin and why. -/
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

/-- **`Q_ST = F_ST` under drift alone.** This is the NULL the whole `Q_ST`-`F_ST` test is
read against, and until now this file described the test in prose without stating it.

Under pure drift the two variance components are determined by `F_ST` and the ancestral
additive variance: the between-population component is `2·F_ST·V_A`, which is the body
`expectedPGSDiffVariance` carries and which `battery_bulk3.py` measured at 60.79 against
60.98 ± 1.36, 183.12 against 185.13 ± 4.14 and 372.76 against 366.22 ± 8.19; the
within-population component is the retained fraction `(1 - F_ST)·V_A`. Feeding those two
into `Q_ST` returns `F_ST` exactly, for every `F_ST` and every nonzero `V_A`.

That exactness is the point. The test detects selection by `Q_ST` DEPARTING from `F_ST`,
so a null that held only approximately, or only in a limit, would leave every departure
ambiguous between selection and the approximation. The `2` in `Q_ST`'s denominator is what
makes it exact -- it is the same factor of two that
`expectedPGSDiffVariance`'s docstring records being 50.7 percent low at 22.7 sems without.

    Empirical status: NOT AN EMPIRICAL CLAIM -- this is algebra, given the two components.
    What is measured is the between-population component it is fed, and that measurement is
    cited above. A departure of a REAL `Q_ST` from a real `F_ST` is evidence about
    selection; this theorem is what makes "departure" mean something. -/
theorem qst_eq_fst_under_drift (fst V_A : ℝ) (hV : V_A ≠ 0) :
    qst (2 * fst * V_A) ((1 - fst) * V_A) = fst := by
  unfold qst Descent.Core.oddsLike
  field_simp
  ring

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
    corrected value is what `PortabilityDrift.Var_Delta_Mu` states for this same
    quantity, and that definition was validated on the same engine at 0.29 to
    1.19 sems -- so the two agreed only after this correction. `Var_Delta_Mu` is
    now DEFINED as this body rather than the other way round: the drift variance
    of a mean is population genetics, so the canonical body is the PopGen one and
    the transport file aliases it downward.

    The docstring below on `expectedPGSDiffVariance` predicted precisely this
    failure: a common wrong factor built into both sides of a cross-identity
    cancels and the identity survives. It did, for three definitions at once.

    Empirical status: **VALIDATED** after correction; the superseded body
    **FALSIFIED** at 22.7 sems.

    Power: the prediction spans 60.79 to 372.76 across the design. -/
noncomputable def pgsDriftVariance_one_pop (V_A fst : ℝ) : ℝ :=
  Descent.Core.ploidy * fst * V_A

/-- Reference evaluation; see `Descent.Core.Ratios` for what these pin and why. -/
theorem pgsDriftVariance_one_pop_at_reference_point :
    pgsDriftVariance_one_pop (1 / 2) (1 / 2) = 1 / 2 := by
  unfold pgsDriftVariance_one_pop Descent.Core.ploidy
  norm_num

/-- Single-population PGS drift variance is nonneg. -/
theorem pgsDriftVariance_one_pop_nonneg (V_A fst : ℝ)
    (h_VA : 0 ≤ V_A) (h_fst : 0 ≤ fst) :
    0 ≤ pgsDriftVariance_one_pop V_A fst := by
  unfold pgsDriftVariance_one_pop Descent.Core.ploidy
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
  unfold pgsDriftVarianceFromLoci pgsDriftVariance_one_pop Descent.Core.ploidy
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
  unfold pgsDiffVariance_two_pop pgsDriftVariance_one_pop Descent.Core.ploidy
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
    Descent.Core.ploidy
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
## Directional Selection and the Selection-Strength Regimes

Directional selection moves the score's mean; the two regimes a selection
coefficient can sit in, weak and strong relative to drift, are disjoint.

There is no cross-population effect-correlation law here for any selection
regime. The bodies that stood in this section returned a correlation rising
with selection strength, and forward Wright-Fisher measured it falling —
stabilizing selection toward a SHARED optimum decorrelates two populations
faster, not slower, because a shared optimum is reachable by different allelic
routes. The ordering those bodies were kept for, fluctuating decorrelating
further than stabilizing at matched strength, is real in the measurements and
has no body left to state it on.
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

/-- **The one-population PGS drift variance carries the ploidy factor explicitly.**

Its `2` is the `ploidy` convention: `ploidy · F_ST · V_A`.  `Portability.Var_Delta_Mu` is
this body under its transport name, and this pair of theorems is what says so rather than
leaving it to the reader. -/
theorem pgsDriftVariance_one_pop_eq_ploidy_form (V_A fst : ℝ) :
    PopGen.pgsDriftVariance_one_pop V_A fst = Descent.Core.ploidy * fst * V_A := by
  unfold PopGen.pgsDriftVariance_one_pop Descent.Core.ploidy
  ring

/-- The between-population drift variance of the score, carrying the same
ploidy factor as `Var_Delta_Mu`. -/
theorem expectedPGSDiffVariance_eq_ploidy_form (V_A fst : ℝ) :
    PopGen.expectedPGSDiffVariance V_A fst = Descent.Core.ploidy * Descent.Core.ploidy * fst * V_A
      := by
  unfold PopGen.expectedPGSDiffVariance Descent.Core.ploidy; ring

end Descent.PopGen
