/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Calibrator.Probability
import Calibrator.PopulationGeneticsFoundations
import Calibrator.PortabilityDrift
import Calibrator.OpenQuestions

namespace Calibrator

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
  V_between / (V_between + 2 * V_within)

/-- **Cross-check: `Q_ST` and the coalescent `F_ST` are one map applied to two
different pairs of quantities.** `PopulationGeneticsFoundations.coalFst` sends
`(t, Nₑ)` to `t / (t + 2 Nₑ)`; `qst` sends `(V_b, V_w)` to
`V_b / (V_b + 2 V_w)`. The whole point of the `Q_ST` versus `F_ST` comparison
is that these two numbers are compared on the same scale, which requires the
factor of two to be the same factor of two in both. This theorem makes a
divergence between them a failed proof rather than a silent recalibration. -/
theorem qst_eq_coalFst_form (V_between V_within : ℝ) :
    qst V_between V_within = coalFst V_between V_within := by
  unfold qst coalFst; ring

/-- QST is in [0, 1] for nonneg components with positive denominator. -/
theorem qst_in_unit (V_b V_w : ℝ)
    (h_b : 0 ≤ V_b) (h_w : 0 < V_w) :
    0 ≤ qst V_b V_w ∧ qst V_b V_w ≤ 1 := by
  unfold qst
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
    - Var(ΔPGS) = Σᵢ βᵢ² × Var(Δpᵢ)     (independent loci)
                = Σᵢ βᵢ² × 2pᵢ(1-pᵢ) × Fst  (definition of Fst)
                = Fst × Σᵢ 2pᵢ(1-pᵢ)βᵢ²
                = Fst × V_A              (definition of additive genetic variance)

    This gives the variance of PGS change in one population due to drift.

    Empirical status: UNTESTED. -/
noncomputable def pgsDriftVariance_one_pop (V_A fst : ℝ) : ℝ :=
  fst * V_A

/-- Single-population PGS drift variance is nonneg. -/
theorem pgsDriftVariance_one_pop_nonneg (V_A fst : ℝ)
    (h_VA : 0 ≤ V_A) (h_fst : 0 ≤ fst) :
    0 ≤ pgsDriftVariance_one_pop V_A fst := by
  unfold pgsDriftVariance_one_pop; positivity

/-- **The same drift variance, as a sum over loci.**

The derivation quoted in the docstring above lived only in that docstring: the
closed form `fst × V_A` was a definition, and no object in this file was the
locus-wise process it was supposed to summarise. This is that process, on the
standardized scale where each locus contributes drift variance `fst` per unit
squared effect:

  `Var(ΔPGS) = Σᵢ fst × βᵢ²`.

`pgsDriftVarianceFromLoci_eq_closedForm` is the theorem that the sum and the
closed form agree, so the closed form can now be contradicted by changing either
one.

    Empirical status: UNTESTED. -/
noncomputable def pgsDriftVarianceFromLoci {n : ℕ} (fst : ℝ) (β : Fin n → ℝ) : ℝ :=
  ∑ i : Fin n, fst * β i ^ 2

/-- **The locus sum equals the closed form.** This is the step that was carried
in prose. -/
theorem pgsDriftVarianceFromLoci_eq_closedForm {n : ℕ} (fst : ℝ) (β : Fin n → ℝ) :
    pgsDriftVarianceFromLoci fst β =
      pgsDriftVariance_one_pop (∑ i : Fin n, β i ^ 2) fst := by
  unfold pgsDriftVarianceFromLoci pgsDriftVariance_one_pop
  rw [Finset.mul_sum]

/-- **PGS difference variance between two independently drifting populations.**

    For two populations that diverged from a common ancestor and drifted
    independently:
    - Var(PGS₁ - PGS₂) = Var(PGS₁) + Var(PGS₂)  (independence of drift)
                        = Fst × V_A + Fst × V_A
                        = 2 × Fst × V_A
                        = 2 × pgsDriftVariance_one_pop(V_A, Fst)

    The factor of 2 arises because both populations drift independently
    from their common ancestor, analogous to the factor of 2 in
    expectedFreqDiffSq for allele frequency differences.

    Empirical status: UNTESTED. -/
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
    Var(ΔPGS) = V_A × 2FST.
    The expected |ΔPGS| ∝ √(V_A × FST).

    Empirical status: UNTESTED. -/
noncomputable def expectedPGSDiffVariance (V_A fst : ℝ) : ℝ :=
  V_A * 2 * fst

/-- **The two-population PGS difference variance equals expectedPGSDiffVariance.**

    This connects the step-by-step derivation to the original definition:
    pgsDiffVariance_two_pop V_A fst
      = 2 × (fst × V_A)          (unfolding pgsDriftVariance_one_pop)
      = V_A × 2 × fst            (commutativity of multiplication)
      = expectedPGSDiffVariance V_A fst -/
theorem pgsDiffVariance_eq_expected (V_A fst : ℝ) :
    pgsDiffVariance_two_pop V_A fst = expectedPGSDiffVariance V_A fst := by
  unfold pgsDiffVariance_two_pop pgsDriftVariance_one_pop expectedPGSDiffVariance
  ring

/-- **And the two-population difference variance is the sum of two independent
copies of the locus sum**, which is the content the factor of two was standing
for. Chained with `pgsDiffVariance_eq_expected`, this ties
`expectedPGSDiffVariance` back to a process over loci rather than to a
restatement of itself. -/
theorem pgsDiffVariance_two_pop_eq_lociSum {n : ℕ} (fst : ℝ) (β : Fin n → ℝ) :
    pgsDiffVariance_two_pop (∑ i : Fin n, β i ^ 2) fst =
      pgsDriftVarianceFromLoci fst β + pgsDriftVarianceFromLoci fst β := by
  rw [pgsDriftVarianceFromLoci_eq_closedForm]
  unfold pgsDiffVariance_two_pop
  ring

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
    (h_naive_pos : 0 < stat_naive)
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
the `max 0` in `Calibrator.PopulationGeneticsFoundations.selectionMigrationEquilibrium`,
and with it the ordering theorem needs no range hypothesis at all.
-/

/-- **Effect correlation under stabilizing selection.** Neutral drift
decorrelates effects by `d`; stabilizing selection toward a shared optimum damps
that decorrelation by the factor `1 / (1 + s·N)`, where `s` is the selection
strength and `N` the effective population size.

    Empirical status: UNTESTED. -/
noncomputable def effectCorrelationStabilizingDriftSelection (d s N : ℝ) : ℝ :=
  1 - d / (1 + s * N)

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

    Empirical status: UNTESTED. -/
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
    (h_d_pos : 0 < d) (h_d_le : d ≤ 1)
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
  refine ⟨?_, stabilizing_maintains_architecture d s N h_d_pos h_d_le h_s h_N⟩
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
    (h_raw_pos : 0 < signal_raw) (h_bias_pos : 0 < strat_bias)
    (h_partial : strat_bias < signal_raw) :
    -- After removing stratification bias, signal is reduced but not eliminated
    0 < signal_raw - strat_bias ∧ signal_raw - strat_bias < signal_raw := by
  exact ⟨by linarith, by linarith⟩


end DetectingAdaptation

end Calibrator
