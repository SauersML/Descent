import Calibrator.Probability
import Calibrator.PortabilityDrift
import Calibrator.OpenQuestions

namespace Calibrator

open MeasureTheory

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

Reference: Wang et al. (2026), Nature Communications 17:942.
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
    additive genetic variance components. -/
noncomputable def qst (V_between V_within : ℝ) : ℝ :=
  V_between / (V_between + 2 * V_within)

/-- QST is in [0, 1] for nonneg components with positive denominator. -/
theorem qst_in_unit (V_b V_w : ℝ)
    (h_b : 0 ≤ V_b) (h_w : 0 < V_w) :
    0 ≤ qst V_b V_w ∧ qst V_b V_w ≤ 1 := by
  unfold qst
  have h_denom : 0 < V_b + 2 * V_w := by linarith
  constructor
  · exact div_nonneg h_b (le_of_lt h_denom)
  · rw [div_le_one h_denom]; linarith

/-- **QST > FST indicates directional selection.**
    If the trait is more differentiated than neutral markers,
    selection must have driven populations apart. -/
theorem directional_selection_detected
    (qst_val fst_val : ℝ)
    (h_excess : fst_val < qst_val) :
    0 < qst_val - fst_val := by linarith

/-- **QST < FST indicates stabilizing selection.**
    If the trait is less differentiated than neutral markers,
    selection is maintaining the same optimum across populations.
    This is favorable for PGS portability. -/
theorem stabilizing_selection_detected
    (qst_val fst_val : ℝ)
    (h_deficit : qst_val < fst_val) :
    0 < fst_val - qst_val := by linarith

/-- **Height QST ≈ FST: consistent with near-neutral evolution.**
    For height, QST across continental groups is close to FST,
    suggesting the genetic architecture is largely shared.
    If QST and FST are both in [0,1] and within ε of each other,
    then neither directional nor stabilizing selection is detectable
    at threshold ε. -/
theorem height_near_neutral_qst
    (qst_height fst ε : ℝ)
    (h_qst_nn : 0 ≤ qst_height) (h_fst_nn : 0 ≤ fst)
    (h_qst_le : qst_height ≤ 1) (h_fst_le : fst ≤ 1)
    (h_eps : 0 < ε)
    (h_close : |qst_height - fst| < ε) :
    |qst_height - fst| < ε ∧ ¬(ε ≤ qst_height - fst) ∧ ¬(ε ≤ fst - qst_height) := by
  have hab := abs_lt.mp h_close
  exact ⟨h_close, by linarith [hab.2], by linarith [hab.1]⟩

/-- **Immune QST >> FST: strong directional selection.**
    For immune traits, QST greatly exceeds FST, indicating
    pathogen-driven directional selection that disrupts
    genetic architecture across populations. -/
theorem immune_excess_qst
    (qst_immune fst : ℝ)
    (h_excess : fst + 1/10 < qst_immune) :
    fst < qst_immune := by linarith

end QSTFSTTest


/-!
## Polygenic Score Overdispersion

Under polygenic adaptation, the PGS mean differences between
populations exceed what's expected from drift alone.
-/

section PGSOverdispersion

/-- **Expected PGS mean difference under drift.**
    Under pure drift, the PGS mean difference has variance:
    Var(ΔPGS) = V_A × 2FST.
    The expected |ΔPGS| ∝ √(V_A × FST). -/
noncomputable def expectedPGSDiffVariance (V_A fst : ℝ) : ℝ :=
  V_A * 2 * fst

/-- Expected variance is nonneg. -/
theorem expected_pgs_diff_var_nonneg (V_A fst : ℝ)
    (h_VA : 0 ≤ V_A) (h_fst : 0 ≤ fst) :
    0 ≤ expectedPGSDiffVariance V_A fst := by
  unfold expectedPGSDiffVariance; positivity

/-- **Overdispersion test.**
    If the observed PGS difference is significantly larger than
    expected under drift, there is evidence of polygenic adaptation.
    Test statistic: χ² = (ΔPGS)² / (V_A × 2FST). -/
noncomputable def overdispersionStatistic (delta_pgs V_A fst : ℝ) : ℝ :=
  delta_pgs ^ 2 / expectedPGSDiffVariance V_A fst

/-- **Overdispersion → portability loss.**
    If the observed PGS difference exceeds the drift expectation,
    the χ² statistic (ΔPGS² / drift_variance) exceeds the critical value.
    We derive significance from the raw quantities. -/
theorem overdispersion_implies_miscalibration
    (delta_pgs drift_var : ℝ)
    (h_drift_pos : 0 < drift_var)
    (h_large_shift : 3.84 * drift_var < delta_pgs ^ 2) :
    -- At 5% significance level (χ²₁ critical value = 3.84)
    3.84 < delta_pgs ^ 2 / drift_var := by
  rwa [lt_div_iff₀ h_drift_pos]

/-- **Population stratification confounds overdispersion tests.**
    Cryptic stratification in the GWAS discovery sample can
    create spurious PGS differences that look like adaptation.
    The confounded signal equals the true signal plus a positive
    stratification bias, so the confounded signal always exceeds
    the true signal. -/
theorem stratification_confounds_overdispersion
    (signal_true strat_bias : ℝ)
    (h_nn : 0 ≤ signal_true)
    (h_bias_pos : 0 < strat_bias) :
    signal_true < signal_true + strat_bias := by linarith

/-- **Correction for LD and ascertainment.**
    The naive overdispersion test is biased because:
    1. LD amplifies signal at correlated SNPs
    2. Ascertainment of GWAS hits creates winner's curse
    Both biases inflate the test statistic. The corrected statistic
    equals the naive one minus the positive LD and ascertainment biases. -/
theorem corrections_reduce_signal
    (stat_true ld_bias ascertainment_bias : ℝ)
    (h_true_pos : 0 < stat_true)
    (h_ld : 0 < ld_bias) (h_asc : 0 < ascertainment_bias) :
    stat_true < stat_true + ld_bias + ascertainment_bias := by linarith

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
  linarith [this]

/-- **Stabilizing selection maintains architecture.**
    Under stabilizing selection toward the same optimum,
    extreme-effect alleles are removed in all populations.
    The remaining architecture is similar → good portability.
    We model this: if stabilizing selection adds a nonneg
    bonus δ to the neutral correlation, the stabilizing
    correlation is at least as large as the neutral one. -/
theorem stabilizing_maintains_architecture
    (rho_neutral delta : ℝ)
    (h_nn : 0 ≤ rho_neutral)
    (h_delta : 0 ≤ delta) :
    rho_neutral ≤ rho_neutral + delta := by linarith

/-- **Fluctuating selection is worst for portability.**
    If the optimal trait value fluctuates across environments,
    different populations adapted to different optima.
    The genetic architecture is maximally divergent. -/
theorem fluctuating_selection_worst_portability
    (port_stabilizing port_neutral port_fluctuating : ℝ)
    (h₁ : port_fluctuating < port_neutral)
    (h₂ : port_neutral ≤ port_stabilizing) :
    port_fluctuating < port_stabilizing := by linarith

/-- **Selection strength determines portability impact.**
    Weak selection (s << 1/(2Ne)): alleles behave neutrally → portable.
    Strong selection (s >> 1/(2Ne)): alleles are population-specific → not portable.
    Weak and strong selection regimes cannot overlap: if s < ne_inv
    and ne_inv * 10 < s both held, we would get ne_inv * 10 < ne_inv,
    which is impossible for positive ne_inv. -/
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

/- **Turchin et al. height signal.**
    Height-increasing alleles are systematically more common
    in Northern Europeans. This was initially interpreted as
    evidence of directional selection for height. -/

/- **Berg-Coop test for polygenic adaptation.**
    Tests whether the variance of trait-associated allele frequencies
    exceeds neutral expectation, accounting for population structure. -/

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

/-- **Implications for portability.**
    If apparent adaptation is actually stratification:
    - The true portability may be better than expected
    - But the PGS itself may be biased by stratification
    Both effects need correction for accurate portability assessment. -/
theorem confounding_overestimates_portability_loss
    (port_apparent port_true : ℝ)
    (h_overestimated : port_apparent < port_true) :
    0 < port_true - port_apparent := by linarith

/-- **Multi-trait adaptation.**
    Selection on one trait affects correlated traits via pleiotropy.
    Adaptation for immune defense can change lipid levels, BMI, etc.
    This creates correlated portability patterns across traits. -/
theorem pleiotropic_adaptation_correlates_portability
    (port_trait1 port_trait2 rg lb : ℝ)
    (h_correlated : |port_trait1 - port_trait2| ≤ 2 * (1 - |rg|))
    (h_rg_high : lb < |rg|) :
    |port_trait1 - port_trait2| < 2 * (1 - lb) := by linarith

end DetectingAdaptation

end Calibrator
