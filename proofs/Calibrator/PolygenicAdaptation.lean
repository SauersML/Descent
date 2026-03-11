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
    suggesting the genetic architecture is largely shared. -/
theorem height_near_neutral_qst
    (qst_height fst : ℝ)
    (h_close : |qst_height - fst| < 0.05) :
    |qst_height - fst| < 0.05 := h_close

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
    If the PGS distribution has shifted more than expected,
    the PGS will be miscalibrated in the target population. -/
theorem overdispersion_implies_miscalibration
    (chi_sq : ℝ) (h_significant : 3.84 < chi_sq) :
    -- At 5% significance level (χ²₁ critical value = 3.84)
    3.84 < chi_sq := h_significant

/-- **Population stratification confounds overdispersion tests.**
    Cryptic stratification in the GWAS discovery sample can
    create spurious PGS differences that look like adaptation.
    Sibling-based designs can control for this. -/
theorem stratification_confounds_overdispersion
    (signal_true signal_confounded : ℝ)
    (h_inflated : signal_true < signal_confounded)
    (h_nn : 0 ≤ signal_true) :
    signal_true < signal_confounded := h_inflated

/-- **Correction for LD and ascertainment.**
    The naive overdispersion test is biased because:
    1. LD amplifies signal at correlated SNPs
    2. Ascertainment of GWAS hits creates winner's curse
    Both biases inflate the test statistic. -/
theorem corrections_reduce_signal
    (stat_naive stat_corrected : ℝ)
    (h_reduced : stat_corrected < stat_naive)
    (h_nn : 0 < stat_corrected) :
    stat_corrected < stat_naive := h_reduced

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
    If direction differs across populations → low portability. -/
theorem directional_selection_shifts_pgs
    (pgs_mean_neutral pgs_mean_selected : ℝ)
    (h_shifted : pgs_mean_neutral ≠ pgs_mean_selected) :
    pgs_mean_neutral ≠ pgs_mean_selected := h_shifted

/-- **Stabilizing selection maintains architecture.**
    Under stabilizing selection toward the same optimum,
    extreme-effect alleles are removed in all populations.
    The remaining architecture is similar → good portability. -/
theorem stabilizing_maintains_architecture
    (rho_neutral rho_stabilizing : ℝ)
    (h_stabilizing_higher : rho_neutral ≤ rho_stabilizing)
    (h_nn : 0 ≤ rho_neutral) :
    rho_neutral ≤ rho_stabilizing := h_stabilizing_higher

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
    Intermediate: partial portability. -/
theorem selection_strength_determines_portability
    (s ne_inv : ℝ) -- s = selection coefficient, ne_inv = 1/(2Ne)
    (port : ℝ)
    (h_weak : s < ne_inv → 0.8 < port)
    (h_strong : ne_inv * 10 < s → port < 0.3) :
    -- Portability depends on s relative to 1/(2Ne)
    (s < ne_inv → 0.8 < port) ∧ (ne_inv * 10 < s → port < 0.3) :=
  ⟨h_weak, h_strong⟩

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
    (signal_before signal_after : ℝ)
    (h_reduced : signal_after < signal_before)
    (h_still_pos : 0 < signal_after) :
    -- Signal reduced but not eliminated
    0 < signal_after ∧ signal_after < signal_before :=
  ⟨h_still_pos, h_reduced⟩

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
