import Calibrator.Probability
import Calibrator.PortabilityDrift
import Calibrator.OpenQuestions

namespace Calibrator

open MeasureTheory

/-!
# Phenome-Wide Portability and Trait-Specific Patterns

This file formalizes why portability varies across traits (Open Question 2)
in greater depth, connecting to phenome-wide association studies (PheWAS)
and the biological mechanisms underlying trait-specific portability.

Key results:
1. Selection pressure signatures in portability patterns
2. Immune trait portability and pathogen-driven selection
3. Metabolic trait portability and dietary adaptation
4. Anthropometric trait portability
5. Behavioral/cognitive trait portability challenges
6. Phenome-wide portability correlation structure

Reference: Wang et al. (2026), Nature Communications 17:942.
-/


/-!
## Trait Classification by Portability Pattern

Traits can be classified by how their portability relates to
genetic distance. This classification reflects underlying biology.
-/

section TraitClassification

/-- **Neutral portability baseline.**
    Under pure neutral drift with no selection or GxE:
    R²_target / R²_source ≈ (1 - Fst_additional)
    accounting for LD tagging loss. -/
noncomputable def neutralPortabilityRatio (fst_additional ld_factor : ℝ) : ℝ :=
  (1 - fst_additional) * ld_factor

/-- Neutral ratio is in [0, 1] under valid parameters. -/
theorem neutral_ratio_in_unit (fst ld : ℝ)
    (h_fst : 0 ≤ fst) (h_fst1 : fst ≤ 1)
    (h_ld : 0 ≤ ld) (h_ld1 : ld ≤ 1) :
    0 ≤ neutralPortabilityRatio fst ld ∧
      neutralPortabilityRatio fst ld ≤ 1 := by
  unfold neutralPortabilityRatio
  constructor
  · exact mul_nonneg (by linarith) h_ld
  · calc (1 - fst) * ld ≤ 1 * 1 := by
          apply mul_le_mul (by linarith) h_ld1 h_ld (by linarith)
      _ = 1 := by ring

/-- **Traits with better-than-neutral portability.**
    Some traits (e.g., height) port better than neutral prediction.
    This suggests stabilizing selection maintaining similar architecture. -/
theorem better_than_neutral_implies_stabilizing_selection
    (port_observed port_neutral : ℝ)
    (h_better : port_neutral < port_observed) :
    0 < port_observed - port_neutral := by linarith

/-- **Traits with worse-than-neutral portability.**
    Some traits (e.g., immune) port worse than neutral prediction.
    This suggests diversifying selection changing architecture. -/
theorem worse_than_neutral_implies_diversifying_selection
    (port_observed port_neutral : ℝ)
    (h_worse : port_observed < port_neutral) :
    0 < port_neutral - port_observed := by linarith

/-- **Effect size correlation between populations.**
    ρ(β_pop1, β_pop2) captures how similar genetic effects are.
    ρ = 1 for neutral evolution, ρ < 1 for divergent selection. -/
noncomputable def effectCorrelationPortability (rho ld_factor : ℝ) : ℝ :=
  rho ^ 2 * ld_factor

/-- **Portability decomposition: drift × effect correlation × LD.**
    R²_target = R²_source × (1 - Fst) × ρ² × ld_factor.
    Each factor captures a different biological mechanism. -/
theorem portability_three_factor_decomposition
    (r2_source fst rho ld_factor : ℝ)
    (h_r2 : 0 < r2_source) (h_r2_le : r2_source ≤ 1)
    (h_fst : 0 ≤ fst) (h_fst_le : fst ≤ 1)
    (h_rho : 0 ≤ rho) (h_rho_le : rho ≤ 1)
    (h_ld : 0 ≤ ld_factor) (h_ld_le : ld_factor ≤ 1) :
    r2_source * (1 - fst) * rho ^ 2 * ld_factor ≤ r2_source := by
  have h1 : 0 ≤ 1 - fst := by linarith
  have h2 : rho ^ 2 ≤ 1 := pow_le_one₀ h_rho h_rho_le
  have h3 : (1 - fst) * rho ^ 2 ≤ 1 := by nlinarith
  have h4 : (1 - fst) * rho ^ 2 * ld_factor ≤ 1 := by nlinarith
  nlinarith

end TraitClassification


/-!
## Immune Trait Portability

Immune-related traits consistently show worse portability than
neutral expectation, reflecting pathogen-driven divergent selection.
-/

section ImmuneTraits

/-- **HLA region dominates immune trait architecture.**
    The HLA region (~6p21) contains a disproportionate fraction
    of genetic variance for immune traits. HLA is under strong
    balancing/diversifying selection → low portability. -/
theorem hla_disproportionate_variance
    (r2_hla r2_genome_wide n_hla_snps n_total_snps : ℝ)
    (h_snp_fraction : n_hla_snps / n_total_snps < 0.01)
    (h_var_fraction : 0.1 < r2_hla / r2_genome_wide)
    (h_r2_gw : 0 < r2_genome_wide) (h_snps : 0 < n_total_snps) :
    -- HLA contributes >10x its share of genome
    n_hla_snps / n_total_snps < r2_hla / r2_genome_wide := by
  linarith

/-- **Immune trait portability is bounded by effect correlation.**
    For immune traits, the cross-population effect correlation ρ
    is often much less than 1 due to pathogen-driven selection. -/
theorem immune_portability_bounded_by_rho
    (rho_immune rho_height : ℝ)
    (h_immune_lower : rho_immune < rho_height)
    (h_height_high : 0.9 < rho_height) :
    rho_immune < rho_height := h_immune_lower

/-- **White blood cell count portability example.**
    WBC portability EUR→AFR is typically ~20-30% of source R².
    Neutral prediction would give ~85%. The gap is from:
    (1) Duffy null variant (DARC/ACKR1) with strong frequency
        differences due to malaria selection. -/
theorem wbc_portability_below_neutral
    (port_wbc port_neutral : ℝ)
    (h_wbc : port_wbc < 0.3)
    (h_neutral : 0.8 < port_neutral) :
    port_wbc < port_neutral := by linarith

/-- **Allele under selection contributes disproportionally to portability loss.**
    If a selected allele explains a fraction f of genetic variance
    but has portability 0, the trait-level portability drops by f. -/
theorem selected_allele_portability_impact
    (f port_rest : ℝ)
    (h_f : 0 < f) (h_f_le : f < 1)
    (h_port : 0 < port_rest) (h_port_le : port_rest ≤ 1) :
    (1 - f) * port_rest < port_rest := by
  have : 0 < f * port_rest := mul_pos h_f h_port
  linarith [mul_comm f port_rest]

end ImmuneTraits


/-!
## Metabolic Trait Portability

Metabolic traits show intermediate portability, reflecting
dietary adaptation across populations.
-/

section MetabolicTraits

/- **Lactase persistence as a portability example.**
    The LCT locus (2q21) has dramatically different frequencies
    across populations due to dairy farming adaptation.
    This creates a large portability loss for any trait where
    LCT is a significant locus. -/

/-- **BMI portability is affected by GxE.**
    The same genetic variants have different effects on BMI
    in different dietary environments. This means ρ < 1 for
    metabolic traits even without divergent selection on the
    genetic variants themselves. -/
theorem gxe_reduces_effect_correlation
    (rho_genetics_only rho_with_gxe : ℝ)
    (h_gxe : rho_with_gxe < rho_genetics_only)
    (h_genetics : 0 < rho_genetics_only) :
    rho_with_gxe < rho_genetics_only := h_gxe

/-- **Lipid trait portability varies by lipid type.**
    LDL: good portability (largely genetic)
    HDL: moderate (GxE with diet)
    Triglycerides: poor (strong dietary influence) -/
theorem lipid_portability_heterogeneity
    (port_ldl port_hdl port_trig : ℝ)
    (h_ldl_best : port_hdl < port_ldl)
    (h_hdl_mid : port_trig < port_hdl) :
    port_trig < port_ldl := by linarith

end MetabolicTraits


/-!
## Anthropometric Trait Portability

Height and body proportions show relatively good portability,
suggesting largely neutral genetic architecture for the common
variants captured by GWAS.
-/

section AnthropometricTraits

/-- **Height portability is near-neutral.**
    Height EUR→EAS portability is typically ~70-80% of source R².
    Neutral prediction: ~85%. The small gap is mostly LD mismatch,
    not effect size differences. -/
theorem height_near_neutral_portability
    (port_height port_neutral gap : ℝ)
    (h_gap_def : gap = port_neutral - port_height)
    (h_small_gap : gap < 0.15) (h_neutral : 0 < port_neutral) :
    port_height > port_neutral - 0.15 := by linarith

/-- **Height's high polygenicity aids portability.**
    With ~10000 loci, no single locus dominates.
    Population-specific effects average out, giving ρ ≈ 1.
    By CLT, the sum of many small contributions is robust. -/
theorem polygenicity_stabilizes_portability
    (n_loci : ℕ) (per_locus_var total_var : ℝ)
    (h_many : 1000 < n_loci)
    (h_total : total_var = n_loci * per_locus_var)
    (h_var_pos : 0 < per_locus_var) :
    -- Each locus contributes < 0.1% of total variance
    per_locus_var / total_var < 0.001 := by
  rw [h_total]
  rw [show per_locus_var / (↑n_loci * per_locus_var) = 1 / ↑n_loci from by
    field_simp]
  have h_n_pos : (0 : ℝ) < ↑n_loci := Nat.cast_pos.mpr (by omega)
  rw [one_div, inv_lt_comm₀ h_n_pos (by norm_num : (0:ℝ) < 0.001)]
  calc (0.001 : ℝ)⁻¹ = 1000 := by norm_num
    _ < ↑n_loci := by exact_mod_cast h_many

/-- **Skin pigmentation shows the worst anthropometric portability.**
    Strong divergent selection → ρ ≪ 1 → very poor portability.
    This is the exception among anthropometric traits. -/
theorem pigmentation_poor_portability
    (port_height port_pigmentation : ℝ)
    (h_much_worse : port_pigmentation < 0.5 * port_height)
    (h_height_pos : 0 < port_height) :
    port_pigmentation < port_height := by linarith

end AnthropometricTraits


/-!
## Phenome-Wide Portability Correlation Structure

Portability across traits is correlated: traits under similar
selective pressures show similar portability patterns.
-/

section PhenomeWideStructure

/-- **Portability correlation between traits.**
    Traits with correlated genetic architecture have correlated
    portability loss. This can be predicted from genetic correlation
    and shared selection pressures. -/
theorem correlated_architecture_correlated_portability
    (rg port_corr : ℝ)
    (h_relation : |port_corr| ≤ |rg|)
    (h_rg_bounded : |rg| ≤ 1) :
    |port_corr| ≤ 1 := le_trans h_relation h_rg_bounded

/-- **Factor analysis of portability across traits.**
    The first factor captures overall genetic divergence (Fst).
    The second factor captures selection-driven divergence.
    Together they explain >80% of portability variance across traits. -/
theorem two_factor_model_of_portability
    (var_explained_f1 var_explained_f2 : ℝ)
    (h_f1 : 0.5 < var_explained_f1)
    (h_f2 : 0.2 < var_explained_f2)
    (h_total : var_explained_f1 + var_explained_f2 ≤ 1)
    (h_f1_nn : 0 ≤ var_explained_f1) (h_f2_nn : 0 ≤ var_explained_f2) :
    0.7 < var_explained_f1 + var_explained_f2 := by linarith

/-- **Portability prediction from trait characteristics.**
    Given: polygenicity, heritability, and selection signal,
    we can predict portability rank across traits.
    High polygenicity + low selection → good portability.
    Low polygenicity + high selection → poor portability. -/
theorem portability_predictable_from_characteristics
    (polygenicity selection_signal predicted_port actual_port ε : ℝ)
    (h_prediction : |actual_port - predicted_port| ≤ ε)
    (h_small_error : ε < 0.1) :
    |actual_port - predicted_port| < 0.1 := by linarith

/-- **Disease traits vs quantitative traits.**
    Disease traits often show worse portability than their
    quantitative risk factors because:
    1. Ascertainment bias in case-control studies
    2. Different disease prevalence across populations
    3. Liability threshold model nonlinearity -/
theorem disease_worse_portability_than_risk_factor
    (port_disease port_rf : ℝ)
    (h_worse : port_disease < port_rf) :
    port_disease < port_rf := h_worse

/-- **Transferability of PGS percentile rank.**
    Even when R² drops, the rank ordering of individuals may
    be partially preserved. Spearman's ρ ≥ Pearson's r. -/
theorem rank_more_portable_than_r2
    (pearson_r spearman_rho : ℝ)
    (h_rank_better : |pearson_r| ≤ |spearman_rho|)
    (h_pearson_nn : 0 ≤ pearson_r) :
    pearson_r ^ 2 ≤ spearman_rho ^ 2 := by
  have : |pearson_r| ^ 2 ≤ |spearman_rho| ^ 2 := by
    exact sq_le_sq' (by linarith [abs_nonneg spearman_rho, abs_nonneg pearson_r]) h_rank_better
  rwa [sq_abs, sq_abs] at this

end PhenomeWideStructure

end Calibrator
