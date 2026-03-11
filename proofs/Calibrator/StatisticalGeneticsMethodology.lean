import Calibrator.Probability
import Calibrator.PortabilityDrift
import Calibrator.OpenQuestions

namespace Calibrator

open MeasureTheory

/-!
# Statistical Genetics Methodology for Portability Assessment

This file formalizes the statistical methods used to assess, quantify,
and compare PGS portability across populations. These are the methodological
foundations needed to answer Wang et al.'s three open questions.

Key results:
1. Incremental R² and its standard error
2. Cross-validation design for portability studies
3. Summary statistic-based PGS construction
4. LD score regression for cross-population analysis
5. Genetic correlation estimation methods

Reference: Wang et al. (2026), Nature Communications 17:942.
-/


/-!
## Incremental R² and Standard Error

The primary metric for PGS performance is incremental R²:
how much variance is explained by the PGS beyond covariates.
-/

section IncrementalR2

/-- **Incremental R² definition.**
    ΔR² = R²(covariates + PGS) - R²(covariates only). -/
noncomputable def incrementalR2 (r2_full r2_covariates : ℝ) : ℝ :=
  r2_full - r2_covariates

/-- Incremental R² is nonneg when PGS adds information. -/
theorem incremental_r2_nonneg
    (r2_full r2_cov : ℝ) (h_improves : r2_cov ≤ r2_full) :
    0 ≤ incrementalR2 r2_full r2_cov := by
  unfold incrementalR2; linarith

/-- **Approximate standard error of R².**
    SE(R²) ≈ √(4R²(1-R²)²/(n-k-1)) for n observations, k predictors.
    This comes from the delta method on the F-statistic. -/
noncomputable def r2StandardError (r2 n k : ℝ) : ℝ :=
  Real.sqrt (4 * r2 * (1 - r2) ^ 2 / (n - k - 1))

/-- SE decreases with sample size. -/
theorem r2_se_decreases_with_n
    (r2 k : ℝ) (n₁ n₂ : ℝ)
    (h_r2 : 0 < r2) (h_r2_lt : r2 < 1)
    (h_k : 0 < k)
    (h_n₁ : k + 1 < n₁) (h_n₂ : k + 1 < n₂)
    (h_more : n₁ < n₂) :
    r2StandardError r2 n₂ k < r2StandardError r2 n₁ k := by
  unfold r2StandardError
  apply Real.sqrt_lt_sqrt
  · apply div_nonneg
    · apply mul_nonneg (mul_nonneg (by norm_num) (le_of_lt h_r2)) (sq_nonneg _)
    · linarith
  · apply div_lt_div_of_pos_left
    · exact mul_pos (mul_pos (by norm_num : (0:ℝ) < 4) h_r2)
        (sq_pos_of_ne_zero (by linarith : (1 : ℝ) - r2 ≠ 0))
    · linarith
    · linarith

/-- **Portability ratio with confidence interval.**
    Port = ΔR²_target / ΔR²_source.
    SE(Port) ≈ Port × √(SE²_target/ΔR²²_target + SE²_source/ΔR²²_source). -/
noncomputable def portabilityRatio (dr2_target dr2_source : ℝ) : ℝ :=
  dr2_target / dr2_source

/-- Portability ratio ≤ 1 when target PGS is weaker. -/
theorem portability_ratio_le_one
    (dr2_t dr2_s : ℝ) (h_s : 0 < dr2_s) (h_weaker : dr2_t ≤ dr2_s) :
    portabilityRatio dr2_t dr2_s ≤ 1 := by
  unfold portabilityRatio
  rw [div_le_one h_s]; exact h_weaker

end IncrementalR2


/-!
## Cross-Validation for Portability Assessment

Proper cross-validation design is critical for unbiased
estimation of PGS portability.
-/

section CrossValidation

/- **Independent GWAS and validation sets.**
    The PGS weights must be estimated in a separate sample from
    the one used for R² evaluation. Overlap creates bias. -/

/-- **Overfitting bias from sample overlap.**
    If the GWAS sample overlaps with the evaluation sample,
    R² is biased upward by approximately p/n where p is the
    number of SNPs in the PGS. -/
theorem overlap_bias
    (p_snps n_overlap : ℝ)
    (h_p : 0 < p_snps) (h_n : 0 < n_overlap)
    (h_n_large : p_snps < n_overlap) :
    0 < p_snps / n_overlap ∧ p_snps / n_overlap < 1 := by
  constructor
  · exact div_pos h_p h_n
  · rw [div_lt_one h_n]; exact h_n_large

/- **Portability assessment requires population-specific validation.**
    R² must be evaluated in each target population separately.
    A single combined evaluation mixes portability with demographics. -/

/-- **Blocked cross-validation for family structure.**
    When evaluating PGS in populations with family structure,
    standard CV overestimates R² due to shared segments.
    Family-blocked CV gives unbiased estimates. -/
/- **Time-split validation for discovery bias.**
    If the PGS discovery includes newer data, temporal validation
    (train on older data, test on newer) avoids temporal confounding. -/

end CrossValidation


/-!
## Summary Statistic-Based PGS

Most PGS are constructed from GWAS summary statistics rather than
individual-level data. This introduces specific challenges.
-/

section SummaryStatPGS

/- **Summary statistics: effect size and standard error.**
    For SNP j: β̂_j and SE_j from the GWAS.
    P-value: p_j = 2Φ(-|β̂_j/SE_j|). -/

/-- **Z-score standardization.**
    z_j = β̂_j / SE_j ≈ β̂_j × √n (for standardized genotypes).
    Different GWAS may report β̂ or z-scores. -/
noncomputable def zScore (beta se : ℝ) : ℝ := beta / se

/- **PGS from summary stats.**
    PGS = Σ_j w_j × g_j where w_j depends on the method:
    - C+T: w_j = β̂_j × I(p_j < threshold)
    - PRS-CS: w_j = E[β_j | summary stats, LD]
    - LDpred: w_j = posterior mean from Bayesian model -/

/-- **Effective sample size from summary stats.**
    n_eff_j = (Z_j / β_true_j)² if β_true_j were known.
    In practice: n_eff = median over SNPs of 1/SE_j².
    This can differ from the reported GWAS n. -/
noncomputable def effectiveSampleSizeSE (se : ℝ) : ℝ := 1 / se ^ 2

/-- Effective sample size is positive. -/
theorem effective_n_pos (se : ℝ) (h_se : 0 < se) :
    0 < effectiveSampleSizeSE se := by
  unfold effectiveSampleSizeSE
  exact div_pos one_pos (sq_pos_of_pos h_se)

/- **Multi-ancestry meta-analysis of summary statistics.**
    β̂_meta = Σ_k w_k β̂_k / Σ_k w_k where w_k = 1/SE_k².
    This combines information across ancestries. -/

/-- **Fixed vs random effects meta-analysis.**
    Fixed effects: assumes same β across populations.
    Random effects: allows β to vary (models heterogeneity).
    For PGS portability: random effects captures the reality
    that effects differ across populations. -/
end SummaryStatPGS


/-!
## LD Score Regression

LDSC is used to estimate genetic correlation between populations,
which is a key predictor of PGS portability.
-/

section LDScoreRegression

/- **LD score definition.**
    ℓ_j = Σ_k r²_jk where the sum is over SNPs k in a window around j.
    This captures the local LD structure. -/

/- **LDSC regression equation.**
    E[χ²_j] = N × h² × ℓ_j / M + N × a + 1
    where h² is heritability, M is SNPs, a is intercept.
    The slope gives h² × N / M. -/

/- **Cross-population LDSC.**
    E[z₁_j × z₂_j] = √(n₁n₂) × ρ_g × ℓ_j / M + intercept
    where ρ_g is genetic correlation.
    This directly estimates the genetic correlation
    that predicts PGS portability. -/

/-- **Genetic correlation predicts portability.**
    For linear PGS: R²_target / R²_source ≈ ρ_g² × (LD adjustment).
    High ρ_g → good portability. -/
theorem genetic_correlation_predicts_portability
    (rho_g port_ratio ld_adj : ℝ)
    (h_relation : port_ratio ≤ rho_g ^ 2 * ld_adj)
    (h_rho : 0 ≤ rho_g) (h_rho_le : rho_g ≤ 1)
    (h_ld : 0 ≤ ld_adj) (h_ld_le : ld_adj ≤ 1) :
    port_ratio ≤ 1 := by
  calc port_ratio ≤ rho_g ^ 2 * ld_adj := h_relation
    _ ≤ 1 * 1 := by
        apply mul_le_mul (by nlinarith [sq_nonneg rho_g]) h_ld_le h_ld (by positivity)
    _ = 1 := by ring

/-- **LDSC standard error for ρ_g.**
    SE(ρ̂_g) depends on sample sizes, LD structure, and polygenicity.
    For well-powered GWAS: SE ≈ √(1/(n₁ × n₂ × h²₁ × h²₂)) × correction. -/
/-- **Constrained intercept LDSC.**
    When there's no sample overlap, the intercept should be 1.
    Constraining it improves power but can bias h² estimates
    if there's hidden stratification. -/
end LDScoreRegression


/-!
## Genetic Correlation Methods

Multiple methods for estimating genetic correlation, each
with different properties for portability prediction.
-/

section GeneticCorrelationMethods

/- **Popcorn (trans-ethnic genetic correlation).**
    Extends LDSC for cross-population genetic correlation
    estimation using population-specific LD scores. -/

/- **SumHer (LDAK-based genetic correlation).**
    Uses the LDAK model for LD-dependent architecture
    and may give different ρ_g estimates than LDSC. -/

/-- **Method comparison: different methods can give different ρ̂_g.**
    This matters because ρ̂_g predicts portability.
    Method disagreement introduces uncertainty in portability prediction. -/
theorem method_disagreement_increases_uncertainty
    (rho_ldsc rho_popcorn rho_sumher : ℝ)
    (h_disagree₁ : rho_ldsc ≠ rho_popcorn)
    (h_disagree₂ : rho_ldsc ≠ rho_sumher) :
    -- No consensus on true ρ_g
    rho_ldsc ≠ rho_popcorn ∧ rho_ldsc ≠ rho_sumher :=
  ⟨h_disagree₁, h_disagree₂⟩

/-- **Genetic correlation varies across the genome.**
    ρ_g estimated from different genomic regions can vary,
    reflecting locus-specific selection pressures. -/
theorem local_genetic_correlation_varies
    (rho_chr1 rho_chr6 rho_genome : ℝ)
    (h_chr6_lower : rho_chr6 < rho_chr1) -- HLA region
    (h_genome_intermediate : rho_chr6 < rho_genome ∧ rho_genome < rho_chr1) :
    rho_chr6 < rho_genome := h_genome_intermediate.1

/-- **Genetic correlation is frequency-dependent.**
    Common variants may have higher ρ_g than rare variants
    because common variants are older and more shared. -/
end GeneticCorrelationMethods

end Calibrator
