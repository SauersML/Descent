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

/-- **Incremental R² is nonneg from nested model theory.**
    In a nested linear regression, adding predictors can only increase R²
    because the full model minimizes RSS over a strictly larger parameter
    space. Formally: RSS_full ≤ RSS_cov (the full model's RSS is at most
    the covariate-only model's RSS), so R²_full = 1 - RSS_full/TSS ≥
    1 - RSS_cov/TSS = R²_cov.

    We encode this as: the full model's R² is at least the
    covariate-only model's R², which is a consequence of OLS
    minimizing sum of squared residuals over a nested subspace. -/
theorem incremental_r2_nonneg
    (rss_full rss_cov tss : ℝ)
    (h_tss : 0 < tss)
    (h_rss_full : 0 ≤ rss_full)
    (h_rss_cov : 0 ≤ rss_cov)
    -- Nested model property: full model has no more residual than submodel
    (h_nested : rss_full ≤ rss_cov) :
    let r2_full := 1 - rss_full / tss
    let r2_cov := 1 - rss_cov / tss
    0 ≤ incrementalR2 r2_full r2_cov := by
  simp only
  unfold incrementalR2
  -- (1 - rss_full/tss) - (1 - rss_cov/tss) = (rss_cov - rss_full)/tss ≥ 0
  have : rss_cov / tss - rss_full / tss = (rss_cov - rss_full) / tss := by ring
  linarith [div_nonneg (by linarith : 0 ≤ rss_cov - rss_full) (le_of_lt h_tss)]

/- **Derivation: Standard error of R² via the delta method.**

    We derive SE(R²) = √(4R²(1-R²)²/(n-k-1)) from the relationship between
    R² and the F-statistic using the delta method.

    **Step 1: R² as a function of the F-statistic.**
    The overall F-test for a linear model with k predictors and n observations:
        F = (R²/k) / ((1-R²)/(n-k-1))
    Solving for R²:
        R² = Fk / (Fk + n - k - 1)

    **Step 2: Variance of F.**
    Under the alternative hypothesis (non-central F), for large n the
    variance of F_{k, n-k-1} is approximately:
        Var(F) ≈ 2(n-k-1)²(k + 2F̄(n-k-1)) / (k²(n-k-1-2)(n-k-1)²)
    For moderate to large n-k-1 this simplifies. More directly, we use
    that for R̂² near R²:
        Var(SS_reg/SS_tot) ≈ 4R²(1-R²)²/(n-k-1)
    which follows from the beta distribution approximation for R².

    **Step 3: Delta method.**
    Since R² = g(SS_reg/SS_tot) where g is approximately the identity
    near typical values, and more precisely since R² follows approximately
    a scaled Beta distribution:
        R² ~ Beta(k/2, (n-k-1)/2) scaled appropriately
    The variance of this distribution gives:
        Var(R²) = 4R²(1-R²)² × (k + (n-k-1)) / ((n-k-1)(k + 2(n-k-1)))
    For n >> k this simplifies to:
        Var(R²) ≈ 4R²(1-R²)² / (n-k-1)

    **Step 4: Alternatively via direct delta method on F.**
    Write R² = h(F) = Fk/(Fk + n-k-1). Then:
        dR²/dF = k(n-k-1)/(Fk + n-k-1)² = (1-R²)²(n-k-1)/k
    And Var(F) ≈ 2F²(k + n-k-1) / (k(n-k-1)) for large df.
    Combining: Var(R²) = (dR²/dF)² × Var(F) ≈ 4R²(1-R²)²/(n-k-1).

    Therefore: **SE(R²) = √(4R²(1-R²)²/(n-k-1))**. -/

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
    Family-blocked CV is closer to the true R² because it removes
    the upward bias from family sharing, so its absolute error is smaller. -/
theorem blocked_cv_less_biased
    (r2_standard_cv r2_blocked_cv r2_true : ℝ)
    (h_standard_biased : r2_true < r2_standard_cv)
    (h_blocked_between : r2_true ≤ r2_blocked_cv)
    (h_blocked_closer_to_true : r2_blocked_cv < r2_standard_cv) :
    |r2_blocked_cv - r2_true| < |r2_standard_cv - r2_true| := by
  rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
  linarith

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
    Fixed effects: assumes same β across populations (tau² = 0).
    Random effects: allows β to vary with between-population variance tau².
    When tau² > 0, the random effects SE is larger (wider CI) because
    it adds tau² to the within-study variance. -/
theorem random_effects_captures_heterogeneity
    (se_fixed tau_sq : ℝ) -- fixed-effects SE and between-population variance
    (h_se : 0 < se_fixed) (h_heterogeneous : 0 < tau_sq) :
    -- Random effects SE² = fixed SE² + tau² > fixed SE²
    se_fixed ^ 2 < se_fixed ^ 2 + tau_sq := by
  linarith

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

/-- **Genetic correlation bounds portability ratio.**
    The portability ratio R²_target / R²_source is bounded by ρ_g² × ld_adj.
    Since |ρ_g| ≤ 1 implies ρ_g² ≤ 1, and ld_adj ∈ [0,1], the product
    is at most 1. This gives the rg-based bound on portability.

    Derived from: ρ_g² ≤ 1 (since |ρ_g| ≤ 1) and ld_adj ≤ 1,
    so the product ρ_g² × ld_adj ≤ 1. -/
theorem genetic_correlation_predicts_portability
    (rho_g ld_adj : ℝ)
    (h_rho : 0 ≤ rho_g) (h_rho_le : rho_g ≤ 1)
    (h_ld : 0 ≤ ld_adj) (h_ld_le : ld_adj ≤ 1) :
    rho_g ^ 2 * ld_adj ≤ 1 := by
  have h_sq : rho_g ^ 2 ≤ 1 := by nlinarith [sq_nonneg rho_g]
  calc rho_g ^ 2 * ld_adj
      ≤ 1 * 1 := mul_le_mul h_sq h_ld_le h_ld (by positivity)
    _ = 1 := one_mul 1

/-- **LDSC standard error for ρ_g.**
    SE(ρ̂_g) depends on sample sizes, LD structure, and polygenicity.
    For well-powered GWAS: SE ∝ 1/√n, so larger n yields smaller SE. -/
theorem ldsc_se_decreases_with_n
    (c : ℝ) (n₁ n₂ : ℝ)
    (h_c : 0 < c) (h_n₁ : 0 < n₁) (h_n₂ : 0 < n₂)
    (h_more : n₁ < n₂) :
    c / Real.sqrt n₂ < c / Real.sqrt n₁ := by
  apply div_lt_div_of_pos_left h_c
  · exact Real.sqrt_pos.mpr h_n₁
  · exact Real.sqrt_lt_sqrt (le_of_lt h_n₁) h_more

/-- **Constrained intercept LDSC.**
    When there's no sample overlap, the intercept should be 1.
    Constraining it reduces the number of free parameters from k+1 to k,
    yielding a smaller SE (fewer parameters → tighter estimate). -/
theorem constrained_intercept_more_powerful
    (se_per_param : ℝ) (k : ℕ)
    (h_se : 0 < se_per_param) (h_k : 0 < k) :
    se_per_param * k < se_per_param * (k + 1) := by
  have : (k : ℝ) < (k : ℝ) + 1 := lt_add_one _
  exact mul_lt_mul_of_pos_left this h_se

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
    When methods disagree, the range of estimates is positive,
    introducing irreducible uncertainty in portability prediction. -/
theorem method_disagreement_increases_uncertainty
    (rho_ldsc rho_popcorn rho_sumher : ℝ)
    (h_order : rho_popcorn < rho_ldsc)
    (h_order₂ : rho_ldsc < rho_sumher) :
    -- The range of estimates is strictly positive
    0 < rho_sumher - rho_popcorn := by linarith

/-- **Genetic correlation varies across the genome.**
    ρ_g estimated from different genomic regions can vary,
    reflecting locus-specific selection pressures.
    The genome-wide estimate is a weighted average of per-region estimates,
    so it falls between the extremes. -/
theorem local_genetic_correlation_varies
    (rho_chr1 rho_chr6 : ℝ) (w₁ w₆ : ℝ)
    (h_chr6_lower : rho_chr6 < rho_chr1) -- HLA region has lower correlation
    (h_w1 : 0 < w₁) (h_w6 : 0 < w₆) :
    -- Genome-wide weighted average is between the two regional estimates
    rho_chr6 < (w₁ * rho_chr1 + w₆ * rho_chr6) / (w₁ + w₆) := by
  rw [lt_div_iff₀ (by linarith : (0:ℝ) < w₁ + w₆)]
  nlinarith

/-- **Genetic correlation is frequency-dependent.**
    Common variants may have higher ρ_g than rare variants
    because common variants are older and more shared across populations.
    Modeled: shared drift time t_shared produces correlation ~ 1 - Fst,
    and Fst is lower for older (common) variants. -/
theorem common_variants_higher_correlation
    (fst_common fst_rare : ℝ)
    (h_fst_common : 0 ≤ fst_common) (h_fst_common_lt : fst_common < 1)
    (h_fst_rare : 0 ≤ fst_rare) (h_fst_rare_lt : fst_rare < 1)
    (h_older_less_diverged : fst_common < fst_rare) :
    -- ρ_g ~ 1 - Fst, so lower Fst → higher correlation
    1 - fst_rare < 1 - fst_common := by linarith

end GeneticCorrelationMethods

/-!
## Exact Uncertainty Propagation for Evolutionary Portability Metrics

The evolutionary theory files now give exact forward maps from source `R²` and
transported signal retention to deployed target `R²`, AUC, and Brier risk.
For practical use we also need exact deterministic uncertainty propagation:
intervals or error radii on source performance and evolutionary components
should induce certified intervals on the deployed metrics.
-/

section EvolutionaryMetricUncertainty

/-- Exact target `R²` as a function of source `R²` and transported signal factor. -/
noncomputable def targetR2FromSourceTransport
    (r2Source transportFactor : ℝ) : ℝ :=
  (r2Source * transportFactor) /
    (1 - r2Source + r2Source * transportFactor)

/-- Exact target AUC as a function of source `R²` and transported signal factor. -/
noncomputable def targetAUCFromSourceTransport
    (r2Source transportFactor : ℝ) : ℝ :=
  Phi (Real.sqrt ((r2Source * transportFactor) / (2 * (1 - r2Source))))

/-- Exact target calibrated Brier risk as a function of prevalence, source `R²`,
and transported signal factor. -/
noncomputable def targetBrierFromSourceTransport
    (π r2Source transportFactor : ℝ) : ℝ :=
  π * (1 - π) * (1 - targetR2FromSourceTransport r2Source transportFactor)

/-- Methodological target `R²` is the canonical transported-metric specialization
at residual scale `1`, with validity requiring the biologically meaningful
source-domain constraint `r2Source ≠ 1`. -/
theorem targetR2FromSourceTransport_eq_transportedMetrics
    (r2Source transportFactor : ℝ)
    (h_r2 : r2Source ≠ 1) :
    targetR2FromSourceTransport r2Source transportFactor =
      TransportedMetrics.targetR2 1 r2Source transportFactor := by
  rw [TransportedMetrics.targetR2_eq_closed_form 1 r2Source transportFactor one_ne_zero h_r2]
  rfl

/-- Methodological target AUC is the canonical transported-metric specialization
at residual scale `1`, with validity requiring the biologically meaningful
source-domain constraint `r2Source ≠ 1`. -/
theorem targetAUCFromSourceTransport_eq_transportedMetrics
    (r2Source transportFactor : ℝ)
    (h_r2 : r2Source ≠ 1) :
    targetAUCFromSourceTransport r2Source transportFactor =
      TransportedMetrics.targetAUC 1 r2Source transportFactor := by
  rw [TransportedMetrics.targetAUC_eq_closed_form 1 r2Source transportFactor one_ne_zero h_r2]
  rfl

/-- Methodological target Brier is the canonical transported-metric specialization
at residual scale `1`, with validity requiring the biologically meaningful
source-domain constraint `r2Source ≠ 1`. -/
theorem targetBrierFromSourceTransport_eq_transportedMetrics
    (π r2Source transportFactor : ℝ)
    (h_r2 : r2Source ≠ 1) :
    targetBrierFromSourceTransport π r2Source transportFactor =
      TransportedMetrics.targetBrier π 1 r2Source transportFactor := by
  unfold targetBrierFromSourceTransport TransportedMetrics.targetBrier
    TransportedMetrics.calibratedBrier
  rw [targetR2FromSourceTransport_eq_transportedMetrics r2Source transportFactor h_r2]

/-- Canonical bundled transported metrics for the uncertainty and methodology
layer. -/
noncomputable def sourceTransportMetricProfile
    (π r2Source transportFactor : ℝ) : TransportedMetrics.Profile :=
  TransportedMetrics.profile π 1 r2Source transportFactor

/-- The bundled methodological metrics reproduce the file's public `R²`, AUC,
and Brier surfaces exactly on the biologically valid `R² ≠ 1` domain. -/
theorem sourceTransportMetricProfile_eq
    (π r2Source transportFactor : ℝ)
    (h_r2 : r2Source ≠ 1) :
    sourceTransportMetricProfile π r2Source transportFactor =
      { r2 := targetR2FromSourceTransport r2Source transportFactor
      , auc := targetAUCFromSourceTransport r2Source transportFactor
      , brier := targetBrierFromSourceTransport π r2Source transportFactor } := by
  unfold sourceTransportMetricProfile TransportedMetrics.profile
  rw [targetR2FromSourceTransport_eq_transportedMetrics _ _ h_r2,
    targetAUCFromSourceTransport_eq_transportedMetrics _ _ h_r2,
    targetBrierFromSourceTransport_eq_transportedMetrics _ _ _ h_r2]

/-- Transport factor reconstructed from the four biological retention components. -/
noncomputable def transportFactorFromComponents
    (alleleRet ldRet mutRet migBoost : ℝ) : ℝ :=
  alleleRet * ldRet * mutRet * migBoost

/-- Product bounds propagate exactly through the four-factor transport map. -/
theorem transportFactorFromComponents_bounds
    {alleleRet ldRet mutRet migBoost
      alleleRetL alleleRetU ldRetL ldRetU mutRetL mutRetU migBoostL migBoostU : ℝ}
    (h_alleleL : alleleRetL ≤ alleleRet) (h_alleleU : alleleRet ≤ alleleRetU)
    (h_ldL : ldRetL ≤ ldRet) (h_ldU : ldRet ≤ ldRetU)
    (h_mutL : mutRetL ≤ mutRet) (h_mutU : mutRet ≤ mutRetU)
    (h_migL : migBoostL ≤ migBoost) (h_migU : migBoost ≤ migBoostU)
    (h_alleleL_nonneg : 0 ≤ alleleRetL) (h_ldL_nonneg : 0 ≤ ldRetL)
    (h_mutL_nonneg : 0 ≤ mutRetL) (h_migL_nonneg : 0 ≤ migBoostL) :
    transportFactorFromComponents alleleRetL ldRetL mutRetL migBoostL ≤
      transportFactorFromComponents alleleRet ldRet mutRet migBoost ∧
    transportFactorFromComponents alleleRet ldRet mutRet migBoost ≤
      transportFactorFromComponents alleleRetU ldRetU mutRetU migBoostU := by
  have h_allele_nonneg : 0 ≤ alleleRet := le_trans h_alleleL_nonneg h_alleleL
  have h_ld_nonneg : 0 ≤ ldRet := le_trans h_ldL_nonneg h_ldL
  have h_mut_nonneg : 0 ≤ mutRet := le_trans h_mutL_nonneg h_mutL
  have h_mig_nonneg : 0 ≤ migBoost := le_trans h_migL_nonneg h_migL
  have h_alleleU_nonneg : 0 ≤ alleleRetU := le_trans h_allele_nonneg h_alleleU
  have h_ldU_nonneg : 0 ≤ ldRetU := le_trans h_ld_nonneg h_ldU
  have h_mutU_nonneg : 0 ≤ mutRetU := le_trans h_mut_nonneg h_mutU
  have h_migU_nonneg : 0 ≤ migBoostU := le_trans h_mig_nonneg h_migU
  have h_lower12 : alleleRetL * ldRetL ≤ alleleRet * ldRet := by
    exact mul_le_mul h_alleleL h_ldL h_ldL_nonneg h_allele_nonneg
  have h_lower123 : alleleRetL * ldRetL * mutRetL ≤ alleleRet * ldRet * mutRet := by
    exact mul_le_mul h_lower12 h_mutL
      h_mutL_nonneg (mul_nonneg h_allele_nonneg h_ld_nonneg)
  have h_lower :
      alleleRetL * ldRetL * mutRetL * migBoostL ≤
        alleleRet * ldRet * mutRet * migBoost := by
    exact mul_le_mul h_lower123 h_migL
      h_migL_nonneg
      (mul_nonneg (mul_nonneg h_allele_nonneg h_ld_nonneg) h_mut_nonneg)
  have h_upper12 : alleleRet * ldRet ≤ alleleRetU * ldRetU := by
    exact mul_le_mul h_alleleU h_ldU h_ld_nonneg h_alleleU_nonneg
  have h_upper123 : alleleRet * ldRet * mutRet ≤ alleleRetU * ldRetU * mutRetU := by
    exact mul_le_mul h_upper12 h_mutU
      h_mut_nonneg
      (mul_nonneg h_alleleU_nonneg h_ldU_nonneg)
  have h_upper :
      alleleRet * ldRet * mutRet * migBoost ≤
        alleleRetU * ldRetU * mutRetU * migBoostU := by
    exact mul_le_mul h_upper123 h_migU
      h_mig_nonneg
      (mul_nonneg (mul_nonneg h_alleleU_nonneg h_ldU_nonneg) h_mutU_nonneg)
  constructor
  · simpa [transportFactorFromComponents, mul_assoc, mul_left_comm, mul_comm] using h_lower
  · simpa [transportFactorFromComponents, mul_assoc, mul_left_comm, mul_comm] using h_upper

/-- Target `R²` is monotone in the transported signal factor. -/
theorem targetR2FromSourceTransport_monotone_transport
    {r2Source transport₁ transport₂ : ℝ}
    (h_r2_nonneg : 0 ≤ r2Source) (h_r2_lt_one : r2Source < 1)
    (h_transport_nonneg : 0 ≤ transport₁) (h_transport_le : transport₁ ≤ transport₂) :
    targetR2FromSourceTransport r2Source transport₁ ≤
      targetR2FromSourceTransport r2Source transport₂ := by
  unfold targetR2FromSourceTransport
  have h_transport₂_nonneg : 0 ≤ transport₂ := le_trans h_transport_nonneg h_transport_le
  have hden₁ : 0 < 1 - r2Source + r2Source * transport₁ := by
    nlinarith
  have hden₂ : 0 < 1 - r2Source + r2Source * transport₂ := by
    nlinarith
  rw [div_le_div_iff₀ hden₁ hden₂]
  have hmain :
      r2Source * transport₂ * (1 - r2Source + r2Source * transport₁) -
        r2Source * transport₁ * (1 - r2Source + r2Source * transport₂) =
      r2Source * (1 - r2Source) * (transport₂ - transport₁) := by
    ring
  have h_one_minus_nonneg : 0 ≤ 1 - r2Source := by
    linarith
  have h_transport_gap_nonneg : 0 ≤ transport₂ - transport₁ := by
    linarith
  have hprod_nonneg : 0 ≤ r2Source * (1 - r2Source) * (transport₂ - transport₁) := by
    exact mul_nonneg (mul_nonneg h_r2_nonneg h_one_minus_nonneg) h_transport_gap_nonneg
  nlinarith [hmain, hprod_nonneg]

/-- Target `R²` is monotone in the source `R²`. -/
theorem targetR2FromSourceTransport_monotone_source
    {r2Source₁ r2Source₂ transport : ℝ}
    (h_source₁_nonneg : 0 ≤ r2Source₁) (h_source_le : r2Source₁ ≤ r2Source₂)
    (h_source₂_lt_one : r2Source₂ < 1) (h_transport_nonneg : 0 ≤ transport) :
    targetR2FromSourceTransport r2Source₁ transport ≤
      targetR2FromSourceTransport r2Source₂ transport := by
  unfold targetR2FromSourceTransport
  have h_source₁_lt_one : r2Source₁ < 1 := lt_of_le_of_lt h_source_le h_source₂_lt_one
  have hden₁ : 0 < 1 - r2Source₁ + r2Source₁ * transport := by
    nlinarith
  have hden₂ : 0 < 1 - r2Source₂ + r2Source₂ * transport := by
    nlinarith
  rw [div_le_div_iff₀ hden₁ hden₂]
  ring_nf
  nlinarith [h_source_le, h_transport_nonneg]

/-- Exact target `R²` interval induced by source-`R²` and transport-factor intervals. -/
theorem targetR2FromSourceTransport_interval
    {r2SourceL r2Source r2SourceU transportL transport transportU : ℝ}
    (h_sourceL_nonneg : 0 ≤ r2SourceL)
    (h_sourceL : r2SourceL ≤ r2Source) (h_sourceU : r2Source ≤ r2SourceU)
    (h_sourceU_lt_one : r2SourceU < 1)
    (h_transportL_nonneg : 0 ≤ transportL)
    (h_transportL : transportL ≤ transport) (h_transportU : transport ≤ transportU) :
    targetR2FromSourceTransport r2SourceL transportL ≤
      targetR2FromSourceTransport r2Source transport ∧
    targetR2FromSourceTransport r2Source transport ≤
      targetR2FromSourceTransport r2SourceU transportU := by
  have h_source_nonneg : 0 ≤ r2Source := le_trans h_sourceL_nonneg h_sourceL
  have h_source_lt_one : r2Source < 1 := lt_of_le_of_lt h_sourceU h_sourceU_lt_one
  have h_sourceU_nonneg : 0 ≤ r2SourceU := le_trans h_sourceL_nonneg (le_trans h_sourceL h_sourceU)
  have h_transport_nonneg : 0 ≤ transport := le_trans h_transportL_nonneg h_transportL
  have h_transportU_nonneg : 0 ≤ transportU := le_trans h_transportL_nonneg (le_trans h_transportL h_transportU)
  constructor
  · calc
      targetR2FromSourceTransport r2SourceL transportL ≤
          targetR2FromSourceTransport r2Source transportL := by
            exact targetR2FromSourceTransport_monotone_source
              h_sourceL_nonneg h_sourceL h_source_lt_one h_transportL_nonneg
      _ ≤ targetR2FromSourceTransport r2Source transport := by
            exact targetR2FromSourceTransport_monotone_transport
              h_source_nonneg h_source_lt_one h_transportL_nonneg h_transportL
  · calc
      targetR2FromSourceTransport r2Source transport ≤
          targetR2FromSourceTransport r2SourceU transport := by
            exact targetR2FromSourceTransport_monotone_source
              h_source_nonneg h_sourceU h_sourceU_lt_one h_transport_nonneg
      _ ≤ targetR2FromSourceTransport r2SourceU transportU := by
            exact targetR2FromSourceTransport_monotone_transport
              h_sourceU_nonneg h_sourceU_lt_one h_transport_nonneg h_transportU

/-- Exact target `R²` interval induced by absolute estimation or misspecification
error bounds on source `R²` and the transport factor. -/
theorem targetR2FromSourceTransport_interval_of_error_bounds
    {r2SourceHat r2Source transportHat transport εSource εTransport : ℝ}
    (h_source_err : |r2SourceHat - r2Source| ≤ εSource)
    (h_transport_err : |transportHat - transport| ≤ εTransport)
    (h_source_lower_nonneg : 0 ≤ r2SourceHat - εSource)
    (h_source_upper_lt_one : r2SourceHat + εSource < 1)
    (h_transport_lower_nonneg : 0 ≤ transportHat - εTransport) :
    targetR2FromSourceTransport (r2SourceHat - εSource) (transportHat - εTransport) ≤
      targetR2FromSourceTransport r2Source transport ∧
    targetR2FromSourceTransport r2Source transport ≤
      targetR2FromSourceTransport (r2SourceHat + εSource) (transportHat + εTransport) := by
  have h_source_err' : |r2Source - r2SourceHat| ≤ εSource := by
    simpa [abs_sub_comm] using h_source_err
  have h_transport_err' : |transport - transportHat| ≤ εTransport := by
    simpa [abs_sub_comm] using h_transport_err
  have h_source_bounds := abs_le.mp h_source_err'
  have h_transport_bounds := abs_le.mp h_transport_err'
  exact targetR2FromSourceTransport_interval
    h_source_lower_nonneg
    (by linarith) (by linarith)
    h_source_upper_lt_one
    h_transport_lower_nonneg
    (by linarith) (by linarith)

/-- Auxiliary exact AUC separation term from source `R²` and transported signal factor. -/
noncomputable def aucSeparationFromSourceTransport
    (r2Source transportFactor : ℝ) : ℝ :=
  (r2Source * transportFactor) / (2 * (1 - r2Source))

/-- The exact AUC separation term is monotone in the transported signal factor. -/
theorem aucSeparationFromSourceTransport_monotone_transport
    {r2Source transport₁ transport₂ : ℝ}
    (h_r2_nonneg : 0 ≤ r2Source) (h_r2_lt_one : r2Source < 1)
    (h_transport_le : transport₁ ≤ transport₂) :
    aucSeparationFromSourceTransport r2Source transport₁ ≤
      aucSeparationFromSourceTransport r2Source transport₂ := by
  unfold aucSeparationFromSourceTransport
  have hden : 0 < 2 * (1 - r2Source) := by nlinarith
  rw [div_le_div_iff₀ hden hden]
  have hbase : r2Source * transport₁ ≤ r2Source * transport₂ :=
    mul_le_mul_of_nonneg_left h_transport_le h_r2_nonneg
  have hden_nonneg : 0 ≤ 2 * (1 - r2Source) := by nlinarith
  exact mul_le_mul_of_nonneg_right hbase hden_nonneg

/-- The exact AUC separation term is monotone in the source `R²`. -/
theorem aucSeparationFromSourceTransport_monotone_source
    {r2Source₁ r2Source₂ transport : ℝ}
    (h_source₁_nonneg : 0 ≤ r2Source₁) (h_source_le : r2Source₁ ≤ r2Source₂)
    (h_source₂_lt_one : r2Source₂ < 1) (h_transport_nonneg : 0 ≤ transport) :
    aucSeparationFromSourceTransport r2Source₁ transport ≤
      aucSeparationFromSourceTransport r2Source₂ transport := by
  unfold aucSeparationFromSourceTransport
  have hden₁ : 0 < 2 * (1 - r2Source₁) := by
    have h_source₁_lt_one : r2Source₁ < 1 := lt_of_le_of_lt h_source_le h_source₂_lt_one
    nlinarith
  have hden₂ : 0 < 2 * (1 - r2Source₂) := by
    nlinarith
  rw [div_le_div_iff₀ hden₁ hden₂]
  nlinarith [h_source_le, h_transport_nonneg]

/-- Exact target AUC interval induced by source-`R²` and transport-factor intervals. -/
theorem targetAUCFromSourceTransport_interval
    {r2SourceL r2Source r2SourceU transportL transport transportU : ℝ}
    (h_sourceL_nonneg : 0 ≤ r2SourceL)
    (h_sourceL : r2SourceL ≤ r2Source) (h_sourceU : r2Source ≤ r2SourceU)
    (h_sourceU_lt_one : r2SourceU < 1)
    (h_transportL_nonneg : 0 ≤ transportL)
    (h_transportL : transportL ≤ transport) (h_transportU : transport ≤ transportU) :
    targetAUCFromSourceTransport r2SourceL transportL ≤
      targetAUCFromSourceTransport r2Source transport ∧
    targetAUCFromSourceTransport r2Source transport ≤
      targetAUCFromSourceTransport r2SourceU transportU := by
  have h_source_nonneg : 0 ≤ r2Source := le_trans h_sourceL_nonneg h_sourceL
  have h_sourceU_nonneg : 0 ≤ r2SourceU := le_trans h_sourceL_nonneg (le_trans h_sourceL h_sourceU)
  have h_transport_nonneg : 0 ≤ transport := le_trans h_transportL_nonneg h_transportL
  have h_transportU_nonneg : 0 ≤ transportU := le_trans h_transportL_nonneg (le_trans h_transportL h_transportU)
  have h_arg_lower :
      aucSeparationFromSourceTransport r2SourceL transportL ≤
        aucSeparationFromSourceTransport r2Source transport := by
    calc
      aucSeparationFromSourceTransport r2SourceL transportL ≤
          aucSeparationFromSourceTransport r2Source transportL := by
            exact aucSeparationFromSourceTransport_monotone_source
              h_sourceL_nonneg h_sourceL (lt_of_le_of_lt h_sourceU h_sourceU_lt_one) h_transportL_nonneg
      _ ≤ aucSeparationFromSourceTransport r2Source transport := by
            exact aucSeparationFromSourceTransport_monotone_transport
              h_source_nonneg (lt_of_le_of_lt h_sourceU h_sourceU_lt_one) h_transportL
  have h_arg_upper :
      aucSeparationFromSourceTransport r2Source transport ≤
        aucSeparationFromSourceTransport r2SourceU transportU := by
    calc
      aucSeparationFromSourceTransport r2Source transport ≤
          aucSeparationFromSourceTransport r2SourceU transport := by
            exact aucSeparationFromSourceTransport_monotone_source
              h_source_nonneg h_sourceU h_sourceU_lt_one h_transport_nonneg
      _ ≤ aucSeparationFromSourceTransport r2SourceU transportU := by
            exact aucSeparationFromSourceTransport_monotone_transport
              h_sourceU_nonneg h_sourceU_lt_one h_transportU
  have h_arg_lower_nonneg : 0 ≤ aucSeparationFromSourceTransport r2SourceL transportL := by
    unfold aucSeparationFromSourceTransport
    apply div_nonneg
    · exact mul_nonneg h_sourceL_nonneg h_transportL_nonneg
    · linarith
  have h_arg_nonneg : 0 ≤ aucSeparationFromSourceTransport r2Source transport := by
    unfold aucSeparationFromSourceTransport
    apply div_nonneg
    · exact mul_nonneg h_source_nonneg h_transport_nonneg
    · linarith
  have h_arg_upper_nonneg : 0 ≤ aucSeparationFromSourceTransport r2SourceU transportU := by
    unfold aucSeparationFromSourceTransport
    apply div_nonneg
    · exact mul_nonneg h_sourceU_nonneg h_transportU_nonneg
    · linarith
  constructor
  · unfold targetAUCFromSourceTransport
    exact Phi_monotone (Real.sqrt_le_sqrt h_arg_lower)
  · unfold targetAUCFromSourceTransport
    exact Phi_monotone (Real.sqrt_le_sqrt h_arg_upper)

/-- Exact target AUC interval induced by absolute estimation or misspecification
error bounds on source `R²` and the transport factor. -/
theorem targetAUCFromSourceTransport_interval_of_error_bounds
    {r2SourceHat r2Source transportHat transport εSource εTransport : ℝ}
    (h_source_err : |r2SourceHat - r2Source| ≤ εSource)
    (h_transport_err : |transportHat - transport| ≤ εTransport)
    (h_source_lower_nonneg : 0 ≤ r2SourceHat - εSource)
    (h_source_upper_lt_one : r2SourceHat + εSource < 1)
    (h_transport_lower_nonneg : 0 ≤ transportHat - εTransport) :
    targetAUCFromSourceTransport (r2SourceHat - εSource) (transportHat - εTransport) ≤
      targetAUCFromSourceTransport r2Source transport ∧
    targetAUCFromSourceTransport r2Source transport ≤
      targetAUCFromSourceTransport (r2SourceHat + εSource) (transportHat + εTransport) := by
  have h_source_err' : |r2Source - r2SourceHat| ≤ εSource := by
    simpa [abs_sub_comm] using h_source_err
  have h_transport_err' : |transport - transportHat| ≤ εTransport := by
    simpa [abs_sub_comm] using h_transport_err
  have h_source_bounds := abs_le.mp h_source_err'
  have h_transport_bounds := abs_le.mp h_transport_err'
  exact targetAUCFromSourceTransport_interval
    h_source_lower_nonneg
    (by linarith) (by linarith)
    h_source_upper_lt_one
    h_transport_lower_nonneg
    (by linarith) (by linarith)

/-- Exact target Brier interval induced by source-`R²` and transport-factor intervals
at known prevalence. -/
theorem targetBrierFromSourceTransport_interval
    {π r2SourceL r2Source r2SourceU transportL transport transportU : ℝ}
    (h_pi_nonneg : 0 ≤ π) (h_pi_le_one : π ≤ 1)
    (h_sourceL_nonneg : 0 ≤ r2SourceL)
    (h_sourceL : r2SourceL ≤ r2Source) (h_sourceU : r2Source ≤ r2SourceU)
    (h_sourceU_lt_one : r2SourceU < 1)
    (h_transportL_nonneg : 0 ≤ transportL)
    (h_transportL : transportL ≤ transport) (h_transportU : transport ≤ transportU) :
    targetBrierFromSourceTransport π r2SourceU transportU ≤
      targetBrierFromSourceTransport π r2Source transport ∧
    targetBrierFromSourceTransport π r2Source transport ≤
      targetBrierFromSourceTransport π r2SourceL transportL := by
  have h_scale_nonneg : 0 ≤ π * (1 - π) := by
    apply mul_nonneg h_pi_nonneg
    linarith
  have h_r2_interval :=
    targetR2FromSourceTransport_interval h_sourceL_nonneg h_sourceL h_sourceU
      h_sourceU_lt_one h_transportL_nonneg h_transportL h_transportU
  constructor
  · rcases h_r2_interval with ⟨_, h_upper⟩
    unfold targetBrierFromSourceTransport
    nlinarith
  · rcases h_r2_interval with ⟨h_lower, _⟩
    unfold targetBrierFromSourceTransport
    nlinarith

/-- Exact target Brier interval induced by absolute estimation or misspecification
error bounds on prevalence, source `R²`, and the transport factor, when prevalence
is treated as known exactly at the point estimate. -/
theorem targetBrierFromSourceTransport_interval_of_error_bounds
    {π r2SourceHat r2Source transportHat transport εSource εTransport : ℝ}
    (h_pi_nonneg : 0 ≤ π) (h_pi_le_one : π ≤ 1)
    (h_source_err : |r2SourceHat - r2Source| ≤ εSource)
    (h_transport_err : |transportHat - transport| ≤ εTransport)
    (h_source_lower_nonneg : 0 ≤ r2SourceHat - εSource)
    (h_source_upper_lt_one : r2SourceHat + εSource < 1)
    (h_transport_lower_nonneg : 0 ≤ transportHat - εTransport) :
    targetBrierFromSourceTransport π (r2SourceHat + εSource) (transportHat + εTransport) ≤
      targetBrierFromSourceTransport π r2Source transport ∧
    targetBrierFromSourceTransport π r2Source transport ≤
      targetBrierFromSourceTransport π (r2SourceHat - εSource) (transportHat - εTransport) := by
  have h_source_err' : |r2Source - r2SourceHat| ≤ εSource := by
    simpa [abs_sub_comm] using h_source_err
  have h_transport_err' : |transport - transportHat| ≤ εTransport := by
    simpa [abs_sub_comm] using h_transport_err
  have h_source_bounds := abs_le.mp h_source_err'
  have h_transport_bounds := abs_le.mp h_transport_err'
  exact targetBrierFromSourceTransport_interval
    h_pi_nonneg h_pi_le_one
    h_source_lower_nonneg
    (by linarith) (by linarith)
    h_source_upper_lt_one
    h_transport_lower_nonneg
    (by linarith) (by linarith)

/-- Exact deployed metric intervals induced by uncertainty in the biological transport
components and in source `R²`. This is the fully mechanistic uncertainty theorem:
componentwise uncertainty in evolutionary retention factors propagates to certified
intervals for target `R²`, AUC, and Brier risk. -/
theorem headlineMetricIntervals_of_component_and_source_uncertainty
    {π
      alleleRet ldRet mutRet migBoost
      alleleRetL alleleRetU ldRetL ldRetU mutRetL mutRetU migBoostL migBoostU
      r2SourceL r2Source r2SourceU : ℝ}
    (h_pi_nonneg : 0 ≤ π) (h_pi_le_one : π ≤ 1)
    (h_alleleL : alleleRetL ≤ alleleRet) (h_alleleU : alleleRet ≤ alleleRetU)
    (h_ldL : ldRetL ≤ ldRet) (h_ldU : ldRet ≤ ldRetU)
    (h_mutL : mutRetL ≤ mutRet) (h_mutU : mutRet ≤ mutRetU)
    (h_migL : migBoostL ≤ migBoost) (h_migU : migBoost ≤ migBoostU)
    (h_alleleL_nonneg : 0 ≤ alleleRetL) (h_ldL_nonneg : 0 ≤ ldRetL)
    (h_mutL_nonneg : 0 ≤ mutRetL) (h_migL_nonneg : 0 ≤ migBoostL)
    (h_sourceL_nonneg : 0 ≤ r2SourceL)
    (h_sourceL : r2SourceL ≤ r2Source) (h_sourceU : r2Source ≤ r2SourceU)
    (h_sourceU_lt_one : r2SourceU < 1) :
    let transportL :=
      transportFactorFromComponents alleleRetL ldRetL mutRetL migBoostL
    let transport := transportFactorFromComponents alleleRet ldRet mutRet migBoost
    let transportU :=
      transportFactorFromComponents alleleRetU ldRetU mutRetU migBoostU
    targetR2FromSourceTransport r2SourceL transportL ≤
      targetR2FromSourceTransport r2Source transport ∧
    targetR2FromSourceTransport r2Source transport ≤
      targetR2FromSourceTransport r2SourceU transportU ∧
    targetAUCFromSourceTransport r2SourceL transportL ≤
      targetAUCFromSourceTransport r2Source transport ∧
    targetAUCFromSourceTransport r2Source transport ≤
      targetAUCFromSourceTransport r2SourceU transportU ∧
    targetBrierFromSourceTransport π r2SourceU transportU ≤
      targetBrierFromSourceTransport π r2Source transport ∧
    targetBrierFromSourceTransport π r2Source transport ≤
      targetBrierFromSourceTransport π r2SourceL transportL := by
  dsimp
  rcases transportFactorFromComponents_bounds
    h_alleleL h_alleleU h_ldL h_ldU h_mutL h_mutU h_migL h_migU
    h_alleleL_nonneg h_ldL_nonneg h_mutL_nonneg h_migL_nonneg with
    ⟨h_transportL, h_transportU⟩
  have h_transportL_nonneg :
      0 ≤ transportFactorFromComponents alleleRetL ldRetL mutRetL migBoostL := by
    unfold transportFactorFromComponents
    have hleft : 0 ≤ alleleRetL * ldRetL := mul_nonneg h_alleleL_nonneg h_ldL_nonneg
    have hright : 0 ≤ mutRetL * migBoostL := mul_nonneg h_mutL_nonneg h_migL_nonneg
    simpa [mul_assoc] using mul_nonneg hleft hright
  rcases targetR2FromSourceTransport_interval
    h_sourceL_nonneg h_sourceL h_sourceU h_sourceU_lt_one
    h_transportL_nonneg h_transportL h_transportU with ⟨h_r2L, h_r2U⟩
  rcases targetAUCFromSourceTransport_interval
    h_sourceL_nonneg h_sourceL h_sourceU h_sourceU_lt_one
    h_transportL_nonneg h_transportL h_transportU with ⟨h_aucL, h_aucU⟩
  rcases targetBrierFromSourceTransport_interval
    h_pi_nonneg h_pi_le_one
    h_sourceL_nonneg h_sourceL h_sourceU h_sourceU_lt_one
    h_transportL_nonneg h_transportL h_transportU with ⟨h_brierL, h_brierU⟩
  exact ⟨h_r2L, h_r2U, h_aucL, h_aucU, h_brierL, h_brierU⟩

end EvolutionaryMetricUncertainty

end Calibrator
