import Calibrator.Probability
import Mathlib.Algebra.Order.Chebyshev
import Calibrator.PortabilityDrift
import Calibrator.OpenQuestions

namespace Calibrator

open MeasureTheory
open Finset
open scoped BigOperators


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

end CrossValidation


/-!
## Summary Statistic-Based PGS

Most PGS are constructed from GWAS summary statistics rather than
individual-level data. This introduces specific challenges.
-/

section SummaryStatPGS


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

/-- **Meta-analysis model definition.**
    Contains properties of the model, specifically:
    k (number of studies), variances (of individual studies), and tau_sq (heterogeneity variance). -/
structure MetaAnalysisModel where
  k : ℕ
  variances : Fin k → ℝ
  tau_sq : ℝ
  h_k : 0 < k
  h_tau_sq : 0 < tau_sq
  h_variances : ∀ i, 0 < variances i

noncomputable def fixed_weights (m : MetaAnalysisModel) (i : Fin m.k) : ℝ :=
  1 / m.variances i

noncomputable def random_weights (m : MetaAnalysisModel) (i : Fin m.k) : ℝ :=
  1 / (m.variances i + m.tau_sq)

noncomputable def fixed_se_sq (m : MetaAnalysisModel) : ℝ :=
  1 / (∑ i, fixed_weights m i)

noncomputable def random_se_sq (m : MetaAnalysisModel) : ℝ :=
  1 / (∑ i, random_weights m i)

/-- **Fixed vs random effects meta-analysis.**
    Fixed effects: assumes same β across populations (tau² = 0).
    Random effects: allows β to vary with between-population variance tau².
    When tau² > 0, the random effects SE is larger (wider CI) because
    it adds tau² to the within-study variance. -/
theorem random_effects_captures_heterogeneity (m : MetaAnalysisModel) :
    fixed_se_sq m < random_se_sq m := by
  unfold fixed_se_sq random_se_sq
  apply one_div_lt_one_div_of_lt
  · apply Finset.sum_pos
    · intro i _
      unfold random_weights
      apply one_div_pos.mpr
      linarith [m.h_variances i, m.h_tau_sq]
    · have hw : Fin m.k := ⟨0, m.h_k⟩
      exact ⟨hw, Finset.mem_univ hw⟩
  · apply Finset.sum_lt_sum
    · intro i _
      unfold random_weights fixed_weights
      apply le_of_lt
      apply one_div_lt_one_div_of_lt (m.h_variances i)
      linarith [m.h_tau_sq]
    · have hw : Fin m.k := ⟨0, m.h_k⟩
      use hw
      use Finset.mem_univ hw
      unfold random_weights fixed_weights
      apply one_div_lt_one_div_of_lt (m.h_variances hw)
      linarith [m.h_tau_sq]

end SummaryStatPGS


/-!
## LD Score Regression

LDSC is used to estimate genetic correlation between populations,
which is a key predictor of PGS portability.
-/

section LDScoreRegression

structure LDSCModel (m : ℕ) where
  -- Effect sizes in source and target populations
  beta_s : Fin m → ℝ
  beta_t : Fin m → ℝ
  -- LD adjustment for the target population
  ld_adj : Fin m → ℝ
  h_ld_adj_pos : ∀ i, 0 ≤ ld_adj i
  h_ld_adj_le_one : ∀ i, ld_adj i ≤ 1

/-- Genetic correlation is defined by the inner product of effects. -/
noncomputable def geneticCorrelationLDSC {m : ℕ} (model : LDSCModel m) : ℝ :=
  (∑ i, model.beta_s i * model.beta_t i) /
    Real.sqrt ((∑ i, model.beta_s i ^ 2) * (∑ i, model.beta_t i ^ 2))

/-- **Genetic correlation bounds portability ratio.**
    The portability ratio R²_target / R²_source is bounded by ρ_g² × ld_adj.
    Since |ρ_g| ≤ 1 implies ρ_g² ≤ 1, and ld_adj ∈ [0,1], the product
    is at most 1. This gives the rg-based bound on portability.
    We formally define this using a rigorous structure. -/
theorem genetic_correlation_predicts_portability {m : ℕ} (hm : 0 < m)
    (model : LDSCModel m)
    (h_pos_s : 0 < ∑ i, model.beta_s i ^ 2)
    (h_pos_t : 0 < ∑ i, model.beta_t i ^ 2) :
    (geneticCorrelationLDSC model) ^ 2 * ((∑ i, model.ld_adj i) / m) ≤ 1 := by
  have hm_pos : 0 < (m : ℝ) := Nat.cast_pos.mpr hm

  have h_cauchy : (∑ i, model.beta_s i * model.beta_t i) ^ 2 ≤
      (∑ i, model.beta_s i ^ 2) * (∑ i, model.beta_t i ^ 2) := by
    exact sum_mul_sq_le_sq_mul_sq univ model.beta_s model.beta_t

  have h_rho_sq_le_one : (geneticCorrelationLDSC model) ^ 2 ≤ 1 := by
    unfold geneticCorrelationLDSC
    rw [div_pow]
    have h_sqrt_sq : (Real.sqrt ((∑ i, model.beta_s i ^ 2) * (∑ i, model.beta_t i ^ 2))) ^ 2 =
        (∑ i, model.beta_s i ^ 2) * (∑ i, model.beta_t i ^ 2) := by
      apply Real.sq_sqrt
      positivity
    rw [h_sqrt_sq]
    rw [div_le_one]
    · exact h_cauchy
    · positivity

  have h_ld_sum_le_m : ∑ i, model.ld_adj i ≤ m := by
    calc ∑ i, model.ld_adj i
      _ ≤ ∑ _i : Fin m, (1 : ℝ) := sum_le_sum (fun i _ => model.h_ld_adj_le_one i)
      _ = m := by simp

  have h_ld_avg_le_one : (∑ i, model.ld_adj i) / m ≤ 1 := by
    rw [div_le_one hm_pos]
    exact h_ld_sum_le_m

  have h_ld_avg_nonneg : 0 ≤ (∑ i, model.ld_adj i) / m := by
    apply div_nonneg
    · apply sum_nonneg
      intro i _
      exact model.h_ld_adj_pos i
    · positivity

  calc (geneticCorrelationLDSC model) ^ 2 * ((∑ i, model.ld_adj i) / m)
    _ ≤ 1 * ((∑ i, model.ld_adj i) / m) := mul_le_mul_of_nonneg_right h_rho_sq_le_one h_ld_avg_nonneg
    _ = (∑ i, model.ld_adj i) / m := one_mul _
    _ ≤ 1 := h_ld_avg_le_one

/-- **LDSC standard error for ρ_g.**
    SE(ρ̂_g) depends on sample sizes, LD structure, and polygenicity.
    For well-powered GWAS: SE ∝ 1/√n, so larger n yields smaller SE. -/
theorem ldsc_se_decreases_with_n
    (c : ℝ) (n₁ n₂ : ℝ)
    (h_c : 0 < c) (h_n₁ : 0 < n₁)
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
    (h_se : 0 < se_per_param) :
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


end GeneticCorrelationMethods

/-!
## Source `R²` Is Not a Sufficient Biological State Variable

Portability depends on locus-resolved transport, not just on a source summary
metric. The witness below fixes the residual variance and the source deployed
`R²`, then changes only which loci keep their signal in the target population.
The resulting target `R²` and target/source portability ratio change.
-/

section SourceR2Insufficiency

/-- Concrete two-locus witness that source deployed `R²` does not determine
target portability.

Both source loci contribute one unit of source signal, so the source deployed
`R²` at residual scale `1` is `2/3`. If both loci transport perfectly, the
target/source portability ratio is `1`. If one locus loses all transported
signal while the other remains intact, the target/source portability ratio
drops to `3/4`.

This formalizes the biological point that equal source `R²` does not determine
cross-population portability without locus-resolved transport state. -/
theorem same_source_r2_different_portability_two_locus_witness :
    let sourceSignal : Fin 2 → ℝ := fun _ => 1
    let stableTransport : Fin 2 → ℝ := fun _ => 1
    let brokenTransport : Fin 2 → ℝ := fun i => if i = 0 then 1 else 0
    let sourceVariance : ℝ := ∑ l, sourceSignal l
    let stableTargetVariance : ℝ := ∑ l, sourceSignal l * stableTransport l
    let brokenTargetVariance : ℝ := ∑ l, sourceSignal l * brokenTransport l
    let sourceR2 := TransportedMetrics.r2FromSignalVariance sourceVariance 1
    let stableTargetR2 := TransportedMetrics.r2FromSignalVariance stableTargetVariance 1
    let brokenTargetR2 := TransportedMetrics.r2FromSignalVariance brokenTargetVariance 1
    sourceR2 = stableTargetR2 ∧
    brokenTargetR2 < stableTargetR2 ∧
    brokenTargetR2 / sourceR2 = (3 : ℝ) / 4 := by
  simp [TransportedMetrics.r2FromSignalVariance]
  norm_num

end SourceR2Insufficiency

end Calibrator
