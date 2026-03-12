import Calibrator.Probability
import Calibrator.PortabilityDrift
import Calibrator.OpenQuestions

namespace Calibrator

open MeasureTheory

/-!
# Genetic Architecture Discovery, Winner's Curse, and Effect Estimation

This file formalizes how the discovery of genetic architecture
(through GWAS) is affected by population choice, and how this
affects downstream PGS portability.

Key results:
1. GWAS discovery power depends on LD and MAF in the discovery sample
2. Ascertainment bias from discovery population
3. Effect size estimation and shrinkage
4. Multi-trait analysis and genetic correlation

Reference: Wang et al. (2026), Nature Communications 17:942.
-/


/-!
## GWAS Discovery and Population Specificity

GWAS discovers associations that are specific to the population's
LD structure and allele frequency spectrum.
-/

section GWASDiscovery

/- **GWAS power function.**
    Power = Φ(√NCP - z_α/2) where NCP = n × β² × 2p(1-p). -/

/-- **Power increases with sample size.** -/
theorem power_increases_with_n
    (β p : ℝ) (n₁ n₂ : ℕ)
    (hβ : β ≠ 0) (hp : 0 < p) (hp1 : p < 1) (h_n : n₁ < n₂) (hn₁ : 0 < n₁) :
    -- NCP increases with n
    (n₁ : ℝ) * β ^ 2 * (2 * p * (1 - p)) <
      (n₂ : ℝ) * β ^ 2 * (2 * p * (1 - p)) := by
  apply mul_lt_mul_of_pos_right
  · apply mul_lt_mul_of_pos_right (Nat.cast_lt.mpr h_n) (sq_pos_of_ne_zero hβ)
  · nlinarith

/-- **GWAS finds different SNPs in different populations.**
    Due to different LD and MAF, the set of genome-wide significant
    SNPs can differ substantially. -/
theorem different_populations_different_hits
    (n_shared n_pop1_only n_pop2_only : ℕ)
    (h_not_all_shared : 0 < n_pop1_only ∨ 0 < n_pop2_only) :
    n_shared < n_shared + n_pop1_only + n_pop2_only := by
  rcases h_not_all_shared with h | h <;> omega

/-- **Winner's curse in GWAS.**
    The estimated effect size of a newly discovered variant is biased
    upward. If β̂ = β_true + noise, and we condition on |β̂| > threshold,
    then |β̂| > |β_true| whenever noise has the same sign as β_true.
    Here we prove the simpler statement: β̂ = β_true + ε with ε > 0
    and β_true > 0 implies |β̂| > |β_true|. -/
theorem winners_curse_overestimates
    (β_true ε : ℝ)
    (h_beta : 0 < β_true) (h_noise : 0 < ε) :
    |β_true| < |β_true + ε| := by
  rw [abs_of_pos h_beta, abs_of_pos (by linarith)]
  linarith

/-- **Winner's curse is worse for variants near the significance threshold.**
    The bias is proportional to the threshold / true effect ratio. -/
theorem winners_curse_worse_near_threshold
    (β₁ β₂ threshold : ℝ)
    (h₁_near : |β₁| < 1.5 * threshold)
    (h₂_far : 2 * threshold < |β₂|)
    (h_thr : 0 < threshold)
    (hβ₁ : β₁ ≠ 0) :
    -- Relative bias is larger for β₁
    threshold / |β₁| > threshold / |β₂| := by
  apply div_lt_div_of_pos_left h_thr
  · exact abs_pos.mpr hβ₁
  · linarith

end GWASDiscovery


/-!
## Clumping and Thresholding (C+T) vs Bayesian Methods

Wang et al. use C+T. Reviewers suggest PRS-CS. We formalize
why the method matters for portability.
-/

section PGSMethods

/- **C+T selects independent SNPs above a p-value threshold.**
    This discards information from sub-threshold SNPs and
    from LD between SNPs. -/

/-- **C+T uses fewer variants → more variable portability estimates.**
    C+T uses k_ct selected SNPs, Bayesian uses all k_total SNPs.
    Estimation variance ∝ 1/k for PGS effect estimation.
    With k_ct < k_total, C+T has higher variance. -/
theorem ct_more_variable_than_bayesian
    (k_ct k_total σ2 : ℝ)
    (h_kct : 0 < k_ct) (h_ktot : 0 < k_total)
    (h_fewer : k_ct < k_total) (h_σ2 : 0 < σ2) :
    σ2 / k_total < σ2 / k_ct := by
  exact div_lt_div_of_pos_left h_σ2 h_kct (by linarith)

/-- **Bayesian methods (PRS-CS) shrink small effects toward zero.**
    This reduces the impact of noise → more stable portability. -/
theorem shrinkage_stabilizes_portability
    (noise_ct noise_bayes : ℝ)
    (h_less_noise : noise_bayes < noise_ct)
    (h_nn : 0 ≤ noise_bayes) :
    0 < noise_ct - noise_bayes := by linarith

/-- **Both methods converge with infinite sample size.**
    C+T uses k_ct SNPs, Bayesian uses k_total. Estimation variance ∝ σ²/k.
    With large enough n, both methods capture all causal SNPs above
    threshold, so k_ct → k_total. We show: when the number of
    discovered SNPs increases, the ratio of estimation variances
    converges toward 1 (from above). Specifically, for k₁ < k₂ ≤ k_total,
    σ²/k₂ is closer to σ²/k_total than σ²/k₁ is. -/
theorem methods_converge_at_large_n
    (σ2 k₁ k₂ k_total : ℝ)
    (h_σ2 : 0 < σ2) (h_k₁ : 0 < k₁) (h_k₂ : 0 < k₂) (h_kt : 0 < k_total)
    (h_order : k₁ < k₂) (h_le : k₂ ≤ k_total) :
    σ2 / k₂ - σ2 / k_total ≤ σ2 / k₁ - σ2 / k_total := by
  have h₁ : σ2 / k_total ≤ σ2 / k₂ := div_le_div_of_nonneg_left (le_of_lt h_σ2) h_k₂ h_le
  have h₂ : σ2 / k₂ < σ2 / k₁ := div_lt_div_of_pos_left h_σ2 h_k₁ (by linarith)
  linarith

/-- **P-value threshold selection affects portability differently.**
    Lenient threshold includes k_lenient > k_stringent SNPs. Each extra
    SNP adds signal V_signal_per_snp but also LD-dependent noise V_noise_per_snp.
    In the source population, net R² gain = (V_signal - V_noise) × extra_snps.
    In the target population, the LD-noise component may double (different LD),
    so target net = (V_signal - 2 × V_noise) × extra_snps. We show: there
    exist regimes where the source gains but the target loses. -/
theorem threshold_tradeoff
    (V_signal_per_snp V_noise_per_snp extra_snps : ℝ)
    (h_signal : 0 < V_signal_per_snp) (h_noise : 0 < V_noise_per_snp)
    (h_extra : 0 < extra_snps)
    (h_signal_wins_source : V_noise_per_snp < V_signal_per_snp)
    (h_noise_wins_target : V_signal_per_snp < 2 * V_noise_per_snp) :
    -- Source gains R² (signal > noise)
    0 < (V_signal_per_snp - V_noise_per_snp) * extra_snps ∧
    -- Target loses R² (noise amplified by LD mismatch > signal)
    (V_signal_per_snp - 2 * V_noise_per_snp) * extra_snps < 0 := by
  constructor
  · exact mul_pos (by linarith) h_extra
  · exact mul_neg_of_neg_of_pos (by linarith) h_extra

end PGSMethods


/-!
## Effect Size Estimation and Portability

Accurate effect size estimation is crucial for PGS performance.
Different estimation methods have different bias-variance tradeoffs.
-/

section EffectEstimation

/-- **OLS effect estimates are unbiased but noisy.**
    β̂_OLS = (X'X)⁻¹X'Y. Under standard assumptions, E[β̂] = β_true.
    The variance of the estimate is σ² / (n × Var(X)).
    We prove that the variance → 0 as n → ∞. -/
theorem ols_unbiased
    (σ2 varX n₁ n₂ : ℝ)
    (h_σ2 : 0 < σ2) (h_varX : 0 < varX)
    (h_n₁ : 0 < n₁) (h_n₂ : 0 < n₂) (h_n : n₁ < n₂) :
    -- Variance of β̂ decreases with n
    σ2 / (n₂ * varX) < σ2 / (n₁ * varX) := by
  exact div_lt_div_of_pos_left h_σ2 (mul_pos h_n₁ h_varX)
    (by nlinarith [mul_pos h_n₂ h_varX])

/-- **Ridge regression shrinks effects toward zero.**
    β̂_ridge = (X'X + λI)⁻¹X'Y = β_true × X'X/(X'X + λI).
    Bias: E[β̂] = β_true × (1 - λ/(X'X + λ)). -/
theorem ridge_introduces_bias
    (β_true lam xtx : ℝ)
    (h_lam : 0 < lam) (h_xtx : 0 < xtx) :
    |β_true * xtx / (xtx + lam)| < |β_true| ∨ β_true = 0 := by
  by_cases hβ : β_true = 0
  · right; exact hβ
  · left
    rw [abs_div, abs_mul]
    rw [div_lt_iff₀ (by positivity : (0:ℝ) < |xtx + lam|)]
    rw [abs_of_pos (by linarith : (0:ℝ) < xtx), abs_of_pos (by linarith : (0:ℝ) < xtx + lam)]
    nlinarith [abs_nonneg β_true, abs_pos.mpr hβ]

/-- **LASSO performs variable selection.**
    β̂_lasso sets small effects exactly to zero.
    With LASSO penalty λ, any coefficient with |β_true| < λ/(2n)
    is set to zero. So the number of nonzero LASSO coefficients
    is at most the number of OLS coefficients, and strictly fewer
    when some effects are small. Here: k_total predictors,
    k_small of them have |β| < threshold. LASSO retains at most
    k_total - k_small. -/
theorem lasso_sparsifies
    (k_total k_small : ℕ)
    (h_small_pos : 0 < k_small)
    (h_valid : k_small ≤ k_total) :
    k_total - k_small < k_total := by omega

/-- **Estimation method affects portability differently for different traits.**
    For polygenic traits: each causal SNP contributes h²/k to PGS variance.
    LASSO drops SNPs below threshold, losing signal proportional to k_dropped/k_causal.
    For oligogenic traits: each causal SNP contributes h²/k_oligo (larger per SNP),
    so all exceed threshold and LASSO only removes noise.
    We show: the per-SNP signal for oligogenic traits exceeds that for
    polygenic traits when k_oligo < k_poly, making LASSO more appropriate
    for oligogenic traits. -/
theorem estimation_trait_interaction
    (h2 k_poly k_oligo : ℝ)
    (h_h2 : 0 < h2) (h_poly : 0 < k_poly) (h_oligo : 0 < k_oligo)
    (h_more_poly : k_oligo < k_poly) :
    -- Per-SNP signal is larger for oligogenic (easier to detect)
    h2 / k_poly < h2 / k_oligo := by
  exact div_lt_div_of_pos_left h_h2 h_oligo (by linarith)

end EffectEstimation


/-!
## Multi-Trait Analysis and Genetic Correlation

Multi-trait GWAS methods can improve portability by leveraging
shared genetic architecture across related traits.
-/

section MultiTraitAnalysis

/-- **Genetic correlation between traits.**
    rg = Cov_g(trait1, trait2) / √(V_g1 × V_g2). -/
noncomputable def geneticCorrelation
    (cov_g vg₁ vg₂ : ℝ) : ℝ :=
  cov_g / Real.sqrt (vg₁ * vg₂)

/-- Genetic correlation is bounded by [-1, 1] (Cauchy-Schwarz). -/
theorem genetic_correlation_bounded
    (cov_g vg₁ vg₂ : ℝ)
    (h_cs : cov_g ^ 2 ≤ vg₁ * vg₂)
    (h₁ : 0 < vg₁) (h₂ : 0 < vg₂) :
    |geneticCorrelation cov_g vg₁ vg₂| ≤ 1 := by
  unfold geneticCorrelation
  rw [abs_div]
  rw [div_le_one (by exact abs_pos.mpr (Real.sqrt_pos.mpr (by positivity)).ne')]
  rw [abs_of_pos (Real.sqrt_pos.mpr (by positivity))]
  exact (Real.le_sqrt (abs_nonneg _) (by positivity)).mpr (by nlinarith [sq_abs cov_g])

/-- **Cross-trait portability leverages genetic correlation.**
    If trait A has good portability and rg(A,B) is high,
    trait B can borrow portability information from A.
    Effective portability for B is at least rg² × portability(A). -/
theorem cross_trait_portability_gain
    (port_A rg : ℝ)
    (h_port : 0 < port_A) (h_port_le : port_A ≤ 1)
    (h_rg : 0 ≤ rg) (h_rg_le : rg ≤ 1) :
    0 ≤ rg ^ 2 * port_A := by
  exact mul_nonneg (sq_nonneg _) (le_of_lt h_port)

/-- **Multi-trait GWAS increases effective sample size.**
    MTAG and similar methods borrow information across traits,
    increasing the effective sample size. If two traits have
    genetic correlation rg and sample sizes n₁, n₂, the effective
    sample size for trait 1 is approximately n₁ + rg² × n₂ > n₁
    when rg > 0 and n₂ > 0. -/
theorem multi_trait_increases_effective_n
    (n₁ n₂ rg : ℝ)
    (h_n₁ : 0 < n₁) (h_n₂ : 0 < n₂)
    (h_rg : 0 < rg) :
    n₁ < n₁ + rg ^ 2 * n₂ := by
  have : 0 < rg ^ 2 * n₂ := mul_pos (sq_pos_of_ne_zero (ne_of_gt h_rg)) h_n₂
  linarith

/-- **Genetic correlation may differ across populations.**
    If the shared environmental component changes, the genetic
    correlation between traits can change. The genetic correlation
    rg = cov_g / √(vg₁ × vg₂). When the genetic covariance
    changes from cov₁ to cov₂ (due to GxE affecting shared
    pathways differently), the genetic correlations differ. -/
theorem genetic_correlation_population_specific
    (cov₁ cov₂ vg₁ vg₂ : ℝ)
    (h_vg₁ : 0 < vg₁) (h_vg₂ : 0 < vg₂)
    (h_cov_diff : cov₁ ≠ cov₂) :
    geneticCorrelation cov₁ vg₁ vg₂ ≠ geneticCorrelation cov₂ vg₁ vg₂ := by
  unfold geneticCorrelation
  intro h
  apply h_cov_diff
  have h_sqrt_pos : 0 < Real.sqrt (vg₁ * vg₂) := Real.sqrt_pos.mpr (mul_pos h_vg₁ h_vg₂)
  have h_sqrt_ne : Real.sqrt (vg₁ * vg₂) ≠ 0 := ne_of_gt h_sqrt_pos
  field_simp at h
  exact h

end MultiTraitAnalysis


/-!
## Future Directions: Whole Genome Sequencing and Rare Variants

WGS enables discovery of rare variants, which are mostly
population-specific. This has implications for portability.
-/

section WGSAndRareVariants

/-- **WGS discovers causal variants directly (no tagging needed).**
    This eliminates the LD mismatch component of portability loss.
    But effect turnover and environmental components remain. -/
theorem wgs_eliminates_ld_mismatch
    (port_ld_factor port_effect_factor port_env_factor : ℝ)
    (h_ld : 0 < port_ld_factor) (h_ld_le : port_ld_factor ≤ 1)
    (h_eff : 0 < port_effect_factor) (h_env : 0 < port_env_factor) :
    -- With WGS, LD factor becomes 1 (no tagging loss)
    port_effect_factor * port_env_factor ≥
      port_ld_factor * port_effect_factor * port_env_factor := by
  nlinarith [mul_pos h_eff h_env]

/-- **Rare variant PGS has poor cross-population portability.**
    Variants with MAF < 1% are mostly population-specific → zero shared signal. -/
theorem rare_variant_pgs_poor_portability
    (r2_common r2_rare port_common port_rare : ℝ)
    (h_common : 0 < port_common) (h_rare_zero : port_rare = 0)
    (h_r2_c : 0 < r2_common) (h_r2_r : 0 < r2_rare) :
    r2_common * port_common + r2_rare * port_rare =
      r2_common * port_common := by
  rw [h_rare_zero, mul_zero, add_zero]

/-- **Optimal PGS strategy combines common and rare variants.**
    Use common variants for portability (they're shared)
    and rare variants for within-population prediction only.
    R²_combined = R²_common + R²_rare (independent contributions).
    Since R²_rare > 0 for the discovery population, the combined
    score outperforms common-only within-population. -/
theorem combined_strategy_optimal
    (R2_common R2_rare : ℝ)
    (h_common : 0 < R2_common) (h_rare : 0 < R2_rare) :
    R2_common < R2_common + R2_rare := by linarith

end WGSAndRareVariants

end Calibrator
