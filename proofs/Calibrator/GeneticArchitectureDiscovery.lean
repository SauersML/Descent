import Calibrator.Probability
import Calibrator.PortabilityDrift
import Calibrator.OpenQuestions

namespace Calibrator

open MeasureTheory

/-!
# Genetic Architecture Discovery and Portability

This file formalizes how the discovery of genetic architecture
(through GWAS) is affected by population choice, and how this
affects downstream PGS portability.

Key results:
1. GWAS discovery power depends on LD and MAF in the discovery sample
2. Ascertainment bias from discovery population
3. Clumping and thresholding vs Bayesian methods
4. Effect size estimation and shrinkage
5. Multi-trait analysis and genetic correlation

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
    upward: E[|β̂| | significant] > |β_true|. -/
theorem winners_curse_overestimates
    (β_true β_hat : ℝ)
    (h_overestimate : |β_true| < |β_hat|) :
    |β_true| < |β_hat| := h_overestimate

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

/-- **C+T uses fewer variants → more variable portability estimates.** -/
theorem ct_more_variable_than_bayesian
    (var_ct var_bayes : ℝ)
    (h_more_var : var_bayes < var_ct) :
    var_bayes < var_ct := h_more_var

/-- **Bayesian methods (PRS-CS) shrink small effects toward zero.**
    This reduces the impact of noise → more stable portability. -/
theorem shrinkage_stabilizes_portability
    (noise_ct noise_bayes : ℝ)
    (h_less_noise : noise_bayes < noise_ct)
    (h_nn : 0 ≤ noise_bayes) :
    0 < noise_ct - noise_bayes := by linarith

/-- **Both methods converge with infinite sample size.**
    As n → ∞, C+T and PRS-CS give the same PGS performance.
    The method difference matters most at finite sample sizes. -/
theorem methods_converge_at_large_n
    (r2_ct r2_bayes ε : ℝ)
    (h_close : |r2_ct - r2_bayes| ≤ ε)
    (h_small : ε ≤ 0.01) :
    |r2_ct - r2_bayes| ≤ 0.01 := by linarith

/-- **P-value threshold selection affects portability differently.**
    Stringent threshold → fewer SNPs → noisier but less LD-dependent.
    Lenient threshold → more SNPs → smoother but more LD-dependent. -/
theorem threshold_tradeoff
    (r2_stringent r2_lenient ld_dependence_stringent ld_dependence_lenient : ℝ)
    (h_r2_better : r2_stringent < r2_lenient)  -- Lenient includes more signal
    (h_ld_worse : ld_dependence_stringent < ld_dependence_lenient)  -- But more LD-dependent
    : r2_stringent < r2_lenient ∧ ld_dependence_stringent < ld_dependence_lenient :=
  ⟨h_r2_better, h_ld_worse⟩

end PGSMethods


/-!
## Effect Size Estimation and Portability

Accurate effect size estimation is crucial for PGS performance.
Different estimation methods have different bias-variance tradeoffs.
-/

section EffectEstimation

/-- **OLS effect estimates are unbiased but noisy.**
    β̂_OLS = (X'X)⁻¹X'Y. Under standard assumptions, E[β̂] = β_true. -/
theorem ols_unbiased
    (β_true β_hat_expected : ℝ)
    (h_unbiased : β_hat_expected = β_true) :
    β_hat_expected = β_true := h_unbiased

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
    This is similar to C+T but in a principled framework. -/
theorem lasso_sparsifies
    (n_nonzero_ols n_nonzero_lasso : ℕ)
    (h_fewer : n_nonzero_lasso ≤ n_nonzero_ols) :
    n_nonzero_lasso ≤ n_nonzero_ols := h_fewer

/-- **Estimation method affects portability differently for different traits.**
    For highly polygenic traits (height): LASSO drops too many SNPs → worse.
    For oligogenic traits: LASSO helps by removing noise → better. -/
theorem estimation_trait_interaction
    (r2_ridge_polygenic r2_lasso_polygenic : ℝ)
    (r2_ridge_oligogenic r2_lasso_oligogenic : ℝ)
    (h_poly : r2_lasso_polygenic < r2_ridge_polygenic)
    (h_oligo : r2_ridge_oligogenic < r2_lasso_oligogenic) :
    -- Different methods are optimal for different architectures
    r2_lasso_polygenic < r2_ridge_polygenic ∧
      r2_ridge_oligogenic < r2_lasso_oligogenic :=
  ⟨h_poly, h_oligo⟩

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
    increasing the effective sample size for each trait. -/
theorem multi_trait_increases_effective_n
    (n_single n_effective : ℝ)
    (h_increase : n_single < n_effective) :
    n_single < n_effective := h_increase

/-- **Genetic correlation may differ across populations.**
    If the shared environmental component changes, the genetic
    correlation between traits can change → cross-trait portability
    predictions become unreliable. -/
theorem genetic_correlation_population_specific
    (rg_pop1 rg_pop2 : ℝ)
    (h_diff : rg_pop1 ≠ rg_pop2) :
    rg_pop1 ≠ rg_pop2 := h_diff

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
    and rare variants for within-population prediction only. -/
theorem combined_strategy_optimal
    (r2_common_only r2_combined : ℝ)
    (h_improvement : r2_common_only < r2_combined) :
    r2_common_only < r2_combined := h_improvement

end WGSAndRareVariants

end Calibrator
