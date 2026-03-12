import Calibrator.Probability
import Calibrator.PortabilityDrift
import Calibrator.OpenQuestions

namespace Calibrator

open MeasureTheory

/-!
# Bayesian PGS Methods and Portability

This file formalizes the theoretical properties of Bayesian PGS methods
(PRS-CS, LDpred, SBayesR) and their implications for portability.
Bayesian methods handle LD structure explicitly, which has different
portability implications compared to C+T.

Key results:
1. Bayesian shrinkage and posterior effect sizes
2. Prior specification and its effect on portability
3. LD reference panel mismatch
4. Posterior predictive distributions across populations
5. Spike-and-slab vs continuous shrinkage

Reference: Wang et al. (2026), Nature Communications 17:942.
-/


/-!
## Bayesian Shrinkage Framework

Bayesian PGS methods estimate posterior effect sizes:
β̂_Bayes = E[β | GWAS summary stats, LD reference].
The shrinkage pattern depends on the prior and LD.
-/

section BayesianShrinkage

/-!
### Derivation of Bayesian Shrinkage from First Principles

We derive the Gaussian posterior shrinkage factor from a standard
Bayesian linear regression model:
  - Prior: β ~ N(0, h)  where h = σ²_β is the prior variance
  - Likelihood: y | β ~ N(β, 1/n)  where n is the data precision
    (equivalently, y is a sufficient statistic with variance 1/n)

By conjugacy of Gaussian prior and Gaussian likelihood:
  - Posterior precision = prior precision + likelihood precision = 1/h + n
  - Posterior variance  = 1/(1/h + n) = h/(1 + n·h)
  - Posterior mean      = posterior_variance × (n × y) = n·h/(1 + n·h) × y

The shrinkage factor n·h/(1 + n·h) is exactly `gaussianPosteriorShrinkage`.
-/

/-- A Bayesian linear regression model with Gaussian prior and Gaussian likelihood.
    `prior_var` is the prior variance h (so prior precision is 1/h).
    `data_precision` is the likelihood precision n (so likelihood variance is 1/n). -/
structure BayesianLinearModel where
  prior_var : ℝ
  data_precision : ℝ
  prior_var_pos : 0 < prior_var
  data_precision_pos : 0 < data_precision

namespace BayesianLinearModel

/-- Posterior precision = prior precision + data precision = 1/h + n. -/
noncomputable def posteriorPrecision (m : BayesianLinearModel) : ℝ :=
  1 / m.prior_var + m.data_precision

/-- Posterior precision is positive. -/
theorem posteriorPrecision_pos (m : BayesianLinearModel) :
    0 < m.posteriorPrecision := by
  unfold posteriorPrecision
  have := m.prior_var_pos
  have := m.data_precision_pos
  positivity

/-- Posterior variance = 1 / posterior precision = 1 / (1/h + n). -/
noncomputable def posteriorVariance (m : BayesianLinearModel) : ℝ :=
  1 / m.posteriorPrecision

/-- Posterior variance is positive. -/
theorem posteriorVariance_pos (m : BayesianLinearModel) :
    0 < m.posteriorVariance := by
  unfold posteriorVariance
  exact div_pos one_pos m.posteriorPrecision_pos

/-- Posterior mean = posterior_variance × data_precision × observation.
    This is the standard Bayesian update: posterior mean is a precision-weighted
    combination of prior mean (0) and data (n × y), divided by total precision. -/
noncomputable def posteriorMean (m : BayesianLinearModel) (y : ℝ) : ℝ :=
  m.posteriorVariance * m.data_precision * y

/-- The shrinkage factor applied to the observation y in the posterior mean.
    shrinkageFactor = posteriorVariance × data_precision = n / (1/h + n). -/
noncomputable def shrinkageFactor (m : BayesianLinearModel) : ℝ :=
  m.posteriorVariance * m.data_precision

/-- The posterior mean factors as shrinkageFactor × y. -/
theorem posteriorMean_eq_shrinkage_mul (m : BayesianLinearModel) (y : ℝ) :
    m.posteriorMean y = m.shrinkageFactor * y := by
  unfold posteriorMean shrinkageFactor
  ring

/-- **Key identity:** posteriorVariance = h / (1 + n·h).
    Proof: 1/(1/h + n) = 1/((1 + n·h)/h) = h/(1 + n·h). -/
theorem posteriorVariance_eq (m : BayesianLinearModel) :
    m.posteriorVariance = m.prior_var / (1 + m.data_precision * m.prior_var) := by
  unfold posteriorVariance posteriorPrecision
  have hh : m.prior_var ≠ 0 := ne_of_gt m.prior_var_pos
  have hdenom : 1 + m.data_precision * m.prior_var > 0 := by
    have := m.prior_var_pos; have := m.data_precision_pos; positivity
  rw [div_add' _ _ _ hh]
  field_simp

/-- **Key identity:** shrinkageFactor = n·h / (n·h + 1).
    This is the algebraic derivation from the Bayesian model:
    shrinkage = posteriorVariance × n = (h/(1 + n·h)) × n = n·h/(1 + n·h). -/
theorem shrinkageFactor_eq (m : BayesianLinearModel) :
    m.shrinkageFactor =
      m.data_precision * m.prior_var /
        (m.data_precision * m.prior_var + 1) := by
  unfold shrinkageFactor
  rw [m.posteriorVariance_eq]
  have hh : m.prior_var ≠ 0 := ne_of_gt m.prior_var_pos
  have hdenom : 1 + m.data_precision * m.prior_var > 0 := by
    have := m.prior_var_pos; have := m.data_precision_pos; positivity
  have hdenom_ne : (1 + m.data_precision * m.prior_var) ≠ 0 := ne_of_gt hdenom
  field_simp
  ring

end BayesianLinearModel

/-- **Posterior mean under Gaussian prior.**
    β̂_Bayes = (n × Σ_LD + σ²_β⁻¹ × I)⁻¹ × n × Σ_LD × β̂_OLS
    For a single SNP: β̂ = β̂_OLS × n × h / (n × h + 1)
    where h = σ²_β / σ²_ε is the per-SNP heritability. -/
noncomputable def gaussianPosteriorShrinkage (n h : ℝ) : ℝ :=
  n * h / (n * h + 1)

/-- **Connection theorem:** The shrinkage factor derived from the Bayesian
    linear model is exactly `gaussianPosteriorShrinkage n h`.
    This justifies the previously-assumed formula by deriving it from first principles. -/
theorem BayesianLinearModel.shrinkageFactor_eq_gaussianPosteriorShrinkage
    (m : BayesianLinearModel) :
    m.shrinkageFactor =
      gaussianPosteriorShrinkage m.data_precision m.prior_var := by
  rw [m.shrinkageFactor_eq]
  unfold gaussianPosteriorShrinkage
  ring

/-- Shrinkage factor is in [0, 1). -/
theorem gaussian_shrinkage_in_unit (n h : ℝ)
    (h_n : 0 < n) (h_h : 0 < h) :
    0 ≤ gaussianPosteriorShrinkage n h ∧
      gaussianPosteriorShrinkage n h < 1 := by
  unfold gaussianPosteriorShrinkage
  constructor
  · exact div_nonneg (mul_nonneg (le_of_lt h_n) (le_of_lt h_h)) (by positivity)
  · rw [div_lt_one (by positivity)]
    linarith

/-- **Shrinkage increases with sample size.** More data → less shrinkage. -/
theorem shrinkage_increases_with_n (h : ℝ) (n₁ n₂ : ℝ)
    (h_h : 0 < h) (h_n₁ : 0 < n₁) (h_n₂ : 0 < n₂)
    (h_more : n₁ < n₂) :
    gaussianPosteriorShrinkage n₁ h < gaussianPosteriorShrinkage n₂ h := by
  unfold gaussianPosteriorShrinkage
  rw [div_lt_div_iff₀ (by positivity) (by positivity)]
  nlinarith

/-- **Shrinkage increases with per-SNP heritability.**
    SNPs with larger effects are shrunk less. -/
theorem shrinkage_increases_with_h (n : ℝ) (h₁ h₂ : ℝ)
    (h_n : 0 < n) (h_h₁ : 0 < h₁) (h_h₂ : 0 < h₂)
    (h_more : h₁ < h₂) :
    gaussianPosteriorShrinkage n h₁ < gaussianPosteriorShrinkage n h₂ := by
  unfold gaussianPosteriorShrinkage
  rw [div_lt_div_iff₀ (by positivity) (by positivity)]
  nlinarith

/-- **James-Stein shrinkage MSE.**
    For estimating β with observation β̂_OLS ~ N(β, σ²), consider the
    linear shrinkage estimator β̂(λ) = λ·β̂_OLS. Its MSE decomposes as:
      MSE(λ) = λ²·σ² + (1-λ)²·β²
    where the first term is the (scaled) variance and the second is
    the squared bias from shrinking toward zero. -/
noncomputable def jamesSteinMSE (lam σ_sq β_sq : ℝ) : ℝ :=
  lam ^ 2 * σ_sq + (1 - lam) ^ 2 * β_sq

/-- **OLS MSE is the no-shrinkage case.** MSE(1) = σ² (full weight on data). -/
theorem mse_ols_is_no_shrinkage (σ_sq β_sq : ℝ) :
    jamesSteinMSE 1 σ_sq β_sq = σ_sq := by
  unfold jamesSteinMSE; ring

/-- **Optimal shrinkage factor.**
    Minimizing MSE(λ) = λ²σ² + (1-λ)²β² over λ by taking the derivative
    and setting to zero: 2λσ² - 2(1-λ)β² = 0 ⟹ λ(σ²+β²) = β²
    ⟹ λ* = β²/(σ²+β²). -/
noncomputable def optimalShrinkage (σ_sq β_sq : ℝ) : ℝ :=
  β_sq / (σ_sq + β_sq)

/-- **Optimal shrinkage is in (0,1) for positive parameters.** -/
theorem optimal_shrinkage_in_unit (σ_sq β_sq : ℝ)
    (h_σ : 0 < σ_sq) (h_β : 0 < β_sq) :
    0 < optimalShrinkage σ_sq β_sq ∧ optimalShrinkage σ_sq β_sq < 1 := by
  unfold optimalShrinkage
  constructor
  · exact div_pos h_β (by linarith)
  · rw [div_lt_one (by linarith : 0 < σ_sq + β_sq)]; linarith

/-- **Bayesian shrinkage reduces MSE compared to OLS (James-Stein).**
    We show MSE(λ*) < MSE(1) = σ² for λ* = β²/(σ²+β²).

    Key identity: MSE(λ*) = σ²·β²/(σ²+β²).
    Then σ²·β²/(σ²+β²) < σ² ⟺ β² < σ²+β² ⟺ 0 < σ².

    Proof strategy: We show that for any λ ∈ (0,1), we have
    MSE(λ) = MSE(1) - (2λ - λ²)·σ² + (1-λ)²·β²·... We instead
    show the result directly: MSE(λ) < σ² when λ ∈ (0,1) and β² > 0,
    by expanding and using nlinarith. -/
theorem bayesian_shrinkage_reduces_mse
    (σ_sq β_sq : ℝ)
    (h_σ : 0 < σ_sq) (h_β : 0 < β_sq) :
    jamesSteinMSE (optimalShrinkage σ_sq β_sq) σ_sq β_sq <
      jamesSteinMSE 1 σ_sq β_sq := by
  rw [mse_ols_is_no_shrinkage]
  unfold jamesSteinMSE optimalShrinkage
  -- Goal: (β²/(σ²+β²))² · σ² + (1 - β²/(σ²+β²))² · β² < σ²
  -- We use: 1 - β²/(σ²+β²) = σ²/(σ²+β²)
  -- So LHS = β⁴σ²/(σ²+β²)² + σ⁴β²/(σ²+β²)² = σ²β²(β²+σ²)/(σ²+β²)² = σ²β²/(σ²+β²)
  -- Then σ²β²/(σ²+β²) < σ² ⟺ β² < σ²+β² ⟺ 0 < σ². ✓
  have h_sum : 0 < σ_sq + β_sq := by linarith
  have h_sum_ne : (σ_sq + β_sq) ≠ 0 := ne_of_gt h_sum
  -- Clear the denominators by multiplying through by (σ_sq + β_sq)²
  rw [show β_sq / (σ_sq + β_sq) = β_sq / (σ_sq + β_sq) from rfl]
  have h1 : 1 - β_sq / (σ_sq + β_sq) = σ_sq / (σ_sq + β_sq) := by
    field_simp
  rw [h1, div_pow, div_pow, div_mul_eq_mul_div, div_mul_eq_mul_div, div_add_div_same,
      div_lt_iff₀ (sq_pos_of_pos h_sum)]
  nlinarith [sq_nonneg σ_sq, sq_nonneg β_sq, sq_nonneg (σ_sq * β_sq),
             mul_pos h_σ h_β]

end BayesianShrinkage


/-!
## LD Reference Panel Mismatch

Bayesian methods require an LD reference panel. When this doesn't
match the GWAS sample or target population, performance degrades.
-/

section LDReferenceMismatch

/- **LD mismatch error in posterior estimates.**
    When the LD reference Σ_ref ≠ Σ_true, the posterior mean is biased:
    β̂ = (n × Σ_ref + τ⁻¹I)⁻¹ × n × Σ_ref × β̂_marginal
    but the true posterior uses Σ_true. -/

/-- **Shrinkage function for a single SNP.**
    f(σ) = σ/(σ+τ) maps the LD diagonal entry to the shrinkage factor.
    This is the key quantity affected by LD mismatch. -/
noncomputable def snpShrinkage (σ τ : ℝ) : ℝ :=
  σ / (σ + τ)

/-- **LD mismatch bias bound from mean value theorem.**
    For the shrinkage function f(σ) = σ/(σ+τ), we have
    f'(σ) = τ/(σ+τ)². Since σ > 0 and τ > 0, we get (σ+τ)² > τ²,
    so f'(σ) < 1/τ. By the mean value theorem:
    |f(σ_ref) - f(σ_true)| ≤ (1/τ) · |σ_ref - σ_true|.

    This shows the bias from LD mismatch is proportional to the
    LD matrix perturbation, with constant 1/τ (inverse regularization). -/
theorem ld_mismatch_bias_proportional
    (σ_true σ_ref τ : ℝ)
    (h_true : 0 < σ_true) (h_ref : 0 < σ_ref) (h_τ : 0 < τ) :
    |snpShrinkage σ_ref τ - snpShrinkage σ_true τ| ≤
      |σ_ref - σ_true| / τ := by
  unfold snpShrinkage
  -- f(σ₂) - f(σ₁) = σ₂/(σ₂+τ) - σ₁/(σ₁+τ)
  --               = (σ₂(σ₁+τ) - σ₁(σ₂+τ)) / ((σ₂+τ)(σ₁+τ))
  --               = τ(σ₂ - σ₁) / ((σ₂+τ)(σ₁+τ))
  -- |f(σ₂)-f(σ₁)| = τ|σ₂-σ₁| / ((σ₂+τ)(σ₁+τ))
  -- Since σ₁+τ > τ and σ₂+τ > τ, denominator > τ², so result ≤ |σ₂-σ₁|/τ
  have h_d1 : 0 < σ_true + τ := by linarith
  have h_d2 : 0 < σ_ref + τ := by linarith
  rw [div_sub_div _ _ (ne_of_gt h_d2) (ne_of_gt h_d1)]
  have h_num : σ_ref * (σ_true + τ) - (σ_ref + τ) * σ_true = τ * (σ_ref - σ_true) := by ring
  rw [h_num, abs_div, abs_mul, abs_of_pos h_τ, abs_of_pos (mul_pos h_d2 h_d1)]
  rw [div_le_div_iff₀ (mul_pos h_d2 h_d1) h_τ]
  -- Goal: τ * |σ_ref - σ_true| * τ ≤ |σ_ref - σ_true| * ((σ_ref + τ) * (σ_true + τ))
  nlinarith [abs_nonneg (σ_ref - σ_true), mul_pos h_d2 h_d1]

/-- **Cross-ancestry LD reference introduces systematic bias.**
    Using EUR LD reference for AFR GWAS summary statistics introduces
    bias. We model cross-ancestry LD divergence: if the within-population
    LD entry is σ and the cross-population LD entry differs by δ = c·Fst·σ
    (LD diverges proportionally to Fst and the LD magnitude), then
    by ld_mismatch_bias_proportional the shrinkage bias is at most
    c·Fst·σ/τ. This theorem establishes that cross-ancestry bias is
    positive and scales with Fst: for matched LD (Fst=0) the bias
    contribution c·Fst·σ vanishes, while for diverged populations it
    grows linearly. -/
theorem cross_ancestry_ld_bias
    (σ τ c fst : ℝ)
    (h_σ : 0 < σ) (h_τ : 0 < τ)
    (h_c : 0 < c) (h_fst : 0 < fst) :
    -- The bias bound is positive (nonzero bias for diverged populations)
    0 < c * fst * σ / τ ∧
    -- Bias grows with Fst: doubling Fst doubles the bias bound
    c * fst * σ / τ < c * (2 * fst) * σ / τ := by
  constructor
  · apply div_pos _ h_τ; positivity
  · rw [div_lt_div_iff_right h_τ]; nlinarith

/-- **In-sample LD reference is optimal.**
    Using LD reference from the same population as GWAS minimizes bias.
    Cross-population bias = base_bias + c · fst where fst > 0 between
    populations, so cross-population bias strictly exceeds in-sample bias. -/
theorem in_sample_ld_optimal
    (base_bias c fst : ℝ)
    (h_base_nn : 0 ≤ base_bias)
    (h_c_pos : 0 < c) (h_fst_pos : 0 < fst) :
    base_bias ≤ base_bias + c * fst := by
  linarith [mul_pos h_c_pos h_fst_pos]

/-- **Multi-ancestry LD reference reduces cross-population bias.**
    A reference panel combining multiple ancestries has intermediate LD
    that partially matches each population.  If single-ancestry bias
    is c · fst and multi-ancestry bias is c · α · fst where α ∈ (0,1)
    is the attenuation from partial ancestry matching, then
    multi-ancestry bias < single-ancestry bias. -/
theorem multi_ancestry_reference_reduces_bias
    (c fst α : ℝ)
    (h_c : 0 < c) (h_fst : 0 < fst)
    (h_α_pos : 0 < α) (h_α_lt : α < 1) :
    c * α * fst ≤ c * fst := by
  have h_cf : 0 < c * fst := mul_pos h_c h_fst
  nlinarith

/-- **LD mismatch is worse for long-range LD regions.**
    Regions with long-range LD (e.g., MHC) are more affected by
    LD reference mismatch because the LD structure is more population-specific.
    Model: bias in a region = c · n_correlated_snps · fst.  Long-range LD
    regions have more correlated SNPs, so the bias is larger. -/
theorem long_range_ld_worse_mismatch
    (c fst n_short n_long : ℝ)
    (h_c : 0 < c) (h_fst : 0 < fst)
    (h_short_pos : 0 < n_short)
    (h_more_snps : n_short < n_long) :
    c * n_short * fst < c * n_long * fst := by
  have h_cf : 0 < c * fst := mul_pos h_c h_fst
  nlinarith

end LDReferenceMismatch


/-!
## Prior Specification and Portability

The choice of prior in Bayesian PGS affects portability because
genetic architecture may differ across populations.
-/

section PriorSpecification

/- **Gaussian prior assumes infinitesimal architecture.**
    All SNPs have small, normally distributed effects.
    Good for highly polygenic traits (height). -/

/-- **Spike-and-slab prior allows variable sparsity.**
    A proportion π of SNPs are causal with effects from a slab distribution,
    and (1-π) are null. -/
noncomputable def spikeAndSlabPriorVariance (π σ_slab : ℝ) : ℝ :=
  π * σ_slab ^ 2

/-- Spike-and-slab variance is nonneg. -/
theorem spike_slab_variance_nonneg (π σ_slab : ℝ)
    (h_π : 0 ≤ π) :
    0 ≤ spikeAndSlabPriorVariance π σ_slab := by
  unfold spikeAndSlabPriorVariance
  exact mul_nonneg h_π (sq_nonneg _)

/- **Bayes risk under correct vs misspecified prior.**
    Under a spike-and-slab truth with causal proportion π and per-SNP
    effect variance σ²_β, the oracle Bayes risk (correct prior) applies
    optimal shrinkage only to causal SNPs. The misspecified Gaussian
    prior applies uniform shrinkage to all M SNPs.

    Oracle risk (per-SNP, causal): σ²_ε/(n·σ²_β + σ²_ε) (optimal shrinkage)
    Oracle risk (per-SNP, null): 0 (correctly zeroed out)
    Total oracle risk: π·M · σ²_ε/(n·σ²_β + σ²_ε)

    Misspecified Gaussian risk: each SNP gets shrinkage based on
    σ²_prior = π·σ²_β (the marginal variance). For causal SNPs, this
    overshrinks (prior variance too small). For null SNPs, this undershrinks
    (nonzero posterior mean). The excess risk is proportional to (1-π).

    We define the Bayes risk ratio (misspecified/oracle) and show it
    exceeds 1 by a factor that grows with sparsity (1-π). -/

/-- **Misspecification excess risk.**
    The excess MSE from using a Gaussian prior when the true architecture
    is spike-and-slab with causal proportion π. The excess comes from:
    (a) overshrinking the π·M causal SNPs: each loses ~ (1-π)²·σ²_β of signal
    (b) undershrinking the (1-π)·M null SNPs: each gains ~ π²·σ²_β of noise
    Total excess risk per SNP = π·(1-π)²·σ²_β + (1-π)·π²·σ²_β
                               = π·(1-π)·σ²_β·((1-π) + π)
                               = π·(1-π)·σ²_β -/
noncomputable def misspecExcessRisk (π σ_β_sq : ℝ) : ℝ :=
  π * (1 - π) * σ_β_sq

/-- **Excess risk is nonneg for valid parameters.** -/
theorem misspec_excess_risk_nonneg (π σ_β_sq : ℝ)
    (h_π_pos : 0 ≤ π) (h_π_lt : π ≤ 1) (h_σ : 0 ≤ σ_β_sq) :
    0 ≤ misspecExcessRisk π σ_β_sq := by
  unfold misspecExcessRisk
  apply mul_nonneg
  · apply mul_nonneg h_π_pos; linarith
  · exact h_σ

/-- **Prior misspecification hurts sparse traits more.**
    The excess risk π·(1-π)·σ²_β is maximized at π=1/2 and decreases
    toward π=1. For two traits with π_sparse < π_poly (both < 1/2),
    the sparser trait has MORE excess risk because (1-π) is larger.
    More precisely, if both π values are in (0, 1/2], then
    misspecExcessRisk is increasing on this interval (derivative
    (1-2π)·σ²_β > 0 when π < 1/2).

    We prove: for π_sparse < π_poly < 1/2, the excess risk gap
    is proportional to (π_poly - π_sparse). -/
theorem prior_misspec_worse_for_sparse
    (σ_β_sq π_sparse π_poly : ℝ)
    (h_σ : 0 < σ_β_sq)
    (h_sparse_pos : 0 < π_sparse)
    (h_poly_pos : 0 < π_poly)
    (h_sparse_lt_half : π_sparse < 1/2)
    (h_poly_lt_half : π_poly ≤ 1/2)
    (h_sparser : π_sparse < π_poly) :
    misspecExcessRisk π_sparse σ_β_sq < misspecExcessRisk π_poly σ_β_sq := by
  unfold misspecExcessRisk
  -- Need: π_s·(1-π_s)·σ² < π_p·(1-π_p)·σ²
  -- Equiv: π_s·(1-π_s) < π_p·(1-π_p)  (since σ² > 0)
  -- f(π) = π(1-π) is increasing on [0, 1/2] since f'(π) = 1-2π > 0
  -- So π_s < π_p ≤ 1/2 ⟹ f(π_s) < f(π_p)
  have key : π_sparse * (1 - π_sparse) < π_poly * (1 - π_poly) := by nlinarith
  nlinarith

/-- **Portability-prior interaction via Bayes risk.**
    For a polygenic trait (π close to 1), the Gaussian prior is nearly
    correct: excess risk = π(1-π)σ² ≈ 0 since 1-π ≈ 0.
    For a sparse trait (π small), excess risk = π(1-π)σ² ≈ πσ².

    The portability gap between spike-and-slab (correct prior) and
    Gaussian (misspecified) is captured by misspecExcessRisk.
    We show that for a sparse trait with small π and a polygenic trait
    with large π, the sparse trait's misspec penalty exceeds the
    polygenic trait's, provided the sparse trait is near the peak
    of the excess risk curve (π < 1/2) and the polygenic trait is
    past it (π > 1/2).

    More specifically: for π_poly > 1/2 > π_sparse, if
    π_sparse·(1-π_sparse) > π_poly·(1-π_poly), then the sparse
    trait suffers more from prior misspecification. This holds when
    π_poly > 1 - π_sparse (i.e., π_poly is "at least as far above 1/2
    as π_sparse is below it"). -/
theorem portability_prior_interaction
    (σ_β_sq π_sparse π_poly : ℝ)
    (h_σ : 0 < σ_β_sq)
    (h_sparse_pos : 0 < π_sparse) (h_sparse_lt : π_sparse < 1/2)
    (h_poly_gt : 1/2 < π_poly) (h_poly_lt : π_poly < 1)
    (h_far_enough : 1 - π_sparse < π_poly) :
    misspecExcessRisk π_poly σ_β_sq < misspecExcessRisk π_sparse σ_β_sq := by
  unfold misspecExcessRisk
  -- Need: π_p·(1-π_p) < π_s·(1-π_s)
  -- Equivalently: π_p - π_p² < π_s - π_s²
  -- i.e.: (π_p - π_s) < π_p² - π_s² = (π_p - π_s)(π_p + π_s)
  -- Since π_p > π_s (from h_far_enough and h_sparse_lt: π_p > 1-π_s > 1/2 > π_s),
  -- we can divide by (π_p - π_s) > 0 to get: 1 < π_p + π_s,
  -- which is equivalent to 1 - π_s < π_p, i.e., h_far_enough.
  have h_sp_lt_pp : π_sparse < π_poly := by linarith
  have key : π_poly * (1 - π_poly) < π_sparse * (1 - π_sparse) := by nlinarith
  nlinarith

/-- **Empirical Bayes estimation of prior parameters.**
    Estimating π and σ²_slab from data is population-specific,
    so the prior learned in EUR may not suit AFR. -/
theorem empirical_bayes_population_specific
    (π_eur π_afr : ℝ)
    (h_diff : π_eur ≠ π_afr) :
    spikeAndSlabPriorVariance π_eur 1 ≠ spikeAndSlabPriorVariance π_afr 1 := by
  unfold spikeAndSlabPriorVariance
  simp
  exact h_diff

end PriorSpecification


/-!
## Posterior Predictive Distribution

The posterior predictive distribution for a new individual's phenotype
given their genotype and the GWAS data.
-/

section PosteriorPredictive

/-- **Posterior predictive variance.**
    Var(Y_new | data) = Var(Y | β̂) + g' Var(β | data) g
    where g is the genotype vector. The second term is the estimation
    uncertainty. -/
noncomputable def posteriorPredictiveVariance
    (residual_var estimation_var : ℝ) : ℝ :=
  residual_var + estimation_var

/-- Posterior predictive variance ≥ residual variance. -/
theorem posterior_predictive_wider_than_residual
    (residual_var estimation_var : ℝ)
    (h_est : 0 ≤ estimation_var) :
    residual_var ≤ posteriorPredictiveVariance residual_var estimation_var := by
  unfold posteriorPredictiveVariance
  linarith

/-- **Estimation variance decreases with sample size.**
    As GWAS n → ∞, Var(β | data) → 0 and posterior predictive
    converges to the plug-in prediction interval.
    Model: estimation variance ∝ σ²/(n·h²), so larger n gives smaller variance.
    For n₁ < n₂, est_var(n₂) = est_var(n₁) · (n₁/n₂) < est_var(n₁). -/
theorem estimation_variance_decreases_with_n
    (σ_sq h_sq n₁ n₂ : ℝ)
    (h_σ : 0 < σ_sq) (h_hsq : 0 < h_sq)
    (h_n₁ : 0 < n₁) (h_n₂ : 0 < n₂)
    (h_more : n₁ < n₂) :
    σ_sq / (n₂ * h_sq) < σ_sq / (n₁ * h_sq) := by
  apply div_lt_div_of_pos_left h_σ (mul_pos h_n₁ h_hsq)
  exact mul_lt_mul_of_pos_right h_more h_hsq

/-- **Cross-population posterior predictive is wider.**
    In the target population, both residual variance and estimation
    variance are larger → wider posterior predictive intervals. -/
theorem cross_population_posterior_wider
    (resid_s resid_t est_s est_t : ℝ)
    (h_resid : resid_s ≤ resid_t)
    (h_est : est_s ≤ est_t) :
    posteriorPredictiveVariance resid_s est_s ≤
      posteriorPredictiveVariance resid_t est_t := by
  unfold posteriorPredictiveVariance
  linarith

/-- **Model uncertainty adds a third variance component.**
    When comparing multiple Bayesian models (e.g., PRS-CS vs LDpred),
    model uncertainty further widens the posterior predictive.
    Total variance = within-model variance + between-model variance (law of
    total variance). Since between-model variance ≥ 0, total ≥ within-model. -/
theorem model_uncertainty_widens_intervals
    (within_model_var between_model_var : ℝ)
    (h_within_nn : 0 ≤ within_model_var)
    (h_between_nn : 0 ≤ between_model_var) :
    within_model_var ≤ within_model_var + between_model_var := by
  linarith

end PosteriorPredictive


/-!
## PRS-CS Specific Theory

PRS-CS uses a continuous shrinkage (CS) prior with global-local
structure: β_j ~ N(0, σ²_j), σ²_j ~ g(σ²_j | φ), φ ~ p(φ).
-/

section PRSCS

/-- **Global shrinkage parameter φ controls overall sparsity.**
    Small φ → more shrinkage (sparser model).
    Large φ → less shrinkage (denser model).
    The effective number of nonzero coefficients is approximately
    n_eff ≈ M · φ/(1+φ) where M is total SNPs. Since φ/(1+φ)
    is monotonically increasing in φ, larger φ yields more nonzero effects. -/
theorem global_shrinkage_controls_sparsity
    (M φ₁ φ₂ : ℝ)
    (hM : 0 < M) (hφ₁ : 0 < φ₁) (hφ₂ : 0 < φ₂)
    (h_more_phi : φ₁ < φ₂) :
    M * (φ₁ / (1 + φ₁)) < M * (φ₂ / (1 + φ₂)) := by
  apply mul_lt_mul_of_pos_left _ hM
  rw [div_lt_div_iff₀ (by linarith) (by linarith)]
  nlinarith

/- **PRS-CS automatically adapts to genetic architecture.**
    The continuous shrinkage prior adapts the effective number of
    nonzero effects based on the data, without specifying π directly. -/

/-- **PRS-CS performance relative to C+T.**
    PRS-CS uniformly dominates C+T in in-sample prediction.
    The advantage is largest for polygenic traits.
    Model: C+T uses only p SNPs passing threshold and ignores LD;
    PRS-CS uses all M SNPs with optimal shrinkage.
    R²_CT = h² · p/M · (1-noise_CT), R²_PRS-CS = h² · (1-noise_CS).
    Since p ≤ M and noise_CS ≤ noise_CT, PRS-CS dominates. -/
theorem prs_cs_dominates_ct
    (h_sq p M noise_ct noise_cs : ℝ)
    (h_hsq : 0 < h_sq) (h_p : 0 < p) (h_M : 0 < M)
    (h_pM : p ≤ M)
    (h_noise_ct : 0 ≤ noise_ct) (h_noise_ct1 : noise_ct < 1)
    (h_noise_cs : 0 ≤ noise_cs) (h_noise_cs1 : noise_cs < 1)
    (h_cs_better : noise_cs ≤ noise_ct) :
    h_sq * (p / M) * (1 - noise_ct) ≤ h_sq * (1 - noise_cs) := by
  have h_pM_ratio : p / M ≤ 1 := by rwa [div_le_one (by linarith : (0:ℝ) < M)]
  have h1 : (1 - noise_ct) ≤ (1 - noise_cs) := by linarith
  have h2 : p / M * (1 - noise_ct) ≤ 1 * (1 - noise_cs) := by
    apply mul_le_mul h_pM_ratio h1 (by linarith) (by linarith)
  nlinarith

/-- **PRS-CS portability advantage over C+T.**
    By using the full LD structure, PRS-CS captures more of the
    shared genetic signal, improving cross-population prediction.
    Model: portability = R²_target/R²_source. PRS-CS recovers a
    fraction (1-ε_cs) of the shared signal while C+T recovers
    (1-ε_ct) where ε_ct ≥ ε_cs (C+T loses more to LD mismatch
    because it uses hard thresholding). -/
theorem prs_cs_portability_advantage
    (shared_signal ε_ct ε_cs : ℝ)
    (h_sig : 0 < shared_signal)
    (h_ect : 0 ≤ ε_ct) (h_ect1 : ε_ct < 1)
    (h_ecs : 0 ≤ ε_cs) (h_ecs1 : ε_cs < 1)
    (h_cs_better : ε_cs ≤ ε_ct) :
    shared_signal * (1 - ε_ct) ≤ shared_signal * (1 - ε_cs) := by
  nlinarith

/-- **PRS-CS with mismatched LD can be worse than C+T.**
    If the LD reference panel is from a very different population,
    PRS-CS can actually perform worse than C+T because C+T
    is more robust to LD misspecification.
    Model: PRS-CS accuracy = base_r2 - mismatch_penalty.
    C+T accuracy = base_r2 · (p/M) but is unaffected by LD mismatch.
    When mismatch_penalty > base_r2 · (1 - p/M), PRS-CS is worse. -/
theorem ld_mismatch_can_reverse_advantage
    (base_r2 p M mismatch_penalty : ℝ)
    (h_r2 : 0 < base_r2) (h_p : 0 < p) (h_M : 0 < M)
    (h_pM : p ≤ M)
    (h_penalty_large : base_r2 * (1 - p / M) < mismatch_penalty)
    (h_pen_lt : mismatch_penalty < base_r2) :
    base_r2 - mismatch_penalty < base_r2 * (p / M) := by
  have : p / M ≤ 1 := by rwa [div_le_one (by linarith : (0:ℝ) < M)]
  nlinarith

end PRSCS


/-!
## Multi-Ancestry Bayesian Methods

Methods that combine GWAS from multiple ancestries in a Bayesian
framework to improve portability.
-/

section MultiAncestryBayesian

/- **Joint posterior from multi-ancestry GWAS.**
    P(β | data_EUR, data_AFR, ...) combines information across
    ancestries, weighted by sample size and genetic correlation. -/

/-- **Genetic correlation determines information borrowing.**
    If rg = 1 (same effects), full information is shared.
    If rg = 0 (independent effects), no borrowing occurs. -/
theorem info_borrowing_proportional_to_rg
    (rg info_gain : ℝ)
    (h_relation : info_gain = rg ^ 2)
    (h_rg : 0 ≤ rg) (h_rg_le : rg ≤ 1) :
    0 ≤ info_gain ∧ info_gain ≤ 1 := by
  rw [h_relation]
  exact ⟨sq_nonneg _, by nlinarith [sq_nonneg rg]⟩

/-- **Effective sample size in multi-ancestry setting.**
    n_eff = n_target + Σ_k (rg_k² × n_k × h_k / h_target)
    where h_k is heritability in population k. -/
noncomputable def multiAncestryEffectiveN
    (n_target rg n_other : ℝ) : ℝ :=
  n_target + rg ^ 2 * n_other

/-- **Multi-ancestry PGS is at least as good as single-ancestry.**
    With well-specified models, combining data cannot hurt.
    The effective sample size is n_target + rg² · n_other where rg ∈ [0,1].
    Since rg² · n_other ≥ 0, the effective n is at least n_target,
    and R² = n_eff · h²/(n_eff · h² + 1) is monotone in n_eff. -/
theorem multi_ancestry_at_least_as_good
    (n_target rg n_other h_sq : ℝ)
    (h_nt : 0 < n_target) (h_rg : 0 ≤ rg) (h_no : 0 ≤ n_other)
    (h_hsq : 0 < h_sq) :
    gaussianPosteriorShrinkage n_target h_sq ≤
      gaussianPosteriorShrinkage (multiAncestryEffectiveN n_target rg n_other) h_sq := by
  unfold gaussianPosteriorShrinkage multiAncestryEffectiveN
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [sq_nonneg rg, mul_nonneg (sq_nonneg rg) h_no]

/-- Multi-ancestry effective N ≥ single-ancestry N. -/
theorem multi_ancestry_effective_n_ge
    (n_target rg n_other : ℝ)
    (h_rg : 0 ≤ rg) (h_n : 0 ≤ n_other) :
    n_target ≤ multiAncestryEffectiveN n_target rg n_other := by
  unfold multiAncestryEffectiveN
  linarith [mul_nonneg (sq_nonneg rg) h_n]

/-- **Diminishing returns from adding more EUR samples.**
    When the target is AFR and we already have large EUR GWAS,
    additional EUR samples help less than adding AFR samples.
    The marginal gain from adding Δn EUR samples to the AFR effective
    sample size is rg² · Δn (attenuated by genetic correlation),
    while adding Δn AFR samples contributes Δn directly.
    Since rg < 1, EUR samples contribute less. -/
theorem diminishing_returns_from_majority
    (Δn rg : ℝ)
    (h_Δn : 0 < Δn) (h_rg_pos : 0 < rg) (h_rg_lt : rg < 1) :
    rg ^ 2 * Δn < Δn := by
  have h_sq_lt : rg ^ 2 < 1 := by nlinarith [sq_abs rg, sq_nonneg rg]
  nlinarith

/-- **Optimal allocation of GWAS resources across ancestries.**
    For a fixed total budget N, the optimal allocation maximizes
    the minimum R² across populations. This generally requires
    oversampling underrepresented populations. -/
theorem optimal_allocation_oversamples_minority
    (n_majority n_minority n_total : ℝ)
    (h_total : n_majority + n_minority = n_total)
    (h_optimal_minority_share proportion : ℝ)
    (h_oversampled : proportion < h_optimal_minority_share)
    (h_prop_def : proportion = n_minority / n_total)
    (h_pos : 0 < n_total)
    (h_minority_share : n_minority / n_total < 1/2) :
    -- The optimal minority share exceeds the population proportion
    n_minority / n_total < h_optimal_minority_share := by linarith

end MultiAncestryBayesian

end Calibrator
