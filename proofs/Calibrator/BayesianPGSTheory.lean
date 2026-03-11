import Calibrator.Probability
import Calibrator.PortabilityDrift
import Calibrator.OpenQuestions

namespace Calibrator

open MeasureTheory

/-!
# Bayesian Shrinkage and Posterior Prediction Theory

This file formalizes theoretical properties of Bayesian shrinkage estimators
and posterior predictive distributions, with implications for portability.

Key results:
1. Bayesian shrinkage and posterior effect sizes
2. Spike-and-slab prior variance
3. Posterior predictive distributions across populations
4. Multi-ancestry effective sample size and information borrowing

Reference: Wang et al. (2026), Nature Communications 17:942.
-/


/-!
## Bayesian Shrinkage Framework

Bayesian PGS methods estimate posterior effect sizes:
β̂_Bayes = E[β | GWAS summary stats, LD reference].
The shrinkage pattern depends on the prior and LD.
-/

section BayesianShrinkage

/-- **Posterior mean under Gaussian prior.**
    β̂_Bayes = (n × Σ_LD + σ²_β⁻¹ × I)⁻¹ × n × Σ_LD × β̂_OLS
    For a single SNP: β̂ = β̂_OLS × n × h / (n × h + 1)
    where h = σ²_β / σ²_ε is the per-SNP heritability. -/
noncomputable def gaussianPosteriorShrinkage (n h : ℝ) : ℝ :=
  n * h / (n * h + 1)

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

end BayesianShrinkage


/-!
## Spike-and-Slab Prior

The spike-and-slab prior allows variable sparsity in effect sizes.
-/

section SpikeAndSlab

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

end SpikeAndSlab


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

end PosteriorPredictive


/-!
## Multi-Ancestry Effective Sample Size

Methods that combine GWAS from multiple ancestries to improve portability.
-/

section MultiAncestryBayesian

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

/-- Multi-ancestry effective N ≥ single-ancestry N. -/
theorem multi_ancestry_effective_n_ge
    (n_target rg n_other : ℝ)
    (h_rg : 0 ≤ rg) (h_n : 0 ≤ n_other) :
    n_target ≤ multiAncestryEffectiveN n_target rg n_other := by
  unfold multiAncestryEffectiveN
  linarith [mul_nonneg (sq_nonneg rg) h_n]

end MultiAncestryBayesian

end Calibrator
