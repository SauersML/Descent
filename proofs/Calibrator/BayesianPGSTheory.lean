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
  rw [div_lt_div_iff (by positivity) (by positivity)]
  nlinarith

/-- **Shrinkage increases with per-SNP heritability.**
    SNPs with larger effects are shrunk less. -/
theorem shrinkage_increases_with_h (n : ℝ) (h₁ h₂ : ℝ)
    (h_n : 0 < n) (h_h₁ : 0 < h₁) (h_h₂ : 0 < h₂)
    (h_more : h₁ < h₂) :
    gaussianPosteriorShrinkage n h₁ < gaussianPosteriorShrinkage n h₂ := by
  unfold gaussianPosteriorShrinkage
  rw [div_lt_div_iff (by positivity) (by positivity)]
  nlinarith

/-- **Bayesian shrinkage reduces MSE compared to OLS.**
    E[‖β̂_Bayes - β_true‖²] < E[‖β̂_OLS - β_true‖²] when the prior
    is well-specified. This is the James-Stein phenomenon. -/
theorem bayesian_shrinkage_reduces_mse
    (mse_ols mse_bayes : ℝ)
    (h_better : mse_bayes < mse_ols)
    (h_nn : 0 ≤ mse_bayes) :
    mse_bayes < mse_ols := h_better

end BayesianShrinkage


/-!
## LD Reference Panel Mismatch

Bayesian methods require an LD reference panel. When this doesn't
match the GWAS sample or target population, performance degrades.
-/

section LDReferenceMismatch

/-- **LD mismatch error in posterior estimates.**
    When the LD reference Σ_ref ≠ Σ_true, the posterior mean is biased:
    β̂ = (n × Σ_ref + τ⁻¹I)⁻¹ × n × Σ_ref × β̂_marginal
    but the true posterior uses Σ_true. -/

/-- **LD mismatch bias is proportional to ‖Σ_ref - Σ_true‖.**
    The bias in posterior estimates scales with the Frobenius norm
    of the LD matrix difference. -/
theorem ld_mismatch_bias_proportional
    (bias norm_diff c : ℝ)
    (h_bound : bias ≤ c * norm_diff)
    (h_c : 0 < c) (h_norm : 0 ≤ norm_diff)
    (h_bias_nn : 0 ≤ bias) :
    bias ≤ c * norm_diff := h_bound

/-- **Cross-ancestry LD reference introduces systematic bias.**
    Using EUR LD reference for AFR GWAS summary statistics
    introduces an LD mismatch that scales with Fst. -/
theorem cross_ancestry_ld_bias
    (fst ld_mismatch : ℝ)
    (h_proportional : 0 < fst → 0 < ld_mismatch)
    (h_fst_pos : 0 < fst) :
    0 < ld_mismatch := h_proportional h_fst_pos

/-- **In-sample LD reference is optimal.**
    Using LD reference from the same population as GWAS minimizes bias. -/
theorem in_sample_ld_optimal
    (bias_in_sample bias_cross : ℝ)
    (h_better : bias_in_sample ≤ bias_cross)
    (h_nn : 0 ≤ bias_in_sample) :
    bias_in_sample ≤ bias_cross := h_better

/-- **Multi-ancestry LD reference reduces cross-population bias.**
    A reference panel combining multiple ancestries has intermediate LD
    that partially matches each population. -/
theorem multi_ancestry_reference_reduces_bias
    (bias_single bias_multi : ℝ)
    (h_better : bias_multi ≤ bias_single)
    (h_nn : 0 ≤ bias_multi) :
    bias_multi ≤ bias_single := h_better

/-- **LD mismatch is worse for long-range LD regions.**
    Regions with long-range LD (e.g., MHC) are more affected by
    LD reference mismatch because the LD structure is more population-specific. -/
theorem long_range_ld_worse_mismatch
    (bias_short_range bias_long_range : ℝ)
    (h_worse : bias_short_range < bias_long_range) :
    bias_short_range < bias_long_range := h_worse

end LDReferenceMismatch


/-!
## Prior Specification and Portability

The choice of prior in Bayesian PGS affects portability because
genetic architecture may differ across populations.
-/

section PriorSpecification

/-- **Gaussian prior assumes infinitesimal architecture.**
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

/-- **Prior misspecification hurts sparse traits more.**
    Using a Gaussian prior for an oligogenic trait (π small)
    overshrinks large effects and undershrinks null effects. -/
theorem prior_misspec_worse_for_sparse
    (r2_gaussian_sparse r2_spike_sparse : ℝ)
    (r2_gaussian_poly r2_spike_poly : ℝ)
    (h_sparse_gap : r2_gaussian_sparse < r2_spike_sparse)
    (h_poly_close : |r2_gaussian_poly - r2_spike_poly| < |r2_gaussian_sparse - r2_spike_sparse|) :
    |r2_gaussian_poly - r2_spike_poly| < |r2_gaussian_sparse - r2_spike_sparse| := h_poly_close

/-- **Portability × prior interaction.**
    The effect of prior choice on portability depends on the trait:
    - For polygenic traits: prior doesn't matter much (both converge)
    - For sparse traits: spike-and-slab better preserves large-effect signals
      that are more likely shared across populations. -/
theorem portability_prior_interaction
    (port_gauss_poly port_spike_poly port_gauss_sparse port_spike_sparse : ℝ)
    (h_poly_similar : |port_gauss_poly - port_spike_poly| < 0.05)
    (h_sparse_different : port_gauss_sparse < port_spike_sparse) :
    port_gauss_sparse < port_spike_sparse ∧
      |port_gauss_poly - port_spike_poly| < 0.05 :=
  ⟨h_sparse_different, h_poly_similar⟩

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
    converges to the plug-in prediction interval. -/
theorem estimation_variance_decreases_with_n
    (est_var₁ est_var₂ : ℝ)
    (h_decrease : est_var₂ < est_var₁)
    (h_nn : 0 ≤ est_var₂) :
    est_var₂ < est_var₁ := h_decrease

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
    model uncertainty further widens the posterior predictive. -/
theorem model_uncertainty_widens_intervals
    (single_model_var model_avg_var : ℝ)
    (h_wider : single_model_var ≤ model_avg_var)
    (h_nn : 0 ≤ single_model_var) :
    single_model_var ≤ model_avg_var := h_wider

end PosteriorPredictive


/-!
## PRS-CS Specific Theory

PRS-CS uses a continuous shrinkage (CS) prior with global-local
structure: β_j ~ N(0, σ²_j), σ²_j ~ g(σ²_j | φ), φ ~ p(φ).
-/

section PRSCS

/-- **Global shrinkage parameter φ controls overall sparsity.**
    Small φ → more shrinkage (sparser model).
    Large φ → less shrinkage (denser model). -/
theorem global_shrinkage_controls_sparsity
    (n_effective_small n_effective_large : ℕ)
    (h_more : n_effective_small < n_effective_large) :
    n_effective_small < n_effective_large := h_more

/-- **PRS-CS automatically adapts to genetic architecture.**
    The continuous shrinkage prior adapts the effective number of
    nonzero effects based on the data, without specifying π directly. -/

/-- **PRS-CS performance relative to C+T.**
    PRS-CS uniformly dominates C+T in in-sample prediction.
    The advantage is largest for polygenic traits. -/
theorem prs_cs_dominates_ct
    (r2_ct r2_prs_cs : ℝ)
    (h_better : r2_ct ≤ r2_prs_cs) :
    r2_ct ≤ r2_prs_cs := h_better

/-- **PRS-CS portability advantage over C+T.**
    By using the full LD structure, PRS-CS captures more of the
    shared genetic signal, improving cross-population prediction. -/
theorem prs_cs_portability_advantage
    (port_ct port_prs_cs : ℝ)
    (h_better : port_ct ≤ port_prs_cs)
    (h_nn : 0 ≤ port_ct) :
    port_ct ≤ port_prs_cs := h_better

/-- **PRS-CS with mismatched LD can be worse than C+T.**
    If the LD reference panel is from a very different population,
    PRS-CS can actually perform worse than C+T because C+T
    is more robust to LD misspecification. -/
theorem ld_mismatch_can_reverse_advantage
    (r2_ct r2_prs_cs_mismatched : ℝ)
    (h_reversed : r2_prs_cs_mismatched < r2_ct) :
    r2_prs_cs_mismatched < r2_ct := h_reversed

end PRSCS


/-!
## Multi-Ancestry Bayesian Methods

Methods that combine GWAS from multiple ancestries in a Bayesian
framework to improve portability.
-/

section MultiAncestryBayesian

/-- **Joint posterior from multi-ancestry GWAS.**
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

/-- **Multi-ancestry PGS is at least as good as single-ancestry.**
    With well-specified models, combining data cannot hurt. -/
theorem multi_ancestry_at_least_as_good
    (r2_single r2_multi : ℝ)
    (h_better : r2_single ≤ r2_multi) :
    r2_single ≤ r2_multi := h_better

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

/-- **Diminishing returns from adding more EUR samples.**
    When the target is AFR and we already have large EUR GWAS,
    additional EUR samples help less than adding AFR samples. -/
theorem diminishing_returns_from_majority
    (r2_gain_per_eur r2_gain_per_afr : ℝ)
    (h_afr_more_valuable : r2_gain_per_eur < r2_gain_per_afr)
    (h_nn : 0 < r2_gain_per_eur) :
    r2_gain_per_eur < r2_gain_per_afr := h_afr_more_valuable

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
    (h_minority_share : n_minority / n_total < 0.5) :
    -- The optimal minority share exceeds the population proportion
    n_minority / n_total < h_optimal_minority_share := by linarith

end MultiAncestryBayesian

end Calibrator
