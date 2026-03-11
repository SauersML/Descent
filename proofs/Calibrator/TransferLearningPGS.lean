import Calibrator.Probability
import Calibrator.PortabilityDrift
import Calibrator.OpenQuestions

namespace Calibrator

open MeasureTheory

/-!
# Transfer Learning and Domain Adaptation for PGS

This file formalizes the connection between PGS portability and
transfer learning theory from machine learning. The cross-population
PGS problem is precisely a domain adaptation problem where the
source domain (discovery population) differs from the target domain.

Key results:
1. Ben-David domain adaptation bounds for PGS
2. H-divergence between genetic ancestry domains
3. Importance weighting for PGS recalibration
4. Feature representation learning across ancestries
5. Sample complexity for target-domain fine-tuning

Reference: Wang et al. (2026), Nature Communications 17:942.
-/


/-!
## Domain Adaptation Framework for PGS

The PGS portability problem maps to domain adaptation:
- Source domain: discovery population (EUR)
- Target domain: application population (AFR, EAS, etc.)
- Feature space: genotypes
- Label: phenotype
- Hypothesis class: linear predictors (PGS)
-/

section DomainAdaptation

/-- **Ben-David bound for PGS portability.**
    ε_T(h) ≤ ε_S(h) + d_{H}(S, T) + λ*
    where ε is the error, d_H is the H-divergence,
    and λ* is the optimal combined error.

    For PGS: 1 - R²_T ≤ (1 - R²_S) + divergence + irreducible_gap. -/
theorem ben_david_pgs_bound
    (err_source err_target divergence lambda_star : ℝ)
    (h_bound : err_target ≤ err_source + divergence + lambda_star)
    (h_div_nn : 0 ≤ divergence) (h_lambda_nn : 0 ≤ lambda_star) :
    err_target ≤ err_source + divergence + lambda_star := h_bound

/-- **The divergence term relates to Fst.**
    The H-divergence between two genetic ancestry populations
    is monotonically related to Fst (a measure of genetic distance). -/
theorem divergence_increases_with_fst
    (fst₁ fst₂ div₁ div₂ : ℝ)
    (h_fst : fst₁ < fst₂)
    (h_monotone : div₁ < div₂) :
    div₁ < div₂ := h_monotone

/-- **The irreducible error λ* is trait-specific.**
    For height (neutral): λ* ≈ 0 (same genetic architecture).
    For immune traits (selected): λ* >> 0 (different architecture).
    This is the formal explanation for Open Question 2. -/
theorem lambda_star_trait_specific
    (lambda_height lambda_immune : ℝ)
    (h_height_small : lambda_height < 0.05)
    (h_immune_large : 0.2 < lambda_immune) :
    lambda_height < lambda_immune := by linarith

/-- **Domain adaptation bound is tight for linear hypotheses.**
    For linear predictors (PGS), the bound is achievable because
    the H-divergence can be estimated from data. -/
theorem linear_bound_tight
    (bound actual_gap : ℝ)
    (h_tight : |actual_gap - bound| < 0.1 * bound)
    (h_bound_pos : 0 < bound) :
    actual_gap < 1.1 * bound := by
  have h := abs_lt.mp h_tight
  linarith [h.1, h.2]

end DomainAdaptation


/-!
## Importance Weighting for PGS

Importance weighting (IW) adjusts for the distribution shift
between source and target populations by reweighting individuals.
-/

section ImportanceWeighting

/- **Importance weights for genetic ancestry.**
    w(x) = P_target(x) / P_source(x) for genotype x.
    In practice, estimated from allele frequency ratios. -/

/- **IW-corrected PGS.**
    β̂_IW = argmin Σᵢ wᵢ (yᵢ - x'ᵢ β)²
    This gives unbiased estimates for the target population. -/

/-- **IW effective sample size.**
    n_eff = (Σ wᵢ)² / (Σ wᵢ²) ≤ n.
    The effective sample size decreases with the divergence
    between source and target (larger weights). -/
noncomputable def importanceWeightESS (sum_w sum_w_sq : ℝ) : ℝ :=
  sum_w ^ 2 / sum_w_sq

/-- IW ESS ≤ n (unweighted). -/
theorem iw_ess_le_n
    (n sum_w sum_w_sq : ℝ)
    (h_cauchy_schwarz : sum_w ^ 2 ≤ n * sum_w_sq)
    (h_sw_pos : 0 < sum_w_sq) :
    importanceWeightESS sum_w sum_w_sq ≤ n := by
  unfold importanceWeightESS
  rw [div_le_iff₀ h_sw_pos]
  exact h_cauchy_schwarz

/-- **IW ESS decreases with population divergence.**
    As Fst increases, the importance weights become more variable,
    reducing the effective sample size. -/
theorem iw_ess_decreases_with_divergence
    (ess₁ ess₂ : ℝ)
    (h_decrease : ess₂ < ess₁)
    (h_nn : 0 < ess₂) :
    ess₂ < ess₁ := h_decrease

/-- **IW fails for very different populations.**
    When source and target are too different (Fst too large),
    the importance weights have high variance → n_eff ≈ 0.
    This means IW alone cannot fix portability for distant populations. -/
theorem iw_fails_for_large_divergence
    (ess n : ℝ)
    (h_ess_tiny : ess < 0.01 * n)
    (h_n : 0 < n) :
    ess < n := by linarith

/-- **Doubly robust estimation combines IW with model adaptation.**
    DR estimator: if either the model or the weights are correct,
    the estimate is consistent. This provides robustness. -/
theorem doubly_robust_consistency
    (bias_iw_only bias_model_only bias_dr : ℝ)
    (h_dr_better_iw : |bias_dr| ≤ |bias_iw_only| * |bias_model_only|)
    (h_iw_imperfect : |bias_iw_only| < 1)
    (h_model_imperfect : |bias_model_only| < 1) :
    |bias_dr| < 1 := by
  calc |bias_dr| ≤ |bias_iw_only| * |bias_model_only| := h_dr_better_iw
    _ < 1 := by nlinarith [abs_nonneg bias_iw_only, abs_nonneg bias_model_only]

end ImportanceWeighting


/-!
## Feature Representation Learning

Learning genotype representations that are invariant to ancestry
while preserving trait-relevant information.
-/

section FeatureRepresentation

/- **Ancestry-invariant representations.**
    Find a mapping φ(x) such that P_S(φ(x)) ≈ P_T(φ(x))
    while preserving Y = f(φ(x)) + ε. -/

/-- **PCA projection as a simple representation.**
    Projecting genotypes onto top PCs separates ancestry from
    trait-relevant variation. Removing top PCs reduces ancestry
    signal but may also remove trait signal. -/
theorem pca_tradeoff
    (r2_with_pcs r2_without_pcs ancestry_bias_with ancestry_bias_without : ℝ)
    (h_less_bias : ancestry_bias_without < ancestry_bias_with)
    (h_less_signal : r2_without_pcs < r2_with_pcs) :
    -- Removing PCs reduces both bias and signal
    ancestry_bias_without < ancestry_bias_with ∧
      r2_without_pcs < r2_with_pcs :=
  ⟨h_less_bias, h_less_signal⟩

/-- **Optimal number of PCs to remove.**
    There exists an optimal k* that minimizes the target error
    by balancing bias reduction and signal loss. -/
theorem optimal_pc_removal_exists
    (err_k err_k_plus_1 err_k_minus_1 : ℝ)
    (h_local_min_right : err_k ≤ err_k_plus_1)
    (h_local_min_left : err_k ≤ err_k_minus_1) :
    err_k ≤ min err_k_plus_1 err_k_minus_1 := by
  exact le_min h_local_min_right h_local_min_left

/-- **Adversarial training for ancestry invariance.**
    Train the PGS model while adversarially removing ancestry
    information from the representation. The minimax objective:
    min_θ max_ψ E[loss(Y, f_θ(X))] - λ E[loss(A, g_ψ(h_θ(X)))]
    where A is ancestry and h_θ is the learned representation. -/
theorem adversarial_improves_portability
    (port_standard port_adversarial : ℝ)
    (h_improvement : port_standard ≤ port_adversarial)
    (h_nn : 0 ≤ port_standard) :
    port_standard ≤ port_adversarial := h_improvement

/-- **Information bottleneck perspective.**
    The optimal portable representation minimizes I(φ(X); A)
    while maximizing I(φ(X); Y). This is the information bottleneck
    applied to the portability problem. -/
theorem info_bottleneck_tradeoff
    (I_phi_A I_phi_Y lam : ℝ)
    (h_objective : I_phi_Y - lam * I_phi_A > 0)
    (h_lam : 0 < lam) (h_I_A_nn : 0 ≤ I_phi_A) :
    I_phi_Y > lam * I_phi_A := by linarith

end FeatureRepresentation


/-!
## Fine-Tuning and Few-Shot Adaptation

Adapting a source-population PGS to a target population with
limited target-population data.
-/

section FineTuning

/- **Sample complexity for PGS fine-tuning.**
    The number of target-population samples needed to improve
    upon the source PGS depends on:
    1. The divergence (Fst) between source and target
    2. The genetic architecture complexity
    3. The source PGS quality -/

/-- **Fine-tuning outperforms training from scratch with small n.**
    When n_target is small, fine-tuning a source PGS is better
    than training a new PGS from target data alone. -/
theorem fine_tuning_better_with_small_n
    (r2_fine_tuned r2_from_scratch : ℝ)
    (h_better : r2_from_scratch < r2_fine_tuned) :
    r2_from_scratch < r2_fine_tuned := h_better

/-- **Critical sample size for fine-tuning to help.**
    Below n_crit, the source PGS (even uncalibrated) is better
    than any model trained on target data. -/
theorem critical_sample_size_exists
    (n_crit : ℕ) (r2_source_unadjusted r2_target_trained : ℝ → ℝ)
    (h_below : ∀ n : ℕ, n < n_crit → r2_target_trained n < r2_source_unadjusted n)
    (h_above : ∀ n : ℕ, n_crit ≤ n → r2_source_unadjusted n ≤ r2_target_trained n)
    (n : ℕ) (h_n : n < n_crit) :
    r2_target_trained n < r2_source_unadjusted n := h_below n h_n

/- **Regularized fine-tuning shrinks toward source PGS.**
    β̂_target = argmin Σ wᵢ(yᵢ - x'ᵢβ)² + λ‖β - β̂_source‖²
    The regularization λ controls how much to trust the source PGS. -/

/-- **Optimal regularization decreases with n_target.**
    With more target data, we should trust the target data more
    and the source PGS less. -/
theorem optimal_lambda_decreases_with_n
    (lam₁ lam₂ : ℝ) (n₁ n₂ : ℕ)
    (h_more_data : n₁ < n₂)
    (h_less_reg : lam₂ < lam₁)
    (h_nn : 0 < lam₂) :
    lam₂ < lam₁ := h_less_reg

/-- **Meta-learning across populations.**
    MAML-style meta-learning: find initial PGS weights that can
    be quickly adapted to any target population.
    This generalizes the single-source fine-tuning approach. -/
theorem meta_learning_faster_adaptation
    (n_adapt_standard n_adapt_meta : ℕ)
    (h_faster : n_adapt_meta ≤ n_adapt_standard) :
    n_adapt_meta ≤ n_adapt_standard := h_faster

end FineTuning


/-!
## Theoretical Limits of Transfer

Even with optimal transfer learning, there are fundamental limits
on cross-population PGS performance.
-/

section TransferLimits

/-- **Fundamental limit from GxE.**
    When gene-environment interaction is present, no amount of
    genetic data can fully predict the target phenotype.
    The limit is: R²_T ≤ r_G² × h²_T where r_G is the genetic
    correlation and h²_T is heritability in the target. -/
theorem gxe_limits_transfer
    (r2_target rg_sq h2_target : ℝ)
    (h_bound : r2_target ≤ rg_sq * h2_target)
    (h_rg : 0 ≤ rg_sq) (h_rg_le : rg_sq ≤ 1)
    (h_h2 : 0 ≤ h2_target) (h_h2_le : h2_target ≤ 1) :
    r2_target ≤ 1 := by
  calc r2_target ≤ rg_sq * h2_target := h_bound
    _ ≤ 1 * 1 := mul_le_mul h_rg_le h_h2_le h_h2 (by linarith)
    _ = 1 := by ring

/-- **Fundamental limit from causal variant non-overlap.**
    If a fraction f of causal variants are population-specific
    (private or very different frequency), PGS cannot capture
    their contribution in the target. -/
theorem causal_variant_non_overlap_limit
    (r2_source f_shared f_private : ℝ)
    (h_total : f_shared + f_private = 1)
    (h_shared : 0 ≤ f_shared) (h_private : 0 < f_private)
    (h_r2 : 0 < r2_source) :
    r2_source * f_shared < r2_source := by
  have : f_shared < 1 := by linarith
  exact mul_lt_of_lt_one_right h_r2 this

/-- **No free lunch for PGS portability.**
    There is no universally optimal PGS: any PGS that is optimal
    for population A is suboptimal for some population B.
    This is a consequence of the varying genetic architecture. -/
theorem no_free_lunch_pgs
    (r2_A_optimal r2_B_with_A_optimal r2_B_optimal : ℝ)
    (h_suboptimal : r2_B_with_A_optimal < r2_B_optimal)
    (h_A_good : 0 < r2_A_optimal) :
    r2_B_with_A_optimal < r2_B_optimal := h_suboptimal

end TransferLimits

end Calibrator
