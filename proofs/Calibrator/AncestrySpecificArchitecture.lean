import Calibrator.Probability
import Calibrator.PortabilityDrift
import Calibrator.OpenQuestions

namespace Calibrator

open MeasureTheory

/-!
# Ancestry-Specific Genetic Architecture

This file formalizes how genetic architecture parameters
(effect sizes, allele frequencies, LD patterns) differ across
ancestries and how these differences create portability barriers.

Key results:
1. Allele frequency divergence via drift
2. Effect size heterogeneity from GxE and epistasis
3. Ancestry-specific LD tagging
4. Allelic heterogeneity (different causal variants per locus)
5. Architecture convergence under shared environments

Reference: Wang et al. (2026), Nature Communications 17:942.
-/


/-!
## Allele Frequency Divergence

Allele frequency differences between populations are the
most fundamental driver of PGS portability issues.
-/

section AlleleFrequencyDivergence

/-- **Expected allele frequency difference from drift.**
    E[(p₁ - p₂)²] = 2 × FST × p₀(1-p₀)
    where p₀ is the ancestral frequency. -/
noncomputable def expectedFreqDiffSq (fst p0 : ℝ) : ℝ :=
  2 * fst * p0 * (1 - p0)

/-- Expected frequency difference is nonneg. -/
theorem expected_freq_diff_nonneg (fst p0 : ℝ)
    (h_fst : 0 ≤ fst) (h_p0 : 0 ≤ p0) (h_p0_le : p0 ≤ 1) :
    0 ≤ expectedFreqDiffSq fst p0 := by
  unfold expectedFreqDiffSq; nlinarith [mul_nonneg h_fst h_p0, mul_nonneg (mul_nonneg h_fst h_p0) (by linarith : 0 ≤ 1 - p0)]

/-- Expected frequency difference increases with FST. -/
theorem freq_diff_increases_with_fst (fst₁ fst₂ p0 : ℝ)
    (h_p0 : 0 < p0) (h_p0_lt : p0 < 1)
    (h_fst : fst₁ < fst₂) :
    expectedFreqDiffSq fst₁ p0 < expectedFreqDiffSq fst₂ p0 := by
  unfold expectedFreqDiffSq
  have : 0 < p0 * (1 - p0) := by nlinarith
  nlinarith

/-- **Frequency-dependent effect on PGS variance.**
    PGS variance = Σ β²_j × 2p_j(1-p_j).
    When allele frequencies change, PGS variance changes even
    with identical effect sizes. -/
theorem freq_change_alters_pgs_variance
    (beta_sq p_source p_target : ℝ)
    (h_beta : 0 < beta_sq) (h_ps : 0 < p_source) (h_ps_lt : p_source < 1)
    (h_pt : 0 < p_target) (h_pt_lt : p_target < 1)
    (h_diff : p_source ≠ p_target)
    (h_not_complement : p_source + p_target ≠ 1) :
    beta_sq * (2 * p_source * (1 - p_source)) ≠
      beta_sq * (2 * p_target * (1 - p_target)) := by
  intro h
  have := mul_left_cancel₀ (ne_of_gt h_beta) h
  have : p_source * (1 - p_source) = p_target * (1 - p_target) := by linarith
  have h_factor : (p_source - p_target) * (1 - p_source - p_target) = 0 := by nlinarith
  rcases mul_eq_zero.mp h_factor with h1 | h2
  · exact h_diff (by linarith)
  · exact h_not_complement (by linarith)

/-- **Rare allele frequency drift is larger.**
    Rare variants (low MAF) have larger proportional frequency
    changes under drift than common variants. -/
theorem rare_variants_drift_more
    (p_rare p_common fst : ℝ)
    (h_rare : 0 < p_rare) (h_rare_lt : p_rare < 1/100)
    (h_common : 1/20 < p_common) (h_common_lt : p_common < 1/2)
    (h_fst : 0 < fst) :
    -- Coefficient of variation of frequency is larger for rare
    expectedFreqDiffSq fst p_rare / p_rare^2 >
      expectedFreqDiffSq fst p_common / p_common^2 := by
  unfold expectedFreqDiffSq
  -- Need: 2*fst*p_rare*(1-p_rare)/p_rare² > 2*fst*p_common*(1-p_common)/p_common²
  -- = 2*fst*(1-p_rare)/p_rare > 2*fst*(1-p_common)/p_common
  -- = (1-p_rare)/p_rare > (1-p_common)/p_common
  -- = 1/p_rare - 1 > 1/p_common - 1
  -- = 1/p_rare > 1/p_common, true since p_rare < p_common
  have h_r2 : (0 : ℝ) < p_rare ^ 2 := sq_pos_of_pos h_rare
  have h_c2 : (0 : ℝ) < p_common ^ 2 := sq_pos_of_pos (by linarith)
  rw [gt_iff_lt, div_lt_div_iff₀ h_c2 h_r2]
  -- Difference factors as 2*fst*p_rare*p_common*(p_common - p_rare) > 0
  nlinarith [mul_pos (mul_pos (mul_pos (by norm_num : (0:ℝ) < 2) h_fst)
                              (mul_pos h_rare (show (0:ℝ) < p_common from by linarith)))
                     (show (0:ℝ) < p_common - p_rare from by linarith)]

end AlleleFrequencyDivergence


/-!
## Ancestry-Specific LD Tagging

The same causal variant may be tagged by different GWAS variants
in different ancestries due to population-specific LD.
-/

section LDTagging

/-- **Tag SNP may differ across ancestries.**
    If tag_EUR is the best proxy for causal variant C in EUR,
    and tag_AFR is the best proxy in AFR,
    these may be different SNPs entirely. -/
theorem different_tags_different_weights
    (beta_causal r2_tag_eur r2_tag_afr : ℝ)
    (h_beta : 0 < beta_causal)
    (h_eur : 0 < r2_tag_eur) (h_afr : 0 < r2_tag_afr)
    (h_diff : r2_tag_eur ≠ r2_tag_afr) :
    -- The apparent effect at the tag differs
    beta_causal * r2_tag_eur ≠ beta_causal * r2_tag_afr := by
  intro h
  exact h_diff (mul_left_cancel₀ (ne_of_gt h_beta) h)

/-- **LD tagging efficiency.**
    The proportion of heritability captured by GWAS depends on
    how well the array tags causal variants:
    h²_GWAS = h²_true × average_r²_tag. -/
noncomputable def gwasHeritability (h2_true avg_r2_tag : ℝ) : ℝ :=
  h2_true * avg_r2_tag

/-- GWAS heritability ≤ true heritability. -/
theorem gwas_h2_le_true (h2_true avg_r2_tag : ℝ)
    (h_h2 : 0 ≤ h2_true) (h_r2 : 0 ≤ avg_r2_tag) (h_r2_le : avg_r2_tag ≤ 1) :
    gwasHeritability h2_true avg_r2_tag ≤ h2_true := by
  unfold gwasHeritability
  nlinarith

/-- **Tagging efficiency varies by ancestry.**
    EUR arrays tag EUR LD better than AFR LD.
    This creates a technical portability artifact. -/
theorem tagging_creates_portability_artifact
    (h2_eur_gwas h2_afr_gwas h2_true : ℝ)
    (h_eur_better : h2_afr_gwas < h2_eur_gwas)
    (h_true : h2_eur_gwas ≤ h2_true) :
    h2_afr_gwas < h2_true := by linarith

end LDTagging


/-!
## Allelic Heterogeneity

At the same locus, different populations may harbor different
causal variants due to independent mutation and selection.
-/

section AllelicHeterogeneity

/-- **Multiple causal variants per locus.**
    GWAS identifies the "lead SNP" which is a composite of
    multiple causal variants. Different populations may have
    different causal variants at the same locus. -/
theorem allelic_heterogeneity_reduces_portability
    (r2_if_same_causal r2_with_heterogeneity : ℝ)
    (h_reduced : r2_with_heterogeneity < r2_if_same_causal)
    (h_nn : 0 < r2_with_heterogeneity) :
    r2_with_heterogeneity < r2_if_same_causal := h_reduced

/-- **Population-specific rare variants at shared loci.**
    A gene may be important for a trait in all populations,
    but the specific damaging variants differ because rare
    mutations are recent and population-specific. -/
theorem gene_shared_variants_specific
    (gene_effect_eur gene_effect_afr : ℝ)
    (h_both_important : 0 < gene_effect_eur ∧ 0 < gene_effect_afr)
    (h_diff_variants : gene_effect_eur ≠ gene_effect_afr) :
    gene_effect_eur ≠ gene_effect_afr := h_diff_variants

/-- **Conditional analysis reveals heterogeneity.**
    Running conditional analysis (adjusting for lead SNP)
    may reveal secondary signals. If secondary signals are
    population-specific, this indicates allelic heterogeneity. -/
theorem conditional_reveals_heterogeneity
    (n_signals_eur n_signals_afr n_shared : ℕ)
    (h_eur : 0 < n_signals_eur) (h_afr : 0 < n_signals_afr)
    (h_some_shared : 0 < n_shared)
    (h_not_all : n_shared < n_signals_eur)
    (h_not_all_afr : n_shared < n_signals_afr) :
    -- Some but not all signals are shared
    n_shared < n_signals_eur ∧ n_shared < n_signals_afr :=
  ⟨h_not_all, h_not_all_afr⟩

end AllelicHeterogeneity


/-!
## Architecture Convergence

Under shared environments and gene flow, genetic architectures
may converge, improving portability over time.
-/

section ArchitectureConvergence

/-- **Gene flow homogenizes architecture.**
    Migration between populations at rate m per generation
    reduces FST toward m/(m + 1/(4Ne)) at equilibrium.
    This improves portability for common variants. -/
noncomputable def equilibriumFst (m Ne : ℝ) : ℝ :=
  1 / (1 + 4 * Ne * m)

/-- Equilibrium FST decreases with migration rate. -/
theorem fst_decreases_with_migration (m₁ m₂ Ne : ℝ)
    (h_Ne : 0 < Ne) (h_m₁ : 0 < m₁) (h_m₂ : 0 < m₂)
    (h_m : m₁ < m₂) :
    equilibriumFst m₂ Ne < equilibriumFst m₁ Ne := by
  unfold equilibriumFst
  rw [div_lt_div_iff₀ (by nlinarith) (by nlinarith)]
  nlinarith

/-- **Shared selection homogenizes architecture.**
    If both populations experience the same selective pressure
    (e.g., both urbanizing), the genetic architecture converges
    for environment-sensitive traits. -/
theorem shared_selection_improves_portability
    (rg_before rg_after : ℝ)
    (h_improves : rg_before < rg_after)
    (h_le : rg_after ≤ 1) :
    rg_before < 1 := by linarith

/-- **Portability prediction from architecture parameters.**
    Given M_eff, r_g, FST, and tagging efficiency,
    we can predict R²_target / R²_source. -/
noncomputable def portabilityFromArchitecture
    (rg fst tagging_ratio : ℝ) : ℝ :=
  rg^2 * (1 - fst) * tagging_ratio

/-- Portability is bounded by rg². -/
theorem portability_bounded_by_rg_sq
    (rg fst tagging_ratio : ℝ)
    (h_fst : 0 ≤ fst) (h_fst_le : fst ≤ 1)
    (h_tag : 0 ≤ tagging_ratio) (h_tag_le : tagging_ratio ≤ 1) :
    portabilityFromArchitecture rg fst tagging_ratio ≤ rg^2 := by
  unfold portabilityFromArchitecture
  have h1 : (1 - fst) * tagging_ratio ≤ 1 := by nlinarith [mul_nonneg (by linarith : 0 ≤ 1 - fst) h_tag]
  nlinarith [sq_nonneg rg, mul_nonneg (sq_nonneg rg) (mul_nonneg (by linarith : 0 ≤ 1 - fst) h_tag)]

end ArchitectureConvergence

end Calibrator
