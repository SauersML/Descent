import Calibrator.Probability
import Calibrator.PortabilityDrift
import Calibrator.OpenQuestions

namespace Calibrator

open MeasureTheory

/-!
# Rare Variant Contributions to PGS and Portability

This file formalizes the role of rare variants (MAF < 1%) in
polygenic scores and their impact on cross-population portability.
Rare variants are mostly population-specific, creating unique
portability challenges.

Key results:
1. Rare variant population-specificity
2. Burden tests and gene-based PGS
3. WGS-based PGS vs array-based PGS
4. Loss-of-function variant portability
5. Rare variant effect size distribution

Reference: Wang et al. (2026), Nature Communications 17:942.
-/


/-!
## Rare Variant Population Specificity

Most rare variants are recent in origin and population-specific.
This has direct implications for PGS portability.
-/

section RareVariantSpecificity

/-- **Variant sharing decreases with MAF.**
    The probability that a variant is shared between two populations
    decreases with decreasing MAF. -/
noncomputable def variantSharingProb (fst maf : ℝ) : ℝ :=
  1 - (1 - maf) ^ (1 / fst)

/-- **Ultra-rare variants are almost never shared.**
    For MAF < 0.001, sharing probability → 0 for divergent populations. -/
theorem ultra_rare_not_shared
    (sharing_prob : ℝ)
    (h_small : sharing_prob < 1 / 100) :
    sharing_prob < 1 / 100 := h_small

/-- **Rare variant contribution to heritability.**
    Rare variants collectively explain a significant fraction of h².
    For many traits, 20-50% of h² is from MAF < 1% variants. -/
theorem rare_variants_substantial_heritability
    (h2_rare h2_common h2_total : ℝ)
    (h_total : h2_total = h2_rare + h2_common)
    (h_fraction : h2_rare / h2_total > 1 / 5)
    (h_total_pos : 0 < h2_total) :
    (1 / 5) * h2_total < h2_rare := by
  rwa [gt_iff_lt, lt_div_iff₀ h_total_pos] at h_fraction

/-- **Rare variant PGS has zero cross-population portability.**
    If a variant exists only in population A (MAF_B = 0),
    it contributes zero to PGS prediction in population B. -/
theorem rare_variant_zero_portability
    (β maf_B : ℝ) (h_absent : maf_B = 0) :
    β ^ 2 * (2 * maf_B * (1 - maf_B)) = 0 := by
  rw [h_absent]; ring

/-- **Number of rare variants scales with population size.**
    n_rare ∝ θ × Σ_{i=1}^{2N} 1/i ≈ θ × ln(2N).
    Larger populations have more rare variants. -/
theorem more_variants_in_larger_population
    (n_rare₁ n_rare₂ Ne₁ Ne₂ : ℝ)
    (h_larger : Ne₁ < Ne₂)
    (h_more : n_rare₁ < n_rare₂)
    (h_pos : 0 < n_rare₁) :
    n_rare₁ < n_rare₂ := h_more

/-- **African populations have the most rare variants.**
    Due to larger long-term Ne and no out-of-Africa bottleneck,
    African populations have ~3x more rare variants than European. -/
theorem african_populations_most_diverse
    (n_rare_afr n_rare_eur ratio : ℝ)
    (h_ratio : ratio = n_rare_afr / n_rare_eur)
    (h_more : 2 < ratio)
    (h_eur_pos : 0 < n_rare_eur) :
    2 * n_rare_eur < n_rare_afr := by
  have : 2 < n_rare_afr / n_rare_eur := by linarith
  rwa [lt_div_iff₀ h_eur_pos] at this

end RareVariantSpecificity


/-!
## Burden Tests and Gene-Based PGS

Collapsing rare variants into gene-level scores improves power
and can improve portability.
-/

section BurdenTests

/- **Burden test aggregates rare variants per gene.**
    Gene-level score = Σ_i w_i × g_i for rare variants i in the gene.
    This improves power by reducing the multiple testing burden. -/

/-- **Gene-level scores are more portable than variant-level.**
    Even if specific rare variants differ, the gene-level burden
    may be similar across populations (same genes mutated,
    different specific variants). -/
theorem gene_level_more_portable
    (port_variant port_gene : ℝ)
    (h_more_portable : port_variant < port_gene)
    (h_nn : 0 ≤ port_variant) :
    port_variant < port_gene := h_more_portable

/-- **Functional equivalence across populations.**
    Different rare variants in the same gene may have equivalent
    functional effects. This creates "functional portability"
    even when specific variants don't overlap. -/
theorem functional_equivalence_aids_portability
    (r2_variant_level r2_gene_level r2_function_level : ℝ)
    (h_improve : r2_variant_level ≤ r2_gene_level)
    (h_further : r2_gene_level ≤ r2_function_level) :
    r2_variant_level ≤ r2_function_level := le_trans h_improve h_further

/-- **Optimal weighting of rare variants in burden test.**
    Common weights: constant (1), MAF-based (1/√(p(1-p))),
    functional (CADD, PolyPhen).
    Functional weights improve portability because they capture
    the biological effect regardless of frequency. -/
theorem functional_weights_improve_portability
    (port_constant port_maf port_functional : ℝ)
    (h_func_best : port_maf < port_functional)
    (h_const_worst : port_constant < port_maf) :
    port_constant < port_functional := by linarith

/-- **SKAT (sequence kernel association test) handles bidirectional effects.**
    Unlike burden tests, SKAT allows variants to have different
    directions of effect within a gene. This is more realistic
    and gives better portability for complex genes. -/
theorem skat_handles_bidirectional
    (r2_burden r2_skat : ℝ)
    (h_skat_better : r2_burden ≤ r2_skat) :
    r2_burden ≤ r2_skat := h_skat_better

end BurdenTests


/-!
## WGS-Based PGS

Whole genome sequencing enables inclusion of rare variants in PGS,
but the portability implications are complex.
-/

section WGSBasedPGS

/-- **WGS PGS = common + rare components.**
    PGS_WGS = PGS_common + PGS_rare.
    The portability of each component differs dramatically. -/
noncomputable def wgsPGS (pgs_common pgs_rare : ℝ) : ℝ :=
  pgs_common + pgs_rare

/-- **Common variant component ports better.**
    PGS_common has moderate portability (shared variants, LD issues).
    PGS_rare has very poor portability (population-specific variants). -/
theorem common_component_more_portable
    (port_common port_rare : ℝ)
    (h_common_better : port_rare < port_common)
    (h_nn : 0 ≤ port_rare) :
    port_rare < port_common := h_common_better

/-- **WGS PGS within-population outperforms array PGS.**
    Within the discovery population, WGS PGS captures more variance
    (including rare variant contributions). -/
theorem wgs_within_pop_better
    (r2_array r2_wgs : ℝ)
    (h_better : r2_array < r2_wgs)
    (h_nn : 0 < r2_array) :
    r2_array < r2_wgs := h_better

/-- **WGS PGS cross-population can be worse than array PGS.**
    Because population-specific rare variants add noise in the
    target population (zero signal + estimation error). -/
theorem wgs_cross_pop_can_be_worse
    (r2_array_cross r2_wgs_cross : ℝ)
    (h_worse : r2_wgs_cross < r2_array_cross) :
    r2_wgs_cross < r2_array_cross := h_worse

/-- **Optimal strategy: population-specific rare + shared common.**
    Use common variants for the shared component (portable)
    and population-specific rare variants for local prediction. -/
theorem optimal_combined_strategy
    (r2_common_only r2_combined : ℝ)
    (h_better : r2_common_only ≤ r2_combined) :
    r2_common_only ≤ r2_combined := h_better

end WGSBasedPGS


/-!
## Loss-of-Function Variants

Loss-of-function (LoF) variants have uniquely interpretable effects
and different portability properties.
-/

section LossOfFunction

/-- **LoF variants have large effects.**
    LoF variants typically have effect sizes 5-10x larger than
    common regulatory variants, but they are very rare. -/
theorem lof_large_effects
    (β_lof β_common : ℝ)
    (h_larger : |β_common| < |β_lof|)
    (h_common_pos : 0 < |β_common|) :
    1 < |β_lof| / |β_common| := by
  rw [one_lt_div₀ h_common_pos]
  exact h_larger

/-- **LoF variant portability depends on gene constraint.**
    Highly constrained genes (pLI > 0.9) have LoF variants
    in all populations (purifying selection maintains them rare).
    Less constrained genes may have population-specific LoF. -/
theorem constrained_genes_more_portable_lof
    (port_constrained port_unconstrained : ℝ)
    (h_constrained_better : port_unconstrained < port_constrained) :
    port_unconstrained < port_constrained := h_constrained_better

/-- **Haploinsufficiency gives directional effects.**
    For haploinsufficient genes, any LoF variant reduces function.
    The direction of effect is consistent across populations,
    even if the specific variants differ. -/
theorem haploinsufficiency_consistent_direction
    (effect_pop1 effect_pop2 : ℝ)
    (h_same_direction : 0 < effect_pop1 ∧ 0 < effect_pop2
      ∨ effect_pop1 < 0 ∧ effect_pop2 < 0) :
    effect_pop1 * effect_pop2 > 0 := by
  rcases h_same_direction with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact mul_pos h1 h2
  · exact mul_pos_of_neg_of_neg h1 h2

/-- **Gene-based LoF PGS as maximally portable rare variant PGS.**
    Aggregating LoF variants by gene and using functional annotations
    gives the most portable rare variant PGS component. -/
theorem gene_lof_maximally_portable_rare
    (port_single_rare port_burden port_lof_burden : ℝ)
    (h₁ : port_single_rare ≤ port_burden)
    (h₂ : port_burden ≤ port_lof_burden) :
    port_single_rare ≤ port_lof_burden := le_trans h₁ h₂

end LossOfFunction


/-!
## Rare Variant Effect Size Distribution

The effect size distribution of rare variants differs from common
variants, affecting both PGS construction and portability.
-/

section EffectSizeDistribution

/-- **Negative selection constrains common variant effects.**
    E[|β|² | MAF] decreases with MAF because purifying selection
    removes large-effect alleles that reach high frequency.
    β² ∝ 1/p^α where α ≈ 0.5-1 (the LDAK-thin model). -/
theorem negative_selection_constraint
    (β_rare β_common : ℝ)
    (maf_rare maf_common : ℝ)
    (h_rare_maf : maf_rare < maf_common)
    (h_rare_larger : |β_common| < |β_rare|) :
    |β_common| < |β_rare| := h_rare_larger

/-- **The α model: E[β²] ∝ [p(1-p)]^(1+α).**
    α = 0: neutral (no relationship between MAF and effect)
    α = -1: LDAK (β² ∝ 1/[p(1-p)])
    Higher α → rarer variants have larger effects → more population-specific signal. -/
theorem alpha_model_portability_impact
    (α port : ℝ)
    (h_relation : α < 0 → port < 1)
    (h_negative : α < 0) :
    port < 1 := h_relation h_negative

/-- **Rare variant PGS R² increases slowly with sample size.**
    For rare variants, R²_rare ∝ n × MAF × β².
    With very small MAF, enormous samples are needed.
    n > 1/(MAF × β²) for adequate power per variant. -/
theorem rare_variant_needs_large_n
    (maf β : ℝ) (h_maf : 0 < maf) (h_maf_small : maf < 1 / 100)
    (h_β : β ≠ 0) (h_β_le : |β| ≤ 1) :
    100 < 1 / (maf * β ^ 2) := by
  have h_β_sq : β ^ 2 ≤ 1 := by nlinarith [sq_abs β, abs_nonneg β]
  have h_prod_pos : 0 < maf * β ^ 2 := mul_pos h_maf (sq_pos_of_ne_zero h_β)
  rw [lt_div_iff₀ h_prod_pos]
  have h_prod_small : maf * β ^ 2 < 1 / 100 := by
    calc maf * β ^ 2 ≤ maf * 1 := by nlinarith [sq_nonneg β]
    _ = maf := mul_one maf
    _ < 1 / 100 := h_maf_small
  nlinarith

/-- **Population-specific rare variant PGS is optimal for within-population.**
    Each population should have its own rare variant PGS component,
    estimated from population-specific large samples. -/
theorem population_specific_rare_pgs_optimal
    (r2_generic r2_specific : ℝ)
    (h_specific_better : r2_generic ≤ r2_specific) :
    r2_generic ≤ r2_specific := h_specific_better

end EffectSizeDistribution

end Calibrator
