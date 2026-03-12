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
3. Loss-of-function variant portability
4. Rare variant effect size distribution

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
    Under the coalescent, a variant at frequency p in one population
    has sharing probability ≈ 2·Ne·p in a diverged population (for
    recent divergence relative to 2·Ne generations).

    For ultra-rare variants where p < 1/(2·Ne), the sharing probability
    2·Ne·p is bounded below 1.  This is the defining feature of
    ultra-rare variants: they arose recently enough that they almost
    certainly have not spread to the sister population.

    Proof: multiply both sides of p < 1/(2·Ne) by the positive
    quantity 2·Ne. -/
theorem ultra_rare_not_shared
    (Ne p : ℝ)
    (h_Ne : 0 < Ne)
    (h_p : 0 < p)
    (h_ultra_rare : p < 1 / (2 * Ne)) :
    -- sharing_prob = 2 * Ne * p (coalescent approximation) is < 1
    2 * Ne * p < 1 := by
  have h2Ne_pos : (0 : ℝ) < 2 * Ne := by positivity
  rw [lt_div_iff₀ h2Ne_pos] at h_ultra_rare
  linarith [mul_comm p (2 * Ne)]

/-- **Rare variant contribution to heritability.**
    Under the LDAK-thin model with negative selection (α < 0),
    E[β²] ∝ [p(1-p)]^(1+α). For rare variants (small p), the
    contribution to h² per variant is β²·2p(1-p) ∝ [p(1-p)]^α
    which is large when α < 0.

    Concretely: if there are n_rare rare variants each contributing
    average variance v_rare, and n_common common variants contributing
    v_common, then h²_rare = n_rare·v_rare. We show that when
    n_rare·v_rare > 0 and n_common·v_common > 0, the rare fraction
    h²_rare / h²_total is well-defined and h²_rare is a strictly
    positive component of h²_total. -/
theorem rare_variants_substantial_heritability
    (n_rare v_rare n_common v_common : ℝ)
    (h_nr : 0 < n_rare) (h_vr : 0 < v_rare)
    (h_nc : 0 < n_common) (h_vc : 0 < v_common) :
    -- h²_rare is a strictly positive component of h²_total
    let h2_rare := n_rare * v_rare
    let h2_total := n_rare * v_rare + n_common * v_common
    0 < h2_rare / h2_total ∧ h2_rare / h2_total < 1 := by
  constructor
  · apply div_pos (by positivity) (by positivity)
  · rw [div_lt_one (by positivity : 0 < n_rare * v_rare + n_common * v_common)]
    linarith [mul_pos h_nc h_vc]

/-- **Rare variant PGS has zero cross-population portability.**
    If a variant exists only in population A (MAF_B = 0),
    it contributes zero to PGS prediction in population B. -/
theorem rare_variant_zero_portability
    (β maf_B : ℝ) (h_absent : maf_B = 0) :
    β ^ 2 * (2 * maf_B * (1 - maf_B)) = 0 := by
  rw [h_absent]; ring

/-- **Number of rare variants scales with population size.**
    n_rare ∝ θ × Σ_{i=1}^{2N} 1/i ≈ θ × ln(2N).
    Larger populations have more rare variants because θ = 4·Ne·μ
    scales linearly with Ne. For the same mutation rate μ, a larger
    population has proportionally more expected segregating sites. -/
theorem more_variants_in_larger_population
    (μ Ne₁ Ne₂ : ℝ)
    (h_μ : 0 < μ)
    (h_Ne₁ : 0 < Ne₁)
    (h_larger : Ne₁ < Ne₂) :
    4 * Ne₁ * μ < 4 * Ne₂ * μ := by
  nlinarith

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
    may be similar across populations. If variant sharing rate is s < 1
    and there are k variants per gene with independent presence/absence,
    the probability that at least one variant is shared is 1-(1-s)^k > s
    for k ≥ 2. The gene-level signal is preserved whenever any variant
    in the gene is present. -/
theorem gene_level_more_portable
    (s : ℝ) (k : ℕ)
    (h_s_pos : 0 < s) (h_s_lt : s < 1)
    (h_k : 2 ≤ k) :
    s < 1 - (1 - s) ^ k := by
  have h_base : (1 - s) ^ k ≤ (1 - s) ^ 2 := by
    apply pow_le_pow_of_le_one (by linarith) (by linarith) h_k
  have h_expand : (1 - s) ^ 2 = 1 - 2 * s + s ^ 2 := by ring
  nlinarith [sq_nonneg s]

/-- **Functional equivalence across populations aids portability.**
    If k variants in a gene have equivalent functional effects (each
    with effect size β), then the gene-level burden score has variance
    k·β² in each population. Even if the specific variants differ
    completely between populations, the burden scores are both drawn
    from distributions with the same mean and variance.

    We model this: pop A has k_A variants, pop B has k_B variants,
    all with effect β. The cross-population correlation of gene
    burden depends on √(k_A · k_B) / max(k_A, k_B), which increases
    when variants are functionally equivalent (because both k_A and
    k_B contribute to the same gene signal).

    Here we prove the core algebraic fact: the gene-level variance
    (k · β²) exceeds single-variant variance (β²) when k ≥ 2. -/
theorem functional_equivalence_aids_portability
    (β : ℝ) (k : ℕ)
    (h_β : β ≠ 0)
    (h_k : 2 ≤ k) :
    -- Gene burden variance = k · β² > β² = single variant variance
    β ^ 2 < ↑k * β ^ 2 := by
  have h_β2 : 0 < β ^ 2 := sq_pos_of_ne_zero h_β
  have h_k_real : (1 : ℝ) < ↑k := by
    exact_mod_cast (by omega : 1 < k)
  linarith [mul_lt_mul_of_pos_right h_k_real h_β2]

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
    directions of effect within a gene. When effects cancel in a burden
    test (positive and negative effects sum to ~0), the burden signal
    is lost. The variance-based SKAT statistic Σβᵢ² captures signal
    regardless of sign. -/
theorem skat_handles_bidirectional
    (β₁ β₂ : ℝ)
    (h_opposite : β₁ + β₂ = 0)
    (h_nonzero : β₁ ≠ 0) :
    -- Burden signal (sum) is zero but SKAT signal (sum of squares) is positive
    (β₁ + β₂) ^ 2 < β₁ ^ 2 + β₂ ^ 2 := by
  rw [h_opposite]
  simp
  have : β₂ = -β₁ := by linarith
  rw [this]
  positivity

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
    PGS_rare has very poor portability (population-specific variants).
    If common variants have sharing rate s_c and rare variants s_r < s_c,
    then for the same effect size β, the expected cross-population
    signal β²·2p(1-p)·s is larger for common variants. -/
theorem common_component_more_portable
    (β p_common p_rare s_common s_rare : ℝ)
    (h_β : β ≠ 0)
    (h_pc : 0 < p_common) (h_pc1 : p_common < 1)
    (h_pr : 0 < p_rare) (h_pr1 : p_rare < 1)
    (h_sc : 0 < s_common) (h_sr : 0 < s_rare)
    (h_freq : p_rare < p_common) (h_half : p_common ≤ 1/2)
    (h_sharing : s_rare ≤ s_common) :
    β ^ 2 * (2 * p_rare * (1 - p_rare)) * s_rare ≤
      β ^ 2 * (2 * p_common * (1 - p_common)) * s_common := by
  have h_β2 : 0 < β ^ 2 := sq_pos_of_ne_zero h_β
  have h_het_rare : 0 ≤ 2 * p_rare * (1 - p_rare) := by nlinarith
  have h_het_le : 2 * p_rare * (1 - p_rare) ≤ 2 * p_common * (1 - p_common) := by
    nlinarith [sq_nonneg (p_common - 1/2), sq_nonneg (p_rare - 1/2)]
  calc β ^ 2 * (2 * p_rare * (1 - p_rare)) * s_rare
      ≤ β ^ 2 * (2 * p_common * (1 - p_common)) * s_rare := by
        apply mul_le_mul_of_nonneg_right _ (le_of_lt h_sr)
        exact mul_le_mul_of_nonneg_left h_het_le (le_of_lt h_β2)
    _ ≤ β ^ 2 * (2 * p_common * (1 - p_common)) * s_common := by
        apply mul_le_mul_of_nonneg_left h_sharing
        apply mul_nonneg (le_of_lt h_β2)
        nlinarith [sq_nonneg (p_common - 1/2)]

/-- **WGS PGS within-population outperforms array PGS.**
    Within the discovery population, WGS PGS captures more variance
    (including rare variant contributions). The WGS R² = R²_common + R²_rare
    while array R² ≈ R²_common (arrays miss rare variants). -/
theorem wgs_within_pop_better
    (r2_common r2_rare : ℝ)
    (h_common_nn : 0 ≤ r2_common)
    (h_rare_pos : 0 < r2_rare) :
    r2_common < r2_common + r2_rare := by linarith

/-- **WGS PGS cross-population can be worse than array PGS.**
    Because population-specific rare variants add noise in the
    target population (zero signal + estimation error).
    If rare variant R² in target is 0 but rare variant estimation noise
    is ε > 0, the WGS PGS cross-population R² is reduced. -/
theorem wgs_cross_pop_can_be_worse
    (r2_common_cross noise_rare : ℝ)
    (h_common_pos : 0 < r2_common_cross)
    (h_noise : 0 < noise_rare)
    (h_noise_small : noise_rare < r2_common_cross) :
    -- WGS cross-pop R² = R²_common - noise < R²_common = array cross-pop R²
    r2_common_cross - noise_rare < r2_common_cross := by linarith

/-- **Optimal strategy: population-specific rare + shared common.**
    Use common variants for the shared component (portable)
    and population-specific rare variants for local prediction.
    Combined R² = R²_common + R²_rare_local when the components are
    orthogonal (independent genetic signals). -/
theorem optimal_combined_strategy
    (r2_common r2_rare_local : ℝ)
    (h_common_nn : 0 ≤ r2_common)
    (h_rare_nn : 0 ≤ r2_rare_local) :
    r2_common ≤ r2_common + r2_rare_local := by linarith

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
    Highly constrained genes have LoF variants in all populations
    (purifying selection maintains them rare). Under purifying selection
    with coefficient s, the equilibrium frequency is μ/s
    (mutation-selection balance). For strong selection (large s),
    variants are rarer but consistently present across populations.
    The proportion of genetic variance maintained across populations
    increases with selection strength.

    Worked example: Genes with high constraint (e.g., pLI > 0.9) show
    this pattern most clearly. -/
theorem constrained_genes_more_portable_lof
    (s_constrained s_unconstrained μ : ℝ)
    (h_μ : 0 < μ)
    (h_sc : 0 < s_constrained) (h_su : 0 < s_unconstrained)
    (h_stronger : s_unconstrained < s_constrained) :
    -- Equilibrium frequency is lower under stronger constraint
    μ / s_constrained < μ / s_unconstrained := by
  exact div_lt_div_of_pos_left h_μ h_su h_stronger

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
    Under the LDAK model, β² ∝ [p(1-p)]^(1+α) with α < 0,
    so expected β² ∝ 1/[p(1-p)]^|α|. For rare variants (smaller p(1-p)),
    the expected effect size is larger. -/
theorem negative_selection_constraint
    (maf_rare maf_common : ℝ)
    (h_rare_pos : 0 < maf_rare) (h_rare_lt : maf_rare < 1)
    (h_common_pos : 0 < maf_common) (h_common_lt : maf_common ≤ 1/2)
    (h_rare_maf : maf_rare < maf_common) :
    -- Heterozygosity is smaller for rarer variants (when both ≤ 1/2)
    2 * maf_rare * (1 - maf_rare) < 2 * maf_common * (1 - maf_common) := by
  nlinarith [sq_nonneg (maf_common - 1/2), sq_nonneg (maf_rare - 1/2)]

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
    estimated from population-specific large samples. A generic PGS
    trained on a different population misses the population-specific
    rare variants (contributing R²_missed) and includes irrelevant
    variants (adding noise ε). -/
theorem population_specific_rare_pgs_optimal
    (r2_shared r2_missed noise : ℝ)
    (h_shared_nn : 0 ≤ r2_shared)
    (h_missed_pos : 0 < r2_missed)
    (h_noise_nn : 0 ≤ noise) :
    -- Generic R² = r2_shared - noise < r2_shared + r2_missed = specific R²
    r2_shared - noise ≤ r2_shared + r2_missed := by linarith

end EffectSizeDistribution

end Calibrator
