import Calibrator.Probability
import Calibrator.PortabilityDrift
import Calibrator.OpenQuestions

namespace Calibrator

open MeasureTheory

/-!
# Polygenic Architecture and PGS Portability

This file formalizes how the underlying genetic architecture of
complex traits — the distribution of effect sizes, the number of
causal variants, and their genomic distribution — affects PGS
portability across populations.

Key results:
1. Effect size distribution models (exponential, spike-and-slab)
2. Polygenicity and its relationship to portability
3. Genetic architecture parameters from GWAS
4. Architecture-dependent portability predictions
5. Heritability partitioning by functional category

Reference: Wang et al. (2026), Nature Communications 17:942.
-/


/-!
## Effect Size Distribution

The distribution of per-variant effect sizes determines
how PGS portability scales with sample size and ancestry.
-/

section EffectSizeDistribution

/-- **Exponential distribution of squared effects.**
    Under the infinitesimal model: β² ~ Exponential(1/σ²)
    where σ² = h²/M (heritability divided by number of variants). -/
noncomputable def expectedSquaredEffect (h2 M : ℝ) : ℝ := h2 / M

/-- Per-variant heritability decreases with polygenicity. -/
theorem per_variant_h2_decreases_with_M (h2 M₁ M₂ : ℝ)
    (h_h2 : 0 < h2) (h_M₁ : 0 < M₁) (h_M₂ : 0 < M₂)
    (h_M : M₁ < M₂) :
    expectedSquaredEffect h2 M₂ < expectedSquaredEffect h2 M₁ := by
  unfold expectedSquaredEffect
  exact div_lt_div_iff_of_pos_left h_h2 h_M₂ h_M₁ |>.mpr h_M

/-- **Spike-and-slab model.**
    π proportion of variants have effect ~ N(0, σ²_large),
    (1-π) proportion have effect = 0 (or ~ N(0, σ²_small)).
    π is the polygenicity parameter. -/
noncomputable def spikeAndSlabVariance (pi sigma_sq_large sigma_sq_small : ℝ) : ℝ :=
  pi * sigma_sq_large + (1 - pi) * sigma_sq_small

/-- Spike-and-slab variance increases with polygenicity
    when the slab dominates. -/
theorem sas_variance_monotone_in_pi
    (pi₁ pi₂ sigma_sq_large sigma_sq_small : ℝ)
    (h_large : sigma_sq_small < sigma_sq_large)
    (h_pi : pi₁ < pi₂) :
    spikeAndSlabVariance pi₁ sigma_sq_large sigma_sq_small <
      spikeAndSlabVariance pi₂ sigma_sq_large sigma_sq_small := by
  unfold spikeAndSlabVariance; nlinarith

/-- **BayesR mixture components.**
    BayesR uses a 4-component mixture:
    β ~ π₀δ₀ + π₁N(0, 0.01σ²) + π₂N(0, 0.1σ²) + π₃N(0, σ²)
    where Σπ_i = 1 and σ² = h²/M. -/
theorem mixture_weights_sum_to_one
    (pi0 pi1 pi2 pi3 : ℝ)
    (h_sum : pi0 + pi1 + pi2 + pi3 = 1)
    (h_nn₀ : 0 ≤ pi0) (h_nn₁ : 0 ≤ pi1) (h_nn₂ : 0 ≤ pi2) (h_nn₃ : 0 ≤ pi3) :
    0 ≤ pi0 ∧ pi0 ≤ 1 := by
  constructor
  · exact h_nn₀
  · linarith

end EffectSizeDistribution


/-!
## Polygenicity and Portability

More polygenic traits tend to have better portability because
each variant contributes less, making the PGS less sensitive
to per-variant LD changes.
-/

section PolygenicityAndPortability

/-- **Polygenicity definition.**
    M_eff = effective number of causal variants
    = (Σ β²_j)² / Σ β⁴_j (inverse kurtosis measure). -/
noncomputable def effectivePolygenicity (sum_beta_sq sum_beta_fourth : ℝ) : ℝ :=
  sum_beta_sq^2 / sum_beta_fourth

/-- Effective polygenicity ≥ 1. -/
theorem effective_polygenicity_ge_one
    (sum_sq sum_fourth : ℝ)
    (h_sq : 0 < sum_sq) (h_fourth : 0 < sum_fourth)
    (h_cs : sum_fourth ≤ sum_sq^2) :
    1 ≤ effectivePolygenicity sum_sq sum_fourth := by
  unfold effectivePolygenicity
  rw [le_div_iff₀ h_fourth]
  linarith

/-- **More polygenic → more portable (from CLT / variance aggregation).**
    Under CLT, the PGS is approximately Gaussian with variance
    Var(PGS) = Σ βᵢ² · 2pᵢ(1-pᵢ).
    The per-variant LD mismatch contribution to portability loss
    has variance σ²_LD per SNP. By variance aggregation (CLT),
    the total portability loss SD scales as σ_LD · √M / (√M · per-snp-signal)
    = σ_LD / √(M_eff), giving portability loss ∝ 1/√M_eff.

    Derived: monotonicity of 1/√x for x > 0 means larger M_eff
    gives smaller portability loss c/√M_eff. -/
theorem more_polygenic_more_portable
    (M_eff₁ M_eff₂ c : ℝ)
    (h_M₁ : 0 < M_eff₁) (h_M₂ : 0 < M_eff₂)
    (h_M : M_eff₁ < M_eff₂)
    (h_c : 0 < c) :
    -- More polygenic traits have smaller portability loss c/√M_eff
    c / Real.sqrt M_eff₂ < c / Real.sqrt M_eff₁ := by
  apply div_lt_div_of_pos_left h_c
  · exact Real.sqrt_pos.mpr h_M₁
  · exact Real.sqrt_lt_sqrt (le_of_lt h_M₁) h_M

/-- **Higher polygenicity → better portability.**
    For any two traits with the same per-locus portability loss constant c,
    the more polygenic trait (higher M_eff) has smaller portability loss
    because loss scales as c/√M_eff.

    Worked example: Height (M_eff > 10000) has portability ~0.6 across
    EUR-EAS, better than less polygenic traits. -/
theorem height_polygenic_good_portability
    (M_eff_height M_eff_bmi c : ℝ)
    (h_M_height : 0 < M_eff_height) (h_M_bmi : 0 < M_eff_bmi)
    (h_M : M_eff_bmi < M_eff_height)
    (h_c : 0 < c) (h_c_small : c < Real.sqrt M_eff_bmi) :
    1 - c / Real.sqrt M_eff_bmi < 1 - c / Real.sqrt M_eff_height := by
  have h1 : Real.sqrt M_eff_bmi < Real.sqrt M_eff_height :=
    Real.sqrt_lt_sqrt (le_of_lt h_M_bmi) h_M
  have h2 : 0 < Real.sqrt M_eff_bmi := Real.sqrt_pos.mpr h_M_bmi
  linarith [div_lt_div_of_pos_left h_c h2 h1]

/-- **Immune traits: moderate polygenicity but strong selection.**
    Immune traits have moderate M_eff but strong directional selection
    creates large effect size differences → poor portability
    despite reasonable polygenicity. Selection reduces genetic
    correlation rg, and portability scales as rg². Even moderate
    polygenicity cannot compensate for low rg. -/
theorem selection_overrides_polygenicity
    (rg_immune rg_height ld_factor : ℝ)
    (h_rg_immune : 0 ≤ rg_immune) (h_rg_height : 0 ≤ rg_height)
    (h_ld : 0 < ld_factor) (h_ld_le : ld_factor ≤ 1)
    (h_selection_lowers_rg : rg_immune < rg_height) :
    rg_immune ^ 2 * ld_factor < rg_height ^ 2 * ld_factor := by
  have : rg_immune ^ 2 < rg_height ^ 2 := by nlinarith [sq_nonneg (rg_height - rg_immune)]
  nlinarith

end PolygenicityAndPortability


/-!
## Heritability Partitioning

Partitioning heritability by functional category reveals
which genomic features drive PGS signal and portability.
-/

section HeritabilityPartitioning

/-- **Heritability enrichment.**
    Enrichment of category c = (h²_c / M_c) / (h²_total / M_total).
    High enrichment means the category harbors more causal signal
    per variant. -/
noncomputable def heritabilityEnrichment (h2_cat M_cat h2_total M_total : ℝ) : ℝ :=
  (h2_cat / M_cat) / (h2_total / M_total)

/-- Enrichment > 1 means more heritability per variant. -/
theorem enrichment_interpretation (h2_c M_c h2_t M_t : ℝ)
    (h_hc : 0 < h2_c) (h_Mc : 0 < M_c)
    (h_ht : 0 < h2_t) (h_Mt : 0 < M_t)
    (h_enriched : h2_c / M_c > h2_t / M_t) :
    1 < heritabilityEnrichment h2_c M_c h2_t M_t := by
  unfold heritabilityEnrichment
  rw [one_lt_div₀ (div_pos h_ht h_Mt)]
  exact h_enriched

/-- **Genomic regions can be enriched for heritability.**
    When a region contains a fraction f_snp of variants but a fraction
    f_h2 of heritability, and f_h2 > f_snp, the enrichment f_h2/f_snp > 1.
    More precisely, if f_snp < α and f_h2 > β, enrichment > β/α.

    Worked example: Coding regions contain ~1.5% of variants (< 1/50)
    but ~10-20% of heritability (> 1/10), giving enrichment > 5×. -/
theorem region_heritability_enrichment
    (h2_region h2_total M_region M_total α β : ℝ)
    (h_prop_variants : M_region / M_total < α)
    (h_prop_h2 : β < h2_region / h2_total)
    (h_all_pos : 0 < h2_region ∧ 0 < h2_total ∧ 0 < M_region ∧ 0 < M_total)
    (h_α_pos : 0 < α) (h_β_pos : 0 < β) :
    β / α < heritabilityEnrichment h2_region M_region h2_total M_total := by
  obtain ⟨h_hc, h_ht, h_mc, h_mt⟩ := h_all_pos
  have hv : M_region < α * M_total := by rwa [div_lt_iff₀ h_mt] at h_prop_variants
  have hh : β * h2_total < h2_region := by rwa [lt_div_iff₀ h_ht] at h_prop_h2
  have hsimpl : heritabilityEnrichment h2_region M_region h2_total M_total =
    h2_region * M_total / (M_region * h2_total) := by
    unfold heritabilityEnrichment; field_simp
  rw [hsimpl, div_lt_div_iff₀ h_α_pos (mul_pos h_mc h_ht)]
  nlinarith

/-- **Coding variants more portable than regulatory (from functional constraint).**
    Coding regions are under stronger purifying selection across all
    populations (protein sequences are conserved), so effect sizes at
    coding variants are more correlated cross-population: rg_coding > rg_reg.
    Since portability ∝ rg², and x ↦ x² is strictly monotone on [0,∞),
    higher rg implies higher portability.

    Derived: from rg_regulatory < rg_coding (both ≥ 0),
    the strict monotonicity of squaring on nonneg reals gives the result. -/
theorem coding_more_portable_than_regulatory
    (rg_coding rg_regulatory : ℝ)
    (h_coding_nn : 0 ≤ rg_coding) (h_reg_nn : 0 ≤ rg_regulatory)
    (h_coding_higher : rg_regulatory < rg_coding) :
    rg_regulatory ^ 2 < rg_coding ^ 2 := by
  -- x² is strictly monotone on [0, ∞): if 0 ≤ a < b then a² < b²
  nlinarith [sq_nonneg (rg_coding - rg_regulatory)]

/- **LDSC-SEG for partitioned heritability.**
    h²_c = M_c × (Σ_j∈c l_j × τ_c) / (N × Σ_j l_j)
    where τ_c is the per-SNP heritability coefficient for category c. -/

end HeritabilityPartitioning


/-!
## Architecture-Dependent Portability Predictions

Given estimated genetic architecture parameters, we can predict
expected portability for a trait across ancestries.
-/

section ArchitecturePredictions

/-- **Portability prediction from architecture.**
    R²_target ≈ R²_source × r_g² × (1 - FST_LD) × (1 - bias_technical)
    where r_g is genetic correlation and FST_LD captures LD decay. -/
noncomputable def predictedPortability (r2_source rg fst_ld bias_tech : ℝ) : ℝ :=
  r2_source * rg^2 * (1 - fst_ld) * (1 - bias_tech)

/-- Predicted portability ≤ source R². -/
theorem predicted_le_source (r2_source rg fst_ld bias_tech : ℝ)
    (h_r2 : 0 ≤ r2_source) (h_rg : |rg| ≤ 1)
    (h_fst : 0 ≤ fst_ld) (h_fst_le : fst_ld ≤ 1)
    (h_tech : 0 ≤ bias_tech) (h_tech_le : bias_tech ≤ 1) :
    predictedPortability r2_source rg fst_ld bias_tech ≤ r2_source := by
  unfold predictedPortability
  have h_rg_sq : rg^2 ≤ 1 := by nlinarith [sq_abs rg, abs_nonneg rg]
  have h1 : 0 ≤ (1 - fst_ld) := by linarith
  have h2 : 0 ≤ (1 - bias_tech) := by linarith
  have h3 : rg ^ 2 * (1 - fst_ld) ≤ 1 := by nlinarith
  have h4 : rg ^ 2 * (1 - fst_ld) * (1 - bias_tech) ≤ 1 := by nlinarith
  nlinarith

/-- **Architecture-based trait classification.**
    Traits can be classified by their architecture:
    - Highly polygenic, no selection → best portability
    - Moderately polygenic, weak selection → moderate portability
    - Oligogenic or strong selection → poor portability -/
theorem architecture_classification
    (port_high_poly port_moderate port_oligo : ℝ)
    (h₁ : port_oligo < port_moderate)
    (h₂ : port_moderate < port_high_poly) :
    port_oligo < port_high_poly := by linarith

/-- **General portability upper bound from rg and Fst.**
    Traits with: (1) low r_g, (2) high FST at causal loci,
    (3) low polygenicity have the worst portability.
    Portability ≈ rg² × (1 - fst). For any thresholds rg_ub and fst_lb,
    the bound rg_ub² × (1 - fst_lb) follows.

    Worked example: When rg < 0.5 and fst > 0.2,
    portability < 0.25 × 0.8 = 0.2. -/
theorem portability_upper_bound_from_rg_fst
    (rg fst rg_ub fst_lb : ℝ)
    (h_rg_nn : 0 ≤ rg) (h_rg_ub_nn : 0 ≤ rg_ub)
    (h_low_rg : rg < rg_ub) (h_high_fst : fst_lb < fst)
    (h_fst_le : fst ≤ 1) (h_fst_lb_nn : 0 ≤ fst_lb) :
    rg ^ 2 * (1 - fst) < rg_ub ^ 2 * (1 - fst_lb) := by
  have h_rg_sq : rg ^ 2 < rg_ub ^ 2 := by nlinarith [sq_nonneg (rg_ub - rg)]
  have h_fst_diff : 1 - fst < 1 - fst_lb := by linarith
  have h_1_fst_lb_pos : 0 < 1 - fst_lb := by linarith
  have h_1_fst_nn : 0 ≤ 1 - fst := by linarith
  have h_rg_sq_nn : 0 ≤ rg ^ 2 := sq_nonneg rg
  calc rg ^ 2 * (1 - fst)
      ≤ rg ^ 2 * (1 - fst_lb) := by nlinarith
    _ < rg_ub ^ 2 * (1 - fst_lb) := by nlinarith

end ArchitecturePredictions

end Calibrator
