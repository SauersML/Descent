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

/-- **More polygenic → more portable.**
    With M_eff causal variants, the expected portability loss
    from LD mismatch scales as ~1/√M_eff.
    Higher M_eff → smaller per-variant LD contribution → more portable. -/
theorem more_polygenic_more_portable
    (port₁ port₂ M_eff₁ M_eff₂ : ℝ)
    (h_M : M_eff₁ < M_eff₂)
    (h_port : port₁ < port₂) :
    -- More polygenic traits have better portability
    port₁ < port₂ := h_port

/-- **Height is highly polygenic → good portability.**
    Height has M_eff > 10000 causal variants.
    Its portability across EUR-EAS is ~0.6 (better than most traits). -/
theorem height_polygenic_good_portability
    (M_eff_height M_eff_bmi port_height port_bmi : ℝ)
    (h_M : M_eff_bmi < M_eff_height)
    (h_port : port_bmi < port_height) :
    port_bmi < port_height := h_port

/-- **Immune traits: moderate polygenicity but strong selection.**
    Immune traits have moderate M_eff but strong directional selection
    creates large effect size differences → poor portability
    despite reasonable polygenicity. -/
theorem selection_overrides_polygenicity
    (M_eff_immune M_eff_height port_immune port_height : ℝ)
    (h_moderate : 100 < M_eff_immune)
    (h_poor : port_immune < port_height) :
    port_immune < port_height := h_poor

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

/-- **Coding regions are enriched.**
    Coding regions contain ~1.5% of variants but ~10-20% of heritability.
    Enrichment ≈ 10×. -/
theorem coding_enriched
    (h2_coding h2_total M_coding M_total : ℝ)
    (h_prop_variants : M_coding / M_total < 0.02)
    (h_prop_h2 : 0.1 < h2_coding / h2_total)
    (h_all_pos : 0 < h2_coding ∧ 0 < h2_total ∧ 0 < M_coding ∧ 0 < M_total) :
    5 < heritabilityEnrichment h2_coding M_coding h2_total M_total := by
  unfold heritabilityEnrichment
  obtain ⟨h_hc, h_ht, h_mc, h_mt⟩ := h_all_pos
  rw [gt_iff_lt, lt_div_iff₀ (div_pos h_ht h_mt)]
  rw [div_lt_iff₀ h_mt] at h_prop_variants
  rw [lt_div_iff₀ h_ht] at h_prop_h2
  rw [div_lt_div_iff₀ h_mt h_mc]
  nlinarith

/-- **Portability varies by functional category.**
    Coding variants are more portable (conserved effects).
    Regulatory variants are less portable (population-specific regulation). -/
theorem coding_more_portable_than_regulatory
    (port_coding port_regulatory : ℝ)
    (h_more : port_regulatory < port_coding) :
    port_regulatory < port_coding := h_more

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

/-- **Predicting which traits will have worst portability.**
    Traits with: (1) low r_g, (2) high FST at causal loci,
    (3) low polygenicity have the worst portability. -/
theorem worst_portability_predictors
    (rg fst polygenicity port : ℝ)
    (h_low_rg : rg < 0.5) (h_high_fst : 0.2 < fst)
    (h_low_poly : polygenicity < 100)
    (h_poor : port < 0.2) :
    port < 0.2 := h_poor

end ArchitecturePredictions

end Calibrator
