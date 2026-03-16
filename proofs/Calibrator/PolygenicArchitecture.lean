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

/-- **CLT-based portability model for polygenic traits.**
    `M_eff` is the effective number of approximately independent causal loci.
    `perLocusSignal` is the mean signal contribution per locus, and
    `perLocusMismatchSD` is the standard deviation of the per-locus LD-mismatch
    contribution. Under variance aggregation, total mismatch SD grows like `√M_eff`
    while total signal grows like `M_eff`. -/
structure PolygenicCLTPortabilityModel where
  M_eff : ℝ
  perLocusSignal : ℝ
  perLocusMismatchSD : ℝ

namespace PolygenicCLTPortabilityModel

/-- Aggregate signal scales linearly with the effective number of loci. -/
def aggregateSignal (model : PolygenicCLTPortabilityModel) : ℝ :=
  model.M_eff * model.perLocusSignal

/-- Independent per-locus mismatch contributions aggregate with `√M_eff` scaling. -/
noncomputable def aggregateMismatchSD (model : PolygenicCLTPortabilityModel) : ℝ :=
  Real.sqrt model.M_eff * model.perLocusMismatchSD

/-- Relative portability loss is mismatch SD divided by aggregate signal. -/
noncomputable def relativePortabilityLoss (model : PolygenicCLTPortabilityModel) : ℝ :=
  model.aggregateMismatchSD / model.aggregateSignal

/-- The part of the loss scale that does not depend on `M_eff`. -/
noncomputable def lossConstant (model : PolygenicCLTPortabilityModel) : ℝ :=
  model.perLocusMismatchSD / model.perLocusSignal

/-- A simple portability score obtained by subtracting relative loss from `1`. -/
noncomputable def portabilityScore (model : PolygenicCLTPortabilityModel) : ℝ :=
  1 - model.relativePortabilityLoss

@[simp] theorem portabilityScore_eq_one_sub_relativePortabilityLoss
    (model : PolygenicCLTPortabilityModel) :
    model.portabilityScore = 1 - model.relativePortabilityLoss := by
  rfl

/-- The `1 / √M_eff` loss law is derived from the CLT scaling assumptions above,
    not assumed as a theorem premise. -/
theorem relativePortabilityLoss_eq_lossConstant_div_sqrt
    (model : PolygenicCLTPortabilityModel)
    (h_M : 0 < model.M_eff)
    (h_signal : 0 < model.perLocusSignal) :
    model.relativePortabilityLoss = model.lossConstant / Real.sqrt model.M_eff := by
  unfold relativePortabilityLoss aggregateMismatchSD aggregateSignal lossConstant
  have h_sqrt_ne : Real.sqrt model.M_eff ≠ 0 := Real.sqrt_ne_zero'.mpr h_M
  have h_signal_ne : model.perLocusSignal ≠ 0 := h_signal.ne'
  calc
    (Real.sqrt model.M_eff * model.perLocusMismatchSD) / (model.M_eff * model.perLocusSignal)
      = (Real.sqrt model.M_eff * model.perLocusMismatchSD) /
          ((Real.sqrt model.M_eff * Real.sqrt model.M_eff) * model.perLocusSignal) := by
            congr 1
            nlinarith [Real.sq_sqrt (le_of_lt h_M)]
    _ = (model.perLocusMismatchSD / model.perLocusSignal) / Real.sqrt model.M_eff := by
          field_simp [h_sqrt_ne, h_signal_ne]

end PolygenicCLTPortabilityModel

/-- Portability score from the CLT portability model, written directly in terms of the
    effective number of loci and per-locus parameters. -/
noncomputable def cltPolygenicPortabilityScore
    (M_eff perLocusSignal perLocusMismatchSD : ℝ) : ℝ :=
  let model : PolygenicCLTPortabilityModel :=
    { M_eff := M_eff
      perLocusSignal := perLocusSignal
      perLocusMismatchSD := perLocusMismatchSD }
  model.portabilityScore

/-- Overall portability after multiplying the polygenicity-only score by a
    cross-population effect-correlation penalty `rg²` and an LD-retention factor. -/
noncomputable def selectionAdjustedPortability
    (model : PolygenicCLTPortabilityModel) (rg ld_factor : ℝ) : ℝ :=
  ld_factor * (rg ^ 2 * model.portabilityScore)

@[simp] theorem selectionAdjustedPortability_eq_formula
    (model : PolygenicCLTPortabilityModel) (rg ld_factor : ℝ) :
    selectionAdjustedPortability model rg ld_factor =
      ld_factor * (rg ^ 2 * model.portabilityScore) := by
  rfl

/-- **More polygenic → more portable (from the formal CLT model).**
    If two traits share the same per-locus signal and per-locus LD-mismatch scale,
    then the trait with larger `M_eff` has smaller relative portability loss because
    aggregate mismatch grows like `√M_eff` while aggregate signal grows like `M_eff`. -/
theorem more_polygenic_more_portable
    (model₁ model₂ : PolygenicCLTPortabilityModel)
    (h_M₁ : 0 < model₁.M_eff) (h_M₂ : 0 < model₂.M_eff)
    (h_M : model₁.M_eff < model₂.M_eff)
    (h_signal : 0 < model₁.perLocusSignal)
    (h_mismatch : 0 < model₁.perLocusMismatchSD)
    (h_same_signal : model₁.perLocusSignal = model₂.perLocusSignal)
    (h_same_mismatch : model₁.perLocusMismatchSD = model₂.perLocusMismatchSD) :
    model₂.relativePortabilityLoss < model₁.relativePortabilityLoss := by
  rw [PolygenicCLTPortabilityModel.relativePortabilityLoss_eq_lossConstant_div_sqrt
      model₂ h_M₂]
  · rw [PolygenicCLTPortabilityModel.relativePortabilityLoss_eq_lossConstant_div_sqrt
      model₁ h_M₁ h_signal]
    unfold PolygenicCLTPortabilityModel.lossConstant
    rw [← h_same_signal, ← h_same_mismatch]
    have h_const_pos : 0 < model₁.perLocusMismatchSD / model₁.perLocusSignal := by
      exact div_pos h_mismatch h_signal
    exact div_lt_div_of_pos_left h_const_pos
      (Real.sqrt_pos.mpr h_M₁)
      (Real.sqrt_lt_sqrt (le_of_lt h_M₁) h_M)
  · simpa [h_same_signal] using h_signal

/-- **Higher polygenicity → better portability.**
    For two traits with the same per-locus signal and LD-mismatch scale, the more
    polygenic trait has the higher CLT portability score because its derived
    relative loss is smaller. -/
theorem height_polygenic_good_portability
    (M_eff_height M_eff_bmi perLocusSignal perLocusMismatchSD : ℝ)
    (h_M_height : 0 < M_eff_height) (h_M_bmi : 0 < M_eff_bmi)
    (h_M : M_eff_bmi < M_eff_height)
    (h_signal : 0 < perLocusSignal)
    (h_mismatch : 0 < perLocusMismatchSD) :
    cltPolygenicPortabilityScore M_eff_bmi perLocusSignal perLocusMismatchSD <
      cltPolygenicPortabilityScore M_eff_height perLocusSignal perLocusMismatchSD := by
  let bmiModel : PolygenicCLTPortabilityModel :=
    { M_eff := M_eff_bmi
      perLocusSignal := perLocusSignal
      perLocusMismatchSD := perLocusMismatchSD }
  let heightModel : PolygenicCLTPortabilityModel :=
    { M_eff := M_eff_height
      perLocusSignal := perLocusSignal
      perLocusMismatchSD := perLocusMismatchSD }
  have h_loss :
      heightModel.relativePortabilityLoss < bmiModel.relativePortabilityLoss := by
    exact more_polygenic_more_portable
      bmiModel heightModel h_M_bmi h_M_height h_M h_signal h_mismatch rfl rfl
  dsimp [cltPolygenicPortabilityScore, bmiModel, heightModel] at ⊢
  rw [PolygenicCLTPortabilityModel.portabilityScore_eq_one_sub_relativePortabilityLoss,
    PolygenicCLTPortabilityModel.portabilityScore_eq_one_sub_relativePortabilityLoss]
  linarith

/-- The CLT portability score has the explicit closed form
    `1 - lossConstant / √M_eff`. -/
theorem PolygenicCLTPortabilityModel.portabilityScore_eq_one_sub_lossConstant_div_sqrt
    (model : PolygenicCLTPortabilityModel)
    (h_M : 0 < model.M_eff)
    (h_signal : 0 < model.perLocusSignal) :
    model.portabilityScore = 1 - model.lossConstant / Real.sqrt model.M_eff := by
  rw [PolygenicCLTPortabilityModel.portabilityScore_eq_one_sub_relativePortabilityLoss,
    PolygenicCLTPortabilityModel.relativePortabilityLoss_eq_lossConstant_div_sqrt
    model h_M h_signal]

/-- Relative portability loss is nonnegative under positive signal and
    nonnegative mismatch scale. -/
theorem PolygenicCLTPortabilityModel.relativePortabilityLoss_nonneg
    (model : PolygenicCLTPortabilityModel)
    (h_M : 0 < model.M_eff)
    (h_signal : 0 < model.perLocusSignal)
    (h_mismatch : 0 ≤ model.perLocusMismatchSD) :
    0 ≤ model.relativePortabilityLoss := by
  rw [PolygenicCLTPortabilityModel.relativePortabilityLoss_eq_lossConstant_div_sqrt
    model h_M h_signal]
  unfold PolygenicCLTPortabilityModel.lossConstant
  exact div_nonneg
    (div_nonneg h_mismatch (le_of_lt h_signal))
    (le_of_lt (Real.sqrt_pos.mpr h_M))

/-- The CLT portability score is always at most `1`. -/
theorem PolygenicCLTPortabilityModel.portabilityScore_le_one
    (model : PolygenicCLTPortabilityModel)
    (h_M : 0 < model.M_eff)
    (h_signal : 0 < model.perLocusSignal)
    (h_mismatch : 0 ≤ model.perLocusMismatchSD) :
    model.portabilityScore ≤ 1 := by
  rw [PolygenicCLTPortabilityModel.portabilityScore_eq_one_sub_relativePortabilityLoss]
  have h_loss_nn :=
    PolygenicCLTPortabilityModel.relativePortabilityLoss_nonneg model h_M h_signal h_mismatch
  linarith

/-- **Selection can outweigh a polygenicity advantage.**
    In the CLT model, larger `M_eff` improves the polygenicity-only portability
    score. But overall portability also multiplies by the cross-population
    effect-correlation factor `rg²`. So a selected trait can be more polygenic
    than a neutral trait and still have worse total portability if selection
    depresses `rg` enough. -/
theorem selection_overrides_polygenicity
    (neutralModel selectedModel : PolygenicCLTPortabilityModel)
    (rg_neutral rg_selected ld_factor : ℝ)
    (h_M_neutral : 0 < neutralModel.M_eff)
    (h_M_selected : 0 < selectedModel.M_eff)
    (h_more_polygenic : neutralModel.M_eff < selectedModel.M_eff)
    (h_signal : 0 < neutralModel.perLocusSignal)
    (h_mismatch : 0 < neutralModel.perLocusMismatchSD)
    (h_same_signal : neutralModel.perLocusSignal = selectedModel.perLocusSignal)
    (h_same_mismatch : neutralModel.perLocusMismatchSD = selectedModel.perLocusMismatchSD)
    (h_ld : 0 < ld_factor)
    (h_selection_dominates :
      rg_selected ^ 2 <
        rg_neutral ^ 2 *
          (1 - neutralModel.lossConstant / Real.sqrt neutralModel.M_eff)) :
    neutralModel.portabilityScore < selectedModel.portabilityScore ∧
      selectionAdjustedPortability selectedModel rg_selected ld_factor <
        selectionAdjustedPortability neutralModel rg_neutral ld_factor := by
  have h_poly_loss :
      selectedModel.relativePortabilityLoss < neutralModel.relativePortabilityLoss := by
    exact more_polygenic_more_portable
      neutralModel selectedModel h_M_neutral h_M_selected h_more_polygenic
      h_signal h_mismatch h_same_signal h_same_mismatch
  have h_poly_score :
      neutralModel.portabilityScore < selectedModel.portabilityScore := by
    rw [PolygenicCLTPortabilityModel.portabilityScore_eq_one_sub_relativePortabilityLoss,
      PolygenicCLTPortabilityModel.portabilityScore_eq_one_sub_relativePortabilityLoss]
    linarith
  have h_selected_signal : 0 < selectedModel.perLocusSignal := by
    simpa [h_same_signal] using h_signal
  have h_selected_mismatch_nn : 0 ≤ selectedModel.perLocusMismatchSD := by
    simpa [h_same_mismatch] using (le_of_lt h_mismatch)
  have h_selected_score_le_one :
      selectedModel.portabilityScore ≤ 1 := by
    exact PolygenicCLTPortabilityModel.portabilityScore_le_one
      selectedModel h_M_selected h_selected_signal h_selected_mismatch_nn
  have h_neutral_score_eq :
      neutralModel.portabilityScore =
        1 - neutralModel.lossConstant / Real.sqrt neutralModel.M_eff := by
    exact PolygenicCLTPortabilityModel.portabilityScore_eq_one_sub_lossConstant_div_sqrt
      neutralModel h_M_neutral h_signal
  have h_selection_dominates' :
      rg_selected ^ 2 < rg_neutral ^ 2 * neutralModel.portabilityScore := by
    rw [h_neutral_score_eq]
    exact h_selection_dominates
  have h_selected_core_le :
      rg_selected ^ 2 * selectedModel.portabilityScore ≤ rg_selected ^ 2 := by
    have h_sq_nn : 0 ≤ rg_selected ^ 2 := sq_nonneg rg_selected
    have h_mul :
        rg_selected ^ 2 * selectedModel.portabilityScore ≤
          rg_selected ^ 2 * 1 := by
      exact mul_le_mul_of_nonneg_left h_selected_score_le_one h_sq_nn
    simpa using h_mul
  have h_core_lt :
      rg_selected ^ 2 * selectedModel.portabilityScore <
        rg_neutral ^ 2 * neutralModel.portabilityScore := by
    exact lt_of_le_of_lt h_selected_core_le h_selection_dominates'
  have h_adjusted_lt :
      (rg_selected ^ 2 * selectedModel.portabilityScore) * ld_factor <
        (rg_neutral ^ 2 * neutralModel.portabilityScore) * ld_factor := by
    exact mul_lt_mul_of_pos_right h_core_lt h_ld
  refine ⟨h_poly_score, ?_⟩
  simpa [selectionAdjustedPortability, mul_assoc, mul_left_comm, mul_comm] using h_adjusted_lt

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
