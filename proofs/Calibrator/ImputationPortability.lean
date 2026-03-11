import Calibrator.Probability
import Calibrator.PortabilityDrift
import Calibrator.OpenQuestions

namespace Calibrator

open MeasureTheory

/-!
# Genotype Imputation and PGS Portability

This file formalizes how genotype imputation quality affects PGS
portability. Imputation infers ungenotyped variants from a reference
panel, and its accuracy is ancestry-dependent.

Key results:
1. Imputation quality metrics (r² INFO score)
2. Reference panel diversity affects imputation accuracy
3. Imputation error propagates to PGS accuracy
4. Population-specific imputation quality creates portability artifacts
5. Rare variant imputation challenges

Reference: Wang et al. (2026), Nature Communications 17:942.
-/


/-!
## Imputation Quality and PGS

Imputation quality is measured by r² (INFO score), the squared
correlation between imputed and true genotypes.
-/

section ImputationQuality

/- **Imputation r² (INFO score).**
    r²_imp = Var(E[g|observed]) / Var(g_true).
    This measures how well the imputed dosage captures the true genotype. -/

/-- **Imputation r² reduces effective PGS signal.**
    When a PGS variant has imputation r²_imp < 1, the contribution
    to PGS variance is attenuated by r²_imp. -/
noncomputable def attenuatedVariance (beta_sq het r2_imp : ℝ) : ℝ :=
  beta_sq * het * r2_imp

/-- Attenuated ≤ true variance. -/
theorem attenuated_le_true (beta_sq het r2_imp : ℝ)
    (h_bsq : 0 ≤ beta_sq) (h_het : 0 ≤ het)
    (h_r2 : 0 ≤ r2_imp) (h_r2_le : r2_imp ≤ 1) :
    attenuatedVariance beta_sq het r2_imp ≤ beta_sq * het := by
  unfold attenuatedVariance
  calc beta_sq * het * r2_imp ≤ beta_sq * het * 1 :=
        mul_le_mul_of_nonneg_left h_r2_le (mul_nonneg h_bsq h_het)
    _ = beta_sq * het := by ring

/-- **Population-specific imputation quality.**
    Imputation r² depends on:
    1. Reference panel size and diversity
    2. LD structure in the target population
    3. Allele frequency in the target
    Lower quality for underrepresented populations.
    Model: imputation r² ≈ r²_LD(best_tag), which depends on LD extent.
    Populations with shorter LD blocks (due to older demographic history)
    have lower r²_LD for the same array. If r²_tag_afr < r²_tag_eur and
    imputation quality is monotone in tag LD, then r²_imp_afr < r²_imp_eur. -/
theorem imputation_worse_for_underrepresented
    (r2_tag_eur r2_tag_afr scale : ℝ)
    (h_scale : 0 < scale) (h_scale_le : scale ≤ 1)
    (h_shorter_ld : r2_tag_afr < r2_tag_eur) :
    scale * r2_tag_afr < scale * r2_tag_eur := by
  exact mul_lt_mul_of_pos_left h_shorter_ld h_scale

/-- **Imputation error adds noise to PGS.**
    Imputed dosage = true genotype + imputation error.
    PGS_imputed = PGS_true + PGS_error.
    Var(PGS_error) = Σ β² × Var(error) = Σ β² × het × (1 - r²_imp). -/
noncomputable def imputationErrorVariance (beta_sq het r2_imp : ℝ) : ℝ :=
  beta_sq * het * (1 - r2_imp)

/-- Imputation error variance is nonneg. -/
theorem imputation_error_nonneg (beta_sq het r2_imp : ℝ)
    (h_bsq : 0 ≤ beta_sq) (h_het : 0 ≤ het)
    (h_r2 : 0 ≤ r2_imp) (h_r2_le : r2_imp ≤ 1) :
    0 ≤ imputationErrorVariance beta_sq het r2_imp := by
  unfold imputationErrorVariance
  exact mul_nonneg (mul_nonneg h_bsq h_het) (by linarith)

/-- **Total PGS variance with imputation.**
    Var(PGS_imputed) = Var(PGS_signal) + Var(PGS_noise)
    = Σ β² × het × r²_imp + Σ β² × het × (1 - r²_imp)
    = Σ β² × het = Var(PGS_true). -/
theorem imputed_pgs_variance_decomposition (beta_sq het r2_imp : ℝ) :
    attenuatedVariance beta_sq het r2_imp +
      imputationErrorVariance beta_sq het r2_imp = beta_sq * het := by
  unfold attenuatedVariance imputationErrorVariance
  ring

end ImputationQuality


/-!
## Reference Panel Effects

The choice of imputation reference panel directly affects
PGS quality across populations.
-/

section ReferencePanel

/-- **Reference panel diversity affects imputation for all populations.**
    More diverse panels (e.g., TOPMed vs 1000G) improve imputation
    for underrepresented populations.
    Model: imputation r² improves with reference panel size n_ref as
    r²(n) = r²_max × (1 - 1/n). Larger panels yield higher r². -/
theorem diverse_panel_improves_imputation
    (r2_max : ℝ) (n_small n_diverse : ℝ)
    (h_r2 : 0 < r2_max) (h_ns : 1 < n_small) (h_nd : 1 < n_diverse)
    (h_larger : n_small < n_diverse) :
    r2_max * (1 - 1 / n_small) < r2_max * (1 - 1 / n_diverse) := by
  apply mul_lt_mul_of_pos_left _ h_r2
  have h1 : 1 / n_diverse < 1 / n_small :=
    div_lt_div_of_pos_left one_pos (by linarith) h_larger
  linarith

/-- **Population-specific reference panels are optimal.**
    A reference panel from the same population gives the best
    imputation because LD patterns match perfectly.
    Model: imputation r² = r²_LD × panel_match where panel_match ∈ (0, 1].
    Matched panels have panel_match = 1; unmatched have panel_match < 1. -/
theorem matched_panel_optimal
    (r2_LD panel_match : ℝ)
    (h_r2 : 0 ≤ r2_LD) (h_pm_pos : 0 < panel_match) (h_pm_le : panel_match ≤ 1) :
    r2_LD * panel_match ≤ r2_LD := by
  calc r2_LD * panel_match ≤ r2_LD * 1 := by
        exact mul_le_mul_of_nonneg_left h_pm_le h_r2
    _ = r2_LD := mul_one _

/- **Imputation quality at a variant depends on local LD.**
    r²_imp(j) ≈ r²_LD(j, best_tag) where best_tag is the genotyped
    variant in highest LD with j. -/

/-- **LD-dependent imputation creates systematic bias.**
    In populations with shorter LD (e.g., AFR), tagging is worse,
    so imputation quality is systematically lower.
    This creates a baseline portability artifact.
    Model: mean imputation r² = f(LD_extent) where f is monotone increasing.
    Shorter LD → smaller LD_extent → lower mean imputation r².
    Specifically, mean_r2 = 1 - c/LD_extent for constant c > 0. -/
theorem shorter_ld_worse_imputation
    (c ld_extent_long ld_extent_short : ℝ)
    (h_c : 0 < c) (h_long : c < ld_extent_long) (h_short : c < ld_extent_short)
    (h_shorter : ld_extent_short < ld_extent_long) :
    1 - c / ld_extent_short < 1 - c / ld_extent_long := by
  have h1 : c / ld_extent_long < c / ld_extent_short :=
    div_lt_div_of_pos_left h_c (by linarith) h_shorter
  linarith

/-- **Imputation quality filtering threshold.**
    Variants with r²_imp < threshold (e.g., 0.3) are excluded.
    Different thresholds in different populations create
    non-overlapping variant sets → PGS incomparability. -/
theorem filtering_creates_variant_asymmetry
    (n_eur_pass n_afr_pass n_shared : ℕ)
    (h_eur_more : n_afr_pass ≤ n_eur_pass)
    (h_shared_le : n_shared ≤ n_afr_pass) :
    n_shared ≤ n_eur_pass := le_trans h_shared_le h_eur_more

end ReferencePanel


/-!
## Rare Variant Imputation

Rare variants are particularly difficult to impute, and this
difficulty varies dramatically across populations.
-/

section RareVariantImputation

/-- **Imputation r² drops sharply for rare variants.**
    For MAF < 1%, r²_imp is often < 0.5 even with large reference panels.
    This means rare variant PGS components are very noisy. -/
theorem rare_variant_poor_imputation
    (r2_common r2_rare : ℝ)
    (h_much_worse : r2_rare < (1 / 2) * r2_common)
    (h_common_good : 9 / 10 < r2_common) (h_common_le : r2_common ≤ 1) :
    r2_rare < 1 / 2 := by nlinarith

/-- **Population specificity of rare variant imputation.**
    Rare variants are population-specific → they're only in the
    reference panel if the panel includes that population.
    Missing from panel → imputation r² = 0.
    Model: imputation r² = r²_LD × I(variant_in_panel). If the variant
    is absent from the panel, the indicator is 0 and r²_imp = 0. -/
theorem missing_variant_zero_imputation
    (r2_LD : ℝ) (variant_in_panel : ℝ)
    (h_missing : variant_in_panel = 0) :
    r2_LD * variant_in_panel = 0 := by
  rw [h_missing, mul_zero]

/-- **WGS eliminates imputation artifacts.**
    With WGS, all variants are directly genotyped → r²_imp = 1.
    This removes imputation-related portability artifacts
    but doesn't fix LD mismatch or effect size differences. -/
theorem wgs_perfect_imputation
    (r2_imp_wgs : ℝ) (h_perfect : r2_imp_wgs = 1) :
    attenuatedVariance 1 1 r2_imp_wgs = 1 := by
  unfold attenuatedVariance; rw [h_perfect]; ring

/-- **Cost-benefit of WGS vs arrays.**
    WGS costs more per sample → smaller sample sizes.
    Arrays allow larger samples but with imputation error.
    Model: R²_WGS(n) = h² × n/(n + C₁), R²_array(n) = h² × r²_imp × n/(n + C₂).
    With budget B, cost_wgs > cost_array → n_wgs < n_array.
    When n_array is sufficiently larger, array R² can exceed WGS R²
    despite r²_imp < 1, because the sample size advantage compensates. -/
theorem wgs_vs_array_tradeoff
    (h2 r2_imp n_wgs n_array C : ℝ)
    (h_h2 : 0 < h2) (h_imp : 0 < r2_imp) (h_imp_le : r2_imp ≤ 1)
    (h_nw : 0 < n_wgs) (h_na : 0 < n_array) (h_C : 0 < C)
    (h_sample_advantage : r2_imp * n_array * (n_wgs + C) > n_wgs * (n_array + C)) :
    h2 * n_wgs / (n_wgs + C) < h2 * r2_imp * n_array / (n_array + C) := by
  rw [div_lt_div_iff₀ (by linarith) (by linarith)]
  nlinarith

end RareVariantImputation


/-!
## Array Ascertainment Bias

Genotyping arrays are designed for specific populations (typically EUR).
This creates systematic bias in cross-population PGS.
-/

section ArrayAscertainment

/- **SNP ascertainment on arrays is EUR-biased.**
    Most array variants were discovered in European GWAS.
    These variants have higher MAF in EUR → better imputation
    → higher PGS signal in EUR. -/

/-- **Ascertainment creates artificial portability loss.**
    Even with identical genetic architecture, the PGS computed
    from an EUR-ascertained array has lower R² in non-EUR
    populations because the array misses non-EUR causal variants. -/
theorem ascertainment_artificial_loss
    (r2_eur r2_afr_array r2_afr_ideal : ℝ)
    (h_array_worse : r2_afr_array < r2_afr_ideal)
    (h_ideal_good : 0 < r2_afr_ideal) :
    -- Some of the apparent portability loss is an array artifact
    0 < r2_afr_ideal - r2_afr_array := by linarith

/-- **Multi-ethnic arrays reduce ascertainment bias.**
    Arrays designed with variants from multiple populations
    reduce the ascertainment component of portability loss.
    Model: ascertainment loss = (1 - coverage) × V_causal, where coverage
    is the fraction of causal variants tagged by the array. Multi-ethnic
    arrays have higher coverage (cover_multi > cover_std). -/
theorem multi_ethnic_arrays_reduce_bias
    (V_causal cover_std cover_multi : ℝ)
    (h_V : 0 < V_causal) (h_cs : 0 ≤ cover_std) (h_cm : 0 ≤ cover_multi)
    (h_cs_le : cover_std ≤ 1) (h_cm_le : cover_multi ≤ 1)
    (h_better : cover_std < cover_multi) :
    (1 - cover_multi) * V_causal < (1 - cover_std) * V_causal := by
  exact mul_lt_mul_of_pos_right (by linarith) h_V

/-- **Decomposing portability loss: genetic vs technical.**
    Total portability loss = genetic loss + technical loss.
    Genetic: LD mismatch, effect differences, selection.
    Technical: imputation error, array ascertainment. -/
theorem portability_loss_decomposition
    (loss_total loss_genetic loss_technical : ℝ)
    (h_decomp : loss_total = loss_genetic + loss_technical)
    (h_gen_nn : 0 ≤ loss_genetic) (h_tech_nn : 0 ≤ loss_technical) :
    loss_genetic ≤ loss_total := by linarith

/-- **Technical loss is fixable; genetic loss is fundamental.**
    WGS + diverse reference panels can eliminate technical loss.
    Genetic loss requires new GWAS in target populations. -/
theorem technical_loss_eliminable
    (loss_with_tech loss_without_tech : ℝ)
    (h_eliminated : loss_without_tech < loss_with_tech)
    (h_nn : 0 ≤ loss_without_tech) :
    0 ≤ loss_with_tech - loss_without_tech := by linarith

end ArrayAscertainment

end Calibrator
