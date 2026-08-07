/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.PhenomeWidePortability

assert_below Descent.Decision Descent.Program

namespace Descent.Portability

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

Provenance: derived here, not imported. Wang et al. (2026), Nature Communications 17:942,
substantiates nothing below. It is an empirical study of the polygenic-score portability
gap and does not treat genotype imputation quality. Sources for individual results,
where they exist, are cited at those results.
-/

/-!
## Imputation Quality and PGS

Imputation quality is measured by r² (INFO score), the squared
correlation between imputed and true genotypes.
-/

section ImputationQuality

/-- **Imputation r² reduces effective PGS signal.**
    When a PGS variant has imputation r²_imp < 1, the contribution
    to PGS variance is attenuated by r²_imp. -/
noncomputable def attenuatedVariance (beta_sq het r2_imp : ℝ) : ℝ :=
  Descent.Core.product3 beta_sq het r2_imp

/-- Reference evaluation; see `Descent.Core.Ratios` for what these pin and why. -/
theorem attenuatedVariance_at_reference_point :
    attenuatedVariance 2 2 2 = 8 := by
  norm_num [attenuatedVariance,
      Descent.Core.product3]

/-- Attenuated ≤ true variance. -/
theorem attenuated_le_true (beta_sq het r2_imp : ℝ)
    (h_bsq : 0 ≤ beta_sq) (h_het : 0 ≤ het)
    (h_r2_le : r2_imp ≤ 1) :
    attenuatedVariance beta_sq het r2_imp ≤ beta_sq * het := by
  unfold attenuatedVariance Descent.Core.product3
  calc beta_sq * het * r2_imp ≤ beta_sq * het * 1 :=
        mul_le_mul_of_nonneg_left h_r2_le (mul_nonneg h_bsq h_het)
    _ = beta_sq * het := by ring

/-- **Imputation error adds noise to PGS.**
    Imputed dosage = true genotype + imputation error.
    PGS_imputed = PGS_true + PGS_error.
    Var(PGS_error) = Σ β² × Var(error) = Σ β² × het × (1 - r²_imp). -/
noncomputable def imputationErrorVariance (beta_sq het r2_imp : ℝ) : ℝ :=
  beta_sq * het * (1 - r2_imp)

/-- Reference evaluation; see `Descent.Core.Ratios` for what these pin and why. -/
theorem imputationErrorVariance_at_reference_point :
    imputationErrorVariance 2 2 2 = -4 := by
  norm_num [imputationErrorVariance]

/-- Imputation error variance is nonneg. -/
theorem imputation_error_nonneg (beta_sq het r2_imp : ℝ)
    (h_bsq : 0 ≤ beta_sq) (h_het : 0 ≤ het)
    (h_r2_le : r2_imp ≤ 1) :
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
  unfold attenuatedVariance imputationErrorVariance Descent.Core.product3
  ring

/-- **Perfect imputation is exactly the no-attenuation boundary.**  For a variant with nonzero
true variance contribution, attenuated and true PGS variance agree if and only if imputation
quality is one. -/
theorem attenuatedVariance_eq_true_iff
    (beta_sq het r2_imp : ℝ) (h_true : beta_sq * het ≠ 0) :
    attenuatedVariance beta_sq het r2_imp = beta_sq * het ↔ r2_imp = 1 := by
  unfold attenuatedVariance Descent.Core.product3
  constructor
  · intro h_equal
    apply mul_left_cancel₀ h_true
    calc
      (beta_sq * het) * r2_imp = beta_sq * het := h_equal
      _ = (beta_sq * het) * 1 := (mul_one _).symm
  · rintro rfl
    ring

/-- For a variant with nonzero true variance contribution, imputation error vanishes exactly at
unit imputation quality. -/
theorem imputationErrorVariance_eq_zero_iff
    (beta_sq het r2_imp : ℝ) (h_true : beta_sq * het ≠ 0) :
    imputationErrorVariance beta_sq het r2_imp = 0 ↔ r2_imp = 1 := by
  unfold imputationErrorVariance
  rw [mul_eq_zero]
  simp only [h_true, false_or]
  constructor <;> intro h <;> linarith

end ImputationQuality

/-!
## Reference Panel Effects

The choice of imputation reference panel directly affects
PGS quality across populations.
-/

section ReferencePanel

/-- Imputation quality after multiplying the local LD ceiling by reference-panel match. -/
noncomputable def panelAdjustedImputationQuality (r2_LD panelMatch : ℝ) : ℝ :=
  Descent.Core.product r2_LD panelMatch

/-- Panel mismatch cannot exceed the local LD imputation ceiling when LD signal is nonnegative
and panel match is at most one. -/
theorem panelAdjustedImputationQuality_le_ld
    (r2_LD panel_match : ℝ)
    (h_r2 : 0 ≤ r2_LD) (h_pm_le : panel_match ≤ 1) :
    panelAdjustedImputationQuality r2_LD panel_match ≤ r2_LD := by
  unfold panelAdjustedImputationQuality Descent.Core.product
  calc r2_LD * panel_match ≤ r2_LD * 1 :=
        mul_le_mul_of_nonneg_left h_pm_le h_r2
    _ = r2_LD := mul_one _

/-- With a nonzero LD ceiling, the panel-adjusted quality attains that ceiling exactly for a
perfectly matched reference panel. -/
theorem panelAdjustedImputationQuality_eq_ld_iff
    (r2_LD panelMatch : ℝ) (h_ld : r2_LD ≠ 0) :
    panelAdjustedImputationQuality r2_LD panelMatch = r2_LD ↔ panelMatch = 1 := by
  unfold panelAdjustedImputationQuality Descent.Core.product
  constructor
  · intro h_equal
    apply mul_left_cancel₀ h_ld
    calc
      r2_LD * panelMatch = r2_LD := h_equal
      _ = r2_LD * 1 := (mul_one _).symm
  · rintro rfl
    ring

/-- With a nonzero LD ceiling, panel-adjusted imputation quality vanishes exactly when panel
match vanishes. -/
theorem panelAdjustedImputationQuality_eq_zero_iff
    (r2_LD panelMatch : ℝ) (h_ld : r2_LD ≠ 0) :
    panelAdjustedImputationQuality r2_LD panelMatch = 0 ↔ panelMatch = 0 := by
  unfold panelAdjustedImputationQuality Descent.Core.product
  rw [mul_eq_zero]
  simp [h_ld]

/-- **Panel mismatch scales the variance an imputed variant contributes.**

The variance a variant carries at a panel-adjusted quality is the variance it carries at the
bare LD ceiling, multiplied by the panel match — the mismatch factor passes straight through
the attenuation and out the other side. This is what licenses reading `panelMatch` as a
portability coefficient rather than as one more term inside a quality score: a panel that
matches half as well leaves half the variance, at every `r²_LD` and every effect size.

It also pins `attenuatedVariance` and `panelAdjustedImputationQuality` to each other. Both are
products, and a product is exactly the shape under which the two orders of multiplication
agree; were either body a share, a sum or a clamp, the two sides would part company. -/
theorem attenuatedVariance_panelAdjusted (beta_sq het r2_LD panelMatch : ℝ) :
    attenuatedVariance beta_sq het (panelAdjustedImputationQuality r2_LD panelMatch) =
      Descent.Core.product (attenuatedVariance beta_sq het r2_LD) panelMatch := by
  unfold attenuatedVariance panelAdjustedImputationQuality Descent.Core.product3
    Descent.Core.product
  ring

end ReferencePanel

/-!
## Rare Variant Imputation

Rare variants are particularly difficult to impute, and this
difficulty varies dramatically across populations.
-/

section RareVariantImputation

/-- **Population specificity of rare variant imputation.**
    Rare variants are population-specific → they're only in the
    reference panel if the panel includes that population.
    Missing from panel → imputation r² = 0.
    Model: imputation r² = r²_LD × I(variant_in_panel). If the variant
    is absent from the panel, the indicator is 0 and r²_imp = 0. -/
theorem panelAdjustedImputationQuality_eq_zero_of_panel_absent
    (r2_LD : ℝ) (variant_in_panel : ℝ)
    (h_missing : variant_in_panel = 0) :
    panelAdjustedImputationQuality r2_LD variant_in_panel = 0 := by
  simp [panelAdjustedImputationQuality, h_missing,
      Descent.Core.product]

/-- **At unit imputation quality the attenuation factor is one.**

    `attenuatedVariance a b c = a * b * c`, so with all three arguments one this is `1 * 1 * 1`.
    That whole-genome sequencing achieves `r²_imp = 1` is supplied as the hypothesis, not
    derived, and that it therefore removes imputation-related portability artifacts is a reading
    of the arithmetic rather than a consequence of it: no sequencing platform, no variant and no
    portability quantity appears below. -/
theorem wgs_preserves_true_variance
    (beta_sq het r2_imp_wgs : ℝ) (h_perfect : r2_imp_wgs = 1) :
    attenuatedVariance beta_sq het r2_imp_wgs = beta_sq * het := by
  simp [attenuatedVariance, h_perfect,
      Descent.Core.product3]

/-- **Cost-benefit of WGS vs arrays.**
    WGS costs more per sample → smaller sample sizes.
    Arrays allow larger samples but with imputation error.
    Model: R²_WGS(n) = h² × n/(n + C₁), R²_array(n) = h² × r²_imp × n/(n + C₂).
    With budget B, cost_wgs > cost_array → n_wgs < n_array.
    When n_array is sufficiently larger, array R² can exceed WGS R²
    despite r²_imp < 1, because the sample size advantage compensates. -/
theorem wgs_vs_array_tradeoff
    (h2 r2_imp n_wgs n_array C : ℝ)
    (h_h2 : 0 < h2)
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

/-- Difference in `R²` corresponding to apparent portability loss relative
    to the source-population score performance. -/
noncomputable def apparent_portability_loss
    (r2_source r2_target_array : ℝ) : ℝ :=
  Descent.Core.difference r2_source r2_target_array

/-- Reference evaluation; see `Descent.Core.Ratios` for what these pin and why. -/
theorem apparent_portability_loss_at_reference_point :
    apparent_portability_loss 2 1 = 1 := by
  norm_num [apparent_portability_loss,
      Descent.Core.difference]

/-- Difference in `R²` corresponding to true biological portability loss,
    as measured with an ideal non-ascertained array or sequencing design. -/
noncomputable def true_portability_loss
    (r2_source r2_target_ideal : ℝ) : ℝ :=
  Descent.Core.difference r2_source r2_target_ideal

/-- Reference evaluation; see `Descent.Core.Ratios` for what these pin and why. -/
theorem true_portability_loss_at_reference_point :
    true_portability_loss 2 1 = 1 := by
  norm_num [true_portability_loss,
      Descent.Core.difference]

/-- **Ascertainment creates artificial portability loss.**
    Even with identical genetic architecture, the PGS computed
    from an EUR-ascertained array has lower R² in non-EUR
    populations because the array misses non-EUR causal variants.

    **DO NOT COLLAPSE `apparent_portability_loss` INTO `true_portability_loss`.** Both
    bodies are `a - b`, so `validation/extract/equivalence.py` reports them as one
    equivalence class and a duplicate-body sweep will propose merging them. They are two
    different quantities: one is measured against the array actually deployed, the other
    against an ideal non-ascertained design that does not exist. Their arithmetic
    coincides and their referents do not, which is the whole content of this theorem —
    the gap between them is the ascertainment artifact.

    Note honestly what is and is not proved. The first conjunct is a decomposition and is
    an identity (`ring`). The second conjunct is `h_array_worse` restated through the two
    definitions, so it is trivial to prove — but, unlike a vacuous statement, it CAN
    fail: drop the hypothesis and it is false. Contrast
    `DriftRegime.cluster_identities_hold_at_every_retention`, which holds at every value
    of its argument and is intentionally unfalsifiable. -/
theorem ascertainment_artificial_loss
    (r2_source r2_target_array r2_target_ideal : ℝ)
    (h_array_worse : r2_target_array < r2_target_ideal) :
    apparent_portability_loss r2_source r2_target_array =
        true_portability_loss r2_source r2_target_ideal +
          (r2_target_ideal - r2_target_array) ∧
      0 <
        apparent_portability_loss r2_source r2_target_array -
          true_portability_loss r2_source r2_target_ideal := by
  constructor
  · dsimp [apparent_portability_loss, true_portability_loss,
      Descent.Core.difference]
    ring
  · dsimp [apparent_portability_loss, true_portability_loss,
      Descent.Core.difference]
    linarith

/-- Ascertainment loss from incompletely tagged causal variation. -/
noncomputable def ascertainment_loss (coverage v_causal : ℝ) : ℝ :=
  Descent.Core.retainedFraction coverage v_causal

/-- Reference evaluation; see `Descent.Core.Ratios` for what these pin and why. -/
theorem ascertainment_loss_at_reference_point :
    ascertainment_loss (1 / 2) (1 / 2) = 1 / 4 := by
  unfold ascertainment_loss Descent.Core.retainedFraction
  norm_num

/-- **Cross-check: incomplete tagging attenuates exactly as drift does.**
`PortabilityDrift.presentDayPGSVariance` and
`PhenomeWidePortability.neutralPortabilityRatioLD` are the same
`(1 - x) · y` attenuation applied to a different pair of quantities. Three
independent spellings of one map is the configuration in which a convention
change in one goes unnoticed in the others. -/
theorem ascertainment_loss_eq_presentDayPGSVariance (coverage v_causal : ℝ) :
    ascertainment_loss coverage v_causal =
      presentDayPGSVariance v_causal coverage := by
  unfold ascertainment_loss presentDayPGSVariance pgsVarianceFromHet Descent.Core.product
    Descent.Core.retainedFraction; ring

theorem ascertainment_loss_eq_neutralPortabilityRatioLD (coverage v_causal : ℝ) :
    ascertainment_loss coverage v_causal =
      neutralPortabilityRatioLD coverage v_causal := by
  unfold ascertainment_loss neutralPortabilityRatioLD Descent.Core.retainedFraction; ring

/-- **Multi-ethnic arrays reduce ascertainment bias.**
    Arrays designed with variants from multiple populations
    reduce the ascertainment component of portability loss.
    Model: ascertainment loss = (1 - coverage) × V_causal, where coverage
    is the fraction of causal variants tagged by the array. Multi-ethnic
    arrays have higher coverage (cover_multi > cover_std). -/
theorem multi_ethnic_arrays_reduce_bias
    (V_causal cover_std cover_multi : ℝ)
    (h_V : 0 < V_causal)
    (h_better : cover_std < cover_multi) :
    ascertainment_loss cover_multi V_causal <
      ascertainment_loss cover_std V_causal := by
  dsimp [ascertainment_loss, Descent.Core.retainedFraction]
  exact mul_lt_mul_of_pos_right (by linarith) h_V

/-- Total portability loss as the sum of biological and technical components. -/
noncomputable def total_portability_loss (loss_genetic loss_technical : ℝ) : ℝ :=
  Descent.Core.sum loss_genetic loss_technical

/-- Reference evaluation; see `Descent.Core.Ratios` for what these pin and why. -/
theorem total_portability_loss_at_reference_point :
    total_portability_loss 2 2 = 4 := by
  norm_num [total_portability_loss,
      Descent.Core.sum]

/-- **The apparent loss is the total of the true loss and the ascertainment gap.**

`ascertainment_artificial_loss` writes that decomposition with a bare `+`. Written through
`total_portability_loss` instead, it says which named quantity that sum is: the technical
component is the `R²` an ideal design would have recovered and the deployed array did not,
and the genetic component is `true_portability_loss`. The three loss quantities of this file
are one identity rather than three unrelated differences.

This is the statement that fails if any of the three drifts apart. `apparent` and `true` are
both `a - b` and are deliberately kept distinct — see `ascertainment_artificial_loss` — so
nothing but a theorem naming all three can detect a body changing under one of the names. -/
theorem apparent_portability_loss_eq_total_of_ideal
    (r2_source r2_target_array r2_target_ideal : ℝ) :
    apparent_portability_loss r2_source r2_target_array =
      total_portability_loss (true_portability_loss r2_source r2_target_ideal)
        (Descent.Core.difference r2_target_ideal r2_target_array) := by
  unfold apparent_portability_loss true_portability_loss total_portability_loss
    Descent.Core.difference Descent.Core.sum
  ring

/-- **Decomposing portability loss: genetic vs technical.**
    Total portability loss = genetic loss + technical loss.
    Genetic: LD mismatch, effect differences, selection.
    Technical: imputation error, array ascertainment. -/
theorem portability_loss_decomposition
    (loss_genetic loss_technical : ℝ)
    (h_gen_nn : 0 ≤ loss_genetic) (h_tech_nn : 0 ≤ loss_technical) :
    total_portability_loss loss_genetic loss_technical =
        loss_genetic + loss_technical ∧
      loss_genetic ≤ total_portability_loss loss_genetic loss_technical ∧
      loss_technical ≤ total_portability_loss loss_genetic loss_technical := by
  constructor
  · rfl
  constructor
  · dsimp [total_portability_loss,
      Descent.Core.sum]
    linarith
  · dsimp [total_portability_loss,
      Descent.Core.sum]
    linarith

end ArrayAscertainment

end Descent.Portability
