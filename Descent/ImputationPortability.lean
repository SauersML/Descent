/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.PhenomeWidePortability

namespace Descent

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
  beta_sq * het * r2_imp

/-- Reference evaluation: the body is fixed at a point, not merely bounded or shown invariant.
An inequality or an invariance leaves a family of bodies satisfying it; a value does not. -/
theorem attenuatedVariance_at_reference_point :
    attenuatedVariance 2 2 2 = 8 := by
  norm_num [attenuatedVariance]


/-- Attenuated ≤ true variance. -/
theorem attenuated_le_true (beta_sq het r2_imp : ℝ)
    (h_bsq : 0 ≤ beta_sq) (h_het : 0 ≤ het)
    (h_r2_le : r2_imp ≤ 1) :
    attenuatedVariance beta_sq het r2_imp ≤ beta_sq * het := by
  unfold attenuatedVariance
  calc beta_sq * het * r2_imp ≤ beta_sq * het * 1 :=
        mul_le_mul_of_nonneg_left h_r2_le (mul_nonneg h_bsq h_het)
    _ = beta_sq * het := by ring

/-- **Imputation error adds noise to PGS.**
    Imputed dosage = true genotype + imputation error.
    PGS_imputed = PGS_true + PGS_error.
    Var(PGS_error) = Σ β² × Var(error) = Σ β² × het × (1 - r²_imp). -/
noncomputable def imputationErrorVariance (beta_sq het r2_imp : ℝ) : ℝ :=
  beta_sq * het * (1 - r2_imp)

/-- Reference evaluation: the body is fixed at a point, not merely bounded or shown invariant.
An inequality or an invariance leaves a family of bodies satisfying it; a value does not. -/
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
  unfold attenuatedVariance imputationErrorVariance
  ring

/-- **Perfect imputation is exactly the no-attenuation boundary.**  For a variant with nonzero
true variance contribution, attenuated and true PGS variance agree if and only if imputation
quality is one. -/
theorem attenuatedVariance_eq_true_iff
    (beta_sq het r2_imp : ℝ) (h_true : beta_sq * het ≠ 0) :
    attenuatedVariance beta_sq het r2_imp = beta_sq * het ↔ r2_imp = 1 := by
  unfold attenuatedVariance
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
  r2_LD * panelMatch

/-- Panel mismatch cannot exceed the local LD imputation ceiling when LD signal is nonnegative
and panel match is at most one. -/
theorem panelAdjustedImputationQuality_le_ld
    (r2_LD panel_match : ℝ)
    (h_r2 : 0 ≤ r2_LD) (h_pm_le : panel_match ≤ 1) :
    panelAdjustedImputationQuality r2_LD panel_match ≤ r2_LD := by
  unfold panelAdjustedImputationQuality
  calc r2_LD * panel_match ≤ r2_LD * 1 :=
        mul_le_mul_of_nonneg_left h_pm_le h_r2
    _ = r2_LD := mul_one _

/-- With a nonzero LD ceiling, the panel-adjusted quality attains that ceiling exactly for a
perfectly matched reference panel. -/
theorem panelAdjustedImputationQuality_eq_ld_iff
    (r2_LD panelMatch : ℝ) (h_ld : r2_LD ≠ 0) :
    panelAdjustedImputationQuality r2_LD panelMatch = r2_LD ↔ panelMatch = 1 := by
  unfold panelAdjustedImputationQuality
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
  unfold panelAdjustedImputationQuality
  rw [mul_eq_zero]
  simp [h_ld]

/-- **Imputation quality as a function of LD extent alone.**

    The name carries the restriction because the signature cannot carry the alternative.
    Realised imputation `r²` is dominated by reference-panel size and by minor-allele
    frequency, and neither appears here: this is the LD-extent dependence with everything else
    held fixed, so it cannot be read as a predicted `r²` for a given panel.

    `1 - c / ld_extent` is an `r²` and must lie in `[0, 1]`, but the bare
    expression goes negative for `ld_extent < c` — which is the short-LD limit
    the portability claim is about, not a remote corner. The clamp at `0` is
    what makes this a quality measure at every LD extent; the theorems below
    that need the unclamped branch say so with a hypothesis `c < ld_extent`.

    Empirical status: UNTESTED. -/
noncomputable def ldExtentImputationQuality (c ld_extent : ℝ) : ℝ :=
  max 0 (1 - c / ld_extent)

/-- **ldExtentImputationQuality at its junk point, named.** A panel with no linkage-disequilibrium
extent imputes nothing. The divisor is zero, the penalty term is junk-zero, and the quality
clamps to `1`: PERFECT imputation from a panel that carries no information. The `max 0` guard
protects the lower end and lets the upper end fail unremarked. Consumers must guard the argument
that makes the divisor vanish. -/
theorem ldExtentImputationQuality_zero_extent_is_junk (c : ℝ) :
    ldExtentImputationQuality c 0 = 1 := by
  unfold ldExtentImputationQuality
  simp

/-- The clamped quality measure is an `r²`: it lies in `[0, 1]` for every
positive tagging constant and LD extent, with no side condition. -/
theorem ldExtentImputationQuality_mem_unit (c ld_extent : ℝ)
    (h_c : 0 < c) (h_ld : 0 < ld_extent) :
    0 ≤ ldExtentImputationQuality c ld_extent ∧ ldExtentImputationQuality c ld_extent ≤ 1 := by
  have h_frac_pos : 0 < c / ld_extent := div_pos h_c h_ld
  unfold ldExtentImputationQuality
  refine ⟨le_max_left _ _, ?_⟩
  apply max_le
  · norm_num
  · linarith

/-- **Exact LD cutoff for non-imputability.**  At positive LD extent, the clamped LD-only quality
is zero exactly when the available LD extent does not exceed the tagging constant. -/
theorem ldExtentImputationQuality_eq_zero_iff
    (c ld_extent : ℝ) (h_ld : 0 < ld_extent) :
    ldExtentImputationQuality c ld_extent = 0 ↔ ld_extent ≤ c := by
  constructor
  · intro h_zero
    have h_penalty : 1 - c / ld_extent ≤ 0 := by
      calc
        1 - c / ld_extent ≤ max 0 (1 - c / ld_extent) := le_max_right _ _
        _ = 0 := h_zero
    have h_ratio : 1 ≤ c / ld_extent := by linarith
    have := (le_div_iff₀ h_ld).1 h_ratio
    simpa using this
  · intro h_cutoff
    have h_ratio : 1 ≤ c / ld_extent := by
      apply (le_div_iff₀ h_ld).2
      simpa using h_cutoff
    unfold ldExtentImputationQuality
    rw [max_eq_left (by linarith)]

/-- At positive LD extent, LD-only imputation quality is strictly positive exactly above the
tagging cutoff. -/
theorem ldExtentImputationQuality_pos_iff
    (c ld_extent : ℝ) (h_ld : 0 < ld_extent) :
    0 < ldExtentImputationQuality c ld_extent ↔ c < ld_extent := by
  constructor
  · intro h_quality
    by_contra h_not_above
    have h_zero :=
      (ldExtentImputationQuality_eq_zero_iff c ld_extent h_ld).2 (le_of_not_gt h_not_above)
    linarith
  · intro h_above
    have h_ratio : c / ld_extent < 1 := (div_lt_one h_ld).2 h_above
    calc
      0 < 1 - c / ld_extent := by linarith
      _ ≤ ldExtentImputationQuality c ld_extent := by
        exact le_max_right _ _

/-- **LD-dependent imputation creates systematic bias.**
    In populations with shorter LD (e.g., AFR), tagging is worse,
    so imputation quality is systematically lower.
    This creates a baseline portability artifact.
    Model: mean imputation r² = `ldExtentImputationQuality c ld_extent`, monotone
    increasing in LD extent. Shorter LD → smaller LD_extent → lower mean
    imputation r². The hypothesis `c < ld_extent_short` is what puts both
    populations on the unclamped branch; below it the measure is `0` in both and
    the comparison is an equality rather than a strict inequality. -/
theorem shorter_ld_worse_imputation
    (c ld_extent_long ld_extent_short : ℝ)
    (h_c : 0 < c) (h_short : c < ld_extent_short)
    (h_shorter : ld_extent_short < ld_extent_long) :
    ldExtentImputationQuality c ld_extent_short < ldExtentImputationQuality c ld_extent_long := by
  have h_short_pos : 0 < ld_extent_short := by linarith
  have h_long_pos : 0 < ld_extent_long := by linarith
  have h1 : c / ld_extent_long < c / ld_extent_short :=
    div_lt_div_of_pos_left h_c h_short_pos h_shorter
  have h_short_lt_one : c / ld_extent_short < 1 := by
    rw [div_lt_one h_short_pos]; linarith
  have h_long_lt_one : c / ld_extent_long < 1 := by
    rw [div_lt_one h_long_pos]; linarith
  unfold ldExtentImputationQuality
  rw [max_eq_right (by linarith : (0 : ℝ) ≤ 1 - c / ld_extent_short),
    max_eq_right (by linarith : (0 : ℝ) ≤ 1 - c / ld_extent_long)]
  linarith

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
  simp [panelAdjustedImputationQuality, h_missing]

/-- **At unit imputation quality the attenuation factor is one.**

    `attenuatedVariance a b c = a * b * c`, so with all three arguments one this is `1 * 1 * 1`.
    That whole-genome sequencing achieves `r²_imp = 1` is supplied as the hypothesis, not
    derived, and that it therefore removes imputation-related portability artifacts is a reading
    of the arithmetic rather than a consequence of it: no sequencing platform, no variant and no
    portability quantity appears below. -/
theorem wgs_preserves_true_variance
    (beta_sq het r2_imp_wgs : ℝ) (h_perfect : r2_imp_wgs = 1) :
    attenuatedVariance beta_sq het r2_imp_wgs = beta_sq * het := by
  simp [attenuatedVariance, h_perfect]

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
  r2_source - r2_target_array

/-- Reference evaluation: the body is fixed at a point, not merely bounded or shown invariant.
An inequality or an invariance leaves a family of bodies satisfying it; a value does not. -/
theorem apparent_portability_loss_at_reference_point :
    apparent_portability_loss 2 1 = 1 := by
  norm_num [apparent_portability_loss]


/-- Difference in `R²` corresponding to true biological portability loss,
    as measured with an ideal non-ascertained array or sequencing design. -/
noncomputable def true_portability_loss
    (r2_source r2_target_ideal : ℝ) : ℝ :=
  r2_source - r2_target_ideal

/-- Reference evaluation: the body is fixed at a point, not merely bounded or shown invariant.
An inequality or an invariance leaves a family of bodies satisfying it; a value does not. -/
theorem true_portability_loss_at_reference_point :
    true_portability_loss 2 1 = 1 := by
  norm_num [true_portability_loss]


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
  · dsimp [apparent_portability_loss, true_portability_loss]
    ring
  · dsimp [apparent_portability_loss, true_portability_loss]
    linarith

/-- Ascertainment loss from incompletely tagged causal variation. -/
noncomputable def ascertainment_loss (coverage v_causal : ℝ) : ℝ :=
  (1 - coverage) * v_causal

/-- **ascertainment_loss pinned at a reference point.** No theorem in the corpus evaluated this
definition, so every body agreeing with it in sign and monotonicity was indistinguishable from
it. At all arguments equal to `1 / 2` it is `1 / 4`, which fixes the coefficients a one-sided
bound or an invariance leaves free. -/
theorem ascertainment_loss_at_reference_point :
    ascertainment_loss (1 / 2) (1 / 2) = 1 / 4 := by
  unfold ascertainment_loss
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
  unfold ascertainment_loss presentDayPGSVariance pgsVarianceFromHet; ring

theorem ascertainment_loss_eq_neutralPortabilityRatioLD (coverage v_causal : ℝ) :
    ascertainment_loss coverage v_causal =
      neutralPortabilityRatioLD coverage v_causal := by
  unfold ascertainment_loss neutralPortabilityRatioLD; ring

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
  dsimp [ascertainment_loss]
  exact mul_lt_mul_of_pos_right (by linarith) h_V

/-- Total portability loss as the sum of biological and technical components. -/
noncomputable def total_portability_loss (loss_genetic loss_technical : ℝ) : ℝ :=
  loss_genetic + loss_technical

/-- Reference evaluation: the body is fixed at a point, not merely bounded or shown invariant.
An inequality or an invariance leaves a family of bodies satisfying it; a value does not. -/
theorem total_portability_loss_at_reference_point :
    total_portability_loss 2 2 = 4 := by
  norm_num [total_portability_loss]


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
  · dsimp [total_portability_loss]
    linarith
  · dsimp [total_portability_loss]
    linarith


end ArrayAscertainment

end Descent
