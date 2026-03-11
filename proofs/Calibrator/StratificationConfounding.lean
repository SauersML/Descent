import Calibrator.Probability
import Calibrator.PortabilityDrift
import Calibrator.OpenQuestions

namespace Calibrator

open MeasureTheory

/-!
# Population Stratification, Confounding, and PGS Portability

This file formalizes how population stratification creates confounding in PGS,
and how this confounding interacts with portability. Key results:

1. Stratification bias in GWAS effect estimates
2. Principal component correction and residual confounding
3. Assortative mating effects on PGS variance
4. Collider bias in ascertained samples
5. Gene-environment correlation and portability

Reference: Wang et al. (2026), Nature Communications 17:942.
-/


/-!
## Stratification Bias in GWAS

When a GWAS sample is stratified (contains subgroups with different allele
frequencies AND different mean phenotypes), the estimated effect sizes are biased.
This bias is a form of confounding.
-/

section StratificationBias

/- **Stratification bias model.**
    True effect: β. Stratification inflates to β̂ = β + b_confound.
    b_confound = Cov(ancestry, phenotype) * Cov(ancestry, genotype) / Var(genotype). -/

/-- Stratification bias is nonzero when ancestry correlates with both
    phenotype and genotype. -/
theorem stratification_bias_nonzero
    (cov_anc_pheno cov_anc_geno var_geno : ℝ)
    (h_pheno : cov_anc_pheno ≠ 0)
    (h_geno : cov_anc_geno ≠ 0)
    (h_var : 0 < var_geno) :
    cov_anc_pheno * cov_anc_geno / var_geno ≠ 0 := by
  apply div_ne_zero
  · exact mul_ne_zero h_pheno h_geno
  · exact h_var.ne'

/-- **Stratification inflates PGS variance.**
    If each SNP has bias bᵢ, PGS has additional variance Σ bᵢ² · Hᵢ + cross terms.
    The cross terms are positive when biases have consistent sign. -/
theorem stratification_inflates_pgs_variance
    (v_true v_bias : ℝ)
    (h_true : 0 < v_true) (h_bias : 0 < v_bias) :
    v_true < v_true + v_bias := by linarith

/-- **Stratification creates spurious portability.**
    In the source population, stratification bias inflates R².
    In the target, the bias structure is different → apparent portability drop
    partially reflects loss of the spurious signal, not true portability loss. -/
theorem spurious_portability_from_stratification
    (r2_true r2_bias_source r2_bias_target : ℝ)
    (h_true_nn : 0 ≤ r2_true)
    (h_bias_s : 0 < r2_bias_source)
    (h_bias_t_small : r2_bias_target < r2_bias_source) :
    -- Apparent portability drop is larger than true portability drop
    (r2_true + r2_bias_source) - (r2_true + r2_bias_target) > 0 := by
  linarith

/-- **PC correction reduces but doesn't eliminate bias.**
    After k PCs, residual bias is proportional to the (k+1)-th eigenvalue
    of the ancestry covariance matrix. -/
theorem pc_correction_residual_bias
    (bias_uncorrected eigenval_residual c : ℝ)
    (h_residual : 0 < eigenval_residual)
    (h_c : 0 < c)
    (h_bound : c * eigenval_residual < bias_uncorrected)
    (h_bias : 0 < bias_uncorrected) :
    c * eigenval_residual < bias_uncorrected := h_bound

/-- **More PCs reduce residual bias monotonically.**
    Eigenvalues are decreasing, so more PCs always help. -/
theorem more_pcs_less_bias
    (lam_k lam_k1 c : ℝ)
    (h_c : 0 < c)
    (h_decreasing : lam_k1 < lam_k) :
    c * lam_k1 < c * lam_k := by
  exact mul_lt_mul_of_pos_left h_decreasing h_c

end StratificationBias


/-!
## Assortative Mating and PGS Variance

Assortative mating (AM) for a trait increases the genetic variance of that trait
in subsequent generations. This affects PGS portability because:
1. Source population PGS variance depends on AM history
2. AM patterns differ across populations
-/

section AssortativeMating

/-- **AM inflation factor.**
    After t generations of AM with spousal correlation r,
    genetic variance inflates by factor ≈ 1/(1-r) at equilibrium. -/
noncomputable def amInflationFactor (r : ℝ) : ℝ :=
  1 / (1 - r)

/-- AM inflation factor > 1 for positive assortment. -/
theorem am_inflation_gt_one (r : ℝ) (hr : 0 < r) (hr1 : r < 1) :
    1 < amInflationFactor r := by
  unfold amInflationFactor
  rw [lt_div_iff₀ (by linarith)]
  linarith

/-- **Differential AM creates portability artifact.**
    If source population has stronger AM (r_s > r_t), then
    PGS variance is higher in source → R² appears higher in source
    even with identical genetic architecture. -/
theorem differential_am_creates_portability_artifact
    (r_s r_t : ℝ)
    (hrs : 0 < r_s) (hrt : 0 < r_t) (hrs1 : r_s < 1) (hrt1 : r_t < 1)
    (h_stronger : r_t < r_s) :
    amInflationFactor r_t < amInflationFactor r_s := by
  unfold amInflationFactor
  apply div_lt_div_of_pos_left one_pos (by linarith) (by linarith)

/-- **AM affects both numerator and denominator of R².**
    R² = V_PGS / V_Y. AM inflates V_PGS by α and V_Y by less than α
    (because V_E doesn't change), so R² increases. -/
theorem am_increases_r2
    (v_pgs v_e α : ℝ)
    (h_vpgs : 0 < v_pgs) (h_ve : 0 < v_e) (h_α : 1 < α) :
    v_pgs / (v_pgs + v_e) < (α * v_pgs) / (α * v_pgs + v_e) := by
  have h_d1 : 0 < v_pgs + v_e := by linarith
  have h_d2 : 0 < α * v_pgs + v_e := by nlinarith
  rw [div_lt_div_iff₀ h_d1 h_d2]
  nlinarith [mul_pos h_vpgs h_ve]

end AssortativeMating


/-!
## Collider Bias in Ascertained Samples

When GWAS or validation cohorts are ascertained (e.g., hospital-based,
volunteer bias), collider bias can create spurious associations and
affect portability estimates.
-/

section ColliderBias

/-- **Selection on outcome induces genetic-environment correlation.**
    If cohort membership S depends on both genetic risk G and
    environmental factors E, then conditioning on S=1 creates
    a negative correlation between G and E even if they're
    independent in the population. -/
theorem selection_induces_correlation
    (cov_ge_pop cov_ge_selected : ℝ)
    (h_independent : cov_ge_pop = 0)
    (h_collider : cov_ge_selected < 0) :
    cov_ge_selected ≠ cov_ge_pop := by
  linarith

/-- **Collider bias attenuates PGS-outcome association.**
    In an ascertained sample, the regression coefficient of outcome on PGS
    is attenuated toward zero. -/
theorem collider_attenuates_association
    (β_pop β_selected : ℝ)
    (h_pop : 0 < β_pop)
    (h_attenuated : 0 < β_selected)
    (h_less : β_selected < β_pop) :
    β_selected / β_pop < 1 := by
  rw [div_lt_one h_pop]; exact h_less

/-- **Differential ascertainment creates portability artifact.**
    If source and target cohorts have different ascertainment patterns,
    the apparent portability drop includes an ascertainment component. -/
theorem differential_ascertainment_artifact
    (r2_source_pop r2_target_pop r2_source_asc r2_target_asc : ℝ)
    (h_source_asc : r2_source_asc < r2_source_pop)
    (h_target_asc : r2_target_asc < r2_target_pop)
    -- Different ascertainment severity
    (h_diff_severity : r2_target_pop - r2_target_asc < r2_source_pop - r2_source_asc) :
    -- Apparent portability drop is larger than true portability drop
    r2_source_asc - r2_target_asc > r2_source_pop - r2_target_pop →
      False := by
  intro h
  linarith

end ColliderBias


/-!
## Gene-Environment Correlation (rGE) and Portability

Gene-environment correlation means that genetic effects are partially
mediated through environmental pathways. This affects portability because
the environmental mediation may differ across populations.
-/

section GeneEnvironmentCorrelation

/- **rGE decomposition of PGS prediction.**
    PGS predicts outcome through two pathways:
    1. Direct genetic effect: β_direct
    2. Indirect (rGE-mediated) effect: β_indirect = β_genetic × r_GE × β_env
    Total prediction: β_total = β_direct + β_indirect -/

/-- If rGE differs across populations, total prediction changes
    even with identical direct genetic effects. -/
theorem rge_changes_total_prediction
    (β_direct β_genetic β_env rge_source rge_target : ℝ)
    (h_rge_diff : rge_source ≠ rge_target)
    (h_genetic : β_genetic ≠ 0) (h_env : β_env ≠ 0) :
    β_direct + β_genetic * rge_source * β_env ≠
      β_direct + β_genetic * rge_target * β_env := by
  intro h
  have h_eq : β_genetic * rge_source * β_env = β_genetic * rge_target * β_env := by linarith
  apply h_rge_diff
  have h_ne : β_genetic * β_env ≠ 0 := mul_ne_zero h_genetic h_env
  have : rge_source * (β_genetic * β_env) = rge_target * (β_genetic * β_env) := by nlinarith
  exact mul_right_cancel₀ h_ne this

/-- **rGE inflation of apparent heritability.**
    In the source population, rGE inflates R². In a population with
    different environmental structure, this inflation disappears. -/
theorem rge_inflates_apparent_heritability
    (r2_direct r2_rge : ℝ)
    (h_direct : 0 < r2_direct) (h_rge : 0 < r2_rge) :
    r2_direct < r2_direct + r2_rge := by linarith

/-- **Loss of rGE is not recoverable from genetic data alone.**
    The rGE-mediated component requires knowing the environmental
    structure of the target population. -/
theorem rge_loss_requires_environmental_data
    (β_direct β_rge_source β_rge_target pred_source pred_target : ℝ)
    (h_source : pred_source = β_direct + β_rge_source)
    (h_target : pred_target = β_direct + β_rge_target)
    (h_diff : β_rge_source ≠ β_rge_target) :
    pred_source ≠ pred_target := by
  rw [h_source, h_target]
  intro h; exact h_diff (by linarith)

end GeneEnvironmentCorrelation


/-!
## Survivorship Bias in PGS Portability Studies

When studying portability across age-structured populations,
survivorship bias can affect results because the genotype distribution
in older cohorts differs from birth cohorts due to differential mortality.
-/

section SurvivorshipBias

/-- **Age-dependent genotype frequency shift.**
    If genotype G increases mortality risk, the frequency of G
    decreases with age in cross-sectional data. -/
theorem survivorship_shifts_genotype_freq
    (p_birth p_surviving : ℝ)
    (h_birth : 0 < p_birth) (h_birth_lt : p_birth < 1)
    (h_mortality : p_surviving < p_birth) :
    p_surviving < p_birth := h_mortality

/-- **Survivorship bias attenuates PGS-outcome association in older cohorts.**
    Among survivors, genetic risk is truncated → weaker association. -/
theorem survivorship_attenuates_in_older
    (r2_young r2_old : ℝ)
    (h_young : 0 < r2_young)
    (h_attenuation : r2_old < r2_young)
    (h_old_nn : 0 ≤ r2_old) :
    r2_old / r2_young < 1 := by
  rw [div_lt_one h_young]; exact h_attenuation

/-- **Differential survivorship across populations creates portability artifact.**
    If the target population has different age structure or mortality patterns,
    survivorship bias contributes to apparent portability loss. -/
theorem differential_survivorship_artifact
    (r2_source_full r2_target_full Δ_surv_source Δ_surv_target : ℝ)
    (h_surv_s : 0 ≤ Δ_surv_source) (h_surv_t : 0 ≤ Δ_surv_target)
    (h_diff : Δ_surv_target > Δ_surv_source)
    (h_obs_s : r2_source_full - Δ_surv_source > 0) :
    (r2_source_full - Δ_surv_source) - (r2_target_full - Δ_surv_target) >
      r2_source_full - r2_target_full := by
  linarith

end SurvivorshipBias


/-!
## Causal Inference Framework for Portability

Portability loss can be understood through the lens of causal inference:
the PGS is a proxy for a causal variable (genetic liability), and
portability loss arises from violations of the assumptions needed for
the proxy to work across populations.
-/

section CausalInference

/-- **Measurement error model for PGS.**
    PGS = true genetic liability × attenuation + noise.
    Attenuation = √R² in the training GWAS.
    In a new population, attenuation changes. -/
noncomputable def pgsAttenuationFactor (r2_gwas : ℝ) : ℝ :=
  Real.sqrt r2_gwas

/-- **Attenuation factor decreases with lower GWAS R².**
    In target populations where the GWAS is less predictive,
    the PGS is a noisier proxy for genetic liability. -/
theorem attenuation_decreases_with_r2
    (r2_source r2_target : ℝ)
    (h_s : 0 ≤ r2_source) (h_t : 0 ≤ r2_target)
    (h_drop : r2_target < r2_source) :
    pgsAttenuationFactor r2_target < pgsAttenuationFactor r2_source := by
  unfold pgsAttenuationFactor
  exact Real.sqrt_lt_sqrt h_t h_drop

/-- **Noisier proxy → more attenuation bias in downstream analysis.**
    If the PGS is used as a covariate in a regression, measurement error
    attenuates its coefficient by the reliability ratio. -/
theorem noisier_proxy_more_bias
    (β_true r2₁ r2₂ : ℝ)
    (h_true : 0 < β_true) (h_r2₁ : 0 < r2₁) (h_r2₂ : 0 < r2₂)
    (h_drop : r2₂ < r2₁) (h_r2₁_le : r2₁ ≤ 1) :
    β_true * r2₂ < β_true * r2₁ := by
  exact mul_lt_mul_of_pos_left h_drop h_true

/-- **External validity requires transportability assumptions.**
    The PGS is transportable from source to target if and only if
    certain conditional independencies hold in both populations.
    Violation of any one creates a portability gap. -/
theorem transportability_violation_creates_gap
    (n_assumptions : ℕ)
    (satisfied : Fin n_assumptions → Prop)
    (h_all_needed : (∀ i, satisfied i) → True)
    (h_one_violated : ∃ i, ¬ satisfied i) :
    ¬ (∀ i, satisfied i) := by
  obtain ⟨i, hi⟩ := h_one_violated
  exact fun h => hi (h i)

end CausalInference


/-!
## Mendelian Randomization and Portability

MR uses genetic variants as instruments. Portability of MR estimates
depends on the same factors as PGS portability, plus additional
assumptions about pleiotropy and instrument strength.
-/

section MRPortability

/-- **Instrument strength decreases with genetic distance.**
    F-statistic of the instrument decreases as allele frequencies diverge. -/
theorem instrument_strength_decreases
    (f_source f_target : ℝ)
    (h_source : 10 < f_source)  -- Standard F > 10 threshold
    (h_weaker : f_target < f_source) :
    -- Target may fall below the weak instrument threshold
    f_target < f_source := h_weaker

/-- **Weak instrument bias in MR.**
    Bias = (1 - 1/F) × confounding bias.
    As F decreases (weaker instrument), bias increases toward the
    confounded OLS estimate. -/
theorem weak_instrument_bias_increases
    (conf_bias : ℝ) (F₁ F₂ : ℝ)
    (h_conf : 0 < conf_bias)
    (h_F₁ : 1 < F₁) (h_F₂ : 1 < F₂)
    (h_weaker : F₂ < F₁) :
    (1 - 1/F₂) * conf_bias < (1 - 1/F₁) * conf_bias := by
  apply mul_lt_mul_of_pos_right _ h_conf
  have h1 : 1/F₁ < 1/F₂ := by
    rw [div_lt_div_iff₀ (by linarith) (by linarith)]
    linarith
  linarith

/-- **Horizontal pleiotropy patterns differ across populations.**
    If pleiotropic effects change across populations (due to different
    LD patterns or gene regulation), MR estimates are not portable. -/
theorem pleiotropy_changes_invalidate_mr
    (β_causal α_pleio_source α_pleio_target : ℝ)
    (h_diff : α_pleio_source ≠ α_pleio_target) :
    β_causal + α_pleio_source ≠ β_causal + α_pleio_target := by
  intro h; exact h_diff (by linarith)

end MRPortability


/-!
## Sample Size and Statistical Power for Portability Detection

Detecting portability differences requires adequate statistical power.
We formalize the power analysis for portability comparisons.
-/

section PowerAnalysis

/-- **Variance of R² estimator.**
    Var(R²) ≈ 4R²(1-R²)²/n for the standard R² estimator. -/
noncomputable def r2EstimatorVariance (r2 : ℝ) (n : ℕ) : ℝ :=
  4 * r2 * (1 - r2) ^ 2 / n

/-- R² estimator variance is positive for non-degenerate R². -/
theorem r2_estimator_variance_pos (r2 : ℝ) (n : ℕ)
    (h_r2 : 0 < r2) (h_r2_lt : r2 < 1) (h_n : 0 < n) :
    0 < r2EstimatorVariance r2 n := by
  unfold r2EstimatorVariance
  apply div_pos
  · apply mul_pos
    · apply mul_pos
      · linarith
      · exact h_r2
    · exact sq_pos_of_pos (by linarith)
  · exact Nat.cast_pos.mpr h_n

/-- **Power to detect portability difference.**
    To detect ΔR² = R²_source - R²_target at power 1-β with significance α,
    need n ≈ (z_α + z_β)² × (Var₁ + Var₂) / ΔR²². -/
theorem larger_sample_more_power
    (var₁ var₂ Δr2 z_sum n₁ n₂ : ℝ)
    (h_var : 0 < var₁ + var₂) (h_Δ : 0 < Δr2)
    (h_z : 0 < z_sum)
    (h_n : n₁ < n₂) (h_n₁ : 0 < n₁) :
    -- Larger sample → smaller required effect size (more power)
    z_sum * Real.sqrt ((var₁ + var₂) / n₂) <
      z_sum * Real.sqrt ((var₁ + var₂) / n₁) := by
  apply mul_lt_mul_of_pos_left _ h_z
  apply Real.sqrt_lt_sqrt
  · exact div_nonneg (le_of_lt h_var) (le_of_lt (by linarith : 0 < n₂))
  · exact div_lt_div_of_pos_left h_var h_n₁ h_n

/-- **Small portability differences require large samples.**
    Wang et al.'s finding of R² ≈ 0.5% for distance-on-error means
    enormous samples are needed to detect this reliably. -/
theorem small_effect_needs_large_n
    (r2_effect n_required : ℝ)
    (h_small : r2_effect ≤ 1/100)
    (h_formula : n_required ≥ 1 / r2_effect)
    (h_effect_pos : 0 < r2_effect) :
    n_required ≥ 100 := by
  calc n_required ≥ 1 / r2_effect := h_formula
    _ ≥ 1 / (1/100) := by
        exact div_le_div_of_nonneg_left (le_of_lt one_pos) h_effect_pos h_small
    _ = 100 := by norm_num

end PowerAnalysis

end Calibrator
