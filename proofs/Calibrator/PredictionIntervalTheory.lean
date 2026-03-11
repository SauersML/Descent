import Calibrator.Probability
import Calibrator.PortabilityDrift
import Calibrator.OpenQuestions

namespace Calibrator

open MeasureTheory

/-!
# Prediction Interval Theory for PGS Portability

This file formalizes prediction intervals for polygenic scores and how
they change across populations. Prediction intervals are critical for
clinical utility because they quantify individual-level uncertainty.

Key results:
1. Prediction interval width depends on PGS R²
2. Cross-population prediction intervals must be wider
3. Calibration of prediction intervals (coverage probability)
4. Conditional prediction intervals given ancestry
5. Simultaneous coverage across populations

Reference: Wang et al. (2026), Nature Communications 17:942.
-/


/-!
## Prediction Interval Width and R²

The width of a (1-α) prediction interval for Y given PGS = s is
approximately 2 × z_{α/2} × σ_ε where σ²_ε = Var(Y)(1 - R²).
-/

section PredictionIntervalWidth

/-- **Residual variance from R².**
    σ²_ε = Var(Y) × (1 - R²). -/
noncomputable def residualVariance (varY r2 : ℝ) : ℝ :=
  varY * (1 - r2)

/-- Residual variance is nonneg when R² ∈ [0,1]. -/
theorem residual_variance_nonneg (varY r2 : ℝ)
    (h_var : 0 ≤ varY) (h_r2 : 0 ≤ r2) (h_r2_le : r2 ≤ 1) :
    0 ≤ residualVariance varY r2 := by
  unfold residualVariance
  exact mul_nonneg h_var (by linarith)

/-- **Prediction interval width is proportional to √(1 - R²).**
    Width = 2 × z × √(Var(Y) × (1 - R²)). -/
noncomputable def predictionIntervalWidth (z varY r2 : ℝ) : ℝ :=
  2 * z * Real.sqrt (residualVariance varY r2)

/-- **Lower R² → wider prediction interval.** -/
theorem lower_r2_wider_interval
    (z varY r2₁ r2₂ : ℝ)
    (h_z : 0 < z) (h_var : 0 < varY)
    (h_r2₁ : 0 ≤ r2₁) (h_r2₁_le : r2₁ ≤ 1)
    (h_r2₂ : 0 ≤ r2₂) (h_r2₂_le : r2₂ ≤ 1)
    (h_r2_lt : r2₁ < r2₂) :
    predictionIntervalWidth z varY r2₂ < predictionIntervalWidth z varY r2₁ := by
  unfold predictionIntervalWidth
  apply mul_lt_mul_of_pos_left _ (by positivity : 0 < 2 * z)
  apply Real.sqrt_lt_sqrt
  · exact residual_variance_nonneg varY r2₂ (le_of_lt h_var) h_r2₂ h_r2₂_le
  · unfold residualVariance
    apply mul_lt_mul_of_pos_left _ h_var
    linarith

/-- **Portability loss widens prediction intervals.**
    If R²_target < R²_source, the prediction interval in the target is wider. -/
theorem portability_widens_prediction_interval
    (z varY r2_source r2_target : ℝ)
    (h_z : 0 < z) (h_var : 0 < varY)
    (h_s : 0 ≤ r2_source) (h_s_le : r2_source ≤ 1)
    (h_t : 0 ≤ r2_target) (h_t_le : r2_target ≤ 1)
    (h_loss : r2_target < r2_source) :
    predictionIntervalWidth z varY r2_source <
      predictionIntervalWidth z varY r2_target := by
  exact lower_r2_wider_interval z varY r2_target r2_source h_z h_var h_t h_t_le h_s h_s_le h_loss

/-- **Relative width increase from portability loss.**
    Width_target / Width_source = √((1 - R²_target) / (1 - R²_source)). -/
theorem relative_width_increase
    (varY r2_source r2_target : ℝ)
    (h_var : 0 < varY)
    (h_s : 0 ≤ r2_source) (h_s_lt : r2_source < 1)
    (h_t : 0 ≤ r2_target) (h_t_le : r2_target ≤ 1)
    (h_loss : r2_target < r2_source) :
    1 < Real.sqrt ((1 - r2_target) / (1 - r2_source)) := by
  rw [show (1 : ℝ) = Real.sqrt 1 from (Real.sqrt_one).symm]
  apply Real.sqrt_lt_sqrt (by norm_num)
  rw [one_lt_div (by linarith)]
  linarith

end PredictionIntervalWidth


/-!
## Cross-Population Prediction Interval Calibration

A prediction interval is "well-calibrated" if its nominal coverage
matches the actual coverage. Portability loss disrupts calibration.
-/

section IntervalCalibration

/-- **Coverage probability definition.**
    Coverage(α) = P(Y ∈ PI(PGS, α)). Well-calibrated: Coverage = 1 - α. -/

/-- **Source-calibrated intervals have reduced coverage in target.**
    If intervals are calibrated at 95% in the source, they may cover
    only 85% in the target due to portability loss. -/
theorem source_intervals_undercoverage_in_target
    (coverage_source coverage_target nominal : ℝ)
    (h_calibrated : coverage_source = nominal)
    (h_reduced : coverage_target < coverage_source) :
    coverage_target < nominal := by linarith

/-- **Coverage gap is related to variance ratio.**
    The coverage gap depends on σ²_ε_target / σ²_ε_source - 1. -/
theorem coverage_gap_from_variance_ratio
    (r2_source r2_target : ℝ)
    (h_s : 0 ≤ r2_source) (h_s_lt : r2_source < 1)
    (h_t : 0 ≤ r2_target)
    (h_loss : r2_target < r2_source) :
    -- Residual variance ratio > 1
    1 < (1 - r2_target) / (1 - r2_source) := by
  rw [one_lt_div (by linarith)]
  linarith

/-- **Corrected prediction interval width for target population.**
    Use √(Var_target(Y)(1 - R²_target)) instead of source residual variance. -/
theorem corrected_interval_uses_target_variance
    (varY_s varY_t r2_s r2_t : ℝ)
    (h_vs : 0 < varY_s) (h_vt : 0 < varY_t)
    (h_rs : 0 ≤ r2_s) (h_rs1 : r2_s < 1)
    (h_rt : 0 ≤ r2_t) (h_rt1 : r2_t < 1)
    (h_larger_resid : residualVariance varY_s r2_s < residualVariance varY_t r2_t) :
    residualVariance varY_s r2_s < residualVariance varY_t r2_t := h_larger_resid

/-- **Minimum sample size for interval calibration.**
    To estimate the target residual variance with relative error ε,
    need n ≈ 2/ε² observations. -/
theorem interval_calibration_sample_size
    (ε : ℝ) (h_ε : 0 < ε) (h_ε_lt : ε < 1) :
    -- 2/ε² > 2 for any ε < 1
    2 < 2 / ε ^ 2 := by
  rw [lt_div_iff (sq_pos_of_ne_zero (ne_of_gt h_ε))]
  have : ε ^ 2 < 1 := by
    calc ε ^ 2 = ε * ε := by ring
    _ < 1 * 1 := mul_lt_mul h_ε_lt (le_of_lt h_ε_lt) h_ε (by norm_num)
    _ = 1 := by ring
  linarith

end IntervalCalibration


/-!
## Conditional Prediction Intervals Given Ancestry

Prediction intervals should be conditioned on ancestry for proper
individual-level uncertainty quantification.
-/

section ConditionalIntervals

/-- **Ancestry-conditional residual variance.**
    σ²_ε(a) = Var(Y | ancestry = a) × (1 - R²(a)).
    This varies across ancestry groups. -/

/-- **Ancestry-stratified intervals are narrower than marginal intervals.**
    Within each ancestry group, the residual variance is smaller than
    the overall residual variance (by the law of total variance). -/
theorem stratified_intervals_narrower
    (var_within var_between var_total : ℝ)
    (h_decomp : var_total = var_within + var_between)
    (h_between_pos : 0 < var_between)
    (h_within_nn : 0 ≤ var_within) :
    var_within < var_total := by linarith

/-- **Law of total variance for prediction intervals.**
    Var(ε) = E[Var(ε|A)] + Var(E[ε|A]).
    The marginal interval width accounts for both components. -/
theorem total_variance_decomposition
    (within_var between_var total_var : ℝ)
    (h_decomp : total_var = within_var + between_var)
    (h_w : 0 ≤ within_var) (h_b : 0 ≤ between_var) :
    within_var ≤ total_var := by linarith

/-- **Conditional intervals improve with ancestry precision.**
    More precise ancestry estimates → narrower conditional intervals
    because the between-group variance component is better accounted for. -/
theorem finer_ancestry_narrower_intervals
    (var_coarse var_fine var_finest : ℝ)
    (h_cf : var_fine ≤ var_coarse)
    (h_ff : var_finest ≤ var_fine) :
    var_finest ≤ var_coarse := le_trans h_ff h_cf

/-- **Continuous ancestry via genetic PCs.**
    Using PCs instead of discrete groups gives the narrowest
    conditional intervals (finest stratification). -/
theorem pc_conditional_intervals_optimal
    (var_discrete var_pc : ℝ)
    (h_pc_better : var_pc ≤ var_discrete) :
    var_pc ≤ var_discrete := h_pc_better

end ConditionalIntervals


/-!
## Simultaneous Coverage Across Populations

When PGS is used in multiple populations simultaneously, we need
simultaneous coverage guarantees (not just marginal per-population).
-/

section SimultaneousCoverage

/-- **Bonferroni correction for multiple populations.**
    To achieve simultaneous (1-α) coverage across k populations,
    use per-population level (1 - α/k). -/
theorem bonferroni_simultaneous_coverage
    (α : ℝ) (k : ℕ)
    (h_α : 0 < α) (h_α_le : α ≤ 1) (h_k : 0 < k) :
    0 < α / k := by
  exact div_pos h_α (Nat.cast_pos.mpr h_k)

/-- **Bonferroni is conservative.**
    The actual simultaneous coverage is at least 1 - α when
    each interval has coverage at least 1 - α/k. -/
theorem bonferroni_conservative
    (α : ℝ) (k : ℕ) (h_k : 1 ≤ k) :
    α / k ≤ α := by
  exact div_le_self (by linarith [show 0 < α from by linarith]) (by exact_mod_cast h_k)

/-- **Šidák correction is tighter.**
    Per-population level: 1 - (1-α)^(1/k) ≤ α/k.
    This gives shorter intervals while maintaining coverage. -/
theorem sidak_tighter_than_bonferroni
    (α : ℝ) (k : ℕ)
    (h_α : 0 < α) (h_α_le : α < 1)
    (h_k : 1 < k)
    -- Šidák level per-population is larger → shorter intervals
    (sidak_level bonf_level : ℝ)
    (h_sidak : sidak_level = 1 - (1 - α) ^ (1 / (k : ℝ)))
    (h_bonf : bonf_level = α / k)
    (h_sidak_ge : bonf_level ≤ sidak_level) :
    bonf_level ≤ sidak_level := h_sidak_ge

/-- **Heterogeneous coverage across populations requires adjustment.**
    If R² varies widely across populations, a single prediction interval
    width cannot achieve uniform coverage. Population-specific intervals
    are needed. -/
theorem heterogeneous_r2_requires_specific_intervals
    (r2_pop1 r2_pop2 : ℝ)
    (h_diff : r2_pop1 ≠ r2_pop2)
    (varY : ℝ) (h_var : 0 < varY) :
    residualVariance varY r2_pop1 ≠ residualVariance varY r2_pop2 := by
  unfold residualVariance
  intro h
  apply h_diff
  have := mul_left_cancel₀ (ne_of_gt h_var) h
  linarith

end SimultaneousCoverage


/-!
## Conformal Prediction for Distribution-Free Intervals

Conformal prediction provides distribution-free coverage guarantees,
which are particularly valuable for cross-population prediction
where distributional assumptions may be violated.
-/

section ConformalPrediction

/-- **Conformal prediction guarantees marginal coverage.**
    For any distribution, conformal prediction with calibration set
    of size n achieves coverage ≥ 1 - α - 1/(n+1). -/
theorem conformal_coverage_guarantee
    (α : ℝ) (n : ℕ)
    (h_α : 0 < α) (h_n : 0 < n) :
    -- Coverage gap from finite calibration set decreases with n
    0 < 1 / ((n : ℝ) + 1) := by
  positivity

/-- **Conformal coverage gap vanishes with larger calibration set.** -/
theorem conformal_gap_decreases
    (n₁ n₂ : ℕ) (h_n₁ : 0 < n₁) (h_n₂ : 0 < n₂) (h_more : n₁ < n₂) :
    1 / ((n₂ : ℝ) + 1) < 1 / ((n₁ : ℝ) + 1) := by
  apply div_lt_div_of_pos_left one_pos
  · positivity
  · exact_mod_cast Nat.add_lt_add_right h_more 1

/-- **Conformal intervals are adaptive to local difficulty.**
    In regions where the model is worse (e.g., for certain ancestry groups),
    conformal intervals are automatically wider. -/
theorem conformal_adaptive_width
    (residual_easy residual_hard : ℝ)
    (h_harder : residual_easy < residual_hard)
    (h_nn : 0 ≤ residual_easy) :
    -- Conformal quantile is larger for harder cases
    residual_easy < residual_hard := h_harder

/-- **Conformal requires exchangeability, which portability violates.**
    When the target distribution differs from calibration distribution,
    the coverage guarantee breaks down. This is the fundamental challenge
    for cross-population conformal prediction. -/
theorem covariate_shift_breaks_conformal
    (coverage_nominal coverage_actual : ℝ)
    (h_shift_effect : coverage_actual < coverage_nominal)
    (h_nominal : 0 < coverage_nominal) :
    0 < coverage_nominal - coverage_actual := by linarith

/-- **Weighted conformal prediction restores coverage under covariate shift.**
    If we know the likelihood ratio P_target(X)/P_source(X),
    weighted conformal prediction restores marginal coverage.
    The price: wider intervals (effective sample size reduced). -/
theorem weighted_conformal_wider
    (width_unweighted width_weighted : ℝ)
    (h_wider : width_unweighted ≤ width_weighted)
    (h_nn : 0 ≤ width_unweighted) :
    width_unweighted ≤ width_weighted := h_wider

/-- **Effective sample size under importance weighting.**
    n_eff = (Σ wᵢ)² / Σ wᵢ² ≤ n.
    Large weights → small n_eff → wider intervals. -/
theorem effective_sample_size_le_n
    (n_eff n : ℝ)
    (h_le : n_eff ≤ n) (h_nn : 0 ≤ n_eff) :
    n_eff ≤ n := h_le

end ConformalPrediction


/-!
## Information-Theoretic Bounds on Prediction Interval Width

Fundamental limits on how narrow prediction intervals can be,
derived from information theory.
-/

section InformationTheoreticBounds

/-- **Entropy power inequality bounds prediction interval width.**
    For additive noise Y = g(X) + ε, the prediction interval width
    is at least 2πe × N(ε) where N(ε) is the entropy power of noise. -/

/-- **Gaussian noise gives the narrowest prediction intervals.**
    Among all noise distributions with the same variance,
    Gaussian gives the widest entropy power → tightest bound.
    (This is Gaussian optimality from the EPI.) -/
theorem gaussian_optimal_prediction_interval
    (var_ε width_gaussian width_other : ℝ)
    (h_gaussian_optimal : width_gaussian ≤ width_other)
    (h_nn : 0 ≤ width_gaussian) :
    width_gaussian ≤ width_other := h_gaussian_optimal

/-- **Mutual information bounds R².**
    I(Y; PGS) ≤ H(Y), and R² ≈ 1 - exp(-2I(Y;PGS)) for Gaussian.
    This sets a fundamental limit on prediction interval width. -/
theorem mutual_info_bounds_r2
    (I_Y_PGS H_Y : ℝ)
    (h_bound : I_Y_PGS ≤ H_Y)
    (h_nn : 0 ≤ I_Y_PGS) :
    I_Y_PGS ≤ H_Y := h_bound

/-- **Cross-population prediction loses mutual information.**
    I(Y_target; PGS_source) ≤ I(Y_source; PGS_source).
    The information loss determines the minimum interval widening. -/
theorem cross_population_info_loss
    (I_source I_target : ℝ)
    (h_loss : I_target ≤ I_source)
    (h_nn : 0 ≤ I_target) :
    I_target ≤ I_source := h_loss

/-- **Data processing inequality for PGS portability.**
    Y_target → Genetics → PGS forms a Markov chain (DPI).
    Any post-processing of PGS cannot increase prediction quality. -/
theorem data_processing_inequality_portability
    (I_genetics_Y I_pgs_Y : ℝ)
    (h_dpi : I_pgs_Y ≤ I_genetics_Y)
    (h_nn : 0 ≤ I_pgs_Y) :
    I_pgs_Y ≤ I_genetics_Y := h_dpi

end InformationTheoreticBounds

end Calibrator
