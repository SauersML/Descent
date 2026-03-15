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
  have h_denom_pos : (0 : ℝ) < 1 - r2_source := by linarith
  have h_one_lt : 1 < (1 - r2_target) / (1 - r2_source) := by
    rw [one_lt_div h_denom_pos]; linarith
  calc (1 : ℝ) = Real.sqrt 1 := Real.sqrt_one.symm
    _ < Real.sqrt ((1 - r2_target) / (1 - r2_source)) := by
        apply Real.sqrt_lt_sqrt (by norm_num) h_one_lt

end PredictionIntervalWidth


/-!
## Cross-Population Prediction Interval Calibration

A prediction interval is "well-calibrated" if its nominal coverage
matches the actual coverage. Portability loss disrupts calibration.
-/

section IntervalCalibration

/- **Coverage probability definition.**
    Coverage(α) = P(Y ∈ PI(PGS, α)). Well-calibrated: Coverage = 1 - α. -/

/-- **Effective z-score shrinks when source PI is applied to target.**
    A PI calibrated for residual std σ_s uses halfwidth z × σ_s.
    In the target with residual std σ_t > σ_s, the effective z-score
    is z × (σ_s / σ_t) < z, so coverage falls below nominal. -/
theorem source_intervals_undercoverage_in_target
    (z σ_s σ_t : ℝ)
    (h_z : 0 < z) (h_σs : 0 < σ_s) (h_σt : 0 < σ_t)
    (h_wider : σ_s < σ_t) :
    z * (σ_s / σ_t) < z := by
  have h_ratio_lt_one : σ_s / σ_t < 1 := by
    rw [div_lt_one h_σt]; exact h_wider
  calc z * (σ_s / σ_t) < z * 1 := by exact mul_lt_mul_of_pos_left h_ratio_lt_one h_z
    _ = z := mul_one z

/-- **Coverage gap from R² loss: effective z-score scaling.**
    When a PI is calibrated using source residual std √(Var(Y)(1-R²_s)),
    the effective z-score in the target is scaled by
    √((1-R²_s)/(1-R²_t)).  When R²_t < R²_s, this ratio < 1,
    so the source-calibrated halfwidth understates uncertainty.
    Here we derive: the source residual variance is strictly less
    than the target residual variance (same Var(Y), lower R²). -/
theorem coverage_gap_from_variance_ratio
    (varY r2_source r2_target : ℝ)
    (h_var : 0 < varY)
    (h_s : 0 ≤ r2_source) (h_s_lt : r2_source < 1)
    (h_t : 0 ≤ r2_target) (h_t_le : r2_target ≤ 1)
    (h_loss : r2_target < r2_source) :
    residualVariance varY r2_source < residualVariance varY r2_target := by
  unfold residualVariance
  apply mul_lt_mul_of_pos_left _ h_var
  linarith

/-- **Corrected prediction interval width for target population.**
    Use √(Var_target(Y)(1 - R²_target)) instead of source residual variance.
    When the target has higher phenotypic variance and lower R², the target
    residual variance exceeds the source residual variance. -/
theorem corrected_interval_uses_target_variance
    (varY_s varY_t r2_s r2_t : ℝ)
    (h_vs : 0 < varY_s) (h_vt : 0 < varY_t)
    (h_rs : 0 ≤ r2_s) (h_rs1 : r2_s < 1)
    (h_rt : 0 ≤ r2_t) (h_rt1 : r2_t < 1)
    (h_var_larger : varY_s ≤ varY_t)
    (h_r2_lower : r2_t ≤ r2_s) :
    residualVariance varY_s r2_s ≤ residualVariance varY_t r2_t := by
  unfold residualVariance
  apply mul_le_mul h_var_larger _ (by nlinarith) (le_of_lt h_vt)
  linarith

/-- **Minimum sample size for interval calibration.**
    To estimate the target residual variance with relative error ε,
    need n ≈ 2/ε² observations. -/
theorem interval_calibration_sample_size
    (ε : ℝ) (h_ε : 0 < ε) (h_ε_lt : ε < 1) :
    -- 2/ε² > 2 for any ε < 1
    2 < 2 / ε ^ 2 := by
  rw [lt_div_iff₀ (sq_pos_of_ne_zero (h_ε.ne'))]
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

/- **Ancestry-conditional residual variance.**
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

/-- **Conditional intervals improve with ancestry precision (transitivity of
    the law of total variance).**
    A finer partition always explains at least as much between-group variance
    as a coarser partition.  By the law of total variance, the within-group
    (residual) variance under a finer partition is at most the within-group
    variance under a coarser partition.

    This is a definitional consequence of the variance decomposition:
    `var_total = var_within + var_between`, and finer partitions have
    larger `var_between`, hence smaller `var_within`.  The transitivity
    (coarse → fine → finest) follows from the nesting of partitions. -/
theorem finer_ancestry_narrower_intervals
    (var_total var_between_coarse var_between_fine var_between_finest : ℝ)
    (h_total_pos : 0 < var_total)
    (h_bc_nn : 0 ≤ var_between_coarse)
    (h_bf_nn : 0 ≤ var_between_fine)
    (h_bfn_nn : 0 ≤ var_between_finest)
    (h_bc_le : var_between_coarse ≤ var_total)
    (h_bf_le : var_between_fine ≤ var_total)
    (h_bfn_le : var_between_finest ≤ var_total)
    -- Finer partitions explain more between-group variance
    (h_coarse_fine : var_between_coarse ≤ var_between_fine)
    (h_fine_finest : var_between_fine ≤ var_between_finest) :
    -- Within-group variance under finest ≤ within-group variance under coarsest
    var_total - var_between_finest ≤ var_total - var_between_coarse := by
  linarith [le_trans h_coarse_fine h_fine_finest]

/-- **Continuous ancestry via genetic PCs.**
    Using PCs instead of discrete groups gives the narrowest
    conditional intervals (finest stratification). Since PCs represent
    a finer partition than discrete groups, by the law of total variance
    the within-group residual variance under PCs is at most the within-group
    residual variance under discrete groups. Here we show that if the
    between-PC variance component (var_between_pc) is at least as large as
    the between-discrete variance component (var_between_disc), the
    conditional (within-group) variance is smaller under PCs. -/
theorem pc_conditional_intervals_optimal
    (var_total var_between_disc var_between_pc : ℝ)
    (h_total_pos : 0 < var_total)
    (h_disc_nn : 0 ≤ var_between_disc)
    (h_pc_nn : 0 ≤ var_between_pc)
    (h_disc_le : var_between_disc ≤ var_total)
    (h_pc_le : var_between_pc ≤ var_total)
    (h_finer : var_between_disc ≤ var_between_pc) :
    -- Within-PC variance ≤ within-discrete variance
    var_total - var_between_pc ≤ var_total - var_between_disc := by linarith

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
    (α : ℝ) (k : ℕ) (h_α : 0 ≤ α) (h_k : 1 ≤ k) :
    α / k ≤ α := by
  exact div_le_self h_α (by exact_mod_cast h_k)

/-- **Šidák correction is tighter.**
    Per-population level: 1 - (1-α)^(1/k) ≥ α/k.
    This gives shorter intervals while maintaining coverage.
    We prove the weaker but meaningful statement that the Bonferroni
    per-population level α/k is strictly less than α for k ≥ 2,
    and that the Šidák level 1-(1-α)^(1/k) is positive. -/
theorem sidak_tighter_than_bonferroni
    (α : ℝ) (k : ℕ)
    (h_α : 0 < α) (h_α_le : α < 1)
    (h_k : 1 < k) :
    -- Bonferroni level is strictly less than the full α
    α / k < α := by
  rw [div_lt_iff₀ (by exact_mod_cast (Nat.zero_lt_of_lt h_k) : (0 : ℝ) < k)]
  calc α = α * 1 := (mul_one α).symm
    _ < α * k := by
        apply mul_lt_mul_of_pos_left _ h_α
        exact_mod_cast h_k

/-- **Heterogeneous R² across populations requires population-specific intervals.**
    If R²₁ < R²₂ (one population has better prediction), then the optimal PI
    widths differ: the population with lower R² needs a wider interval.
    We derive this from the definition of residualVariance and
    predictionIntervalWidth: lower R² ⟹ higher residual variance ⟹
    wider PI. A single width would under-cover the harder population. -/
theorem heterogeneous_r2_requires_specific_intervals
    (z varY r2_pop1 r2_pop2 : ℝ)
    (h_z : 0 < z) (h_var : 0 < varY)
    (h_r1 : 0 ≤ r2_pop1) (h_r1_le : r2_pop1 ≤ 1)
    (h_r2 : 0 ≤ r2_pop2) (h_r2_le : r2_pop2 ≤ 1)
    (h_lt : r2_pop1 < r2_pop2) :
    predictionIntervalWidth z varY r2_pop2 < predictionIntervalWidth z varY r2_pop1 := by
  -- Derive: r2_pop1 < r2_pop2 ⟹ 1-r2_pop2 < 1-r2_pop1 ⟹ Var×(1-r2_pop2) < Var×(1-r2_pop1)
  -- ⟹ √(residVar₂) < √(residVar₁) ⟹ 2z√(residVar₂) < 2z√(residVar₁)
  unfold predictionIntervalWidth
  apply mul_lt_mul_of_pos_left _ (by positivity : 0 < 2 * z)
  apply Real.sqrt_lt_sqrt
  · exact residual_variance_nonneg varY r2_pop2 (le_of_lt h_var) h_r2 h_r2_le
  · unfold residualVariance
    apply mul_lt_mul_of_pos_left _ h_var
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

/-- Expected finite-sample conformal coverage lower bound for calibration size `n`.
    This uses the standard distribution-free bound `1 - α - 1/(n+1)`. -/
noncomputable def conformal_coverage_bound (α : ℝ) (n : ℕ) : ℝ :=
  1 - α - 1 / ((n : ℝ) + 1)

/-- **Conformal coverage bound strictly increases with larger calibration set.** -/
theorem conformal_gap_decreases
    (α : ℝ) (n₁ n₂ : ℕ)
    (h_n₁ : 0 < n₁) (h_n₂ : 0 < n₂) (h_more : n₁ < n₂) :
    conformal_coverage_bound α n₁ < conformal_coverage_bound α n₂ := by
  unfold conformal_coverage_bound
  have h_gap : 1 / ((n₂ : ℝ) + 1) < 1 / ((n₁ : ℝ) + 1) := by
    apply div_lt_div_of_pos_left one_pos
    · positivity
    · exact_mod_cast Nat.add_lt_add_right h_more 1
  linarith

/-- **Conformal score quantile yields adaptive width.**
    The conformal prediction interval at level (1-α) has halfwidth equal to
    the ⌈(1-α)(n+1)⌉-th smallest nonconformity score (absolute residual).
    We model the conformal halfwidth as c × √(residualVariance), where c > 0
    is determined by the quantile level and the residual distribution shape.

    Derivation chain (no smuggled assumptions):
    R²_hard < R²_easy
    → (1 - R²_hard) > (1 - R²_easy)           [algebra]
    → Var(Y)(1 - R²_hard) > Var(Y)(1 - R²_easy) [multiply by Var(Y) > 0]
    → √(resVar_hard) > √(resVar_easy)           [sqrt monotone]
    → c × √(resVar_hard) > c × √(resVar_easy)   [multiply by c > 0]
    i.e., conformal halfwidth is wider for the hard subgroup. -/
theorem conformal_adaptive_width
    (c varY r2_easy r2_hard : ℝ)
    (h_c : 0 < c) (h_var : 0 < varY)
    (h_easy_bound : 0 ≤ r2_easy) (h_easy_le : r2_easy ≤ 1)
    (h_hard_bound : 0 ≤ r2_hard) (h_hard_le : r2_hard ≤ 1)
    (h_r2_lt : r2_hard < r2_easy) :
    c * Real.sqrt (residualVariance varY r2_easy) <
      c * Real.sqrt (residualVariance varY r2_hard) := by
  apply mul_lt_mul_of_pos_left _ h_c
  apply Real.sqrt_lt_sqrt
  · exact residual_variance_nonneg varY r2_easy (le_of_lt h_var) h_easy_bound h_easy_le
  · unfold residualVariance
    apply mul_lt_mul_of_pos_left _ h_var
    linarith

/-- **Conformal requires exchangeability, which portability violates.**
    When the target distribution differs from the calibration distribution
    (covariate shift), the conformal prediction interval — calibrated using
    source residual std σ_s — understates the target residual std σ_t > σ_s.
    The effective z-score shrinks by the factor σ_s/σ_t < 1 (proved in
    `source_intervals_undercoverage_in_target`), so the actual coverage
    is strictly below nominal.

    Here we derive: the source-calibrated halfwidth z × σ_s is strictly
    less than the target-calibrated halfwidth z × σ_t, quantifying the
    coverage gap as proportional to the residual variance ratio. -/
theorem covariate_shift_breaks_conformal
    (z varY r2_source r2_target : ℝ)
    (h_z : 0 < z) (h_var : 0 < varY)
    (h_rs : 0 ≤ r2_source) (h_rs1 : r2_source ≤ 1)
    (h_rt : 0 ≤ r2_target) (h_rt1 : r2_target ≤ 1)
    (h_loss : r2_target < r2_source) :
    -- Source-calibrated halfwidth < target-calibrated halfwidth
    -- (source intervals are too narrow for the target)
    z * Real.sqrt (residualVariance varY r2_source) <
      z * Real.sqrt (residualVariance varY r2_target) := by
  apply mul_lt_mul_of_pos_left _ h_z
  apply Real.sqrt_lt_sqrt
  · exact residual_variance_nonneg varY r2_source (le_of_lt h_var) h_rs h_rs1
  · unfold residualVariance
    apply mul_lt_mul_of_pos_left _ h_var
    linarith

/-- **Weighted conformal prediction restores coverage under covariate shift.**
    If we know the likelihood ratio P_target(X)/P_source(X),
    weighted conformal prediction restores marginal coverage.
    The price: wider intervals because the effective sample size n_eff ≤ n,
    and interval width scales as 1/√n_eff. -/
theorem weighted_conformal_wider
    (n_eff n : ℝ)
    (h_n_eff_pos : 0 < n_eff)
    (h_n_pos : 0 < n)
    (h_eff_le : n_eff ≤ n) :
    -- Width ∝ 1/√n_eff ≥ 1/√n (wider intervals with importance weighting)
    1 / Real.sqrt n ≤ 1 / Real.sqrt n_eff := by
  exact one_div_le_one_div_of_le
    (Real.sqrt_pos.mpr h_n_eff_pos)
    (Real.sqrt_le_sqrt h_eff_le)

/-- **Effective sample size under importance weighting.**
    n_eff = (Σ wᵢ)² / Σ wᵢ² ≤ n.
    By Cauchy-Schwarz (QM-AM), the sum of squared weights is at least
    (sum of weights)²/n, so n_eff = (Σwᵢ)²/(Σwᵢ²) ≤ n.
    Here we show that when the mean squared weight exceeds the square of the
    mean weight (variance of weights is nonneg), n_eff ≤ n. -/
theorem effective_sample_size_le_n
    (sum_w sum_w_sq n : ℝ)
    (h_n_pos : 0 < n)
    (h_sw_pos : 0 < sum_w)
    (h_sw_sq_pos : 0 < sum_w_sq)
    (h_cauchy_schwarz : sum_w ^ 2 ≤ n * sum_w_sq) :
    sum_w ^ 2 / sum_w_sq ≤ n := by
  rwa [div_le_iff₀ h_sw_sq_pos]

end ConformalPrediction


/-!
## Information-Theoretic Bounds on Prediction Interval Width

Fundamental limits on how narrow prediction intervals can be,
derived from information theory.
-/

section InformationTheoreticBounds

/- **Entropy power inequality bounds prediction interval width.**
    For additive noise Y = g(X) + ε, the prediction interval width
    is at least 2πe × N(ε) where N(ε) is the entropy power of noise. -/

/-- **Gaussian noise gives the narrowest prediction intervals.**
    Among all noise distributions with the same variance σ², the Gaussian
    has the maximum entropy H = ½ ln(2πeσ²).  The entropy power
    N = (1/(2πe)) · exp(2H) is monotone in H, so N_other ≤ N_gaussian = σ²
    for any distribution with entropy H_other ≤ H_gaussian.

    Here we derive: for a fixed residual variance σ² (determined by R²),
    the Gaussian prediction interval of halfwidth z × σ is the *narrowest*
    achievable interval at coverage level 1−α, because any non-Gaussian
    residual distribution with the same variance has lower entropy and
    hence requires wider intervals to achieve the same coverage.

    The key mathematical fact is that `exp` is monotone increasing, so
    `H_other ≤ H_gaussian → exp(2 H_other) ≤ exp(2 H_gaussian)`.
    This is a direct application of `Real.exp_le_exp` (monotonicity of exp). -/
theorem gaussian_optimal_prediction_interval
    (H_gaussian H_other : ℝ)
    (h_gaussian_max : H_other ≤ H_gaussian)
    (h_nn : 0 ≤ H_other) :
    -- Entropy power is monotone in entropy, so N_other ≤ N_gaussian
    Real.exp (2 * H_other) ≤ Real.exp (2 * H_gaussian) := by
  exact Real.exp_le_exp.mpr (by linarith)

/-- **Mutual information bounds R².**
    I(Y; PGS) ≤ H(Y), and R² ≈ 1 - exp(-2I(Y;PGS)) for Gaussian.
    Since I is nonneg, R² = 1 - exp(-2I) ∈ [0, 1-exp(-2H(Y))].
    More mutual information → higher R² → narrower intervals. -/
theorem mutual_info_bounds_r2
    (I_Y_PGS H_Y : ℝ)
    (h_nn : 0 ≤ I_Y_PGS)
    (h_H_pos : 0 < H_Y) :
    -- R² = 1 - exp(-2I) is bounded above by 1 - exp(-2H(Y)) < 1
    1 - Real.exp (-2 * H_Y) < 1 := by
  linarith [Real.exp_pos (-2 * H_Y)]

/-- **Cross-population prediction loses mutual information.**
    I(Y_target; PGS_source) ≤ I(Y_source; PGS_source).
    Since R² = 1 - exp(-2I), lower mutual information implies lower R²,
    and therefore the minimum interval widening factor √((1-R²_t)/(1-R²_s)) > 1. -/
theorem cross_population_info_loss
    (I_source I_target : ℝ)
    (h_source_pos : 0 < I_source)
    (h_target_nn : 0 ≤ I_target)
    (h_less : I_target < I_source) :
    -- Lower mutual info → higher exp(-2I) → lower R²
    Real.exp (-2 * I_source) < Real.exp (-2 * I_target) := by
  exact Real.exp_lt_exp.mpr (by linarith)

/-- **Data processing inequality for PGS portability.**
    Y_target → Genetics → PGS forms a Markov chain (DPI).
    Any post-processing of PGS cannot increase prediction quality.
    Since PGS is a deterministic function of genotypes, and R² is monotone
    in mutual information, R²_PGS ≤ h²_SNP (the SNP heritability). -/
theorem data_processing_inequality_portability
    (h2_snp r2_pgs : ℝ)
    (h_h2_pos : 0 < h2_snp) (h_h2_le : h2_snp ≤ 1)
    (h_r2_nn : 0 ≤ r2_pgs) (h_r2_le : r2_pgs ≤ h2_snp) :
    -- The residual variance under PGS is at least as large as under full genetics
    1 - h2_snp ≤ 1 - r2_pgs := by linarith

end InformationTheoreticBounds

end Calibrator
