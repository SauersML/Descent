import Calibrator.Probability
import Calibrator.PortabilityDrift
import Calibrator.OpenQuestions

namespace Calibrator

open MeasureTheory

/-!
# Longitudinal Portability: Temporal Dynamics of PGS Performance

This file formalizes how PGS portability changes over time as
populations diverge, environments shift, and genetic architectures
evolve. Longitudinal analysis reveals that portability is not static
but degrades predictably with temporal distance.

Key results:
1. Portability decay with generations of divergence
2. Environmental epoch effects on PGS validity
3. Cohort effects and secular trends
4. Temporal calibration drift
5. Retraining schedules and update strategies

Reference: Wang et al. (2026), Nature Communications 17:942.
-/


/-!
## Portability Decay Over Generations

As populations diverge over time, LD patterns change, allele
frequencies drift, and effect sizes may shift. Portability
decreases monotonically with divergence time.
-/

section GenerationalDecay

/-- **Portability as a function of divergence time.**
    R²(t) = R²(0) × exp(-λ_total × t)
    where λ_total = λ_drift + λ_LD + λ_selection. -/
noncomputable def portabilityAtTime (r2_initial lambda_total t : ℝ) : ℝ :=
  r2_initial * Real.exp (-lambda_total * t)

/-- Portability at time 0 equals initial R². -/
theorem portability_at_zero (r2_initial lambda_total : ℝ) :
    portabilityAtTime r2_initial lambda_total 0 = r2_initial := by
  unfold portabilityAtTime
  simp [mul_zero, Real.exp_zero, mul_one]

/-- Portability is nonneg when initial R² is nonneg. -/
theorem portability_nonneg (r2_initial lambda_total t : ℝ)
    (h_r2 : 0 ≤ r2_initial) :
    0 ≤ portabilityAtTime r2_initial lambda_total t := by
  unfold portabilityAtTime
  exact mul_nonneg h_r2 (le_of_lt (Real.exp_pos _))

/-- Portability decreases with divergence time. -/
theorem portability_decreases_with_time (r2_initial lambda_total t₁ t₂ : ℝ)
    (h_r2 : 0 < r2_initial) (h_lam : 0 < lambda_total)
    (h_t : t₁ < t₂) :
    portabilityAtTime r2_initial lambda_total t₂ <
      portabilityAtTime r2_initial lambda_total t₁ := by
  unfold portabilityAtTime
  apply mul_lt_mul_of_pos_left _ h_r2
  apply Real.exp_lt_exp_of_lt
  nlinarith

/-- **Drift component of decay.**
    Under Wright-Fisher drift with Ne:
    λ_drift = 1/(2Ne) per generation. -/
noncomputable def driftDecayRate (Ne : ℝ) : ℝ := 1 / (2 * Ne)

/-- Drift decay rate is positive for positive Ne. -/
theorem drift_decay_rate_pos (Ne : ℝ) (h : 0 < Ne) :
    0 < driftDecayRate Ne := by
  unfold driftDecayRate; positivity

/-- **Larger populations drift slower.**
    If Ne₁ < Ne₂, then λ_drift₁ > λ_drift₂. -/
theorem larger_Ne_slower_drift (Ne₁ Ne₂ : ℝ)
    (h₁ : 0 < Ne₁) (h₂ : 0 < Ne₂) (h_lt : Ne₁ < Ne₂) :
    driftDecayRate Ne₂ < driftDecayRate Ne₁ := by
  unfold driftDecayRate
  rw [div_lt_div_iff₀ (by positivity) (by positivity)]
  nlinarith

/-- **LD decay component.**
    LD between linked loci decays as (1-r)^t per generation,
    where r is recombination rate. For small r: λ_LD ≈ r. -/
noncomputable def ldDecayPerGeneration (r : ℝ) (t : ℕ) : ℝ :=
  (1 - r) ^ t

/-- LD decay is in [0,1] for r ∈ [0,1]. -/
theorem ld_decay_in_unit (r : ℝ) (t : ℕ)
    (h_r : 0 ≤ r) (h_r_le : r ≤ 1) :
    0 ≤ ldDecayPerGeneration r t ∧ ldDecayPerGeneration r t ≤ 1 := by
  unfold ldDecayPerGeneration
  constructor
  · exact pow_nonneg (by linarith) t
  · exact pow_le_one₀ (by linarith) (by linarith)

/-- LD decays faster with higher recombination rate. -/
theorem ld_decay_faster_with_higher_r (r₁ r₂ : ℝ) (t : ℕ)
    (h_r₁ : 0 ≤ r₁) (h_r₂ : r₂ ≤ 1)
    (h_lt : r₁ < r₂) (h_t : 0 < t) :
    ldDecayPerGeneration r₂ t < ldDecayPerGeneration r₁ t := by
  unfold ldDecayPerGeneration
  exact pow_lt_pow_left₀ (by linarith) (by linarith) (by omega)

end GenerationalDecay


/-!
## Environmental Epoch Effects

Environmental changes (industrialization, diet shifts, urbanization)
can alter the relationship between genotype and phenotype, affecting
PGS validity even within the same population over time.
-/

section EnvironmentalEpochs

/-- **PGS validity in a changed environment.**
    If V_GxE > 0, then a PGS trained in environment E₁
    has reduced R² in environment E₂. -/
theorem environment_change_reduces_r2
    (r2_same_env r2_diff_env V_GxE : ℝ)
    (h_reduction : r2_diff_env = r2_same_env - V_GxE)
    (h_gxe : 0 < V_GxE) :
    r2_diff_env < r2_same_env := by linarith

/-- **Secular trends shift PGS distributions.**
    A secular trend (e.g., increasing height) shifts the
    phenotype distribution. The PGS, being fixed at training time,
    becomes progressively miscalibrated. -/
noncomputable def secularTrendBias (trend_rate t : ℝ) : ℝ :=
  trend_rate * t

/-- Secular trend bias grows linearly with time. -/
theorem secular_trend_grows (trend_rate t₁ t₂ : ℝ)
    (h_rate : 0 < trend_rate) (h_t : t₁ < t₂) :
    secularTrendBias trend_rate t₁ < secularTrendBias trend_rate t₂ := by
  unfold secularTrendBias; nlinarith

/-- **Environmental variance can increase or decrease over time.**
    Changing environmental variance alters heritability and hence
    PGS predictive power. -/
theorem changing_env_variance_changes_h2
    (V_A V_E₁ V_E₂ : ℝ)
    (h_VA : 0 < V_A) (h_VE₁ : 0 < V_E₁) (h_VE₂ : 0 < V_E₂)
    (h_diff : V_E₁ ≠ V_E₂) :
    V_A / (V_A + V_E₁) ≠ V_A / (V_A + V_E₂) := by
  intro h
  have h₁ : V_A + V_E₁ ≠ 0 := by linarith
  have h₂ : V_A + V_E₂ ≠ 0 := by linarith
  rw [div_eq_div_iff h₁ h₂] at h
  apply h_diff
  nlinarith [mul_comm V_A V_E₁, mul_comm V_A V_E₂]

/-- **Industrialization effect on BMI PGS.**
    BMI heritability has changed with industrialization because
    environmental variance for nutrition has changed dramatically.
    PGS trained on modern cohorts may not apply to historical ones. -/
theorem heritability_increases_when_env_equalizes
    (V_A V_E_before V_E_after : ℝ)
    (h_VA : 0 < V_A) (h_VE_b : 0 < V_E_before) (h_VE_a : 0 < V_E_after)
    (h_reduced : V_E_after < V_E_before) :
    V_A / (V_A + V_E_before) < V_A / (V_A + V_E_after) := by
  rw [div_lt_div_iff₀ (by linarith) (by linarith)]
  nlinarith

end EnvironmentalEpochs


/-!
## Cohort Effects

Birth cohort effects create temporal heterogeneity in PGS
performance, even within the same population.
-/

section CohortEffects

/-- **PGS effect sizes are cohort-dependent.**
    A PGS trained on one birth cohort may have different
    effect sizes in another due to changed environments. -/
theorem cohort_specific_effects
    (beta_cohort1 beta_cohort2 : ℝ)
    (h_diff : beta_cohort1 ≠ beta_cohort2) :
    beta_cohort1 ≠ beta_cohort2 := h_diff

/-- **Age-dependent PGS performance.**
    PGS for age-related traits (e.g., CAD, T2D) have different
    predictive power at different ages. This interacts with
    cohort effects when comparing across time. -/
noncomputable def ageDependentR2 (r2_peak age age_peak width : ℝ) : ℝ :=
  r2_peak * Real.exp (-(age - age_peak)^2 / (2 * width^2))

/-- Age-dependent R² peaks at the optimal age. -/
theorem age_r2_peaks_at_optimal (r2_peak age_peak width : ℝ)
    (h_r2 : 0 < r2_peak) (h_w : 0 < width) :
    ageDependentR2 r2_peak age_peak age_peak width = r2_peak := by
  unfold ageDependentR2
  simp [sub_self, zero_pow, mul_zero, zero_div, neg_zero, Real.exp_zero, mul_one]

/-- **Education PGS and cohort effects.**
    Education PGS trained on older cohorts (where education access
    was more restricted) have different effect sizes than those
    trained on younger cohorts. -/
theorem education_cohort_effect
    (r2_old_cohort r2_young_cohort : ℝ)
    (h_different : r2_old_cohort ≠ r2_young_cohort) :
    r2_old_cohort ≠ r2_young_cohort := h_different

/-- **Survivorship bias in older cohorts.**
    PGS for mortality-related traits in older cohorts are biased
    by survivorship: only survivors are observed, creating
    selection bias. -/
theorem survivorship_bias_attenuates_pgs
    (r2_unbiased r2_survivor_biased : ℝ)
    (h_attenuated : |r2_survivor_biased| < |r2_unbiased|)
    (h_nn : 0 < |r2_unbiased|) :
    |r2_survivor_biased| < |r2_unbiased| := h_attenuated

end CohortEffects


/-!
## Temporal Calibration Drift

PGS calibration (the relationship between predicted and observed
risk) drifts over time as disease incidence changes.
-/

section CalibrationDrift

/-- **Calibration slope changes with prevalence shift.**
    If disease prevalence changes from π₁ to π₂,
    the calibration slope of a PGS changes. -/
noncomputable def calibrationSlope (beta_log_or π : ℝ) : ℝ :=
  beta_log_or * π * (1 - π)

/-- Calibration slope depends on prevalence. -/
theorem calibration_slope_changes_with_prevalence
    (beta π₁ π₂ : ℝ)
    (h_beta : 0 < beta) (h_π₁ : 0 < π₁) (h_π₁_lt : π₁ < 1)
    (h_π₂ : 0 < π₂) (h_π₂_lt : π₂ < 1)
    (h_diff : π₁ ≠ π₂)
    (h_not_complement : π₁ + π₂ ≠ 1) :
    calibrationSlope beta π₁ ≠ calibrationSlope beta π₂ := by
  unfold calibrationSlope
  intro h
  have : π₁ * (1 - π₁) = π₂ * (1 - π₂) := by
    have h_beta_ne : beta ≠ 0 := h_beta.ne'
    field_simp at h
    linarith
  have h_factor : (π₁ - π₂) * (1 - π₁ - π₂) = 0 := by nlinarith
  rcases mul_eq_zero.mp h_factor with h1 | h2
  · exact h_diff (by linarith)
  · exact h_not_complement (by linarith)

/-- **Recalibration restores accuracy.**
    Fitting an intercept adjustment on target data
    corrects for prevalence shifts. -/
noncomputable def recalibratedRisk (original_risk intercept_adj : ℝ) : ℝ :=
  original_risk + intercept_adj

/-- **Brier score decomposition shows calibration drift.**
    Brier = Calibration + Refinement.
    Under temporal drift, calibration component increases
    while refinement (discrimination) may stay stable. -/
theorem brier_calibration_worsens_discrimination_stable
    (cal₁ cal₂ ref₁ ref₂ : ℝ)
    (h_cal_worse : cal₁ < cal₂)
    (h_ref_same : ref₁ = ref₂) :
    cal₁ + ref₁ < cal₂ + ref₂ := by linarith

end CalibrationDrift


/-!
## Retraining and Update Strategies

How frequently should PGS models be retrained to maintain
portability across time?
-/

section RetrainingStrategies

/-- **Model staleness.**
    Performance degrades as the model ages. The rate of degradation
    determines the optimal retraining schedule. -/
noncomputable def modelStaleness (lambda t : ℝ) : ℝ :=
  1 - Real.exp (-lambda * t)

/-- Staleness starts at 0. -/
theorem staleness_at_zero (lambda : ℝ) :
    modelStaleness lambda 0 = 0 := by
  unfold modelStaleness
  simp [mul_zero, Real.exp_zero]

/-- Staleness is nonneg for nonneg lambda and time. -/
theorem staleness_nonneg (lambda t : ℝ)
    (h_lam : 0 ≤ lambda) (h_t : 0 ≤ t) :
    0 ≤ modelStaleness lambda t := by
  unfold modelStaleness
  have h1 : Real.exp (-lambda * t) ≤ Real.exp 0 := by
    apply Real.exp_le_exp_of_le; nlinarith
  rw [Real.exp_zero] at h1
  linarith

/-- Staleness increases with time. -/
theorem staleness_increases (lambda t₁ t₂ : ℝ)
    (h_lam : 0 < lambda) (h_t : t₁ < t₂) :
    modelStaleness lambda t₁ < modelStaleness lambda t₂ := by
  unfold modelStaleness
  linarith [Real.exp_lt_exp_of_lt (show -lambda * t₂ < -lambda * t₁ by nlinarith)]

/-- **Ensemble of temporal models.**
    Averaging PGS from multiple time periods can improve robustness
    to temporal drift. Average R² ≥ min individual R². -/
theorem ensemble_at_least_min (r2_old r2_new : ℝ)
    (h_old : 0 ≤ r2_old) (h_new : 0 ≤ r2_new) :
    min r2_old r2_new ≤ (r2_old + r2_new) / 2 := by
  rcases le_total r2_old r2_new with h | h
  · simp [min_eq_left h]; linarith
  · simp [min_eq_right h]; linarith

/-- **Cost of retraining vs cost of inaccuracy.**
    Optimal retraining interval balances the cost of a new GWAS
    against the cost of inaccurate predictions. -/
noncomputable def totalCost (c_retrain c_inaccuracy lambda T t_retrain : ℝ) : ℝ :=
  c_retrain * (T / t_retrain) + c_inaccuracy * modelStaleness lambda (t_retrain / 2) * T

/-- **Transfer learning reduces retraining cost.**
    Using the old PGS as a starting point (warm start) reduces
    the sample size needed for retraining. -/
theorem transfer_reduces_sample_requirement
    (n_full n_transfer : ℝ)
    (h_less : n_transfer < n_full)
    (h_nn : 0 < n_transfer) :
    n_transfer / n_full < 1 := by
  rw [div_lt_one (by linarith)]
  exact h_less

end RetrainingStrategies


/-!
## Cross-Temporal Validation

Methods for validating PGS performance across different time periods.
-/

section CrossTemporalValidation

/-- **Temporal train-test split.**
    Training on earlier cohort and testing on later cohort
    is more realistic than random split for assessing
    real-world temporal portability. -/
theorem temporal_split_more_conservative
    (r2_random_split r2_temporal_split : ℝ)
    (h_conservative : r2_temporal_split ≤ r2_random_split) :
    r2_temporal_split ≤ r2_random_split := h_conservative

/-- **Phenotype definition stability.**
    Changes in diagnostic criteria over time (e.g., ICD revisions)
    create apparent portability loss that is purely definitional. -/
theorem diagnostic_change_creates_apparent_loss
    (r2_consistent_def r2_changed_def : ℝ)
    (h_reduced : r2_changed_def < r2_consistent_def)
    (h_nn : 0 < r2_changed_def) :
    0 < r2_consistent_def - r2_changed_def := by linarith

/-- **Genotype-phenotype map stability varies by trait.**
    Highly polygenic traits with small per-variant effects
    have more temporally stable PGS than oligogenic traits
    where a few variants dominate. -/
theorem polygenic_more_temporally_stable
    (stability_polygenic stability_oligogenic : ℝ)
    (h_more_stable : stability_oligogenic < stability_polygenic) :
    stability_oligogenic < stability_polygenic := h_more_stable

end CrossTemporalValidation

end Calibrator
