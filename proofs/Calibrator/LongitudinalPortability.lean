import Calibrator.Probability
import Calibrator.PortabilityDrift
import Calibrator.PGSCalibrationTheory
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
noncomputable def longitudinalDriftDecayRate (Ne : ℝ) : ℝ := 1 / (2 * Ne)

/-- Drift decay rate is positive for positive Ne. -/
theorem drift_decay_rate_pos (Ne : ℝ) (h : 0 < Ne) :
    0 < longitudinalDriftDecayRate Ne := by
  unfold longitudinalDriftDecayRate
  positivity

/-- **Larger populations drift slower.**
    If Ne₁ < Ne₂, then λ_drift₁ > λ_drift₂. -/
theorem larger_Ne_slower_drift (Ne₁ Ne₂ : ℝ)
    (h₁ : 0 < Ne₁) (h₂ : 0 < Ne₂) (h_lt : Ne₁ < Ne₂) :
    longitudinalDriftDecayRate Ne₂ < longitudinalDriftDecayRate Ne₁ := by
  unfold longitudinalDriftDecayRate
  have h1' : 0 < 2 * Ne₁ := by positivity
  have h2' : 0 < 2 * Ne₂ := by positivity
  apply (div_lt_div_iff₀ h2' h1').2
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
    effect sizes in another due to changed environments.
    Model: the observed effect β_obs = β_genetic × env_modifier, where
    env_modifier differs between cohorts due to changing environments.
    If env₁ ≠ env₂ and β_genetic ≠ 0, then the observed effects differ. -/
theorem cohort_specific_effects
    (beta_genetic env₁ env₂ : ℝ)
    (h_beta : beta_genetic ≠ 0)
    (h_env_diff : env₁ ≠ env₂) :
    beta_genetic * env₁ ≠ beta_genetic * env₂ := by
  intro h
  exact h_env_diff (mul_left_cancel₀ h_beta h)

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
    trained on younger cohorts.
    Model: R² = V_A / (V_A + V_E), where V_E differs between cohorts.
    Older cohorts had more environmental barriers (V_E_old > V_E_young),
    so R²_old < R²_young. -/
theorem education_cohort_effect
    (V_A V_E_old V_E_young : ℝ)
    (h_VA : 0 < V_A) (h_VE_old : 0 < V_E_old) (h_VE_young : 0 < V_E_young)
    (h_more_barriers : V_E_young < V_E_old) :
    V_A / (V_A + V_E_old) ≠ V_A / (V_A + V_E_young) := by
  intro h
  have h₁ : V_A + V_E_old ≠ 0 := by linarith
  have h₂ : V_A + V_E_young ≠ 0 := by linarith
  rw [div_eq_div_iff h₁ h₂] at h
  nlinarith [mul_comm V_A V_E_old, mul_comm V_A V_E_young]

/-- **Survivorship bias in older cohorts.**
    PGS for mortality-related traits in older cohorts are biased
    by survivorship: only survivors are observed, creating
    selection bias.
    Model: observed effect = true effect × attenuation, where
    attenuation = (1 - selection_intensity) and 0 < selection_intensity < 1.
    Therefore |β_observed| < |β_true|. -/
theorem survivorship_bias_attenuates_pgs
    (beta_true attenuation : ℝ)
    (h_beta : beta_true ≠ 0)
    (h_att_pos : 0 < attenuation) (h_att_lt : attenuation < 1) :
    |beta_true * attenuation| < |beta_true| := by
  rw [abs_mul]
  calc |beta_true| * |attenuation|
      < |beta_true| * 1 := by {
        apply mul_lt_mul_of_pos_left _ (abs_pos.mpr h_beta)
        rwa [abs_of_pos h_att_pos]
      }
    _ = |beta_true| := mul_one _

end CohortEffects


/-!
## Temporal Calibration Drift

PGS calibration (the relationship between predicted and observed
risk) drifts over time as disease incidence changes.
-/

section CalibrationDrift

/-- Exact temporal calibration-in-the-large (CITL) for a cohort with observed
prevalence `π_obs` and mean predicted risk `π_pred`. -/
noncomputable def temporalCalibrationInTheLarge (π_obs π_pred : ℝ) : ℝ :=
  calibrationInTheLarge π_obs π_pred

/-- Exact temporal calibration drift from a prevalence shift with fixed mean
prediction. The temporal CITL shift equals the prevalence shift exactly. -/
theorem temporal_calibration_changes_with_prevalence
    (π₁ π₂ mean_pred : ℝ) :
    temporalCalibrationInTheLarge π₂ mean_pred -
      temporalCalibrationInTheLarge π₁ mean_pred = π₂ - π₁ := by
  simpa [temporalCalibrationInTheLarge] using
    prevalence_shift_changes_calibration mean_pred π₁ π₂

/-- If the source cohort is CITL-calibrated, any temporal prevalence shift
produces a nonzero temporal CITL in the target cohort. -/
theorem temporal_calibration_drift_nonzero_of_prevalence_shift
    (π₁ π₂ mean_pred : ℝ)
    (h_src_cal : temporalCalibrationInTheLarge π₁ mean_pred = 0)
    (h_shift : π₁ ≠ π₂) :
    temporalCalibrationInTheLarge π₂ mean_pred ≠ 0 := by
  have h_delta :
      temporalCalibrationInTheLarge π₂ mean_pred -
        temporalCalibrationInTheLarge π₁ mean_pred = π₂ - π₁ :=
    temporal_calibration_changes_with_prevalence π₁ π₂ mean_pred
  intro hzero
  rw [hzero, h_src_cal] at h_delta
  exact h_shift (by linarith)

/-- **Recalibration restores accuracy.**
    Fitting an intercept adjustment on target data
    corrects for prevalence shifts. -/
noncomputable def recalibratedRisk (original_risk intercept_adj : ℝ) : ℝ :=
  original_risk + intercept_adj

/-- Exact temporal Brier risk under a calibrated Bernoulli model with
prevalence `π` and explained-risk fraction `r2`. -/
noncomputable def temporalExactBrierRisk (π r2 : ℝ) : ℝ :=
  exactCalibratedBrierRiskFromR2 π r2

/-- With discrimination held fixed, temporal prevalence changes that increase
the Bernoulli variance factor strictly worsen exact Brier risk. -/
theorem brier_calibration_worsens_discrimination_stable
    (π₁ π₂ r2 : ℝ)
    (h_r2 : r2 < 1)
    (h_prev : π₁ * (1 - π₁) < π₂ * (1 - π₂)) :
    temporalExactBrierRisk π₁ r2 < temporalExactBrierRisk π₂ r2 := by
  unfold temporalExactBrierRisk exactCalibratedBrierRiskFromR2
  have h_factor : 0 < 1 - r2 := by linarith
  nlinarith

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
    real-world temporal portability.
    Model: R²_random = R²_true, but R²_temporal = R²_true × decay(Δt)
    where decay(Δt) = exp(-λ × Δt) ≤ 1. So R²_temporal ≤ R²_random. -/
theorem temporal_split_more_conservative
    (r2_true lambda delta_t : ℝ)
    (h_r2 : 0 ≤ r2_true) (h_lam : 0 ≤ lambda) (h_dt : 0 ≤ delta_t) :
    r2_true * Real.exp (-lambda * delta_t) ≤ r2_true := by
  have h_exp_le : Real.exp (-lambda * delta_t) ≤ 1 := by
    calc
      Real.exp (-lambda * delta_t) ≤ Real.exp 0 := by
        apply Real.exp_le_exp.mpr
        nlinarith
      _ = 1 := by simp
  calc r2_true * Real.exp (-lambda * delta_t)
      ≤ r2_true * 1 := mul_le_mul_of_nonneg_left h_exp_le h_r2
    _ = r2_true := mul_one _

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
    where a few variants dominate.
    Model: stability = 1 - max_variant_contribution, where
    max_variant_contribution = max(β²_i) / Σ β²_i.
    Polygenic traits have many small effects → smaller max contribution.
    Oligogenic traits have few large effects → larger max contribution. -/
theorem polygenic_more_temporally_stable
    (max_contrib_poly max_contrib_oligo : ℝ)
    (h_poly_small : 0 ≤ max_contrib_poly) (h_poly_le : max_contrib_poly ≤ 1)
    (h_oligo_small : 0 ≤ max_contrib_oligo) (h_oligo_le : max_contrib_oligo ≤ 1)
    (h_poly_more_even : max_contrib_poly < max_contrib_oligo) :
    1 - max_contrib_oligo < 1 - max_contrib_poly := by linarith

end CrossTemporalValidation

end Calibrator
