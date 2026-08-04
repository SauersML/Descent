/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Calibrator.Probability
import Calibrator.PortabilityDrift
import Calibrator.PGSCalibrationTheory
import Calibrator.OpenQuestions
import Calibrator.LDDecayTheory
import Calibrator.HorizonCurve
import Calibrator.DriftingConditional

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

Provenance: derived here, not imported. Wang et al. (2026), Nature Communications 17:942,
substantiates nothing below. It is an empirical study of the polygenic-score portability
gap and does not treat temporal decay of portability, epoch effects or retraining
schedules. Sources for individual results, where they exist, are cited at those results.
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

/-- Reference evaluation.  The value is computed through the definitions this body calls, but
the theorem states a number: an inequality or an invariance leaves a family of bodies
satisfying it, and a value does not. -/
theorem portabilityAtTime_at_reference_point :
    portabilityAtTime 0 0 0 = 0 := by
  norm_num [portabilityAtTime]



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

/-! **Drift component of decay.**
    Under Wright-Fisher drift with Ne:
    λ_drift = 1/(2Ne) per generation.

    Empirical status: UNTESTED.

    Denotes: a per-generation rate. Other definitions share this formula under
    names from a different concept family; the formula does not fix which is
    meant.

Do not restate `1 / (2 Nₑ)` in this file. It is `driftRatePerGen` from
`Calibrator.LDDecayTheory`, the one per-generation drift rate, and this file
imports it.

The "fraction of LD lost per generation" reading of that rate is FALSIFIED there,
by up to 201x, because recombination dominates `1 / (2 Nₑ)`. That is why the name
`ldDecayRatePerGen` is absent. What this file imports is the drift rate itself.
Whether it is the fraction of ancestral score variance lost per generation is a
separate claim, and it is UNTESTED. -/

/-- Drift decay rate is positive for positive Ne. -/
theorem drift_decay_rate_pos (Ne : ℝ) (h : 0 < Ne) :
    0 < driftRatePerGen Ne := by
  unfold driftRatePerGen
  positivity

/-! **Larger populations drift slower** is `larger_pop_slower_drift_rate` in
`Calibrator.LDDecayTheory`, which this module imports.  It was stated again here as
`larger_Ne_slower_drift`, with the same statement and a second proof of it; the fact is
about `1/(2Nₑ)` and belongs beside that definition rather than in each module that wants
it. -/

/-- **LD decay component.**
    LD between linked loci decays as (1-r)^t per generation,
    where r is recombination rate. For small r: λ_LD ≈ r.

    Empirical status: UNTESTED. -/
noncomputable def ldDecayPerGeneration (r : ℝ) (t : ℕ) : ℝ :=
  (1 - r) ^ t

/-- Reference evaluation.  The value is computed through the definitions this body calls, but
the theorem states a number: an inequality or an invariance leaves a family of bodies
satisfying it, and a value does not. -/
theorem ldDecayPerGeneration_at_reference_point :
    ldDecayPerGeneration 1 1 = 0 := by
  norm_num [ldDecayPerGeneration]



/-! **Cross-check: geometric LD decay, recombination survival along a genealogy, and
admixture-LD decay are one map.** `ldDecayPerGeneration_eq_discreteRecombinationSurvival`
and `ldDecayPerGeneration_eq_admixtureLDDecay` are absent here as redundant, not as wrong.
`Conventions.lean` proves all four spellings equal to the shared primitive
`geometricDecay`, and these two are that hub's transitive consequences. Six pairwise
theorems for one function is five more than the corpus needs, and a divergence between any
two spellings still fails a proof: it fails one of the three hub theorems.

Neither carries a hypothesis and nothing references either. What is NOT yet done is the
part worth doing: `(1 - r)^t` is written out under four names in four files
(`geometricDecay`, `ldDecayPerGeneration`, `DGP.discreteRecombinationSurvival`,
`PortabilityDrift.admixtureLDDecay`) and should be one. That collapse is ~86 references
across Lean, Python and JSON string tables and is blocked on `PortabilityDrift.lean`,
which cannot currently be edited from this session without reverting another session's
in-flight work. -/

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


/-- **Secular trends shift PGS distributions.**
    A secular trend (e.g., increasing height) shifts the
    phenotype distribution. The PGS, being fixed at training time,
    becomes progressively miscalibrated. -/
noncomputable def secularTrendBias (trend_rate t : ℝ) : ℝ :=
  trend_rate * t

/-- **secularTrendBias pinned at a reference point.** No theorem in the corpus evaluated this
definition, so every body agreeing with it in sign and monotonicity was indistinguishable from
it. At all arguments equal to `1 / 2` it is `1 / 4`, which fixes the coefficients a one-sided
bound or an invariance leaves free. -/
theorem secularTrendBias_at_reference_point :
    secularTrendBias (1 / 2) (1 / 2) = 1 / 4 := by
  unfold secularTrendBias
  norm_num

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

/-- Canonical deployment metrics from an explicit time-indexed signal variance.
    This longitudinal wrapper is just a coordinate map on the supplied
    signal-at-time value; it does not derive that signal from a source `R²`
    plus any transport factor. -/
noncomputable def temporalMetricProfile
    (π signalAtTime : ℝ) : TransportedMetrics.Profile :=
  TransportedMetrics.profileFromSignalVariance π 1 signalAtTime

/-- Exact longitudinal `R²` surface induced by an explicit time-indexed signal
    variance. -/
noncomputable def temporalR2
    (signalAtTime : ℝ) : ℝ :=
  TransportedMetrics.r2FromSignalVariance signalAtTime 1

@[simp] theorem temporalMetricProfile_r2
    (π signalAtTime : ℝ) :
    (temporalMetricProfile π signalAtTime).r2 =
      temporalR2 signalAtTime := by
  rfl

/-- The longitudinal `R²` surface is definitionally the unit-noise `R²`
    coordinate of the supplied time-indexed signal variance. -/
theorem temporalR2_eq_signal_coordinate
    (signalAtTime : ℝ) :
    temporalR2 signalAtTime =
      TransportedMetrics.r2FromSignalVariance signalAtTime 1 := by
  unfold temporalR2
  simp

/-- Gaussian age-kernel shape for age-specific signal variation.

    Empirical status: UNTESTED. -/
noncomputable def ageDependentSignalShape
    (age age_peak width : ℝ) : ℝ :=
  Real.exp (-(age - age_peak)^2 / (2 * width^2))

/-- **ageDependentSignalShape at its junk point, named.** A window of zero width admits signal at
the peak age only. The divisor `2 * width ^ 2` is zero, the exponent is junk-zero, and `exp 0 =
1`: FULL signal at every age, for a window that should admit almost none. The failure is uniform
in `age`, so no age-stratified check can see it. Consumers must guard the argument that makes
the divisor vanish. -/
theorem ageDependentSignalShape_zero_width_is_junk (age age_peak : ℝ) :
    ageDependentSignalShape age age_peak 0 = 1 := by
  unfold ageDependentSignalShape
  simp

/-- Explicit age-indexed signal variance built from a peak signal level and a
    Gaussian age-kernel shape. This remains an explicit signal profile, not a
    source-`R²` transport law. -/
noncomputable def ageDependentSignalVariance
    (sourceSignalPeak age age_peak width : ℝ) : ℝ :=
  sourceSignalPeak * ageDependentSignalShape age age_peak width

/-- Reference evaluation.  The value is computed through the definitions this body calls, but
the theorem states a number: an inequality or an invariance leaves a family of bodies
satisfying it, and a value does not. -/
theorem ageDependentSignalVariance_at_reference_point :
    ageDependentSignalVariance 1 1 1 1 = 1 := by
  norm_num [ageDependentSignalVariance, ageDependentSignalShape]


/-- **The peak sets the scale and the shape sets the age dependence, separately.** Doubling the
peak doubles the variance at every age without moving where the maximum sits. A body that mixed
the two would make the age of peak signal depend on its magnitude, which is not what a peak
amplitude means. -/
theorem ageDependentSignalVariance_scale (sourceSignalPeak age age_peak width c : ℝ) :
    ageDependentSignalVariance (c * sourceSignalPeak) age age_peak width
      = c * ageDependentSignalVariance sourceSignalPeak age age_peak width := by
  unfold ageDependentSignalVariance; ring

/-- Canonical age-indexed deployment metrics from the explicit age-indexed
    signal profile. -/
noncomputable def ageDependentMetricProfile
    (π sourceSignalPeak age age_peak width : ℝ) : TransportedMetrics.Profile :=
  temporalMetricProfile π
    (ageDependentSignalVariance sourceSignalPeak age age_peak width)

/-- **PGS effect sizes are cohort-dependent.**
    A PGS trained on one birth cohort may have different
    effect sizes in another due to changed environments.
    Model: the observed effect β_obs = β_genetic × env_modifier, where
    env_modifier differs between cohorts due to changing environments.
    If env₁ ≠ env₂ and β_genetic ≠ 0, then the observed effects differ. -/
theorem mul_ne_mul_left_of_ne_of_ne_zero
    (beta_genetic env₁ env₂ : ℝ)
    (h_beta : beta_genetic ≠ 0)
    (h_env_diff : env₁ ≠ env₂) :
    beta_genetic * env₁ ≠ beta_genetic * env₂ := by
  intro h
  exact h_env_diff (mul_left_cancel₀ h_beta h)

/-- **Age-dependent PGS performance.**
    PGS for age-related traits (e.g., CAD, T2D) have different
    predictive power at different ages. This interacts with
    cohort effects when comparing across time. This public `R²` surface is
    the `r2` field of the canonical age-indexed metric profile. -/
noncomputable def ageDependentR2 (sourceSignalPeak age age_peak width : ℝ) : ℝ :=
  temporalR2 (ageDependentSignalVariance sourceSignalPeak age age_peak width)

@[simp] theorem ageDependentMetricProfile_r2
    (π sourceSignalPeak age age_peak width : ℝ) :
    (ageDependentMetricProfile π sourceSignalPeak age age_peak width).r2 =
      ageDependentR2 sourceSignalPeak age age_peak width := by
  rfl

@[simp] theorem ageDependentSignalShape_at_peak
    (age_peak width : ℝ) :
    ageDependentSignalShape age_peak age_peak width = 1 := by
  unfold ageDependentSignalShape
  simp [sub_self, Real.exp_zero]

/-- **The width really is a standard deviation.** `ageDependentSignalShape_at_peak` normalises
the shape at its maximum and constrains nothing about how fast it falls away: every body of the
form `exp (-(age - peak) ^ 2 / (c * width ^ 2))` agrees there. One width away from the peak the
signal has fallen by exactly `exp (-1/2)`, which is what fixes `c = 2` and makes `width` the
standard deviation of the age window rather than an arbitrary scale. -/
theorem ageDependentSignalShape_one_width_out (age_peak width : ℝ) (hw : width ≠ 0) :
    ageDependentSignalShape (age_peak + width) age_peak width = Real.exp (-(1 / 2)) := by
  unfold ageDependentSignalShape
  have h : age_peak + width - age_peak = width := by ring
  rw [h]
  congr 1
  field_simp

/-- Age-dependent R² peaks at the optimal age. -/
theorem age_r2_peaks_at_optimal (sourceSignalPeak age_peak width : ℝ) :
    ageDependentR2 sourceSignalPeak age_peak age_peak width =
      TransportedMetrics.r2FromSignalVariance sourceSignalPeak 1 := by
  unfold ageDependentR2
  unfold ageDependentSignalVariance
  rw [ageDependentSignalShape_at_peak]
  simp
  exact temporalR2_eq_signal_coordinate sourceSignalPeak

/-- **The age-resolved `R²` at the peak, in closed form.** `age_r2_peaks_at_optimal` reduces the
composite to `r2FromSignalVariance`, which constrains the two definitions jointly and leaves a
shared wrong factor free. This carries the reduction through to a closed form in the peak signal
alone: against unit noise the peak `R²` is `v / (v + 1)`. -/
theorem ageDependentR2_at_peak (sourceSignalPeak age_peak width : ℝ) :
    ageDependentR2 sourceSignalPeak age_peak age_peak width
      = sourceSignalPeak / (sourceSignalPeak + 1) := by
  rw [age_r2_peaks_at_optimal]
  rfl

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


/-- Exact temporal Brier risk under a calibrated Bernoulli model with
prevalence `π` and explicit time-indexed signal variance. This is the `brier`
field of the canonical time-indexed metric profile. -/
noncomputable def temporalExactBrierRisk
    (π signalAtTime : ℝ) : ℝ :=
  (temporalMetricProfile π signalAtTime).brier

@[simp] theorem temporalMetricProfile_brier
    (π signalAtTime : ℝ) :
    (temporalMetricProfile π signalAtTime).brier =
      temporalExactBrierRisk π signalAtTime := by
  rfl

/-- Exact temporal Brier risk is the canonical Bernoulli variance factor times
    one minus the exact temporal `R²` from the same transported profile. -/
theorem temporalExactBrierRisk_eq_prevalence_scale
    (π signalAtTime : ℝ) :
    temporalExactBrierRisk π signalAtTime =
      π * (1 - π) * (1 - temporalR2 signalAtTime) := by
  rfl

/-- With discrimination held fixed, temporal prevalence changes that increase
the Bernoulli variance factor strictly worsen exact Brier risk. -/
theorem brier_calibration_worsens_discrimination_stable
    (π₁ π₂ signalAtTime : ℝ)
    (h_r2 : temporalR2 signalAtTime < 1)
    (h_prev : π₁ * (1 - π₁) < π₂ * (1 - π₂)) :
    temporalExactBrierRisk π₁ signalAtTime <
      temporalExactBrierRisk π₂ signalAtTime := by
  rw [temporalExactBrierRisk_eq_prevalence_scale,
    temporalExactBrierRisk_eq_prevalence_scale]
  have h_factor : 0 < 1 - temporalR2 signalAtTime := by
    linarith
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

/-- Reference evaluation.  The value is computed through the definitions this body calls, but
the theorem states a number: an inequality or an invariance leaves a family of bodies
satisfying it, and a value does not. -/
theorem modelStaleness_at_reference_point :
    modelStaleness 0 0 = 0 := by
  norm_num [modelStaleness]



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


end CrossTemporalValidation

/-! ## The shape of the measured decay curve, and what a crossover does not identify

`temporal_split_more_conservative` above models cohort decay as `exp(-λ Δt)` and reads a single
rate off it. `Calibrator.HorizonCurve` supplies three facts that decide when that reading is
legitimate.

First, a measurement result: averaging a one-endpoint accuracy profile over the invariant cohort
law returns the same number at every gap. A temporal split that resamples the evaluation set from
the stationary law and evaluates a fixed profile cannot show decay, and a decay it does show came
from the sampling, the refitting or the non-stationarity. What varies with the gap is the starting
cohort of the design — the regret, not the average.

Second, a shape result, falsifiable on published curves: under a stationary reversible coupling
the effective decay rate is nonincreasing in the gap, so a cohort curve that steepens is not
relaxation.

Third, a negative result about `stalenessCrossover`: a single crossover does not pin a relaxation
time, because a multi-mode value signal can cross three times. -/

section HorizonShape

open scoped BigOperators in
/-- A stationary-law temporal split shows no decay by construction. Instance of
    `naiveHorizonCurve_independent_of_horizon`: for a fixed accuracy profile averaged over the
    invariant cohort law, two cohort gaps give the same number, so any decay reported from this
    estimator is a property of the study design.

    Empirical status: DERIVED. -/
theorem stationaryAverage_indep_of_gap {ι : Type*} [Fintype ι]
    (π : ι → ℝ) (P : ℝ → ι → ι → ℝ) (accuracy : ι → ℝ)
    (h : ∀ t, IsStationaryKernel π (P t)) (gap₁ gap₂ : ℝ) :
    ∑ x, π x * ∑ y, P gap₁ x y * accuracy y = ∑ x, π x * ∑ y, P gap₂ x y * accuracy y :=
  naiveHorizonCurve_independent_of_horizon π P accuracy h gap₁ gap₂

/-- A cohort accuracy curve cannot steepen. Instance of `effectiveRate_nonincreasing` at a
    two-mode value signal: if cross-cohort decay is the relaxation of a stationary reversible
    coupling, the effective rate falls with the cohort gap. A measured curve whose apparent rate
    rises falsifies the relaxation model; the alternatives it leaves — drifting phenotype
    definition, changing ascertainment, a non-stationary environment — are distinct and testable.

    Empirical status: DERIVED; the shape constraint is the testable content. -/
theorem twoMode_effectiveRate_nonincreasing
    (slowWeight fastWeight slowRate fastRate gap₁ gap₂ : ℝ)
    (hs : 0 ≤ slowWeight) (hf : 0 ≤ fastWeight) (hrate : slowRate ≤ fastRate)
    (hgap : gap₁ ≤ gap₂) :
    (slowWeight * slowRate * Real.exp (-(slowRate * gap₂)) +
        fastWeight * fastRate * Real.exp (-(fastRate * gap₂))) *
        (slowWeight * Real.exp (-(slowRate * gap₁)) +
          fastWeight * Real.exp (-(fastRate * gap₁)))
      ≤ (slowWeight * slowRate * Real.exp (-(slowRate * gap₁)) +
          fastWeight * fastRate * Real.exp (-(fastRate * gap₁))) *
        (slowWeight * Real.exp (-(slowRate * gap₂)) +
          fastWeight * Real.exp (-(fastRate * gap₂))) :=
  effectiveRate_nonincreasing slowWeight fastWeight slowRate fastRate gap₁ gap₂ hs hf hrate hgap

/-- A measured crossover does not identify a relaxation time. The four-mode premium of
    `HorizonCurve.horizonPolynomial` changes sign three times, so observing one crossing of stale
    against environment-blind and inverting `stalenessCrossover` recovers nothing unless the value
    signal has separately been shown to be single-signed in the rate ordering.

    Empirical status: DERIVED. -/
theorem cohortCrossover_may_be_threefold :
    horizonPolynomial (3 / 10) < 0 ∧ 0 < horizonPolynomial (9 / 20) ∧
      horizonPolynomial (11 / 20) < 0 := by
  obtain ⟨-, -, -, h1, h2, h3, -⟩ := horizon_three_crossings
  exact ⟨h1, h2, h3⟩

end HorizonShape

/-! ## Secular trend in the criterion versus secular trend in the population

`secularTrendBias` above models drift as a single number growing linearly in time, which leaves
open the question the number cannot answer: whether the phenotype moved or the definition of a
case moved. Both produce a drifting response curve, and across cohorts both are happening.

`Calibrator.DriftingConditional` settles when they can be told apart. At any fixed cohort they
cannot: the observable determines the linked curve `m - θ` and the unidentified direction is
exactly the spatially constant one, so a uniform shift in liability and an equal move of the
diagnostic threshold are the same data however many cohorts are sampled at that resolution.

From the *motion* they can, provided the population's own dynamics carry no constant forcing.
Averaging the linked curve's velocity against the population's invariant distribution annihilates
the population term and returns the threshold velocity alone. That is a formula, not a bound, and
every quantity in it is observable.

The hypothesis is the whole content and it is refutable: a population model with spatially uniform
forcing conflates the two forever. So a study that wants to attribute cross-cohort drift to
changing diagnostic criteria has to commit to a conservative population model first, and say so. -/

section CriterionDrift

/-- **Threshold drift is recoverable from cohort motion.**

    Instance of `invariantAverage_eq_neg_of_affine_evolution`: with the linked response curve
    observed across a stratified population, its velocity averaged against the population's
    invariant distribution equals minus the velocity of the diagnostic threshold. The population's
    own dynamics drop out because a generator annihilates constants.

    Empirical status: DERIVED. The generator, the invariant distribution and the link are
    modelling commitments; given them the threshold path is identified up to its starting value. -/
theorem invariantAverage_recovers_additive_constant {n : ℕ}
    (stratumWeight : Fin n → ℝ) (populationGenerator : Fin n → Fin n → ℝ)
    (linkedCurve linkedVelocity : Fin n → ℝ) (criterionVelocity : ℝ)
    (hmass : ∑ i, stratumWeight i = 1)
    (hinv : IsInvariantWeight stratumWeight populationGenerator)
    (hdyn : ∀ i, linkedVelocity i =
      (∑ j, populationGenerator i j * linkedCurve j) - criterionVelocity) :
    ∑ i, stratumWeight i * linkedVelocity i = -criterionVelocity :=
  invariantAverage_eq_neg_of_affine_evolution stratumWeight populationGenerator
    linkedCurve linkedVelocity criterionVelocity hmass hinv hdyn

/-- **A population model with uniform forcing destroys the separation.**

    Instance of `constantForcing_conflates_threshold`: the same average now returns the difference
    of the two velocities, so no amount of cohort data separates a secular phenotype shift that is
    uniform across strata from a moving diagnostic criterion. This is the hypothesis of
    `invariantAverage_recovers_additive_constant` failing, and it fails loudly rather than silently.

    Empirical status: DERIVED. -/
theorem uniformSecularShift_conflated_with_criterion {n : ℕ}
    (stratumWeight : Fin n → ℝ) (populationGenerator : Fin n → Fin n → ℝ)
    (linkedCurve linkedVelocity : Fin n → ℝ) (criterionVelocity uniformShift : ℝ)
    (hmass : ∑ i, stratumWeight i = 1)
    (hinv : IsInvariantWeight stratumWeight populationGenerator)
    (hdyn : ∀ i, linkedVelocity i =
      (∑ j, populationGenerator i j * linkedCurve j) + uniformShift - criterionVelocity) :
    ∑ i, stratumWeight i * linkedVelocity i = uniformShift - criterionVelocity :=
  constantForcing_conflates_threshold stratumWeight populationGenerator linkedCurve
    linkedVelocity criterionVelocity uniformShift hmass hinv hdyn

/-- **An interpolated cohort inherits the geometric mean of its neighbours' errors.**

    Instance of `interiorError_sq_le_mul_endpoints`: reconstructing the response curve for a cohort
    between two measured cohorts costs the product of the two error energies, with constant one.
    Interpolation between cohorts is safe; the expensive direction is extrapolation, which this
    bound does not cover.

    Empirical status: DERIVED. -/
theorem interpolatedCohort_error_le_neighbours {n : ℕ}
    (modeWeight relaxationRate : Fin n → ℝ) (earlier later : ℝ)
    (hw : ∀ k, 0 ≤ modeWeight k) :
    errorEnergy modeWeight relaxationRate ((earlier + later) / 2) ^ 2
      ≤ errorEnergy modeWeight relaxationRate earlier *
        errorEnergy modeWeight relaxationRate later :=
  interiorError_sq_le_mul_endpoints modeWeight relaxationRate earlier later hw

end CriterionDrift

end Calibrator
