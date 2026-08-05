/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.PGSCalibrationTheory.CalibrationVsDiscrimination

namespace Descent.Portability

open MeasureTheory
open PopGen.TransportedMetrics (equalVarianceGaussianAUCFromSignalVariance)

/-!
# `PGSCalibrationTheory.PopulationCalibrationDrift`

Part of the split of `Descent/Portability/PGSCalibrationTheory.lean`, which was 3,689 lines.

The parts are a CHAIN: each imports the one before, in the order the original was written.
That is the conservative choice, deliberately. A monolith's declarations depend on each
other in whatever order they happen to appear, and cutting it into modules that import only
what they use means discovering that order first -- worth doing, and not what this does.
The chain preserves every resolution the single file had, so the split cannot change what
any proof sees.

Where a cut falls inside a section, the section is reopened and reclosed by name. A section
scopes `variable`s and this file declares none at that level, so the reopening is exact.
-/



/-!
## Population-Specific Calibration Drift

When a PGS trained in one population is applied to another,
calibration drifts systematically.
-/

section PopulationCalibrationDrift

/-- Shared logistic-scale calibration profile induced by a prevalence shift.

    **This profile's `citl` is a difference of MARGINAL prevalence logits, and
    that is not the intercept correction a deployment needs.** The two coincide
    only when the score is constant, because `logit E[p]` is not `E[logit p]`.

    Empirical status: **FALSIFIED** as the deployment
    calibration-in-the-large, and exact for a constant predictor
    (`validation/empirical/simcov/battery_pgscal01.py`). Two million
    individuals per arm, a logistic risk model, and a target differing from the
    source by a baseline-risk (intercept) shift and nothing else — the one
    regime the phrase "induced by a prevalence shift" names. The oracle is the
    intercept correction the target actually needs: the `a` solving
    `Σᵢ (yᵢ - expit(ηᵢ + a)) = 0` with the source linear predictor held as an
    offset. Both prevalences are fed at their realised cohort values.

      score sd   true intercept shift   this citl   fitted correction   sems
      1.2              0.80              0.66237    0.79967±0.00204     67.2
      1.5              0.60              0.42940    0.60007±0.00181     94.4
      2.0              1.50              0.94064    1.49676±0.00149    374.0
      1.0             -0.90             -0.75407   -0.89961±0.00190     76.4

    The failure is one-directional: `|citl|` is 17% to 37% SMALLER than the
    correction required, so a deployment sized from this number under-corrects.
    The gap grows with the spread of the score and vanishes with it — the
    positive control is a zero-variance score, where the fitted correction
    returns the 0.7 intercept shift it was given at 0.26 sems and this body
    returns 0.7 as well. The identity-scale reading `π_target - π_source` is
    rejected on the same cells at up to 878 sems, so the failure is not an
    artefact of comparing across links.

    Consumers that read this `citl` as the recalibration a target population
    needs — rather than as the shift in marginal log-odds, which is what it is —
    are reading an attenuated number. -/
noncomputable def prevalenceLogisticCalibrationProfile
    (pi_source pi_target slope : ℝ) : CalibrationProfile :=
  logisticCalibrationProfile (prevalenceLogit pi_target) (prevalenceLogit pi_source) slope

@[simp] theorem prevalenceLogisticCalibrationProfile_citl
    (pi_source pi_target slope : ℝ) :
    (prevalenceLogisticCalibrationProfile pi_source pi_target slope).citl =
      prevalenceCITLShift pi_source pi_target := by
  unfold prevalenceLogisticCalibrationProfile prevalenceCITLShift
    logisticCalibrationProfile calibrationProfile prevalenceLogit
    calibrationInTheLarge Descent.Core.difference
  ring

@[simp] theorem prevalenceLogisticCalibrationProfile_slope
    (pi_source pi_target slope : ℝ) :
    (prevalenceLogisticCalibrationProfile pi_source pi_target slope).slope = slope := by
  rfl

/-- CITL shift is zero when prevalences match. -/
theorem no_citl_shift_same_prevalence (pi : ℝ) :
    prevalenceCITLShift pi pi = 0 := by
  rw [← prevalenceLogisticCalibrationProfile_citl pi pi (1 : ℝ)]
  simp [prevalenceLogisticCalibrationProfile, logisticCalibrationProfile,
    calibrationProfile, calibrationInTheLarge,
      Descent.Core.difference]

/-- CITL shift is positive when target has higher prevalence. -/
theorem citl_shift_positive_higher_prevalence
    (pi_s pi_t : ℝ) (h_s : 0 < pi_s)
    (h_higher : pi_s < pi_t)
    (h_t : pi_t < 1) :
    0 < prevalenceCITLShift pi_s pi_t := by
  have h_t_pos : 0 < pi_t := lt_trans h_s h_higher
  have h_den_s : 0 < 1 - pi_s := by linarith
  have h_den_t : 0 < 1 - pi_t := by linarith
  have h_odds_pos_s : 0 < pi_s / (1 - pi_s) :=
    div_pos h_s h_den_s
  have h_odds_lt : pi_s / (1 - pi_s) < pi_t / (1 - pi_t) := by
    rw [div_lt_div_iff₀ h_den_s h_den_t]
    nlinarith
  unfold prevalenceCITLShift prevalenceLogit
  apply sub_pos.mpr
  exact Real.log_lt_log h_odds_pos_s h_odds_lt

/-- **Environmental confounding shifts calibration.**
    If environmental risk factors change the population mean outcome by
    `env_effect` while the model's mean prediction is unchanged, then
    calibration-in-the-large shifts by exactly `env_effect`. -/
theorem env_differences_shift_calibration
    (mean_obs mean_pred env_effect : ℝ) :
    calibrationInTheLarge (mean_obs + env_effect) mean_pred =
      calibrationInTheLarge mean_obs mean_pred + env_effect := by
  unfold calibrationInTheLarge Descent.Core.difference
  ring

/-- Under a source model calibrated in the large, any nonzero environmental
    shift induces nonzero target CITL. -/
theorem env_differences_shift_calibration_nonzero_of_calibrated_source
    (mean_obs mean_pred env_effect : ℝ)
    (h_src_cal : calibrationInTheLarge mean_obs mean_pred = 0)
    (h_effect : env_effect ≠ 0) :
    calibrationInTheLarge (mean_obs + env_effect) mean_pred ≠ 0 := by
  rw [env_differences_shift_calibration]
  rw [h_src_cal]
  simpa using h_effect

/-- **Genetic risk distribution shift.**
    If the PGS mean shifts by Δμ in the target population, the CITL
    shifts correspondingly. Using calibrationInTheLarge:
    CITL_target = (mean_obs_target) - (mean_pred), where mean_pred
    was calibrated to source. The shift in mean PGS creates a CITL
    equal to the mean difference when the model was calibrated (CITL=0) in source.
    CITL_target = mean_obs_target - mean_obs_source + (mean_pgs_source - mean_pgs_target). -/
theorem genetic_distribution_shift
    (mean_obs_s mean_obs_t mean_pgs_s mean_pgs_t : ℝ) :
    calibrationInTheLarge mean_obs_t mean_pgs_t =
      calibrationInTheLarge mean_obs_s mean_pgs_s +
        (mean_obs_t - mean_obs_s) + (mean_pgs_s - mean_pgs_t) := by
  unfold calibrationInTheLarge Descent.Core.difference
  ring

/-- If the source model is calibrated in the large, the target CITL equals the
    observed-mean shift plus the PGS-mean shift exactly. -/
theorem genetic_distribution_shift_of_calibrated_source
    (mean_obs_s mean_obs_t mean_pgs_s mean_pgs_t : ℝ)
    (h_calibrated_source : calibrationInTheLarge mean_obs_s mean_pgs_s = 0) :
    calibrationInTheLarge mean_obs_t mean_pgs_t =
      mean_obs_t - mean_obs_s + (mean_pgs_s - mean_pgs_t) := by
  rw [genetic_distribution_shift]
  rw [h_calibrated_source]
  ring

/-- Under a calibrated source model, any nonzero net mean shift induces
    nonzero target CITL. -/
theorem genetic_distribution_shift_nonzero_of_calibrated_source
    (mean_obs_s mean_obs_t mean_pgs_s mean_pgs_t : ℝ)
    (h_calibrated_source : calibrationInTheLarge mean_obs_s mean_pgs_s = 0)
    (h_net_shift : mean_obs_t - mean_obs_s + (mean_pgs_s - mean_pgs_t) ≠ 0) :
    calibrationInTheLarge mean_obs_t mean_pgs_t ≠ 0 := by
  rw [genetic_distribution_shift_of_calibrated_source
    mean_obs_s mean_obs_t mean_pgs_s mean_pgs_t h_calibrated_source]
  exact h_net_shift

end PopulationCalibrationDrift

end Descent.Portability
