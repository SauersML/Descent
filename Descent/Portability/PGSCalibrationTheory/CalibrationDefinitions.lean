/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.PopGen.DGP

assert_below Descent.Decision Descent.Program

namespace Descent.Portability

open MeasureTheory
open PopGen.TransportedMetrics (equalVarianceGaussianAUCFromSignalVariance)

/-!
# `PGSCalibrationTheory.CalibrationDefinitions`

Part of the split of `Descent/Portability/PGSCalibrationTheory.lean`, which was 3,689 lines.

This part is the HEAD of the fan. The split first made the parts a CHAIN -- each importing
the one before, in the order the original text ran -- which preserved every resolution the
single file had and charged every part a dependency on everything written above it, used or
not. This part is what the others were resolved against: it declares the definitions they
name and carries the imports they share, and it names no sibling itself.

Where a cut falls inside a section, the section is reopened and reclosed by name. A section
scopes `variable`s and this file declares none at that level, so the reopening is exact.
-/

section CalibrationDefinitions

/-- Link scale on which calibration is interpreted. -/
inductive CalibrationLink where
  | identity
  | logistic
deriving DecidableEq, Repr

/-- Shared calibration surface used across the codebase. -/
structure CalibrationProfile where
  citl : ℝ
  slope : ℝ
  link : CalibrationLink

/-- Generic calibration moments that determine a profile once a link label is
chosen. This is the common data layer shared by the generic calibration
algebra and the explicit cross-population transport model. -/
structure CalibrationMoments where
  meanObserved : ℝ
  meanPredicted : ℝ
  slope : ℝ

/-- **Calibration-in-the-large (CITL).**
    CITL = mean(observed) - mean(predicted).
    CITL = 0 means the average prediction matches the average outcome. -/
noncomputable def calibrationInTheLarge (mean_observed mean_predicted : ℝ) : ℝ :=
  Descent.Core.difference mean_observed mean_predicted

/-- **Calibration-in-the-large's sign convention, pinned.** This definition carries no result of
its own, and its entire content is which way the subtraction runs. It is negative when the model
predicts a higher mean than is observed, so a negative value reports over-prediction; the
reversed body reports over-prediction as under-prediction. -/
theorem calibrationInTheLarge_negative_when_overpredicting :
    calibrationInTheLarge 1 3 = -2 := by
  unfold calibrationInTheLarge Descent.Core.difference
  norm_num

/-- **An intercept recalibration moves CITL by exactly its own size.**

Shifting the predicted mean by a recalibration intercept takes the calibration-in-the-large
to the `Descent.Core.difference` between the old value and that intercept -- one unit of
intercept for one unit of CITL, with no dependence on the observed mean or on how badly
calibrated the model already was. This is what makes intercept recalibration exact rather
than iterative: the intercept that zeroes CITL is the CITL itself. A body that scaled the
means before subtracting them would move CITL by some other amount and the recalibration
would have to be solved for. -/
theorem calibrationInTheLarge_predicted_shift
    (mean_observed mean_predicted intercept : ℝ) :
    calibrationInTheLarge mean_observed (Descent.Core.sum mean_predicted intercept) =
      Descent.Core.difference
        (calibrationInTheLarge mean_observed mean_predicted) intercept := by
  unfold calibrationInTheLarge Descent.Core.difference Descent.Core.sum
  ring

/-- **Calibration slope.**
    Regress observed on predicted: Y = a + b × predicted.
    b = 1 means well-calibrated spread.
    b < 1 means predictions are too extreme (overfitting).
    b > 1 means predictions are too conservative. -/
noncomputable def calibrationSlopeDeviation (slope : ℝ) : ℝ := |slope - 1|

/-- Shared calibration profile constructor. -/
noncomputable def calibrationProfile
    (link : CalibrationLink) (mean_observed mean_predicted slope : ℝ) :
    CalibrationProfile where
  citl := calibrationInTheLarge mean_observed mean_predicted
  slope := slope
  link := link

/-- Generic profile builder from calibration moments. -/
noncomputable def CalibrationMoments.toProfile
    (mom : CalibrationMoments) (link : CalibrationLink) : CalibrationProfile :=
  calibrationProfile link mom.meanObserved mom.meanPredicted mom.slope

/-- Shift source calibration moments into target calibration moments by adding
explicit observed and predicted mean shifts and replacing the slope with the
target slope. -/
noncomputable def CalibrationMoments.shifted
    (mom : CalibrationMoments) (observedShift predictedShift slope : ℝ) :
    CalibrationMoments where
  meanObserved := mom.meanObserved + observedShift
  meanPredicted := mom.meanPredicted + predictedShift
  slope := slope

/-- Identity-scale calibration profile. -/
noncomputable def identityCalibrationProfile
    (mean_observed mean_predicted slope : ℝ) : CalibrationProfile :=
  calibrationProfile CalibrationLink.identity mean_observed mean_predicted slope

/-- Logistic-scale calibration profile. -/
noncomputable def logisticCalibrationProfile
    (mean_observed mean_predicted slope : ℝ) : CalibrationProfile :=
  calibrationProfile CalibrationLink.logistic mean_observed mean_predicted slope

/-- The simp lemmas immediately below are definitional facts about the shared
calibration-profile container. They do not encode any cross-population
transport model. The biologically meaningful cross-ancestry calibration state
starts later in `CrossPopulationCalibrationShiftModel`. -/

@[simp] theorem calibrationProfile_citl
    (link : CalibrationLink) (mean_observed mean_predicted slope : ℝ) :
    (calibrationProfile link mean_observed mean_predicted slope).citl =
      calibrationInTheLarge mean_observed mean_predicted := by
  rfl

@[simp] theorem calibrationProfile_slope
    (link : CalibrationLink) (mean_observed mean_predicted slope : ℝ) :
    (calibrationProfile link mean_observed mean_predicted slope).slope = slope := by
  rfl

@[simp] theorem calibrationProfile_link
    (link : CalibrationLink) (mean_observed mean_predicted slope : ℝ) :
    (calibrationProfile link mean_observed mean_predicted slope).link = link := by
  rfl

@[simp] theorem identityCalibrationProfile_citl
    (mean_observed mean_predicted slope : ℝ) :
    (identityCalibrationProfile mean_observed mean_predicted slope).citl =
      calibrationInTheLarge mean_observed mean_predicted := by
  rfl

@[simp] theorem identityCalibrationProfile_slope
    (mean_observed mean_predicted slope : ℝ) :
    (identityCalibrationProfile mean_observed mean_predicted slope).slope = slope := by
  rfl

@[simp] theorem identityCalibrationProfile_link
    (mean_observed mean_predicted slope : ℝ) :
    (identityCalibrationProfile mean_observed mean_predicted slope).link =
      CalibrationLink.identity := by
  rfl

@[simp] theorem logisticCalibrationProfile_citl
    (mean_observed mean_predicted slope : ℝ) :
    (logisticCalibrationProfile mean_observed mean_predicted slope).citl =
      calibrationInTheLarge mean_observed mean_predicted := by
  rfl

@[simp] theorem logisticCalibrationProfile_slope
    (mean_observed mean_predicted slope : ℝ) :
    (logisticCalibrationProfile mean_observed mean_predicted slope).slope = slope := by
  rfl

@[simp] theorem logisticCalibrationProfile_link
    (mean_observed mean_predicted slope : ℝ) :
    (logisticCalibrationProfile mean_observed mean_predicted slope).link =
      CalibrationLink.logistic := by
  rfl

@[simp] theorem calibrationProfile_slopeDeviation
    (link : CalibrationLink) (mean_observed mean_predicted slope : ℝ) :
    calibrationSlopeDeviation (calibrationProfile link mean_observed mean_predicted slope).slope =
      calibrationSlopeDeviation slope := by
  rfl

@[simp] theorem CalibrationMoments.toProfile_citl
    (mom : CalibrationMoments) (link : CalibrationLink) :
    (mom.toProfile link).citl =
      calibrationInTheLarge mom.meanObserved mom.meanPredicted := by
  rfl

@[simp] theorem CalibrationMoments.toProfile_slope
    (mom : CalibrationMoments) (link : CalibrationLink) :
    (mom.toProfile link).slope = mom.slope := by
  rfl

@[simp] theorem CalibrationMoments.toProfile_link
    (mom : CalibrationMoments) (link : CalibrationLink) :
    (mom.toProfile link).link = link := by
  rfl

@[simp] theorem CalibrationMoments.toProfile_slopeDeviation
    (mom : CalibrationMoments) (link : CalibrationLink) :
    calibrationSlopeDeviation (mom.toProfile link).slope =
      calibrationSlopeDeviation mom.slope := by
  rfl

@[simp] theorem CalibrationMoments.shifted_meanObserved
    (mom : CalibrationMoments) (observedShift predictedShift slope : ℝ) :
    (mom.shifted observedShift predictedShift slope).meanObserved =
      mom.meanObserved + observedShift := by
  rfl

@[simp] theorem CalibrationMoments.shifted_meanPredicted
    (mom : CalibrationMoments) (observedShift predictedShift slope : ℝ) :
    (mom.shifted observedShift predictedShift slope).meanPredicted =
      mom.meanPredicted + predictedShift := by
  rfl

@[simp] theorem CalibrationMoments.shifted_slope
    (mom : CalibrationMoments) (observedShift predictedShift slope : ℝ) :
    (mom.shifted observedShift predictedShift slope).slope = slope := by
  rfl

/-- Generic profile algebra for target-vs-source calibration moments: once the
target moments are obtained by shifting observed and predicted means, the CITL
change is source CITL plus observed shift minus predicted shift, regardless of
which link label the profile carries. -/
theorem CalibrationMoments.shifted_toProfile_citl_eq_source_citl_add_shift_budget
    (mom : CalibrationMoments)
    (observedShift predictedShift slope : ℝ)
    (link : CalibrationLink) :
    ((mom.shifted observedShift predictedShift slope).toProfile link).citl =
      (mom.toProfile link).citl + observedShift - predictedShift := by
  unfold CalibrationMoments.shifted CalibrationMoments.toProfile
    calibrationProfile calibrationInTheLarge Descent.Core.difference
  ring

/-- Shared absolute-deviation identity for any subunit calibration slope. -/
theorem calibrationSlopeDeviation_eq_one_sub_of_lt_one
    (slope : ℝ) (h_slope : slope < 1) :
    calibrationSlopeDeviation slope = 1 - slope := by
  unfold calibrationSlopeDeviation
  have hneg : slope - 1 < 0 := by linarith
  rw [abs_of_neg hneg]
  ring

/-- **Hosmer-Lemeshow statistic.**
    Group predictions into deciles, compare observed vs expected
    in each group. H-L ~ χ² under good calibration. -/
noncomputable def hosmerLemeshowContrib (observed expected n_group : ℝ) : ℝ :=
  n_group * (observed - expected)^2 / (expected * (1 - expected))

/-- **The Hosmer-Lemeshow denominator really is the binomial variance, pinned.** This definition
carries no result of its own. A group of one whose expected risk is one half and whose observed
rate is one contributes exactly one: the squared deviation is a quarter and the binomial variance
`p (1 - p)` is a quarter, so the contribution is the deviation measured in variance units. A body
dividing by `expected` alone contributes one half here. -/
theorem hosmerLemeshowContrib_unit_variance :
    hosmerLemeshowContrib 1 (1 / 2) 1 = 1 := by
  unfold hosmerLemeshowContrib
  norm_num

/-- **The Hosmer-Lemeshow contribution at a certain forecast, named.** A group whose expected
risk is one has binomial variance zero, so any observed deviation from certainty is infinitely
surprising. The divisor is zero and Lean returns `0`: the group contributes nothing to the
goodness-of-fit statistic no matter how badly the forecast missed. This is the worst direction
for the error to run, since it silently removes exactly the groups where the model failed most.
Consumers must require `0 < expected < 1`. -/
theorem hosmerLemeshowContrib_certain_forecast_is_junk :
    hosmerLemeshowContrib 0 1 1 = 0 := by
  unfold hosmerLemeshowContrib
  norm_num

/-- H-L contribution is nonneg. -/
theorem hl_contrib_nonneg (obs exp n : ℝ)
    (h_n : 0 ≤ n) (h_exp : 0 < exp) (h_exp_lt : exp < 1) :
    0 ≤ hosmerLemeshowContrib obs exp n := by
  unfold hosmerLemeshowContrib
  apply div_nonneg
  · exact mul_nonneg h_n (sq_nonneg _)
  · exact mul_nonneg (le_of_lt h_exp) (by linarith)

end CalibrationDefinitions

end Descent.Portability
