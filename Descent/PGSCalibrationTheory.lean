/-
Released under AGPL-3.0-or-later as described in the file LICENSE.
-/
import Descent.OpenQuestions

namespace Descent

open MeasureTheory
open TransportedMetrics (equalVarianceGaussianAUCFromSignalVariance)

/-!
# PGS Calibration Theory

This file formalizes the theory of PGS calibration — the relationship
between predicted risk and observed outcomes. Calibration is distinct
from discrimination (AUC/R²) and can vary independently across
populations.

Key results:
1. Calibration definitions (calibration-in-the-large, slope, Hosmer-Lemeshow)
2. Calibration vs discrimination independence
3. Population-specific calibration drift
4. Recalibration methods and their limits
5. Decision-theoretic implications of miscalibration

Provenance: derived here, not imported. Wang et al. (2026), Nature Communications 17:942,
substantiates nothing below. It is an empirical study of the polygenic-score portability
gap and does not treat the calibration slope, calibration-in-the-large or the
Hosmer-Lemeshow test. Sources for individual results, where they exist, are cited at
those results.
-/


/-!
## Calibration Definitions

A PGS is well-calibrated if E[Y|PGS = s] = s for binary outcomes,
or if E[Y|PGS = s] = f(s) where f is the identity for the
intended scale.
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
  mean_observed - mean_predicted

/-- **Calibration-in-the-large's sign convention, pinned.** This definition carries no result of
its own, and its entire content is which way the subtraction runs. It is negative when the model
predicts a higher mean than is observed, so a negative value reports over-prediction; the
reversed body reports over-prediction as under-prediction. -/
theorem calibrationInTheLarge_negative_when_overpredicting :
    calibrationInTheLarge 1 3 = -2 := by
  unfold calibrationInTheLarge
  norm_num

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
    calibrationProfile calibrationInTheLarge
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

/-- Logistic-scale prevalence log-odds.

    Empirical status: **VALIDATED**
    (`validation/empirical/simcov/battery_bulk6.py`,
    `test_prevalence_logit`). The oracle is the fitted intercept of an
    intercept-only logistic model on four million simulated binary outcomes,
    which is what a calibration-in-the-large is read off in practice; worst 2.66
    sems over a prediction spanning -3.89182 to -0.61904. -/
noncomputable def prevalenceLogit (pi : ℝ) : ℝ :=
  Real.log (pi / (1 - pi))

/-- **The prevalence logit at zero prevalence, named.** A disease that never occurs has log-odds
of minus infinity. The ratio `pi / (1 - pi)` is zero, `Real.log 0` is junk-zero, and the logit
comes back as `0` -- which is the logit of prevalence ONE HALF. A never-occurring outcome and a
coin flip are assigned the same log-odds, and every calibration-in-the-large shift computed as a
difference of logits inherits it. Consumers must require `0 < pi`. -/
theorem prevalenceLogit_zero_prevalence_is_junk :
    prevalenceLogit 0 = 0 := by
  unfold prevalenceLogit
  simp

/-- **The prevalence logit at unit prevalence, named.** The other end fails to the same value by
a different route: `1 - pi` is zero, the ratio is junk-zero, and `Real.log 0` is junk-zero again.
So a universal outcome and a never-occurring one are BOTH reported at the log-odds of a coin
flip, and are indistinguishable from each other as well as from the middle. Consumers must
require `pi < 1`. -/
theorem prevalenceLogit_unit_prevalence_is_junk :
    prevalenceLogit 1 = 0 := by
  unfold prevalenceLogit
  simp

/-- The logit is zero exactly at even odds. -/
theorem prevalenceLogit_half : prevalenceLogit (1 / 2) = 0 := by
  unfold prevalenceLogit; norm_num

/-- **The logit is odd about even odds**: swapping a disease for its complement flips the sign.
This is the property that makes it a log-odds rather than any other increasing reparameterisation
of prevalence. -/
theorem prevalenceLogit_reflect (pi : ℝ) :
    prevalenceLogit (1 - pi) = -prevalenceLogit pi := by
  unfold prevalenceLogit
  rw [sub_sub_cancel, ← Real.log_inv, inv_div]

/-- **Prevalence-driven logistic intercept shift.**
    If disease prevalence is `π_source` in training and `π_target`
    in the target, the intercept shift on the logistic linear-predictor
    scale is `logit(π_target) - logit(π_source)`.

    Empirical status: **VALIDATED**
    (`validation/empirical/simcov/battery_bulk6.py`,
    `test_prevalence_logit`). Difference of fitted intercepts between two
    simulated populations:

      shift            this def   fitted               sems
      0.02 -> 0.10      1.69460   1.69828±0.00394      0.93
      0.10 -> 0.35      1.57819   1.57618±0.00197      1.02
      0.35 -> 0.02     -3.27278  -3.27761±0.00373      1.29

    The design includes a SIGN REVERSAL, so a formula that had the two
    prevalences the wrong way round would show rather than cancel.

    Power: the prediction spans -3.27278 to 1.69460. Definitional within the logistic model declared
    above: it fixes the shift rather than predicting an observable. -/
noncomputable def prevalenceCITLShift (pi_source pi_target : ℝ) : ℝ :=
  prevalenceLogit pi_target - prevalenceLogit pi_source

/-- Reference evaluation.  The value is computed through the definitions this body calls, but
the theorem states a number: an inequality or an invariance leaves a family of bodies
satisfying it, and a value does not. -/
theorem prevalenceCITLShift_at_reference_point :
    prevalenceCITLShift (1 / 2) (2 / 3) = Real.log 2 := by
  unfold prevalenceCITLShift prevalenceLogit
  norm_num



/-!
## Calibration vs Discrimination

Calibration and discrimination are independent properties.
A model can have good discrimination but poor calibration
and vice versa.
-/

section CalibrationVsDiscrimination

/-- **Additive score shifts preserve AUC and shift CITL by the same offset.**

    AUC depends only on pairwise ranking of scores. Adding a constant offset leaves every
    pairwise comparison unchanged, so population AUC is invariant. Calibration-in-the-large
    shifts by exactly that offset with opposite sign.

    This is not a claim that AUC is independent of calibration, which would be a two-sided
    claim about a family of models. What is exhibited is one family — constant offsets —
    along which AUC is constant and CITL is not. That refutes "discrimination determines
    calibration", which is the use the file makes of it, and does not establish the
    converse, that calibration fails to constrain discrimination.

    Note also that `mean_obs` and `mean_pred` are free reals unconnected to `pop` or
    `score`: the CITL half of the conjunction is an algebraic identity about two arbitrary
    numbers, not a computation of the AUC-invariant score's calibration. -/
theorem auc_invariant_and_citl_shifts_under_score_offset
    {Z : Type*} [MeasurableSpace Z]
    (pop : BinaryPopulation Z) (score : Z → ℝ)
    (mean_obs mean_pred c : ℝ) :
    populationAUC pop (fun z ↦ score z + c) = populationAUC pop score ∧
      calibrationInTheLarge mean_obs (mean_pred + c) =
        calibrationInTheLarge mean_obs mean_pred - c := by
  constructor
  · simpa [Function.comp] using
      populationAUC_strictMono_invariant pop score (fun x ↦ x + c) (by
        intro a b hab
        linarith)
  · unfold calibrationInTheLarge
    ring

/-- **At a fixed mean prediction, the CITL difference is exactly the prevalence
    difference.**

    The name is kept because `LongitudinalPortability` depends on it, but read it as the
    identity it is: `calibrationInTheLarge` is `observed − predicted`, so holding the
    prediction fixed and moving the observed mean from `π₁` to `π₂` moves CITL by
    `π₂ − π₁`. That is `ring`, and in particular it says nothing when `π₁ = π₂`. The
    consequence the name suggests — that a prevalence *change* forces a calibration change —
    is the special case `π₁ ≠ π₂` of this identity, and holds only under the fixed-mean
    prediction assumption built into the statement. -/
theorem prevalence_shift_changes_calibration
    (mean_pred π₁ π₂ : ℝ) :
    calibrationInTheLarge π₂ mean_pred -
      calibrationInTheLarge π₁ mean_pred = π₂ - π₁ := by
  unfold calibrationInTheLarge
  ring

/-- Explicit cross-population calibration-shift budget.

This state separates the distinct reasons why identity-scale calibration can
change after transport:

- prevalence / mean outcome shift,
- environmental mean-outcome shift,
- genetic mean-outcome shift not captured by prevalence alone,
- score-mean transport shift from changed target genetic architecture, and
- any deployment intercept offset applied to the transported score.

This does not treat target calibration drift as a function of prevalence
alone. -/
structure CrossPopulationCalibrationShiftModel where
  /-- Observed mean in the reference population, from which the target is shifted. -/
  baseObservedMean : ℝ
  /-- Predicted mean in the reference population. -/
  basePredictedMean : ℝ
  prevalenceShift : ℝ
  environmentalObservedShift : ℝ
  geneticObservedShift : ℝ
  scoreMeanShift : ℝ
  deploymentInterceptShift : ℝ
  /-- Deployed slope in each population. -/
  slope : Pop → ℝ

/-- Total target observed-mean shift relative to source. -/
noncomputable def CrossPopulationCalibrationShiftModel.observedMeanShift
    (m : CrossPopulationCalibrationShiftModel) : ℝ :=
  m.prevalenceShift + m.environmentalObservedShift + m.geneticObservedShift

/-- Total target predicted-mean shift relative to source. -/
noncomputable def CrossPopulationCalibrationShiftModel.predictedMeanShift
    (m : CrossPopulationCalibrationShiftModel) : ℝ :=
  m.scoreMeanShift + m.deploymentInterceptShift

/-- **Removing the recalibration intercept leaves the score movement.** The predicted mean shift
has exactly two sources, and separating them is what makes recalibration identifiable from a
genuine change in the score distribution. -/
theorem CrossPopulationCalibrationShiftModel.predictedMeanShift_sub_intercept
    (m : CrossPopulationCalibrationShiftModel) :
    m.predictedMeanShift - m.deploymentInterceptShift = m.scoreMeanShift := by
  unfold CrossPopulationCalibrationShiftModel.predictedMeanShift
  ring

/-- **Observed mean in a population.** The source is the reference; the shift budget
applies at the target, recorded by `Pop.pair` rather than by a second definition. -/
noncomputable def CrossPopulationCalibrationShiftModel.observedMean
    (m : CrossPopulationCalibrationShiftModel) (P : Pop) : ℝ :=
  m.baseObservedMean + Pop.pair 0 m.observedMeanShift P

/-- **Deployed mean prediction in a population.** -/
noncomputable def CrossPopulationCalibrationShiftModel.predictedMean
    (m : CrossPopulationCalibrationShiftModel) (P : Pop) : ℝ :=
  m.basePredictedMean + Pop.pair 0 m.predictedMeanShift P

/-- **Calibration moments in a population.**

The mechanistic cross-population calibration model talks in terms of observed and
predicted means plus a deployed slope. These moments are the common bridge into the
generic `CalibrationProfile` algebra.

Both populations read their own means and slope off this one indexed definition. **Do not
build the target moments by applying a `shifted` budget to the source moments** -- that is
a second route to the same triple, kept in step by hand;
`targetCalibrationMoments_eq_shifted` states that the shift route agrees. -/
noncomputable def CrossPopulationCalibrationShiftModel.calibrationMoments
    (m : CrossPopulationCalibrationShiftModel) (P : Pop) : CalibrationMoments where
  meanObserved := m.observedMean P
  meanPredicted := m.predictedMean P
  slope := m.slope P

/-- **Calibration profile in a population**, at any link. -/
noncomputable def CrossPopulationCalibrationShiftModel.calibrationProfile
    (m : CrossPopulationCalibrationShiftModel) (P : Pop) (link : CalibrationLink) :
    CalibrationProfile :=
  (m.calibrationMoments P).toProfile link

/-- **Identity-scale calibration profile in a population.** -/
noncomputable def CrossPopulationCalibrationShiftModel.identityCalibrationProfile
    (m : CrossPopulationCalibrationShiftModel) (P : Pop) : CalibrationProfile :=
  m.calibrationProfile P CalibrationLink.identity

@[simp] theorem CrossPopulationCalibrationShiftModel.observedMean_source
    (m : CrossPopulationCalibrationShiftModel) :
    m.observedMean Pop.source = m.baseObservedMean := by
  simp [CrossPopulationCalibrationShiftModel.observedMean]

@[simp] theorem CrossPopulationCalibrationShiftModel.predictedMean_source
    (m : CrossPopulationCalibrationShiftModel) :
    m.predictedMean Pop.source = m.basePredictedMean := by
  simp [CrossPopulationCalibrationShiftModel.predictedMean]

/-- **The target moments are the source moments carried by the shift budget.** This used
to be the definition of the target moments; it is now a theorem relating two routes. -/
theorem CrossPopulationCalibrationShiftModel.targetCalibrationMoments_eq_shifted
    (m : CrossPopulationCalibrationShiftModel) :
    m.calibrationMoments Pop.target =
      (m.calibrationMoments Pop.source).shifted
        m.observedMeanShift m.predictedMeanShift (m.slope Pop.target) := by
  simp [CrossPopulationCalibrationShiftModel.calibrationMoments,
    CrossPopulationCalibrationShiftModel.observedMean,
    CrossPopulationCalibrationShiftModel.predictedMean, CalibrationMoments.shifted]

@[simp] theorem CrossPopulationCalibrationShiftModel.sourceCalibrationMoments_meanObserved
    (m : CrossPopulationCalibrationShiftModel) :
    (m.calibrationMoments Pop.source).meanObserved = (m.observedMean Pop.source) := by
  rfl

@[simp] theorem CrossPopulationCalibrationShiftModel.sourceCalibrationMoments_meanPredicted
    (m : CrossPopulationCalibrationShiftModel) :
    (m.calibrationMoments Pop.source).meanPredicted = (m.predictedMean Pop.source) := by
  rfl

@[simp] theorem CrossPopulationCalibrationShiftModel.sourceCalibrationMoments_slope
    (m : CrossPopulationCalibrationShiftModel) :
    (m.calibrationMoments Pop.source).slope = (m.slope Pop.source) := by
  rfl

@[simp] theorem CrossPopulationCalibrationShiftModel.targetCalibrationMoments_eq_source_shifted
    (m : CrossPopulationCalibrationShiftModel) :
    (m.calibrationMoments Pop.target) =
      (m.calibrationMoments Pop.source).shifted
        m.observedMeanShift m.predictedMeanShift (m.slope Pop.target) :=
  CrossPopulationCalibrationShiftModel.targetCalibrationMoments_eq_shifted m

@[simp] theorem CrossPopulationCalibrationShiftModel.sourceCalibrationProfile_eq_toProfile
    (m : CrossPopulationCalibrationShiftModel) (link : CalibrationLink) :
    m.calibrationProfile Pop.source link =
      (m.calibrationMoments Pop.source).toProfile link := by
  rfl

@[simp] theorem CrossPopulationCalibrationShiftModel.targetCalibrationProfile_eq_toProfile
    (m : CrossPopulationCalibrationShiftModel) (link : CalibrationLink) :
    m.calibrationProfile Pop.target link =
      (m.calibrationMoments Pop.target).toProfile link := by
  rfl

@[simp] theorem CrossPopulationCalibrationShiftModel.targetObservedMean_eq
    (m : CrossPopulationCalibrationShiftModel) :
    (m.observedMean Pop.target) =
      (m.observedMean Pop.source) +
        m.prevalenceShift + m.environmentalObservedShift + m.geneticObservedShift := by
  simp [CrossPopulationCalibrationShiftModel.observedMean,
    CrossPopulationCalibrationShiftModel.observedMeanShift, add_left_comm,
    add_comm]

@[simp] theorem CrossPopulationCalibrationShiftModel.targetPredictedMean_eq
    (m : CrossPopulationCalibrationShiftModel) :
    (m.predictedMean Pop.target) =
      (m.predictedMean Pop.source) + m.scoreMeanShift + m.deploymentInterceptShift := by
  simp [CrossPopulationCalibrationShiftModel.predictedMean,
    CrossPopulationCalibrationShiftModel.predictedMeanShift, add_assoc]

/-- Generic CITL bridge: the mechanistic target shift budget feeds directly into
the shared calibration-profile algebra for any chosen link label. -/
theorem
    CrossPopulationCalibrationShiftModel.target_profile_citl_eq_source_profile_citl_add_shift_budget
    (m : CrossPopulationCalibrationShiftModel) (link : CalibrationLink) :
    (m.calibrationProfile Pop.target link).citl =
      (m.calibrationProfile Pop.source link).citl +
        m.observedMeanShift - m.predictedMeanShift := by
  rw [CrossPopulationCalibrationShiftModel.calibrationProfile,
    CrossPopulationCalibrationShiftModel.targetCalibrationMoments_eq_shifted,
    CrossPopulationCalibrationShiftModel.calibrationProfile]
  exact
    CalibrationMoments.shifted_toProfile_citl_eq_source_citl_add_shift_budget
      (m.calibrationMoments Pop.source)
      m.observedMeanShift m.predictedMeanShift (m.slope Pop.target) link

/-- Exact CITL decomposition under the explicit calibration-shift budget. -/
theorem CrossPopulationCalibrationShiftModel.target_citl_eq_source_citl_add_shift_budget
    (m : CrossPopulationCalibrationShiftModel) :
    ((m.identityCalibrationProfile Pop.target)).citl =
      ((m.identityCalibrationProfile Pop.source)).citl +
        m.observedMeanShift - m.predictedMeanShift := by
  simpa [CrossPopulationCalibrationShiftModel.identityCalibrationProfile,
    CrossPopulationCalibrationShiftModel.identityCalibrationProfile] using
    CrossPopulationCalibrationShiftModel.target_profile_citl_eq_source_profile_citl_add_shift_budget
      m CalibrationLink.identity

/-- Under a source model calibrated in the large, target CITL is exactly the
full explicit shift budget: observed-mean drift minus predicted-mean drift. -/
theorem source_calibrated_target_citl_eq_shift_budget
    (m : CrossPopulationCalibrationShiftModel)
    (h_src_cal : ((m.identityCalibrationProfile Pop.source)).citl = 0) :
    ((m.identityCalibrationProfile Pop.target)).citl =
      m.observedMeanShift - m.predictedMeanShift := by
  rw [m.target_citl_eq_source_citl_add_shift_budget, h_src_cal]
  ring

/-- Under a source model calibrated in the large, absolute target CITL is the
absolute explicit shift budget. -/
theorem source_calibrated_target_abs_citl_eq_abs_shift_budget
    (m : CrossPopulationCalibrationShiftModel)
    (h_src_cal : ((m.identityCalibrationProfile Pop.source)).citl = 0) :
    |((m.identityCalibrationProfile Pop.target)).citl| =
      |m.observedMeanShift - m.predictedMeanShift| := by
  rw [source_calibrated_target_citl_eq_shift_budget m h_src_cal]

/-- With no environmental, genetic, score-mean, or deployment-intercept shifts,
the explicit calibration budget reduces to pure prevalence shift. This is a
special case, not the general cross-population calibration law. -/
theorem source_calibrated_target_citl_eq_prevalence_shift_of_no_other_shifts
    (m : CrossPopulationCalibrationShiftModel)
    (h_src_cal : ((m.identityCalibrationProfile Pop.source)).citl = 0)
    (h_env : m.environmentalObservedShift = 0)
    (h_genetic : m.geneticObservedShift = 0)
    (h_score : m.scoreMeanShift = 0)
    (h_intercept : m.deploymentInterceptShift = 0) :
    ((m.identityCalibrationProfile Pop.target)).citl = m.prevalenceShift := by
  rw [source_calibrated_target_citl_eq_shift_budget m h_src_cal]
  simp [CrossPopulationCalibrationShiftModel.observedMeanShift,
    CrossPopulationCalibrationShiftModel.predictedMeanShift,
    h_env, h_genetic, h_score, h_intercept]

/-- The absolute pure-prevalence formula is likewise only a zero-other-shifts
special case of the full calibration budget. -/
theorem source_calibrated_target_abs_citl_eq_abs_prevalence_shift_of_no_other_shifts
    (m : CrossPopulationCalibrationShiftModel)
    (h_src_cal : ((m.identityCalibrationProfile Pop.source)).citl = 0)
    (h_env : m.environmentalObservedShift = 0)
    (h_genetic : m.geneticObservedShift = 0)
    (h_score : m.scoreMeanShift = 0)
    (h_intercept : m.deploymentInterceptShift = 0) :
    |((m.identityCalibrationProfile Pop.target)).citl| = |m.prevalenceShift| := by
  rw [source_calibrated_target_abs_citl_eq_abs_shift_budget m h_src_cal]
  simp [CrossPopulationCalibrationShiftModel.observedMeanShift,
    CrossPopulationCalibrationShiftModel.predictedMeanShift,
    h_env, h_genetic, h_score, h_intercept]

/-- Prevalence equality does not force zero target CITL. If the source is
calibrated and non-prevalence calibration shifts remain, then target CITL
still changes even when prevalence itself is unchanged. -/
theorem source_calibrated_target_citl_eq_nonprevalence_shift_when_prevalence_preserved
    (m : CrossPopulationCalibrationShiftModel)
    (h_src_cal : ((m.identityCalibrationProfile Pop.source)).citl = 0)
    (h_prev : m.prevalenceShift = 0) :
    ((m.identityCalibrationProfile Pop.target)).citl =
      m.environmentalObservedShift + m.geneticObservedShift -
        m.scoreMeanShift - m.deploymentInterceptShift := by
  rw [source_calibrated_target_citl_eq_shift_budget m h_src_cal]
  simp [CrossPopulationCalibrationShiftModel.observedMeanShift,
    CrossPopulationCalibrationShiftModel.predictedMeanShift, h_prev]
  ring

/-- Mechanistic calibration state on top of the explicit SNP-level portability
model.

This is the calibration-law companion to `CrossPopulationMetricModel`:
- calibration slope is derived from the literal source-weighted score moments;
- predicted-mean drift is derived from source weights applied to target-vs-source
  tag-mean shifts plus deployment intercept drift; and
- observed-mean drift is recorded through prevalence, environmental, and genetic
  outcome-mean shifts. -/
structure CrossPopulationMechanisticCalibrationModel (p q : ℕ) where
  metric : CrossPopulationMetricModel p q
  /-- Observed mean in the reference population. -/
  baseObservedMean : ℝ
  prevalenceShift : ℝ
  environmentalObservedShift : ℝ
  geneticObservedShift : ℝ
  /-- Deployment intercept in the reference population. -/
  baseDeploymentIntercept : ℝ
  deploymentInterceptShift : ℝ
  /-- Mean tag genotype in each population. -/
  tagMean : Pop → Fin p → ℝ

/-- **The class is inhabited.**  A theorem quantified over an uninhabited structure is
true and empty: kernel-checked, clean axiom report, no content.  This is the witness that
makes the theorems below statements about something. -/
noncomputable def CrossPopulationMechanisticCalibrationModel.witness (p q : ℕ) :
    CrossPopulationMechanisticCalibrationModel p q where
  metric := CrossPopulationMetricModel.witness p q
  baseObservedMean := 0
  prevalenceShift := 0
  environmentalObservedShift := 0
  geneticObservedShift := 0
  baseDeploymentIntercept := 0
  deploymentInterceptShift := 0
  tagMean := fun _ ↦ 0

/-- **Deployment intercept in a population.** The shift applies at the target only. -/
noncomputable def CrossPopulationMechanisticCalibrationModel.deploymentIntercept
    {p q : ℕ} (m : CrossPopulationMechanisticCalibrationModel p q) (P : Pop) : ℝ :=
  m.baseDeploymentIntercept + Pop.pair 0 m.deploymentInterceptShift P

/-- Total target observed-mean shift under the mechanistic calibration state. -/
noncomputable def CrossPopulationMechanisticCalibrationModel.observedMeanShift
    {p q : ℕ} (m : CrossPopulationMechanisticCalibrationModel p q) : ℝ :=
  m.prevalenceShift + m.environmentalObservedShift + m.geneticObservedShift

/-- **Mean transported score in a population.** -/
noncomputable def CrossPopulationMechanisticCalibrationModel.scoreMean
    {p q : ℕ} (m : CrossPopulationMechanisticCalibrationModel p q) (P : Pop) : ℝ :=
  sourceWeightedTagScore m.metric (m.tagMean P)

/-- Predicted-mean shift induced by the source-weighted score acting on the
target-vs-source tag-mean difference. This is the AF/tag-mean channel through
which score means change across populations. -/
noncomputable def CrossPopulationMechanisticCalibrationModel.scoreMeanShift
    {p q : ℕ} (m : CrossPopulationMechanisticCalibrationModel p q) : ℝ :=
  m.scoreMean Pop.target - m.scoreMean Pop.source

/-- **Deployed mean prediction in a population.** -/
noncomputable def CrossPopulationMechanisticCalibrationModel.predictedMean
    {p q : ℕ} (m : CrossPopulationMechanisticCalibrationModel p q) (P : Pop) : ℝ :=
  m.deploymentIntercept P + m.scoreMean P

/-- **Observed mean in a population.** -/
noncomputable def CrossPopulationMechanisticCalibrationModel.observedMean
    {p q : ℕ} (m : CrossPopulationMechanisticCalibrationModel p q) (P : Pop) : ℝ :=
  m.baseObservedMean + Pop.pair 0 m.observedMeanShift P

/-- **Literal calibration slope in a population** on the explicit SNP-level transport
state. This was two definitions differing only in which `Pop` they passed through. -/
noncomputable def CrossPopulationMechanisticCalibrationModel.calibrationSlope
    {p q : ℕ} (m : CrossPopulationMechanisticCalibrationModel p q) (P : Pop) : ℝ :=
  calibrationSlopeFromSourceWeights m.metric P

/-- Algebraic bridge from the mechanistic calibration state into the generic
shift-profile container. -/
noncomputable def CrossPopulationMechanisticCalibrationModel.toShiftModel
    {p q : ℕ} (m : CrossPopulationMechanisticCalibrationModel p q) :
    CrossPopulationCalibrationShiftModel where
  baseObservedMean := (m.observedMean Pop.source)
  basePredictedMean := (m.predictedMean Pop.source)
  prevalenceShift := m.prevalenceShift
  environmentalObservedShift := m.environmentalObservedShift
  geneticObservedShift := m.geneticObservedShift
  scoreMeanShift := m.scoreMeanShift
  deploymentInterceptShift := m.deploymentInterceptShift
  slope := Pop.pair (m.calibrationSlope Pop.source) (m.calibrationSlope Pop.target)

/-- Shared source calibration profile on the mechanistic calibration state. -/
noncomputable def CrossPopulationMechanisticCalibrationModel.calibrationProfile
    {p q : ℕ} (m : CrossPopulationMechanisticCalibrationModel p q)
    (P : Pop) (link : CalibrationLink) : CalibrationProfile :=
  m.toShiftModel.calibrationProfile P link

/-- **Identity-scale calibration profile in a population**, on the mechanistic state. -/
noncomputable def CrossPopulationMechanisticCalibrationModel.identityCalibrationProfile
    {p q : ℕ} (m : CrossPopulationMechanisticCalibrationModel p q) (P : Pop) :
    CalibrationProfile :=
  m.calibrationProfile P CalibrationLink.identity

@[simp] theorem CrossPopulationMechanisticCalibrationModel.scoreMeanShift_eq_target_minus_source
    {p q : ℕ} (m : CrossPopulationMechanisticCalibrationModel p q) :
    m.scoreMeanShift = (m.scoreMean Pop.target) - (m.scoreMean Pop.source) := by
  rfl

@[simp] theorem CrossPopulationMechanisticCalibrationModel.targetPredictedMean_eq
    {p q : ℕ} (m : CrossPopulationMechanisticCalibrationModel p q) :
    (m.predictedMean Pop.target) =
      (m.predictedMean Pop.source) + m.scoreMeanShift + m.deploymentInterceptShift := by
  simp [CrossPopulationMechanisticCalibrationModel.predictedMean,
    CrossPopulationMechanisticCalibrationModel.deploymentIntercept,
    CrossPopulationMechanisticCalibrationModel.scoreMeanShift]
  ring

@[simp] theorem CrossPopulationMechanisticCalibrationModel.toShiftModel_sourceSlope
    {p q : ℕ} (m : CrossPopulationMechanisticCalibrationModel p q) :
    (m.toShiftModel.slope Pop.source) = calibrationSlopeFromSourceWeights m.metric Pop.source := by
  rfl

@[simp] theorem CrossPopulationMechanisticCalibrationModel.toShiftModel_targetSlope
    {p q : ℕ} (m : CrossPopulationMechanisticCalibrationModel p q) :
    (m.toShiftModel.slope Pop.target) = calibrationSlopeFromSourceWeights m.metric Pop.target := by
  rfl

@[simp] theorem CrossPopulationMechanisticCalibrationModel.toShiftModel_targetObservedMean
    {p q : ℕ} (m : CrossPopulationMechanisticCalibrationModel p q) :
    (m.toShiftModel.observedMean Pop.target) = (m.observedMean Pop.target) := by
  simp [CrossPopulationMechanisticCalibrationModel.toShiftModel,
    CrossPopulationMechanisticCalibrationModel.observedMean,
    CrossPopulationMechanisticCalibrationModel.observedMeanShift,
    CrossPopulationCalibrationShiftModel.observedMean,
    CrossPopulationCalibrationShiftModel.observedMeanShift, add_assoc]

@[simp] theorem CrossPopulationMechanisticCalibrationModel.toShiftModel_targetPredictedMean
    {p q : ℕ} (m : CrossPopulationMechanisticCalibrationModel p q) :
    (m.toShiftModel.predictedMean Pop.target) = (m.predictedMean Pop.target) := by
  simp [CrossPopulationMechanisticCalibrationModel.toShiftModel,
    CrossPopulationMechanisticCalibrationModel.predictedMean,
    CrossPopulationMechanisticCalibrationModel.deploymentIntercept,
    CrossPopulationMechanisticCalibrationModel.scoreMeanShift_eq_target_minus_source,
    CrossPopulationCalibrationShiftModel.predictedMean,
    CrossPopulationCalibrationShiftModel.predictedMeanShift]
  ring

namespace CrossPopulationMechanisticCalibrationModel

/-- Shared definitional reduction for the three mechanistic calibration-profile projections
below.  Keeping this list in one tactic prevents source and target laws from silently drifting
to different model layers. -/
macro "unfold_mechanistic_calibration_profile" : tactic =>
  `(tactic| simp only
    [CrossPopulationMechanisticCalibrationModel.calibrationProfile,
      CrossPopulationMechanisticCalibrationModel.toShiftModel,
      CrossPopulationCalibrationShiftModel.calibrationProfile,
      CrossPopulationCalibrationShiftModel.calibrationMoments,
      CrossPopulationMechanisticCalibrationModel.calibrationSlope])

/-- Exact mechanistic source calibration-profile law. The source predicted mean
is the deployed intercept plus the source-weighted source tag mean, and the
source slope is the literal source `Cov/Var` ratio from the SNP-level score
equation. -/
theorem sourceCalibrationProfile_exact_mechanistic_portability_law
    {p q : ℕ} (m : CrossPopulationMechanisticCalibrationModel p q)
    (link : CalibrationLink) :
    m.calibrationProfile Pop.source link =
      { citl :=
          (m.observedMean Pop.source) -
            ((m.deploymentIntercept Pop.source) +
              sourceWeightedTagScore m.metric (m.tagMean Pop.source))
      , slope :=
          predictiveCovarianceFromSourceWeights m.metric Pop.source /
            scoreVarianceFromSourceWeights m.metric Pop.source
      , link := link } := by
  cases link <;>
    unfold_mechanistic_calibration_profile <;>
    simp [
      CrossPopulationMechanisticCalibrationModel.observedMean,
      CrossPopulationMechanisticCalibrationModel.predictedMean,
      CrossPopulationMechanisticCalibrationModel.deploymentIntercept,
      CrossPopulationMechanisticCalibrationModel.scoreMean,
      CalibrationMoments.toProfile, Descent.calibrationProfile,
      calibrationSlopeFromSourceWeights, calibrationInTheLarge]

/-- Exact mechanistic target calibration-profile portability law. The target
predicted mean is the deployed source weights applied to the target tag mean,
plus deployment intercept drift, and the target slope is the literal
transported `Cov/Var` ratio from the SNP-level score equation. -/
theorem targetCalibrationProfile_exact_mechanistic_portability_law
    {p q : ℕ} (m : CrossPopulationMechanisticCalibrationModel p q)
    (link : CalibrationLink) :
    m.calibrationProfile Pop.target link =
      { citl :=
          ((m.observedMean Pop.source) +
              (m.prevalenceShift + m.environmentalObservedShift + m.geneticObservedShift)) -
            ((m.deploymentIntercept Pop.source) + m.deploymentInterceptShift +
              sourceWeightedTagScore m.metric (m.tagMean Pop.target))
      , slope :=
          predictiveCovarianceFromSourceWeights m.metric Pop.target /
            scoreVarianceFromSourceWeights m.metric Pop.target
      , link := link } := by
  cases link <;>
    unfold_mechanistic_calibration_profile <;>
    simp [
      CrossPopulationMechanisticCalibrationModel.predictedMean,
      CrossPopulationMechanisticCalibrationModel.scoreMean,
      CrossPopulationMechanisticCalibrationModel.deploymentIntercept,
      CalibrationMoments.toProfile,
      Descent.calibrationProfile, calibrationSlopeFromSourceWeights,
      calibrationInTheLarge, sub_eq_add_neg, add_assoc] <;> ring

/-- Exact mechanistic CITL law: calibration-in-the-large is source CITL plus
observed-mean drift minus the source-weighted score-mean drift and deployment
intercept drift. -/
theorem target_profile_citl_eq_source_profile_citl_add_exact_biological_shift_budget
    {p q : ℕ} (m : CrossPopulationMechanisticCalibrationModel p q)
    (link : CalibrationLink) :
    (m.calibrationProfile Pop.target link).citl =
      (m.calibrationProfile Pop.source link).citl +
        m.observedMeanShift - (m.scoreMeanShift + m.deploymentInterceptShift) := by
  simpa [CrossPopulationMechanisticCalibrationModel.calibrationProfile,
    CrossPopulationMechanisticCalibrationModel.toShiftModel,
    CrossPopulationMechanisticCalibrationModel.observedMeanShift,
    CrossPopulationMechanisticCalibrationModel.scoreMeanShift,
    CrossPopulationCalibrationShiftModel.observedMeanShift,
    CrossPopulationCalibrationShiftModel.predictedMeanShift] using
    CrossPopulationCalibrationShiftModel.target_profile_citl_eq_source_profile_citl_add_shift_budget
      m.toShiftModel link

end CrossPopulationMechanisticCalibrationModel

/-- Exact mechanistic target slope law with direct-causal, proxy-tagging, and
context channels made explicit. -/
theorem CrossPopulationMechanisticCalibrationModel.target_profile_slope_eq_direct_proxy_context_law
    {p q : ℕ} (m : CrossPopulationMechanisticCalibrationModel p q)
    (link : CalibrationLink) :
    (m.calibrationProfile Pop.target link).slope =
      (sourceWeightedTagScore m.metric (directCausalProjection m.metric Pop.target) +
        sourceWeightedTagScore m.metric (proxyTaggingProjection m.metric Pop.target) +
        sourceWeightedTagScore m.metric (m.metric.contextCross Pop.target)) /
          scoreVarianceFromSourceWeights m.metric Pop.target := by
  unfold_mechanistic_calibration_profile
  simp [
    CalibrationMoments.toProfile, calibrationProfile,
    targetCalibrationSlopeFromSourceWeights_exact_direct_proxy_context_law]

/-- **The AUC-and-CITL projection**, as one proposition about a source profile, a target
profile and a shift budget: discrimination falls, the target's calibration-in-the-large is
the budget, its size is the budget's size, and it is strictly worse than the source's.

The two theorems below conclude exactly this, at two different source profiles, and each
wrote the four conjuncts and their `let`-bound profiles out in full.  Named, the difference
between them is visible in one argument -- which prevalence the source profile is read at
-- instead of being buried in nine lines that agree. -/
def AucDropsAndCitlWorsens (cal : CrossPopulationCalibrationShiftModel)
    (sourceMetrics targetMetrics : TransportedMetrics.Profile) : Prop :=
  targetMetrics.auc < sourceMetrics.auc ∧
    ((cal.identityCalibrationProfile Pop.target)).citl =
      cal.observedMeanShift - cal.predictedMeanShift ∧
    |((cal.identityCalibrationProfile Pop.target)).citl| =
      |cal.observedMeanShift - cal.predictedMeanShift| ∧
    |((cal.identityCalibrationProfile Pop.source)).citl| <
      |((cal.identityCalibrationProfile Pop.target)).citl|

/-- **An `R²` drop transports to an AUC drop**, through the explained-`R²` chart and its
strict monotonicity on the unit interval.

This is the step both projection theorems below take to reach their AUC conjunct, and both
took it inline: the same two chart rewrites and the same appeal to monotonicity, eight
lines each.  The step is about the score's `R²`, not about which prevalence a source
profile is read at, so it is stated here without either. -/
theorem targetAUCFromSourceWeights_lt_source_of_r2_drop {p q : ℕ}
    (metric : CrossPopulationMetricModel p q)
    (h_source_r2_unit : r2FromSourceWeights metric Pop.source ∈ Set.Ico 0 1)
    (h_target_r2_unit : r2FromSourceWeights metric Pop.target ∈ Set.Ico 0 1)
    (h_r2_drop :
      r2FromSourceWeights metric Pop.target < r2FromSourceWeights metric Pop.source) :
    equalVarianceGaussianAUCFromSourceWeights metric Pop.target <
      equalVarianceGaussianAUCFromSourceWeights metric Pop.source := by
  rw [targetEqualVarianceGaussianAUCFromSourceWeights_eq_explainedR2_chart_of_lt_one
      metric h_target_r2_unit.2,
    sourceEqualVarianceGaussianAUCFromSourceWeights_eq_explainedR2_chart_of_lt_one
      metric h_source_r2_unit.2]
  exact equalVarianceGaussianAUCFromExplainedR2_strictMonoOn_unitInterval
    h_target_r2_unit h_source_r2_unit h_r2_drop

/-- **What a perfectly calibrated source and a nonzero shift budget give at the target**:
the target CITL is the budget, its size is the budget's size, and it is strictly worse than
the source's, which is zero.

Both projection theorems below need exactly these three facts and each derived them inline,
in the same order, from the same two lemmas -- seventeen lines, twice. -/
theorem source_calibrated_target_citl_facts
    (cal : CrossPopulationCalibrationShiftModel)
    (h_src_cal : ((cal.identityCalibrationProfile Pop.source)).citl = 0)
    (h_shift_nonzero : cal.observedMeanShift - cal.predictedMeanShift ≠ 0) :
    ((cal.identityCalibrationProfile Pop.target)).citl =
        cal.observedMeanShift - cal.predictedMeanShift ∧
      |((cal.identityCalibrationProfile Pop.target)).citl| =
        |cal.observedMeanShift - cal.predictedMeanShift| ∧
      |((cal.identityCalibrationProfile Pop.source)).citl| <
        |((cal.identityCalibrationProfile Pop.target)).citl| := by
  have h_citl_eq :
      ((cal.identityCalibrationProfile Pop.target)).citl =
        cal.observedMeanShift - cal.predictedMeanShift :=
    source_calibrated_target_citl_eq_shift_budget cal h_src_cal
  refine ⟨h_citl_eq, source_calibrated_target_abs_citl_eq_abs_shift_budget cal h_src_cal, ?_⟩
  have h_tgt_ne_zero : ((cal.identityCalibrationProfile Pop.target)).citl ≠ 0 := by
    rw [h_citl_eq]
    exact h_shift_nonzero
  have h_tgt_abs_pos :
      0 < |((cal.identityCalibrationProfile Pop.target)).citl| :=
    abs_pos.mpr h_tgt_ne_zero
  simpa [h_src_cal] using h_tgt_abs_pos

/-- **Exact cross-ancestry metric profile from the mechanistic SNP-level
transport model plus an explicit calibration-shift budget.**

This is the headline exact theorem for the calibration block:

- AUC is the mechanistic source-vs-target AUC from the explicit
  source-weights-on-target-covariance score equation;
- CITL is the explicit observed-minus-predicted target shift budget;
- absolute CITL worsens whenever that shift budget is nonzero; and
- Brier is the mechanistic source-vs-target calibrated Brier comparison on the
  target-population observed prevalence scale.

No neutral-allele-frequency benchmark metrics appear in the statement. This is
the generic shift-budget corollary used by the fully mechanistic calibration
law below.

**What is assumed rather than derived**, since the word "exact" in the name is about the
formulae and not about the direction of travel. Three of the four conclusions are
transport of a hypothesis, not a discovery:

- `targetMetrics.auc < sourceMetrics.auc` and `sourceMetrics.brier < targetMetrics.brier`
  both come from `h_r2_drop`, which *assumes* the target R² is lower. Nothing here shows
  that cross-ancestry transport lowers R². What is proved is that a drop in R² propagates
  to AUC and to calibrated Brier through the monotone charts — a real and reusable step,
  but a conditional one.
- `|sourceProfile.citl| < |targetProfile.citl|` is immediate from `h_src_cal`, which
  assumes the source is perfectly calibrated in the large, together with
  `h_shift_nonzero`. Against a source CITL pinned to `0`, any nonzero shift is worse.

This theorem carries **no** `hPhiStrict : StrictMono Phi` hypothesis, and needs none.
`Probability.strictMono_Phi` proves it: `Phi` is `ProbabilityTheory.cdf (gaussianReal 0 1)`,
and its strict monotonicity follows from the Gaussian density being positive.  Every use
below resolves against that theorem. -/
theorem source_to_target_exact_metric_profile_from_shift_budget
    {p q : ℕ}
    (metric : CrossPopulationMetricModel p q)
    (cal : CrossPopulationCalibrationShiftModel)
    (h_target_mean_eq_prevalence :
      (cal.observedMean Pop.target) = metric.targetPrevalence)
    (h_source_r2_unit : r2FromSourceWeights metric Pop.source ∈ Set.Ico 0 1)
    (h_target_r2_unit : r2FromSourceWeights metric Pop.target ∈ Set.Ico 0 1)
    (h_r2_drop :
      r2FromSourceWeights metric Pop.target < r2FromSourceWeights metric Pop.source)
    (h_src_cal : ((cal.identityCalibrationProfile Pop.source)).citl = 0)
    (h_shift_nonzero :
      cal.observedMeanShift - cal.predictedMeanShift ≠ 0) :
    AucDropsAndCitlWorsens cal
        (sourceMetricProfileFromSourceWeightsAtPrevalence metric (cal.observedMean Pop.target))
        (targetMetricProfileFromSourceWeights metric) ∧
      (sourceMetricProfileFromSourceWeightsAtPrevalence metric
          (cal.observedMean Pop.target)).brier <
        (targetMetricProfileFromSourceWeights metric).brier := by
  unfold AucDropsAndCitlWorsens
  have h_auc :
      (targetMetricProfileFromSourceWeights metric).auc <
        (sourceMetricProfileFromSourceWeightsAtPrevalence
          metric (cal.observedMean Pop.target)).auc := by
    rw [targetMetricProfileFromSourceWeights_auc,
      sourceMetricProfileFromSourceWeightsAtPrevalence_auc]
    exact targetAUCFromSourceWeights_lt_source_of_r2_drop metric
      h_source_r2_unit h_target_r2_unit h_r2_drop
  obtain ⟨h_citl_eq, h_abs_eq, h_abs_worse⟩ :=
    source_calibrated_target_citl_facts cal h_src_cal h_shift_nonzero
  have h_brier :
      (sourceMetricProfileFromSourceWeightsAtPrevalence
        metric (cal.observedMean Pop.target)).brier <
        (targetMetricProfileFromSourceWeights metric).brier := by
    rw [sourceMetricProfileFromSourceWeightsAtPrevalence_brier,
      targetMetricProfileFromSourceWeights_brier,
      sourceCalibratedBrierFromSourceWeightsAtPrevalence_eq_explainedR2_chart,
      targetCalibratedBrierFromSourceWeights_eq_explainedR2_chart,
      h_target_mean_eq_prevalence]
    simpa [brierFromR2, sourceBrierFromR2, TransportedMetrics.calibratedBrier] using
      brierFromR2_strictAnti metric.targetPrevalence
        metric.targetPrevalence_pos metric.targetPrevalence_lt_one h_r2_drop
  exact ⟨⟨h_auc, h_citl_eq, h_abs_eq, h_abs_worse⟩, h_brier⟩

/-- **Exact cross-ancestry metric portability law from the mechanistic
SNP-level transport model and mechanistic calibration state.**

This is the headline law surface for deployed metrics:

- AUC is the mechanistic source-vs-target AUC from the explicit
  source-weights-on-target-covariance score equation;
- CITL is the exact biological mean-shift budget
  `observed drift - source-weighted score-mean drift - deployment intercept drift`;
- calibration slope is the literal transported `Cov/Var` ratio on the same
  score equation; and
- Brier is the mechanistic source-vs-target calibrated Brier comparison on the
  target-population observed prevalence scale.

The same reading applies as for `source_to_target_exact_metric_profile_from_shift_budget`,
which this theorem is a mechanistic instance of: the AUC drop and the Brier worsening are
carried by the hypothesis `h_r2_drop`, and the calibration worsening by `h_src_cal`
together with `h_shift_nonzero`. "Exact" qualifies the formulae for CITL and slope, which
are computed from the SNP-level state, not the direction of the metric changes, which are
assumed. -/
theorem source_to_target_exact_metric_profile
    {p q : ℕ}
    (cal : CrossPopulationMechanisticCalibrationModel p q)
    (h_target_mean_eq_prevalence :
      (cal.observedMean Pop.target) = cal.metric.targetPrevalence)
    (h_source_r2_unit : r2FromSourceWeights cal.metric Pop.source ∈ Set.Ico 0 1)
    (h_target_r2_unit : r2FromSourceWeights cal.metric Pop.target ∈ Set.Ico 0 1)
    (h_r2_drop :
      r2FromSourceWeights cal.metric Pop.target < r2FromSourceWeights cal.metric Pop.source)
    (h_src_cal : ((cal.identityCalibrationProfile Pop.source)).citl = 0)
    (h_shift_nonzero :
      cal.observedMeanShift - (cal.scoreMeanShift + cal.deploymentInterceptShift) ≠ 0) :
    let sourceProfile := (cal.identityCalibrationProfile Pop.source)
    let targetProfile := (cal.identityCalibrationProfile Pop.target)
    let sourceMetrics :=
      sourceMetricProfileFromSourceWeightsAtPrevalence cal.metric (cal.observedMean Pop.target)
    let targetMetrics := targetMetricProfileFromSourceWeights cal.metric
    targetMetrics.auc < sourceMetrics.auc ∧
    targetProfile.citl =
      cal.observedMeanShift - (cal.scoreMeanShift + cal.deploymentInterceptShift) ∧
    |targetProfile.citl| =
      |cal.observedMeanShift - (cal.scoreMeanShift + cal.deploymentInterceptShift)| ∧
    |sourceProfile.citl| < |targetProfile.citl| ∧
    sourceMetrics.brier < targetMetrics.brier := by
  have h_target_mean_eq_prevalence_shift :
      (cal.toShiftModel.observedMean Pop.target) = cal.metric.targetPrevalence := by
    simpa [CrossPopulationMechanisticCalibrationModel.toShiftModel,
      CrossPopulationMechanisticCalibrationModel.observedMean,
      CrossPopulationMechanisticCalibrationModel.observedMeanShift,
      CrossPopulationCalibrationShiftModel.observedMean,
      CrossPopulationCalibrationShiftModel.observedMeanShift] using
      h_target_mean_eq_prevalence
  have h_src_cal_shift :
      ((cal.toShiftModel.identityCalibrationProfile Pop.source)).citl = 0 := by
    simpa only [CrossPopulationMechanisticCalibrationModel.identityCalibrationProfile,
      CrossPopulationMechanisticCalibrationModel.calibrationProfile,
      CrossPopulationCalibrationShiftModel.identityCalibrationProfile] using h_src_cal
  have h_shift_nonzero_shift :
      cal.toShiftModel.observedMeanShift - cal.toShiftModel.predictedMeanShift ≠ 0 := by
    simpa [CrossPopulationMechanisticCalibrationModel.toShiftModel,
      CrossPopulationMechanisticCalibrationModel.observedMeanShift,
      CrossPopulationMechanisticCalibrationModel.scoreMeanShift,
      CrossPopulationCalibrationShiftModel.observedMeanShift,
      CrossPopulationCalibrationShiftModel.predictedMeanShift,
      sub_eq_add_neg, add_assoc] using h_shift_nonzero
  have h_main :=
    source_to_target_exact_metric_profile_from_shift_budget cal.metric cal.toShiftModel
      h_target_mean_eq_prevalence_shift h_source_r2_unit h_target_r2_unit h_r2_drop
      h_src_cal_shift h_shift_nonzero_shift
  unfold AucDropsAndCitlWorsens at h_main
  dsimp at h_main ⊢
  rcases h_main with ⟨⟨h_auc, h_citl, h_abs, h_worse⟩, h_brier⟩
  refine ⟨h_auc, ?_, ?_, ?_, ?_⟩
  · simpa [CrossPopulationMechanisticCalibrationModel.identityCalibrationProfile,
      CrossPopulationMechanisticCalibrationModel.calibrationProfile,
      CrossPopulationMechanisticCalibrationModel.toShiftModel,
      CrossPopulationMechanisticCalibrationModel.observedMeanShift,
      CrossPopulationMechanisticCalibrationModel.scoreMeanShift,
      CrossPopulationCalibrationShiftModel.observedMeanShift,
      CrossPopulationCalibrationShiftModel.predictedMeanShift] using h_citl
  · simpa [CrossPopulationMechanisticCalibrationModel.identityCalibrationProfile,
      CrossPopulationMechanisticCalibrationModel.calibrationProfile,
      CrossPopulationMechanisticCalibrationModel.toShiftModel,
      CrossPopulationMechanisticCalibrationModel.observedMeanShift,
      CrossPopulationMechanisticCalibrationModel.scoreMeanShift,
      CrossPopulationCalibrationShiftModel.observedMeanShift,
      CrossPopulationCalibrationShiftModel.predictedMeanShift] using h_abs
  · exact h_worse
  · simpa [CrossPopulationMechanisticCalibrationModel.toShiftModel,
      CrossPopulationMechanisticCalibrationModel.observedMean,
      CrossPopulationMechanisticCalibrationModel.observedMeanShift,
      CrossPopulationCalibrationShiftModel.observedMean,
      CrossPopulationCalibrationShiftModel.observedMeanShift, add_assoc] using h_brier

/-- Generation-indexed mechanistic calibration state tied directly to the
generation-indexed SNP/popgen transport model. -/
structure CrossPopulationGenerationalCalibrationModel (p q : ℕ) where
  metric : CrossPopulationGenerationalModel p q
  baseObservedMean : ℝ
  prevalenceShiftAt : ℕ → ℝ
  environmentalObservedShiftAt : ℕ → ℝ
  geneticObservedShiftAt : ℕ → ℝ
  baseDeploymentIntercept : ℝ
  deploymentInterceptShiftAt : ℕ → ℝ
  baseTagMean : Fin p → ℝ
  targetTagMeanAt : ℕ → Fin p → ℝ

/-- **The generational calibration state is inhabited**, at every panel size `(p, q)`.

    The only field carrying obligations is `metric`, and it is supplied by
    `CrossPopulationGenerationalModel.witness` rather than assumed. The remaining
    fields are the flat state: no observed-mean shift, no intercept drift, and
    equal tag means in the two populations at every generation — the configuration
    in which the calibration profile is exactly the source one. It establishes
    that the generational results below are about something; a state with genuine
    drift is what they are for. -/
noncomputable def CrossPopulationGenerationalCalibrationModel.witness (p q : ℕ) :
    CrossPopulationGenerationalCalibrationModel p q where
  metric := CrossPopulationGenerationalModel.witness p q
  baseObservedMean := 0
  prevalenceShiftAt := fun _ ↦ 0
  environmentalObservedShiftAt := fun _ ↦ 0
  geneticObservedShiftAt := fun _ ↦ 0
  baseDeploymentIntercept := 0
  deploymentInterceptShiftAt := fun _ ↦ 0
  baseTagMean := fun _ ↦ 0
  targetTagMeanAt := fun _ _ ↦ 0

/-- **Mean tag genotype in a population at generation `t`.** The source state is fixed, so
the source slice ignores `t`; indexing both populations the same way is what lets the
score, prediction and observation below be one definition each instead of two. -/
noncomputable def CrossPopulationGenerationalCalibrationModel.tagMeanAt
    {p q : ℕ} (m : CrossPopulationGenerationalCalibrationModel p q) (P : Pop) (t : ℕ) :
    Fin p → ℝ :=
  Pop.pair m.baseTagMean (m.targetTagMeanAt t) P

/-- **Deployment intercept in a population at generation `t`.** -/
noncomputable def CrossPopulationGenerationalCalibrationModel.deploymentInterceptAt
    {p q : ℕ} (m : CrossPopulationGenerationalCalibrationModel p q) (P : Pop) (t : ℕ) : ℝ :=
  m.baseDeploymentIntercept + Pop.pair 0 (m.deploymentInterceptShiftAt t) P

/-- Total target observed-mean shift at generation `t`. -/
noncomputable def CrossPopulationGenerationalCalibrationModel.observedMeanShiftAt
    {p q : ℕ} (m : CrossPopulationGenerationalCalibrationModel p q) (t : ℕ) : ℝ :=
  m.prevalenceShiftAt t + m.environmentalObservedShiftAt t + m.geneticObservedShiftAt t

/-- **Mean transported score in a population at generation `t`.** -/
noncomputable def CrossPopulationGenerationalCalibrationModel.scoreMeanAt
    {p q : ℕ} (m : CrossPopulationGenerationalCalibrationModel p q) (P : Pop) (t : ℕ) : ℝ :=
  sourceWeightedTagScore (m.metric.toMetricModelAt t) (m.tagMeanAt P t)

/-- **Score-mean shift at generation `t`**, as the difference of the two score means
rather than a separately written score of a tag-mean difference. -/
noncomputable def CrossPopulationGenerationalCalibrationModel.scoreMeanShiftAt
    {p q : ℕ} (m : CrossPopulationGenerationalCalibrationModel p q) (t : ℕ) : ℝ :=
  m.scoreMeanAt Pop.target t - m.scoreMeanAt Pop.source t

/-- **Deployed mean prediction in a population at generation `t`.** -/
noncomputable def CrossPopulationGenerationalCalibrationModel.predictedMeanAt
    {p q : ℕ} (m : CrossPopulationGenerationalCalibrationModel p q) (P : Pop) (t : ℕ) : ℝ :=
  m.deploymentInterceptAt P t + m.scoreMeanAt P t

/-- **Observed mean in a population at generation `t`.** -/
noncomputable def CrossPopulationGenerationalCalibrationModel.observedMeanAt
    {p q : ℕ} (m : CrossPopulationGenerationalCalibrationModel p q) (P : Pop) (t : ℕ) : ℝ :=
  m.baseObservedMean + Pop.pair 0 (m.observedMeanShiftAt t) P

/-- Slice the generational calibration state to the static mechanistic
calibration state at generation `t`. -/
noncomputable def CrossPopulationGenerationalCalibrationModel.toMechanisticCalibrationModelAt
    {p q : ℕ} (m : CrossPopulationGenerationalCalibrationModel p q) (t : ℕ) :
    CrossPopulationMechanisticCalibrationModel p q where
  metric := m.metric.toMetricModelAt t
  baseObservedMean := m.baseObservedMean
  prevalenceShift := m.prevalenceShiftAt t
  environmentalObservedShift := m.environmentalObservedShiftAt t
  geneticObservedShift := m.geneticObservedShiftAt t
  baseDeploymentIntercept := m.baseDeploymentIntercept
  deploymentInterceptShift := m.deploymentInterceptShiftAt t
  tagMean := Pop.pair m.baseTagMean (m.targetTagMeanAt t)

/-- The score-mean shift is the difference of the two score means. This needed a
`sourceWeightedTagScore`/`dotProduct` linearity argument while the shift was defined as the
score of a tag-mean difference; defining it as the difference makes it `rfl`. -/
@[simp] theorem CrossPopulationGenerationalCalibrationModel.scoreMeanShiftAt_eq_target_minus_source
    {p q : ℕ} (m : CrossPopulationGenerationalCalibrationModel p q) (t : ℕ) :
    m.scoreMeanShiftAt t = m.scoreMeanAt Pop.target t - m.scoreMeanAt Pop.source t := rfl

@[simp] theorem CrossPopulationGenerationalCalibrationModel.targetPredictedMeanAt_eq
    {p q : ℕ} (m : CrossPopulationGenerationalCalibrationModel p q) (t : ℕ) :
    m.predictedMeanAt Pop.target t =
      m.predictedMeanAt Pop.source t + m.scoreMeanShiftAt t + m.deploymentInterceptShiftAt t := by
  unfold CrossPopulationGenerationalCalibrationModel.predictedMeanAt
    CrossPopulationGenerationalCalibrationModel.scoreMeanShiftAt
    CrossPopulationGenerationalCalibrationModel.deploymentInterceptAt
  simp
  ring

@[simp] theorem
    CrossPopulationGenerationalCalibrationModel.toMechanisticCalibrationModelAt_targetObservedMean
    {p q : ℕ} (m : CrossPopulationGenerationalCalibrationModel p q) (t : ℕ) :
    (m.toMechanisticCalibrationModelAt t).observedMean Pop.target =
      m.observedMeanAt Pop.target t := by
  simp [CrossPopulationGenerationalCalibrationModel.toMechanisticCalibrationModelAt,
    CrossPopulationGenerationalCalibrationModel.observedMeanAt,
    CrossPopulationGenerationalCalibrationModel.observedMeanShiftAt,
    CrossPopulationMechanisticCalibrationModel.observedMean,
    CrossPopulationMechanisticCalibrationModel.observedMeanShift, add_assoc]

@[simp] theorem
    CrossPopulationGenerationalCalibrationModel.toMechanisticCalibrationModelAt_targetPredictedMean
    {p q : ℕ} (m : CrossPopulationGenerationalCalibrationModel p q) (t : ℕ) :
    (m.toMechanisticCalibrationModelAt t).predictedMean Pop.target =
      m.predictedMeanAt Pop.target t := by
  simp [CrossPopulationGenerationalCalibrationModel.toMechanisticCalibrationModelAt,
    CrossPopulationGenerationalCalibrationModel.predictedMeanAt,
    CrossPopulationGenerationalCalibrationModel.scoreMeanAt,
    CrossPopulationGenerationalCalibrationModel.tagMeanAt,
    CrossPopulationGenerationalCalibrationModel.deploymentInterceptAt,
    CrossPopulationMechanisticCalibrationModel.predictedMean,
    CrossPopulationMechanisticCalibrationModel.deploymentIntercept,
    CrossPopulationMechanisticCalibrationModel.scoreMean]

/-- Shared target calibration profile at generation `t`. -/
noncomputable def targetCalibrationProfileAtGeneration
    {p q : ℕ} (m : CrossPopulationGenerationalCalibrationModel p q)
    (t : ℕ) (link : CalibrationLink) : CalibrationProfile :=
  (m.toMechanisticCalibrationModelAt t).calibrationProfile Pop.target link

/-- Identity-scale target calibration profile at generation `t`. -/
noncomputable def targetIdentityCalibrationProfileAtGeneration
    {p q : ℕ} (m : CrossPopulationGenerationalCalibrationModel p q)
    (t : ℕ) : CalibrationProfile :=
  targetCalibrationProfileAtGeneration m t CalibrationLink.identity

/-- **The closed form the generation-indexed target calibration profile takes**: the
observed mean carried by the prevalence, environmental and genetic shifts, less the
deployment intercept and the transported score mean, with the target slope.

The record was written out in the law below and again in the theorem that bundles that law
with its metric counterpart -- nine lines of it, twice, where a shift added to one copy and
not the other typechecks. -/
noncomputable def targetCalibrationProfileAtGenerationClosedForm
    {p q : ℕ} (m : CrossPopulationGenerationalCalibrationModel p q)
    (t : ℕ) (link : CalibrationLink) : CalibrationProfile :=
  { citl :=
      (m.baseObservedMean +
          (m.prevalenceShiftAt t + m.environmentalObservedShiftAt t +
            m.geneticObservedShiftAt t)) -
        (m.baseDeploymentIntercept + m.deploymentInterceptShiftAt t +
          sourceWeightedTagScore (m.metric.toMetricModelAt t) (m.targetTagMeanAt t))
  , slope := calibrationSlopeFromSourceWeights (m.metric.toMetricModelAt t) Pop.target
  , link := link }

open CrossPopulationMechanisticCalibrationModel in
/-- Exact generation-indexed target calibration-profile law on the explicit
population-genetic state slice. -/
theorem targetCalibrationProfileAtGeneration_exact_mechanistic_popgen_portability_law
    {p q : ℕ} (m : CrossPopulationGenerationalCalibrationModel p q)
    (t : ℕ) (link : CalibrationLink) :
    targetCalibrationProfileAtGeneration m t link =
      targetCalibrationProfileAtGenerationClosedForm m t link := by
  unfold targetCalibrationProfileAtGenerationClosedForm
  unfold targetCalibrationProfileAtGeneration
  rw [targetCalibrationProfile_exact_mechanistic_portability_law]
  simp [
    CrossPopulationGenerationalCalibrationModel.toMechanisticCalibrationModelAt,
    CrossPopulationMechanisticCalibrationModel.observedMean,
    CrossPopulationMechanisticCalibrationModel.observedMeanShift,
    CrossPopulationMechanisticCalibrationModel.deploymentIntercept,
    calibrationSlopeFromSourceWeights]

/-- Exact generation-indexed target CITL law on the explicit population-genetic
state slice. -/
theorem targetIdentityCalibrationProfileAtGeneration_citl_eq_exact_biological_shift_budget
    {p q : ℕ} (m : CrossPopulationGenerationalCalibrationModel p q) (t : ℕ)
    (h_src_cal :
      ((m.toMechanisticCalibrationModelAt t).identityCalibrationProfile Pop.source).citl = 0) :
    (targetIdentityCalibrationProfileAtGeneration m t).citl =
      m.observedMeanShiftAt t - (m.scoreMeanShiftAt t + m.deploymentInterceptShiftAt t) := by
  simpa [targetIdentityCalibrationProfileAtGeneration, targetCalibrationProfileAtGeneration,
    CrossPopulationGenerationalCalibrationModel.toMechanisticCalibrationModelAt,
    CrossPopulationGenerationalCalibrationModel.observedMeanShiftAt,
    CrossPopulationGenerationalCalibrationModel.scoreMeanShiftAt,
    CrossPopulationMechanisticCalibrationModel.identityCalibrationProfile,
    CrossPopulationMechanisticCalibrationModel.identityCalibrationProfile] using
    source_calibrated_target_citl_eq_shift_budget
      (m.toMechanisticCalibrationModelAt t).toShiftModel
      (by simpa only [CrossPopulationMechanisticCalibrationModel.identityCalibrationProfile,
            CrossPopulationMechanisticCalibrationModel.calibrationProfile,
            CrossPopulationCalibrationShiftModel.identityCalibrationProfile] using h_src_cal)

/-- Bundled exact generation-indexed deployment law: the target metric profile
and target calibration profile are both determined by the same time-sliced
SNP/popgen transport state at generation `t`. -/
theorem targetMetricAndCalibrationProfilesAtGeneration_exact_mechanistic_popgen_portability_law
    {p q : ℕ} (m : CrossPopulationGenerationalCalibrationModel p q)
    (t : ℕ) (link : CalibrationLink) :
    targetMetricProfileAtGeneration m.metric t =
      { r2 :=
          (predictiveCovarianceFromSourceWeights (m.metric.toMetricModelAt t) Pop.target) ^ 2 /
            (scoreVarianceFromSourceWeights (m.metric.toMetricModelAt t) Pop.target *
              effectiveOutcomeVariance (m.metric.toMetricModelAt t) Pop.target)
      , auc :=
          equalVarianceGaussianAUCFromSignalVariance
            ((predictiveCovarianceFromSourceWeights (m.metric.toMetricModelAt t) Pop.target) ^ 2 /
              scoreVarianceFromSourceWeights (m.metric.toMetricModelAt t) Pop.target)
            (effectiveOutcomeVariance (m.metric.toMetricModelAt t) Pop.target -
              (predictiveCovarianceFromSourceWeights (m.metric.toMetricModelAt t) Pop.target) ^ 2 /
                scoreVarianceFromSourceWeights (m.metric.toMetricModelAt t) Pop.target)
      , brier :=
          TransportedMetrics.calibratedBrierFromVariances
            (m.metric.targetPrevalenceAt t)
            ((predictiveCovarianceFromSourceWeights (m.metric.toMetricModelAt t) Pop.target) ^ 2 /
              scoreVarianceFromSourceWeights (m.metric.toMetricModelAt t) Pop.target)
            (effectiveOutcomeVariance (m.metric.toMetricModelAt t) Pop.target -
              (predictiveCovarianceFromSourceWeights (m.metric.toMetricModelAt t) Pop.target) ^ 2 /
                scoreVarianceFromSourceWeights (m.metric.toMetricModelAt t) Pop.target) } ∧
    targetCalibrationProfileAtGeneration m t link =
      targetCalibrationProfileAtGenerationClosedForm m t link := by
  constructor
  · exact targetMetricProfileAtGeneration_exact_mechanistic_popgen_portability_law m.metric t
  · exact targetCalibrationProfileAtGeneration_exact_mechanistic_popgen_portability_law m t link

section CrossAncestryProjection

/-! The two projection theorems in this section take the same model, the same calibration
shift model, and the same three assumptions about them -- an `R²` in the unit interval at
each population, a drop between them, and a perfectly calibrated source.  Each restated
that block, eight lines of it, and the restatements are what the duplication guard was
seeing.  The block is a `variable` line here, and `include` makes it a premise of each
theorem exactly as writing it out did; what differs between the two theorems stays written
where it differs. -/

variable {p q : ℕ}
  (metric : CrossPopulationMetricModel p q)
  (cal : CrossPopulationCalibrationShiftModel)
  (h_source_r2_unit : r2FromSourceWeights metric Pop.source ∈ Set.Ico 0 1)
  (h_target_r2_unit : r2FromSourceWeights metric Pop.target ∈ Set.Ico 0 1)
  (h_r2_drop :
    r2FromSourceWeights metric Pop.target < r2FromSourceWeights metric Pop.source)
  (h_src_cal : ((cal.identityCalibrationProfile Pop.source)).citl = 0)

include h_source_r2_unit h_target_r2_unit h_r2_drop h_src_cal in
/-- **An assumed R² drop transports to an AUC drop, and an assumed nonzero shift budget
transports to worsened CITL.**

This is the AUC+CITL projection of the full exact metric theorem above. The
discrimination term is the mechanistic AUC from the explicit SNP-level
transport model, and the calibration term is the full observed-minus-predicted
target shift budget.

The name `cross_ancestry_auc_drops_and_citl_worsens_from_explicit_shift_budget` is absent
on purpose. It asserts that cross-ancestry AUC drops, and this theorem does not show that.
`h_r2_drop` assumes the R² drop and the monotone chart carries it to AUC. `h_src_cal` and
`h_shift_nonzero` assume a perfectly calibrated source and a nonzero budget, against which
any shift is worse. The qualifier `from_explicit_shift_budget` covers the calibration half
alone, so the name must state the R² input too. -/
theorem auc_drop_and_citl_worsening_of_r2_drop_and_shift_budget
    (h_shift_nonzero :
      cal.observedMeanShift - cal.predictedMeanShift ≠ 0) :
    AucDropsAndCitlWorsens cal
      (sourceMetricProfileFromSourceWeightsAtTargetPrevalence metric)
      (targetMetricProfileFromSourceWeights metric) := by
  unfold AucDropsAndCitlWorsens
  have h_auc :
      (targetMetricProfileFromSourceWeights metric).auc <
        (sourceMetricProfileFromSourceWeightsAtTargetPrevalence metric).auc := by
    rw [targetMetricProfileFromSourceWeights_auc,
      sourceMetricProfileFromSourceWeightsAtTargetPrevalence_auc]
    exact targetAUCFromSourceWeights_lt_source_of_r2_drop metric
      h_source_r2_unit h_target_r2_unit h_r2_drop
  obtain ⟨h_citl_eq, h_abs_eq, h_abs_worse⟩ :=
    source_calibrated_target_citl_facts cal h_src_cal h_shift_nonzero
  exact ⟨h_auc, h_citl_eq, h_abs_eq, h_abs_worse⟩

include h_source_r2_unit h_target_r2_unit h_r2_drop h_src_cal in
/-- **Prevalence-only cross-ancestry CITL worsening is just a special case.**
When every non-prevalence calibration shift vanishes, the full explicit shift
budget reduces to prevalence shift alone. This theorem is deliberately scoped
as a benchmark special case rather than a general SNP-level deployment law.

As above, the AUC drop is `h_r2_drop` transported through the monotone chart, not a
consequence of ancestry distance; the name now says so. -/
theorem auc_drop_and_baseRate_only_citl_worsening_of_r2_drop
    (h_env : cal.environmentalObservedShift = 0)
    (h_genetic : cal.geneticObservedShift = 0)
    (h_score : cal.scoreMeanShift = 0)
    (h_intercept : cal.deploymentInterceptShift = 0)
    (h_prev_shift : cal.prevalenceShift ≠ 0) :
    let sourceProfile := (cal.identityCalibrationProfile Pop.source)
    let targetProfile := (cal.identityCalibrationProfile Pop.target)
    let sourceMetrics := sourceMetricProfileFromSourceWeightsAtTargetPrevalence metric
    let targetMetrics := targetMetricProfileFromSourceWeights metric
    targetMetrics.auc < sourceMetrics.auc ∧
    targetProfile.citl = cal.prevalenceShift ∧
    |targetProfile.citl| = |cal.prevalenceShift| ∧
    |sourceProfile.citl| < |targetProfile.citl| := by
  have h_shift_nonzero :
      cal.observedMeanShift - cal.predictedMeanShift ≠ 0 := by
    simp [CrossPopulationCalibrationShiftModel.observedMeanShift,
      CrossPopulationCalibrationShiftModel.predictedMeanShift,
      h_env, h_genetic, h_score, h_intercept, h_prev_shift]
  have h_main :=
    auc_drop_and_citl_worsening_of_r2_drop_and_shift_budget
      metric cal h_source_r2_unit h_target_r2_unit h_r2_drop
      h_src_cal h_shift_nonzero
  unfold AucDropsAndCitlWorsens at h_main
  dsimp at h_main ⊢
  rcases h_main with ⟨h_auc, h_citl, h_abs, h_worse⟩
  refine ⟨h_auc, ?_, ?_, h_worse⟩
  · rw [source_calibrated_target_citl_eq_prevalence_shift_of_no_other_shifts
      cal h_src_cal h_env h_genetic h_score h_intercept]
  · rw [source_calibrated_target_abs_citl_eq_abs_prevalence_shift_of_no_other_shifts
      cal h_src_cal h_env h_genetic h_score h_intercept]

end CrossAncestryProjection

/-- **Neutral-benchmark cross-ancestry AUC drops while observable calibrated
Brier worsens.**
    `AUC` measures discrimination, while `Brier` is the standard proper scoring
    rule carried by the observable drift benchmark. Under positive drift, the
    benchmark target AUC is strictly lower and the benchmark target Brier score
    is strictly higher. This theorem is only about that benchmark slice, not
    the full mechanistic SNP-level deployment model. -/
theorem neutralAF_benchmark_cross_ancestry_auc_drops_and_brier_worsens
    (π V_A V_E fstSource fstTarget : ℝ)
    (hπ0 : 0 < π) (hπ1 : π < 1)
    (hVA : 0 < V_A) (hVE : 0 < V_E)
    (h_fst : fstSource < fstTarget)
    (h_fst_bounds : 0 ≤ fstSource ∧ fstTarget < 1) :
    presentDayEqualVarianceGaussianAUC V_A V_E fstTarget <
      presentDayEqualVarianceGaussianAUC V_A V_E fstSource ∧
    sourceBrierFromR2 π (presentDayR2 V_A V_E fstSource) <
      targetExactCalibratedBrierRisk π V_A V_E fstTarget := by
  constructor
  · exact targetAUC_lt_source_of_neutralAF_benchmark
      V_A V_E fstSource fstTarget hVA hVE h_fst h_fst_bounds
  · exact targetBrier_strict_gt_source_of_neutralAF_benchmark π V_A V_E fstSource fstTarget
      hπ0 hπ1 hVA hVE h_fst h_fst_bounds

end CalibrationVsDiscrimination


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
    calibrationInTheLarge
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
    calibrationProfile, calibrationInTheLarge]

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
  unfold calibrationInTheLarge
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
  unfold calibrationInTheLarge
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


/-!
## Recalibration Methods

Methods to restore calibration when applying PGS across populations.
-/

section RecalibrationMethods

/-- **Intercept recalibration.**
    Fit new intercept a in Y = a + PGS.
    This corrects CITL but not slope miscalibration. -/
noncomputable def interceptRecalibrated (pgs new_intercept : ℝ) : ℝ :=
  new_intercept + pgs

/-- **Intercept recalibration is a shift, pinned.** This definition carries no result of its own.
The new intercept is added to the score without touching its scale, which is what distinguishes
intercept recalibration from a slope refit. -/
theorem interceptRecalibrated_shifts_without_scaling :
    interceptRecalibrated 1 2 = 3 := by
  unfold interceptRecalibrated
  norm_num

/-- Intercept recalibration shifts CITL by exactly the fitted intercept. -/
theorem intercept_recalibration_shifts_citl
    (mean_obs mean_pgs new_intercept : ℝ) :
    calibrationInTheLarge mean_obs
        (interceptRecalibrated mean_pgs new_intercept) =
      calibrationInTheLarge mean_obs mean_pgs - new_intercept := by
  unfold calibrationInTheLarge interceptRecalibrated
  ring

/-- Intercept recalibration corrects CITL when the intercept is the fitted one.
    The fitted intercept is written out rather than assumed of a free variable,
    so nothing is received from the caller. -/
theorem intercept_recal_corrects_citl
    (mean_obs mean_pgs : ℝ) :
    calibrationInTheLarge mean_obs
      (interceptRecalibrated mean_pgs
        (calibrationInTheLarge mean_obs mean_pgs)) = 0 := by
  rw [intercept_recalibration_shifts_citl]
  ring

/-- **Logistic recalibration.**
    Fit Y = a + b × PGS (both intercept and slope).
    This corrects both CITL and slope miscalibration
    but requires labeled target data. -/
noncomputable def logisticRecalibrated (pgs a b : ℝ) : ℝ :=
  a + b * pgs

/-- **Which coefficient multiplies the score, pinned.** This definition carries no result of its
own. The slope multiplies the score and the intercept does not: at score two, intercept one and
slope three the recalibrated value is seven, where the body with the roles exchanged gives
five. -/
theorem logisticRecalibrated_slope_multiplies_score :
    logisticRecalibrated 2 1 3 = 7 := by
  unfold logisticRecalibrated
  norm_num

/-- Exact CITL formula after logistic recalibration. -/
theorem logistic_recalibration_shifts_citl
    (mean_obs mean_pgs a b : ℝ) :
    calibrationInTheLarge mean_obs (logisticRecalibrated mean_pgs a b) =
      calibrationInTheLarge mean_obs mean_pgs - a - (b - 1) * mean_pgs := by
  unfold calibrationInTheLarge logisticRecalibrated
  ring

/-- Choosing the fitted intercept `a = mean_obs - b * mean_pgs` makes the
    recalibrated prediction match the observed mean exactly, so CITL becomes
    zero for any chosen slope `b`. -/
theorem logistic_recalibration_corrects_citl
    (mean_obs mean_pgs b : ℝ) :
    calibrationInTheLarge mean_obs
      (logisticRecalibrated mean_pgs (mean_obs - b * mean_pgs) b) = 0 := by
  rw [logistic_recalibration_shifts_citl]
  unfold calibrationInTheLarge
  ring

/-- Effective calibration slope after logistic recalibration.
    If the target linear predictor uses slope `slope` on the original PGS
    scale, and deployed predictions use fitted slope `fittedSlope`, then the
    target linear predictor as a function of the deployed predictor has slope
    `slope / fittedSlope`. -/
noncomputable def recalibratedCalibrationSlope
    (slope fittedSlope : ℝ) : ℝ :=
  slope / fittedSlope

/-- **The recalibrated slope's orientation, pinned.** This definition carries no result of its
own. Dividing by a fitted slope below one inflates the calibration slope rather than deflating
it, which is the direction that makes refitting correct an under-dispersed score. -/
theorem recalibratedCalibrationSlope_inflates_when_fit_shallow :
    recalibratedCalibrationSlope 3 2 = 3 / 2 := by
  unfold recalibratedCalibrationSlope
  norm_num

/-- **The recalibrated slope at a null fit, named.** A fitted slope of zero means the score
carried no signal in the recalibration sample, so the correction factor diverges and no
recalibration is possible. The divisor is zero and Lean returns `0`, reporting a recalibrated
slope of zero -- which reads downstream as a well-behaved, if useless, score rather than as a
failed fit. Consumers must require `fittedSlope ≠ 0`. -/
theorem recalibratedCalibrationSlope_null_fit_is_junk (slope : ℝ) :
    recalibratedCalibrationSlope slope 0 = 0 := by
  unfold recalibratedCalibrationSlope
  norm_num

/-- Exact affine representation of the target linear predictor in terms of the
    logistic-recalibrated predictor. -/
theorem target_linear_predictor_eq_affine_in_logistic_recalibrated
    (pgs targetIntercept slope fittedIntercept fittedSlope : ℝ)
    (h_fit_nonzero : fittedSlope ≠ 0) :
    targetIntercept + slope * pgs =
      (targetIntercept -
          recalibratedCalibrationSlope slope fittedSlope * fittedIntercept) +
        recalibratedCalibrationSlope slope fittedSlope *
          logisticRecalibrated pgs fittedIntercept fittedSlope := by
  unfold recalibratedCalibrationSlope logisticRecalibrated
  field_simp [h_fit_nonzero]
  ring

/-- If the fitted slope equals the target calibration slope, the recalibrated
    predictor has exact calibration slope `1`. -/
theorem logistic_recalibration_corrects_slope
    (slope : ℝ)
    (h_slope_nonzero : slope ≠ 0) :
    recalibratedCalibrationSlope slope slope = 1 ∧
      calibrationSlopeDeviation
        (recalibratedCalibrationSlope slope slope) = 0 := by
  constructor
  · unfold recalibratedCalibrationSlope
    exact div_self h_slope_nonzero
  · unfold calibrationSlopeDeviation recalibratedCalibrationSlope
    rw [div_self h_slope_nonzero, sub_self, abs_zero]

/-- Shared logistic calibration profile of the fully recalibrated predictor. -/
theorem logistic_refit_profile_corrects_citl_and_slope
    (mean_obs mean_pgs slope : ℝ)
    (h_slope_nonzero : slope ≠ 0) :
    let profile :=
      logisticCalibrationProfile
        mean_obs
        (logisticRecalibrated mean_pgs (mean_obs - slope * mean_pgs) slope)
        (recalibratedCalibrationSlope slope slope)
    profile.citl = 0 ∧ calibrationSlopeDeviation profile.slope = 0 := by
  dsimp
  constructor
  · exact logistic_recalibration_corrects_citl mean_obs mean_pgs slope
  · exact (logistic_recalibration_corrects_slope slope h_slope_nonzero).2

/-- Logistic recalibration with the fitted intercept and fitted slope corrects
    both calibration-in-the-large and slope deviation exactly. -/
theorem logistic_recalibration_corrects_citl_and_slope
    (mean_obs mean_pgs slope : ℝ)
    (h_slope_nonzero : slope ≠ 0) :
    calibrationInTheLarge mean_obs
        (logisticRecalibrated mean_pgs (mean_obs - slope * mean_pgs) slope) = 0 ∧
      calibrationSlopeDeviation
        (recalibratedCalibrationSlope slope slope) = 0 := by
  simpa [calibrationSlopeDeviation] using
    logistic_refit_profile_corrects_citl_and_slope
      mean_obs mean_pgs slope h_slope_nonzero

/-- Logistic recalibration preserves AUC because it is a strictly increasing
    affine transform when the fitted slope is positive. -/
theorem logistic_recalibration_preserves_auc
    {Z : Type*} [MeasurableSpace Z]
    (pop : BinaryPopulation Z) (score : Z → ℝ)
    (a b : ℝ)
    (h_b_pos : 0 < b) :
    populationAUC pop (fun z ↦ logisticRecalibrated (score z) a b) =
      populationAUC pop score := by
  simpa [logisticRecalibrated, Function.comp] using
    (populationAUC_strictMono_invariant pop score (fun x ↦ a + b * x) (by
      intro x y hxy
      linarith [mul_lt_mul_of_pos_left hxy h_b_pos]))

/-- **Trace-MSE lower bound for target recalibration.**
    In an orthogonal Fisher model with `d` target calibration parameters and
    per-event Fisher information `I_event`, the summed estimation variance is
    lower-bounded by `d / (n_events * I_event)`. This is the exact precision
    object that drives target-data requirements; there is no hard-coded
    "200 events per parameter" rule in the theorem. -/
noncomputable def recalibrationTraceMSELowerBound
    (nEvents nParams infoPerEvent : ℝ) : ℝ :=
  nParams / (nEvents * infoPerEvent)

/-- **The recalibration error floor at zero events, named.** With no events the recalibration
parameters are unidentifiable and the mean squared error is bounded below by nothing useful --
the bound diverges. The divisor is zero and Lean returns `0`: a floor of zero, which reads as
PERFECT recalibration being attainable from an empty sample. A lower bound that collapses to zero
exactly where estimation is impossible is the most dangerous direction for this quantity to fail,
since it certifies rather than warns. Consumers must require `nEvents ≠ 0` and
`infoPerEvent ≠ 0`. -/
theorem recalibrationTraceMSELowerBound_no_events_is_junk (nParams infoPerEvent : ℝ) :
    recalibrationTraceMSELowerBound 0 nParams infoPerEvent = 0 := by
  unfold recalibrationTraceMSELowerBound
  simp

/-- **Total information times the bound is the parameter count.** That is what makes it an
events-per-parameter rule rather than a bare ratio. -/
theorem recalibrationTraceMSELowerBound_mul_information
    (nEvents nParams infoPerEvent : ℝ) (h : nEvents * infoPerEvent ≠ 0) :
    recalibrationTraceMSELowerBound nEvents nParams infoPerEvent * (nEvents * infoPerEvent)
      = nParams := by
  unfold recalibrationTraceMSELowerBound
  exact div_mul_cancel₀ _ h

/-! ### Post-hoc recalibration cannot reorder, and refitting can

`logistic_recalibration_corrects_citl_and_slope` shows an affine map in the logit fixes
calibration-in-the-large and the calibration slope, and `logistic_recalibration_preserves_auc`
shows it leaves discrimination untouched. The second is usually read as reassurance. It is also a
limitation, and this section makes the limitation exact.

A post-hoc recalibration is a monotone map applied to a fitted score, and monotone maps preserve
order. So if the true conditional risk ranks two individuals in the opposite order to the fitted
score, NO recalibration recovers it -- not Platt, not isotonic, not any procedure whose only
input is the score. Refitting the index does recover it, and the witness below exhibits both
halves on two individuals.

This is what separates recalibration from joint estimation. Fitting a link and an index together
can move the ranking; fitting the index under a fixed link and repairing the output afterwards
cannot. The gap is not a matter of sample size, and no amount of calibration data closes it.

Empirical status: DERIVED. The witness is exhibited, not measured; the claim is about what
post-hoc maps can express.
-/

/-- Fitted scores of two individuals. -/
noncomputable def reorderScore : Fin 2 -> Real := ![0, 1]

/-- A target conditional risk that ranks the same two individuals the other way. -/
noncomputable def reorderTarget : Fin 2 -> Real := ![4 / 5, 1 / 5]

/-- **No monotone recalibration of the fitted score attains the target.**

The proof is one application of monotonicity: the score puts individual `0` below individual `1`,
so any monotone map puts their recalibrated risks in that order too, while the target does not. -/
theorem posthoc_recalibration_cannot_reorder :
    ¬ ∃ g : Real -> Real, Monotone g ∧ ∀ i, g (reorderScore i) = reorderTarget i := by
  rintro ⟨g, hmono, hg⟩
  have hle : g (reorderScore 0) ≤ g (reorderScore 1) := by
    apply hmono
    norm_num [reorderScore]
  rw [hg 0, hg 1] at hle
  norm_num [reorderTarget] at hle

/-- **Refitting the index does attain it.** Flipping the sign of the linear predictor reverses the
ranking, after which an affine recalibration lands exactly on the target. The pair with the
theorem above is the content: the target is not unreachable, it is unreachable *post hoc*. -/
theorem refit_attains_reordered_target :
    ∃ g : Real -> Real, Monotone g ∧ ∀ i, g (-(reorderScore i)) = reorderTarget i := by
  refine ⟨fun t ↦ 4 / 5 + 3 / 5 * t, ?_, ?_⟩
  · intro u v huv
    simp only
    linarith
  · intro i
    fin_cases i <;> norm_num [reorderScore, reorderTarget]

/-- **Exact event threshold for a target recalibration precision goal.**
    Solving `d / (n_events * I_event) ≤ τ` for `n_events` gives the exact event
    requirement `d / (I_event * τ)`. Specializing to logistic recalibration
    means `d = 2` (intercept and slope), but the theorem is generic in the
    number of calibration parameters. -/
noncomputable def requiredEventsForRecalibration
    (nParams infoPerEvent targetTraceMSE : ℝ) : ℝ :=
  nParams / (infoPerEvent * targetTraceMSE)

/-- **requiredEventsForRecalibration at zero infoPerEvent, named.** With no information per event,
no number of events recalibrates the model. Lean returns `0`, reporting that recalibration needs no
events at all. Consumers must require `infoPerEvent ≠ 0`. -/
theorem requiredEventsForRecalibration_zero_infoperevent_is_junk
    (nParams targetTraceMSE : ℝ) :
    requiredEventsForRecalibration nParams 0 targetTraceMSE = 0 := by
  unfold requiredEventsForRecalibration
  simp

/-- **Sample size needed for recalibration.**
    Under the orthogonal Fisher trace-MSE model, achieving target calibration
    precision `τ` is equivalent to having at least
    `d / (I_event * τ)` target events, where `d` is the number of fitted
    recalibration parameters and `I_event` is the per-event Fisher information.
    This is an exact event-threshold theorem about calibration uncertainty,
    not bookkeeping on a fixed heuristic constant. -/
theorem recalibration_needs_events
    (nEvents nParams infoPerEvent targetTraceMSE : ℝ)
    (h_n : 0 < nEvents)
    (h_info : 0 < infoPerEvent)
    (h_target : 0 < targetTraceMSE) :
    recalibrationTraceMSELowerBound nEvents nParams infoPerEvent ≤ targetTraceMSE ↔
      requiredEventsForRecalibration nParams infoPerEvent targetTraceMSE ≤ nEvents := by
  unfold recalibrationTraceMSELowerBound requiredEventsForRecalibration
  constructor
  · intro h
    rw [div_le_iff₀ (mul_pos h_n h_info)] at h
    rw [div_le_iff₀ (mul_pos h_info h_target)]
    nlinarith
  · intro h
    rw [div_le_iff₀ (mul_pos h_info h_target)] at h
    rw [div_le_iff₀ (mul_pos h_n h_info)]
    nlinarith

/-- **Required event count increases with recalibration dimension.**
    Holding per-event information and the target trace-MSE goal fixed, fitting
    more target-specific calibration parameters strictly increases the event
    count needed to achieve the same uncertainty target. -/
theorem required_events_increase_with_recalibration_dimension
    (nParams₁ nParams₂ infoPerEvent targetTraceMSE : ℝ)
    (h_dim : nParams₁ < nParams₂)
    (h_info : 0 < infoPerEvent)
    (h_target : 0 < targetTraceMSE) :
    requiredEventsForRecalibration nParams₁ infoPerEvent targetTraceMSE <
      requiredEventsForRecalibration nParams₂ infoPerEvent targetTraceMSE := by
  unfold requiredEventsForRecalibration
  exact div_lt_div_of_pos_right h_dim (mul_pos h_info h_target)

/-- **Required event count decreases with per-event information.**
    More informative target events, whether from sharper score spread or richer
    recalibration covariates, strictly reduce the event count needed to hit a
    fixed trace-MSE target. -/
theorem required_events_decrease_with_event_information
    (nParams info₁ info₂ targetTraceMSE : ℝ)
    (h_params : 0 < nParams)
    (h_info₁ : 0 < info₁)
    (h_info : info₁ < info₂)
    (h_target : 0 < targetTraceMSE) :
    requiredEventsForRecalibration nParams info₂ targetTraceMSE <
      requiredEventsForRecalibration nParams info₁ targetTraceMSE := by
  unfold requiredEventsForRecalibration
  have hden₁ : 0 < info₁ * targetTraceMSE := mul_pos h_info₁ h_target
  exact div_lt_div_of_pos_left h_params hden₁ (by nlinarith)

/-- **Rarer target prevalence requires more labeled target samples for the same
    recalibration precision.**
    If only a fraction `π` of target individuals are events, then the total
    target cohort size needed to reach a given recalibration trace-MSE target is
    the required event count divided by `π`. Therefore rarer diseases require
    larger target cohorts even when the per-event information and calibration
    precision target are fixed. -/
noncomputable def requiredTargetCohortSizeForRecalibration
    (nParams prevalence infoPerEvent targetTraceMSE : ℝ) : ℝ :=
  requiredEventsForRecalibration nParams infoPerEvent targetTraceMSE / prevalence

/-- **requiredTargetCohortSizeForRecalibration at zero prevalence, named.** At zero prevalence no
cohort of any size yields events, so the required size diverges. Lean returns `0`: recalibration
is free in a population where the outcome never occurs. Consumers must require `prevalence ≠ 0`.
-/
theorem requiredTargetCohortSizeForRecalibration_zero_prevalence_is_junk
    (nParams infoPerEvent targetTraceMSE : ℝ) :
    requiredTargetCohortSizeForRecalibration nParams 0 infoPerEvent targetTraceMSE = 0 := by
  unfold requiredTargetCohortSizeForRecalibration
  simp

/-- **Exact labeled-cohort threshold for target recalibration.**
    If a fraction `π` of target individuals are events, then `n = n_events / π`
    labeled target samples are needed. Therefore hitting a target trace-MSE
    level is equivalent to having at least
    `requiredTargetCohortSizeForRecalibration d π I_event τ` labeled target
    individuals. This connects calibration precision directly to the clinically
    relevant target-cohort size rather than only to the abstract event count. -/
theorem recalibration_needs_target_cohort
    (nTarget nParams prevalence infoPerEvent targetTraceMSE : ℝ)
    (h_target_n : 0 < nTarget)
    (h_prev : 0 < prevalence)
    (h_info : 0 < infoPerEvent)
    (h_target : 0 < targetTraceMSE) :
    recalibrationTraceMSELowerBound (prevalence * nTarget) nParams infoPerEvent ≤ targetTraceMSE ↔
      requiredTargetCohortSizeForRecalibration nParams prevalence infoPerEvent targetTraceMSE
        ≤ nTarget := by
  have h_events : 0 < prevalence * nTarget := mul_pos h_prev h_target_n
  rw [recalibration_needs_events (prevalence * nTarget) nParams infoPerEvent targetTraceMSE
    h_events h_info h_target]
  unfold requiredTargetCohortSizeForRecalibration
  rw [div_le_iff₀ h_prev]
  ring_nf

/-- At fixed parameter count, per-event information, and target precision,
    lower event prevalence strictly increases the total target cohort size
    needed for recalibration. -/
theorem rarer_target_prevalence_requires_larger_recalibration_cohort
    (nParams π₁ π₂ infoPerEvent targetTraceMSE : ℝ)
    (h_params : 0 < nParams)
    (hπ₁ : 0 < π₁)
    (hπ : π₁ < π₂)
    (h_info : 0 < infoPerEvent)
    (h_target : 0 < targetTraceMSE) :
    requiredTargetCohortSizeForRecalibration nParams π₂ infoPerEvent targetTraceMSE <
      requiredTargetCohortSizeForRecalibration nParams π₁ infoPerEvent targetTraceMSE := by
  have h_required_pos : 0 < requiredEventsForRecalibration nParams infoPerEvent targetTraceMSE := by
    unfold requiredEventsForRecalibration
    exact div_pos h_params (mul_pos h_info h_target)
  have hπ₂ : 0 < π₂ := lt_trans hπ₁ hπ
  unfold requiredTargetCohortSizeForRecalibration
  field_simp [ne_of_gt h_required_pos, ne_of_gt hπ₁, ne_of_gt hπ₂]
  nlinarith

/-- **Recalibration does not change AUC.**
    Recalibration applies a strictly increasing affine transform
    `s ↦ a + b × s` with `b > 0`. Such transforms preserve pairwise score
    orderings, so population AUC is unchanged. -/
theorem recalibration_preserves_auc
    {Z : Type*} [MeasurableSpace Z]
    (pop : BinaryPopulation Z) (score : Z → ℝ)
    (a b : ℝ)
    (h_b_pos : 0 < b) :
    populationAUC pop (fun z ↦ a + b * score z) = populationAUC pop score := by
  simpa [Function.comp] using
    populationAUC_strictMono_invariant pop score (fun x ↦ a + b * x) (by
      intro x y hxy
      linarith [mul_lt_mul_of_pos_left hxy h_b_pos])

end RecalibrationMethods


/-!
## Decision-Theoretic Implications

Miscalibration has direct consequences for clinical decisions
based on PGS thresholds.
-/

section DecisionImplications

/-- A risk score is classified as high risk when it exceeds the decision
    threshold. -/
def classifiedHighRisk (threshold predictedRisk : ℝ) : Prop :=
  threshold < predictedRisk

/-- **Miscalibration changes clinical decisions.**
    If the PGS is miscalibrated with CITL shift c > 0 (over-prediction),
    a patient with true risk r < threshold gets predicted risk r + c.
    When c > threshold - r, the patient is incorrectly classified
    as high risk: predicted_risk = r + c > threshold > r = true_risk. -/
theorem miscalibration_changes_decisions
    (true_risk threshold c : ℝ)
    (h_truly_low : true_risk < threshold)
    (h_miscal : threshold - true_risk < c) :
    ¬ classifiedHighRisk threshold true_risk ∧
      classifiedHighRisk threshold (true_risk + c) := by
  unfold classifiedHighRisk
  constructor
  · linarith
  · linarith

/-- **Net reclassification improvement (NRI) from recalibration.**
    NRI measures the proportion of patients correctly reclassified.
    NRI = (net up-classification among events) + (net down-classification among non-events). -/
noncomputable def nri
    (up_events down_events up_nonevents down_nonevents n_events n_nonevents : ℝ) : ℝ :=
  (up_events - down_events) / n_events + (down_nonevents - up_nonevents) / n_nonevents

/-- With no events the first reclassification term divides by zero and Mathlib returns `0`, so
the index reports the non-event half alone rather than being undefined. -/
theorem nri_at_zero_events_is_junk
    (up_events down_events up_nonevents down_nonevents n_nonevents : ℝ) :
    nri up_events down_events up_nonevents down_nonevents 0 n_nonevents
      = (down_nonevents - up_nonevents) / n_nonevents := by
  simp [nri]

/-- And symmetrically with no non-events. -/
theorem nri_at_zero_nonevents_is_junk
    (up_events down_events up_nonevents down_nonevents n_events : ℝ) :
    nri up_events down_events up_nonevents down_nonevents n_events 0
      = (up_events - down_events) / n_events := by
  simp [nri]


/-- **Reclassifying nobody scores zero, whatever the denominators are.** The index is a sum of
two net rates and each vanishes when its own movements cancel; a body carrying an additive term
in the counts would report improvement for a model that moved no one. -/
theorem nri_no_movement (up_events up_nonevents n_events n_nonevents : ℝ) :
    nri up_events up_events up_nonevents up_nonevents n_events n_nonevents = 0 := by
  unfold nri
  ring

/-- **Downward reclassification at a clinical decision threshold.**
    A downward intercept correction of size `δ > 0` moves an individual from
    high risk to low risk exactly when the baseline score lies in the threshold
    band `(threshold, threshold + δ]`. -/
theorem down_reclassified_after_downward_shift_iff_mem_band
    (threshold score δ : ℝ) :
    classifiedHighRisk threshold score ∧
      ¬ classifiedHighRisk threshold (score - δ) ↔
      score ∈ Set.Ioc threshold (threshold + δ) := by
  unfold classifiedHighRisk
  constructor
  · intro h
    rcases h with ⟨h_high, h_not_high_after⟩
    constructor
    · exact h_high
    · have h_after_le : score - δ ≤ threshold := not_lt.mp h_not_high_after
      linarith
  · intro h
    rcases h with ⟨h_high, h_band_upper⟩
    constructor
    · exact h_high
    · have h_after_le : score - δ ≤ threshold := by
        linarith
      exact not_lt.mpr h_after_le

/-- **Threshold-band reclassification rate.**
    Under a downward intercept correction by `δ > 0`, this is the fraction of
    a class-specific score law lying in the band `(threshold, threshold + δ]`.
    It is under this model the reclassification rate for that class.

    Empirical status: UNTESTED. -/
noncomputable def thresholdBandRate
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (threshold δ : ℝ) : ℝ :=
  (μ (Set.Ioc threshold (threshold + δ))).toReal

/-- **Downward reclassification rate under intercept recalibration.**
    This is the probability that a score is above threshold before
    recalibration but at or below threshold after subtracting `δ`. -/
noncomputable def downReclassificationRate
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (threshold δ : ℝ) : ℝ :=
  (μ {score | classifiedHighRisk threshold score ∧
      ¬ classifiedHighRisk threshold (score - δ)}).toReal

/-- Downward reclassification is exactly threshold-band mass. -/
theorem downReclassificationRate_eq_thresholdBandRate
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (threshold δ : ℝ) :
    downReclassificationRate μ threshold δ = thresholdBandRate μ threshold δ := by
  unfold downReclassificationRate thresholdBandRate
  have hset :
      {score | classifiedHighRisk threshold score ∧
          ¬ classifiedHighRisk threshold (score - δ)} =
        Set.Ioc threshold (threshold + δ) := by
    ext score
    exact down_reclassified_after_downward_shift_iff_mem_band threshold score δ
  rw [hset]

/-- **NRI induced by a downward intercept recalibration.**
    For an over-predicting model corrected by subtracting `δ > 0` from every
    score, only downward reclassifications can occur. Event NRI is therefore
    the sensitivity loss, while non-event NRI is the specificity gain. -/
noncomputable def nriFromDownwardInterceptRecalibration
    (μevent μnonevent : Measure ℝ)
    [IsProbabilityMeasure μevent] [IsProbabilityMeasure μnonevent]
    (threshold δ : ℝ) : ℝ :=
  nri
    0 (downReclassificationRate μevent threshold δ)
    0 (downReclassificationRate μnonevent threshold δ)
    1 1

/-- Exact NRI formula for a downward intercept correction. -/
theorem nriFromDownwardInterceptRecalibration_eq_band_difference
    (μevent μnonevent : Measure ℝ)
    [IsProbabilityMeasure μevent] [IsProbabilityMeasure μnonevent]
    (threshold δ : ℝ) :
    nriFromDownwardInterceptRecalibration μevent μnonevent threshold δ =
      thresholdBandRate μnonevent threshold δ -
        thresholdBandRate μevent threshold δ := by
  unfold nriFromDownwardInterceptRecalibration nri
  rw [downReclassificationRate_eq_thresholdBandRate μevent threshold δ]
  rw [downReclassificationRate_eq_thresholdBandRate μnonevent threshold δ]
  ring

/-- **Positive NRI means recalibration improves threshold classification.**
    For a downward intercept recalibration, positive NRI is equivalent to the
    moved threshold band `(threshold, threshold + δ]` containing a larger
    fraction of non-events than of events. Equivalently, the specificity gain
    exceeds the sensitivity loss. -/
theorem positive_nri_means_improvement
    (μevent μnonevent : Measure ℝ)
    [IsProbabilityMeasure μevent] [IsProbabilityMeasure μnonevent]
    (threshold δ : ℝ) :
    0 < nriFromDownwardInterceptRecalibration μevent μnonevent threshold δ ↔
      thresholdBandRate μevent threshold δ <
        thresholdBandRate μnonevent threshold δ := by
  rw [nriFromDownwardInterceptRecalibration_eq_band_difference
    μevent μnonevent threshold δ]
  constructor <;> intro h <;> linarith

/-- **Outcome prevalence among reclassified patients.**
    Let `π` be the cohort event prevalence. Among the patients moved across the
    decision threshold by a downward intercept recalibration, this is the event
    rate in the moved threshold band `(threshold, threshold + δ]`.

    Empirical status: **VALIDATED**
    (`validation/empirical/simcov/battery_pgscal01.py`). Four million
    patients per cell, event scores `N(μ_e, 1)` and non-event scores `N(0, 1)`;
    the oracle is the COUNTED event fraction among the patients whose score
    falls in the band. The band masses and `π` are model quantities — exact
    normal band masses and the nominal prevalence — and are never estimated from
    the cohort the oracle counts, which would turn this body into a
    rearrangement of those counts and put nothing on trial.

      design                    this body   counted in band      sems
      π=0.10 band (0.5, 1.0]     0.12429     0.12425±0.00042     0.10
      π=0.30 band (1.0, 1.7]     0.49220     0.49276±0.00063     0.88
      π=0.05 band (0.0, 0.4]     0.02279     0.02266±0.00019     0.68
      π=0.20 band (-0.5, 0.1]    0.13563     0.13583±0.00037     0.54

    The identity gate: the prior-free `f_e / (f_e + f_n)` — the same ratio with
    the cohort prevalence dropped, which is the ordinary base-rate mistake — is
    rejected at up to 1486 sems and a factor of thirteen. The positive control,
    the simulated cohort reproducing its own nominal event rate, passes at 0.26
    sems. -/
noncomputable def reclassifiedBandEventPrevalence
    (π : ℝ)
    (μevent μnonevent : Measure ℝ)
    [IsProbabilityMeasure μevent] [IsProbabilityMeasure μnonevent]
    (threshold δ : ℝ) : ℝ :=
  (π * thresholdBandRate μevent threshold δ) /
    (π * thresholdBandRate μevent threshold δ +
      (1 - π) * thresholdBandRate μnonevent threshold δ)

/-- An empty reclassification band divides by zero and Mathlib returns `0`, so the posterior
event prevalence in the band reads as certainly-no-event rather than undefined. -/
theorem reclassifiedBandEventPrevalence_at_empty_band_is_junk
    (π : ℝ) (μevent μnonevent : Measure ℝ)
    [IsProbabilityMeasure μevent] [IsProbabilityMeasure μnonevent]
    (threshold δ : ℝ)
    (hzero : π * thresholdBandRate μevent threshold δ +
      (1 - π) * thresholdBandRate μnonevent threshold δ = 0) :
    reclassifiedBandEventPrevalence π μevent μnonevent threshold δ = 0 := by
  unfold reclassifiedBandEventPrevalence
  rw [hzero, div_zero]


/-- **Positive NRI means the reclassified band is lower risk than the cohort.**
    For a downward intercept recalibration, positive NRI is equivalent to the
    patients moved from high risk to low risk having event prevalence below the
    overall cohort prevalence `π`. This is the clinically useful interpretation:
    threshold reclassification helps exactly when the patients being moved below
    threshold are genuinely lower risk than the cohort average. -/
theorem positive_nri_iff_reclassifiedBandEventPrevalence_below_cohort_prevalence
    (π : ℝ)
    (μevent μnonevent : Measure ℝ)
    [IsProbabilityMeasure μevent] [IsProbabilityMeasure μnonevent]
    (threshold δ : ℝ)
    (h_pi : 0 < π)
    (h_pi_lt : π < 1)
    (h_band :
      0 < π * thresholdBandRate μevent threshold δ +
          (1 - π) * thresholdBandRate μnonevent threshold δ) :
    0 < nriFromDownwardInterceptRecalibration μevent μnonevent threshold δ ↔
      reclassifiedBandEventPrevalence π μevent μnonevent threshold δ < π := by
  rw [positive_nri_means_improvement μevent μnonevent threshold δ]
  unfold reclassifiedBandEventPrevalence
  constructor
  · intro h
    have h_scale_pos : 0 < π * (1 - π) := by
      nlinarith
    have h_scaled :
        π * (1 - π) * thresholdBandRate μevent threshold δ <
          π * (1 - π) * thresholdBandRate μnonevent threshold δ :=
      mul_lt_mul_of_pos_left h h_scale_pos
    rw [div_lt_iff₀ h_band]
    nlinarith [h_scaled]
  · intro h
    have h_cross :
        π * thresholdBandRate μevent threshold δ <
          π *
            (π * thresholdBandRate μevent threshold δ +
              (1 - π) * thresholdBandRate μnonevent threshold δ) :=
      (div_lt_iff₀ h_band).1 h
    have h_scale_pos : 0 < π * (1 - π) := by
      nlinarith
    have h_scaled :
        π * (1 - π) * thresholdBandRate μevent threshold δ <
          π * (1 - π) * thresholdBandRate μnonevent threshold δ := by
      nlinarith [h_cross]
    have h_scaled' :
        (π * (1 - π)) * thresholdBandRate μevent threshold δ <
          (π * (1 - π)) * thresholdBandRate μnonevent threshold δ := by
      simpa [mul_assoc] using h_scaled
    nlinarith [h_scaled', h_scale_pos]

/-- **Finite-horizon longitudinal treatment model.**
    `discount t` encodes the time value of health at follow-up time `t`. -/
structure LongitudinalTreatmentModel (T : ℕ) where
  discount : Fin T → ℝ
  discount_nonneg : ∀ t, 0 ≤ discount t

/-- **Individual clinical pathway over a finite horizon.**
    `followupWeight` can encode uncensoring, freedom from competing events,
    adherence, or clinical eligibility at each follow-up time. Treatment
    benefit and harm are allowed to vary across time. -/
structure ClinicalPathway (T : ℕ) where
  followupWeight : Fin T → ℝ
  eventProb : Fin T → ℝ
  treatmentBenefit : Fin T → ℝ
  treatmentHarm : Fin T → ℝ
  followupWeight_nonneg : ∀ t, 0 ≤ followupWeight t

/-- **Per-time discounted QALY contribution under treatment.**
    This is the exact contribution of a treated patient at time `t` under the
    clinical pathway model. -/
noncomputable def qalyContributionAtTime {T : ℕ}
    (model : LongitudinalTreatmentModel T) (path : ClinicalPathway T) (t : Fin T) : ℝ :=
  model.discount t * path.followupWeight t *
    (path.eventProb t * path.treatmentBenefit t - path.treatmentHarm t)

/-- Reference evaluation: a fully discounted-away epoch contributes nothing. -/
theorem qalyContributionAtTime_at_zero_discount {T : ℕ}
    (model : LongitudinalTreatmentModel T) (path : ClinicalPathway T) (t : Fin T)
    (hzero : model.discount t = 0) :
    qalyContributionAtTime model path t = 0 := by
  unfold qalyContributionAtTime
  rw [hzero]
  ring


/-- **Net treatment margin of a clinical pathway.**
    Positive margin means treatment is beneficial in expectation after exact
    aggregation over discounted follow-up, treatment heterogeneity, and
    censoring/eligibility weights. -/
noncomputable def treatmentMargin {T : ℕ}
    (model : LongitudinalTreatmentModel T) (path : ClinicalPathway T) : ℝ :=
  Finset.univ.sum (fun t ↦ qalyContributionAtTime model path t)

/-- A deployed rule treats when the predicted pathway has positive net QALY
    margin. -/
def receivesTreatment {T : ℕ}
    (model : LongitudinalTreatmentModel T) (path : ClinicalPathway T) : Prop :=
  0 < treatmentMargin model path

/-- **QALY gain under a predicted-pathway treatment decision.**
    The deployed decision treats iff the predicted pathway implies positive
    net benefit; realized utility is then evaluated under the true pathway. -/
noncomputable def qalyGainUnderDecision {T : ℕ}
    (model : LongitudinalTreatmentModel T)
    (truePath predictedPath : ClinicalPathway T) : ℝ := by
    classical
    exact if receivesTreatment model predictedPath then
      treatmentMargin model truePath
    else
      0

/-- **Per-individual QALY loss from using a predicted instead of true pathway.**
    This is exact oracle regret relative to the decision that would be made
    from the patient's true longitudinal pathway. -/
noncomputable def qalyLoss {T : ℕ}
    (model : LongitudinalTreatmentModel T)
    (truePath predictedPath : ClinicalPathway T) : ℝ :=
  qalyGainUnderDecision model truePath truePath -
    qalyGainUnderDecision model truePath predictedPath

/-- **Decision-regret margin for longitudinal clinical utility.**
    False positives pay the negative part of the true treatment margin, false
    negatives pay the positive part, and correct decisions pay zero. -/
noncomputable def qalyDecisionRegretMargin {T : ℕ}
    (model : LongitudinalTreatmentModel T)
    (truePath predictedPath : ClinicalPathway T) : ℝ := by
    classical
    exact if receivesTreatment model predictedPath then
        max (-treatmentMargin model truePath) 0
      else
        max (treatmentMargin model truePath) 0

/-- Oracle self-decision recovers the positive part of the true treatment
    margin. -/
theorem qalyGainUnderDecision_self_eq_max_treatmentMargin
    {T : ℕ} (model : LongitudinalTreatmentModel T) (path : ClinicalPathway T) :
    qalyGainUnderDecision model path path = max (treatmentMargin model path) 0 := by
  unfold qalyGainUnderDecision receivesTreatment
  by_cases h : 0 < treatmentMargin model path
  · rw [if_pos h, max_eq_left (le_of_lt h)]
  · rw [if_neg h, max_eq_right (not_lt.mp h)]

/-- **QALY loss equals the exact longitudinal decision-regret margin.** -/
theorem qalyLoss_eq_qalyDecisionRegretMargin
    {T : ℕ} (model : LongitudinalTreatmentModel T)
    (truePath predictedPath : ClinicalPathway T) :
    qalyLoss model truePath predictedPath =
      qalyDecisionRegretMargin model truePath predictedPath := by
  by_cases h_pred : receivesTreatment model predictedPath
  · by_cases h_true : receivesTreatment model truePath
    · have h_true_pos : 0 < treatmentMargin model truePath := h_true
      have h_max : max (-treatmentMargin model truePath) 0 = 0 :=
        max_eq_right (by linarith)
      unfold qalyLoss qalyGainUnderDecision qalyDecisionRegretMargin
      rw [if_pos h_true, if_pos h_pred, if_pos h_pred, h_max]
      ring
    · have h_true_nonpos : treatmentMargin model truePath ≤ 0 := not_lt.mp h_true
      have h_max :
          max (-treatmentMargin model truePath) 0 =
            -treatmentMargin model truePath :=
        max_eq_left (by linarith)
      unfold qalyLoss qalyGainUnderDecision qalyDecisionRegretMargin
      rw [if_neg h_true, if_pos h_pred, if_pos h_pred, h_max]
      ring
  · by_cases h_true : receivesTreatment model truePath
    · have h_max :
          max (treatmentMargin model truePath) 0 =
            treatmentMargin model truePath :=
        max_eq_left (le_of_lt h_true)
      unfold qalyLoss qalyGainUnderDecision qalyDecisionRegretMargin
      rw [if_pos h_true, if_neg h_pred, if_neg h_pred, h_max]
      ring
    · have h_true_nonpos : treatmentMargin model truePath ≤ 0 := not_lt.mp h_true
      have h_max : max (treatmentMargin model truePath) 0 = 0 :=
        max_eq_right h_true_nonpos
      unfold qalyLoss qalyGainUnderDecision qalyDecisionRegretMargin
      rw [if_neg h_true, if_neg h_pred, if_neg h_pred, h_max]
      ring

/-- QALY loss is always nonnegative under the longitudinal regret model. -/
theorem qalyLoss_nonneg
    {T : ℕ} (model : LongitudinalTreatmentModel T)
    (truePath predictedPath : ClinicalPathway T) :
    0 ≤ qalyLoss model truePath predictedPath := by
  rw [qalyLoss_eq_qalyDecisionRegretMargin]
  unfold qalyDecisionRegretMargin
  by_cases h_pred : receivesTreatment model predictedPath
  · rw [if_pos h_pred]
    exact le_max_right _ _
  · rw [if_neg h_pred]
    exact le_max_right _ _

/-- **Perfect pathway calibration implies zero QALY loss.**
    If the predicted pathway induces the same net treatment margin as the true
    pathway, then the deployed treatment decision matches the oracle decision. -/
theorem qalyLoss_eq_zero_of_perfect_pathway_calibration
    {T : ℕ} (model : LongitudinalTreatmentModel T)
    (truePath predictedPath : ClinicalPathway T)
    (h_cal :
      treatmentMargin model predictedPath =
        treatmentMargin model truePath) :
    qalyLoss model truePath predictedPath = 0 := by
  unfold qalyLoss qalyGainUnderDecision receivesTreatment
  simp [h_cal]

/-- If the deployed and oracle pathway margins induce the same treatment
    decision, the exact QALY regret is zero. -/
theorem qalyLoss_eq_zero_of_same_decision
    {T : ℕ} (model : LongitudinalTreatmentModel T)
    (truePath predictedPath : ClinicalPathway T)
    (h_decision :
      receivesTreatment model predictedPath ↔
        receivesTreatment model truePath) :
    qalyLoss model truePath predictedPath = 0 := by
  unfold qalyLoss qalyGainUnderDecision
  by_cases h_true : receivesTreatment model truePath
  · have h_pred : receivesTreatment model predictedPath := h_decision.mpr h_true
    rw [if_pos h_true, if_pos h_pred]
    ring
  · have h_pred : ¬ receivesTreatment model predictedPath := by
      intro h_pred
      exact h_true (h_decision.mp h_pred)
    rw [if_neg h_true, if_neg h_pred]
    ring

/-- **A margin error smaller than the true decision margin preserves the
    treatment decision.**
    This is the exact finite-horizon decision-stability criterion under the
    longitudinal pathway model. -/
theorem receivesTreatment_iff_of_margin_error_lt_abs_true_margin
    {T : ℕ} (model : LongitudinalTreatmentModel T)
    (truePath predictedPath : ClinicalPathway T)
    (h_margin :
      |treatmentMargin model predictedPath - treatmentMargin model truePath| <
        |treatmentMargin model truePath|) :
    receivesTreatment model predictedPath ↔
      receivesTreatment model truePath := by
  unfold receivesTreatment
  set mTrue : ℝ := treatmentMargin model truePath
  set mPred : ℝ := treatmentMargin model predictedPath
  by_cases h_true : 0 < mTrue
  · have h_pred : 0 < mPred := by
      by_cases h_pred_nonpos : mPred ≤ 0
      · have h_abs_eq : |mPred - mTrue| = -(mPred - mTrue) :=
          abs_of_nonpos (by linarith)
        have h_true_abs : |mTrue| = mTrue := abs_of_pos h_true
        rw [h_abs_eq, h_true_abs] at h_margin
        linarith
      · linarith
    constructor
    · intro _
      exact h_true
    · intro _
      exact h_pred
  · have h_true_nonpos : mTrue ≤ 0 := not_lt.mp h_true
    have h_pred_nonpos : mPred ≤ 0 := by
      by_cases h_pred : 0 < mPred
      · have h_abs_eq : |mPred - mTrue| = mPred - mTrue := by
          apply abs_of_nonneg
          linarith
        have h_true_abs : |mTrue| = -mTrue := abs_of_nonpos h_true_nonpos
        rw [h_abs_eq, h_true_abs] at h_margin
        linarith
      · exact not_lt.mp h_pred
    constructor
    · intro h_pred
      exact False.elim ((not_lt_of_ge h_pred_nonpos) h_pred)
    · intro h_true'
      exact False.elim ((not_lt_of_ge h_true_nonpos) h_true')

/-- **Exact pathway-margin stability implies zero QALY regret.**
    If the deployed pathway margin error is smaller than the absolute true
    treatment margin, the deployed and oracle treatment decisions coincide. -/
theorem qalyLoss_eq_zero_of_margin_error_lt_abs_true_margin
    {T : ℕ} (model : LongitudinalTreatmentModel T)
    (truePath predictedPath : ClinicalPathway T)
    (h_margin :
      |treatmentMargin model predictedPath - treatmentMargin model truePath| <
        |treatmentMargin model truePath|) :
    qalyLoss model truePath predictedPath = 0 := by
  apply qalyLoss_eq_zero_of_same_decision
  exact receivesTreatment_iff_of_margin_error_lt_abs_true_margin
    model truePath predictedPath h_margin

/-- **Exact longitudinal QALY regret is bounded by pathway-margin error.**
    This converts miscalibration of the finite-horizon treatment margin into an
    exact utility-loss bound with no surrogate risk approximation. -/
theorem qalyLoss_le_abs_margin_error
    {T : ℕ} (model : LongitudinalTreatmentModel T)
    (truePath predictedPath : ClinicalPathway T) :
    qalyLoss model truePath predictedPath ≤
      |treatmentMargin model predictedPath - treatmentMargin model truePath| := by
  rw [qalyLoss_eq_qalyDecisionRegretMargin]
  set mTrue : ℝ := treatmentMargin model truePath
  set mPred : ℝ := treatmentMargin model predictedPath
  unfold qalyDecisionRegretMargin receivesTreatment
  change (if 0 < mPred then max (-mTrue) 0 else max mTrue 0) ≤ |mPred - mTrue|
  by_cases h_pred : 0 < mPred
  · rw [if_pos h_pred]
    by_cases h_true : 0 < mTrue
    · have h_max : max (-mTrue) 0 = 0 :=
        max_eq_right (by linarith)
      rw [h_max]
      exact abs_nonneg (mPred - mTrue)
    · have h_true_nonpos : mTrue ≤ 0 := not_lt.mp h_true
      have h_max : max (-mTrue) 0 = -mTrue :=
        max_eq_left (by linarith)
      have h_abs_eq : |mPred - mTrue| = mPred - mTrue :=
        abs_of_nonneg (by linarith)
      rw [h_max, h_abs_eq]
      linarith
  · rw [if_neg h_pred]
    have h_pred_nonpos : mPred ≤ 0 := not_lt.mp h_pred
    by_cases h_true : 0 < mTrue
    · have h_max : max mTrue 0 = mTrue :=
        max_eq_left (le_of_lt h_true)
      have h_abs_eq : |mPred - mTrue| = -(mPred - mTrue) :=
        abs_of_nonpos (by linarith)
      rw [h_max, h_abs_eq]
      linarith
    · have h_true_nonpos : mTrue ≤ 0 := not_lt.mp h_true
      have h_max : max mTrue 0 = 0 :=
        max_eq_right h_true_nonpos
      rw [h_max]
      exact abs_nonneg (mPred - mTrue)

/-- **The error the deployed pathway makes in net benefit at one time**: mis-stated event
risk against the true benefit, plus the deployed risk against the benefit error, less the
harm error.

This expression was written out in full at every place the treatment-margin argument
touched it -- in the decomposition, in three `calc` steps, and in four `have` statements.
Named, the argument reads as what it is: a bound on a weight error times a net benefit plus
a weight times THIS. -/
noncomputable def pathwayNetBenefitError {T : ℕ}
    (truePath predictedPath : ClinicalPathway T) (t : Fin T) : ℝ :=
  (predictedPath.eventProb t - truePath.eventProb t) * truePath.treatmentBenefit t +
    predictedPath.eventProb t *
      (predictedPath.treatmentBenefit t - truePath.treatmentBenefit t) -
    (predictedPath.treatmentHarm t - truePath.treatmentHarm t)

/-- Vanishing identity: a predicted pathway that matches the truth has no net-benefit error. -/
theorem pathwayNetBenefitError_self_eq_zero {T : ℕ}
    (truePath : ClinicalPathway T) (t : Fin T) :
    pathwayNetBenefitError truePath truePath t = 0 := by
  unfold pathwayNetBenefitError
  ring


/-- **The per-time treatment-margin error**: the follow-up weight error against the true net
benefit, plus the deployed weight against the net-benefit error, discounted. -/
noncomputable def treatmentMarginErrorTerm {T : ℕ} (model : LongitudinalTreatmentModel T)
    (truePath predictedPath : ClinicalPathway T) (t : Fin T) : ℝ :=
  model.discount t *
    ((predictedPath.followupWeight t - truePath.followupWeight t) *
        (truePath.eventProb t * truePath.treatmentBenefit t - truePath.treatmentHarm t) +
      predictedPath.followupWeight t * pathwayNetBenefitError truePath predictedPath t)

/-- Vanishing identity: matching pathways leave no margin error term. -/
theorem treatmentMarginErrorTerm_self_eq_zero {T : ℕ}
    (model : LongitudinalTreatmentModel T) (truePath : ClinicalPathway T) (t : Fin T) :
    treatmentMarginErrorTerm model truePath truePath t = 0 := by
  unfold treatmentMarginErrorTerm
  rw [pathwayNetBenefitError_self_eq_zero]
  ring


/-- **Exact componentwise decomposition of longitudinal treatment-margin error.**
    This separates the effect of miscalibrating censoring/follow-up weights,
    event risk, heterogeneous treatment benefit, and treatment harm. -/
theorem treatmentMargin_error_eq_componentwise_sum
    {T : ℕ} (model : LongitudinalTreatmentModel T)
    (truePath predictedPath : ClinicalPathway T) :
    treatmentMargin model predictedPath - treatmentMargin model truePath =
      ∑ t, treatmentMarginErrorTerm model truePath predictedPath t := by
  unfold treatmentMargin qalyContributionAtTime treatmentMarginErrorTerm
    pathwayNetBenefitError
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl ?_
  intro t _
  ring

/-- **Two products and a subtraction, bounded factor by factor.**

The per-time treatment-margin error is `xy + zw - v`, and bounding it took an eight-line
`calc` -- rewrite as `(xy + zw) + (-v)`, apply the triangle inequality twice, then
`abs_mul` -- written out wherever the shape occurred.  Nothing in that argument is about
pathways, so none of it needs the pathway names it was written in. -/
theorem abs_two_products_sub_le (x y z w v : ℝ) :
    |x * y + z * w - v| ≤ |x| * |y| + |z| * |w| + |v| := by
  calc |x * y + z * w - v|
      ≤ |x * y + z * w| + |v| := by
        simpa [sub_eq_add_neg, abs_neg] using abs_add_le (x * y + z * w) (-v)
    _ ≤ |x * y| + |z * w| + |v| := by
        have := abs_add_le (x * y) (z * w)
        linarith
    _ = |x| * |y| + |z| * |w| + |v| := by
        rw [abs_mul, abs_mul]

section ComponentwiseCalibrationBudget

/-! The three theorems below are about one deployed pathway measured against one true
pathway under one componentwise error budget, and each restated that budget in full:
seventeen lines of hypotheses, three times.  The budget is a `variable` block now, and
`include` makes it a premise of each theorem exactly as writing it out did.

It is deliberately NOT a structure.  A bundle of hypotheses with no construction that
satisfies it is what the `identifications` guard calls an unwitnessed bundle, and this
corpus has been bitten by that shape; a `variable` block carries the same hypotheses
without inventing a certificate. -/

variable {T : ℕ} (model : LongitudinalTreatmentModel T)
  (truePath predictedPath : ClinicalPathway T)
  (εWeight εEvent εBenefit εHarm
    weightBound eventBound benefitBound netBound : Fin T → ℝ)
  (h_weight_err : ∀ t,
    |predictedPath.followupWeight t - truePath.followupWeight t| ≤ εWeight t)
  (h_event_err : ∀ t,
    |predictedPath.eventProb t - truePath.eventProb t| ≤ εEvent t)
  (h_benefit_err : ∀ t,
    |predictedPath.treatmentBenefit t - truePath.treatmentBenefit t| ≤ εBenefit t)
  (h_harm_err : ∀ t,
    |predictedPath.treatmentHarm t - truePath.treatmentHarm t| ≤ εHarm t)
  (h_weight_bound : ∀ t, |predictedPath.followupWeight t| ≤ weightBound t)
  (h_event_bound : ∀ t, |predictedPath.eventProb t| ≤ eventBound t)
  (h_benefit_bound : ∀ t, |truePath.treatmentBenefit t| ≤ benefitBound t)
  (h_net_bound : ∀ t,
    |truePath.eventProb t * truePath.treatmentBenefit t -
        truePath.treatmentHarm t| ≤ netBound t)

include h_weight_err h_event_err h_benefit_err h_harm_err
  h_weight_bound h_event_bound h_benefit_bound h_net_bound

/-- **Componentwise calibration error bound for longitudinal treatment margin.**
    If the deployed pathway approximates the true censoring/eligibility weights,
    event probabilities, treatment-benefit heterogeneity, and treatment harm
    with bounded error, then the exact finite-horizon treatment-margin error is
    bounded by the corresponding weighted sum of those componentwise errors. -/
theorem abs_treatmentMargin_error_le_componentwise_calibration_bound :
    |treatmentMargin model predictedPath - treatmentMargin model truePath| ≤
      Finset.univ.sum (fun t ↦
        model.discount t *
          (εWeight t * netBound t +
            weightBound t *
              (εEvent t * benefitBound t +
                eventBound t * εBenefit t + εHarm t))) := by
  rw [treatmentMargin_error_eq_componentwise_sum]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  refine Finset.sum_le_sum ?_
  intro t _
  have hdisc : 0 ≤ model.discount t := model.discount_nonneg t
  have hεWeight_nonneg : 0 ≤ εWeight t :=
    le_trans (abs_nonneg _) (h_weight_err t)
  have hεEvent_nonneg : 0 ≤ εEvent t :=
    le_trans (abs_nonneg _) (h_event_err t)
  have hεBenefit_nonneg : 0 ≤ εBenefit t :=
    le_trans (abs_nonneg _) (h_benefit_err t)
  have hεHarm_nonneg : 0 ≤ εHarm t :=
    le_trans (abs_nonneg _) (h_harm_err t)
  have hWeight_nonneg : 0 ≤ weightBound t :=
    le_trans (abs_nonneg _) (h_weight_bound t)
  have hEvent_nonneg : 0 ≤ eventBound t :=
    le_trans (abs_nonneg _) (h_event_bound t)
  have hBenefit_nonneg : 0 ≤ benefitBound t :=
    le_trans (abs_nonneg _) (h_benefit_bound t)
  have hNet_nonneg : 0 ≤ netBound t :=
    le_trans (abs_nonneg _) (h_net_bound t)
  have h_term1 :
      |predictedPath.followupWeight t - truePath.followupWeight t| *
          |truePath.eventProb t * truePath.treatmentBenefit t -
            truePath.treatmentHarm t| ≤
        εWeight t * netBound t :=
    mul_le_mul (h_weight_err t) (h_net_bound t) (abs_nonneg _) hεWeight_nonneg
  have h_term2a :
      |predictedPath.eventProb t - truePath.eventProb t| *
          |truePath.treatmentBenefit t| ≤
        εEvent t * benefitBound t :=
    mul_le_mul (h_event_err t) (h_benefit_bound t) (abs_nonneg _) hεEvent_nonneg
  have h_term2b :
      |predictedPath.eventProb t| *
          |predictedPath.treatmentBenefit t - truePath.treatmentBenefit t| ≤
        eventBound t * εBenefit t :=
    mul_le_mul (h_event_bound t) (h_benefit_err t) (abs_nonneg _) hEvent_nonneg
  have h_nested :
      |pathwayNetBenefitError truePath predictedPath t| ≤
        εEvent t * benefitBound t + eventBound t * εBenefit t + εHarm t := by
    unfold pathwayNetBenefitError
    have hsplit := abs_two_products_sub_le
      (predictedPath.eventProb t - truePath.eventProb t)
      (truePath.treatmentBenefit t)
      (predictedPath.eventProb t)
      (predictedPath.treatmentBenefit t - truePath.treatmentBenefit t)
      (predictedPath.treatmentHarm t - truePath.treatmentHarm t)
    linarith [hsplit, h_term2a, h_term2b, h_harm_err t]
  have h_term2 :
      |predictedPath.followupWeight t| *
          |pathwayNetBenefitError truePath predictedPath t| ≤
        weightBound t *
          (εEvent t * benefitBound t + eventBound t * εBenefit t + εHarm t) :=
    mul_le_mul (h_weight_bound t) h_nested (abs_nonneg _) hWeight_nonneg
  have h_inner_bound :
      |predictedPath.followupWeight t - truePath.followupWeight t| *
          |truePath.eventProb t * truePath.treatmentBenefit t -
            truePath.treatmentHarm t| +
        |predictedPath.followupWeight t| *
          |pathwayNetBenefitError truePath predictedPath t| ≤
        εWeight t * netBound t +
          weightBound t *
            (εEvent t * benefitBound t + eventBound t * εBenefit t + εHarm t) := by
    linarith [h_term1, h_term2]
  calc
    |treatmentMarginErrorTerm model truePath predictedPath t|
        = model.discount t *
            |(predictedPath.followupWeight t - truePath.followupWeight t) *
                (truePath.eventProb t * truePath.treatmentBenefit t -
                  truePath.treatmentHarm t) +
              predictedPath.followupWeight t *
                pathwayNetBenefitError truePath predictedPath t| := by
          unfold treatmentMarginErrorTerm
          rw [abs_mul, abs_of_nonneg hdisc]
    _ ≤ model.discount t *
          (|(predictedPath.followupWeight t - truePath.followupWeight t) *
              (truePath.eventProb t * truePath.treatmentBenefit t -
                truePath.treatmentHarm t)| +
            |predictedPath.followupWeight t *
              pathwayNetBenefitError truePath predictedPath t|) := by
          gcongr
          exact abs_add_le _ _
    _ = model.discount t *
          (|predictedPath.followupWeight t - truePath.followupWeight t| *
              |truePath.eventProb t * truePath.treatmentBenefit t -
                truePath.treatmentHarm t| +
            |predictedPath.followupWeight t| *
              |pathwayNetBenefitError truePath predictedPath t|) := by
          rw [abs_mul, abs_mul]
    _ ≤ model.discount t *
          (εWeight t * netBound t +
            weightBound t *
              (εEvent t * benefitBound t +
                eventBound t * εBenefit t + εHarm t)) :=
          mul_le_mul_of_nonneg_left h_inner_bound hdisc

/-- **Exact longitudinal QALY-loss bound from calibration errors in the event
    process, heterogeneous treatment effects, harms, and censoring weights.** -/
theorem qalyLoss_le_componentwise_calibration_bound :
    qalyLoss model truePath predictedPath ≤
      Finset.univ.sum (fun t ↦
        model.discount t *
          (εWeight t * netBound t +
            weightBound t *
              (εEvent t * benefitBound t +
                eventBound t * εBenefit t + εHarm t))) :=
  le_trans (qalyLoss_le_abs_margin_error model truePath predictedPath)
    (abs_treatmentMargin_error_le_componentwise_calibration_bound
      model truePath predictedPath εWeight εEvent εBenefit εHarm
      weightBound eventBound benefitBound netBound
      h_weight_err h_event_err h_benefit_err h_harm_err
      h_weight_bound h_event_bound h_benefit_bound h_net_bound)

/-- **If componentwise pathway calibration error is smaller than the true
    longitudinal treatment margin, the deployed and oracle clinical decisions
    coincide exactly and QALY regret vanishes.** -/
theorem qalyLoss_eq_zero_of_componentwise_calibration_bound_lt_abs_true_margin
    (h_small :
      Finset.univ.sum (fun t ↦
        model.discount t *
          (εWeight t * netBound t +
            weightBound t *
              (εEvent t * benefitBound t +
                eventBound t * εBenefit t + εHarm t))) <
        |treatmentMargin model truePath|) :
    qalyLoss model truePath predictedPath = 0 := by
  apply qalyLoss_eq_zero_of_margin_error_lt_abs_true_margin
  exact lt_of_le_of_lt
    (abs_treatmentMargin_error_le_componentwise_calibration_bound
      model truePath predictedPath εWeight εEvent εBenefit εHarm
      weightBound eventBound benefitBound netBound
      h_weight_err h_event_err h_benefit_err h_harm_err
      h_weight_bound h_event_bound h_benefit_bound h_net_bound)
    h_small

end ComponentwiseCalibrationBudget

/-- **Expected QALY loss from pathway miscalibration.**
    This is the population expectation of exact oracle regret under the
    longitudinal pathway model. -/
noncomputable def expectedQalyLoss {Z : Type*} [MeasurableSpace Z] {T : ℕ}
    (μ : Measure Z) (model : LongitudinalTreatmentModel T)
    (truePath predictedPath : Z → ClinicalPathway T) : ℝ :=
  ∫ z, qalyLoss model (truePath z) (predictedPath z) ∂μ

/-- Perfect pathway calibration implies zero expected QALY loss. -/
theorem expectedQalyLoss_eq_zero_of_perfect_pathway_calibration
    {Z : Type*} [MeasurableSpace Z] {T : ℕ}
    (μ : Measure Z) (model : LongitudinalTreatmentModel T)
    (truePath predictedPath : Z → ClinicalPathway T)
    (h_cal : ∀ z,
      treatmentMargin model (predictedPath z) =
        treatmentMargin model (truePath z)) :
    expectedQalyLoss μ model truePath predictedPath = 0 := by
  unfold expectedQalyLoss
  have hfun :
      (fun z ↦ qalyLoss model (truePath z) (predictedPath z)) =
        fun _ ↦ (0 : ℝ) := by
    funext z
    exact qalyLoss_eq_zero_of_perfect_pathway_calibration
      model (truePath z) (predictedPath z) (h_cal z)
  rw [hfun]
  simp

/-- **Expected QALY loss equals expected longitudinal decision regret.** -/
theorem expectedQalyLoss_eq_expected_qalyDecisionRegretMargin
    {Z : Type*} [MeasurableSpace Z] {T : ℕ}
    (μ : Measure Z) (model : LongitudinalTreatmentModel T)
    (truePath predictedPath : Z → ClinicalPathway T) :
    expectedQalyLoss μ model truePath predictedPath =
      ∫ z, qalyDecisionRegretMargin model (truePath z) (predictedPath z) ∂μ := by
  unfold expectedQalyLoss
  refine integral_congr_ae ?_
  exact Filter.Eventually.of_forall (fun z ↦
    qalyLoss_eq_qalyDecisionRegretMargin
      model (truePath z) (predictedPath z))

/-- Shared one-step screening decision interface.
    `threshold` is the risk cutoff used by the policy, `benefit` is the utility
    of a true-positive treatment, and `harm` is the utility cost of a
    false-positive treatment. -/
structure ScreeningDecisionModel where
  threshold : ℝ
  benefit : ℝ
  harm : ℝ

/-- One-step longitudinal embedding of the shared screening model. -/
noncomputable def screeningLongitudinalModel
    (_model : ScreeningDecisionModel) : LongitudinalTreatmentModel 1 where
  discount := fun _ ↦ 1
  discount_nonneg := by
    intro _
    norm_num

/-- One-step clinical pathway induced by a scalar event risk under the shared
    screening model. A treated event yields utility `benefit`, a treated
    non-event yields utility `-harm`, and no treatment yields `0`. -/
noncomputable def screeningClinicalPathway
    (model : ScreeningDecisionModel) (risk : ℝ) : ClinicalPathway 1 where
  followupWeight := fun _ ↦ 1
  eventProb := fun _ ↦ risk
  treatmentBenefit := fun _ ↦ model.benefit + model.harm
  treatmentHarm := fun _ ↦ model.harm
  followupWeight_nonneg := by
    intro _
    norm_num

/-- If the screening-model utility ratio matches the decision threshold, the
    one-step treatment margin is exactly `(benefit + harm) × (risk - threshold)`.
    This is the shared bridge from policy thresholding to exact pathway utility. -/
theorem treatmentMargin_screeningClinicalPathway
    (model : ScreeningDecisionModel) (risk : ℝ)
    (h_threshold :
      model.harm = model.threshold * (model.benefit + model.harm)) :
    treatmentMargin (screeningLongitudinalModel model)
      (screeningClinicalPathway model risk) =
        (model.benefit + model.harm) * (risk - model.threshold) := by
  unfold treatmentMargin qalyContributionAtTime
    screeningLongitudinalModel screeningClinicalPathway
  rw [Fin.sum_univ_one]
  dsimp
  norm_num
  nlinarith

/-- Under the exact threshold/utility relation, the shared screening model
    treats exactly when the input risk exceeds the policy threshold. -/
theorem receivesTreatment_screeningClinicalPathway_iff
    (model : ScreeningDecisionModel) (risk : ℝ)
    (h_total_pos : 0 < model.benefit + model.harm)
    (h_threshold :
      model.harm = model.threshold * (model.benefit + model.harm)) :
    receivesTreatment (screeningLongitudinalModel model)
      (screeningClinicalPathway model risk) ↔
        classifiedHighRisk model.threshold risk := by
  unfold receivesTreatment classifiedHighRisk
  rw [treatmentMargin_screeningClinicalPathway model risk h_threshold]
  constructor <;> intro h <;> nlinarith

/-- Count-based expected screening utility on a per-person scale. -/
noncomputable def screeningUtilityFromCounts
    (model : ScreeningDecisionModel) (tp fp n : ℝ) : ℝ :=
  model.benefit * (tp / n) - model.harm * (fp / n)

/-- **screeningUtilityFromCounts at its junk point, named.** With no one screened both rates divide
by zero and are junk-zero, so the net utility is exactly `0` -- the break-even value. An empty
screening programme is reported as precisely neutral rather than as undefined, and neutral is a
defensible-looking answer that no downstream check will question. Consumers must exclude the
argument that makes the guard vanish. -/
theorem screeningUtilityFromCounts_empty_cohort_is_junk
    (model : ScreeningDecisionModel) (tp fp : ℝ) :
    screeningUtilityFromCounts model tp fp 0 = 0 := by
  unfold screeningUtilityFromCounts
  simp

/-- Rate-based expected screening utility on a per-person scale. -/
noncomputable def screeningUtilityFromRates
    (model : ScreeningDecisionModel) (sens spec prevalence : ℝ) : ℝ :=
  sens * prevalence * model.benefit -
    (1 - spec) * (1 - prevalence) * model.harm

/-- Vanishing identity: a perfectly specific test on a zero-prevalence population has no
utility, whatever its sensitivity -- there is nobody to benefit and nobody to harm. -/
theorem screeningUtilityFromRates_zero_prevalence_eq_zero (model : ScreeningDecisionModel)
    (sens : ℝ) :
    screeningUtilityFromRates model sens 1 0 = 0 := by
  unfold screeningUtilityFromRates
  ring


/-- The count-based and rate-based screening utilities agree when true- and
    false-positive counts are instantiated from sensitivity, specificity,
    prevalence, and sample size. -/
theorem screeningUtilityFromCounts_eq_screeningUtilityFromRates
    (model : ScreeningDecisionModel)
    (sens spec prevalence n : ℝ)
    (h_n : 0 < n) :
    screeningUtilityFromCounts model
        (sens * prevalence * n)
        ((1 - spec) * (1 - prevalence) * n) n =
      screeningUtilityFromRates model sens spec prevalence := by
  unfold screeningUtilityFromCounts screeningUtilityFromRates
  field_simp [ne_of_gt h_n]

/-- Treating an event under the shared screening model yields exactly the
    model's true-positive utility. -/
theorem qalyGainUnderDecision_screening_case_treat
    (model : ScreeningDecisionModel) (decisionRisk : ℝ)
    (h_total_pos : 0 < model.benefit + model.harm)
    (h_threshold :
      model.harm = model.threshold * (model.benefit + model.harm))
    (h_decision : classifiedHighRisk model.threshold decisionRisk) :
    qalyGainUnderDecision (screeningLongitudinalModel model)
      (screeningClinicalPathway model 1)
      (screeningClinicalPathway model decisionRisk) =
        model.benefit := by
  have h_treat :
      receivesTreatment (screeningLongitudinalModel model)
        (screeningClinicalPathway model decisionRisk) :=
    (receivesTreatment_screeningClinicalPathway_iff
      model decisionRisk h_total_pos h_threshold).2 h_decision
  unfold qalyGainUnderDecision
  rw [if_pos h_treat, treatmentMargin_screeningClinicalPathway model 1 h_threshold]
  nlinarith

/-- Treating a non-event under the shared screening model yields exactly the
    model's false-positive utility cost. -/
theorem qalyGainUnderDecision_screening_control_treat
    (model : ScreeningDecisionModel) (decisionRisk : ℝ)
    (h_total_pos : 0 < model.benefit + model.harm)
    (h_threshold :
      model.harm = model.threshold * (model.benefit + model.harm))
    (h_decision : classifiedHighRisk model.threshold decisionRisk) :
    qalyGainUnderDecision (screeningLongitudinalModel model)
      (screeningClinicalPathway model 0)
      (screeningClinicalPathway model decisionRisk) =
        -model.harm := by
  have h_treat :
      receivesTreatment (screeningLongitudinalModel model)
        (screeningClinicalPathway model decisionRisk) :=
    (receivesTreatment_screeningClinicalPathway_iff
      model decisionRisk h_total_pos h_threshold).2 h_decision
  unfold qalyGainUnderDecision
  rw [if_pos h_treat, treatmentMargin_screeningClinicalPathway model 0 h_threshold]
  nlinarith

/-- If the shared screening policy does not treat, realized utility is zero for
    both events and non-events. -/
theorem qalyGainUnderDecision_screening_no_treat
    (model : ScreeningDecisionModel) (trueRisk decisionRisk : ℝ)
    (h_total_pos : 0 < model.benefit + model.harm)
    (h_threshold :
      model.harm = model.threshold * (model.benefit + model.harm))
    (h_not_decision : ¬ classifiedHighRisk model.threshold decisionRisk) :
    qalyGainUnderDecision (screeningLongitudinalModel model)
      (screeningClinicalPathway model trueRisk)
      (screeningClinicalPathway model decisionRisk) =
        0 := by
  have h_not_treat :
      ¬ receivesTreatment (screeningLongitudinalModel model)
        (screeningClinicalPathway model decisionRisk) := by
    intro h_treat
    exact h_not_decision
      ((receivesTreatment_screeningClinicalPathway_iff
        model decisionRisk h_total_pos h_threshold).1 h_treat)
  unfold qalyGainUnderDecision
  simp [h_not_treat]

/-- Canonical screening model behind the cost-effectiveness section:
    the policy threshold is exactly `harm / (benefit + harm)`. -/
noncomputable def qalyScreeningDecisionModel
    (benefit harm : ℝ) : ScreeningDecisionModel where
  threshold := harm / (benefit + harm)
  benefit := benefit
  harm := harm

/-- With neither benefit nor harm the threshold divides by zero and Mathlib returns `0`: a
model that screens everyone, which is the opposite of what a decision with no stakes should
recommend. -/
theorem qalyScreeningDecisionModel_at_zero_stakes_is_junk (benefit harm : ℝ)
    (hzero : benefit + harm = 0) :
    (qalyScreeningDecisionModel benefit harm).threshold = 0 := by
  unfold qalyScreeningDecisionModel
  simp [hzero]


/-- The canonical cost-effectiveness screening model satisfies the exact
    threshold/utility bridge equation. -/
theorem qalyScreeningDecisionModel_harm_eq_threshold_scale
    (benefit harm : ℝ)
    (h_total : benefit + harm ≠ 0) :
    (qalyScreeningDecisionModel benefit harm).harm =
      (qalyScreeningDecisionModel benefit harm).threshold *
        ((qalyScreeningDecisionModel benefit harm).benefit +
          (qalyScreeningDecisionModel benefit harm).harm) := by
  unfold qalyScreeningDecisionModel
  field_simp [h_total]

/-- The canonical QALY-style screening model has positive total utility scale
    whenever benefit and harm are both positive. -/
theorem qalyScreeningDecisionModel_total_pos
    (benefit harm : ℝ)
    (h_benefit : 0 < benefit) (h_harm : 0 < harm) :
    0 <
      (qalyScreeningDecisionModel benefit harm).benefit +
        (qalyScreeningDecisionModel benefit harm).harm := by
  unfold qalyScreeningDecisionModel
  linarith

/-- Canonical QALY-style screening utility on operating-point rates. -/
noncomputable def screeningQalyGain
    (sens spec prevalence benefit harm : ℝ) : ℝ :=
  screeningUtilityFromRates (qalyScreeningDecisionModel benefit harm)
    sens spec prevalence

/-- The canonical screening-QALY utility is exactly the familiar
    `sens × π × benefit − (1−spec) × (1−π) × harm` formula. -/
theorem screeningQalyGain_eq_formula
    (sens spec prevalence benefit harm : ℝ) :
    screeningQalyGain sens spec prevalence benefit harm =
      sens * prevalence * benefit -
        (1 - spec) * (1 - prevalence) * harm := by
  unfold screeningQalyGain screeningUtilityFromRates qalyScreeningDecisionModel
  ring

/-- **Exact QALY break-even boundary.** Screening has positive QALY gain exactly when weighted
true-positive benefit exceeds weighted false-positive harm.  This iff is assumption-free: domain
restrictions such as rates in `[0,1]` are needed for interpretation, not for the algebraic
decision boundary. -/
theorem screeningQalyGain_pos_iff
    (sens spec prevalence benefit harm : ℝ) :
    0 < screeningQalyGain sens spec prevalence benefit harm ↔
      (1 - spec) * (1 - prevalence) * harm < sens * prevalence * benefit := by
  rw [screeningQalyGain_eq_formula]
  constructor <;> intro h <;> linarith

/-- Screening is exactly QALY-neutral precisely on the weighted benefit/harm equality surface. -/
theorem screeningQalyGain_eq_zero_iff
    (sens spec prevalence benefit harm : ℝ) :
    screeningQalyGain sens spec prevalence benefit harm = 0 ↔
      sens * prevalence * benefit = (1 - spec) * (1 - prevalence) * harm := by
  rw [screeningQalyGain_eq_formula]
  exact sub_eq_zero

/-- Screening has negative QALY gain exactly when weighted false-positive harm exceeds weighted
true-positive benefit. -/
theorem screeningQalyGain_neg_iff
    (sens spec prevalence benefit harm : ℝ) :
    screeningQalyGain sens spec prevalence benefit harm < 0 ↔
      sens * prevalence * benefit < (1 - spec) * (1 - prevalence) * harm := by
  rw [screeningQalyGain_eq_formula]
  constructor <;> intro h <;> linarith

/-- **Break-even prevalence for a screening operating point.**  This is the prevalence at which
weighted true-positive benefit balances weighted false-positive harm in the declared model.

Empirical status: **VALIDATED against a simulated programme** (`simcov/battery_bulk41b.py`,
`group_g`). 2×10⁶ individuals at each of 69 prevalences, test outcomes DRAWN at the stated
sensitivity and specificity rather than computed, net benefit accumulated as benefit per true
positive minus harm per false positive; the observable is the prevalence at which the MEASURED
net benefit crosses zero, read by interpolation.

  sens   spec   harm    this body   measured crossing   sems
  0.90   0.90    1.5     0.14286        0.14281         0.05
  0.80   0.95    3.0     0.15789        0.15798         0.04
  0.95   0.70    1.0     0.24000        0.24034         0.64
  0.70   0.99   20.0     0.22222        0.22303         0.07

Three competing forms are carried on the same cells and all three are refuted: swapping the
numerator misses by 965 sems, the odds form `(1-spec)·harm/(sens·benefit)` by 140, and
leaving `spec` uncomplemented by 459. The positive control -- the net benefit at a FIXED
prevalence against `b·π·sens - h·(1-π)(1-spec)`, a different quantity on the same simulator --
passes at 0.11 sems.

An earlier design (`battery_bulk40.py`, `group_g`) chose harm-to-benefit ratios that put every
crossing near π = 0.005 on a grid of spacing 0.0068, so the error bar was 35% of the quantity
and the odds form matched too. The harm-to-benefit ratios here put the crossing between 0.14
and 0.24, where the grid resolves it and the odds form separates.

What is validated is the ARITHMETIC of the declared linear QALY model. Its clinical adequacy
-- whether benefit and harm are commensurable on one scale at all -- is not established by
data in this corpus and is not the kind of thing this simulation could establish. -/
noncomputable def screeningBreakEvenPrevalence
    (sens spec benefit harm : ℝ) : ℝ :=
  (1 - spec) * harm / (sens * benefit + (1 - spec) * harm)

/-- **Exact prevalence threshold for positive screening utility.**  Whenever the combined
benefit/harm scale is positive, screening has positive QALY gain exactly above the break-even
prevalence.  Sensitivity and specificity enter jointly: neither prevalence nor discrimination
alone determines utility. -/
theorem screeningQalyGain_pos_iff_prevalence_gt
    (sens spec prevalence benefit harm : ℝ)
    (h_scale : 0 < sens * benefit + (1 - spec) * harm) :
    0 < screeningQalyGain sens spec prevalence benefit harm ↔
      screeningBreakEvenPrevalence sens spec benefit harm < prevalence := by
  rw [screeningQalyGain_pos_iff]
  unfold screeningBreakEvenPrevalence
  rw [div_lt_iff₀ h_scale]
  constructor <;> intro h <;> nlinarith

/-- At positive combined utility scale, screening is QALY-neutral exactly at its break-even
prevalence. -/
theorem screeningQalyGain_eq_zero_iff_prevalence_eq
    (sens spec prevalence benefit harm : ℝ)
    (h_scale : 0 < sens * benefit + (1 - spec) * harm) :
    screeningQalyGain sens spec prevalence benefit harm = 0 ↔
      prevalence = screeningBreakEvenPrevalence sens spec benefit harm := by
  rw [screeningQalyGain_eq_zero_iff]
  unfold screeningBreakEvenPrevalence
  rw [eq_div_iff h_scale.ne']
  constructor <;> intro h <;> nlinarith

/-- At positive combined utility scale, screening has negative QALY gain exactly below its
break-even prevalence. -/
theorem screeningQalyGain_neg_iff_prevalence_lt
    (sens spec prevalence benefit harm : ℝ)
    (h_scale : 0 < sens * benefit + (1 - spec) * harm) :
    screeningQalyGain sens spec prevalence benefit harm < 0 ↔
      prevalence < screeningBreakEvenPrevalence sens spec benefit harm := by
  rw [screeningQalyGain_neg_iff]
  unfold screeningBreakEvenPrevalence
  rw [lt_div_iff₀ h_scale]
  constructor <;> intro h <;> nlinarith

/-- Canonical decision-curve screening model: benefit is normalized to `1` and
    false-positive harm is the usual decision-curve odds weight `t / (1-t)`. -/
noncomputable def decisionCurveScreeningModel
    (t : ℝ) : ScreeningDecisionModel where
  threshold := t
  benefit := 1
  harm := t / (1 - t)

/-- At a unit threshold the odds ratio divides by zero and Mathlib returns `0` harm, so the
model reports screening as costless exactly where it should be prohibitive. -/
theorem decisionCurveScreeningModel_at_unit_threshold_is_junk :
    (decisionCurveScreeningModel 1).harm = 0 := by
  simp [decisionCurveScreeningModel]


/-- The decision-curve screening model satisfies the exact threshold/utility
    bridge equation whenever `t ≠ 1`. -/
theorem decisionCurveScreeningModel_harm_eq_threshold_scale
    (t : ℝ) (h_t : t ≠ 1) :
    (decisionCurveScreeningModel t).harm =
      (decisionCurveScreeningModel t).threshold *
        ((decisionCurveScreeningModel t).benefit +
          (decisionCurveScreeningModel t).harm) := by
  unfold decisionCurveScreeningModel
  have h_one_sub : 1 - t ≠ 0 := sub_ne_zero.mpr (Ne.symm h_t)
  field_simp [h_one_sub]
  ring

/-- The decision-curve screening model has positive total utility scale in the
    standard regime `0 < t < 1`. -/
theorem decisionCurveScreeningModel_total_pos
    (t : ℝ) (ht : 0 < t) (ht1 : t < 1) :
    0 <
      (decisionCurveScreeningModel t).benefit +
        (decisionCurveScreeningModel t).harm := by
  unfold decisionCurveScreeningModel
  have h_one_sub : 0 < 1 - t := by linarith
  have h_div : 0 < t / (1 - t) := div_pos ht h_one_sub
  linarith

/-- Canonical decision-curve net benefit on a per-person scale. -/
noncomputable def decisionCurveNetBenefit
    (tp fp n t : ℝ) : ℝ :=
  screeningUtilityFromCounts (decisionCurveScreeningModel t) tp fp n

/-- The canonical decision-curve net benefit is exactly the usual
    `TP/N − FP/N × t/(1−t)` expression. -/
theorem decisionCurveNetBenefit_eq_formula
    (tp fp n t : ℝ) :
    decisionCurveNetBenefit tp fp n t =
      tp / n - fp / n * (t / (1 - t)) := by
  unfold decisionCurveNetBenefit screeningUtilityFromCounts
    decisionCurveScreeningModel
  ring

/-- **Clinical treatment model induced by a decision threshold.**
    This is the exact one-time specialization of the longitudinal pathway model
    in which treatment yields benefit `benefit × trueRisk` in expectation and
    incurs harm `harm` whenever given. The clinically optimal threshold is
    therefore `harm / benefit`; we encode this exactly as
    `harm = benefit × threshold`. -/
structure ThresholdTreatmentModel where
  threshold : ℝ
  benefit : ℝ
  harm : ℝ
  benefit_pos : 0 < benefit
  harm_eq_threshold : harm = benefit * threshold

/-- **The class is inhabited.**  A theorem quantified over an uninhabited structure is
true and empty: kernel-checked, clean axiom report, no content.  This is the witness that
makes the theorems below statements about something. -/
noncomputable def ThresholdTreatmentModel.witness : ThresholdTreatmentModel where
  threshold := 1
  benefit := 1
  harm := 1
  benefit_pos := by norm_num
  harm_eq_threshold := by norm_num

/-- One-step longitudinal model corresponding to a single threshold-based
    treatment decision.

    Empirical status: UNTESTED. -/
noncomputable def thresholdLongitudinalModel
    (_model : ThresholdTreatmentModel) : LongitudinalTreatmentModel 1 where
  discount := fun _ ↦ 1
  discount_nonneg := by
    intro _
    norm_num

/-- **The one-step horizon carries no decision model.**

A `LongitudinalTreatmentModel 1` holds only the discount schedule, and over a single
period both embeddings undiscount it. So the threshold model and the screening model
produce the identical longitudinal object: everything that separates the two decision
rules lives in the clinical pathway, not in the horizon. Anyone who later gives one
embedding a nontrivial discount has to give the other one too, or this stops
compiling. -/
theorem thresholdLongitudinalModel_eq_screeningLongitudinalModel
    (model : ThresholdTreatmentModel) (screening : ScreeningDecisionModel) :
    thresholdLongitudinalModel model = screeningLongitudinalModel screening := rfl

/-- One-step clinical pathway induced by a scalar risk under the threshold
    treatment model.

    Empirical status: UNTESTED. -/
noncomputable def thresholdClinicalPathway
    (model : ThresholdTreatmentModel) (risk : ℝ) : ClinicalPathway 1 where
  followupWeight := fun _ ↦ 1
  eventProb := fun _ ↦ risk
  treatmentBenefit := fun _ ↦ model.benefit
  treatmentHarm := fun _ ↦ model.harm
  followupWeight_nonneg := by
    intro _
    norm_num

/-- The exact one-step treatment margin is benefit times risk above threshold. -/
theorem treatmentMargin_thresholdClinicalPathway
    (model : ThresholdTreatmentModel) (risk : ℝ) :
    treatmentMargin (thresholdLongitudinalModel model)
      (thresholdClinicalPathway model risk) =
        model.benefit * (risk - model.threshold) := by
  unfold treatmentMargin qalyContributionAtTime
    thresholdLongitudinalModel thresholdClinicalPathway
  rw [Fin.sum_univ_one]
  simp [model.harm_eq_threshold]
  ring

/-- In the one-step specialization, positive treatment margin is exactly the
    high-risk classification event. -/
theorem receivesTreatment_thresholdClinicalPathway_iff
    (model : ThresholdTreatmentModel) (risk : ℝ) :
    receivesTreatment (thresholdLongitudinalModel model)
      (thresholdClinicalPathway model risk) ↔
        classifiedHighRisk model.threshold risk := by
  unfold receivesTreatment classifiedHighRisk
  rw [treatmentMargin_thresholdClinicalPathway]
  constructor <;> intro h <;> nlinarith [model.benefit_pos]

/-- **Threshold-based QALY gain under a scalar risk decision.**
    The deployed system treats when the risk used for decision-making exceeds
    the clinical treatment threshold.

    Empirical status: UNTESTED. -/
noncomputable def thresholdQalyGainUnderDecision
    (model : ThresholdTreatmentModel) (trueRisk decisionRisk : ℝ) : ℝ :=
  if _ : model.threshold < decisionRisk then
      model.benefit * trueRisk - model.harm
    else
      0

/-- Reference evaluation: below the treatment threshold no decision is taken and the gain is
zero, whatever the true risk. -/
theorem thresholdQalyGainUnderDecision_at_no_treatment (model : ThresholdTreatmentModel)
    (trueRisk decisionRisk : ℝ) (hbelow : decisionRisk ≤ model.threshold) :
    thresholdQalyGainUnderDecision model trueRisk decisionRisk = 0 := by
  unfold thresholdQalyGainUnderDecision
  rw [dif_neg (by linarith)]


/-- **Per-individual one-step QALY loss from using predicted instead of true
    risk.** This is the threshold-rule specialization of `qalyLoss`.

    Empirical status: UNTESTED. -/
noncomputable def thresholdQalyLoss
    (model : ThresholdTreatmentModel) (trueRisk predictedRisk : ℝ) : ℝ :=
  thresholdQalyGainUnderDecision model trueRisk trueRisk -
    thresholdQalyGainUnderDecision model trueRisk predictedRisk

/-- **Threshold-decision regret margin.**
    This is the clinically relevant risk margin by which the deployed decision
    disagrees with the oracle threshold rule:
    - false positives pay `threshold - trueRisk`,
    - false negatives pay `trueRisk - threshold`,
    - correct decisions pay `0`.

    Empirical status: UNTESTED. -/
noncomputable def thresholdDecisionRegretMargin
    (model : ThresholdTreatmentModel) (trueRisk predictedRisk : ℝ) : ℝ := by
    classical
    exact if classifiedHighRisk model.threshold predictedRisk then
        max (model.threshold - trueRisk) 0
      else
        max (trueRisk - model.threshold) 0

/-- The threshold one-step gain is exactly the general pathway gain under the
    threshold specialization. -/
theorem qalyGainUnderDecision_threshold_eq_thresholdQalyGainUnderDecision
    (model : ThresholdTreatmentModel) (trueRisk decisionRisk : ℝ) :
    qalyGainUnderDecision (thresholdLongitudinalModel model)
      (thresholdClinicalPathway model trueRisk)
      (thresholdClinicalPathway model decisionRisk) =
        thresholdQalyGainUnderDecision model trueRisk decisionRisk := by
  by_cases h : model.threshold < decisionRisk
  · have h_treat :
        receivesTreatment (thresholdLongitudinalModel model)
          (thresholdClinicalPathway model decisionRisk) :=
      (receivesTreatment_thresholdClinicalPathway_iff model decisionRisk).2 h
    unfold qalyGainUnderDecision
    rw [if_pos h_treat, treatmentMargin_thresholdClinicalPathway]
    simp [thresholdQalyGainUnderDecision, h, model.harm_eq_threshold]
    ring
  · have h_not_treat :
        ¬ receivesTreatment (thresholdLongitudinalModel model)
          (thresholdClinicalPathway model decisionRisk) :=
      fun h_treat ↦
        h ((receivesTreatment_thresholdClinicalPathway_iff model decisionRisk).1 h_treat)
    unfold qalyGainUnderDecision
    rw [if_neg h_not_treat]
    simp [thresholdQalyGainUnderDecision, h]

/-- The threshold one-step loss is exactly the general pathway loss under the
    threshold specialization. -/
theorem qalyLoss_threshold_eq_thresholdQalyLoss
    (model : ThresholdTreatmentModel) (trueRisk predictedRisk : ℝ) :
    qalyLoss (thresholdLongitudinalModel model)
      (thresholdClinicalPathway model trueRisk)
      (thresholdClinicalPathway model predictedRisk) =
        thresholdQalyLoss model trueRisk predictedRisk := by
  unfold qalyLoss thresholdQalyLoss
  rw [qalyGainUnderDecision_threshold_eq_thresholdQalyGainUnderDecision,
    qalyGainUnderDecision_threshold_eq_thresholdQalyGainUnderDecision]

/-- **Exact QALY loss for a false positive treatment decision.**
    If the patient's true risk is below threshold but the predicted risk is
    above threshold, the loss equals the treatment benefit scale times the
    distance from the true risk to the treatment threshold. -/
theorem thresholdQalyLoss_false_positive_exact
    (model : ThresholdTreatmentModel) (trueRisk predictedRisk : ℝ)
    (h_true_low : trueRisk ≤ model.threshold)
    (h_pred_high : classifiedHighRisk model.threshold predictedRisk) :
    thresholdQalyLoss model trueRisk predictedRisk =
      model.benefit * (model.threshold - trueRisk) := by
  have h_true_not_high : ¬ model.threshold < trueRisk := not_lt.mpr h_true_low
  have h_pred_high' : model.threshold < predictedRisk := by
    simpa [classifiedHighRisk] using h_pred_high
  unfold thresholdQalyLoss thresholdQalyGainUnderDecision
  simp [h_true_not_high, h_pred_high', model.harm_eq_threshold]
  ring_nf

/-- **Exact QALY loss for a false negative treatment decision.**
    If the patient's true risk is above threshold but the predicted risk is
    at or below threshold, the loss equals the missed-treatment margin above
    threshold on the QALY-benefit scale. -/
theorem thresholdQalyLoss_false_negative_exact
    (model : ThresholdTreatmentModel) (trueRisk predictedRisk : ℝ)
    (h_true_high : model.threshold < trueRisk)
    (h_pred_not_high : ¬ classifiedHighRisk model.threshold predictedRisk) :
    thresholdQalyLoss model trueRisk predictedRisk =
      model.benefit * (trueRisk - model.threshold) := by
  have h_pred_not_high' : ¬ model.threshold < predictedRisk := by
    simpa [classifiedHighRisk] using h_pred_not_high
  unfold thresholdQalyLoss thresholdQalyGainUnderDecision
  simp [h_true_high, h_pred_not_high', model.harm_eq_threshold]
  ring_nf

/-- **Threshold QALY loss equals benefit-scaled threshold-decision regret.**
    This is the exact one-step specialization of the general longitudinal QALY
    regret model. -/
theorem thresholdQalyLoss_eq_benefit_mul_thresholdDecisionRegretMargin
    (model : ThresholdTreatmentModel) (trueRisk predictedRisk : ℝ) :
    thresholdQalyLoss model trueRisk predictedRisk =
      model.benefit * thresholdDecisionRegretMargin model trueRisk predictedRisk := by
  by_cases h_pred : classifiedHighRisk model.threshold predictedRisk
  · by_cases h_true_low : trueRisk ≤ model.threshold
    · unfold thresholdDecisionRegretMargin
      rw [if_pos h_pred]
      rw [thresholdQalyLoss_false_positive_exact model trueRisk predictedRisk h_true_low h_pred]
      have hmax : max (model.threshold - trueRisk) 0 = model.threshold - trueRisk :=
        max_eq_left (by linarith)
      rw [hmax]
    · have h_true_high : model.threshold < trueRisk := by linarith
      have h_pred_high' : model.threshold < predictedRisk := by
        simpa [classifiedHighRisk] using h_pred
      have h_zero : thresholdQalyLoss model trueRisk predictedRisk = 0 := by
        unfold thresholdQalyLoss thresholdQalyGainUnderDecision
        simp [h_true_high, h_pred_high', model.harm_eq_threshold]
      unfold thresholdDecisionRegretMargin
      rw [if_pos h_pred]
      rw [h_zero]
      have hmax : max (model.threshold - trueRisk) 0 = 0 :=
        max_eq_right (by linarith)
      rw [hmax]
      ring
  · by_cases h_true_high : model.threshold < trueRisk
    · unfold thresholdDecisionRegretMargin
      rw [if_neg h_pred]
      rw [thresholdQalyLoss_false_negative_exact model trueRisk predictedRisk h_true_high h_pred]
      have hmax : max (trueRisk - model.threshold) 0 = trueRisk - model.threshold :=
        max_eq_left (by linarith)
      rw [hmax]
    · have h_true_low : trueRisk ≤ model.threshold := by linarith
      have h_pred_not_high' : ¬ model.threshold < predictedRisk := by
        simpa [classifiedHighRisk] using h_pred
      have h_zero : thresholdQalyLoss model trueRisk predictedRisk = 0 := by
        unfold thresholdQalyLoss thresholdQalyGainUnderDecision
        simp [h_true_high, h_pred_not_high']
      unfold thresholdDecisionRegretMargin
      rw [if_neg h_pred]
      rw [h_zero]
      have hmax : max (trueRisk - model.threshold) 0 = 0 :=
        max_eq_right (by linarith)
      rw [hmax]
      ring

/-- Threshold-specialized QALY loss is always nonnegative. -/
theorem thresholdQalyLoss_nonneg
    (model : ThresholdTreatmentModel) (trueRisk predictedRisk : ℝ) :
    0 ≤ thresholdQalyLoss model trueRisk predictedRisk := by
  rw [thresholdQalyLoss_eq_benefit_mul_thresholdDecisionRegretMargin]
  have h_margin_nonneg :
      0 ≤ thresholdDecisionRegretMargin model trueRisk predictedRisk := by
    unfold thresholdDecisionRegretMargin
    by_cases h_pred : classifiedHighRisk model.threshold predictedRisk
    · rw [if_pos h_pred]
      exact le_max_right _ _
    · rw [if_neg h_pred]
      exact le_max_right _ _
  exact mul_nonneg model.benefit_pos.le h_margin_nonneg

/-- **Threshold-specialized QALY loss is zero under perfect calibration at the
    decision point.** -/
theorem thresholdQalyLoss_eq_zero_of_perfect_calibration
    (model : ThresholdTreatmentModel) (trueRisk predictedRisk : ℝ)
    (h_cal : predictedRisk = trueRisk) :
    thresholdQalyLoss model trueRisk predictedRisk = 0 := by
  subst h_cal
  unfold thresholdQalyLoss
  ring

/-- **Miscalibration-induced overtreatment has an exact threshold QALY cost.**
    A positive intercept shift that pushes a truly low-risk patient above the
    treatment threshold creates a false positive treatment decision, and the
    resulting regret is exactly the false-positive QALY loss. -/
theorem miscalibration_induced_false_positive_qaly_loss
    (model : ThresholdTreatmentModel) (trueRisk c : ℝ)
    (h_truly_low : trueRisk < model.threshold)
    (h_miscal : model.threshold - trueRisk < c) :
    thresholdQalyLoss model trueRisk (trueRisk + c) =
      model.benefit * (model.threshold - trueRisk) := by
  have h_decision :=
    miscalibration_changes_decisions trueRisk model.threshold c h_truly_low h_miscal
  exact thresholdQalyLoss_false_positive_exact
    model trueRisk (trueRisk + c) (le_of_lt h_truly_low) h_decision.2

/-- **Expected threshold-specialized QALY loss from miscalibration.**

    Empirical status: UNTESTED. -/
noncomputable def expectedThresholdQalyLoss {Z : Type*} [MeasurableSpace Z]
    (μ : Measure Z) (model : ThresholdTreatmentModel)
    (trueRisk predictedRisk : Z → ℝ) : ℝ :=
  ∫ z, thresholdQalyLoss model (trueRisk z) (predictedRisk z) ∂μ

/-- The expected loss under the threshold specialization agrees exactly with
    the general pathway expected loss. -/
theorem expectedQalyLoss_threshold_eq_expectedThresholdQalyLoss
    {Z : Type*} [MeasurableSpace Z]
    (μ : Measure Z) (model : ThresholdTreatmentModel)
    (trueRisk predictedRisk : Z → ℝ) :
    expectedQalyLoss μ (thresholdLongitudinalModel model)
      (fun z ↦ thresholdClinicalPathway model (trueRisk z))
      (fun z ↦ thresholdClinicalPathway model (predictedRisk z)) =
        expectedThresholdQalyLoss μ model trueRisk predictedRisk := by
  unfold expectedQalyLoss expectedThresholdQalyLoss
  refine integral_congr_ae ?_
  exact Filter.Eventually.of_forall (fun z ↦
    qalyLoss_threshold_eq_thresholdQalyLoss
      model (trueRisk z) (predictedRisk z))

/-- Perfect calibration implies zero expected threshold-specialized QALY loss. -/
theorem expectedThresholdQalyLoss_eq_zero_of_perfect_calibration
    {Z : Type*} [MeasurableSpace Z]
    (μ : Measure Z) (model : ThresholdTreatmentModel)
    (trueRisk predictedRisk : Z → ℝ)
    (h_cal : ∀ z, predictedRisk z = trueRisk z) :
    expectedThresholdQalyLoss μ model trueRisk predictedRisk = 0 := by
  unfold expectedThresholdQalyLoss
  have hfun :
      (fun z ↦ thresholdQalyLoss model (trueRisk z) (predictedRisk z)) =
        fun _ ↦ (0 : ℝ) := by
    funext z
    exact thresholdQalyLoss_eq_zero_of_perfect_calibration
      model (trueRisk z) (predictedRisk z) (h_cal z)
  rw [hfun]
  simp

/-- **Expected threshold-specialized QALY loss is the expected
    threshold-decision regret.** -/
theorem expectedThresholdQalyLoss_eq_expected_thresholdDecisionRegret
    {Z : Type*} [MeasurableSpace Z]
    (μ : Measure Z) (model : ThresholdTreatmentModel)
    (trueRisk predictedRisk : Z → ℝ) :
    expectedThresholdQalyLoss μ model trueRisk predictedRisk =
      ∫ z, model.benefit *
        thresholdDecisionRegretMargin model (trueRisk z) (predictedRisk z) ∂μ := by
  unfold expectedThresholdQalyLoss
  refine integral_congr_ae ?_
  exact Filter.Eventually.of_forall (fun z ↦
    thresholdQalyLoss_eq_benefit_mul_thresholdDecisionRegretMargin
      model (trueRisk z) (predictedRisk z))

end DecisionImplications

end Descent
