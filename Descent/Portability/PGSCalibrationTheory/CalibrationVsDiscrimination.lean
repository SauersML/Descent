/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.PGSCalibrationTheory.CalibrationDefinitions
-- Importing `Descent.Portability.PortabilityDrift` instead would be importing the chapter
-- head, and the head sits above the whole six-module drift recurrence: `Definitions` ->
-- `ClosedPopulationRegime` -> `PresentDayMetrics` -> `MutationDrift` -> `MigrationDrift` ->
-- `MigrationDriftRecurrence`.  This file names nothing from the last three.  Everything it
-- does name is declared in `PresentDayMoments` (21 declarations), `PresentDayMetrics` (14)
-- and `Generational` (2), and `PresentDayMoments` imports the other two -- so one specific
-- import reaches every symbol the head was being asked for, and stops charging this file a
-- rebuild whenever a migration recurrence it never mentions changes.
import Descent.Portability.PortabilityDrift.PresentDayMoments
-- `BinaryPopulation`, `populationAUC` and `populationAUC_strictMono_invariant` are named
-- below, so the module declaring them is imported directly rather than reached along a
-- path that runs through some other chapter's head.
import Descent.Portability.PopulationAUC

assert_below Descent.Decision Descent.Program

namespace Descent.Portability

open MeasureTheory
open PopGen.TransportedMetrics (equalVarianceGaussianAUCFromSignalVariance)

/-!
# `PGSCalibrationTheory.CalibrationVsDiscrimination`

Part of the split of `Descent/Portability/PGSCalibrationTheory.lean`, which was 3,689 lines.

The parts are a FAN: each imports the parts that declare the symbols it names, and nothing
else. The split first made them a CHAIN -- each importing the one before, in the order the
original text ran -- which preserved every resolution the single file had and charged every
part a dependency on everything written above it, used or not. Recovering the real order is
the work that chain deferred: each part's identifiers were resolved against its siblings'
declarations, and the imports above are the answer, so what a part rests on is readable
from its header instead of inherited from its position in a file that no longer exists.

Where a cut falls inside a section, the section is reopened and reclosed by name. A section
scopes `variable`s and this file declares none at that level, so the reopening is exact.
-/


/-- Logistic-scale prevalence log-odds.

    Empirical status: **VALIDATED**
    (`validation/empirical/simcov/battery_bulk6.py`,
    `test_prevalence_logit`). The oracle is the fitted intercept of an
    intercept-only logistic model on four million simulated binary outcomes,
    which is what a calibration-in-the-large is read off in practice; worst 2.66
    sems over a prediction spanning -3.89182 to -0.61904.

    Power: the prediction spans -3.89182 to -0.61904 across the design. -/
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

/-- Reference evaluation; see `Descent.Core.Ratios` for what these pin and why. -/
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
  · unfold calibrationInTheLarge Descent.Core.difference
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
  unfold calibrationInTheLarge Descent.Core.difference
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

/-! ### The observed-mean shift law, written once

Two calibration models in this file carry the same three shift channels and compute the
same two quantities from them. They are different models -- one is a scalar shift record,
the other carries an SNP-level transport state -- but the LAW relating a base mean, three
shift channels and a population to an observed mean is one law, and it was written twice.

`CrossPopulationGenerationalCalibrationModel` is the third model in this file and does
NOT share it: it derives its shifts from a generational process rather than carrying them
as fields, which is the distinction the two functions below make visible. -/

/-- **Total observed-mean shift**, the three channels summed.

The channels are named rather than pooled because a calibration failure attributable to
prevalence is a different finding from one attributable to a genetic mean difference, and
a model that carried only the total could not tell them apart. -/
noncomputable def totalObservedMeanShift
    (prevalence environmental genetic : ℝ) : ℝ :=
  Descent.Core.sum3 prevalence environmental genetic

/-- **Each channel is attributable, and carries no cross term.**

Zeroing one channel moves the budget by the `Descent.Core.difference` of exactly that
channel, whatever the other two carry. This is the property the three names exist to
provide: a calibration failure can be charged to prevalence, to environment or to genetics
by reading one channel, without first knowing the others. A budget that let the channels
interact would still have three names and no attribution behind them. -/
theorem totalObservedMeanShift_channel_attribution
    (prevalence environmental genetic : ℝ) :
    Descent.Core.difference (totalObservedMeanShift prevalence environmental genetic)
        (totalObservedMeanShift 0 environmental genetic) = prevalence ∧
    Descent.Core.difference (totalObservedMeanShift prevalence environmental genetic)
        (totalObservedMeanShift prevalence 0 genetic) = environmental ∧
    Descent.Core.difference (totalObservedMeanShift prevalence environmental genetic)
        (totalObservedMeanShift prevalence environmental 0) = genetic := by
  unfold totalObservedMeanShift Descent.Core.sum3 Descent.Core.difference
  refine ⟨by ring, by ring, by ring⟩

/-- **Observed mean in a population**: the base mean, shifted in the target only.

`Pop.pair 0 shift` is the asymmetry -- the reference population is where the base mean was
measured, so it takes no shift by construction. Writing it this way rather than as two
fields is what stops a source and a target formula drifting apart. -/
noncomputable def shiftedObservedMean (baseMean shift : ℝ) (P : Pop) : ℝ :=
  baseMean + Pop.pair 0 shift P

/-- **No shift, no difference between the populations.** The anchor: a model with all
three channels at zero reports the same observed mean in both. -/
@[simp] theorem shiftedObservedMean_at_zero (baseMean : ℝ) (P : Pop) :
    shiftedObservedMean baseMean 0 P = baseMean := by
  unfold shiftedObservedMean
  cases P <;> simp

/-- **The reference population never shifts**, whatever the channels carry. -/
@[simp] theorem shiftedObservedMean_source (baseMean shift : ℝ) :
    shiftedObservedMean baseMean shift Pop.source = baseMean := by
  unfold shiftedObservedMean; simp

/-- Total target observed-mean shift relative to source. -/
noncomputable def CrossPopulationCalibrationShiftModel.observedMeanShift
    (m : CrossPopulationCalibrationShiftModel) : ℝ :=
  totalObservedMeanShift m.prevalenceShift m.environmentalObservedShift
    m.geneticObservedShift

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
  shiftedObservedMean m.baseObservedMean m.observedMeanShift P

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
  simp [CrossPopulationCalibrationShiftModel.observedMean,
      totalObservedMeanShift, shiftedObservedMean,
      Descent.Core.sum3]

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
    CrossPopulationCalibrationShiftModel.predictedMean, CalibrationMoments.shifted,
      totalObservedMeanShift, shiftedObservedMean,
      Descent.Core.sum3]

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
    add_comm,
      totalObservedMeanShift, shiftedObservedMean,
      Descent.Core.sum3]

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
    h_env, h_genetic, h_score, h_intercept,
      totalObservedMeanShift, shiftedObservedMean,
      Descent.Core.sum3]

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
    h_env, h_genetic, h_score, h_intercept,
      totalObservedMeanShift, shiftedObservedMean,
      Descent.Core.sum3]

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
    CrossPopulationCalibrationShiftModel.predictedMeanShift, h_prev,
      totalObservedMeanShift, shiftedObservedMean,
      Descent.Core.sum3]
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
  totalObservedMeanShift m.prevalenceShift m.environmentalObservedShift
    m.geneticObservedShift

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
  shiftedObservedMean m.baseObservedMean m.observedMeanShift P

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
    CrossPopulationCalibrationShiftModel.observedMeanShift, add_assoc,
      totalObservedMeanShift, shiftedObservedMean,
      Descent.Core.sum3]

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

/-- **Cross between the mechanistic calibration state and the shift model it induces.**

A mechanistic calibration state and its induced shift model carry the same mean-shift budget in
differently named fields, so a law proved on one layer is transported to the other by
normalising both through the same chain: the induced shift model, the observed- and score-mean
shifts as each layer spells them, and the three-way observed shift underneath both. That chain
is the crossing, and it is the same one at every law that crosses. What a law needs beyond the
mean-shift plumbing -- a calibration profile to open, an associativity step -- it passes in,
and the transported fact is the `using` term. -/
macro "mechanistic_shift_budget" ms:Lean.Parser.Tactic.simpLemma,* " using " e:term : tactic =>
  `(tactic| simpa [$ms,*,
      CrossPopulationMechanisticCalibrationModel.toShiftModel,
      CrossPopulationMechanisticCalibrationModel.observedMeanShift,
      CrossPopulationMechanisticCalibrationModel.scoreMeanShift,
      CrossPopulationCalibrationShiftModel.observedMeanShift,
      CrossPopulationCalibrationShiftModel.predictedMeanShift,
      totalObservedMeanShift, shiftedObservedMean, Descent.Core.sum3] using $e)

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
      CalibrationMoments.toProfile, Descent.Portability.calibrationProfile,
      calibrationSlopeFromSourceWeights, calibrationInTheLarge,
      Descent.Core.difference,
      totalObservedMeanShift, shiftedObservedMean,
      Descent.Core.sum3]

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
      Descent.Portability.calibrationProfile, calibrationSlopeFromSourceWeights,
      calibrationInTheLarge, sub_eq_add_neg, add_assoc,
      Descent.Core.difference] <;> ring

/-- Exact mechanistic CITL law: calibration-in-the-large is source CITL plus
observed-mean drift minus the source-weighted score-mean drift and deployment
intercept drift. -/
theorem target_profile_citl_eq_source_profile_citl_add_exact_biological_shift_budget
    {p q : ℕ} (m : CrossPopulationMechanisticCalibrationModel p q)
    (link : CalibrationLink) :
    (m.calibrationProfile Pop.target link).citl =
      (m.calibrationProfile Pop.source link).citl +
        m.observedMeanShift - (m.scoreMeanShift + m.deploymentInterceptShift) := by
  mechanistic_shift_budget
    CrossPopulationMechanisticCalibrationModel.calibrationProfile using
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
    (sourceMetrics targetMetrics : PopGen.TransportedMetrics.Profile) : Prop :=
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

- `targetMetrics.auc < sourceMetrics.auc`
  both come from `h_r2_drop`, which *assumes* the target R² is lower. Nothing here shows
  that cross-ancestry transport lowers R². What is proved is that a drop in R² propagates
  to AUC and to calibrated Brier through the monotone charts — a real and reusable step,
  but a conditional one.
- `|sourceProfile.citl| < |targetProfile.citl|` is immediate from `h_src_cal`, which
  assumes the source is perfectly calibrated in the large, together with `h_shift_nonzero`. Against
  a source CITL pinned to `0`, any nonzero shift is worse.

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
        (targetMetricProfileFromSourceWeights metric) := by
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
  exact ⟨h_auc, h_citl_eq, h_abs_eq, h_abs_worse⟩

/-- **Exact cross-ancestry metric portability law from the mechanistic
SNP-level transport model and mechanistic calibration state.**

This is the headline law surface for deployed metrics:

- AUC is the mechanistic source-vs-target AUC from the explicit
  source-weights-on-target-covariance score equation;
- CITL is the exact biological mean-shift budget
  `observed drift - source-weighted score-mean drift - deployment intercept drift`;
- calibration slope is the literal transported `Cov/Var` ratio on the same
  score equation; and
- calibration slope is the literal transported `Cov/Var` ratio on the same score equation.

The same reading applies as for `source_to_target_exact_metric_profile_from_shift_budget`,
which this theorem is a mechanistic instance of: the AUC drop is carried by the hypothesis
`h_r2_drop`, and the calibration worsening by `h_src_cal` together with `h_shift_nonzero`.
"Exact" qualifies the formulae for CITL and slope, which are computed from the SNP-level
state, not the direction of the metric changes, which are assumed.

The profile's `brier` coordinate is not ordered here: `liabilityBrierExact` needs Slepian-type
monotonicity of the bivariate normal orthant, which Mathlib does not carry. -/
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
    |sourceProfile.citl| < |targetProfile.citl| := by
  have h_target_mean_eq_prevalence_shift :
      (cal.toShiftModel.observedMean Pop.target) = cal.metric.targetPrevalence := by
    simpa [CrossPopulationMechanisticCalibrationModel.toShiftModel,
      CrossPopulationMechanisticCalibrationModel.observedMean,
      CrossPopulationMechanisticCalibrationModel.observedMeanShift,
      CrossPopulationCalibrationShiftModel.observedMean,
      CrossPopulationCalibrationShiftModel.observedMeanShift,
      totalObservedMeanShift, shiftedObservedMean,
      Descent.Core.sum3] using
      h_target_mean_eq_prevalence
  have h_src_cal_shift :
      ((cal.toShiftModel.identityCalibrationProfile Pop.source)).citl = 0 := by
    simpa only [CrossPopulationMechanisticCalibrationModel.identityCalibrationProfile,
      CrossPopulationMechanisticCalibrationModel.calibrationProfile,
      CrossPopulationCalibrationShiftModel.identityCalibrationProfile] using h_src_cal
  have h_shift_nonzero_shift :
      cal.toShiftModel.observedMeanShift - cal.toShiftModel.predictedMeanShift ≠ 0 := by
    mechanistic_shift_budget sub_eq_add_neg, add_assoc using h_shift_nonzero
  have h_main :=
    source_to_target_exact_metric_profile_from_shift_budget cal.metric cal.toShiftModel
      h_target_mean_eq_prevalence_shift h_source_r2_unit h_target_r2_unit h_r2_drop
      h_src_cal_shift h_shift_nonzero_shift
  unfold AucDropsAndCitlWorsens at h_main
  dsimp at h_main ⊢
  obtain ⟨h_auc, h_citl, h_abs, h_worse⟩ := h_main
  refine ⟨h_auc, ?_, ?_, ?_⟩
  · mechanistic_shift_budget
      CrossPopulationMechanisticCalibrationModel.identityCalibrationProfile,
      CrossPopulationMechanisticCalibrationModel.calibrationProfile using h_citl
  · mechanistic_shift_budget
      CrossPopulationMechanisticCalibrationModel.identityCalibrationProfile,
      CrossPopulationMechanisticCalibrationModel.calibrationProfile using h_abs
  · exact h_worse

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
    CrossPopulationMechanisticCalibrationModel.observedMeanShift, add_assoc,
      totalObservedMeanShift, shiftedObservedMean,
      Descent.Core.sum3]

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
    calibrationSlopeFromSourceWeights,
      totalObservedMeanShift, shiftedObservedMean,
      Descent.Core.sum3]

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
    CrossPopulationMechanisticCalibrationModel.identityCalibrationProfile,
      totalObservedMeanShift, shiftedObservedMean,
      Descent.Core.sum3] using
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
          PopGen.TransportedMetrics.equalVarianceGaussianAUCFromSignalVariance
            ((predictiveCovarianceFromSourceWeights (m.metric.toMetricModelAt t) Pop.target) ^ 2 /
              scoreVarianceFromSourceWeights (m.metric.toMetricModelAt t) Pop.target)
            (effectiveOutcomeVariance (m.metric.toMetricModelAt t) Pop.target -
              (predictiveCovarianceFromSourceWeights (m.metric.toMetricModelAt t) Pop.target) ^ 2 /
                scoreVarianceFromSourceWeights (m.metric.toMetricModelAt t) Pop.target)
      , brier :=
          PopGen.TransportedMetrics.liabilityBrierExact
            (m.metric.outcome.targetPrevalenceAt t)
            (r2FromSourceWeights (m.metric.toMetricModelAt t) Pop.target) } ∧
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
      h_env, h_genetic, h_score, h_intercept, h_prev_shift,
      totalObservedMeanShift, shiftedObservedMean,
      Descent.Core.sum3]
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
      targetCalibratedBrierRisk π V_A V_E fstTarget := by
  constructor
  · exact targetAUC_lt_source_of_neutralAF_benchmark
      V_A V_E fstSource fstTarget hVA hVE h_fst h_fst_bounds
  · exact targetBrier_strict_gt_source_of_neutralAF_benchmark π V_A V_E fstSource fstTarget
      hπ0 hπ1 hVA hVE h_fst h_fst_bounds

end CalibrationVsDiscrimination

end Descent.Portability
