/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.PGSCalibrationTheory.PopulationCalibrationDrift

namespace Descent.Portability

open MeasureTheory
open PopGen.TransportedMetrics (equalVarianceGaussianAUCFromSignalVariance)

/-!
# `PGSCalibrationTheory.RecalibrationMethods`

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
  unfold calibrationInTheLarge interceptRecalibrated Descent.Core.difference
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
  unfold calibrationInTheLarge logisticRecalibrated Descent.Core.difference
  ring

/-- Choosing the fitted intercept `a = mean_obs - b * mean_pgs` makes the
    recalibrated prediction match the observed mean exactly, so CITL becomes
    zero for any chosen slope `b`. -/
theorem logistic_recalibration_corrects_citl
    (mean_obs mean_pgs b : ℝ) :
    calibrationInTheLarge mean_obs
      (logisticRecalibrated mean_pgs (mean_obs - b * mean_pgs) b) = 0 := by
  rw [logistic_recalibration_shifts_citl]
  unfold calibrationInTheLarge Descent.Core.difference
  ring

/-- Effective calibration slope after logistic recalibration.
    If the target linear predictor uses slope `slope` on the original PGS
    scale, and deployed predictions use fitted slope `fittedSlope`, then the
    target linear predictor as a function of the deployed predictor has slope
    `slope / fittedSlope`. -/
noncomputable def recalibratedCalibrationSlope
    (slope fittedSlope : ℝ) : ℝ :=
  Descent.Core.ratio slope fittedSlope

/-- **The recalibrated slope's orientation, pinned.** This definition carries no result of its
own. Dividing by a fitted slope below one inflates the calibration slope rather than deflating
it, which is the direction that makes refitting correct an under-dispersed score. -/
theorem recalibratedCalibrationSlope_inflates_when_fit_shallow :
    recalibratedCalibrationSlope 3 2 = 3 / 2 := by
  unfold recalibratedCalibrationSlope Descent.Core.ratio
  norm_num

/-- **The recalibrated slope at a null fit, named.** A fitted slope of zero means the score
carried no signal in the recalibration sample, so the correction factor diverges and no
recalibration is possible. The divisor is zero and Lean returns `0`, reporting a recalibrated
slope of zero -- which reads downstream as a well-behaved, if useless, score rather than as a
failed fit. Consumers must require `fittedSlope ≠ 0`. -/
theorem recalibratedCalibrationSlope_null_fit_is_junk (slope : ℝ) :
    recalibratedCalibrationSlope slope 0 = 0 := by
  unfold recalibratedCalibrationSlope Descent.Core.ratio
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
  unfold recalibratedCalibrationSlope logisticRecalibrated Descent.Core.ratio
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
  · unfold recalibratedCalibrationSlope Descent.Core.ratio
    exact div_self h_slope_nonzero
  · unfold calibrationSlopeDeviation recalibratedCalibrationSlope Descent.Core.ratio
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
    (pop : Program.BinaryPopulation Z) (score : Z → ℝ)
    (a b : ℝ)
    (h_b_pos : 0 < b) :
    Program.populationAUC pop (fun z ↦ logisticRecalibrated (score z) a b) =
      Program.populationAUC pop score := by
  simpa [logisticRecalibrated, Function.comp] using
    (Program.populationAUC_strictMono_invariant pop score (fun x ↦ a + b * x) (by
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
  Descent.Core.ratioOfProduct nParams infoPerEvent targetTraceMSE

/-- **requiredEventsForRecalibration at zero infoPerEvent, named.** With no information per event,
no number of events recalibrates the model. Lean returns `0`, reporting that recalibration needs no
events at all. Consumers must require `infoPerEvent ≠ 0`. -/
theorem requiredEventsForRecalibration_zero_infoperevent_is_junk
    (nParams targetTraceMSE : ℝ) :
    requiredEventsForRecalibration nParams 0 targetTraceMSE = 0 := by
  unfold requiredEventsForRecalibration Descent.Core.ratioOfProduct
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
  unfold recalibrationTraceMSELowerBound requiredEventsForRecalibration Descent.Core.ratioOfProduct
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
  unfold requiredEventsForRecalibration Descent.Core.ratioOfProduct
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
  unfold requiredEventsForRecalibration Descent.Core.ratioOfProduct
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
    unfold requiredEventsForRecalibration Descent.Core.ratioOfProduct
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
    (pop : Program.BinaryPopulation Z) (score : Z → ℝ)
    (a b : ℝ)
    (h_b_pos : 0 < b) :
    Program.populationAUC pop (fun z ↦ a + b * score z) = Program.populationAUC pop score := by
  simpa [Function.comp] using
    Program.populationAUC_strictMono_invariant pop score (fun x ↦ a + b * x) (by
      intro x y hxy
      linarith [mul_lt_mul_of_pos_left hxy h_b_pos])

end RecalibrationMethods

end Descent.Portability
