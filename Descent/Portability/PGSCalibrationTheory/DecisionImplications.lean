/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.PGSCalibrationTheory.RecalibrationMethods

namespace Descent.Portability

open MeasureTheory
open PopGen.TransportedMetrics (equalVarianceGaussianAUCFromSignalVariance)

/-!
# `PGSCalibrationTheory.DecisionImplications`

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

    The identity gate: the prior-free `f_e / (f_e + f_n)` — the same ratio with the cohort
    prevalence dropped, which is the ordinary base-rate mistake — is
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

/-- The expected loss under the threshold specialization agrees exactly with the general pathway
expected loss. -/
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

end Descent.Portability
