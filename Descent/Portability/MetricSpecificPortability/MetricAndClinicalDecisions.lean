/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.MetricSpecificPortability.PrecisionRecall
import Descent.Layer

assert_below Descent.Decision

-- LAYER DEBT. This file cannot yet assert it is below `Descent.Program`:
--   Program: reaches 2 module(s) -- `Descent.Program.Conclusions`, `Descent.Program.OpenQuestions`
-- The repair is to move what it reaches for DOWN, not to move this file up.

namespace Descent.Portability

open MeasureTheory

/-!
# `MetricSpecificPortability.MetricAndClinicalDecisions`

Part of the split of `Descent/Portability/MetricSpecificPortability.lean`, which was 3,946 lines.

The parts are a FAN, not a chain. The head carries the definitions and every import the
subsystem draws on from outside it; each other part imports the head and whichever siblings
actually declare the names it uses. The split first laid the parts out as a chain, each
importing the one before in the order the original was written, which made every part
transitively downstream of everything written earlier -- so the depth of the corpus was a
function of the length of a file rather than of what depends on what. The order here was
recovered by resolving each name a part references back to the sibling that declares it.

Where a cut falls inside a section, the section is reopened and reclosed by name. A section
scopes `variable`s and this file declares none at that level, so the reopening is exact.
-/



/-!
## Metric Choice Affects Clinical Decision-Making

Different metrics lead to different clinical decisions, so metric-
specific portability has direct practical consequences.
-/

section MetricAndClinicalDecisions

/-- **Screening PPV shifts even when case-finding sensitivity is unchanged.**
    Under a pure prevalence shift with identical sensitivity and specificity, the PPV
    portability gap is strictly positive and the higher-prevalence use case has strictly
    higher PPV. This is the metric split relevant to screening versus case-finding use
    cases.

    Do not write the first conjunct as `sensitivityPortabilityGap se se <
    ppvPortabilityGap …`: that spells `0` as `|se - se|`. The sensitivity half is
    `sensitivityPortabilityGap_self`, an identity, not a consequence of the prevalence
    shift. -/
theorem different_uses_different_metrics
    (se sp K_source K_target : ℝ)
    (h_se : 0 < se) (h_sp1 : sp < 1)
    (h_Ks : 0 < K_source) (h_Ks' : K_source < 1)
    (h_Kt' : K_target < 1)
    (h_order : K_source < K_target) :
    0 < ppvPortabilityGap se sp K_source K_target ∧
    metricPPV se sp K_source < metricPPV se sp K_target := by
  constructor
  · exact ppv_gap_pos_under_prevalence_shift
      se sp K_source K_target h_se h_sp1 h_Ks h_Ks' h_Kt' h_order
  · exact ppv_increases_with_prevalence
      se sp K_source K_target h_se h_sp1 h_Ks h_Ks' h_Kt' h_order

/-! ### What the metric split is, and is not

This module's headline is that metric choice changes the portability verdict, and
`different_uses_different_metrics` is the exhibit. The Gaussian level-set collapse of
`Descent.Spectral.FoldedSpectrum` sharpens that claim, and in doing so narrows it.

**The collapse.** Every *level-set functional* -- any threshold-based readout metric:
sensitivity, specificity, any exceedance probability, any quantile -- factors through
exactly two numbers of the transferred pair, the correlation drop and the variance ratio
(`LevelSetCoordinates`). So two deployments whose readouts agree in those two coordinates
agree in **every** threshold metric at once (`levelSet_metrics_agree_of_coords_eq`). No
choice among threshold metrics can separate them.

**What that does to the headline.** Prevalence is not one of the two coordinates. It is a
property of the outcome marginal, not of the readout. `metricPPV` reads it; sensitivity and
specificity do not. So the split this module exhibits is **not** a disagreement between
metrics at fixed readout -- the collapse forbids that -- it is the difference between a
metric that reads prevalence and metrics that do not.

That is a real narrowing, and it is the useful form for a reader deciding what to report:
holding the readout fixed, swapping one threshold metric for another cannot reverse a
portability verdict. To get a reversal you need either a prevalence shift (this module's
route) or the two coordinates to order oppositely
(`FoldedSpectrum.no_levelSet_reversal_of_aligned_coordinates`, the "only if" half). Metric
choice on its own is not a mechanism.

The theorem below states exactly this and no more. Note which parts come from where: the
first two conjuncts are the collapse and are **not provable in this file**; the last two are
this file's own `metricPPV` facts. -/

/-- A screening deployment: the two readout-side coordinates a threshold metric can see,
plus the prevalence, which is outcome-side and which the collapse does not contain. -/
structure ScreeningDeployment where
  /-- The readout-side coordinates: correlation drop and variance ratio. -/
  readout : Spectral.LevelSetCoordinates
  /-- Outcome-side base rate. Deliberately **not** part of `readout`. -/
  prevalence : ℝ

/-- **Two deployments sharing a readout and differing only in prevalence.**

The result below is that everything separating a pair of deployments here is a
prevalence effect; stated over the class alone it is a conditional about objects
none of which had been exhibited. This is the pair the statement is about, built
so that the shared readout is shared BY CONSTRUCTION rather than by hypothesis
-- which is the point, since the readout is what threshold metrics factor
through and the prevalence is what they do not.

    Empirical status: NOT AN EMPIRICAL CLAIM -- a pair of deployment records. The
    claim with content is that real source and target deployments differ this
    way, which this does not assert. -/
def ScreeningDeployment.atPrevalence (readout : Spectral.LevelSetCoordinates)
    (prevalence : ℝ) : ScreeningDeployment where
  readout := readout
  prevalence := prevalence

instance ScreeningDeployment.instNonempty : Nonempty ScreeningDeployment :=
  ⟨ScreeningDeployment.atPrevalence Spectral.LevelSetCoordinates.undegraded 0⟩

/-- The constructed pair does share its readout, so the shared-readout hypothesis
of the split result is discharged rather than assumed for this family. -/
theorem ScreeningDeployment.atPrevalence_readout_eq (readout : Spectral.LevelSetCoordinates)
    (prevalence prevalence' : ℝ) :
    (ScreeningDeployment.atPrevalence readout prevalence).readout =
      (ScreeningDeployment.atPrevalence readout prevalence').readout := rfl

/-- **The metric split is a prevalence effect, not a metric-choice effect.**

`sens` and `spec` are any threshold metrics of the readout, i.e. any level-set functionals
of the two coordinates. Given two deployments with the *same* readout coordinates:

* they agree in sensitivity and in specificity -- and this is the part that needs
  `Descent.Spectral.FoldedSpectrum`, since it holds for *every* level-set functional at once, not
  because of anything about these two in particular;
* at equal prevalence they therefore agree in PPV as well, so no threshold metric separates
  them at all;
* and a strict prevalence increase strictly raises PPV, which is the split
  `different_uses_different_metrics` reports.

Read together: everything that moves here moves because prevalence moved. Delete
`FoldedSpectrum` and the first conjunct has no proof.

**SCOPE, NARROWED AGAINST MEASUREMENT: this is about DISCRIMINATION metrics, not
"threshold metrics" in general, and it is FALSE for proper scoring rules.**

Murphy's decomposition is `Brier = reliability - resolution + uncertainty`. Resolution and
AUC both collapse onto `(R², prevalence)`, so the statement above covers them — but
**reliability is calibration, and it is a free third coordinate that neither readout
coordinate sees.**

Demonstrated by holding `R²` and prevalence fixed and varying only the score-to-probability
map through strictly monotone maps, which by construction cannot change any ranking:

* AUC spread **exactly 0.00**;
* resolution spread **exactly 0.00**;
* Brier spread **0.0162**, of which **0.0162 is the reliability term**.

The same split appears in the `sims/` data: `R²` alone explains `94.6%` of within-cell AUC
variance and only `67%` of Brier.

So this theorem is right about AUC, sensitivity, specificity and PPV, and **wrong about
Brier, the log score, and every proper scoring rule** — each carries a reliability term
invisible to both coordinates. A monotone recalibration moves a proper scoring rule while
leaving every quantity in this theorem's conclusion fixed. -/
theorem metric_split_is_prevalence_not_metric_choice
    (sens spec : ScreeningDeployment → ℝ)
    (hsens : Spectral.IsLevelSetFunctional sens ScreeningDeployment.readout)
    (hspec : Spectral.IsLevelSetFunctional spec ScreeningDeployment.readout)
    (d₁ d₂ : ScreeningDeployment)
    (hreadout : d₁.readout = d₂.readout) :
    sens d₁ = sens d₂ ∧
    spec d₁ = spec d₂ ∧
    (d₁.prevalence = d₂.prevalence →
      metricPPV (sens d₁) (spec d₁) d₁.prevalence =
        metricPPV (sens d₂) (spec d₂) d₂.prevalence) ∧
    (0 < sens d₁ → spec d₁ < 1 →
      0 < d₁.prevalence → d₁.prevalence < 1 → d₂.prevalence < 1 →
      d₁.prevalence < d₂.prevalence →
      metricPPV (sens d₁) (spec d₁) d₁.prevalence <
        metricPPV (sens d₂) (spec d₂) d₂.prevalence) := by
  -- The two agreements are the collapse, instantiated at this deployment type.
  have hs : sens d₁ = sens d₂ :=
    Spectral.levelSet_metrics_agree_of_coords_eq ScreeningDeployment.readout sens hsens d₁ d₂ hreadout
  have hp : spec d₁ = spec d₂ :=
    Spectral.levelSet_metrics_agree_of_coords_eq ScreeningDeployment.readout spec hspec d₁ d₂ hreadout
  refine ⟨hs, hp, ?_, ?_⟩
  · intro hK
    rw [hs, hp, hK]
  · intro h_se h_sp1 h_K1 h_K1' h_K2' h_order
    rw [← hs, ← hp]
    exact ppv_increases_with_prevalence _ _ _ _ h_se h_sp1 h_K1 h_K1' h_K2' h_order

/-- **The collapse, exhibited on a concrete pair of deployments.**

`metric_split_is_prevalence_not_metric_choice` is conditioned on two deployments
sharing a readout. `ScreeningDeployment.atPrevalence` builds exactly such a pair
-- same readout coordinates, different prevalence -- so the hypothesis is
discharged by construction rather than assumed, and the sensitivity/specificity
agreement becomes an unconditional statement about deployments that exist.

The scope narrowing on the theorem above carries over unchanged: this is about
discrimination metrics, and it is false for proper scoring rules, which carry a
reliability term neither readout coordinate sees. -/
theorem ScreeningDeployment.metric_split_atPrevalence
    (sens spec : ScreeningDeployment → ℝ)
    (hsens : Spectral.IsLevelSetFunctional sens ScreeningDeployment.readout)
    (hspec : Spectral.IsLevelSetFunctional spec ScreeningDeployment.readout)
    (readout : Spectral.LevelSetCoordinates) (prevalence prevalence' : ℝ) :
    sens (ScreeningDeployment.atPrevalence readout prevalence) =
        sens (ScreeningDeployment.atPrevalence readout prevalence') ∧
      spec (ScreeningDeployment.atPrevalence readout prevalence) =
        spec (ScreeningDeployment.atPrevalence readout prevalence') := by
  have hsplit := metric_split_is_prevalence_not_metric_choice sens spec hsens hspec
    (ScreeningDeployment.atPrevalence readout prevalence)
    (ScreeningDeployment.atPrevalence readout prevalence') rfl
  exact ⟨hsplit.1, hsplit.2.1⟩

/-- **Decision curve analysis: Brier score is population-specific (from definition).**
    At fixed prevalence, any nonzero `R²` shift induces a strictly positive
    absolute Brier portability gap. -/
theorem brier_portability_gap_positive_of_r2_shift
    (π r2_source r2_target : ℝ)
    (h_π : 0 < π) (h_π' : π < 1)
    (h_diff : r2_source ≠ r2_target) :
    0 < |brierFromR2 π r2_source - brierFromR2 π r2_target| := by
  have h_ne : brierFromR2 π r2_source ≠ brierFromR2 π r2_target := by
    unfold brierFromR2
    intro h
    apply h_diff
    have h_prev : 0 < π * (1 - π) := by nlinarith
    have h_prev_ne : π * (1 - π) ≠ 0 := ne_of_gt h_prev
    have := mul_left_cancel₀ h_prev_ne h
    linarith
  exact abs_pos.mpr (sub_ne_zero.mpr h_ne)

/-- **Lower target sensitivity and specificity reduce net benefit at a fixed
    decision threshold.** -/
theorem clinical_utility_threshold
    (sens_source spec_source sens_target spec_target π t : ℝ)
    (h_π : 0 < π) (h_π1 : π < 1)
    (ht : 0 < t) (ht1 : t < 1)
    (h_sens : sens_target < sens_source)
    (h_spec : spec_target < spec_source) :
    decisionCurveNetBenefit (sens_target * π) ((1 - spec_target) * (1 - π)) 1 t <
      decisionCurveNetBenefit (sens_source * π) ((1 - spec_source) * (1 - π)) 1 t := by
  rw [decisionCurveNetBenefit_eq_formula, decisionCurveNetBenefit_eq_formula]
  have h_threshold_weight_pos : 0 < t / (1 - t) := div_pos ht (by linarith)
  have h_tp : sens_target * π < sens_source * π :=
    mul_lt_mul_of_pos_right h_sens h_π
  have h_fp :
      (1 - spec_source) * (1 - π) <
        (1 - spec_target) * (1 - π) := by
    apply mul_lt_mul_of_pos_right
    · linarith
    · linarith
  have h_fp_weighted :
      (1 - spec_source) * (1 - π) * (t / (1 - t)) <
        (1 - spec_target) * (1 - π) * (t / (1 - t)) :=
    mul_lt_mul_of_pos_right h_fp h_threshold_weight_pos
  simp only [div_one]
  linarith

/-- **The exact mechanistic deployed metric profile can record joint loss in
`R²`, AUC, and Brier.**

This theorem is stated on the explicit SNP-level transport model rather than on
a drift benchmark. If the transported source weights lose explained
signal in the target population, then:

- target `R²` is strictly lower;
- exact target liability-threshold AUC is strictly lower; and
- exact target calibrated Brier is strictly worse when source and target are
  compared on the same target prevalence scale.

The point is that the repository's deployed metric profile can report joint
deterioration across discrimination- and calibration-sensitive metrics from the
same mechanistic target state. -/
theorem target_metrics_worse_of_r2_drop
    {p q : ℕ} (m : CrossPopulationMetricModel p q)
    (h_source_r2_unit : r2FromSourceWeights m Pop.source ∈ Set.Ico 0 1)
    (h_target_r2_unit : r2FromSourceWeights m Pop.target ∈ Set.Ico 0 1)
    (h_r2_drop : r2FromSourceWeights m Pop.target < r2FromSourceWeights m Pop.source) :
    let sourceMetrics := sourceMetricProfileFromSourceWeightsAtTargetPrevalence m
    let targetMetrics := targetMetricProfileFromSourceWeights m
    targetMetrics.r2 < sourceMetrics.r2 ∧
    targetMetrics.auc < sourceMetrics.auc ∧
    sourceMetrics.brier < targetMetrics.brier := by
  dsimp
  have h_auc :
      (targetMetricProfileFromSourceWeights m).auc <
        (sourceMetricProfileFromSourceWeightsAtTargetPrevalence m).auc := by
    rw [targetMetricProfileFromSourceWeights_auc,
      sourceMetricProfileFromSourceWeightsAtTargetPrevalence_auc,
      targetEqualVarianceGaussianAUCFromSourceWeights_eq_explainedR2_chart_of_lt_one
        m h_target_r2_unit.2,
      sourceEqualVarianceGaussianAUCFromSourceWeights_eq_explainedR2_chart_of_lt_one
        m h_source_r2_unit.2]
    exact equalVarianceGaussianAUCFromExplainedR2_strictMonoOn_unitInterval
      h_target_r2_unit h_source_r2_unit h_r2_drop
  have h_brier :
      (sourceMetricProfileFromSourceWeightsAtTargetPrevalence m).brier <
        (targetMetricProfileFromSourceWeights m).brier := by
    rw [sourceMetricProfileFromSourceWeightsAtTargetPrevalence_brier,
      targetMetricProfileFromSourceWeights_brier,
      sourceCalibratedBrierFromSourceWeightsAtPrevalence_eq_explainedR2_chart,
      targetCalibratedBrierFromSourceWeights_eq_explainedR2_chart]
    simpa [brierFromR2, sourceBrierFromR2, PopGen.TransportedMetrics.calibratedBrier] using
      brierFromR2_strictAnti m.targetPrevalence
        m.targetPrevalence_pos m.targetPrevalence_lt_one h_r2_drop
  exact ⟨h_r2_drop, h_auc, h_brier⟩

end MetricAndClinicalDecisions


/-!
## Proper Scoring Rules and Portability

Proper scoring rules incentivize honest probability assessments.
Their portability depends on the specific scoring rule used.
-/

section ProperScoringRules

/-- **Brier score is a proper scoring rule.**
    Brier(p, y) = (p - y)². The unique minimizer is p = P(Y=1|X). -/
noncomputable abbrev brierScoreMetric (p y : ℝ) : ℝ := Program.brierScore p y

/-- The local metric surface is exactly the core Brier score object from
    `Conclusions`. -/
@[simp] theorem brierScoreMetric_eq_core (p y : ℝ) :
    brierScoreMetric p y = Program.brierScore p y := by
  rfl

/-- Brier score is nonneg. -/
theorem brier_nonneg (p y : ℝ) : 0 ≤ brierScoreMetric p y := by
  simpa [brierScoreMetric, Program.brierScore] using sq_nonneg (y - p)

/-- **Brier score is bounded above by 1 (derived from definition).**
    Since `brierFromR2 π r2 = π(1-π)(1-r2)`, and π(1-π) ≤ 1/4 (AM-GM)
    and (1-r2) ≤ 1, the Brier score is bounded by 1/4.
    This contrasts with log loss which is unbounded.
    The boundedness means Brier's portability degradation is also bounded. -/
theorem brier_score_bounded
    (π r2 : ℝ)
    (h_π : 0 ≤ π) (h_π' : π ≤ 1)
    (h_r2 : 0 ≤ r2) (h_r2' : r2 ≤ 1) :
    brierFromR2 π r2 ≤ 1/4 := by
  unfold brierFromR2 PopGen.TransportedMetrics.calibratedBrier
  have h1 : π * (1 - π) ≤ 1/4 := by nlinarith [sq_nonneg (π - 1/2)]
  have h_one_minus_pi : 0 ≤ 1 - π := by linarith
  have h2 : 0 ≤ 1 - r2 := by linarith
  have h3 : 1 - r2 ≤ 1 := by linarith
  have h_nonneg : 0 ≤ π * (1 - π) * (1 - r2) :=
    mul_nonneg (mul_nonneg h_π h_one_minus_pi) h2
  nlinarith

/-! **Brier portability decomposition as the exact proper-score result** is
`brier_increase_mainly_calibration` above, which proves the decomposition, the positivity
of both terms, their order, and the half-share.

A second theorem here, `brier_proper_score_portability_decomposition`, restated the
decomposition and the half-share alone -- the same sixteen-line hypothesis block copied,
and a proof that destructures the stronger result and rebuilds two of its five conjuncts.
A projection of a theorem is not a theorem; the caller who wants two of the five can take
them from the one that proves all five. -/

end ProperScoringRules

end Descent.Portability
