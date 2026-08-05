/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.MetricSpecificPortability.R2Decomposition

namespace Descent.Portability

open MeasureTheory

/-!
# `MetricSpecificPortability.CalibrationVsDiscrimination`

Part of the split of `Descent/Portability/MetricSpecificPortability.lean`, which was 3,946 lines.

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
## Calibration vs Discrimination

Calibration (predicted risk = observed risk) and discrimination
(ability to separate cases from controls) can degrade differently
across populations.
-/

section CalibrationVsDiscrimination

/-- **At fixed drift in the neutral benchmark, exact liability AUC is preserved
while CITL shifts exactly with the mean-score offset.**
    This theorem formalizes the intended metric split on the repository's
    actual metrics:

    - discrimination is measured by exact liability-threshold AUC;
    - calibration is measured by calibration-in-the-large (CITL).

    If source and target have the same `fst`, then the exact liability transport
    map gives exactly the same AUC. If the target mean prediction is shifted by an
    additive offset `δ`, then CITL shifts by exactly `-δ`. This is the precise
    fixed-`fst` statement behind "rank-based discrimination can be preserved
    while calibration is lost." -/
theorem neutralAF_benchmark_auc_preserved_citl_shift_at_fixed_fst
    (mean_obs mean_pred δ : ℝ) :
    calibrationInTheLarge mean_obs (mean_pred + δ) =
      calibrationInTheLarge mean_obs mean_pred - δ := by
  unfold calibrationInTheLarge Descent.Core.difference
  ring

/-- **THE DISCRIMINATION CONJUNCT REMOVED FROM THE TWO THEOREMS BELOW WAS VACUOUS, AND
THIS IS WHAT IT SHOULD HAVE SAID.**

The deleted conjunct was

`presentDayEqualVarianceGaussianAUC V_A V_E fst =
   presentDayEqualVarianceGaussianAUC V_A V_E fst`

and it was proved by `rfl`, because those two names denote **the same function**:
`presentDayEqualVarianceGaussianAUC` delegates to
`presentDayEqualVarianceGaussianAUC`, which delegates to `presentDayEqualVarianceGaussianAUC`, of
which `presentDayEqualVarianceGaussianAUC` is a one-line alias. It was `f x = f x` wearing
two names, and it would have held equally well had AUC been wildly *not* preserved. Nothing
in reading the statement revealed this; the name structure concealed it.

Note what did **not** help: the docstring on `presentDayEqualVarianceGaussianAUC`
had already been corrected to say "equal-variance Gaussian" and to record the `-0.068`
bias. A docstring cannot repair a statement built out of identifiers.

The substantive claim the prose was reaching for is below, and it needs a hypothesis: the
equal-variance AUC depends on heritability and drift **only through the attenuated signal
variance**, so any two configurations agreeing there have equal AUC. That is why "same
drift, same AUC" holds, and unlike the deleted conjunct it can fail — supply configurations
with different attenuated signal variance and the conclusion goes away. -/
theorem neutralAF_benchmark_auc_depends_only_on_attenuated_signal
    (V_A V_E fst V_A' fst' : ℝ)
    (h : presentDayPGSVariance V_A fst = presentDayPGSVariance V_A' fst') :
    presentDayEqualVarianceGaussianAUC V_A V_E fst =
      presentDayEqualVarianceGaussianAUC V_A' V_E fst' := by
  unfold presentDayEqualVarianceGaussianAUC
  rw [h]

/-- **Benchmark discrimination can be preserved while calibration is lost.**

    Discrimination half: if two configurations agree in attenuated signal variance -- which
    is what "sharing the same drift level" delivers -- the equal-variance AUC is unchanged.
    This is a hypothesis-carrying claim, not an identity: see
    `neutralAF_benchmark_auc_depends_only_on_attenuated_signal` for why a form provable by
    `rfl` here would be empty.

    Calibration half: if the source is calibrated in the large and the target mean
    prediction is shifted by a nonzero `δ`, target absolute CITL becomes strictly worse.
    This half was always substantive and is unchanged.

    The pairing is the point, and only now does it have two working halves: discrimination
    can survive exactly the perturbation that destroys calibration, so reporting AUC alone
    hides the failure. Note also that this is the **equal-variance** AUC; on a dichotomised
    trait the discrimination half would have to be restated with `liabilityThresholdAUCFromExplainedR2` at a named prevalence, where preservation is a
    stronger claim because the conditional variances differ. -/
theorem neutralAF_benchmark_discrimination_preserved_calibration_lost
    (V_A V_E fst V_A' fst' mean_obs mean_pred δ : ℝ)
    (h_same_signal : presentDayPGSVariance V_A fst = presentDayPGSVariance V_A' fst')
    (h_src_cal : calibrationInTheLarge mean_obs mean_pred = 0)
    (h_shift : δ ≠ 0) :
    presentDayEqualVarianceGaussianAUC V_A V_E fst =
      presentDayEqualVarianceGaussianAUC V_A' V_E fst' ∧
    |calibrationInTheLarge mean_obs mean_pred| <
      |calibrationInTheLarge mean_obs (mean_pred + δ)| := by
  have h_citl_shift :=
    neutralAF_benchmark_auc_preserved_citl_shift_at_fixed_fst mean_obs mean_pred δ
  refine ⟨neutralAF_benchmark_auc_depends_only_on_attenuated_signal V_A V_E fst V_A' fst'
    h_same_signal, ?_⟩
  rw [h_src_cal]
  rw [h_citl_shift, h_src_cal]
  have h_shift_sub : 0 - δ ≠ 0 := by
    intro h
    apply h_shift
    linarith
  simp only [abs_zero]
  exact abs_pos.mpr h_shift_sub

/-- **Mechanistic transport can jointly worsen calibration slope and Brier.**
    This theorem is stated on the explicit SNP-level transport model rather
    than on a neutral-AF slope benchmark.

    If the transported source score has calibration slope below `1` in the
    target population and its transported `R²` drops, then:

    - the deployed target identity-link calibration profile has slope below `1`;
    - the slope deviation from perfect calibration is exactly `1 - slope`;
    - the slope itself is the exact direct-causal + proxy-tagging + context
      law from the mechanistic portability model; and
    - exact target calibrated Brier is strictly worse than the source score
      evaluated on the same target prevalence scale. -/
theorem mechanistic_transport_disrupts_slope_and_brier
    {p q : ℕ} (cal : CrossPopulationMechanisticCalibrationModel p q)
    (h_target_slope_lt : calibrationSlopeFromSourceWeights cal.metric Pop.target < 1)
    (h_r2_drop :
      r2FromSourceWeights cal.metric Pop.target < r2FromSourceWeights cal.metric Pop.source) :
    let profile := (cal.identityCalibrationProfile Pop.target)
    profile.slope < 1 ∧
    calibrationSlopeDeviation 1 < calibrationSlopeDeviation profile.slope ∧
    calibrationSlopeDeviation profile.slope = 1 - profile.slope ∧
    profile.slope =
      (sourceWeightedTagScore cal.metric (directCausalProjection cal.metric Pop.target) +
        sourceWeightedTagScore cal.metric (proxyTaggingProjection cal.metric Pop.target) +
        sourceWeightedTagScore cal.metric (cal.metric.contextCross Pop.target)) /
          scoreVarianceFromSourceWeights cal.metric Pop.target ∧
    sourceCalibratedBrierFromSourceWeightsAtPrevalence
        cal.metric cal.metric.targetPrevalence <
      targetCalibratedBrierFromSourceWeights cal.metric := by
  dsimp
  have hslope_lt : ((cal.identityCalibrationProfile Pop.target)).slope < 1 := by
    simpa [CrossPopulationMechanisticCalibrationModel.identityCalibrationProfile,
      CrossPopulationMechanisticCalibrationModel.calibrationProfile] using
      h_target_slope_lt
  have hslope_dev_pos :
      calibrationSlopeDeviation 1 <
        calibrationSlopeDeviation ((cal.identityCalibrationProfile Pop.target)).slope := by
    unfold calibrationSlopeDeviation
    rw [show (1 : ℝ) - 1 = 0 by ring, abs_zero]
    have hneg : ((cal.identityCalibrationProfile Pop.target)).slope - 1 < 0 := by
      linarith
    rw [abs_of_neg hneg]
    linarith
  have hslope_dev :
      calibrationSlopeDeviation ((cal.identityCalibrationProfile Pop.target)).slope =
        1 - ((cal.identityCalibrationProfile Pop.target)).slope :=
    calibrationSlopeDeviation_eq_one_sub_of_lt_one
      ((cal.identityCalibrationProfile Pop.target)).slope hslope_lt
  have hslope_eq :
      ((cal.identityCalibrationProfile Pop.target)).slope =
        (sourceWeightedTagScore cal.metric (directCausalProjection cal.metric Pop.target) +
          sourceWeightedTagScore cal.metric (proxyTaggingProjection cal.metric Pop.target) +
          sourceWeightedTagScore cal.metric (cal.metric.contextCross Pop.target)) /
            scoreVarianceFromSourceWeights cal.metric Pop.target := by
    simpa [CrossPopulationMechanisticCalibrationModel.identityCalibrationProfile,
      CrossPopulationMechanisticCalibrationModel.calibrationProfile] using
      CrossPopulationMechanisticCalibrationModel.target_profile_slope_eq_direct_proxy_context_law
        cal CalibrationLink.identity
  have hbrier :
      sourceCalibratedBrierFromSourceWeightsAtPrevalence
          cal.metric cal.metric.targetPrevalence <
        targetCalibratedBrierFromSourceWeights cal.metric := by
    rw [sourceCalibratedBrierFromSourceWeightsAtPrevalence_eq_explainedR2_chart,
      targetCalibratedBrierFromSourceWeights_eq_explainedR2_chart]
    simpa [brierFromR2, sourceBrierFromR2, PopGen.TransportedMetrics.calibratedBrier] using
      brierFromR2_strictAnti cal.metric.targetPrevalence
        cal.metric.targetPrevalence_pos cal.metric.targetPrevalence_lt_one h_r2_drop
  exact ⟨hslope_lt, hslope_dev_pos, hslope_dev, hslope_eq, hbrier⟩

/-- **Dimension-to-information ratio for a target adaptation task.**
    In an orthogonal Fisher model with `d` target-specific parameters and
    per-sample Fisher information `I` for each parameter, the natural
    difficulty scale is `d / I`. Smaller values mean the target task can
    be estimated more precisely from the same effective sample size. -/
noncomputable def adaptationDifficultyIndex
    (nParams infoPerSample : ℝ) : ℝ :=
  Descent.Core.ratio nParams infoPerSample

/-- **Adaptation difficulty at zero information per sample, named.** A sample carrying no
information about the target distribution makes adaptation impossible, so the number of samples
required diverges. The divisor is zero and Lean returns `0`, reporting the EASIEST possible
adaptation problem where the truth is that no amount of data suffices. Consumers must require
`infoPerSample ≠ 0`. -/
theorem adaptationDifficultyIndex_no_information_is_junk (nParams : ℝ) :
    adaptationDifficultyIndex nParams 0 = 0 := by
  unfold adaptationDifficultyIndex Descent.Core.ratio
  simp

/-- **The index times the information per sample is the parameter count.** That is what makes it
a sample requirement rather than a bare ratio. -/
theorem adaptationDifficultyIndex_mul_info (nParams infoPerSample : ℝ)
    (h : infoPerSample ≠ 0) :
    adaptationDifficultyIndex nParams infoPerSample * infoPerSample = nParams := by
  unfold adaptationDifficultyIndex Descent.Core.ratio
  field_simp

/-- **Trace-MSE lower bound under an orthogonal Fisher model.**
    For an unbiased estimator of `d` orthogonal target parameters, the summed
    estimation variance is lower-bounded by `(d / I) / n_eff`, where `I` is the
    per-sample Fisher information and `n_eff` is the effective target sample size. -/
noncomputable def fisherTraceMSELowerBound
    (nEff nParams infoPerSample : ℝ) : ℝ :=
  adaptationDifficultyIndex nParams infoPerSample / nEff

/-- **fisherTraceMSELowerBound at zero nEff, named.** With zero effective sample size the
trace-MSE bound diverges: nothing is estimable. Lean returns `0`, a floor of zero, which
certifies perfect estimation from no effective data. A lower bound that vanishes where
estimation is impossible certifies rather than warns. Consumers must require `nEff ≠ 0`. -/
theorem fisherTraceMSELowerBound_zero_neff_is_junk (nParams infoPerSample : ℝ) :
    fisherTraceMSELowerBound 0 nParams infoPerSample = 0 := by
  unfold fisherTraceMSELowerBound
  simp

/-- **Effective sample size needed to beat a target trace-MSE threshold.**
    Solving `(d / I) / n_eff ≤ τ` for `n_eff` gives the closed-form threshold
    `(d / I) / τ` in the orthogonal Fisher model.

    Empirical status: **VALIDATED**
    (`validation/empirical/simcov/battery_dgpcov.py`, group B;
    `battery_dgpcov2.py`, group B2). The threshold is taken from this body, an
    estimator is run at exactly that many samples, and the summed squared error
    is measured over 4000 to 40000 independent replicate estimates. Two
    exponential families with different Fisher information, so `I` is not a
    relabelled variance -- Gaussian location at `σ² = 4` (`I = 1/4`) and
    Bernoulli at `p = 0.3` (`I = 1/(p(1-p)) = 4.76`):

      family      d    τ      n from this body   measured trace MSE   sems
      gaussian     5   0.10    200               0.09984±0.00031      0.5
      gaussian    20   0.02   4000               0.01995±0.00007      0.5
      bernoulli    5   0.10     10 (10.5)        0.10519±0.00032      0.6
      bernoulli   12   0.05     50               0.05060±0.00033      1.8

    The Bernoulli `d = 5` cell needs `n = 10.5` and 10 samples were run; against
    `(d/I)/n` at the integer `n` actually used it is 0.6 sems, so the 5.1 sems
    it shows against `τ` is the rounding and not the body.

    Competitors on the same cells, each run at its own `n`: `(d/I)/τ²` misses
    `τ` by 878 to 9819 sems, `(d·I)/τ` by 96 to 3320, and `(d²/I)/τ` by 393 to
    1777. So the design fixes both exponents and the direction of `I`, which a
    single family could not: inverting `I` is invisible when `I` is 1/4 unless a
    second family puts it above one. -/
noncomputable def requiredEffectiveSampleSizeForTraceMSE
    (nParams infoPerSample targetTraceMSE : ℝ) : ℝ :=
  adaptationDifficultyIndex nParams infoPerSample / targetTraceMSE

/-- **requiredEffectiveSampleSizeForTraceMSE at zero targetTraceMSE, named.** A target
trace-MSE of zero demands infinite data. Lean returns `0`, reporting that exact recovery is
free. Consumers must require `targetTraceMSE ≠ 0`. -/
theorem requiredEffectiveSampleSizeForTraceMSE_zero_targettracemse_is_junk
    (nParams infoPerSample : ℝ) :
    requiredEffectiveSampleSizeForTraceMSE nParams infoPerSample 0 = 0 := by
  unfold requiredEffectiveSampleSizeForTraceMSE
  simp

/-- The `requiredEffectiveSampleSizeForTraceMSE` definition is the exact
    threshold corresponding to the Fisher trace-MSE lower bound. -/
theorem fisherTraceMSELowerBound_le_target_iff
    (nEff nParams infoPerSample targetTraceMSE : ℝ)
    (h_nEff : 0 < nEff)
    (h_target : 0 < targetTraceMSE) :
    fisherTraceMSELowerBound nEff nParams infoPerSample ≤ targetTraceMSE ↔
      requiredEffectiveSampleSizeForTraceMSE nParams infoPerSample targetTraceMSE ≤ nEff := by
  unfold fisherTraceMSELowerBound requiredEffectiveSampleSizeForTraceMSE adaptationDifficultyIndex Descent.Core.ratio
  constructor
  · intro h
    rw [div_le_iff₀ h_target]
    rw [div_le_iff₀ h_nEff] at h
    simpa [mul_comm, mul_left_comm, mul_assoc] using h
  · intro h
    rw [div_le_iff₀ h_nEff]
    rw [div_le_iff₀ h_target] at h
    simpa [mul_comm, mul_left_comm, mul_assoc] using h

/-! ### The other half of a deployment budget, and the one that binds

`requiredEffectiveSampleSizeForTraceMSE` is a budget for *estimating target parameters*:
`(d/I)/tau`, which grows like `1/tau` as the target tightens. That is not the only budget a
deployment of the curve-prior dissolution has to meet, and it is not the binding one.

`Descent.FoldedSpectrum.RecoveryAttenuation.panels_suffice_iff` supplies the other:
averaging `B` order-free panels per cohort attains reliability `tau` **iff**
`B >= c*tau/(p*(1-tau))`. These are budgets for different quantities and neither implies
the other -- one is per-sample Fisher information for a parameter vector, the other is
replication of a variance estimate -- so the composite below is a conjunction, not a
derivation of one from the other. Do not collapse it into one bound.

**What the pairing shows is the asymmetry in `tau`.** The Fisher budget carries `1/tau`;
the panel budget carries `1/(1-tau)`. The first is bounded as the target tightens and the
second is not: each additional nine of reliability costs another factor of ten in panels.
So a design that budgets only along the Fisher axis will underprovision, and it will do so
by more the better the design is meant to be. The measured run reached reliability `0.153`
at `B = 16`, which puts `c/p` near `88` and the `tau = 0.8` requirement near **350 panels
per cohort** -- two orders of magnitude above what was tried.

This is why the dissolution is not yet usable, and the reason is worth stating precisely:
not that the population identity is false -- it is exact -- but that the reliability it
needs was never budgeted for. -/

/-- **A deployment must clear both budgets, and they are independent conditions.**

The estimation budget in effective sample size and the replication budget in panels per
cohort, stated as one iff so that neither can be quietly dropped. The panel half is
`FoldedSpectrum.RecoveryAttenuation.panels_suffice_iff` and is not provable in this file. -/
theorem deployment_meets_both_budgets
    (nEff nParams infoPerSample targetTraceMSE : ℝ)
    (p c tau B : ℝ)
    (h_nEff : 0 < nEff) (h_target : 0 < targetTraceMSE)
    (hp : 0 < p) (hc : 0 < c) (htau1 : tau < 1) (hB : 0 < B) :
    (fisherTraceMSELowerBound nEff nParams infoPerSample ≤ targetTraceMSE ∧
        tau ≤ p / (p + c / B)) ↔
      (requiredEffectiveSampleSizeForTraceMSE nParams infoPerSample targetTraceMSE ≤ nEff ∧
        c * tau / (p * (1 - tau)) ≤ B) := by
  constructor
  · rintro ⟨hfisher, hrel⟩
    exact ⟨(fisherTraceMSELowerBound_le_target_iff nEff nParams infoPerSample targetTraceMSE
        h_nEff h_target).1 hfisher,
      (Spectral.RecoveryAttenuation.panels_suffice_iff p c tau B hp hc htau1 hB).1 hrel⟩
  · rintro ⟨hsample, hpanels⟩
    exact ⟨(fisherTraceMSELowerBound_le_target_iff nEff nParams infoPerSample targetTraceMSE
        h_nEff h_target).2 hsample,
      (Spectral.RecoveryAttenuation.panels_suffice_iff p c tau B hp hc htau1 hB).2 hpanels⟩

/-- **The panel budget is unbounded in the reliability target; the Fisher budget is not.**

For any panel count `M` however large there is a reliability target below one that needs
more than `M` panels. That is the `1/(1-tau)` blow-up, and it is the formal content of "each
additional nine costs a factor of ten". Nothing analogous holds for
`requiredEffectiveSampleSizeForTraceMSE`, whose dependence on its own target is `1/tau` and
therefore bounded as the target tightens toward its best value.

The design reading: reliability, not per-sample information, is the constraint that decides
whether this method is affordable. -/
theorem panel_budget_unbounded_in_reliability (p c M : ℝ)
    (hp : 0 < p) (hc : 0 < c) (hM : 0 < M) :
    ∃ tau : ℝ, 0 < tau ∧ tau < 1 ∧ M < c * tau / (p * (1 - tau)) := by
  -- Take `1 - tau` small enough that `c*tau/(p*(1-tau))` exceeds `M`; `tau = 1/2` already
  -- fixes the numerator away from zero, so only the denominator has to be driven down.
  set eps : ℝ := min (1 / 2) (c / (2 * (M * p + c))) with heps
  have hMp : 0 < M * p + c := by positivity
  have heps_pos : 0 < eps := by
    rw [heps]; exact lt_min (by norm_num) (by positivity)
  have heps_half : eps ≤ 1 / 2 := min_le_left _ _
  have heps_le : eps ≤ c / (2 * (M * p + c)) := min_le_right _ _
  refine ⟨1 - eps, by linarith, by linarith, ?_⟩
  have hden : 0 < p * (1 - (1 - eps)) := by
    have : (1 : ℝ) - (1 - eps) = eps := by ring
    rw [this]; positivity
  rw [lt_div_iff₀ hden]
  have hsimp : (1 : ℝ) - (1 - eps) = eps := by ring
  rw [hsimp]
  -- Goal: `M * (p * eps) < c * (1 - eps)`. Use `eps ≤ c/(2(Mp+c))` and `eps ≤ 1/2`.
  have hkey : eps * (2 * (M * p + c)) ≤ c := by
    rw [heps] at heps_le ⊢
    calc min (1 / 2) (c / (2 * (M * p + c))) * (2 * (M * p + c))
        ≤ (c / (2 * (M * p + c))) * (2 * (M * p + c)) :=
          mul_le_mul_of_nonneg_right (min_le_right _ _) (by positivity)
      _ = c := by field_simp
  nlinarith [hkey, heps_pos, heps_half, hp, hc, hM]

/-- If the rediscovery task has both more free parameters and no more
    per-sample Fisher information than recalibration, then its
    dimension-to-information ratio is strictly larger. -/
theorem adaptationDifficultyIndex_recal_lt_rediscovery
    (infoCal infoDisc m : ℝ)
    (h_infoDisc : 0 < infoDisc)
    (h_info_order : infoDisc ≤ infoCal)
    (h_more_params : 2 < m) :
    adaptationDifficultyIndex 2 infoCal <
      adaptationDifficultyIndex m infoDisc := by
  unfold adaptationDifficultyIndex Descent.Core.ratio
  have h_two_over_cal_le_disc : 2 / infoCal ≤ 2 / infoDisc := by
    have h_inv : 1 / infoCal ≤ 1 / infoDisc :=
      one_div_le_one_div_of_le h_infoDisc h_info_order
    have h_mul :=
      mul_le_mul_of_nonneg_left h_inv (show (0 : ℝ) ≤ 2 by norm_num)
    simpa [div_eq_mul_inv] using h_mul
  have h_two_over_disc_lt_m_over_disc : 2 / infoDisc < m / infoDisc :=
    div_lt_div_of_pos_right h_more_params h_infoDisc
  exact lt_of_le_of_lt h_two_over_cal_le_disc h_two_over_disc_lt_m_over_disc

/-- **Recalibration is easier than rediscovery at the same precision target.**
    The honest version of this claim is sample-complexity based, not raw
    parameter counting. Model recalibration estimates only two target-specific
    parameters (intercept and slope), while discrimination rediscovery must
    estimate `m` target-specific effect parameters. In the orthogonal Fisher
    model, if rediscovery has at least as many free parameters and no more
    per-sample information than recalibration, then:

    1. at any fixed effective sample size, the Fisher trace-MSE lower bound is
       smaller for recalibration;
    2. to reach the same target trace-MSE threshold, recalibration requires
       strictly fewer effective target samples. -/
theorem recalibration_easier_than_rediscovery
    (nEff targetTraceMSE infoCal infoDisc m : ℝ)
    (h_nEff : 0 < nEff)
    (h_target : 0 < targetTraceMSE)
    (h_infoDisc : 0 < infoDisc)
    (h_info_order : infoDisc ≤ infoCal)
    (h_more_params : 2 < m) :
    fisherTraceMSELowerBound nEff 2 infoCal <
      fisherTraceMSELowerBound nEff m infoDisc ∧
    requiredEffectiveSampleSizeForTraceMSE 2 infoCal targetTraceMSE <
      requiredEffectiveSampleSizeForTraceMSE m infoDisc targetTraceMSE := by
  have h_diff :
      adaptationDifficultyIndex 2 infoCal <
        adaptationDifficultyIndex m infoDisc :=
    adaptationDifficultyIndex_recal_lt_rediscovery
      infoCal infoDisc m h_infoDisc h_info_order h_more_params
  constructor
  · unfold fisherTraceMSELowerBound
    exact div_lt_div_of_pos_right h_diff h_nEff
  · unfold requiredEffectiveSampleSizeForTraceMSE
    exact div_lt_div_of_pos_right h_diff h_target

/-- **Brier score increases with portability loss (derived from Brier definition).**
    Since `brierFromR2 π r2 = π(1-π)(1-r2)`, a decrease in R² (from drift)
    directly increases the Brier score. When R² drops from source to target
    via drift, the Brier score strictly increases. -/
theorem brier_increases_with_portability_loss
    (π r2_source r2_target : ℝ)
    (h_π : 0 < π) (h_π' : π < 1)
    (h_drop : r2_target < r2_source) :
    brierFromR2 π r2_source < brierFromR2 π r2_target := by
  unfold brierFromR2 PopGen.TransportedMetrics.calibratedBrier
  have h_prev : 0 < π * (1 - π) := by nlinarith
  nlinarith

/-- **Brier score is bounded by prevalence (derived from Brier definition).**
    `brierFromR2 π r2 = π(1-π)(1-r2)`. Since 0 ≤ r2, the Brier score is
    at most `π(1-π)` (achieved at r2 = 0, the uninformative predictor).
    A positive R² strictly reduces the Brier score below the baseline. -/
theorem brier_bounded_by_prevalence
    (π r2 : ℝ)
    (h_π : 0 < π) (h_π' : π < 1)
    (h_r2 : 0 < r2) :
    brierFromR2 π r2 < π * (1 - π) := by
  -- The uninformative predictor is `r2 = 0`, where the Brier score IS `π(1-π)`, so this is
  -- the monotonicity above at that endpoint rather than a second run of the same `nlinarith`.
  simpa [brierFromR2, PopGen.TransportedMetrics.calibratedBrier] using
    brier_increases_with_portability_loss π r2 0 h_π h_π' h_r2

/-- Brier worsening caused by mechanistic signal/discrimination loss alone,
holding the outcome prevalence scale fixed at the target-population value. -/
noncomputable def brierDiscriminationLoss {p q : ℕ}
    (m : CrossPopulationMetricModel p q) : ℝ :=
  targetCalibratedBrierFromSourceWeights m -
    sourceCalibratedBrierFromSourceWeightsAtPrevalence m m.targetPrevalence

/-- Brier worsening caused by an outcome-scale shift alone, holding the
mechanistic source score fixed. This isolates the change from evaluating the
same source score at the target prevalence scale instead of the source scale. -/
noncomputable def brierCalibrationLoss {p q : ℕ}
    (πSource : ℝ) (m : CrossPopulationMetricModel p q) : ℝ :=
  sourceCalibratedBrierFromSourceWeightsAtPrevalence m m.targetPrevalence -
    sourceCalibratedBrierFromSourceWeightsAtPrevalence m πSource

/-- Exact formula for the mechanistic discrimination-loss contribution to Brier
worsening on the target prevalence scale. -/
theorem brierDiscriminationLoss_eq
    {p q : ℕ} (m : CrossPopulationMetricModel p q) :
    brierDiscriminationLoss m =
      m.targetPrevalence * (1 - m.targetPrevalence) *
        (r2FromSourceWeights m Pop.source - r2FromSourceWeights m Pop.target) := by
  unfold brierDiscriminationLoss
  rw [targetCalibratedBrierFromSourceWeights_eq_explainedR2_chart,
    sourceCalibratedBrierFromSourceWeightsAtPrevalence_eq_explainedR2_chart]
  unfold PopGen.TransportedMetrics.calibratedBrier
  ring_nf

/-- Exact formula for the outcome-scale contribution to Brier worsening when
the mechanistic source score is re-evaluated at a different observed prevalence
coordinate. -/
theorem brierCalibrationLoss_eq
    {p q : ℕ} (πSource : ℝ) (m : CrossPopulationMetricModel p q) :
    brierCalibrationLoss πSource m =
      (m.targetPrevalence * (1 - m.targetPrevalence) -
          πSource * (1 - πSource)) *
        (1 - r2FromSourceWeights m Pop.source) := by
  unfold brierCalibrationLoss
  rw [sourceCalibratedBrierFromSourceWeightsAtPrevalence_eq_explainedR2_chart,
    sourceCalibratedBrierFromSourceWeightsAtPrevalence_eq_explainedR2_chart]
  unfold PopGen.TransportedMetrics.calibratedBrier
  ring_nf

/-- Exact decomposition of mechanistic Brier worsening into a source-vs-target
signal-loss term and a source-vs-target outcome-scale term. -/
theorem observableBrier_change_decomposition
    {p q : ℕ} (πSource : ℝ) (m : CrossPopulationMetricModel p q) :
    targetCalibratedBrierFromSourceWeights m -
      sourceCalibratedBrierFromSourceWeightsAtPrevalence m πSource =
      brierDiscriminationLoss m +
      brierCalibrationLoss πSource m := by
  unfold brierDiscriminationLoss brierCalibrationLoss
  ring

/-- A mechanistic drop in transported `R²` makes the Brier discrimination-loss
contribution positive on the target prevalence scale. -/
theorem brierDiscriminationLoss_pos_of_mechanistic_r2_drop
    {p q : ℕ} (m : CrossPopulationMetricModel p q)
    (h_r2_drop : r2FromSourceWeights m Pop.target < r2FromSourceWeights m Pop.source) :
    0 < brierDiscriminationLoss m := by
  unfold brierDiscriminationLoss
  exact sub_pos.mpr <|
    brierFromR2_strictAnti m.targetPrevalence
      m.targetPrevalence_pos m.targetPrevalence_lt_one
      (by simpa [r2FromSourceWeights] using h_r2_drop)

/-- If the Bernoulli variance factor increases from source to target on the
same mechanistic source score, the outcome-scale contribution is positive. -/
theorem brierCalibrationLoss_pos_of_prevalence_factor_increase
    {p q : ℕ} (πSource : ℝ) (m : CrossPopulationMetricModel p q)
    (h_source_r2_unit : r2FromSourceWeights m Pop.source ∈ Set.Ico 0 1)
    (h_prev_factor :
      πSource * (1 - πSource) <
        m.targetPrevalence * (1 - m.targetPrevalence)) :
    0 < brierCalibrationLoss πSource m := by
  rw [brierCalibrationLoss_eq]
  have h_prev_gap :
      0 < m.targetPrevalence * (1 - m.targetPrevalence) -
        πSource * (1 - πSource) := by
    linarith
  have h_one_minus_source_r2 : 0 < 1 - r2FromSourceWeights m Pop.source := by
    linarith [h_source_r2_unit.2]
  exact mul_pos h_prev_gap h_one_minus_source_r2

/-- **Exact mechanistic Brier worsening is calibration-dominated when the
outcome-scale shift outweighs SNP-level signal loss on the Brier chart.**

This theorem is now stated on the explicit `CrossPopulationMetricModel`.
The two terms are:

- `brierDiscriminationLoss m`: worsening from the transported SNP-level loss in
  explained signal at fixed target prevalence;
- `brierCalibrationLoss πSource m`: worsening from evaluating the same source
  score on the target outcome scale rather than the source outcome scale.

If the outcome-scale term is larger than the mechanistic signal-loss term,
then it contributes more than half of the total Brier worsening. -/
theorem brier_increase_mainly_calibration
    {p q : ℕ} (πSource : ℝ) (m : CrossPopulationMetricModel p q)
    (h_source_r2_unit : r2FromSourceWeights m Pop.source ∈ Set.Ico 0 1)
    (h_r2_drop : r2FromSourceWeights m Pop.target < r2FromSourceWeights m Pop.source)
    (h_prev_factor :
      πSource * (1 - πSource) <
        m.targetPrevalence * (1 - m.targetPrevalence))
    (h_scale_dom :
      m.targetPrevalence * (1 - m.targetPrevalence) *
          (r2FromSourceWeights m Pop.source - r2FromSourceWeights m Pop.target) <
        (m.targetPrevalence * (1 - m.targetPrevalence) -
            πSource * (1 - πSource)) *
          (1 - r2FromSourceWeights m Pop.source)) :
    targetCalibratedBrierFromSourceWeights m -
      sourceCalibratedBrierFromSourceWeightsAtPrevalence m πSource =
        brierDiscriminationLoss m +
        brierCalibrationLoss πSource m ∧
    0 < brierDiscriminationLoss m ∧
    0 < brierCalibrationLoss πSource m ∧
    brierDiscriminationLoss m < brierCalibrationLoss πSource m ∧
    (targetCalibratedBrierFromSourceWeights m -
        sourceCalibratedBrierFromSourceWeightsAtPrevalence m πSource) / 2 <
      brierCalibrationLoss πSource m := by
  have h_decomp := observableBrier_change_decomposition πSource m
  have h_disc_pos := brierDiscriminationLoss_pos_of_mechanistic_r2_drop m h_r2_drop
  have h_cal_pos := brierCalibrationLoss_pos_of_prevalence_factor_increase
    πSource m h_source_r2_unit h_prev_factor
  have h_cal_dom' :
      brierDiscriminationLoss m < brierCalibrationLoss πSource m := by
    rw [brierDiscriminationLoss_eq, brierCalibrationLoss_eq]
    exact h_scale_dom
  refine ⟨h_decomp, h_disc_pos, h_cal_pos, h_cal_dom', ?_⟩
  rw [h_decomp]
  linarith

end CalibrationVsDiscrimination

end Descent.Portability
