import Calibrator.Probability
import Calibrator.PortabilityDrift
import Calibrator.PGSCalibrationTheory
import Calibrator.ClinicalUtilityFairness
import Calibrator.OpenQuestions

namespace Calibrator

open MeasureTheory

/-!
# Metric-Specific Portability (Open Question 3)

This file formalizes Wang et al.'s Open Question 3: portability depends
on the prediction metric used. Different metrics (R², AUC, Brier, NRI,
calibration) can show different portability patterns for the same trait
and populations.

Key results:
1. R² vs AUC portability relationship
2. Calibration vs discrimination portability
3. Precision vs recall portability
4. Metric decomposition and cross-population behavior
5. Optimal metric choice for clinical applications

Reference: Wang et al. (2026), Nature Communications 17:942.
-/


/-!
## R² Decomposition from First Principles

We derive the decomposition R² = discrimination × calibration from the
standard regression definition R² = 1 − SS_res/SS_tot, rather than
assuming it as a parameter structure.

### Setup
- Y is the observed outcome with variance Var(Y).
- Ŷ is the predicted value from a model.
- R² = 1 − SS_res/SS_tot = 1 − Var(Y − Ŷ)/Var(Y).
- By the law of total variance,
    Var(Y) = Var(E[Y|Ŷ]) + E[Var(Y|Ŷ)],
  so R² = Var(E[Y|Ŷ])/Var(Y) when we use the population version.

### Decomposition
Write E[Y|Ŷ] = f(Ŷ), the calibration function.
- **Discrimination** captures how spread out the predictions are
  relative to outcome variance: disc = Var(Ŷ)/Var(Y).
- **Calibration** captures how well the calibration function f
  preserves the variance of Ŷ: cal = Var(f(Ŷ))/Var(Ŷ).

Then: R² = Var(E[Y|Ŷ])/Var(Y)
         = Var(f(Ŷ))/Var(Y)
         = [Var(f(Ŷ))/Var(Ŷ)] × [Var(Ŷ)/Var(Y)]
         = cal × disc.

When perfectly calibrated, f = id, so cal = 1 and R² = disc.
-/

section R2Decomposition

/-- Algebraic representation of the components entering the R² decomposition.

    All quantities are real-valued summary statistics computed from the joint
    distribution of (Y, Ŷ).  The structure records:
    • `varY`      — Var(Y), total outcome variance,
    • `varYhat`   — Var(Ŷ), variance of the predictor,
    • `varCondE`  — Var(E[Y|Ŷ]) = Var(f(Ŷ)), explained variance,
    where f is the calibration function f(ŷ) = E[Y | Ŷ = ŷ].

    From these three quantities every other object (R², discrimination,
    calibration) is a ratio, and the key factorization is purely algebraic. -/
structure R2DecompositionData where
  varY     : ℝ   -- Var(Y), total outcome variance
  varYhat  : ℝ   -- Var(Ŷ), variance of the predictor
  varCondE : ℝ   -- Var(E[Y|Ŷ]) = Var(f(Ŷ)), the explained variance
  hVarY_pos     : 0 < varY
  hVarYhat_pos  : 0 < varYhat
  hVarCondE_pos : 0 < varCondE
  -- Var(f(Ŷ)) ≤ Var(Ŷ) (f can only shrink variance unless it stretches)
  hCondE_le_Yhat : varCondE ≤ varYhat
  -- Var(Ŷ) ≤ Var(Y) (predictor can't have more spread than outcome in R² ≤ 1 regime)
  hYhat_le_Y : varYhat ≤ varY
  -- Var(E[Y|Ŷ]) ≤ Var(Y) (law of total variance: explained ≤ total)
  hCondE_le_Y : varCondE ≤ varY

/-- **R² from the standard definition** (population version).

    R² = Var(E[Y|Ŷ]) / Var(Y).

    This is equivalent to 1 − SS_res/SS_tot when SS_res is evaluated
    at the population level, because
      SS_res/SS_tot = Var(Y − E[Y|Ŷ])/Var(Y)
                    = E[Var(Y|Ŷ)]/Var(Y)
                    = 1 − Var(E[Y|Ŷ])/Var(Y)
    by the law of total variance. -/
noncomputable def R2DecompositionData.r2 (d : R2DecompositionData) : ℝ :=
  d.varCondE / d.varY

/-- **Discrimination component**: Var(Ŷ)/Var(Y).

    Measures the predictor's ability to spread predictions across the
    range of outcomes — the rank-ordering / signal-spread component.
    Monotonically related to AUC for binary outcomes via the liability
    threshold model. -/
noncomputable def R2DecompositionData.discrimination (d : R2DecompositionData) : ℝ :=
  d.varYhat / d.varY

/-- **Calibration component**: Var(f(Ŷ))/Var(Ŷ) where f(ŷ) = E[Y|Ŷ=ŷ].

    Measures how well the calibration function preserves the predictor's
    variance.  When perfectly calibrated (f = id), this equals 1.
    When miscalibrated, f compresses Ŷ's spread, so this factor < 1. -/
noncomputable def R2DecompositionData.calibration (d : R2DecompositionData) : ℝ :=
  d.varCondE / d.varYhat

/-- **The fundamental factorization**: R² = discrimination × calibration.

    Proof:  R²   = Var(E[Y|Ŷ]) / Var(Y)
                 = [Var(Ŷ)/Var(Y)] × [Var(E[Y|Ŷ])/Var(Ŷ)]
                 = disc × cal.

    This is a purely algebraic identity once we note
    (a/c) = (b/c) × (a/b) for positive b, c. -/
theorem R2DecompositionData.r2_eq_disc_mul_cal (d : R2DecompositionData) :
    d.r2 = d.discrimination * d.calibration := by
  unfold r2 discrimination calibration
  rw [div_mul_div_comm]
  rw [div_eq_div_iff (ne_of_gt d.hVarY_pos)
        (mul_ne_zero (ne_of_gt d.hVarY_pos) (ne_of_gt d.hVarYhat_pos))]
  ring

/-- **R² is bounded by discrimination**.

    Since calibration ≤ 1 (from Var(f(Ŷ)) ≤ Var(Ŷ)), we have
    R² = disc × cal ≤ disc × 1 = disc. -/
theorem R2DecompositionData.r2_le_discrimination (d : R2DecompositionData) :
    d.r2 ≤ d.discrimination := by
  unfold r2 discrimination
  exact div_le_div_of_nonneg_right d.hCondE_le_Yhat (le_of_lt d.hVarY_pos)

/-- **R² is nonneg** (immediate from positive components). -/
theorem R2DecompositionData.r2_nonneg (d : R2DecompositionData) :
    0 ≤ d.r2 := by
  unfold r2
  exact div_nonneg (le_of_lt d.hVarCondE_pos) (le_of_lt d.hVarY_pos)

/-- **R² ≤ 1** (from Var(E[Y|Ŷ]) ≤ Var(Y)). -/
theorem R2DecompositionData.r2_le_one (d : R2DecompositionData) :
    d.r2 ≤ 1 := by
  unfold r2
  rw [div_le_iff₀ d.hVarY_pos]
  simpa using d.hCondE_le_Y

/-- **Discrimination is in [0, 1]**. -/
theorem R2DecompositionData.disc_le_one (d : R2DecompositionData) :
    d.discrimination ≤ 1 := by
  unfold discrimination
  rw [div_le_iff₀ d.hVarY_pos]
  simpa using d.hYhat_le_Y

theorem R2DecompositionData.disc_pos (d : R2DecompositionData) :
    0 < d.discrimination := by
  unfold discrimination
  exact div_pos d.hVarYhat_pos d.hVarY_pos

/-- **Calibration is in [0, 1]**. -/
theorem R2DecompositionData.cal_le_one (d : R2DecompositionData) :
    d.calibration ≤ 1 := by
  unfold calibration
  rw [div_le_iff₀ d.hVarYhat_pos]
  simpa using d.hCondE_le_Yhat

theorem R2DecompositionData.cal_pos (d : R2DecompositionData) :
    0 < d.calibration := by
  unfold calibration
  exact div_pos d.hVarCondE_pos d.hVarYhat_pos

/-- **Perfect calibration implies R² = discrimination**.

    When f = id, Var(f(Ŷ)) = Var(Ŷ), so cal = 1 and R² = disc. -/
theorem R2DecompositionData.perfect_calibration_r2_eq_disc (d : R2DecompositionData)
    (h_perfect : d.varCondE = d.varYhat) :
    d.r2 = d.discrimination := by
  unfold r2 discrimination
  rw [h_perfect]

/-- **Calibration loss strictly reduces R² below discrimination**.

    If cal < 1 (i.e., Var(f(Ŷ)) < Var(Ŷ)), then R² < disc. -/
theorem R2DecompositionData.cal_loss_reduces_r2 (d : R2DecompositionData)
    (h_miscal : d.varCondE < d.varYhat) :
    d.r2 < d.discrimination := by
  unfold r2 discrimination
  exact div_lt_div_of_pos_right h_miscal d.hVarY_pos

/-- **R² is less portable than true AUC when only calibration is lost.**

    Assume source and target scores are evaluated on the same binary population
    and differ only by a strictly increasing recalibration map, so the literal
    population AUC is preserved exactly by rank invariance. If the source is
    perfectly calibrated but the target loses calibration, then:

    - the literal population AUC is preserved exactly;
    - the absolute AUC portability gap is exactly `0`;
    - the `R²` portability ratio equals the residual target calibration;
    - the `R²` portability loss `1 - R²_target / R²_source` is strictly positive.

    This states the metric comparison directly on the repository's actual
    population AUC functional, not on a liability-model surrogate. -/
theorem r2_less_portable_than_auc_from_decomposition
    {Z : Type*} [MeasurableSpace Z]
    (pop : BinaryPopulation Z)
    (scoreSource scoreTarget : Z → ℝ)
    (source target : R2DecompositionData)
    (g : ℝ → ℝ)
    (hg : StrictMono g)
    (hScoreTarget : scoreTarget = g ∘ scoreSource)
    -- Calibration is strictly lost: Var(f(Ŷ))/Var(Ŷ) is lower in target
    (hCalLoss : target.calibration < source.calibration)
    -- Source is perfectly calibrated (f = id in source)
    (hSourceCal : source.varCondE = source.varYhat)
    -- Discrimination transfers perfectly, so the only `R²` loss comes from
    -- calibration.
    (hDiscPreserved : target.discrimination = source.discrimination) :
    populationAUC pop scoreTarget = populationAUC pop scoreSource ∧
    |ENNReal.toReal (populationAUC pop scoreTarget) -
        ENNReal.toReal (populationAUC pop scoreSource)| = 0 ∧
    target.r2 / source.r2 = target.calibration ∧
    0 < 1 - target.r2 / source.r2 := by
  have h_src_r2 : source.r2 = source.discrimination * source.calibration :=
    source.r2_eq_disc_mul_cal
  have h_tgt_r2 : target.r2 = target.discrimination * target.calibration :=
    target.r2_eq_disc_mul_cal
  have h_src_cal : source.calibration = 1 := by
    unfold R2DecompositionData.calibration
    rw [hSourceCal]
    exact div_self (ne_of_gt source.hVarYhat_pos)
  have h_src_r2_eq : source.r2 = source.discrimination := by
    rw [h_src_r2, h_src_cal, mul_one]
  have h_tgt_cal_lt : target.calibration < 1 := by
    rw [h_src_cal] at hCalLoss; exact hCalLoss
  have h_r2_ratio : target.r2 / source.r2 = target.calibration := by
    rw [h_tgt_r2, h_src_r2_eq, hDiscPreserved]
    field_simp [ne_of_gt source.disc_pos]
  have h_auc_eq : populationAUC pop scoreTarget = populationAUC pop scoreSource := by
    rw [hScoreTarget]
    simpa [Function.comp] using
      (populationAUC_strictMono_invariant pop scoreSource g hg)
  have h_auc_gap_zero :
      |ENNReal.toReal (populationAUC pop scoreTarget) -
          ENNReal.toReal (populationAUC pop scoreSource)| = 0 := by
    rw [h_auc_eq]
    simp
  have h_r2_gap_pos : 0 < 1 - target.r2 / source.r2 := by
    rw [h_r2_ratio]
    linarith
  exact ⟨h_auc_eq, h_auc_gap_zero, h_r2_ratio, h_r2_gap_pos⟩

/-- **Cross-population R² ratio equals product of component ratios**.

    If the source is perfectly calibrated:
      R²_target / R²_source = (disc_target / disc_source) × cal_target

    This makes explicit that R² portability is the product of how well
    discrimination transfers and the residual calibration in the target. -/
theorem r2_portability_ratio_factorization
    (source target : R2DecompositionData)
    (hSourceCal : source.varCondE = source.varYhat) :
    target.r2 / source.r2 =
      (target.discrimination / source.discrimination) * target.calibration := by
  have h_src_r2 := source.r2_eq_disc_mul_cal
  have h_tgt_r2 := target.r2_eq_disc_mul_cal
  have h_src_cal : source.calibration = 1 := by
    unfold R2DecompositionData.calibration
    rw [hSourceCal]
    exact div_self (ne_of_gt source.hVarYhat_pos)
  have h_src_r2_eq : source.r2 = source.discrimination := by
    rw [h_src_r2, h_src_cal, mul_one]
  rw [h_tgt_r2, h_src_r2_eq, mul_div_assoc]
  ring

end R2Decomposition


/-!
## R² vs AUC: Different Portability Measures

R² measures variance explained (continuous traits).
AUC measures discriminative ability (binary traits).
These metrics respond differently to distribution shifts.
-/

section R2VsAUC

/-- **R² is sensitive to drift in the neutral allele-frequency benchmark.**
    When drift increases (`fstS < fstT`), `presentDayR2` strictly decreases, so
    the source-to-target R² drop is positive. -/
theorem r2_sensitive_to_drift
    (V_A V_E fstS fstT : ℝ)
    (hVA : 0 < V_A) (hVE : 0 < V_E)
    (hfst : fstS < fstT)
    (hfstT_le_one : fstT ≤ 1) :
    0 < presentDayR2 V_A V_E fstS - presentDayR2 V_A V_E fstT := by
  have h := drift_degrades_R2 V_A V_E fstS fstT hVA hVE hfst hfstT_le_one
  linarith

/-- **Exact present-day liability AUC formula.**
    Under the equal-variance Gaussian liability model, the present-day AUC is
    exactly `Φ(√(SNR/2))`, where `SNR = presentDaySignalToNoise`. -/
theorem presentDayLiabilityAUC_formula
    (V_A V_E fst : ℝ) :
    presentDayLiabilityAUC V_A V_E fst =
      Phi (Real.sqrt (presentDaySignalToNoise V_A V_E fst / 2)) := by
  simp [presentDayLiabilityAUC, presentDayAUC]

/-- **Brier score depends on prevalence (derived from Brier definition).**
    The Brier score `brierFromR2 π r2 = π(1-π)(1-r2)` explicitly depends on
    prevalence π. Higher prevalence (up to 0.5) gives higher Brier score
    for the same R², because π(1-π) increases on (0, 0.5).
    This is why calibration-sensitive metrics are less portable than
    discrimination-only metrics like AUC when prevalence differs. -/
theorem brier_depends_on_prevalence
    (r2 π₁ π₂ : ℝ)
    (h_r2_lt : r2 < 1)
    (h_order : π₁ < π₂) (h_half : π₂ ≤ 1/2) :
    brierFromR2 π₁ r2 < brierFromR2 π₂ r2 := by
  unfold brierFromR2 exactCalibratedBrierRiskFromR2
  have h_factor : 0 < 1 - r2 := by linarith
  -- Need: π₁(1-π₁) < π₂(1-π₂) when 0 < π₁ < π₂ ≤ 1/2
  -- f(x) = x(1-x) is increasing on (0, 1/2)
  have h_prod : π₁ * (1 - π₁) < π₂ * (1 - π₂) := by nlinarith
  nlinarith

/-- **Source liability AUC is strictly increasing in source `R²`.**
    Under the exact liability-threshold chart
    `AUC = Φ(√(r2 / (2(1-r2))))`, higher source `R²` yields higher source
    liability AUC.
    This is a true metric comparison, not just a formula expansion. -/
theorem sourceLiabilityAUC_strictly_increases_with_r2
    (r2₁ r2₂ : ℝ)
    (h_r2₁ : 0 < r2₁) (h_r2₂ : r2₂ < 1)
    (h_lt : r2₁ < r2₂)
    (hPhiStrict : StrictMono Phi) :
    liabilityAUCFromExplainedR2 r2₁ <
      liabilityAUCFromExplainedR2 r2₂ := by
  have h_r2₂_pos : 0 < r2₂ := lt_trans h_r2₁ h_lt
  exact liabilityAUCFromExplainedR2_strictMonoOn_unitInterval hPhiStrict
    ⟨le_of_lt h_r2₁, lt_trans h_lt h_r2₂⟩
    ⟨le_of_lt h_r2₂_pos, h_r2₂⟩
    h_lt

/-- **Liability AUC is sensitive to the neutral allele-frequency benchmark.**
    With fixed source `R²`, increasing drift strictly lowers the benchmark
    liability-threshold AUC. This is the exact metric-level AUC analogue of the
    benchmark `R²` drift result. -/
theorem liability_auc_sensitive_to_drift
    (V_A V_E fstS fstT : ℝ)
    (hVA : 0 < V_A) (hVE : 0 < V_E)
    (h_fst : fstS < fstT)
    (h_fst_bounds : 0 ≤ fstS ∧ fstT < 1)
    (hPhiStrict : StrictMono Phi) :
    0 < presentDayLiabilityAUC V_A V_E fstS -
      targetExactLiabilityAUCFromNeutralAFBenchmark V_A V_E fstT := by
  have h_drop :=
    targetLiabilityAUC_lt_source_of_neutralAF_benchmark
      V_A V_E fstS fstT hVA hVE h_fst h_fst_bounds hPhiStrict
  linarith

/-- **Brier worsens when R² drops and the prevalence factor weakly increases.**
    This theorem is about the Brier metric alone. Under the observable formula
    `Brier = π(1-π)(1-r2)`, a lower target `r2` together with a weakly larger
    prevalence factor implies a weakly worse target Brier score. -/
theorem brier_worsens_when_r2_drops_and_prevalence_factor_grows
    (π_source π_target r2_source r2_target : ℝ)
    (h_πs : 0 < π_source) (h_πs' : π_source < 1)
    (h_r2s' : r2_source < 1)
    -- R² drops in target
    (h_r2_drop : r2_target < r2_source)
    -- Prevalence factor is at least as large in target
    (h_prev : π_source * (1 - π_source) ≤ π_target * (1 - π_target)) :
    -- Target Brier ≥ source Brier (higher = worse)
    brierFromR2 π_source r2_source ≤ brierFromR2 π_target r2_target := by
  unfold brierFromR2 exactCalibratedBrierRiskFromR2
  have h1 : 0 < 1 - r2_source := by linarith
  have h2 : 0 < 1 - r2_target := by linarith
  -- (1 - r2_target) ≥ (1 - r2_source) and π_t(1-π_t) ≥ π_s(1-π_s)
  nlinarith [mul_nonneg (le_of_lt h_πs) (by linarith : 0 ≤ 1 - π_source)]

end R2VsAUC


/-!
## Calibration vs Discrimination

Calibration (predicted risk = observed risk) and discrimination
(ability to separate cases from controls) can degrade differently
across populations.
-/

section CalibrationVsDiscrimination

/-- **At fixed drift, exact liability AUC is preserved while CITL shifts exactly
with the mean-score offset.**
    This theorem formalizes the intended metric split on the repository's
    actual metrics:

    - discrimination is measured by exact liability-threshold AUC;
    - calibration is measured by calibration-in-the-large (CITL).

    If source and target have the same `fst`, then the exact liability transport
    map gives exactly the same AUC. If the target mean prediction is shifted by an
    additive offset `δ`, then CITL shifts by exactly `-δ`. This is the precise
    fixed-`fst` statement behind "rank-based discrimination can be preserved
    while calibration is lost." -/
theorem auc_preserved_citl_shift_at_fixed_fst
    (V_A V_E fst mean_obs mean_pred δ : ℝ) :
    targetExactLiabilityAUCFromNeutralAFBenchmark V_A V_E fst =
      presentDayLiabilityAUC V_A V_E fst ∧
    calibrationInTheLarge mean_obs (mean_pred + δ) =
      calibrationInTheLarge mean_obs mean_pred - δ := by
  constructor
  · rfl
  · unfold calibrationInTheLarge
    ring

/-- **Discrimination preserved while calibration is lost at fixed drift.**
    In the neutral allele-frequency benchmark, if source and target share the same
    drift level `fst`, then AUC is unchanged. If the source is calibrated in
    the large and the target mean prediction is shifted by a nonzero offset
    `δ`, then target absolute CITL becomes strictly worse.

    This is the actual fixed-`fst` result the surrounding prose was aiming at:
    AUC is preserved, while calibration loss is witnessed by a standard
    calibration metric rather than an `R²` surrogate. -/
theorem discrimination_preserved_calibration_lost
    (V_A V_E fst mean_obs mean_pred δ : ℝ)
    (h_src_cal : calibrationInTheLarge mean_obs mean_pred = 0)
    (h_shift : δ ≠ 0) :
    targetExactLiabilityAUCFromNeutralAFBenchmark V_A V_E fst =
      presentDayLiabilityAUC V_A V_E fst ∧
    |calibrationInTheLarge mean_obs mean_pred| <
      |calibrationInTheLarge mean_obs (mean_pred + δ)| := by
  rcases auc_preserved_citl_shift_at_fixed_fst V_A V_E fst mean_obs mean_pred δ with
    ⟨h_auc, h_citl_shift⟩
  refine ⟨h_auc, ?_⟩
  rw [h_src_cal]
  rw [h_citl_shift, h_src_cal]
  have h_shift_sub : 0 - δ ≠ 0 := by
    intro h
    apply h_shift
    linarith
  simp only [abs_zero]
  exact abs_pos.mpr h_shift_sub

/-- **Allele-frequency shift worsens the benchmark calibration slope and Brier score.**
    In the observable drift benchmark, a larger target `F_ST` lowers the shared
    linear regression slope coordinate
    `Cov(Y_target, Ŷ_source) / Var(Ŷ_source)` for the transported
    source-calibrated score from `PGSCalibrationTheory`.

    - the benchmark target calibration slope is strictly below the ideal source baseline
      `1`;
    - the calibration-slope deviation from perfect calibration is therefore
      strictly larger than the source value `0`, and equals exactly `1 - slope`;
    - the slope itself has the exact drift formula `(1 - fstT) / (1 - fstS)`;
    - at any nondegenerate prevalence `π`, the observable target Brier score is
      strictly worse than the source Brier score.

    This remains a benchmark slope/Brier theorem, not a complete mechanistic
    SNP-level calibration law. -/
theorem allele_freq_shift_disrupts_benchmark_calibration_slope_and_brier
    (π V_A V_E fstS fstT : ℝ)
    (hπ0 : 0 < π) (hπ1 : π < 1)
    (hVA : 0 < V_A) (hVE : 0 < V_E)
    (hfst : fstS < fstT)
    (hfst_bounds : 0 ≤ fstS ∧ fstT < 1) :
    let profile := neutralAFIdentityCalibrationProfile π π fstS fstT
    profile.slope < 1 ∧
    calibrationSlopeDeviation 1 < profile.slopeDeviation ∧
    profile.slopeDeviation = 1 - profile.slope ∧
    profile.slope = transportedLinearCalibrationSlope V_A fstS fstT ∧
    profile.slope = (1 - fstT) / (1 - fstS) ∧
    sourceBrierFromR2 π (presentDayR2 V_A V_E fstS) <
      targetBrierFromNeutralAFBenchmark π V_A V_E fstT := by
  dsimp
  have hfstS_lt_one : fstS < 1 := lt_trans hfst hfst_bounds.2
  have hslope_eq :
      transportedLinearCalibrationSlope V_A fstS fstT = (1 - fstT) / (1 - fstS) := by
    exact transportedLinearCalibrationSlope_eq_fst_ratio V_A fstS fstT hVA hfstS_lt_one
  have hprofile_eq_transport :
      (neutralAFIdentityCalibrationProfile π π fstS fstT).slope =
        transportedLinearCalibrationSlope V_A fstS fstT := by
    simp [neutralAFIdentityCalibrationProfile,
      transportedLinearCalibrationSlope_eq_neutralAFBenchmarkRatio, hVA, hfstS_lt_one]
  have hslope_lt :
      (neutralAFIdentityCalibrationProfile π π fstS fstT).slope < 1 := by
    rw [hprofile_eq_transport]
    exact transportedLinearCalibrationSlope_lt_one V_A fstS fstT hVA hfst
      (le_of_lt hfst_bounds.2)
  have hslope_dev_pos :
      calibrationSlopeDeviation 1 <
        (neutralAFIdentityCalibrationProfile π π fstS fstT).slopeDeviation := by
    unfold CalibrationProfile.slopeDeviation calibrationSlopeDeviation
    rw [show (1 : ℝ) - 1 = 0 by ring, abs_zero]
    have hneg :
        (neutralAFIdentityCalibrationProfile π π fstS fstT).slope - 1 < 0 := by
      linarith [hslope_lt]
    rw [abs_of_neg hneg]
    linarith
  have hslope_dev :
      (neutralAFIdentityCalibrationProfile π π fstS fstT).slopeDeviation =
        1 - (neutralAFIdentityCalibrationProfile π π fstS fstT).slope := by
    exact calibrationSlopeDeviation_eq_one_sub_of_lt_one
      (neutralAFIdentityCalibrationProfile π π fstS fstT).slope hslope_lt
  have hbrier :
      sourceBrierFromR2 π (presentDayR2 V_A V_E fstS) <
        targetBrierFromNeutralAFBenchmark π V_A V_E fstT := by
    exact targetBrier_strict_gt_source_of_neutralAF_benchmark
      π V_A V_E fstS fstT hπ0 hπ1 hVA hVE hfst hfst_bounds
  have hslope_eq_closed :
      (neutralAFIdentityCalibrationProfile π π fstS fstT).slope = (1 - fstT) / (1 - fstS) := by
    rw [hprofile_eq_transport, hslope_eq]
  exact ⟨hslope_lt, hslope_dev_pos, hslope_dev, hprofile_eq_transport, hslope_eq_closed, hbrier⟩

/-- **Dimension-to-information ratio for a target adaptation task.**
    In an orthogonal Fisher model with `d` target-specific parameters and
    per-sample Fisher information `I` for each parameter, the natural
    difficulty scale is `d / I`. Smaller values mean the target task can
    be estimated more precisely from the same effective sample size. -/
noncomputable def adaptationDifficultyIndex
    (nParams infoPerSample : ℝ) : ℝ :=
  nParams / infoPerSample

/-- **Trace-MSE lower bound under an orthogonal Fisher model.**
    For an unbiased estimator of `d` orthogonal target parameters, the summed
    estimation variance is lower-bounded by `(d / I) / n_eff`, where `I` is the
    per-sample Fisher information and `n_eff` is the effective target sample size. -/
noncomputable def fisherTraceMSELowerBound
    (nEff nParams infoPerSample : ℝ) : ℝ :=
  adaptationDifficultyIndex nParams infoPerSample / nEff

/-- **Effective sample size needed to beat a target trace-MSE threshold.**
    Solving `(d / I) / n_eff ≤ τ` for `n_eff` gives the exact threshold
    `(d / I) / τ` in the orthogonal Fisher model. -/
noncomputable def requiredEffectiveSampleSizeForTraceMSE
    (nParams infoPerSample targetTraceMSE : ℝ) : ℝ :=
  adaptationDifficultyIndex nParams infoPerSample / targetTraceMSE

/-- The `requiredEffectiveSampleSizeForTraceMSE` definition is the exact
    threshold corresponding to the Fisher trace-MSE lower bound. -/
theorem fisherTraceMSELowerBound_le_target_iff
    (nEff nParams infoPerSample targetTraceMSE : ℝ)
    (h_nEff : 0 < nEff)
    (h_target : 0 < targetTraceMSE) :
    fisherTraceMSELowerBound nEff nParams infoPerSample ≤ targetTraceMSE ↔
      requiredEffectiveSampleSizeForTraceMSE nParams infoPerSample targetTraceMSE ≤ nEff := by
  unfold fisherTraceMSELowerBound requiredEffectiveSampleSizeForTraceMSE adaptationDifficultyIndex
  constructor
  · intro h
    rw [div_le_iff₀ h_target]
    rw [div_le_iff₀ h_nEff] at h
    simpa [mul_comm, mul_left_comm, mul_assoc] using h
  · intro h
    rw [div_le_iff₀ h_nEff]
    rw [div_le_iff₀ h_target] at h
    simpa [mul_comm, mul_left_comm, mul_assoc] using h

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
  unfold adaptationDifficultyIndex
  have h_two_over_cal_le_disc : 2 / infoCal ≤ 2 / infoDisc := by
    have h_inv : 1 / infoCal ≤ 1 / infoDisc := by
      exact one_div_le_one_div_of_le h_infoDisc h_info_order
    have h_mul :=
      mul_le_mul_of_nonneg_left h_inv (show (0 : ℝ) ≤ 2 by norm_num)
    simpa [div_eq_mul_inv] using h_mul
  have h_two_over_disc_lt_m_over_disc : 2 / infoDisc < m / infoDisc := by
    exact div_lt_div_of_pos_right h_more_params h_infoDisc
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
  unfold brierFromR2 exactCalibratedBrierRiskFromR2
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
  unfold brierFromR2 exactCalibratedBrierRiskFromR2
  have h_prev : 0 < π * (1 - π) := by nlinarith
  nlinarith

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
        (sourceR2FromSourceWeights m - targetR2FromSourceWeights m) := by
  unfold brierDiscriminationLoss
  rw [targetCalibratedBrierFromSourceWeights_eq_explainedR2_chart,
    sourceCalibratedBrierFromSourceWeightsAtPrevalence_eq_explainedR2_chart]
  unfold TransportedMetrics.calibratedBrier
  ring_nf

/-- Exact formula for the outcome-scale contribution to Brier worsening when
the mechanistic source score is re-evaluated at a different observed prevalence
coordinate. -/
theorem brierCalibrationLoss_eq
    {p q : ℕ} (πSource : ℝ) (m : CrossPopulationMetricModel p q) :
    brierCalibrationLoss πSource m =
      (m.targetPrevalence * (1 - m.targetPrevalence) -
          πSource * (1 - πSource)) *
        (1 - sourceR2FromSourceWeights m) := by
  unfold brierCalibrationLoss
  rw [sourceCalibratedBrierFromSourceWeightsAtPrevalence_eq_explainedR2_chart,
    sourceCalibratedBrierFromSourceWeightsAtPrevalence_eq_explainedR2_chart]
  unfold TransportedMetrics.calibratedBrier
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
    (h_r2_drop : targetR2FromSourceWeights m < sourceR2FromSourceWeights m) :
    0 < brierDiscriminationLoss m := by
  unfold brierDiscriminationLoss
  exact sub_pos.mpr <|
    brierFromR2_strictAnti m.targetPrevalence
      m.targetPrevalence_pos m.targetPrevalence_lt_one
      (by simpa [targetR2FromSourceWeights, sourceR2FromSourceWeights] using h_r2_drop)

/-- If the Bernoulli variance factor increases from source to target on the
same mechanistic source score, the outcome-scale contribution is positive. -/
theorem brierCalibrationLoss_pos_of_prevalence_factor_increase
    {p q : ℕ} (πSource : ℝ) (m : CrossPopulationMetricModel p q)
    (h_source_r2_unit : sourceR2FromSourceWeights m ∈ Set.Ico 0 1)
    (h_prev_factor :
      πSource * (1 - πSource) <
        m.targetPrevalence * (1 - m.targetPrevalence)) :
    0 < brierCalibrationLoss πSource m := by
  rw [brierCalibrationLoss_eq]
  have h_prev_gap :
      0 < m.targetPrevalence * (1 - m.targetPrevalence) -
        πSource * (1 - πSource) := by
    linarith
  have h_one_minus_source_r2 : 0 < 1 - sourceR2FromSourceWeights m := by
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
    (h_source_r2_unit : sourceR2FromSourceWeights m ∈ Set.Ico 0 1)
    (h_r2_drop : targetR2FromSourceWeights m < sourceR2FromSourceWeights m)
    (h_prev_factor :
      πSource * (1 - πSource) <
        m.targetPrevalence * (1 - m.targetPrevalence))
    (h_scale_dom :
      m.targetPrevalence * (1 - m.targetPrevalence) *
          (sourceR2FromSourceWeights m - targetR2FromSourceWeights m) <
        (m.targetPrevalence * (1 - m.targetPrevalence) -
            πSource * (1 - πSource)) *
          (1 - sourceR2FromSourceWeights m)) :
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


/-!
## Precision vs Recall in PGS Risk Stratification

Clinical PGS use involves classifying individuals as high-risk
or normal-risk. Precision and recall can have different portability.
-/

section PrecisionRecall

/-- **Precision (PPV) of high-risk classification.**
    PPV = P(actually high risk | PGS says high risk).
    Depends on prevalence via Bayes' theorem. -/
noncomputable def metricPPV (sensitivity specificity prevalence : ℝ) : ℝ :=
  sensitivity * prevalence /
    (sensitivity * prevalence + (1 - specificity) * (1 - prevalence))

/-- Absolute portability gap for sensitivity between source and target use cases. -/
def sensitivityPortabilityGap (sensSource sensTarget : ℝ) : ℝ :=
  |sensTarget - sensSource|

/-- Absolute portability gap for PPV between source and target prevalences. -/
noncomputable def ppvPortabilityGap
    (sensitivity specificity prevalenceSource prevalenceTarget : ℝ) : ℝ :=
  |metricPPV sensitivity specificity prevalenceTarget -
    metricPPV sensitivity specificity prevalenceSource|

/- **Recall (sensitivity) of high-risk classification.**
    Sensitivity = P(PGS says high risk | actually high risk).
    Depends on the PGS's discriminative ability. -/

/-- **PPV is strictly increasing in prevalence.**
    At fixed sensitivity and specificity, higher prevalence yields higher PPV.
    This is the concrete base-rate sensitivity of PPV. -/
theorem ppv_increases_with_prevalence
    (se sp K₁ K₂ : ℝ)
    (h_se : 0 < se) (h_sp1 : sp < 1)
    (h_K1 : 0 < K₁) (h_K1' : K₁ < 1)
    (h_K2' : K₂ < 1)
    (h_order : K₁ < K₂) :
    metricPPV se sp K₁ < metricPPV se sp K₂ := by
  unfold metricPPV
  have h_d1 : 0 < se * K₁ + (1 - sp) * (1 - K₁) := by nlinarith
  have h_d2 : 0 < se * K₂ + (1 - sp) * (1 - K₂) := by nlinarith
  have h_d1_ne : se * K₁ + (1 - sp) * (1 - K₁) ≠ 0 := ne_of_gt h_d1
  have h_d2_ne : se * K₂ + (1 - sp) * (1 - K₂) ≠ 0 := ne_of_gt h_d2
  field_simp [h_d1_ne, h_d2_ne]
  nlinarith [mul_pos h_se (sub_pos.mpr h_sp1)]

/-- **If prevalence shifts while sensitivity and specificity are fixed, PPV changes but sensitivity does not.**
    This is the concrete metric statement behind the portability claim. Under a
    pure prevalence shift with identical sensitivity and specificity,
    sensitivity has zero portability gap while PPV has a strictly positive gap,
    so the PPV portability gap strictly exceeds the sensitivity portability gap. -/
theorem sensitivity_more_portable_than_ppv
    (se sp K_source K_target : ℝ)
    (h_se : 0 < se) (h_sp1 : sp < 1)
    (h_Ks : 0 < K_source) (h_Ks' : K_source < 1)
    (h_Kt' : K_target < 1)
    (h_order : K_source < K_target) :
    sensitivityPortabilityGap se se <
      ppvPortabilityGap se sp K_source K_target := by
  have h_ppv :
      metricPPV se sp K_source < metricPPV se sp K_target :=
    ppv_increases_with_prevalence
      se sp K_source K_target h_se h_sp1 h_Ks h_Ks' h_Kt' h_order
  have h_gap_pos :
      0 < metricPPV se sp K_target - metricPPV se sp K_source := sub_pos.mpr h_ppv
  have h_ppv_gap :
      0 < ppvPortabilityGap se sp K_source K_target := by
    unfold ppvPortabilityGap
    rw [abs_of_pos h_gap_pos]
    exact h_gap_pos
  simpa [sensitivityPortabilityGap] using h_ppv_gap

/-- **Number needed to screen (NNS) portability.**
    NNS = 1/PPV. If PPV drops, NNS increases → more individuals
    need screening for each true positive. -/
theorem nns_increases_with_ppv_drop
    (ppv₁ ppv₂ : ℝ)
    (h_ppv₂ : 0 < ppv₂)
    (h_drop : ppv₂ < ppv₁) :
    1 / ppv₁ < 1 / ppv₂ := by
  exact div_lt_div_of_pos_left one_pos h_ppv₂ h_drop

/-- **F1 score captures precision-recall balance.**
    F1 = 2 × PPV × sensitivity / (PPV + sensitivity).
    F1 portability reflects both precision and recall portability. -/
noncomputable def f1ScoreMetric (precision sens : ℝ) : ℝ :=
  2 * precision * sens / (precision + sens)

/-- F1 is bounded above by 1 when both precision and sensitivity lie in `(0,1]`. -/
theorem f1_le_one
    (precision sens : ℝ)
    (h_p : 0 < precision) (h_r : 0 < sens)
    (h_p1 : precision ≤ 1) (h_r1 : sens ≤ 1) :
    f1ScoreMetric precision sens ≤ 1 := by
  unfold f1ScoreMetric
  rw [div_le_one (by linarith)]
  nlinarith [mul_nonneg (le_of_lt h_p) (by linarith : 0 ≤ 1 - sens),
             mul_nonneg (le_of_lt h_r) (by linarith : 0 ≤ 1 - precision)]

end PrecisionRecall


/-!
## Metric Choice Affects Clinical Decision-Making

Different metrics lead to different clinical decisions, so metric-
specific portability has direct practical consequences.
-/

section MetricAndClinicalDecisions

/-- **Screening PPV can shift even when case-finding sensitivity is unchanged.**
    Under a pure prevalence shift with identical sensitivity and specificity,
    the sensitivity portability gap stays below the PPV portability gap, and the
    higher-prevalence use case has strictly higher PPV.
    This is the metric split relevant to screening versus case-finding use
    cases. -/
theorem different_uses_different_metrics
    (se sp K_source K_target : ℝ)
    (h_se : 0 < se) (h_sp1 : sp < 1)
    (h_Ks : 0 < K_source) (h_Ks' : K_source < 1)
    (h_Kt' : K_target < 1)
    (h_order : K_source < K_target) :
    sensitivityPortabilityGap se se <
      ppvPortabilityGap se sp K_source K_target ∧
    metricPPV se sp K_source < metricPPV se sp K_target := by
  constructor
  · exact sensitivity_more_portable_than_ppv
      se sp K_source K_target h_se h_sp1 h_Ks h_Ks' h_Kt' h_order
  · exact ppv_increases_with_prevalence
      se sp K_source K_target h_se h_sp1 h_Ks h_Ks' h_Kt' h_order

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
  have h_tp : sens_target * π < sens_source * π := by
    exact mul_lt_mul_of_pos_right h_sens h_π
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
the old drift benchmark. If the transported source weights lose explained
signal in the target population, then:

- target `R²` is strictly lower;
- exact target liability-threshold AUC is strictly lower; and
- exact target calibrated Brier is strictly worse when source and target are
  compared on the same target prevalence scale.

The point is that the repository's deployed metric profile can report joint
deterioration across discrimination- and calibration-sensitive metrics from the
same mechanistic target state. -/
theorem metrics_both_degrade_under_drift
    {p q : ℕ} (m : CrossPopulationMetricModel p q)
    (h_source_r2_unit : sourceR2FromSourceWeights m ∈ Set.Ico 0 1)
    (h_target_r2_unit : targetR2FromSourceWeights m ∈ Set.Ico 0 1)
    (h_r2_drop : targetR2FromSourceWeights m < sourceR2FromSourceWeights m)
    (hPhiStrict : StrictMono Phi) :
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
      targetLiabilityAUCFromSourceWeights_eq_explainedR2_chart,
      sourceLiabilityAUCFromSourceWeights_eq_explainedR2_chart]
    exact liabilityAUCFromExplainedR2_strictMonoOn_unitInterval hPhiStrict
      h_target_r2_unit h_source_r2_unit h_r2_drop
  have h_brier :
      (sourceMetricProfileFromSourceWeightsAtTargetPrevalence m).brier <
        (targetMetricProfileFromSourceWeights m).brier := by
    rw [sourceMetricProfileFromSourceWeightsAtTargetPrevalence_brier,
      targetMetricProfileFromSourceWeights_brier,
      sourceCalibratedBrierFromSourceWeightsAtPrevalence_eq_explainedR2_chart,
      targetCalibratedBrierFromSourceWeights_eq_explainedR2_chart]
    simpa [brierFromR2, sourceBrierFromR2, TransportedMetrics.calibratedBrier] using
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
noncomputable abbrev brierScoreMetric (p y : ℝ) : ℝ := brierScore p y

/-- The local metric surface is exactly the core Brier score object from
    `Conclusions`. -/
@[simp] theorem brierScoreMetric_eq_core (p y : ℝ) :
    brierScoreMetric p y = brierScore p y := by
  rfl

/-- Brier score is nonneg. -/
theorem brier_nonneg (p y : ℝ) : 0 ≤ brierScoreMetric p y := by
  simpa [brierScoreMetric, brierScore] using sq_nonneg (y - p)

/- **Log score (cross-entropy) is also proper.**
    Log(p, y) = -y log(p) - (1-y) log(1-p).
    Log score is more sensitive to calibration than Brier. -/

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
  unfold brierFromR2 exactCalibratedBrierRiskFromR2
  have h1 : π * (1 - π) ≤ 1/4 := by nlinarith [sq_nonneg (π - 1/2)]
  have h_one_minus_pi : 0 ≤ 1 - π := by linarith
  have h2 : 0 ≤ 1 - r2 := by linarith
  have h3 : 1 - r2 ≤ 1 := by linarith
  have h_nonneg : 0 ≤ π * (1 - π) * (1 - r2) := by
    exact mul_nonneg (mul_nonneg h_π h_one_minus_pi) h2
  nlinarith

/-- **Brier portability decomposition as the exact proper-score result on the
mechanistic transport model.**

Because the exported deployed Brier surface is an exact proper scoring rule on
the source/target variance state, total Brier worsening decomposes into:

- a mechanistic signal-loss term from the target SNP/LD/effect state; and
- an outcome-scale term from evaluating the same source score at the target
  prevalence scale.

If the latter dominates, it contributes more than half of the total Brier
worsening. -/
theorem brier_proper_score_portability_decomposition
    {p q : ℕ} (πSource : ℝ) (m : CrossPopulationMetricModel p q)
    (h_source_r2_unit : sourceR2FromSourceWeights m ∈ Set.Ico 0 1)
    (h_r2_drop : targetR2FromSourceWeights m < sourceR2FromSourceWeights m)
    (h_prev_factor :
      πSource * (1 - πSource) <
        m.targetPrevalence * (1 - m.targetPrevalence))
    (h_scale_dom :
      m.targetPrevalence * (1 - m.targetPrevalence) *
          (sourceR2FromSourceWeights m - targetR2FromSourceWeights m) <
        (m.targetPrevalence * (1 - m.targetPrevalence) -
            πSource * (1 - πSource)) *
          (1 - sourceR2FromSourceWeights m)) :
    targetCalibratedBrierFromSourceWeights m -
      sourceCalibratedBrierFromSourceWeightsAtPrevalence m πSource =
        brierDiscriminationLoss m +
        brierCalibrationLoss πSource m ∧
    (targetCalibratedBrierFromSourceWeights m -
        sourceCalibratedBrierFromSourceWeightsAtPrevalence m πSource) / 2 <
      brierCalibrationLoss πSource m := by
  rcases brier_increase_mainly_calibration
      πSource m h_source_r2_unit h_r2_drop h_prev_factor h_scale_dom with
    ⟨h_decomp, _h_disc_pos, _h_cal_pos, _h_dom, h_half⟩
  exact ⟨h_decomp, h_half⟩

end ProperScoringRules

end Calibrator
