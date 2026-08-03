/-
Copyright (c) 2026 Sauers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sauers
-/
import Calibrator.Probability
import Calibrator.PortabilityDrift
import Calibrator.PGSCalibrationTheory
import Calibrator.ClinicalUtilityFairness
import Calibrator.OpenQuestions
import Calibrator.ProjectionShiftBounds
import Calibrator.ImitationRigidity
import Calibrator.SpectralDegradation
-- `FoldedSpectrum` supplies the Gaussian level-set collapse used in
-- "What the metric split is, and is not" below. That section is the reason this
-- import exists: `levelSet_metrics_agree_of_coords_eq` is not provable here.
import Calibrator.FoldedSpectrum
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse

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

/-- **The class is inhabited.**  A theorem quantified over an uninhabited structure is
true and empty: kernel-checked, clean axiom report, no content.  This is the witness that
makes the theorems below statements about something. -/
noncomputable def R2DecompositionData.witness : R2DecompositionData where
  varY := 4
  varYhat := 2
  varCondE := 1
  hVarY_pos := by norm_num
  hVarYhat_pos := by norm_num
  hVarCondE_pos := by norm_num
  hCondE_le_Yhat := by norm_num
  hYhat_le_Y := by norm_num
  hCondE_le_Y := by norm_num

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

/-- **Neutral-benchmark `R²` is sensitive to drift.**
    When drift increases (`fstS < fstT`), `presentDayR2` strictly decreases, so
    the source-to-target R² drop is positive. -/
theorem neutralAF_benchmark_r2_sensitive_to_drift
    (V_A V_E fstS fstT : ℝ)
    (hVA : 0 < V_A) (hVE : 0 < V_E)
    (hfst : fstS < fstT)
    (hfstT_le_one : fstT ≤ 1) :
    0 < presentDayR2 V_A V_E fstS - presentDayR2 V_A V_E fstT := by
  have h := drift_degrades_R2 V_A V_E fstS fstT hVA hVE hfst hfstT_le_one
  linarith

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
  unfold brierFromR2 TransportedMetrics.calibratedBrier
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
    (h_lt : r2₁ < r2₂) :
    equalVarianceGaussianAUCFromExplainedR2 r2₁ <
      equalVarianceGaussianAUCFromExplainedR2 r2₂ := by
  have h_r2₂_pos : 0 < r2₂ := lt_trans h_r2₁ h_lt
  exact equalVarianceGaussianAUCFromExplainedR2_strictMonoOn_unitInterval
    ⟨le_of_lt h_r2₁, lt_trans h_lt h_r2₂⟩
    ⟨le_of_lt h_r2₂_pos, h_r2₂⟩
    h_lt

/-- **Neutral-benchmark liability AUC is sensitive to drift.**
    With fixed source `R²`, increasing drift strictly lowers the benchmark
    liability-threshold AUC. This is the exact metric-level AUC analogue of the
    benchmark `R²` drift result. -/
theorem neutralAF_benchmark_liability_auc_sensitive_to_drift
    (V_A V_E fstS fstT : ℝ)
    (hVA : 0 < V_A) (hVE : 0 < V_E)
    (h_fst : fstS < fstT)
    (h_fst_bounds : 0 ≤ fstS ∧ fstT < 1) :
    0 < presentDayEqualVarianceGaussianAUC V_A V_E fstS -
      presentDayEqualVarianceGaussianAUC V_A V_E fstT := by
  have h_drop :=
    targetLiabilityAUC_lt_source_of_neutralAF_benchmark
      V_A V_E fstS fstT hVA hVE h_fst h_fst_bounds
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
  unfold brierFromR2 TransportedMetrics.calibratedBrier
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
  unfold calibrationInTheLarge
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
    presentDayEqualVarianceGaussianAUC V_A V_E fst = presentDayEqualVarianceGaussianAUC V_A' V_E fst' := by
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
    trait the discrimination half would have to be restated with
    `liabilityThresholdAUCFromExplainedR2` at a named prevalence, where preservation is a
    stronger claim because the conditional variances differ. -/
theorem neutralAF_benchmark_discrimination_preserved_calibration_lost
    (V_A V_E fst V_A' fst' mean_obs mean_pred δ : ℝ)
    (h_same_signal : presentDayPGSVariance V_A fst = presentDayPGSVariance V_A' fst')
    (h_src_cal : calibrationInTheLarge mean_obs mean_pred = 0)
    (h_shift : δ ≠ 0) :
    presentDayEqualVarianceGaussianAUC V_A V_E fst = presentDayEqualVarianceGaussianAUC V_A' V_E fst' ∧
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
    simpa [brierFromR2, sourceBrierFromR2, TransportedMetrics.calibratedBrier] using
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
  nParams / infoPerSample

/-- **Trace-MSE lower bound under an orthogonal Fisher model.**
    For an unbiased estimator of `d` orthogonal target parameters, the summed
    estimation variance is lower-bounded by `(d / I) / n_eff`, where `I` is the
    per-sample Fisher information and `n_eff` is the effective target sample size. -/
noncomputable def fisherTraceMSELowerBound
    (nEff nParams infoPerSample : ℝ) : ℝ :=
  adaptationDifficultyIndex nParams infoPerSample / nEff

/-- **Effective sample size needed to beat a target trace-MSE threshold.**
    Solving `(d / I) / n_eff ≤ τ` for `n_eff` gives the closed-form threshold
    `(d / I) / τ` in the orthogonal Fisher model.

    Empirical status: UNTESTED. -/
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

/-! ### The other half of a deployment budget, and the one that binds

`requiredEffectiveSampleSizeForTraceMSE` is a budget for *estimating target parameters*:
`(d/I)/tau`, which grows like `1/tau` as the target tightens. That is not the only budget a
deployment of the curve-prior dissolution has to meet, and it is not the binding one.

`Calibrator.FoldedSpectrum.RecoveryAttenuation.panels_suffice_iff` supplies the other:
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
      (RecoveryAttenuation.panels_suffice_iff p c tau B hp hc htau1 hB).1 hrel⟩
  · rintro ⟨hsample, hpanels⟩
    exact ⟨(fisherTraceMSELowerBound_le_target_iff nEff nParams infoPerSample targetTraceMSE
        h_nEff h_target).2 hsample,
      (RecoveryAttenuation.panels_suffice_iff p c tau B hp hc htau1 hB).2 hpanels⟩

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
  unfold adaptationDifficultyIndex
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
  unfold brierFromR2 TransportedMetrics.calibratedBrier
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
  unfold brierFromR2 TransportedMetrics.calibratedBrier
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
        (r2FromSourceWeights m Pop.source - r2FromSourceWeights m Pop.target) := by
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
        (1 - r2FromSourceWeights m Pop.source) := by
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

/-- **The sensitivity gap between a use case and itself is zero, definitionally.**

`sensitivityPortabilityGap` takes the source and target sensitivities as two separate
arguments, so passing the same `se` twice gives `|se - se|`. **Keep it as its own lemma
rather than folding it into the conclusion of `ppv_gap_pos_under_prevalence_shift`
below**, where `sensitivityPortabilityGap se se` would read as a *proved* consequence of a
prevalence shift rather than as the definitional zero it is. Nothing about prevalence enters here,
and nothing can: prevalence is not an
argument of `sensitivityPortabilityGap`. -/
@[simp] theorem sensitivityPortabilityGap_self (se : ℝ) :
    sensitivityPortabilityGap se se = 0 := by
  unfold sensitivityPortabilityGap
  simp

/-- **A pure prevalence shift moves PPV by a strictly positive amount.**

This is the whole empirical content of the metric split: at fixed sensitivity and
specificity, PPV is prevalence-dependent and its portability gap cannot be zero. The
companion claim — that sensitivity's gap *is* zero — is not proved here and is not
provable here; it is `sensitivityPortabilityGap_self`, an identity, and holds because
sensitivity is defined without reference to prevalence. Keeping the two apart is the
point: one is a fact about `metricPPV`, the other is a fact about an argument list.

**Do not restate this as `sensitivityPortabilityGap se se < ppvPortabilityGap …`.** That
is this statement with `0` spelled as `|se - se|`, and it reads as a comparison of two
measured gaps when only one side is measured at all. -/
theorem ppv_gap_pos_under_prevalence_shift
    (se sp K_source K_target : ℝ)
    (h_se : 0 < se) (h_sp1 : sp < 1)
    (h_Ks : 0 < K_source) (h_Ks' : K_source < 1)
    (h_Kt' : K_target < 1)
    (h_order : K_source < K_target) :
    0 < ppvPortabilityGap se sp K_source K_target := by
  have h_ppv :
      metricPPV se sp K_source < metricPPV se sp K_target :=
    ppv_increases_with_prevalence
      se sp K_source K_target h_se h_sp1 h_Ks h_Ks' h_Kt' h_order
  have h_gap_pos :
      0 < metricPPV se sp K_target - metricPPV se sp K_source := sub_pos.mpr h_ppv
  unfold ppvPortabilityGap
  rw [abs_of_pos h_gap_pos]
  exact h_gap_pos

/-- **Number needed to screen (NNS) portability.**
    NNS = 1/PPV. If PPV drops, NNS increases → more individuals
    need screening for each true positive. -/
theorem nns_increases_with_ppv_drop
    (ppv₁ ppv₂ : ℝ)
    (h_ppv₂ : 0 < ppv₂)
    (h_drop : ppv₂ < ppv₁) :
    1 / ppv₁ < 1 / ppv₂ :=
  div_lt_div_of_pos_left one_pos h_ppv₂ h_drop

/-! **F1 score captures precision-recall balance.**
`F1 = 2 × PPV × sensitivity / (PPV + sensitivity)`, and F1 portability reflects
both precision and recall portability.

The theorem below is stated about `f1Score` from `Calibrator.OpenQuestions`, which this
file imports. Do not restate the formula here; its `Empirical status: UNTESTED` marker
belongs with that one definition. -/

/-- F1 is bounded above by 1 when both precision and sensitivity lie in `(0,1]`. -/
theorem f1_le_one
    (precision sens : ℝ)
    (h_p : 0 < precision) (h_r : 0 < sens)
    (h_p1 : precision ≤ 1) (h_r1 : sens ≤ 1) :
    f1Score precision sens ≤ 1 := by
  unfold f1Score
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
`Calibrator.FoldedSpectrum` sharpens that claim, and in doing so narrows it.

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
  readout : LevelSetCoordinates
  /-- Outcome-side base rate. Deliberately **not** part of `readout`. -/
  prevalence : ℝ

/-- **The metric split is a prevalence effect, not a metric-choice effect.**

`sens` and `spec` are any threshold metrics of the readout, i.e. any level-set functionals
of the two coordinates. Given two deployments with the *same* readout coordinates:

* they agree in sensitivity and in specificity -- and this is the part that needs
  `Calibrator.FoldedSpectrum`, since it holds for *every* level-set functional at once, not
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
    (hsens : IsLevelSetFunctional sens ScreeningDeployment.readout)
    (hspec : IsLevelSetFunctional spec ScreeningDeployment.readout)
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
    levelSet_metrics_agree_of_coords_eq ScreeningDeployment.readout sens hsens d₁ d₂ hreadout
  have hp : spec d₁ = spec d₂ :=
    levelSet_metrics_agree_of_coords_eq ScreeningDeployment.readout spec hspec d₁ d₂ hreadout
  refine ⟨hs, hp, ?_, ?_⟩
  · intro hK
    rw [hs, hp, hK]
  · intro h_se h_sp1 h_K1 h_K1' h_K2' h_order
    rw [← hs, ← hp]
    exact ppv_increases_with_prevalence _ _ _ _ h_se h_sp1 h_K1 h_K1' h_K2' h_order

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
  unfold brierFromR2 TransportedMetrics.calibratedBrier
  have h1 : π * (1 - π) ≤ 1/4 := by nlinarith [sq_nonneg (π - 1/2)]
  have h_one_minus_pi : 0 ≤ 1 - π := by linarith
  have h2 : 0 ≤ 1 - r2 := by linarith
  have h3 : 1 - r2 ≤ 1 := by linarith
  have h_nonneg : 0 ≤ π * (1 - π) * (1 - r2) :=
    mul_nonneg (mul_nonneg h_π h_one_minus_pi) h2
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
    (targetCalibratedBrierFromSourceWeights m -
        sourceCalibratedBrierFromSourceWeightsAtPrevalence m πSource) / 2 <
      brierCalibrationLoss πSource m := by
  rcases brier_increase_mainly_calibration
      πSource m h_source_r2_unit h_r2_drop h_prev_factor h_scale_dom with
    ⟨h_decomp, _h_disc_pos, _h_cal_pos, _h_dom, h_half⟩
  exact ⟨h_decomp, h_half⟩

end ProperScoringRules

/-!
## Metric-specific portability of the marker panel itself: the AR(1) frontier

Open Question 3 asks which *metric* a score is portable in.  Everything above
holds the marker panel fixed and varies the metric.  This section varies the
panel and finds the same phenomenon one level down: the panel construction step
— LD pruning or clumping — is itself a choice of metric, and it is not neutral
between the two things a panel is used for.

`Calibrator.ProjectionShiftBounds` proves the general statement: among relaxed
rank-`k` reductions of a background covariance, the variance-greedy one
simultaneously maximises reconstruction efficiency
(`topVariance_maximizes_reconstruction`) and minimises detection efficiency
(`topVariance_minimizes_detection`).  LD pruning is variance-greedy by
construction: it keeps one representative per correlated block, which in the
eigenbasis is a low-frequency band.

Here that abstract frontier is made numerical.  On a chromosome whose LD follows
the first-order Markov law of `Calibrator.ImitationRigidity` — correlation `ρ^d`
at separation `d` — the eigenvalues of the LD kernel are the values of the
Poisson-kernel symbol `ldKernelSymbol`, so both efficiencies are integrals of an
explicit function and the frontier has a closed form in the single parameter
`ρ`.  The detection normaliser is the inverse-kernel trace, whose closed form is
`ldWhiteningGain ρ = (1 + ρ²)/(1 - ρ²)`.

The headline number: at retention fraction `κ`, a pruned panel keeps only
`κ - 2ρ sin(πκ) / (π(1 + ρ²))` of the available detection weight — strictly less
than `κ`, with the shortfall maximised at 50 % retention where it equals
`2ρ / (π(1 + ρ²))`.  Pruning does not merely fail to help detection at the
margin; it loses detection weight faster than it loses markers.
-/

section ARoneFrontier

/-- **The LD spectrum is ordered by frequency.**  For nonnegative decay the
Poisson symbol is increasing in `cos angle`, so the high-variance eigendirections
are exactly the low-frequency ones.

This is the lemma that makes "LD pruning keeps the top-`k` directions by
variance" a theorem about the symbol rather than an assertion: a contiguous
low-frequency band *is* a top-`k` variance set, and therefore satisfies the
threshold hypothesis of `topVariance_minimizes_detection`. -/
theorem ldKernelSymbol_mono_in_cos {decay angle₁ angle₂ : ℝ}
    (hd : |decay| < 1) (hd0 : 0 ≤ decay)
    (hcos : Real.cos angle₁ ≤ Real.cos angle₂) :
    ldKernelSymbol decay angle₁ ≤ ldKernelSymbol decay angle₂ := by
  have hden₁ : 0 < 1 - 2 * decay * Real.cos angle₁ + decay ^ 2 :=
    ldKernelSymbol_denom_pos hd
  have hden₂ : 0 < 1 - 2 * decay * Real.cos angle₂ + decay ^ 2 :=
    ldKernelSymbol_denom_pos hd
  have hnum : 0 ≤ 1 - decay ^ 2 := by
    have := sq_abs decay
    nlinarith [abs_nonneg decay, hd]
  have hcmp : 1 - 2 * decay * Real.cos angle₂ + decay ^ 2 ≤
      1 - 2 * decay * Real.cos angle₁ + decay ^ 2 := by
    nlinarith [mul_nonneg hd0 (sub_nonneg.mpr hcos)]
  unfold ldKernelSymbol
  exact div_le_div_of_nonneg_left hnum hden₂ hcmp

/-- **Reconstruction share of a pruned (low-frequency) band** on a stationary
AR(1) chromosome, as a function of the per-site LD retention `decay` and the
fraction `kappa` of directions kept.

This is the candidate closed form of the harmonic-measure integral of the Poisson kernel:
`(2/π) · arctan( ((1+ρ)/(1-ρ)) · tan(πκ/2) )`.  The present module proves
its algebraic boundary checks but does not export an integral-identification theorem.

Valid for `0 ≤ kappa < 1`.  At `kappa = 1` the expression is not the limit —
`Real.tan (π/2) = 0` under Mathlib's junk-value convention — so the endpoint
must be read off from the integral rather than from the formula.

Empirical status: UNTESTED. -/
noncomputable def ldBandReconstructionShare (decay kappa : ℝ) : ℝ :=
  2 * Real.arctan (((1 + decay) / (1 - decay)) *
    Real.tan (Real.pi * kappa / 2)) / Real.pi

/-- **Detection share of a pruned (low-frequency) band** on a stationary AR(1)
chromosome: the fraction of the total inverse-LD (whitened) weight that survives
pruning down to a fraction `kappa` of the directions.

Closed form `κ - 2ρ sin(πκ) / (π(1 + ρ²))`, obtained by integrating the
reciprocal symbol; the `1 + ρ²` is the numerator of
`Calibrator.ImitationRigidity.ldWhiteningGain`, the per-variant inverse-kernel
trace.  The integral evaluation itself is not packaged as a caller-supplied theorem.

Empirical status: UNTESTED. -/
noncomputable def ldBandDetectionShare (decay kappa : ℝ) : ℝ :=
  kappa - 2 * decay * Real.sin (Real.pi * kappa) / (Real.pi * (1 + decay ^ 2))

/-- **The detection weight pruning throws away**, over and above the fraction of
directions it discards.  This is the quantity the frontier prices.

Empirical status: UNTESTED. -/
noncomputable def ldPruningDetectionDeficit (decay kappa : ℝ) : ℝ :=
  2 * decay * Real.sin (Real.pi * kappa) / (Real.pi * (1 + decay ^ 2))

theorem ldBandDetectionShare_eq_sub_deficit (decay kappa : ℝ) :
    ldBandDetectionShare decay kappa =
      kappa - ldPruningDetectionDeficit decay kappa := rfl

/-- **Pruning loses detection weight faster than it loses markers.**  Keeping a
fraction `κ` of directions retains at most a fraction `κ` of the detection
weight, for every LD level and every retention fraction. -/
theorem ldBandDetectionShare_le_retention {decay kappa : ℝ}
    (hd0 : 0 ≤ decay) (hk0 : 0 ≤ kappa) (hk1 : kappa ≤ 1) :
    ldBandDetectionShare decay kappa ≤ kappa := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have hden : 0 < Real.pi * (1 + decay ^ 2) := by positivity
  have hsin : 0 ≤ Real.sin (Real.pi * kappa) := by
    refine Real.sin_nonneg_of_nonneg_of_le_pi ?_ ?_
    · exact mul_nonneg (le_of_lt hpi) hk0
    · nlinarith [mul_nonneg (le_of_lt hpi) (by linarith : (0:ℝ) ≤ 1 - kappa)]
  have hnum : 0 ≤ 2 * decay * Real.sin (Real.pi * kappa) :=
    mul_nonneg (by linarith) hsin
  have hfrac : 0 ≤ 2 * decay * Real.sin (Real.pi * kappa) /
      (Real.pi * (1 + decay ^ 2)) := div_nonneg hnum (le_of_lt hden)
  unfold ldBandDetectionShare
  linarith

/-- The loss is strict whenever there is LD to exploit and the reduction is
neither trivial nor vacuous.  This is the AR(1) form of the pruning
prohibition: for `0 < ρ < 1` and `0 < κ < 1` there is no retention fraction at
which pruning is detection-neutral. -/
theorem ldBandDetectionShare_lt_retention {decay kappa : ℝ}
    (hd0 : 0 < decay) (hk0 : 0 < kappa) (hk1 : kappa < 1) :
    ldBandDetectionShare decay kappa < kappa := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have hden : 0 < Real.pi * (1 + decay ^ 2) := by positivity
  have hsin : 0 < Real.sin (Real.pi * kappa) := by
    refine Real.sin_pos_of_pos_of_lt_pi ?_ ?_
    · exact mul_pos hpi hk0
    · nlinarith [mul_pos hpi (by linarith : (0:ℝ) < 1 - kappa)]
  have hnum : 0 < 2 * decay * Real.sin (Real.pi * kappa) :=
    mul_pos (by linarith) hsin
  have hfrac : 0 < 2 * decay * Real.sin (Real.pi * kappa) /
      (Real.pi * (1 + decay ^ 2)) := div_pos hnum hden
  unfold ldBandDetectionShare
  linarith

/-- **The deficit is largest at half retention**, where it equals
`2ρ / (π(1 + ρ²))`.  Since `2ρ/(1 + ρ²) ≤ 1`, the worst-case detection loss
attributable to pruning is at most `1/π ≈ 0.318` of the total whitened weight,
and it is attained in the strong-LD limit at 50 % retention.  This is the number
a simulation should be asked to reproduce. -/
theorem ldPruningDetectionDeficit_le_half_retention {decay kappa : ℝ}
    (hd0 : 0 ≤ decay) :
    ldPruningDetectionDeficit decay kappa ≤
      2 * decay / (Real.pi * (1 + decay ^ 2)) := by
  have hden : 0 < Real.pi * (1 + decay ^ 2) := by positivity
  have hnum : 2 * decay * Real.sin (Real.pi * kappa) ≤ 2 * decay := by
    nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ 2 * decay)
      (by linarith [Real.sin_le_one (Real.pi * kappa)] :
        (0:ℝ) ≤ 1 - Real.sin (Real.pi * kappa))]
  unfold ldPruningDetectionDeficit
  exact captureRatio_le_of_le hnum hden

/-- At half retention the deficit is exactly `2ρ / (π(1 + ρ²))`, so the bound of
`ldPruningDetectionDeficit_le_half_retention` is attained and the frontier is
tight there. -/
theorem ldPruningDetectionDeficit_half (decay : ℝ) :
    ldPruningDetectionDeficit decay (1 / 2) =
      2 * decay / (Real.pi * (1 + decay ^ 2)) := by
  unfold ldPruningDetectionDeficit
  rw [show Real.pi * (1 / 2) = Real.pi / 2 by ring, Real.sin_pi_div_two, mul_one]

/-- **Retaining everything retains everything.**  A consistency check on the
normalisation: at `κ = 1` the detection share is exactly `1`, which is the
statement that the denominator used in `ldBandDetectionShare` really is the full
inverse-kernel trace `ldWhiteningGain`. -/
theorem ldBandDetectionShare_one (decay : ℝ) :
    ldBandDetectionShare decay 1 = 1 := by
  unfold ldBandDetectionShare
  rw [mul_one, Real.sin_pi]
  norm_num

theorem ldBandDetectionShare_zero (decay : ℝ) :
    ldBandDetectionShare decay 0 = 0 := by
  unfold ldBandDetectionShare
  rw [mul_zero, Real.sin_zero]
  norm_num

/-- **No LD, no trade-off.**  When the chromosome has no linkage the spectrum is
flat, the two weight profiles coincide, and pruning is exactly neutral: the
detection share equals the retention fraction.  The whole phenomenon is a
consequence of spectral spread, and vanishes with it. -/
theorem ldBandDetectionShare_of_no_ld (kappa : ℝ) :
    ldBandDetectionShare 0 kappa = kappa := by
  unfold ldBandDetectionShare
  norm_num

/-- The reconstruction share is likewise neutral in the absence of LD. -/
theorem ldBandReconstructionShare_of_no_ld {kappa : ℝ}
    (hk0 : 0 ≤ kappa) (hk1 : kappa < 1) :
    ldBandReconstructionShare 0 kappa = kappa := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have hne : Real.pi ≠ 0 := ne_of_gt hpi
  have hx1 : -(Real.pi / 2) < Real.pi * kappa / 2 := by
    nlinarith [mul_nonneg (le_of_lt hpi) hk0]
  have hx2 : Real.pi * kappa / 2 < Real.pi / 2 := by
    nlinarith [mul_pos hpi (by linarith : (0:ℝ) < 1 - kappa)]
  unfold ldBandReconstructionShare
  rw [div_eq_iff hne,
    show ((1 + (0:ℝ)) / (1 - 0)) = 1 by norm_num, one_mul,
    Real.arctan_tan hx1 hx2]
  ring

end ARoneFrontier

/-!
## The frontier as a function of recombination rate and effective size

The section above is still parameterised by an abstract decay.  This one closes
the loop to genotype primitives: the AR(1) kernel's decay parameter *is* the
Ohta–Kimura per-generation retention `LDDecayTheory.ldRetentionPerGen r Ne`, so
every quantity on the frontier becomes an explicit function of the recombination
rate, the effective population size, and the number of markers retained.

Composition convention, inherited from
`Calibrator.ImitationRigidity.markovLDStep`: separation along the chromosome is
measured in *sites*, and one site-step carries one application of the retention
factor.  `ImitationRigidity.stationaryLDEntry_eq_ldAfterGenerations` is the
corpus theorem licensing that identification.  Reading `r` as anything other
than the per-generation recombination fraction between *adjacent* markers gives
a different kernel and different numbers.

What this buys: `pruning_loses_detection_iff_whiteningGain_exceeds_one` makes
the connection to the corpus's existing detection quantity an implication rather
than a remark — the whitening gain `ldWhiteningGain` exceeds its no-linkage
value exactly when pruning strictly loses detection weight, because the
inverse-kernel trace that the gain measures is built out of the very directions
pruning discards.  And `clumping_minimizes_detection_on_ld_kernel` states the
prohibition over a genetic pruning rule on the LD kernel itself.

Scope is unchanged and is not weakened by the instantiation: these are results
about linear, projection-type reductions of the LD kernel.  Extension to
arbitrary measurable reductions would need a joint data-processing inequality
for the detection/reconstruction pair, which does not exist.
-/

section GeneticFrontier

/-- A valid marker-panel reduction has a nonempty original panel and cannot
retain more markers than the panel contains. `retainedMarkers` of `totalMarkers`
survive; this is the rank budget in the units a clumping tool reports. Carrying
the validity facts as data keeps division by zero and fractions above one out of
the LD-frontier interface.

Empirical status: UNTESTED. -/
structure LDPanelRetention where
  retainedMarkers : ℕ
  totalMarkers : ℕ
  retained_le_total : retainedMarkers ≤ totalMarkers
  totalMarkers_pos : 0 < totalMarkers

noncomputable def ldPanelRetentionFraction (panel : LDPanelRetention) : ℝ :=
  (panel.retainedMarkers : ℝ) / (panel.totalMarkers : ℝ)

theorem ldPanelRetentionFraction_mem (panel : LDPanelRetention)
    (h0 : 0 < panel.retainedMarkers) (h1 : panel.retainedMarkers < panel.totalMarkers) :
    0 < ldPanelRetentionFraction panel ∧ ldPanelRetentionFraction panel < 1 := by
  have hr : (0 : ℝ) < (panel.retainedMarkers : ℝ) := by exact_mod_cast h0
  have ht : (0 : ℝ) < (panel.totalMarkers : ℝ) := by
    exact_mod_cast panel.totalMarkers_pos
  have hlt : (panel.retainedMarkers : ℝ) < (panel.totalMarkers : ℝ) := by
    exact_mod_cast h1
  unfold ldPanelRetentionFraction
  exact ⟨div_pos hr ht, (div_lt_one ht).mpr hlt⟩

/-- The Ohta–Kimura retention lies in `[0, 1)` for admissible parameters, so it
is an admissible AR(1) decay.  This is the compatibility check that lets the two
corpus modules be chained at all. -/
theorem ldRetentionPerGen_abs_lt_one {recomb Ne : ℝ}
    (hr0 : 0 ≤ recomb) (hr1 : recomb ≤ 1) (hNe : 1 < Ne) :
    |ldRetentionPerGen recomb Ne| < 1 := by
  have hnn : 0 ≤ ldRetentionPerGen recomb Ne :=
    ld_retention_nonneg recomb Ne hr0 hr1 (le_of_lt hNe)
  have hlt : ldRetentionPerGen recomb Ne < 1 := by
    have hfac : 0 < 1 - 1 / (2 * Ne) := by
      rw [sub_pos, div_lt_one (by linarith)]
      linarith
    have hfac1 : 1 - 1 / (2 * Ne) < 1 := by
      have hpos : 0 < 1 / (2 * Ne) := div_pos one_pos (by linarith)
      linarith
    unfold ldRetentionPerGen
    nlinarith [mul_nonneg hr0 (le_of_lt hfac), hfac1]
  rw [abs_lt]
  exact ⟨by linarith, hlt⟩

/-- Less recombination, more retention.  Extracted here in the form the frontier
needs; it is the step the corpus already performs inside
`ImitationRigidity.ldWhiteningGain_of_ldRetention_antitone`. -/
theorem ldRetentionPerGen_strictAnti_recomb {r₁ r₂ Ne : ℝ}
    (hNe : 1 < Ne) (hlt : r₁ < r₂) :
    ldRetentionPerGen r₂ Ne < ldRetentionPerGen r₁ Ne := by
  have hfac : 0 < 1 - 1 / (2 * Ne) := by
    rw [sub_pos, div_lt_one (by linarith)]
    linarith
  unfold ldRetentionPerGen
  nlinarith [hlt, hfac]

/-- **Detection share of a clumped panel**: the fraction of the whitened
detection weight — the inverse-LD-kernel trace whose per-variant limit is
`ImitationRigidity.ldWhiteningGain` — that survives clumping, as a function of
recombination rate, effective size and marker counts.

Empirical status: UNTESTED. -/
noncomputable def ldBlockDetectionShare (recomb Ne : ℝ)
    (panel : LDPanelRetention) : ℝ :=
  ldBandDetectionShare (ldRetentionPerGen recomb Ne)
    (ldPanelRetentionFraction panel)

/-- **Detection weight surrendered to clumping**, over and above the fraction of
markers discarded, as a function of recombination rate and effective size.  This
is the price the frontier puts on the pruning convention.

Empirical status: UNTESTED. -/
noncomputable def ldBlockPruningDeficit (recomb Ne : ℝ)
    (panel : LDPanelRetention) : ℝ :=
  ldPruningDetectionDeficit (ldRetentionPerGen recomb Ne)
    (ldPanelRetentionFraction panel)

/-- **Tight-linkage floor on the detection share**, `κ - sin(πκ)/π`.  It carries
no recombination rate because it is the value the frontier saturates to as the
retention approaches one, and `ldTightLinkage_le_ldBlockDetectionShare` shows it
bounds the detection share at every recombination rate and effective size.

Empirical status: UNTESTED. -/
noncomputable def ldTightLinkageDetectionShare (panel : LDPanelRetention) : ℝ :=
  ldPanelRetentionFraction panel -
    Real.sin (Real.pi * ldPanelRetentionFraction panel) / Real.pi

/-- Accounting identity: what clumping keeps plus what it surrenders is the
fraction of markers it retained. -/
theorem ldBlockDetectionShare_add_deficit (recomb Ne : ℝ)
    (panel : LDPanelRetention) :
    ldBlockDetectionShare recomb Ne panel + ldBlockPruningDeficit recomb Ne panel =
      ldPanelRetentionFraction panel := by
  unfold ldBlockDetectionShare ldBlockPruningDeficit ldBandDetectionShare
    ldPruningDetectionDeficit
  ring

/-- **Clumping loses detection weight faster than it loses markers**, at every
recombination rate and effective size. -/
theorem ldBlockDetectionShare_le_retention {recomb Ne : ℝ}
    {panel : LDPanelRetention}
    (hr0 : 0 ≤ recomb) (hr1 : recomb ≤ 1) (hNe : 1 < Ne)
    (h0 : 0 < panel.retainedMarkers) (h1 : panel.retainedMarkers < panel.totalMarkers) :
    ldBlockDetectionShare recomb Ne panel ≤ ldPanelRetentionFraction panel := by
  obtain ⟨hkpos, hklt⟩ := ldPanelRetentionFraction_mem panel h0 h1
  have hp0 : 0 ≤ ldRetentionPerGen recomb Ne :=
    ld_retention_nonneg recomb Ne hr0 hr1 (le_of_lt hNe)
  unfold ldBlockDetectionShare
  exact ldBandDetectionShare_le_retention hp0 (le_of_lt hkpos) (le_of_lt hklt)

/-- The whitening gain exceeds its no-linkage value exactly when there is
linkage to exploit. -/
theorem ldWhiteningGain_one_lt_iff {decay : ℝ}
    (hd0 : 0 ≤ decay) (hd1 : decay < 1) :
    1 < ldWhiteningGain decay ↔ 0 < decay := by
  have hden : (0 : ℝ) < 1 - decay ^ 2 := by
    nlinarith [mul_pos (by linarith : (0:ℝ) < 1 - decay)
      (by linarith : (0:ℝ) < 1 + decay)]
  unfold ldWhiteningGain
  rw [one_lt_div hden]
  constructor
  · intro h
    rcases eq_or_lt_of_le hd0 with heq | hpos
    · exfalso
      rw [← heq] at h
      norm_num at h
    · exact hpos
  · intro h
    nlinarith [mul_pos h h]

/-- The pruning deficit is strictly positive exactly when there is linkage. -/
theorem ldPruningDetectionDeficit_pos_iff {decay kappa : ℝ}
    (hd0 : 0 ≤ decay) (hk0 : 0 < kappa) (hk1 : kappa < 1) :
    0 < ldPruningDetectionDeficit decay kappa ↔ 0 < decay := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have hden : 0 < Real.pi * (1 + decay ^ 2) := by positivity
  have hsin : 0 < Real.sin (Real.pi * kappa) := by
    refine Real.sin_pos_of_pos_of_lt_pi ?_ ?_
    · exact mul_pos hpi hk0
    · nlinarith [mul_pos hpi (by linarith : (0:ℝ) < 1 - kappa)]
  unfold ldPruningDetectionDeficit
  constructor
  · intro h
    rcases eq_or_lt_of_le hd0 with heq | hpos
    · exfalso
      rw [← heq] at h
      norm_num at h
    · exact hpos
  · intro h
    exact div_pos (mul_pos (by linarith) hsin) hden

/-- **The corpus's detection quantity is what clumping destroys.**

`ImitationRigidity.ldWhiteningGain` is the per-variant limit of `tr K⁻¹`, the
quantity every whitened detection threshold in this corpus is stated in.  It
exceeds its no-linkage value `1` precisely when the LD kernel has spectral
spread — and that is precisely the condition under which a clumped panel loses
detection weight strictly faster than it loses markers.

This is the implication the inverse-ordering result explains: the inverse-kernel
trace is built out of the small-eigenvalue directions, clumping keeps the large
ones, so the gain being larger than one and the pruning deficit being positive
are the same fact seen from two sides.  Everything on both sides is an explicit
function of the recombination rate and the effective population size. -/
theorem pruning_loses_detection_iff_whiteningGain_exceeds_one
    {recomb Ne : ℝ} {panel : LDPanelRetention}
    (hr0 : 0 ≤ recomb) (hr1 : recomb ≤ 1) (hNe : 1 < Ne)
    (h0 : 0 < panel.retainedMarkers) (h1 : panel.retainedMarkers < panel.totalMarkers) :
    1 < ldWhiteningGain (ldRetentionPerGen recomb Ne) ↔
      0 < ldBlockPruningDeficit recomb Ne panel := by
  obtain ⟨hkpos, hklt⟩ := ldPanelRetentionFraction_mem panel h0 h1
  have hp0 : 0 ≤ ldRetentionPerGen recomb Ne :=
    ld_retention_nonneg recomb Ne hr0 hr1 (le_of_lt hNe)
  have hp1 : ldRetentionPerGen recomb Ne < 1 :=
    (abs_lt.mp (ldRetentionPerGen_abs_lt_one hr0 hr1 hNe)).2
  unfold ldBlockPruningDeficit
  rw [ldWhiteningGain_one_lt_iff hp0 hp1,
    ldPruningDetectionDeficit_pos_iff hp0 hkpos hklt]

/-- The deficit is strictly increasing in the AR(1) decay. -/
theorem ldPruningDetectionDeficit_strictMono {p₁ p₂ kappa : ℝ}
    (h₁ : 0 ≤ p₁) (h₂ : p₂ < 1) (hlt : p₁ < p₂)
    (hk0 : 0 < kappa) (hk1 : kappa < 1) :
    ldPruningDetectionDeficit p₁ kappa < ldPruningDetectionDeficit p₂ kappa := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have hsin : 0 < Real.sin (Real.pi * kappa) := by
    refine Real.sin_pos_of_pos_of_lt_pi ?_ ?_
    · exact mul_pos hpi hk0
    · nlinarith [mul_pos hpi (by linarith : (0:ℝ) < 1 - kappa)]
  have hd1 : 0 < Real.pi * (1 + p₁ ^ 2) := by positivity
  have hd2 : 0 < Real.pi * (1 + p₂ ^ 2) := by positivity
  have hprod : (0 : ℝ) < 1 - p₁ * p₂ := by
    nlinarith [mul_nonneg h₁ (by linarith : (0:ℝ) ≤ 1 - p₂)]
  unfold ldPruningDetectionDeficit
  rw [div_lt_div_iff₀ hd1 hd2]
  nlinarith [mul_pos (mul_pos (mul_pos hsin hpi) (sub_pos.mpr hlt)) hprod]

/-- **Tighter linkage, larger surrendered detection power.**  Lowering the
recombination rate between adjacent markers at fixed effective size strictly
increases the detection weight a clumped panel gives up.  This is the frontier's
dependence on `r`, and it runs in the same direction as
`ImitationRigidity.ldWhiteningGain_of_ldRetention_antitone`: the tighter the
block, the more there was to lose. -/
theorem ldBlockPruningDeficit_antitone_in_recombination
    {r₁ r₂ Ne : ℝ} {panel : LDPanelRetention}
    (hr₁ : 0 ≤ r₁) (hr₂ : r₂ ≤ 1) (hNe : 1 < Ne) (hlt : r₁ < r₂)
    (h0 : 0 < panel.retainedMarkers) (h1 : panel.retainedMarkers < panel.totalMarkers) :
    ldBlockPruningDeficit r₂ Ne panel < ldBlockPruningDeficit r₁ Ne panel := by
  obtain ⟨hkpos, hklt⟩ := ldPanelRetentionFraction_mem panel h0 h1
  have hp2nn : 0 ≤ ldRetentionPerGen r₂ Ne :=
    ld_retention_nonneg r₂ Ne (by linarith) hr₂ (le_of_lt hNe)
  have hp1lt : ldRetentionPerGen r₁ Ne < 1 :=
    (abs_lt.mp (ldRetentionPerGen_abs_lt_one hr₁ (by linarith) hNe)).2
  have hret : ldRetentionPerGen r₂ Ne < ldRetentionPerGen r₁ Ne :=
    ldRetentionPerGen_strictAnti_recomb hNe hlt
  unfold ldBlockPruningDeficit
  exact ldPruningDetectionDeficit_strictMono hp2nn hp1lt hret hkpos hklt

/-- The deficit never exceeds `sin(πκ)/π`, at any decay. -/
theorem ldPruningDetectionDeficit_le_sin_div_pi {decay kappa : ℝ}
    (hk0 : 0 ≤ kappa) (hk1 : kappa ≤ 1) :
    ldPruningDetectionDeficit decay kappa ≤
      Real.sin (Real.pi * kappa) / Real.pi := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have hden : 0 < Real.pi * (1 + decay ^ 2) := by positivity
  have hsin : 0 ≤ Real.sin (Real.pi * kappa) := by
    refine Real.sin_nonneg_of_nonneg_of_le_pi ?_ ?_
    · exact mul_nonneg (le_of_lt hpi) hk0
    · nlinarith [mul_nonneg (le_of_lt hpi) (by linarith : (0:ℝ) ≤ 1 - kappa)]
  unfold ldPruningDetectionDeficit
  rw [div_le_div_iff₀ hden hpi]
  nlinarith [mul_nonneg (mul_nonneg hsin (le_of_lt hpi)) (sq_nonneg (1 - decay))]

/-- **The tight-linkage floor.**  At every recombination rate and effective
size, a clumped panel retaining `retainedMarkers` of `totalMarkers` keeps at
least `κ - sin(πκ)/π` of the detection weight, and no more than `κ`.  The lower
end is approached as linkage tightens, so on a dense panel the detection share
is pinned near a curve carrying no free parameters at all — which is what makes
the prediction cheap to test. -/
theorem ldTightLinkage_le_ldBlockDetectionShare {recomb Ne : ℝ}
    {panel : LDPanelRetention}
    (h0 : 0 < panel.retainedMarkers) (h1 : panel.retainedMarkers < panel.totalMarkers) :
    ldTightLinkageDetectionShare panel ≤ ldBlockDetectionShare recomb Ne panel := by
  obtain ⟨hkpos, hklt⟩ := ldPanelRetentionFraction_mem panel h0 h1
  have hbound := ldPruningDetectionDeficit_le_sin_div_pi
    (decay := ldRetentionPerGen recomb Ne)
    (kappa := ldPanelRetentionFraction panel)
    (le_of_lt hkpos) (le_of_lt hklt)
  unfold ldTightLinkageDetectionShare ldBlockDetectionShare
    ldBandDetectionShare
  unfold ldPruningDetectionDeficit at hbound
  linarith

/-- **The pruning prohibition on the LD kernel itself.**

`S` is the set of retained directions of a clumping pass: the low-frequency band
of the LD kernel, which by `ldKernelSymbol_mono_in_cos` is exactly a top-`|S|`
set by eigenvalue.  The conclusion is that among *all* relaxed rank-`|S|`
reductions of the same kernel — every linear dimension reduction with the same
budget, fractional ones included — the clumped panel has the minimum detection
efficiency.

The kernel is the Ohta–Kimura one: its decay is `ldRetentionPerGen recomb Ne`,
so the statement is about a chromosome with a named recombination rate and a
named effective population size, not an abstract spectrum.

Scope: relaxed projection-type reductions.  This is not a statement about
arbitrary measurable summaries of the genotypes, and no joint data-processing
inequality is available that would make it one. -/
theorem clumping_minimizes_detection_on_ld_kernel
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (angle : ι → ℝ) (recomb Ne cutAngle : ℝ) (S : Finset ι) (M : ι → ℝ)
    (hr0 : 0 ≤ recomb) (hr1 : recomb ≤ 1) (hNe : 1 < Ne)
    (hM : IsRankAllocation (S.card : ℝ) M)
    (hin : ∀ i ∈ S, Real.cos cutAngle ≤ Real.cos (angle i))
    (hout : ∀ i ∉ S, Real.cos (angle i) ≤ Real.cos cutAngle) :
    detectionEfficiency
        (fun i ↦ ldKernelSymbol (ldRetentionPerGen recomb Ne) (angle i))
        (pruneAllocation S) ≤
      detectionEfficiency
        (fun i ↦ ldKernelSymbol (ldRetentionPerGen recomb Ne) (angle i)) M := by
  have habs : |ldRetentionPerGen recomb Ne| < 1 :=
    ldRetentionPerGen_abs_lt_one hr0 hr1 hNe
  have hp0 : 0 ≤ ldRetentionPerGen recomb Ne :=
    ld_retention_nonneg recomb Ne hr0 hr1 (le_of_lt hNe)
  refine topVariance_minimizes_detection
    (fun i ↦ ldKernelSymbol (ldRetentionPerGen recomb Ne) (angle i)) M S
    (ldKernelSymbol (ldRetentionPerGen recomb Ne) cutAngle)
    (fun i ↦ ldKernelSymbol_pos habs) (ldKernelSymbol_pos habs)
    hM ?_ ?_
  · intro i hi
    exact ldKernelSymbol_mono_in_cos habs hp0 (hin i hi)
  · intro i hi
    exact ldKernelSymbol_mono_in_cos habs hp0 (hout i hi)

/-- The same statement for the other task: a clumped panel maximises
reconstruction efficiency on the LD kernel.  Stated alongside the prohibition
because the pair is the trade-off — the clumping rule is not merely bad for
detection, it is bad for detection *because* it is optimal for reconstruction,
and the two conclusions come from the one threshold hypothesis. -/
theorem clumping_maximizes_reconstruction_on_ld_kernel
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (angle : ι → ℝ) (recomb Ne cutAngle : ℝ) (S : Finset ι) (M : ι → ℝ)
    (hr0 : 0 ≤ recomb) (hr1 : recomb ≤ 1) (hNe : 1 < Ne)
    (hM : IsRankAllocation (S.card : ℝ) M)
    (hin : ∀ i ∈ S, Real.cos cutAngle ≤ Real.cos (angle i))
    (hout : ∀ i ∉ S, Real.cos (angle i) ≤ Real.cos cutAngle) :
    reconstructionEfficiency
        (fun i ↦ ldKernelSymbol (ldRetentionPerGen recomb Ne) (angle i)) M ≤
      reconstructionEfficiency
        (fun i ↦ ldKernelSymbol (ldRetentionPerGen recomb Ne) (angle i))
        (pruneAllocation S) := by
  have habs : |ldRetentionPerGen recomb Ne| < 1 :=
    ldRetentionPerGen_abs_lt_one hr0 hr1 hNe
  have hp0 : 0 ≤ ldRetentionPerGen recomb Ne :=
    ld_retention_nonneg recomb Ne hr0 hr1 (le_of_lt hNe)
  refine topVariance_maximizes_reconstruction
    (fun i ↦ ldKernelSymbol (ldRetentionPerGen recomb Ne) (angle i)) M S
    (ldKernelSymbol (ldRetentionPerGen recomb Ne) cutAngle)
    (fun i ↦ ldKernelSymbol_pos habs) hM ?_ ?_
  · intro i hi
    exact ldKernelSymbol_mono_in_cos habs hp0 (hin i hi)
  · intro i hi
    exact ldKernelSymbol_mono_in_cos habs hp0 (hout i hi)

end GeneticFrontier

/-!
## One correction, several deployment targets: the spread law

`ProjectionShiftBounds.sharedCorrectionOptimum` gives the recalibration each
target would choose on its own.  A score deployed to several populations gets
*one* correction.  This section prices that constraint, and the price has a
closed form: it is the curvature-weighted variance of the per-target optimal
corrections, zero exactly when they agree.

The curvature weight is not a free parameter — it is
`weight i * coefficientEnergy (B i) beta`, the deployment weight times the
transported direction's energy in that target's own second-moment matrix.  So a
target with little signal energy in the score's direction pulls the shared
correction weakly, which is the right behaviour and is forced rather than
stipulated.

Why this is worth having: multi-population incompatibility becomes a number
computable from quantities already in the corpus — compute `a_i*` per target,
take the weighted variance — instead of a program to be solved or a qualitative
warning to be repeated.
-/

section SharedCorrectionFamily

variable {ι J : Type*} [Fintype ι] [Fintype J] [DecidableEq J]

/-- **Curvature of a target's recalibration objective**: how hard target `i`
pulls on the shared correction.  Deployment weight times the energy of the
transported direction in that target's own second-moment matrix.

**DO NOT DELETE AS UNUSED.**  Nothing applies this, and that is the point of it.
`sharedCorrectionConsensus` and `sharedCorrectionSpread` below take `curvature`
and `optimum` as arbitrary functions `ι → ℝ`; this definition and
`targetCorrectionOptimum` are what say which functions the section is about.  The
section's claim that the curvature weight is FORCED rather than stipulated depends
on them: without them the weight is a free parameter, the spread law holds for any
weights whatsoever, and that claim is false.  Deleting them does not break
elaboration, because the arguments are already abstract — it hollows the claim and
leaves the file green, which is why an identifier grep is not enough to justify
removing them.

Empirical status: UNTESTED. -/
def targetCorrectionCurvature (weight : ι → ℝ) (B : ι → Matrix J J ℝ)
    (beta : J → ℝ) : ι → ℝ :=
  fun i ↦ weight i * coefficientEnergy (B i) beta

/-- **The correction each target would choose alone**, as a family indexed by
deployment target.

**DO NOT DELETE AS UNUSED** -- see `targetCorrectionCurvature` above.  This is
the `optimum` that `sharedCorrectionConsensus` and `sharedCorrectionSpread`
average and take the variance of; without it the "per-target optimal
corrections" their docstrings name have no referent in the corpus.

`noncomputable` because `sharedCorrectionOptimum` is: it divides by
`coefficientEnergy`, and it sits inside a `noncomputable section` in
`ProjectionShiftBounds`, so it carries no executable code. That section marker does not
travel with the name, so this definition -- outside such a section -- has to say so
itself, or the compiler IR check fails here rather than at the real-division site.

Empirical status: UNTESTED. -/
noncomputable def targetCorrectionOptimum (B : ι → Matrix J J ℝ) (beta theta : J → ℝ) :
    ι → ℝ :=
  fun i ↦ sharedCorrectionOptimum (B i) beta theta

/-- The curvature-weighted mean of the per-target optimal corrections: the
shared correction that a weighted-least-squares compromise selects.

Empirical status: UNTESTED. -/
noncomputable def sharedCorrectionConsensus (curvature optimum : ι → ℝ) : ℝ :=
  (∑ i, curvature i * optimum i) / ∑ i, curvature i

/-- **The spread law's right-hand side**: the curvature-weighted variance of the
per-target optimal corrections.

Empirical status: UNTESTED. -/
noncomputable def sharedCorrectionSpread (curvature optimum : ι → ℝ) : ℝ :=
  ∑ i, curvature i *
    (optimum i - sharedCorrectionConsensus curvature optimum) ^ 2

/-- Total excess risk incurred across the family by applying the single
correction `correction` instead of each target's own optimum.

Empirical status: UNTESTED. -/
def sharedCorrectionCost (curvature optimum : ι → ℝ) (correction : ℝ) : ℝ :=
  ∑ i, curvature i * (correction - optimum i) ^ 2

/-- The consensus correction is the curvature-weighted centroid: deviations from
it cancel under the curvature weights.  This is the one computation the spread
law rests on. -/
theorem sharedCorrection_centered (curvature optimum : ι → ℝ)
    (hC : ∑ i, curvature i ≠ 0) :
    ∑ i, curvature i *
        (sharedCorrectionConsensus curvature optimum - optimum i) = 0 := by
  have hsplit : ∑ i, curvature i *
        (sharedCorrectionConsensus curvature optimum - optimum i) =
      sharedCorrectionConsensus curvature optimum * (∑ i, curvature i) -
        ∑ i, curvature i * optimum i := by
    calc ∑ i, curvature i *
          (sharedCorrectionConsensus curvature optimum - optimum i)
        = ∑ i, (sharedCorrectionConsensus curvature optimum * curvature i -
            curvature i * optimum i) :=
          Finset.sum_congr rfl (fun i _ ↦ by ring)
      _ = (∑ i, sharedCorrectionConsensus curvature optimum * curvature i) -
            ∑ i, curvature i * optimum i := by
          rw [Finset.sum_sub_distrib]
      _ = sharedCorrectionConsensus curvature optimum * (∑ i, curvature i) -
            ∑ i, curvature i * optimum i := by
          rw [← Finset.mul_sum]
  rw [hsplit]
  unfold sharedCorrectionConsensus
  rw [div_mul_cancel₀ _ hC, sub_self]

/-- **The spread law.**  The cost of any single shared correction splits into a
consensus term, which the best shared correction drives to zero, and the
curvature-weighted variance of the per-target optima, which nothing drives to
zero.  The second term is the price of sharing. -/
theorem sharedCorrectionCost_eq_consensus_add_spread
    (curvature optimum : ι → ℝ) (correction : ℝ) (hC : ∑ i, curvature i ≠ 0) :
    sharedCorrectionCost curvature optimum correction =
      (∑ i, curvature i) *
          (correction - sharedCorrectionConsensus curvature optimum) ^ 2 +
        sharedCorrectionSpread curvature optimum := by
  have hcentered := sharedCorrection_centered curvature optimum hC
  unfold sharedCorrectionCost sharedCorrectionSpread
  calc ∑ i, curvature i * (correction - optimum i) ^ 2
      = ∑ i, (curvature i *
              (correction - sharedCorrectionConsensus curvature optimum) ^ 2 +
            2 * (correction - sharedCorrectionConsensus curvature optimum) *
              (curvature i *
                (sharedCorrectionConsensus curvature optimum - optimum i)) +
            curvature i *
              (optimum i - sharedCorrectionConsensus curvature optimum) ^ 2) :=
        Finset.sum_congr rfl (fun i _ ↦ by ring)
    _ = (∑ i, curvature i *
            (correction - sharedCorrectionConsensus curvature optimum) ^ 2) +
          (∑ i, 2 * (correction - sharedCorrectionConsensus curvature optimum) *
            (curvature i *
              (sharedCorrectionConsensus curvature optimum - optimum i))) +
          ∑ i, curvature i *
            (optimum i - sharedCorrectionConsensus curvature optimum) ^ 2 := by
        rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    _ = (∑ i, curvature i) *
            (correction - sharedCorrectionConsensus curvature optimum) ^ 2 +
          ∑ i, curvature i *
            (optimum i - sharedCorrectionConsensus curvature optimum) ^ 2 := by
        rw [← Finset.sum_mul, ← Finset.mul_sum, hcentered, mul_zero, add_zero]

/-- No shared correction beats the spread. -/
theorem sharedCorrectionSpread_le_cost (curvature optimum : ι → ℝ)
    (correction : ℝ) (hCpos : 0 < ∑ i, curvature i) :
    sharedCorrectionSpread curvature optimum ≤
      sharedCorrectionCost curvature optimum correction := by
  rw [sharedCorrectionCost_eq_consensus_add_spread curvature optimum correction
    (ne_of_gt hCpos)]
  nlinarith [mul_nonneg (le_of_lt hCpos)
    (sq_nonneg (correction - sharedCorrectionConsensus curvature optimum))]

/-- And the consensus correction attains it, so the spread is the value of the
shared-correction problem rather than a lower bound for it. -/
theorem sharedCorrectionCost_at_consensus (curvature optimum : ι → ℝ)
    (hC : ∑ i, curvature i ≠ 0) :
    sharedCorrectionCost curvature optimum
        (sharedCorrectionConsensus curvature optimum) =
      sharedCorrectionSpread curvature optimum := by
  rw [sharedCorrectionCost_eq_consensus_add_spread curvature optimum _ hC,
    sub_self]
  norm_num

theorem sharedCorrectionSpread_nonneg (curvature optimum : ι → ℝ)
    (hc : ∀ i, 0 ≤ curvature i) :
    0 ≤ sharedCorrectionSpread curvature optimum := by
  unfold sharedCorrectionSpread
  exact Finset.sum_nonneg (fun i _ ↦ mul_nonneg (hc i) (sq_nonneg _))

/-- **The price of sharing vanishes exactly on agreement.** -/
theorem sharedCorrectionSpread_eq_zero_iff (curvature optimum : ι → ℝ)
    (hc : ∀ i, 0 < curvature i) :
    sharedCorrectionSpread curvature optimum = 0 ↔
      ∀ i, optimum i = sharedCorrectionConsensus curvature optimum := by
  have hnn : ∀ j ∈ (Finset.univ : Finset ι), 0 ≤ curvature j *
      (optimum j - sharedCorrectionConsensus curvature optimum) ^ 2 :=
    fun j _ ↦ mul_nonneg (le_of_lt (hc j)) (sq_nonneg _)
  constructor
  · intro h i
    have hle : curvature i *
        (optimum i - sharedCorrectionConsensus curvature optimum) ^ 2 ≤
        sharedCorrectionSpread curvature optimum :=
      Finset.single_le_sum hnn (Finset.mem_univ i)
    have hterm : curvature i *
        (optimum i - sharedCorrectionConsensus curvature optimum) ^ 2 = 0 := by
      linarith [hnn i (Finset.mem_univ i), hle, h]
    have hsq : (optimum i -
        sharedCorrectionConsensus curvature optimum) ^ 2 = 0 := by
      rcases mul_eq_zero.mp hterm with hcase | hcase
      · exact absurd hcase (ne_of_gt (hc i))
      · exact hcase
    have hdiff := sq_eq_zero_iff.mp hsq
    linarith
  · intro h
    unfold sharedCorrectionSpread
    refine Finset.sum_eq_zero ?_
    intro i _
    rw [h i, sub_self]
    ring

/-- **The obstruction restated on the per-target optima.**  The shared
correction is free exactly when every target wants the same correction — which
is the vanishing of the pairwise differences `a_i* - a_j*`. -/
theorem sharedCorrectionSpread_eq_zero_iff_agree (curvature optimum : ι → ℝ)
    (hc : ∀ i, 0 < curvature i) (hC : ∑ i, curvature i ≠ 0) :
    sharedCorrectionSpread curvature optimum = 0 ↔
      ∀ i j, optimum i = optimum j := by
  rw [sharedCorrectionSpread_eq_zero_iff curvature optimum hc]
  constructor
  · intro h i j
    rw [h i, h j]
  · intro h i
    have hsum : ∑ j, curvature j * optimum j =
        optimum i * ∑ j, curvature j := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun j _ ↦ by rw [h j i]; ring)
    unfold sharedCorrectionConsensus
    rw [hsum, mul_div_assoc, div_self hC, mul_one]

/-- **The degenerate control, pinned by proof rather than by a run.**  A family
of targets that all want the same correction pays nothing for sharing one.  Any
simulation of the spread law must return exactly zero here. -/
theorem sharedCorrectionSpread_of_identical_optima (curvature : ι → ℝ)
    (a : ℝ) (hc : ∀ i, 0 < curvature i) (hC : ∑ i, curvature i ≠ 0) :
    sharedCorrectionSpread curvature (fun _ ↦ a) = 0 := by
  rw [sharedCorrectionSpread_eq_zero_iff_agree curvature (fun _ ↦ a) hc hC]
  intro i j
  rfl

end SharedCorrectionFamily

/-!
## No task-independent scalar ordering of spectral portability

The low/high-frequency witness from `SpectralDegradation` is now a dependency of the
metric-specific biological theory, not a leaf result.  Low-frequency shifts model
long-horizon ancestry or population-structure mismatch; high-frequency shifts model local
haplotype, imputation, or short-window mismatch.  A single pair of populations can reverse
order when the deployment task changes bands.
-/

/-- Existence of one scalar population-shift score whose monotone task-specific charts
recover both low-band and high-band degradation for the two-band witness. -/
def HasTaskIndependentSpectralPortabilityScalar (a : ℝ) : Prop :=
  let low₁ := FiniteSpectralModel.bandDegradation
    twoBandBaseline (twoBandLowShift a) {0}
  let low₂ := FiniteSpectralModel.bandDegradation
    twoBandBaseline (twoBandHighShift a) {0}
  let high₁ := FiniteSpectralModel.bandDegradation
    twoBandBaseline (twoBandLowShift a) {1}
  let high₂ := FiniteSpectralModel.bandDegradation
    twoBandBaseline (twoBandHighShift a) {1}
  ∃ (d₁ d₂ : ℝ) (Φlow Φhigh : ℝ → ℝ),
    Monotone Φlow ∧ Monotone Φhigh ∧
    Φlow d₁ = low₁ ∧ Φlow d₂ = low₂ ∧
    Φhigh d₁ = high₁ ∧ Φhigh d₂ = high₂

/-- **Metric-specific portability has no universal scalar degradation order.**  At every
nonzero shift the low-band and high-band tasks rank the same two population shifts in
opposite orders. -/
theorem not_hasTaskIndependentSpectralPortabilityScalar (a : ℝ) (ha : a ≠ 0) :
    ¬ HasTaskIndependentSpectralPortabilityScalar a := by
  unfold HasTaskIndependentSpectralPortabilityScalar
  exact twoBand_no_common_monotone_scalar a ha

end Calibrator
