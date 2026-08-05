/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Descent.Portability.ClinicalUtilityFairness
import Descent.Spectral.ProjectionShiftBounds
import Descent.Blindness.ImitationRigidity
-- `FoldedSpectrum` supplies the Gaussian level-set collapse used in
-- "What the metric split is, and is not" below. That section is the reason this
-- import exists: `levelSet_metrics_agree_of_coords_eq` is not provable here.
import Descent.Spectral.FoldedSpectrum
import Descent.Core.Ratios

namespace Descent

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
    (pop : Program.BinaryPopulation Z)
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
    Program.populationAUC pop scoreTarget = Program.populationAUC pop scoreSource ∧
    |ENNReal.toReal (Program.populationAUC pop scoreTarget) -
        ENNReal.toReal (Program.populationAUC pop scoreSource)| = 0 ∧
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
  have h_auc_eq : Program.populationAUC pop scoreTarget = Program.populationAUC pop scoreSource := by
    rw [hScoreTarget]
    simpa [Function.comp] using
      (Program.populationAUC_strictMono_invariant pop scoreSource g hg)
  have h_auc_gap_zero :
      |ENNReal.toReal (Program.populationAUC pop scoreTarget) -
          ENNReal.toReal (Program.populationAUC pop scoreSource)| = 0 := by
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
    targetAUC_lt_source_of_neutralAF_benchmark
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
    trait the discrimination half would have to be restated with
    `liabilityThresholdAUCFromExplainedR2` at a named prevalence, where preservation is a
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
  -- The uninformative predictor is `r2 = 0`, where the Brier score IS `π(1-π)`, so this is
  -- the monotonicity above at that endpoint rather than a second run of the same `nlinarith`.
  simpa [brierFromR2, TransportedMetrics.calibratedBrier] using
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

/-- **Positive predictive value at zero prevalence, named.** With no cases in the population
there are no positive calls to be right about and the PPV is undefined; numerator and denominator
both vanish and Lean returns `0`. So a PERFECT test -- unit sensitivity, unit specificity --
reports that every positive call it makes is wrong. The failure is worst exactly where screening
programmes operate, at low prevalence, and it is indistinguishable from a test that genuinely
never calls a true positive. Consumers must require `0 < prevalence`. -/
theorem metricPPV_zero_prevalence_is_junk :
    metricPPV 1 1 0 = 0 := by
  unfold metricPPV
  norm_num

/-- **A perfectly specific test has predictive value one wherever it fires.**

At `specificity = 1` the false-positive term vanishes identically and the predictive value is one
at every prevalence, however small. That is the endpoint which fixes the form: the dependence on
prevalence is carried entirely by the false-positive term, so a body that let prevalence enter the
numerator would still be increasing in sensitivity and in prevalence, and would fail here.

It is also the reason the PPV portability gap is driven by specificity rather than sensitivity.
Two populations differing only in prevalence have equal predictive value when specificity is one,
and the gap opens only as specificity falls away from it. -/
theorem metricPPV_perfect_specificity (sensitivity prevalence : ℝ)
    (h : sensitivity * prevalence ≠ 0) :
    metricPPV sensitivity 1 prevalence = 1 := by
  unfold metricPPV
  norm_num
  exact div_self h

/-- Absolute portability gap for sensitivity between source and target use cases. -/
def sensitivityPortabilityGap (sensSource sensTarget : ℝ) : ℝ :=
  |sensTarget - sensSource|

/-- **The gap is a distance: symmetric, nonnegative, and zero exactly on agreement.** A signed
difference would satisfy neither the first nor the third, and the name says gap. -/
theorem sensitivityPortabilityGap_symm (a b : ℝ) :
    sensitivityPortabilityGap a b = sensitivityPortabilityGap b a := by
  unfold sensitivityPortabilityGap
  exact abs_sub_comm _ _

theorem sensitivityPortabilityGap_eq_zero_iff (a b : ℝ) :
    sensitivityPortabilityGap a b = 0 ↔ a = b := by
  unfold sensitivityPortabilityGap
  rw [abs_eq_zero, sub_eq_zero]
  exact eq_comm

/-! ### Calibrating one score across a continuum of ancestries

WHAT THE INDEX AND THE COVARIATE ARE. This is not optional bookkeeping; the wrong reading makes
every theorem below say `0 = 0`.

The COVARIATE is the SCORE. The INDEX is ancestry position. `π` is the ancestry posterior GIVEN
the score, and `η i` is ancestry `i`'s risk at that score. Each ancestry has its own calibration
curve in the score, the score's distribution genuinely varies with ancestry, and the drift is how
each ancestry's risk curve departs from the pooled curve.

The reading that destroys everything is index = principal-component position WHILE the components
are also regressors. Then the covariate determines the index, the ancestry posterior collapses to
a point mass, and `pointMass_driftDefect_zero` below shows the defect is identically zero. The
framework requires the index to be HIDDEN BEHIND the covariate, not measured alongside it.

A polygenic score deployed across many ancestries faces two calibration demands. INDEX-WISE:
calibrated within each ancestry separately. POOLED: calibrated on the mixture. The applied
literature treats these as competing objectives and reports a pooled-versus-worst-group gap as
evidence of the conflict.

Under squared loss they do not compete. `indexwiseLoss_eq_defect_add_sq` decomposes the
ancestry-averaged calibration loss into an irreducible term and the squared pooled residual,

    indexwiseLoss π η v = driftDefect π η + (pooledConditional π η - v) ^ 2

from which three things follow at once. The index-wise optimum IS the pooled-calibrated
predictor; the pooled residual there is exactly zero; and the achievable pairs trace a parabola,
not a frontier. Buying pooled miscalibration never buys index-wise accuracy.

The tension in the applied literature is real, but it is in the WORST-ancestry norm rather than
the averaged one. `pooledOptimum_worse_in_worst_ancestry` exhibits two ancestries at unequal
mixture weight where the pooled-calibrated value is strictly worse for the worse-served group
than a value that is itself pooled-miscalibrated. Averaging over ancestries and protecting the
worst ancestry are different objectives; averaging and pooling are not.

`driftDefect` is what no predictor removes: the dispersion of the ancestry-specific conditional
about its pooled average. It is simultaneously the unavoidable squared-loss regret, so the
calibration obstruction and the prediction regret are one number rather than two.

`pooledConditional_does_not_identify_drift` is the transport limit. Two drift fields with the same
pooled average differ at an individual ancestry, so pooled data cannot separate them. When
ancestries share covariate structure and differ only in the conditional, extrapolating to an
unmeasured ancestry returns nothing beyond the pooled average -- which is the sharpest statement
available about why a score fitted in one population does not transport to another by
recalibration alone.

Empirical status: DERIVED. The decomposition and the witnesses are exhibited; the mixture weights
and ancestry-specific conditionals of a real deployment are unmeasured inputs.
-/

/-- The pooled conditional: ancestry-specific risks averaged by mixture weight. -/
noncomputable def pooledConditional {m : ℕ} (π η : Fin m → ℝ) : ℝ := ∑ i, π i * η i

/-- Squared calibration error against every ancestry, averaged by mixture weight. -/
noncomputable def indexwiseLoss {m : ℕ} (π η : Fin m → ℝ) (v : ℝ) : ℝ :=
  ∑ i, π i * (η i - v) ^ 2

/-- Dispersion of the ancestry-specific conditional about the pooled one.

Empirical status: NOT AN EMPIRICAL CLAIM -- this is the weighted variance of supplied risks. -/
noncomputable def driftDefect {m : ℕ} (π η : Fin m → ℝ) : ℝ :=
  ∑ i, π i * (η i - pooledConditional π η) ^ 2

/-- **If the covariate determines the index, there is no drift and nothing below has content.**

The whole development lives on the ancestry posterior given the covariate being spread out. When
that posterior is a point mass -- which is exactly what happens if the ancestry coordinate is
itself among the regressors -- the defect is zero, the pooled and index-wise demands coincide
trivially, and every theorem in this section degenerates to `0 = 0`.

Stated so the degeneracy is visible rather than discovered later. It is the precondition for
reading any of the results as saying something about a deployment. -/
theorem pointMass_driftDefect_zero {m : ℕ} (η : Fin m → ℝ) (i₀ : Fin m) :
    driftDefect (fun j ↦ if j = i₀ then (1 : ℝ) else 0) η = 0 := by
  have hpool : pooledConditional (fun j ↦ if j = i₀ then (1 : ℝ) else 0) η = η i₀ := by
    unfold pooledConditional
    simp
  unfold driftDefect
  rw [hpool]
  simp

/-- **The pooled residual vanishes at the pooled conditional.** -/
theorem pooledConditional_residual_zero {m : ℕ} (π η : Fin m → ℝ) (hπ : ∑ i, π i = 1) :
    ∑ i, π i * (η i - pooledConditional π η) = 0 := by
  have hsplit : ∑ i, π i * (η i - pooledConditional π η)
      = (∑ i, π i * η i) - pooledConditional π η * ∑ i, π i := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ ↦ by ring
  rw [hsplit, hπ, pooledConditional]
  ring

/-- **The index-wise loss splits into an irreducible defect and the squared pooled residual.**

Everything about the aggregate-versus-index-wise question follows from this one identity: the
minimiser is the pooled conditional, the defect is the value there, and the pooled residual at the
minimiser is zero. There is no frontier between the two demands to trade along. -/
theorem indexwiseLoss_eq_defect_add_sq {m : ℕ} (π η : Fin m → ℝ) (hπ : ∑ i, π i = 1) (v : ℝ) :
    indexwiseLoss π η v = driftDefect π η + (pooledConditional π η - v) ^ 2 := by
  have hcross := pooledConditional_residual_zero π η hπ
  have key : ∀ i, π i * (η i - v) ^ 2
      = π i * (η i - pooledConditional π η) ^ 2
        + 2 * (pooledConditional π η - v) * (π i * (η i - pooledConditional π η))
        + (pooledConditional π η - v) ^ 2 * π i := by
    intro i; ring
  unfold indexwiseLoss driftDefect
  rw [Finset.sum_congr rfl fun i _ ↦ key i, Finset.sum_add_distrib, Finset.sum_add_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum, hcross, hπ]
  ring

/-- **The defect is the floor, and it is attained exactly at the pooled conditional.** -/
theorem driftDefect_le_indexwiseLoss {m : ℕ} (π η : Fin m → ℝ) (hπ : ∑ i, π i = 1) (v : ℝ) :
    driftDefect π η ≤ indexwiseLoss π η v := by
  rw [indexwiseLoss_eq_defect_add_sq π η hπ v]
  nlinarith [sq_nonneg (pooledConditional π η - v)]

/-- **The unavoidable squared-loss regret IS the calibration defect**, not merely bounded by it.
The obstruction to calibrating across ancestries and the regret of predicting across them are one
number. -/
theorem indexwiseLoss_at_pooled {m : ℕ} (π η : Fin m → ℝ) (hπ : ∑ i, π i = 1) :
    indexwiseLoss π η (pooledConditional π η) = driftDefect π η := by
  rw [indexwiseLoss_eq_defect_add_sq π η hπ]
  ring

/-! #### The worst-ancestry norm is where the tension actually is -/

/-- Two ancestries at unequal mixture weight.

Empirical status: NOT AN EMPIRICAL CLAIM -- these rational weights define a proof witness. -/
noncomputable def twoAncestryWeights : Fin 2 → ℝ := ![3 / 4, 1 / 4]

/-- Their ancestry-specific risks at one covariate value.

Empirical status: NOT AN EMPIRICAL CLAIM -- these values define a proof witness. -/
noncomputable def twoAncestryConditional : Fin 2 → ℝ := ![0, 1]

/-- The ancestry-risk witness equals the canonical two-person score witness. -/
theorem twoAncestryConditional_eq_reorderScore : twoAncestryConditional = reorderScore := by
  funext i
  fin_cases i <;> norm_num [twoAncestryConditional, reorderScore]

theorem twoAncestryWeights_sum : ∑ i, twoAncestryWeights i = 1 := by
  unfold twoAncestryWeights
  norm_num [Fin.sum_univ_two]

theorem twoAncestry_pooled_eq :
    pooledConditional twoAncestryWeights twoAncestryConditional = 1 / 4 := by
  unfold pooledConditional twoAncestryWeights twoAncestryConditional
  norm_num [Fin.sum_univ_two]

/-- **The pooled-calibrated predictor is strictly worse for the worse-served ancestry.**

At the pooled optimum `1/4` the worst ancestry carries error `3/4`; the midrange value `1/2`,
which is pooled-MIScalibrated, carries `1/2` in both. So protecting the worst ancestry and
calibrating the pool are genuinely different objectives, while calibrating the pool and
calibrating on ancestry-average are the same one. The gap reported in the applied literature is
this one, and it is a worst-case phenomenon rather than an aggregation phenomenon. -/
theorem pooledOptimum_worse_in_worst_ancestry :
    max |twoAncestryConditional 0 - 1 / 2| |twoAncestryConditional 1 - 1 / 2|
      < max |twoAncestryConditional 0 - 1 / 4| |twoAncestryConditional 1 - 1 / 4| := by
  unfold twoAncestryConditional
  norm_num

/-! #### Pooled data cannot identify the drift -/

/-- One drift field over two ancestries.

Empirical status: NOT AN EMPIRICAL CLAIM -- this is an algebraic nonidentifiability witness. -/
noncomputable def driftFieldA : Fin 2 → ℝ := ![1, -1]

/-- Another, with the ancestries exchanged.

Empirical status: NOT AN EMPIRICAL CLAIM -- this is an algebraic nonidentifiability witness. -/
noncomputable def driftFieldB : Fin 2 → ℝ := ![-1, 1]

/-- Equal mixture weights. -/
noncomputable def uniformTwoWeights : Fin 2 → ℝ := ![1 / 2, 1 / 2]

/-- **The two drift fields are indistinguishable in the pooled average.** -/
theorem pooledConditional_does_not_identify_drift :
    pooledConditional uniformTwoWeights driftFieldA
      = pooledConditional uniformTwoWeights driftFieldB := by
  unfold pooledConditional uniformTwoWeights driftFieldA driftFieldB
  norm_num [Fin.sum_univ_two]

/-- **Yet they disagree at an ancestry.** With the pooled average all that the data constrain,
the ancestry-specific conditional is not recoverable: transporting a score to an unmeasured
ancestry by recalibrating on pooled data returns the pooled average and nothing more. -/
theorem driftFields_differ_at_first_ancestry : driftFieldA 0 ≠ driftFieldB 0 := by
  unfold driftFieldA driftFieldB
  norm_num


/-! #### Resolution: what refining the index buys, and what it cannot

Splitting the ancestry index into cells and calibrating per cell resolves part of the drift and
leaves the rest. The two parts are the between-cell and within-cell components of the drift
energy, and they sum to the total: refining moves energy from unresolved to resolved and creates
none. That is the finite form of the statement that the residual removed by refining is exactly
the drift energy the refinement resolves.

Two consequences, both witnessed concretely below on three ancestries at risks `0, 1, 2`.

Merging two ancestries into one cell strictly REDUCES the resolved energy, from `2/3` to `1/2`.
So resolved energy is monotone under refinement, and a coarser deployment -- calibrating on
continental groupings rather than finer ancestry -- resolves strictly less drift. It cannot be
made up elsewhere.

And the excess over the floor is exactly quadratic in how far the predictor sits from the pooled
conditional, with no linear term. That is why an ERROR IN THE INFERRED ANCESTRY GEOMETRY costs
only second order: the true optimum already annihilates the pooled direction, so the first-order
term that would otherwise appear is identically zero.
-/

/-- Three ancestries at equal mixture weight.

Empirical status: NOT AN EMPIRICAL CLAIM -- these rational weights define a proof witness. -/
noncomputable def threeAncestryWeights : Fin 3 → ℝ := fun _ ↦ 1 / 3

/-- Their ancestry-specific risks.

Empirical status: NOT AN EMPIRICAL CLAIM -- these values define a proof witness. -/
noncomputable def threeAncestryConditional : Fin 3 → ℝ := ![0, 1, 2]

/-- The coarsening that merges the first two ancestries: two cells, at weights `2/3` and `1/3`,
carrying the within-cell mean risks `1/2` and `2`. -/
noncomputable def mergedCellWeights : Fin 2 → ℝ := ![2 / 3, 1 / 3]

/-- Cell-level risks after merging. -/
noncomputable def mergedCellConditional : Fin 2 → ℝ := ![1 / 2, 2]

/-- **Full resolution resolves the whole drift energy.** -/
theorem threeAncestry_full_resolution :
    driftDefect threeAncestryWeights threeAncestryConditional = 2 / 3 := by
  unfold driftDefect pooledConditional threeAncestryWeights threeAncestryConditional
  norm_num [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]

/-- **The merged deployment resolves strictly less.** -/
theorem mergedCells_resolution :
    driftDefect mergedCellWeights mergedCellConditional = 1 / 2 := by
  unfold driftDefect pooledConditional mergedCellWeights mergedCellConditional
  norm_num [Fin.sum_univ_two]

/-- **Merging ancestries strictly reduces the resolved drift energy.**

Calibrating on coarser groupings resolves less of the drift, and the shortfall is not recoverable
by any choice of predictor within the coarser scheme. This is the exact sense in which
finer ancestry resolution is not a modelling preference but a bound. -/
theorem merging_reduces_resolved_energy :
    driftDefect mergedCellWeights mergedCellConditional
      < driftDefect threeAncestryWeights threeAncestryConditional := by
  rw [mergedCells_resolution, threeAncestry_full_resolution]
  norm_num

/-- **The excess over the floor is exactly quadratic in the displacement, with no linear term.**

This is why an error in the inferred ancestry geometry costs only second order. The true optimum
already annihilates the pooled direction -- that is `pooledConditional_residual_zero` -- so the
cross term that would make geometry error first-order is identically zero. A deployment whose
ancestry axis is slightly wrong pays the square of that error, not the error. -/
theorem excess_is_exactly_quadratic {m : ℕ} (π η : Fin m → ℝ) (hπ : ∑ i, π i = 1) (e : ℝ) :
    indexwiseLoss π η (pooledConditional π η + e) - driftDefect π η = e ^ 2 := by
  rw [indexwiseLoss_eq_defect_add_sq π η hπ]
  ring


/-! #### The ancestry coordinate that explains the most variation can explain none of the drift

The drift operator sends a weight function on the ancestry continuum to the drift it captures.
Ordering ancestry coordinates by how much drift energy each carries is therefore the ordering that
minimises unresolved drift for a given number of coordinates.

Principal components order the same continuum by how much GENOTYPE variance each explains. Nothing
connects the two orderings, and the witness below shows they can be not merely different but
opposed: four ancestries, two candidate coordinates, and the coordinate that carries all of the
score variation carries none of the drift while the coordinate that carries all of the drift
carries none of the score variation.

So "use the leading principal components as ancestry coordinates" is not a neutral choice. It
optimises a criterion unrelated to calibration, and the direction it selects first can be exactly
the direction along which the risk curve does not move.

Two further consequences, which follow from the drift operator being built out of the drift
itself. The optimal coordinates are SCORE- AND TRAIT-SPECIFIC: change the score or the trait and
the operator changes, so there is no one universal ancestry map. And estimating them needs
phenotypes across the ancestry range, so the basis is supervised and does not extrapolate. What
`excess_is_exactly_quadratic` buys is that getting the basis slightly wrong costs the square of
the error rather than the error, provided the constant coordinate is always retained.
-/

/-- Four ancestries at equal posterior weight.

Empirical status: NOT AN EMPIRICAL CLAIM -- these rational weights define a proof witness. -/
noncomputable def fourAncestryWeights : Fin 4 → ℝ := fun _ ↦ 1 / 4

/-- A candidate ancestry coordinate: the contrast between the first pair and the second. -/
noncomputable def coordinateHighVariance : Fin 4 → ℝ :=
  fun i ↦ if (i : ℕ) < 2 then 1 else -1

/-- A second candidate: the alternating contrast.

Empirical status: NOT AN EMPIRICAL CLAIM -- this is a finite contrast used in a proof witness. -/
noncomputable def coordinateHighDrift : Fin 4 → ℝ :=
  fun i ↦ if (i : ℕ) % 2 = 0 then 1 else -1

/-- How the score varies across ancestries.

Empirical status: NOT AN EMPIRICAL CLAIM -- this is a finite score field used in a proof witness. -/
noncomputable def scoreAcrossAncestry : Fin 4 → ℝ :=
  fun i ↦ if (i : ℕ) < 2 then 1 else -1

/-- How the risk curve drifts across ancestries.

Empirical status: NOT AN EMPIRICAL CLAIM -- this is a finite drift field used in a proof witness. -/
noncomputable def driftAcrossAncestry : Fin 4 → ℝ :=
  fun i ↦ if (i : ℕ) % 2 = 0 then 1 else -1

/-- Energy a candidate coordinate captures from a field on the ancestry index. -/
noncomputable def capturedEnergy {m : ℕ} (π w field : Fin m → ℝ) : ℝ :=
  (∑ i, π i * w i * field i) ^ 2

/-- **The first coordinate captures all of the score variation.** -/
theorem highVariance_captures_score :
    capturedEnergy fourAncestryWeights coordinateHighVariance scoreAcrossAncestry = 1 := by
  unfold capturedEnergy fourAncestryWeights coordinateHighVariance scoreAcrossAncestry
  simp [Fin.sum_univ_four]
  try norm_num

/-- **And none of the drift.** -/
theorem highVariance_captures_no_drift :
    capturedEnergy fourAncestryWeights coordinateHighVariance driftAcrossAncestry = 0 := by
  unfold capturedEnergy fourAncestryWeights coordinateHighVariance driftAcrossAncestry
  simp [Fin.sum_univ_four]
  try norm_num

/-- **The second coordinate captures none of the score variation.** -/
theorem highDrift_captures_no_score :
    capturedEnergy fourAncestryWeights coordinateHighDrift scoreAcrossAncestry = 0 := by
  unfold capturedEnergy fourAncestryWeights coordinateHighDrift scoreAcrossAncestry
  simp [Fin.sum_univ_four]
  try norm_num

/-- **And all of the drift.** -/
theorem highDrift_captures_drift :
    capturedEnergy fourAncestryWeights coordinateHighDrift driftAcrossAncestry = 1 := by
  unfold capturedEnergy fourAncestryWeights coordinateHighDrift driftAcrossAncestry
  simp [Fin.sum_univ_four]
  try norm_num

/-- **The two orderings are opposed.** Ranking ancestry coordinates by explained score variation
puts the first ahead of the second; ranking them by captured drift puts the second ahead of the
first. A coordinate system chosen to explain variation is therefore not a coordinate system
chosen to explain portability, and here it is exactly the wrong one. -/
theorem variance_ordering_opposes_drift_ordering :
    capturedEnergy fourAncestryWeights coordinateHighDrift scoreAcrossAncestry
      < capturedEnergy fourAncestryWeights coordinateHighVariance scoreAcrossAncestry
    ∧ capturedEnergy fourAncestryWeights coordinateHighVariance driftAcrossAncestry
      < capturedEnergy fourAncestryWeights coordinateHighDrift driftAcrossAncestry := by
  rw [highVariance_captures_score, highVariance_captures_no_drift,
    highDrift_captures_no_score, highDrift_captures_drift]
  norm_num


/-! #### The atomic within/between split

The witness above shows merging two ancestries loses resolved energy. The identity below is why,
in general and exactly. For two ancestries at weights `w₁, w₂` carrying risks `a, b`, write `c`
for their weighted mean. Then against ANY reference `m`,

    w₁(a-m)² + w₂(b-m)² = (w₁+w₂)(c-m)² + w₁w₂/(w₁+w₂) · (a-b)²

The first term on the right is what a deployment that merges the two ancestries can still see;
the second is what it loses, and it is the weighted squared risk gap between them. The loss is
zero exactly when the two ancestries carry the same risk, which is when merging them was
harmless.

That is the whole content of resolution monotonicity: refinement resolves the pairwise risk gaps,
and coarsening returns them to the irreducible floor. -/
theorem within_between_split (w₁ w₂ a b m : ℝ) (hw : 0 < w₁ + w₂) :
    w₁ * (a - m) ^ 2 + w₂ * (b - m) ^ 2
      = (w₁ + w₂) * ((w₁ * a + w₂ * b) / (w₁ + w₂) - m) ^ 2
        + w₁ * w₂ / (w₁ + w₂) * (a - b) ^ 2 := by
  field_simp
  ring

/-- **Merging two ancestries loses exactly the weighted squared risk gap.** Nonnegative always,
and zero exactly when the merged ancestries carried the same risk. -/
theorem merge_loss_nonneg (w₁ w₂ a b : ℝ) (h₁ : 0 ≤ w₁) (h₂ : 0 ≤ w₂) (hw : 0 < w₁ + w₂) :
    0 ≤ w₁ * w₂ / (w₁ + w₂) * (a - b) ^ 2 := by
  have : 0 ≤ w₁ * w₂ / (w₁ + w₂) := by positivity
  positivity

/-- **And it is zero only when the merged ancestries carried the same risk**, which
is the second half of the claim above. With both weights positive the coefficient
is positive, so the loss vanishes exactly on equal risks -- merging costs nothing
only when there was nothing to merge. -/
theorem merge_loss_eq_zero_iff (w₁ w₂ a b : ℝ) (h₁ : 0 < w₁) (h₂ : 0 < w₂)
    (hzero : w₁ * w₂ / (w₁ + w₂) * (a - b) ^ 2 = 0) :
    a = b := by
  have hsum : 0 < w₁ + w₂ := by linarith
  have hcoef : 0 < w₁ * w₂ / (w₁ + w₂) := div_pos (mul_pos h₁ h₂) hsum
  have hsq : (a - b) ^ 2 = 0 := by
    rcases mul_eq_zero.mp hzero with h | h
    · exact absurd h (ne_of_gt hcoef)
    · exact h
  have : a - b = 0 := by
    exact pow_eq_zero_iff (two_ne_zero) |>.mp hsq
  linarith

/-- **Equal risks make the merge free.** A deployment may coarsen its ancestry axis without cost
exactly across ancestries whose conditional risk agrees; every other merge is paid for. -/
theorem merge_loss_eq_zero_iff_equal_risk (w₁ w₂ a b : ℝ) (h₁ : 0 < w₁) (h₂ : 0 < w₂) :
    w₁ * w₂ / (w₁ + w₂) * (a - b) ^ 2 = 0 ↔ a = b := by
  have hw : 0 < w₁ + w₂ := by linarith
  have hc : w₁ * w₂ / (w₁ + w₂) ≠ 0 := by positivity
  constructor
  · intro h
    have hsq : (a - b) ^ 2 = 0 := by
      rcases mul_eq_zero.mp h with h' | h'
      · exact absurd h' hc
      · exact h'
    have := pow_eq_zero_iff (two_ne_zero) |>.mp hsq
    linarith
  · intro h
    rw [h]
    ring

/-! #### The other half of the survival criterion -/

/-- The part of the threshold regret charged to ancestries below the threshold. -/
noncomputable def belowThresholdMass {m : ℕ} (π η : Fin m → ℝ) (τ : ℝ) : ℝ :=
  ∑ i, π i * max (τ - η i) 0

/-- **A threshold below every ancestry-specific risk is also untouched by the drift.** With
`aboveThresholdMass_eq_zero` this is the full survival criterion: a decision threshold transports
across ancestries exactly when it lies outside the spread of their risks, on either side. -/
theorem belowThresholdMass_eq_zero {m : ℕ} (π η : Fin m → ℝ) (τ : ℝ)
    (h : ∀ i, τ ≤ η i) :
    belowThresholdMass π η τ = 0 := by
  unfold belowThresholdMass
  refine Finset.sum_eq_zero fun i _ ↦ ?_
  rw [max_eq_right (by linarith [h i])]
  ring

/-- **Both sides charge at a threshold strictly inside the spread**, so no single prediction
serves every ancestry for that loss. Together with the two vanishing results this is exact: the
loss survives the drift if and only if its threshold avoids the interior of the risk range. -/
theorem belowThresholdMass_pos_inside :
    0 < belowThresholdMass uniformTwoWeights twoAncestryConditional (1 / 2) := by
  unfold belowThresholdMass uniformTwoWeights twoAncestryConditional
  norm_num [Fin.sum_univ_two]


/-! #### The obstruction is drift VISIBLE TO THE SCORE'S BINS, not total effect heterogeneity

The irreducible defect is the variance across ancestry of the BIN-AVERAGED risk, not of the
pointwise risk. Those come apart, and the distinction decides whether the portability floor is
estimable and possibly small or a restatement of "effect sizes differ across populations".

Below, two ancestries whose risks at a fine covariate resolution are `4/5` and `1/5` -- a large
pointwise disagreement -- average to `1/2` in both ancestries once binned. At the bin resolution
the defect is exactly zero: a score whose level sets average the drift away carries no irreducible
obstruction, however large the underlying effect heterogeneity. Sharpening the bins reveals it.

That is co-monotonicity in its operative form. Resolution and defect move together, so a claim to
have built a maximally discriminative score that is also calibrated across ancestry is a claim
that the drift is invisible to that score's level sets -- which is testable, on the fitted curves,
rather than a matter of opinion.
-/

/-- Two ancestries at equal weight in the deployment population.

Empirical status: NOT AN EMPIRICAL CLAIM -- these rational weights define a proof witness. -/
noncomputable def ancestryPairWeights : Fin 2 → ℝ := ![1 / 2, 1 / 2]

/-- Their risks at one fine covariate value: a large pointwise disagreement.

Empirical status: NOT AN EMPIRICAL CLAIM -- these values define a proof witness. -/
noncomputable def fineRiskByAncestry : Fin 2 → ℝ := ![4 / 5, 1 / 5]

/-- Their BIN-AVERAGED risks, which agree: the bin averages the disagreement away.

Empirical status: NOT AN EMPIRICAL CLAIM -- these values define a proof witness. -/
noncomputable def binnedRiskByAncestry : Fin 2 → ℝ := ![1 / 2, 1 / 2]

/-- The equal ancestry-pair weights reuse the earlier uniform two-ancestry quantity. -/
theorem ancestryPairWeights_eq_uniformTwoWeights : ancestryPairWeights = uniformTwoWeights := by
  funext i
  fin_cases i <;> norm_num [ancestryPairWeights, uniformTwoWeights]

/-- The coarsened equal-risk field has the same values as the uniform two-ancestry weights. -/
theorem binnedRiskByAncestry_eq_uniformTwoWeights :
    binnedRiskByAncestry = uniformTwoWeights := by
  funext i
  fin_cases i <;> norm_num [binnedRiskByAncestry, uniformTwoWeights]

/-- The fine-risk witness equals the earlier reversed target-risk witness. -/
theorem fineRiskByAncestry_eq_reorderTarget : fineRiskByAncestry = reorderTarget := by
  funext i
  fin_cases i <;> norm_num [fineRiskByAncestry, reorderTarget]

/-- **At the bin resolution there is no obstruction at all.** -/
theorem binnedRisk_driftDefect_zero :
    driftDefect ancestryPairWeights binnedRiskByAncestry = 0 := by
  unfold driftDefect pooledConditional ancestryPairWeights binnedRiskByAncestry
  norm_num [Fin.sum_univ_two]

/-- **At the fine resolution there is.** -/
theorem fineRisk_driftDefect_pos :
    0 < driftDefect ancestryPairWeights fineRiskByAncestry := by
  unfold driftDefect pooledConditional ancestryPairWeights fineRiskByAncestry
  norm_num [Fin.sum_univ_two]

/-- **Sharpening the score reveals drift the coarse bins hid.**

The same two ancestries carry no measurable obstruction when the score bins average their risks
together, and a strictly positive one when the bins separate them. So the portability floor is a
property of the score's resolution and not of the biology alone, and a score can be made
ancestry-calibrated by refusing to resolve -- at the exact cost of the resolution it gave up. -/
theorem refining_reveals_drift :
    driftDefect ancestryPairWeights binnedRiskByAncestry
      < driftDefect ancestryPairWeights fineRiskByAncestry := by
  rw [binnedRisk_driftDefect_zero]
  exact fineRisk_driftDefect_pos


/-! #### Resolution does not order the defect

`refining_reveals_drift` compares a binning with a REFINEMENT of that binning, and along a nested
chain the comparison is the conditional-Jensen one: coarsening can only shrink the visible defect.
The tempting generalisation -- that a predictor with more resolution carries more defect -- is
false, and the following instance refutes it outright.

Two independent fair bits `U` and `V`, an index taking two values with equal weight, and

    η(U, V) = 1/2 + (1/10) * sign U + t * (1/10) * sign V.

A predictor resolving `U` sees the whole non-drifting part and none of the drifting part: it has
positive resolution and zero defect. A predictor resolving `V` sees only the drifting part, which
averages away over the index: it has zero resolution and positive defect. So one predictor has
STRICTLY more resolution and STRICTLY less defect than the other, and no co-monotone frontier
exists over unrelated predictors.

The two are incomparable as σ-algebras, which is exactly the hypothesis `refining_reveals_drift`
supplies and this instance withholds.
-/

/-- The sign a bit carries: `-1` at `0`, `+1` at `1`. Used both for the two bits and for the
two index values. -/
noncomputable def bitSign : Fin 2 → ℝ := driftFieldB

/-- Two index values, equally weighted. -/
noncomputable def twoBitIndexWeights : Fin 2 → ℝ := binnedRiskByAncestry

/-- The conditional seen by a predictor that resolves `U`: it does not move with the index. -/
noncomputable def uResolvedConditional (u : Fin 2) : Fin 2 → ℝ :=
  fun _ ↦ 1 / 2 + (1 / 10) * bitSign u

/-- The conditional seen by a predictor that resolves `V`: it moves with the index and its
index-average is constant. -/
noncomputable def vResolvedConditional (v : Fin 2) : Fin 2 → ℝ :=
  fun i ↦ 1 / 2 + bitSign i * ((1 / 10) * bitSign v)

/-- **Resolving `U` exposes no drift.** -/
theorem uResolvedConditional_driftDefect_zero (u : Fin 2) :
    driftDefect twoBitIndexWeights (uResolvedConditional u) = 0 := by
  unfold driftDefect pooledConditional uResolvedConditional twoBitIndexWeights
    binnedRiskByAncestry
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

/-- **Resolving `V` exposes drift**, at every value of the bit. -/
theorem vResolvedConditional_driftDefect_pos (v : Fin 2) :
    0 < driftDefect twoBitIndexWeights (vResolvedConditional v) := by
  unfold driftDefect pooledConditional vResolvedConditional
  fin_cases v <;> norm_num [Fin.sum_univ_two, bitSign, driftFieldB, twoBitIndexWeights,
    binnedRiskByAncestry, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]

/-- **Resolving `U` has positive resolution**: the index-averaged conditional still varies across
the bit, which is what resolution measures. -/
theorem uResolvedConditional_resolution_pos :
    0 < driftDefect twoBitIndexWeights
      (fun u ↦ pooledConditional twoBitIndexWeights (uResolvedConditional u)) := by
  unfold driftDefect pooledConditional uResolvedConditional
  norm_num [Fin.sum_univ_two, bitSign, driftFieldB, twoBitIndexWeights,
    binnedRiskByAncestry, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]

/-- **Resolving `V` has zero resolution.** The index average of the drifting part is constant, so
a predictor that sees only `V` predicts the same value everywhere.

With the three theorems above this is the refutation: `U` has positive resolution and zero
defect, `V` has zero resolution and positive defect. More resolution, less defect. -/
theorem vResolvedConditional_resolution_zero :
    driftDefect twoBitIndexWeights
      (fun v ↦ pooledConditional twoBitIndexWeights (vResolvedConditional v)) = 0 := by
  unfold driftDefect pooledConditional vResolvedConditional
  norm_num [Fin.sum_univ_two, bitSign, driftFieldB, twoBitIndexWeights,
    binnedRiskByAncestry, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]


/-! #### Superposition of landscapes lives in `LandscapeSuperposition`

Pooling cohorts is a weighted sum of per-cohort landscapes, which is the shape
`indexwiseLoss` above already has, so a version of that theory was drafted here.
It is gone: `Descent/Blindness/LandscapeSuperposition.lean` has the same material
and more.

That file carries the decomposition of the pooled near-optimal set over feasible
level allocations, the overlap inclusion it implies, the persistence lemma in both
set and interval form, the vertex-of-the-simplex counterexample showing the
decomposition is not uniform in the weights, and the spherical calibration
arithmetic -- two barriered summands whose equal mixture is barrier-free. On that
last one it proves the mixture certificate positive across the whole overlap
range rather than at a single point, which the version here did not.

The connection worth keeping in mind from this module: the identity's usable half
is one-directional, and it is the same asymmetry `driftDefect` has. A barrier
excluded by some cohort at every split of the target is excluded by the pooled
fit; that pooling DISSOLVES a barrier does not follow, and needs configurations
built at the intermediate overlaps.
-/


/-- **The pooled calibration target decomposes into per-ancestry loss budgets.**

`indexwiseLoss` is a nonnegatively weighted sum of per-ancestry squared errors, so
it is a superposition landscape in the sense of `LandscapeSuperposition`, and that
file's decomposition specialises here. A prediction meets a pooled calibration
target exactly when there is a way of dividing the loss budget across ancestries
that the prediction meets ancestry by ancestry -- and the division witnessing it
is the prediction's own per-ancestry error.

Nonnegativity of the mixture weights is what makes the reverse direction true. -/
theorem pooledTarget_iff_exists_budget {m : ℕ} (π η : Fin m → ℝ) (ε v : ℝ)
    (hπ : ∀ i, 0 ≤ π i) :
    indexwiseLoss π η v ≤ ε ↔
      ∃ budget : Fin m → ℝ, (∑ i, π i * budget i) ≤ ε ∧ ∀ i, (η i - v) ^ 2 ≤ budget i := by
  constructor
  · intro h
    exact ⟨fun i ↦ (η i - v) ^ 2, h, fun i ↦ le_rfl⟩
  · rintro ⟨budget, hsum, hle⟩
    refine le_trans ?_ hsum
    exact Finset.sum_le_sum fun i _ ↦ mul_le_mul_of_nonneg_left (hle i) (hπ i)

/-- **A score no budget split can rescue is rejected by the pooled fit.**

The usable half of the decomposition, in the direction the corpus cares about. If
for every division of the loss budget across ancestries some ancestry is over its
share, then the pooled objective rejects the prediction too. Pooling cohorts
cannot rescue a score that fails ancestry-wise under every allocation.

The converse does not follow and is not stated: that pooling ADMITS a prediction
no single allocation admits would need a prediction constructed at the
intermediate errors, which no inclusion of this shape supplies. It is the same
asymmetry `driftDefect_le_indexwiseLoss` has -- a floor that transfers upward and
not down. -/
theorem pooledTarget_reject_of_every_budget_rejected {m : ℕ} (π η : Fin m → ℝ) (ε v : ℝ)
    (hπ : ∀ i, 0 ≤ π i)
    (hreject : ∀ budget : Fin m → ℝ, (∑ i, π i * budget i) ≤ ε →
      ∃ i, budget i < (η i - v) ^ 2) :
    ¬ (indexwiseLoss π η v ≤ ε) := by
  intro h
  obtain ⟨budget, hsum, hle⟩ := (pooledTarget_iff_exists_budget π η ε v hπ).mp h
  obtain ⟨i, hi⟩ := hreject budget hsum
  exact absurd (hle i) (not_le.mpr hi)


/-! #### Heterogeneous cohorts can remove a barrier that each cohort alone has

The superposition decomposition above says a barrier persists unless some
allocation satisfies every cohort at once. This records the population geometry
where that escape is available, and how much minority data it takes.

For a design whose covariance couples the planted support to a decoy support with
strength `α`, the population loss at overlap fraction `x` away from the truth is
`φ_q(x) = x(1 - qx) / (1 - qx(1-x))` with `q = α²`. A barrier exists exactly when
that profile has an interior maximum, which happens exactly when `1 - 3q + q²`
turns negative -- so the transition is at the root of that quadratic.

The root is the golden-ratio conjugate squared, and the transition in `α` is the
golden-ratio conjugate itself. Mixing two cohorts with couplings `±ρ` in
proportion `π` gives an average coupling `ρ(2π - 1)`, so a minority fraction of
`½(1 - ρ_c/ρ)` suffices to bring the mixture below the transition. At the
strongest possible coupling that is `(3 - √5)/4`, a little over nineteen per cent.

The biological reading is the one the corpus cares about: a barrier created by
linkage between a causal locus and a decoy in one ancestry can be removed by
including a second ancestry in which the linkage has the opposite sign, and the
required minority fraction is bounded away from a half. It is not a statement
about better conditioning -- the eigenvalue extremes and the coherence can be
held fixed while this happens.
-/

/-- Population loss profile at overlap fraction `x` from the truth, for coupling
strength squared `q`. -/
noncomputable def ogpOverlapProfile (q x : ℝ) : ℝ :=
  Descent.Core.overlapProfile q x

/-- With a vanishing denominator Mathlib returns `0`, which is a value this quantity can also
take legitimately, so the branch is named rather than left to be inferred from the result. -/
theorem ogpOverlapProfile_at_zero_denominator_is_junk (q x : ℝ)
    (hzero : (1 - q * x * (1 - x)) = 0) :
    ogpOverlapProfile q x = 0 := by
  unfold ogpOverlapProfile Descent.Core.overlapProfile
  rw [hzero, div_zero]


/-- **At zero overlap the profile is `1 - q`.** The best distant candidate keeps
the fraction of the loss that the coupling cannot explain away. -/
theorem ogpOverlapProfile_at_zero_overlap (q : ℝ) :
    ogpOverlapProfile q 1 = 1 - q := by
  unfold ogpOverlapProfile Descent.Core.overlapProfile
  norm_num

/-- The sign of this quadratic decides whether the loss profile has an interior
maximum, and so whether the landscape has a barrier. -/
noncomputable def ogpTransitionPolynomial (q : ℝ) : ℝ := 1 - 3 * q + q ^ 2

/-- **The transition is at the golden-ratio conjugate squared.** -/
theorem ogpTransitionPolynomial_root :
    ogpTransitionPolynomial ((3 - Real.sqrt 5) / 2) = 0 := by
  unfold ogpTransitionPolynomial
  have h : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  nlinarith [h]

/-- **And so the transition in the coupling itself is the golden-ratio
conjugate**, since squaring it returns the root above.

Stated as a root of `ogpTransitionPolynomial` rather than as the bare arithmetic identity
`((√5 - 1)/2)² = (3 - √5)/2`: the name claims something about the overlap-gap transition,
and this is that claim.  The arithmetic is still what proves it. -/
theorem ogpCouplingThreshold_sq :
    ogpTransitionPolynomial (((Real.sqrt 5 - 1) / 2) ^ 2) = 0 ∧
      ((Real.sqrt 5 - 1) / 2) ^ 2 = (3 - Real.sqrt 5) / 2 := by
  have h : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have hsq : ((Real.sqrt 5 - 1) / 2) ^ 2 = (3 - Real.sqrt 5) / 2 := by nlinarith [h]
  exact ⟨by rw [hsq]; exact ogpTransitionPolynomial_root, hsq⟩

/-- **The minority fraction that removes the barrier at maximal coupling.**

Two cohorts with couplings of opposite sign, mixed in proportion `π`, have average
coupling `ρ(2π - 1)`. Setting that to the threshold and solving for the minority
share gives `½(1 - ρ_c/ρ)`; at `ρ = 1` it is `(3 - √5)/4`, a little over nineteen
per cent. Bounded away from a half: the minority cohort does not have to be
half the data. -/
theorem ogpMinorityFraction_at_unit_coupling :
    (1 - (Real.sqrt 5 - 1) / 2) / 2 = (3 - Real.sqrt 5) / 4 := by
  ring

/-! #### The sign restriction the nineteen per cent depends on

The construction above mixes couplings `ρ` and `-ρ`, and it closes the barrier by
passing the mixed coupling through zero at `π = 1/2`. That is a cancellation of
opposite signs, not an averaging of magnitudes, and the distinction decides
whether the minority share means anything for study design: real ancestries
usually differ in the *magnitude* of their linkage correlations, not the sign.
Sign flips occur -- a variant arising on a different haplotype background -- but
they are not the typical case.

The two results below say exactly that: the mixed coupling is the convex
combination of the two cohort couplings, and it reaches zero only at the balance
point. The complementary half -- that same-sign cohorts keep their sign under
every mixture, so no mixture reaches zero -- is
`sameSignAncestryPooling_preservesActiveCorrelation` in `LandscapeSuperposition`,
and is not restated here.

So the demonstrated mechanism is narrower than "diversity helps", and whether
same-sign cohorts of differing magnitude can also close a barrier is not settled
by this construction. -/
noncomputable def mixtureCoupling (ρ π : ℝ) : ℝ := ρ * (2 * π - 1)

/-- **The mixed coupling is the convex combination of `ρ` and `-ρ`.** Written this
way the mechanism is visible: the two cohorts enter with opposite signs. -/
theorem mixtureCoupling_eq_convex (ρ π : ℝ) :
    mixtureCoupling ρ π = π * ρ + (1 - π) * (-ρ) := by
  unfold mixtureCoupling
  ring

/-- **Opposite signs close the barrier at the balance point, and only there.** -/
theorem mixtureCoupling_eq_zero_iff (ρ π : ℝ) (hρ : ρ ≠ 0) :
    mixtureCoupling ρ π = 0 ↔ π = 1 / 2 := by
  unfold mixtureCoupling
  constructor
  · intro h
    rcases mul_eq_zero.mp h with h' | h'
    · exact absurd h' hρ
    · linarith
  · intro h
    rw [h]
    ring


/-! #### A direction invisible to the pooled design is invisible to every cohort

The exact-degeneracy counterpart, and it runs the other way from the barrier
result. Pooling cannot manufacture identifiability: if a coefficient direction
carries no signal in the pooled design, it carries none in any cohort. What
pooling does is the converse -- a direction invisible in one cohort can be visible
in the pool, because the pooled quadratic form is a nonnegatively weighted sum and
vanishes only when every term does.

So heterogeneous cohorts shrink the exactly-unidentifiable set by intersecting
it, which is the precise sense in which adding an ancestry can resolve an
ambiguity that no single ancestry resolves. -/
theorem pooledQuadratic_eq_zero_iff {K : ℕ} (π : Fin K → ℝ) (Q : Fin K → ℝ)
    (hπ : ∀ g, 0 < π g) (hQ : ∀ g, 0 ≤ Q g) (g : Fin K)
    (hzero : ∑ h, π h * Q h = 0) :
    Q g = 0 := by
  have hnn : ∀ h ∈ (Finset.univ : Finset (Fin K)), 0 ≤ π h * Q h :=
    fun h _ ↦ mul_nonneg (hπ h).le (hQ h)
  have := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hzero g (Finset.mem_univ g)
  exact (mul_eq_zero.mp this).resolve_left (hπ g).ne'



/-! #### Heterogeneity fattens the lower tail, so barriers close by filling not deleting

The intuition that pooling cohorts removes a barrier by DELETING the distant
cluster is backwards, and the correction is a one-line concavity argument.

The large-deviation rate for an anomalously small residual is built from
`log (1 + 2λs)` in the per-cohort residual scales `s`. That function is concave,
so a mixture of cohorts has rate at most that of a single cohort at the average
scale. Holding the average covariance fixed, heterogeneity cannot make a
candidate's anomalously good fit exponentially less likely -- it makes it at
least as likely.

So at fixed average covariance a barrier closes by FILLING the intermediate
region, not by removing the far cluster. That matches the decomposition above,
whose usable half certifies persistence and says nothing about dissolution: the
dissolution direction needs configurations built at intermediate overlaps, and
this says the tails there are if anything fatter than the homogeneous
comparison would suggest.
-/

/-- **Two cohorts have a smaller rate than one cohort at their average scale.**

Concavity of the logarithm, applied at the residual scales. `π` and `1 - π` are
the cohort proportions and `s₁`, `s₂` the per-cohort residual scales; the
right-hand side is the rate of a homogeneous design whose scale is the mixture
average. A smaller rate means a fatter lower tail. -/
theorem mixtureRate_le_averagedRate (π s₁ s₂ lam : ℝ)
    (hπ0 : 0 ≤ π) (hπ1 : π ≤ 1) (hs₁ : 0 < 1 + 2 * lam * s₁) (hs₂ : 0 < 1 + 2 * lam * s₂) :
    π * Real.log (1 + 2 * lam * s₁) + (1 - π) * Real.log (1 + 2 * lam * s₂)
      ≤ Real.log (1 + 2 * lam * (π * s₁ + (1 - π) * s₂)) := by
  have hcon : ConcaveOn ℝ (Set.Ioi 0) Real.log := strictConcaveOn_log_Ioi.concaveOn
  have h := hcon.2 (Set.mem_Ioi.mpr hs₁) (Set.mem_Ioi.mpr hs₂) hπ0
    (by linarith : (0:ℝ) ≤ 1 - π) (by ring : π + (1 - π) = 1)
  have hmix : π • (1 + 2 * lam * s₁) + (1 - π) • (1 + 2 * lam * s₂)
      = 1 + 2 * lam * (π * s₁ + (1 - π) * s₂) := by
    simp only [smul_eq_mul]
    ring
  rw [hmix] at h
  simpa [smul_eq_mul] using h

/-! #### The frequency-spectrum inverse problem locks complexity to ill-posedness

For a demographic history with at most `K` epochs, the sharp stability exponent
for recovering it from the expected site-frequency spectrum is `1 / (2K - 3)`.
Read through the sample size the spectrum comes from, that constant is not an
arbitrary function of `K`.

A sample of `n = 2K - 2` haplotypes has exactly `n - 1 = 2K - 3` spectrum entries,
so the exponent is the reciprocal of the number of entries available. Each extra
epoch demands two more samples AND costs two in the exponent: the model's
complexity and the inverse problem's ill-posedness move together, and no
sampling effort separates them.

Two epochs are Lipschitz-stable. Three already have cube-root instability, four
fifth-root. -/

/-- Sample size whose spectrum resolves a `K`-epoch history. -/
def epochSampleSize (K : ℕ) : ℕ :=
  Descent.Core.pairedEpochCount K

/-- Number of unfolded spectrum entries at that sample size. -/
def spectrumEntries (n : ℕ) : ℕ := n - 1

/-- **The stability exponent's denominator is the number of spectrum entries.**
Not a coincidence of the parameterisation: it says the recoverable resolution is
set by how many numbers the spectrum has, and each epoch consumes two of them. -/
theorem spectrumEntries_epochSampleSize (K : ℕ) (hK : 2 ≤ K) :
    spectrumEntries (epochSampleSize K) = 2 * K - 3 := by
  unfold spectrumEntries epochSampleSize Descent.Core.pairedEpochCount
  omega

/-- **Two epochs are Lipschitz-stable.** -/
theorem spectrumEntries_two_epochs : spectrumEntries (epochSampleSize 2) = 1 := by decide

/-- **Three epochs are cube-root stable.** -/
theorem spectrumEntries_three_epochs : spectrumEntries (epochSampleSize 3) = 3 := by decide

/-- **Four epochs are fifth-root stable.** -/
theorem spectrumEntries_four_epochs : spectrumEntries (epochSampleSize 4) = 5 := by decide


/-! #### Drift invisible to genotype is irreducible by any amount of genotyping

The defect splits into a part measurable with respect to the genotype-distribution structure and a
part orthogonal to it. Only the first is attackable by more reference panels, deeper sequencing,
or better ancestry inference: the second is invisible to every genotype-measurable statistic, so
no quantity of genotype data touches it.

The witness is two ancestries whose genotype distributions coincide -- so any genotype-based
method assigns them the same value, and any inferred ancestry coordinate merges them -- carrying
different conditional risks. At the genotype-visible resolution the defect is zero. The true
defect is positive. The gap is irreducible.

This is the formal shape of the binding empirical objection to the whole extrapolation programme.
Harpak and colleagues report that variation in individual-level prediction accuracy is only weakly
predicted by genetic distance and is explained comparably well by socioeconomic measures. If that
is so, a large part of the drift field sits in exactly the orthogonal component witnessed here,
and the fill-distance machinery -- which prices extrapolation in a metric induced by the GENOTYPE
marginals -- is pricing the wrong thing. More diverse genotyping shrinks the attackable part and
leaves the rest untouched.

The theory gives the accounting and not the causal decomposition. It says which portion of a
measured portability gap is in principle reachable by genetic data; it does not say how large
that portion is, and the empirical claim is that it may be the smaller one.
-/

/-- Two ancestries indistinguishable by genotype: any genotype-measurable statistic, and hence any
inferred ancestry coordinate, assigns them the common value.

Empirical status: NOT AN EMPIRICAL CLAIM -- these values define a nonidentifiability witness. -/
noncomputable def genotypeVisibleRisk : Fin 2 → ℝ := ![1 / 2, 1 / 2]

/-- Their true conditional risks, which differ.

Empirical status: NOT AN EMPIRICAL CLAIM -- these values define a nonidentifiability witness. -/
noncomputable def trueRiskUnderSocialDrift : Fin 2 → ℝ := ![4 / 5, 1 / 5]

/-- The genotype-visible witness deliberately reuses the earlier coarsened risk field. -/
theorem genotypeVisibleRisk_eq_binnedRiskByAncestry :
    genotypeVisibleRisk = binnedRiskByAncestry := by
  funext i
  fin_cases i <;> norm_num [genotypeVisibleRisk, binnedRiskByAncestry]

/-- The genotype-visible witness is also the earlier uniform two-ancestry vector. -/
theorem genotypeVisibleRisk_eq_uniformTwoWeights :
    genotypeVisibleRisk = uniformTwoWeights := by
  funext i
  fin_cases i <;> norm_num [genotypeVisibleRisk, uniformTwoWeights]

/-- The social-drift witness deliberately reuses the earlier fine risk field. -/
theorem trueRiskUnderSocialDrift_eq_fineRiskByAncestry :
    trueRiskUnderSocialDrift = fineRiskByAncestry := by
  funext i
  fin_cases i <;> norm_num [trueRiskUnderSocialDrift, fineRiskByAncestry]

/-- The same reversed conditional is also the repository's post-hoc-recalibration witness. -/
theorem trueRiskUnderSocialDrift_eq_reorderTarget :
    trueRiskUnderSocialDrift = reorderTarget := by
  funext i
  fin_cases i <;> norm_num [trueRiskUnderSocialDrift, reorderTarget]

/-- **Genotype data sees no obstruction here.** -/
theorem genotypeVisible_driftDefect_zero :
    driftDefect ancestryPairWeights genotypeVisibleRisk = 0 := by
  unfold driftDefect pooledConditional ancestryPairWeights genotypeVisibleRisk
  norm_num [Fin.sum_univ_two]

/-- **The obstruction is nonetheless there.** -/
theorem trueRisk_driftDefect_pos :
    0 < driftDefect ancestryPairWeights trueRiskUnderSocialDrift := by
  unfold driftDefect pooledConditional ancestryPairWeights trueRiskUnderSocialDrift
  norm_num [Fin.sum_univ_two]

/-- **So no amount of genotyping closes it.** Every genotype-measurable statistic takes the same
value on the two ancestries, so every predictor built from genotype data alone assigns them the
same risk and carries the full gap. Diversifying the reference panel moves the attackable
component and cannot move this one. -/
theorem genotype_invisible_drift_irreducible :
    driftDefect ancestryPairWeights genotypeVisibleRisk
      < driftDefect ancestryPairWeights trueRiskUnderSocialDrift := by
  rw [genotypeVisible_driftDefect_zero]
  exact trueRisk_driftDefect_pos

/-! #### A decision loss wants a median, not the mean that meta-analysis estimates

Under squared loss the single best target is the ancestry-weighted MEAN, which is what a
fixed-effects meta-analysis across cohorts estimates. Under a threshold decision loss it is a
weighted MEDIAN of the ancestry-conditional risks. When the ancestry distribution is skewed --
and a GWAS-derived `π` is heavily skewed -- these are different numbers, so the quantity the
literature estimates is not the quantity a deployment decision needs.

The witness below has three ancestries at weights `2/5, 3/10, 3/10` carrying risks `0, 0, 1`. The
weighted mean is `3/10`; the weighted median is `0`. Absolute loss at `0` is `3/10`, and at the
mean it is `21/50` -- strictly worse. The pooled mean is not merely a different summary, it is
suboptimal for the decision.
-/

/-- A skewed ancestry distribution.

Empirical status: NOT AN EMPIRICAL CLAIM -- these rational weights define a proof witness. -/
noncomputable def skewedAncestryWeights : Fin 3 → ℝ := ![2 / 5, 3 / 10, 3 / 10]

/-- Ancestry-conditional risks at the operating point.

Empirical status: NOT AN EMPIRICAL CLAIM -- these values define a proof witness. -/
noncomputable def skewedAncestryRisks : Fin 3 → ℝ := ![0, 0, 1]

/-- Ancestry-weighted absolute loss, the criterion a threshold decision induces. -/
noncomputable def absoluteLoss {m : ℕ} (π η : Fin m → ℝ) (v : ℝ) : ℝ :=
  ∑ i, π i * |η i - v|

/-- Reference evaluation at two atoms with distinct masses and locations. -/
theorem absoluteLoss_at_reference_point :
    absoluteLoss (![1, 3] : Fin 2 → ℝ) (![2, 5] : Fin 2 → ℝ) 4 = 5 := by
  norm_num [absoluteLoss, Fin.sum_univ_two]


/-- **The pooled mean is `3/10`.** -/
theorem skewedAncestry_pooled_mean :
    pooledConditional skewedAncestryWeights skewedAncestryRisks = 3 / 10 := by
  unfold pooledConditional skewedAncestryWeights skewedAncestryRisks
  norm_num [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]

/-- **The median beats the mean under absolute loss.**

So the target a decision loss wants is not the one a meta-analysis reports. Estimating the pooled
effect and deploying it at a threshold optimises the wrong functional, and the gap widens with the
skew of the ancestry distribution. -/
theorem median_beats_mean_under_absolute_loss :
    absoluteLoss skewedAncestryWeights skewedAncestryRisks 0
      < absoluteLoss skewedAncestryWeights skewedAncestryRisks (3 / 10) := by
  unfold absoluteLoss skewedAncestryWeights skewedAncestryRisks
  norm_num [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons, abs_of_nonneg, abs_of_nonpos]

/-! #### Unequal per-ancestry sample sizes inflate the effective resolution

Splitting the index into `k` cells and estimating within each costs an estimation term
proportional to the EFFECTIVE cell count `N * ∑ πᵢ / nᵢ`, not to `k`.  For equal cell
weights this is minimized by equal allocation and any departure costs a harmonic factor.  For
unequal weights the square-root law proved below replaces proportional allocation.

The equal-weight two-cell case is stated first: the penalty is at least four, attained by equal
allocation, and grows without bound as the split becomes lopsided.  The subsequent theorems then
separate posterior-weighted and worst-ancestry recruitment objectives.
-/

/-- **The harmonic penalty for unequal allocation.** -/
theorem harmonic_allocation_penalty (n₁ n₂ : ℝ) (h₁ : 0 < n₁) (h₂ : 0 < n₂) :
    4 ≤ (n₁ + n₂) * (1 / n₁ + 1 / n₂) := by
  have hexp : (n₁ + n₂) * (1 / n₁ + 1 / n₂) = 2 + n₁ / n₂ + n₂ / n₁ := by
    field_simp
    ring
  rw [hexp]
  have hkey : 2 ≤ n₁ / n₂ + n₂ / n₁ := by
    rw [div_add_div _ _ (ne_of_gt h₂) (ne_of_gt h₁), le_div_iff₀ (by positivity)]
    nlinarith [sq_nonneg (n₁ - n₂)]
  linarith

/-- **Equal allocation attains it**, so the bound is the exact cost of departing from
proportional design rather than a loose estimate. -/
theorem harmonic_allocation_penalty_equal (n : ℝ) (h : 0 < n) :
    (n + n) * (1 / n + 1 / n) = 4 := by
  field_simp
  ring

/-! #### Recruitment depends on the deployment objective

The preceding equal-weight witness does not justify proportional recruitment for unequal ancestry
weights.  For the stated `L²(π)` estimation term `∑ πᵢ / nᵢ`, the exact two-cell lower
bound is attained by square-root (Neyman) allocation, `nᵢ ∝ √πᵢ`.  A worst-ancestry
objective is different again: with equal per-sample noise it is minimized by equal precision,
independently of the deployment mixture.  Thus an objective must be fixed before a recruitment
rule can be called optimal.
-/

/-- The two-cell contribution to posterior-weighted mean squared estimation error.

Empirical status: NOT AN EMPIRICAL CLAIM -- this is the algebraic objective being optimized. -/
noncomputable def twoCellL2EstimationPenalty (p n₁ n₂ : ℝ) : ℝ :=
  p / n₁ + (1 - p) / n₂

/-- **twoCellL2EstimationPenalty at its junk point, named.** An empty first cell makes its
estimation penalty unbounded. The divisor is zero, that term vanishes, and the penalty reduces
to the second cell alone -- so a design that samples one ancestry not at all is charged only for
the ancestry it did sample. Consumers must exclude the argument that makes the guard vanish. -/
theorem twoCellL2EstimationPenalty_empty_first_cell_is_junk (p n₂ : ℝ) :
    twoCellL2EstimationPenalty p 0 n₂ = (1 - p) / n₂ := by
  unfold twoCellL2EstimationPenalty
  simp

/-- The two-cell worst-ancestry estimation error when both cells have equal observation noise.

Empirical status: NOT AN EMPIRICAL CLAIM -- this is the algebraic objective being optimized. -/
noncomputable def twoCellWorstEstimationPenalty (n₁ n₂ : ℝ) : ℝ :=
  max (1 / n₁) (1 / n₂)

/-- **twoCellWorstEstimationPenalty at its junk point, named.** Two empty cells give an unbounded
worst-case estimation penalty. Both reciprocals are junk-zero and the maximum is `0`: the best
possible worst case, certified for a design with no data in either cell. Consumers must guard
the argument that makes the divisor vanish. -/
theorem twoCellWorstEstimationPenalty_empty_cells_is_junk :
    twoCellWorstEstimationPenalty 0 0 = 0 := by
  unfold twoCellWorstEstimationPenalty
  simp

/-- **The exact `L²(π)` recruitment bound.**  Its right side is the total sample size times
the weighted estimation penalty.  Equality holds precisely on the square-root allocation ray. -/
theorem twoCell_l2_allocation_lower_bound (p n₁ n₂ : ℝ)
    (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1) (hn₁ : 0 < n₁) (hn₂ : 0 < n₂) :
    (Real.sqrt p + Real.sqrt (1 - p)) ^ 2 ≤
      (n₁ + n₂) * twoCellL2EstimationPenalty p n₁ n₂ := by
  have hsqp : Real.sqrt p ^ 2 = p := Real.sq_sqrt hp₀
  have hsqc : Real.sqrt (1 - p) ^ 2 = 1 - p :=
    Real.sq_sqrt (sub_nonneg.mpr hp₁)
  have hscaled :
      ((n₁ + n₂) * twoCellL2EstimationPenalty p n₁ n₂ -
          (Real.sqrt p + Real.sqrt (1 - p)) ^ 2) * (n₁ * n₂) =
        (Real.sqrt p * n₂ - Real.sqrt (1 - p) * n₁) ^ 2 := by
    unfold twoCellL2EstimationPenalty
    field_simp [ne_of_gt hn₁, ne_of_gt hn₂]
    ring_nf
    rw [hsqp, hsqc]
    ring
  nlinarith [sq_nonneg (Real.sqrt p * n₂ - Real.sqrt (1 - p) * n₁),
    mul_pos hn₁ hn₂]

/-- **Worst-ancestry recruitment has a different lower bound.**  Equal precision minimizes the
largest cell variance; deployment prevalence does not enter this objective. -/
theorem twoCell_worst_allocation_lower_bound (n₁ n₂ : ℝ) (hn₁ : 0 < n₁) (hn₂ : 0 < n₂) :
    2 / (n₁ + n₂) ≤ twoCellWorstEstimationPenalty n₁ n₂ := by
  rcases le_total n₁ n₂ with h₁₂ | h₂₁
  · apply le_trans _ (le_max_left _ _)
    rw [div_le_div_iff₀ (add_pos hn₁ hn₂) hn₁]
    nlinarith
  · apply le_trans _ (le_max_right _ _)
    rw [div_le_div_iff₀ (add_pos hn₁ hn₂) hn₂]
    nlinarith

/-- Equal recruitment attains the worst-ancestry lower bound exactly. -/
theorem twoCell_worst_allocation_equal (n : ℝ) (hn : 0 < n) :
    twoCellWorstEstimationPenalty n n = 2 / (n + n) := by
  unfold twoCellWorstEstimationPenalty
  rw [max_self]
  field_simp
  norm_num

/-- **Proportional recruitment can be strictly suboptimal even for the `L²(π)` objective.**
At deployment weight `4/5`, both allocations below use `15n` samples.  The square-root allocation
`10n:5n` has lower weighted estimation error than the proportional allocation `12n:3n`. -/
theorem squareRoot_allocation_beats_proportional (n : ℝ) (hn : 0 < n) :
    twoCellL2EstimationPenalty (4 / 5) (10 * n) (5 * n) <
      twoCellL2EstimationPenalty (4 / 5) (12 * n) (3 * n) := by
  unfold twoCellL2EstimationPenalty
  field_simp [ne_of_gt hn]
  nlinarith


/-! #### Resolution monotonicity in general, not just on a witness

The merge witness shows coarsening loses drift energy in one instance; the atomic split shows
exactly what a two-way merge costs. The general statement is that a CELL of any size, collapsed
to its weighted mean, retains at most the energy it had, and the shortfall is the within-cell
dispersion.

This is weighted Cauchy-Schwarz, and it is what makes resolution monotone under arbitrary
refinement rather than only under pairwise merges: any coarsening is a composition of cell
collapses, and each one loses energy.

Biologically it says the same thing at every granularity. A deployment that calibrates on
continental groupings resolves at most what one calibrating on finer ancestry resolves, whatever
the groupings are, and the deficit is the spread of risk inside each grouping. -/
theorem cell_collapse_loses_energy {m : ℕ} (s : Finset (Fin m)) (π w : Fin m → ℝ)
    (hπ : ∀ i, 0 ≤ π i) :
    (∑ i ∈ s, π i * w i) ^ 2 ≤ (∑ i ∈ s, π i) * ∑ i ∈ s, π i * w i ^ 2 := by
  have key := Finset.sum_mul_sq_le_sq_mul_sq s
    (fun i ↦ Real.sqrt (π i)) (fun i ↦ Real.sqrt (π i) * w i)
  have hprod : ∀ i ∈ s, Real.sqrt (π i) * (Real.sqrt (π i) * w i) = π i * w i := by
    intro i _
    rw [← mul_assoc, Real.mul_self_sqrt (hπ i)]
  have hsq1 : ∀ i ∈ s, Real.sqrt (π i) ^ 2 = π i := by
    intro i _
    rw [Real.sq_sqrt (hπ i)]
  have hsq2 : ∀ i ∈ s, (Real.sqrt (π i) * w i) ^ 2 = π i * w i ^ 2 := by
    intro i _
    rw [mul_pow, Real.sq_sqrt (hπ i)]
  calc (∑ i ∈ s, π i * w i) ^ 2
      = (∑ i ∈ s, Real.sqrt (π i) * (Real.sqrt (π i) * w i)) ^ 2 := by
        rw [Finset.sum_congr rfl hprod]
    _ ≤ (∑ i ∈ s, Real.sqrt (π i) ^ 2) * ∑ i ∈ s, (Real.sqrt (π i) * w i) ^ 2 := key
    _ = (∑ i ∈ s, π i) * ∑ i ∈ s, π i * w i ^ 2 := by
        rw [Finset.sum_congr rfl hsq1, Finset.sum_congr rfl hsq2]

/-- **A cell of unit weight retains at most its energy.** The normalised form, which is the one
that composes: collapsing a cell to its mean can only lose. -/
theorem cell_collapse_loses_energy_normalised {m : ℕ} (s : Finset (Fin m)) (π w : Fin m → ℝ)
    (hπ : ∀ i, 0 ≤ π i) (hs : ∑ i ∈ s, π i = 1) :
    (∑ i ∈ s, π i * w i) ^ 2 ≤ ∑ i ∈ s, π i * w i ^ 2 := by
  have h := cell_collapse_loses_energy s π w hπ
  rwa [hs, one_mul] at h

/-! #### Which decision losses survive the drift

A threshold decision loss at `τ` charges only for outcomes on the wrong side of `τ`. If every
ancestry-specific risk lies on one side of the threshold, the drift moves no decision and the
loss is unaffected: the score is simultaneously optimal for that loss at every ancestry. If the
threshold falls strictly inside the range of ancestry-specific risks, no single prediction is
optimal for all of them.

That is the exact criterion. A clinical threshold set outside the spread of ancestry-specific
risks transports; one set inside it does not, however well the score is calibrated.
-/

/-- The part of the threshold regret charged to ancestries above the threshold. -/
noncomputable def aboveThresholdMass {m : ℕ} (π η : Fin m → ℝ) (τ : ℝ) : ℝ :=
  ∑ i, π i * max (η i - τ) 0

/-- **A threshold above every ancestry-specific risk is untouched by the drift.** -/
theorem aboveThresholdMass_eq_zero {m : ℕ} (π η : Fin m → ℝ) (τ : ℝ)
    (h : ∀ i, η i ≤ τ) :
    aboveThresholdMass π η τ = 0 := by
  unfold aboveThresholdMass
  refine Finset.sum_eq_zero fun i _ ↦ ?_
  rw [max_eq_right (by linarith [h i])]
  ring

/-- **A threshold strictly inside the drift range is not.** With two ancestries at risks `0` and
`1` and a threshold at one half, the above-threshold mass is positive, so the decision the loss
recommends differs between ancestries and no single prediction serves both. -/
theorem aboveThresholdMass_pos_inside :
    0 < aboveThresholdMass uniformTwoWeights twoAncestryConditional (1 / 2) := by
  unfold aboveThresholdMass uniformTwoWeights twoAncestryConditional
  norm_num [Fin.sum_univ_two]


/-! #### Why a threshold inside the drift range admits no single decision

`aboveThresholdMass_eq_zero` and `belowThresholdMass_eq_zero` say a threshold outside the range of
ancestry-specific risks is untouched. The reason a threshold INSIDE the range cannot be served is
sharper than "the regret is positive": the two ancestries fall on opposite sides of it, so the
decision the loss recommends is literally different at each, and no single prediction is the
right decision at both.

That is the deployment question, stated exactly. It is not "is the score calibrated" but "does
the spread of ancestry-specific risk at my operating point straddle my clinical cutoff". The
first is an aggregate diagnostic; the second is decidable from the fitted per-ancestry curves and
is the one that determines whether the cutoff transports. -/
theorem threshold_inside_separates_ancestries (τ : ℝ) (h0 : 0 < τ) (h1 : τ < 1) :
    twoAncestryConditional 0 < τ ∧ τ < twoAncestryConditional 1 := by
  have e0 : twoAncestryConditional 0 = 0 := by unfold twoAncestryConditional; norm_num
  have e1 : twoAncestryConditional 1 = 1 := by unfold twoAncestryConditional; norm_num
  rw [e0, e1]
  exact ⟨h0, h1⟩

/-- **A threshold outside the range does not separate them.** Both ancestries sit on the same side,
so the decision is the same at each and the cutoff transports unchanged. The pair with the theorem
above is the survival criterion in decision form. -/
theorem threshold_outside_does_not_separate (τ : ℝ) (h : 1 < τ) :
    twoAncestryConditional 0 < τ ∧ twoAncestryConditional 1 < τ := by
  have e0 : twoAncestryConditional 0 = 0 := by unfold twoAncestryConditional; norm_num
  have e1 : twoAncestryConditional 1 = 1 := by unfold twoAncestryConditional; norm_num
  rw [e0, e1]
  exact ⟨by linarith, h⟩

/-- **Equal risks across ancestries leave nothing to obstruct.** The defect vanishes exactly when
the conditional does not drift, which is the other degenerate case worth naming beside
`pointMass_driftDefect_zero`: there the index was determined by the covariate, here the index
exists but carries no risk variation. Either way the framework says nothing, and a deployment
should know which of the two it is in. -/
theorem constantConditional_driftDefect_zero {m : ℕ} (π : Fin m → ℝ) (c : ℝ)
    (hπ : ∑ i, π i = 1) :
    driftDefect π (fun _ ↦ c) = 0 := by
  have hpool : pooledConditional π (fun _ ↦ c) = c := by
    unfold pooledConditional
    rw [← Finset.sum_mul, hπ, one_mul]
  unfold driftDefect
  rw [hpool]
  simp

/-! #### The score's own distribution cannot see how it aligns with ancestry

`pooledConditional_does_not_identify_drift` says the pooled conditional cannot see drift across
ancestries. This is the same failure one layer up, in the metric: the DISTRIBUTION of a score's
values across a population does not determine how those values are arranged relative to ancestry
distance.

Three ancestries at metric positions `0, 1, 3`, equally weighted, and a score taking the values
`0, 1, 2`. Permuting which ancestry receives which value leaves the score's distribution exactly
unchanged, and the ancestry geometry exactly unchanged, while the alignment energy moves from
`10/3` to `2`. So no functional of the score's marginal distribution -- not its mean, variance,
quantiles, or full histogram -- can detect alignment.
-/

/-- Three ancestries at positions `0`, `1`, `3` on the line.

Empirical status: NOT AN EMPIRICAL CLAIM -- this is a finite counterexample. -/
noncomputable def ancestryPosition : Fin 3 → ℝ := ![0, 1, 3]

/-- The third ancestry occupies position three in the finite counterexample. -/
@[simp] theorem ancestryPosition_two : ancestryPosition 2 = 3 := rfl

/-- Distance between two ancestries on the line.

Empirical status: NOT AN EMPIRICAL CLAIM -- this is the metric of a finite counterexample. -/
noncomputable def threeAncestryDistance : Fin 3 → Fin 3 → ℝ :=
  fun i j ↦ |ancestryPosition i - ancestryPosition j|

/-- A score assigning values `0, 1, 2` to the three ancestries.

Empirical status: NOT AN EMPIRICAL CLAIM -- this reuses the finite drift witness. -/
noncomputable def ancestryScore : Fin 3 → ℝ := threeAncestryConditional

/-- The same three values, permuted between the ancestries.

Empirical status: NOT AN EMPIRICAL CLAIM -- this is a finite counterexample. -/
noncomputable def ancestryScoreSwapped : Fin 3 → ℝ := ![0, 2, 1]

/-- Dirichlet-type energy coupling ancestry distance to score differences.

Empirical status: NOT AN EMPIRICAL CLAIM -- this defines the counterexample's energy. -/
noncomputable def ancestryAlignmentEnergy (m : Fin 3 → ℝ) : ℝ :=
  (1 / 9) * ∑ i, ∑ j, threeAncestryDistance i j * (m i - m j) ^ 2

/-- **The two scores have the same marginal**, being the same values permuted. -/
theorem ancestryScoreSwapped_is_permutation :
    ancestryScoreSwapped = ancestryScore ∘ ![0, 2, 1] := by
  funext i
  fin_cases i <;> rfl

/-- **The aligned arrangement's energy.** -/
theorem ancestryAlignmentEnergy_score : ancestryAlignmentEnergy ancestryScore = 10 / 3 := by
  unfold ancestryAlignmentEnergy threeAncestryDistance ancestryPosition ancestryScore
  simp only [Fin.sum_univ_three, threeAncestryConditional, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
  norm_num [abs_of_nonneg, abs_of_nonpos]

/-- **The permuted arrangement's energy**, against the same metric and the same score values.

With `ancestryScoreSwapped_is_permutation` this is the separation: identical ancestry geometry,
identical score distribution, different alignment. -/
theorem ancestryAlignmentEnergy_swapped : ancestryAlignmentEnergy ancestryScoreSwapped = 2 := by
  unfold ancestryAlignmentEnergy threeAncestryDistance ancestryPosition ancestryScoreSwapped
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons]
  norm_num [abs_of_nonneg, abs_of_nonpos]


/-! #### A rare ancestry is not proportionately harmless

The drift defect is an `L²` quantity, and the functional built from it moves like the SQUARE ROOT
of a subgroup's mass, not like the mass. So the standard dismissal -- "that ancestry is one per
cent of the sample, so it can move a global statistic by at most one per cent" -- is wrong by a
square root, and wrong in the direction that understates the damage.

Concretely: a population that is `1 - ε` one ancestry and `ε` another, whose conditionals differ
by one, has drift defect `ε (1 - ε)`. The mixture was perturbed by `ε`; the calibration functional
`√defect` moved by `√(ε(1-ε)) ≍ √ε`. No Lipschitz constant in the mass exists, and the theorem
below says so in the form that needs no square roots: the defect strictly exceeds the square of
the rare group's share.

This is the exact mechanism behind the failure of any uniform-Lipschitz claim for a variance-type
decoration functional: on the exceptional set of mass `ε` the values differ by `O(1)`, which
contributes `O(ε)` to a SQUARED quantity and therefore `O(√ε)` to the functional itself.
-/

/-- A population that is `1 - ε` one ancestry and `ε` another.

Empirical status: NOT AN EMPIRICAL CLAIM -- this is a fixed two-point weight. -/
noncomputable def rareAncestryWeights (ε : ℝ) : Fin 2 → ℝ := ![1 - ε, ε]

/-- The rare ancestry carries a conditional risk one unit away from the common one.

Empirical status: NOT AN EMPIRICAL CLAIM -- this reuses the canonical two-ancestry witness. -/
noncomputable def rareAncestryRisks : Fin 2 → ℝ := twoAncestryConditional

/-- **The rare ancestry's defect, exactly.** -/
theorem rareAncestry_driftDefect_eq (ε : ℝ) :
    driftDefect (rareAncestryWeights ε) rareAncestryRisks = ε * (1 - ε) := by
  unfold driftDefect pooledConditional rareAncestryWeights rareAncestryRisks
    twoAncestryConditional
  simp [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

/-- **And it exceeds the square of the rare group's share**, for any share below one half.

Read as a rate: the defect is `Θ(ε)` where a Lipschitz response to an `ε` perturbation of the
mixture would be `O(ε²)`. The calibration functional is the square root of this, so it moves like
`√ε`. A subgroup at one per cent of the sample moves it by ten per cent. -/
theorem rareAncestry_defect_exceeds_share_squared (ε : ℝ) (h0 : 0 < ε) (h1 : ε < 1 / 2) :
    ε ^ 2 < driftDefect (rareAncestryWeights ε) rareAncestryRisks := by
  rw [rareAncestry_driftDefect_eq]
  nlinarith

/-- **And the converse**, which the "exactly when" above asserts and the theorem before it does
not supply. If every ancestry carries positive weight and the defect vanishes, then every
ancestry's conditional equals the pooled one -- so the defect is zero precisely on the
non-drifting conditionals, and a zero defect is evidence about the biology rather than an
artefact of the weighting.

The positivity hypothesis is needed and is not decoration: an ancestry of weight zero contributes
nothing to the defect and its conditional is unconstrained. -/
theorem constantConditional_of_driftDefect_zero {m : ℕ} (π η : Fin m → ℝ)
    (hpos : ∀ i, 0 < π i) (h : driftDefect π η = 0) (i : Fin m) :
    η i = pooledConditional π η := by
  unfold driftDefect at h
  have hnn : ∀ j ∈ (Finset.univ : Finset (Fin m)),
      0 ≤ π j * (η j - pooledConditional π η) ^ 2 :=
    fun j _ ↦ mul_nonneg (hpos j).le (sq_nonneg _)
  have hzero := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp h i (Finset.mem_univ i)
  have hsq : (η i - pooledConditional π η) ^ 2 = 0 :=
    (mul_eq_zero.mp hzero).resolve_left (hpos i).ne'
  have hx : η i - pooledConditional π η = 0 := by
    exact sq_eq_zero_iff.mp hsq
  linarith

/-- **The gap is bounded by the two sensitivities it compares.** Symmetry and the vanishing
criterion are shared by every positive multiple of this distance; the triangle bound is not,
so it is the one that fixes the multiple at one. -/
theorem sensitivityPortabilityGap_le_add_abs (a b : ℝ) :
    sensitivityPortabilityGap a b ≤ |a| + |b| := by
  unfold sensitivityPortabilityGap
  calc |b - a| ≤ |b| + |a| := abs_sub b a
    _ = |a| + |b| := by ring

/-- Absolute portability gap for PPV between source and target prevalences. -/
noncomputable def ppvPortabilityGap
    (sensitivity specificity prevalenceSource prevalenceTarget : ℝ) : ℝ :=
  |metricPPV sensitivity specificity prevalenceTarget -
    metricPPV sensitivity specificity prevalenceSource|

/-- **Equal prevalences leave no gap, whatever the operating point.**

RENAMED off `_at_reference_point`. The old name claimed to pin the body's scale,
and a statement of `0` cannot: `c · 0 = 0` for every `c`, so every rescaling of
this gap satisfies it. The vanishing is nonetheless real content — it says the
gap is a function of the DIFFERENCE between the two prevalences and not of their
level, which is exactly the property that makes it a portability gap rather than
a second copy of the PPV.

Note the quantifiers are what give it its strength: it holds for every
`sensitivity` and `specificity`, so it also says the operating point cannot
manufacture a gap on its own. That is worth keeping and is not what a reference
evaluation is for.

The scale is pinned separately, by `ppvPortabilityGap_at_reference_point` below,
which is what this theorem cannot do. -/
theorem ppvPortabilityGap_self (sensitivity specificity prevalence : ℝ) :
    ppvPortabilityGap sensitivity specificity prevalence prevalence = 0 := by
  unfold ppvPortabilityGap
  simp

/-- Reference evaluation; see `Descent.Core.Ratios` for what these pin and why. -/
theorem ppvPortabilityGap_at_reference_point :
    ppvPortabilityGap 1 (1 / 2) (1 / 5) (1 / 2) = 1 / 3 ∧
      ppvPortabilityGap 1 (1 / 2) (1 / 2) (1 / 5) = 1 / 3 := by
  constructor <;>
    · unfold ppvPortabilityGap metricPPV
      norm_num [abs_of_nonneg, abs_of_nonpos]


/-- **The gap is bounded by the two predictive values it compares.** Strict positivity under a
prevalence shift is shared by every positive multiple of this distance; the triangle bound is
not, so it is what fixes the multiple at one. -/
theorem ppvPortabilityGap_le_add_abs
    (sensitivity specificity prevalenceSource prevalenceTarget : ℝ) :
    ppvPortabilityGap sensitivity specificity prevalenceSource prevalenceTarget
      ≤ |metricPPV sensitivity specificity prevalenceTarget|
        + |metricPPV sensitivity specificity prevalenceSource| := by
  unfold ppvPortabilityGap
  exact abs_sub _ _

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

The theorem below is stated about `f1Score` from `Descent.Program.OpenQuestions`, which this
file imports. Do not restate the formula here; its `Empirical status: UNTESTED` marker
belongs with that one definition. -/

/-- F1 is bounded above by 1 when both precision and sensitivity lie in `(0,1]`. -/
theorem f1_le_one
    (precision sens : ℝ)
    (h_p : 0 < precision) (h_r : 0 < sens)
    (h_p1 : precision ≤ 1) (h_r1 : sens ≤ 1) :
    Program.f1Score precision sens ≤ 1 := by
  unfold Program.f1Score
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
  readout : LevelSetCoordinates
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
def ScreeningDeployment.atPrevalence (readout : LevelSetCoordinates)
    (prevalence : ℝ) : ScreeningDeployment where
  readout := readout
  prevalence := prevalence

instance ScreeningDeployment.instNonempty : Nonempty ScreeningDeployment :=
  ⟨ScreeningDeployment.atPrevalence LevelSetCoordinates.undegraded 0⟩

/-- The constructed pair does share its readout, so the shared-readout hypothesis
of the split result is discharged rather than assumed for this family. -/
theorem ScreeningDeployment.atPrevalence_readout_eq (readout : LevelSetCoordinates)
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
    (hsens : IsLevelSetFunctional sens ScreeningDeployment.readout)
    (hspec : IsLevelSetFunctional spec ScreeningDeployment.readout)
    (readout : LevelSetCoordinates) (prevalence prevalence' : ℝ) :
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
  unfold brierFromR2 TransportedMetrics.calibratedBrier
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

/-!
## Metric-specific portability of the marker panel itself: the AR(1) frontier

Open Question 3 asks which *metric* a score is portable in.  Everything above
holds the marker panel fixed and varies the metric.  This section varies the
panel and finds the same phenomenon one level down: the panel construction step
— LD pruning or clumping — is itself a choice of metric, and it is not neutral
between the two things a panel is used for.

`Descent.Spectral.ProjectionShiftBounds` proves the general statement: among relaxed
rank-`k` reductions of a background covariance, the variance-greedy one
simultaneously maximises reconstruction efficiency
(`topVariance_maximizes_reconstruction`) and minimises detection efficiency
(`topVariance_minimizes_detection`).  LD pruning is variance-greedy by
construction: it keeps one representative per correlated block, which in the
eigenbasis is a low-frequency band.

Here that abstract frontier is made numerical.  On a chromosome whose LD follows
the first-order Markov law of `Descent.Blindness.ImitationRigidity` — correlation `ρ^d`
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

Empirical status: **VALIDATED**
(`validation/empirical/simcov/battery_ldband.py`). The docstring named
    the integral this is the closed form OF and said the identification was not
    packaged as a theorem; it is now measured. Adaptive quadrature over nine
    cells, `rho` in {0.2, 0.5, 0.8} crossed with `kappa` in {0.1, 0.3, 0.6}: agreement to
    1.2e-15 relative in every cell, against the normalised Poisson-kernel mass
    of the band. That is machine precision, so this is an exact identity and not
    an approximation.

    The quadrature owes nothing to the closed form -- it integrates
    `(1 - rho^2) / (1 - 2 rho cos t + rho^2)` directly -- so this is not a
    generative self-test.

    Power: the prediction spans 0.14849 to 0.94872 across the design. -/
noncomputable def ldBandReconstructionShare (decay kappa : ℝ) : ℝ :=
  2 * Real.arctan (((1 + decay) / (1 - decay)) *
    Real.tan (Real.pi * kappa / 2)) / Real.pi

/-- **ldBandReconstructionShare at unit decay, named.** At `decay = 1` the band-edge ratio `(1 +
decay) / (1 - decay)` diverges: the reconstruction covers the whole band. The divisor is zero,
the ratio is junk-zero, and the share collapses to `2 * arctan 0` -- zero reconstruction at every
`kappa`, the opposite limit, and with the dependence on `kappa` erased along the way. Consumers
must exclude it by hypothesis. -/
theorem ldBandReconstructionShare_unit_decay_is_junk (kappa : ℝ) :
    ldBandReconstructionShare 1 kappa = 2 * Real.arctan 0 := by
  unfold ldBandReconstructionShare
  norm_num

/-- **Detection share of a pruned (low-frequency) band** on a stationary AR(1)
chromosome: the fraction of the total inverse-LD (whitened) weight that survives
pruning down to a fraction `kappa` of the directions.

Closed form `κ - 2ρ sin(πκ) / (π(1 + ρ²))`, obtained by integrating the
reciprocal symbol; the `1 + ρ²` is the numerator of
`Descent.ImitationRigidity.ldWhiteningGain`, the per-variant inverse-kernel
trace.  The integral evaluation itself is not packaged as a caller-supplied theorem.

Empirical status: **VALIDATED**
(`validation/empirical/simcov/battery_ldband.py`). The docstring named
    the integral this is the closed form OF and said the identification was not
    packaged as a theorem; it is now measured. Adaptive quadrature over nine
    cells, `rho` in {0.2, 0.5, 0.8} crossed with `kappa` in {0.1, 0.3, 0.6}: agreement to
    2.1e-15 relative in every cell, against the normalised mass of the
    reciprocal symbol `(1 - 2 rho cos t + rho^2) / (1 + rho^2)` on the same
    band, computed by quadrature.

    Power: the prediction spans 0.00404 to 0.48357, a factor of 120, and both
    `rho` and `kappa` move separately so the dependence on each is tested. -/
noncomputable def ldBandDetectionShare (decay kappa : ℝ) : ℝ :=
  kappa - 2 * decay * Real.sin (Real.pi * kappa) / (Real.pi * (1 + decay ^ 2))

/-- **The detection weight pruning throws away**, over and above the fraction of
directions it discards.  This is the quantity the frontier prices.

Empirical status: **VALIDATED**
(`validation/empirical/simcov/battery_ldband.py`). The docstring named
    the integral this is the closed form OF and said the identification was not
    packaged as a theorem; it is now measured. Adaptive quadrature over nine
    cells, `rho` in {0.2, 0.5, 0.8} crossed with `kappa` in {0.1, 0.3, 0.6}: agreement to
    7.2e-16 relative against `kappa` minus the quadrature detection share.

    Power: the prediction spans 0.03783 to 0.29535 across the design. -/
noncomputable def ldPruningDetectionDeficit (decay kappa : ℝ) : ℝ :=
  2 * decay * Real.sin (Real.pi * kappa) / (Real.pi * (1 + decay ^ 2))

/-- With a vanishing denominator Mathlib returns `0`, which is a value this quantity can also
take legitimately, so the branch is named rather than left to be inferred from the result. -/
theorem ldPruningDetectionDeficit_at_zero_denominator_is_junk (decay kappa : ℝ)
    (hzero : (Real.pi * (1 + decay ^ 2)) = 0) :
    ldPruningDetectionDeficit decay kappa = 0 := by
  unfold ldPruningDetectionDeficit
  rw [hzero, div_zero]


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
`Descent.ImitationRigidity.markovLDStep`: separation along the chromosome is
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

/-- **The panel class is inhabited**, so the six theorems taking an
`LDPanelRetention` are statements about something rather than about an empty
class. One marker of two retained is chosen deliberately over the degenerate
fills: it satisfies `0 < retainedMarkers` and `retainedMarkers < totalMarkers`
as well, which are the side conditions those theorems carry, so the witness
exercises the interval case rather than an endpoint where the fraction is `0`
or `1`. -/
def LDPanelRetention.halfRetained : LDPanelRetention where
  retainedMarkers := 1
  totalMarkers := 2
  retained_le_total := by norm_num
  totalMarkers_pos := by norm_num

theorem LDPanelRetention.nonempty : Nonempty LDPanelRetention :=
  ⟨LDPanelRetention.halfRetained⟩

/-- Fraction of a panel's markers that survive pruning.

    Empirical status: NOT AN EMPIRICAL CLAIM. Retained over total is the definition of a
    retained FRACTION; the two counts are fields of the structure, so the quotient is fixed
    once the panel is. What pruning actually retains on a real panel is empirical, but that
    is a claim about `retainedMarkers`, not about this division. -/
noncomputable def ldPanelRetentionFraction (panel : LDPanelRetention) : ℝ :=
  (panel.retainedMarkers : ℝ) / (panel.totalMarkers : ℝ)

/-- With a vanishing denominator Mathlib returns `0`, which is a value this quantity can also
take legitimately, so the branch is named rather than left to be inferred from the result. -/
theorem ldPanelRetentionFraction_at_zero_denominator_is_junk (panel : LDPanelRetention)
    (hzero : (panel.totalMarkers : ℝ) = 0) :
    ldPanelRetentionFraction panel = 0 := by
  unfold ldPanelRetentionFraction
  rw [hzero, div_zero]


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
    ld_retention_nonneg recomb Ne hr1 (le_of_lt hNe)
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

/-- **Detection share of a clumped panel**: the fraction of the whitened detection weight — the
inverse-LD-kernel trace whose per-variant limit is `ImitationRigidity.ldWhiteningGain` — that
survives clumping, as a function of the band kernel's decay and the marker counts.

`decay` is the AR(1) decay of the LD band, indexed by MARKER SEPARATION along the chromosome.
It is deliberately not computed here from a recombination rate and an effective size:
`ldRetentionPerGen` is a per-GENERATION retention, and feeding it here would make linkage
disequilibrium decay with physical distance at the rate it decays with time. The stationary law
relating separation to LD is Sved's, which this corpus carries as
`LDDecayTheory.ohtaKimuraSigmaDSq`; supplying `decay` from it is a modelling step and belongs at
the call site, where it can be named.

Empirical status: **FALSIFIED**
(`validation/empirical/simcov/battery_dgpcov.py`, group D;
`battery_dgpcov2.py`, group D2). The `kappa` of `ldBandDetectionShare` is a
fraction of DIRECTIONS -- a contiguous low-frequency band of the AR(1) symbol.
`ldPanelRetentionFraction` is a fraction of MARKERS. Feeding the second into the
first is a change of object, not a change of variable, and the two are not
close.

The instrument is exact linear algebra on the AR(1) kernel `Σᵢⱼ = ρ^|i-j|`, not
a simulation: the surviving whitened detection weight of a retained panel `S` is
`tr((Σ_SS)⁻¹) / tr(Σ⁻¹)`, computed at `n` = 512, 1024 and 2048 markers with
agreement to five digits between panel sizes, so nothing here is a finite-`n`
artefact.

  ρ    κ      this body   uniform thinning   random panel   contiguous panel
  0.5  1/2    0.24535     0.34005            0.41790        0.49980
  0.8  1/2    0.18945     0.26195            0.36031        0.49962
  0.5  1/3    0.11290     0.20648            0.25299
  0.8  1/3    0.06448     0.12520            0.19601
  0.5  1/4    0.06994     0.15120            0.18110
  0.8  1/4    0.03041     0.07699            0.13229

(the `κ = 1/2` row at `n` = 1024, the others at `n` = 2048; the two panel sizes
agree to four digits wherever both were run)

Every marker-subset reading exceeds the body, by 38 percent at `κ = 1/2` and by
a factor of 2.5 at `κ = 1/4`; the shortfall grows as pruning gets more
aggressive, which is the regime the frontier is about. The thinned column has a
closed form -- a panel keeping every `s`-th marker of an AR(1) chromosome is
itself AR(1) at `ρ^s`, so its share is `κ(1+ρ^{2s})(1-ρ²) / ((1-ρ^{2s})(1+ρ²))`
-- and it reproduces the measured column to four digits, which is the check that
the numbers are the kernel's and not the inverter's.

POSITIVE CONTROL, and it is what makes this a falsification of the composition
rather than of `ldBandDetectionShare`: the band operation the closed form is FOR
-- the normalised mass of the reciprocal symbol on `|t| ≤ πκ`, by quadrature --
agrees with the body to five decimals in every cell above. The formula is right
about directions. It is this definition that hands it markers.

There is also no repair by substituting a different `κ`. The three marker
columns disagree with EACH OTHER at the same `κ` and `ρ` (0.262, 0.356, 0.500 at
`ρ = 0.8`, `κ = 1/2`), so the retained detection weight of a pruned panel is not
a function of `(decay, κ)` at all: it depends on WHICH markers are kept. A
definition of this signature cannot express the quantity its name claims. The
`retainedMarkers / totalMarkers` reading is charitable at that -- the reading on
which the retained weight is the retained block of `Σ⁻¹` gives exactly `κ` and a
deficit of zero. -/
noncomputable def ldBlockDetectionShare (decay : ℝ)
    (panel : LDPanelRetention) : ℝ :=
  ldBandDetectionShare decay (ldPanelRetentionFraction panel)

/-- **Detection weight surrendered to clumping**, over and above the fraction of markers
discarded, as a function of the band kernel's decay.  This is the price the frontier puts on the
pruning convention.

Empirical status: **FALSIFIED**, for the reason recorded in full at
`ldBlockDetectionShare` above and on the same cells
(`validation/empirical/simcov/battery_dgpcov.py`, group D): the `kappa`
of `ldPruningDetectionDeficit` counts DIRECTIONS and `ldPanelRetentionFraction`
counts MARKERS. At `κ = 1/2` this body prices the loss at 0.25465 (`ρ = 0.5`)
and 0.31055 (`ρ = 0.8`); the measured deficit of a uniformly thinned panel is
0.15995 and 0.23805, of a random half-panel 0.08210 and 0.13969, and of a
contiguous half-panel 0.00020 and 0.00038. The frontier is therefore charging
between 1.6 and 800 times the price the kernel exacts, and the spread across those three panels
at one `(decay, κ)` is the same evidence that no function of this signature can
be the quantity. -/
noncomputable def ldBlockPruningDeficit (decay : ℝ)
    (panel : LDPanelRetention) : ℝ :=
  ldPruningDetectionDeficit decay (ldPanelRetentionFraction panel)

/-- **Tight-linkage floor on the detection share**, `κ - sin(πκ)/π`.  It carries no decay
parameter because it is the value the frontier saturates to as the band decay approaches one,
and `ldTightLinkage_le_ldBlockDetectionShare` shows it bounds the detection share at every
decay.

Empirical status: **VALIDATED**
    (`validation/empirical/simcov/battery_bulk4.py`,
    `test_tight_linkage_share`). It claims the `rho -> 1` limit of
    `ldBandDetectionShare`, and the limit is taken ON THE INTEGRAL rather than
    on the closed form: quadrature of the reciprocal symbol at `rho = 0.999999`
    agrees to 0.00 sems at every `kappa` in {0.1, 0.3, 0.6, 0.9}, predictions
    0.00164, 0.04248, 0.29727 and 0.80164.

    Power: the prediction spans 0.00164 to 0.80164, a factor of 490. -/
noncomputable def ldTightLinkageDetectionShare (panel : LDPanelRetention) : ℝ :=
  ldPanelRetentionFraction panel -
    Real.sin (Real.pi * ldPanelRetentionFraction panel) / Real.pi

/-- Accounting identity: what clumping keeps plus what it surrenders is the
fraction of markers it retained. -/
theorem ldBlockDetectionShare_add_deficit (decay : ℝ)
    (panel : LDPanelRetention) :
    ldBlockDetectionShare decay panel + ldBlockPruningDeficit decay panel =
      ldPanelRetentionFraction panel := by
  unfold ldBlockDetectionShare ldBlockPruningDeficit ldBandDetectionShare
    ldPruningDetectionDeficit
  ring

/-- **Clumping loses detection weight faster than it loses markers**, at every band decay. -/
theorem ldBlockDetectionShare_le_retention {decay : ℝ}
    {panel : LDPanelRetention}
    (hd0 : 0 ≤ decay)
    (h0 : 0 < panel.retainedMarkers) (h1 : panel.retainedMarkers < panel.totalMarkers) :
    ldBlockDetectionShare decay panel ≤ ldPanelRetentionFraction panel := by
  obtain ⟨hkpos, hklt⟩ := ldPanelRetentionFraction_mem panel h0 h1
  unfold ldBlockDetectionShare
  exact ldBandDetectionShare_le_retention hd0 (le_of_lt hkpos) (le_of_lt hklt)

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
are the same fact seen from two sides.  Both sides are functions of the band decay; what that
decay is in terms of a recombination rate and an effective size is a separate modelling step,
and it is not the per-generation retention. -/
theorem pruning_loses_detection_iff_whiteningGain_exceeds_one
    {decay : ℝ} {panel : LDPanelRetention}
    (hd0 : 0 ≤ decay) (hd1 : decay < 1)
    (h0 : 0 < panel.retainedMarkers) (h1 : panel.retainedMarkers < panel.totalMarkers) :
    1 < ldWhiteningGain decay ↔ 0 < ldBlockPruningDeficit decay panel := by
  obtain ⟨hkpos, hklt⟩ := ldPanelRetentionFraction_mem panel h0 h1
  unfold ldBlockPruningDeficit
  rw [ldWhiteningGain_one_lt_iff hd0 hd1,
    ldPruningDetectionDeficit_pos_iff hd0 hkpos hklt]

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

/-- **Tighter linkage, larger surrendered detection power**, stated on the band decay: a panel
whose LD band decays more slowly gives up strictly more detection weight to clumping. It runs in
the same direction as `ImitationRigidity.ldWhiteningGain_of_ldRetention_antitone` — the tighter
the block, the more there was to lose. What a recombination rate and an effective size imply for
`decay` is the modelling step named at `ldBlockDetectionShare`, and is not supplied here. -/
theorem ldBlockPruningDeficit_strictMono_in_decay
    {d₁ d₂ : ℝ} {panel : LDPanelRetention}
    (hd₁ : 0 ≤ d₁) (hd₂ : d₂ < 1) (hlt : d₁ < d₂)
    (h0 : 0 < panel.retainedMarkers) (h1 : panel.retainedMarkers < panel.totalMarkers) :
    ldBlockPruningDeficit d₁ panel < ldBlockPruningDeficit d₂ panel := by
  obtain ⟨hkpos, hklt⟩ := ldPanelRetentionFraction_mem panel h0 h1
  unfold ldBlockPruningDeficit
  exact ldPruningDetectionDeficit_strictMono hd₁ hd₂ hlt hkpos hklt

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

/-- **The tight-linkage floor.**  At every band decay, a clumped panel retaining
`retainedMarkers` of `totalMarkers` keeps at least `κ - sin(πκ)/π` of the detection weight, and
no more than `κ`.  The lower end is approached as linkage tightens, so on a dense panel the
detection share is pinned near a curve carrying no free parameters at all — which is what makes
the prediction cheap to test. -/
theorem ldTightLinkage_le_ldBlockDetectionShare {decay : ℝ}
    {panel : LDPanelRetention}
    (h0 : 0 < panel.retainedMarkers) (h1 : panel.retainedMarkers < panel.totalMarkers) :
    ldTightLinkageDetectionShare panel ≤ ldBlockDetectionShare decay panel := by
  obtain ⟨hkpos, hklt⟩ := ldPanelRetentionFraction_mem panel h0 h1
  have hbound := ldPruningDetectionDeficit_le_sin_div_pi
    (decay := decay)
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

The kernel is the AR(1) LD band at decay `decay`, indexed by marker separation. What that decay
is in terms of a recombination rate and an effective size is a modelling step named at
`ldBlockDetectionShare`; the per-generation retention is not it.

Scope: relaxed projection-type reductions.  This is not a statement about
arbitrary measurable summaries of the genotypes, and no joint data-processing
inequality is available that would make it one. -/
theorem clumping_minimizes_detection_on_ld_kernel
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (angle : ι → ℝ) (decay cutAngle : ℝ) (S : Finset ι) (M : ι → ℝ)
    (hd0 : 0 ≤ decay) (hdabs : |decay| < 1)
    (hM : IsRankAllocation (S.card : ℝ) M)
    (hin : ∀ i ∈ S, Real.cos cutAngle ≤ Real.cos (angle i))
    (hout : ∀ i ∉ S, Real.cos (angle i) ≤ Real.cos cutAngle) :
    detectionEfficiency
        (fun i ↦ ldKernelSymbol decay (angle i))
        (pruneAllocation S) ≤
      detectionEfficiency
        (fun i ↦ ldKernelSymbol decay (angle i)) M := by
  have habs : |decay| < 1 := hdabs
  have hp0 : 0 ≤ decay := hd0
  refine topVariance_minimizes_detection
    (fun i ↦ ldKernelSymbol decay (angle i)) M S
    (ldKernelSymbol decay cutAngle)
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
    (angle : ι → ℝ) (decay cutAngle : ℝ) (S : Finset ι) (M : ι → ℝ)
    (hd0 : 0 ≤ decay) (hdabs : |decay| < 1)
    (hM : IsRankAllocation (S.card : ℝ) M)
    (hin : ∀ i ∈ S, Real.cos cutAngle ≤ Real.cos (angle i))
    (hout : ∀ i ∉ S, Real.cos (angle i) ≤ Real.cos cutAngle) :
    reconstructionEfficiency
        (fun i ↦ ldKernelSymbol decay (angle i)) M ≤
      reconstructionEfficiency
        (fun i ↦ ldKernelSymbol decay (angle i))
        (pruneAllocation S) := by
  have habs : |decay| < 1 := hdabs
  have hp0 : 0 ≤ decay := hd0
  refine topVariance_maximizes_reconstruction
    (fun i ↦ ldKernelSymbol decay (angle i)) M S
    (ldKernelSymbol decay cutAngle)
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
noncomputable def targetCorrectionCurvature (weight : ι → ℝ) (B : ι → Matrix J J ℝ)
    (beta : J → ℝ) : ι → ℝ :=
  fun i ↦ weight i * coefficientEnergy (B i) beta

/-- **The curvature is the energy scaled by the target's weight**, evaluated where the
family is not degenerate.

Written because the docstring above says an identifier grep is not enough to justify
removing this definition: what makes it load-bearing is a statement that USES it, and a
statement that only quantified over abstract arguments would be satisfied by the constant
zero. At weight one the curvature IS the coefficient energy of that target's operator,
which is the claim the name makes. -/
theorem targetCorrectionCurvature_at_unit_weight (B : ι → Matrix J J ℝ) (beta : J → ℝ)
    (i : ι) :
    targetCorrectionCurvature (fun _ ↦ 1) B beta i = coefficientEnergy (B i) beta := by
  unfold targetCorrectionCurvature
  ring

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

/-- **Each target's own optimum is the shared optimum for that target's operator.**
The definition unfolded, stated so the indexed family is tied to the scalar it indexes
rather than merely resembling it. -/
theorem targetCorrectionOptimum_apply (B : ι → Matrix J J ℝ) (beta theta : J → ℝ)
    (i : ι) :
    targetCorrectionOptimum B beta theta i = sharedCorrectionOptimum (B i) beta theta :=
  rfl

/-- The curvature-weighted mean of the per-target optimal corrections: the
shared correction that a weighted-least-squares compromise selects.

Empirical status: UNTESTED. -/
noncomputable def sharedCorrectionConsensus (curvature optimum : ι → ℝ) : ℝ :=
  (∑ i, curvature i * optimum i) / ∑ i, curvature i

/-- **sharedCorrectionConsensus over an empty index, named.** The consensus is a
curvature-weighted mean of the per-task optima, and with no tasks both sums vanish. Lean returns
`0`, which is a perfectly ordinary correction value -- so a consensus over an empty set of tasks
is reported as a definite recommendation rather than as absent. Consumers must require a nonempty
index. -/
theorem sharedCorrectionConsensus_no_curvature_is_junk (curvature optimum : Fin 0 → ℝ) :
    sharedCorrectionConsensus curvature optimum = 0 := by
  unfold sharedCorrectionConsensus
  simp

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

-- `HasTaskIndependentSpectralPortabilityScalar` is defined in `Descent.Spectral.SpectralDegradation`,
-- beside the two-band witness it quantifies over.  It was written out again here, `let`
-- bindings and all, which is how the biological consumer and the spectral witness came to
-- carry two copies of one predicate.

/-- **Metric-specific portability has no universal scalar degradation order.**  At every
nonzero shift the low-band and high-band tasks rank the same two population shifts in
opposite orders. -/
theorem not_hasTaskIndependentSpectralPortabilityScalar (a : ℝ) (ha : a ≠ 0) :
    ¬ HasTaskIndependentSpectralPortabilityScalar a := by
  unfold HasTaskIndependentSpectralPortabilityScalar
  exact twoBand_no_common_monotone_scalar a ha

end Descent
