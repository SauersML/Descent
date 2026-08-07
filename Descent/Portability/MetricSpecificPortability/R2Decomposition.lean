/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Descent.Portability.ClinicalUtilityFairness
import Descent.Spectral.ProjectionShiftBounds
import Descent.Blindness.ImitationRigidity
import Descent.Spectral.FoldedSpectrum
-- `BinaryPopulation`, `populationAUC` and `populationAUC_strictMono_invariant` are named
-- below, so the module declaring them is imported directly rather than reached along a
-- path that runs through some other chapter's head.
import Descent.Portability.PopulationAUC

assert_below Descent.Decision Descent.Program

namespace Descent.Portability

open MeasureTheory

/-!
# `MetricSpecificPortability.R2Decomposition`

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
  have h_auc_eq : populationAUC pop scoreTarget = populationAUC pop scoreSource
    := by
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
  unfold brierFromR2 PopGen.TransportedMetrics.calibratedBrier
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
  unfold brierFromR2 PopGen.TransportedMetrics.calibratedBrier
  have h1 : 0 < 1 - r2_source := by linarith
  have h2 : 0 < 1 - r2_target := by linarith
  -- (1 - r2_target) ≥ (1 - r2_source) and π_t(1-π_t) ≥ π_s(1-π_s)
  nlinarith [mul_nonneg (le_of_lt h_πs) (by linarith : 0 ≤ 1 - π_source)]

end R2VsAUC

end Descent.Portability
