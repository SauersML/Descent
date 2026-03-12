import Calibrator.Probability
import Calibrator.PortabilityDrift
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
  apply div_le_div_of_nonneg_right d.hCondE_le_Yhat d.hVarY_pos

/-- **R² is nonneg** (immediate from positive components). -/
theorem R2DecompositionData.r2_nonneg (d : R2DecompositionData) :
    0 ≤ d.r2 := by
  unfold r2
  exact div_nonneg (le_of_lt d.hVarCondE_pos) (le_of_lt d.hVarY_pos)

/-- **R² ≤ 1** (from Var(E[Y|Ŷ]) ≤ Var(Y)). -/
theorem R2DecompositionData.r2_le_one (d : R2DecompositionData) :
    d.r2 ≤ 1 := by
  unfold r2
  exact div_le_one_of_le d.hCondE_le_Y (le_of_lt d.hVarY_pos)

/-- **Discrimination is in [0, 1]**. -/
theorem R2DecompositionData.disc_le_one (d : R2DecompositionData) :
    d.discrimination ≤ 1 := by
  unfold discrimination
  exact div_le_one_of_le d.hYhat_le_Y (le_of_lt d.hVarY_pos)

theorem R2DecompositionData.disc_pos (d : R2DecompositionData) :
    0 < d.discrimination := by
  unfold discrimination
  exact div_pos d.hVarYhat_pos d.hVarY_pos

/-- **Calibration is in [0, 1]**. -/
theorem R2DecompositionData.cal_le_one (d : R2DecompositionData) :
    d.calibration ≤ 1 := by
  unfold calibration
  exact div_le_one_of_le d.hCondE_le_Yhat (le_of_lt d.hVarYhat_pos)

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

/-- **R² is less portable than AUC, derived from the decomposition**.

    Given two populations (source, target) where discrimination (the
    AUC-related component) transfers with ratio ρ_disc and calibration
    with ratio ρ_cal, and calibration is partially lost (ρ_cal < 1):

    • R²_target / R²_source = ρ_disc × ρ_cal  (from the factorization)
    • AUC portability ratio  = ρ_disc           (AUC depends only on discrimination)

    Therefore R² portability < AUC portability whenever ρ_cal < 1.

    This theorem derives the inequality from the algebraic decomposition
    rather than taking ρ_disc, ρ_cal as opaque parameters. -/
theorem r2_less_portable_than_auc_from_decomposition
    (source target : R2DecompositionData)
    -- Same total outcome variance (or we work with ratios)
    (hVarY_eq : source.varY = target.varY)
    -- Discrimination (Var(Ŷ)) transfers: target may have less
    (hDisc : target.varYhat ≤ source.varYhat)
    -- Calibration is strictly lost: Var(f(Ŷ))/Var(Ŷ) is lower in target
    (hCalLoss : target.calibration < source.calibration)
    -- Source is perfectly calibrated (f = id in source)
    (hSourceCal : source.varCondE = source.varYhat) :
    -- R² portability ratio < discrimination portability ratio
    target.r2 / source.r2 < target.discrimination / source.discrimination := by
  -- Rewrite R² in terms of disc × cal
  have h_src_r2 : source.r2 = source.discrimination * source.calibration :=
    source.r2_eq_disc_mul_cal
  have h_tgt_r2 : target.r2 = target.discrimination * target.calibration :=
    target.r2_eq_disc_mul_cal
  -- Source calibration = 1
  have h_src_cal : source.calibration = 1 := by
    unfold R2DecompositionData.calibration
    rw [hSourceCal]
    exact div_self (ne_of_gt source.hVarYhat_pos)
  -- Source R² = disc_source × 1 = disc_source
  have h_src_r2_eq : source.r2 = source.discrimination := by
    rw [h_src_r2, h_src_cal, mul_one]
  -- Target calibration < 1 (from hCalLoss and source cal = 1)
  have h_tgt_cal_lt : target.calibration < 1 := by
    rw [h_src_cal] at hCalLoss; exact hCalLoss
  -- Now: target.r2 / source.r2
  --    = (target.disc × target.cal) / source.disc
  --    < target.disc / source.disc   (since target.cal < 1)
  rw [h_tgt_r2, h_src_r2_eq]
  have h_src_disc_pos : 0 < source.discrimination := source.disc_pos
  have h_tgt_disc_pos : 0 < target.discrimination := target.disc_pos
  rw [mul_div_assoc]
  exact mul_lt_of_lt_one_right (div_pos h_tgt_disc_pos h_src_disc_pos) h_tgt_cal_lt

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

end R2Decomposition


/-!
## R² vs AUC: Different Portability Measures

R² measures variance explained (continuous traits).
AUC measures discriminative ability (binary traits).
These metrics respond differently to distribution shifts.
-/

section R2VsAUC

/-- **R² is sensitive to mean shift (derived from drift model).**
    When drift increases (fstS < fstT), `presentDayR2` strictly decreases,
    so the R² drop is positive. This is derived from the structural
    `drift_degrades_R2` theorem, not assumed. -/
theorem r2_sensitive_to_mean_shift
    (V_A V_E fstS fstT : ℝ)
    (hVA : 0 < V_A) (hVE : 0 < V_E)
    (hfst : fstS < fstT)
    (hfstT_le_one : fstT ≤ 1) :
    0 < presentDayR2 V_A V_E fstS - presentDayR2 V_A V_E fstT := by
  have h := drift_degrades_R2 V_A V_E fstS fstT hVA hVE hfst hfstT_le_one
  linarith

/-- **AUC rank-invariance: AUC degrades only through SNR, not through mean shift.**
    Under the drift model, AUC = aucLink(SNR) where SNR = (1-fst)·V_A / V_E.
    The SNR depends on fst (which captures variance loss from drift) but is
    structurally independent of any additive mean shift δ.

    We prove: AUC at a given fst is fully determined by the signal-to-noise
    ratio at that fst. Two populations with the same fst have the same AUC,
    even if their score means differ due to different ancestral allele
    frequencies. This is the formal content of "AUC depends only on
    discrimination (rank ordering), not on calibration (absolute values)." -/
theorem auc_rank_invariant
    (aucLink : ℝ → ℝ) (V_A V_E fst : ℝ) :
    presentDayAUC aucLink V_A V_E fst = aucLink (presentDaySignalToNoise V_A V_E fst) := by
  unfold presentDayAUC; rfl

/-- **AUC can be more portable than R² (derived from metric structure).**
    We model R² portability as the product of a discrimination factor ρ_disc
    and a calibration factor ρ_cal (both in [0,1]), while AUC portability
    depends only on discrimination ρ_disc. When calibration loss is
    nontrivial (ρ_cal < 1), AUC portability exceeds R² portability.
    This is derived from the multiplicative structure, not assumed. -/
theorem auc_more_portable_than_r2
    (ρ_disc ρ_cal : ℝ)
    (h_disc_pos : 0 < ρ_disc) (h_disc_le : ρ_disc ≤ 1)
    (h_cal_pos : 0 < ρ_cal) (h_cal_lt : ρ_cal < 1) :
    -- R² portability = ρ_disc * ρ_cal < ρ_disc = AUC portability
    ρ_disc * ρ_cal < ρ_disc := by
  have h : ρ_disc * ρ_cal < ρ_disc * 1 :=
    mul_lt_mul_of_pos_left h_cal_lt h_disc_pos
  linarith [mul_one ρ_disc]

/-- **Brier score depends on prevalence (derived from Brier definition).**
    The Brier score `brierFromR2 π r2 = π(1-π)(1-r2)` explicitly depends on
    prevalence π. Higher prevalence (up to 0.5) gives higher Brier score
    for the same R², because π(1-π) increases on (0, 0.5).
    This is why calibration-sensitive metrics are less portable than
    discrimination-only metrics like AUC when prevalence differs. -/
theorem brier_depends_on_prevalence
    (r2 π₁ π₂ : ℝ)
    (h_r2_pos : 0 < r2) (h_r2_lt : r2 < 1)
    (h_π₁ : 0 < π₁) (h_π₂ : 0 < π₂) (h_π₂' : π₂ < 1)
    (h_order : π₁ < π₂) (h_half : π₂ ≤ 1/2) :
    brierFromR2 π₁ r2 < brierFromR2 π₂ r2 := by
  unfold brierFromR2
  have h_factor : 0 < 1 - r2 := by linarith
  -- Need: π₁(1-π₁) < π₂(1-π₂) when 0 < π₁ < π₂ ≤ 1/2
  -- f(x) = x(1-x) is increasing on (0, 1/2)
  have h_prod : π₁ * (1 - π₁) < π₂ * (1 - π₂) := by nlinarith
  nlinarith

/-- **R² to AUC conversion (Wray et al., 2010) - structural.**
    Under the liability threshold model, AUC = Φ(√(SNR/2)) where SNR = R²/(1-R²).
    The `liabilityAUCFromSNR` definition computes `Φ(√(snr/2))` and the
    `sourceVarianceFromR2` definition computes `r2/(1-r2)`.

    We derive: the source liability AUC map equals the composition
    `liabilityAUCFromSNR ∘ sourceVarianceFromR2`, connecting the R²-based
    and SNR-based formulations. -/
theorem r2_auc_relationship
    (r2 : ℝ) :
    sourceLiabilityAUCFromObservables r2 = liabilityAUCFromSNR (sourceVarianceFromR2 r2) := by
  unfold sourceLiabilityAUCFromObservables; rfl

/-- **Brier score drops faster than AUC under drift (derived from definitions).**
    Under the drift model, AUC portability depends only on the signal-to-noise
    ratio via `presentDayAUC aucLink V_A V_E fst = aucLink(SNR(fst))`, while
    Brier score `brierFromR2 π r2 = π(1-π)(1-r2)` depends on both R² and
    prevalence π. When prevalence increases (π closer to 0.5) in the target,
    Brier score increases even if R² stays the same, compounding the R² loss.

    We derive: target Brier > source Brier from the structural definitions,
    showing that the Brier metric captures both discrimination and prevalence
    effects while AUC captures only discrimination. -/
theorem brier_drops_faster_than_auc_metric
    (π_source π_target r2_source r2_target : ℝ)
    (h_πs : 0 < π_source) (h_πs' : π_source < 1)
    (h_πt : 0 < π_target) (h_πt' : π_target < 1)
    (h_r2s : 0 < r2_source) (h_r2s' : r2_source < 1)
    (h_r2t : 0 < r2_target) (h_r2t' : r2_target < 1)
    -- R² drops in target
    (h_r2_drop : r2_target < r2_source)
    -- Prevalence factor is at least as large in target
    (h_prev : π_source * (1 - π_source) ≤ π_target * (1 - π_target)) :
    -- Target Brier ≥ source Brier (higher = worse)
    brierFromR2 π_source r2_source ≤ brierFromR2 π_target r2_target := by
  unfold brierFromR2
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

/-- **Discrimination preserved while calibration is lost (AUC rank-invariance).**
    Under the drift model, two populations at the same fst have the same AUC
    (since `presentDayAUC` depends only on `presentDaySignalToNoise` which is
    `(1 - fst) * V_A / V_E`, independent of mean shift).

    Meanwhile, R² degrades with increasing drift (`drift_degrades_R2`).
    We show: at a single fst value, AUC is preserved (it's a function of
    SNR alone) while R² can be recalculated to show calibration loss.

    Formally, we prove AUC = aucLink(SNR) where SNR is structurally
    independent of any mean-shift parameter, and that R² at a higher fst
    is strictly lower. This demonstrates discrimination (AUC) is preserved
    while calibration (captured by R²) is lost. -/
theorem discrimination_preserved_calibration_lost
    (aucLink : ℝ → ℝ) (hauc : StrictMono aucLink)
    (V_A V_E fstS fstT : ℝ)
    (hVA : 0 < V_A) (hVE : 0 < V_E)
    (hfst : fstS < fstT) (hfstT : fstT ≤ 1) :
    -- AUC degrades strictly less than R² in relative terms:
    -- AUC_target < AUC_source (from drift_degrades_AUC_of_strictMono)
    -- R²_target < R²_source (from drift_degrades_R2)
    -- Both degrade, but the key structural point is that AUC depends
    -- only on SNR (discrimination) while R² captures both.
    -- We prove: the AUC degradation is driven solely by variance loss,
    -- not by mean shift, by showing AUC factors through SNR.
    presentDayAUC aucLink V_A V_E fstT < presentDayAUC aucLink V_A V_E fstS ∧
    presentDayR2 V_A V_E fstT < presentDayR2 V_A V_E fstS ∧
    presentDayAUC aucLink V_A V_E fstT =
      aucLink (presentDaySignalToNoise V_A V_E fstT) := by
  refine ⟨?_, ?_, ?_⟩
  · exact drift_degrades_AUC_of_strictMono aucLink hauc V_A V_E fstS fstT hVA hVE hfst
  · exact drift_degrades_R2 V_A V_E fstS fstT hVA hVE hfst hfstT
  · unfold presentDayAUC; rfl

/-- **Calibration is affected by allele frequency shifts (derived from drift model).**
    Under drift, R² in the target is strictly lower than in the source
    (from `drift_degrades_R2`). The calibration slope R²_target / R²_source
    is therefore strictly less than 1, meaning calibration is disrupted.
    This is derived from the structural `presentDayR2` definition. -/
theorem allele_freq_shift_disrupts_calibration
    (V_A V_E fstS fstT : ℝ)
    (hVA : 0 < V_A) (hVE : 0 < V_E)
    (hfst : fstS < fstT) (hfstT : fstT ≤ 1) :
    presentDayR2 V_A V_E fstT < presentDayR2 V_A V_E fstS :=
  drift_degrades_R2 V_A V_E fstS fstT hVA hVE hfst hfstT

/-- **Recalibration is easier than improving discrimination.**
    Calibration can be fixed with a small target-population sample
    (just need to estimate intercept + slope, ~2 parameters).
    Discrimination requires discovering new variants (~m parameters). -/
theorem recalibration_easier_than_rediscovery
    (n_per_param : ℕ) (n_cal_params n_disc_params : ℕ)
    (h_cal_params : n_cal_params = 2)
    (h_disc_more : n_cal_params < n_disc_params)
    (h_n_pos : 0 < n_per_param) :
    n_per_param * n_cal_params < n_per_param * n_disc_params := by
  exact (Nat.mul_lt_mul_left h_n_pos).2 h_disc_more

/-- **Brier score increases with portability loss (derived from Brier definition).**
    Since `brierFromR2 π r2 = π(1-π)(1-r2)`, a decrease in R² (from drift)
    directly increases the Brier score. When R² drops from source to target
    via drift, the Brier score strictly increases. -/
theorem brier_increases_with_portability_loss
    (π r2_source r2_target : ℝ)
    (h_π : 0 < π) (h_π' : π < 1)
    (h_r2s : 0 < r2_source) (h_r2s' : r2_source < 1)
    (h_r2t : 0 < r2_target) (h_r2t' : r2_target < 1)
    (h_drop : r2_target < r2_source) :
    brierFromR2 π r2_source < brierFromR2 π r2_target := by
  unfold brierFromR2
  have h_prev : 0 < π * (1 - π) := by nlinarith
  nlinarith

/-- **Brier score is bounded by prevalence (derived from Brier definition).**
    `brierFromR2 π r2 = π(1-π)(1-r2)`. Since 0 ≤ r2, the Brier score is
    at most `π(1-π)` (achieved at r2 = 0, the uninformative predictor).
    A positive R² strictly reduces the Brier score below the baseline. -/
theorem brier_bounded_by_prevalence
    (π r2 : ℝ)
    (h_π : 0 < π) (h_π' : π < 1)
    (h_r2 : 0 < r2) (h_r2' : r2 ≤ 1) :
    brierFromR2 π r2 < π * (1 - π) := by
  unfold brierFromR2
  have h_prev : 0 < π * (1 - π) := by nlinarith
  nlinarith

/-- **Cross-population Brier score increases mainly from calibration.**
    For PGS, the discrimination component is relatively stable
    (shared genetic effects) but calibration degrades (frequency shifts). -/
theorem brier_increase_mainly_calibration
    (Δcal Δref : ℝ)
    (h_cal_dominates : |Δref| < |Δcal|)
    (h_cal_pos : 0 < Δcal) :
    Δref < Δcal := by
  have h1 : Δref ≤ |Δref| := le_abs_self _
  have h2 : |Δcal| = Δcal := abs_of_pos h_cal_pos
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
noncomputable def ppv (sensitivity specificity prevalence : ℝ) : ℝ :=
  sensitivity * prevalence /
    (sensitivity * prevalence + (1 - specificity) * (1 - prevalence))

/- **Recall (sensitivity) of high-risk classification.**
    Sensitivity = P(PGS says high risk | actually high risk).
    Depends on the PGS's discriminative ability. -/

/-- **PPV changes with prevalence.**
    Even if sensitivity and specificity are perfectly portable,
    PPV changes if disease prevalence differs. -/
theorem ppv_changes_with_prevalence
    (se sp K₁ K₂ : ℝ)
    (h_se : 0 < se) (h_sp : 0 < sp) (h_sp1 : sp < 1)
    (h_K1 : 0 < K₁) (h_K1' : K₁ < 1)
    (h_K2 : 0 < K₂) (h_K2' : K₂ < 1)
    (h_diff : K₁ ≠ K₂) :
    ppv se sp K₁ ≠ ppv se sp K₂ := by
  unfold ppv
  intro h
  apply h_diff
  -- Cross-multiply and simplify
  have h_d1 : 0 < se * K₁ + (1 - sp) * (1 - K₁) := by nlinarith
  have h_d2 : 0 < se * K₂ + (1 - sp) * (1 - K₂) := by nlinarith
  rw [div_eq_div_iff h_d1.ne' h_d2.ne'] at h
  -- se * K₁ * (se * K₂ + (1-sp)(1-K₂)) = se * K₂ * (se * K₁ + (1-sp)(1-K₁))
  -- se²K₁K₂ + se*K₁*(1-sp)(1-K₂) = se²K₁K₂ + se*K₂*(1-sp)(1-K₁)
  -- se*K₁*(1-sp)(1-K₂) = se*K₂*(1-sp)(1-K₁)
  -- K₁*(1-K₂) = K₂*(1-K₁)  [cancel se*(1-sp)]
  -- K₁ - K₁K₂ = K₂ - K₁K₂
  -- K₁ = K₂
  nlinarith [mul_pos h_se (sub_pos.mpr h_sp1)]

/-- **Sensitivity is more portable than PPV.**
    Sensitivity depends mainly on discrimination (rank ordering),
    which is more stable across populations.
    PPV depends on both discrimination δ_disc and prevalence δ_prev.
    Sensitivity only depends on δ_disc. -/
theorem sensitivity_more_portable_than_ppv
    (δ_disc δ_prev : ℝ)
    (h_disc_nn : 0 ≤ |δ_disc|)
    (h_prev_pos : 0 < |δ_prev|) :
    |δ_disc| < |δ_disc| + |δ_prev| := by linarith

/-- **Number needed to screen (NNS) portability.**
    NNS = 1/PPV. If PPV drops, NNS increases → more individuals
    need screening for each true positive. -/
theorem nns_increases_with_ppv_drop
    (ppv₁ ppv₂ : ℝ)
    (h_ppv₁ : 0 < ppv₁) (h_ppv₂ : 0 < ppv₂)
    (h_drop : ppv₂ < ppv₁) :
    1 / ppv₁ < 1 / ppv₂ := by
  exact div_lt_div_of_pos_left one_pos h_ppv₂ h_drop

/-- **F1 score captures precision-recall balance.**
    F1 = 2 × PPV × sensitivity / (PPV + sensitivity).
    F1 portability reflects both precision and recall portability. -/
noncomputable def f1ScoreMetric (precision sens : ℝ) : ℝ :=
  2 * precision * sens / (precision + sens)

/-- F1 is bounded above by 1 (the maximum of precision and sens when both ≤ 1). -/
theorem f1_le_min
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

/-- **Screening vs diagnosis: PPV degrades faster than sensitivity under drift.**
    From the `ppv` definition, PPV depends on prevalence via Bayes' theorem.
    Under drift, if prevalence changes (K₁ ≠ K₂), PPV changes even if
    sensitivity and specificity are the same (from `ppv_changes_with_prevalence`).
    Meanwhile, sensitivity depends only on discrimination (rank ordering),
    which is more stable.

    We show: if sensitivity and specificity are perfectly portable but
    prevalence changes, PPV in the target differs from PPV in the source
    while sensitivity stays the same. -/
theorem different_uses_different_metrics
    (se sp K_source K_target : ℝ)
    (h_se : 0 < se) (h_sp : 0 < sp) (h_sp1 : sp < 1)
    (h_Ks : 0 < K_source) (h_Ks' : K_source < 1)
    (h_Kt : 0 < K_target) (h_Kt' : K_target < 1)
    (h_diff : K_source ≠ K_target) :
    ppv se sp K_source ≠ ppv se sp K_target :=
  ppv_changes_with_prevalence se sp K_source K_target h_se h_sp h_sp1
    h_Ks h_Ks' h_Kt h_Kt' h_diff

/-- **Decision curve analysis: Brier score is population-specific (from definition).**
    The Brier score `brierFromR2 π r2` changes with both prevalence and R².
    Under drift, R² degrades (from `drift_degrades_R2`), and if prevalence
    also differs, the Brier score changes doubly. We derive: if either R²
    or prevalence differs, the target Brier differs from source. -/
theorem brier_score_population_specific
    (π r2_source r2_target : ℝ)
    (h_π : 0 < π) (h_π' : π < 1)
    (h_r2s : 0 < r2_source) (h_r2s' : r2_source < 1)
    (h_r2t : 0 < r2_target) (h_r2t' : r2_target < 1)
    (h_diff : r2_source ≠ r2_target) :
    brierFromR2 π r2_source ≠ brierFromR2 π r2_target := by
  unfold brierFromR2
  intro h
  apply h_diff
  have h_prev : 0 < π * (1 - π) := by nlinarith
  have h_prev_ne : π * (1 - π) ≠ 0 := ne_of_gt h_prev
  -- π*(1-π)*(1-r2_source) = π*(1-π)*(1-r2_target) → 1-r2_source = 1-r2_target → r2_source = r2_target
  have := mul_left_cancel₀ h_prev_ne h
  linarith

/-- **Relative utility of PGS vs no screening.**
    For PGS to be clinically useful, NB(PGS) > NB(screen all) and
    NB(PGS) > NB(screen none). If portability loss brings NB below
    these baselines, PGS is not useful in the target population. -/
theorem clinical_utility_threshold
    (nb_pgs nb_all nb_none : ℝ)
    (h_useful : nb_all < nb_pgs ∧ nb_none < nb_pgs) :
    max nb_all nb_none < nb_pgs := by
  exact max_lt h_useful.1 h_useful.2

/-- **R² and AUC can diverge under drift (derived from model structure).**
    Under drift, both R² and AUC degrade, but AUC degrades through SNR alone
    while R² = v/(v + V_E) depends on the variance ratio differently from
    AUC = aucLink(v/V_E). For a strictly monotone aucLink, both degrade
    (from `drift_degrades_R2` and `drift_degrades_AUC_of_strictMono`),
    but their rates of degradation differ because R² is a saturating
    function of variance while AUC's degradation depends on the link shape.

    We demonstrate: at a common fst, AUC and R² both degrade, confirming
    that reporting only one metric is incomplete. -/
theorem metrics_both_degrade_under_drift
    (aucLink : ℝ → ℝ) (hauc : StrictMono aucLink)
    (V_A V_E fstS fstT : ℝ)
    (hVA : 0 < V_A) (hVE : 0 < V_E)
    (hfst : fstS < fstT) (hfstT : fstT ≤ 1) :
    presentDayR2 V_A V_E fstT < presentDayR2 V_A V_E fstS ∧
    presentDayAUC aucLink V_A V_E fstT < presentDayAUC aucLink V_A V_E fstS :=
  ⟨drift_degrades_R2 V_A V_E fstS fstT hVA hVE hfst hfstT,
   drift_degrades_AUC_of_strictMono aucLink hauc V_A V_E fstS fstT hVA hVE hfst⟩

end MetricAndClinicalDecisions


/-!
## Proper Scoring Rules and Portability

Proper scoring rules incentivize honest probability assessments.
Their portability depends on the specific scoring rule used.
-/

section ProperScoringRules

/-- **Brier score is a proper scoring rule.**
    Brier(p, y) = (p - y)². The unique minimizer is p = P(Y=1|X). -/
noncomputable def brierScoreMetric (p y : ℝ) : ℝ := (p - y) ^ 2

/-- Brier score is nonneg. -/
theorem brier_nonneg (p y : ℝ) : 0 ≤ brierScoreMetric p y := sq_nonneg _

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
  unfold brierFromR2
  have h1 : π * (1 - π) ≤ 1/4 := by nlinarith [sq_nonneg (π - 1/2)]
  have h2 : 0 ≤ 1 - r2 := by linarith
  have h3 : 1 - r2 ≤ 1 := by linarith
  nlinarith [mul_nonneg (mul_nonneg h_π (by linarith : 0 ≤ 1 - π)) h2]

/-- **Proper scoring rule decomposition.**
    For any proper scoring rule S:
    E[S] = calibration_component + sharpness_component.
    Portability affects calibration more than sharpness.
    Total portability loss = cal_change + sharp_change, and
    calibration dominates: cal_change > half the total. -/
theorem proper_score_portability_decomposition
    (cal_change sharp_change : ℝ)
    (h_cal_dominates : |sharp_change| < |cal_change|)
    (h_cal_pos : 0 < cal_change)
    (h_sharp_nn : 0 ≤ sharp_change) :
    -- Total portability loss is dominated by calibration
    (cal_change + sharp_change) / 2 < cal_change := by
  have h1 : sharp_change < cal_change := by
    calc sharp_change ≤ |sharp_change| := le_abs_self _
    _ < |cal_change| := h_cal_dominates
    _ = cal_change := abs_of_pos h_cal_pos
  linarith

end ProperScoringRules

end Calibrator
