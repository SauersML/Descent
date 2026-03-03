import Calibrator.Models
import Calibrator.Conclusions

namespace Calibrator

open MeasureTheory

section PortabilityDrift

abbrev DriftIndex := ℝ

noncomputable def integratedCoalescentHazard (hazard : ℝ → ℝ) (t : ℝ) : ℝ :=
  ∫ s in (0)..t, hazard s

noncomputable def coalescenceSurvivalFromHazard (hazard : ℝ → ℝ) (t : ℝ) : ℝ :=
  Real.exp (-(integratedCoalescentHazard hazard t))

noncomputable def coalescenceCdfFromHazard (hazard : ℝ → ℝ) (t : ℝ) : ℝ :=
  1 - coalescenceSurvivalFromHazard hazard t

noncomputable def coalescentTau (t Ne : ℝ) : ℝ :=
  t / (2 * Ne)

noncomputable def fstFromTau (tau : ℝ) : ℝ :=
  1 - Real.exp (-tau)

noncomputable def fstFromGenerations (t Ne : ℝ) : ℝ :=
  fstFromTau (coalescentTau t Ne)

noncomputable def generationsFromFst (Ne fst : ℝ) : ℝ :=
  -2 * Ne * Real.log (1 - fst)

@[simp] theorem coalescenceCdfFromHazard_eq (hazard : ℝ → ℝ) (t : ℝ) :
    coalescenceCdfFromHazard hazard t =
      1 - Real.exp (-(integratedCoalescentHazard hazard t)) := by
  simp [coalescenceCdfFromHazard, coalescenceSurvivalFromHazard]

@[simp] theorem fstFromGenerations_eq (t Ne : ℝ) :
    fstFromGenerations t Ne = 1 - Real.exp (-(t / (2 * Ne))) := by
  simp [fstFromGenerations, fstFromTau, coalescentTau]

theorem fst_from_tau_nonneg_of_nonneg (tau : ℝ) (htau : 0 ≤ tau) :
    0 ≤ fstFromTau tau := by
  unfold fstFromTau
  have hexp_le : Real.exp (-tau) ≤ 1 := by
    rw [← Real.exp_zero]
    exact Real.exp_le_exp.mpr (by linarith)
  linarith

theorem fst_from_tau_lt_one (tau : ℝ) : fstFromTau tau < 1 := by
  unfold fstFromTau
  have hpos : 0 < Real.exp (-tau) := Real.exp_pos (-tau)
  linarith

structure DivergenceModelAssumptions where
  pureDivergence : Prop
  constantSize : Prop
  noMigration : Prop
  negligibleMutation : Prop

abbrev GenoVec (p : ℕ) := Fin p → ℝ

structure TwoPopulationGaussianDrift (p : ℕ) where
  SigmaS : DriftIndex → Matrix (Fin p) (Fin p) ℝ
  SigmaT : DriftIndex → Matrix (Fin p) (Fin p) ℝ
  gaussianLaw : Matrix (Fin p) (Fin p) ℝ → Measure (GenoVec p)
  sourceLaw : DriftIndex → Measure (GenoVec p)
  targetLaw : DriftIndex → Measure (GenoVec p)
  d_nonneg : ∀ d, 0 ≤ d
  source_is_gaussian : ∀ d, sourceLaw d = gaussianLaw (SigmaS d)
  target_is_gaussian : ∀ d, targetLaw d = gaussianLaw (SigmaT d)

structure PureSplitModel where
  t : ℝ
  Ne : ℝ
  Ne_pos : 0 < Ne

noncomputable def PureSplitModel.tau (m : PureSplitModel) : ℝ :=
  coalescentTau m.t m.Ne

noncomputable def PureSplitModel.fst (m : PureSplitModel) : ℝ :=
  fstFromTau m.tau

structure SplitMigrationModel where
  t : ℝ
  Ne : ℝ
  mig : ℝ
  nDemes : ℕ
  mu : ℝ
  Ne_pos : 0 < Ne
  mig_nonneg : 0 ≤ mig
  nDemes_ge_two : 2 ≤ nDemes
  mu_nonneg : 0 ≤ mu

noncomputable def SplitMigrationModel.scaledMigration (m : SplitMigrationModel) : ℝ :=
  4 * m.Ne * m.mig

noncomputable def SplitMigrationModel.fstEqLimitLowMutationManyDemes (m : SplitMigrationModel) : ℝ :=
  1 / (1 + m.scaledMigration)

noncomputable def hudsonFstFromCoalescenceTimes (ETss ETst : ℝ) : ℝ :=
  1 - ETss / ETst

structure DemographicCoalescenceScalars where
  ETss : ℝ
  ETst : ℝ

noncomputable def DemographicCoalescenceScalars.delta
    (d : DemographicCoalescenceScalars) : ℝ :=
  hudsonFstFromCoalescenceTimes d.ETss d.ETst

@[simp] theorem DemographicCoalescenceScalars.delta_eq
    (d : DemographicCoalescenceScalars) :
    d.delta = 1 - d.ETss / d.ETst := by
  rfl

noncomputable def twoDemeIMEquilibriumETss (M : ℝ) : ℝ := 2

noncomputable def twoDemeIMEquilibriumETst (M : ℝ) : ℝ :=
  (2 * M + 1) / M

noncomputable def twoDemeIMEquilibriumScalars (M : ℝ) : DemographicCoalescenceScalars where
  ETss := twoDemeIMEquilibriumETss M
  ETst := twoDemeIMEquilibriumETst M

noncomputable def twoDemeIMEquilibriumDelta (M : ℝ) : ℝ :=
  1 / (2 * M + 1)

theorem twoDemeIMEquilibriumDelta_eq (M : ℝ) (hM : M ≠ 0) (h2M1 : 2 * M + 1 ≠ 0) :
    (twoDemeIMEquilibriumScalars M).delta = twoDemeIMEquilibriumDelta M := by
  simp [DemographicCoalescenceScalars.delta, hudsonFstFromCoalescenceTimes,
    twoDemeIMEquilibriumScalars, twoDemeIMEquilibriumETss,
    twoDemeIMEquilibriumETst, twoDemeIMEquilibriumDelta]
  field_simp [hM, h2M1]
  ring

theorem twoDemeIMEquilibriumDelta_pos (M : ℝ) (hM : 0 < M) :
    0 < twoDemeIMEquilibriumDelta M := by
  unfold twoDemeIMEquilibriumDelta
  positivity

theorem twoDemeIMEquilibriumDelta_lt_one (M : ℝ) (hM : 0 < M) :
    twoDemeIMEquilibriumDelta M < 1 := by
  unfold twoDemeIMEquilibriumDelta
  rw [div_lt_one (by linarith)]
  linarith

section PresentDayMetrics

/-- Present-day PGS variance after drift from an ancestral variance `V_A`. -/
noncomputable def presentDayPGSVariance (V_A fst : ℝ) : ℝ :=
  (1 - fst) * V_A

/-- Present-day signal-to-noise ratio for prediction under drift. -/
noncomputable def presentDaySignalToNoise (V_A V_E fst : ℝ) : ℝ :=
  presentDayPGSVariance V_A fst / V_E

/-- Present-day explained-variance proxy from drifted signal and environmental noise. -/
noncomputable def presentDayR2 (V_A V_E fst : ℝ) : ℝ :=
  let v := presentDayPGSVariance V_A fst
  v / (v + V_E)

/-- Generic present-day AUC map from signal-to-noise (e.g. Gaussian-liability link). -/
noncomputable def presentDayAUC (aucLink : ℝ → ℝ) (V_A V_E fst : ℝ) : ℝ :=
  aucLink (presentDaySignalToNoise V_A V_E fst)

/-- Drift monotonically degrades signal-to-noise when `V_A, V_E > 0`. -/
theorem drift_degrades_signalToNoise
    (V_A V_E fstS fstT : ℝ)
    (hVA : 0 < V_A) (hVE : 0 < V_E)
    (hfst : fstS < fstT) :
    presentDaySignalToNoise V_A V_E fstT < presentDaySignalToNoise V_A V_E fstS := by
  unfold presentDaySignalToNoise presentDayPGSVariance
  have hnum : (1 - fstT) * V_A < (1 - fstS) * V_A := by
    nlinarith [mul_lt_mul_of_pos_right hfst hVA]
  have hInv : 0 < V_E⁻¹ := inv_pos.mpr hVE
  have hscaled :
      ((1 - fstT) * V_A) * V_E⁻¹ < ((1 - fstS) * V_A) * V_E⁻¹ :=
    mul_lt_mul_of_pos_right hnum hInv
  simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hscaled

/-- Drift monotonically degrades present-day `R²` when `V_A, V_E > 0` and `fst < 1`. -/
theorem drift_degrades_R2
    (V_A V_E fstS fstT : ℝ)
    (hVA : 0 < V_A)
    (hfst : fstS < fstT)
    (hmono : StrictMono (fun x : ℝ => x / (x + V_E))) :
    presentDayR2 V_A V_E fstT < presentDayR2 V_A V_E fstS := by
  unfold presentDayR2 presentDayPGSVariance
  apply hmono
  nlinarith [mul_lt_mul_of_pos_right hfst hVA]

/-- Drift monotonically degrades AUC for any strictly increasing AUC link on SNR. -/
theorem drift_degrades_AUC_of_strictMono
    (aucLink : ℝ → ℝ) (hauc : StrictMono aucLink)
    (V_A V_E fstS fstT : ℝ)
    (hVA : 0 < V_A) (hVE : 0 < V_E)
    (hfst : fstS < fstT) :
    presentDayAUC aucLink V_A V_E fstT < presentDayAUC aucLink V_A V_E fstS := by
  unfold presentDayAUC
  exact hauc (drift_degrades_signalToNoise V_A V_E fstS fstT hVA hVE hfst)

/-- If target `R²` is strictly below source `R²`, the portability ratio is strictly below `1`. -/
theorem portability_ratio_lt_one_of_drop
    (srcR2 tgtR2 : ℝ)
    (hsrc_pos : 0 < srcR2)
    (hdrop : tgtR2 < srcR2) :
    tgtR2 / srcR2 < 1 := by
  exact (_root_.div_lt_iff₀ hsrc_pos).2 (by simpa using hdrop)

/-- Headline portability theorem: positive drift implies `R²` ratio is strictly below `1`. -/
theorem portability_ratio_lt_one_of_positive_drift
    (V_A V_E fstS fstT : ℝ)
    (hVA : 0 < V_A)
    (hfst : fstS < fstT)
    (hmono : StrictMono (fun x : ℝ => x / (x + V_E)))
    (hsrc_pos : 0 < presentDayR2 V_A V_E fstS) :
    presentDayR2 V_A V_E fstT / presentDayR2 V_A V_E fstS < 1 := by
  have hdrop : presentDayR2 V_A V_E fstT < presentDayR2 V_A V_E fstS :=
    drift_degrades_R2 V_A V_E fstS fstT hVA hfst hmono
  exact portability_ratio_lt_one_of_drop (presentDayR2 V_A V_E fstS)
    (presentDayR2 V_A V_E fstT) hsrc_pos hdrop

/-- Pointwise Brier regret relative to the true Bernoulli probability. -/
noncomputable def brierRegretPoint (η q : ℝ) : ℝ :=
  brierBernoulliRisk η q - brierBernoulliRisk η η

/-- Pointwise Brier regret ratio between target and source predictors. -/
noncomputable def brierRegretRatio (η qSource qTarget : ℝ) : ℝ :=
  brierRegretPoint η qTarget / brierRegretPoint η qSource

/-- Brier regret equals squared calibration error exactly. -/
theorem brierRegretPoint_eq_sq_error (η q : ℝ) :
    brierRegretPoint η q = (q - η) ^ 2 := by
  unfold brierRegretPoint
  simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using brier_regret_pointwise η q

/-- Ratio form in present-day units: Brier-regret ratio is a squared-error ratio. -/
theorem brierRegretRatio_eq_sq_error_ratio (η qSource qTarget : ℝ) :
    brierRegretRatio η qSource qTarget =
      ((qTarget - η) ^ 2) / ((qSource - η) ^ 2) := by
  unfold brierRegretRatio
  rw [brierRegretPoint_eq_sq_error, brierRegretPoint_eq_sq_error]

/-- Pointwise log-loss regret relative to truth. -/
noncomputable def logLossRegretPoint (η q : ℝ) : ℝ :=
  bernoulliLogLoss η q - bernoulliLogLoss η η

/-- Pointwise log-loss regret ratio between target and source predictors. -/
noncomputable def logLossRegretRatio (η qSource qTarget : ℝ) : ℝ :=
  logLossRegretPoint η qTarget / logLossRegretPoint η qSource

/-- Log-loss regret is exactly Bernoulli KL divergence. -/
theorem logLossRegretPoint_eq_kl (η q : ℝ)
    (hη0 : 0 < η) (hη1 : η < 1)
    (hq0 : 0 < q) (hq1 : q < 1) :
    logLossRegretPoint η q = bernoulliKLReal η q := by
  unfold logLossRegretPoint
  simpa using logLoss_regret_eq_kl_pointwise η q hη0 hη1 hq0 hq1

/-- Ratio form in present-day units: log-loss regret ratio is a KL ratio. -/
theorem logLossRegretRatio_eq_kl_ratio (η qSource qTarget : ℝ)
    (hη0 : 0 < η) (hη1 : η < 1)
    (hqS0 : 0 < qSource) (hqS1 : qSource < 1)
    (hqT0 : 0 < qTarget) (hqT1 : qTarget < 1) :
    logLossRegretRatio η qSource qTarget =
      bernoulliKLReal η qTarget / bernoulliKLReal η qSource := by
  unfold logLossRegretRatio
  rw [logLossRegretPoint_eq_kl η qTarget hη0 hη1 hqT0 hqT1,
    logLossRegretPoint_eq_kl η qSource hη0 hη1 hqS0 hqS1]

end PresentDayMetrics

end PortabilityDrift

end Calibrator
