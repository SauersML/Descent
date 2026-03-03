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

/-- Source variance implied by present-day source `R²` after fixing noise scale to `1`. -/
noncomputable def sourceVarianceFromR2 (r2Source : ℝ) : ℝ :=
  r2Source / (1 - r2Source)

/-- Drift transport written purely from present-day source variance and observable `F_ST`s. -/
noncomputable def targetVarianceFromSource
    (vSource fstSource fstTarget : ℝ) : ℝ :=
  vSource * ((1 - fstTarget) / (1 - fstSource))

/-- `R²` induced by a variance ratio after fixing environmental scale to `1`. -/
noncomputable def r2FromVarianceScaleOne (v : ℝ) : ℝ :=
  v / (v + 1)

/-- On nonnegative variances, `v ↦ v/(v+1)` is strictly increasing. -/
theorem r2FromVarianceScaleOne_strictMono_nonneg
    (x y : ℝ) (hx : 0 ≤ x) (hxy : x < y) :
    r2FromVarianceScaleOne x < r2FromVarianceScaleOne y := by
  unfold r2FromVarianceScaleOne
  have hx1 : 0 < x + 1 := by linarith
  have hy1 : 0 < y + 1 := by linarith [hx, hxy]
  have hxy1 : x + 1 < y + 1 := by linarith
  have hInv : 1 / (y + 1) < 1 / (x + 1) := by
    rw [one_div_lt_one_div hy1 hx1]
    exact hxy1
  have hsub : 1 - 1 / (x + 1) < 1 - 1 / (y + 1) := by linarith
  have hxne : x + 1 ≠ 0 := by linarith
  have hyne : y + 1 ≠ 0 := by linarith
  have hxrepr : x / (x + 1) = 1 - 1 / (x + 1) := by
    field_simp [hxne]
    ring
  have hyrepr : y / (y + 1) = 1 - 1 / (y + 1) := by
    field_simp [hyne]
    ring
  simpa [hxrepr, hyrepr] using hsub

/-- Present-day target `R²` written only from source `R²` and source/target `F_ST`. -/
noncomputable def targetR2FromObservables
    (r2Source fstSource fstTarget : ℝ) : ℝ :=
  r2FromVarianceScaleOne
    (targetVarianceFromSource (sourceVarianceFromR2 r2Source) fstSource fstTarget)

/-- Source `R²` represented through the scale-one variance map. -/
theorem sourceR2_eq_r2FromVarianceScaleOne (r2Source : ℝ)
    (h_r2 : 0 < r2Source ∧ r2Source < 1) :
    r2FromVarianceScaleOne (sourceVarianceFromR2 r2Source) = r2Source := by
  rcases h_r2 with ⟨h0, h1⟩
  unfold r2FromVarianceScaleOne sourceVarianceFromR2
  have hden : 1 - r2Source ≠ 0 := by linarith
  field_simp [hden]
  ring

/-- Positivity of source variance induced by `0 < R²_source < 1`. -/
theorem sourceVarianceFromR2_pos (r2Source : ℝ)
    (h_r2 : 0 < r2Source ∧ r2Source < 1) :
    0 < sourceVarianceFromR2 r2Source := by
  rcases h_r2 with ⟨h0, h1⟩
  unfold sourceVarianceFromR2
  have hden : 0 < 1 - r2Source := by linarith
  exact div_pos h0 hden

/-- Under `fstSource < fstTarget < 1`, target variance is strictly below source variance. -/
theorem targetVarianceFromSource_lt_source
    (vSource fstSource fstTarget : ℝ)
    (hv : 0 < vSource)
    (hfst : fstSource < fstTarget)
    (hfstBound : fstTarget < 1) :
    targetVarianceFromSource vSource fstSource fstTarget < vSource := by
  unfold targetVarianceFromSource
  have hden : 0 < 1 - fstSource := by
    have : fstSource < 1 := lt_trans hfst hfstBound
    linarith
  have hratio : ((1 - fstTarget) / (1 - fstSource)) < 1 := by
    rw [div_lt_one hden]
    linarith
  have hmul : vSource * ((1 - fstTarget) / (1 - fstSource)) < vSource * 1 :=
    mul_lt_mul_of_pos_left hratio hv
  simpa using hmul

/-- Under `fstSource < fstTarget < 1`, transported target variance stays positive. -/
theorem targetVarianceFromSource_pos
    (vSource fstSource fstTarget : ℝ)
    (hv : 0 < vSource)
    (hfst : fstSource < fstTarget)
    (hfstBound : fstTarget < 1) :
    0 < targetVarianceFromSource vSource fstSource fstTarget := by
  unfold targetVarianceFromSource
  have hden : 0 < 1 - fstSource := by
    have : fstSource < 1 := lt_trans hfst hfstBound
    linarith
  have hnum : 0 < 1 - fstTarget := by linarith
  have hratio : 0 < (1 - fstTarget) / (1 - fstSource) := div_pos hnum hden
  exact mul_pos hv hratio

/-- Observable-only portability theorem: target/source `R²` ratio is strictly below `1`. -/
theorem portability_ratio_from_observables
    (r2Source fstSource fstTarget : ℝ)
    (h_r2 : 0 < r2Source ∧ r2Source < 1)
    (h_fst : fstSource < fstTarget)
    (h_fst_bounds : 0 ≤ fstSource ∧ fstTarget < 1) :
    targetR2FromObservables r2Source fstSource fstTarget / r2Source < 1 := by
  rcases h_fst_bounds with ⟨_, hfstT_lt_one⟩
  have hvS_pos : 0 < sourceVarianceFromR2 r2Source :=
    sourceVarianceFromR2_pos r2Source h_r2
  have hvT_lt : targetVarianceFromSource (sourceVarianceFromR2 r2Source) fstSource fstTarget
      < sourceVarianceFromR2 r2Source :=
    targetVarianceFromSource_lt_source (sourceVarianceFromR2 r2Source)
      fstSource fstTarget hvS_pos h_fst hfstT_lt_one
  have hr2_drop :
      r2FromVarianceScaleOne
          (targetVarianceFromSource (sourceVarianceFromR2 r2Source) fstSource fstTarget)
        < r2FromVarianceScaleOne (sourceVarianceFromR2 r2Source) := by
    have hvT_nonneg :
        0 ≤ targetVarianceFromSource (sourceVarianceFromR2 r2Source) fstSource fstTarget := by
      exact le_of_lt (targetVarianceFromSource_pos
        (sourceVarianceFromR2 r2Source) fstSource fstTarget hvS_pos h_fst hfstT_lt_one)
    exact r2FromVarianceScaleOne_strictMono_nonneg
      (targetVarianceFromSource (sourceVarianceFromR2 r2Source) fstSource fstTarget)
      (sourceVarianceFromR2 r2Source) hvT_nonneg hvT_lt
  have hr2S_pos : 0 < r2FromVarianceScaleOne (sourceVarianceFromR2 r2Source) := by
    unfold r2FromVarianceScaleOne
    have hden : 0 < sourceVarianceFromR2 r2Source + 1 := by linarith [hvS_pos]
    exact div_pos hvS_pos hden
  have hratio :
      (r2FromVarianceScaleOne
          (targetVarianceFromSource (sourceVarianceFromR2 r2Source) fstSource fstTarget))
        / (r2FromVarianceScaleOne (sourceVarianceFromR2 r2Source)) < 1 :=
    portability_ratio_lt_one_of_drop
      (r2FromVarianceScaleOne (sourceVarianceFromR2 r2Source))
      (r2FromVarianceScaleOne
        (targetVarianceFromSource (sourceVarianceFromR2 r2Source) fstSource fstTarget))
      hr2S_pos hr2_drop
  have hsrc_eq : r2FromVarianceScaleOne (sourceVarianceFromR2 r2Source) = r2Source :=
    sourceR2_eq_r2FromVarianceScaleOne r2Source h_r2
  unfold targetR2FromObservables
  simpa [hsrc_eq] using hratio

/-- Observable-only strict `R²` drop: target `R²` is below source `R²`. -/
theorem targetR2_lt_source_from_observables
    (r2Source fstSource fstTarget : ℝ)
    (h_r2 : 0 < r2Source ∧ r2Source < 1)
    (h_fst : fstSource < fstTarget)
    (h_fst_bounds : 0 ≤ fstSource ∧ fstTarget < 1) :
    targetR2FromObservables r2Source fstSource fstTarget < r2Source := by
  rcases h_fst_bounds with ⟨_, hfstT_lt_one⟩
  have hvS_pos : 0 < sourceVarianceFromR2 r2Source :=
    sourceVarianceFromR2_pos r2Source h_r2
  have hvT_lt : targetVarianceFromSource (sourceVarianceFromR2 r2Source) fstSource fstTarget
      < sourceVarianceFromR2 r2Source :=
    targetVarianceFromSource_lt_source (sourceVarianceFromR2 r2Source)
      fstSource fstTarget hvS_pos h_fst hfstT_lt_one
  have hr2_drop :
      r2FromVarianceScaleOne
          (targetVarianceFromSource (sourceVarianceFromR2 r2Source) fstSource fstTarget)
        < r2FromVarianceScaleOne (sourceVarianceFromR2 r2Source) := by
    have hvT_nonneg :
        0 ≤ targetVarianceFromSource (sourceVarianceFromR2 r2Source) fstSource fstTarget := by
      exact le_of_lt (targetVarianceFromSource_pos
        (sourceVarianceFromR2 r2Source) fstSource fstTarget hvS_pos h_fst hfstT_lt_one)
    exact r2FromVarianceScaleOne_strictMono_nonneg
      (targetVarianceFromSource (sourceVarianceFromR2 r2Source) fstSource fstTarget)
      (sourceVarianceFromR2 r2Source) hvT_nonneg hvT_lt
  have hsrc_eq : r2FromVarianceScaleOne (sourceVarianceFromR2 r2Source) = r2Source :=
    sourceR2_eq_r2FromVarianceScaleOne r2Source h_r2
  unfold targetR2FromObservables
  simpa [hsrc_eq] using hr2_drop

/-- Drift transport ratio from observable source/target `F_ST`. -/
noncomputable def driftTransportRatio (fstSource fstTarget : ℝ) : ℝ :=
  (1 - fstTarget) / (1 - fstSource)

/-- Exact transport identity: target signal variance equals ratio times source variance. -/
theorem targetVarianceFromSource_eq_ratio_mul
    (vSource fstSource fstTarget : ℝ) :
    targetVarianceFromSource vSource fstSource fstTarget =
      driftTransportRatio fstSource fstTarget * vSource := by
  unfold targetVarianceFromSource driftTransportRatio
  ring

/-- Exact closed form for target `R²` from source `R²` and drift ratio `r`. -/
theorem targetR2FromObservables_closed_form
    (r2Source fstSource fstTarget : ℝ)
    (h_r2 : 0 < r2Source ∧ r2Source < 1) :
    targetR2FromObservables r2Source fstSource fstTarget =
      ((driftTransportRatio fstSource fstTarget) * r2Source) /
        (1 - r2Source + (driftTransportRatio fstSource fstTarget) * r2Source) := by
  rcases h_r2 with ⟨_, h1⟩
  set r : ℝ := driftTransportRatio fstSource fstTarget
  have h_target :
      targetVarianceFromSource (sourceVarianceFromR2 r2Source) fstSource fstTarget
        = r * sourceVarianceFromR2 r2Source := by
    simpa [r, mul_comm] using
      (targetVarianceFromSource_eq_ratio_mul
        (sourceVarianceFromR2 r2Source) fstSource fstTarget)
  unfold targetR2FromObservables r2FromVarianceScaleOne
  rw [h_target]
  unfold sourceVarianceFromR2
  have hden : 1 - r2Source ≠ 0 := by linarith
  field_simp [hden]
  ring_nf

/-- AUC conversion map used in the dashboard when environmental scale is fixed to `1`. -/
noncomputable def aucFromR2 (aucLink : ℝ → ℝ) (r2 : ℝ) : ℝ :=
  aucLink (sourceVarianceFromR2 r2)

/-- Observable source AUC map used by the dashboard. -/
noncomputable def sourceAUCFromObservables
    (aucLink : ℝ → ℝ) (r2Source : ℝ) : ℝ :=
  aucLink (sourceVarianceFromR2 r2Source)

/-- Brier conversion map used in the dashboard (`π(1-π)(1-R²)`). -/
noncomputable def brierFromR2 (π r2 : ℝ) : ℝ :=
  π * (1 - π) * (1 - r2)

/-- Observable target AUC map used by the dashboard: transport variance, then apply AUC link. -/
noncomputable def targetAUCFromObservables
    (aucLink : ℝ → ℝ) (r2Source fstSource fstTarget : ℝ) : ℝ :=
  aucLink (targetVarianceFromSource (sourceVarianceFromR2 r2Source) fstSource fstTarget)

/-- Observable source Brier map used by the dashboard. -/
noncomputable def sourceBrierFromObservables (π r2Source : ℝ) : ℝ :=
  brierFromR2 π r2Source

/-- Observable target Brier map used by the dashboard (`Brier(R²_target)`). -/
noncomputable def targetBrierFromObservables
    (π r2Source fstSource fstTarget : ℝ) : ℝ :=
  brierFromR2 π (targetR2FromObservables r2Source fstSource fstTarget)

/-- The AUC observable map is exactly "transport then link" by definition. -/
@[simp] theorem targetAUCFromObservables_eq
    (aucLink : ℝ → ℝ) (r2Source fstSource fstTarget : ℝ) :
    targetAUCFromObservables aucLink r2Source fstSource fstTarget =
      aucLink (targetVarianceFromSource (sourceVarianceFromR2 r2Source) fstSource fstTarget) := by
  rfl

/-- Full observable AUC degradation theorem:
strictly higher drift implies strictly lower target AUC for any strictly increasing AUC link. -/
theorem targetAUC_lt_source_of_observables
    (aucLink : ℝ → ℝ) (hauc : StrictMono aucLink)
    (r2Source fstSource fstTarget : ℝ)
    (h_r2 : 0 < r2Source ∧ r2Source < 1)
    (h_fst : fstSource < fstTarget)
    (h_fst_bounds : 0 ≤ fstSource ∧ fstTarget < 1) :
    targetAUCFromObservables aucLink r2Source fstSource fstTarget <
      sourceAUCFromObservables aucLink r2Source := by
  rcases h_fst_bounds with ⟨_, hfstT_lt_one⟩
  have hvS_pos : 0 < sourceVarianceFromR2 r2Source :=
    sourceVarianceFromR2_pos r2Source h_r2
  have hvT_lt : targetVarianceFromSource (sourceVarianceFromR2 r2Source) fstSource fstTarget
      < sourceVarianceFromR2 r2Source :=
    targetVarianceFromSource_lt_source (sourceVarianceFromR2 r2Source)
      fstSource fstTarget hvS_pos h_fst hfstT_lt_one
  unfold targetAUCFromObservables sourceAUCFromObservables
  exact hauc hvT_lt

/-- The Brier observable map is exactly `brierFromR2` at transported target `R²` by definition. -/
@[simp] theorem targetBrierFromObservables_eq
    (π r2Source fstSource fstTarget : ℝ) :
    targetBrierFromObservables π r2Source fstSource fstTarget =
      brierFromR2 π (targetR2FromObservables r2Source fstSource fstTarget) := by
  rfl

/-- Full observable Brier degradation theorem:
if target `R²` drops and `0 ≤ π ≤ 1`, target Brier is at least source Brier. -/
theorem targetBrier_ge_source_of_observables
    (π r2Source fstSource fstTarget : ℝ)
    (h_pi : 0 ≤ π ∧ π ≤ 1)
    (h_r2 : 0 < r2Source ∧ r2Source < 1)
    (h_fst : fstSource < fstTarget)
    (h_fst_bounds : 0 ≤ fstSource ∧ fstTarget < 1) :
    sourceBrierFromObservables π r2Source ≤
      targetBrierFromObservables π r2Source fstSource fstTarget := by
  rcases h_pi with ⟨hpi0, hpi1⟩
  have hr2_drop : targetR2FromObservables r2Source fstSource fstTarget < r2Source :=
    targetR2_lt_source_from_observables r2Source fstSource fstTarget h_r2 h_fst h_fst_bounds
  have hcoef_nonneg : 0 ≤ π * (1 - π) := by nlinarith
  unfold sourceBrierFromObservables targetBrierFromObservables brierFromR2
  have hbase : 1 - r2Source ≤ 1 - targetR2FromObservables r2Source fstSource fstTarget := by linarith
  exact mul_le_mul_of_nonneg_left hbase hcoef_nonneg

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
