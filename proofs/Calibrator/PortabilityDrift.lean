import Calibrator.Models
import Calibrator.Conclusions
import Calibrator.DGP

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

/-- Branchwise-to-pairwise `F_ST` map under independent drift from a common ancestor. -/
noncomputable def pairwiseFstFromBranches (fstS fstT : ℝ) : ℝ :=
  1 - (1 - fstS) * (1 - fstT)

@[simp] theorem pairwise_fst_decomposition (fstS fstT : ℝ) :
    pairwiseFstFromBranches fstS fstT = fstS + fstT - fstS * fstT := by
  unfold pairwiseFstFromBranches
  ring_nf

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

/-- The exact discrete Wright-Fisher retention factor after `t` generations. -/
noncomputable def wrightFisherDriftRetention (N t : ℕ) : ℝ :=
  (1 - 1 / (2 * (N : ℝ))) ^ t

/-- Exact discrete Wright-Fisher branch drift index after `t` generations. -/
noncomputable def wrightFisherFst (N t : ℕ) : ℝ :=
  1 - wrightFisherDriftRetention N t

theorem wrightFisherFst_eq
    (N t : ℕ) :
    wrightFisherFst N t = 1 - (1 - 1 / (2 * (N : ℝ))) ^ t := by
  simp [wrightFisherFst, wrightFisherDriftRetention]

private lemma wrightFisherBase_bounds (N : ℕ) (hN : 0 < N) :
    0 < 1 - 1 / (2 * (N : ℝ)) ∧ 1 - 1 / (2 * (N : ℝ)) ≤ 1 := by
  have hNge : (1 : ℝ) ≤ N := by exact_mod_cast Nat.succ_le_of_lt hN
  have hpos : 0 < 2 * (N : ℝ) := by positivity
  constructor
  · have : (1 : ℝ) < 2 * (N : ℝ) := by nlinarith
    have := div_lt_one_of_lt this (by positivity)
    linarith
  · have := div_nonneg (le_refl (1 : ℝ)) (le_of_lt hpos)
    linarith

theorem wrightFisherFst_nonneg
    (N t : ℕ)
    (hN : 0 < N) :
    0 ≤ wrightFisherFst N t := by
  obtain ⟨hbase_pos, hbase_le_one⟩ := wrightFisherBase_bounds N hN
  rw [wrightFisherFst_eq]
  have : (1 - 1 / (2 * (N : ℝ))) ^ t ≤ 1 :=
    pow_le_one₀ (le_of_lt hbase_pos) hbase_le_one
  linarith

theorem wrightFisherFst_lt_one
    (N t : ℕ)
    (hN : 0 < N) :
    wrightFisherFst N t < 1 := by
  obtain ⟨hbase_pos, _⟩ := wrightFisherBase_bounds N hN
  rw [wrightFisherFst_eq]
  have : 0 < (1 - 1 / (2 * (N : ℝ))) ^ t := pow_pos hbase_pos t
  linarith

/-- Drift-driven variance of the between-population PGS-mean difference.
For one branch with drift index `fst`, this is `2 * fst * V_A`. -/
noncomputable def Var_Delta_Mu (V_A fst : ℝ) : ℝ :=
  2 * fst * V_A

/-- Drift-driven expected absolute PGS-mean shift under a Normal approximation. -/
noncomputable def Expected_Abs_Shift (V_A fstS fstT : ℝ) : ℝ :=
  Real.sqrt (Var_Delta_Mu V_A (fstS + fstT)) * Real.sqrt (2 / Real.pi)

/-- Variance identity used by the dashboard mean-shift card. -/
theorem variance_mean_pgs_diff (V_A fst : ℝ) :
    Var_Delta_Mu V_A fst = 2 * fst * V_A := by
  rfl

/-- Rigorous algebraic proof of the expected absolute mean-shift formula for
    discrete Wright-Fisher drift, via explicit `Real.sqrt` and fraction manipulation. -/
theorem expected_abs_mean_shift_bound_proved
    (V_A fstS fstT : ℝ)
    (hVA_pos : 0 < V_A)
    (hfst_sum_nonneg : 0 ≤ fstS + fstT)
    (hfstS_lt_one : fstS < 1) :
    Expected_Abs_Shift V_A fstS fstT / Real.sqrt (presentDayPGSVariance V_A fstS) =
      2 * Real.sqrt ((fstS + fstT) / (Real.pi * (1 - fstS))) := by
  unfold Expected_Abs_Shift Var_Delta_Mu presentDayPGSVariance
  have h1 :
      Real.sqrt (2 * (fstS + fstT) * V_A) =
        Real.sqrt (2 * (fstS + fstT)) * Real.sqrt V_A := by
    have h_nonneg : 0 ≤ 2 * (fstS + fstT) := mul_nonneg (by norm_num) hfst_sum_nonneg
    rw [Real.sqrt_mul h_nonneg]
  have h2 :
      Real.sqrt ((1 - fstS) * V_A) =
        Real.sqrt (1 - fstS) * Real.sqrt V_A := by
    have h_nonneg : 0 ≤ 1 - fstS := by linarith
    rw [Real.sqrt_mul h_nonneg]
  rw [h1, h2]
  have h_sqrt_VA_ne_zero : Real.sqrt V_A ≠ 0 := Real.sqrt_ne_zero'.mpr hVA_pos
  have h_div :
      (Real.sqrt (2 * (fstS + fstT)) * Real.sqrt V_A * Real.sqrt (2 / Real.pi)) /
          (Real.sqrt (1 - fstS) * Real.sqrt V_A) =
        (Real.sqrt (2 * (fstS + fstT)) * Real.sqrt (2 / Real.pi)) /
          Real.sqrt (1 - fstS) := by
    calc
      (Real.sqrt (2 * (fstS + fstT)) * Real.sqrt V_A * Real.sqrt (2 / Real.pi)) /
          (Real.sqrt (1 - fstS) * Real.sqrt V_A)
        = (Real.sqrt (2 * (fstS + fstT)) * Real.sqrt (2 / Real.pi) * Real.sqrt V_A) /
            (Real.sqrt (1 - fstS) * Real.sqrt V_A) := by
              congr 1
              ring
      _ =
          (Real.sqrt (2 * (fstS + fstT)) * Real.sqrt (2 / Real.pi)) /
            Real.sqrt (1 - fstS) := by
              rw [mul_div_mul_right _ _ h_sqrt_VA_ne_zero]
  rw [h_div]
  have h3 :
      Real.sqrt (2 * (fstS + fstT)) * Real.sqrt (2 / Real.pi) =
        Real.sqrt (4 * (fstS + fstT) / Real.pi) := by
    have h_nonneg : 0 ≤ 2 * (fstS + fstT) := mul_nonneg (by norm_num) hfst_sum_nonneg
    rw [← Real.sqrt_mul h_nonneg]
    congr 1
    ring
  rw [h3]
  have h4 :
      Real.sqrt (4 * (fstS + fstT) / Real.pi) / Real.sqrt (1 - fstS) =
        Real.sqrt ((4 * (fstS + fstT) / Real.pi) / (1 - fstS)) := by
    have h_nonneg : 0 ≤ 4 * (fstS + fstT) / Real.pi := by
      apply div_nonneg
      · linarith
      · exact Real.pi_pos.le
    rw [← Real.sqrt_div h_nonneg]
  rw [h4]
  have h5 :
      (4 * (fstS + fstT) / Real.pi) / (1 - fstS) =
        4 * ((fstS + fstT) / (Real.pi * (1 - fstS))) := by
    calc
      (4 * (fstS + fstT) / Real.pi) / (1 - fstS) =
          (4 * (fstS + fstT)) / (Real.pi * (1 - fstS)) := by
            rw [div_div]
      _ = 4 * ((fstS + fstT) / (Real.pi * (1 - fstS))) := by
            ring
  rw [h5]
  have h4_nonneg : (0 : ℝ) ≤ 4 := by norm_num
  rw [Real.sqrt_mul h4_nonneg]
  norm_num

/-- Exact discrete Wright-Fisher mean-shift formula in source-standard-deviation units. -/
theorem expected_abs_mean_shift_of_wrightFisher
    (V_A : ℝ)
    (NS tS NT tT : ℕ)
    (hVA_pos : 0 < V_A)
    (hNS : 0 < NS)
    (hNT : 0 < NT) :
    Expected_Abs_Shift V_A (wrightFisherFst NS tS) (wrightFisherFst NT tT) /
        Real.sqrt (presentDayPGSVariance V_A (wrightFisherFst NS tS)) =
      2 * Real.sqrt
        ((wrightFisherFst NS tS + wrightFisherFst NT tT) /
          (Real.pi * (1 - wrightFisherFst NS tS))) := by
  apply expected_abs_mean_shift_bound_proved
  · exact hVA_pos
  · exact add_nonneg (wrightFisherFst_nonneg NS tS hNS) (wrightFisherFst_nonneg NT tT hNT)
  · exact wrightFisherFst_lt_one NS tS hNS

/-- Present-day signal-to-noise ratio for prediction under drift. -/
noncomputable def presentDaySignalToNoise (V_A V_E fst : ℝ) : ℝ :=
  presentDayPGSVariance V_A fst / V_E

/-- Present-day explained-variance proxy from drifted signal and environmental noise. -/
noncomputable def presentDayR2 (V_A V_E fst : ℝ) : ℝ :=
  let v := presentDayPGSVariance V_A fst
  v / (v + V_E)

/-- Exact bridge theorem: the dashboard algebraic `presentDayR2` equals statistical
`rsquared` when the relevant second-moment identities hold. -/
theorem presentDayR2_eq_statistical_rsquared
    {k : ℕ} [Fintype (Fin k)]
    (dgp : DataGeneratingProcess k)
    (signal : Predictor k)
    (V_A V_E fst : ℝ)
    (h_vf :
      (let μ := dgp.jointMeasure
       let mf : ℝ := ∫ pc, signal pc.1 pc.2 ∂μ
       ∫ pc, (signal pc.1 pc.2 - mf) ^ 2 ∂μ) = presentDayPGSVariance V_A fst)
    (h_vg :
      (let μ := dgp.jointMeasure
       let mg : ℝ := ∫ pc, dgp.trueExpectation pc.1 pc.2 ∂μ
       ∫ pc, (dgp.trueExpectation pc.1 pc.2 - mg) ^ 2 ∂μ) =
        presentDayPGSVariance V_A fst + V_E)
    (h_cov :
      (let μ := dgp.jointMeasure
       let mf : ℝ := ∫ pc, signal pc.1 pc.2 ∂μ
       let mg : ℝ := ∫ pc, dgp.trueExpectation pc.1 pc.2 ∂μ
       ∫ pc, (signal pc.1 pc.2 - mf) * (dgp.trueExpectation pc.1 pc.2 - mg) ∂μ) =
        presentDayPGSVariance V_A fst)
    (h_vsig_pos : 0 < presentDayPGSVariance V_A fst)
    (h_vtrue_pos : 0 < presentDayPGSVariance V_A fst + V_E) :
    presentDayR2 V_A V_E fst = rsquared dgp signal dgp.trueExpectation := by
  have h_vsig_ne : presentDayPGSVariance V_A fst ≠ 0 := by linarith
  have h_vtrue_ne : presentDayPGSVariance V_A fst + V_E ≠ 0 := by linarith
  have h_if_not :
      ¬(presentDayPGSVariance V_A fst = 0 ∨ presentDayPGSVariance V_A fst + V_E = 0) := by
    intro h
    rcases h with h0 | h1
    · exact h_vsig_ne h0
    · exact h_vtrue_ne h1
  have h_rs :
      rsquared dgp signal dgp.trueExpectation = (presentDayPGSVariance V_A fst) ^ 2 /
          (presentDayPGSVariance V_A fst * (presentDayPGSVariance V_A fst + V_E)) := by
    unfold rsquared
    simp [h_vf, h_vg, h_cov, h_if_not]
  rw [h_rs]
  unfold presentDayR2
  field_simp [h_vsig_ne, h_vtrue_ne]



/-- Expected `R²` from signal variance and environmental variance. -/
noncomputable def expectedR2 (vSignal V_E : ℝ) : ℝ :=
  vSignal / (vSignal + V_E)

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
    (hVA : 0 < V_A) (hVE : 0 < V_E)
    (hfst : fstS < fstT)
    (hfstT_le_one : fstT ≤ 1) :
    presentDayR2 V_A V_E fstT < presentDayR2 V_A V_E fstS := by
  unfold presentDayR2 presentDayPGSVariance
  have h_mono : ∀ (x y : ℝ), 0 ≤ x → x < y → x / (x + V_E) < y / (y + V_E) := by
    intro x y hx hxy
    have hxE : 0 < x + V_E := by linarith
    have hyE : 0 < y + V_E := by linarith [hx, hxy]
    have hxyE : x + V_E < y + V_E := by linarith
    have hInv : 1 / (y + V_E) < 1 / (x + V_E) := by
      rw [one_div_lt_one_div hyE hxE]
      exact hxyE
    have hsub : 1 - V_E / (x + V_E) < 1 - V_E / (y + V_E) := by
      have hmul := mul_lt_mul_of_pos_left hInv hVE
      have hfrac : V_E / (y + V_E) < V_E / (x + V_E) := by
        simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hmul
      nlinarith [hfrac]
    have hxne : x + V_E ≠ 0 := by linarith
    have hyne : y + V_E ≠ 0 := by linarith
    have hxrepr : x / (x + V_E) = 1 - V_E / (x + V_E) := by
      field_simp [hxne]
      ring
    have hyrepr : y / (y + V_E) = 1 - V_E / (y + V_E) := by
      field_simp [hyne]
      ring
    simpa [hxrepr, hyrepr] using hsub
  have hT_nonneg : 0 ≤ (1 - fstT) * V_A := by
    have : 0 ≤ 1 - fstT := by linarith
    exact mul_nonneg this (le_of_lt hVA)
  have h_lt : (1 - fstT) * V_A < (1 - fstS) * V_A := by
    nlinarith [mul_lt_mul_of_pos_right hfst hVA]
  exact h_mono ((1 - fstT) * V_A) ((1 - fstS) * V_A) hT_nonneg h_lt

/-- Drift monotonically degrades AUC for any strictly increasing AUC link on SNR. -/
theorem drift_degrades_AUC_of_strictMono
    (aucLink : ℝ → ℝ) (hauc : StrictMono aucLink)
    (V_A V_E fstS fstT : ℝ)
    (hVA : 0 < V_A) (hVE : 0 < V_E)
    (hfst : fstS < fstT) :
    presentDayAUC aucLink V_A V_E fstT < presentDayAUC aucLink V_A V_E fstS := by
  simpa [presentDayAUC] using hauc (drift_degrades_signalToNoise V_A V_E fstS fstT hVA hVE hfst)

/-- Real-world PGS variance with both drift and LD tagging efficiency. -/
noncomputable def realWorldPGSVariance (V_A fst rhoSq : ℝ) : ℝ :=
  rhoSq * (1 - fst) * V_A

/-- Causal-vs-observed architecture split:
`betaCausal` and `sigmaCausal*` describe biology, while `tagging*` describes array-level observability. -/
structure CausalObservableArchitecture (p : ℕ) where
  betaCausal : Fin p → ℝ
  sigmaCausalSource : Matrix (Fin p) (Fin p) ℝ
  sigmaCausalTarget : Matrix (Fin p) (Fin p) ℝ
  taggingSource : Matrix (Fin p) (Fin p) ℝ
  taggingTarget : Matrix (Fin p) (Fin p) ℝ

/-- Observable covariance induced by causal covariance and a tagging map. -/
noncomputable def observableCovariance {p : ℕ}
    (tag : Matrix (Fin p) (Fin p) ℝ) (sigmaCausal : Matrix (Fin p) (Fin p) ℝ) :
    Matrix (Fin p) (Fin p) ℝ :=
  tag * sigmaCausal * tag.transpose

/-- Source observable LD architecture. -/
noncomputable def sourceObservableCovariance {p : ℕ}
    (arch : CausalObservableArchitecture p) : Matrix (Fin p) (Fin p) ℝ :=
  observableCovariance arch.taggingSource arch.sigmaCausalSource

/-- Target observable LD architecture. -/
noncomputable def targetObservableCovariance {p : ℕ}
    (arch : CausalObservableArchitecture p) : Matrix (Fin p) (Fin p) ℝ :=
  observableCovariance arch.taggingTarget arch.sigmaCausalTarget

/-- Source ERM weights in closed form (normal equations) under invertible source covariance. -/
noncomputable def sourceERMWeights {p : ℕ}
    (sigmaObsSource : Matrix (Fin p) (Fin p) ℝ)
    (crossSource : Fin p → ℝ) : Fin p → ℝ :=
  sigmaObsSource⁻¹.mulVec crossSource

/-- Target population risk for a linear score `w` under covariance/cross/noise moments. -/
noncomputable def targetLinearRisk {p : ℕ}
    (sigmaObsTarget : Matrix (Fin p) (Fin p) ℝ)
    (crossTarget : Fin p → ℝ)
    (noiseVar : ℝ)
    (w : Fin p → ℝ) : ℝ :=
  noiseVar + dotProduct w (sigmaObsTarget.mulVec w) - 2 * dotProduct w crossTarget

/-- If source ERM satisfies source normal equations but not target normal equations,
the learned projection is source-LD specific (Euro-centric mismatch statement). -/
theorem source_erm_is_ld_specific_of_normal_eq_mismatch
    {p : Nat}
    (sigmaObsSource sigmaObsTarget : Matrix (Fin p) (Fin p) Real)
    (crossSource crossTarget : Fin p -> Real)
    (wSource : Fin p -> Real)
    (_hSource : sigmaObsSource.mulVec wSource = crossSource)
    (hMismatch : sigmaObsTarget.mulVec wSource ≠ crossTarget) :
    ¬ sigmaObsTarget.mulVec wSource = crossTarget := by
  exact hMismatch

/-- If one coefficient vector solves source normal equations and another solves target normal equations,
and no single vector can satisfy both systems, then source ERM and target ERM must differ. -/
theorem source_target_erm_differ_of_ld_system_conflict
    {p : Nat}
    (sigmaObsSource sigmaObsTarget : Matrix (Fin p) (Fin p) Real)
    (crossSource crossTarget : Fin p -> Real)
    (wSource wTarget : Fin p -> Real)
    (hSource : sigmaObsSource.mulVec wSource = crossSource)
    (hTarget : sigmaObsTarget.mulVec wTarget = crossTarget)
    (hConflict :
      ∀ w : Fin p -> Real, sigmaObsSource.mulVec w = crossSource -> sigmaObsTarget.mulVec w ≠ crossTarget) :
    wSource ≠ wTarget := by
  intro hEq
  have hNotTargetAtSource : sigmaObsTarget.mulVec wSource ≠ crossTarget := hConflict wSource hSource
  have hTargetAtSource : sigmaObsTarget.mulVec wSource = crossTarget := by simpa [hEq] using hTarget
  exact hNotTargetAtSource hTargetAtSource

/-- Multi-locus tag/causal architecture used in statistical genetics portability formulas. -/
structure MultiLocusTagModel (p q : ℕ) where
  betaCausal : Fin q → ℝ
  sigmaTagSource : Matrix (Fin p) (Fin p) ℝ
  sigmaTagTarget : Matrix (Fin p) (Fin p) ℝ
  sigmaTagCausalSource : Matrix (Fin p) (Fin q) ℝ
  sigmaTagCausalTarget : Matrix (Fin p) (Fin q) ℝ

/-- Minimal `1 × 1` tag/causal fixture for tests of OLS weight transport under LD shift. -/
def concreteTagModel (rS rT : ℝ) : MultiLocusTagModel 1 1 :=
  { betaCausal := ![1]
    sigmaTagSource := !![1]
    sigmaTagTarget := !![1]
    sigmaTagCausalSource := !![rS]
    sigmaTagCausalTarget := !![rT] }

/-- Dense source covariance witness for non-degenerate ERM-transport tests. -/
def sigmaObsSource : Matrix (Fin 2) (Fin 2) ℝ :=
  !![1, 0.5; 0.5, 1]

/-- Dense target covariance witness for non-degenerate ERM-transport tests. -/
def sigmaObsTarget : Matrix (Fin 2) (Fin 2) ℝ :=
  !![1, 0.1; 0.1, 1]

/-- Source cross-covariance vector paired with `sigmaObsSource`. -/
def crossSource : Fin 2 → ℝ :=
  ![0.8, 0.4]

/-- Target cross-covariance vector paired with `sigmaObsTarget`. -/
def crossTarget : Fin 2 → ℝ :=
  ![0.8, 0.0]

/-- Exact source OLS solution for the dense witness system. -/
noncomputable def wSource_opt : Fin 2 → ℝ :=
  ![0.8, 0.0]

/-- Exact target OLS solution for the dense witness system. -/
noncomputable def wTarget_opt : Fin 2 → ℝ :=
  ![80 / 99, -8 / 99]

/-- Source OLS-style weights: `w_S = Σ_S^{-1} Σ_tc,S β_c`. -/
noncomputable def sourceOLSWeights {p q : ℕ}
    (m : MultiLocusTagModel p q) : Fin p → ℝ :=
  m.sigmaTagSource⁻¹.mulVec (m.sigmaTagCausalSource.mulVec m.betaCausal)

/-- Target quadratic form for the transported source score:
`w_S^T Σ_T w_S`. -/
noncomputable def targetScoreQuadraticFormFromSource {p q : ℕ}
    (m : MultiLocusTagModel p q) : ℝ :=
  let wS := sourceOLSWeights m
  dotProduct wS (m.sigmaTagTarget.mulVec wS)

/-- Target tag-causal alignment term for transported source score:
`w_S^T Σ_tc,T β_c`. -/
noncomputable def targetTagCausalAlignmentFromSource {p q : ℕ}
    (m : MultiLocusTagModel p q) : ℝ :=
  let wS := sourceOLSWeights m
  dotProduct wS (m.sigmaTagCausalTarget.mulVec m.betaCausal)

/-- Present-day target `R²` proxy induced by source-trained weights and target LD geometry. -/
noncomputable def targetR2FromSourceWeights {p q : ℕ}
    (m : MultiLocusTagModel p q) (V_E : ℝ) : ℝ :=
  targetScoreQuadraticFormFromSource m / (targetScoreQuadraticFormFromSource m + V_E)

/-- The target variance term is exactly the target quadratic form `w_S^T Σ_T w_S`. -/
theorem target_score_quadratic_form_identity {p q : ℕ}
    (m : MultiLocusTagModel p q) :
    targetScoreQuadraticFormFromSource m =
      dotProduct (sourceOLSWeights m) (m.sigmaTagTarget.mulVec (sourceOLSWeights m)) := by
  simp [targetScoreQuadraticFormFromSource]

/-- Ohta-Kimura-style LD-correlation decay proxy across populations:
correlation decays exponentially with recombination distance and divergence. -/
noncomputable def ldCorrelationDecay (distance fstGap lambda : ℝ) : ℝ :=
  Real.exp (-(lambda * fstGap * distance))

/-- For positive divergence scale, LD correlation strictly decreases with distance. -/
theorem ldCorrelationDecay_strictAnti_distance
    (d1 d2 fstGap lambda : ℝ)
    (hScale : 0 < lambda * fstGap)
    (hDist : d1 < d2) :
    ldCorrelationDecay d2 fstGap lambda < ldCorrelationDecay d1 fstGap lambda := by
  unfold ldCorrelationDecay
  apply Real.exp_lt_exp.mpr
  nlinarith [mul_lt_mul_of_pos_left hDist hScale]

/-- For positive distance and decay scale, LD correlation strictly decreases with `F_ST`. -/
theorem ldCorrelationDecay_strictAnti_fst
    (distance lambda fstSource fstTarget : ℝ)
    (hDist : 0 < distance)
    (hLambda : 0 < lambda)
    (hFst : fstSource < fstTarget) :
    ldCorrelationDecay distance fstTarget lambda < ldCorrelationDecay distance fstSource lambda := by
  unfold ldCorrelationDecay
  apply Real.exp_lt_exp.mpr
  have h_pos : 0 < lambda * distance := mul_pos hLambda hDist
  have h_lt : fstSource * (lambda * distance) < fstTarget * (lambda * distance) :=
    mul_lt_mul_of_pos_right hFst h_pos
  linarith

/-- Drift-only transport multiplier on observed signal variance. -/
noncomputable def alleleFreqTransport (fstSource fstTarget : ℝ) : ℝ :=
  (1 - fstTarget) / (1 - fstSource)

/-- LD-only transport multiplier (tagging transfer). -/
noncomputable def ldTransport (rhoSource rhoTarget : ℝ) : ℝ :=
  rhoTarget / rhoSource

/-- Total signal transport from source to target decomposes into AF and LD factors. -/
noncomputable def totalSignalTransport
    (fstSource fstTarget rhoSource rhoTarget : ℝ) : ℝ :=
  alleleFreqTransport fstSource fstTarget * ldTransport rhoSource rhoTarget

/-- Exact decomposition identity for transport multipliers. -/
theorem totalSignalTransport_decomposes
    (fstSource fstTarget rhoSource rhoTarget : ℝ) :
    totalSignalTransport fstSource fstTarget rhoSource rhoTarget =
      alleleFreqTransport fstSource fstTarget * ldTransport rhoSource rhoTarget := by
  rfl

/-- AF-only transport loss proxy (1 - AF transport multiplier). -/
noncomputable def afTransportLoss (fstSource fstTarget : ℝ) : ℝ :=
  1 - alleleFreqTransport fstSource fstTarget

/-- LD-only transport loss proxy (1 - LD transport multiplier). -/
noncomputable def ldTransportLoss (rhoSource rhoTarget : ℝ) : ℝ :=
  1 - ldTransport rhoSource rhoTarget

/-- Joint transport loss proxy decomposes additively into AF and LD parts. -/
noncomputable def jointTransportLoss
    (fstSource fstTarget rhoSource rhoTarget : ℝ) : ℝ :=
  afTransportLoss fstSource fstTarget + ldTransportLoss rhoSource rhoTarget

/-- AF+LD decomposition identity. -/
theorem jointTransportLoss_decomposes
    (fstSource fstTarget rhoSource rhoTarget : ℝ) :
    jointTransportLoss fstSource fstTarget rhoSource rhoTarget =
      afTransportLoss fstSource fstTarget + ldTransportLoss rhoSource rhoTarget := by
  rfl

/-- LD dominance criterion: if LD loss exceeds AF loss, joint loss is strictly closer to LD. -/
theorem ld_strictly_dominates_af_in_joint_loss
    (fstSource fstTarget rhoSource rhoTarget : ℝ)
    (hDom : afTransportLoss fstSource fstTarget < ldTransportLoss rhoSource rhoTarget) :
    jointTransportLoss fstSource fstTarget rhoSource rhoTarget >
      2 * afTransportLoss fstSource fstTarget := by
  unfold jointTransportLoss
  linarith

/-- For fixed `V_E > 0`, `v ↦ v / (v + V_E)` is strictly increasing on nonnegative variances. -/
theorem expectedR2_strictMono_nonneg
    (V_E x y : ℝ)
    (hVE : 0 < V_E) (hx : 0 ≤ x) (hxy : x < y) :
    expectedR2 x V_E < expectedR2 y V_E := by
  unfold expectedR2
  have hxE : 0 < x + V_E := by linarith
  have hyE : 0 < y + V_E := by linarith [hx, hxy]
  -- Use the identity v/(v+E) = 1 - E/(v+E) to reduce to monotonicity of E/(v+E)
  have hxne : x + V_E ≠ 0 := ne_of_gt hxE
  have hyne : y + V_E ≠ 0 := ne_of_gt hyE
  have hxrepr : x / (x + V_E) = 1 - V_E / (x + V_E) := by field_simp; ring
  have hyrepr : y / (y + V_E) = 1 - V_E / (y + V_E) := by field_simp; ring
  rw [hxrepr, hyrepr]
  -- E/(y+E) < E/(x+E) because x+E < y+E and E > 0
  have : V_E / (y + V_E) < V_E / (x + V_E) :=
    div_lt_div_of_pos_left hVE hxE (by linarith)
  linarith

/-- With any imperfect source tagging (`ρS > 0`), worsening target tagging (`ρT < ρS`)
strictly lowers portability when drift terms are fixed. -/
theorem portability_ratio_with_target_ld_decay_any_source
    (V_A V_E fstS fstT rhoS rhoT : ℝ)
    (hVA : 0 < V_A) (hVE : 0 < V_E)
    (hfstS_lt_one : fstS < 1) (hfstT_lt_one : fstT < 1)
    (h_rho : 0 < rhoT ∧ rhoT < rhoS) :
    expectedR2 (realWorldPGSVariance V_A fstT rhoT) V_E /
      expectedR2 (realWorldPGSVariance V_A fstS rhoS) V_E <
    expectedR2 (realWorldPGSVariance V_A fstT rhoS) V_E /
      expectedR2 (realWorldPGSVariance V_A fstS rhoS) V_E := by
  rcases h_rho with ⟨hRhoT_pos, hRhoT_lt_rhoS⟩
  have hRhoS_pos : 0 < rhoS := lt_trans hRhoT_pos hRhoT_lt_rhoS
  have hu_pos : 0 < (1 - fstT) * V_A := mul_pos (by linarith) hVA
  -- Numerator: rhoT < rhoS implies R²(rhoT·u) < R²(rhoS·u)
  have h_num_lt :
      expectedR2 (realWorldPGSVariance V_A fstT rhoT) V_E <
        expectedR2 (realWorldPGSVariance V_A fstT rhoS) V_E := by
    apply expectedR2_strictMono_nonneg V_E _ _ hVE
    · unfold realWorldPGSVariance
      exact le_of_lt (by simpa [mul_assoc] using mul_pos hRhoT_pos hu_pos)
    · simpa [realWorldPGSVariance, mul_assoc] using
        mul_lt_mul_of_pos_right hRhoT_lt_rhoS hu_pos
  -- Denominator positivity
  have hsource_sig_pos : 0 < realWorldPGSVariance V_A fstS rhoS := by
    unfold realWorldPGSVariance
    simpa [mul_assoc] using mul_pos (mul_pos hRhoS_pos (by linarith : 0 < 1 - fstS)) hVA
  have h_den_pos : 0 < expectedR2 (realWorldPGSVariance V_A fstS rhoS) V_E := by
    unfold expectedR2
    exact div_pos hsource_sig_pos (by linarith)
  -- Divide both sides by positive denominator
  simpa [div_eq_mul_inv] using
    mul_lt_mul_of_pos_right h_num_lt (inv_pos.mpr h_den_pos)

/-- With source perfectly tagged (`ρ_S = 1`), adding target LD decay (`ρ_T < 1`)
strictly lowers the portability ratio versus drift-only transport. -/
theorem portability_ratio_with_ld_decay
    (V_A V_E fstS fstT rhoS rhoT : ℝ)
    (hVA : 0 < V_A) (hVE : 0 < V_E)
    (hfst : fstS < fstT) (hfstT_lt_one : fstT < 1) (hRhoS : rhoS = 1)
    (h_rho : 0 < rhoT ∧ rhoT < rhoS) :
    expectedR2 (realWorldPGSVariance V_A fstT rhoT) V_E /
      expectedR2 (realWorldPGSVariance V_A fstS rhoS) V_E <
    expectedR2 (presentDayPGSVariance V_A fstT) V_E /
      expectedR2 (presentDayPGSVariance V_A fstS) V_E := by
  rcases h_rho with ⟨hRhoT_pos, hRhoT_lt_rhoS⟩
  have hfstS_lt_one : fstS < 1 := lt_trans hfst hfstT_lt_one
  have hTargetPos : 0 < (1 - fstT) * V_A := by
    have : 0 < 1 - fstT := by linarith
    exact mul_pos this hVA
  have hTarget_nonneg : 0 ≤ (1 - fstT) * V_A := le_of_lt hTargetPos
  have hRhoT_lt_one : rhoT < 1 := by simpa [hRhoS] using hRhoT_lt_rhoS
  have hRealTarget_lt :
      realWorldPGSVariance V_A fstT rhoT < presentDayPGSVariance V_A fstT := by
    have hscaled :
        rhoT * ((1 - fstT) * V_A) < 1 * ((1 - fstT) * V_A) :=
      mul_lt_mul_of_pos_right hRhoT_lt_one hTargetPos
    simpa [realWorldPGSVariance, presentDayPGSVariance, mul_assoc] using hscaled
  have hR2Target_lt :
      expectedR2 (realWorldPGSVariance V_A fstT rhoT) V_E <
        expectedR2 (presentDayPGSVariance V_A fstT) V_E := by
    apply expectedR2_strictMono_nonneg V_E
    · exact hVE
    · unfold realWorldPGSVariance
      have hRhoTerm_nonneg : 0 ≤ rhoT * (1 - fstT) := by
        have hOneMinus_nonneg : 0 ≤ 1 - fstT := by linarith
        exact mul_nonneg (le_of_lt hRhoT_pos) hOneMinus_nonneg
      exact mul_nonneg hRhoTerm_nonneg (le_of_lt hVA)
    · exact hRealTarget_lt
  have hSourcePos : 0 < presentDayPGSVariance V_A fstS := by
    unfold presentDayPGSVariance
    have : 0 < 1 - fstS := by linarith
    exact mul_pos this hVA
  have hR2Source_pos : 0 < expectedR2 (presentDayPGSVariance V_A fstS) V_E := by
    unfold expectedR2
    have hden : 0 < presentDayPGSVariance V_A fstS + V_E := by linarith [hSourcePos, hVE]
    exact div_pos hSourcePos hden
  have hL :
      expectedR2 (realWorldPGSVariance V_A fstT rhoT) V_E /
          expectedR2 (presentDayPGSVariance V_A fstS) V_E <
        expectedR2 (presentDayPGSVariance V_A fstT) V_E /
          expectedR2 (presentDayPGSVariance V_A fstS) V_E := by
    have hmul :
        expectedR2 (realWorldPGSVariance V_A fstT rhoT) V_E * (expectedR2 (presentDayPGSVariance V_A fstS) V_E)⁻¹ <
          expectedR2 (presentDayPGSVariance V_A fstT) V_E * (expectedR2 (presentDayPGSVariance V_A fstS) V_E)⁻¹ :=
      mul_lt_mul_of_pos_right hR2Target_lt (inv_pos.mpr hR2Source_pos)
    simpa [div_eq_mul_inv] using hmul
  simpa [hRhoS, realWorldPGSVariance] using hL

/-- General LD-aware portability theorem without assuming perfect source tagging.
Under `0 < rhoT < rhoS ≤ 1` and `fstS < fstT < 1`, the LD+drift portability ratio
is strictly below the drift-only portability ratio. -/
theorem portability_ratio_with_ld_decay_general
    (V_A V_E fstS fstT rhoS rhoT : ℝ)
    (hVA : 0 < V_A) (hVE : 0 < V_E)
    (hfst : fstS < fstT) (hfstT_lt_one : fstT < 1)
    (hRhoS : rhoS = 1)
    (h_rho : 0 < rhoT ∧ rhoT < rhoS ∧ rhoS ≤ 1) :
    expectedR2 (realWorldPGSVariance V_A fstT rhoT) V_E /
      expectedR2 (realWorldPGSVariance V_A fstS rhoS) V_E <
    expectedR2 (presentDayPGSVariance V_A fstT) V_E /
      expectedR2 (presentDayPGSVariance V_A fstS) V_E := by
  rcases h_rho with ⟨hRhoT_pos, hRhoT_lt_rhoS, _⟩
  exact portability_ratio_with_ld_decay V_A V_E fstS fstT rhoS rhoT
    hVA hVE hfst hfstT_lt_one hRhoS ⟨hRhoT_pos, hRhoT_lt_rhoS⟩

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
    (hVA : 0 < V_A) (hVE : 0 < V_E)
    (hfst : fstS < fstT)
    (hfstT_le_one : fstT ≤ 1)
    (hsrc_pos : 0 < presentDayR2 V_A V_E fstS) :
    presentDayR2 V_A V_E fstT / presentDayR2 V_A V_E fstS < 1 := by
  have hdrop : presentDayR2 V_A V_E fstT < presentDayR2 V_A V_E fstS :=
    drift_degrades_R2 V_A V_E fstS fstT hVA hVE hfst hfstT_le_one
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
  -- r2FromVarianceScaleOne v = v/(v+1) = expectedR2 v 1
  show r2FromVarianceScaleOne x < r2FromVarianceScaleOne y
  have : expectedR2 x 1 < expectedR2 y 1 :=
    expectedR2_strictMono_nonneg 1 x y one_pos hx hxy
  simpa [expectedR2, r2FromVarianceScaleOne] using this

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

/-- Exact liability-threshold AUC as a function of SNR:
`AUC = Φ(√(snr/2))`. -/
noncomputable def liabilityAUCFromSNR (snr : ℝ) : ℝ :=
  Phi (Real.sqrt (snr / 2))

/-- Exact liability-threshold AUC from signal and environmental variances. -/
noncomputable def liabilityAUCFromVariances (vSignal vEnv : ℝ) : ℝ :=
  Phi (Real.sqrt (vSignal / (2 * vEnv)))

/-- With `vEnv = 1`, variance form equals SNR form exactly. -/
theorem liabilityAUCFromVariances_scaleOne (vSignal : ℝ) :
    liabilityAUCFromVariances vSignal 1 = liabilityAUCFromSNR vSignal := by
  unfold liabilityAUCFromVariances liabilityAUCFromSNR
  ring_nf

/-- On nonnegative SNR, the liability-threshold AUC map is strictly increasing
whenever `Phi` is strictly increasing. -/
theorem liabilityAUCFromSNR_strictMonoOn_nonneg
    (hPhiStrict : StrictMono Phi) :
    StrictMonoOn liabilityAUCFromSNR (Set.Ici 0) := by
  intro x hx y hy hxy
  unfold liabilityAUCFromSNR
  apply hPhiStrict
  have hx2 : 0 ≤ x / 2 := by
    exact div_nonneg hx (by positivity)
  have hxy2 : x / 2 < y / 2 := by nlinarith
  exact Real.sqrt_lt_sqrt hx2 hxy2

/-- Observable source liability AUC under the exact LTM map. -/
noncomputable def sourceLiabilityAUCFromObservables (r2Source : ℝ) : ℝ :=
  liabilityAUCFromSNR (sourceVarianceFromR2 r2Source)

/-- Observable target liability AUC under the exact LTM map. -/
noncomputable def targetLiabilityAUCFromObservables
    (r2Source fstSource fstTarget : ℝ) : ℝ :=
  liabilityAUCFromSNR
    (targetVarianceFromSource (sourceVarianceFromR2 r2Source) fstSource fstTarget)

/-- Full observable liability-AUC degradation theorem (exact LTM formula):
if drift increases (`fstTarget > fstSource`), target AUC is strictly lower than source AUC. -/
theorem targetLiabilityAUC_lt_source_of_observables
    (r2Source fstSource fstTarget : ℝ)
    (h_r2 : 0 < r2Source ∧ r2Source < 1)
    (h_fst : fstSource < fstTarget)
    (h_fst_bounds : 0 ≤ fstSource ∧ fstTarget < 1)
    (hPhiStrict : StrictMono Phi) :
    targetLiabilityAUCFromObservables r2Source fstSource fstTarget <
      sourceLiabilityAUCFromObservables r2Source := by
  rcases h_fst_bounds with ⟨_, hfstT_lt_one⟩
  have hvS_pos : 0 < sourceVarianceFromR2 r2Source :=
    sourceVarianceFromR2_pos r2Source h_r2
  have hvT_pos :
      0 < targetVarianceFromSource (sourceVarianceFromR2 r2Source) fstSource fstTarget :=
    targetVarianceFromSource_pos (sourceVarianceFromR2 r2Source)
      fstSource fstTarget hvS_pos h_fst hfstT_lt_one
  have hvT_lt :
      targetVarianceFromSource (sourceVarianceFromR2 r2Source) fstSource fstTarget
        < sourceVarianceFromR2 r2Source :=
    targetVarianceFromSource_lt_source (sourceVarianceFromR2 r2Source)
      fstSource fstTarget hvS_pos h_fst hfstT_lt_one
  have hmono := liabilityAUCFromSNR_strictMonoOn_nonneg hPhiStrict
  unfold targetLiabilityAUCFromObservables sourceLiabilityAUCFromObservables
  exact hmono (by exact le_of_lt hvT_pos) (by exact le_of_lt hvS_pos) hvT_lt

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

/-- Drift transport ratio is nonneg when both drifts are below 1. -/
theorem driftTransportRatio_nonneg
    (fstSource fstTarget : ℝ)
    (hS : fstSource < 1) (hT : fstTarget ≤ 1) :
    0 ≤ driftTransportRatio fstSource fstTarget := by
  unfold driftTransportRatio
  exact div_nonneg (by linarith) (by linarith)

/-- Drift transport ratio is strictly below 1 when target has more drift. -/
theorem driftTransportRatio_lt_one
    (fstSource fstTarget : ℝ)
    (hS : fstSource < 1)
    (hfst : fstSource < fstTarget) :
    driftTransportRatio fstSource fstTarget < 1 := by
  unfold driftTransportRatio
  rw [div_lt_one (by linarith : (0 : ℝ) < 1 - fstSource)]
  linarith

/-- At zero divergence, drift transport ratio equals 1 (no signal loss). -/
@[simp] theorem driftTransportRatio_self (fst : ℝ) (hfst : fst < 1) :
    driftTransportRatio fst fst = 1 := by
  unfold driftTransportRatio
  exact div_self (by linarith : (1 : ℝ) - fst ≠ 0)

/-- At zero divergence, target R² equals source R². -/
theorem targetR2FromObservables_self (r2Source fst : ℝ)
    (h_r2 : 0 < r2Source ∧ r2Source < 1)
    (hfst : fst < 1) :
    targetR2FromObservables r2Source fst fst = r2Source := by
  unfold targetR2FromObservables targetVarianceFromSource
  have hden : (1 : ℝ) - fst ≠ 0 := by linarith
  have hratio : (1 - fst) / (1 - fst) = 1 := div_self hden
  rw [hratio, mul_one]
  exact sourceR2_eq_r2FromVarianceScaleOne r2Source h_r2

/-- For valid prevalence `0 < π < 1`, the linear Brier approximation `π(1-π)(1-R²)`
is strictly decreasing in `R²`. -/
theorem brierFromR2_strictAnti (π : ℝ) (hπ0 : 0 < π) (hπ1 : π < 1) :
    StrictAnti (brierFromR2 π) := by
  intro r2a r2b hab
  unfold brierFromR2
  have hcoef : 0 < π * (1 - π) := mul_pos hπ0 (by linarith)
  nlinarith

/-- Strict Brier degradation: under positive drift and non-degenerate prevalence,
target Brier is strictly worse than source Brier. -/
theorem targetBrier_strict_gt_source_of_observables
    (π r2Source fstSource fstTarget : ℝ)
    (hπ0 : 0 < π) (hπ1 : π < 1)
    (h_r2 : 0 < r2Source ∧ r2Source < 1)
    (h_fst : fstSource < fstTarget)
    (h_fst_bounds : 0 ≤ fstSource ∧ fstTarget < 1) :
    sourceBrierFromObservables π r2Source <
      targetBrierFromObservables π r2Source fstSource fstTarget := by
  have hr2_drop := targetR2_lt_source_from_observables r2Source fstSource fstTarget
    h_r2 h_fst h_fst_bounds
  unfold sourceBrierFromObservables targetBrierFromObservables
  exact brierFromR2_strictAnti π hπ0 hπ1 hr2_drop

/-- Squared mean PGS difference under the pure split model. -/
noncomputable def expectedSqMeanPGSDiff_pureSplit (V_A fstS fstT : ℝ) : ℝ :=
  Var_Delta_Mu V_A (fstS + fstT)

/-- The expected squared mean PGS difference equals `2(F_S + F_T) V_A`. -/
@[simp] theorem expectedSqMeanPGSDiff_pureSplit_eq (V_A fstS fstT : ℝ) :
    expectedSqMeanPGSDiff_pureSplit V_A fstS fstT = 2 * (fstS + fstT) * V_A := by
  rfl

/-- The expected squared mean PGS difference under the IM equilibrium model:
`E[(Δμ)²] = 4δ V_A` where `δ = 1/(2M+1)`. -/
noncomputable def expectedSqMeanPGSDiff_IMEquilibrium (V_A M : ℝ) : ℝ :=
  Var_Delta_Mu V_A (2 * twoDemeIMEquilibriumDelta M)

/-- IM equilibrium squared mean difference equals `4δ V_A`. -/
@[simp] theorem expectedSqMeanPGSDiff_IMEquilibrium_eq (V_A M : ℝ) :
    expectedSqMeanPGSDiff_IMEquilibrium V_A M =
      4 * twoDemeIMEquilibriumDelta M * V_A := by
  unfold expectedSqMeanPGSDiff_IMEquilibrium Var_Delta_Mu
  ring

/-- IM equilibrium: increasing migration strictly decreases genetic differentiation. -/
theorem twoDemeIMEquilibriumDelta_strictAnti :
    StrictAnti (fun M : ℝ => twoDemeIMEquilibriumDelta M) := by
  intro a b hab
  unfold twoDemeIMEquilibriumDelta
  have ha : 0 < 2 * a + 1 := by linarith
  have hb : 0 < 2 * b + 1 := by linarith
  rw [div_lt_div_iff hb ha]
  linarith

/-- Under the IM model, the mean-shift variance is strictly decreasing in migration rate
when `V_A > 0`. -/
theorem expectedSqMeanPGSDiff_IMEquilibrium_strictAnti_M
    (V_A : ℝ) (hVA : 0 < V_A) :
    StrictAnti (fun M : ℝ => expectedSqMeanPGSDiff_IMEquilibrium V_A M) := by
  intro a b hab
  simp only [expectedSqMeanPGSDiff_IMEquilibrium_eq]
  have := twoDemeIMEquilibriumDelta_strictAnti hab
  nlinarith

end PresentDayMetrics

end PortabilityDrift

end Calibrator
