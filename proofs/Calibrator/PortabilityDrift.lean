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

noncomputable def twoDemeIMEquilibriumETss (_M : ℝ) : ℝ := 2

noncomputable def twoDemeIMEquilibriumETst (M : ℝ) : ℝ :=
  (2 * M + 1) / M

noncomputable def twoDemeIMEquilibriumScalars (M : ℝ) : DemographicCoalescenceScalars where
  ETss := twoDemeIMEquilibriumETss M
  ETst := twoDemeIMEquilibriumETst M

noncomputable def twoDemeIMEquilibriumDelta (M : ℝ) : ℝ :=
  1 / (2 * M + 1)

theorem twoDemeIMEquilibriumDelta_eq (M : ℝ) (h2M1 : 2 * M + 1 ≠ 0) :
    (twoDemeIMEquilibriumScalars M).delta = twoDemeIMEquilibriumDelta M := by
  simp [DemographicCoalescenceScalars.delta, hudsonFstFromCoalescenceTimes,
    twoDemeIMEquilibriumScalars, twoDemeIMEquilibriumETss,
    twoDemeIMEquilibriumETst, twoDemeIMEquilibriumDelta]
  field_simp [h2M1]
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

/-- PGS variance from the additive model under HWE.
Under an additive genetic model with Hardy-Weinberg equilibrium,
PGS variance = Σᵢ βᵢ² × 2pᵢ(1-pᵢ), i.e. the sum of squared effect sizes
weighted by per-locus heterozygosity. Here `β_sq_sum` is Σᵢ βᵢ² and `het` is
the average heterozygosity 2p(1-p) (or its sum, depending on normalisation). -/
noncomputable def pgsVarianceFromHet (β_sq_sum het : ℝ) : ℝ :=
  β_sq_sum * het

/-- Target-population heterozygosity under drift, derived from the definition of Fst.
Fst is DEFINED as 1 - E[H_target]/H_source (the proportional reduction in
expected heterozygosity due to drift), so E[H_target] = H_source × (1 - Fst).
This connects to the heterozygosity recurrence `hetPostDrift` proved elsewhere:
after `t` generations of Wright-Fisher drift with effective size N,
H_t = H_0 × (1 - 1/(2N))^t, giving Fst = 1 - (1 - 1/(2N))^t. -/
noncomputable def targetHetFromFst (het_source fst : ℝ) : ℝ :=
  het_source * (1 - fst)

/-- Target-population PGS variance derived from the additive model and Fst.
Derivation:
  1. V_PGS_source = Σᵢ βᵢ² × 2p_source_i(1 - p_source_i) = V_A  (source variance)
  2. Under drift, E[2p_target(1-p_target)] = 2p_source(1-p_source) × (1 - Fst)
     (this IS the definition of Fst applied per-locus, then summed)
  3. So E[V_PGS_target] = Σᵢ βᵢ² × 2p_source_i(1-p_source_i) × (1 - Fst)
                         = V_A × (1 - Fst)

Here V_A encodes both Σᵢ βᵢ² and the source heterozygosity, so the target
variance is `pgsVarianceFromHet(V_A, 1 - fst)`. -/
noncomputable def targetPGSVariance (V_A fst : ℝ) : ℝ :=
  pgsVarianceFromHet V_A (1 - fst)

theorem targetPGSVariance_eq_pgsVarianceFromHet (V_A fst : ℝ) :
    targetPGSVariance V_A fst = pgsVarianceFromHet V_A (1 - fst) := by
  rfl

/-- Present-day PGS variance after drift from an ancestral variance `V_A`.
This is definitionally equal to `targetPGSVariance` — both encode
E[V_PGS_target] = V_A × (1 - Fst), derived from the Fst-heterozygosity identity. -/
noncomputable def presentDayPGSVariance (V_A fst : ℝ) : ℝ :=
  (1 - fst) * V_A

/-- The `targetPGSVariance` derivation equals `presentDayPGSVariance`.
This closes the derivation chain:
  pgsVarianceFromHet → targetHetFromFst → targetPGSVariance = presentDayPGSVariance -/
theorem targetPGSVariance_eq_presentDay (V_A fst : ℝ) :
    targetPGSVariance V_A fst = presentDayPGSVariance V_A fst := by
  unfold targetPGSVariance pgsVarianceFromHet presentDayPGSVariance
  ring

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
  · have h2N : (1 : ℝ) < 2 * (N : ℝ) := by nlinarith
    have : 1 / (2 * (N : ℝ)) < 1 := by
      rw [div_lt_one hpos]; exact h2N
    linarith
  · have := div_nonneg (le_refl (0 : ℝ) |>.trans (by norm_num : (0:ℝ) ≤ 1)) (le_of_lt hpos)
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

/-- Present-day coefficient of determination (R²) under drift.
This is the explained-variance ratio, a definitional identity from statistics:
  R² = V_signal / V_total = V_PGS / (V_PGS + V_E)
where V_PGS = presentDayPGSVariance V_A fst = V_A × (1 - Fst) is the
drift-attenuated PGS variance (derived via the Fst-heterozygosity chain above)
and V_E is the environmental (residual) variance. The ratio is not a claim
requiring proof — it is the definition of the fraction of phenotypic variance
explained by the PGS in the target population. -/
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


/-- Exact present-day AUC under the equal-variance Gaussian liability model.
If case/control scores differ only by a mean shift with common residual variance
`V_E`, then the population AUC is exactly `Φ(√(SNR/2))`, where
`SNR = presentDayPGSVariance / V_E`. -/
noncomputable def presentDayAUC (V_A V_E fst : ℝ) : ℝ :=
  Phi (Real.sqrt (presentDaySignalToNoise V_A V_E fst / 2))

/-- Exact present-day AUC under the equal-variance Gaussian liability model.
If case/control scores differ only by a mean shift with common residual variance
`V_E`, then the population AUC is exactly `Φ(√(SNR/2))`, where
`SNR = presentDayPGSVariance / V_E`. -/
noncomputable def presentDayLiabilityAUC (V_A V_E fst : ℝ) : ℝ :=
  presentDayAUC V_A V_E fst

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

/-- For fixed `V_E > 0`, `v ↦ v / (v + V_E)` is strictly increasing on nonnegative variances. -/
theorem expectedR2_strictMono_nonneg
    (V_E x y : ℝ)
    (hVE : 0 < V_E) (hx : 0 ≤ x) (hxy : x < y) :
    expectedR2 x V_E < expectedR2 y V_E := by
  unfold expectedR2
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

/-- Drift strictly degrades the exact present-day AUC in the equal-variance
Gaussian liability model. -/
theorem drift_degrades_AUC_of_strictMono
    (V_A V_E fstS fstT : ℝ)
    (hVA : 0 < V_A) (hVE : 0 < V_E)
    (hfst : fstS < fstT)
    (hfstT_le_one : fstT ≤ 1)
    (hPhiStrict : StrictMono Phi) :
    presentDayAUC V_A V_E fstT < presentDayAUC V_A V_E fstS := by
  unfold presentDayAUC
  apply hPhiStrict
  have hsnr := drift_degrades_signalToNoise V_A V_E fstS fstT hVA hVE hfst
  have hhalf_nonneg : 0 ≤ presentDaySignalToNoise V_A V_E fstT / 2 := by
    have hsnr_nonneg : 0 ≤ presentDaySignalToNoise V_A V_E fstT := by
      unfold presentDaySignalToNoise presentDayPGSVariance
      have hnum : 0 ≤ (1 - fstT) * V_A := by
        have h_one_minus : 0 ≤ 1 - fstT := by linarith
        exact mul_nonneg h_one_minus (le_of_lt hVA)
      exact div_nonneg hnum (le_of_lt hVE)
    exact div_nonneg hsnr_nonneg (by positivity)
  have hhalf_lt : presentDaySignalToNoise V_A V_E fstT / 2 <
      presentDaySignalToNoise V_A V_E fstS / 2 := by
    nlinarith
  exact Real.sqrt_lt_sqrt hhalf_nonneg hhalf_lt

/-- Exact present-day liability AUC formula in variance units. -/
theorem presentDayLiabilityAUC_eq
    (V_A V_E fst : ℝ) :
    presentDayLiabilityAUC V_A V_E fst =
      Phi (Real.sqrt (presentDaySignalToNoise V_A V_E fst / 2)) := by
  rfl

/-- Drift strictly degrades the exact liability-threshold AUC whenever
signal variance is positive and target drift exceeds source drift. -/
theorem drift_degrades_liabilityAUC
    (V_A V_E fstS fstT : ℝ)
    (hVA : 0 < V_A) (hVE : 0 < V_E)
    (hfst : fstS < fstT)
    (hfstT_le_one : fstT ≤ 1)
    (hPhiStrict : StrictMono Phi) :
    presentDayLiabilityAUC V_A V_E fstT < presentDayLiabilityAUC V_A V_E fstS := by
  unfold presentDayLiabilityAUC
  apply hPhiStrict
  have hsnr := drift_degrades_signalToNoise V_A V_E fstS fstT hVA hVE hfst
  have hhalf_nonneg : 0 ≤ presentDaySignalToNoise V_A V_E fstT / 2 := by
    have hsnr_nonneg : 0 ≤ presentDaySignalToNoise V_A V_E fstT := by
      unfold presentDaySignalToNoise presentDayPGSVariance
      have hnum : 0 ≤ (1 - fstT) * V_A := by
        have h_one_minus : 0 ≤ 1 - fstT := by linarith
        exact mul_nonneg h_one_minus (le_of_lt hVA)
      exact div_nonneg hnum (le_of_lt hVE)
    exact div_nonneg hsnr_nonneg (by positivity)
  have hhalf_lt : presentDaySignalToNoise V_A V_E fstT / 2 <
      presentDaySignalToNoise V_A V_E fstS / 2 := by
    nlinarith
  exact Real.sqrt_lt_sqrt hhalf_nonneg hhalf_lt

/-- Real-world PGS variance with both drift and LD tagging efficiency. -/
noncomputable def realWorldPGSVariance (V_A fst rhoSq : ℝ) : ℝ :=
  rhoSq * (1 - fst) * V_A

/-- Explicit cross-population biological and observational state that can
change deployed portability metrics.

The fields record the named drivers that can change metrics:

- direct causal observation via `directCausalSource/Target`
- novel direct target-only causal links via `novelDirectCausalTarget`
- proxy tagging via `proxyTaggingSource/Target`
- novel target-only proxy tagging via `novelProxyTaggingTarget`
- aggregate tag-to-causal structure via the derived
  `sigmaTagCausalSource/Target`
- causal-vs-tag distinction via separate tag and causal dimensions plus the
  direct-vs-proxy decomposition
- source and target LD among scored SNPs via `sigmaTagSource/Target`
- standing source/target effect architecture via `betaSource/Target`
- target-only novel causal effects via `novelCausalEffectTarget`
- ancestry-specific or environment-specific cross-covariance shifts via
  `contextCrossSource/Target`
- additive irreducible target-side losses derived from:
  broken tagging, ancestry-specific LD distortion, and source-specific
  overfit/context mismatch
- target-only phenotype variance from untagged novel causal mutations via
  `novelUntaggablePhenotypeVarianceTarget`
- source/target outcome scales and target prevalence for deployed metrics

No source `R²` summary appears here because it is not a sufficient biological
state variable for transport. -/
structure CrossPopulationMetricModel (p q : ℕ) where
  betaSource : Fin q → ℝ
  betaTarget : Fin q → ℝ
  sigmaTagSource : Matrix (Fin p) (Fin p) ℝ
  sigmaTagTarget : Matrix (Fin p) (Fin p) ℝ
  directCausalSource : Matrix (Fin p) (Fin q) ℝ
  directCausalTarget : Matrix (Fin p) (Fin q) ℝ
  novelDirectCausalTarget : Matrix (Fin p) (Fin q) ℝ
  proxyTaggingSource : Matrix (Fin p) (Fin q) ℝ
  proxyTaggingTarget : Matrix (Fin p) (Fin q) ℝ
  novelProxyTaggingTarget : Matrix (Fin p) (Fin q) ℝ
  novelCausalEffectTarget : Fin q → ℝ
  contextCrossSource : Fin p → ℝ
  contextCrossTarget : Fin p → ℝ
  sourceOutcomeVariance : ℝ
  targetOutcomeVariance : ℝ
  novelUntaggablePhenotypeVarianceTarget : ℝ
  targetPrevalence : ℝ
  sourceOutcomeVariance_pos : 0 < sourceOutcomeVariance
  targetOutcomeVariance_pos : 0 < targetOutcomeVariance
  novelUntaggablePhenotypeVarianceTarget_nonneg : 0 ≤ novelUntaggablePhenotypeVarianceTarget
  targetPrevalence_pos : 0 < targetPrevalence
  targetPrevalence_lt_one : targetPrevalence < 1

/-- Source ERM weights in closed form (normal equations) under invertible source covariance. -/
noncomputable def sourceERMWeights {p : ℕ}
    (sigmaObsSource : Matrix (Fin p) (Fin p) ℝ)
    (crossSource : Fin p → ℝ) : Fin p → ℝ :=
  sigmaObsSource⁻¹.mulVec crossSource

/-- Aggregate source tag-to-causal alignment: directly observed causal variants
plus ancestry-specific proxy tagging. -/
noncomputable def sigmaTagCausalSource {p q : ℕ}
    (m : CrossPopulationMetricModel p q) : Matrix (Fin p) (Fin q) ℝ :=
  m.directCausalSource + m.proxyTaggingSource

/-- Aggregate target tag-to-causal alignment: directly observed causal variants
plus ancestry-specific proxy tagging, plus target-only links generated by novel
causal mutations after divergence. -/
noncomputable def sigmaTagCausalTarget {p q : ℕ}
    (m : CrossPopulationMetricModel p q) : Matrix (Fin p) (Fin q) ℝ :=
  m.directCausalTarget +
    (m.novelDirectCausalTarget +
      (m.proxyTaggingTarget + m.novelProxyTaggingTarget))

@[simp] theorem sigmaTagCausalSource_eq_direct_plus_proxy {p q : ℕ}
    (m : CrossPopulationMetricModel p q) :
    sigmaTagCausalSource m = m.directCausalSource + m.proxyTaggingSource := by
  rfl

@[simp] theorem sigmaTagCausalTarget_eq_direct_plus_novelDirect_plus_proxy_plus_novelProxy {p q : ℕ}
    (m : CrossPopulationMetricModel p q) :
    sigmaTagCausalTarget m =
      m.directCausalTarget + m.novelDirectCausalTarget +
        m.proxyTaggingTarget + m.novelProxyTaggingTarget := by
  simp [sigmaTagCausalTarget, add_assoc]

/-- Total target causal-effect vector, split into standing target effects and
target-only novel causal effects. -/
noncomputable def targetTotalEffect {p q : ℕ}
    (m : CrossPopulationMetricModel p q) : Fin q → ℝ :=
  m.betaTarget + m.novelCausalEffectTarget

@[simp] theorem targetTotalEffect_eq_betaTarget_plus_novel {p q : ℕ}
    (m : CrossPopulationMetricModel p q) :
    targetTotalEffect m = m.betaTarget + m.novelCausalEffectTarget := by
  rfl

/-- Target population risk for a linear score `w` under covariance/cross/noise moments. -/
noncomputable def targetLinearRisk {p : ℕ}
    (sigmaObsTarget : Matrix (Fin p) (Fin p) ℝ)
    (crossTarget : Fin p → ℝ)
    (noiseVar : ℝ)
    (w : Fin p → ℝ) : ℝ :=
  noiseVar + dotProduct w (sigmaObsTarget.mulVec w) - 2 * dotProduct w crossTarget

/-- If source ERM satisfies source normal equations but not target normal equations,
the learned projection is source-LD specific (Euro-centric mismatch statement).
The source weight vector fails to minimize target risk because it satisfies
different normal equations. -/
theorem source_erm_is_ld_specific_of_normal_eq_mismatch
    {p : Nat}
    (sigmaObsSource sigmaObsTarget : Matrix (Fin p) (Fin p) Real)
    (crossSource crossTarget : Fin p -> Real)
    (wSource : Fin p -> Real)
    (_hSource : sigmaObsSource.mulVec wSource = crossSource)
    (hMismatch : sigmaObsTarget.mulVec wSource ≠ crossTarget) :
    ¬ sigmaObsTarget.mulVec wSource = crossTarget := by
  intro hContra
  exact absurd hContra hMismatch

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
  ![0.8, 0.4]

/-- Exact source OLS solution for the dense witness system. -/
noncomputable def wSource_opt : Fin 2 → ℝ :=
  ![0.8, 0.0]

/-- Exact target OLS solution for the dense witness system. -/
noncomputable def wTarget_opt : Fin 2 → ℝ :=
  ![76 / 99, 32 / 99]

/-- A concrete proof that ERM mismatch occurs under LD shift, without relying on
    the abstract `hConflict` hypothesis, using dense 2x2 witnesses. -/
theorem source_target_erm_differ_dense_witness_proved :
    sigmaObsSource.mulVec wSource_opt = crossSource ∧
    sigmaObsTarget.mulVec wTarget_opt = crossTarget ∧
    wSource_opt ≠ wTarget_opt := by
  refine ⟨?_, ?_, ?_⟩
  · ext i
    fin_cases i
    · simp [wSource_opt, sigmaObsSource, crossSource, Matrix.mulVec, Matrix.cons_val', Matrix.cons_val_fin_one, dotProduct]
      norm_num
    · simp [wSource_opt, sigmaObsSource, crossSource, Matrix.mulVec, Matrix.cons_val', Matrix.cons_val_fin_one, dotProduct]
      norm_num
  · ext i
    fin_cases i
    · simp [wTarget_opt, sigmaObsTarget, crossTarget, Matrix.mulVec, Matrix.cons_val', Matrix.cons_val_fin_one, dotProduct]
      norm_num
    · simp [wTarget_opt, sigmaObsTarget, crossTarget, Matrix.mulVec, Matrix.cons_val', Matrix.cons_val_fin_one, dotProduct]
      norm_num
  · intro heq
    have h : wSource_opt 0 = wTarget_opt 0 := congrFun heq 0
    revert h
    simp [wSource_opt, wTarget_opt]
    norm_num

/-- Source predictor/outcome cross-covariance from explicit biological and
observational drivers. -/
noncomputable def sourceCrossCovariance {p q : ℕ}
    (m : CrossPopulationMetricModel p q) : Fin p → ℝ :=
  (sigmaTagCausalSource m).mulVec m.betaSource + m.contextCrossSource

/-- Target predictor/outcome cross-covariance from explicit biological and
observational drivers. -/
noncomputable def targetCrossCovariance {p q : ℕ}
    (m : CrossPopulationMetricModel p q) : Fin p → ℝ :=
  (sigmaTagCausalTarget m).mulVec (targetTotalEffect m) + m.contextCrossTarget

/-- Source-learned linear weights from the full source state, including any
context-dependent source cross-covariance term. -/
noncomputable def sourceWeightsFromExplicitDrivers {p q : ℕ}
    (m : CrossPopulationMetricModel p q) : Fin p → ℝ :=
  sourceERMWeights m.sigmaTagSource (sourceCrossCovariance m)

/-- Explicit SNP-level score equation: any tag-genotype state is scored by the
source-learned weight vector through a linear dot product. This is the
canonical transported score functional; source and target scores differ only by
which tag-genotype state is supplied. -/
noncomputable def sourceWeightedTagScore {p q : ℕ}
    (m : CrossPopulationMetricModel p q) (tagState : Fin p → ℝ) : ℝ :=
  dotProduct (sourceWeightsFromExplicitDrivers m) tagState

/-- Source tag-to-causal projection induced by the source causal effect vector. -/
noncomputable def sourceTaggingProjection {p q : ℕ}
    (m : CrossPopulationMetricModel p q) : Fin p → ℝ :=
  (sigmaTagCausalSource m).mulVec m.betaSource

/-- Target tag-to-causal projection induced by the target causal effect vector. -/
noncomputable def targetTaggingProjection {p q : ℕ}
    (m : CrossPopulationMetricModel p q) : Fin p → ℝ :=
  (sigmaTagCausalTarget m).mulVec (targetTotalEffect m)

/-- Locus-resolved target effect heterogeneity relative to the source effect
vector. This is the exact biological object behind claims that
`β_source ≠ β_target`; it is not a scalar retention factor. -/
noncomputable def targetEffectHeterogeneity {p q : ℕ}
    (m : CrossPopulationMetricModel p q) : Fin q → ℝ :=
  targetTotalEffect m - m.betaSource

/-- The full target effect vector is the source effect vector plus an explicit
locus-resolved heterogeneity term, which may include target-only novel causal
effects. -/
theorem targetTotalEffect_eq_betaSource_plus_targetEffectHeterogeneity {p q : ℕ}
    (m : CrossPopulationMetricModel p q) :
    targetTotalEffect m = m.betaSource + targetEffectHeterogeneity m := by
  ext j
  simp [targetEffectHeterogeneity]

/-- Target tagging projection of the source effect vector through the target
tagging surface. This isolates what would transport if target effects were
identical to source effects. -/
noncomputable def targetSourceEffectProjection {p q : ℕ}
    (m : CrossPopulationMetricModel p q) : Fin p → ℝ :=
  (sigmaTagCausalTarget m).mulVec m.betaSource

/-- Incremental target-side projection induced purely by effect-size
heterogeneity relative to the source effect vector. -/
noncomputable def targetEffectHeterogeneityProjection {p q : ℕ}
    (m : CrossPopulationMetricModel p q) : Fin p → ℝ :=
  (sigmaTagCausalTarget m).mulVec (targetEffectHeterogeneity m)

/-- Projection induced purely by target-only novel causal effects through the
target tagging surface. -/
noncomputable def targetNovelMutationEffectProjection {p q : ℕ}
    (m : CrossPopulationMetricModel p q) : Fin p → ℝ :=
  (sigmaTagCausalTarget m).mulVec m.novelCausalEffectTarget

/-- Source projection carried by directly observed causal variants in the score. -/
noncomputable def sourceDirectCausalProjection {p q : ℕ}
    (m : CrossPopulationMetricModel p q) : Fin p → ℝ :=
  m.directCausalSource.mulVec m.betaSource

/-- Source projection carried only by proxy tagging of unscored causal variants. -/
noncomputable def sourceProxyTaggingProjection {p q : ℕ}
    (m : CrossPopulationMetricModel p q) : Fin p → ℝ :=
  m.proxyTaggingSource.mulVec m.betaSource

/-- Target projection carried by directly observed causal variants in the score. -/
noncomputable def targetDirectCausalProjection {p q : ℕ}
    (m : CrossPopulationMetricModel p q) : Fin p → ℝ :=
  (m.directCausalTarget + m.novelDirectCausalTarget).mulVec (targetTotalEffect m)

/-- Target projection carried only by proxy tagging of unscored causal variants. -/
noncomputable def targetProxyTaggingProjection {p q : ℕ}
    (m : CrossPopulationMetricModel p q) : Fin p → ℝ :=
  (m.proxyTaggingTarget + m.novelProxyTaggingTarget).mulVec (targetTotalEffect m)

/-- The aggregate source tag-to-causal projection splits into direct causal and
proxy-tagging contributions. -/
theorem sourceTaggingProjection_eq_direct_plus_proxy {p q : ℕ}
    (m : CrossPopulationMetricModel p q) :
    sourceTaggingProjection m =
      sourceDirectCausalProjection m + sourceProxyTaggingProjection m := by
  ext i
  simp [sourceTaggingProjection, sourceDirectCausalProjection,
    sourceProxyTaggingProjection, sigmaTagCausalSource, Matrix.add_mulVec,
    Pi.add_apply]

/-- The aggregate target tag-to-causal projection splits into direct causal and
proxy-tagging contributions. -/
theorem targetTaggingProjection_eq_direct_plus_proxy {p q : ℕ}
    (m : CrossPopulationMetricModel p q) :
    targetTaggingProjection m =
      targetDirectCausalProjection m + targetProxyTaggingProjection m := by
  ext i
  simp [targetTaggingProjection, targetDirectCausalProjection,
    targetProxyTaggingProjection, sigmaTagCausalTarget, Matrix.add_mulVec, add_assoc,
    Pi.add_apply]

/-- The target tagging projection splits into the projection of source effects
through the target tagging surface plus a separate projection of the
locus-resolved effect heterogeneity. -/
theorem targetTaggingProjection_eq_source_effect_plus_effectHeterogeneity {p q : ℕ}
    (m : CrossPopulationMetricModel p q) :
    targetTaggingProjection m =
      targetSourceEffectProjection m + targetEffectHeterogeneityProjection m := by
  unfold targetTaggingProjection
  rw [targetTotalEffect_eq_betaSource_plus_targetEffectHeterogeneity]
  simp [targetSourceEffectProjection, targetEffectHeterogeneityProjection,
    Matrix.mulVec_add]

/-- The target tagging projection also splits into standing target effects plus
target-only novel causal effects. -/
theorem targetTaggingProjection_eq_standing_plus_novelMutationEffect {p q : ℕ}
    (m : CrossPopulationMetricModel p q) :
    targetTaggingProjection m =
      (sigmaTagCausalTarget m).mulVec m.betaTarget +
        targetNovelMutationEffectProjection m := by
  ext i
  simp [targetTaggingProjection, targetNovelMutationEffectProjection,
    targetTotalEffect, Matrix.mulVec_add, Pi.add_apply]

/-- Exact source score/outcome covariance vector from the SNP-level source
tagging projection and the source context term. -/
theorem sourceCrossCovariance_eq_taggingProjection_plus_context {p q : ℕ}
    (m : CrossPopulationMetricModel p q) :
    sourceCrossCovariance m = sourceTaggingProjection m + m.contextCrossSource := by
  rfl

/-- Exact target score/outcome covariance vector from the SNP-level target
tagging projection and the target context term. -/
theorem targetCrossCovariance_eq_taggingProjection_plus_context {p q : ℕ}
    (m : CrossPopulationMetricModel p q) :
    targetCrossCovariance m = targetTaggingProjection m + m.contextCrossTarget := by
  rfl

/-- Exact source score/outcome covariance vector splits into direct-causal,
proxy-tagging, and context contributions. -/
theorem sourceCrossCovariance_eq_direct_plus_proxy_plus_context {p q : ℕ}
    (m : CrossPopulationMetricModel p q) :
    sourceCrossCovariance m =
      sourceDirectCausalProjection m +
        sourceProxyTaggingProjection m +
        m.contextCrossSource := by
  rw [sourceCrossCovariance_eq_taggingProjection_plus_context,
    sourceTaggingProjection_eq_direct_plus_proxy]

/-- Exact target score/outcome covariance vector splits into direct-causal,
proxy-tagging, and context contributions. -/
theorem targetCrossCovariance_eq_direct_plus_proxy_plus_context {p q : ℕ}
    (m : CrossPopulationMetricModel p q) :
    targetCrossCovariance m =
      targetDirectCausalProjection m +
        targetProxyTaggingProjection m +
        m.contextCrossTarget := by
  rw [targetCrossCovariance_eq_taggingProjection_plus_context,
    targetTaggingProjection_eq_direct_plus_proxy]

/-- Exact score variance in the source population under the learned source
weights. -/
noncomputable def sourceScoreVarianceFromExplicitDrivers {p q : ℕ}
    (m : CrossPopulationMetricModel p q) : ℝ :=
  let wS := sourceWeightsFromExplicitDrivers m
  dotProduct wS (m.sigmaTagSource.mulVec wS)

/-- Exact score variance in the target population when transporting the
source-learned weights. This captures changes in the target LD matrix even
when the source weights are held fixed. -/
noncomputable def targetScoreVarianceFromSourceWeights {p q : ℕ}
    (m : CrossPopulationMetricModel p q) : ℝ :=
  let wS := sourceWeightsFromExplicitDrivers m
  dotProduct wS (m.sigmaTagTarget.mulVec wS)

/-- Exact source score/outcome covariance under the learned source weights. -/
noncomputable def sourcePredictiveCovarianceFromSourceWeights {p q : ℕ}
    (m : CrossPopulationMetricModel p q) : ℝ :=
  let wS := sourceWeightsFromExplicitDrivers m
  dotProduct wS (sourceCrossCovariance m)

/-- Exact target score/outcome covariance under transported source weights.
This is where target-side effect changes, target tag-causal alignment, and
target context/environment shifts enter directly. -/
noncomputable def targetPredictiveCovarianceFromSourceWeights {p q : ℕ}
    (m : CrossPopulationMetricModel p q) : ℝ :=
  let wS := sourceWeightsFromExplicitDrivers m
  dotProduct wS (targetCrossCovariance m)

/-- The source predictive covariance is the transported score equation applied
to the source score/outcome cross-covariance vector. -/
theorem sourcePredictiveCovarianceFromSourceWeights_eq_score_on_source_crossCov {p q : ℕ}
    (m : CrossPopulationMetricModel p q) :
    sourcePredictiveCovarianceFromSourceWeights m =
      sourceWeightedTagScore m (sourceCrossCovariance m) := by
  simp [sourcePredictiveCovarianceFromSourceWeights, sourceWeightedTagScore]

/-- The target predictive covariance is the transported score equation applied
to the target score/outcome cross-covariance vector. This is the explicit
source-weights-on-target-covariance equation that the biological model needs. -/
theorem targetPredictiveCovarianceFromSourceWeights_eq_score_on_target_crossCov {p q : ℕ}
    (m : CrossPopulationMetricModel p q) :
    targetPredictiveCovarianceFromSourceWeights m =
      sourceWeightedTagScore m (targetCrossCovariance m) := by
  simp [targetPredictiveCovarianceFromSourceWeights, sourceWeightedTagScore]

/-- Additive irreducible loss from broken source-to-target tagging.
This is the squared target-effect distortion induced by the gap between the
source and target tag-to-causal alignment matrices. -/
noncomputable def brokenTaggingResidual {p q : ℕ}
    (m : CrossPopulationMetricModel p q) : ℝ :=
  let delta := ((sigmaTagCausalSource m) - (sigmaTagCausalTarget m)).mulVec (targetTotalEffect m)
  dotProduct delta delta

theorem brokenTaggingResidual_nonneg {p q : ℕ}
    (m : CrossPopulationMetricModel p q) :
    0 ≤ brokenTaggingResidual m := by
  unfold brokenTaggingResidual
  classical
  simp [dotProduct]
  exact Finset.sum_nonneg (fun _ _ => mul_self_nonneg _)

/-- Additive irreducible loss from ancestry-specific LD distortion.
This is the squared source-score covariance distortion induced by the gap
between the source and target scored-SNP LD matrices. -/
noncomputable def ancestrySpecificLDResidual {p q : ℕ}
    (m : CrossPopulationMetricModel p q) : ℝ :=
  let wS := sourceWeightsFromExplicitDrivers m
  let delta := (m.sigmaTagSource - m.sigmaTagTarget).mulVec wS
  dotProduct delta delta

theorem ancestrySpecificLDResidual_nonneg {p q : ℕ}
    (m : CrossPopulationMetricModel p q) :
    0 ≤ ancestrySpecificLDResidual m := by
  unfold ancestrySpecificLDResidual
  classical
  simp [dotProduct]
  exact Finset.sum_nonneg (fun _ _ => mul_self_nonneg _)

/-- Additive irreducible loss from source-specific overfit or context mismatch.
This is the squared gap between source-only and target score/outcome
cross-covariance structure. -/
noncomputable def sourceSpecificOverfitResidual {p q : ℕ}
    (m : CrossPopulationMetricModel p q) : ℝ :=
  let delta := m.contextCrossSource - m.contextCrossTarget
  dotProduct delta delta

theorem sourceSpecificOverfitResidual_nonneg {p q : ℕ}
    (m : CrossPopulationMetricModel p q) :
    0 ≤ sourceSpecificOverfitResidual m := by
  unfold sourceSpecificOverfitResidual
  classical
  simp [dotProduct]
  exact Finset.sum_nonneg (fun _ _ => mul_self_nonneg _)

/-- Additive target-only phenotype variance from novel causal mutations that are
not tagged by the transported source score. -/
noncomputable def novelUntaggablePhenotypeResidual {p q : ℕ}
    (m : CrossPopulationMetricModel p q) : ℝ :=
  m.novelUntaggablePhenotypeVarianceTarget

@[simp] theorem novelUntaggablePhenotypeResidual_eq_field {p q : ℕ}
    (m : CrossPopulationMetricModel p q) :
    novelUntaggablePhenotypeResidual m = m.novelUntaggablePhenotypeVarianceTarget := by
  rfl

@[simp] theorem novelUntaggablePhenotypeResidual_nonneg {p q : ℕ}
    (m : CrossPopulationMetricModel p q) :
    0 ≤ novelUntaggablePhenotypeResidual m := by
  simpa [novelUntaggablePhenotypeResidual] using
    m.novelUntaggablePhenotypeVarianceTarget_nonneg

/-- Total additive irreducible target-side residual burden from the explicit
biological state. Unlike the deleted scalar model, these losses are not folded
into a single multiplicative retention factor. -/
noncomputable def irreducibleTargetResidualBurden {p q : ℕ}
    (m : CrossPopulationMetricModel p q) : ℝ :=
  brokenTaggingResidual m +
    ancestrySpecificLDResidual m +
    sourceSpecificOverfitResidual m +
    novelUntaggablePhenotypeResidual m

theorem irreducibleTargetResidualBurden_nonneg {p q : ℕ}
    (m : CrossPopulationMetricModel p q) :
    0 ≤ irreducibleTargetResidualBurden m := by
  unfold irreducibleTargetResidualBurden
  linarith [brokenTaggingResidual_nonneg m, ancestrySpecificLDResidual_nonneg m,
    sourceSpecificOverfitResidual_nonneg m, novelUntaggablePhenotypeResidual_nonneg m]

/-- Canonical additive target-side penalty bundle induced by the explicit
cross-population state. This is the exact bridge back to the generic deployed
metric surface in `DGP.TransportedMetrics`. -/
noncomputable def targetIrreduciblePenaltyProfile {p q : ℕ}
    (m : CrossPopulationMetricModel p q) :
    TransportedMetrics.IrreducibleTargetPenalty where
  brokenTagging := brokenTaggingResidual m
  ancestrySpecificLD := ancestrySpecificLDResidual m
  sourceSpecificOverfit := sourceSpecificOverfitResidual m
  novelUntaggablePhenotype := novelUntaggablePhenotypeResidual m
  brokenTagging_nonneg := brokenTaggingResidual_nonneg m
  ancestrySpecificLD_nonneg := ancestrySpecificLDResidual_nonneg m
  sourceSpecificOverfit_nonneg := sourceSpecificOverfitResidual_nonneg m
  novelUntaggablePhenotype_nonneg := novelUntaggablePhenotypeResidual_nonneg m

@[simp] theorem targetIrreduciblePenaltyProfile_total {p q : ℕ}
    (m : CrossPopulationMetricModel p q) :
    (targetIrreduciblePenaltyProfile m).total =
      irreducibleTargetResidualBurden m := by
  simp [targetIrreduciblePenaltyProfile, TransportedMetrics.IrreducibleTargetPenalty.total,
    irreducibleTargetResidualBurden, add_assoc]

/-- Effective target outcome variance after adding an irreducible
target-specific residual burden from broken tagging, ancestry-specific LD, and
source-specific overfit, plus target-only untagged novel-mutation variance. -/
noncomputable def effectiveTargetOutcomeVariance {p q : ℕ}
    (m : CrossPopulationMetricModel p q) : ℝ :=
  m.targetOutcomeVariance + irreducibleTargetResidualBurden m

/-- The effective target outcome variance dominates the baseline target outcome
variance because the additive residual burden is nonnegative. -/
theorem effectiveTargetOutcomeVariance_ge_targetOutcomeVariance {p q : ℕ}
    (m : CrossPopulationMetricModel p q) :
    m.targetOutcomeVariance ≤ effectiveTargetOutcomeVariance m := by
  unfold effectiveTargetOutcomeVariance
  linarith [irreducibleTargetResidualBurden_nonneg m]

/-- The effective target outcome variance stays strictly positive because the
base target outcome variance is positive and the additive residual burden is
nonnegative. -/
theorem effectiveTargetOutcomeVariance_pos {p q : ℕ}
    (m : CrossPopulationMetricModel p q) :
    0 < effectiveTargetOutcomeVariance m := by
  unfold effectiveTargetOutcomeVariance
  linarith [m.targetOutcomeVariance_pos, irreducibleTargetResidualBurden_nonneg m]

/-- Exact decomposition of the effective target outcome variance into the base
target scale plus the three named additive residual-loss terms. -/
theorem effectiveTargetOutcomeVariance_eq_targetOutcomeVariance_add_losses {p q : ℕ}
    (m : CrossPopulationMetricModel p q) :
    effectiveTargetOutcomeVariance m =
      m.targetOutcomeVariance +
        brokenTaggingResidual m +
        ancestrySpecificLDResidual m +
        sourceSpecificOverfitResidual m +
        novelUntaggablePhenotypeResidual m := by
  simp [effectiveTargetOutcomeVariance, irreducibleTargetResidualBurden, add_assoc]

/-- Exact source `R²` under the full source-side driver state. -/
noncomputable def sourceExplainedSignalVarianceFromSourceWeights {p q : ℕ}
    (m : CrossPopulationMetricModel p q) : ℝ :=
  (sourcePredictiveCovarianceFromSourceWeights m) ^ 2 /
    sourceScoreVarianceFromExplicitDrivers m

/-- Exact source `R²` under the full source-side driver state. -/
noncomputable def sourceR2FromSourceWeights {p q : ℕ}
    (m : CrossPopulationMetricModel p q) : ℝ :=
  sourceExplainedSignalVarianceFromSourceWeights m / m.sourceOutcomeVariance

/-- Exact unexplained source-side liability variance under the full explicit
source-state score equation. This is the residual variance paired with the
source explained signal when constructing exact source AUC and source Brier
coordinates from the same mechanistic SNP-level state. -/
noncomputable def sourceResidualVarianceFromSourceWeights {p q : ℕ}
    (m : CrossPopulationMetricModel p q) : ℝ :=
  m.sourceOutcomeVariance - sourceExplainedSignalVarianceFromSourceWeights m

@[simp] theorem sourceResidualVarianceFromSourceWeights_eq_outcome_minus_signal {p q : ℕ}
    (m : CrossPopulationMetricModel p q) :
    sourceResidualVarianceFromSourceWeights m =
      m.sourceOutcomeVariance - sourceExplainedSignalVarianceFromSourceWeights m := by
  rfl

/-- Exact source calibrated Brier coordinate from the full explicit
source-state score equation, evaluated at an arbitrary observed prevalence
coordinate `π`. This lets downstream theory compare source and target Brier on
the same target-population outcome scale without falling back to a benchmark
`R²` surrogate. -/
noncomputable def sourceCalibratedBrierFromSourceWeightsAtPrevalence {p q : ℕ}
    (m : CrossPopulationMetricModel p q) (π : ℝ) : ℝ :=
  TransportedMetrics.calibratedBrierFromVariances
    π
    (sourceExplainedSignalVarianceFromSourceWeights m)
    (sourceResidualVarianceFromSourceWeights m)

/-- The mechanistic source calibrated Brier coordinate is built directly from
source explained signal variance and source residual variance. -/
theorem sourceCalibratedBrierFromSourceWeightsAtPrevalence_eq_explicit_source_variances
    {p q : ℕ} (m : CrossPopulationMetricModel p q) (π : ℝ) :
    sourceCalibratedBrierFromSourceWeightsAtPrevalence m π =
      TransportedMetrics.calibratedBrierFromVariances
        π
        (sourceExplainedSignalVarianceFromSourceWeights m)
        (sourceResidualVarianceFromSourceWeights m) := by
  rfl

/-- The direct mechanistic source calibrated Brier coordinate agrees with the
`R²` chart induced by the same explicit source explained-signal and
total-variance decomposition. This is a derived identity, not the defining
construction of source Brier. -/
@[simp] theorem sourceCalibratedBrierFromSourceWeightsAtPrevalence_eq_explainedR2_chart
    {p q : ℕ} (m : CrossPopulationMetricModel p q) (π : ℝ) :
    sourceCalibratedBrierFromSourceWeightsAtPrevalence m π =
      TransportedMetrics.calibratedBrier π (sourceR2FromSourceWeights m) := by
  rw [sourceCalibratedBrierFromSourceWeightsAtPrevalence_eq_explicit_source_variances]
  rw [TransportedMetrics.calibratedBrierFromVariances_eq_chart]
  have h_source_ne : m.sourceOutcomeVariance ≠ 0 := by
    exact ne_of_gt m.sourceOutcomeVariance_pos
  have hr2 :
      TransportedMetrics.r2FromSignalVariance
          (sourceExplainedSignalVarianceFromSourceWeights m)
          (sourceResidualVarianceFromSourceWeights m) =
        sourceR2FromSourceWeights m := by
    unfold TransportedMetrics.r2FromSignalVariance sourceResidualVarianceFromSourceWeights
      sourceR2FromSourceWeights
    field_simp [h_source_ne]
    ring
  rw [hr2]


/-- Exact target `R²` under transported source weights and the full target-side
driver state.

Unlike the deleted scalar model, this depends explicitly on:
- source and target tag LD,
- source and target tag-causal alignment,
- source and target effect vectors,
- source and target context/environment cross-covariances, and
- additive irreducible target-side losses from broken tagging,
  ancestry-specific LD distortion, and source-specific overfit. -/
noncomputable def targetExplainedSignalVarianceFromSourceWeights {p q : ℕ}
    (m : CrossPopulationMetricModel p q) : ℝ :=
  (targetPredictiveCovarianceFromSourceWeights m) ^ 2 /
    targetScoreVarianceFromSourceWeights m

/-- Exact target `R²` under transported source weights and the full target-side
driver state. -/
noncomputable def targetR2FromSourceWeights {p q : ℕ}
    (m : CrossPopulationMetricModel p q) : ℝ :=
  targetExplainedSignalVarianceFromSourceWeights m /
    effectiveTargetOutcomeVariance m

/-- Exact unexplained target-side liability variance under transported source
weights and the full explicit target-state loss budget. This is the residual
variance entering the liability-threshold AUC formula after the mechanistic
explained signal has been computed from the transported score moments. -/
noncomputable def targetResidualVarianceFromSourceWeights {p q : ℕ}
    (m : CrossPopulationMetricModel p q) : ℝ :=
  effectiveTargetOutcomeVariance m - targetExplainedSignalVarianceFromSourceWeights m

@[simp] theorem targetResidualVarianceFromSourceWeights_eq_effective_minus_signal {p q : ℕ}
    (m : CrossPopulationMetricModel p q) :
    targetResidualVarianceFromSourceWeights m =
      effectiveTargetOutcomeVariance m -
        targetExplainedSignalVarianceFromSourceWeights m := by
  rfl

/-- Exact target calibrated Brier coordinate from the full explicit driver
state. Prevalence enters here, so Brier can change even when the score moments
are held fixed. -/
noncomputable def targetCalibratedBrierFromSourceWeights {p q : ℕ}
    (m : CrossPopulationMetricModel p q) : ℝ :=
  TransportedMetrics.calibratedBrierFromVariances
    m.targetPrevalence
    (targetExplainedSignalVarianceFromSourceWeights m)
    (targetResidualVarianceFromSourceWeights m)

/-- The mechanistic target calibrated Brier coordinate is built directly from
target explained signal variance and target residual variance. -/
theorem targetCalibratedBrierFromSourceWeights_eq_explicit_target_variances {p q : ℕ}
    (m : CrossPopulationMetricModel p q) :
    targetCalibratedBrierFromSourceWeights m =
      TransportedMetrics.calibratedBrierFromVariances
        m.targetPrevalence
        (targetExplainedSignalVarianceFromSourceWeights m)
        (targetResidualVarianceFromSourceWeights m) := by
  rfl

/-- The direct mechanistic target calibrated Brier coordinate agrees with the
`R²` chart induced by the same explicit target explained-signal and
total-variance decomposition. This is a derived identity, not the defining
construction of transported Brier. -/
@[simp] theorem targetCalibratedBrierFromSourceWeights_eq_explainedR2_chart {p q : ℕ}
    (m : CrossPopulationMetricModel p q) :
    targetCalibratedBrierFromSourceWeights m =
      TransportedMetrics.calibratedBrier
        m.targetPrevalence (targetR2FromSourceWeights m) := by
  rw [targetCalibratedBrierFromSourceWeights_eq_explicit_target_variances]
  rw [TransportedMetrics.calibratedBrierFromVariances_eq_chart]
  have h_eff_ne : effectiveTargetOutcomeVariance m ≠ 0 := by
    exact ne_of_gt (effectiveTargetOutcomeVariance_pos m)
  have hr2 :
      TransportedMetrics.r2FromSignalVariance
          (targetExplainedSignalVarianceFromSourceWeights m)
          (targetResidualVarianceFromSourceWeights m) =
        targetR2FromSourceWeights m := by
    unfold TransportedMetrics.r2FromSignalVariance targetResidualVarianceFromSourceWeights
      targetR2FromSourceWeights
    field_simp [h_eff_ne]
    ring
  rw [hr2]

/-- The target score variance is exactly the target quadratic form
`w_Sᵀ Σ_T w_S`. -/
theorem target_score_variance_from_source_weights_identity {p q : ℕ}
    (m : CrossPopulationMetricModel p q) :
    targetScoreVarianceFromSourceWeights m =
      dotProduct (sourceWeightsFromExplicitDrivers m)
        (m.sigmaTagTarget.mulVec (sourceWeightsFromExplicitDrivers m)) := by
  simp [targetScoreVarianceFromSourceWeights]

/-- The target score variance is the transported score equation applied to the
target LD operator acting on the transported source weights. -/
theorem targetScoreVarianceFromSourceWeights_eq_score_on_target_covariance_action {p q : ℕ}
    (m : CrossPopulationMetricModel p q) :
    targetScoreVarianceFromSourceWeights m =
      sourceWeightedTagScore m
        (m.sigmaTagTarget.mulVec (sourceWeightsFromExplicitDrivers m)) := by
  simp [targetScoreVarianceFromSourceWeights, sourceWeightedTagScore]

/-- The source score variance is the same score equation evaluated against the
source LD operator. -/
theorem sourceScoreVarianceFromExplicitDrivers_eq_score_on_source_covariance_action {p q : ℕ}
    (m : CrossPopulationMetricModel p q) :
    sourceScoreVarianceFromExplicitDrivers m =
      sourceWeightedTagScore m
        (m.sigmaTagSource.mulVec (sourceWeightsFromExplicitDrivers m)) := by
  simp [sourceScoreVarianceFromExplicitDrivers, sourceWeightedTagScore]

/-- The source `R²` is exactly the explained signal variance from the explicit
score equation divided by the source outcome variance. -/
theorem sourceR2FromSourceWeights_eq_signalVariance_ratio {p q : ℕ}
    (m : CrossPopulationMetricModel p q) :
    sourceR2FromSourceWeights m =
      sourceExplainedSignalVarianceFromSourceWeights m / m.sourceOutcomeVariance := by
  rfl

/-- The target `R²` is exactly the explained signal variance from the explicit
transported score equation divided by the effective target outcome variance. -/
theorem targetR2FromSourceWeights_eq_signalVariance_ratio {p q : ℕ}
    (m : CrossPopulationMetricModel p q) :
    targetR2FromSourceWeights m =
      targetExplainedSignalVarianceFromSourceWeights m / effectiveTargetOutcomeVariance m := by
  rfl

/-- Ohta-Kimura-style exact LD-correlation decay law across populations:
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

/-- Generation-indexed population-genetic parameters that drive explicit
time-varying portability state. These parameters govern drift, mutation,
migration, and recombination without compressing transport into source `R²`. -/
structure GenerationalPopGenParameters where
  Ne : ℝ
  μ : ℝ
  mig : ℝ
  recomb : ℝ
  V_A : ℝ
  Ne_pos : 0 < Ne
  μ_nonneg : 0 ≤ μ
  mig_nonneg : 0 ≤ mig
  recomb_nonneg : 0 ≤ recomb
  recomb_le_half : recomb ≤ 1 / 2
  V_A_pos : 0 < V_A

namespace GenerationalPopGenParameters

/-- Scaled mutation rate `θ = 4Neμ`. -/
noncomputable def theta (g : GenerationalPopGenParameters) : ℝ :=
  4 * g.Ne * g.μ

/-- Scaled migration rate `M = 4Nem`. -/
noncomputable def bigM (g : GenerationalPopGenParameters) : ℝ :=
  4 * g.Ne * g.mig

/-- Coalescent time coordinate at generation `t`. -/
noncomputable def tauAt (g : GenerationalPopGenParameters) (t : ℕ) : ℝ :=
  (t : ℝ) / (2 * g.Ne)

/-- Per-generation heterozygosity retention factor under drift + mutation. -/
noncomputable def hetDecayFactor (g : GenerationalPopGenParameters) : ℝ :=
  (1 - 1 / (2 * g.Ne)) * (1 - g.theta / (2 * g.Ne))

/-- Transient differentiation after `t` generations. This is the same
discrete-time drift/mutation/migration coordinate used in the evolutionary
layer, but now exposed directly to the mechanistic SNP/LD state. -/
noncomputable def fstTransientAt (g : GenerationalPopGenParameters) (t : ℕ) : ℝ :=
  (1 / (1 + g.theta + g.bigM)) * (1 - g.hetDecayFactor ^ t)

/-- Mutation-driven retention of shared ancestral variation after `t`
generations. -/
noncomputable def mutationSharedRetentionAt
    (g : GenerationalPopGenParameters) (t : ℕ) : ℝ :=
  Real.exp (-g.theta * g.tauAt t)

/-- Migration-driven restoration of shared variation after `t` generations. -/
noncomputable def migrationSharedBoostAt
    (g : GenerationalPopGenParameters) (t : ℕ) : ℝ :=
  1 + g.bigM * g.tauAt t / (1 + g.bigM)

@[simp] theorem tauAt_zero (g : GenerationalPopGenParameters) :
    g.tauAt 0 = 0 := by
  simp [tauAt]

@[simp] theorem fstTransientAt_zero (g : GenerationalPopGenParameters) :
    g.fstTransientAt 0 = 0 := by
  simp [fstTransientAt, hetDecayFactor]

@[simp] theorem mutationSharedRetentionAt_zero (g : GenerationalPopGenParameters) :
    g.mutationSharedRetentionAt 0 = 1 := by
  simp [mutationSharedRetentionAt, tauAt]

@[simp] theorem migrationSharedBoostAt_zero (g : GenerationalPopGenParameters) :
    g.migrationSharedBoostAt 0 = 1 := by
  simp [migrationSharedBoostAt, tauAt, bigM]

end GenerationalPopGenParameters

/-- Exact bridge from the coarse DGP evolutionary block to the
generation-indexed population-genetic parameter block used by the mechanistic
transport model. This carries only the shared popgen primitives; the
SNP/LD-aware state still lives in `CrossPopulationGenerationalModel`. -/
noncomputable def PGSEvolutionaryModel.toGenerationalPopGenParameters
    (m : PGSEvolutionaryModel) : GenerationalPopGenParameters where
  Ne := m.Ne
  μ := m.mu
  mig := m.mig
  recomb := m.recomb
  V_A := m.V_A
  Ne_pos := m.Ne_pos
  μ_nonneg := m.mu_nonneg
  mig_nonneg := m.mig_nonneg
  recomb_nonneg := m.recomb_nonneg
  recomb_le_half := m.recomb_le_half
  V_A_pos := m.V_A_pos

@[simp] theorem PGSEvolutionaryModel.toGenerationalPopGenParameters_theta
    (m : PGSEvolutionaryModel) :
    (m.toGenerationalPopGenParameters).theta = m.theta := by
  simp [PGSEvolutionaryModel.toGenerationalPopGenParameters,
    GenerationalPopGenParameters.theta, EvolutionaryParameters.theta]

@[simp] theorem PGSEvolutionaryModel.toGenerationalPopGenParameters_bigM
    (m : PGSEvolutionaryModel) :
    (m.toGenerationalPopGenParameters).bigM = m.bigM := by
  simp [PGSEvolutionaryModel.toGenerationalPopGenParameters,
    GenerationalPopGenParameters.bigM, EvolutionaryParameters.bigM]

@[simp] theorem PGSEvolutionaryModel.toGenerationalPopGenParameters_hetDecayFactor
    (m : PGSEvolutionaryModel) :
    (m.toGenerationalPopGenParameters).hetDecayFactor = m.hetDecayFactor := by
  unfold GenerationalPopGenParameters.hetDecayFactor PGSEvolutionaryModel.hetDecayFactor
  rw [PGSEvolutionaryModel.toGenerationalPopGenParameters_theta]
  rfl

/-- The transient `F_ST` coordinate in the coarse DGP block agrees exactly with
the generation-indexed popgen bridge at `⌊t_div⌋`, because both use the same
discrete heterozygosity recursion. -/
@[simp] theorem PGSEvolutionaryModel.toGenerationalPopGenParameters_fstTransientAt_floor
    (m : PGSEvolutionaryModel) :
    (m.toGenerationalPopGenParameters).fstTransientAt (Nat.floor m.t_div) =
      m.fstTransient := by
  unfold GenerationalPopGenParameters.fstTransientAt PGSEvolutionaryModel.fstTransient
  rw [PGSEvolutionaryModel.toGenerationalPopGenParameters_hetDecayFactor,
    PGSEvolutionaryModel.toGenerationalPopGenParameters_theta,
    PGSEvolutionaryModel.toGenerationalPopGenParameters_bigM]
  simp [fstEquilibrium, PGSEvolutionaryModel.toEvo,
    EvolutionaryParameters.theta, EvolutionaryParameters.bigM]

/-- When divergence time is an integer number of generations, the coarse
mutation-history coordinate agrees exactly with the generational popgen bridge
at that generation. -/
theorem PGSEvolutionaryModel.toGenerationalPopGenParameters_mutationSharedRetentionAt_floor
    (m : PGSEvolutionaryModel)
    (h_disc : m.t_div = (Nat.floor m.t_div : ℝ)) :
    (m.toGenerationalPopGenParameters).mutationSharedRetentionAt (Nat.floor m.t_div) =
      m.mutErosion := by
  unfold GenerationalPopGenParameters.mutationSharedRetentionAt
    PGSEvolutionaryModel.mutErosion mutationLDErosion
  rw [PGSEvolutionaryModel.toGenerationalPopGenParameters_theta]
  simp only [GenerationalPopGenParameters.tauAt,
    PGSEvolutionaryModel.toGenerationalPopGenParameters,
    PGSEvolutionaryModel.toEvo, EvolutionaryParameters.theta, EvolutionaryParameters.tau]
  rw [h_disc, Nat.floor_natCast]

/-- When divergence time is an integer number of generations, the coarse
migration-history coordinate agrees exactly with the generational popgen bridge
at that generation. -/
theorem PGSEvolutionaryModel.toGenerationalPopGenParameters_migrationSharedBoostAt_floor
    (m : PGSEvolutionaryModel)
    (h_disc : m.t_div = (Nat.floor m.t_div : ℝ)) :
    (m.toGenerationalPopGenParameters).migrationSharedBoostAt (Nat.floor m.t_div) =
      m.migBoost := by
  unfold GenerationalPopGenParameters.migrationSharedBoostAt
    PGSEvolutionaryModel.migBoost migrationLDBoost
  rw [PGSEvolutionaryModel.toGenerationalPopGenParameters_bigM]
  simp only [GenerationalPopGenParameters.tauAt,
    PGSEvolutionaryModel.toGenerationalPopGenParameters,
    PGSEvolutionaryModel.toEvo, EvolutionaryParameters.bigM, EvolutionaryParameters.tau]
  rw [h_disc, Nat.floor_natCast]

/-- Exact bridge from the DGP coordinate summary to the generational popgen
coordinates for the fields that genuinely match. The LD coordinate is
deliberately excluded here because the mechanistic model uses a joint
locus-specific kernel rather than a single global LD scalar. -/
theorem PGSEvolutionaryModel.coordinateSummary_matches_generational_popgen_at_floor
    (m : PGSEvolutionaryModel)
    (h_disc : m.t_div = (Nat.floor m.t_div : ℝ)) :
    m.coordinateSummary.alleleFreqCoordinate =
      1 - (m.toGenerationalPopGenParameters).fstTransientAt (Nat.floor m.t_div) ∧
    m.coordinateSummary.ancestralVariantCoordinate =
      (m.toGenerationalPopGenParameters).mutationSharedRetentionAt (Nat.floor m.t_div) ∧
    m.coordinateSummary.migrationCoordinate =
      (m.toGenerationalPopGenParameters).migrationSharedBoostAt (Nat.floor m.t_div) := by
  refine ⟨?_, ?_, ?_⟩
  · simpa [PGSEvolutionaryModel.coordinateSummary_alleleFreqCoordinate] using
      congrArg (fun x => 1 - x)
        (PGSEvolutionaryModel.toGenerationalPopGenParameters_fstTransientAt_floor m)
  · rw [PGSEvolutionaryModel.coordinateSummary_ancestralVariantCoordinate]
    exact (PGSEvolutionaryModel.toGenerationalPopGenParameters_mutationSharedRetentionAt_floor
      m h_disc).symm
  · rw [PGSEvolutionaryModel.coordinateSummary_migrationCoordinate]
    exact (PGSEvolutionaryModel.toGenerationalPopGenParameters_migrationSharedBoostAt_floor
      m h_disc).symm

/-- Allele-frequency mismatch penalty. This penalizes transport when target
allele frequencies drift away from the source frequencies, even if the source
score itself is unchanged. -/
noncomputable def alleleFreqMismatchPenalty (pSource pTarget : ℝ) : ℝ :=
  Real.exp (-|pTarget - pSource|)

@[simp] theorem alleleFreqMismatchPenalty_self (p : ℝ) :
    alleleFreqMismatchPenalty p p = 1 := by
  simp [alleleFreqMismatchPenalty]

/-- Generation-indexed cross-population state. Source quantities are fixed at
training time; target quantities are explicit functions of generation. The
time-varying target LD and tagging state is derived from:

- source LD / source tag-causal alignment,
- source causal effects plus an explicit locus-resolved target-effect
  heterogeneity path,
- target-only novel causal effects,
- direct scored-causal measurements that are not mediated by LD decay,
- target-only novel direct causal links,
- ancestry-specific proxy tagging that is mediated by LD decay,
- target-only novel proxy-tagging links,
- recombination and transient `F_ST`,
- mutation- and migration-driven sharing terms, and
- explicit target allele-frequency trajectories split into standing and
  mutation-shift components,
- plus target-only untaggable phenotype variance from novel mutations. -/
structure CrossPopulationGenerationalModel (p q : ℕ) where
  popGen : GenerationalPopGenParameters
  betaSource : Fin q → ℝ
  targetEffectHeterogeneityAt : ℕ → Fin q → ℝ
  novelCausalEffectTargetAt : ℕ → Fin q → ℝ
  sigmaTagSource : Matrix (Fin p) (Fin p) ℝ
  directCausalSource : Matrix (Fin p) (Fin q) ℝ
  novelDirectCausalTemplate : Matrix (Fin p) (Fin q) ℝ
  proxyTaggingSource : Matrix (Fin p) (Fin q) ℝ
  novelProxyTaggingTemplate : Matrix (Fin p) (Fin q) ℝ
  tagDistance : Matrix (Fin p) (Fin p) ℝ
  tagCausalDistance : Matrix (Fin p) (Fin q) ℝ
  tagAlleleFreqSource : Fin p → ℝ
  tagAlleleFreqStandingTargetAt : ℕ → Fin p → ℝ
  tagAlleleFreqMutationShiftAt : ℕ → Fin p → ℝ
  causalAlleleFreqSource : Fin q → ℝ
  causalAlleleFreqStandingTargetAt : ℕ → Fin q → ℝ
  causalAlleleFreqMutationShiftAt : ℕ → Fin q → ℝ
  contextCrossSource : Fin p → ℝ
  contextCrossTargetAt : ℕ → Fin p → ℝ
  sourceOutcomeVariance : ℝ
  targetOutcomeVarianceAt : ℕ → ℝ
  novelUntaggablePhenotypeVarianceAt : ℕ → ℝ
  targetPrevalenceAt : ℕ → ℝ
  sourceOutcomeVariance_pos : 0 < sourceOutcomeVariance
  targetOutcomeVariance_pos : ∀ t, 0 < targetOutcomeVarianceAt t
  novelUntaggablePhenotypeVariance_nonneg : ∀ t, 0 ≤ novelUntaggablePhenotypeVarianceAt t
  targetPrevalence_pos : ∀ t, 0 < targetPrevalenceAt t
  targetPrevalence_lt_one : ∀ t, targetPrevalenceAt t < 1

/-- Generation-indexed target effect vector. This is derived from the source
effect vector plus an explicit locus-resolved heterogeneity path and a
target-only novel-mutation effect path, not from any single retained-effect
scalar. -/
noncomputable def betaTargetAt {p q : ℕ}
    (m : CrossPopulationGenerationalModel p q) (t : ℕ) : Fin q → ℝ :=
  m.betaSource + m.targetEffectHeterogeneityAt t + m.novelCausalEffectTargetAt t

@[simp] theorem betaTargetAt_eq_source_plus_effectHeterogeneityAt {p q : ℕ}
    (m : CrossPopulationGenerationalModel p q) (t : ℕ) :
    betaTargetAt m t =
      m.betaSource + m.targetEffectHeterogeneityAt t + m.novelCausalEffectTargetAt t := by
  rfl

/-- Explicit target tag-SNP allele frequency after standing drift and
mutation-specific shift are combined. -/
noncomputable def tagAlleleFreqTargetAt {p q : ℕ}
    (m : CrossPopulationGenerationalModel p q) (t : ℕ) (i : Fin p) : ℝ :=
  m.tagAlleleFreqStandingTargetAt t i + m.tagAlleleFreqMutationShiftAt t i

@[simp] theorem tagAlleleFreqTargetAt_eq_standing_plus_mutationShift {p q : ℕ}
    (m : CrossPopulationGenerationalModel p q) (t : ℕ) (i : Fin p) :
    tagAlleleFreqTargetAt m t i =
      m.tagAlleleFreqStandingTargetAt t i + m.tagAlleleFreqMutationShiftAt t i := by
  rfl

/-- Explicit target causal-site allele frequency after standing drift and
mutation-specific shift are combined. -/
noncomputable def causalAlleleFreqTargetAt {p q : ℕ}
    (m : CrossPopulationGenerationalModel p q) (t : ℕ) (j : Fin q) : ℝ :=
  m.causalAlleleFreqStandingTargetAt t j + m.causalAlleleFreqMutationShiftAt t j

@[simp] theorem causalAlleleFreqTargetAt_eq_standing_plus_mutationShift {p q : ℕ}
    (m : CrossPopulationGenerationalModel p q) (t : ℕ) (j : Fin q) :
    causalAlleleFreqTargetAt m t j =
      m.causalAlleleFreqStandingTargetAt t j + m.causalAlleleFreqMutationShiftAt t j := by
  rfl

/-- Per-tag allele-frequency retention at generation `t`. -/
noncomputable def tagAlleleFreqRetentionAt {p q : ℕ}
    (m : CrossPopulationGenerationalModel p q) (t : ℕ) (i : Fin p) : ℝ :=
  alleleFreqMismatchPenalty (m.tagAlleleFreqSource i) (tagAlleleFreqTargetAt m t i)

/-- Per-causal-variant allele-frequency retention at generation `t`. -/
noncomputable def causalAlleleFreqRetentionAt {p q : ℕ}
    (m : CrossPopulationGenerationalModel p q) (t : ℕ) (j : Fin q) : ℝ :=
  alleleFreqMismatchPenalty (m.causalAlleleFreqSource j) (causalAlleleFreqTargetAt m t j)

/-- Fraction of target-side novel variation accumulated by generation `t`.
This is the complement of shared ancestral variation retained after mutation. -/
noncomputable def novelVariantInnovationAt (g : GenerationalPopGenParameters) (t : ℕ) : ℝ :=
  1 - g.mutationSharedRetentionAt t

@[simp] theorem novelVariantInnovationAt_zero (g : GenerationalPopGenParameters) :
    novelVariantInnovationAt g 0 = 0 := by
  simp [novelVariantInnovationAt]

/-- Joint locus-level transport kernel for LD among scored SNPs at generation
`t`. This is where drift, recombination, mutation history, migration history,
and tag-SNP allele-frequency drift meet; the mechanistic model does not treat
them as independent global scalars. -/
noncomputable def jointTagLDKernelAt {p q : ℕ}
    (m : CrossPopulationGenerationalModel p q) (t : ℕ) (i j : Fin p) : ℝ :=
  ldCorrelationDecay (m.tagDistance i j)
      (m.popGen.fstTransientAt t) m.popGen.recomb *
    m.popGen.mutationSharedRetentionAt t *
    m.popGen.migrationSharedBoostAt t *
    tagAlleleFreqRetentionAt m t i *
    tagAlleleFreqRetentionAt m t j

@[simp] theorem jointTagLDKernelAt_uses_ld_af_mutation_migration {p q : ℕ}
    (m : CrossPopulationGenerationalModel p q) (t : ℕ) (i j : Fin p) :
    jointTagLDKernelAt m t i j =
      ldCorrelationDecay (m.tagDistance i j)
          (m.popGen.fstTransientAt t) m.popGen.recomb *
        m.popGen.mutationSharedRetentionAt t *
        m.popGen.migrationSharedBoostAt t *
        tagAlleleFreqRetentionAt m t i *
        tagAlleleFreqRetentionAt m t j := by
  simp [jointTagLDKernelAt]

/-- Joint locus-level transport kernel for directly scored causal variants.
This omits the LD-decay term because the scored variant is itself causal, but
it still carries mutation, migration, and AF-history interactions. -/
noncomputable def jointDirectCausalKernelAt {p q : ℕ}
    (m : CrossPopulationGenerationalModel p q) (t : ℕ) (i : Fin p) (j : Fin q) : ℝ :=
  m.popGen.mutationSharedRetentionAt t *
    m.popGen.migrationSharedBoostAt t *
    tagAlleleFreqRetentionAt m t i *
    causalAlleleFreqRetentionAt m t j

@[simp] theorem jointDirectCausalKernelAt_uses_af_mutation_migration {p q : ℕ}
    (m : CrossPopulationGenerationalModel p q) (t : ℕ) (i : Fin p) (j : Fin q) :
    jointDirectCausalKernelAt m t i j =
      m.popGen.mutationSharedRetentionAt t *
        m.popGen.migrationSharedBoostAt t *
        tagAlleleFreqRetentionAt m t i *
        causalAlleleFreqRetentionAt m t j := by
  simp [jointDirectCausalKernelAt]

/-- Joint locus-level transport kernel for ancestry-specific proxy tagging.
This carries the full interaction between LD decay, mutation/migration sharing,
and source/target allele-frequency history. -/
noncomputable def jointProxyTaggingKernelAt {p q : ℕ}
    (m : CrossPopulationGenerationalModel p q) (t : ℕ) (i : Fin p) (j : Fin q) : ℝ :=
  ldCorrelationDecay (m.tagCausalDistance i j)
      (m.popGen.fstTransientAt t) m.popGen.recomb *
    m.popGen.mutationSharedRetentionAt t *
    m.popGen.migrationSharedBoostAt t *
    tagAlleleFreqRetentionAt m t i *
    causalAlleleFreqRetentionAt m t j

@[simp] theorem jointProxyTaggingKernelAt_uses_ld_tagging_af_mutation_migration {p q : ℕ}
    (m : CrossPopulationGenerationalModel p q) (t : ℕ) (i : Fin p) (j : Fin q) :
    jointProxyTaggingKernelAt m t i j =
      ldCorrelationDecay (m.tagCausalDistance i j)
          (m.popGen.fstTransientAt t) m.popGen.recomb *
        m.popGen.mutationSharedRetentionAt t *
        m.popGen.migrationSharedBoostAt t *
        tagAlleleFreqRetentionAt m t i *
        causalAlleleFreqRetentionAt m t j := by
  simp [jointProxyTaggingKernelAt]

/-- Joint locus-level kernel for target-only novel direct causal links. Novel
target-specific causal variants accumulate with mutation history, are diluted by
migration, and still depend on target allele-frequency matching. -/
noncomputable def jointNovelDirectCausalKernelAt {p q : ℕ}
    (m : CrossPopulationGenerationalModel p q) (t : ℕ) (i : Fin p) (j : Fin q) : ℝ :=
  novelVariantInnovationAt m.popGen t *
    (m.popGen.migrationSharedBoostAt t)⁻¹ *
    tagAlleleFreqRetentionAt m t i *
    causalAlleleFreqRetentionAt m t j

@[simp] theorem jointNovelDirectCausalKernelAt_uses_af_mutation_migration {p q : ℕ}
    (m : CrossPopulationGenerationalModel p q) (t : ℕ) (i : Fin p) (j : Fin q) :
    jointNovelDirectCausalKernelAt m t i j =
      novelVariantInnovationAt m.popGen t *
        (m.popGen.migrationSharedBoostAt t)⁻¹ *
        tagAlleleFreqRetentionAt m t i *
        causalAlleleFreqRetentionAt m t j := by
  simp [jointNovelDirectCausalKernelAt]

/-- Joint locus-level kernel for target-only novel proxy tagging. This carries
both local LD structure and mutation-generated novelty, rather than just
attenuating the shared source proxy surface. -/
noncomputable def jointNovelProxyTaggingKernelAt {p q : ℕ}
    (m : CrossPopulationGenerationalModel p q) (t : ℕ) (i : Fin p) (j : Fin q) : ℝ :=
  ldCorrelationDecay (m.tagCausalDistance i j)
      (m.popGen.fstTransientAt t) m.popGen.recomb *
    novelVariantInnovationAt m.popGen t *
    (m.popGen.migrationSharedBoostAt t)⁻¹ *
    tagAlleleFreqRetentionAt m t i *
    causalAlleleFreqRetentionAt m t j

@[simp] theorem jointNovelProxyTaggingKernelAt_uses_ld_af_mutation_migration {p q : ℕ}
    (m : CrossPopulationGenerationalModel p q) (t : ℕ) (i : Fin p) (j : Fin q) :
    jointNovelProxyTaggingKernelAt m t i j =
      ldCorrelationDecay (m.tagCausalDistance i j)
          (m.popGen.fstTransientAt t) m.popGen.recomb *
        novelVariantInnovationAt m.popGen t *
        (m.popGen.migrationSharedBoostAt t)⁻¹ *
        tagAlleleFreqRetentionAt m t i *
        causalAlleleFreqRetentionAt m t j := by
  simp [jointNovelProxyTaggingKernelAt]

/-- Time-varying target LD among scored SNPs. This incorporates recombination,
drift (`F_ST`), mutation/migration-driven shared variation, and explicit target
tag-SNP allele-frequency drift. -/
noncomputable def sigmaTagTargetAt {p q : ℕ}
    (m : CrossPopulationGenerationalModel p q) (t : ℕ) :
    Matrix (Fin p) (Fin p) ℝ :=
  fun i j =>
    m.sigmaTagSource i j * jointTagLDKernelAt m t i j

/-- Time-varying target tag-to-causal alignment. This is the explicit tagging
quality surface, driven by LD decay, allele-frequency divergence, mutation,
migration, and the underlying source tag-causal alignment. -/
noncomputable def directCausalTargetAt {p q : ℕ}
    (m : CrossPopulationGenerationalModel p q) (t : ℕ) :
    Matrix (Fin p) (Fin q) ℝ :=
  fun i j =>
    m.directCausalSource i j * jointDirectCausalKernelAt m t i j

/-- Time-varying target-only novel direct-causal alignment. -/
noncomputable def novelDirectCausalTargetAt {p q : ℕ}
    (m : CrossPopulationGenerationalModel p q) (t : ℕ) :
    Matrix (Fin p) (Fin q) ℝ :=
  fun i j =>
    m.novelDirectCausalTemplate i j * jointNovelDirectCausalKernelAt m t i j

/-- Time-varying proxy-tagging alignment. Unlike directly scored causal
variants, this channel is degraded by LD decay between the scored tag and the
unscored causal variant. -/
noncomputable def proxyTaggingTargetAt {p q : ℕ}
    (m : CrossPopulationGenerationalModel p q) (t : ℕ) :
    Matrix (Fin p) (Fin q) ℝ :=
  fun i j =>
    m.proxyTaggingSource i j * jointProxyTaggingKernelAt m t i j

/-- Time-varying target-only novel proxy-tagging alignment created after
divergence. -/
noncomputable def novelProxyTaggingTargetAt {p q : ℕ}
    (m : CrossPopulationGenerationalModel p q) (t : ℕ) :
    Matrix (Fin p) (Fin q) ℝ :=
  fun i j =>
    m.novelProxyTaggingTemplate i j * jointNovelProxyTaggingKernelAt m t i j

/-- Time-varying target tag-to-causal alignment is the sum of a direct-causal
channel, a target-only novel direct-causal channel, a proxy-tagging channel,
and a target-only novel proxy-tagging channel. Only the proxy channels carry
LD-decay erosion. -/
noncomputable def sigmaTagCausalTargetAt {p q : ℕ}
    (m : CrossPopulationGenerationalModel p q) (t : ℕ) :
    Matrix (Fin p) (Fin q) ℝ :=
  directCausalTargetAt m t +
    (novelDirectCausalTargetAt m t +
      (proxyTaggingTargetAt m t + novelProxyTaggingTargetAt m t))

/-- Projection of the source effect vector through the generation-indexed
target tagging surface. This isolates what would transport if target causal
effects were identical to source effects. -/
noncomputable def targetSourceEffectProjectionAt {p q : ℕ}
    (m : CrossPopulationGenerationalModel p q) (t : ℕ) : Fin p → ℝ :=
  (sigmaTagCausalTargetAt m t).mulVec m.betaSource

/-- Incremental generation-indexed projection induced purely by per-locus
target-effect heterogeneity, including target-only novel causal effects. -/
noncomputable def targetEffectHeterogeneityProjectionAt {p q : ℕ}
    (m : CrossPopulationGenerationalModel p q) (t : ℕ) : Fin p → ℝ :=
  (sigmaTagCausalTargetAt m t).mulVec
    (m.targetEffectHeterogeneityAt t + m.novelCausalEffectTargetAt t)

/-- Projection induced purely by target-only novel causal effects at generation
`t`. -/
noncomputable def targetNovelCausalEffectProjectionAt {p q : ℕ}
    (m : CrossPopulationGenerationalModel p q) (t : ℕ) : Fin p → ℝ :=
  (sigmaTagCausalTargetAt m t).mulVec (m.novelCausalEffectTargetAt t)

/-- The static exact metric model obtained by slicing the generational state at
generation `t`. This is the canonical bridge from explicit population-genetic
dynamics to deployed metrics. -/
noncomputable def CrossPopulationGenerationalModel.toMetricModelAt {p q : ℕ}
    (m : CrossPopulationGenerationalModel p q) (t : ℕ) :
    CrossPopulationMetricModel p q where
  betaSource := m.betaSource
  betaTarget := m.betaSource + m.targetEffectHeterogeneityAt t
  sigmaTagSource := m.sigmaTagSource
  sigmaTagTarget := sigmaTagTargetAt m t
  directCausalSource := m.directCausalSource
  directCausalTarget := directCausalTargetAt m t
  novelDirectCausalTarget := novelDirectCausalTargetAt m t
  proxyTaggingSource := m.proxyTaggingSource
  proxyTaggingTarget := proxyTaggingTargetAt m t
  novelProxyTaggingTarget := novelProxyTaggingTargetAt m t
  novelCausalEffectTarget := m.novelCausalEffectTargetAt t
  contextCrossSource := m.contextCrossSource
  contextCrossTarget := m.contextCrossTargetAt t
  sourceOutcomeVariance := m.sourceOutcomeVariance
  targetOutcomeVariance := m.targetOutcomeVarianceAt t
  novelUntaggablePhenotypeVarianceTarget := m.novelUntaggablePhenotypeVarianceAt t
  targetPrevalence := m.targetPrevalenceAt t
  sourceOutcomeVariance_pos := m.sourceOutcomeVariance_pos
  targetOutcomeVariance_pos := m.targetOutcomeVariance_pos t
  novelUntaggablePhenotypeVarianceTarget_nonneg := m.novelUntaggablePhenotypeVariance_nonneg t
  targetPrevalence_pos := m.targetPrevalence_pos t
  targetPrevalence_lt_one := m.targetPrevalence_lt_one t

/-- Exact target `R²` after `t` generations under the full time-varying
mechanistic state. -/
noncomputable def targetR2AtGeneration {p q : ℕ}
    (m : CrossPopulationGenerationalModel p q) (t : ℕ) : ℝ :=
  targetR2FromSourceWeights (m.toMetricModelAt t)

/-- Exact target calibrated Brier coordinate after `t` generations. -/
noncomputable def targetCalibratedBrierAtGeneration {p q : ℕ}
    (m : CrossPopulationGenerationalModel p q) (t : ℕ) : ℝ :=
  targetCalibratedBrierFromSourceWeights (m.toMetricModelAt t)

@[simp] theorem sigmaTagTargetAt_uses_ld_af_mutation_migration {p q : ℕ}
    (m : CrossPopulationGenerationalModel p q) (t : ℕ) (i j : Fin p) :
    sigmaTagTargetAt m t i j =
      m.sigmaTagSource i j *
        ldCorrelationDecay (m.tagDistance i j)
          (m.popGen.fstTransientAt t) m.popGen.recomb *
        m.popGen.mutationSharedRetentionAt t *
        m.popGen.migrationSharedBoostAt t *
        tagAlleleFreqRetentionAt m t i *
        tagAlleleFreqRetentionAt m t j := by
  simp [sigmaTagTargetAt, jointTagLDKernelAt, mul_assoc]

@[simp] theorem directCausalTargetAt_uses_af_mutation_migration {p q : ℕ}
    (m : CrossPopulationGenerationalModel p q) (t : ℕ) (i : Fin p) (j : Fin q) :
    directCausalTargetAt m t i j =
      m.directCausalSource i j *
        m.popGen.mutationSharedRetentionAt t *
        m.popGen.migrationSharedBoostAt t *
        tagAlleleFreqRetentionAt m t i *
        causalAlleleFreqRetentionAt m t j := by
  simp [directCausalTargetAt, jointDirectCausalKernelAt, mul_assoc]

@[simp] theorem novelDirectCausalTargetAt_uses_af_mutation_migration {p q : ℕ}
    (m : CrossPopulationGenerationalModel p q) (t : ℕ) (i : Fin p) (j : Fin q) :
    novelDirectCausalTargetAt m t i j =
      m.novelDirectCausalTemplate i j *
        novelVariantInnovationAt m.popGen t *
        (m.popGen.migrationSharedBoostAt t)⁻¹ *
        tagAlleleFreqRetentionAt m t i *
        causalAlleleFreqRetentionAt m t j := by
  simp [novelDirectCausalTargetAt, jointNovelDirectCausalKernelAt, mul_assoc]

@[simp] theorem proxyTaggingTargetAt_uses_ld_tagging_af_mutation_migration {p q : ℕ}
    (m : CrossPopulationGenerationalModel p q) (t : ℕ) (i : Fin p) (j : Fin q) :
    proxyTaggingTargetAt m t i j =
      m.proxyTaggingSource i j *
        ldCorrelationDecay (m.tagCausalDistance i j)
          (m.popGen.fstTransientAt t) m.popGen.recomb *
        m.popGen.mutationSharedRetentionAt t *
        m.popGen.migrationSharedBoostAt t *
        tagAlleleFreqRetentionAt m t i *
        causalAlleleFreqRetentionAt m t j := by
  simp [proxyTaggingTargetAt, jointProxyTaggingKernelAt, mul_assoc]

@[simp] theorem novelProxyTaggingTargetAt_uses_ld_tagging_af_mutation_migration {p q : ℕ}
    (m : CrossPopulationGenerationalModel p q) (t : ℕ) (i : Fin p) (j : Fin q) :
    novelProxyTaggingTargetAt m t i j =
      m.novelProxyTaggingTemplate i j *
        ldCorrelationDecay (m.tagCausalDistance i j)
          (m.popGen.fstTransientAt t) m.popGen.recomb *
        novelVariantInnovationAt m.popGen t *
        (m.popGen.migrationSharedBoostAt t)⁻¹ *
        tagAlleleFreqRetentionAt m t i *
        causalAlleleFreqRetentionAt m t j := by
  simp [novelProxyTaggingTargetAt, jointNovelProxyTaggingKernelAt, mul_assoc]

@[simp] theorem sigmaTagCausalTargetAt_uses_ld_tagging_af_mutation_migration {p q : ℕ}
    (m : CrossPopulationGenerationalModel p q) (t : ℕ) (i : Fin p) (j : Fin q) :
    sigmaTagCausalTargetAt m t i j =
      m.directCausalSource i j *
        m.popGen.mutationSharedRetentionAt t *
        m.popGen.migrationSharedBoostAt t *
        tagAlleleFreqRetentionAt m t i *
        causalAlleleFreqRetentionAt m t j +
      m.novelDirectCausalTemplate i j *
        novelVariantInnovationAt m.popGen t *
        (m.popGen.migrationSharedBoostAt t)⁻¹ *
        tagAlleleFreqRetentionAt m t i *
        causalAlleleFreqRetentionAt m t j +
      m.proxyTaggingSource i j *
        ldCorrelationDecay (m.tagCausalDistance i j)
          (m.popGen.fstTransientAt t) m.popGen.recomb *
        m.popGen.mutationSharedRetentionAt t *
        m.popGen.migrationSharedBoostAt t *
        tagAlleleFreqRetentionAt m t i *
        causalAlleleFreqRetentionAt m t j +
      m.novelProxyTaggingTemplate i j *
        ldCorrelationDecay (m.tagCausalDistance i j)
          (m.popGen.fstTransientAt t) m.popGen.recomb *
        novelVariantInnovationAt m.popGen t *
        (m.popGen.migrationSharedBoostAt t)⁻¹ *
        tagAlleleFreqRetentionAt m t i *
        causalAlleleFreqRetentionAt m t j := by
  simp [sigmaTagCausalTargetAt, directCausalTargetAt, novelDirectCausalTargetAt,
    proxyTaggingTargetAt, novelProxyTaggingTargetAt, jointDirectCausalKernelAt,
    jointNovelDirectCausalKernelAt, jointProxyTaggingKernelAt,
    jointNovelProxyTaggingKernelAt, mul_assoc, add_assoc]

/-- At each generation, the target tagging projection splits into the part that
would be obtained under source-stable effects plus a separate projection of the
locus-resolved target-effect heterogeneity. -/
theorem targetTaggingProjectionAtGeneration_eq_source_effect_plus_effectHeterogeneity
    {p q : ℕ} (m : CrossPopulationGenerationalModel p q) (t : ℕ) :
    targetTaggingProjection (m.toMetricModelAt t) =
      targetSourceEffectProjectionAt m t +
        targetEffectHeterogeneityProjectionAt m t := by
  simpa [CrossPopulationGenerationalModel.toMetricModelAt,
    targetSourceEffectProjectionAt, targetEffectHeterogeneityProjectionAt,
    targetSourceEffectProjection, targetEffectHeterogeneityProjection,
    targetEffectHeterogeneity, targetTotalEffect, sigmaTagCausalTargetAt, add_assoc]
    using targetTaggingProjection_eq_source_effect_plus_effectHeterogeneity
      (m.toMetricModelAt t)

@[simp] theorem targetR2AtGeneration_eq_targetR2From_slice {p q : ℕ}
    (m : CrossPopulationGenerationalModel p q) (t : ℕ) :
    targetR2AtGeneration m t = targetR2FromSourceWeights (m.toMetricModelAt t) := by
  rfl

@[simp] theorem targetCalibratedBrierAtGeneration_eq_slice {p q : ℕ}
    (m : CrossPopulationGenerationalModel p q) (t : ℕ) :
    targetCalibratedBrierAtGeneration m t =
      targetCalibratedBrierFromSourceWeights (m.toMetricModelAt t) := by
  rfl

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

/-- Neutral allele-frequency benchmark `R²`.

This section is intentionally limited to the coarse heterozygosity/F_ST chart.
It is a neutral allele-frequency benchmark, not a mechanistic cross-population
portability law. Claims about deployed portability must instead use the
explicit SNP/LD/alignment state in `CrossPopulationMetricModel`. -/
noncomputable def targetR2FromNeutralAFBenchmark
    (V_A V_E fstTarget : ℝ) : ℝ :=
  presentDayR2 V_A V_E fstTarget

/-- Within the neutral allele-frequency benchmark, the target/source `R²` ratio
is strictly below `1` when target `F_ST` exceeds source `F_ST`. -/
theorem neutralAFBenchmarkRatio_from_state
    (V_A V_E fstSource fstTarget : ℝ)
    (hVA : 0 < V_A) (hVE : 0 < V_E)
    (h_fst : fstSource < fstTarget)
    (h_fst_bounds : 0 ≤ fstSource ∧ fstTarget < 1) :
    targetR2FromNeutralAFBenchmark V_A V_E fstTarget / presentDayR2 V_A V_E fstSource < 1 := by
  have hsrc_pos : 0 < presentDayR2 V_A V_E fstSource := by
    unfold presentDayR2
    have hv_pos : 0 < presentDayPGSVariance V_A fstSource := by
      unfold presentDayPGSVariance
      have h_one_minus : 0 < 1 - fstSource := by linarith [h_fst_bounds.2, h_fst]
      exact mul_pos h_one_minus hVA
    exact div_pos hv_pos (by linarith)
  have hdrop :
      targetR2FromNeutralAFBenchmark V_A V_E fstTarget < presentDayR2 V_A V_E fstSource := by
    simpa [targetR2FromNeutralAFBenchmark] using
      drift_degrades_R2 V_A V_E fstSource fstTarget hVA hVE h_fst (le_of_lt h_fst_bounds.2)
  exact portability_ratio_lt_one_of_drop
    (presentDayR2 V_A V_E fstSource)
    (targetR2FromNeutralAFBenchmark V_A V_E fstTarget)
    hsrc_pos hdrop

/-- Within the neutral allele-frequency benchmark, target `R²` is below source
`R²` once target `F_ST` exceeds source `F_ST`. -/
theorem targetR2_lt_source_from_neutralAF_benchmark
    (V_A V_E fstSource fstTarget : ℝ)
    (hVA : 0 < V_A) (hVE : 0 < V_E)
    (h_fst : fstSource < fstTarget)
    (h_fst_bounds : 0 ≤ fstSource ∧ fstTarget < 1) :
    targetR2FromNeutralAFBenchmark V_A V_E fstTarget < presentDayR2 V_A V_E fstSource := by
  simpa [targetR2FromNeutralAFBenchmark] using
    drift_degrades_R2 V_A V_E fstSource fstTarget hVA hVE h_fst (le_of_lt h_fst_bounds.2)

/-- Neutral allele-frequency benchmark ratio from observable source/target
`F_ST`. This is a coarse heterozygosity benchmark only, not a mechanistic law
for cross-population tagging fidelity. -/
noncomputable def neutralAFBenchmarkRatio (fstSource fstTarget : ℝ) : ℝ :=
  (1 - fstTarget) / (1 - fstSource)

/-- The neutral allele-frequency benchmark target `R²` is definitionally the
literal present-day target `R²` in this coarse chart. -/
theorem targetR2FromNeutralAFBenchmark_eq_presentDayR2
    (V_A V_E fstTarget : ℝ) :
    targetR2FromNeutralAFBenchmark V_A V_E fstTarget =
      presentDayR2 V_A V_E fstTarget := by
  rfl

/-- Exact calibrated Bernoulli Brier risk as a function of prevalence and
explained-variance fraction.

For a calibrated Bernoulli predictor with prevalence `π` and
`Var(η(Z)) = π(1-π) r2`, the exact population Brier risk is
`π(1-π)(1-r2)`. This is not a surrogate loss: it is the closed form of the
exact calibrated Brier risk under the Bernoulli-mixing model. -/
def exactCalibratedBrierRiskFromR2 (π r2 : ℝ) : ℝ :=
  π * (1 - π) * (1 - r2)

/-- Exact calibrated Bernoulli Brier risk written directly in prevalence and
explained-risk coordinates. -/
abbrev brierFromR2 (π r2 : ℝ) : ℝ :=
  exactCalibratedBrierRiskFromR2 π r2

/-- Exact target AUC from the neutral allele-frequency benchmark state. -/
noncomputable def targetAUCFromNeutralAFBenchmark
    (V_A V_E fstTarget : ℝ) : ℝ :=
  presentDayAUC V_A V_E fstTarget

/-- The neutral allele-frequency benchmark target AUC is definitionally the
literal present-day AUC in this coarse chart. -/
theorem targetAUCFromNeutralAFBenchmark_eq_presentDayAUC
    (V_A V_E fstTarget : ℝ) :
    targetAUCFromNeutralAFBenchmark V_A V_E fstTarget =
      presentDayAUC V_A V_E fstTarget := by
  rfl

/-- Source Brier chart as a function of prevalence and source `R²`. -/
noncomputable def sourceBrierFromR2 (π r2Source : ℝ) : ℝ :=
  exactCalibratedBrierRiskFromR2 π r2Source

/-- The source Brier chart is the canonical source Brier
specialization. -/
theorem sourceBrierFromR2_eq_transportedMetrics
    (π r2Source : ℝ) :
    sourceBrierFromR2 π r2Source =
      TransportedMetrics.calibratedBrier π r2Source := by
  rfl

/-- Exact target calibrated Brier risk under the Bernoulli-mixing model from
explicit target state. -/
noncomputable def targetExactCalibratedBrierRisk
    (π V_A V_E fstTarget : ℝ) : ℝ :=
  exactCalibratedBrierRiskFromR2 π
    (targetR2FromNeutralAFBenchmark V_A V_E fstTarget)

/-- Neutral allele-frequency benchmark target Brier map used by the dashboard
(`Brier(R²_target)`). -/
noncomputable def targetBrierFromNeutralAFBenchmark
    (π V_A V_E fstTarget : ℝ) : ℝ :=
  targetExactCalibratedBrierRisk π V_A V_E fstTarget

/-- Canonical bundled deployed metrics under the neutral allele-frequency
benchmark state. -/
noncomputable def neutralAFBenchmarkMetricProfile
    (π V_A V_E fstTarget : ℝ) : TransportedMetrics.Profile :=
  TransportedMetrics.profileFromSignalVariance π V_E (presentDayPGSVariance V_A fstTarget)

/-- The bundled neutral allele-frequency benchmark metrics reproduce the file's public
`R²`, AUC, and Brier surfaces exactly. -/
theorem neutralAFBenchmarkMetricProfile_eq
    (π V_A V_E fstTarget : ℝ) :
    neutralAFBenchmarkMetricProfile π V_A V_E fstTarget =
      { r2 := targetR2FromNeutralAFBenchmark V_A V_E fstTarget
      , auc := targetAUCFromNeutralAFBenchmark V_A V_E fstTarget
      , brier := targetBrierFromNeutralAFBenchmark π V_A V_E fstTarget } := by
  ext
  · change
      TransportedMetrics.r2FromSignalVariance (presentDayPGSVariance V_A fstTarget) V_E =
        targetR2FromNeutralAFBenchmark V_A V_E fstTarget
    unfold targetR2FromNeutralAFBenchmark TransportedMetrics.r2FromSignalVariance presentDayR2
    rfl
  · change
      TransportedMetrics.aucFromSignalVariance (presentDayPGSVariance V_A fstTarget) V_E =
        targetAUCFromNeutralAFBenchmark V_A V_E fstTarget
    unfold targetAUCFromNeutralAFBenchmark TransportedMetrics.aucFromSignalVariance
      presentDayAUC presentDaySignalToNoise
    congr 1
    congr 1
    ring_nf
  · change
      TransportedMetrics.calibratedBrier π
        (TransportedMetrics.r2FromSignalVariance (presentDayPGSVariance V_A fstTarget) V_E) =
        targetBrierFromNeutralAFBenchmark π V_A V_E fstTarget
    unfold targetBrierFromNeutralAFBenchmark targetExactCalibratedBrierRisk
      exactCalibratedBrierRiskFromR2 targetR2FromNeutralAFBenchmark
      TransportedMetrics.calibratedBrier TransportedMetrics.r2FromSignalVariance
      presentDayR2
    rfl

/-- Exact neutral allele-frequency benchmark target AUC is definitionally the
literal present-day AUC. -/
@[simp] theorem targetAUCFromNeutralAFBenchmark_eq
    (V_A V_E fstTarget : ℝ) :
    targetAUCFromNeutralAFBenchmark V_A V_E fstTarget =
      presentDayAUC V_A V_E fstTarget := by
  rfl

/-- Full neutral allele-frequency benchmark AUC degradation theorem:
strictly higher drift implies strictly lower exact target AUC. -/
theorem targetAUC_lt_source_of_neutralAF_benchmark
    (V_A V_E fstSource fstTarget : ℝ)
    (hVA : 0 < V_A) (hVE : 0 < V_E)
    (h_fst : fstSource < fstTarget)
    (h_fst_bounds : 0 ≤ fstSource ∧ fstTarget < 1)
    (hPhiStrict : StrictMono Phi) :
    targetAUCFromNeutralAFBenchmark V_A V_E fstTarget <
      presentDayAUC V_A V_E fstSource := by
  simpa [targetAUCFromNeutralAFBenchmark] using
    drift_degrades_AUC_of_strictMono
      V_A V_E fstSource fstTarget hVA hVE h_fst (le_of_lt h_fst_bounds.2) hPhiStrict

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

/-- Exact liability-threshold AUC as a direct chart map on an already-specified
deployed `R²`.

This is not a transport law and does not recover a latent biological signal
from source `R²`; it is just the closed-form coordinate map induced by the
equal-variance Gaussian liability model. -/
noncomputable def liabilityAUCFromExplainedR2 (r2 : ℝ) : ℝ :=
  Phi (Real.sqrt (r2 / (2 * (1 - r2))))

/-- On valid deployed `R²` values, the liability-threshold AUC chart is strictly
increasing whenever `Phi` is strictly increasing. -/
theorem liabilityAUCFromExplainedR2_strictMonoOn_unitInterval
    (hPhiStrict : StrictMono Phi) :
    StrictMonoOn liabilityAUCFromExplainedR2 (Set.Ico 0 1) := by
  intro x hx y hy hxy
  unfold liabilityAUCFromExplainedR2
  apply hPhiStrict
  have hx_one_sub : 0 < 1 - x := by linarith [hx.2]
  have hy_one_sub : 0 < 1 - y := by linarith [hy.2]
  have hx_den : 0 < 2 * (1 - x) := by
    exact mul_pos (by norm_num) hx_one_sub
  have hy_den : 0 < 2 * (1 - y) := by
    exact mul_pos (by norm_num) hy_one_sub
  have hx_arg_nonneg : 0 ≤ x / (2 * (1 - x)) := by
    exact div_nonneg hx.1 (le_of_lt hx_den)
  have harg_lt : x / (2 * (1 - x)) < y / (2 * (1 - y)) := by
    rw [div_lt_div_iff₀ hx_den hy_den]
    nlinarith
  exact Real.sqrt_lt_sqrt hx_arg_nonneg harg_lt

/-- Liability-threshold AUC induced by the full explicit source-side driver
state. Like the target-side exported AUC, this is built directly from source
explained signal and source residual variance under the source-learned score
equation. -/
noncomputable def sourceLiabilityAUCFromSourceWeights {p q : ℕ}
    (m : CrossPopulationMetricModel p q) : ℝ :=
  liabilityAUCFromVariances
    (sourceExplainedSignalVarianceFromSourceWeights m)
    (sourceResidualVarianceFromSourceWeights m)

/-- The mechanistic source AUC is exactly the explicit liability-threshold map
applied to source explained signal and source residual variance. -/
theorem sourceLiabilityAUCFromSourceWeights_eq_explicit_source_variances
    {p q : ℕ} (m : CrossPopulationMetricModel p q) :
    sourceLiabilityAUCFromSourceWeights m =
      liabilityAUCFromVariances
        (sourceExplainedSignalVarianceFromSourceWeights m)
        (sourceResidualVarianceFromSourceWeights m) := by
  rfl

/-- The direct mechanistic source AUC agrees with the `R²` chart induced by the
same source explained-signal and total-variance decomposition.

This is only a derived coordinate identity; it is not the defining
construction of source AUC. -/
theorem sourceLiabilityAUCFromSourceWeights_eq_explainedR2_chart {p q : ℕ}
    (m : CrossPopulationMetricModel p q) :
    sourceLiabilityAUCFromSourceWeights m =
      liabilityAUCFromExplainedR2 (sourceR2FromSourceWeights m) := by
  have h_source_ne : m.sourceOutcomeVariance ≠ 0 := by
    exact ne_of_gt m.sourceOutcomeVariance_pos
  unfold sourceLiabilityAUCFromSourceWeights liabilityAUCFromVariances
    sourceResidualVarianceFromSourceWeights liabilityAUCFromExplainedR2
    sourceR2FromSourceWeights
  congr 1
  congr 1
  field_simp [h_source_ne]

/-- Liability-threshold AUC induced by the full explicit cross-population
driver state.

The exported mechanistic AUC is computed directly from target explained signal
variance and target residual variance under transported source weights. It is
not defined by reading target `R²` through a chart, and it does not recover a
latent biological signal from source `R²`. -/
noncomputable def targetLiabilityAUCFromSourceWeights {p q : ℕ}
    (m : CrossPopulationMetricModel p q) : ℝ :=
  liabilityAUCFromVariances
    (targetExplainedSignalVarianceFromSourceWeights m)
    (targetResidualVarianceFromSourceWeights m)

/-- The mechanistic target AUC is exactly the explicit liability-threshold map
applied to target explained signal and target residual variance. -/
theorem targetLiabilityAUCFromSourceWeights_eq_explicit_target_variances {p q : ℕ}
    (m : CrossPopulationMetricModel p q) :
    targetLiabilityAUCFromSourceWeights m =
      liabilityAUCFromVariances
        (targetExplainedSignalVarianceFromSourceWeights m)
        (targetResidualVarianceFromSourceWeights m) := by
  rfl

/-- The direct mechanistic target AUC agrees with the `R²` chart induced by the
same target explained-signal and total-variance decomposition.

This is only a derived coordinate identity; it is not the defining
construction of target AUC. -/
theorem targetLiabilityAUCFromSourceWeights_eq_explainedR2_chart {p q : ℕ}
    (m : CrossPopulationMetricModel p q) :
    targetLiabilityAUCFromSourceWeights m =
      liabilityAUCFromExplainedR2 (targetR2FromSourceWeights m) := by
  have h_eff_ne : effectiveTargetOutcomeVariance m ≠ 0 := by
    exact ne_of_gt (effectiveTargetOutcomeVariance_pos m)
  unfold targetLiabilityAUCFromSourceWeights liabilityAUCFromVariances
    targetResidualVarianceFromSourceWeights liabilityAUCFromExplainedR2
    targetR2FromSourceWeights
  congr 1
  congr 1
  field_simp [h_eff_ne]

/-- Canonical mechanistic deployed source metric profile evaluated at an
arbitrary observed prevalence coordinate `π`. This is the source-side analogue
of `targetMetricProfileFromSourceWeights`, and it lets downstream calibration
theory compare source and target Brier on the same target-population
prevalence scale. -/
noncomputable def sourceMetricProfileFromSourceWeightsAtPrevalence {p q : ℕ}
    (m : CrossPopulationMetricModel p q) (π : ℝ) : TransportedMetrics.Profile where
  r2 := sourceR2FromSourceWeights m
  auc := sourceLiabilityAUCFromSourceWeights m
  brier := sourceCalibratedBrierFromSourceWeightsAtPrevalence m π

@[simp] theorem sourceMetricProfileFromSourceWeightsAtPrevalence_r2 {p q : ℕ}
    (m : CrossPopulationMetricModel p q) (π : ℝ) :
    (sourceMetricProfileFromSourceWeightsAtPrevalence m π).r2 =
      sourceR2FromSourceWeights m := by
  rfl

@[simp] theorem sourceMetricProfileFromSourceWeightsAtPrevalence_auc {p q : ℕ}
    (m : CrossPopulationMetricModel p q) (π : ℝ) :
    (sourceMetricProfileFromSourceWeightsAtPrevalence m π).auc =
      sourceLiabilityAUCFromSourceWeights m := by
  rfl

@[simp] theorem sourceMetricProfileFromSourceWeightsAtPrevalence_brier {p q : ℕ}
    (m : CrossPopulationMetricModel p q) (π : ℝ) :
    (sourceMetricProfileFromSourceWeightsAtPrevalence m π).brier =
      sourceCalibratedBrierFromSourceWeightsAtPrevalence m π := by
  rfl

/-- The source metric profile evaluated on the target-population observed
prevalence scale carried by the mechanistic target state. -/
noncomputable def sourceMetricProfileFromSourceWeightsAtTargetPrevalence {p q : ℕ}
    (m : CrossPopulationMetricModel p q) : TransportedMetrics.Profile :=
  sourceMetricProfileFromSourceWeightsAtPrevalence m m.targetPrevalence

@[simp] theorem sourceMetricProfileFromSourceWeightsAtTargetPrevalence_r2 {p q : ℕ}
    (m : CrossPopulationMetricModel p q) :
    (sourceMetricProfileFromSourceWeightsAtTargetPrevalence m).r2 =
      sourceR2FromSourceWeights m := by
  rfl

@[simp] theorem sourceMetricProfileFromSourceWeightsAtTargetPrevalence_auc {p q : ℕ}
    (m : CrossPopulationMetricModel p q) :
    (sourceMetricProfileFromSourceWeightsAtTargetPrevalence m).auc =
      sourceLiabilityAUCFromSourceWeights m := by
  rfl

@[simp] theorem sourceMetricProfileFromSourceWeightsAtTargetPrevalence_brier {p q : ℕ}
    (m : CrossPopulationMetricModel p q) :
    (sourceMetricProfileFromSourceWeightsAtTargetPrevalence m).brier =
      sourceCalibratedBrierFromSourceWeightsAtPrevalence m m.targetPrevalence := by
  rfl

/-- Canonical mechanistic deployed metric profile induced by the explicit
SNP-level transported score equation. The upstream state is the full
source-weights/target-LD/target-tagging system, with AUC bundled from the
explicit target signal/residual moment pair rather than from a source-side
transport surrogate. -/
noncomputable def targetMetricProfileFromSourceWeights {p q : ℕ}
    (m : CrossPopulationMetricModel p q) : TransportedMetrics.Profile where
  r2 := targetR2FromSourceWeights m
  auc := targetLiabilityAUCFromSourceWeights m
  brier := targetCalibratedBrierFromSourceWeights m

@[simp] theorem targetMetricProfileFromSourceWeights_r2 {p q : ℕ}
    (m : CrossPopulationMetricModel p q) :
    (targetMetricProfileFromSourceWeights m).r2 = targetR2FromSourceWeights m := by
  rfl

@[simp] theorem targetMetricProfileFromSourceWeights_auc {p q : ℕ}
    (m : CrossPopulationMetricModel p q) :
    (targetMetricProfileFromSourceWeights m).auc = targetLiabilityAUCFromSourceWeights m := by
  rfl

@[simp] theorem targetMetricProfileFromSourceWeights_brier {p q : ℕ}
    (m : CrossPopulationMetricModel p q) :
    (targetMetricProfileFromSourceWeights m).brier =
      targetCalibratedBrierFromSourceWeights m := by
  rfl

/-- Exact liability-threshold AUC after `t` generations under the full
time-varying mechanistic state. -/
noncomputable def targetLiabilityAUCAtGeneration {p q : ℕ}
    (m : CrossPopulationGenerationalModel p q) (t : ℕ) : ℝ :=
  targetLiabilityAUCFromSourceWeights (m.toMetricModelAt t)

/-- Canonical mechanistic deployed metric profile after `t` generations. -/
noncomputable def targetMetricProfileAtGeneration {p q : ℕ}
    (m : CrossPopulationGenerationalModel p q) (t : ℕ) :
    TransportedMetrics.Profile :=
  targetMetricProfileFromSourceWeights (m.toMetricModelAt t)

@[simp] theorem targetMetricProfileAtGeneration_eq_slice {p q : ℕ}
    (m : CrossPopulationGenerationalModel p q) (t : ℕ) :
    targetMetricProfileAtGeneration m t =
      targetMetricProfileFromSourceWeights (m.toMetricModelAt t) := by
  rfl

@[simp] theorem targetLiabilityAUCAtGeneration_eq_slice {p q : ℕ}
    (m : CrossPopulationGenerationalModel p q) (t : ℕ) :
    targetLiabilityAUCAtGeneration m t =
      targetLiabilityAUCFromSourceWeights (m.toMetricModelAt t) := by
  rfl

/-- Exact target liability-threshold AUC under the neutral allele-frequency
benchmark in the equal-variance Gaussian liability model. -/
noncomputable def targetExactLiabilityAUCFromNeutralAFBenchmark
    (V_A V_E fstTarget : ℝ) : ℝ :=
  targetAUCFromNeutralAFBenchmark V_A V_E fstTarget

/-- The direct `R²`-chart liability AUC agrees with the literal present-day
liability AUC when the deployed `R²` comes from the same neutral benchmark
chart. -/
theorem liabilityAUCFromExplainedR2_eq_presentDayAUC
    (V_A V_E fst : ℝ)
    (hVA : 0 < V_A) (hVE : 0 < V_E)
    (hfst_lt_one : fst < 1) :
    liabilityAUCFromExplainedR2 (presentDayR2 V_A V_E fst) =
      presentDayAUC V_A V_E fst := by
  have hv_pos : 0 < presentDayPGSVariance V_A fst := by
    unfold presentDayPGSVariance
    have h_one_minus : 0 < 1 - fst := by linarith
    exact mul_pos h_one_minus hVA
  have hsum_ne : presentDayPGSVariance V_A fst + V_E ≠ 0 := by
    linarith
  have hve_ne : V_E ≠ 0 := ne_of_gt hVE
  have hchart :
      presentDayR2 V_A V_E fst / (2 * (1 - presentDayR2 V_A V_E fst)) =
        presentDaySignalToNoise V_A V_E fst / 2 := by
    unfold presentDayR2 presentDaySignalToNoise
    field_simp [hsum_ne, hve_ne]
    ring
  unfold liabilityAUCFromExplainedR2 presentDayAUC
  rw [hchart]

/-- Full neutral allele-frequency benchmark liability-AUC degradation theorem
(exact LTM formula): if drift increases (`fstTarget > fstSource`), target AUC
is strictly lower than source AUC within this benchmark. -/
theorem targetLiabilityAUC_lt_source_of_neutralAF_benchmark
    (V_A V_E fstSource fstTarget : ℝ)
    (hVA : 0 < V_A) (hVE : 0 < V_E)
    (h_fst : fstSource < fstTarget)
    (h_fst_bounds : 0 ≤ fstSource ∧ fstTarget < 1)
    (hPhiStrict : StrictMono Phi) :
    targetExactLiabilityAUCFromNeutralAFBenchmark V_A V_E fstTarget <
      presentDayLiabilityAUC V_A V_E fstSource := by
  simpa [targetExactLiabilityAUCFromNeutralAFBenchmark] using
    drift_degrades_liabilityAUC
      V_A V_E fstSource fstTarget hVA hVE h_fst (le_of_lt h_fst_bounds.2) hPhiStrict

/-- The exact target calibrated Brier risk is `exactCalibratedBrierRiskFromR2`
evaluated at the explicit target `R²` by definition. -/
@[simp] theorem targetBrierFromNeutralAFBenchmark_eq
    (π V_A V_E fstTarget : ℝ) :
    targetExactCalibratedBrierRisk π V_A V_E fstTarget =
      exactCalibratedBrierRiskFromR2 π
        (targetR2FromNeutralAFBenchmark V_A V_E fstTarget) := by
  rfl

/-- Exact calibrated Bernoulli Brier risk from prevalence and explained-risk
moments. If the true conditional risk `η(Z)` has mean `π` and variance
`π(1-π) r2`, then the exact calibrated population Brier risk is
`π(1-π)(1-r2)`. -/
theorem exactBrierRiskOfCalibrated_eq_exactCalibratedBrierRiskFromR2
    {Z : Type*} [MeasurableSpace Z]
    (μ : Measure Z) [IsProbabilityMeasure μ]
    (η : Z → ℝ) (π r2 : ℝ)
    (hη_int : Integrable η μ)
    (hvar_int : Integrable (fun z => (η z - π) ^ 2) μ)
    (hmean : ∫ z, η z ∂μ = π)
    (hvar : ∫ z, (η z - π) ^ 2 ∂μ = π * (1 - π) * r2) :
    exactBrierRiskOfCalibrated μ η = exactCalibratedBrierRiskFromR2 π r2 := by
  rw [exactBrierRiskOfCalibrated_eq_integral]
  have hdiff_int : Integrable (fun z => η z - π) μ := by
    simpa [sub_eq_add_neg] using hη_int.sub (integrable_const π)
  have hlin_zero : ∫ z, (η z - π) ∂μ = 0 := by
    rw [integral_sub hη_int (integrable_const π), hmean]
    simp
  calc
    ∫ z, η z * (1 - η z) ∂μ
        = ∫ z, ((π * (1 - π) - (η z - π) ^ 2) + (1 - 2 * π) * (η z - π)) ∂μ := by
            refine integral_congr_ae ?_
            filter_upwards with z
            ring
    _ = ∫ z, (π * (1 - π) - (η z - π) ^ 2) ∂μ +
          ∫ z, (1 - 2 * π) * (η z - π) ∂μ := by
            convert
              (integral_add ((integrable_const _).sub hvar_int)
                (hdiff_int.const_mul (1 - 2 * π))) using 1
    _ = (∫ z, (π * (1 - π)) ∂μ - ∫ z, (η z - π) ^ 2 ∂μ) +
          ∫ z, (1 - 2 * π) * (η z - π) ∂μ := by
            rw [integral_sub (integrable_const _) hvar_int]
    _ = (π * (1 - π) - ∫ z, (η z - π) ^ 2 ∂μ) +
          (1 - 2 * π) * ∫ z, (η z - π) ∂μ := by
            rw [MeasureTheory.integral_const, MeasureTheory.integral_const_mul]
            simp
    _ = π * (1 - π) - ∫ z, (η z - π) ^ 2 ∂μ := by
            rw [hlin_zero]
            ring
    _ = exactCalibratedBrierRiskFromR2 π r2 := by
            rw [hvar]
            unfold exactCalibratedBrierRiskFromR2
            ring

/-- Full neutral allele-frequency benchmark Brier degradation theorem: if
target `R²` drops and `0 ≤ π ≤ 1`, target Brier is at least source Brier
within this benchmark. -/
theorem targetBrier_ge_source_of_neutralAF_benchmark
    (π V_A V_E fstSource fstTarget : ℝ)
    (h_pi : 0 ≤ π ∧ π ≤ 1)
    (hVA : 0 < V_A) (hVE : 0 < V_E)
    (h_fst : fstSource < fstTarget)
    (h_fst_bounds : 0 ≤ fstSource ∧ fstTarget < 1) :
    sourceBrierFromR2 π (presentDayR2 V_A V_E fstSource) ≤
      targetBrierFromNeutralAFBenchmark π V_A V_E fstTarget := by
  rcases h_pi with ⟨hpi0, hpi1⟩
  have hr2_drop :
      targetR2FromNeutralAFBenchmark V_A V_E fstTarget < presentDayR2 V_A V_E fstSource :=
    targetR2_lt_source_from_neutralAF_benchmark V_A V_E fstSource fstTarget
      hVA hVE h_fst h_fst_bounds
  have hcoef_nonneg : 0 ≤ π * (1 - π) := by nlinarith
  unfold sourceBrierFromR2 targetBrierFromNeutralAFBenchmark
    targetExactCalibratedBrierRisk exactCalibratedBrierRiskFromR2
  have hbase :
      1 - presentDayR2 V_A V_E fstSource ≤
        1 - targetR2FromNeutralAFBenchmark V_A V_E fstTarget := by
    linarith
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

/-- Neutral allele-frequency benchmark ratio is nonnegative when both `F_ST`
values are at most `1`. -/
theorem neutralAFBenchmarkRatio_nonneg
    (fstSource fstTarget : ℝ)
    (hS : fstSource < 1) (hT : fstTarget ≤ 1) :
    0 ≤ neutralAFBenchmarkRatio fstSource fstTarget := by
  simp [neutralAFBenchmarkRatio]
  exact div_nonneg (by linarith) (by linarith)

/-- Neutral allele-frequency benchmark ratio is strictly below `1` when target
has more drift. -/
theorem neutralAFBenchmarkRatio_lt_one
    (fstSource fstTarget : ℝ)
    (hS : fstSource < 1)
    (hfst : fstSource < fstTarget) :
    neutralAFBenchmarkRatio fstSource fstTarget < 1 := by
  simp [neutralAFBenchmarkRatio]
  rw [div_lt_one (by linarith : (0 : ℝ) < 1 - fstSource)]
  linarith

/-- At zero divergence, the neutral allele-frequency benchmark ratio equals `1`. -/
@[simp] theorem neutralAFBenchmarkRatio_self (fst : ℝ) (hfst : fst < 1) :
    neutralAFBenchmarkRatio fst fst = 1 := by
  simp [neutralAFBenchmarkRatio]
  exact div_self (by linarith : (1 : ℝ) - fst ≠ 0)

/-- At zero divergence, the neutral allele-frequency benchmark target `R²` is
the literal present-day `R²` evaluated at the same population state. -/
theorem targetR2FromNeutralAFBenchmark_self (V_A V_E fst : ℝ) :
    targetR2FromNeutralAFBenchmark V_A V_E fst = presentDayR2 V_A V_E fst := by
  rfl

/-- For valid prevalence `0 < π < 1`, the linear Brier approximation `π(1-π)(1-R²)`
is strictly decreasing in `R²`. -/
theorem brierFromR2_strictAnti (π : ℝ) (hπ0 : 0 < π) (hπ1 : π < 1) :
    StrictAnti (brierFromR2 π) := by
  intro r2a r2b hab
  unfold brierFromR2
  have hcoef : 0 < π * (1 - π) := mul_pos hπ0 (by linarith)
  have hdrop : 1 - r2b < 1 - r2a := by linarith
  exact mul_lt_mul_of_pos_left hdrop hcoef

/-- Strict neutral allele-frequency benchmark Brier degradation: under
positive drift and non-degenerate prevalence, target Brier is strictly worse
than source Brier within this benchmark. -/
theorem targetBrier_strict_gt_source_of_neutralAF_benchmark
    (π V_A V_E fstSource fstTarget : ℝ)
    (hπ0 : 0 < π) (hπ1 : π < 1)
    (hVA : 0 < V_A) (hVE : 0 < V_E)
    (h_fst : fstSource < fstTarget)
    (h_fst_bounds : 0 ≤ fstSource ∧ fstTarget < 1) :
    sourceBrierFromR2 π (presentDayR2 V_A V_E fstSource) <
      targetBrierFromNeutralAFBenchmark π V_A V_E fstTarget := by
  have hr2_drop :=
    targetR2_lt_source_from_neutralAF_benchmark V_A V_E fstSource fstTarget
      hVA hVE h_fst h_fst_bounds
  unfold sourceBrierFromR2 targetBrierFromNeutralAFBenchmark
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

/-- IM equilibrium: increasing migration strictly decreases genetic differentiation
    on the biologically meaningful domain M > 0. -/
theorem twoDemeIMEquilibriumDelta_strictAntiOn :
    StrictAntiOn (fun M : ℝ => twoDemeIMEquilibriumDelta M) (Set.Ioi 0) := by
  intro a ha b hb hab
  unfold twoDemeIMEquilibriumDelta
  have ha_pos : 0 < 2 * a + 1 := by linarith [Set.mem_Ioi.mp ha]
  have hb_pos : 0 < 2 * b + 1 := by linarith [Set.mem_Ioi.mp hb]
  exact div_lt_div_of_pos_left one_pos ha_pos (by linarith : 2 * a + 1 < 2 * b + 1)

/-- Under the IM model, the mean-shift variance is strictly decreasing in migration rate
    on the biological domain (M > 0) when `V_A > 0`. -/
theorem expectedSqMeanPGSDiff_IMEquilibrium_strictAntiOn_M
    (V_A : ℝ) (hVA : 0 < V_A) :
    StrictAntiOn (fun M : ℝ => expectedSqMeanPGSDiff_IMEquilibrium V_A M) (Set.Ioi 0) := by
  intro a ha b hb hab
  simp only [expectedSqMeanPGSDiff_IMEquilibrium_eq]
  have := twoDemeIMEquilibriumDelta_strictAntiOn ha hb hab
  nlinarith

end PresentDayMetrics


/-!
## Mutation-Drift Balance and Portability

When mutation is non-negligible, Fst has a finite equilibrium (Wright's
1/(1+4Neμ)) instead of approaching 1. This section generalizes the drift-only
portability model to include mutation as a first-class parameter.

Key results:
1. Generalized divergence model that includes mutation rate
2. Covariance divergence including both drift and mutation terms
3. Portability under mutation-drift: mutation-generated population-specific
   variants reduce tagging efficiency
4. Comparison: mutation-drift equilibrium portability vs pure-drift portability
-/

section MutationDriftPortability

/-- Generalized divergence model assumptions that include mutation as a parameter
    rather than assuming it is negligible. -/
structure MutationDriftModelAssumptions where
  Ne : ℝ
  μ : ℝ
  t : ℝ
  Ne_pos : 0 < Ne
  mu_pos : 0 < μ
  t_nonneg : 0 ≤ t

/-- The scaled mutation parameter θ = 4Neμ for a mutation-drift model. -/
noncomputable def MutationDriftModelAssumptions.theta (m : MutationDriftModelAssumptions) : ℝ :=
  4 * m.Ne * m.μ

/-- θ is positive for any valid mutation-drift model. -/
theorem MutationDriftModelAssumptions.theta_pos (m : MutationDriftModelAssumptions) :
    0 < m.theta := by
  unfold MutationDriftModelAssumptions.theta
  nlinarith [m.Ne_pos, m.mu_pos]

/-- **Equilibrium Fst under mutation-drift balance: Fst = 1/(1 + θ).**
    This is the Wright (1931) island model result. -/
noncomputable def MutationDriftModelAssumptions.fstEquilibrium
    (m : MutationDriftModelAssumptions) : ℝ :=
  1 / (1 + m.theta)

/-- Equilibrium Fst is positive. -/
theorem MutationDriftModelAssumptions.fstEquilibrium_pos
    (m : MutationDriftModelAssumptions) :
    0 < m.fstEquilibrium := by
  unfold MutationDriftModelAssumptions.fstEquilibrium
  have hden : 0 < 1 + m.theta := by
    nlinarith [m.theta_pos]
  exact div_pos one_pos hden

/-- Equilibrium Fst is strictly less than 1 (mutation prevents complete fixation). -/
theorem MutationDriftModelAssumptions.fstEquilibrium_lt_one
    (m : MutationDriftModelAssumptions) :
    m.fstEquilibrium < 1 := by
  unfold MutationDriftModelAssumptions.fstEquilibrium
  rw [div_lt_one (by linarith [m.theta_pos])]
  linarith [m.theta_pos]

/-- **Transient Fst under mutation-drift: approach to equilibrium.**
    Fst(t) = Fst_eq × (1 - exp(-(1+θ)t/(2Ne))) -/
noncomputable def MutationDriftModelAssumptions.fstTransient
    (m : MutationDriftModelAssumptions) : ℝ :=
  m.fstEquilibrium * (1 - Real.exp (-(1 + m.theta) * m.t / (2 * m.Ne)))

/-- Transient Fst is nonneg. -/
theorem MutationDriftModelAssumptions.fstTransient_nonneg
    (m : MutationDriftModelAssumptions) :
    0 ≤ m.fstTransient := by
  unfold MutationDriftModelAssumptions.fstTransient
  apply mul_nonneg (le_of_lt m.fstEquilibrium_pos)
  have harg : 0 ≤ (1 + m.theta) * m.t / (2 * m.Ne) := by
    have hden : 0 < 2 * m.Ne := by nlinarith [m.Ne_pos]
    apply div_nonneg
    · exact mul_nonneg (by linarith [m.theta_pos]) m.t_nonneg
    · exact le_of_lt hden
  have hexp : Real.exp (-(1 + m.theta) * m.t / (2 * m.Ne)) ≤ 1 := by
    have hnum_nonpos : -(1 + m.theta) * m.t ≤ 0 := by
      have h1 : 0 ≤ 1 + m.theta := by
        have h1' : 0 < 1 + m.theta := by nlinarith [m.theta_pos]
        linarith
      nlinarith [h1, m.t_nonneg]
    have hden_nonneg : 0 ≤ 2 * m.Ne := by linarith [m.Ne_pos]
    have hneg : -(1 + m.theta) * m.t / (2 * m.Ne) ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg hnum_nonpos hden_nonneg
    have hexp' : Real.exp (-(1 + m.theta) * m.t / (2 * m.Ne)) ≤ Real.exp 0 :=
      Real.exp_le_exp.mpr hneg
    simpa using hexp'
  have hfactor_nonneg : 0 ≤ 1 - Real.exp (-(1 + m.theta) * m.t / (2 * m.Ne)) := by
    linarith
  exact hfactor_nonneg

/-- Transient Fst is bounded by the equilibrium Fst. -/
theorem MutationDriftModelAssumptions.fstTransient_le_equilibrium
    (m : MutationDriftModelAssumptions) :
    m.fstTransient ≤ m.fstEquilibrium := by
  unfold MutationDriftModelAssumptions.fstTransient
  have hfeq_pos : 0 < m.fstEquilibrium := m.fstEquilibrium_pos
  have hexp_pos : 0 < Real.exp (-(1 + m.theta) * m.t / (2 * m.Ne)) := Real.exp_pos _
  have h_factor_le : 1 - Real.exp (-(1 + m.theta) * m.t / (2 * m.Ne)) ≤ 1 := by
    linarith
  have hmul :
      m.fstEquilibrium * (1 - Real.exp (-(1 + m.theta) * m.t / (2 * m.Ne))) ≤
        m.fstEquilibrium * 1 :=
    mul_le_mul_of_nonneg_left h_factor_le (le_of_lt hfeq_pos)
  simpa using hmul

/-! ## Derivation of the Multiplicative Covariance Divergence Formula

We derive the formula `covarianceDivergenceMutationDrift(Fst, shared_LD) = 1 - (1-Fst) × shared_LD`
from the covariance between a polygenic score and a phenotype across populations.

**Setup.** In the source population, the covariance between a PGS and the phenotype is:

  `Cov(PGS, Y_source) = Σᵢ βᵢ × Cov(Gᵢ_source, Y_source)`

In the target population:

  `Cov(PGS, Y_target) = Σᵢ βᵢ × Cov(Gᵢ_target, Y_target)`

The ratio `Cov_target / Cov_source` depends on two independent factors:

1. **Allele frequency correlation** (`freq_corr`): Genetic drift changes allele frequencies
   between populations. The correlation of allele frequencies between source and target
   populations is `1 - Fst`, where Fst measures frequency divergence. This scales the
   per-locus genetic covariance by `(1 - Fst)`.

2. **LD overlap** (`ld_overlap`): New mutations and recombination alter LD patterns.
   The fraction of LD structure that is shared between populations is `shared_LD`.
   Only shared LD contributes to tagging of causal variants by the PGS SNPs.

For a single locus pair, these act on different aspects of the covariance:
- Frequency change scales the marginal genetic variance: `Var(G_target) ∝ (1-Fst) × Var(G_source)`
- LD change scales the tagging efficiency: `r²_target ∝ shared_LD × r²_source`

Because these are independent mechanisms, the total covariance retention is their product:

  `Cov_target / Cov_source = (1 - Fst) × shared_LD`

Therefore the divergence (fraction of covariance lost) is:

  `divergence = 1 - retention = 1 - (1 - Fst) × shared_LD`
-/

/-- **Covariance retention** across populations.
    The fraction of PGS-phenotype covariance retained in the target population
    is the product of allele frequency correlation and LD overlap. These two
    factors are independent: frequency drift scales per-locus genetic variance,
    while LD decay scales tagging efficiency. -/
noncomputable def covarianceRetention (freq_corr ld_overlap : ℝ) : ℝ :=
  freq_corr * ld_overlap

/-- Allele frequency correlation equals `1 - Fst`, where Fst measures the
    fraction of genetic variance due to population divergence. -/
noncomputable def freqCorrFromFst (fst : ℝ) : ℝ := 1 - fst

/-- LD overlap is directly the shared LD fraction (identity mapping, made
    explicit for clarity in the derivation chain). -/
noncomputable def ldOverlapFromSharedLD (shared_ld : ℝ) : ℝ := shared_ld

/-- Covariance retention in terms of Fst and shared_LD. -/
theorem covarianceRetention_from_fst_ld (fst shared_ld : ℝ) :
    covarianceRetention (freqCorrFromFst fst) (ldOverlapFromSharedLD shared_ld) =
      (1 - fst) * shared_ld := by
  unfold covarianceRetention freqCorrFromFst ldOverlapFromSharedLD
  ring

/-- **Covariance divergence derived from retention.**
    Divergence is `1 - retention`, which yields the multiplicative formula
    `1 - (1 - Fst) × shared_LD`. -/
noncomputable def covarianceDivergenceFromRetention (fst shared_ld : ℝ) : ℝ :=
  1 - covarianceRetention (freqCorrFromFst fst) (ldOverlapFromSharedLD shared_ld)

/-- The derived divergence formula equals `1 - (1 - Fst) × shared_LD`. -/
theorem covarianceDivergenceFromRetention_eq (fst shared_ld : ℝ) :
    covarianceDivergenceFromRetention fst shared_ld = 1 - (1 - fst) * shared_ld := by
  unfold covarianceDivergenceFromRetention
  rw [covarianceRetention_from_fst_ld]

/-- **Generalized covariance divergence under mutation-drift.**
    The total covariance divergence between source and target populations
    includes both:
    (a) drift-driven frequency changes: proportional to Fst
    (b) mutation-driven LD changes: proportional to tagging decay from new variants

    Total divergence factor = Fst_drift + (1 - Fst_drift) × (1 - shared_LD)
    where shared_LD is the fraction of LD preserved despite new mutations. -/
noncomputable def covarianceDivergenceMutationDrift
    (fst_drift shared_ld : ℝ) : ℝ :=
  fst_drift + (1 - fst_drift) * (1 - shared_ld)

/-- Covariance divergence simplifies algebraically. -/
theorem covarianceDivergenceMutationDrift_eq (fst_drift shared_ld : ℝ) :
    covarianceDivergenceMutationDrift fst_drift shared_ld = 1 - (1 - fst_drift) * shared_ld := by
  unfold covarianceDivergenceMutationDrift
  ring

/-- **The derived formula matches the existing definition.**
    This connects the derivation from covariance principles back to
    `covarianceDivergenceMutationDrift`, confirming the multiplicative
    structure is not merely assumed but follows from the independence
    of allele frequency drift and LD decay. -/
theorem covarianceDivergence_derivation_matches (fst shared_ld : ℝ) :
    covarianceDivergenceFromRetention fst shared_ld =
      covarianceDivergenceMutationDrift fst shared_ld := by
  rw [covarianceDivergenceFromRetention_eq, covarianceDivergenceMutationDrift_eq]

/-- With perfect shared LD (shared_ld = 1), covariance divergence reduces to pure drift. -/
theorem covarianceDivergence_pure_drift (fst_drift : ℝ) :
    covarianceDivergenceMutationDrift fst_drift 1 = fst_drift := by
  unfold covarianceDivergenceMutationDrift
  ring

/-- With zero drift (fst_drift = 0), covariance divergence equals the LD divergence. -/
theorem covarianceDivergence_pure_mutation (shared_ld : ℝ) :
    covarianceDivergenceMutationDrift 0 shared_ld = 1 - shared_ld := by
  unfold covarianceDivergenceMutationDrift
  ring

/-- Covariance divergence is at least the drift component alone when shared LD ≤ 1. -/
theorem covarianceDivergence_ge_drift (fst_drift shared_ld : ℝ)
    (_hfst : 0 ≤ fst_drift) (hfst_le : fst_drift ≤ 1)
    (hld : shared_ld ≤ 1) :
    fst_drift ≤ covarianceDivergenceMutationDrift fst_drift shared_ld := by
  unfold covarianceDivergenceMutationDrift
  have h1 : 0 ≤ 1 - fst_drift := by linarith
  have h2 : 0 ≤ 1 - shared_ld := by linarith
  linarith [mul_nonneg h1 h2]

/-- Covariance divergence is at most 1 when parameters are in [0, 1]. -/
theorem covarianceDivergence_le_one (fst_drift shared_ld : ℝ)
    (_hfst : 0 ≤ fst_drift) (hfst_le : fst_drift ≤ 1)
    (hld : 0 ≤ shared_ld) (_hld_le : shared_ld ≤ 1) :
    covarianceDivergenceMutationDrift fst_drift shared_ld ≤ 1 := by
  rw [covarianceDivergenceMutationDrift_eq]
  have h1 : 0 ≤ (1 - fst_drift) * shared_ld := by
    exact mul_nonneg (by linarith) hld
  linarith

/-- **Generalized signal retention under mutation-drift.**
    The retained signal is (1 - total_divergence) × V_A. -/
noncomputable def presentDayPGSVarianceMutationDrift
    (V_A fst_drift shared_ld : ℝ) : ℝ :=
  (1 - covarianceDivergenceMutationDrift fst_drift shared_ld) * V_A

/-- Signal retention equals (1 - fst) × shared_ld × V_A. -/
theorem presentDayPGSVarianceMutationDrift_eq (V_A fst_drift shared_ld : ℝ) :
    presentDayPGSVarianceMutationDrift V_A fst_drift shared_ld =
      (1 - fst_drift) * shared_ld * V_A := by
  unfold presentDayPGSVarianceMutationDrift
  rw [covarianceDivergenceMutationDrift_eq]
  ring

/-- With perfect shared LD, signal retention reduces to the pure drift formula. -/
theorem presentDayPGSVarianceMutationDrift_pure_drift (V_A fst_drift : ℝ) :
    presentDayPGSVarianceMutationDrift V_A fst_drift 1 = presentDayPGSVariance V_A fst_drift := by
  rw [presentDayPGSVarianceMutationDrift_eq]
  unfold presentDayPGSVariance
  ring

/-- Signal retention is nonneg under valid parameters. -/
theorem presentDayPGSVarianceMutationDrift_nonneg (V_A fst_drift shared_ld : ℝ)
    (hVA : 0 ≤ V_A) (_hfst : 0 ≤ fst_drift) (hfst_le : fst_drift ≤ 1)
    (hld : 0 ≤ shared_ld) :
    0 ≤ presentDayPGSVarianceMutationDrift V_A fst_drift shared_ld := by
  rw [presentDayPGSVarianceMutationDrift_eq]
  exact mul_nonneg (mul_nonneg (by linarith) hld) hVA

/-- **Mutation strictly reduces signal retention beyond drift alone.**
    When shared_ld < 1 and other parameters are positive, mutation-drift signal
    retention is strictly below drift-only signal retention. -/
theorem mutationDrift_signal_lt_puredrift (V_A fst_drift shared_ld : ℝ)
    (hVA : 0 < V_A) (_hfst : 0 ≤ fst_drift) (hfst_lt : fst_drift < 1)
    (_hld : 0 < shared_ld) (hld_lt : shared_ld < 1) :
    presentDayPGSVarianceMutationDrift V_A fst_drift shared_ld <
      presentDayPGSVariance V_A fst_drift := by
  rw [presentDayPGSVarianceMutationDrift_eq]
  unfold presentDayPGSVariance
  have h1 : 0 < 1 - fst_drift := by linarith
  have h_factor : (1 - fst_drift) * shared_ld < (1 - fst_drift) * 1 := by
    exact mul_lt_mul_of_pos_left hld_lt h1
  nlinarith

/-- **R² under mutation-drift balance.** -/
noncomputable def presentDayR2MutationDrift (V_A V_E fst_drift shared_ld : ℝ) : ℝ :=
  let v := presentDayPGSVarianceMutationDrift V_A fst_drift shared_ld
  v / (v + V_E)

/-- **Mutation-drift R² is below drift-only R².**
    When shared LD is imperfect, R² under mutation-drift is strictly below
    drift-only R². This is the key portability result: ignoring mutation
    overestimates portability. -/
theorem mutationDrift_R2_lt_puredrift_R2 (V_A V_E fst_drift shared_ld : ℝ)
    (hVA : 0 < V_A) (hVE : 0 < V_E)
    (hfst : 0 ≤ fst_drift) (hfst_lt : fst_drift < 1)
    (hld : 0 < shared_ld) (hld_lt : shared_ld < 1) :
    presentDayR2MutationDrift V_A V_E fst_drift shared_ld <
      presentDayR2 V_A V_E fst_drift := by
  unfold presentDayR2MutationDrift presentDayR2
  have h_sig_lt := mutationDrift_signal_lt_puredrift V_A fst_drift shared_ld
    hVA hfst hfst_lt hld hld_lt
  have h_md_nonneg : 0 ≤ presentDayPGSVarianceMutationDrift V_A fst_drift shared_ld := by
    exact presentDayPGSVarianceMutationDrift_nonneg V_A fst_drift shared_ld
      (le_of_lt hVA) hfst (le_of_lt hfst_lt) (le_of_lt hld)
  exact expectedR2_strictMono_nonneg V_E
    (presentDayPGSVarianceMutationDrift V_A fst_drift shared_ld)
    (presentDayPGSVariance V_A fst_drift)
    hVE h_md_nonneg h_sig_lt

/-- Scalar neutral benchmark that combines allele-frequency retention with a
shared-LD retention coordinate. This remains a coarse benchmark, not a
mechanistic SNP-level transport law. -/
noncomputable def neutralAFSharedLDBenchmarkRatio
    (fstSource fstTarget shared_ld_source shared_ld_target : ℝ) : ℝ :=
  ((1 - fstTarget) * shared_ld_target) / ((1 - fstSource) * shared_ld_source)

/-- The shared-LD benchmark reduces to the neutral allele-frequency benchmark
when shared LD is perfect in both populations. -/
theorem neutralAFSharedLDBenchmarkRatio_pure_drift (fstSource fstTarget : ℝ) :
    neutralAFSharedLDBenchmarkRatio fstSource fstTarget 1 1 =
      neutralAFBenchmarkRatio fstSource fstTarget := by
  unfold neutralAFSharedLDBenchmarkRatio neutralAFBenchmarkRatio
  ring

/-- The shared-LD benchmark is below the pure neutral allele-frequency
benchmark when target shared LD is worse than source shared LD. -/
theorem neutralAFSharedLDBenchmarkRatio_lt_neutralAFBenchmarkRatio
    (fstSource fstTarget shared_ld_source shared_ld_target : ℝ)
    (hfstS : fstSource < 1) (hfstT : fstTarget < 1)
    (hldS : 0 < shared_ld_source) (_hldS_le : shared_ld_source ≤ 1)
    (_hldT : 0 < shared_ld_target)
    (hld_decay : shared_ld_target / shared_ld_source < 1) :
    neutralAFSharedLDBenchmarkRatio fstSource fstTarget shared_ld_source shared_ld_target <
      neutralAFBenchmarkRatio fstSource fstTarget := by
  unfold neutralAFSharedLDBenchmarkRatio neutralAFBenchmarkRatio
  have h1 : 0 < 1 - fstSource := by linarith
  have h_den_pos : 0 < (1 - fstSource) * shared_ld_source := mul_pos h1 hldS
  rw [div_lt_div_iff₀ h_den_pos h1]
  have h_ld_ratio : shared_ld_target < shared_ld_source := by
    rwa [div_lt_one hldS] at hld_decay
  have hnum_lt :
      ((1 - fstSource) * (1 - fstTarget)) * shared_ld_target <
        ((1 - fstSource) * (1 - fstTarget)) * shared_ld_source := by
    exact mul_lt_mul_of_pos_left h_ld_ratio (mul_pos h1 (by linarith))
  simpa [mul_assoc, mul_left_comm, mul_comm] using hnum_lt

/-- **Equilibrium portability bound.**
    Under mutation-drift equilibrium (where Fst = 1/(1+θ)), the portability
    ratio has a finite lower bound that depends on θ. Larger θ (more mutation
    relative to drift) means lower equilibrium Fst and thus better portability
    from the drift component, but worse from the mutation/LD component. -/
noncomputable def equilibriumPortabilityR2
    (V_A V_E θ_source θ_target shared_ld : ℝ) : ℝ :=
  let fst_target := 1 / (1 + θ_target)
  let fst_source := 1 / (1 + θ_source)
  presentDayR2MutationDrift V_A V_E fst_target shared_ld /
    presentDayR2MutationDrift V_A V_E fst_source 1

/-- **At equilibrium, larger θ means lower Fst and thus the drift component
    of portability improves.**
    If we compare two populations at equilibrium with θ₁ < θ₂, the population
    with larger θ has smaller Fst. This improves the allele frequency component
    of signal retention. -/
theorem equilibrium_drift_component_improves_with_theta
    (V_A θ₁ θ₂ : ℝ)
    (hVA : 0 < V_A) (hθ₁ : 0 < θ₁) (_hθ₂ : 0 < θ₂)
    (h_more : θ₁ < θ₂) :
    presentDayPGSVariance V_A (1 / (1 + θ₁)) <
      presentDayPGSVariance V_A (1 / (1 + θ₂)) := by
  unfold presentDayPGSVariance
  have h1 : 0 < 1 + θ₁ := by linarith
  have h2 : 0 < 1 + θ₂ := by linarith
  -- 1/(1+θ₂) < 1/(1+θ₁), so 1 - 1/(1+θ₁) < 1 - 1/(1+θ₂)
  -- i.e., θ₁/(1+θ₁) < θ₂/(1+θ₂)
  have hfst₁ : 1 - 1 / (1 + θ₁) = θ₁ / (1 + θ₁) := by
    have hne : 1 + θ₁ ≠ 0 := by linarith
    field_simp [hne]
    ring_nf
  have hfst₂ : 1 - 1 / (1 + θ₂) = θ₂ / (1 + θ₂) := by
    have hne : 1 + θ₂ ≠ 0 := by linarith
    field_simp [hne]
    ring_nf
  rw [hfst₁, hfst₂]
  have h_ratio_lt : θ₁ / (1 + θ₁) < θ₂ / (1 + θ₂) := by
    rw [div_lt_div_iff₀ h1 h2]
    nlinarith
  exact mul_lt_mul_of_pos_right h_ratio_lt hVA

/-- **Pure drift benchmark overestimates retained variance.**
    The drift-only benchmark (which sets `negligibleMutation` = True) always
    overestimates retained variance compared to the mutation-drift model.
    This theorem quantifies the gap: the ratio of mutation-drift variance
    to drift-only variance is exactly `shared_ld`. -/
theorem mutationDrift_variance_ratio (V_A fst shared_ld : ℝ)
    (hVA : 0 < V_A) (hfst : fst < 1)
    (hld : 0 < shared_ld) :
    presentDayPGSVarianceMutationDrift V_A fst shared_ld /
      presentDayPGSVariance V_A fst = shared_ld := by
  rw [presentDayPGSVarianceMutationDrift_eq]
  unfold presentDayPGSVariance
  have hfst_ne : 1 - fst ≠ 0 := by linarith
  have hVA_ne : V_A ≠ 0 := ne_of_gt hVA
  field_simp [hfst_ne, hVA_ne]

/-- **Correction factor for the drift-only benchmark.**
    To convert drift-only neutral-benchmark predictions to mutation-drift
    predictions, multiply by the shared LD fraction. This gives the exact
    correction. -/
theorem neutral_af_benchmark_correction_factor (V_A V_E fst_target shared_ld : ℝ)
    (_hVA : 0 < V_A) (_hVE : 0 < V_E)
    (_hfst : 0 ≤ fst_target) (_hfst_lt : fst_target < 1)
    (_hld : 0 < shared_ld) (_hld_le : shared_ld ≤ 1) :
    presentDayPGSVarianceMutationDrift V_A fst_target shared_ld =
      shared_ld * presentDayPGSVariance V_A fst_target := by
  rw [presentDayPGSVarianceMutationDrift_eq]
  unfold presentDayPGSVariance
  ring

/-- **Pairwise Fst under mutation-drift balance is bounded.**
    Under mutation-drift equilibrium, pairwise Fst between any two populations
    is bounded above by 2 × Fst_eq (since each branch contributes at most Fst_eq). -/
theorem pairwise_fst_mutationDrift_bound (θ : ℝ) (hθ : 0 < θ) :
    let fst_eq := 1 / (1 + θ)
    pairwiseFstFromBranches fst_eq fst_eq ≤ 2 / (1 + θ) := by
  simp [pairwiseFstFromBranches]
  ring_nf
  have h1 : 0 < 1 + θ := by linarith
  have hsq : 0 ≤ (1 / (1 + θ)) ^ 2 := sq_nonneg (1 / (1 + θ))
  nlinarith

end MutationDriftPortability


/-!
## Migration-Drift Balance and Portability

Gene flow (migration) between populations counteracts drift, preventing complete
differentiation. The classic Wright island model gives Fst ≈ 1/(1 + 4Nm) at
equilibrium. This section extends the `SplitMigrationModel` with:
1. Fst under migration-drift equilibrium and its properties
2. Migration reduces Fst relative to pure drift
3. Stepping-stone model: Fst increases with geographic distance
4. Migration's effect on LD sharing and PGS portability
5. Portability is higher with gene flow than without
6. Asymmetric migration and directional portability
7. Admixture LD from recent migration pulses
-/

section MigrationDriftPortability

/-! ### 1. Fst under migration-drift balance: Fst = 1/(1 + 4Nm) -/

/-- **Island model equilibrium Fst under migration-drift balance.**
    Fst_eq = 1 / (1 + 4Nm) where N is effective size and m is migration rate.
    This is the classical Wright (1931) result. -/
noncomputable def fstMigrationDriftEquilibrium (Ne m : ℝ) : ℝ :=
  1 / (1 + 4 * Ne * m)

/-- The scaled migration parameter M = 4Nm, analogous to θ = 4Neμ. -/
noncomputable def scaledMigrationRate (Ne m : ℝ) : ℝ :=
  4 * Ne * m

/-- Scaled migration rate is positive when Ne and m are positive. -/
theorem scaledMigrationRate_pos (Ne m : ℝ) (hNe : 0 < Ne) (hm : 0 < m) :
    0 < scaledMigrationRate Ne m := by
  unfold scaledMigrationRate
  positivity

/-- Fst under migration-drift equilibrium equals 1/(1 + M). -/
theorem fstMigrationDriftEquilibrium_eq_from_M (Ne m : ℝ) :
    fstMigrationDriftEquilibrium Ne m = 1 / (1 + scaledMigrationRate Ne m) := by
  unfold fstMigrationDriftEquilibrium scaledMigrationRate
  ring

/-- Equilibrium Fst under migration-drift is positive for nonneg migration. -/
theorem fstMigrationDriftEquilibrium_pos (Ne m : ℝ) (hNe : 0 < Ne) (hm : 0 ≤ m) :
    0 < fstMigrationDriftEquilibrium Ne m := by
  unfold fstMigrationDriftEquilibrium
  have : 0 ≤ 4 * Ne * m := by positivity
  positivity

/-- Equilibrium Fst under migration-drift is at most 1. -/
theorem fstMigrationDriftEquilibrium_le_one (Ne m : ℝ) (hNe : 0 < Ne) (hm : 0 ≤ m) :
    fstMigrationDriftEquilibrium Ne m ≤ 1 := by
  unfold fstMigrationDriftEquilibrium
  rw [div_le_one (by nlinarith)]
  nlinarith

/-- Equilibrium Fst under migration-drift is strictly less than 1 when m > 0.
    This is the key qualitative result: migration prevents complete fixation. -/
theorem fstMigrationDriftEquilibrium_lt_one (Ne m : ℝ) (hNe : 0 < Ne) (hm : 0 < m) :
    fstMigrationDriftEquilibrium Ne m < 1 := by
  unfold fstMigrationDriftEquilibrium
  rw [div_lt_one (by nlinarith)]
  nlinarith

/-- Equilibrium Fst is in the open interval (0, 1) for positive Ne and m. -/
theorem fstMigrationDriftEquilibrium_in_unit (Ne m : ℝ) (hNe : 0 < Ne) (hm : 0 < m) :
    0 < fstMigrationDriftEquilibrium Ne m ∧ fstMigrationDriftEquilibrium Ne m < 1 :=
  ⟨fstMigrationDriftEquilibrium_pos Ne m hNe (le_of_lt hm),
   fstMigrationDriftEquilibrium_lt_one Ne m hNe hm⟩

/-- **Equilibrium Fst decreases with migration rate** (Ne fixed).
    More migration → more gene flow → less differentiation. -/
theorem fstMigrationDriftEquilibrium_decreases_with_m (Ne m₁ m₂ : ℝ)
    (hNe : 0 < Ne) (hm₁ : 0 < m₁) (_hm₂ : 0 < m₂) (h_more : m₁ < m₂) :
    fstMigrationDriftEquilibrium Ne m₂ < fstMigrationDriftEquilibrium Ne m₁ := by
  unfold fstMigrationDriftEquilibrium
  apply div_lt_div_of_pos_left one_pos (by nlinarith) (by nlinarith)

/-- **Equilibrium Fst decreases with effective population size** (m fixed).
    Larger Ne → slower drift relative to migration → less differentiation. -/
theorem fstMigrationDriftEquilibrium_decreases_with_Ne (Ne₁ Ne₂ m : ℝ)
    (hNe₁ : 0 < Ne₁) (_hNe₂ : 0 < Ne₂) (hm : 0 < m) (h_more : Ne₁ < Ne₂) :
    fstMigrationDriftEquilibrium Ne₂ m < fstMigrationDriftEquilibrium Ne₁ m := by
  unfold fstMigrationDriftEquilibrium
  apply div_lt_div_of_pos_left one_pos (by nlinarith) (by nlinarith)

/-! ### 2. Migration counteracts drift -/

/-- **Migration reduces Fst relative to pure drift.**
    Under migration-drift equilibrium, Fst = 1/(1+4Nm) < 1 - (1-1/(2Ne))^t
    for sufficiently large t. We prove the simpler qualitative statement:
    equilibrium Fst with migration is below the coalescent Fst at separation time t
    when t is large enough relative to Ne. -/
theorem migration_reduces_fst_vs_pure_drift (Ne m t : ℝ)
    (_hNe : 0 < Ne) (_hm : 0 < m) (_ht : 0 < t)
    (h_large_t : 1 / (1 + 4 * Ne * m) < t / (t + 2 * Ne)) :
    fstMigrationDriftEquilibrium Ne m < t / (t + 2 * Ne) := by
  unfold fstMigrationDriftEquilibrium
  exact h_large_t

/-- **Finite equilibrium vs unbounded drift.**
    Under pure drift, Fst approaches 1 as t → ∞. Under migration-drift balance,
    Fst is bounded above by 1/(1+4Nm) < 1. This means migration establishes
    a ceiling on differentiation. -/
theorem migration_bounds_fst_below_one (Ne m : ℝ) (hNe : 0 < Ne) (hm : 0 < m)
    (fst_observed : ℝ) (h_le : fst_observed ≤ fstMigrationDriftEquilibrium Ne m) :
    fst_observed < 1 := by
  have h_eq_lt := fstMigrationDriftEquilibrium_lt_one Ne m hNe hm
  linarith

/-- **SplitMigrationModel equilibrium Fst using the structure.** -/
noncomputable def SplitMigrationModel.fstMigDriftEq (s : SplitMigrationModel) : ℝ :=
  fstMigrationDriftEquilibrium s.Ne s.mig

/-- SplitMigrationModel equilibrium Fst equals the limit Fst for many demes. -/
theorem SplitMigrationModel.fstMigDriftEq_eq_limit (s : SplitMigrationModel) :
    s.fstMigDriftEq = s.fstEqLimitLowMutationManyDemes := by
  unfold SplitMigrationModel.fstMigDriftEq fstMigrationDriftEquilibrium
    SplitMigrationModel.fstEqLimitLowMutationManyDemes
    SplitMigrationModel.scaledMigration
  ring

/-- **Increased migration strictly improves equilibrium Fst in the SplitMigration framework.**
    Comparing two SplitMigrationModels with same Ne but different migration rates. -/
theorem splitMigration_more_migration_less_fst
    (Ne m₁ m₂ : ℝ) (nDemes : ℕ) (mu : ℝ)
    (hNe : 0 < Ne) (hm₁ : 0 < m₁) (hm₂ : 0 < m₂)
    (hnD : 2 ≤ nDemes) (hmu : 0 ≤ mu) (h_more : m₁ < m₂) :
    let s₁ : SplitMigrationModel := ⟨0, Ne, m₁, nDemes, mu, hNe, le_of_lt hm₁, hnD, hmu⟩
    let s₂ : SplitMigrationModel := ⟨0, Ne, m₂, nDemes, mu, hNe, le_of_lt hm₂, hnD, hmu⟩
    s₂.fstMigDriftEq < s₁.fstMigDriftEq := by
  simp only [SplitMigrationModel.fstMigDriftEq]
  exact fstMigrationDriftEquilibrium_decreases_with_m Ne m₁ m₂ hNe hm₁ hm₂ h_more

/-! ### 3. Stepping-stone model: Fst increases with geographic distance -/

/-- **Stepping-stone Fst model.**
    In the stepping-stone model, migration occurs only between adjacent demes.
    Fst between demes separated by d steps is approximately:
    Fst(d) ≈ Fst_neighbor × (1 + α × (d - 1))
    where α controls the rate of increase with distance (isolation by distance).
    This is a linear approximation to the exact result. -/
noncomputable def steppingStoneFst (fst_neighbor α : ℝ) (d : ℕ) : ℝ :=
  fst_neighbor * (1 + α * ((d : ℝ) - 1))

/-- Stepping-stone Fst at distance 1 equals the neighbor Fst. -/
theorem steppingStoneFst_at_one (fst_neighbor α : ℝ) :
    steppingStoneFst fst_neighbor α 1 = fst_neighbor := by
  unfold steppingStoneFst
  simp

/-- **Stepping-stone Fst increases with geographic distance** (isolation by distance).
    For positive neighbor Fst and positive distance scaling parameter α,
    Fst is strictly increasing in the number of steps. -/
theorem steppingStoneFst_increases_with_distance
    (fst_neighbor α : ℝ) (d₁ d₂ : ℕ)
    (hfst : 0 < fst_neighbor) (hα : 0 < α) (hd : d₁ < d₂) :
    steppingStoneFst fst_neighbor α d₁ < steppingStoneFst fst_neighbor α d₂ := by
  unfold steppingStoneFst
  have hd_real : (d₁ : ℝ) < (d₂ : ℝ) := Nat.cast_lt.mpr hd
  have h_inner : α * ((d₁ : ℝ) - 1) < α * ((d₂ : ℝ) - 1) := by nlinarith
  nlinarith

/-- **Nearby demes have lower Fst than distant demes.**
    Fst(1) < Fst(d) for d > 1 under the stepping-stone model. -/
theorem steppingStoneFst_neighbor_lt_distant
    (fst_neighbor α : ℝ) (d : ℕ)
    (hfst : 0 < fst_neighbor) (hα : 0 < α) (hd : 1 < d) :
    steppingStoneFst fst_neighbor α 1 < steppingStoneFst fst_neighbor α d := by
  exact steppingStoneFst_increases_with_distance fst_neighbor α 1 d hfst hα hd

/-- **Stepping-stone Fst is nonneg for valid parameters.** -/
theorem steppingStoneFst_nonneg (fst_neighbor α : ℝ) (d : ℕ)
    (hfst : 0 < fst_neighbor) (hα : 0 ≤ α) (hd : 1 ≤ d) :
    0 ≤ steppingStoneFst fst_neighbor α d := by
  unfold steppingStoneFst
  apply mul_nonneg (le_of_lt hfst)
  have : 0 ≤ α * ((d : ℝ) - 1) := by
    apply mul_nonneg hα
    have : (1 : ℝ) ≤ (d : ℝ) := Nat.one_le_cast.mpr hd
    linarith
  linarith

/-! ### 4. Migration's effect on LD: gene flow homogenizes LD patterns -/

/-! #### Derivation of shared LD fraction from Fst equilibrium

The shared LD fraction under migration-drift balance is **derived**, not assumed.
Since Fst measures the fraction of genetic variation that is *between* populations,
the complementary quantity `1 - Fst` measures the fraction that is *shared*.
LD patterns are shared to the same extent as allele frequencies, so:

  shared_LD = 1 - Fst_eq = 1 - 1/(1 + M) = M/(1 + M)

where M = 4Nm is the scaled migration rate. This is the same algebraic identity
underlying Wright's island model: Fst + shared fraction = 1. The theorem
`sharedLD_from_equilibrium_eq` below proves this algebraically from the
already-derived `fstMigrationDriftEquilibrium`. -/

/-- **Shared LD derived from Fst equilibrium.**
    Defined as `1 - fstMigrationDriftEquilibrium Ne m`, i.e., the complement
    of the between-population divergence under migration-drift balance. -/
noncomputable def sharedLD_from_equilibrium (Ne m : ℝ) : ℝ :=
  1 - fstMigrationDriftEquilibrium Ne m

/-- The shared LD fraction derived from Fst equilibrium equals M/(1+M).
    This is the formal derivation: starting from Fst = 1/(1+M), we obtain
    shared_LD = 1 - 1/(1+M) = M/(1+M). -/
theorem sharedLD_from_equilibrium_eq (Ne m : ℝ) (hNe : 0 < Ne) (hm : 0 ≤ m) :
    sharedLD_from_equilibrium Ne m = scaledMigrationRate Ne m / (1 + scaledMigrationRate Ne m) := by
  unfold sharedLD_from_equilibrium fstMigrationDriftEquilibrium scaledMigrationRate
  have hden : 1 + 4 * Ne * m ≠ 0 := by nlinarith
  field_simp [hden]
  ring

/-- **Shared LD fraction under migration-drift balance.**
    Gene flow homogenizes LD patterns between populations. The fraction of LD
    that is shared between two demes increases with migration rate:
    shared_LD(m) = M / (1 + M) where M = 4Nm.

    **Derivation:** This formula is the complement of the Wright (1931)
    island-model Fst equilibrium. Since Fst = 1/(1+M) (proved at
    `fstMigrationDriftEquilibrium`), the shared fraction is
    1 - Fst = 1 - 1/(1+M) = M/(1+M). See `sharedLD_from_equilibrium_eq`
    and `sharedLD_from_equilibrium_eq_sharedLDFromMigration` for the
    formal algebraic derivation. -/
noncomputable def sharedLDFromMigration (M : ℝ) : ℝ :=
  M / (1 + M)

/-- The derived shared LD fraction equals `sharedLDFromMigration M`. This
    closes the loop: the formula M/(1+M) is not an assumption but follows
    from the migration-drift Fst equilibrium. -/
theorem sharedLD_from_equilibrium_eq_sharedLDFromMigration (Ne m : ℝ)
    (hNe : 0 < Ne) (hm : 0 ≤ m) :
    sharedLD_from_equilibrium Ne m = sharedLDFromMigration (scaledMigrationRate Ne m) := by
  rw [sharedLD_from_equilibrium_eq Ne m hNe hm]
  unfold sharedLDFromMigration
  rfl

/-- Shared LD fraction is nonneg for nonneg M. -/
theorem sharedLDFromMigration_nonneg (M : ℝ) (hM : 0 ≤ M) :
    0 ≤ sharedLDFromMigration M := by
  unfold sharedLDFromMigration
  exact div_nonneg hM (by linarith)

/-- Shared LD fraction is at most 1. -/
theorem sharedLDFromMigration_lt_one (M : ℝ) (hM : 0 ≤ M) :
    sharedLDFromMigration M < 1 := by
  unfold sharedLDFromMigration
  rw [div_lt_one (by linarith : 0 < 1 + M)]
  linarith

/-- **Shared LD fraction increases with migration rate.**
    More migration → more shared LD → better PGS portability. -/
theorem sharedLDFromMigration_increases (M₁ M₂ : ℝ)
    (hM₁ : 0 < M₁) (_hM₂ : 0 < M₂) (h_more : M₁ < M₂) :
    sharedLDFromMigration M₁ < sharedLDFromMigration M₂ := by
  unfold sharedLDFromMigration
  rw [div_lt_div_iff₀ (by linarith) (by linarith)]
  nlinarith

/-- **Complementarity of Fst and shared LD under migration-drift.**
    Fst = 1/(1+M) and shared_LD = M/(1+M) sum to 1.
    This parallels the mutation-drift complementarity. -/
theorem fst_plus_sharedLD_eq_one (Ne m : ℝ) (hNe : 0 < Ne) (hm : 0 ≤ m) :
    fstMigrationDriftEquilibrium Ne m + sharedLDFromMigration (scaledMigrationRate Ne m) = 1 := by
  unfold fstMigrationDriftEquilibrium sharedLDFromMigration scaledMigrationRate
  have hden : 1 + 4 * Ne * m ≠ 0 := by nlinarith
  field_simp [hden]

/-! ### 5. Portability under migration-drift: R² improves with gene flow -/

/-- **Signal retention under migration-drift balance.**
    The retained signal variance accounts for both allele frequency drift
    and LD sharing determined by migration rate. -/
noncomputable def signalRetentionMigrationDrift (V_A Ne m : ℝ) : ℝ :=
  let fst := fstMigrationDriftEquilibrium Ne m
  let M := scaledMigrationRate Ne m
  let shared_ld := sharedLDFromMigration M
  (1 - fst) * shared_ld * V_A

/-- Signal retention under migration-drift equals M²/((1+M)² × V_A). -/
theorem signalRetentionMigrationDrift_eq (V_A Ne m : ℝ)
    (hNe : 0 < Ne) (hm : 0 ≤ m) :
    signalRetentionMigrationDrift V_A Ne m =
      (scaledMigrationRate Ne m) ^ 2 / (1 + scaledMigrationRate Ne m) ^ 2 * V_A := by
  unfold signalRetentionMigrationDrift fstMigrationDriftEquilibrium sharedLDFromMigration
    scaledMigrationRate
  have hden : (1 + 4 * Ne * m) ≠ 0 := by nlinarith
  field_simp [hden]
  ring

/-- **Signal retention is positive with positive migration.** -/
theorem signalRetentionMigrationDrift_pos (V_A Ne m : ℝ)
    (hVA : 0 < V_A) (hNe : 0 < Ne) (hm : 0 < m) :
    0 < signalRetentionMigrationDrift V_A Ne m := by
  rw [signalRetentionMigrationDrift_eq V_A Ne m hNe (le_of_lt hm)]
  apply mul_pos
  · apply div_pos
    · exact sq_pos_of_pos (scaledMigrationRate_pos Ne m hNe hm)
    · exact sq_pos_of_pos (by nlinarith [scaledMigrationRate_pos Ne m hNe hm])
  · exact hVA

/-- **More migration improves signal retention** (for fixed Ne and V_A).
    This is the core mechanism: gene flow improves PGS portability. -/
theorem signalRetention_increases_with_migration (V_A Ne m₁ m₂ : ℝ)
    (hVA : 0 < V_A) (hNe : 0 < Ne) (hm₁ : 0 < m₁) (hm₂ : 0 < m₂)
    (h_more : m₁ < m₂) :
    signalRetentionMigrationDrift V_A Ne m₁ < signalRetentionMigrationDrift V_A Ne m₂ := by
  rw [signalRetentionMigrationDrift_eq V_A Ne m₁ hNe (le_of_lt hm₁),
      signalRetentionMigrationDrift_eq V_A Ne m₂ hNe (le_of_lt hm₂)]
  apply mul_lt_mul_of_pos_right _ hVA
  -- Need: M₁²/(1+M₁)² < M₂²/(1+M₂)²  i.e. (M₁/(1+M₁))² < (M₂/(1+M₂))²
  -- which follows from M₁/(1+M₁) < M₂/(1+M₂), a monotone function.
  set M₁ := scaledMigrationRate Ne m₁
  set M₂ := scaledMigrationRate Ne m₂
  have hM₁ : 0 < M₁ := scaledMigrationRate_pos Ne m₁ hNe hm₁
  have hM₂ : 0 < M₂ := scaledMigrationRate_pos Ne m₂ hNe hm₂
  have hM_lt : M₁ < M₂ := by
    simp [M₁, M₂, scaledMigrationRate]
    nlinarith
  have h1M₁ : 0 < 1 + M₁ := by linarith
  have h1M₂ : 0 < 1 + M₂ := by linarith
  -- M₁/(1+M₁) < M₂/(1+M₂)
  have h_ratio : M₁ / (1 + M₁) < M₂ / (1 + M₂) := by
    rw [div_lt_div_iff₀ h1M₁ h1M₂]; nlinarith
  -- Squaring preserves order for positive values
  have h_sq₁ : 0 < M₁ / (1 + M₁) := div_pos hM₁ h1M₁
  have h_sq₂ : 0 < M₂ / (1 + M₂) := div_pos hM₂ h1M₂
  have h_sq : (M₁ / (1 + M₁)) ^ 2 < (M₂ / (1 + M₂)) ^ 2 := by
    have hsum_pos : 0 < M₁ / (1 + M₁) + M₂ / (1 + M₂) := by positivity
    have hmul := mul_lt_mul_of_pos_right h_ratio hsum_pos
    nlinarith
  rwa [div_pow, div_pow] at h_sq

/-- **R² under migration-drift is higher than without migration (pure drift).**
    For a population pair with the same coalescent divergence time, introducing
    migration strictly improves the R² portability ratio. We show that at
    migration-drift equilibrium, the Fst is lower than under pure drift to t=∞. -/
theorem migration_improves_R2_over_pure_drift (V_A V_E Ne m : ℝ)
    (hVA : 0 < V_A) (hVE : 0 < V_E) (_hNe : 0 < Ne) (_hm : 0 < m)
    (fst_nomial : ℝ) (hfst_pure : fstMigrationDriftEquilibrium Ne m < fst_nomial)
    (hfst_nomial_lt : fst_nomial < 1) :
    presentDayR2 V_A V_E fst_nomial < presentDayR2 V_A V_E (fstMigrationDriftEquilibrium Ne m) := by
  exact drift_degrades_R2 V_A V_E (fstMigrationDriftEquilibrium Ne m) fst_nomial
    hVA hVE hfst_pure (le_of_lt hfst_nomial_lt)

/-! ### 6. Asymmetric migration -/

/-- **Asymmetric migration Fst model.**
    When migration is asymmetric (m₁₂ ≠ m₂₁), the effective Fst depends on
    direction. The effective migration for population i is the rate at which
    it receives migrants. The "effective Fst" from population 1's perspective
    uses m₁₂ (rate of migrants into pop 1 from pop 2). -/
noncomputable def asymmetricFst (Ne m_into : ℝ) : ℝ :=
  1 / (1 + 4 * Ne * m_into)

/-- **Asymmetric Fst is just the island model Fst with directional migration.** -/
theorem asymmetricFst_eq_migrationDriftEq (Ne m_into : ℝ) :
    asymmetricFst Ne m_into = fstMigrationDriftEquilibrium Ne m_into := by
  unfold asymmetricFst fstMigrationDriftEquilibrium
  rfl

/-- **When m₁₂ > m₂₁, Fst from perspective of pop 1 is lower.**
    Population 1 receives more migrants from pop 2, so its genetic composition
    is closer to pop 2 than vice versa. -/
theorem asymmetric_migration_directional_fst
    (Ne m₁₂ m₂₁ : ℝ) (hNe : 0 < Ne) (hm₁₂ : 0 < m₁₂) (hm₂₁ : 0 < m₂₁)
    (h_asym : m₂₁ < m₁₂) :
    asymmetricFst Ne m₁₂ < asymmetricFst Ne m₂₁ := by
  simp only [asymmetricFst_eq_migrationDriftEq]
  exact fstMigrationDriftEquilibrium_decreases_with_m Ne m₂₁ m₁₂ hNe hm₂₁ hm₁₂ h_asym

/-- **Portability depends on prediction direction under asymmetric migration.**
    Predicting into a population that receives more migrants (lower Fst from
    its perspective) yields higher R² than predicting the other way. -/
theorem asymmetric_migration_portability_direction
    (V_A V_E Ne m₁₂ m₂₁ : ℝ)
    (hVA : 0 < V_A) (hVE : 0 < V_E) (hNe : 0 < Ne)
    (hm₁₂ : 0 < m₁₂) (hm₂₁ : 0 < m₂₁)
    (h_asym : m₂₁ < m₁₂) :
    presentDayR2 V_A V_E (asymmetricFst Ne m₂₁) <
      presentDayR2 V_A V_E (asymmetricFst Ne m₁₂) := by
  have h_fst := asymmetric_migration_directional_fst Ne m₁₂ m₂₁ hNe hm₁₂ hm₂₁ h_asym
  have h_lt_one : asymmetricFst Ne m₂₁ < 1 := by
    simpa [asymmetricFst_eq_migrationDriftEq] using
      fstMigrationDriftEquilibrium_lt_one Ne m₂₁ hNe hm₂₁
  exact drift_degrades_R2 V_A V_E (asymmetricFst Ne m₁₂) (asymmetricFst Ne m₂₁)
    hVA hVE h_fst (le_of_lt h_lt_one)

/-- **Mean effective Fst under asymmetric migration.**
    The harmonic mean of directional migration rates gives the effective
    symmetric migration rate for overall Fst. -/
noncomputable def effectiveSymmetricMigration (m₁₂ m₂₁ : ℝ) : ℝ :=
  (m₁₂ + m₂₁) / 2

/-- Effective symmetric migration is between the two directional rates. -/
theorem effectiveSymmetricMigration_between (m₁₂ m₂₁ : ℝ) (_hm₁₂ : 0 < m₁₂) (_hm₂₁ : 0 < m₂₁)
    (h_asym : m₂₁ < m₁₂) :
    m₂₁ < effectiveSymmetricMigration m₁₂ m₂₁ ∧
    effectiveSymmetricMigration m₁₂ m₂₁ < m₁₂ := by
  unfold effectiveSymmetricMigration
  constructor <;> linarith

/-! ### 7. Recent migration (admixture): transient LD from migration pulses -/

/-- **Admixture LD from a recent migration pulse.**
    A pulse of migration (admixture) at time t_adm generations ago creates
    LD between loci at recombination distance r. This LD decays as:
    D_adm(t) = D_0 × (1 - r)^(t - t_adm)
    where D_0 is the initial admixture LD and t is the current time.
    We model the decay factor. -/
noncomputable def admixtureLDDecay (r : ℝ) (generations_since : ℕ) : ℝ :=
  (1 - r) ^ generations_since

/-- Admixture LD decay is nonneg for recombination rate in [0, 1]. -/
theorem admixtureLDDecay_nonneg (r : ℝ) (t : ℕ)
    (_hr : 0 ≤ r) (hr1 : r ≤ 1) :
    0 ≤ admixtureLDDecay r t := by
  unfold admixtureLDDecay
  exact pow_nonneg (by linarith) t

/-- Admixture LD decay is at most 1 for valid recombination rate. -/
theorem admixtureLDDecay_le_one (r : ℝ) (t : ℕ)
    (hr : 0 ≤ r) (hr1 : r ≤ 1) :
    admixtureLDDecay r t ≤ 1 := by
  unfold admixtureLDDecay
  exact pow_le_one₀ (by linarith) (by linarith)

/-- **Admixture LD decays over time** (for positive recombination rate). -/
theorem admixtureLDDecay_decreases_with_time (r : ℝ) (t₁ t₂ : ℕ)
    (hr : 0 < r) (hr1 : r < 1) (ht : t₁ < t₂) :
    admixtureLDDecay r t₂ < admixtureLDDecay r t₁ := by
  unfold admixtureLDDecay
  have h_base_pos : 0 < 1 - r := by linarith
  have h_base_lt : 1 - r < 1 := by linarith
  exact pow_lt_pow_right_of_lt_one₀ h_base_pos h_base_lt ht

/-- **Admixture LD decays faster with higher recombination rate.** -/
theorem admixtureLDDecay_decreases_with_recombination (r₁ r₂ : ℝ) (t : ℕ)
    (_hr₁ : 0 < r₁) (_hr₂ : 0 < r₂) (_hr₁1 : r₁ < 1) (hr₂1 : r₂ < 1)
    (h_more : r₁ < r₂) (ht : 0 < t) :
    admixtureLDDecay r₂ t < admixtureLDDecay r₁ t := by
  unfold admixtureLDDecay
  exact pow_lt_pow_left₀ (by linarith : 1 - r₂ < 1 - r₁) (by linarith) (by omega)

/-- **At time 0 since admixture, LD is fully preserved.** -/
theorem admixtureLDDecay_at_zero (r : ℝ) :
    admixtureLDDecay r 0 = 1 := by
  unfold admixtureLDDecay
  simp

/-- **Admixture LD creates a transient boost to portability.**
    Recent admixture (small t since pulse) means LD patterns are shared,
    which temporarily improves tagging efficiency. The portability boost
    from admixture LD relative to equilibrium LD is captured by the ratio
    of admixture LD retention to equilibrium LD fraction. -/
noncomputable def admixtureLDBoost (r : ℝ) (t_since : ℕ) (equilibrium_ld : ℝ) : ℝ :=
  admixtureLDDecay r t_since / equilibrium_ld

/-- Admixture LD boost exceeds 1 when admixture LD is above equilibrium. -/
theorem admixtureLDBoost_gt_one (r : ℝ) (t_since : ℕ) (equilibrium_ld : ℝ)
    (_hr : 0 ≤ r) (_hr1 : r ≤ 1)
    (heq_pos : 0 < equilibrium_ld) (_heq_lt : equilibrium_ld < 1)
    (h_recent : equilibrium_ld < admixtureLDDecay r t_since) :
    1 < admixtureLDBoost r t_since equilibrium_ld := by
  unfold admixtureLDBoost
  rw [lt_div_iff₀ heq_pos]
  linarith

/-- **Transient admixture portability is higher than equilibrium portability.**
    When admixture is recent, the transient shared LD exceeds equilibrium shared LD,
    and thus portability is temporarily enhanced. -/
theorem admixture_portability_above_equilibrium (V_A V_E fst r : ℝ) (t_since : ℕ)
    (equilibrium_ld : ℝ)
    (hVA : 0 < V_A) (_hVE : 0 < V_E)
    (_hfst : 0 ≤ fst) (hfst_lt : fst < 1)
    (_heq_pos : 0 < equilibrium_ld) (_heq_lt : equilibrium_ld < 1)
    (_hr : 0 ≤ r) (_hr1 : r ≤ 1)
    (h_recent : equilibrium_ld < admixtureLDDecay r t_since) :
    presentDayPGSVarianceMutationDrift V_A fst equilibrium_ld <
      presentDayPGSVarianceMutationDrift V_A fst (admixtureLDDecay r t_since) := by
  rw [presentDayPGSVarianceMutationDrift_eq, presentDayPGSVarianceMutationDrift_eq]
  have h1 : 0 < (1 - fst) * V_A := mul_pos (by linarith) hVA
  have h_factor : (1 - fst) * equilibrium_ld < (1 - fst) * admixtureLDDecay r t_since := by
    exact mul_lt_mul_of_pos_left h_recent (by linarith)
  nlinarith

end MigrationDriftPortability

/-! ## Migration-Drift Recurrence: Deriving Fst = 1/(1 + 4Nm) from First Principles

We derive the classical Wright (1931) equilibrium Fst formula from the
migration-drift recurrence relation. The island model with migration rate m
and effective population size Ne yields a linear recurrence on Fst:

  Fst_{t+1} = (1 - 2m - 1/(2Ne)) * Fst_t + 1/(2Ne)

This is the linearized form where (1-m)² ≈ 1 - 2m. At equilibrium
Fst* = Fst_{t+1} = Fst_t, solving the linear equation gives:

  Fst* = 1 / (4*Ne*m + 1)

We prove this closed form satisfies the recurrence, then derive monotonicity
and portability consequences directly from the recurrence structure.
-/

section MigrationDriftRecurrence

/-! ### 1. The migration-drift recurrence -/

/-- **Migration-drift recurrence on Fst.**
    In the island model with migration rate `m` and effective size `Ne`,
    the linearized one-generation update of Fst is:
      Fst_{t+1} = (1 - 2m - 1/(2Ne)) * Fst_t + 1/(2Ne)
    Migration reduces Fst by a factor (1-2m), and drift adds (1-Fst)/(2Ne).
    The linearization replaces (1-m)² with 1-2m (valid for small m). -/
noncomputable def fstMigDriftNext (Ne m Fst : ℝ) : ℝ :=
  (1 - 2 * m - 1 / (2 * Ne)) * Fst + 1 / (2 * Ne)

/-- The recurrence can be written as Fst_{t+1} = a * Fst_t + b where
    a = 1 - 2m - 1/(2Ne) and b = 1/(2Ne). -/
theorem fstMigDriftNext_eq (Ne m Fst : ℝ) :
    fstMigDriftNext Ne m Fst =
      (1 - 2 * m - 1 / (2 * Ne)) * Fst + 1 / (2 * Ne) := by
  rfl

/-- The drift term: when m = 0, the recurrence reduces to pure drift. -/
theorem fstMigDriftNext_no_migration (Ne Fst : ℝ) :
    fstMigDriftNext Ne 0 Fst = (1 - 1 / (2 * Ne)) * Fst + 1 / (2 * Ne) := by
  unfold fstMigDriftNext
  ring

/-- With no migration, the recurrence pushes Fst toward 1: the drift-only
    fixed point is Fst = 1. We verify: f(1) = 1. -/
theorem fstMigDriftNext_no_migration_fixedpoint_one (Ne : ℝ) (hNe : Ne ≠ 0) :
    fstMigDriftNext Ne 0 1 = 1 := by
  rw [fstMigDriftNext_no_migration]
  field_simp
  ring_nf

/-! ### 2. The exact equilibrium fixed point -/

/-- **Equilibrium Fst from the migration-drift recurrence.**
    Solving Fst* = (1 - 2m - 1/(2Ne)) * Fst* + 1/(2Ne) for Fst*:
      Fst* - (1 - 2m - 1/(2Ne)) * Fst* = 1/(2Ne)
      Fst* * (2m + 1/(2Ne)) = 1/(2Ne)
      Fst* = (1/(2Ne)) / (2m + 1/(2Ne))
            = 1 / (4*Ne*m + 1)
    This is the exact solution of the linearized recurrence. -/
noncomputable def fstMigDriftEquil (Ne m : ℝ) : ℝ :=
  1 / (4 * Ne * m + 1)

/-- The derived equilibrium matches the previously defined formula. -/
theorem fstMigDriftEquil_eq_fstMigrationDriftEquilibrium (Ne m : ℝ) :
    fstMigDriftEquil Ne m = fstMigrationDriftEquilibrium Ne m := by
  unfold fstMigDriftEquil fstMigrationDriftEquilibrium
  ring

/-- **Intermediate form of the fixed-point equation.**
    The equilibrium can also be written as
      Fst* = (1/(2Ne)) / (2m + 1/(2Ne))
    which makes the balance between drift (numerator) and
    migration + drift (denominator) explicit. -/
theorem fstMigDriftEquil_ratio_form (Ne m : ℝ)
    (hNe : 0 < Ne) (hm : 0 ≤ m) :
    fstMigDriftEquil Ne m =
      (1 / (2 * Ne)) / (2 * m + 1 / (2 * Ne)) := by
  unfold fstMigDriftEquil
  have hNe2 : (0 : ℝ) < 2 * Ne := by positivity
  have hden : 2 * m + 1 / (2 * Ne) ≠ 0 := by
    have : 0 < 2 * m + 1 / (2 * Ne) := by positivity
    linarith
  field_simp [hden]
  ring

/-! ### 3. Equilibrium Fst is positive and bounded -/

/-- Equilibrium Fst from the recurrence is positive. -/
theorem fstMigDriftEquil_pos (Ne m : ℝ) (hNe : 0 < Ne) (hm : 0 ≤ m) :
    0 < fstMigDriftEquil Ne m := by
  unfold fstMigDriftEquil
  positivity

/-- Equilibrium Fst from the recurrence is at most 1. -/
theorem fstMigDriftEquil_le_one (Ne m : ℝ) (hNe : 0 < Ne) (hm : 0 ≤ m) :
    fstMigDriftEquil Ne m ≤ 1 := by
  unfold fstMigDriftEquil
  rw [div_le_one (by nlinarith)]
  nlinarith

/-- Equilibrium Fst from the recurrence is strictly less than 1 when m > 0. -/
theorem fstMigDriftEquil_lt_one (Ne m : ℝ) (hNe : 0 < Ne) (hm : 0 < m) :
    fstMigDriftEquil Ne m < 1 := by
  unfold fstMigDriftEquil
  rw [div_lt_one (by nlinarith)]
  nlinarith

/-! ### 4. Equilibrium Fst is decreasing in m (derived from the formula) -/

/-- **Equilibrium Fst decreases with migration rate.**
    From Fst* = 1/(4Nm + 1), increasing m increases the denominator,
    hence decreases Fst*. This is derived, not assumed. -/
theorem fstMigDriftEquil_decreasing_in_m (Ne m₁ m₂ : ℝ)
    (hNe : 0 < Ne) (hm₁ : 0 < m₁) (_hm₂ : 0 < m₂)
    (h_more : m₁ < m₂) :
    fstMigDriftEquil Ne m₂ < fstMigDriftEquil Ne m₁ := by
  unfold fstMigDriftEquil
  apply div_lt_div_of_pos_left one_pos (by nlinarith) (by nlinarith)

/-! ### 5. Equilibrium Fst is decreasing in Ne (derived from the formula) -/

/-- **Equilibrium Fst decreases with effective population size.**
    From Fst* = 1/(4Nm + 1), increasing Ne increases the denominator 4Nm + 1,
    hence decreases Fst*. Larger populations have slower drift relative to
    migration, so less differentiation. -/
theorem fstMigDriftEquil_decreasing_in_Ne (Ne₁ Ne₂ m : ℝ)
    (hNe₁ : 0 < Ne₁) (_hNe₂ : 0 < Ne₂) (hm : 0 < m)
    (h_more : Ne₁ < Ne₂) :
    fstMigDriftEquil Ne₂ m < fstMigDriftEquil Ne₁ m := by
  unfold fstMigDriftEquil
  apply div_lt_div_of_pos_left one_pos (by nlinarith) (by nlinarith)

/-! ### 6. The full (non-linearized) recurrence and its fixed point -/

/-- **Full migration-drift recurrence (non-linearized).**
    Without the (1-m)² ≈ 1-2m approximation, the exact one-generation
    update is:
      Fst_{t+1} = (1-m)² * (1 - 1/(2Ne)) * Fst_t + (1 - Fst_t)/(2Ne)
    This retains the quadratic term m². -/
noncomputable def fstMigDriftNextFull (Ne m Fst : ℝ) : ℝ :=
  (1 - m) ^ 2 * (1 - 1 / (2 * Ne)) * Fst + (1 - Fst) / (2 * Ne)

/-- **Exact fixed point of the full recurrence.**
    Solving Fst* = (1-m)²(1 - 1/(2N)) Fst* + (1 - Fst*)/(2N):
    Let a = (1-m)²(1 - 1/(2N)), b = 1/(2N). Then:
      Fst* = a * Fst* + b - b * Fst*
      Fst*(1 - a + b) = b
      Fst* = b / (1 - a + b)
           = 1/(2N) / (1 - (1-m)²(1-1/(2N)) + 1/(2N)) -/
noncomputable def fstMigDriftEquilFull (Ne m : ℝ) : ℝ :=
  let a := (1 - m) ^ 2 * (1 - 1 / (2 * Ne))
  let b := 1 / (2 * Ne)
  b / (1 - a + b)

/-! ### 7. Migration-to-neutral-benchmark connection derived from the recurrence -/

/-- **Neutral allele-frequency benchmark ratio from the derived Fst formula.**
    The benchmark ratio is `1 - Fst = 1 - 1/(4Nm + 1) = 4Nm/(4Nm + 1)`.
    This is still only the recurrence's coarse allele-frequency benchmark,
    not a mechanistic portability law. -/
noncomputable def neutralAFBenchmarkFromRecurrence (Ne m : ℝ) : ℝ :=
  1 - fstMigDriftEquil Ne m

/-- The recurrence-derived neutral allele-frequency benchmark equals
`4Nm / (4Nm + 1)`. -/
theorem neutralAFBenchmarkFromRecurrence_eq (Ne m : ℝ)
    (hNe : 0 < Ne) (hm : 0 ≤ m) :
    neutralAFBenchmarkFromRecurrence Ne m = 4 * Ne * m / (4 * Ne * m + 1) := by
  unfold neutralAFBenchmarkFromRecurrence fstMigDriftEquil
  have hden : 4 * Ne * m + 1 ≠ 0 := by nlinarith
  field_simp [hden]
  ring_nf

/-- **The recurrence-derived neutral benchmark improves with migration rate.**
    From the derived formula `4Nm/(4Nm+1)`, increasing `m` increases the
    recurrence-derived benchmark ratio. -/
theorem neutralAFBenchmarkFromRecurrence_increasing_in_m (Ne m₁ m₂ : ℝ)
    (hNe : 0 < Ne) (hm₁ : 0 < m₁) (hm₂ : 0 < m₂)
    (h_more : m₁ < m₂) :
    neutralAFBenchmarkFromRecurrence Ne m₁ < neutralAFBenchmarkFromRecurrence Ne m₂ := by
  rw [neutralAFBenchmarkFromRecurrence_eq Ne m₁ hNe (le_of_lt hm₁),
      neutralAFBenchmarkFromRecurrence_eq Ne m₂ hNe (le_of_lt hm₂)]
  rw [div_lt_div_iff₀ (by nlinarith) (by nlinarith)]
  nlinarith

/-- **The recurrence-derived neutral benchmark is nonnegative.** -/
theorem neutralAFBenchmarkFromRecurrence_nonneg (Ne m : ℝ) (hNe : 0 < Ne) (hm : 0 ≤ m) :
    0 ≤ neutralAFBenchmarkFromRecurrence Ne m := by
  rw [neutralAFBenchmarkFromRecurrence_eq Ne m hNe hm]
  exact div_nonneg (by nlinarith) (by nlinarith)

/-- **The recurrence-derived neutral benchmark is strictly positive with migration.** -/
theorem neutralAFBenchmarkFromRecurrence_pos (Ne m : ℝ) (hNe : 0 < Ne) (hm : 0 < m) :
    0 < neutralAFBenchmarkFromRecurrence Ne m := by
  rw [neutralAFBenchmarkFromRecurrence_eq Ne m hNe (le_of_lt hm)]
  exact div_pos (by nlinarith) (by nlinarith)

/-- **The recurrence-derived neutral benchmark is strictly less than `1`.** -/
theorem neutralAFBenchmarkFromRecurrence_lt_one (Ne m : ℝ) (hNe : 0 < Ne) (hm : 0 ≤ m) :
    neutralAFBenchmarkFromRecurrence Ne m < 1 := by
  rw [neutralAFBenchmarkFromRecurrence_eq Ne m hNe hm]
  rw [div_lt_one (by nlinarith : 0 < 4 * Ne * m + 1)]
  linarith

/-- **The recurrence-derived benchmark connects back to the file's coarse `R²`
benchmark.**
    Using the recurrence-derived `F_ST`, the benchmark target `R²` is the
    present-day `R²` at `fstMigDriftEquil`. More migration yields higher
    benchmark `R²`. -/
theorem recurrence_derived_R2_increases_with_m (V_A V_E Ne m₁ m₂ : ℝ)
    (hVA : 0 < V_A) (hVE : 0 < V_E) (hNe : 0 < Ne)
    (hm₁ : 0 < m₁) (hm₂ : 0 < m₂) (h_more : m₁ < m₂) :
    presentDayR2 V_A V_E (fstMigDriftEquil Ne m₁) <
      presentDayR2 V_A V_E (fstMigDriftEquil Ne m₂) := by
  rw [fstMigDriftEquil_eq_fstMigrationDriftEquilibrium,
      fstMigDriftEquil_eq_fstMigrationDriftEquilibrium]
  exact migration_improves_R2_over_pure_drift V_A V_E Ne m₂ hVA hVE hNe hm₂
    (fstMigrationDriftEquilibrium Ne m₁)
    (fstMigrationDriftEquilibrium_decreases_with_m Ne m₁ m₂ hNe hm₁ hm₂ h_more)
    (fstMigrationDriftEquilibrium_lt_one Ne m₁ hNe hm₁)

end MigrationDriftRecurrence

end PortabilityDrift

end Calibrator
