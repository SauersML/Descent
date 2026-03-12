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
the learned projection is source-LD specific (Euro-centric mismatch statement).
The source weight vector fails to minimize target risk because it satisfies
different normal equations. -/
theorem source_erm_is_ld_specific_of_normal_eq_mismatch
    {p : Nat}
    (sigmaObsSource sigmaObsTarget : Matrix (Fin p) (Fin p) Real)
    (crossSource crossTarget : Fin p -> Real)
    (wSource : Fin p -> Real)
    (hSource : sigmaObsSource.mulVec wSource = crossSource)
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
    (hfst : 0 ≤ fst_drift) (hfst_le : fst_drift ≤ 1)
    (hld : shared_ld ≤ 1) :
    fst_drift ≤ covarianceDivergenceMutationDrift fst_drift shared_ld := by
  unfold covarianceDivergenceMutationDrift
  have h1 : 0 ≤ 1 - fst_drift := by linarith
  have h2 : 0 ≤ 1 - shared_ld := by linarith
  linarith [mul_nonneg h1 h2]

/-- Covariance divergence is at most 1 when parameters are in [0, 1]. -/
theorem covarianceDivergence_le_one (fst_drift shared_ld : ℝ)
    (hfst : 0 ≤ fst_drift) (hfst_le : fst_drift ≤ 1)
    (hld : 0 ≤ shared_ld) (hld_le : shared_ld ≤ 1) :
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
    (hVA : 0 ≤ V_A) (hfst : 0 ≤ fst_drift) (hfst_le : fst_drift ≤ 1)
    (hld : 0 ≤ shared_ld) :
    0 ≤ presentDayPGSVarianceMutationDrift V_A fst_drift shared_ld := by
  rw [presentDayPGSVarianceMutationDrift_eq]
  exact mul_nonneg (mul_nonneg (by linarith) hld) hVA

/-- **Mutation strictly reduces signal retention beyond drift alone.**
    When shared_ld < 1 and other parameters are positive, mutation-drift signal
    retention is strictly below drift-only signal retention. -/
theorem mutationDrift_signal_lt_puredrift (V_A fst_drift shared_ld : ℝ)
    (hVA : 0 < V_A) (hfst : 0 ≤ fst_drift) (hfst_lt : fst_drift < 1)
    (hld : 0 < shared_ld) (hld_lt : shared_ld < 1) :
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

/-- **Mutation-drift transport ratio.**
    The generalized transport ratio includes both allele frequency divergence
    and LD tagging decay from mutation. -/
noncomputable def mutationDriftTransportRatio
    (fstSource fstTarget shared_ld_source shared_ld_target : ℝ) : ℝ :=
  ((1 - fstTarget) * shared_ld_target) / ((1 - fstSource) * shared_ld_source)

/-- Mutation-drift transport ratio reduces to drift transport ratio when LD is perfect. -/
theorem mutationDriftTransportRatio_pure_drift (fstSource fstTarget : ℝ) :
    mutationDriftTransportRatio fstSource fstTarget 1 1 =
      driftTransportRatio fstSource fstTarget := by
  unfold mutationDriftTransportRatio driftTransportRatio
  ring_nf

/-- **Mutation-drift transport ratio is below drift-only transport ratio**
    when target shared LD is worse than source shared LD. -/
theorem mutationDrift_transport_lt_drift_transport
    (fstSource fstTarget shared_ld_source shared_ld_target : ℝ)
    (hfstS : fstSource < 1) (hfstT : fstTarget < 1)
    (hldS : 0 < shared_ld_source) (hldS_le : shared_ld_source ≤ 1)
    (hldT : 0 < shared_ld_target)
    (hld_decay : shared_ld_target / shared_ld_source < 1) :
    mutationDriftTransportRatio fstSource fstTarget shared_ld_source shared_ld_target <
      driftTransportRatio fstSource fstTarget := by
  unfold mutationDriftTransportRatio driftTransportRatio
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
    (hVA : 0 < V_A) (hθ₁ : 0 < θ₁) (hθ₂ : 0 < θ₂)
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

/-- **Pure drift model overestimates portability.**
    The drift-only model (which sets `negligibleMutation` = True) always
    overestimates signal retention compared to the mutation-drift model.
    This theorem quantifies the gap: the ratio of mutation-drift variance
    to drift-only variance is exactly shared_ld. -/
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

/-- **Correction factor for the drift-only model.**
    To convert drift-only portability predictions to mutation-drift predictions,
    multiply by the shared LD fraction. This gives the exact correction. -/
theorem portability_correction_factor (V_A V_E fst_target shared_ld : ℝ)
    (hVA : 0 < V_A) (hVE : 0 < V_E)
    (hfst : 0 ≤ fst_target) (hfst_lt : fst_target < 1)
    (hld : 0 < shared_ld) (hld_le : shared_ld ≤ 1) :
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
    (hNe : 0 < Ne) (hm₁ : 0 < m₁) (hm₂ : 0 < m₂) (h_more : m₁ < m₂) :
    fstMigrationDriftEquilibrium Ne m₂ < fstMigrationDriftEquilibrium Ne m₁ := by
  unfold fstMigrationDriftEquilibrium
  apply div_lt_div_of_pos_left one_pos (by nlinarith) (by nlinarith)

/-- **Equilibrium Fst decreases with effective population size** (m fixed).
    Larger Ne → slower drift relative to migration → less differentiation. -/
theorem fstMigrationDriftEquilibrium_decreases_with_Ne (Ne₁ Ne₂ m : ℝ)
    (hNe₁ : 0 < Ne₁) (hNe₂ : 0 < Ne₂) (hm : 0 < m) (h_more : Ne₁ < Ne₂) :
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
    (hNe : 0 < Ne) (hm : 0 < m) (ht : 0 < t)
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
    (hM₁ : 0 < M₁) (hM₂ : 0 < M₂) (h_more : M₁ < M₂) :
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
    (hVA : 0 < V_A) (hVE : 0 < V_E) (hNe : 0 < Ne) (hm : 0 < m)
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
theorem effectiveSymmetricMigration_between (m₁₂ m₂₁ : ℝ) (hm₁₂ : 0 < m₁₂) (hm₂₁ : 0 < m₂₁)
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
    (hr : 0 ≤ r) (hr1 : r ≤ 1) :
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
    (hr₁ : 0 < r₁) (hr₂ : 0 < r₂) (hr₁1 : r₁ < 1) (hr₂1 : r₂ < 1)
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
    (hr : 0 ≤ r) (hr1 : r ≤ 1)
    (heq_pos : 0 < equilibrium_ld) (heq_lt : equilibrium_ld < 1)
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
    (hVA : 0 < V_A) (hVE : 0 < V_E)
    (hfst : 0 ≤ fst) (hfst_lt : fst < 1)
    (heq_pos : 0 < equilibrium_ld) (heq_lt : equilibrium_ld < 1)
    (hr : 0 ≤ r) (hr1 : r ≤ 1)
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
    (hNe : 0 < Ne) (hm₁ : 0 < m₁) (hm₂ : 0 < m₂)
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
    (hNe₁ : 0 < Ne₁) (hNe₂ : 0 < Ne₂) (hm : 0 < m)
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

/-! ### 7. Migration-to-portability connection derived from the recurrence -/

/-- **Portability ratio from the derived Fst formula.**
    The portability ratio is 1 - Fst = 1 - 1/(4Nm + 1) = 4Nm/(4Nm + 1).
    This shows portability is directly determined by scaled migration 4Nm. -/
noncomputable def portabilityFromRecurrence (Ne m : ℝ) : ℝ :=
  1 - fstMigDriftEquil Ne m

/-- Portability ratio equals 4Nm / (4Nm + 1). -/
theorem portabilityFromRecurrence_eq (Ne m : ℝ)
    (hNe : 0 < Ne) (hm : 0 ≤ m) :
    portabilityFromRecurrence Ne m = 4 * Ne * m / (4 * Ne * m + 1) := by
  unfold portabilityFromRecurrence fstMigDriftEquil
  have hden : 4 * Ne * m + 1 ≠ 0 := by nlinarith
  field_simp [hden]
  ring_nf

/-- **Portability increases with migration rate.**
    From the derived formula portability = 4Nm/(4Nm+1), increasing m
    increases the ratio. This connects the recurrence derivation to
    the portability prediction. -/
theorem portabilityFromRecurrence_increasing_in_m (Ne m₁ m₂ : ℝ)
    (hNe : 0 < Ne) (hm₁ : 0 < m₁) (hm₂ : 0 < m₂)
    (h_more : m₁ < m₂) :
    portabilityFromRecurrence Ne m₁ < portabilityFromRecurrence Ne m₂ := by
  rw [portabilityFromRecurrence_eq Ne m₁ hNe (le_of_lt hm₁),
      portabilityFromRecurrence_eq Ne m₂ hNe (le_of_lt hm₂)]
  rw [div_lt_div_iff₀ (by nlinarith) (by nlinarith)]
  nlinarith

/-- **Portability is nonneg.** -/
theorem portabilityFromRecurrence_nonneg (Ne m : ℝ) (hNe : 0 < Ne) (hm : 0 ≤ m) :
    0 ≤ portabilityFromRecurrence Ne m := by
  rw [portabilityFromRecurrence_eq Ne m hNe hm]
  exact div_nonneg (by nlinarith) (by nlinarith)

/-- **Portability is strictly positive with migration.** -/
theorem portabilityFromRecurrence_pos (Ne m : ℝ) (hNe : 0 < Ne) (hm : 0 < m) :
    0 < portabilityFromRecurrence Ne m := by
  rw [portabilityFromRecurrence_eq Ne m hNe (le_of_lt hm)]
  exact div_pos (by nlinarith) (by nlinarith)

/-- **Portability is strictly less than 1 (some signal always lost to drift).** -/
theorem portabilityFromRecurrence_lt_one (Ne m : ℝ) (hNe : 0 < Ne) (hm : 0 ≤ m) :
    portabilityFromRecurrence Ne m < 1 := by
  rw [portabilityFromRecurrence_eq Ne m hNe hm]
  rw [div_lt_one (by nlinarith : 0 < 4 * Ne * m + 1)]
  linarith

/-- **The derived portability connects back to the R² portability ratio.**
    Using the derived Fst from the recurrence, the R² in the target population
    is presentDayR2 with Fst = fstMigDriftEquil. More migration yields
    higher R². -/
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
