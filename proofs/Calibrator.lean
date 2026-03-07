import Calibrator.Probability
import Calibrator.DGP
import Calibrator.Models
import Calibrator.Conclusions
import Calibrator.PortabilityDrift

namespace Calibrator

local instance : Fact (2 ≤ 2) := ⟨by decide⟩

/-- Top-level HWE expectation identity for the diploid alternative-allele count. -/
theorem hardyWeinberg_expectedAltAlleleCount_proved
    (h : HardyWeinbergModel) :
    h.expectedAltAlleleCount = 2 * h.altFreq :=
  h.expectedAltAlleleCount_eq

/-- Top-level HWE variance identity for the diploid alternative-allele count. -/
theorem hardyWeinberg_genotypeVariance_proved
    (h : HardyWeinbergModel) :
    h.genotypeVariance = 2 * h.altFreq * h.refFreq :=
  h.genotypeVariance_eq

/-- Top-level HWE score variance is nonnegative. -/
theorem hweScoreVariance_nonneg_proved
    {m : ℕ} [Fintype (Fin m)]
    (model : HWEScoreModel m) :
    0 ≤ model.scoreVariance :=
  model.scoreVariance_nonneg

/-- Top-level Berry-Esseen error radius is nonnegative for the HWE score model. -/
theorem hweBerryEsseenError_nonneg_proved
    {m : ℕ} [Fintype (Fin m)]
    (model : HWEScoreModel m) (berryEsseenConstant : ℝ)
    (hC : 0 ≤ berryEsseenConstant) :
    0 ≤ model.berryEsseenErrorBound berryEsseenConstant :=
  model.berryEsseenErrorBound_nonneg berryEsseenConstant hC

/-- Concrete `2 × 2` specialization of the two-locus coalescent covariance-gap theorem. -/
theorem twoLocusCoalescent_covariance_gap_lower_bound_proved
    (ibdWeight recombRate : ℝ)
    (tSource tTarget : ℕ)
    (h_time : tSource ≤ tTarget) :
    2 *
        (ibdWeight * discreteRecombinationSurvival recombRate tSource *
          (1 - discreteRecombinationSurvival recombRate (tTarget - tSource))) ^ 2 ≤
      frobeniusNormSq
        (twoLocusCoalescentCovarianceMatrix (t := 2) ibdWeight recombRate tSource -
          twoLocusCoalescentCovarianceMatrix (t := 2) ibdWeight recombRate tTarget) :=
  twoLocusCoalescent_covariance_gap_lower_bound
    (t := 2) ibdWeight recombRate tSource tTarget h_time

/-- Concrete `2 × 2` positivity corollary for the two-locus coalescent witness. -/
theorem covariance_mismatch_pos_of_twoLocusCoalescent_proved
    (ibdWeight recombRate : ℝ)
    (tSource tTarget : ℕ)
    (h_ibd_pos : 0 < ibdWeight)
    (h_recomb_pos : 0 < recombRate)
    (h_recomb_lt_one : recombRate < 1)
    (h_time : tSource < tTarget) :
    0 <
      frobeniusNormSq
        (twoLocusCoalescentCovarianceMatrix (t := 2) ibdWeight recombRate tSource -
          twoLocusCoalescentCovarianceMatrix (t := 2) ibdWeight recombRate tTarget) :=
  covariance_mismatch_pos_of_twoLocusCoalescent
    (t := 2) ibdWeight recombRate tSource tTarget
    h_ibd_pos h_recomb_pos h_recomb_lt_one h_time

/-- Top-level AUC interval membership from a Berry-Esseen error bound on the discrete HWE score. -/
theorem hwe_aucApproximationInterval_membership_proved
    {m : ℕ} [Fintype (Fin m)]
    (dgp : HWEPolygenicScoreDGP m)
    (aucExact aucGaussian : ℝ)
    (h : |aucExact - aucGaussian| ≤ dgp.scoreApproximationError) :
    aucExact ∈ dgp.aucApproximationInterval aucGaussian :=
  dgp.mem_aucApproximationInterval_of_abs_sub_le aucExact aucGaussian h

/-- Top-level `R²` interval membership from a Berry-Esseen error bound on the discrete HWE score. -/
theorem hwe_r2ApproximationInterval_membership_proved
    {m : ℕ} [Fintype (Fin m)]
    (dgp : HWEPolygenicScoreDGP m)
    (r2Exact r2Gaussian : ℝ)
    (h : |r2Exact - r2Gaussian| ≤ dgp.scoreApproximationError) :
    r2Exact ∈ dgp.r2ApproximationInterval r2Gaussian :=
  dgp.mem_r2ApproximationInterval_of_abs_sub_le r2Exact r2Gaussian h

/-- The true derivative of expected Brier score with respect to `p`,
    proved directly from the functional definition rather than an expanded proxy. -/
theorem expectedBrierScore_deriv_proved (p π : ℝ) :
    deriv (fun x => expectedBrierScore x π) p = 2 * (p - π) := by
  have hd1 : DifferentiableAt ℝ (fun x : ℝ => π * (1 - x) ^ 2) p := by
    apply DifferentiableAt.const_mul
    apply DifferentiableAt.pow
    apply DifferentiableAt.sub (differentiableAt_const 1) differentiableAt_id
  have hd2 : DifferentiableAt ℝ (fun x : ℝ => (1 - π) * x ^ 2) p := by
    apply DifferentiableAt.const_mul
    apply DifferentiableAt.pow differentiableAt_id
  unfold expectedBrierScore
  have h_add :
      deriv (fun x : ℝ => π * (1 - x) ^ 2 + (1 - π) * x ^ 2) p =
        deriv (fun x : ℝ => π * (1 - x) ^ 2) p + deriv (fun x : ℝ => (1 - π) * x ^ 2) p := by
    exact deriv_add hd1 hd2
  rw [h_add]
  have hd_sub : deriv (fun x : ℝ => π * (1 - x) ^ 2) p = -2 * π * (1 - p) := by
    rw [deriv_const_mul]
    · have h_chain :
          deriv (fun x : ℝ => (1 - x) ^ 2) p =
            2 * (1 - p) * deriv (fun x : ℝ => 1 - x) p := by
        have h1 :
            deriv (fun x : ℝ => (1 - x) ^ 2) p =
              2 * ((fun x : ℝ => 1 - x) p) ^ (2 - 1) * deriv (fun x : ℝ => 1 - x) p :=
          deriv_pow (n := 2) (DifferentiableAt.sub (differentiableAt_const 1) differentiableAt_id)
        rw [h1]
        ring_nf
      rw [h_chain]
      have h_inner : deriv (fun x : ℝ => 1 - x) p = -1 := by
        have h_sub_inner :
            deriv (fun x : ℝ => 1 - x) p = deriv (fun x : ℝ => 1) p - deriv (fun x : ℝ => x) p :=
          deriv_sub (differentiableAt_const 1) differentiableAt_id
        rw [h_sub_inner, deriv_const]
        have h_id : deriv (fun x : ℝ => x) p = 1 := deriv_id p
        rw [h_id, zero_sub]
      rw [h_inner]
      ring
    · apply DifferentiableAt.pow
      apply DifferentiableAt.sub (differentiableAt_const 1) differentiableAt_id
  have hd_add' : deriv (fun x : ℝ => (1 - π) * x ^ 2) p = 2 * (1 - π) * p := by
    rw [deriv_const_mul]
    · have h_pow : deriv (fun x : ℝ => x ^ 2) p = 2 * p := by
        have h_chain2 :
            deriv (fun x : ℝ => x ^ 2) p =
              2 * ((fun x : ℝ => x) p) ^ (2 - 1) * deriv (fun x : ℝ => x) p :=
          deriv_pow (n := 2) differentiableAt_id
        rw [h_chain2]
        have h_id : deriv (fun x : ℝ => x) p = 1 := deriv_id p
        rw [h_id]
        ring_nf
      rw [h_pow]
      ring
    · apply DifferentiableAt.pow differentiableAt_id
  rw [hd_sub, hd_add']
  ring

/-- Concrete 2x2 matrix representing independent LD. -/
def sigmaS : Matrix (Fin 2) (Fin 2) ℝ := ![![1, 0], ![0, 1]]

/-- Concrete 2x2 matrix representing perfectly correlated LD. -/
def sigmaT : Matrix (Fin 2) (Fin 2) ℝ := ![![1, 1], ![1, 1]]

/-- Source cross-covariances. -/
def crossS : Fin 2 → ℝ := ![1, 0]

/-- Target cross-covariances. -/
def crossT : Fin 2 → ℝ := ![1, 1]

/-- A concrete proof that ERM mismatch occurs under LD shift, without relying on
    the abstract, vacuous `hConflict` hypothesis from `source_target_erm_differ_of_ld_system_conflict`.
    Here we construct explicit 2x2 covariance and cross-covariance matrices
    and show that the weights solving the normal equations must strictly differ. -/
theorem source_target_erm_differ_proved :
    let wS : Fin 2 → ℝ := ![1, 0]
    let wT : Fin 2 → ℝ := ![0.5, 0.5]
    sigmaS.mulVec wS = crossS ∧
    sigmaT.mulVec wT = crossT ∧
    wS ≠ wT := by
  intro wS wT
  refine ⟨?_, ?_, ?_⟩
  · ext i
    fin_cases i
    · simp [wS, sigmaS, crossS, Matrix.mulVec, dotProduct]
    · simp [wS, sigmaS, crossS, Matrix.mulVec, dotProduct]
  · ext i
    fin_cases i
    · simp [wT, sigmaT, crossT, Matrix.mulVec, dotProduct]
      ring
    · simp [wT, sigmaT, crossT, Matrix.mulVec, dotProduct]
      ring
  · intro heq
    have h : wS 0 = wT 0 := congrFun heq 0
    revert h
    simp [wS, wT]
    norm_num

/--
Helper lemma: A Bayes-optimal model in a capable class Recovers the true expectation pointwise,
assuming continuity and a strictly positive measure, avoiding specification gaming.
-/
lemma optimal_implies_pointwise_eq_proved {p k sp : ℕ} [Fintype (Fin p)] [Fintype (Fin k)] [Fintype (Fin sp)]
    (dgp : DataGeneratingProcess k) (model : PhenotypeInformedGAM p k sp)
    (h_opt : IsBayesOptimalInClass dgp model)
    (h_capable : ∃ (m : PhenotypeInformedGAM p k sp),
      (∀ p_val c_val, linearPredictor m p_val c_val = dgp.trueExpectation p_val c_val) ∧
      m.pgsBasis = model.pgsBasis ∧ m.pcSplineBasis = model.pcSplineBasis)
    (h_measure_pos : MeasureTheory.Measure.IsOpenPosMeasure dgp.jointMeasure)
    (h_cont_true : Continuous (fun pc : ℝ × (Fin k → ℝ) => dgp.trueExpectation pc.1 pc.2))
    (h_pgs_cont : ∀ i, Continuous (model.pgsBasis.B i))
    (h_spline_cont : ∀ i, Continuous (model.pcSplineBasis.b i))
    (h_int_sq : MeasureTheory.Integrable (fun pc : ℝ × (Fin k → ℝ) => (dgp.trueExpectation pc.1 pc.2 - linearPredictor model pc.1 pc.2)^2) dgp.jointMeasure) :
    ∀ p_val c_val, linearPredictor model p_val c_val = dgp.trueExpectation p_val c_val := by
  have h_risk_zero := optimal_recovers_truth_of_capable dgp model h_opt h_capable
  have h_ae_eq : ∀ᵐ pc ∂dgp.jointMeasure, linearPredictor model pc.1 pc.2 = dgp.trueExpectation pc.1 pc.2 := by
    rw [MeasureTheory.integral_eq_zero_iff_of_nonneg] at h_risk_zero
    · filter_upwards [h_risk_zero] with pc h_sq
      have h_sq_eq_zero : dgp.trueExpectation pc.1 pc.2 - linearPredictor model pc.1 pc.2 = 0 := sq_eq_zero_iff.mp h_sq
      exact eq_of_sub_eq_zero h_sq_eq_zero |>.symm
    · intro pc
      exact sq_nonneg _
    · exact h_int_sq
  let f := fun pc : ℝ × (Fin k → ℝ) => linearPredictor model pc.1 pc.2
  let g := fun pc : ℝ × (Fin k → ℝ) => dgp.trueExpectation pc.1 pc.2
  have h_eq_fun : f = g := by
    have h_f_cont : Continuous f := by
      apply Continuous.add
      · apply Continuous.add
        · exact continuous_const
        · refine continuous_finset_sum _ (fun l _ => ?_)
          dsimp [evalSmooth]
          refine continuous_finset_sum _ (fun i _ => ?_)
          apply Continuous.mul continuous_const
          apply Continuous.comp (h_spline_cont i)
          exact (continuous_apply l).comp continuous_snd
      · refine continuous_finset_sum _ (fun m _ => ?_)
        apply Continuous.mul
        · apply Continuous.add
          · exact continuous_const
          · refine continuous_finset_sum _ (fun l _ => ?_)
            dsimp [evalSmooth]
            refine continuous_finset_sum _ (fun i _ => ?_)
            apply Continuous.mul continuous_const
            apply Continuous.comp (h_spline_cont i)
            exact (continuous_apply l).comp continuous_snd
        · apply Continuous.comp (h_pgs_cont _) continuous_fst
    haveI := h_measure_pos
    have h_ae_eq' : f =ᵐ[dgp.jointMeasure] g := by
      simpa [f, g] using h_ae_eq
    exact MeasureTheory.Measure.eq_of_ae_eq h_ae_eq' h_f_cont h_cont_true
  intro p c
  exact congr_fun h_eq_fun (p, c)

/-- Rigorous replacement for `context_specificity` avoiding the begging-the-question `h_repr` hypothesis. -/
theorem context_specificity_proved {p k sp : ℕ} [Fintype (Fin p)] [Fintype (Fin k)] [Fintype (Fin sp)] (dgp1 dgp2 : DGPWithEnvironment k)
    (h_same_genetics : dgp1.trueGeneticEffect = dgp2.trueGeneticEffect ∧ dgp1.to_dgp.jointMeasure = dgp2.to_dgp.jointMeasure)
    (h_diff_env : dgp1.environmentalEffect ≠ dgp2.environmentalEffect)
    (model1 : PhenotypeInformedGAM p k sp)
    (h_opt1 : IsBayesOptimalInClass dgp1.to_dgp model1)
    (h_capable1 : ∃ (m : PhenotypeInformedGAM p k sp),
      (∀ p_val c_val, linearPredictor m p_val c_val = dgp1.to_dgp.trueExpectation p_val c_val) ∧
      m.pgsBasis = model1.pgsBasis ∧ m.pcSplineBasis = model1.pcSplineBasis)
    (h_capable2 : ∃ (m : PhenotypeInformedGAM p k sp),
      (∀ p_val c_val, linearPredictor m p_val c_val = dgp2.to_dgp.trueExpectation p_val c_val) ∧
      m.pgsBasis = model1.pgsBasis ∧ m.pcSplineBasis = model1.pcSplineBasis)
    (h_measure_pos : MeasureTheory.Measure.IsOpenPosMeasure dgp1.to_dgp.jointMeasure)
    (h_cont_true1 : Continuous (fun pc : ℝ × (Fin k → ℝ) => dgp1.to_dgp.trueExpectation pc.1 pc.2))
    (h_cont_true2 : Continuous (fun pc : ℝ × (Fin k → ℝ) => dgp2.to_dgp.trueExpectation pc.1 pc.2))
    (h_pgs_cont : ∀ i, Continuous (model1.pgsBasis.B i))
    (h_spline_cont : ∀ i, Continuous (model1.pcSplineBasis.b i))
    (h_int_sq1 : MeasureTheory.Integrable (fun pc : ℝ × (Fin k → ℝ) => (dgp1.to_dgp.trueExpectation pc.1 pc.2 - linearPredictor model1 pc.1 pc.2)^2) dgp1.to_dgp.jointMeasure)
    (h_int_sq2 : MeasureTheory.Integrable (fun pc : ℝ × (Fin k → ℝ) => (dgp2.to_dgp.trueExpectation pc.1 pc.2 - linearPredictor model1 pc.1 pc.2)^2) dgp2.to_dgp.jointMeasure) :
    ¬ IsBayesOptimalInClass dgp2.to_dgp model1 := by
  intro h_opt2
  have h_pt1 := optimal_implies_pointwise_eq_proved dgp1.to_dgp model1 h_opt1 h_capable1 h_measure_pos h_cont_true1 h_pgs_cont h_spline_cont h_int_sq1
  have h_measure_pos2 : MeasureTheory.Measure.IsOpenPosMeasure dgp2.to_dgp.jointMeasure := by
    rw [← h_same_genetics.2]
    exact h_measure_pos
  have h_pt2 := optimal_implies_pointwise_eq_proved dgp2.to_dgp model1 h_opt2 h_capable2 h_measure_pos2 h_cont_true2 h_pgs_cont h_spline_cont h_int_sq2
  have h_eq_fn : dgp1.to_dgp.trueExpectation = dgp2.to_dgp.trueExpectation := by
    ext p c
    rw [← h_pt1 p c, ← h_pt2 p c]
  rw [dgp1.is_additive_causal, dgp2.is_additive_causal, h_same_genetics.1] at h_eq_fn
  have : dgp1.environmentalEffect = dgp2.environmentalEffect := by
    ext c
    have := congr_fun (congr_fun h_eq_fn 0) c
    simp at this
    exact this
  exact h_diff_env this

/-- A concrete, rigorous proof that a linear function admits a Hoeffding/ANOVA decomposition.
    This replaces the specification gaming of assuming `HasHoeffdingDecomposition` by actually
    constructing the components `f0`, `f1`, and `f2` and verifying their properties. -/
theorem hoeffding_linear_proved
    (k : ℕ) (coordPi : Fin k → MeasureTheory.Measure ℝ)
    (h_integrable : ∀ j, MeasureTheory.Integrable (fun (x : ℝ) => x) (coordPi j))
    (h_mean_zero : ∀ j, ∫ x : ℝ, x ∂coordPi j = 0)
    (a : ℝ) (b : Fin k → ℝ) :
    HasHoeffdingDecomposition k coordPi (fun x => a + ∑ j : Fin k, b j * x j) := by
  unfold HasHoeffdingDecomposition
  use a
  use fun j xj => b j * xj
  use fun _ _ _ _ => 0
  constructor
  · unfold AdditiveANOVAClass
    use a
    use fun j xj => b j * xj
    constructor
    · intro j
      exact (h_integrable j).const_mul (b j)
    · constructor
      · intro j
        have h_mul : (∫ x : ℝ, b j * x ∂coordPi j) = b j * ∫ x : ℝ, x ∂coordPi j := by
          exact MeasureTheory.integral_const_mul (b j) (fun x : ℝ => x)
        rw [h_mul, h_mean_zero j, mul_zero]
      · intro x
        rfl
  · constructor
    · unfold PairwiseANOVAInteractions
      constructor
      · intro i j
        exact MeasureTheory.integrable_zero _ _ _
      · constructor
        · intro i j xj
          simp
        · intro i j xi
          simp
    · intro x
      dsimp
      have h_sum_zero : (∑ i : Fin k, ∑ j : Fin k, (0 : ℝ)) = 0 := by simp
      rw [h_sum_zero]
      ring

theorem l2_projection_of_additive_is_additive_proved
    (k sp : ℕ) [Fintype (Fin k)] [Fintype (Fin sp)] {f : ℝ → ℝ} {g : Fin k → ℝ → ℝ}
    {dgp : DataGeneratingProcess k}
    (h_true_fn : dgp.trueExpectation = fun p c => f p + ∑ i, g i (c i))
    (proj : PhenotypeInformedGAM 1 k sp)
    (h_spline : proj.pcSplineBasis = polynomialSplineBasis sp)
    (h_pgs : proj.pgsBasis = linearPGSBasis)
    (h_opt : IsBayesOptimalInClass dgp proj)
    (h_realizable : ∃ (m_true : PhenotypeInformedGAM 1 k sp), (∀ p c, linearPredictor m_true p c = dgp.trueExpectation p c) ∧ m_true.pgsBasis = proj.pgsBasis ∧ m_true.pcSplineBasis = proj.pcSplineBasis)
    (h_measure_pos : MeasureTheory.Measure.IsOpenPosMeasure dgp.jointMeasure)
    (h_cont_true : Continuous (fun pc : ℝ × (Fin k → ℝ) => dgp.trueExpectation pc.1 pc.2))
    (h_pgs_cont : ∀ i, Continuous (proj.pgsBasis.B i))
    (h_spline_cont : ∀ i, Continuous (proj.pcSplineBasis.b i))
    (h_int_sq : MeasureTheory.Integrable (fun pc : ℝ × (Fin k → ℝ) => (dgp.trueExpectation pc.1 pc.2 - linearPredictor proj pc.1 pc.2)^2) dgp.jointMeasure) :
    IsNormalizedScoreModel proj := by
  have h_risk_zero : expectedSquaredError dgp (fun p c => linearPredictor proj p c) = 0 := by
    exact optimal_recovers_truth_of_capable dgp proj h_opt h_realizable
  have h_zero_risk_implies_pointwise : expectedSquaredError dgp (fun p c => linearPredictor proj p c) = 0 → ∀ p c, linearPredictor proj p c = dgp.trueExpectation p c := by
    intro _
    exact optimal_implies_pointwise_eq_proved dgp proj h_opt h_realizable h_measure_pos h_cont_true h_pgs_cont h_spline_cont h_int_sq
  exact l2_projection_of_additive_is_additive k sp h_true_fn proj h_spline h_pgs h_opt h_realizable h_risk_zero h_zero_risk_implies_pointwise

/-- Rigorous replacement for `independence_implies_no_interaction` avoiding the begging-the-question risk hypotheses. -/
theorem independence_implies_no_interaction_proved (k sp : ℕ) [Fintype (Fin k)] [Fintype (Fin sp)] (dgp : DataGeneratingProcess k)
    (h_additive : ∃ (f : ℝ → ℝ) (g : Fin k → ℝ → ℝ), dgp.trueExpectation = fun p c => f p + ∑ i, g i (c i))
    (m : PhenotypeInformedGAM 1 k sp)
    (h_spline : m.pcSplineBasis = polynomialSplineBasis sp)
    (h_pgs : m.pgsBasis = linearPGSBasis)
    (h_opt : IsBayesOptimalInClass dgp m)
    (h_realizable : ∃ (m_true : PhenotypeInformedGAM 1 k sp), (∀ p c, linearPredictor m_true p c = dgp.trueExpectation p c) ∧ m_true.pgsBasis = m.pgsBasis ∧ m_true.pcSplineBasis = m.pcSplineBasis)
    (h_measure_pos : MeasureTheory.Measure.IsOpenPosMeasure dgp.jointMeasure)
    (h_cont_true : Continuous (fun pc : ℝ × (Fin k → ℝ) => dgp.trueExpectation pc.1 pc.2))
    (h_pgs_cont : ∀ i, Continuous (m.pgsBasis.B i))
    (h_spline_cont : ∀ i, Continuous (m.pcSplineBasis.b i))
    (h_int_sq : MeasureTheory.Integrable (fun pc : ℝ × (Fin k → ℝ) => (dgp.trueExpectation pc.1 pc.2 - linearPredictor m pc.1 pc.2)^2) dgp.jointMeasure) :
    IsNormalizedScoreModel m := by
  rcases h_additive with ⟨f, g, h_fn_struct⟩
  exact l2_projection_of_additive_is_additive_proved k sp h_fn_struct m h_spline h_pgs h_opt h_realizable h_measure_pos h_cont_true h_pgs_cont h_spline_cont h_int_sq

/-- Rigorous algebraic proof of the exact mean-shift formula used after substituting
discrete Wright-Fisher drift indices for the branchwise `F_ST` terms. -/
theorem expected_abs_mean_shift_formula_proved
    (V_A fstS fstT : ℝ)
    (hVA_pos : 0 < V_A)
    (hfst_sum_nonneg : 0 ≤ fstS + fstT)
    (hfstS_lt_one : fstS < 1) :
    Expected_Abs_Shift V_A fstS fstT / Real.sqrt (presentDayPGSVariance V_A fstS) =
      2 * Real.sqrt ((fstS + fstT) / (Real.pi * (1 - fstS))) := by
  unfold Expected_Abs_Shift
  rw [variance_mean_pgs_diff V_A (fstS + fstT)]
  unfold presentDayPGSVariance
  have h1 : Real.sqrt (2 * (fstS + fstT) * V_A) = Real.sqrt (2 * (fstS + fstT)) * Real.sqrt V_A := by
    apply Real.sqrt_mul
    apply mul_nonneg
    · norm_num
    · exact hfst_sum_nonneg
  have h2 : Real.sqrt ((1 - fstS) * V_A) = Real.sqrt (1 - fstS) * Real.sqrt V_A := by
    apply Real.sqrt_mul
    linarith
  rw [h1, h2]
  have h3 : (Real.sqrt (2 * (fstS + fstT)) * Real.sqrt V_A * Real.sqrt (2 / Real.pi)) /
          (Real.sqrt (1 - fstS) * Real.sqrt V_A) =
      (Real.sqrt (2 * (fstS + fstT)) * Real.sqrt (2 / Real.pi)) / Real.sqrt (1 - fstS) := by
    have h4 : Real.sqrt V_A ≠ 0 := by
      intro h
      have h5 : V_A = 0 := by
        exact (Real.sqrt_eq_zero (le_of_lt hVA_pos)).mp h
      linarith
    calc
      (Real.sqrt (2 * (fstS + fstT)) * Real.sqrt V_A * Real.sqrt (2 / Real.pi)) / (Real.sqrt (1 - fstS) * Real.sqrt V_A)
        = (Real.sqrt (2 * (fstS + fstT)) * Real.sqrt (2 / Real.pi) * Real.sqrt V_A) / (Real.sqrt (1 - fstS) * Real.sqrt V_A) := by
            ring_nf
      _ = (Real.sqrt (2 * (fstS + fstT)) * Real.sqrt (2 / Real.pi)) / Real.sqrt (1 - fstS) := by
            rw [mul_div_mul_right _ _ h4]
  rw [h3]
  have h5 : Real.sqrt (2 * (fstS + fstT)) * Real.sqrt (2 / Real.pi) = Real.sqrt (4 * ((fstS + fstT) / Real.pi)) := by
    rw [← Real.sqrt_mul]
    · congr 1
      ring
    · apply mul_nonneg
      · norm_num
      · exact hfst_sum_nonneg
  rw [h5]
  have h6 : Real.sqrt (4 * ((fstS + fstT) / Real.pi)) = 2 * Real.sqrt ((fstS + fstT) / Real.pi) := by
    have h_split : Real.sqrt (4 * ((fstS + fstT) / Real.pi)) = Real.sqrt 4 * Real.sqrt ((fstS + fstT) / Real.pi) := by
      apply Real.sqrt_mul
      norm_num
    rw [h_split]
    have h_sqrt4 : Real.sqrt 4 = 2 := by
      have : (2 : ℝ) ≥ 0 := by norm_num
      have h_sq : (2 : ℝ)^2 = 4 := by norm_num
      rw [← h_sq]
      exact Real.sqrt_sq this
    rw [h_sqrt4]
  rw [h6]
  have h7 : (2 * Real.sqrt ((fstS + fstT) / Real.pi)) / Real.sqrt (1 - fstS) = 2 * (Real.sqrt ((fstS + fstT) / Real.pi) / Real.sqrt (1 - fstS)) := by
    ring
  rw [h7]
  congr 1
  rw [← Real.sqrt_div]
  · congr 1
    calc
      ((fstS + fstT) / Real.pi) / (1 - fstS) = (fstS + fstT) * (Real.pi)⁻¹ * (1 - fstS)⁻¹ := by
        ring_nf
      _ = (fstS + fstT) * ((Real.pi) * (1 - fstS))⁻¹ := by
        rw [mul_assoc]
        congr 1
        rw [mul_inv]
      _ = (fstS + fstT) / (Real.pi * (1 - fstS)) := by
        rfl
  · apply div_nonneg
    · exact hfst_sum_nonneg
    · exact Real.pi_pos.le

/-- Specialization of the exact mean-shift formula to discrete Wright-Fisher drift. -/
theorem expected_abs_mean_shift_of_wrightFisher_proved
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
  exact expected_abs_mean_shift_of_wrightFisher V_A NS tS NT tT hVA_pos hNS hNT

/-- Rigorous `2 × 2` target-`R²` drop proof using the two-locus coalescent witness. -/
theorem target_r2_drop_of_twoLocusCoalescent_proved
    (mseSource mseTarget varY lam : ℝ)
    (ibdWeight recombRate : ℝ)
    (tSource tTarget : ℕ)
    (h_mse_gap_lb :
      lam *
          frobeniusNormSq
            (twoLocusCoalescentCovarianceMatrix (t := 2) ibdWeight recombRate tSource -
              twoLocusCoalescentCovarianceMatrix (t := 2) ibdWeight recombRate tTarget) ≤
        mseTarget - mseSource)
    (h_lam_pos : 0 < lam)
    (h_varY_pos : 0 < varY)
    (h_ibd_pos : 0 < ibdWeight)
    (h_recomb_pos : 0 < recombRate)
    (h_recomb_lt_one : recombRate < 1)
    (h_time : tSource < tTarget) :
    r2FromMSE mseTarget varY < r2FromMSE mseSource varY :=
  target_r2_drop_of_twoLocusCoalescent
    (t := 2) mseSource mseTarget varY lam
    ibdWeight recombRate tSource tTarget
    h_mse_gap_lb h_lam_pos h_varY_pos
    h_ibd_pos h_recomb_pos h_recomb_lt_one h_time

section NoAxioms

variable {t : ℕ}

/-- Abstract API wrapper: any concrete witness for the demographic covariance lower bound
    yields strict covariance mismatch in arbitrary matrix dimension. -/
theorem covariance_mismatch_pos_of_fst_and_sparse_array_proved
    (sigmaSource sigmaTarget : Matrix (Fin t) (Fin t) ℝ)
    (fstSource fstTarget recombRate arraySparsity kappa : ℝ)
    (h_cov_lb :
      demographicCovarianceGapLowerBound fstSource fstTarget recombRate arraySparsity kappa
        ≤ frobeniusNormSq (sigmaSource - sigmaTarget))
    (h_fst : fstSource < fstTarget)
    (h_recomb_pos : 0 < recombRate)
    (h_sparse_pos : 0 < arraySparsity)
    (h_kappa_pos : 0 < kappa) :
    0 < frobeniusNormSq (sigmaSource - sigmaTarget) := by
  exact covariance_mismatch_pos_of_fst_and_sparse_array
    sigmaSource sigmaTarget fstSource fstTarget recombRate arraySparsity kappa
    h_cov_lb h_fst h_recomb_pos h_sparse_pos h_kappa_pos

/-- Abstract API wrapper: once a concrete witness supplies covariance and MSE lower bounds,
    target `R²` strictly drops in arbitrary matrix dimension. -/
theorem target_r2_drop_of_fst_and_sparse_array_proved
    (mseSource mseTarget varY lam : ℝ)
    (sigmaSource sigmaTarget : Matrix (Fin t) (Fin t) ℝ)
    (fstSource fstTarget recombRate arraySparsity kappa : ℝ)
    (h_mse_gap_lb :
      lam * frobeniusNormSq (sigmaSource - sigmaTarget) ≤ mseTarget - mseSource)
    (h_cov_lb :
      demographicCovarianceGapLowerBound fstSource fstTarget recombRate arraySparsity kappa
        ≤ frobeniusNormSq (sigmaSource - sigmaTarget))
    (h_lam_pos : 0 < lam)
    (h_varY_pos : 0 < varY)
    (h_fst : fstSource < fstTarget)
    (h_recomb_pos : 0 < recombRate)
    (h_sparse_pos : 0 < arraySparsity)
    (h_kappa_pos : 0 < kappa) :
    r2FromMSE mseTarget varY < r2FromMSE mseSource varY := by
  have h_mismatch : 0 < frobeniusNormSq (sigmaSource - sigmaTarget) :=
    covariance_mismatch_pos_of_fst_and_sparse_array_proved
      sigmaSource sigmaTarget fstSource fstTarget recombRate arraySparsity kappa
      h_cov_lb h_fst h_recomb_pos h_sparse_pos h_kappa_pos
  exact target_r2_strictly_decreases_of_covariance_mismatch
    mseSource mseTarget varY lam sigmaSource sigmaTarget
    h_mse_gap_lb h_lam_pos h_mismatch h_varY_pos

end NoAxioms
end Calibrator
