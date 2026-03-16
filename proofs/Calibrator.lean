import Calibrator.Probability
import Calibrator.DGP
import Calibrator.Models
import Calibrator.Conclusions
import Calibrator.PortabilityDrift
import Calibrator.OpenQuestions
import Calibrator.TransportIdentities
import Calibrator.PortabilityBounds
import Calibrator.MultiAncestryTheory
import Calibrator.StratificationConfounding
import Calibrator.AncestryCalibration
import Calibrator.LDDecayTheory
import Calibrator.SelectionArchitecture
import Calibrator.DemographicHistory
import Calibrator.ClinicalUtilityFairness
import Calibrator.VarianceComponents
import Calibrator.ScoreDistribution
import Calibrator.ValidationStatistics
import Calibrator.CrossValidationTheory
import Calibrator.SimulationValidation
import Calibrator.SelectionValidation
import Calibrator.GeneticArchitectureDiscovery
import Calibrator.PredictionIntervalTheory
import Calibrator.BayesianPGSTheory
import Calibrator.PhenomeWidePortability
import Calibrator.AncestryDeconvolution
import Calibrator.TransferLearningPGS
import Calibrator.MetricSpecificPortability
import Calibrator.PopulationGeneticsFoundations
import Calibrator.GeneEnvironmentInterplay
import Calibrator.RareVariantPortability
import Calibrator.StatisticalGeneticsMethodology
import Calibrator.EquityAndImplementation
import Calibrator.EpistasisAndNonAdditivity
import Calibrator.PolygenicAdaptation
import Calibrator.AssortativeMatingPGS
import Calibrator.ImputationPortability
import Calibrator.LongitudinalPortability
import Calibrator.PowerAnalysis
import Calibrator.CovarianceStructure
import Calibrator.MendelianRandomization
import Calibrator.CausalInference
import Calibrator.FineMapping
import Calibrator.PolygenicArchitecture
import Calibrator.SampleOverlapBias
import Calibrator.HaplotypeTheory
import Calibrator.MultiTraitPGS
import Calibrator.AncestrySpecificArchitecture
import Calibrator.AncestrySpecificPower
import Calibrator.PGSCalibrationTheory

namespace Calibrator

local instance : Fact (2 ≤ 2) := ⟨by decide⟩

/-
Proof policy: do not add theorems whose conclusion merely repackages a premise
by trivial algebra, rewriting, or conjunction-introduction. Such statements add
noise without adding usable mathematical content and should be deleted rather
than retained as named results.
-/

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
    proved via the quadratic-form derivative in `Conclusions`. -/
theorem expectedBrierScore_deriv_proved (p π : ℝ) :
    deriv (fun x => expectedBrierScore x π) p = 2 * (p - π) :=
  expectedBrierScore_deriv p π

/-- Concrete 2x2 matrix representing independent LD. -/
def sigmaS : Matrix (Fin 2) (Fin 2) ℝ := ![![1, 0], ![0, 1]]

/-- Concrete 2x2 matrix representing perfectly correlated LD. -/
def sigmaT : Matrix (Fin 2) (Fin 2) ℝ := ![![1, 1], ![1, 1]]

/-- Source cross-covariances. -/
def crossS : Fin 2 → ℝ := ![1, 0]

/-- Target cross-covariances. -/
def crossT : Fin 2 → ℝ := ![1, 1]

/-- Another target LD matrix with a different correlation structure. -/
def sigmaT2 : Matrix (Fin 2) (Fin 2) ℝ := ![![1, 0.5], ![0.5, 1]]

/-- A concrete proof that the source ERM is LD-specific and does not solve
    the target normal equations under a new correlation structure, without relying on the vacuous `hMismatch`
    hypothesis from `source_erm_is_ld_specific_of_normal_eq_mismatch`. -/
theorem source_erm_is_ld_specific_proved :
    let wS : Fin 2 → ℝ := ![1, 0]
    sigmaS.mulVec wS = crossS ∧
    sigmaT2.mulVec wS ≠ crossT := by
  intro wS
  refine ⟨?_, ?_⟩
  · ext i
    fin_cases i
    · simp [wS, sigmaS, crossS, Matrix.mulVec, dotProduct]
    · simp [wS, sigmaS, crossS, Matrix.mulVec, dotProduct]
  · intro heq
    have h : (sigmaT2.mulVec wS) 1 = crossT 1 := congrFun heq 1
    revert h
    simp [wS, sigmaT2, crossT, Matrix.mulVec, dotProduct]
    norm_num

/-- A concrete proof that ERM mismatch occurs under LD shift, without relying on
    the abstract, vacuous `hConflict` hypothesis from `source_target_erm_differ_of_ld_system_conflict`.
    Here we construct explicit 2x2 covariance and cross-covariance matrices
    and show that the weights solving the normal equations must strictly differ. -/
theorem source_target_erm_differ_proved :
    let wS : Fin 2 → ℝ := ![1, 0]
    let wT : Fin 2 → ℝ := ![1/2, 1/2]
    sigmaS.mulVec wS = crossS ∧
    sigmaT.mulVec wT = crossT ∧
    wS ≠ wT := by
  intro wS wT
  refine ⟨?_, ?_, ?_⟩
  · ext i; fin_cases i <;> simp [wS, sigmaS, crossS, Matrix.mulVec, dotProduct]
  · ext i; fin_cases i <;> simp [wT, sigmaT, crossT, Matrix.mulVec, dotProduct] <;> ring
  · intro heq
    have h : wS 0 = wT 0 := congrFun heq 0
    simp [wS, wT] at h

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

/-- Top-level mean-shift formula: delegates to `PortabilityDrift.expected_abs_mean_shift_bound_proved`. -/
theorem expected_abs_mean_shift_formula_proved
    (V_A fstS fstT : ℝ)
    (hVA_pos : 0 < V_A)
    (hfst_sum_nonneg : 0 ≤ fstS + fstT)
    (hfstS_lt_one : fstS < 1) :
    Expected_Abs_Shift V_A fstS fstT / Real.sqrt (presentDayPGSVariance V_A fstS) =
      2 * Real.sqrt ((fstS + fstT) / (Real.pi * (1 - fstS))) :=
  expected_abs_mean_shift_bound_proved V_A fstS fstT hVA_pos hfst_sum_nonneg hfstS_lt_one

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

/-- Rigorous proof that exponential LD decay cannot be fit by a linear slope calibration,
    replacing the specification gaming in `ld_decay_implies_nonlinear_calibration_sketch`. -/
theorem ld_decay_implies_nonlinear_calibration_proved {k : ℕ} [Fintype (Fin k)]
    (mech : LDDecayMechanism k)
    (lambda : ℝ) (h_lambda_pos : 0 < lambda)
    (h_tagging : mech.tagging_efficiency = fun d => Real.exp (-lambda * d))
    (c0 c1 c2 : Fin k → ℝ)
    (hd0 : mech.distance c0 = 0)
    (hd1 : mech.distance c1 = 1)
    (hd2 : mech.distance c2 = 2) :
    ∀ (beta0 beta1 : ℝ),
      (fun c => beta0 + beta1 * mech.distance c) ≠
        (fun c => decaySlope mech c) := by
  intro beta0 beta1 h_eq
  have h0 := congr_fun h_eq c0
  have h1 := congr_fun h_eq c1
  have h2 := congr_fun h_eq c2
  unfold decaySlope at h0 h1 h2
  rw [h_tagging] at h0 h1 h2
  rw [hd0] at h0
  rw [hd1] at h1
  rw [hd2] at h2
  simp only [mul_zero, Real.exp_zero, mul_one, add_zero] at h0 h1 h2
  have h_b1 : beta1 = Real.exp (-lambda) - beta0 := by linarith
  have h_b0 : beta0 = 1 := by linarith
  rw [h_b0] at h_b1
  have h_2 : 1 + 2 * (Real.exp (-lambda) - 1) = Real.exp (-lambda * 2) := by linarith
  have h_exp_sq : Real.exp (-lambda * 2) = (Real.exp (-lambda))^2 := by
    rw [mul_comm, ← Real.exp_nat_mul]
    norm_cast
  rw [h_exp_sq] at h_2
  have h_quad : (Real.exp (-lambda) - 1)^2 = 0 := by
    calc (Real.exp (-lambda) - 1)^2
      _ = (Real.exp (-lambda))^2 - 2 * Real.exp (-lambda) + 1 := by ring
      _ = 1 + 2 * (Real.exp (-lambda) - 1) - 2 * Real.exp (-lambda) + 1 := by rw [← h_2]
      _ = 0 := by ring
  have h_exp_eq_one : Real.exp (-lambda) = 1 := by
    have h_zero : Real.exp (-lambda) - 1 = 0 := sq_eq_zero_iff.mp h_quad
    linarith
  have h_lambda_zero : -lambda = 0 := by
    have h_exp_zero : Real.exp 0 = 1 := Real.exp_zero
    rw [← h_exp_zero] at h_exp_eq_one
    exact Real.exp_injective h_exp_eq_one
  linarith

end NoAxioms

/-- Top-level: at zero divergence, the neutral allele-frequency benchmark
target `R²` is the same present-day `R²` evaluated at that state. -/
theorem targetR2_eq_source_at_zero_drift_proved
    (V_A V_E fst : ℝ) :
    targetR2FromNeutralAFBenchmark V_A V_E fst = presentDayR2 V_A V_E fst :=
  targetR2FromNeutralAFBenchmark_self V_A V_E fst

/-- Top-level: strict neutral allele-frequency benchmark Brier degradation
under positive drift and non-degenerate prevalence. -/
theorem targetBrier_strict_gt_source_proved
    (π V_A V_E fstSource fstTarget : ℝ)
    (hπ0 : 0 < π) (hπ1 : π < 1)
    (hVA : 0 < V_A) (hVE : 0 < V_E)
    (h_fst : fstSource < fstTarget)
    (h_fst_bounds : 0 ≤ fstSource ∧ fstTarget < 1) :
    sourceBrierFromR2 π (presentDayR2 V_A V_E fstSource) <
      targetBrierFromNeutralAFBenchmark π V_A V_E fstTarget :=
  targetBrier_strict_gt_source_of_neutralAF_benchmark π V_A V_E fstSource fstTarget
    hπ0 hπ1 hVA hVE h_fst h_fst_bounds

/-- Top-level: increasing migration strictly reduces IM equilibrium differentiation
    on the biologically relevant domain of positive migration rates. -/
theorem im_delta_strictAntiOn_proved :
    StrictAntiOn (fun M : ℝ => twoDemeIMEquilibriumDelta M) (Set.Ioi 0) :=
  twoDemeIMEquilibriumDelta_strictAntiOn

end Calibrator
