import Calibrator.Probability
import Calibrator.DGP
import Calibrator.Conclusions
import Calibrator.PortabilityDrift
import Calibrator.HumanDemography
import Calibrator.AdditiveInvariance
import Calibrator.Identification
import Calibrator.ImitationRigidity
import Calibrator.Conventions
import Calibrator.DemographicCapacity
import Calibrator.DriftRegime
import Calibrator.BlindnessRegistry
import Calibrator.OpenQuestions
import Calibrator.TransportIdentities
import Calibrator.SecondMomentShift
import Calibrator.QuadraticShift
import Calibrator.ProjectionShiftBounds
import Calibrator.WhiteningEquivalence
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
import Calibrator.SimulationValidation
import Calibrator.SelectionValidation
import Calibrator.GeneticArchitectureDiscovery
import Calibrator.BayesianPGSTheory
import Calibrator.PhenomeWidePortability
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
import Calibrator.CausalInference
import Calibrator.PolygenicArchitecture
import Calibrator.SampleOverlapBias
import Calibrator.HaplotypeTheory
import Calibrator.AncestrySpecificArchitecture
import Calibrator.AncestrySpecificPower
import Calibrator.PGSCalibrationTheory
import Calibrator.ObservationalCeiling
import Calibrator.Condensation
import Calibrator.CumulantBlindness
import Calibrator.JetBarrier
import Calibrator.LocalToGlobalCoherence
import Calibrator.HiddenConeAmbiguity
import Calibrator.LatentMechanismCollapse
import Calibrator.PolygenicSpectroscopy
import Calibrator.EpistaticChaos
import Calibrator.CondensationUnification
import Calibrator.CramerStratum
import Calibrator.FoldedSpectrum
import Calibrator.SpectralDegradation

namespace Calibrator

local instance : Fact (2 ≤ 2) := ⟨by decide⟩

/-
Proof policy: do not add theorems whose conclusion merely repackages a premise
by trivial algebra, rewriting, or conjunction-introduction. Such statements add
noise without adding usable mathematical content and should be deleted rather
than retained as named results.
-/


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

/-! Target cross-covariances were restated here as `crossT`. The same witness
vector `![1, 1]` is `DGP.ldWitnessTargetCross`, and the restatement has been
deleted so that the two `2 × 2` witnesses in this development are one witness. -/

/-- Another target LD matrix with a different correlation structure. -/
def sigmaT2 : Matrix (Fin 2) (Fin 2) ℝ := ![![1, 0.5], ![0.5, 1]]

/-- A concrete proof that the source ERM is LD-specific and does not solve
    the target normal equations under a new correlation structure. The mismatch is
    exhibited by explicit `2 × 2` witnesses rather than assumed as a hypothesis. -/
theorem source_erm_is_ld_specific_proved :
    let wS : Fin 2 → ℝ := ![1, 0]
    sigmaS.mulVec wS = crossS ∧
    sigmaT2.mulVec wS ≠ ldWitnessTargetCross := by
  intro wS
  refine ⟨?_, ?_⟩
  · ext i
    fin_cases i
    · simp [wS, sigmaS, crossS, Matrix.mulVec, dotProduct]
    · simp [wS, sigmaS, crossS, Matrix.mulVec, dotProduct]
  · intro heq
    have h : (sigmaT2.mulVec wS) 1 = ldWitnessTargetCross 1 := congrFun heq 1
    revert h
    simp [wS, sigmaT2, ldWitnessTargetCross, Matrix.mulVec, dotProduct]
    norm_num

/-- A concrete proof that ERM mismatch occurs under LD shift, without assuming an
    abstract system-conflict hypothesis.
    Here we construct explicit 2x2 covariance and cross-covariance matrices
    and show that the weights solving the normal equations must strictly differ. -/
theorem source_target_erm_differ_proved :
    let wS : Fin 2 → ℝ := ![1, 0]
    let wT : Fin 2 → ℝ := ![1/2, 1/2]
    sigmaS.mulVec wS = crossS ∧
    sigmaT.mulVec wT = ldWitnessTargetCross ∧
    wS ≠ wT := by
  intro wS wT
  refine ⟨?_, ?_, ?_⟩
  · ext i; fin_cases i <;> simp [wS, sigmaS, crossS, Matrix.mulVec, dotProduct]
  · ext i; fin_cases i <;> simp [wT, sigmaT, ldWitnessTargetCross, Matrix.mulVec, dotProduct] <;> ring
  · intro heq
    have h : wS 0 = wT 0 := congrFun heq 0
    simp [wS, wT] at h


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

/-- Rigorous proof that exponential LD decay cannot be fit by a linear slope calibration.
    Non-affineness is derived from three explicit distances rather than assumed. -/
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

section Condensation

/-!
### Concrete specializations of the condensation results

Same policy as the rest of this file: only specializations that instantiate a general
theorem at genuine numbers, not restatements.
-/

/-- A genome-scale **additive** score at a balanced locus is strictly subcritical:
`1 < log (10 ^ 6) / c(1/2)`. The Gaussian score apparatus of
`Calibrator.ScoreDistribution` applies with enormous margin, and this is the concrete
witness that the condensation theory does not disturb it. -/
theorem additive_score_subcritical_at_balanced_locus_proved :
    1 < maxSafeEpistaticOrder 1000000 (1 / 2) := by
  have hc : 0 < hweMellinDrift (1 / 2) := by
    rw [hweMellinDrift_half]
    exact Real.log_pos (by norm_num)
  refine additive_score_is_subcritical hc ?_
  rw [hweMellinDrift_half]
  exact Real.log_lt_log (by norm_num) (by norm_num)

/-- Pairwise epistasis at a sufficiently rare variant is supercritical for a
million-term aggregate: the Gaussian surrogate converges to a different limit. -/
theorem pairwise_epistasis_supercritical_proved :
    ∃ q : ℝ, 0 < q ∧ q ≤ 1 / 8 ∧
      Real.log 1000000 < 2 * hweMellinDrift q :=
  exists_maf_supercritical (by norm_num) (by norm_num)

/-- The hard-call lattice point produces a strictly inflated exceedance intensity, so
hard calls and dosage surrogates are not exchangeable at high epistatic order. -/
theorem hardCall_lattice_inflation_proved :
    1 < latticeInflation hardCallLatticeSpan :=
  hardCall_intensity_inflated

/-- The expander frustration floor is a genuine constant above `0.127`, so the
non-bipartite twin sits a constant total-variation distance from every globally
realizable system. -/
theorem frustration_floor_proved : (0.127 : ℝ) < expanderAgreementFloor :=
  expanderAgreementFloor_gt

end Condensation

end Calibrator
