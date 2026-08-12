/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.EndToEndScoreLaw
import Descent.Portability.PopulationAUC
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.SpecialFunctions.Sigmoid
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Topology.MetricSpace.Bounded

assert_below Descent.Decision Descent.Program

namespace Descent.Portability

open MeasureTheory

/-!
# Discrimination laws: realized cohorts, population charts, and censored survival

The exact binary evaluator operates on realized outcomes and predicted risks and recomputes
pooled metrics on concatenated individuals.  A separate Gaussian population chart consumes
per-deme score moments; its pooled law keeps case and control mixture weights distinct, so
off-diagonal terms are genuine cross-deme comparisons rather than averages of within-deme
AUCs.
-/

/-! ## E1--E2. Within-deme and pooled Gaussian population charts -/

/-- Mean of the raw deployed score among cases in a deme.  The liability moments are for a
standardised score, hence the explicit rescaling by the marginal score standard deviation. -/
noncomputable def DemeScoreLaw.caseScoreMean (law : DemeScoreLaw) : ℝ :=
  law.scoreMean + Real.sqrt law.moments.scoreVariance * law.pearson *
    liabilityCaseMean law.prevalence

/-- Mean of the raw deployed score among controls in a deme. -/
noncomputable def DemeScoreLaw.controlScoreMean (law : DemeScoreLaw) : ℝ :=
  law.scoreMean + Real.sqrt law.moments.scoreVariance * law.pearson *
    liabilityControlMean law.prevalence

/-- Conditional raw-score variance among cases. -/
noncomputable def DemeScoreLaw.caseScoreVariance (law : DemeScoreLaw) : ℝ :=
  law.moments.scoreVariance * liabilityCaseVariance law.r2True law.prevalence

/-- Conditional raw-score variance among controls. -/
noncomputable def DemeScoreLaw.controlScoreVariance (law : DemeScoreLaw) : ℝ :=
  law.moments.scoreVariance * liabilityControlVariance law.r2True law.prevalence

/-- Signed within-deme Gaussian AUC.  Unlike an `R²`-only chart, this expression retains a
possible target-deme sign reversal through `law.pearson`. -/
noncomputable def DemeScoreLaw.liabilityWithinAUC (law : DemeScoreLaw) : ℝ :=
  Foundations.Phi
    ((law.caseScoreMean - law.controlScoreMean) /
      Real.sqrt (law.caseScoreVariance + law.controlScoreVariance))

/-- Domain on which both conditional Gaussian score laws have positive variance. -/
structure LiabilityDiscriminationDomain (law : DemeScoreLaw) : Prop where
  caseVariance_pos : 0 < liabilityCaseVariance law.r2True law.prevalence
  controlVariance_pos : 0 < liabilityControlVariance law.r2True law.prevalence

/-- E1 on its typed domain. -/
noncomputable def DemeScoreLaw.withinAUC
    (law : DemeScoreLaw) (_ : LiabilityDiscriminationDomain law) : ℝ :=
  law.liabilityWithinAUC

/-- Off-diagonal Gaussian exceedance term: a case drawn from deme `caseDeme` outranks a
control drawn from deme `controlDeme`.  It includes differences in score location, scale,
explained variance, and liability threshold. -/
noncomputable def crossDemeCaseControlAUC
    (caseDeme controlDeme : DemeScoreLaw) : ℝ :=
  Foundations.Phi
    ((caseDeme.caseScoreMean - controlDeme.controlScoreMean) /
      Real.sqrt (caseDeme.caseScoreVariance + controlDeme.controlScoreVariance))

/-- Off-diagonal comparison on its typed conditional-variance domain. -/
noncomputable def crossDemeCaseControlAUCOn
    (caseDeme controlDeme : DemeScoreLaw)
    (_ : LiabilityDiscriminationDomain caseDeme)
    (_ : LiabilityDiscriminationDomain controlDeme) : ℝ :=
  crossDemeCaseControlAUC caseDeme controlDeme

/-- The off-diagonal formula reduces definitionally to the same signed within-deme chart. -/
theorem crossDemeCaseControlAUC_diagonal (law : DemeScoreLaw)
    (domain : LiabilityDiscriminationDomain law) :
    crossDemeCaseControlAUCOn law law domain domain = law.withinAUC domain := by
  rfl

/-- A finite population mixture.  `populationWeight` is the unconditional deme mass; its
normalisation is carried by the type so a pooled AUC cannot silently use cell counts. -/
structure DemeMixture (D : ℕ) where
  law : Fin D → DemeScoreLaw
  discriminationDomain : ∀ d, LiabilityDiscriminationDomain (law d)
  populationWeight : Fin D → ℝ
  weight_nonneg : ∀ d, 0 ≤ populationWeight d
  weight_sum_one : ∑ d, populationWeight d = 1
  caseMass_pos : 0 < ∑ d, populationWeight d * (law d).prevalence
  controlMass_pos : 0 < ∑ d, populationWeight d * (1 - (law d).prevalence)

/-- Total case mass before conditioning on case status. -/
noncomputable def DemeMixture.caseMass {D : ℕ} (mix : DemeMixture D) : ℝ :=
  ∑ d, mix.populationWeight d * (mix.law d).prevalence

/-- Total control mass before conditioning on control status. -/
noncomputable def DemeMixture.controlMass {D : ℕ} (mix : DemeMixture D) : ℝ :=
  ∑ d, mix.populationWeight d * (1 - (mix.law d).prevalence)

/-- Deme weight conditional on drawing a case. -/
noncomputable def DemeMixture.caseWeight {D : ℕ} (mix : DemeMixture D) (d : Fin D) : ℝ :=
  mix.populationWeight d * (mix.law d).prevalence / mix.caseMass

/-- Deme weight conditional on drawing a control. -/
noncomputable def DemeMixture.controlWeight {D : ℕ} (mix : DemeMixture D) (d : Fin D) : ℝ :=
  mix.populationWeight d * (1 - (mix.law d).prevalence) / mix.controlMass

/-- Conditional case weights normalize exactly. -/
theorem DemeMixture.caseWeight_sum_one {D : ℕ} (mix : DemeMixture D) :
    ∑ d, mix.caseWeight d = 1 := by
  unfold DemeMixture.caseWeight DemeMixture.caseMass
  rw [← Finset.sum_div]
  exact div_self (ne_of_gt mix.caseMass_pos)

/-- Conditional control weights normalize exactly. -/
theorem DemeMixture.controlWeight_sum_one {D : ℕ} (mix : DemeMixture D) :
    ∑ d, mix.controlWeight d = 1 := by
  unfold DemeMixture.controlWeight DemeMixture.controlMass
  rw [← Finset.sum_div]
  exact div_self (ne_of_gt mix.controlMass_pos)

/-- E2: pooled population AUC.  Diagonal summands are E1; every off-diagonal summand is the
closed Gaussian case-control exceedance between two different demes. -/
noncomputable def DemeMixture.pooledAUC {D : ℕ} (mix : DemeMixture D) : ℝ :=
  ∑ i, ∑ j, mix.caseWeight i * mix.controlWeight j *
    crossDemeCaseControlAUCOn (mix.law i) (mix.law j)
      (mix.discriminationDomain i) (mix.discriminationDomain j)

/-! ## Exact finite-cohort evaluator used by the simulation pipeline -/

/-- A realized binary-risk cohort on any finite individual index.  Predicted risks are kept
strictly inside `(0,1)`, matching the evaluator after clipping and making `logit` finite. -/
structure BinaryRiskCohort (Individual : Type*) [Fintype Individual] where
  outcome : Individual → Bool
  score : Individual → ℝ
  predictedRisk : Individual → ℝ
  card_pos : 0 < Fintype.card Individual
  predictedRisk_pos : ∀ individual, 0 < predictedRisk individual
  predictedRisk_lt_one : ∀ individual, predictedRisk individual < 1

/-- Number of cases, represented in the metric's real arithmetic. -/
noncomputable def BinaryRiskCohort.caseMass {Individual : Type*} [Fintype Individual]
    (cohort : BinaryRiskCohort Individual) : ℝ :=
  ∑ individual, if cohort.outcome individual then 1 else 0

/-- Number of controls. -/
noncomputable def BinaryRiskCohort.controlMass {Individual : Type*} [Fintype Individual]
    (cohort : BinaryRiskCohort Individual) : ℝ :=
  ∑ individual, if cohort.outcome individual then 0 else 1

/-- Arithmetic mean over a finite cohort. -/
private noncomputable def finiteCohortMean {Individual : Type*} [Fintype Individual]
    (value : Individual → ℝ) : ℝ :=
  (∑ individual, value individual) / Fintype.card Individual

/-- Real-valued binary outcome. -/
def BinaryRiskCohort.outcomeValue {Individual : Type*} [Fintype Individual]
    (cohort : BinaryRiskCohort Individual) (individual : Individual) : ℝ :=
  if cohort.outcome individual then 1 else 0

/-- Exact empirical Brier score, including the pipeline's finite-cohort averaging. -/
noncomputable def BinaryRiskCohort.brier {Individual : Type*} [Fintype Individual]
    (cohort : BinaryRiskCohort Individual) : ℝ :=
  finiteCohortMean fun individual ↦
    (cohort.outcomeValue individual - cohort.predictedRisk individual) ^ 2

/-- Exact empirical deployed-score variance with population (`ddof = 0`) normalization. -/
noncomputable def BinaryRiskCohort.scoreVariance {Individual : Type*} [Fintype Individual]
    (cohort : BinaryRiskCohort Individual) : ℝ :=
  let mean := finiteCohortMean cohort.score
  finiteCohortMean fun individual ↦ (cohort.score individual - mean) ^ 2

/-- Empirical predicted-risk variance, used in observed-risk `R²`. -/
noncomputable def BinaryRiskCohort.predictedRiskVariance
    {Individual : Type*} [Fintype Individual]
    (cohort : BinaryRiskCohort Individual) : ℝ :=
  let mean := finiteCohortMean cohort.predictedRisk
  finiteCohortMean fun individual ↦ (cohort.predictedRisk individual - mean) ^ 2

/-- Empirical binary-outcome variance. -/
noncomputable def BinaryRiskCohort.outcomeVariance {Individual : Type*} [Fintype Individual]
    (cohort : BinaryRiskCohort Individual) : ℝ :=
  let mean := finiteCohortMean cohort.outcomeValue
  finiteCohortMean fun individual ↦ (cohort.outcomeValue individual - mean) ^ 2

/-- Empirical covariance of predicted risk with binary outcome. -/
noncomputable def BinaryRiskCohort.predictiveCovariance
    {Individual : Type*} [Fintype Individual]
    (cohort : BinaryRiskCohort Individual) : ℝ :=
  let predictionMean := finiteCohortMean cohort.predictedRisk
  let outcomeMean := finiteCohortMean cohort.outcomeValue
  finiteCohortMean fun individual ↦
    (cohort.predictedRisk individual - predictionMean) *
      (cohort.outcomeValue individual - outcomeMean)

/-- Domain of empirical `R²`: neither variable is constant. -/
structure BinaryRiskCohort.R2Domain {Individual : Type*} [Fintype Individual]
    (cohort : BinaryRiskCohort Individual) : Prop where
  predictedRiskVariance_pos : 0 < cohort.predictedRiskVariance
  outcomeVariance_pos : 0 < cohort.outcomeVariance

/-- Exact empirical observed-risk `R²`, the squared Pearson correlation of predicted risk
and the realized binary outcome. -/
noncomputable def BinaryRiskCohort.observedRiskR2 {Individual : Type*} [Fintype Individual]
    (cohort : BinaryRiskCohort Individual) (_ : cohort.R2Domain) : ℝ :=
  cohort.predictiveCovariance ^ 2 /
    (cohort.predictedRiskVariance * cohort.outcomeVariance)

/-- Domain of empirical AUC: both outcome classes occur. -/
structure BinaryRiskCohort.AUCDomain {Individual : Type*} [Fintype Individual]
    (cohort : BinaryRiskCohort Individual) : Prop where
  caseMass_pos : 0 < cohort.caseMass
  controlMass_pos : 0 < cohort.controlMass

/-- A singleton cohort cannot contain both a case and a control.  Thus a total real-valued
AUC law on every positive cohort size is impossible independently of demographic
identifiability; the exact endpoint must retain an undefined branch or restrict its domain. -/
theorem BinaryRiskCohort.noAUCDomain_singleton (cohort : BinaryRiskCohort (Fin 1)) :
    ¬ cohort.AUCDomain := by
  intro domain
  cases h : cohort.outcome 0
  · have hcase : cohort.caseMass = 0 := by
      simp [BinaryRiskCohort.caseMass, h]
    linarith [domain.caseMass_pos]
  · have hcontrol : cohort.controlMass = 0 := by
      simp [BinaryRiskCohort.controlMass, h]
    linarith [domain.controlMass_pos]

/-- A singleton binary outcome is constant, so observed-risk squared correlation is also
undefined on the smallest admitted cohort. -/
theorem BinaryRiskCohort.noR2Domain_singleton (cohort : BinaryRiskCohort (Fin 1)) :
    ¬ cohort.R2Domain := by
  intro domain
  have hvariance : cohort.outcomeVariance = 0 := by
    simp [BinaryRiskCohort.outcomeVariance, finiteCohortMean]
  linarith [domain.outcomeVariance_pos]

/-- One case-control comparison with half credit for a predicted-risk tie. -/
noncomputable def empiricalAUCComparison (caseRisk controlRisk : ℝ) : ℝ :=
  if controlRisk < caseRisk then 1 else if caseRisk = controlRisk then 1 / 2 else 0

/-- Exact empirical AUC as the Mann--Whitney pair average used by standard evaluators. -/
noncomputable def BinaryRiskCohort.auc {Individual : Type*} [Fintype Individual]
    (cohort : BinaryRiskCohort Individual) (_ : cohort.AUCDomain) : ℝ :=
  (∑ caseIndividual, ∑ controlIndividual,
    if cohort.outcome caseIndividual && !cohort.outcome controlIndividual then
      empiricalAUCComparison (cohort.predictedRisk caseIndividual)
        (cohort.predictedRisk controlIndividual)
    else 0) / (cohort.caseMass * cohort.controlMass)

/-- Fixed inverse L2 strength used by gnomon's binary calibration refit. -/
def binaryCalibrationC : ℝ := 1000000

/-- The Bernoulli log-partition function.  Naming it separately exposes the strict
convexity that makes the finite ridge-logistic calibration fit identifiable. -/
noncomputable def logisticSoftplus (linearPredictor : ℝ) : ℝ :=
  Real.log (1 + Real.exp linearPredictor)

/-- The derivative of `log (1 + exp z)` is the logistic sigmoid. -/
theorem hasDerivAt_logisticSoftplus (linearPredictor : ℝ) :
    HasDerivAt logisticSoftplus (Real.sigmoid linearPredictor) linearPredictor := by
  have hpositive : 0 < 1 + Real.exp linearPredictor := by positivity
  have hsigmoid : Real.sigmoid linearPredictor =
      Real.exp linearPredictor / (1 + Real.exp linearPredictor) := by
    rw [Real.sigmoid_def]
    have hexp : Real.exp linearPredictor ≠ 0 := (Real.exp_pos _).ne'
    field_simp [Real.exp_neg, hexp]
    rw [add_mul, one_mul]
    rw [← Real.exp_add]
    simp [add_comm]
  have hderiv := ((hasDerivAt_const linearPredictor (1 : ℝ)).add
    (Real.hasDerivAt_exp linearPredictor)).log hpositive.ne'
  simpa only [logisticSoftplus, hsigmoid, Pi.add_apply, zero_add] using hderiv

/-- The derivative identity used by the strict-convexity proof and the score equations. -/
theorem deriv_logisticSoftplus (linearPredictor : ℝ) :
    deriv logisticSoftplus linearPredictor = Real.sigmoid linearPredictor :=
  (hasDerivAt_logisticSoftplus linearPredictor).deriv

/-- Softplus is strictly convex on the complete real line. -/
theorem strictConvexOn_logisticSoftplus :
    StrictConvexOn ℝ Set.univ logisticSoftplus := by
  have hderivative : StrictMonoOn (deriv logisticSoftplus) (interior Set.univ) := by
    intro first _ second _ hlt
    simpa only [deriv_logisticSoftplus] using Real.sigmoid_strictMono hlt
  have hcontinuous : Continuous logisticSoftplus :=
    continuous_iff_continuousAt.mpr fun point ↦
      (hasDerivAt_logisticSoftplus point).continuousAt
  exact hderivative.strictConvexOn_of_deriv convex_univ
    hcontinuous.continuousOn

/-- One exact Bernoulli negative-log-likelihood contribution. -/
noncomputable def binaryLogisticLoss (outcome linearPredictor : ℝ) : ℝ :=
  logisticSoftplus linearPredictor - outcome * linearPredictor

/-- Subtracting the affine outcome term does not change strict convexity. -/
theorem strictConvexOn_binaryLogisticLoss (outcome : ℝ) :
    StrictConvexOn ℝ Set.univ (binaryLogisticLoss outcome) := by
  have haffine : ConvexOn ℝ Set.univ (fun z : ℝ ↦ -(outcome * z)) := by
    refine ⟨convex_univ, ?_⟩
    intro first _ second _ firstWeight secondWeight _ _ _
    apply le_of_eq
    simp only [smul_eq_mul]
    ring
  simpa only [binaryLogisticLoss, sub_eq_add_neg] using
    strictConvexOn_logisticSoftplus.add_convexOn haffine

/-- Softplus dominates zero. -/
theorem logisticSoftplus_nonneg (linearPredictor : ℝ) :
    0 ≤ logisticSoftplus linearPredictor := by
  rw [logisticSoftplus, ← Real.log_one]
  exact Real.log_le_log zero_lt_one (by linarith [Real.exp_pos linearPredictor])

/-- Softplus also dominates its linear argument. -/
theorem linearPredictor_le_logisticSoftplus (linearPredictor : ℝ) :
    linearPredictor ≤ logisticSoftplus linearPredictor := by
  calc
    linearPredictor = Real.log (Real.exp linearPredictor) := (Real.log_exp _).symm
    _ ≤ Real.log (1 + Real.exp linearPredictor) :=
      Real.log_le_log (Real.exp_pos _) (by linarith [Real.exp_pos linearPredictor])
    _ = logisticSoftplus linearPredictor := rfl

/-- Every realized Bernoulli contribution is nonnegative. -/
theorem BinaryRiskCohort.binaryLogisticLoss_outcomeValue_nonneg
    {Individual : Type*} [Fintype Individual]
    (cohort : BinaryRiskCohort Individual) (individual : Individual)
    (linearPredictor : ℝ) :
    0 ≤ binaryLogisticLoss (cohort.outcomeValue individual) linearPredictor := by
  cases h : cohort.outcome individual
  · simpa [BinaryRiskCohort.outcomeValue, h, binaryLogisticLoss] using
      logisticSoftplus_nonneg linearPredictor
  · simp only [BinaryRiskCohort.outcomeValue, h, ↓reduceIte, binaryLogisticLoss, one_mul]
    linarith [linearPredictor_le_logisticSoftplus linearPredictor]

/-- A realized control contribution dominates its linear predictor. -/
theorem BinaryRiskCohort.linearPredictor_le_controlLoss
    {Individual : Type*} [Fintype Individual]
    (cohort : BinaryRiskCohort Individual) (individual : Individual)
    (hcontrol : cohort.outcome individual = false) (linearPredictor : ℝ) :
    linearPredictor ≤ binaryLogisticLoss (cohort.outcomeValue individual) linearPredictor := by
  simpa [BinaryRiskCohort.outcomeValue, hcontrol, binaryLogisticLoss] using
    linearPredictor_le_logisticSoftplus linearPredictor

/-- A realized case contribution dominates the negative linear predictor. -/
theorem BinaryRiskCohort.neg_linearPredictor_le_caseLoss
    {Individual : Type*} [Fintype Individual]
    (cohort : BinaryRiskCohort Individual) (individual : Individual)
    (hcase : cohort.outcome individual = true) (linearPredictor : ℝ) :
    -linearPredictor ≤ binaryLogisticLoss (cohort.outcomeValue individual) linearPredictor := by
  simp only [BinaryRiskCohort.outcomeValue, hcase, ↓reduceIte, binaryLogisticLoss, one_mul]
  linarith [logisticSoftplus_nonneg linearPredictor]

/-- One exact finite-cohort likelihood contribution as a function of both fit parameters. -/
noncomputable def BinaryRiskCohort.calibrationIndividualLoss
    {Individual : Type*} [Fintype Individual]
    (cohort : BinaryRiskCohort Individual) (individual : Individual)
    (parameter : ℝ × ℝ) : ℝ :=
  binaryLogisticLoss (cohort.outcomeValue individual)
    (parameter.1 + parameter.2 * prevalenceLogit (cohort.predictedRisk individual))

/-- Every finite-cohort likelihood contribution is nonnegative. -/
theorem BinaryRiskCohort.calibrationIndividualLoss_nonneg
    {Individual : Type*} [Fintype Individual]
    (cohort : BinaryRiskCohort Individual) (individual : Individual)
    (parameter : ℝ × ℝ) :
    0 ≤ cohort.calibrationIndividualLoss individual parameter :=
  cohort.binaryLogisticLoss_outcomeValue_nonneg individual _

/-- Every individual contribution is continuous in intercept and slope. -/
theorem BinaryRiskCohort.continuous_calibrationIndividualLoss
    {Individual : Type*} [Fintype Individual]
    (cohort : BinaryRiskCohort Individual) (individual : Individual) :
    Continuous (cohort.calibrationIndividualLoss individual) := by
  have hsoftplus : Continuous logisticSoftplus :=
    continuous_iff_continuousAt.mpr fun point ↦
      (hasDerivAt_logisticSoftplus point).continuousAt
  have hloss : Continuous (binaryLogisticLoss (cohort.outcomeValue individual)) := by
    exact hsoftplus.sub
      (continuous_const.mul continuous_id)
  exact hloss.comp
    (continuous_fst.add (continuous_snd.mul continuous_const))

/-- Empirical variance of the clipped-risk logits used by the executable calibration guard. -/
noncomputable def BinaryRiskCohort.logitRiskVariance
    {Individual : Type*} [Fintype Individual]
    (cohort : BinaryRiskCohort Individual) : ℝ :=
  let mean := finiteCohortMean fun individual ↦
    prevalenceLogit (cohort.predictedRisk individual)
  finiteCohortMean fun individual ↦
    (prevalenceLogit (cohort.predictedRisk individual) - mean) ^ 2

/-- Logistic calibration objective at intercept/slope `(a,b)`.  Scikit-learn's `lbfgs`
convention leaves the intercept unpenalized and, after multiplying its mean-loss objective by
cohort size, adds `b²/(2C)` to the summed Bernoulli loss. -/
noncomputable def BinaryRiskCohort.logisticCalibrationObjective
    {Individual : Type*} [Fintype Individual]
    (cohort : BinaryRiskCohort Individual) (parameter : ℝ × ℝ) : ℝ :=
  ∑ individual, cohort.calibrationIndividualLoss individual parameter
  + parameter.2 ^ 2 / (2 * binaryCalibrationC)

/-- The exact finite ridge-logistic objective is continuous. -/
theorem BinaryRiskCohort.continuous_logisticCalibrationObjective
    {Individual : Type*} [Fintype Individual]
    (cohort : BinaryRiskCohort Individual) :
    Continuous cohort.logisticCalibrationObjective := by
  unfold BinaryRiskCohort.logisticCalibrationObjective
  apply Continuous.add
  · exact continuous_finset_sum Finset.univ fun individual _ ↦
      cohort.continuous_calibrationIndividualLoss individual
  · exact (continuous_snd.pow 2).div_const _

/-- The exact finite ridge-logistic objective is nonnegative. -/
theorem BinaryRiskCohort.logisticCalibrationObjective_nonneg
    {Individual : Type*} [Fintype Individual]
    (cohort : BinaryRiskCohort Individual) (parameter : ℝ × ℝ) :
    0 ≤ cohort.logisticCalibrationObjective parameter := by
  unfold BinaryRiskCohort.logisticCalibrationObjective
  apply add_nonneg
  · exact Finset.sum_nonneg fun individual _ ↦
      cohort.calibrationIndividualLoss_nonneg individual parameter
  · exact div_nonneg (sq_nonneg _) (by norm_num [binaryCalibrationC])

/-- Any one likelihood contribution is bounded above by the complete objective. -/
theorem BinaryRiskCohort.calibrationIndividualLoss_le_objective
    {Individual : Type*} [Fintype Individual]
    (cohort : BinaryRiskCohort Individual) (individual : Individual)
    (parameter : ℝ × ℝ) :
    cohort.calibrationIndividualLoss individual parameter ≤
      cohort.logisticCalibrationObjective parameter := by
  unfold BinaryRiskCohort.logisticCalibrationObjective
  calc
    cohort.calibrationIndividualLoss individual parameter ≤
        ∑ other, cohort.calibrationIndividualLoss other parameter :=
      Finset.single_le_sum
        (fun other _ ↦ cohort.calibrationIndividualLoss_nonneg other parameter)
        (Finset.mem_univ individual)
    _ ≤ _ := le_add_of_nonneg_right
      (div_nonneg (sq_nonneg _) (by norm_num [binaryCalibrationC]))

/-- The ridge term is bounded above by the complete objective. -/
theorem BinaryRiskCohort.ridgePenalty_le_objective
    {Individual : Type*} [Fintype Individual]
    (cohort : BinaryRiskCohort Individual) (parameter : ℝ × ℝ) :
    parameter.2 ^ 2 / (2 * binaryCalibrationC) ≤
      cohort.logisticCalibrationObjective parameter := by
  unfold BinaryRiskCohort.logisticCalibrationObjective
  exact le_add_of_nonneg_left (Finset.sum_nonneg fun individual _ ↦
    cohort.calibrationIndividualLoss_nonneg individual parameter)

/-- Positive case mass is equivalent to the occurrence of an actual case. -/
theorem BinaryRiskCohort.exists_case_of_caseMass_pos
    {Individual : Type*} [Fintype Individual]
    (cohort : BinaryRiskCohort Individual) (hcaseMass : 0 < cohort.caseMass) :
    ∃ individual, cohort.outcome individual = true := by
  by_contra hnone
  push_neg at hnone
  have houtcome : ∀ individual, cohort.outcome individual = false := by
    intro individual
    cases h : cohort.outcome individual
    · rfl
    · exact (hnone individual h).elim
  have hzero : cohort.caseMass = 0 := by
    simp [BinaryRiskCohort.caseMass, houtcome]
  linarith

/-- Positive control mass is equivalent to the occurrence of an actual control. -/
theorem BinaryRiskCohort.exists_control_of_controlMass_pos
    {Individual : Type*} [Fintype Individual]
    (cohort : BinaryRiskCohort Individual) (hcontrolMass : 0 < cohort.controlMass) :
    ∃ individual, cohort.outcome individual = false := by
  by_contra hnone
  push_neg at hnone
  have houtcome : ∀ individual, cohort.outcome individual = true := by
    intro individual
    cases h : cohort.outcome individual
    · exact (hnone individual h).elim
    · rfl
  have hzero : cohort.controlMass = 0 := by
    simp [BinaryRiskCohort.controlMass, houtcome]
  linarith

/-- The baseline sublevel is bounded.  The ridge term bounds the slope; one realized control
bounds the intercept above and one realized case bounds it below. -/
theorem BinaryRiskCohort.isBounded_logisticCalibration_baselineSublevel
    {Individual : Type*} [Fintype Individual]
    (cohort : BinaryRiskCohort Individual)
    (caseIndividual controlIndividual : Individual)
    (hcase : cohort.outcome caseIndividual = true)
    (hcontrol : cohort.outcome controlIndividual = false) :
    Bornology.IsBounded {parameter : ℝ × ℝ |
      cohort.logisticCalibrationObjective parameter ≤
        cohort.logisticCalibrationObjective (0, 0)} := by
  let baseline := cohort.logisticCalibrationObjective (0, 0)
  let slopeBound := baseline * (2 * binaryCalibrationC) + 1
  let caseLogit := prevalenceLogit (cohort.predictedRisk caseIndividual)
  let controlLogit := prevalenceLogit (cohort.predictedRisk controlIndividual)
  let interceptBound := baseline + slopeBound * |caseLogit| + slopeBound * |controlLogit|
  apply isBounded_iff_forall_norm_le.mpr
  refine ⟨max interceptBound slopeBound, ?_⟩
  intro parameter hsublevel
  have hbaseline_nonneg : 0 ≤ baseline := by
    exact cohort.logisticCalibrationObjective_nonneg (0, 0)
  have hdenominator : 0 < 2 * binaryCalibrationC := by
    norm_num [binaryCalibrationC]
  have hpenalty : parameter.2 ^ 2 / (2 * binaryCalibrationC) ≤ baseline :=
    (cohort.ridgePenalty_le_objective parameter).trans hsublevel
  have hsquare : parameter.2 ^ 2 ≤ baseline * (2 * binaryCalibrationC) :=
    (div_le_iff₀ hdenominator).mp hpenalty
  have habs_le_square_add_one : |parameter.2| ≤ parameter.2 ^ 2 + 1 := by
    nlinarith [sq_nonneg (|parameter.2| - 1), sq_abs parameter.2,
      abs_nonneg parameter.2]
  have hslope : |parameter.2| ≤ slopeBound := by
    exact habs_le_square_add_one.trans (add_le_add_right hsquare 1)
  have hslopeBound_nonneg : 0 ≤ slopeBound :=
    (abs_nonneg parameter.2).trans hslope
  have hcontrolLinear :
      parameter.1 + parameter.2 * controlLogit ≤
        cohort.calibrationIndividualLoss controlIndividual parameter := by
    simpa only [BinaryRiskCohort.calibrationIndividualLoss, controlLogit] using
      cohort.linearPredictor_le_controlLoss controlIndividual hcontrol
        (parameter.1 + parameter.2 * controlLogit)
  have hcontrolAtMostBaseline :
      parameter.1 + parameter.2 * controlLogit ≤ baseline :=
    hcontrolLinear.trans <|
      (cohort.calibrationIndividualLoss_le_objective controlIndividual parameter).trans hsublevel
  have hparameterUpper : parameter.1 ≤ baseline + slopeBound * |controlLogit| := by
    calc
      parameter.1 ≤ baseline - parameter.2 * controlLogit := by linarith
      _ ≤ baseline + |parameter.2| * |controlLogit| := by
        rw [← abs_mul]
        linarith [neg_le_abs (parameter.2 * controlLogit)]
      _ ≤ baseline + slopeBound * |controlLogit| := by
        exact add_le_add_left
          (mul_le_mul_of_nonneg_right hslope (abs_nonneg controlLogit)) baseline
  have hcaseLinear :
      -(parameter.1 + parameter.2 * caseLogit) ≤
        cohort.calibrationIndividualLoss caseIndividual parameter := by
    simpa only [BinaryRiskCohort.calibrationIndividualLoss, caseLogit] using
      cohort.neg_linearPredictor_le_caseLoss caseIndividual hcase
        (parameter.1 + parameter.2 * caseLogit)
  have hcaseAtMostBaseline :
      -(parameter.1 + parameter.2 * caseLogit) ≤ baseline :=
    hcaseLinear.trans <|
      (cohort.calibrationIndividualLoss_le_objective caseIndividual parameter).trans hsublevel
  have hnegativeParameterUpper : -parameter.1 ≤ baseline + slopeBound * |caseLogit| := by
    calc
      -parameter.1 ≤ baseline + parameter.2 * caseLogit := by linarith
      _ ≤ baseline + |parameter.2| * |caseLogit| := by
        rw [← abs_mul]
        exact add_le_add_left (le_abs_self _) baseline
      _ ≤ baseline + slopeBound * |caseLogit| := by
        exact add_le_add_left
          (mul_le_mul_of_nonneg_right hslope (abs_nonneg caseLogit)) baseline
  have hintercept : |parameter.1| ≤ interceptBound := by
    apply abs_le.mpr
    constructor
    · have : -parameter.1 ≤ interceptBound := by
        exact hnegativeParameterUpper.trans <|
          le_add_of_nonneg_right (mul_nonneg hslopeBound_nonneg (abs_nonneg controlLogit))
      linarith
    · exact hparameterUpper.trans <|
        (by
          dsimp only [interceptBound]
          linarith [mul_nonneg hslopeBound_nonneg (abs_nonneg caseLogit)])
  rw [Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs]
  exact max_le (hintercept.trans (le_max_left _ _))
    (hslope.trans (le_max_right _ _))

/-- A case and a control make the unpenalized intercept coercive, while the positive ridge
makes the slope coercive; hence the exact finite objective attains a global minimum. -/
theorem BinaryRiskCohort.exists_logisticCalibrationMinimizer
    {Individual : Type*} [Fintype Individual]
    (cohort : BinaryRiskCohort Individual)
    (hcaseMass : 0 < cohort.caseMass) (hcontrolMass : 0 < cohort.controlMass) :
    ∃ parameter : ℝ × ℝ, ∀ candidate,
      cohort.logisticCalibrationObjective parameter ≤
        cohort.logisticCalibrationObjective candidate := by
  obtain ⟨caseIndividual, hcase⟩ := cohort.exists_case_of_caseMass_pos hcaseMass
  obtain ⟨controlIndividual, hcontrol⟩ :=
    cohort.exists_control_of_controlMass_pos hcontrolMass
  exact cohort.continuous_logisticCalibrationObjective.exists_forall_le_of_isBounded
    (0, 0) (cohort.isBounded_logisticCalibration_baselineSublevel
      caseIndividual controlIndividual hcase hcontrol)

/-- Each observation's loss is convex in the two calibration parameters.  It is the strictly
convex scalar Bernoulli loss precomposed with an affine predictor. -/
theorem BinaryRiskCohort.convexOn_calibrationIndividualLoss
    {Individual : Type*} [Fintype Individual]
    (cohort : BinaryRiskCohort Individual) (individual : Individual) :
    ConvexOn ℝ Set.univ (cohort.calibrationIndividualLoss individual) := by
  refine ⟨convex_univ, ?_⟩
  intro first _ second _ firstWeight secondWeight hfirstWeight hsecondWeight hweightSum
  let firstPredictor := first.1 + first.2 * prevalenceLogit (cohort.predictedRisk individual)
  let secondPredictor := second.1 + second.2 * prevalenceLogit (cohort.predictedRisk individual)
  have hconvex := (strictConvexOn_binaryLogisticLoss
    (cohort.outcomeValue individual)).convexOn.2
      (Set.mem_univ firstPredictor) (Set.mem_univ secondPredictor)
      hfirstWeight hsecondWeight hweightSum
  have hpredictor :
      (firstWeight • first + secondWeight • second).1 +
          (firstWeight • first + secondWeight • second).2 *
            prevalenceLogit (cohort.predictedRisk individual) =
        firstWeight • firstPredictor + secondWeight • secondPredictor := by
    simp only [firstPredictor, secondPredictor, Prod.smul_fst, Prod.smul_snd,
      Prod.fst_add, Prod.snd_add, smul_eq_mul]
    ring
  change binaryLogisticLoss (cohort.outcomeValue individual)
      ((firstWeight • first + secondWeight • second).1 +
        (firstWeight • first + secondWeight • second).2 *
          prevalenceLogit (cohort.predictedRisk individual)) ≤
    firstWeight • binaryLogisticLoss (cohort.outcomeValue individual) firstPredictor +
      secondWeight • binaryLogisticLoss (cohort.outcomeValue individual) secondPredictor
  rw [hpredictor]
  exact hconvex

/-- The individual parameter loss is strictly Jensen-convex whenever the two affine predictors
differ. -/
theorem BinaryRiskCohort.calibrationIndividualLoss_strict_of_predictor_ne
    {Individual : Type*} [Fintype Individual]
    (cohort : BinaryRiskCohort Individual) (individual : Individual)
    (first second : ℝ × ℝ) (firstWeight secondWeight : ℝ)
    (hfirstWeight : 0 < firstWeight) (hsecondWeight : 0 < secondWeight)
    (hweightSum : firstWeight + secondWeight = 1)
    (hpredictor :
      first.1 + first.2 * prevalenceLogit (cohort.predictedRisk individual) ≠
        second.1 + second.2 * prevalenceLogit (cohort.predictedRisk individual)) :
    cohort.calibrationIndividualLoss individual
        (firstWeight • first + secondWeight • second) <
      firstWeight • cohort.calibrationIndividualLoss individual first +
        secondWeight • cohort.calibrationIndividualLoss individual second := by
  let firstPredictor := first.1 + first.2 * prevalenceLogit (cohort.predictedRisk individual)
  let secondPredictor := second.1 + second.2 * prevalenceLogit (cohort.predictedRisk individual)
  have hstrict := (strictConvexOn_binaryLogisticLoss
    (cohort.outcomeValue individual)).2
      (Set.mem_univ firstPredictor) (Set.mem_univ secondPredictor)
      (by exact hpredictor) hfirstWeight hsecondWeight hweightSum
  have hcombinedPredictor :
      (firstWeight • first + secondWeight • second).1 +
          (firstWeight • first + secondWeight • second).2 *
            prevalenceLogit (cohort.predictedRisk individual) =
        firstWeight • firstPredictor + secondWeight • secondPredictor := by
    simp only [firstPredictor, secondPredictor, Prod.smul_fst, Prod.smul_snd,
      Prod.fst_add, Prod.snd_add, smul_eq_mul]
    ring
  change binaryLogisticLoss (cohort.outcomeValue individual)
      ((firstWeight • first + secondWeight • second).1 +
        (firstWeight • first + secondWeight • second).2 *
          prevalenceLogit (cohort.predictedRisk individual)) <
    firstWeight • binaryLogisticLoss (cohort.outcomeValue individual) firstPredictor +
      secondWeight • binaryLogisticLoss (cohort.outcomeValue individual) secondPredictor
  rw [hcombinedPredictor]
  exact hstrict

/-- Jensen's inequality for the exact scalar ridge penalty. -/
theorem ridgePenalty_convex (first second firstWeight secondWeight : ℝ)
    (hfirstWeight : 0 ≤ firstWeight) (hsecondWeight : 0 ≤ secondWeight)
    (hweightSum : firstWeight + secondWeight = 1) :
    (firstWeight * first + secondWeight * second) ^ 2 / (2 * binaryCalibrationC) ≤
      firstWeight * (first ^ 2 / (2 * binaryCalibrationC)) +
        secondWeight * (second ^ 2 / (2 * binaryCalibrationC)) := by
  have hweightProduct : 0 ≤ firstWeight * secondWeight :=
    mul_nonneg hfirstWeight hsecondWeight
  have hsquare : 0 ≤ (first - second) ^ 2 := sq_nonneg _
  norm_num [binaryCalibrationC]
  nlinarith

/-- The ridge Jensen inequality is strict when both weights are positive and slopes differ. -/
theorem ridgePenalty_strict (first second firstWeight secondWeight : ℝ)
    (hfirstWeight : 0 < firstWeight) (hsecondWeight : 0 < secondWeight)
    (hweightSum : firstWeight + secondWeight = 1) (hne : first ≠ second) :
    (firstWeight * first + secondWeight * second) ^ 2 / (2 * binaryCalibrationC) <
      firstWeight * (first ^ 2 / (2 * binaryCalibrationC)) +
        secondWeight * (second ^ 2 / (2 * binaryCalibrationC)) := by
  have hweightProduct : 0 < firstWeight * secondWeight :=
    mul_pos hfirstWeight hsecondWeight
  have hsquare : 0 < (first - second) ^ 2 :=
    sq_pos_of_ne_zero (sub_ne_zero.mpr hne)
  norm_num [binaryCalibrationC]
  nlinarith

/-- The full finite ridge-logistic objective is strictly convex in intercept and slope.  If
slopes differ, the ridge term supplies strictness.  If slopes agree, distinct parameter pairs
have distinct intercepts, so every observation's Bernoulli contribution supplies strictness. -/
theorem BinaryRiskCohort.strictConvexOn_logisticCalibrationObjective
    {Individual : Type*} [Fintype Individual]
    (cohort : BinaryRiskCohort Individual) :
    StrictConvexOn ℝ Set.univ cohort.logisticCalibrationObjective := by
  haveI : Nonempty Individual := Fintype.card_pos_iff.mp cohort.card_pos
  refine ⟨convex_univ, ?_⟩
  intro first _ second _ hparameters firstWeight secondWeight
    hfirstWeight hsecondWeight hweightSum
  let combined := firstWeight • first + secondWeight • second
  have hsum_le :
      (∑ individual, cohort.calibrationIndividualLoss individual combined) ≤
        firstWeight • (∑ individual, cohort.calibrationIndividualLoss individual first) +
          secondWeight • (∑ individual, cohort.calibrationIndividualLoss individual second) := by
    calc
      (∑ individual, cohort.calibrationIndividualLoss individual combined) ≤
          ∑ individual,
            (firstWeight • cohort.calibrationIndividualLoss individual first +
              secondWeight • cohort.calibrationIndividualLoss individual second) := by
        exact Finset.sum_le_sum fun individual _ ↦
          (cohort.convexOn_calibrationIndividualLoss individual).2
            (Set.mem_univ first) (Set.mem_univ second)
            hfirstWeight.le hsecondWeight.le hweightSum
      _ = _ := by
        rw [Finset.sum_add_distrib, ← Finset.smul_sum, ← Finset.smul_sum]
  by_cases hslope : first.2 = second.2
  · have hintercept : first.1 ≠ second.1 := by
      intro hinterceptEqual
      apply hparameters
      exact Prod.ext hinterceptEqual hslope
    have hsum_strict :
        (∑ individual, cohort.calibrationIndividualLoss individual combined) <
          firstWeight • (∑ individual, cohort.calibrationIndividualLoss individual first) +
            secondWeight • (∑ individual, cohort.calibrationIndividualLoss individual second) := by
      calc
        (∑ individual, cohort.calibrationIndividualLoss individual combined) <
            ∑ individual,
              (firstWeight • cohort.calibrationIndividualLoss individual first +
                secondWeight • cohort.calibrationIndividualLoss individual second) := by
          apply Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty
          intro individual _
          apply cohort.calibrationIndividualLoss_strict_of_predictor_ne
            individual first second firstWeight secondWeight
            hfirstWeight hsecondWeight hweightSum
          intro hpredictor
          apply hintercept
          rw [hslope] at hpredictor
          linarith
        _ = _ := by
          rw [Finset.sum_add_distrib, ← Finset.smul_sum, ← Finset.smul_sum]
    have hpenalty_le := ridgePenalty_convex first.2 second.2 firstWeight secondWeight
      hfirstWeight.le hsecondWeight.le hweightSum
    have htotal := add_lt_add_of_lt_of_le hsum_strict hpenalty_le
    unfold BinaryRiskCohort.logisticCalibrationObjective
    dsimp only [combined] at htotal ⊢
    simp only [Prod.smul_snd, Prod.snd_add, smul_eq_mul] at htotal ⊢
    convert htotal using 1 <;> ring
  · have hpenalty_strict := ridgePenalty_strict first.2 second.2
      firstWeight secondWeight hfirstWeight hsecondWeight hweightSum hslope
    have htotal := add_lt_add_of_le_of_lt hsum_le hpenalty_strict
    unfold BinaryRiskCohort.logisticCalibrationObjective
    dsimp only [combined] at htotal ⊢
    simp only [Prod.smul_snd, Prod.snd_add, smul_eq_mul] at htotal ⊢
    convert htotal using 1 <;> ring

/-- A finite ridge-logistic calibration objective with both outcome classes has exactly one
global minimizer.  Existence is coercivity plus continuity; uniqueness is strict convexity. -/
theorem BinaryRiskCohort.existsUnique_logisticCalibrationMinimizer
    {Individual : Type*} [Fintype Individual]
    (cohort : BinaryRiskCohort Individual)
    (hcaseMass : 0 < cohort.caseMass) (hcontrolMass : 0 < cohort.controlMass) :
    ∃! parameter : ℝ × ℝ, ∀ candidate,
      cohort.logisticCalibrationObjective parameter ≤
        cohort.logisticCalibrationObjective candidate := by
  obtain ⟨parameter, hparameter⟩ :=
    cohort.exists_logisticCalibrationMinimizer hcaseMass hcontrolMass
  refine ⟨parameter, hparameter, ?_⟩
  intro other hother
  have hparameterMin : IsMinOn cohort.logisticCalibrationObjective Set.univ parameter :=
    fun candidate _ ↦ hparameter candidate
  have hotherMin : IsMinOn cohort.logisticCalibrationObjective Set.univ other :=
    fun candidate _ ↦ hother candidate
  exact cohort.strictConvexOn_logisticCalibrationObjective.eq_of_isMinOn
    hotherMin hparameterMin
    (Set.mem_univ other) (Set.mem_univ parameter)

/-- Domain of the logistic recalibration fit: exactly gnomon's executable outcome-metric,
cohort-size, and standard-deviation guards.  Existence and uniqueness of the ideal optimizer
are theorems above, not an assumption stored in this domain. -/
structure BinaryRiskCohort.LogisticCalibrationDomain
    {Individual : Type*} [Fintype Individual]
    (cohort : BinaryRiskCohort Individual) : Prop where
  minimumCohortSize : 20 ≤ Fintype.card Individual
  caseMass_pos : 0 < cohort.caseMass
  controlMass_pos : 0 < cohort.controlMass
  logitSD_above_guard : (1 / 1000000000 : ℝ) < Real.sqrt cohort.logitRiskVariance

/-- Exactly characterized ridge-logistic recalibration parameters: the unique objective
minimizer, not a covariance-ratio surrogate.  Floating-point stopping tolerance is numerical
evaluation error around this operator-defined target. -/
noncomputable def BinaryRiskCohort.logisticCalibrationFit
    {Individual : Type*} [Fintype Individual]
    (cohort : BinaryRiskCohort Individual) (domain : cohort.LogisticCalibrationDomain) :
    ℝ × ℝ :=
  (cohort.existsUnique_logisticCalibrationMinimizer
    domain.caseMass_pos domain.controlMass_pos).exists.choose

/-- The selected calibration pair satisfies the defining global optimum law. -/
theorem BinaryRiskCohort.logisticCalibrationFit_spec
    {Individual : Type*} [Fintype Individual]
    (cohort : BinaryRiskCohort Individual) (domain : cohort.LogisticCalibrationDomain) :
    ∀ candidate, cohort.logisticCalibrationObjective (cohort.logisticCalibrationFit domain) ≤
      cohort.logisticCalibrationObjective candidate :=
  (cohort.existsUnique_logisticCalibrationMinimizer
    domain.caseMass_pos domain.controlMass_pos).exists.choose_spec

/-- Pipeline calibration slope `b` from `y ~ a + b logit(p)`. -/
noncomputable def BinaryRiskCohort.calibrationSlope
    {Individual : Type*} [Fintype Individual]
    (cohort : BinaryRiskCohort Individual) (domain : cohort.LogisticCalibrationDomain) : ℝ :=
  (cohort.logisticCalibrationFit domain).2

/-- Root equation used by gnomon's bounded Brent solve for calibration-in-the-large. -/
noncomputable def BinaryRiskCohort.citlEquation
    {Individual : Type*} [Fintype Individual]
    (cohort : BinaryRiskCohort Individual) (intercept : ℝ) : ℝ :=
  finiteCohortMean (fun individual ↦
    1 / (1 + Real.exp (-(intercept + prevalenceLogit (cohort.predictedRisk individual))))) -
      finiteCohortMean cohort.outcomeValue

/-- The CITL offset equation is continuous. -/
theorem BinaryRiskCohort.continuous_citlEquation
    {Individual : Type*} [Fintype Individual]
    (cohort : BinaryRiskCohort Individual) : Continuous cohort.citlEquation := by
  unfold BinaryRiskCohort.citlEquation finiteCohortMean
  apply Continuous.sub
  · apply Continuous.div_const
    apply continuous_finset_sum
    intro individual _
    apply Continuous.div
    · exact continuous_const
    · exact continuous_const.add (Real.continuous_exp.comp
        ((continuous_id.add continuous_const).neg))
    · intro intercept
      positivity
  · exact continuous_const

/-- The CITL offset equation is strictly increasing on every nonempty cohort. -/
theorem BinaryRiskCohort.strictMono_citlEquation
    {Individual : Type*} [Fintype Individual]
    (cohort : BinaryRiskCohort Individual) : StrictMono cohort.citlEquation := by
  intro first second hlt
  unfold BinaryRiskCohort.citlEquation finiteCohortMean
  have hterm : ∀ individual,
      1 / (1 + Real.exp (-(first + prevalenceLogit (cohort.predictedRisk individual)))) <
        1 / (1 + Real.exp (-(second + prevalenceLogit (cohort.predictedRisk individual)))) := by
    intro individual
    have hexp :
        Real.exp (-(second + prevalenceLogit (cohort.predictedRisk individual))) <
          Real.exp (-(first + prevalenceLogit (cohort.predictedRisk individual))) := by
      exact Real.exp_lt_exp.mpr (by linarith)
    exact one_div_lt_one_div_of_lt (by positivity) (by linarith)
  have hsums :
      (∑ individual,
        1 / (1 + Real.exp (-(first + prevalenceLogit (cohort.predictedRisk individual))))) <
      ∑ individual,
        1 / (1 + Real.exp (-(second + prevalenceLogit (cohort.predictedRisk individual)))) := by
    apply Finset.sum_lt_sum
    · intro individual _
      exact (hterm individual).le
    · obtain ⟨witness⟩ := Fintype.card_pos_iff.mp cohort.card_pos
      exact ⟨witness, Finset.mem_univ _, hterm witness⟩
  have hmeans := div_lt_div_of_pos_right hsums (Nat.cast_pos.mpr cohort.card_pos)
  linarith

/-- Exact executable domain for CITL: the shared minimum-size and two-class guards pass, and
the actual `[-25,25]` Brent endpoints bracket zero.  Existence and uniqueness are derived
below rather than supplied as a proof field. -/
structure BinaryRiskCohort.CITLDomain
    {Individual : Type*} [Fintype Individual]
    (cohort : BinaryRiskCohort Individual) : Prop where
  minimumCohortSize : 20 ≤ Fintype.card Individual
  caseMass_pos : 0 < cohort.caseMass
  controlMass_pos : 0 < cohort.controlMass
  lowerEndpoint_nonpos : cohort.citlEquation (-25) ≤ 0
  upperEndpoint_nonneg : 0 ≤ cohort.citlEquation 25

/-- The executable CITL guards imply a unique root in the actual Brent bracket. -/
theorem BinaryRiskCohort.CITLDomain.existsUniqueBracketedRoot
    {Individual : Type*} [Fintype Individual]
    {cohort : BinaryRiskCohort Individual} (domain : cohort.CITLDomain) :
    ∃! intercept : ℝ,
      intercept ∈ Set.Icc (-25 : ℝ) 25 ∧ cohort.citlEquation intercept = 0 := by
  obtain ⟨root, hrootInterval, hroot⟩ :=
    intermediate_value_Icc (by norm_num : (-25 : ℝ) ≤ 25)
      cohort.continuous_citlEquation.continuousOn
      ⟨domain.lowerEndpoint_nonpos, domain.upperEndpoint_nonneg⟩
  refine ⟨root, ⟨hrootInterval, hroot⟩, ?_⟩
  intro other hother
  exact cohort.strictMono_citlEquation.injective (hother.2.trans hroot.symm)

/-- Exact calibration-in-the-large: the intercept-only refit with `logit(p)` as an offset. -/
noncomputable def BinaryRiskCohort.calibrationInTheLarge
    {Individual : Type*} [Fintype Individual]
    (cohort : BinaryRiskCohort Individual) (domain : cohort.CITLDomain) : ℝ :=
  domain.existsUniqueBracketedRoot.exists.choose

/-- The CITL value lies in the executable bracket and solves the exact offset equation. -/
theorem BinaryRiskCohort.calibrationInTheLarge_spec
    {Individual : Type*} [Fintype Individual]
    (cohort : BinaryRiskCohort Individual) (domain : cohort.CITLDomain) :
    cohort.calibrationInTheLarge domain ∈ Set.Icc (-25 : ℝ) 25 ∧
      cohort.citlEquation (cohort.calibrationInTheLarge domain) = 0 :=
  domain.existsUniqueBracketedRoot.exists.choose_spec

/-- Per-deme realized cohorts with exactly the visible study layout.  Cohort sizes are no
longer duplicated inside the realization, so the evaluator cannot silently analyze a panel
different from the one named by `PipelineStudyDesign`. -/
structure DemeBinaryRiskCohorts {D : ℕ} (design : PipelineStudyDesign D) where
  outcome : ∀ deme, Fin (design.cohortSize deme) → Bool
  score : ∀ deme, Fin (design.cohortSize deme) → ℝ
  predictedRisk : ∀ deme, Fin (design.cohortSize deme) → ℝ
  predictedRisk_pos : ∀ deme individual, 0 < predictedRisk deme individual
  predictedRisk_lt_one : ∀ deme individual, predictedRisk deme individual < 1
  pooledCard_pos : 0 < Fintype.card (Σ deme, Fin (design.cohortSize deme))

/-- One realized deme cohort. -/
def DemeBinaryRiskCohorts.atDeme {D : ℕ} {design : PipelineStudyDesign D}
    (cohorts : DemeBinaryRiskCohorts design)
    (deme : Fin D) : BinaryRiskCohort (Fin (design.cohortSize deme)) where
  outcome := cohorts.outcome deme
  score := cohorts.score deme
  predictedRisk := cohorts.predictedRisk deme
  card_pos := by simpa using design.cohortSize_pos deme
  predictedRisk_pos := cohorts.predictedRisk_pos deme
  predictedRisk_lt_one := cohorts.predictedRisk_lt_one deme

/-- The pooled realized cohort is concatenation, not an average of deme metrics. -/
def DemeBinaryRiskCohorts.pooled {D : ℕ} {design : PipelineStudyDesign D}
    (cohorts : DemeBinaryRiskCohorts design) :
    BinaryRiskCohort (Σ deme, Fin (design.cohortSize deme)) where
  outcome := fun individual ↦ cohorts.outcome individual.1 individual.2
  score := fun individual ↦ cohorts.score individual.1 individual.2
  predictedRisk := fun individual ↦ cohorts.predictedRisk individual.1 individual.2
  card_pos := cohorts.pooledCard_pos
  predictedRisk_pos := fun individual ↦ cohorts.predictedRisk_pos individual.1 individual.2
  predictedRisk_lt_one := fun individual ↦
    cohorts.predictedRisk_lt_one individual.1 individual.2

/-- Evaluate every requested discrimination/calibration coordinate on a realized set of
cohorts.  Each partial metric tests its own mathematical domain, so a degenerate finite draw
returns `none` rather than being excluded from the input type or assigned a numeric sentinel.
Pooled values are recomputed on the concatenated individuals.  Biological intermediates
return `none` because they are not empirical risk-cohort metrics. -/
noncomputable def DemeBinaryRiskCohorts.evaluate {D : ℕ} {design : PipelineStudyDesign D}
    (cohorts : DemeBinaryRiskCohorts design) : PipelineQuantity D → Option ℝ := by
  classical
  exact fun quantity ↦ match quantity with
  | .observedRiskR2 (some deme) =>
      if domain : (cohorts.atDeme deme).R2Domain then
        some ((cohorts.atDeme deme).observedRiskR2 domain) else none
  | .observedRiskR2 none =>
      if domain : cohorts.pooled.R2Domain then
        some (cohorts.pooled.observedRiskR2 domain) else none
  | .withinDemeAUC deme =>
      if domain : (cohorts.atDeme deme).AUCDomain then
        some ((cohorts.atDeme deme).auc domain) else none
  | .pooledAUC =>
      if domain : cohorts.pooled.AUCDomain then some (cohorts.pooled.auc domain) else none
  | .calibrationSlope (some deme) =>
      if domain : (cohorts.atDeme deme).LogisticCalibrationDomain then
        some ((cohorts.atDeme deme).calibrationSlope domain) else none
  | .calibrationSlope none =>
      if domain : cohorts.pooled.LogisticCalibrationDomain then
        some (cohorts.pooled.calibrationSlope domain) else none
  | .calibrationInTheLarge (some deme) =>
      if domain : (cohorts.atDeme deme).CITLDomain then
        some ((cohorts.atDeme deme).calibrationInTheLarge domain) else none
  | .calibrationInTheLarge none =>
      if domain : cohorts.pooled.CITLDomain then
        some (cohorts.pooled.calibrationInTheLarge domain) else none
  | .brierScore (some deme) => some (cohorts.atDeme deme).brier
  | .brierScore none => some cohorts.pooled.brier
  | .scoreVariance (some deme) => some (cohorts.atDeme deme).scoreVariance
  | .scoreVariance none => some cohorts.pooled.scoreVariance
  | _ => none

/-! ### Exact finite-cohort outcome marginalization -/

/-- Scores, model predictions, and true Bernoulli risks on the visible cohort layout before
the binary outcomes are drawn.  This is the finite object on which cohort-size effects must
be evaluated: changing `design.cohortSize` changes both the configuration space and every
definedness event, rather than merely shifting an asymptotic clock. -/
structure DemeRiskPredictionPanel {D : ℕ} (design : PipelineStudyDesign D) where
  score : ∀ deme, Fin (design.cohortSize deme) → ℝ
  predictedRisk : ∀ deme, Fin (design.cohortSize deme) → ℝ
  predictedRisk_pos : ∀ deme individual, 0 < predictedRisk deme individual
  predictedRisk_lt_one : ∀ deme individual, predictedRisk deme individual < 1
  outcomeProbability : ∀ deme, Fin (design.cohortSize deme) → ℝ
  outcomeProbability_nonneg : ∀ deme individual, 0 ≤ outcomeProbability deme individual
  outcomeProbability_le_one : ∀ deme individual, outcomeProbability deme individual ≤ 1

/-- A single binary outcome assignment on the concatenated visible cohort. -/
abbrev DemeOutcomeConfiguration {D : ℕ} (design : PipelineStudyDesign D) :=
  (Σ deme, Fin (design.cohortSize deme)) → Bool

/-- Exact product-Bernoulli probability of one finite outcome configuration. -/
noncomputable def DemeRiskPredictionPanel.outcomeWeight
    {D : ℕ} {design : PipelineStudyDesign D} (panel : DemeRiskPredictionPanel design)
    (outcome : DemeOutcomeConfiguration design) : ℝ :=
  ∏ individual, if outcome individual then
    panel.outcomeProbability individual.1 individual.2
  else 1 - panel.outcomeProbability individual.1 individual.2

/-- Every configuration weight is nonnegative. -/
theorem DemeRiskPredictionPanel.outcomeWeight_nonneg
    {D : ℕ} {design : PipelineStudyDesign D} (panel : DemeRiskPredictionPanel design)
    (outcome : DemeOutcomeConfiguration design) : 0 ≤ panel.outcomeWeight outcome := by
  apply Finset.prod_nonneg
  intro individual _
  split
  · exact panel.outcomeProbability_nonneg individual.1 individual.2
  · linarith [panel.outcomeProbability_le_one individual.1 individual.2]

/-- The finite Bernoulli law is normalized exactly.  This is the product-of-sums identity,
not a Monte Carlo approximation. -/
theorem DemeRiskPredictionPanel.outcomeWeight_sum_one
    {D : ℕ} {design : PipelineStudyDesign D} (panel : DemeRiskPredictionPanel design) :
    ∑ outcome : DemeOutcomeConfiguration design, panel.outcomeWeight outcome = 1 := by
  unfold DemeRiskPredictionPanel.outcomeWeight DemeOutcomeConfiguration
  calc
    (∑ outcome : (Σ deme, Fin (design.cohortSize deme)) → Bool,
        ∏ individual : Σ deme, Fin (design.cohortSize deme),
          if outcome individual then
            panel.outcomeProbability individual.1 individual.2
          else 1 - panel.outcomeProbability individual.1 individual.2) =
      ∏ individual : Σ deme, Fin (design.cohortSize deme), ∑ outcome : Bool,
        if outcome then panel.outcomeProbability individual.1 individual.2
        else 1 - panel.outcomeProbability individual.1 individual.2 := by
          simpa using (Fintype.prod_sum
            (fun (individual : Σ deme, Fin (design.cohortSize deme)) (outcome : Bool) ↦
            if outcome then panel.outcomeProbability individual.1 individual.2
            else 1 - panel.outcomeProbability individual.1 individual.2)).symm
    _ = 1 := by simp

/-- Materialize the exact empirical evaluator input for one outcome configuration. -/
def DemeRiskPredictionPanel.withOutcome
    {D : ℕ} {design : PipelineStudyDesign D} (panel : DemeRiskPredictionPanel design)
    (outcome : DemeOutcomeConfiguration design) : DemeBinaryRiskCohorts design where
  outcome := fun deme individual ↦ outcome ⟨deme, individual⟩
  score := panel.score
  predictedRisk := panel.predictedRisk
  predictedRisk_pos := panel.predictedRisk_pos
  predictedRisk_lt_one := panel.predictedRisk_lt_one
  pooledCard_pos := by
    have hnonempty : Nonempty (Σ deme, Fin (design.cohortSize deme)) :=
      ⟨⟨design.gwasDeme, ⟨0, design.cohortSize_pos design.gwasDeme⟩⟩⟩
    exact Fintype.card_pos_iff.mpr hnonempty

/-- Exact probability that the finite pipeline defines a requested coordinate.  For AUC,
`R²`, and calibration this sum automatically strengthens or weakens with cohort size because
the defining case/control and nonconstant-score events are evaluated on every configuration. -/
noncomputable def DemeRiskPredictionPanel.metricDefinedMass
    {D : ℕ} {design : PipelineStudyDesign D} (panel : DemeRiskPredictionPanel design)
    (coordinate : PipelineQuantity D) : ℝ :=
  ∑ outcome : DemeOutcomeConfiguration design,
    if ((panel.withOutcome outcome).evaluate coordinate).isSome then
      panel.outcomeWeight outcome else 0

/-- Definedness mass is a genuine nonnegative probability. -/
theorem DemeRiskPredictionPanel.metricDefinedMass_nonneg
    {D : ℕ} {design : PipelineStudyDesign D} (panel : DemeRiskPredictionPanel design)
    (coordinate : PipelineQuantity D) : 0 ≤ panel.metricDefinedMass coordinate := by
  unfold DemeRiskPredictionPanel.metricDefinedMass
  exact Finset.sum_nonneg fun outcome _ ↦ by
    split
    · exact panel.outcomeWeight_nonneg outcome
    · exact le_rfl

/-- Definedness mass cannot exceed the normalized outcome law. -/
theorem DemeRiskPredictionPanel.metricDefinedMass_le_one
    {D : ℕ} {design : PipelineStudyDesign D} (panel : DemeRiskPredictionPanel design)
    (coordinate : PipelineQuantity D) : panel.metricDefinedMass coordinate ≤ 1 := by
  rw [← panel.outcomeWeight_sum_one]
  unfold DemeRiskPredictionPanel.metricDefinedMass
  apply Finset.sum_le_sum
  intro outcome _
  split
  · exact le_rfl
  · exact panel.outcomeWeight_nonneg outcome

/-- Exact unnormalized first moment of a requested finite-cohort metric. -/
noncomputable def DemeRiskPredictionPanel.weightedMetric
    {D : ℕ} {design : PipelineStudyDesign D} (panel : DemeRiskPredictionPanel design)
    (coordinate : PipelineQuantity D) : ℝ :=
  ∑ outcome : DemeOutcomeConfiguration design,
    panel.outcomeWeight outcome *
      ((panel.withOutcome outcome).evaluate coordinate).getD 0

/-- Exact conditional finite-cohort metric after binary outcomes are marginalized.  This is
the finite sum targeted by a skip-undefined simulation average. -/
noncomputable def DemeRiskPredictionPanel.expectedMetric
    {D : ℕ} {design : PipelineStudyDesign D} (panel : DemeRiskPredictionPanel design)
    (coordinate : PipelineQuantity D) : Option ℝ :=
  let mass := panel.metricDefinedMass coordinate
  if mass = 0 then none else some (panel.weightedMetric coordinate / mass)

/-- All exact finite-cohort coordinates as one partial report. -/
noncomputable def DemeRiskPredictionPanel.expectedOutput
    {D : ℕ} {design : PipelineStudyDesign D} (panel : DemeRiskPredictionPanel design) :
    PipelineOutput D :=
  panel.expectedMetric

/-- Build the pre-outcome panel from one selected-score draw, an explicit phenotype-baseline
rule, and a prediction rule on that same visible cohort.  The true Bernoulli risks use the
total-liability panel and its derived global prevalence root; neither phenotype choice nor
recalibration is silently defaulted by the metric layer. -/
noncomputable def RealizedPTGWASDraw.toRiskPredictionPanel
    {D : ℕ} {input : VisiblePipelineInput D} (draw : RealizedPTGWASDraw input)
    (phenotypeBaseline : PhenotypeBaseline input)
    (predictedRisk : ∀ deme, Fin (input.studyDesign.cohortSize deme) → ℝ)
    (predictedRisk_pos : ∀ deme individual, 0 < predictedRisk deme individual)
    (predictedRisk_lt_one : ∀ deme individual, predictedRisk deme individual < 1) :
    DemeRiskPredictionPanel input.studyDesign where
  score := draw.winningScoreValue
  predictedRisk := predictedRisk
  predictedRisk_pos := predictedRisk_pos
  predictedRisk_lt_one := predictedRisk_lt_one
  outcomeProbability := (draw.phenotypeLiabilityPanel phenotypeBaseline).risk
  outcomeProbability_nonneg := fun deme individual ↦
    ((draw.phenotypeLiabilityPanel phenotypeBaseline).risk_mem_unitInterval
      deme individual).1.le
  outcomeProbability_le_one := fun deme individual ↦
    ((draw.phenotypeLiabilityPanel phenotypeBaseline).risk_mem_unitInterval
      deme individual).2.le

/-- A variable-marker score kernel extended by one named executable phenotype rung and one
prediction rule.  The only phenotype inputs left open are the affine and random per-deme
baseline realizations: phenoB's zero baseline and phenoC's draw-dependent within-deme
centering are derived by `phenotypeBaselineForRung`.  `predictedRiskAt` remains the
method-specific construction obligation.  All fields may share the same sample, so their
dependence is not discarded. -/
structure PredictionPipelineKernel (Sample : Type*) [MeasurableSpace Sample] (D : ℕ) where
  scoreKernel : VariableMarkerPTGWASKernel Sample D
  phenotypeRung : PhenotypeRung
  affineBaselineAt : ∀ (_ : VisiblePipelineInput D) (_ : Sample), Fin D → ℝ
  randomBaselineAt : ∀ (_ : VisiblePipelineInput D) (_ : Sample), Fin D → ℝ
  predictedRiskAt : ∀ (input : VisiblePipelineInput D) (_ : Sample) (deme : Fin D),
    Fin (input.studyDesign.cohortSize deme) → ℝ
  predictedRisk_pos : ∀ (input : VisiblePipelineInput D) (sample : Sample)
    (deme : Fin D) (individual : Fin (input.studyDesign.cohortSize deme)),
    0 < predictedRiskAt input sample deme individual
  predictedRisk_lt_one : ∀ (input : VisiblePipelineInput D) (sample : Sample)
    (deme : Fin D) (individual : Fin (input.studyDesign.cohortSize deme)),
    predictedRiskAt input sample deme individual < 1

/-- The exact pre-outcome panel induced by one non-outcome pipeline draw. -/
noncomputable def PredictionPipelineKernel.panelAt
    {Sample : Type*} [MeasurableSpace Sample] {D : ℕ}
    (kernel : PredictionPipelineKernel Sample D) (input : VisiblePipelineInput D)
    (sample : Sample) : Option (DemeRiskPredictionPanel input.studyDesign) :=
  (kernel.scoreKernel.realizedAt input sample).map fun draw ↦
    draw.toRiskPredictionPanel
      (draw.phenotypeBaselineForRung kernel.phenotypeRung
        (kernel.affineBaselineAt input sample) (kernel.randomBaselineAt input sample))
      (kernel.predictedRiskAt input sample)
      (kernel.predictedRisk_pos input sample)
      (kernel.predictedRisk_lt_one input sample)

/-- One sample's requested finite metric, with genome/GWAS construction failure and metric
undefinedness represented by the same outer partial-value convention. -/
noncomputable def PredictionPipelineKernel.expectedMetricAt
    {Sample : Type*} [MeasurableSpace Sample] {D : ℕ}
    (kernel : PredictionPipelineKernel Sample D) (input : VisiblePipelineInput D)
    (sample : Sample) (coordinate : PipelineQuantity D) : Option ℝ :=
  (kernel.panelAt input sample).bind fun panel ↦ panel.expectedMetric coordinate

/-- Exact input-indexed law of the remaining genome, GWAS, and prediction randomness after
finite binary outcomes have already been summed analytically.  The inner finite sum changes
with cohort size; the outer integral handles continuous simulator/GWAS draws. -/
structure FinitePipelineKernel (Sample : Type*) [MeasurableSpace Sample] (D : ℕ) where
  predictionKernel : PredictionPipelineKernel Sample D
  metricDefined_measurable : ∀ input coordinate,
    MeasurableSet {sample |
      (predictionKernel.expectedMetricAt input sample coordinate).isSome = true}
  definedMetric_integrable : ∀ input coordinate,
    Integrable (fun sample ↦
      if (predictionKernel.expectedMetricAt input sample coordinate).isSome = true then
        (predictionKernel.expectedMetricAt input sample coordinate).getD 0 else 0)
      (predictionKernel.scoreKernel.drawLaw input)

/-- Every fully constructed finite pipeline kernel induces the generic partial semantics.
Undefined AUC/calibration/`R²` draws remain outside the conditional mean rather than being
replaced by a sentinel. -/
noncomputable def FinitePipelineKernel.toPartialSemantics
    {Sample : Type*} [MeasurableSpace Sample] {D : ℕ}
    (kernel : FinitePipelineKernel Sample D) : PartialPipelineRandomSemantics D Sample where
  drawLaw := kernel.predictionKernel.scoreKernel.drawLaw
  drawLaw_probability := kernel.predictionKernel.scoreKernel.drawLaw_probability
  defined := fun input sample coordinate ↦
    (kernel.predictionKernel.expectedMetricAt input sample coordinate).isSome
  defined_measurable := kernel.metricDefined_measurable
  realizedValue := fun input sample coordinate ↦
    (kernel.predictionKernel.expectedMetricAt input sample coordinate).getD 0
  definedValue_integrable := kernel.definedMetric_integrable

/-- Once the actual kernel is constructed, all finite metric draws integrate to an exact
visible-input partial readout.  The theorem is composition, not a construction of the kernel. -/
theorem FinitePipelineKernel.hasExactExpectedReadout
    {Sample : Type*} [MeasurableSpace Sample] {D : ℕ}
    (kernel : FinitePipelineKernel Sample D) :
    HasExactPipelineReadout kernel.toPartialSemantics.expectedCompletionLaw :=
  kernel.toPartialSemantics.hasExactExpectedReadout

/-- The pooled formula exposes its diagonal and off-diagonal pieces exactly. -/
theorem DemeMixture.pooledAUC_diagonal_offDiagonal {D : ℕ} (mix : DemeMixture D) :
    mix.pooledAUC =
      (∑ i, ∑ j, if i = j then
        mix.caseWeight i * mix.controlWeight j *
          crossDemeCaseControlAUCOn (mix.law i) (mix.law j)
            (mix.discriminationDomain i) (mix.discriminationDomain j) else 0) +
      (∑ i, ∑ j, if i = j then 0 else
        mix.caseWeight i * mix.controlWeight j *
          crossDemeCaseControlAUCOn (mix.law i) (mix.law j)
            (mix.discriminationDomain i) (mix.discriminationDomain j)) := by
  classical
  unfold DemeMixture.pooledAUC
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  by_cases h : i = j <;> simp [h]

/-! ## E3. Harrell C under an administrative horizon -/

/-- Shifting the score origin by `shift` and scaling the baseline hazard by the reciprocal
hazard multiplier leaves every individual hazard unchanged. -/
theorem proportionalHazard_score_origin_invariant
    (baseline logHazardRatio score shift : ℝ) :
    baseline * Real.exp (-logHazardRatio * shift) *
        Real.exp (logHazardRatio * (score + shift)) =
      baseline * Real.exp (logHazardRatio * score) := by
  rw [mul_assoc, ← Real.exp_add]
  congr 1
  ring

/-- The same origin shift preserves every pairwise prognostic-index contrast. -/
theorem prognosticIndex_difference_shift_invariant
    (logHazardRatio score1 score2 shift : ℝ) :
    logHazardRatio * (score1 + shift) - logHazardRatio * (score2 + shift) =
      logHazardRatio * score1 - logHazardRatio * score2 := by
  ring

/-- A proportional-hazards generator with an arbitrary baseline hazard and administrative
horizon.  The cumulative-hazard identity is carried by the type; constant, piecewise,
spline, and generator-native baselines are instances of this same law. -/
structure AdministrativePHGenerator where
  baselineHazard : ℝ → ℝ
  baselineCumulativeHazard : ℝ → ℝ
  logHazardRatio : ℝ
  horizon : ℝ
  baselineHazard_nonneg : ∀ t, 0 ≤ baselineHazard t
  horizon_nonneg : 0 ≤ horizon
  cumulative_zero : baselineCumulativeHazard 0 = 0
  cumulative_spec : ∀ t, 0 ≤ t →
    baselineCumulativeHazard t = ∫ u in (0 : ℝ)..t, baselineHazard u

/-- Individual event hazard at a time and score. -/
noncomputable def AdministrativePHGenerator.eventHazard
    (g : AdministrativePHGenerator) (time score : ℝ) : ℝ :=
  g.baselineHazard time * Real.exp (g.logHazardRatio * score)

/-- Individual cumulative hazard. -/
noncomputable def AdministrativePHGenerator.eventCumulativeHazard
    (g : AdministrativePHGenerator) (time score : ℝ) : ℝ :=
  g.baselineCumulativeHazard time * Real.exp (g.logHazardRatio * score)

/-- Individual survival probability through a time. -/
noncomputable def AdministrativePHGenerator.eventSurvival
    (g : AdministrativePHGenerator) (time score : ℝ) : ℝ :=
  Real.exp (-g.eventCumulativeHazard time score)

/-- Exact probability that individual 1 fails before individual 2 and before the
administrative horizon, conditional on their scores. -/
noncomputable def AdministrativePHGenerator.firstObserved
    (g : AdministrativePHGenerator) (score1 score2 : ℝ) : ℝ :=
  ∫ time in (0 : ℝ)..g.horizon,
    g.eventHazard time score1 * g.eventSurvival time score1 *
      g.eventSurvival time score2

/-- A Gaussian marginal score law for the survival chart. -/
structure SurvivalScoreLaw where
  mean : ℝ
  variance : ℝ
  variance_pos : 0 < variance

/-- Gaussian score density in the raw score coordinate. -/
noncomputable def SurvivalScoreLaw.density (law : SurvivalScoreLaw) (score : ℝ) : ℝ :=
  Real.exp (-((score - law.mean) ^ 2) / (2 * law.variance)) /
    Real.sqrt (2 * Real.pi * law.variance)

/-- Comparable-pair mass under administrative censoring. -/
noncomputable def administrativeComparableMass
    (g : AdministrativePHGenerator) (law : SurvivalScoreLaw) : ℝ :=
  ∫ s1, ∫ s2,
    (g.firstObserved s1 s2 + g.firstObserved s2 s1) *
      law.density s1 * law.density s2

/-- The prognostic index whose order Harrell C evaluates. -/
noncomputable def AdministrativePHGenerator.prognosticIndex
    (g : AdministrativePHGenerator) (score : ℝ) : ℝ :=
  g.logHazardRatio * score

/-- Concordant comparable-pair mass.  Ties receive one half, matching population AUC and
Harrell's convention. -/
noncomputable def administrativeConcordantMass
    (g : AdministrativePHGenerator) (law : SurvivalScoreLaw) : ℝ :=
  ∫ s1, ∫ s2,
    ((if g.prognosticIndex s1 > g.prognosticIndex s2 then g.firstObserved s1 s2 else
       if g.prognosticIndex s1 = g.prognosticIndex s2 then
         (1 / 2) * g.firstObserved s1 s2 else 0) +
     (if g.prognosticIndex s2 > g.prognosticIndex s1 then g.firstObserved s2 s1 else
       if g.prognosticIndex s2 = g.prognosticIndex s1 then
         (1 / 2) * g.firstObserved s2 s1 else 0)) *
      law.density s1 * law.density s2

/-- Domain on which Harrell C has at least one comparable pair in population measure. -/
structure AdministrativeHarrellDomain
    (g : AdministrativePHGenerator) (law : SurvivalScoreLaw) : Prop where
  comparableMass_pos : 0 < administrativeComparableMass g law

/-- E3: population Harrell C for an administrative-horizon construction. -/
noncomputable def administrativeHarrellC
    (g : AdministrativePHGenerator) (law : SurvivalScoreLaw)
    (_ : AdministrativeHarrellDomain g law) : ℝ :=
  administrativeConcordantMass g law / administrativeComparableMass g law

/-- At horizon zero there are no comparable event pairs; the zero returned by the ratio is
the named empty-comparison branch, not a chance-level C-index. -/
theorem AdministrativePHGenerator.firstObserved_zero_horizon
    (g : AdministrativePHGenerator) (s1 s2 : ℝ) (h : g.horizon = 0) :
    g.firstObserved s1 s2 = 0 := by
  simp [AdministrativePHGenerator.firstObserved, h]

/-- A zero administrative horizon admits no Harrell-C domain: comparable mass is exactly
zero, so the metric remains undefined rather than being filled with chance. -/
theorem noAdministrativeHarrellDomain_at_zero_horizon
    (g : AdministrativePHGenerator) (law : SurvivalScoreLaw) (h : g.horizon = 0) :
    ¬ AdministrativeHarrellDomain g law := by
  intro domain
  have hmass : administrativeComparableMass g law = 0 := by
    unfold administrativeComparableMass
    simp [AdministrativePHGenerator.firstObserved, h]
  linarith [domain.comparableMass_pos]

/-- First-observed probabilities depend only on the two individual hazard and survival
curves.  This pins the chart independently of how a generator represents its baseline. -/
theorem firstObserved_ext (g₁ g₂ : AdministrativePHGenerator) (s1 s2 : ℝ)
    (hhazard : ∀ t, g₁.eventHazard t s1 = g₂.eventHazard t s1)
    (hsurv1 : ∀ t, g₁.eventSurvival t s1 = g₂.eventSurvival t s1)
    (hsurv2 : ∀ t, g₁.eventSurvival t s2 = g₂.eventSurvival t s2)
    (hhorizon : g₁.horizon = g₂.horizon) :
    g₁.firstObserved s1 s2 = g₂.firstObserved s1 s2 := by
  unfold AdministrativePHGenerator.firstObserved
  rw [hhorizon]
  apply intervalIntegral.integral_congr
  intro t _
  simp only [hhazard, hsurv1, hsurv2]

/-! ## Inhabitation

A theorem quantified over an uninhabited structure is true and empty, so the survival classes
carry exhibited inhabitants.  The values sit off the boundaries their own hypotheses exclude:
a zero log hazard ratio would make the hazard score-independent and every discrimination
statement below it trivially true, which inhabits the class while testing nothing. -/

/-- Inhabitation for the Gaussian marginal score law, standardized. -/
noncomputable def SurvivalScoreLaw.witness : SurvivalScoreLaw where
  mean := 0
  variance := 1
  variance_pos := by norm_num

/-- Inhabitation for the administrative proportional-hazards generator, at the EXPONENTIAL
baseline: constant unit hazard, whose cumulative hazard is the identity.  This is the one
baseline for which `cumulative_spec` is an integral the corpus can discharge outright rather
than assume, so the witness proves the cumulative-hazard identity instead of carrying it. -/
noncomputable def AdministrativePHGenerator.witness : AdministrativePHGenerator where
  baselineHazard := fun _ ↦ 1
  baselineCumulativeHazard := fun t ↦ t
  logHazardRatio := 1 / 2
  horizon := 1
  baselineHazard_nonneg := by intro t; norm_num
  horizon_nonneg := by norm_num
  cumulative_zero := rfl
  cumulative_spec := by intro t _; simp

end Descent.Portability
