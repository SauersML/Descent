/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.EndToEndCalibrationLaw
import Descent.Portability.PortabilityMasterTheorem

assert_below Descent.Decision Descent.Program

/-!
# The exact accuracy calculator: demography, training, architecture and environment

A demography, a training procedure, a phenotype architecture and an environment determine the
deployed accuracy of a polygenic score in every deme.  This module joins the history kernels to
`PortabilityMasterTheorem` through the expected second moments of each deme.

The compilation.  The master theorem evaluates every deployed metric of a population from its tag
covariance `Σ_X`, tag–causal covariance `K`, causal covariance `Σ_C`, tag and causal means, effects
`β`, and the variance, mean and covariances of the residual that carries environment,
gene–environment interaction and non-additivity (its §2).  `DemeMoments` and `DemeArchitecture` hold
these inputs.  `DemeMoments.r2`, `calibrationSlope`, `calibrationIntercept` and `deployedMse` are
the master formulas on them, through the master statistic (`r2OfStatistic`, `slopeOfStatistic`).
Every master-theorem population has these metrics at its own moments
(`DemeMoments.metrics_ofPopulation`).

The demography.  Under a history kernel the expected within-population moments of a deme
(`expectedDemeMoments`) are the deployment moments of `U · H_n(x₀)` for every budget `n ≥ 2`, with
written-out coefficient vectors (`momentDemeMoments`, `expectedDemeMoments_historyEventKernel`,
`expectedDemeMoments_rateHistoryKernel`).  Two histories that agree on those propagated moments
give every deme the same moments (`expectedDemeMoments_eq_of_moments_eq`), hence the same deployed
accuracy under every training procedure, architecture and environment.

Training.  `ridgeWeights` is `(Σ + λ I)⁻¹ c` with Mathlib's matrix inverse, the adjugate over the
determinant, so it is a rational function of the moments.  `trainedWeights` trains in one deme,
with penalty zero being population least squares.  `pooledTrainedWeights` trains on the
share-weighted within-deme moments of several demes, and reduces to one deme at a unit share
(`pooledTrainedWeights_single`).  Any other weights, pruning and thresholding included, enter the
metrics directly.  In its own deme a ridge score has `Cov(S, Y) = Var S + λ ‖w‖²`
(`predictiveCovariance_trainedWeights`), so its calibration slope is `1 + λ ‖w‖² / Var S`
(`calibrationSlope_trainedWeights`).  The slope is at least one for a nonnegative penalty
(`one_le_calibrationSlope_trainedWeights`) and exactly one for least squares
(`calibrationSlope_trainedWeights_zero`), where `R² = Var S / Var Y` (`r2_trainedWeights_zero`).

The output.  Weights trained in a source deme and deployed in a target deme have a deployed `R²`,
calibration slope, intercept and mean squared error (`DemeMoments.report`) equal to the compiled
metrics of the moment matrices of `U · H₂(x₀)` (`transferReport_historyEventKernel`), and histories
with equal propagated moments give equal reports (`transferReport_eq_of_moments_eq`).

How accuracy changes with each input.  For one weight vector, the score–outcome covariance of a
target deme minus that of a source deme is a demographic tagging channel `wᵀ(K_t - K_s)β_s`, an
architecture channel `wᵀK_t(β_t - β_s)` and an environment channel `wᵀ(c_t - c_s)`
(`predictiveCovariance_sub_channels`).  The score variance moves only through the demographic
channel `wᵀ(Σ_t - Σ_s)w` (`scoreVariance_sub_channel`), and the outcome variance splits into
demographic, architecture and environment channels (`outcomeVariance_sub_channels`).  These are
the transport channels of the master theorem's §3, read on the calculator.

Scope.  The metrics here are the metrics of the expected second moments: the ratio-of-expectations
query of NOTE2 §6.2, not the expectation of each population's metric, which is not a rational
function of finitely many moments.  The environment enters through its moments per deme, supplied
rather than generated, and the tag and causal codings are functions of one sampled haplotype.
`pooledTrainedWeights` uses within-deme moments, as when deme membership is adjusted for; an
unadjusted pooled cohort adds the between-deme covariance of the means.  Training is at the
population level.  Finite-sample GWAS training would need the sampling law of the estimated
moments, with their estimation noise and selection effects, which this module does not state.

## Empirical status

None.  The bodies here are matrix algebra on supplied moments and integrals of polynomials against
Markov kernels, so no measurement can bear on them.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.EndToEndDeploymentLaw

open MeasureTheory ProbabilityTheory MvPolynomial Descent.Coalescent PartialHaplotypeCarrier
  PartialHaplotypeDualGenerator PartialHaplotypeDualSemigroup NeutralFellerGenerator
  NeutralPolynomialSemigroup PartialHaplotypeMicroscopicApproximation PartialHaplotypePulseKernel
  NeutralPulseHistoryKernel NeutralRateHistoryRealization NeutralRateHistoryKernel
  EndToEndPortabilityLaw EndToEndCalibrationLaw
open Descent.Foundations (dot)
open scoped Matrix NNReal

noncomputable section

/-! ## Deployment moments and their metrics -/

/-- **The deployment moments of one deme**: the tag covariance `Σ_X`, the tag–causal covariance
`K`, the causal covariance `Σ_C`, and the tag and causal means. -/
structure DemeMoments (J L : Type*) where
  /-- The tag covariance `Σ_X`. -/
  tagCovariance : Matrix J J ℝ
  /-- The tag–causal covariance `K`. -/
  tagCausalCovariance : Matrix J L ℝ
  /-- The causal covariance `Σ_C`. -/
  causalCovariance : Matrix L L ℝ
  /-- The tag means. -/
  tagMean : J → ℝ
  /-- The causal means. -/
  causalMean : L → ℝ

/-- **A phenotype architecture and environment for one deme**: the effects `β` of the causal
codings, and the variance, mean and covariances with the tag and causal codings of the residual,
which carries environment, gene–environment interaction and non-additive effects. -/
structure DemeArchitecture (J L : Type*) where
  /-- The effects `β` of the causal codings. -/
  effects : L → ℝ
  /-- The residual variance. -/
  residualVariance : ℝ
  /-- The residual mean. -/
  residualMean : ℝ
  /-- The covariances `c_X` of the tag codings with the residual. -/
  residualTagCovariance : J → ℝ
  /-- The covariances `c_C` of the causal codings with the residual. -/
  residualCausalCovariance : L → ℝ

namespace DemeMoments

variable {J L : Type*} [Fintype J] [DecidableEq J] [Fintype L] [DecidableEq L]

/-- The tag–outcome covariance `K β + c_X`. -/
def tagOutcomeCovariance (m : DemeMoments J L) (a : DemeArchitecture J L) : J → ℝ :=
  m.tagCausalCovariance *ᵥ a.effects + a.residualTagCovariance

/-- The score variance `wᵀ Σ_X w`. -/
def scoreVariance (m : DemeMoments J L) (w : J → ℝ) : ℝ :=
  dot w (m.tagCovariance *ᵥ w)

/-- The predictive covariance `wᵀ K β + wᵀ c_X`. -/
def predictiveCovariance (m : DemeMoments J L) (a : DemeArchitecture J L) (w : J → ℝ) : ℝ :=
  dot w (m.tagCausalCovariance *ᵥ a.effects) + dot w a.residualTagCovariance

/-- The outcome variance `βᵀ Σ_C β + 2 βᵀ c_C + Var h`. -/
def outcomeVariance (m : DemeMoments J L) (a : DemeArchitecture J L) : ℝ :=
  dot a.effects (m.causalCovariance *ᵥ a.effects) + 2 * dot a.effects a.residualCausalCovariance
    + a.residualVariance

/-- The master theorem's metric statistic `(Var S, Cov(S, Y), Var Y)`. -/
def statistic (m : DemeMoments J L) (a : DemeArchitecture J L) (w : J → ℝ) : ℝ × ℝ × ℝ :=
  (m.scoreVariance w, m.predictiveCovariance a w, m.outcomeVariance a)

/-- The deployed `R²`. -/
def r2 (m : DemeMoments J L) (a : DemeArchitecture J L) (w : J → ℝ) : ℝ :=
  r2OfStatistic (m.statistic a w)

/-- The deployed calibration slope. -/
def calibrationSlope (m : DemeMoments J L) (a : DemeArchitecture J L) (w : J → ℝ) : ℝ :=
  slopeOfStatistic (m.statistic a w)

/-- The score mean `wᵀ μ_X`. -/
def scoreMean (m : DemeMoments J L) (w : J → ℝ) : ℝ :=
  dot w m.tagMean

/-- The outcome mean `βᵀ μ_C + E h`. -/
def outcomeMean (m : DemeMoments J L) (a : DemeArchitecture J L) : ℝ :=
  dot a.effects m.causalMean + a.residualMean

/-- The deployed calibration intercept `E Y - slope · E S`. -/
def calibrationIntercept (m : DemeMoments J L) (a : DemeArchitecture J L) (w : J → ℝ) : ℝ :=
  m.outcomeMean a - m.calibrationSlope a w * m.scoreMean w

/-- The deployed mean squared error `Var Y + Var S - 2 Cov(S, Y) + (E S - E Y)²`. -/
def deployedMse (m : DemeMoments J L) (a : DemeArchitecture J L) (w : J → ℝ) : ℝ :=
  m.outcomeVariance a + m.scoreVariance w - 2 * m.predictiveCovariance a w
    + (m.scoreMean w - m.outcomeMean a) ^ 2

/-- The deployment report: `R²`, calibration slope, calibration intercept and deployed mean squared
error. -/
def report (m : DemeMoments J L) (a : DemeArchitecture J L) (w : J → ℝ) : ℝ × ℝ × ℝ × ℝ :=
  (m.r2 a w, m.calibrationSlope a w, m.calibrationIntercept a w, m.deployedMse a w)

/-- The predictive covariance is the weights dotted with the tag–outcome covariance. -/
theorem predictiveCovariance_eq_dot (m : DemeMoments J L) (a : DemeArchitecture J L)
    (w : J → ℝ) : m.predictiveCovariance a w = dot w (m.tagOutcomeCovariance a) := by
  rw [predictiveCovariance, tagOutcomeCovariance, Foundations.dot_add_right]

/-- The deployment moments of a master-theorem population. -/
def ofPopulation {Ω : Type*} (P : DeploymentPopulation Ω J L) : DemeMoments J L where
  tagCovariance := P.sigmaX
  tagCausalCovariance := P.kappa
  causalCovariance := P.sigmaC
  tagMean j := P.E (fun ω ↦ P.X ω j)
  causalMean l := P.E (fun ω ↦ P.C ω l)

/-- The architecture and environment of a master-theorem population. -/
def architectureOfPopulation {Ω : Type*} (P : DeploymentPopulation Ω J L) :
    DemeArchitecture J L where
  effects := P.β
  residualVariance := Foundations.variance P.E P.h
  residualMean := P.E P.h
  residualTagCovariance := P.contextX
  residualCausalCovariance := P.contextC

/-- **The compiled metrics are the master theorem's metrics.**  For every master-theorem population
and weights, the deployed `R²`, calibration slope, calibration intercept and mean squared error are
the compiled metrics of the population's own deployment moments and architecture. -/
theorem metrics_ofPopulation {Ω : Type*} (P : DeploymentPopulation Ω J L) (w : J → ℝ) :
    P.r2 w = (ofPopulation P).r2 (architectureOfPopulation P) w
      ∧ P.calibrationSlope w = (ofPopulation P).calibrationSlope (architectureOfPopulation P) w
      ∧ P.calibrationIntercept w
        = (ofPopulation P).calibrationIntercept (architectureOfPopulation P) w
      ∧ P.deployedMse w = (ofPopulation P).deployedMse (architectureOfPopulation P) w := by
  refine ⟨P.r2_eq w, P.calibrationSlope_eq w, P.calibrationIntercept_eq w, ?_⟩
  rw [P.deployedMse_eq w, P.eval_score_eq w, P.eval_phenotype_eq]
  rfl

/-! ## How accuracy changes with each input -/

/-- **The predictive covariance channels.**  For one weight vector, the predictive covariance of a
target deme minus that of a source deme is the demographic tagging channel `wᵀ(K_t - K_s)β_s`,
plus the architecture channel `wᵀK_t(β_t - β_s)`, plus the environment channel `wᵀ(c_t - c_s)`. -/
theorem predictiveCovariance_sub_channels (source target : DemeMoments J L)
    (sourceArch targetArch : DemeArchitecture J L) (w : J → ℝ) :
    target.predictiveCovariance targetArch w - source.predictiveCovariance sourceArch w
      = dot w ((target.tagCausalCovariance - source.tagCausalCovariance) *ᵥ sourceArch.effects)
        + dot w (target.tagCausalCovariance *ᵥ (targetArch.effects - sourceArch.effects))
        + dot w (targetArch.residualTagCovariance - sourceArch.residualTagCovariance) := by
  rw [predictiveCovariance, predictiveCovariance, Matrix.sub_mulVec, Matrix.mulVec_sub,
    Foundations.dot_sub_right', Foundations.dot_sub_right', Foundations.dot_sub_right']
  ring

/-- **The score variance channel.**  The score variance of one weight vector moves between demes
only through the demographic channel `wᵀ(Σ_t - Σ_s)w`. -/
theorem scoreVariance_sub_channel (source target : DemeMoments J L) (w : J → ℝ) :
    target.scoreVariance w - source.scoreVariance w
      = dot w ((target.tagCovariance - source.tagCovariance) *ᵥ w) := by
  rw [scoreVariance, scoreVariance, Matrix.sub_mulVec, Foundations.dot_sub_right']

/-- **The outcome variance channels.**  The outcome variance of a target deme minus that of a
source deme is the demographic channel `β_sᵀ(Σ_{C,t} - Σ_{C,s})β_s`, plus the architecture channel
`β_tᵀΣ_{C,t}β_t - β_sᵀΣ_{C,t}β_s`, plus the environment channel of the residual covariances and
variances. -/
theorem outcomeVariance_sub_channels (source target : DemeMoments J L)
    (sourceArch targetArch : DemeArchitecture J L) :
    target.outcomeVariance targetArch - source.outcomeVariance sourceArch
      = dot sourceArch.effects
          ((target.causalCovariance - source.causalCovariance) *ᵥ sourceArch.effects)
        + (dot targetArch.effects (target.causalCovariance *ᵥ targetArch.effects)
          - dot sourceArch.effects (target.causalCovariance *ᵥ sourceArch.effects))
        + (2 * dot targetArch.effects targetArch.residualCausalCovariance
          - 2 * dot sourceArch.effects sourceArch.residualCausalCovariance
          + (targetArch.residualVariance - sourceArch.residualVariance)) := by
  rw [outcomeVariance, outcomeVariance, Matrix.sub_mulVec, Foundations.dot_sub_right']
  ring

end DemeMoments

/-! ## Training procedures -/

section Training

variable {J L : Type*} [Fintype J] [DecidableEq J] [Fintype L] [DecidableEq L]

/-- **Ridge training**: the weights `(Σ + λ I)⁻¹ c` from a tag covariance `Σ`, a tag–outcome
covariance `c` and a penalty `λ`, with Mathlib's matrix inverse. -/
def ridgeWeights (covariance : Matrix J J ℝ) (target : J → ℝ) (penalty : ℝ) : J → ℝ :=
  (covariance + penalty • (1 : Matrix J J ℝ))⁻¹ *ᵥ target

/-- **The normal equations of ridge training**, where the penalised covariance is invertible. -/
theorem ridgeWeights_normal (covariance : Matrix J J ℝ) (target : J → ℝ) (penalty : ℝ)
    (hunit : IsUnit (covariance + penalty • (1 : Matrix J J ℝ)).det) :
    (covariance + penalty • (1 : Matrix J J ℝ)) *ᵥ ridgeWeights covariance target penalty
      = target := by
  rw [ridgeWeights, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv (h := hunit), Matrix.one_mulVec]

/-- **Ridge weights against their training covariance**: `wᵀ c = wᵀ Σ w + λ wᵀ w`. -/
theorem dot_ridgeWeights_target (covariance : Matrix J J ℝ) (target : J → ℝ) (penalty : ℝ)
    (hunit : IsUnit (covariance + penalty • (1 : Matrix J J ℝ)).det) :
    dot (ridgeWeights covariance target penalty) target
      = dot (ridgeWeights covariance target penalty)
          (covariance *ᵥ ridgeWeights covariance target penalty)
        + penalty * dot (ridgeWeights covariance target penalty)
          (ridgeWeights covariance target penalty) := by
  have hnormal := ridgeWeights_normal covariance target penalty hunit
  set w := ridgeWeights covariance target penalty
  calc dot w target = dot w ((covariance + penalty • (1 : Matrix J J ℝ)) *ᵥ w) := by
        rw [hnormal]
    _ = dot w (covariance *ᵥ w) + penalty * dot w w := by
        rw [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, Foundations.dot_add_right]
        congr 1
        simp only [dot, Descent.Core.innerSum, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ ↦ by ring

/-- **Training in one deme**: ridge weights from the deme's tag covariance and tag–outcome
covariance.  Penalty zero is population least squares. -/
def trainedWeights (m : DemeMoments J L) (a : DemeArchitecture J L) (penalty : ℝ) : J → ℝ :=
  ridgeWeights m.tagCovariance (m.tagOutcomeCovariance a) penalty

/-- **Pooled training over demes**: ridge weights from the share-weighted within-deme tag
covariances and tag–outcome covariances of several demes. -/
def pooledTrainedWeights {Deme : Type*} [Fintype Deme] (share : Deme → ℝ)
    (m : Deme → DemeMoments J L) (a : Deme → DemeArchitecture J L) (penalty : ℝ) : J → ℝ :=
  ridgeWeights (∑ j, share j • (m j).tagCovariance)
    (∑ j, share j • (m j).tagOutcomeCovariance (a j)) penalty

/-- A unit share at one deme picks that deme's term out of a share-weighted sum. -/
theorem sum_single_smul {Deme V : Type*} [Fintype Deme] [DecidableEq Deme] [AddCommMonoid V]
    [Module ℝ V] (training : Deme) (f : Deme → V) :
    ∑ j, Pi.single training (1 : ℝ) j • f j = f training := by
  have hzero : ∀ j ∈ Finset.univ, j ≠ training → Pi.single training (1 : ℝ) j • f j = 0 :=
    fun j _ hj ↦ by rw [Pi.single_eq_of_ne hj, zero_smul]
  rw [Finset.sum_eq_single training hzero (fun hmem ↦ absurd (Finset.mem_univ training) hmem),
    Pi.single_eq_same, one_smul]

/-- **Pooled training with a unit share is training in that deme.** -/
theorem pooledTrainedWeights_single {Deme : Type*} [Fintype Deme] [DecidableEq Deme]
    (training : Deme) (m : Deme → DemeMoments J L) (a : Deme → DemeArchitecture J L)
    (penalty : ℝ) :
    pooledTrainedWeights (Pi.single training 1) m a penalty
      = trainedWeights (m training) (a training) penalty := by
  rw [pooledTrainedWeights, sum_single_smul, sum_single_smul]
  rfl

/-- **Ridge training in its own deme**: the score's covariance with the training outcome exceeds its
variance by the penalty times the squared weight norm. -/
theorem predictiveCovariance_trainedWeights (m : DemeMoments J L) (a : DemeArchitecture J L)
    (penalty : ℝ) (hunit : IsUnit (m.tagCovariance + penalty • (1 : Matrix J J ℝ)).det) :
    m.predictiveCovariance a (trainedWeights m a penalty)
      = m.scoreVariance (trainedWeights m a penalty)
        + penalty * dot (trainedWeights m a penalty) (trainedWeights m a penalty) := by
  rw [DemeMoments.predictiveCovariance_eq_dot, DemeMoments.scoreVariance]
  exact dot_ridgeWeights_target m.tagCovariance (m.tagOutcomeCovariance a) penalty hunit

/-- **The calibration slope of ridge training in its own deme** is `1 + λ ‖w‖² / Var S`. -/
theorem calibrationSlope_trainedWeights (m : DemeMoments J L) (a : DemeArchitecture J L)
    (penalty : ℝ) (hunit : IsUnit (m.tagCovariance + penalty • (1 : Matrix J J ℝ)).det)
    (hvariance : m.scoreVariance (trainedWeights m a penalty) ≠ 0) :
    m.calibrationSlope a (trainedWeights m a penalty)
      = 1 + penalty * dot (trainedWeights m a penalty) (trainedWeights m a penalty)
        / m.scoreVariance (trainedWeights m a penalty) := by
  show m.predictiveCovariance a (trainedWeights m a penalty)
      / m.scoreVariance (trainedWeights m a penalty) = _
  rw [predictiveCovariance_trainedWeights m a penalty hunit, add_div, div_self hvariance]

/-- **Ridge training is over-calibrated in its own deme**: for a nonnegative penalty the
calibration slope is at least one. -/
theorem one_le_calibrationSlope_trainedWeights (m : DemeMoments J L) (a : DemeArchitecture J L)
    (penalty : ℝ) (hpenalty : 0 ≤ penalty)
    (hunit : IsUnit (m.tagCovariance + penalty • (1 : Matrix J J ℝ)).det)
    (hvariance : 0 < m.scoreVariance (trainedWeights m a penalty)) :
    1 ≤ m.calibrationSlope a (trainedWeights m a penalty) := by
  rw [calibrationSlope_trainedWeights m a penalty hunit hvariance.ne']
  have hsquare : 0 ≤ dot (trainedWeights m a penalty) (trainedWeights m a penalty) :=
    Finset.sum_nonneg fun i _ ↦ mul_self_nonneg _
  have hratio := div_nonneg (mul_nonneg hpenalty hsquare) hvariance.le
  linarith

/-- **Least squares is calibrated in its own deme**: at penalty zero the calibration slope is
one. -/
theorem calibrationSlope_trainedWeights_zero (m : DemeMoments J L) (a : DemeArchitecture J L)
    (hunit : IsUnit m.tagCovariance.det)
    (hvariance : m.scoreVariance (trainedWeights m a 0) ≠ 0) :
    m.calibrationSlope a (trainedWeights m a 0) = 1 := by
  have hunitZero : IsUnit (m.tagCovariance + (0 : ℝ) • (1 : Matrix J J ℝ)).det := by
    rwa [zero_smul, add_zero]
  rw [calibrationSlope_trainedWeights m a 0 hunitZero hvariance, zero_mul, zero_div, add_zero]

/-- **The `R²` of least squares in its own deme** is the score's share of the outcome variance. -/
theorem r2_trainedWeights_zero (m : DemeMoments J L) (a : DemeArchitecture J L)
    (hunit : IsUnit m.tagCovariance.det)
    (hvariance : m.scoreVariance (trainedWeights m a 0) ≠ 0) :
    m.r2 a (trainedWeights m a 0)
      = m.scoreVariance (trainedWeights m a 0) / m.outcomeVariance a := by
  have hunitZero : IsUnit (m.tagCovariance + (0 : ℝ) • (1 : Matrix J J ℝ)).det := by
    rwa [zero_smul, add_zero]
  have hcovariance := predictiveCovariance_trainedWeights m a 0 hunitZero
  rw [zero_mul, add_zero] at hcovariance
  show m.predictiveCovariance a (trainedWeights m a 0) ^ 2
      / (m.scoreVariance (trainedWeights m a 0) * m.outcomeVariance a) = _
  rw [hcovariance, pow_two, mul_div_mul_left _ _ hvariance]

end Training

/-! ## Expected deployment moments along a history -/

section Moments

variable {Deme Locus : Type*} {Allele : Locus → Type*}
variable [Fintype Deme] [DecidableEq Deme] [Fintype Locus] [DecidableEq Locus]
  [∀ ℓ, Fintype (Allele ℓ)] [∀ ℓ, DecidableEq (Allele ℓ)]
variable {J L : Type*}

/-- **The expected deployment moments of a deme** under a kernel started at `x₀`: the expected
within-population covariances of the tag codings `X` and causal codings `C`, and their expected
means.  NOTE2 §6.2: the inputs of a ratio-of-expectations query. -/
def expectedDemeMoments
    (κ : Kernel (FrequencyState Deme Locus Allele) (FrequencyState Deme Locus Allele))
    (x0 : FrequencyState Deme Locus Allele) (deme : Deme)
    (X : FullHaplotype Locus Allele → J → ℝ) (C : FullHaplotype Locus Allele → L → ℝ) :
    DemeMoments J L where
  tagCovariance := Matrix.of fun i k ↦
    ∫ y, (stateLaw y deme).covariance (fun hap ↦ X hap i) (fun hap ↦ X hap k) ∂(κ x0)
  tagCausalCovariance := Matrix.of fun i l ↦
    ∫ y, (stateLaw y deme).covariance (fun hap ↦ X hap i) (fun hap ↦ C hap l) ∂(κ x0)
  causalCovariance := Matrix.of fun l l' ↦
    ∫ y, (stateLaw y deme).covariance (fun hap ↦ C hap l) (fun hap ↦ C hap l') ∂(κ x0)
  tagMean i := ∫ y, (stateLaw y deme).expectation (fun hap ↦ X hap i) ∂(κ x0)
  causalMean l := ∫ y, (stateLaw y deme).expectation (fun hap ↦ C hap l) ∂(κ x0)

/-- **The deployment moments of a budget-`n` moment vector**, with written-out coefficient
vectors: every entry is linear in the moment vector. -/
def momentDemeMoments (ℓ₀ : Locus) (n : ℕ) (deme : Deme) (X : FullHaplotype Locus Allele → J → ℝ)
    (C : FullHaplotype Locus Allele → L → ℝ)
    (v : BudgetConfiguration Deme Locus Allele (fun _ ↦ n) → ℝ) : DemeMoments J L where
  tagCovariance := Matrix.of fun i k ↦ budgetCoefficients ℓ₀ (fun _ ↦ n)
    (demeCovariancePolynomial deme (fun hap ↦ X hap i) (fun hap ↦ X hap k)) ⬝ᵥ v
  tagCausalCovariance := Matrix.of fun i l ↦ budgetCoefficients ℓ₀ (fun _ ↦ n)
    (demeCovariancePolynomial deme (fun hap ↦ X hap i) (fun hap ↦ C hap l)) ⬝ᵥ v
  causalCovariance := Matrix.of fun l l' ↦ budgetCoefficients ℓ₀ (fun _ ↦ n)
    (demeCovariancePolynomial deme (fun hap ↦ C hap l) (fun hap ↦ C hap l')) ⬝ᵥ v
  tagMean i := budgetCoefficients ℓ₀ (fun _ ↦ n) (demeMeanPolynomial deme fun hap ↦ X hap i) ⬝ᵥ v
  causalMean l :=
    budgetCoefficients ℓ₀ (fun _ ↦ n) (demeMeanPolynomial deme fun hap ↦ C hap l) ⬝ᵥ v

/-- **The expected deployment moments along a history of epochs, splits and pulses.**  For every
budget `n ≥ 2` they are the deployment moments of the chronological propagator applied to the
budget-`n` configuration moments of the initial state. -/
theorem expectedDemeMoments_historyEventKernel (ℓ₀ : Locus) (hap₀ : FullHaplotype Locus Allele)
    (events : List ((NeutralRates Deme Locus Allele × ℝ≥0) ⊕ PulseMatrix Deme)) {n : ℕ}
    (hn : 2 ≤ n) (x0 : FrequencyState Deme Locus Allele) (deme : Deme)
    (X : FullHaplotype Locus Allele → J → ℝ) (C : FullHaplotype Locus Allele → L → ℝ) :
    expectedDemeMoments (historyEventKernel ℓ₀ hap₀ events) x0 deme X C
      = momentDemeMoments ℓ₀ n deme X C
          (historyEventPropagator (fun _ ↦ n) events *ᵥ budgetMomentFeature (fun _ ↦ n) x0) := by
  simp only [expectedDemeMoments, momentDemeMoments,
    integral_covariance_historyEventKernel ℓ₀ hap₀ events hn,
    integral_expectation_historyEventKernel ℓ₀ hap₀ events (one_le_two.trans hn)]

/-- **The expected deployment moments along a rate history**, at every budget `n ≥ 2`. -/
theorem expectedDemeMoments_rateHistoryKernel {rates : ℝ → NeutralRates Deme Locus Allele}
    {T : ℝ} (hT : 0 ≤ T)
    (hcontinuous : ∀ capacity : Locus → ℕ,
      ContinuousOn (fun t ↦ dualGenerator (rates t) capacity) (Set.Icc 0 T))
    (ℓ₀ : Locus) (hap₀ : FullHaplotype Locus Allele) {n : ℕ} (hn : 2 ≤ n)
    (x0 : FrequencyState Deme Locus Allele) (deme : Deme)
    (X : FullHaplotype Locus Allele → J → ℝ) (C : FullHaplotype Locus Allele → L → ℝ) :
    expectedDemeMoments (rateHistoryKernel rates ℓ₀ hap₀ hT hcontinuous) x0 deme X C
      = momentDemeMoments ℓ₀ n deme X C
          (rateHistoryDualPropagator rates (fun _ ↦ n) T
            *ᵥ budgetMomentFeature (fun _ ↦ n) x0) := by
  simp only [expectedDemeMoments, momentDemeMoments,
    integral_covariance_rateHistoryKernel hT hcontinuous ℓ₀ hap₀ hn,
    integral_expectation_rateHistoryKernel hT hcontinuous ℓ₀ hap₀ (one_le_two.trans hn)]

/-- **Deployment moments see the history only through finitely many moments.**  Two histories,
from two initial states, whose propagated budget-`n` moments agree, `n ≥ 2`, give every deme the
same expected deployment moments. -/
theorem expectedDemeMoments_eq_of_moments_eq (ℓ₀ : Locus) (hap₀ : FullHaplotype Locus Allele)
    {first second : List ((NeutralRates Deme Locus Allele × ℝ≥0) ⊕ PulseMatrix Deme)}
    {x₁ x₂ : FrequencyState Deme Locus Allele} {n : ℕ} (hn : 2 ≤ n) (deme : Deme)
    (hmoments : historyEventPropagator (fun _ ↦ n) first *ᵥ budgetMomentFeature (fun _ ↦ n) x₁
      = historyEventPropagator (fun _ ↦ n) second *ᵥ budgetMomentFeature (fun _ ↦ n) x₂)
    (X : FullHaplotype Locus Allele → J → ℝ) (C : FullHaplotype Locus Allele → L → ℝ) :
    expectedDemeMoments (historyEventKernel ℓ₀ hap₀ first) x₁ deme X C
      = expectedDemeMoments (historyEventKernel ℓ₀ hap₀ second) x₂ deme X C := by
  rw [expectedDemeMoments_historyEventKernel ℓ₀ hap₀ first hn,
    expectedDemeMoments_historyEventKernel ℓ₀ hap₀ second hn, hmoments]

variable [Fintype J] [DecidableEq J] [Fintype L] [DecidableEq L]

/-- **Train in one deme, deploy in another, along a history.**  Weights trained with a penalty in a
source deme and deployed in a target deme have a deployment report, `R²`, calibration slope,
intercept and mean squared error computed from the expected deployment moments, equal to the report
of the moment matrices of `U · H₂(x₀)`. -/
theorem transferReport_historyEventKernel (ℓ₀ : Locus) (hap₀ : FullHaplotype Locus Allele)
    (events : List ((NeutralRates Deme Locus Allele × ℝ≥0) ⊕ PulseMatrix Deme))
    (x0 : FrequencyState Deme Locus Allele) (source target : Deme)
    (X : FullHaplotype Locus Allele → J → ℝ) (C : FullHaplotype Locus Allele → L → ℝ)
    (sourceArch targetArch : DemeArchitecture J L) (penalty : ℝ) :
    (expectedDemeMoments (historyEventKernel ℓ₀ hap₀ events) x0 target X C).report targetArch
        (trainedWeights (expectedDemeMoments (historyEventKernel ℓ₀ hap₀ events) x0 source X C)
          sourceArch penalty)
      = (momentDemeMoments ℓ₀ 2 target X C
            (historyEventPropagator (fun _ ↦ 2) events
              *ᵥ budgetMomentFeature (fun _ ↦ 2) x0)).report
          targetArch
          (trainedWeights (momentDemeMoments ℓ₀ 2 source X C
            (historyEventPropagator (fun _ ↦ 2) events *ᵥ budgetMomentFeature (fun _ ↦ 2) x0))
            sourceArch penalty) := by
  rw [expectedDemeMoments_historyEventKernel ℓ₀ hap₀ events le_rfl x0 target,
    expectedDemeMoments_historyEventKernel ℓ₀ hap₀ events le_rfl x0 source]

/-- **Accuracy sees the history only through finitely many moments.**  Two histories whose
propagated budget-2 moments agree give the same deployment report for every training deme,
deployment deme, codings, architectures, environments and penalty. -/
theorem transferReport_eq_of_moments_eq (ℓ₀ : Locus) (hap₀ : FullHaplotype Locus Allele)
    {first second : List ((NeutralRates Deme Locus Allele × ℝ≥0) ⊕ PulseMatrix Deme)}
    {x₁ x₂ : FrequencyState Deme Locus Allele}
    (hmoments : historyEventPropagator (fun _ ↦ 2) first *ᵥ budgetMomentFeature (fun _ ↦ 2) x₁
      = historyEventPropagator (fun _ ↦ 2) second *ᵥ budgetMomentFeature (fun _ ↦ 2) x₂)
    (source target : Deme)
    (X : FullHaplotype Locus Allele → J → ℝ) (C : FullHaplotype Locus Allele → L → ℝ)
    (sourceArch targetArch : DemeArchitecture J L) (penalty : ℝ) :
    (expectedDemeMoments (historyEventKernel ℓ₀ hap₀ first) x₁ target X C).report targetArch
        (trainedWeights (expectedDemeMoments (historyEventKernel ℓ₀ hap₀ first) x₁ source X C)
          sourceArch penalty)
      = (expectedDemeMoments (historyEventKernel ℓ₀ hap₀ second) x₂ target X C).report targetArch
          (trainedWeights (expectedDemeMoments (historyEventKernel ℓ₀ hap₀ second) x₂ source X C)
            sourceArch penalty) := by
  rw [expectedDemeMoments_eq_of_moments_eq ℓ₀ hap₀ le_rfl source hmoments X C,
    expectedDemeMoments_eq_of_moments_eq ℓ₀ hap₀ le_rfl target hmoments X C]

end Moments

end

end Descent.Portability.EndToEndDeploymentLaw
