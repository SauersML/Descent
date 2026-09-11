/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.ExactMetricEvaluation
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

assert_below Descent.Decision Descent.Program

/-!
# The uniform-penetrance continuous architecture

This module executes the worked example of NOTE2 section 9.1 in closed form. A single
architecture parameter is drawn uniformly on the unit interval and is shared by every
individual of a study; conditionally on it, a fair binary score is drawn and the outcome
occurs exactly when the score is one and the penetrance draw succeeds. That conditional
law is the family of NOTE2 (12) with a continuous mixing law, and each of its population
metrics is an explicit rational or logarithmic function of the parameter.

The conditional law is built as a `FiniteReportLaw` on `Bool x Bool`, so every metric here
is the corpus metric of `ExactMetricEvaluation` rather than a fresh definition: `variance`,
`covariance`, `squaredCorrelation`, `calibrationSlope`, `meanSquaredError`, `binaryCaseMass`,
`binaryAUCNumerator` and `binaryAUC` are all imported. The four quantities NOTE2 section 9.1
needs and the corpus does not yet carry are added here: the discrete calibration error of
NOTE2 (22), the repaired Brier score of NOTE2 (23), the agreement rate, and the log loss in
both its repaired real-valued form and its raw extended-real form.

Proved here: the seven closed forms of NOTE2 section 9.1 (squared correlation, area under
the curve, calibration slope and intercept, Brier score, calibration error, agreement rate,
repaired Brier score) together with the definedness verdict that each corpus metric returns,
the raw log loss being infinite for every parameter below one, the pooled individual law and
its squared correlation of one third, and the reduced numerator and definedness mass of the
replica expansion. The exact integrals of all of these against the uniform architecture law,
the distribution function of the squared correlation, the replica coefficients and the
normalization-aware sandwich are the second half of the module.

The parameter enters the law through a clamp onto the closed unit interval, so the family is
a total function of a real parameter and can be integrated directly; every theorem states the
parameter range it needs, and on that range the clamp is the identity. Not formalized here:
the pooled law is exhibited as an explicit law whose cells are proved equal to the integrals
of the conditional cells, not as an integral of laws in a Bochner sense; and the raw log loss
is stated as an extended-real sum, not as a limit of truncated losses.

## Empirical status

None. The bodies here are algebra: the architecture law is a supplied uniform distribution on
a parameter, and every metric value is a closed-form consequence of the four cell masses, so
no measurement can bear on any of these identities.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.UniformPenetranceArchitecture

open scoped BigOperators ENNReal

noncomputable section

/-- The real value of a binary score or binary outcome. -/
def numeric : Bool → ℝ
  | false => 0
  | true => 1

/-- The real-valued score coordinate of a report cell. -/
def cellScore (cell : Bool × Bool) : ℝ := numeric cell.1

/-- The real-valued outcome coordinate of a report cell. -/
def cellOutcome (cell : Bool × Bool) : ℝ := numeric cell.2

/-- The binary outcome coordinate of a report cell. -/
def outcomeFlag (cell : Bool × Bool) : Bool := cell.2

/-- The indicator that a binary score and a binary outcome agree. -/
def agreement : Bool → Bool → ℝ
  | false, false => 1
  | false, true => 0
  | true, false => 0
  | true, true => 1

/-- Every sum over the two-bit report space is its explicit four-cell sum. -/
theorem sum_cells (weight : Bool × Bool → ℝ) :
    ∑ cell, weight cell =
      weight (false, false) + weight (false, true) + weight (true, false) +
        weight (true, true) := by
  simp only [Fintype.sum_prod_type, Fintype.sum_bool]
  ring

/-- The four cell masses of the conditional law of NOTE2 (12) at penetrance `θ`: the score
is fair, and the outcome occurs only in the positive score group, there with chance `θ`. -/
def penetranceMass (θ : ℝ) : Bool × Bool → ℝ
  | (false, false) => 1 / 2
  | (false, true) => 0
  | (true, false) => (1 - θ) / 2
  | (true, true) => θ / 2

/-- The penetrance parameter, clamped to the closed unit interval on which the family of
NOTE2 (12) is a probability law. On that interval it is the identity. -/
def penetrance (θ : ℝ) : ℝ := max 0 (min 1 θ)

theorem penetrance_nonneg (θ : ℝ) : 0 ≤ penetrance θ := le_max_left _ _

theorem penetrance_le_one (θ : ℝ) : penetrance θ ≤ 1 :=
  max_le zero_le_one (min_le_left _ _)

/-- Inside the unit interval the clamp does nothing. -/
theorem penetrance_eq_self (θ : ℝ) (hlo : 0 ≤ θ) (hhi : θ ≤ 1) : penetrance θ = θ := by
  rw [penetrance, min_eq_right hhi, max_eq_right hlo]

/-- The conditional report law of NOTE2 section 9.1: a fair binary score together with an
outcome that is one exactly when the score is one and the penetrance draw succeeds. -/
def penetranceLaw (θ : ℝ) : FiniteReportLaw (Bool × Bool) where
  mass := penetranceMass (penetrance θ)
  mass_nonneg := by
    have hlo := penetrance_nonneg θ
    have hhi := penetrance_le_one θ
    rintro ⟨score, outcome⟩
    cases score <;> cases outcome <;> simp only [penetranceMass] <;> linarith
  mass_sum := by
    simp only [Fintype.sum_prod_type, Fintype.sum_bool, penetranceMass]
    ring

theorem penetranceLaw_mass (θ : ℝ) (cell : Bool × Bool) :
    (penetranceLaw θ).mass cell = penetranceMass (penetrance θ) cell := rfl

/-- Every report metric has the same three-term exact expectation under the conditional law:
the null-score cell carries half the mass, and the positive-score cells split the rest. -/
theorem expectation_penetranceLaw (θ : ℝ) (hlo : 0 ≤ θ) (hhi : θ ≤ 1)
    (metric : Bool × Bool → ℝ) :
    (penetranceLaw θ).expectation metric =
      metric (false, false) / 2 + (1 - θ) / 2 * metric (true, false) +
        θ / 2 * metric (true, true) := by
  rw [FiniteReportLaw.expectation, sum_cells]
  simp only [penetranceLaw_mass, penetrance_eq_self θ hlo hhi, penetranceMass]
  ring

/-- The score is fair at every penetrance. -/
theorem expectation_cellScore_penetranceLaw (θ : ℝ) (hlo : 0 ≤ θ) (hhi : θ ≤ 1) :
    (penetranceLaw θ).expectation cellScore = 1 / 2 := by
  rw [expectation_penetranceLaw θ hlo hhi]
  simp only [cellScore, numeric]
  ring

/-- The population prevalence is half the penetrance. -/
theorem expectation_cellOutcome_penetranceLaw (θ : ℝ) (hlo : 0 ≤ θ) (hhi : θ ≤ 1) :
    (penetranceLaw θ).expectation cellOutcome = θ / 2 := by
  rw [expectation_penetranceLaw θ hlo hhi]
  simp only [cellOutcome, numeric]
  ring

/-- A fair binary score has variance one quarter. -/
theorem variance_cellScore_penetranceLaw (θ : ℝ) (hlo : 0 ≤ θ) (hhi : θ ≤ 1) :
    (penetranceLaw θ).variance cellScore = 1 / 4 := by
  rw [FiniteReportLaw.variance_eq_rawMoments, expectation_cellScore_penetranceLaw θ hlo hhi,
    expectation_penetranceLaw θ hlo hhi]
  simp only [cellScore, numeric]
  ring

/-- The outcome variance of NOTE2 section 9.1, vanishing exactly at zero penetrance. -/
theorem variance_cellOutcome_penetranceLaw (θ : ℝ) (hlo : 0 ≤ θ) (hhi : θ ≤ 1) :
    (penetranceLaw θ).variance cellOutcome = θ * (2 - θ) / 4 := by
  rw [FiniteReportLaw.variance_eq_rawMoments, expectation_cellOutcome_penetranceLaw θ hlo hhi,
    expectation_penetranceLaw θ hlo hhi]
  simp only [cellOutcome, numeric]
  ring

/-- Score and outcome covary by a quarter of the penetrance. -/
theorem covariance_penetranceLaw (θ : ℝ) (hlo : 0 ≤ θ) (hhi : θ ≤ 1) :
    (penetranceLaw θ).covariance cellScore cellOutcome = θ / 4 := by
  rw [FiniteReportLaw.covariance_eq_rawMoments, expectation_cellScore_penetranceLaw θ hlo hhi,
    expectation_cellOutcome_penetranceLaw θ hlo hhi, expectation_penetranceLaw θ hlo hhi]
  simp only [cellScore, cellOutcome, numeric]
  ring

/-- NOTE2 section 9.1 and NOTE2 (13): the population squared correlation is `θ / (2 - θ)`,
and the corpus metric reports it as defined for every positive penetrance. -/
theorem squaredCorrelation_penetranceLaw (θ : ℝ) (hpos : 0 < θ) (hhi : θ ≤ 1) :
    (penetranceLaw θ).squaredCorrelation cellScore cellOutcome = some (θ / (2 - θ)) := by
  have htwo : (0:ℝ) < 2 - θ := by linarith
  have hvs : (penetranceLaw θ).variance cellScore = 1 / 4 :=
    variance_cellScore_penetranceLaw θ hpos.le hhi
  have hvo : (penetranceLaw θ).variance cellOutcome = θ * (2 - θ) / 4 :=
    variance_cellOutcome_penetranceLaw θ hpos.le hhi
  have hcov : (penetranceLaw θ).covariance cellScore cellOutcome = θ / 4 :=
    covariance_penetranceLaw θ hpos.le hhi
  have hprod : (0:ℝ) < θ * (2 - θ) := mul_pos hpos htwo
  simp only [FiniteReportLaw.squaredCorrelation, hvs, hvo, hcov]
  split_ifs with hcond
  · congr 1
    rw [div_eq_div_iff (by linarith) (ne_of_gt htwo)]
    ring
  · exact absurd ⟨by linarith, by linarith⟩ hcond

/-- At zero penetrance the outcome is constant, so the corpus metric reports the squared
correlation as undefined rather than assigning it a number. -/
theorem squaredCorrelation_penetranceLaw_zero :
    (penetranceLaw 0).squaredCorrelation cellScore cellOutcome = none := by
  have hvo : (penetranceLaw 0).variance cellOutcome = 0 * (2 - 0) / 4 :=
    variance_cellOutcome_penetranceLaw 0 le_rfl zero_le_one
  simp only [FiniteReportLaw.squaredCorrelation, hvo]
  split_ifs with hcond
  · exact absurd hcond.2 (by norm_num)
  · rfl

/-- NOTE2 section 9.1: the population calibration slope is the penetrance itself. -/
theorem calibrationSlope_penetranceLaw (θ : ℝ) (hlo : 0 ≤ θ) (hhi : θ ≤ 1) :
    (penetranceLaw θ).calibrationSlope cellScore cellOutcome = some θ := by
  have hvs : (penetranceLaw θ).variance cellScore = 1 / 4 :=
    variance_cellScore_penetranceLaw θ hlo hhi
  have hcov : (penetranceLaw θ).covariance cellScore cellOutcome = θ / 4 :=
    covariance_penetranceLaw θ hlo hhi
  simp only [FiniteReportLaw.calibrationSlope, hvs, hcov]
  split_ifs with hcond
  · congr 1
    ring
  · exact absurd (by norm_num : (0:ℝ) < 1 / 4) hcond

/-- The least-squares intercept of the population calibration line at a supplied slope. -/
def calibrationIntercept (law : FiniteReportLaw (Bool × Bool)) (slope : ℝ) : ℝ :=
  law.expectation cellOutcome - slope * law.expectation cellScore

/-- NOTE2 section 9.1: at the certified slope the calibration intercept is exactly zero. -/
theorem calibrationIntercept_penetranceLaw (θ : ℝ) (hlo : 0 ≤ θ) (hhi : θ ≤ 1) :
    calibrationIntercept (penetranceLaw θ) θ = 0 := by
  rw [calibrationIntercept, expectation_cellOutcome_penetranceLaw θ hlo hhi,
    expectation_cellScore_penetranceLaw θ hlo hhi]
  ring

/-- NOTE2 section 9.1: the Brier score of the raw binary forecast is the error rate. -/
theorem meanSquaredError_penetranceLaw (θ : ℝ) (hlo : 0 ≤ θ) (hhi : θ ≤ 1) :
    (penetranceLaw θ).meanSquaredError cellScore cellOutcome = (1 - θ) / 2 := by
  rw [FiniteReportLaw.meanSquaredError, expectation_penetranceLaw θ hlo hhi]
  simp only [cellScore, cellOutcome, numeric]
  ring

/-- The case prevalence seen by the corpus area-under-the-curve metric. -/
theorem binaryCaseMass_penetranceLaw (θ : ℝ) (hlo : 0 ≤ θ) (hhi : θ ≤ 1) :
    (penetranceLaw θ).binaryCaseMass outcomeFlag = θ / 2 := by
  rw [FiniteReportLaw.binaryCaseMass, expectation_penetranceLaw θ hlo hhi]
  norm_num [outcomeFlag]
  all_goals ring

/-- The unnormalized case-control ranking credit of NOTE2 section 5.4, with half credit
for the ties that a binary score necessarily produces. -/
theorem binaryAUCNumerator_penetranceLaw (θ : ℝ) (hlo : 0 ≤ θ) (hhi : θ ≤ 1) :
    (penetranceLaw θ).binaryAUCNumerator cellScore outcomeFlag = θ * (3 - θ) / 8 := by
  rw [FiniteReportLaw.binaryAUCNumerator]
  norm_num [expectation_penetranceLaw θ hlo hhi, outcomeFlag, cellScore, numeric,
    empiricalAUCComparison]
  all_goals ring

/-- NOTE2 section 9.1: the population area under the curve is `(3 - θ) / (2 (2 - θ))`,
defined for every positive penetrance. -/
theorem binaryAUC_penetranceLaw (θ : ℝ) (hpos : 0 < θ) (hhi : θ ≤ 1) :
    (penetranceLaw θ).binaryAUC cellScore outcomeFlag =
      some ((3 - θ) / (2 * (2 - θ))) := by
  have htwo : (0:ℝ) < 2 - θ := by linarith
  have hcases : (penetranceLaw θ).binaryCaseMass outcomeFlag = θ / 2 :=
    binaryCaseMass_penetranceLaw θ hpos.le hhi
  have hnum : (penetranceLaw θ).binaryAUCNumerator cellScore outcomeFlag = θ * (3 - θ) / 8 :=
    binaryAUCNumerator_penetranceLaw θ hpos.le hhi
  have hden : (0:ℝ) < θ / 2 * (1 - θ / 2) := mul_pos (by linarith) (by linarith)
  simp only [FiniteReportLaw.binaryAUC, hcases, hnum]
  split_ifs with hcond
  · congr 1
    rw [div_eq_div_iff (ne_of_gt hden) (by linarith : 2 * (2 - θ) ≠ 0)]
    ring
  · exact absurd ⟨by linarith, by linarith⟩ hcond

/-- The mass of the group on which the binary score takes the value `score`. -/
def scoreGroupMass (law : FiniteReportLaw (Bool × Bool)) (score : Bool) : ℝ :=
  law.mass (score, false) + law.mass (score, true)

/-- The joint mass of the score group `score` and a positive outcome. -/
def scoreSuccessMass (law : FiniteReportLaw (Bool × Bool)) (score : Bool) : ℝ :=
  law.mass (score, true)

/-- NOTE2 (22): the discrete calibration error of a binary forecast, summed over score
groups with the forecast read as the numeric score value. -/
def discreteECE (law : FiniteReportLaw (Bool × Bool)) : ℝ :=
  ∑ score, |scoreSuccessMass law score - numeric score * scoreGroupMass law score|

/-- NOTE2 (23): the Brier score repaired by replacing each forecast with the realized rate
of its own score group. Empty score groups contribute nothing. -/
def repairedBrier (law : FiniteReportLaw (Bool × Bool)) : ℝ :=
  law.expectation cellOutcome -
    ∑ score, (if scoreGroupMass law score = 0 then 0
      else scoreSuccessMass law score ^ 2 / scoreGroupMass law score)

/-- The probability that the binary score agrees with the realized outcome. -/
def accuracyRate (law : FiniteReportLaw (Bool × Bool)) : ℝ :=
  law.expectation fun cell ↦ agreement cell.1 cell.2

theorem scoreGroupMass_penetranceLaw_true (θ : ℝ) (hlo : 0 ≤ θ) (hhi : θ ≤ 1) :
    scoreGroupMass (penetranceLaw θ) true = 1 / 2 := by
  simp only [scoreGroupMass, penetranceLaw_mass, penetrance_eq_self θ hlo hhi, penetranceMass]
  ring

theorem scoreGroupMass_penetranceLaw_false (θ : ℝ) (hlo : 0 ≤ θ) (hhi : θ ≤ 1) :
    scoreGroupMass (penetranceLaw θ) false = 1 / 2 := by
  simp only [scoreGroupMass, penetranceLaw_mass, penetrance_eq_self θ hlo hhi, penetranceMass]
  ring

theorem scoreSuccessMass_penetranceLaw_true (θ : ℝ) (hlo : 0 ≤ θ) (hhi : θ ≤ 1) :
    scoreSuccessMass (penetranceLaw θ) true = θ / 2 := by
  simp only [scoreSuccessMass, penetranceLaw_mass, penetrance_eq_self θ hlo hhi, penetranceMass]

theorem scoreSuccessMass_penetranceLaw_false (θ : ℝ) (hlo : 0 ≤ θ) (hhi : θ ≤ 1) :
    scoreSuccessMass (penetranceLaw θ) false = 0 := by
  simp only [scoreSuccessMass, penetranceLaw_mass, penetrance_eq_self θ hlo hhi, penetranceMass]

/-- NOTE2 section 9.1: the calibration error equals the Brier score for this family, both
being the error rate of the raw binary forecast. -/
theorem discreteECE_penetranceLaw (θ : ℝ) (hlo : 0 ≤ θ) (hhi : θ ≤ 1) :
    discreteECE (penetranceLaw θ) = (1 - θ) / 2 := by
  have htrue : scoreSuccessMass (penetranceLaw θ) true -
      numeric true * scoreGroupMass (penetranceLaw θ) true = -((1 - θ) / 2) := by
    rw [scoreSuccessMass_penetranceLaw_true θ hlo hhi,
      scoreGroupMass_penetranceLaw_true θ hlo hhi]
    simp only [numeric]
    ring
  have hfalse : scoreSuccessMass (penetranceLaw θ) false -
      numeric false * scoreGroupMass (penetranceLaw θ) false = 0 := by
    rw [scoreSuccessMass_penetranceLaw_false θ hlo hhi,
      scoreGroupMass_penetranceLaw_false θ hlo hhi]
    simp only [numeric]
    ring
  rw [discreteECE, Fintype.sum_bool, htrue, hfalse, abs_neg, abs_zero,
    abs_of_nonneg (by linarith : (0:ℝ) ≤ (1 - θ) / 2)]
  ring

/-- NOTE2 section 9.1: the repaired Brier score of the uniform-penetrance architecture. -/
theorem repairedBrier_penetranceLaw (θ : ℝ) (hlo : 0 ≤ θ) (hhi : θ ≤ 1) :
    repairedBrier (penetranceLaw θ) = θ * (1 - θ) / 2 := by
  rw [repairedBrier, Fintype.sum_bool, expectation_cellOutcome_penetranceLaw θ hlo hhi,
    scoreGroupMass_penetranceLaw_true θ hlo hhi, scoreGroupMass_penetranceLaw_false θ hlo hhi,
    scoreSuccessMass_penetranceLaw_true θ hlo hhi,
    scoreSuccessMass_penetranceLaw_false θ hlo hhi,
    if_neg (by norm_num : ¬((1:ℝ) / 2 = 0)), if_neg (by norm_num : ¬((1:ℝ) / 2 = 0))]
  ring

/-- NOTE2 section 9.1: the agreement rate of the raw binary forecast. -/
theorem accuracyRate_penetranceLaw (θ : ℝ) (hlo : 0 ≤ θ) (hhi : θ ≤ 1) :
    accuracyRate (penetranceLaw θ) = (1 + θ) / 2 := by
  rw [accuracyRate, expectation_penetranceLaw θ hlo hhi]
  simp only [agreement]
  ring

/-- NOTE2 section 9.1: the log loss after repairing each forecast to the realized rate of
its own score group, expressed through the Shannon entropy of that rate. -/
def repairedLogLoss (law : FiniteReportLaw (Bool × Bool)) : ℝ :=
  ∑ score, scoreGroupMass law score *
    Real.binEntropy (scoreSuccessMass law score / scoreGroupMass law score)

/-- NOTE2 section 9.1: the repaired log loss is half the binary entropy of the penetrance,
the null-score group contributing nothing because its realized rate is zero. -/
theorem repairedLogLoss_penetranceLaw (θ : ℝ) (hlo : 0 ≤ θ) (hhi : θ ≤ 1) :
    repairedLogLoss (penetranceLaw θ) = Real.binEntropy θ / 2 := by
  rw [repairedLogLoss, Fintype.sum_bool, scoreGroupMass_penetranceLaw_true θ hlo hhi,
    scoreGroupMass_penetranceLaw_false θ hlo hhi, scoreSuccessMass_penetranceLaw_true θ hlo hhi,
    scoreSuccessMass_penetranceLaw_false θ hlo hhi]
  rw [show θ / 2 / (1 / 2) = θ by ring, show (0:ℝ) / (1 / 2) = 0 by norm_num]
  rw [Real.binEntropy_zero]
  ring

/-- The forecast probability that the raw binary score assigns to the realized outcome. -/
def forecastOfOutcome : Bool × Bool → ℝ
  | (false, false) => 1
  | (false, true) => 0
  | (true, false) => 0
  | (true, true) => 1

/-- The extended-real log-loss contribution of a forecast. A realized outcome that the
forecast gave no probability contributes an infinite loss. -/
def logLossTerm (forecast : ℝ) : ℝ≥0∞ :=
  if forecast ≤ 0 then ⊤ else ENNReal.ofReal (-Real.log forecast)

/-- The expected raw log loss of a binary forecast, in extended nonnegative reals. -/
def rawLogLoss (law : FiniteReportLaw (Bool × Bool)) : ℝ≥0∞ :=
  ∑ cell, ENNReal.ofReal (law.mass cell) * logLossTerm (forecastOfOutcome cell)

/-- NOTE2 section 9.1: for every penetrance below one the positive-score group contains
outcome-free individuals whose realized outcome the raw binary forecast gave probability
zero, so the expected raw log loss is infinite. -/
theorem rawLogLoss_penetranceLaw (θ : ℝ) (hlo : 0 ≤ θ) (hhi : θ < 1) :
    rawLogLoss (penetranceLaw θ) = ⊤ := by
  have hmass : (penetranceLaw θ).mass (true, false) = (1 - θ) / 2 := by
    simp only [penetranceLaw_mass, penetrance_eq_self θ hlo hhi.le, penetranceMass]
  have hpos : (0:ℝ) < (1 - θ) / 2 := by linarith
  have hne : ENNReal.ofReal ((1 - θ) / 2) ≠ 0 := by
    simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
    exact hpos
  have hinf : logLossTerm (forecastOfOutcome (true, false)) = ⊤ := by
    simp [forecastOfOutcome, logLossTerm]
  have hterm : ENNReal.ofReal ((penetranceLaw θ).mass (true, false)) *
      logLossTerm (forecastOfOutcome (true, false)) = ⊤ := by
    rw [hmass, hinf]
    exact ENNReal.mul_top hne
  rw [rawLogLoss]
  refine eq_top_iff.mpr ?_
  calc (⊤ : ℝ≥0∞) = ENNReal.ofReal ((penetranceLaw θ).mass (true, false)) *
        logLossTerm (forecastOfOutcome (true, false)) := hterm.symm
    _ ≤ ∑ cell, ENNReal.ofReal ((penetranceLaw θ).mass cell) *
          logLossTerm (forecastOfOutcome cell) :=
        Finset.single_le_sum (fun cell _ ↦ zero_le _) (Finset.mem_univ _)

/-- The four cell masses of the pooled individual law of NOTE2 section 9.1, obtained by
averaging the conditional cells over a uniform penetrance. -/
def pooledMass : Bool × Bool → ℝ
  | (false, false) => 1 / 2
  | (false, true) => 0
  | (true, false) => 1 / 4
  | (true, true) => 1 / 4

/-- The pooled individual law: what a single observation drawn from a fresh study looks
like once the architecture parameter has been averaged out. -/
def pooledPenetranceLaw : FiniteReportLaw (Bool × Bool) where
  mass := pooledMass
  mass_nonneg := by
    rintro ⟨score, outcome⟩
    cases score <;> cases outcome <;> norm_num [pooledMass]
  mass_sum := by
    simp only [Fintype.sum_prod_type, Fintype.sum_bool, pooledMass]
    norm_num

theorem pooledPenetranceLaw_mass (cell : Bool × Bool) :
    pooledPenetranceLaw.mass cell = pooledMass cell := rfl

/-- Every report metric has this exact expectation under the pooled individual law. -/
theorem expectation_pooledPenetranceLaw (metric : Bool × Bool → ℝ) :
    pooledPenetranceLaw.expectation metric =
      metric (false, false) / 2 + metric (true, false) / 4 + metric (true, true) / 4 := by
  rw [FiniteReportLaw.expectation, sum_cells]
  simp only [pooledPenetranceLaw_mass, pooledMass]
  ring

/-- NOTE2 section 9.1: the squared correlation of the pooled individual law is one third,
which is not the expected population squared correlation. Conditional-then-average and
average-then-evaluate are different functionals of the same architecture law. -/
theorem squaredCorrelation_pooledPenetranceLaw :
    pooledPenetranceLaw.squaredCorrelation cellScore cellOutcome = some (1 / 3) := by
  have hvs : pooledPenetranceLaw.variance cellScore = 1 / 4 := by
    rw [FiniteReportLaw.variance_eq_rawMoments]
    simp only [expectation_pooledPenetranceLaw, cellScore, numeric]
    ring
  have hvo : pooledPenetranceLaw.variance cellOutcome = 3 / 16 := by
    rw [FiniteReportLaw.variance_eq_rawMoments]
    simp only [expectation_pooledPenetranceLaw, cellOutcome, numeric]
    ring
  have hcov : pooledPenetranceLaw.covariance cellScore cellOutcome = 1 / 8 := by
    rw [FiniteReportLaw.covariance_eq_rawMoments]
    simp only [expectation_pooledPenetranceLaw, cellScore, cellOutcome, numeric]
    ring
  simp only [FiniteReportLaw.squaredCorrelation, hvs, hvo, hcov]
  split_ifs with hcond
  · congr 1
    norm_num
  · exact absurd ⟨by norm_num, by norm_num⟩ hcond

end

end Descent.Portability.UniformPenetranceArchitecture
