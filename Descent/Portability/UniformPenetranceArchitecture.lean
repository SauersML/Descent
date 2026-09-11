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

/-- The binary score is fair at every parameter, so each score group carries half the mass. -/
theorem scoreGroupMass_penetranceLaw_true (θ : ℝ) :
    scoreGroupMass (penetranceLaw θ) true = 1 / 2 := by
  simp only [scoreGroupMass, penetranceLaw_mass, penetranceMass]
  ring

/-- The null-score group also carries half the mass. -/
theorem scoreGroupMass_penetranceLaw_false (θ : ℝ) :
    scoreGroupMass (penetranceLaw θ) false = 1 / 2 := by
  simp only [scoreGroupMass, penetranceLaw_mass, penetranceMass]
  ring

/-- Positive outcomes occur only in the positive score group, there with chance `θ`. -/
theorem scoreSuccessMass_penetranceLaw_true (θ : ℝ) (hlo : 0 ≤ θ) (hhi : θ ≤ 1) :
    scoreSuccessMass (penetranceLaw θ) true = θ / 2 := by
  simp only [scoreSuccessMass, penetranceLaw_mass, penetrance_eq_self θ hlo hhi, penetranceMass]

/-- The null-score group contains no positive outcomes at all. -/
theorem scoreSuccessMass_penetranceLaw_false (θ : ℝ) :
    scoreSuccessMass (penetranceLaw θ) false = 0 := by
  simp only [scoreSuccessMass, penetranceLaw_mass, penetranceMass]

/-- NOTE2 section 9.1: the calibration error equals the Brier score for this family, both
being the error rate of the raw binary forecast. -/
theorem discreteECE_penetranceLaw (θ : ℝ) (hlo : 0 ≤ θ) (hhi : θ ≤ 1) :
    discreteECE (penetranceLaw θ) = (1 - θ) / 2 := by
  have htrue : scoreSuccessMass (penetranceLaw θ) true -
      numeric true * scoreGroupMass (penetranceLaw θ) true = -((1 - θ) / 2) := by
    rw [scoreSuccessMass_penetranceLaw_true θ hlo hhi,
      scoreGroupMass_penetranceLaw_true θ]
    simp only [numeric]
    ring
  have hfalse : scoreSuccessMass (penetranceLaw θ) false -
      numeric false * scoreGroupMass (penetranceLaw θ) false = 0 := by
    rw [scoreSuccessMass_penetranceLaw_false θ,
      scoreGroupMass_penetranceLaw_false θ]
    simp only [numeric]
    ring
  rw [discreteECE, Fintype.sum_bool, htrue, hfalse, abs_neg, abs_zero,
    abs_of_nonneg (by linarith : (0:ℝ) ≤ (1 - θ) / 2)]
  ring

/-- NOTE2 section 9.1: the repaired Brier score of the uniform-penetrance architecture. -/
theorem repairedBrier_penetranceLaw (θ : ℝ) (hlo : 0 ≤ θ) (hhi : θ ≤ 1) :
    repairedBrier (penetranceLaw θ) = θ * (1 - θ) / 2 := by
  rw [repairedBrier, Fintype.sum_bool, expectation_cellOutcome_penetranceLaw θ hlo hhi,
    scoreGroupMass_penetranceLaw_true θ, scoreGroupMass_penetranceLaw_false θ,
    scoreSuccessMass_penetranceLaw_true θ hlo hhi,
    scoreSuccessMass_penetranceLaw_false θ,
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
  rw [repairedLogLoss, Fintype.sum_bool, scoreGroupMass_penetranceLaw_true θ,
    scoreGroupMass_penetranceLaw_false θ, scoreSuccessMass_penetranceLaw_true θ hlo hhi,
    scoreSuccessMass_penetranceLaw_false θ]
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
        Finset.single_le_sum
          (f := fun cell ↦ ENNReal.ofReal ((penetranceLaw θ).mass cell) *
            logLossTerm (forecastOfOutcome cell))
          (fun cell _ ↦ zero_le _) (Finset.mem_univ _)

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

/-! ## Exact expectations against the uniform architecture law -/

/-- Two integrands that agree at every parameter of the half-open unit interval have the
same exact expectation against the uniform architecture law. The excluded left endpoint is
where the corpus metrics report undefinedness rather than a number. -/
theorem integral_unit_congr (first second : ℝ → ℝ)
    (h : ∀ θ, 0 < θ → θ ≤ 1 → first θ = second θ) :
    ∫ θ in (0:ℝ)..1, first θ = ∫ θ in (0:ℝ)..1, second θ := by
  refine intervalIntegral.integral_congr_ae (Filter.Eventually.of_forall ?_)
  intro θ hθ
  rw [Set.uIoc_of_le (by norm_num : (0:ℝ) ≤ 1)] at hθ
  exact h θ hθ.1 hθ.2

/-- Every quadratic integrand has this exact expectation against the uniform law. -/
theorem integral_unit_quadratic (c₀ c₁ c₂ : ℝ) :
    ∫ θ in (0:ℝ)..1, (c₀ + c₁ * θ + c₂ * θ ^ 2) = c₀ + c₁ / 2 + c₂ / 3 := by
  have hi0 : IntervalIntegrable (fun _ : ℝ ↦ c₀) MeasureTheory.volume 0 1 :=
    continuous_const.intervalIntegrable 0 1
  have hi1 : IntervalIntegrable (fun θ : ℝ ↦ c₁ * θ) MeasureTheory.volume 0 1 :=
    (by fun_prop : Continuous fun θ : ℝ ↦ c₁ * θ).intervalIntegrable 0 1
  have hi2 : IntervalIntegrable (fun θ : ℝ ↦ c₂ * θ ^ 2) MeasureTheory.volume 0 1 :=
    (by fun_prop : Continuous fun θ : ℝ ↦ c₂ * θ ^ 2).intervalIntegrable 0 1
  rw [intervalIntegral.integral_add (hi0.add hi1) hi2,
    intervalIntegral.integral_add hi0 hi1, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const, integral_id,
    integral_pow]
  norm_num
  all_goals ring

/-- The exact expectation of every power of the reduced replica variable. -/
theorem integral_unit_half_pow (n : ℕ) :
    ∫ θ in (0:ℝ)..1, (θ / 2) ^ n = 1 / (2 ^ n * ((n : ℝ) + 1)) := by
  have hcast : ((n : ℝ) + 1) ≠ 0 := by positivity
  have htwo : ((2:ℝ) ^ n) ≠ 0 := by positivity
  simp only [div_pow]
  rw [intervalIntegral.integral_div, integral_pow, one_pow,
    zero_pow (by omega : n + 1 ≠ 0)]
  field_simp
  all_goals ring

/-- The squared-correlation integrand is integrable on the unit interval: its denominator
is bounded below by one there. -/
theorem intervalIntegrable_unit_ratio :
    IntervalIntegrable (fun θ : ℝ ↦ θ / (2 - θ)) MeasureTheory.volume 0 1 := by
  apply ContinuousOn.intervalIntegrable
  refine ContinuousOn.div (by fun_prop) (by fun_prop) ?_
  intro θ hθ
  rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] at hθ
  have hpos : (0:ℝ) < 2 - θ := by linarith [hθ.2]
  exact ne_of_gt hpos

/-- NOTE2 section 9.1: the exact expected population squared correlation in closed form. -/
theorem integral_unit_ratio : ∫ θ in (0:ℝ)..1, θ / (2 - θ) = 2 * Real.log 2 - 1 := by
  have hderiv : ∀ θ ∈ Set.uIcc (0:ℝ) 1,
      HasDerivAt (fun t : ℝ ↦ -(2 * Real.log (2 - t)) - t) (θ / (2 - θ)) θ := by
    intro θ hθ
    rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] at hθ
    have hpos : (0:ℝ) < 2 - θ := by linarith [hθ.2]
    have hne : (2:ℝ) - θ ≠ 0 := ne_of_gt hpos
    have hinner : HasDerivAt (fun t : ℝ ↦ 2 - t) (-1) θ := by
      simpa using (hasDerivAt_id θ).const_sub (2:ℝ)
    have hlog : HasDerivAt (fun t : ℝ ↦ Real.log (2 - t)) (-1 / (2 - θ)) θ :=
      hinner.log hne
    have hfull : HasDerivAt (fun t : ℝ ↦ -(2 * Real.log (2 - t)) - t)
        (-(2 * (-1 / (2 - θ))) - 1) θ := ((hlog.const_mul 2).neg).sub (hasDerivAt_id θ)
    refine hfull.congr_deriv ?_
    field_simp
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv intervalIntegrable_unit_ratio]
  norm_num
  all_goals ring

/-- NOTE2 section 9.1: the exact expected population area under the curve in closed form. -/
theorem integral_unit_auc :
    ∫ θ in (0:ℝ)..1, (3 - θ) / (2 * (2 - θ)) = (1 + Real.log 2) / 2 := by
  have hint : IntervalIntegrable (fun θ : ℝ ↦ (3 - θ) / (2 * (2 - θ)))
      MeasureTheory.volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    refine ContinuousOn.div (by fun_prop) (by fun_prop) ?_
    intro θ hθ
    rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] at hθ
    have hpos : (0:ℝ) < 2 * (2 - θ) := by linarith [hθ.2]
    exact ne_of_gt hpos
  have hderiv : ∀ θ ∈ Set.uIcc (0:ℝ) 1,
      HasDerivAt (fun t : ℝ ↦ t / 2 - Real.log (2 - t) / 2) ((3 - θ) / (2 * (2 - θ))) θ := by
    intro θ hθ
    rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] at hθ
    have hpos : (0:ℝ) < 2 - θ := by linarith [hθ.2]
    have hne : (2:ℝ) - θ ≠ 0 := ne_of_gt hpos
    have hinner : HasDerivAt (fun t : ℝ ↦ 2 - t) (-1) θ := by
      simpa using (hasDerivAt_id θ).const_sub (2:ℝ)
    have hlog : HasDerivAt (fun t : ℝ ↦ Real.log (2 - t)) (-1 / (2 - θ)) θ :=
      hinner.log hne
    have hfull : HasDerivAt (fun t : ℝ ↦ t / 2 - Real.log (2 - t) / 2)
        (1 / 2 - (-1 / (2 - θ)) / 2) θ :=
      ((hasDerivAt_id θ).div_const 2).sub (hlog.div_const 2)
    refine hfull.congr_deriv ?_
    field_simp
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  norm_num
  all_goals ring

/-- The exact expectation of the negated entropy term. The integrand extends continuously
by zero at the left endpoint, so the interval integral needs no truncation. -/
theorem integral_unit_negMulLog : ∫ θ in (0:ℝ)..1, Real.negMulLog θ = 1 / 4 := by
  have hcont : ContinuousOn (fun t : ℝ ↦ t * Real.negMulLog t / 2 + t * t / 4)
      (Set.Icc 0 1) := by fun_prop
  have hint : IntervalIntegrable Real.negMulLog MeasureTheory.volume 0 1 :=
    Real.continuous_negMulLog.intervalIntegrable 0 1
  have hderiv : ∀ θ ∈ Set.Ioo (0:ℝ) 1,
      HasDerivWithinAt (fun t : ℝ ↦ t * Real.negMulLog t / 2 + t * t / 4)
        (Real.negMulLog θ) (Set.Ioi θ) θ := by
    intro θ hθ
    have hne : θ ≠ 0 := ne_of_gt hθ.1
    have hbase := (((hasDerivAt_id θ).mul (Real.hasDerivAt_negMulLog hne)).div_const 2).add
      (((hasDerivAt_id θ).mul (hasDerivAt_id θ)).div_const 4)
    refine (hbase.congr_deriv ?_).hasDerivWithinAt
    simp only [Real.negMulLog, id_eq]
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le (by norm_num : (0:ℝ) ≤ 1)
    hcont hderiv hint]
  norm_num [Real.negMulLog]

/-- The reflected entropy term has the same exact expectation, by the reflection of the
unit interval onto itself. -/
theorem integral_unit_negMulLog_one_sub :
    ∫ θ in (0:ℝ)..1, Real.negMulLog (1 - θ) = 1 / 4 := by
  rw [intervalIntegral.integral_comp_sub_left Real.negMulLog 1,
    show (1:ℝ) - 1 = 0 by norm_num, show (1:ℝ) - 0 = 1 by norm_num]
  exact integral_unit_negMulLog

/-- The exact expected binary entropy of a uniform parameter is half a nat. -/
theorem integral_unit_binEntropy : ∫ θ in (0:ℝ)..1, Real.binEntropy θ = 1 / 2 := by
  have hi1 : IntervalIntegrable Real.negMulLog MeasureTheory.volume 0 1 :=
    Real.continuous_negMulLog.intervalIntegrable 0 1
  have hi2 : IntervalIntegrable (fun θ : ℝ ↦ Real.negMulLog (1 - θ))
      MeasureTheory.volume 0 1 :=
    (by fun_prop : Continuous fun θ : ℝ ↦ Real.negMulLog (1 - θ)).intervalIntegrable 0 1
  simp only [Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub]
  rw [intervalIntegral.integral_add hi1 hi2, integral_unit_negMulLog,
    integral_unit_negMulLog_one_sub]
  norm_num

/-- NOTE2 section 9.1: the expected population squared correlation is `2 log 2 - 1`. -/
theorem integral_squaredCorrelation_penetranceLaw :
    ∫ θ in (0:ℝ)..1, ((penetranceLaw θ).squaredCorrelation cellScore cellOutcome).getD 0 =
      2 * Real.log 2 - 1 := by
  refine (integral_unit_congr _ (fun θ ↦ θ / (2 - θ)) ?_).trans integral_unit_ratio
  intro θ hpos hhi
  rw [squaredCorrelation_penetranceLaw θ hpos hhi]
  rfl

/-- NOTE2 section 9.1: the expected population area under the curve is `(1 + log 2) / 2`. -/
theorem integral_binaryAUC_penetranceLaw :
    ∫ θ in (0:ℝ)..1, ((penetranceLaw θ).binaryAUC cellScore outcomeFlag).getD 0 =
      (1 + Real.log 2) / 2 := by
  refine (integral_unit_congr _ (fun θ ↦ (3 - θ) / (2 * (2 - θ))) ?_).trans integral_unit_auc
  intro θ hpos hhi
  rw [binaryAUC_penetranceLaw θ hpos hhi]
  rfl

/-- NOTE2 section 9.1: the expected calibration slope is one half. -/
theorem integral_calibrationSlope_penetranceLaw :
    ∫ θ in (0:ℝ)..1, ((penetranceLaw θ).calibrationSlope cellScore cellOutcome).getD 0 =
      1 / 2 :=
  (integral_unit_congr _ (fun θ ↦ 0 + 1 * θ + 0 * θ ^ 2)
      (fun θ hpos hhi ↦ by
        rw [calibrationSlope_penetranceLaw θ hpos.le hhi]
        show θ = 0 + 1 * θ + 0 * θ ^ 2
        ring)).trans (by rw [integral_unit_quadratic]; norm_num)

/-- NOTE2 section 9.1: the expected Brier score of the raw binary forecast is one quarter. -/
theorem integral_meanSquaredError_penetranceLaw :
    ∫ θ in (0:ℝ)..1, (penetranceLaw θ).meanSquaredError cellScore cellOutcome = 1 / 4 :=
  (integral_unit_congr _ (fun θ ↦ 1 / 2 + (-1 / 2) * θ + 0 * θ ^ 2)
      (fun θ hpos hhi ↦ by
        rw [meanSquaredError_penetranceLaw θ hpos.le hhi]
        ring)).trans (by rw [integral_unit_quadratic]; norm_num)

/-- NOTE2 section 9.1: the expected calibration error is also one quarter. -/
theorem integral_discreteECE_penetranceLaw :
    ∫ θ in (0:ℝ)..1, discreteECE (penetranceLaw θ) = 1 / 4 :=
  (integral_unit_congr _ (fun θ ↦ 1 / 2 + (-1 / 2) * θ + 0 * θ ^ 2)
      (fun θ hpos hhi ↦ by
        rw [discreteECE_penetranceLaw θ hpos.le hhi]
        ring)).trans (by rw [integral_unit_quadratic]; norm_num)

/-- NOTE2 section 9.1: the expected agreement rate is three quarters. -/
theorem integral_accuracyRate_penetranceLaw :
    ∫ θ in (0:ℝ)..1, accuracyRate (penetranceLaw θ) = 3 / 4 :=
  (integral_unit_congr _ (fun θ ↦ 1 / 2 + (1 / 2) * θ + 0 * θ ^ 2)
      (fun θ hpos hhi ↦ by
        rw [accuracyRate_penetranceLaw θ hpos.le hhi]
        ring)).trans (by rw [integral_unit_quadratic]; norm_num)

/-- NOTE2 section 9.1: the expected repaired Brier score is one twelfth. -/
theorem integral_repairedBrier_penetranceLaw :
    ∫ θ in (0:ℝ)..1, repairedBrier (penetranceLaw θ) = 1 / 12 :=
  (integral_unit_congr _ (fun θ ↦ 0 + (1 / 2) * θ + (-1 / 2) * θ ^ 2)
      (fun θ hpos hhi ↦ by
        rw [repairedBrier_penetranceLaw θ hpos.le hhi]
        ring)).trans (by rw [integral_unit_quadratic]; norm_num)

/-- NOTE2 section 9.1: the expected repaired log loss is exactly a quarter of a nat, while
the raw log loss is infinite for almost every study. -/
theorem integral_repairedLogLoss_penetranceLaw :
    ∫ θ in (0:ℝ)..1, repairedLogLoss (penetranceLaw θ) = 1 / 4 :=
  (integral_unit_congr _ (fun θ ↦ Real.binEntropy θ / 2)
      (fun θ hpos hhi ↦ repairedLogLoss_penetranceLaw θ hpos.le hhi)).trans
    (by rw [intervalIntegral.integral_div, integral_unit_binEntropy]; norm_num)

/-! ## The distribution function of the squared correlation -/

/-- NOTE2 section 9.1: the sublevel sets of the population squared correlation are exactly
the intervals `[0, 2r / (1 + r)]`. -/
theorem squaredCorrelation_sublevel_eq_Icc (r : ℝ) (hlo : 0 ≤ r) (hhi : r ≤ 1) :
    {θ : ℝ | θ ∈ Set.Icc (0:ℝ) 1 ∧ θ / (2 - θ) ≤ r} =
      Set.Icc 0 (2 * r / (1 + r)) := by
  have hr : (0:ℝ) < 1 + r := by linarith
  have hbound : 2 * r / (1 + r) ≤ 1 := by
    rw [div_le_one hr]
    linarith
  ext θ
  simp only [Set.mem_setOf_eq, Set.mem_Icc]
  constructor
  · rintro ⟨⟨h0, h1⟩, hle⟩
    have hpos : (0:ℝ) < 2 - θ := by linarith
    rw [div_le_iff₀ hpos] at hle
    refine ⟨h0, ?_⟩
    rw [le_div_iff₀ hr]
    nlinarith
  · rintro ⟨h0, h1⟩
    have hθ1 : θ ≤ 1 := le_trans h1 hbound
    have hpos : (0:ℝ) < 2 - θ := by linarith
    rw [le_div_iff₀ hr] at h1
    refine ⟨⟨h0, hθ1⟩, ?_⟩
    rw [div_le_iff₀ hpos]
    nlinarith

/-- NOTE2 section 9.1: the distribution function of the population squared correlation
under the uniform architecture law is `2r / (1 + r)`. -/
theorem volume_squaredCorrelation_sublevel (r : ℝ) (hlo : 0 ≤ r) (hhi : r ≤ 1) :
    MeasureTheory.volume {θ : ℝ | θ ∈ Set.Icc (0:ℝ) 1 ∧ θ / (2 - θ) ≤ r} =
      ENNReal.ofReal (2 * r / (1 + r)) := by
  rw [squaredCorrelation_sublevel_eq_Icc r hlo hhi, Real.volume_Icc, sub_zero]

/-! ## The pooled individual law as an average of conditional cells -/

/-- NOTE2 section 9.1: every cell of the pooled individual law is the exact integral of the
corresponding conditional cell against the uniform architecture law. -/
theorem pooledPenetranceLaw_mass_eq_integral (cell : Bool × Bool) :
    pooledPenetranceLaw.mass cell = ∫ θ in (0:ℝ)..1, (penetranceLaw θ).mass cell := by
  obtain ⟨score, outcome⟩ := cell
  have hnull : (∫ θ in (0:ℝ)..1, (penetranceLaw θ).mass (false, false)) = 1 / 2 := by
    have h : ∀ θ : ℝ, (penetranceLaw θ).mass (false, false) = 1 / 2 := fun _ ↦ rfl
    simp only [h]
    rw [intervalIntegral.integral_const]
    norm_num
  have hzero : (∫ θ in (0:ℝ)..1, (penetranceLaw θ).mass (false, true)) = 0 := by
    have h : ∀ θ : ℝ, (penetranceLaw θ).mass (false, true) = 0 := fun _ ↦ rfl
    simp only [h]
    exact intervalIntegral.integral_zero
  have herror : (∫ θ in (0:ℝ)..1, (penetranceLaw θ).mass (true, false)) = 1 / 4 :=
    (integral_unit_congr _ (fun θ ↦ 1 / 2 + (-1 / 2) * θ + 0 * θ ^ 2)
        (fun θ hpos hhi ↦ by
          simp only [penetranceLaw_mass, penetrance_eq_self θ hpos.le hhi, penetranceMass]
          ring)).trans (by rw [integral_unit_quadratic]; norm_num)
  have hcase : (∫ θ in (0:ℝ)..1, (penetranceLaw θ).mass (true, true)) = 1 / 4 :=
    (integral_unit_congr _ (fun θ ↦ 0 + (1 / 2) * θ + 0 * θ ^ 2)
        (fun θ hpos hhi ↦ by
          simp only [penetranceLaw_mass, penetrance_eq_self θ hpos.le hhi, penetranceMass]
          ring)).trans (by rw [integral_unit_quadratic]; norm_num)
  cases score <;> cases outcome <;>
    simp only [pooledPenetranceLaw_mass, pooledMass, hnull, hzero, herror, hcase]

/-! ## The replica-domain reduction of the squared correlation -/

/-- The reduced numerator of NOTE2 section 9.1: on this family the squared correlation is
the ratio `N / D` with `N θ = θ / 2`. -/
def replicaNumerator (θ : ℝ) : ℝ := θ / 2

/-- The reduced definedness mass of NOTE2 section 9.1: `D θ = 1 - θ / 2`. -/
def replicaDenominator (θ : ℝ) : ℝ := 1 - θ / 2

/-- The reduced pair reproduces the population squared correlation exactly, so the positive
ratio expansion of NOTE2 (15) applies to it. -/
theorem replicaRatio_eq_ratio (θ : ℝ) (hhi : θ ≤ 1) :
    replicaNumerator θ / replicaDenominator θ = θ / (2 - θ) := by
  have hpos : (0:ℝ) < 2 - θ := by linarith
  have hden : (0:ℝ) < 1 - θ / 2 := by linarith
  rw [replicaNumerator, replicaDenominator, div_eq_div_iff (ne_of_gt hden) (ne_of_gt hpos)]
  ring

/-- The complement of the reduced definedness mass is the reduced replica variable. -/
theorem one_sub_replicaDenominator (θ : ℝ) : 1 - replicaDenominator θ = θ / 2 := by
  rw [replicaDenominator]
  ring

/-- NOTE2 section 9.1: the `k`-th coefficient of the positive ratio expansion (15). -/
theorem integral_replica_coefficient (k : ℕ) :
    ∫ θ in (0:ℝ)..1, replicaNumerator θ * (1 - replicaDenominator θ) ^ k =
      1 / (2 ^ (k + 1) * ((k : ℝ) + 2)) := by
  have hpoint : ∀ θ : ℝ,
      replicaNumerator θ * (1 - replicaDenominator θ) ^ k = (θ / 2) ^ (k + 1) := by
    intro θ
    rw [replicaNumerator, one_sub_replicaDenominator, pow_succ]
    ring
  simp only [hpoint]
  rw [integral_unit_half_pow (k + 1)]
  push_cast
  ring

/-- NOTE2 section 9.1: the unresolved definedness mass after `K` replica terms. -/
theorem integral_replica_tail (K : ℕ) :
    ∫ θ in (0:ℝ)..1, (1 - replicaDenominator θ) ^ K = 1 / (2 ^ K * ((K : ℝ) + 1)) := by
  simp only [one_sub_replicaDenominator]
  exact integral_unit_half_pow K

/-- NOTE2 section 9.1: the resolved definedness mass after `K` replica terms. -/
theorem integral_replica_resolved (K : ℕ) :
    ∫ θ in (0:ℝ)..1, (1 - (1 - replicaDenominator θ) ^ K) =
      1 - 1 / (2 ^ K * ((K : ℝ) + 1)) := by
  have hi1 : IntervalIntegrable (fun _ : ℝ ↦ (1:ℝ)) MeasureTheory.volume 0 1 :=
    continuous_const.intervalIntegrable 0 1
  have hi2 : IntervalIntegrable (fun θ : ℝ ↦ (1 - replicaDenominator θ) ^ K)
      MeasureTheory.volume 0 1 := by
    simp only [one_sub_replicaDenominator]
    exact (by fun_prop : Continuous fun θ : ℝ ↦ (θ / 2) ^ K).intervalIntegrable 0 1
  rw [intervalIntegral.integral_sub hi1 hi2, integral_replica_tail K,
    intervalIntegral.integral_const]
  norm_num

/-- NOTE2 (16): the resolved definedness mass and the unresolved tail sum to one for this
architecture, so the normalization of the certificate (18) is the identity. -/
theorem replica_mass_normalization (K : ℕ) :
    (∫ θ in (0:ℝ)..1, (1 - (1 - replicaDenominator θ) ^ K)) +
      (∫ θ in (0:ℝ)..1, (1 - replicaDenominator θ) ^ K) = 1 := by
  rw [integral_replica_resolved K, integral_replica_tail K]
  ring

/-- The `K`-term replica lower sum of NOTE2 (16), in closed form for this architecture. -/
def replicaLowerSum (K : ℕ) : ℝ := ∑ k ∈ Finset.range K, 1 / (2 ^ (k + 1) * ((k : ℝ) + 2))

/-- The unresolved mass bound of NOTE2 (17), in closed form for this architecture. Here it
is not merely a bound: it is the exact unresolved mass. -/
def replicaTail (K : ℕ) : ℝ := 1 / (2 ^ K * ((K : ℝ) + 1))

theorem intervalIntegrable_replica_partial (K : ℕ) :
    IntervalIntegrable (fun θ : ℝ ↦ ∑ k ∈ Finset.range K, (θ / 2) ^ (k + 1))
      MeasureTheory.volume 0 1 := by
  apply Continuous.intervalIntegrable
  exact continuous_finset_sum _ fun k _ ↦ by fun_prop

/-- The lower sum of NOTE2 (16) is the exact integral of the truncated expansion. -/
theorem integral_replica_partial (K : ℕ) :
    (∫ θ in (0:ℝ)..1, ∑ k ∈ Finset.range K, (θ / 2) ^ (k + 1)) = replicaLowerSum K := by
  have hint : ∀ k ∈ Finset.range K,
      IntervalIntegrable (fun θ : ℝ ↦ (θ / 2) ^ (k + 1)) MeasureTheory.volume 0 1 := by
    intro k _
    exact (by fun_prop : Continuous fun θ : ℝ ↦ (θ / 2) ^ (k + 1)).intervalIntegrable 0 1
  rw [intervalIntegral.integral_finset_sum hint, replicaLowerSum]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [integral_unit_half_pow (k + 1)]
  push_cast
  ring

/-- The truncated positive ratio expansion of NOTE2 (15) with its exact remainder: the
reduced ratio is the `K`-term sum plus the `K`-th replica weight times the ratio itself. -/
theorem ratio_eq_partial_add_remainder (θ : ℝ) (hlo : 0 ≤ θ) (hhi : θ ≤ 1) (K : ℕ) :
    θ / (2 - θ) = (∑ k ∈ Finset.range K, (θ / 2) ^ (k + 1)) +
      (θ / 2) ^ K * (θ / (2 - θ)) := by
  have hpos : (0:ℝ) < 2 - θ := by linarith
  have hkey : θ / (2 - θ) * (1 - θ / 2) = θ / 2 := by
    field_simp
  induction K with
  | zero => simp
  | succ K ih =>
    rw [Finset.sum_range_succ]
    linear_combination ih + (θ / 2) ^ K * hkey

/-- The reduced ratio lies in the unit interval on the whole parameter range, which is what
makes the remainder of NOTE2 (15) bounded by the unresolved mass. -/
theorem ratio_mem_unitInterval (θ : ℝ) (hlo : 0 ≤ θ) (hhi : θ ≤ 1) :
    0 ≤ θ / (2 - θ) ∧ θ / (2 - θ) ≤ 1 := by
  have hpos : (0:ℝ) < 2 - θ := by linarith
  refine ⟨div_nonneg hlo hpos.le, ?_⟩
  rw [div_le_one hpos]
  linarith

/-- NOTE2 (18) and section 9.1: the `K`-term replica readout brackets the exact expected
population squared correlation, with width exactly the unresolved mass. The normalization
of (18) is the identity here because the resolved mass and the unresolved mass sum to one,
which `replica_mass_normalization` records; the bracket therefore reads directly as the
lower sum and the lower sum plus the tail. -/
theorem replica_certificate (K : ℕ) :
    replicaLowerSum K ≤ 2 * Real.log 2 - 1 ∧
      2 * Real.log 2 - 1 ≤ replicaLowerSum K + replicaTail K := by
  have hpow : IntervalIntegrable (fun θ : ℝ ↦ (θ / 2) ^ K) MeasureTheory.volume 0 1 :=
    (by fun_prop : Continuous fun θ : ℝ ↦ (θ / 2) ^ K).intervalIntegrable 0 1
  have hpart := intervalIntegrable_replica_partial K
  have hsum : (∫ θ in (0:ℝ)..1,
      ((∑ k ∈ Finset.range K, (θ / 2) ^ (k + 1)) + (θ / 2) ^ K)) =
      replicaLowerSum K + 1 / (2 ^ K * ((K : ℝ) + 1)) := by
    rw [intervalIntegral.integral_add hpart hpow, integral_replica_partial K,
      integral_unit_half_pow K]
  constructor
  · rw [← integral_replica_partial K, ← integral_unit_ratio]
    refine intervalIntegral.integral_mono_on (by norm_num) hpart
      intervalIntegrable_unit_ratio ?_
    intro θ hθ
    simp only [Set.mem_Icc] at hθ
    have hexp := ratio_eq_partial_add_remainder θ hθ.1 hθ.2 K
    have hr := ratio_mem_unitInterval θ hθ.1 hθ.2
    have hx : (0:ℝ) ≤ (θ / 2) ^ K := pow_nonneg (by linarith [hθ.1]) K
    have hprod : 0 ≤ (θ / 2) ^ K * (θ / (2 - θ)) := mul_nonneg hx hr.1
    linarith
  · have htarget : replicaLowerSum K + replicaTail K =
        ∫ θ in (0:ℝ)..1, ((∑ k ∈ Finset.range K, (θ / 2) ^ (k + 1)) + (θ / 2) ^ K) := by
      rw [hsum, replicaTail]
    rw [htarget, ← integral_unit_ratio]
    refine intervalIntegral.integral_mono_on (by norm_num) intervalIntegrable_unit_ratio
      (hpart.add hpow) ?_
    intro θ hθ
    simp only [Set.mem_Icc] at hθ
    have hexp := ratio_eq_partial_add_remainder θ hθ.1 hθ.2 K
    have hr := ratio_mem_unitInterval θ hθ.1 hθ.2
    have hx : (0:ℝ) ≤ (θ / 2) ^ K := pow_nonneg (by linarith [hθ.1]) K
    have hprod : (θ / 2) ^ K * (θ / (2 - θ)) ≤ (θ / 2) ^ K * 1 :=
      mul_le_mul_of_nonneg_left hr.2 hx
    rw [mul_one] at hprod
    linarith

end

end Descent.Portability.UniformPenetranceArchitecture
