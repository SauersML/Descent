/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.PortabilityMasterTheorem
import Descent.Portability.IIDBinExperiment
import Descent.Portability.EmpiricalAUCComparison
import Descent.Foundations.TransportIdentities
import Mathlib.Analysis.SpecialFunctions.NonIntegrable
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

assert_below Descent.Decision Descent.Program

/-!
# A study family whose reports are perfect and whose expected slope is infinite

This is the divergent example of NOTE2 §6.3. A study draws a shared parameter `U` uniform on
the unit interval, a fair binary outcome `Y`, and reports the score `S = U · Y`. Conditional
on `U = u` the pair `(S, Y)` is the two-point law that puts mass one half on `(0, 0)` and mass
one half on `(u, 1)`; that law is `outcomeExp` with score readout `scoreValue u`.

Three conditional reports are computed exactly. `outcomeExp_squared_correlation` gives
population squared correlation one, `rankAccuracy_eq_one` gives rank accuracy one, and
`conditionalSlope_eq_inv` gives linear calibration slope `1/u`, all for every `u > 0`. So
every study in the family is, by two of the three reports, perfect.

The third report is not integrable. `conditionalSlope_not_integrableOn` shows the slope is not
integrable over the unit interval, and `lintegral_conditionalSlope_eq_top` shows its upper
integral is `⊤`: the expected calibration slope is `+∞` even though every individual study
reports a finite slope. The non-integrability is Mathlib's `intervalIntegrable_inv_iff`, which
says `x ↦ x⁻¹` fails to be interval integrable exactly when zero lies in the closed interval.

Scope. The mixing law over `U` is Lebesgue measure restricted to `Set.Ioc 0 1`, which is the
uniform law on the unit interval up to a Lebesgue-null endpoint. The rank accuracy is the
two-replica functional of NOTE2 §5.4 with the one-half tie credit, computed on this family
only; no general theory of that functional is developed here. Nothing is claimed about the
joint law of `(S, Y)` after averaging over `U`.

## Empirical status

None. The bodies here are algebra and measure theory: the two-point conditional law is
stipulated, and the slope, the squared correlation and the rank accuracy are computed from it
by exact algebra. No measurement bears on any statement in this module.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.UnboundedSlopeExample

open Foundations MeasureTheory

noncomputable section

/-! ### The conditional two-point law -/

/-- The conditional law of NOTE2 §6.3 given the shared parameter: a fair binary outcome. -/
def outcomeExp : ExpFunctional Bool :=
  weightedExp (fun _ ↦ (1 : ℝ) / 2) (fun _ ↦ by norm_num)
    (by norm_num [Fintype.sum_bool])

/-- The score readout `S = u · Y` at parameter `u`. -/
def scoreValue (parameter : ℝ) (outcome : Bool) : ℝ := if outcome then parameter else 0

/-- The outcome readout `Y`, which is the corpus binary label `IIDBinExperiment.label`. -/
def outcomeValue (outcome : Bool) : ℝ := IIDBinExperiment.label outcome

/-- Exact evaluation of the conditional law on an arbitrary statistic. -/
theorem outcomeExp_apply (statistic : Bool → ℝ) :
    outcomeExp statistic = (statistic false + statistic true) / 2 := by
  simp only [outcomeExp, weightedExp_apply, Fintype.sum_bool]
  ring

/-- The conditional mean score is half the parameter. -/
theorem outcomeExp_mean_score (parameter : ℝ) :
    outcomeExp (scoreValue parameter) = parameter / 2 := by
  rw [outcomeExp_apply]
  simp only [scoreValue]
  norm_num

/-- The conditional mean outcome is one half. -/
theorem outcomeExp_mean_outcome : outcomeExp outcomeValue = 1 / 2 := by
  rw [outcomeExp_apply]
  simp only [outcomeValue, IIDBinExperiment.label]
  norm_num

/-- The conditional score variance is a quarter of the squared parameter. -/
theorem outcomeExp_variance_score (parameter : ℝ) :
    variance outcomeExp (scoreValue parameter) = parameter ^ 2 / 4 := by
  rw [variance, outcomeExp_mean_score, outcomeExp_apply]
  simp only [scoreValue]
  norm_num
  ring

/-- The conditional outcome variance is one quarter. -/
theorem outcomeExp_variance_outcome : variance outcomeExp outcomeValue = 1 / 4 := by
  rw [variance, outcomeExp_mean_outcome, outcomeExp_apply]
  simp only [outcomeValue, IIDBinExperiment.label]
  norm_num

/-- The conditional covariance of score and outcome is a quarter of the parameter. -/
theorem outcomeExp_covariance (parameter : ℝ) :
    covariance outcomeExp (scoreValue parameter) outcomeValue = parameter / 4 := by
  rw [covariance, outcomeExp_mean_score, outcomeExp_mean_outcome, outcomeExp_apply]
  simp only [scoreValue, outcomeValue, IIDBinExperiment.label]
  norm_num
  ring

/-- **NOTE2 §6.3.** Conditional on the shared parameter the population squared correlation is
exactly one, for every nonzero parameter value. -/
theorem outcomeExp_squared_correlation (parameter : ℝ) (hparam : parameter ≠ 0) :
    covariance outcomeExp (scoreValue parameter) outcomeValue ^ 2 /
        (variance outcomeExp (scoreValue parameter) * variance outcomeExp outcomeValue) =
      1 := by
  rw [outcomeExp_covariance, outcomeExp_variance_score, outcomeExp_variance_outcome]
  field_simp

/-! ### The conditional rank accuracy -/

/-- The two-replica law of NOTE2 §5.4: two conditionally independent outcome draws. -/
def replicaExp : ExpFunctional (Bool × Bool) :=
  weightedExp (fun _ ↦ (1 : ℝ) / 4) (fun _ ↦ by norm_num)
    (by norm_num [Fintype.sum_prod_type, Fintype.sum_bool])

/-- Exact evaluation of the two-replica law on an arbitrary statistic. -/
theorem replicaExp_apply (statistic : Bool × Bool → ℝ) :
    replicaExp statistic =
      (statistic (false, false) + statistic (false, true) + statistic (true, false) +
        statistic (true, true)) / 4 := by
  simp only [replicaExp, weightedExp_apply, Fintype.sum_prod_type, Fintype.sum_bool]
  ring

/-- The ordering credit of NOTE2 §5.4: full credit for a strict win, half for a tie.  It is the
corpus case-control credit `empiricalAUCComparison`, with the same half-credit convention. -/
def comparisonScore (positiveScore negativeScore : ℝ) : ℝ :=
  empiricalAUCComparison positiveScore negativeScore

/-- The two-replica rank statistic of NOTE2 §5.4, read on a positive/negative replica pair. -/
def rankStatistic (parameter : ℝ) (pair : Bool × Bool) : ℝ :=
  if pair.1 = true ∧ pair.2 = false then
    comparisonScore (scoreValue parameter pair.1) (scoreValue parameter pair.2)
  else 0

/-- The rank accuracy of NOTE2 §5.4: the rank statistic normalized by `p(1 − p)`. -/
def rankAccuracy (parameter : ℝ) : ℝ :=
  replicaExp (rankStatistic parameter) /
    (outcomeExp outcomeValue * (1 - outcomeExp outcomeValue))

/-- **NOTE2 §6.3.** Conditional on a positive shared parameter the rank accuracy is exactly
one: the positive replica always carries the strictly larger score. -/
theorem rankAccuracy_eq_one (parameter : ℝ) (hparam : 0 < parameter) :
    rankAccuracy parameter = 1 := by
  have hnumer : replicaExp (rankStatistic parameter) = 1 / 4 := by
    rw [replicaExp_apply]
    simp only [rankStatistic, scoreValue, comparisonScore, empiricalAUCComparison]
    norm_num [hparam]
  rw [rankAccuracy, hnumer, outcomeExp_mean_outcome]
  norm_num

/-! ### The conditional slope and its divergent expectation -/

/-- The linear calibration slope of the conditional law: covariance over score variance. -/
def conditionalSlope (parameter : ℝ) : ℝ :=
  covariance outcomeExp (scoreValue parameter) outcomeValue /
    variance outcomeExp (scoreValue parameter)

/-- The slope in closed form, valid at every parameter value including zero, where both the
covariance and the variance vanish. -/
theorem conditionalSlope_closed (parameter : ℝ) :
    conditionalSlope parameter = parameter / 4 / (parameter ^ 2 / 4) := by
  rw [conditionalSlope, outcomeExp_covariance, outcomeExp_variance_score]

/-- **NOTE2 §6.3.** Conditional on a nonzero shared parameter the linear calibration slope is
exactly the reciprocal of that parameter. -/
theorem conditionalSlope_eq_inv (parameter : ℝ) (hparam : parameter ≠ 0) :
    conditionalSlope parameter = parameter⁻¹ := by
  rw [conditionalSlope_closed]
  field_simp

/-- The slope is a measurable function of the shared parameter. -/
theorem measurable_conditionalSlope : Measurable conditionalSlope := by
  have hclosed : conditionalSlope = fun parameter ↦ parameter / 4 / (parameter ^ 2 / 4) :=
    funext conditionalSlope_closed
  rw [hclosed]
  exact (measurable_id.div_const 4).div ((measurable_id.pow_const 2).div_const 4)

/-- **NOTE2 §6.3, the divergence.** The conditional slope is not integrable over the unit
interval, so the expected slope is not a finite real number even though every study reports a
finite slope. -/
theorem conditionalSlope_not_integrableOn :
    ¬IntegrableOn conditionalSlope (Set.Ioc 0 1) volume := by
  intro hintegrable
  have heqon : Set.EqOn conditionalSlope (fun parameter : ℝ ↦ parameter⁻¹) (Set.Ioc 0 1) :=
    fun parameter hparam ↦ conditionalSlope_eq_inv parameter (ne_of_gt hparam.1)
  have hinv : IntegrableOn (fun parameter : ℝ ↦ parameter⁻¹) (Set.Ioc 0 1) volume :=
    hintegrable.congr_fun heqon measurableSet_Ioc
  have hinterval :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0 : ℝ) ≤ 1)).mpr hinv
  rw [intervalIntegrable_inv_iff] at hinterval
  rcases hinterval with hzero | hnot
  · norm_num at hzero
  · refine hnot ?_
    rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    exact Set.mem_Icc.mpr ⟨le_refl 0, by norm_num⟩

/-- **NOTE2 §6.3, the divergence as an upper integral.** The upper integral of the conditional
slope over the unit interval is infinite. -/
theorem lintegral_conditionalSlope_eq_top :
    ∫⁻ parameter in Set.Ioc (0 : ℝ) 1,
      ENNReal.ofReal (conditionalSlope parameter) = ⊤ := by
  by_contra hfinite
  have hlt : (∫⁻ parameter in Set.Ioc (0 : ℝ) 1,
      ENNReal.ofReal (conditionalSlope parameter)) < ⊤ := lt_top_iff_ne_top.mpr hfinite
  have hnonneg : 0 ≤ᵐ[volume.restrict (Set.Ioc (0 : ℝ) 1)] conditionalSlope := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with parameter hparam
    show (0 : ℝ) ≤ conditionalSlope parameter
    rw [conditionalSlope_eq_inv parameter (ne_of_gt hparam.1)]
    exact inv_nonneg.mpr hparam.1.le
  have hfinint : HasFiniteIntegral conditionalSlope (volume.restrict (Set.Ioc (0 : ℝ) 1)) :=
    (hasFiniteIntegral_iff_ofReal hnonneg).mpr hlt
  exact conditionalSlope_not_integrableOn
    ⟨measurable_conditionalSlope.aestronglyMeasurable, hfinint⟩

end

end Descent.Portability.UnboundedSlopeExample
