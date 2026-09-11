/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.CounterfactualRegion

assert_below Descent.Decision Descent.Program

/-!
# The four-point law behind the exact zero-test boundary

A fair sign and an independent sign of prescribed mean, multiplied, give a four-point law on
which both variables have mean zero and variance one, the covariance is exactly the
prescribed mean, and the squared correlation is exactly its square. Consequently the squared
correlation of this family vanishes exactly when the prescribed mean vanishes: an exact
zero-test for the squared correlation of finitely supported laws is an exact zero-test for a
single real parameter.

This is the mathematical reduction inside UPT Theorem 10.2. The computability half of that
theorem, that no algorithm decides the vanishing of a uniformly computable real and therefore
none decides the vanishing of this squared correlation, is not formalized here: it needs a
development of computable reals and of uniformly computable finitely supported laws, which
this Mathlib pin does not provide. What is proved here is the part the manuscript's proof
supplies before it invokes the halting problem, stated exactly and unconditionally.

The law is an explicit `def` built with `PortabilityMasterTheorem.weightedExp`, its moments
are computed exactly against `Foundations.variance` and `Foundations.covariance`, and the
sign map is the one already used by `CounterfactualRegion`. The only hypothesis is the
manuscript's domain condition that the prescribed mean lies in the unit interval in absolute
value, which is what makes the four masses nonnegative.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.SquaredCorrelationZeroTest

open Foundations

noncomputable section

/-- The four-point law of a fair sign together with an independent sign whose mean is the
prescribed correlation. -/
def signPairLaw (corr : ℝ) (hcorr : |corr| ≤ 1) : ExpFunctional (Bool × Bool) :=
  weightedExp (fun draw ↦ (1 + corr * CounterfactualRegion.signOf draw.2) / 4)
    (by
      intro draw
      have habs := abs_le.1 hcorr
      by_cases hd : draw.2
      · simp only [CounterfactualRegion.signOf, if_pos hd, mul_one]
        linarith [habs.1]
      · simp only [CounterfactualRegion.signOf, if_neg hd, mul_neg_one]
        linarith [habs.2])
    (by
      simp [Fintype.sum_prod_type, Fintype.sum_bool, CounterfactualRegion.signOf]
      ring)

/-- The scored variable: the fair sign itself. -/
def scoreVar (draw : Bool × Bool) : ℝ := CounterfactualRegion.signOf draw.1

/-- The outcome variable: the product of the two signs. -/
def outcomeVar (draw : Bool × Bool) : ℝ :=
  CounterfactualRegion.signOf draw.1 * CounterfactualRegion.signOf draw.2

/-- The score is the sign map of `CounterfactualRegion` read at the first coordinate, so the
two modules share one sign convention rather than each carrying its own. -/
theorem scoreVar_eq_signOf (draw : Bool × Bool) :
    scoreVar draw = CounterfactualRegion.signOf draw.1 := rfl

/-- The outcome is the product of the two sign values of that same sign map. -/
theorem outcomeVar_eq_signOf_mul (draw : Bool × Bool) :
    outcomeVar draw =
      CounterfactualRegion.signOf draw.1 * CounterfactualRegion.signOf draw.2 := rfl

/-- Exact evaluation of the four-point law on an arbitrary statistic. -/
theorem signPairLaw_apply (corr : ℝ) (hcorr : |corr| ≤ 1) (statistic : Bool × Bool → ℝ) :
    signPairLaw corr hcorr statistic =
      ((1 + corr) * (statistic (true, true) + statistic (false, true)) +
        (1 - corr) * (statistic (true, false) + statistic (false, false))) / 4 := by
  simp [signPairLaw, weightedExp_apply, Fintype.sum_prod_type, Fintype.sum_bool,
    CounterfactualRegion.signOf]
  ring

/-- The score has mean zero. -/
theorem signPairLaw_mean_score (corr : ℝ) (hcorr : |corr| ≤ 1) :
    signPairLaw corr hcorr scoreVar = 0 := by
  rw [signPairLaw_apply]
  simp [scoreVar, CounterfactualRegion.signOf]

/-- The outcome has mean zero. -/
theorem signPairLaw_mean_outcome (corr : ℝ) (hcorr : |corr| ≤ 1) :
    signPairLaw corr hcorr outcomeVar = 0 := by
  rw [signPairLaw_apply]
  simp [outcomeVar, CounterfactualRegion.signOf]

/-- The score has variance one. -/
theorem signPairLaw_variance_score (corr : ℝ) (hcorr : |corr| ≤ 1) :
    variance (signPairLaw corr hcorr) scoreVar = 1 := by
  rw [variance, signPairLaw_mean_score, signPairLaw_apply]
  simp [scoreVar, CounterfactualRegion.signOf]
  ring

/-- The outcome has variance one. -/
theorem signPairLaw_variance_outcome (corr : ℝ) (hcorr : |corr| ≤ 1) :
    variance (signPairLaw corr hcorr) outcomeVar = 1 := by
  rw [variance, signPairLaw_mean_outcome, signPairLaw_apply]
  simp [outcomeVar, CounterfactualRegion.signOf]
  ring

/-- The covariance of score and outcome is exactly the prescribed correlation. -/
theorem signPairLaw_covariance (corr : ℝ) (hcorr : |corr| ≤ 1) :
    covariance (signPairLaw corr hcorr) scoreVar outcomeVar = corr := by
  rw [covariance, signPairLaw_mean_score, signPairLaw_mean_outcome, signPairLaw_apply]
  simp [scoreVar, outcomeVar, CounterfactualRegion.signOf]
  ring

/-- The squared correlation of this four-point law is exactly the square of the prescribed
correlation, which is the reduction UPT Theorem 10.2 uses. -/
theorem signPairLaw_squared_correlation (corr : ℝ) (hcorr : |corr| ≤ 1) :
    (covariance (signPairLaw corr hcorr) scoreVar outcomeVar) ^ 2 /
        (variance (signPairLaw corr hcorr) scoreVar *
          variance (signPairLaw corr hcorr) outcomeVar) = corr ^ 2 := by
  rw [signPairLaw_covariance, signPairLaw_variance_score, signPairLaw_variance_outcome]
  norm_num

/-- An exact zero-test for the squared correlation of this family is an exact zero-test for
the prescribed correlation itself. -/
theorem signPairLaw_squared_correlation_eq_zero_iff (corr : ℝ) (hcorr : |corr| ≤ 1) :
    (covariance (signPairLaw corr hcorr) scoreVar outcomeVar) ^ 2 /
        (variance (signPairLaw corr hcorr) scoreVar *
          variance (signPairLaw corr hcorr) outcomeVar) = 0 ↔ corr = 0 := by
  rw [signPairLaw_squared_correlation]
  exact pow_eq_zero_iff two_ne_zero

end

end Descent.Portability.SquaredCorrelationZeroTest
