/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Foundations.Probability

assert_below Descent.Coalescent Descent.Pangenome Descent.PopGen Descent.Spectral Descent.Blindness
assert_below Descent.Conditionals Descent.Portability Descent.Decision Descent.Program

namespace Descent.Foundations

open MeasureTheory

/-!
# Bernoulli losses: Brier score, log loss, and the divergence between them

The loss functions for a binary outcome, and the facts that connect them. A prediction `q`
against a truth `p` is scored either by squared error -- the Brier score, whose expected value
under `Y ~ Bernoulli(p)` is `expectedBrierScore` -- or by log loss. In both cases the regret of
a prediction against the truth is a divergence: `brier_regret_pointwise` makes it the squared
error `(q - p)^2`, and `logLoss_regret_eq_kl_pointwise` makes it the Bernoulli KL divergence.
That pair is what makes both losses proper.

None of this carries a score between populations and none of it belongs to any one programme.
It is arithmetic on one outcome and one prediction, which is why it sits here rather than in a
chapter that consumes it: the present-day moment results in `Portability` and the
oracle-and-regret argument in `Program` are both stated in these terms, and neither is below
the other.

Two bodies are junk at a boundary and say so rather than leaving it to be discovered.
`bernoulliKLReal_certain_forecast_is_junk` records that a certain-and-wrong forecast returns a
finite negative number exactly where the regret is unbounded, so consumers must require
`0 < q`. The numerical warning in the docstring of `bernoulliKLReal` is part of its contract:
the body must not be evaluated as written near `p = q`.
-/

/-- The Brier Score measures squared error between predicted probability and outcome.
    For a binary outcome y ∈ {0, 1} and prediction p ∈ [0, 1]:
    BS(p, y) = (y - p)²

    This is the standard proper scoring rule for probability forecasts. -/
noncomputable def brierScore (p : ℝ) (y : ℝ) : ℝ := (y - p) ^ 2

/-- The score is never negative: it is a squared error, so a body that lost the square would
fail here wherever the prediction overshoots. -/
theorem brierScore_nonneg (p y : ℝ) : 0 ≤ brierScore p y := by
  unfold brierScore; positivity

/-- **Anchors of the Brier score.** A confident correct call scores `0`, a confident wrong call
scores `1`, and the uninformative call scores `1/4`. Three numbers rather than one, because a
single anchor is met by many wrong bodies. -/
theorem brierScore_anchors :
    brierScore 1 1 = 0 ∧ brierScore 0 1 = 1 ∧ brierScore (1 / 2) 1 = 1 / 4 := by
  refine ⟨?_, ?_, ?_⟩ <;> unfold brierScore <;> norm_num

/-- The score vanishes exactly on a correct point prediction. -/
theorem brierScore_eq_zero_iff (p y : ℝ) : brierScore p y = 0 ↔ p = y := by
  unfold brierScore
  rw [pow_eq_zero_iff two_ne_zero, sub_eq_zero]
  exact eq_comm

/-- Expected Brier Score when Y is Bernoulli(π).
    E[(Y - p)²] = π(1-p)² + (1-π)p²

    This is the loss we want to minimize by choosing p optimally. -/
noncomputable def expectedBrierScore (p : ℝ) (π : ℝ) : ℝ :=
  π * (1 - p) ^ 2 + (1 - π) * p ^ 2

/-- The Brier score at the true probability simplifies to π(1-π),
    which is the irreducible variance of a Bernoulli(π) variable. -/
theorem brierScore_at_true_prob (π : ℝ) :
    expectedBrierScore π π = π * (1 - π) := by
  unfold expectedBrierScore
  ring

/-- Exact population Brier risk of a calibrated predictor (`q = η`). -/
noncomputable def exactBrierRiskOfCalibrated {Z : Type*} [MeasurableSpace Z]
    (μ : Measure Z) (η : Z → ℝ) : ℝ :=
  ∫ z, expectedBrierScore (η z) (η z) ∂μ

/-- Exact calibrated Brier-risk identity: pointwise Bernoulli variance integrated over the
    population. -/
theorem exactBrierRiskOfCalibrated_eq_integral {Z : Type*} [MeasurableSpace Z]
    (μ : Measure Z) (η : Z → ℝ) :
    exactBrierRiskOfCalibrated μ η = ∫ z, η z * (1 - η z) ∂μ := by
  unfold exactBrierRiskOfCalibrated
  refine integral_congr_ae ?_
  filter_upwards with z
  simp [brierScore_at_true_prob]

/-- Bernoulli log-loss (cross-entropy) at truth `p` and prediction `q`. -/
noncomputable def bernoulliLogLoss (p q : ℝ) : ℝ :=
  -(p * Real.log q + (1 - p) * Real.log (1 - q))

/-- Real-valued Bernoulli KL divergence formula.

**Numerical warning -- this body must not be evaluated as written near `p = q`.**
The divergence is second order in `p - q` (`KL ≈ (p-q)² / (2q(1-q))`), but the body
computes it as a sum of two logarithms each of which is first order in `p - q`, so
the first-order parts cancel between the summands and the answer is what survives
the cancellation. Measured float64 against a 60-digit reference, arguments rounded
to float64 first so input representation cannot be charged to the formula, along
`q = p + δ` for `p ∈ {0.001, 0.1, 0.5, 0.9}` and `δ` from `10⁻²` down to `10⁻¹⁴`:
**34 of 52 cells exceed 1e-6 relative error, worst 2.4·10⁹.**

That region is not exotic -- it is the calibrated regime, where a forecaster is
nearly right and the divergence is being used as a small penalty.

**Correction, from measuring rather than reasoning.** An earlier revision of this
warning said the form "cannot be rescued by `log1p`, because the cancellation is
between the two terms and not inside either one". The first clause was wrong. The
reasoning behind it was right as far as it went -- there IS a residual
cancellation between the summands, and `log1p` does not remove it -- but it does
remove a much larger one INSIDE each logarithm, and the measured difference is
enormous. On a widened grid (`q = p ± δ`, `p ∈ {0.001, 0.01, 0.1, 0.5, 0.9}`,
`δ` from `10⁻²` to `10⁻¹⁴`, 104 cells):

    body as written                    worst 4.0·10¹⁰   70/104 cells over 1e-6
    log1p form, exactly equal          worst 1.1·10⁻²   21/104 cells over 1e-6

Twelve orders of magnitude in the worst case and a third of the failing region.
`bernoulliKLReal_eq_logOnePlus`, in `Descent.Program.Conclusions`, proves the two
forms equal, so this is a free substitution and not an approximation.
Implementations must use it. That lemma consumes this definition rather than the
other way round, which is why it is stated there and not here.

What survives is a genuine domain restriction and not a large one: below
`|p - q| ≈ 10⁻⁶` even the stable form loses relative accuracy, because the
divergence is quadratic in a difference whose linear parts cancel between the
summands and no rewrite in elementary functions removes that. A consumer ranking
two nearly calibrated forecasters closer together than that is reading noise
either way; it is the interval that shrank by ten orders of magnitude, not the
existence of one. -/
noncomputable def bernoulliKLReal (p q : ℝ) : ℝ :=
  p * Real.log (p / q) + (1 - p) * Real.log ((1 - p) / (1 - q))

/-- **The Bernoulli KL divergence against a certain forecast, named.** A forecast of zero
probability for an outcome that can occur has infinite KL divergence -- that is the whole content
of the divergence as a penalty. The ratio `p / 0` is junk-zero, `Real.log 0` is junk-zero, and
the first term vanishes, leaving `(1 - p) * log (1 - p)`, which is FINITE AND NEGATIVE for
`p` in `(0, 1)`. So the certificate that is supposed to bound log-loss regret from above returns
a negative number exactly where the regret is unbounded. Consumers must require `0 < q`. -/
theorem bernoulliKLReal_certain_forecast_is_junk (p : ℝ) :
    bernoulliKLReal p 0 = (1 - p) * Real.log (1 - p) := by
  unfold bernoulliKLReal
  simp

/-- Pointwise log-loss regret equals Bernoulli KL. -/
theorem logLoss_regret_eq_kl_pointwise (p q : ℝ)
    (hp0 : 0 < p) (hp1 : p < 1) (hq0 : 0 < q) (hq1 : q < 1) :
    bernoulliLogLoss p q - bernoulliLogLoss p p = bernoulliKLReal p q := by
  have hp_ne : p ≠ 0 := hp0.ne'
  have hq_ne : q ≠ 0 := hq0.ne'
  have hp1_ne : 1 - p ≠ 0 := sub_ne_zero.mpr (ne_of_lt hp1).symm
  have hq1_ne : 1 - q ≠ 0 := sub_ne_zero.mpr (ne_of_lt hq1).symm
  unfold bernoulliLogLoss bernoulliKLReal
  rw [Real.log_div hp_ne hq_ne, Real.log_div hp1_ne hq1_ne]
  ring

/-- Pointwise Brier regret identity (L² certificate). -/
theorem brier_regret_pointwise (p q : ℝ) :
    expectedBrierScore q p - expectedBrierScore p p = (q - p) ^ 2 := by
  unfold expectedBrierScore
  ring

/-- Pointwise Bernoulli Brier risk at true parameter `η` and prediction `q`. -/
noncomputable def brierBernoulliRisk (η q : ℝ) : ℝ :=
  expectedBrierScore q η

end Descent.Foundations
