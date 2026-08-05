/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Calibrator.Probability

namespace Calibrator

/-!
# Validation Statistics

Model-agnostic statistical utilities for validating mechanistic portability
predictions against observed summaries. These definitions do not recover target
behavior from source `R²`; they are generic goodness-of-fit tools.
-/

section GoodnessOfFit

/-- Gaussian profile log-likelihood for an observed scalar summary under a
candidate mean and noise variance.

    Empirical status: UNTESTED. -/
noncomputable def gaussianProfileLogLik
    (observed mean variance : ℝ) : ℝ :=
  -((observed - mean) ^ 2) / (2 * variance) -
    Real.log (2 * Real.pi * variance) / 2

/-- At zero variance both halves hit Mathlib junk: the quadratic term divides by zero and the
normalising `Real.log 0` is `0`, so the profile reports a log-likelihood of exactly zero -- the
value of a perfect fit -- where the true reading is a degenerate model. -/
theorem gaussianProfileLogLik_at_zero_variance_is_junk (observed mean : ℝ) :
    gaussianProfileLogLik observed mean 0 = 0 := by
  simp [gaussianProfileLogLik]


@[simp] theorem gaussianProfileLogLik_exactFit
    (observed variance : ℝ) :
    gaussianProfileLogLik observed observed variance =
      -Real.log (2 * Real.pi * variance) / 2 := by
  unfold gaussianProfileLogLik
  ring_nf

theorem gaussianProfileLogLik_strictAnti_sqResidual
    (observed variance mean₁ mean₂ : ℝ)
    (hVariance : 0 < variance)
    (hSq : (observed - mean₁) ^ 2 < (observed - mean₂) ^ 2) :
    gaussianProfileLogLik observed mean₂ variance <
      gaussianProfileLogLik observed mean₁ variance := by
  have hDen : 0 < 2 * variance := by positivity
  have hSqNeg :
      -(observed - mean₂) ^ 2 < -(observed - mean₁) ^ 2 := by
    nlinarith
  have hNeg :
      -((observed - mean₂) ^ 2 / (2 * variance)) <
        -((observed - mean₁) ^ 2 / (2 * variance)) := by
    have :
        -(observed - mean₂) ^ 2 / (2 * variance) <
          -(observed - mean₁) ^ 2 / (2 * variance) := by
      exact div_lt_div_of_pos_right hSqNeg hDen
    simpa only [neg_div] using this
  have hConst :
      -((observed - mean₂) ^ 2 / (2 * variance)) -
          Real.log (2 * Real.pi * variance) / 2 <
        -((observed - mean₁) ^ 2 / (2 * variance)) -
          Real.log (2 * Real.pi * variance) / 2 := by
    exact add_lt_add_right hNeg (-(Real.log (2 * Real.pi * variance) / 2))
  unfold gaussianProfileLogLik
  simpa only [neg_div] using hConst

/-- **Exact Gaussian fit ordering.** At positive variance, profile likelihood ranks candidate
means in precisely the reverse order of their squared residuals.  This is an iff, so no other
feature of the two means can change their ranking. -/
theorem gaussianProfileLogLik_lt_iff_sqResidual_gt
    (observed variance mean₁ mean₂ : ℝ) (hVariance : 0 < variance) :
    gaussianProfileLogLik observed mean₂ variance <
        gaussianProfileLogLik observed mean₁ variance ↔
      (observed - mean₁) ^ 2 < (observed - mean₂) ^ 2 := by
  constructor
  · intro hlikelihood
    have hDen : 0 < 2 * variance := by positivity
    unfold gaussianProfileLogLik at hlikelihood
    simp only [neg_div] at hlikelihood
    have hdiv : (observed - mean₁) ^ 2 / (2 * variance) <
        (observed - mean₂) ^ 2 / (2 * variance) := by
      linarith
    exact (div_lt_div_iff_of_pos_right hDen).mp hdiv
  · exact gaussianProfileLogLik_strictAnti_sqResidual observed variance mean₁ mean₂ hVariance

/-- **The profile log-likelihood is the log of a Gaussian density**, not a
formula that resembles one.

`gaussianProfileLogLik` is written as an algebraic expression, and every theorem
above is an ordering fact that would hold for `-(observed - mean)² · k` at any
positive `k`, constant offset included. So nothing above pins the `2 · variance`
in the denominator or the `log(2π · variance)/2` normaliser to a Gaussian
model, and the name would carry the modelling claim on its own. This identifies
the body with `ProbabilityTheory.gaussianPDFReal` at the same mean and variance,
which is what the name asserts.

Positive variance is required and is not cosmetic: at `variance = 0` the body
lands on the junk branch named at
`gaussianProfileLogLik_at_zero_variance_is_junk`, reporting the log-likelihood
of a perfect fit, while the density on the right is not a density at all.

This is also what makes the module's dependency on `Calibrator.Probability` a
real one rather than a declared one -- the Gaussian machinery it provides is
what the goodness-of-fit tools here are goodness-of-fit *to*.

    Empirical status: DERIVED. An identity between two closed forms, with no
    free parameter and nothing to measure. -/
theorem gaussianProfileLogLik_eq_log_gaussianPDFReal
    (observed mean : ℝ) (variance : NNReal) (hvariance : 0 < (variance : ℝ)) :
    gaussianProfileLogLik observed mean (variance : ℝ) =
      Real.log (ProbabilityTheory.gaussianPDFReal mean variance observed) := by
  have hnorm : 0 < 2 * Real.pi * (variance : ℝ) := by positivity
  have hsqrt : Real.sqrt (2 * Real.pi * (variance : ℝ)) ≠ 0 :=
    Real.sqrt_ne_zero'.mpr hnorm
  have hdensity : ProbabilityTheory.gaussianPDFReal mean variance observed =
      (Real.sqrt (2 * Real.pi * (variance : ℝ)))⁻¹ *
        Real.exp (-(observed - mean) ^ 2 / (2 * (variance : ℝ))) := rfl
  rw [hdensity, Real.log_mul (inv_ne_zero hsqrt) (Real.exp_ne_zero _), Real.log_inv,
    Real.log_sqrt hnorm.le, Real.log_exp]
  unfold gaussianProfileLogLik
  ring

/-- Likelihood-ratio statistic comparing a null and alternative fit.

    Empirical status: UNTESTED. -/
noncomputable def likelihoodRatioStat
    (logLNull logLAlt : ℝ) : ℝ :=
  -2 * (logLNull - logLAlt)

/-- Reference evaluation, at a point where the body is NONZERO.

The previous point was `likelihoodRatioStat 1 1 = 0`, and it rejected nothing: at
equal log-likelihoods the difference vanishes, so every rescaling `c * body`
satisfies the theorem exactly and the `-2` was pinned by nothing. A reference
value discriminates against a wrong constant factor if and only if the body is
nonzero there -- `scale_competitor_ne_iff`.

`1` and `3` separate the two arguments, so the point also fixes the ORIENTATION:
the null minus the alternative, not the reverse. A body carrying `-1` gives `2`
here and a body carrying `+2` gives `-4`. -/
theorem likelihoodRatioStat_at_reference_point :
    likelihoodRatioStat 1 3 = 4 := by
  norm_num [likelihoodRatioStat]


theorem likelihoodRatioStat_nonneg
    (logLNull logLAlt : ℝ)
    (hFit : logLNull ≤ logLAlt) :
    0 ≤ likelihoodRatioStat logLNull logLAlt := by
  unfold likelihoodRatioStat
  nlinarith

/-- A likelihood-ratio statistic is nonnegative exactly when the alternative fits at least as
well as the null. -/
theorem likelihoodRatioStat_nonneg_iff (logLNull logLAlt : ℝ) :
    0 ≤ likelihoodRatioStat logLNull logLAlt ↔ logLNull ≤ logLAlt := by
  unfold likelihoodRatioStat
  constructor <;> intro h <;> nlinarith

theorem likelihoodRatioStat_pos
    (logLNull logLAlt : ℝ)
    (hFit : logLNull < logLAlt) :
    0 < likelihoodRatioStat logLNull logLAlt := by
  unfold likelihoodRatioStat
  nlinarith

/-- A likelihood-ratio statistic is positive exactly when the alternative fits strictly better
than the null. -/
theorem likelihoodRatioStat_pos_iff (logLNull logLAlt : ℝ) :
    0 < likelihoodRatioStat logLNull logLAlt ↔ logLNull < logLAlt := by
  unfold likelihoodRatioStat
  constructor <;> intro h <;> nlinarith

/-- **Exact fixed-alternative ordering.** With one alternative held fixed, likelihood-ratio
statistics rank nulls in precisely the reverse order of their log-likelihoods. -/
theorem likelihoodRatioStat_lt_iff_of_fixed_alt
    (logLNull₁ logLNull₂ logLAlt : ℝ) :
    likelihoodRatioStat logLNull₁ logLAlt < likelihoodRatioStat logLNull₂ logLAlt ↔
      logLNull₂ < logLNull₁ := by
  unfold likelihoodRatioStat
  constructor <;> intro h <;> nlinarith

end GoodnessOfFit

end Calibrator
