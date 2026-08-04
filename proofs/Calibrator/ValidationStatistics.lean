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

/-- Likelihood-ratio statistic comparing a null and alternative fit.

    Empirical status: UNTESTED. -/
noncomputable def likelihoodRatioStat
    (logLNull logLAlt : ℝ) : ℝ :=
  -2 * (logLNull - logLAlt)

/-- Reference evaluation.  The value is computed through the definitions this body calls, but
the theorem states a number: an inequality or an invariance leaves a family of bodies
satisfying it, and a value does not. -/
theorem likelihoodRatioStat_at_reference_point :
    likelihoodRatioStat 1 1 = 0 := by
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
