/-
Copyright (c) 2026 Sauers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sauers
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

/-- Likelihood-ratio statistic comparing a null and alternative fit.

    Empirical status: UNTESTED. -/
noncomputable def likelihoodRatioStat
    (logLNull logLAlt : ℝ) : ℝ :=
  -2 * (logLNull - logLAlt)

theorem likelihoodRatioStat_nonneg
    (logLNull logLAlt : ℝ)
    (hFit : logLNull ≤ logLAlt) :
    0 ≤ likelihoodRatioStat logLNull logLAlt := by
  unfold likelihoodRatioStat
  nlinarith

theorem likelihoodRatioStat_pos
    (logLNull logLAlt : ℝ)
    (hFit : logLNull < logLAlt) :
    0 < likelihoodRatioStat logLNull logLAlt := by
  unfold likelihoodRatioStat
  nlinarith

end GoodnessOfFit

end Calibrator
