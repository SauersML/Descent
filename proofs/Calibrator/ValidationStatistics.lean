import Calibrator.Probability

namespace Calibrator

/-!
# Validation Statistics

Model-agnostic statistical utilities for validating mechanistic portability
predictions against observed summaries. These definitions do not recover target
behavior from source `R²`; they are generic goodness-of-fit tools.
-/

section GoodnessOfFit

/-- Pearson chi-squared goodness-of-fit statistic for finitely many summary
bins. -/
noncomputable def chiSquaredStat
    {k : ℕ} (observed expected : Fin k → ℝ) : ℝ :=
  ∑ i, (observed i - expected i) ^ 2 / expected i

theorem chiSquaredStat_nonneg
    {k : ℕ} (observed expected : Fin k → ℝ)
    (hExpected : ∀ i, 0 < expected i) :
    0 ≤ chiSquaredStat observed expected := by
  unfold chiSquaredStat
  apply Finset.sum_nonneg
  intro i _
  exact div_nonneg (sq_nonneg _) (le_of_lt (hExpected i))

/-- Signed residual between an observed and predicted summary. -/
def residual (observed predicted : ℝ) : ℝ :=
  observed - predicted

@[simp] theorem residual_eq_sub (observed predicted : ℝ) :
    residual observed predicted = observed - predicted := by
  rfl

theorem residual_positive_of_observed_gt_predicted
    (observed predicted : ℝ)
    (h : predicted < observed) :
    0 < residual observed predicted := by
  unfold residual
  linarith

theorem residual_negative_of_observed_lt_predicted
    (observed predicted : ℝ)
    (h : observed < predicted) :
    residual observed predicted < 0 := by
  unfold residual
  linarith

/-- Gaussian profile log-likelihood for an observed scalar summary under a
candidate mean and noise variance. -/
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

/-- Likelihood-ratio statistic comparing a null and alternative fit. -/
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
