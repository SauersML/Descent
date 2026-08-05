/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Calibrator.SelectionArchitecture
import Calibrator.ValidationStatistics

namespace Calibrator

/-!
# Selection Validation

Held-out model-comparison utilities for contrasting stabilizing and
fluctuating-selection summaries against observed trait-level summaries.

These objects consume explicit architecture summaries from
`SelectionArchitecture`; they do not infer portability from source `R²`.
-/

section SelectionValidation

/-- Observed trait-level summaries and their validation noise scales. -/
structure SelectionValidationModel where
  observedEffectCorrelation : ℝ
  observedSelectedVariance : ℝ
  effectCorrelationNoise : ℝ
  selectedVarianceNoise : ℝ
  effectCorrelationNoise_pos : 0 < effectCorrelationNoise
  selectedVarianceNoise_pos : 0 < selectedVarianceNoise

/-- **The class is inhabited.**  A theorem quantified over an uninhabited structure is
true and empty: kernel-checked, clean axiom report, no content.  This is the witness that
makes the theorems below statements about something. -/
noncomputable def SelectionValidationModel.witness : SelectionValidationModel where
  observedEffectCorrelation := 0
  observedSelectedVariance := 0
  effectCorrelationNoise := 1
  selectedVarianceNoise := 1
  effectCorrelationNoise_pos := by norm_num
  selectedVarianceNoise_pos := by norm_num

/-- A candidate model summarized only by the trait-level summaries it predicts
for validation. -/
structure SelectionModelSummary where
  predictedEffectCorrelation : ℝ
  predictedSelectedVariance : ℝ

/-- **The matching summary**: the candidate that predicts exactly what was
observed.

`SelectionValidationModel` carries a `witness` for the stated reason that a
theorem quantified over an uninhabited structure is true and empty;
`SelectionModelSummary` had none, so the same gap sat on the other half of every
statement here. This is the inhabitant, and it is the one the likelihood machinery
is oriented around rather than an arbitrary pair of reals.

    Empirical status: NOT AN EMPIRICAL CLAIM -- a relabelling of the validation
    model's own observations as predictions. It exhibits the exact-fit point; it
    does not assert that any selection model attains it. -/
def SelectionModelSummary.matching (validation : SelectionValidationModel) :
    SelectionModelSummary where
  predictedEffectCorrelation := validation.observedEffectCorrelation
  predictedSelectedVariance := validation.observedSelectedVariance

noncomputable instance SelectionModelSummary.instNonempty :
    Nonempty SelectionModelSummary :=
  ⟨SelectionModelSummary.matching SelectionValidationModel.witness⟩

/-- Validation log-likelihood of a candidate summary under Gaussian measurement
noise on the observed effect-correlation and selected-variance summaries.

    Empirical status: NOT AN EMPIRICAL CLAIM. The body is the DEFINITION of a Gaussian
    log-likelihood on two independent summaries: given the noise scales the validation model
    already carries, no population can make the sum of two `gaussianProfileLogLik` terms a
    different number. It is an objective a consumer optimizes, not a prediction about data.
    The empirical content sits in its INPUTS -- that the two summary errors are Gaussian,
    independent, and have the stated noise scales -- and those are hypotheses the
    `SelectionValidationModel` supplies. -/
noncomputable def selectionSummaryLogLik
    (validation : SelectionValidationModel)
    (summary : SelectionModelSummary) : ℝ :=
  gaussianProfileLogLik
      validation.observedEffectCorrelation
      summary.predictedEffectCorrelation
      validation.effectCorrelationNoise +
    gaussianProfileLogLik
      validation.observedSelectedVariance
      summary.predictedSelectedVariance
      validation.selectedVarianceNoise

/-- Absolute selected-variance miss of a candidate summary. -/
noncomputable def missedSelectedVariance
    (validation : SelectionValidationModel)
    (summary : SelectionModelSummary) : ℝ :=
  |validation.observedSelectedVariance - summary.predictedSelectedVariance|

theorem missedSelectedVariance_nonneg
    (validation : SelectionValidationModel)
    (summary : SelectionModelSummary) :
    0 ≤ missedSelectedVariance validation summary := by
  unfold missedSelectedVariance
  positivity

/-- **The matching summary misses by nothing**, so the floor of
`missedSelectedVariance_nonneg` is attained. A nonnegativity bound with no
attaining case is compatible with a strictly positive floor -- an irreducible
validation miss -- and this rules that out: the miss is zero for at least one
candidate, so any positive miss a real model shows is the model's, not the
metric's. -/
theorem missedSelectedVariance_matching (validation : SelectionValidationModel) :
    missedSelectedVariance validation (SelectionModelSummary.matching validation) = 0 := by
  unfold missedSelectedVariance SelectionModelSummary.matching
  simp

/-- Likelihood-ratio statistic comparing two selection summaries on the same
observed validation target.

    Empirical status: NOT AN EMPIRICAL CLAIM. The body is `likelihoodRatioStat` applied to
    two `selectionSummaryLogLik` values, which is the DEFINITION of the statistic and not a
    claim about its sampling distribution. Nothing here asserts that it is asymptotically
    chi-squared, or that any critical value calibrates a test -- that is where the empirical
    content of a likelihood-ratio test lives, and this declaration does not reach it. -/
noncomputable def selectionModelLRT
    (validation : SelectionValidationModel)
    (nullSummary altSummary : SelectionModelSummary) : ℝ :=
  likelihoodRatioStat
    (selectionSummaryLogLik validation nullSummary)
    (selectionSummaryLogLik validation altSummary)

theorem selectionSummaryLogLik_eq_of_matchedEffectCorrelation
    (validation : SelectionValidationModel)
    (summary : SelectionModelSummary)
    (hCorr :
      summary.predictedEffectCorrelation =
        validation.observedEffectCorrelation) :
    selectionSummaryLogLik validation summary =
      gaussianProfileLogLik
          validation.observedEffectCorrelation
          validation.observedEffectCorrelation
          validation.effectCorrelationNoise +
        gaussianProfileLogLik
          validation.observedSelectedVariance
          summary.predictedSelectedVariance
          validation.selectedVarianceNoise := by
  simp [selectionSummaryLogLik, hCorr]

theorem gaussianProfileLogLik_eq_missedSelectedVariance
    (validation : SelectionValidationModel)
    (summary : SelectionModelSummary) :
    gaussianProfileLogLik
        validation.observedSelectedVariance
        summary.predictedSelectedVariance
        validation.selectedVarianceNoise =
      -(missedSelectedVariance validation summary) ^ 2 /
          (2 * validation.selectedVarianceNoise) -
        Real.log (2 * Real.pi * validation.selectedVarianceNoise) / 2 := by
  have hsq :
      (missedSelectedVariance validation summary) ^ 2 =
        (validation.observedSelectedVariance -
            summary.predictedSelectedVariance) ^ 2 := by
    simp [missedSelectedVariance, sq_abs]
  unfold gaussianProfileLogLik
  rw [← hsq]

/-- Among summaries that fit the observed effect correlation equally well,
smaller missed selected variance gives strictly higher validation log-likelihood. -/
theorem selectionSummaryLogLik_strictAnti_missedSelectedVariance_of_matchedEffectCorrelation
    (validation : SelectionValidationModel)
    (summary₁ summary₂ : SelectionModelSummary)
    (hCorr₁ :
      summary₁.predictedEffectCorrelation =
        validation.observedEffectCorrelation)
    (hCorr₂ :
      summary₂.predictedEffectCorrelation =
        validation.observedEffectCorrelation)
    (hMiss :
      missedSelectedVariance validation summary₁ <
        missedSelectedVariance validation summary₂) :
    selectionSummaryLogLik validation summary₂ <
      selectionSummaryLogLik validation summary₁ := by
  have hsq :
      (missedSelectedVariance validation summary₁) ^ 2 <
        (missedSelectedVariance validation summary₂) ^ 2 := by
    have h₁ := missedSelectedVariance_nonneg validation summary₁
    have h₂ := missedSelectedVariance_nonneg validation summary₂
    nlinarith
  rw [selectionSummaryLogLik_eq_of_matchedEffectCorrelation validation summary₁ hCorr₁,
    selectionSummaryLogLik_eq_of_matchedEffectCorrelation validation summary₂ hCorr₂,
    gaussianProfileLogLik_eq_missedSelectedVariance,
    gaussianProfileLogLik_eq_missedSelectedVariance]
  have hDen : 0 < 2 * validation.selectedVarianceNoise := by
    nlinarith [validation.selectedVarianceNoise_pos]
  have hDiv :
      (missedSelectedVariance validation summary₁) ^ 2 /
          (2 * validation.selectedVarianceNoise) <
        (missedSelectedVariance validation summary₂) ^ 2 /
          (2 * validation.selectedVarianceNoise) := by
    exact div_lt_div_of_pos_right hsq hDen
  have hNeg :
      -(missedSelectedVariance validation summary₂) ^ 2 /
          (2 * validation.selectedVarianceNoise) <
        -(missedSelectedVariance validation summary₁) ^ 2 /
          (2 * validation.selectedVarianceNoise) := by
    have :
        -((missedSelectedVariance validation summary₂) ^ 2 /
            (2 * validation.selectedVarianceNoise)) <
          -((missedSelectedVariance validation summary₁) ^ 2 /
            (2 * validation.selectedVarianceNoise)) := by
      exact neg_lt_neg hDiv
    simpa only [neg_div] using this
  have hConst :
      -(missedSelectedVariance validation summary₂) ^ 2 /
            (2 * validation.selectedVarianceNoise) -
          Real.log (2 * Real.pi * validation.selectedVarianceNoise) / 2 <
        -(missedSelectedVariance validation summary₁) ^ 2 /
            (2 * validation.selectedVarianceNoise) -
          Real.log (2 * Real.pi * validation.selectedVarianceNoise) / 2 := by
    exact add_lt_add_right hNeg
      (-(Real.log (2 * Real.pi * validation.selectedVarianceNoise) / 2))
  have hTotal :
      gaussianProfileLogLik validation.observedEffectCorrelation
            validation.observedEffectCorrelation
            validation.effectCorrelationNoise +
          (-(missedSelectedVariance validation summary₂) ^ 2 /
              (2 * validation.selectedVarianceNoise) -
            Real.log (2 * Real.pi * validation.selectedVarianceNoise) / 2) <
        gaussianProfileLogLik validation.observedEffectCorrelation
            validation.observedEffectCorrelation
            validation.effectCorrelationNoise +
          (-(missedSelectedVariance validation summary₁) ^ 2 /
              (2 * validation.selectedVarianceNoise) -
            Real.log (2 * Real.pi * validation.selectedVarianceNoise) / 2) := by
    exact add_lt_add_left hConst
      (gaussianProfileLogLik validation.observedEffectCorrelation
        validation.observedEffectCorrelation validation.effectCorrelationNoise)
  exact hTotal

/-- Equal selected-variance miss gives equal validation likelihood when both summaries match the
observed effect correlation. -/
theorem selectionSummaryLogLik_eq_of_missedSelectedVariance_eq_of_matchedEffectCorrelation
    (validation : SelectionValidationModel)
    (summary₁ summary₂ : SelectionModelSummary)
    (hCorr₁ :
      summary₁.predictedEffectCorrelation = validation.observedEffectCorrelation)
    (hCorr₂ :
      summary₂.predictedEffectCorrelation = validation.observedEffectCorrelation)
    (hMiss :
      missedSelectedVariance validation summary₁ =
        missedSelectedVariance validation summary₂) :
    selectionSummaryLogLik validation summary₁ =
      selectionSummaryLogLik validation summary₂ := by
  rw [selectionSummaryLogLik_eq_of_matchedEffectCorrelation validation summary₁ hCorr₁,
    selectionSummaryLogLik_eq_of_matchedEffectCorrelation validation summary₂ hCorr₂,
    gaussianProfileLogLik_eq_missedSelectedVariance,
    gaussianProfileLogLik_eq_missedSelectedVariance, hMiss]

/-- **Exact validation ordering.** Among summaries that match the observed effect correlation,
the Gaussian validation likelihood ranks them in precisely the reverse order of their absolute
selected-variance misses.  The earlier strict-antitonicity theorem is the forward half; this iff
also proves that no other feature of such a summary can alter the ranking. -/
theorem selectionSummaryLogLik_lt_iff_missedSelectedVariance_gt_of_matchedEffectCorrelation
    (validation : SelectionValidationModel)
    (summary₁ summary₂ : SelectionModelSummary)
    (hCorr₁ :
      summary₁.predictedEffectCorrelation = validation.observedEffectCorrelation)
    (hCorr₂ :
      summary₂.predictedEffectCorrelation = validation.observedEffectCorrelation) :
    selectionSummaryLogLik validation summary₂ <
        selectionSummaryLogLik validation summary₁ ↔
      missedSelectedVariance validation summary₁ <
        missedSelectedVariance validation summary₂ := by
  constructor
  · intro hlikelihood
    by_contra hmiss
    have hle : missedSelectedVariance validation summary₂ ≤
        missedSelectedVariance validation summary₁ := le_of_not_gt hmiss
    rcases hle.eq_or_lt with hequal | hstrict
    · have hlikelihoodEq :=
        selectionSummaryLogLik_eq_of_missedSelectedVariance_eq_of_matchedEffectCorrelation
          validation summary₂ summary₁ hCorr₂ hCorr₁ hequal
      exact (ne_of_lt hlikelihood) hlikelihoodEq
    · have hopposite :=
        selectionSummaryLogLik_strictAnti_missedSelectedVariance_of_matchedEffectCorrelation
          validation summary₂ summary₁ hCorr₂ hCorr₁ hstrict
      exact lt_asymm hlikelihood hopposite
  · exact
      selectionSummaryLogLik_strictAnti_missedSelectedVariance_of_matchedEffectCorrelation
        validation summary₁ summary₂ hCorr₁ hCorr₂

/-- With a fixed alternative summary, the likelihood-ratio statistic strictly
increases as the null summary misses the observed selected variance by more,
provided both null summaries fit the observed effect correlation equally well. -/
theorem selectionModelLRT_strictMono_missedSelectedVariance_of_matchedEffectCorrelation
    (validation : SelectionValidationModel)
    (null₁ null₂ altSummary : SelectionModelSummary)
    (hCorr₁ :
      null₁.predictedEffectCorrelation =
        validation.observedEffectCorrelation)
    (hCorr₂ :
      null₂.predictedEffectCorrelation =
        validation.observedEffectCorrelation)
    (hMiss :
      missedSelectedVariance validation null₁ <
        missedSelectedVariance validation null₂) :
    selectionModelLRT validation null₁ altSummary <
      selectionModelLRT validation null₂ altSummary := by
  have hNull :
      selectionSummaryLogLik validation null₂ <
        selectionSummaryLogLik validation null₁ :=
    selectionSummaryLogLik_strictAnti_missedSelectedVariance_of_matchedEffectCorrelation
      validation null₁ null₂ hCorr₁ hCorr₂ hMiss
  unfold selectionModelLRT likelihoodRatioStat
  linarith

/-- **Exact LRT ordering at matched effect correlation.** With the alternative fixed, the
likelihood-ratio statistic ranks two null summaries exactly by their selected-variance miss.
This turns the validation prescription into an iff: a larger statistic means, and only means,
a worse selected-variance fit within the matched-correlation fiber. -/
theorem selectionModelLRT_lt_iff_missedSelectedVariance_lt_of_matchedEffectCorrelation
    (validation : SelectionValidationModel)
    (null₁ null₂ altSummary : SelectionModelSummary)
    (hCorr₁ :
      null₁.predictedEffectCorrelation = validation.observedEffectCorrelation)
    (hCorr₂ :
      null₂.predictedEffectCorrelation = validation.observedEffectCorrelation) :
    selectionModelLRT validation null₁ altSummary <
        selectionModelLRT validation null₂ altSummary ↔
      missedSelectedVariance validation null₁ <
        missedSelectedVariance validation null₂ := by
  change likelihoodRatioStat (selectionSummaryLogLik validation null₁)
      (selectionSummaryLogLik validation altSummary) <
        likelihoodRatioStat (selectionSummaryLogLik validation null₂)
          (selectionSummaryLogLik validation altSummary) ↔ _
  rw [likelihoodRatioStat_lt_iff_of_fixed_alt]
  exact selectionSummaryLogLik_lt_iff_missedSelectedVariance_gt_of_matchedEffectCorrelation
    validation null₁ null₂ hCorr₁ hCorr₂

end SelectionValidation

end Calibrator
