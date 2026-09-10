/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.ExactMetricEvaluation

assert_below Descent.Decision Descent.Program

namespace Descent.Portability.DemographyAccuracyFiber

/-!
# The complete accuracy fiber with a fixed genotype distribution

Two independent centered binary genotype coordinates suffice. The source phenotype and
deployed score are the first coordinate. In the target, only the direction of the additive
effect vector changes: `Yᵣ = √r G₁ + √(1-r) G₂`. For every `r ∈ [0,1]`, genotype law,
score variance, phenotype variance, and additive genetic variance remain fixed, with no
environmental noise, but target accuracy and the target/source accuracy ratio equal `r`.

A history label may be attached to this completion family. Its biological compatibility
requires that this genotype distribution is possible under that history and that the
effect direction is not specified by it. We do not claim this genotype law is generated
by every history. The obstruction is phenotype architecture absent from the observed input,
not random draws from a fully specified architecture law that should be integrated out.
-/

/-- Four equiprobable combinations of two independent centered binary genotypes. -/
noncomputable def genotypeLaw : FiniteReportLaw (Bool × Bool) where
  mass := fun _ ↦ 1 / 4
  mass_nonneg := by intro report; norm_num
  mass_sum := by norm_num [Fintype.sum_prod_type, Fintype.sum_bool]

/-- The first centered genotype, used by the fixed source score. -/
def firstGenotype (report : Bool × Bool) : ℝ := if report.1 then 1 else -1

/-- The second independent centered genotype. -/
def secondGenotype (report : Bool × Bool) : ℝ := if report.2 then 1 else -1

/-- The deployed score is fixed throughout the target architecture family. -/
def score : Bool × Bool → ℝ := firstGenotype

/-- A purely additive target phenotype. The family changes effects, not the genotype law. -/
noncomputable def phenotype (r : ℝ) (report : Bool × Bool) : ℝ :=
  Real.sqrt r * firstGenotype report + Real.sqrt (1 - r) * secondGenotype report

theorem expectation_four (metric : Bool × Bool → ℝ) :
    genotypeLaw.expectation metric =
      (metric (false, false) + metric (false, true) +
        metric (true, false) + metric (true, true)) / 4 := by
  simp [FiniteReportLaw.expectation, genotypeLaw, Fintype.sum_prod_type]
  ring

theorem score_mean : genotypeLaw.expectation score = 0 := by
  rw [expectation_four]
  norm_num [score, firstGenotype]

theorem phenotype_mean (r : ℝ) : genotypeLaw.expectation (phenotype r) = 0 := by
  rw [expectation_four]
  simp [phenotype, firstGenotype, secondGenotype]
  ring

/-- Population score variance, computed from the actual finite genotype law. -/
noncomputable def scoreVariance : ℝ :=
  genotypeLaw.variance score

/-- Population phenotype variance under one additive effect direction. -/
noncomputable def outcomeVariance (r : ℝ) : ℝ :=
  genotypeLaw.variance (phenotype r)

/-- Population score/phenotype covariance under the same law. -/
noncomputable def predictiveCovariance (r : ℝ) : ℝ :=
  genotypeLaw.covariance score (phenotype r)

theorem scoreVariance_eq_one : scoreVariance = 1 := by
  unfold scoreVariance FiniteReportLaw.variance FiniteReportLaw.covariance
  rw [score_mean, expectation_four]
  norm_num [score, firstGenotype]

theorem outcomeVariance_eq_squares (r : ℝ) :
    outcomeVariance r = Real.sqrt r ^ 2 + Real.sqrt (1 - r) ^ 2 := by
  unfold outcomeVariance FiniteReportLaw.variance FiniteReportLaw.covariance
  rw [phenotype_mean, expectation_four]
  simp [phenotype, firstGenotype, secondGenotype]
  ring

theorem outcomeVariance_eq_one (r : ℝ) (hr : 0 ≤ r) (hr1 : r ≤ 1) :
    outcomeVariance r = 1 := by
  rw [outcomeVariance_eq_squares, Real.sq_sqrt hr,
    Real.sq_sqrt (sub_nonneg.mpr hr1)]
  ring

theorem predictiveCovariance_eq_sqrt (r : ℝ) :
    predictiveCovariance r = Real.sqrt r := by
  unfold predictiveCovariance FiniteReportLaw.covariance
  rw [score_mean, phenotype_mean, expectation_four]
  simp [score, phenotype, firstGenotype, secondGenotype]
  ring

/-- Squared correlation, whose denominator is proved positive throughout the family. -/
noncomputable def accuracy (r : ℝ) : ℝ :=
  predictiveCovariance r ^ 2 / (scoreVariance * outcomeVariance r)

/-- Exact accuracy at every effect direction, with both variances fixed at one. -/
theorem accuracy_eq (r : ℝ) (hr : 0 ≤ r) (hr1 : r ≤ 1) :
    accuracy r = r := by
  unfold accuracy
  rw [predictiveCovariance_eq_sqrt, Real.sq_sqrt hr, scoreVariance_eq_one,
    outcomeVariance_eq_one r hr hr1]
  ring

/-- The general partial metric evaluator returns the exact value, with definedness proved. -/
theorem squaredCorrelation_eq (r : ℝ) (hr : 0 ≤ r) (hr1 : r ≤ 1) :
    genotypeLaw.squaredCorrelation score (phenotype r) = some r := by
  change (if 0 < scoreVariance ∧ 0 < outcomeVariance r then
    some (accuracy r) else none) = some r
  rw [scoreVariance_eq_one, outcomeVariance_eq_one r hr hr1, accuracy_eq r hr hr1]
  norm_num

/-- At the source effect direction, phenotype and deployed score coincide pointwise. -/
theorem source_phenotype_eq_score : phenotype 1 = score := by
  funext report
  simp [phenotype, score]

theorem source_accuracy : accuracy 1 = 1 := accuracy_eq 1 (by norm_num) (by norm_num)

/-- The portability ratio is also exactly `r`, since the fixed source accuracy is one. -/
theorem portability_ratio_eq (r : ℝ) (hr : 0 ≤ r) (hr1 : r ≤ 1) :
    accuracy r / accuracy 1 = r := by
  rw [accuracy_eq r hr hr1, source_accuracy, div_one]

/-- No history-only point prediction is exact for all unspecified effect directions at
even one compatible fixed history. The universal quantifier is over completions. -/
theorem no_history_only_exact_accuracy {History : Type*} (history : History) :
    ¬ ∃ predict : History → ℝ,
      ∀ r : ℝ, 0 ≤ r → r ≤ 1 → accuracy r = predict history := by
  rintro ⟨predict, h⟩
  have hzero := h 0 (by norm_num) (by norm_num)
  have hone := h 1 (by norm_num) (by norm_num)
  rw [accuracy_eq 0 (by norm_num) (by norm_num)] at hzero
  rw [source_accuracy] at hone
  linarith

/-- Every point prediction has error at least one half on an attained endpoint. -/
theorem endpoint_error_at_least_half (prediction : ℝ) :
    1 / 2 ≤ max (|accuracy 0 - prediction|) (|accuracy 1 - prediction|) := by
  rw [accuracy_eq 0 (by norm_num) (by norm_num), source_accuracy]
  have hone : 1 - prediction ≤ |1 - prediction| := le_abs_self _
  have hzero' : prediction ≤ |0 - prediction| := by
    simpa using neg_le_abs (0 - prediction)
  have hl := le_max_left (|0 - prediction|) (|1 - prediction|)
  have hr := le_max_right (|0 - prediction|) (|1 - prediction|)
  linarith

/-- The midpoint achieves the sharp error bound throughout the complete fiber. -/
theorem midpoint_error_le_half (r : ℝ) (hr : 0 ≤ r) (hr1 : r ≤ 1) :
    |accuracy r - 1 / 2| ≤ 1 / 2 := by
  rw [accuracy_eq r hr hr1]
  exact abs_le.mpr ⟨by linarith, by linarith⟩

end Descent.Portability.DemographyAccuracyFiber
