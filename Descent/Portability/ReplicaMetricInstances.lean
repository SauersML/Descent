/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.ReplicaDomainCertificate
import Descent.Portability.ChronologyReportLaw
import Descent.Portability.ReplicaMomentCompleteness
import Mathlib.Algebra.MvPolynomial.CommRing

assert_below Descent.Decision Descent.Program

/-!
# Concrete population metrics as bounded replica ratios

NOTE 2 section 5.4 instantiates the replica-domain compiler of sections 5.1 and 5.2 for the
metrics a report actually carries. This module derives every instance from the corpus
definitions of the metrics, not from restatements of them.

Squared correlation. For a score and an outcome in the unit interval, `correlationNumerator`
and `correlationDenominator` are `N = 16 C_SY²` and `D = 16 V_S V_Y` of NOTE 2 (21), built from
the corpus `FiniteReportLaw.covariance` and `variance`. `correlationNumerator_le_denominator`
is Cauchy–Schwarz, `correlationDenominator_le_one` uses `variance_le_quarter`, and
`squaredCorrelation_eq_guardedRatio` shows that the corpus `squaredCorrelation` is exactly the
ratio `N / D` on `D > 0` and undefined elsewhere. `expectation_squaredCorrelation_eq_tsum` is
NOTE 2 (15) for it and `squaredCorrelation_certificate` is Theorem 4, NOTE 2 (18), for the
corpus skip-undefined average `conditionalMetric` over a finite law of study contexts.

AUC. `binaryAUCNumerator_eq_twoReplica` reads the corpus half-credit ranking numerator as an
expectation over two conditionally independent replicas under the corpus product law
`FiniteGeneticTransition.piLaw`. `aucNumerator` and `aucDenominator` are `N = 4A` and
`D = 4p(1 - p)`, with `0 ≤ N ≤ D ≤ 1`, and `binaryAUC_eq_guardedRatio` identifies the corpus
`binaryAUC` with their guarded ratio, so (15) and (18) apply to it as well.

## Empirical status

None. The bodies here are algebra: every quantity is a finite sum or product of the masses of
a stipulated finite law, and every claim is an identity or an inequality between such sums, so
no measurement can bear on them.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.ReplicaMetricInstances

open PositiveRatioExpansion SublawReportCertificate ReplicaDomainCertificate

noncomputable section

variable {Context : Type*} [Fintype Context]

/-! ### Guarded ratio partial metrics -/

section GuardedRatio

/-- A partial metric defined as a ratio exactly where its denominator is positive reads, when
the undefined value is replaced by zero, as the corpus zero-extended ratio. -/
theorem getD_guardedRatio (num den : Context → ℝ) (context : Context) :
    (if 0 < den context then some (num context / den context) else none).getD 0 =
      ratioOnDefined num den context := by
  unfold ratioOnDefined
  split_ifs <;> rfl

/-- The corpus skip-undefined average of a guarded ratio partial metric is the conditional
expectation of the zero-extended ratio given that the denominator is positive, whenever that
event carries positive mass. -/
theorem conditionalMetric_guardedRatio (law : FiniteReportLaw Context) (num den : Context → ℝ)
    (hmass : 0 < law.expectation (definedIndicator fun context ↦ 0 < den context)) :
    law.conditionalMetric (fun context ↦
        if 0 < den context then some (num context / den context) else none) =
      some (conditionalExpectation law (fun context ↦ 0 < den context)
        (ratioOnDefined num den)) := by
  have hdefined : law.definedMass (fun context ↦
      if 0 < den context then some (num context / den context) else none) =
        law.expectation (definedIndicator fun context ↦ 0 < den context) := by
    unfold FiniteReportLaw.definedMass
    congr 1
    funext context
    by_cases hpos : 0 < den context <;> simp [definedIndicator, hpos]
  have hweighted : law.weightedDefinedMetric (fun context ↦
      if 0 < den context then some (num context / den context) else none) =
        law.expectation (ratioOnDefined num den) := by
    unfold FiniteReportLaw.weightedDefinedMetric
    congr 1
    funext context
    exact getD_guardedRatio num den context
  unfold FiniteReportLaw.conditionalMetric conditionalExpectation
  rw [hdefined, hweighted, if_neg hmass.ne', defined_ratio_expectation]

/-- **NOTE 2 equation (15) for a guarded ratio partial metric.** When `0 ≤ num ≤ den ≤ 1`, the
expectation of the partial metric read as zero off its domain is the series of expectations of
`num * (1 - den) ^ power`. -/
theorem expectation_guardedRatio_eq_tsum (law : FiniteReportLaw Context) (num den : Context → ℝ)
    (hnum : ∀ context, 0 ≤ num context) (hle : ∀ context, num context ≤ den context)
    (hden : ∀ context, den context ≤ 1) :
    law.expectation (fun context ↦
        (if 0 < den context then some (num context / den context) else none).getD 0) =
      ∑' power : ℕ, law.expectation (fun context ↦ num context * (1 - den context) ^ power) := by
  simp only [getD_guardedRatio]
  exact expectation_ratioOnDefined_eq_tsum law num den hnum hle hden

/-- **NOTE 2 equation (18) for a guarded ratio partial metric.** With a tolerance dominating
the unresolved definedness mass and positive retained mass, the corpus skip-undefined average
of the partial metric is defined, equals the conditional expectation of the zero-extended ratio
on the defined event, and lies in the certified interval of Theorem 4. -/
theorem guardedRatio_certificate (law : FiniteReportLaw Context) (num den : Context → ℝ)
    (hnum : ∀ context, 0 ≤ num context) (hle : ∀ context, num context ≤ den context)
    (hden : ∀ context, den context ≤ 1) (terms : ℕ) (tolerance : ℝ)
    (htolerance : unresolvedMass law den terms ≤ tolerance)
    (hretained : 0 < retainedMass law den terms) :
    law.conditionalMetric (fun context ↦
        if 0 < den context then some (num context / den context) else none) =
      some (conditionalExpectation law (fun context ↦ 0 < den context)
        (ratioOnDefined num den)) ∧
    (retainedNumerator law num den terms / (retainedMass law den terms + tolerance) ≤
        conditionalExpectation law (fun context ↦ 0 < den context) (ratioOnDefined num den) ∧
      conditionalExpectation law (fun context ↦ 0 < den context) (ratioOnDefined num den) ≤
        (retainedNumerator law num den terms + tolerance) /
          (retainedMass law den terms + tolerance)) := by
  have hdenNonneg : ∀ context, 0 ≤ den context := fun context ↦
    (hnum context).trans (hle context)
  have hmass : 0 < law.expectation (definedIndicator fun context ↦ 0 < den context) := by
    rw [defined_mass_partition law den hdenNonneg terms]
    linarith [unresolvedMass_nonneg law den hden terms]
  exact ⟨conditionalMetric_guardedRatio law num den hmass,
    replica_certificate law num den hnum hle hden terms tolerance htolerance hretained⟩

end GuardedRatio

/-! ### Squared correlation -/

section Correlation

variable {State : Type*} [Fintype State]

/-- **NOTE 2 equation (21), numerator.** Sixteen times the squared score-outcome covariance of
the population law. -/
def correlationNumerator (law : FiniteReportLaw State) (score outcome : State → ℝ) : ℝ :=
  16 * law.covariance score outcome ^ 2

/-- **NOTE 2 equation (21), denominator.** Sixteen times the product of the score variance and
the outcome variance of the population law. -/
def correlationDenominator (law : FiniteReportLaw State) (score outcome : State → ℝ) : ℝ :=
  16 * (law.variance score * law.variance outcome)

/-- An observable with values in the unit interval has variance at most one quarter: its
second moment is at most its mean `m`, and `m - m ^ 2 ≤ 1 / 4`. -/
theorem variance_le_quarter (law : FiniteReportLaw State) (value : State → ℝ)
    (hlow : ∀ state, 0 ≤ value state) (hhigh : ∀ state, value state ≤ 1) :
    law.variance value ≤ 1 / 4 := by
  have hsquare : law.expectation (fun state ↦ value state ^ 2) ≤ law.expectation value :=
    BellmanReportBounds.expectation_mono law _ _ fun state ↦ by
      nlinarith [mul_nonneg (hlow state) (sub_nonneg.mpr (hhigh state))]
  rw [FiniteReportLaw.variance_eq_rawMoments]
  nlinarith [sq_nonneg (law.expectation value - 1 / 2)]

/-- The correlation numerator is nonnegative. -/
theorem correlationNumerator_nonneg (law : FiniteReportLaw State) (score outcome : State → ℝ) :
    0 ≤ correlationNumerator law score outcome :=
  mul_nonneg (by norm_num) (sq_nonneg _)

/-- **NOTE 2 section 5.4, Cauchy–Schwarz.** The correlation numerator never exceeds the
correlation denominator. -/
theorem correlationNumerator_le_denominator (law : FiniteReportLaw State)
    (score outcome : State → ℝ) :
    correlationNumerator law score outcome ≤ correlationDenominator law score outcome := by
  have hcauchy := law.covariance_sq_le_variance_mul score outcome
  unfold correlationNumerator correlationDenominator
  linarith

/-- **NOTE 2 section 5.4.** For a score and an outcome in the unit interval the correlation
denominator is at most one, because each variance is at most one quarter. -/
theorem correlationDenominator_le_one (law : FiniteReportLaw State) (score outcome : State → ℝ)
    (hscore0 : ∀ state, 0 ≤ score state) (hscore1 : ∀ state, score state ≤ 1)
    (houtcome0 : ∀ state, 0 ≤ outcome state) (houtcome1 : ∀ state, outcome state ≤ 1) :
    correlationDenominator law score outcome ≤ 1 := by
  have hscore := variance_le_quarter law score hscore0 hscore1
  have houtcome := variance_le_quarter law outcome houtcome0 houtcome1
  have hproduct := mul_nonneg (sub_nonneg.mpr hscore) (law.variance_nonneg outcome)
  unfold correlationDenominator
  nlinarith

/-- The correlation denominator is positive exactly when both variances are positive. -/
theorem correlationDenominator_pos_iff (law : FiniteReportLaw State)
    (score outcome : State → ℝ) :
    0 < correlationDenominator law score outcome ↔
      0 < law.variance score ∧ 0 < law.variance outcome := by
  have hscore := law.variance_nonneg score
  have houtcome := law.variance_nonneg outcome
  unfold correlationDenominator
  constructor
  · intro hpos
    refine ⟨lt_of_le_of_ne hscore fun hzero ↦ ?_, lt_of_le_of_ne houtcome fun hzero ↦ ?_⟩
    · rw [← hzero, zero_mul, mul_zero] at hpos
      exact lt_irrefl 0 hpos
    · rw [← hzero, mul_zero, mul_zero] at hpos
      exact lt_irrefl 0 hpos
  · intro hboth
    have hprod := mul_pos hboth.1 hboth.2
    linarith

/-- **NOTE 2 section 5.4.** The corpus squared correlation is the guarded ratio of the
numerator and the denominator of NOTE 2 (21): defined exactly where the denominator is
positive, and equal there to their ratio. -/
theorem squaredCorrelation_eq_guardedRatio (law : FiniteReportLaw State)
    (score outcome : State → ℝ) :
    law.squaredCorrelation score outcome =
      if 0 < correlationDenominator law score outcome then
        some (correlationNumerator law score outcome / correlationDenominator law score outcome)
      else none := by
  unfold FiniteReportLaw.squaredCorrelation
  by_cases hboth : 0 < law.variance score ∧ 0 < law.variance outcome
  · rw [if_pos hboth, if_pos ((correlationDenominator_pos_iff law score outcome).mpr hboth)]
    unfold correlationNumerator correlationDenominator
    rw [mul_div_mul_left _ _ (by norm_num : (16 : ℝ) ≠ 0)]
  · rw [if_neg hboth,
      if_neg fun hpos ↦ hboth ((correlationDenominator_pos_iff law score outcome).mp hpos)]

/-- **NOTE 2 equation (15) for squared correlation.** Over a finite law of study contexts, the
expected population squared correlation, read as zero where it is undefined, is the series of
expectations of `N * (1 - D) ^ power` with `N` and `D` of NOTE 2 (21). -/
theorem expectation_squaredCorrelation_eq_tsum (law : FiniteReportLaw Context)
    (population : Context → FiniteReportLaw State) (score outcome : State → ℝ)
    (hscore0 : ∀ state, 0 ≤ score state) (hscore1 : ∀ state, score state ≤ 1)
    (houtcome0 : ∀ state, 0 ≤ outcome state) (houtcome1 : ∀ state, outcome state ≤ 1) :
    law.expectation (fun context ↦
        ((population context).squaredCorrelation score outcome).getD 0) =
      ∑' power : ℕ, law.expectation (fun context ↦
        correlationNumerator (population context) score outcome *
          (1 - correlationDenominator (population context) score outcome) ^ power) := by
  simp only [squaredCorrelation_eq_guardedRatio]
  exact expectation_guardedRatio_eq_tsum law
    (fun context ↦ correlationNumerator (population context) score outcome)
    (fun context ↦ correlationDenominator (population context) score outcome)
    (fun context ↦ correlationNumerator_nonneg (population context) score outcome)
    (fun context ↦ correlationNumerator_le_denominator (population context) score outcome)
    (fun context ↦ correlationDenominator_le_one (population context) score outcome
      hscore0 hscore1 houtcome0 houtcome1)

/-- **NOTE 2 equation (18) for squared correlation, Theorem 4.** With a tolerance dominating
the unresolved definedness mass of `D` and positive retained mass, the corpus skip-undefined
average of the population squared correlation over study contexts is defined, equals the
conditional expectation of `N / D` on `D > 0`, and lies in the certified interval. -/
theorem squaredCorrelation_certificate (law : FiniteReportLaw Context)
    (population : Context → FiniteReportLaw State) (score outcome : State → ℝ)
    (hscore0 : ∀ state, 0 ≤ score state) (hscore1 : ∀ state, score state ≤ 1)
    (houtcome0 : ∀ state, 0 ≤ outcome state) (houtcome1 : ∀ state, outcome state ≤ 1)
    (terms : ℕ) (tolerance : ℝ)
    (htolerance : unresolvedMass law
      (fun context ↦ correlationDenominator (population context) score outcome) terms ≤
        tolerance)
    (hretained : 0 < retainedMass law
      (fun context ↦ correlationDenominator (population context) score outcome) terms) :
    law.conditionalMetric (fun context ↦ (population context).squaredCorrelation score outcome) =
      some (conditionalExpectation law
        (fun context ↦ 0 < correlationDenominator (population context) score outcome)
        (ratioOnDefined (fun context ↦ correlationNumerator (population context) score outcome)
          (fun context ↦ correlationDenominator (population context) score outcome))) ∧
    (retainedNumerator law (fun context ↦ correlationNumerator (population context) score outcome)
          (fun context ↦ correlationDenominator (population context) score outcome) terms /
        (retainedMass law (fun context ↦ correlationDenominator (population context) score outcome)
          terms + tolerance) ≤
      conditionalExpectation law
        (fun context ↦ 0 < correlationDenominator (population context) score outcome)
        (ratioOnDefined (fun context ↦ correlationNumerator (population context) score outcome)
          (fun context ↦ correlationDenominator (population context) score outcome)) ∧
      conditionalExpectation law
        (fun context ↦ 0 < correlationDenominator (population context) score outcome)
        (ratioOnDefined (fun context ↦ correlationNumerator (population context) score outcome)
          (fun context ↦ correlationDenominator (population context) score outcome)) ≤
        (retainedNumerator law
            (fun context ↦ correlationNumerator (population context) score outcome)
            (fun context ↦ correlationDenominator (population context) score outcome) terms +
          tolerance) /
        (retainedMass law (fun context ↦ correlationDenominator (population context) score outcome)
          terms + tolerance)) := by
  have hmetric : (fun context ↦ (population context).squaredCorrelation score outcome) =
      fun context ↦ if 0 < correlationDenominator (population context) score outcome then
        some (correlationNumerator (population context) score outcome /
          correlationDenominator (population context) score outcome) else none :=
    funext fun context ↦ squaredCorrelation_eq_guardedRatio (population context) score outcome
  rw [hmetric]
  exact guardedRatio_certificate law
    (fun context ↦ correlationNumerator (population context) score outcome)
    (fun context ↦ correlationDenominator (population context) score outcome)
    (fun context ↦ correlationNumerator_nonneg (population context) score outcome)
    (fun context ↦ correlationNumerator_le_denominator (population context) score outcome)
    (fun context ↦ correlationDenominator_le_one (population context) score outcome
      hscore0 hscore1 houtcome0 houtcome1) terms tolerance htolerance hretained

end Correlation

end

end Descent.Portability.ReplicaMetricInstances
