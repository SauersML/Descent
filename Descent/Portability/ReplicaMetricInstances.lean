/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.ReplicaDomainCertificate
import Descent.Portability.ChronologyReportLaw
import Descent.Portability.FiniteGeneticTransition
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

omit [Fintype Context] in
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

/-! ### Replica cohorts -/

section Replica

variable {State : Type*} [Fintype State]

/-- **NOTE 2 equation (11), finite study contexts.** The law of a cohort of `size` replicas that
are independent conditionally on the study context: draw a context, then draw every replica
from that context's population law with the corpus product law. -/
def replicaCohortLaw (law : FiniteReportLaw Context)
    (population : Context → FiniteReportLaw State) (size : ℕ) :
    FiniteReportLaw (Fin size → State) :=
  law.bind fun context ↦ FiniteGeneticTransition.piLaw fun _ : Fin size ↦ population context

/-- **NOTE 2 equation (11).** The probability that the replicas read out a listing is the
expectation over study contexts of the product of the population masses of its letters. -/
theorem replicaCohortLaw_mass (law : FiniteReportLaw Context)
    (population : Context → FiniteReportLaw State) (size : ℕ) (listing : Fin size → State) :
    (replicaCohortLaw law population size).mass listing =
      law.expectation (fun context ↦ ∏ slot, (population context).mass (listing slot)) :=
  rfl

end Replica

/-! ### AUC with two replicas -/

section AUC

variable {State : Type*} [Fintype State]

/-- The half-credit comparison credit lies in the unit interval. -/
theorem empiricalAUCComparison_mem_unit (caseRisk controlRisk : ℝ) :
    0 ≤ empiricalAUCComparison caseRisk controlRisk ∧
      empiricalAUCComparison caseRisk controlRisk ≤ 1 := by
  unfold empiricalAUCComparison
  split_ifs <;> norm_num

omit [Fintype State] in
/-- The ranking credit of an ordered pair of replicas: the half-credit comparison when the
first is a case and the second a control, and nothing otherwise. It is nonnegative and at most
the indicator that the first is a case times the indicator that the second is a control. -/
theorem rankingCredit_bounds (score : State → ℝ) (outcome : State → Bool)
    (first second : State) :
    0 ≤ (if outcome first && !outcome second then
        empiricalAUCComparison (score first) (score second) else 0) ∧
      (if outcome first && !outcome second then
          empiricalAUCComparison (score first) (score second) else 0) ≤
        (if outcome first then 1 else 0) * (1 - if outcome second then 1 else 0) := by
  have hunit := empiricalAUCComparison_mem_unit (score first) (score second)
  by_cases hfirst : outcome first <;> by_cases hsecond : outcome second <;>
    simp [hfirst, hsecond, hunit.1, hunit.2]

/-- **NOTE 2 section 5.4, AUC with two replicas.** The corpus ranking numerator is the expected
ranking credit of the first of two replicas drawn independently from the population law under
the corpus product law, the second replica playing the control. -/
theorem binaryAUCNumerator_eq_twoReplica (law : FiniteReportLaw State) (score : State → ℝ)
    (outcome : State → Bool) :
    law.binaryAUCNumerator score outcome =
      (FiniteGeneticTransition.piLaw fun _ : Fin 2 ↦ law).expectation (fun replica ↦
        if outcome (replica 0) && !outcome (replica 1) then
          empiricalAUCComparison (score (replica 0)) (score (replica 1)) else 0) := by
  symm
  calc (FiniteGeneticTransition.piLaw fun _ : Fin 2 ↦ law).expectation (fun replica ↦
        if outcome (replica 0) && !outcome (replica 1) then
          empiricalAUCComparison (score (replica 0)) (score (replica 1)) else 0)
      = ∑ pair : State × State, law.mass pair.1 * (law.mass pair.2 *
          if outcome pair.1 && !outcome pair.2 then
            empiricalAUCComparison (score pair.1) (score pair.2) else 0) :=
        Fintype.sum_equiv (piFinTwoEquiv fun _ ↦ State) _ _ fun replica ↦ by
          rw [FiniteGeneticTransition.piLaw_mass, Fin.prod_univ_two, mul_assoc]
          rfl
    _ = law.binaryAUCNumerator score outcome := by
        simp only [Fintype.sum_prod_type, FiniteReportLaw.binaryAUCNumerator,
          FiniteReportLaw.expectation, Finset.mul_sum]

/-- **NOTE 2 section 5.4, AUC numerator.** `N = 4A`, four times the two-replica ranking
credit. -/
def aucNumerator (law : FiniteReportLaw State) (score : State → ℝ) (outcome : State → Bool) :
    ℝ :=
  4 * law.binaryAUCNumerator score outcome

/-- **NOTE 2 section 5.4, AUC denominator.** `D = 4p(1 - p)`, four times the case mass times
the control mass. -/
def aucDenominator (law : FiniteReportLaw State) (outcome : State → Bool) : ℝ :=
  4 * (law.binaryCaseMass outcome * (1 - law.binaryCaseMass outcome))

/-- The case mass of a population law lies in the unit interval. -/
theorem binaryCaseMass_mem_unit (law : FiniteReportLaw State) (outcome : State → Bool) :
    0 ≤ law.binaryCaseMass outcome ∧ law.binaryCaseMass outcome ≤ 1 := by
  refine ⟨ReplicaDomainCertificate.expectation_nonneg law _ fun state ↦ ?_,
    ReplicaDomainCertificate.expectation_le_const law _ 1 fun state ↦ ?_⟩
  · by_cases hcase : outcome state <;> simp [hcase]
  · by_cases hcase : outcome state <;> simp [hcase]

/-- The AUC numerator is nonnegative. -/
theorem aucNumerator_nonneg (law : FiniteReportLaw State) (score : State → ℝ)
    (outcome : State → Bool) : 0 ≤ aucNumerator law score outcome :=
  mul_nonneg (by norm_num)
    (ReplicaDomainCertificate.expectation_nonneg law _ fun first ↦
      ReplicaDomainCertificate.expectation_nonneg law _ fun second ↦
        (rankingCredit_bounds score outcome first second).1)

/-- **NOTE 2 section 5.4.** The AUC numerator never exceeds the AUC denominator: every
comparison credit is at most the product of the case and control indicators, whose double
expectation is the case mass times the control mass. -/
theorem aucNumerator_le_denominator (law : FiniteReportLaw State) (score : State → ℝ)
    (outcome : State → Bool) :
    aucNumerator law score outcome ≤ aucDenominator law outcome := by
  have hcredit : law.binaryAUCNumerator score outcome ≤
      law.expectation (fun first ↦ law.expectation (fun second ↦
        (if outcome first then 1 else 0) * (1 - if outcome second then 1 else 0))) :=
    BellmanReportBounds.expectation_mono law _ _ fun first ↦
      BellmanReportBounds.expectation_mono law _ _ fun second ↦
        (rankingCredit_bounds score outcome first second).2
  have hproduct : law.expectation (fun first ↦ law.expectation (fun second ↦
      (if outcome first then 1 else 0) * (1 - if outcome second then 1 else 0))) =
        law.binaryCaseMass outcome * (1 - law.binaryCaseMass outcome) := by
    have hcomplement := law.expectation_complement fun state ↦ if outcome state then 1 else 0
    unfold FiniteReportLaw.binaryCaseMass
    rw [← hcomplement]
    simp only [FiniteReportLaw.expectation]
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun first _ ↦ ?_
    rw [Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun second _ ↦ by ring
  unfold aucNumerator aucDenominator
  linarith

/-- **NOTE 2 section 5.4.** The AUC denominator is at most one. -/
theorem aucDenominator_le_one (law : FiniteReportLaw State) (outcome : State → Bool) :
    aucDenominator law outcome ≤ 1 := by
  unfold aucDenominator
  nlinarith [sq_nonneg (2 * law.binaryCaseMass outcome - 1)]

/-- The AUC denominator is positive exactly when both outcome classes carry mass. -/
theorem aucDenominator_pos_iff (law : FiniteReportLaw State) (outcome : State → Bool) :
    0 < aucDenominator law outcome ↔
      0 < law.binaryCaseMass outcome ∧ law.binaryCaseMass outcome < 1 := by
  obtain ⟨hlow, hhigh⟩ := binaryCaseMass_mem_unit law outcome
  unfold aucDenominator
  constructor
  · intro hpos
    refine ⟨lt_of_le_of_ne hlow fun hzero ↦ ?_, lt_of_le_of_ne hhigh fun hone ↦ ?_⟩
    · rw [← hzero] at hpos
      norm_num at hpos
    · rw [hone] at hpos
      norm_num at hpos
  · rintro ⟨hcase, hcontrol⟩
    have hprod := mul_pos hcase (sub_pos.mpr hcontrol)
    linarith

/-- **NOTE 2 section 5.4.** The corpus binary AUC is the guarded ratio `N / D` with `N = 4A` and
`D = 4p(1 - p)`: defined exactly where `D` is positive, and equal there to the ratio. -/
theorem binaryAUC_eq_guardedRatio (law : FiniteReportLaw State) (score : State → ℝ)
    (outcome : State → Bool) :
    law.binaryAUC score outcome =
      if 0 < aucDenominator law outcome then
        some (aucNumerator law score outcome / aucDenominator law outcome)
      else none := by
  simp only [FiniteReportLaw.binaryAUC]
  by_cases hboth : 0 < law.binaryCaseMass outcome ∧ law.binaryCaseMass outcome < 1
  · rw [if_pos hboth, if_pos ((aucDenominator_pos_iff law outcome).mpr hboth)]
    unfold aucNumerator aucDenominator
    rw [mul_div_mul_left _ _ (by norm_num : (4 : ℝ) ≠ 0)]
  · rw [if_neg hboth, if_neg fun hpos ↦ hboth ((aucDenominator_pos_iff law outcome).mp hpos)]

/-- **NOTE 2 section 5.4, degree two.** Over a finite law of study contexts, the expected AUC
numerator is the expectation of four times the ranking credit of two conditionally independent
replicas under the replica cohort law. -/
theorem expectation_aucNumerator_eq_twoReplica (law : FiniteReportLaw Context)
    (population : Context → FiniteReportLaw State) (score : State → ℝ)
    (outcome : State → Bool) :
    law.expectation (fun context ↦ aucNumerator (population context) score outcome) =
      (replicaCohortLaw law population 2).expectation (fun replica ↦
        4 * if outcome (replica 0) && !outcome (replica 1) then
          empiricalAUCComparison (score (replica 0)) (score (replica 1)) else 0) := by
  rw [replicaCohortLaw, FiniteReportLaw.expectation_bind]
  congr 1
  funext context
  rw [aucNumerator, binaryAUCNumerator_eq_twoReplica]
  simp only [FiniteReportLaw.expectation, Finset.mul_sum]
  exact Finset.sum_congr rfl fun replica _ ↦ by ring

/-- **NOTE 2 equation (15) for AUC.** Over a finite law of study contexts, the expected
population AUC, read as zero where it is undefined, is the series of expectations of
`N * (1 - D) ^ power` with `N = 4A` and `D = 4p(1 - p)`. -/
theorem expectation_binaryAUC_eq_tsum (law : FiniteReportLaw Context)
    (population : Context → FiniteReportLaw State) (score : State → ℝ)
    (outcome : State → Bool) :
    law.expectation (fun context ↦ ((population context).binaryAUC score outcome).getD 0) =
      ∑' power : ℕ, law.expectation (fun context ↦
        aucNumerator (population context) score outcome *
          (1 - aucDenominator (population context) outcome) ^ power) := by
  simp only [binaryAUC_eq_guardedRatio]
  exact expectation_guardedRatio_eq_tsum law
    (fun context ↦ aucNumerator (population context) score outcome)
    (fun context ↦ aucDenominator (population context) outcome)
    (fun context ↦ aucNumerator_nonneg (population context) score outcome)
    (fun context ↦ aucNumerator_le_denominator (population context) score outcome)
    (fun context ↦ aucDenominator_le_one (population context) outcome)

/-- **NOTE 2 equation (18) for AUC, Theorem 4.** With a tolerance dominating the unresolved
definedness mass of `D = 4p(1 - p)` and positive retained mass, the corpus skip-undefined
average of the population AUC over study contexts is defined, equals the conditional
expectation of `N / D` on `D > 0`, and lies in the certified interval. -/
theorem binaryAUC_certificate (law : FiniteReportLaw Context)
    (population : Context → FiniteReportLaw State) (score : State → ℝ)
    (outcome : State → Bool) (terms : ℕ) (tolerance : ℝ)
    (htolerance : unresolvedMass law
      (fun context ↦ aucDenominator (population context) outcome) terms ≤ tolerance)
    (hretained : 0 < retainedMass law
      (fun context ↦ aucDenominator (population context) outcome) terms) :
    law.conditionalMetric (fun context ↦ (population context).binaryAUC score outcome) =
      some (conditionalExpectation law
        (fun context ↦ 0 < aucDenominator (population context) outcome)
        (ratioOnDefined (fun context ↦ aucNumerator (population context) score outcome)
          (fun context ↦ aucDenominator (population context) outcome))) ∧
    (retainedNumerator law (fun context ↦ aucNumerator (population context) score outcome)
          (fun context ↦ aucDenominator (population context) outcome) terms /
        (retainedMass law (fun context ↦ aucDenominator (population context) outcome) terms +
          tolerance) ≤
      conditionalExpectation law
        (fun context ↦ 0 < aucDenominator (population context) outcome)
        (ratioOnDefined (fun context ↦ aucNumerator (population context) score outcome)
          (fun context ↦ aucDenominator (population context) outcome)) ∧
      conditionalExpectation law
        (fun context ↦ 0 < aucDenominator (population context) outcome)
        (ratioOnDefined (fun context ↦ aucNumerator (population context) score outcome)
          (fun context ↦ aucDenominator (population context) outcome)) ≤
        (retainedNumerator law (fun context ↦ aucNumerator (population context) score outcome)
            (fun context ↦ aucDenominator (population context) outcome) terms + tolerance) /
          (retainedMass law (fun context ↦ aucDenominator (population context) outcome) terms +
            tolerance)) := by
  have hmetric : (fun context ↦ (population context).binaryAUC score outcome) =
      fun context ↦ if 0 < aucDenominator (population context) outcome then
        some (aucNumerator (population context) score outcome /
          aucDenominator (population context) outcome) else none :=
    funext fun context ↦ binaryAUC_eq_guardedRatio (population context) score outcome
  rw [hmetric]
  exact guardedRatio_certificate law
    (fun context ↦ aucNumerator (population context) score outcome)
    (fun context ↦ aucDenominator (population context) outcome)
    (fun context ↦ aucNumerator_nonneg (population context) score outcome)
    (fun context ↦ aucNumerator_le_denominator (population context) score outcome)
    (fun context ↦ aucDenominator_le_one (population context) outcome) terms tolerance
    htolerance hretained

end AUC

end

end Descent.Portability.ReplicaMetricInstances
