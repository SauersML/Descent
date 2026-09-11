/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Foundations.TransportIdentities
import Descent.Portability.ReplicaDomainCertificate
import Descent.Portability.ChronologyReportLaw
import Descent.Portability.FiniteGeneticTransition
import Descent.Portability.PThresholdTrainingLaw
import Descent.Portability.ReplicaMomentCompleteness
import Descent.Portability.UniformPenetranceArchitecture
import Mathlib.Algebra.MvPolynomial.CommRing

assert_below Descent.Decision Descent.Program

/-!
# Concrete population metrics as bounded replica ratios

NOTE 2 section 5.4 instantiates the replica-domain compiler of sections 5.1 and 5.2 for the
metrics a report actually carries. Every instance is derived from the corpus definitions of
the metrics, not from restatements of them. Scope: population laws and study contexts are
finite report laws; the replica readouts have signed coefficients, as NOTE 2 remarks after (15),
and are not claimed to be pointwise nonnegative. Average precision is compiled as a quotient
whose numerator is itself a finite sum of guarded ratios; no single polynomial series for it is
claimed.

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

Repaired Brier loss. For a law on pairs of a score group and a binary outcome, `scoreGroupMass`
is `q_s` and the mass of the pair `(s, true)` is `a_s`. `conditionalRepairedBrier` is NOTE 2
(23) as a finite sum of zero-extended ratios with `0 ≤ a_s² ≤ q_s ≤ 1`
(`squaredCaseMass_le_scoreGroupMass`), so an empty group contributes zero
(`conditionalRepairedBrier_eq_sum_filter`). It is population optimal:
`conditionalRepairedBrier_le_meanSquaredError` bounds every recalibration of the score and
`meanSquaredError_conditionalMean` attains the bound. `expectation_conditionalRepairedBrier_eq_tsum`
applies (15) to every summand, and `repairedBrier_eq_conditionalRepairedBrier` ties the loss to
the affine repair `ChronologyReportLaw.repairedBrier` of a binary score with both cells occupied.

Calibration error. `calibrationError` is NOTE 2 (22) and equals the corpus
`ChronologyReportLaw.discreteECE` for a binary score (`discreteECE_eq_calibrationError`). Its
absolute values are resolved by finite sign strata: `calibrationError_eq_signedResidual`
evaluates it at the law's own sign pattern, `calibrationError_isGreatest` exhibits it as the
largest of the linear functionals `signedResidual`, each a one-replica moment
(`signedResidual_eq_expectation`), and `expectation_calibrationError_eq_strata` is the exact
stratum expansion over study contexts. `calibrationError_continuous` is continuity in the mass
vector and `abs_calibrationError_sub_le` the total-variation Lipschitz bound.

Degree accounting. `expectationPolynomial`, `pairPolynomial` and `covariancePolynomial` are
polynomials in the population probability vector evaluating to the corpus expectation, double
expectation and covariance. The numerator and denominator polynomials of (21) have total degree
at most four and those of the AUC at most two, so the `k`-th expansion term has degree at most
`4 (k + 1)` (`totalDegree_correlationTerm_le`) and `2 (k + 1)` (`totalDegree_aucTerm_le`).
`expectation_monomialEvent` shows that a monomial moment of degree at most `n` is the
probability, under the corpus product law of `n` replicas, of the explicit `monomialEvent`
built from the corpus `ReplicaMomentCompleteness.exponentListing`, and
`expectation_eval_eq_replicaReadout` combines the two under `replicaCohortLaw`, the
finite-context replica law of NOTE 2 (11). `expectation_correlationTerm_eq_replicaReadout` and
`expectation_aucTerm_eq_replicaReadout` are the instances.

Rates, curves and average precision. `ruleConfusion` is the corpus
`Foundations.ConfusionMatrix` of a score rule on a population law. Its called masses are
one-replica event probabilities (`calledMass_eq_expectation`) and its prevalence is the case
probability for every rule (`prevalence_ruleConfusion`). `confusion_rate_bounds` shows that the
corpus recall, false positive rate and precision are bounded ratios, `rates_mem_unit` places
every ROC and precision-recall point in the unit square, and `expectation_recallRate_eq_tsum`,
`expectation_fpr_eq_tsum` and `expectation_precision_eq_tsum` apply (15) to them through
`expectation_div_eq_tsum`, which reads a quotient with Lean's zero at a vanishing denominator.
`thresholdRule` is the strict threshold rule, with a tied score cleared, and
`calledMass_thresholdRule_antitone` is the monotonicity of the threshold curve.
`averagePrecision` is average precision under a fixed finite-score definition in which tied
score values are called together (`atLeastRule`), and `averagePrecision_eq_sum_recall_increment`
reads it as recall increments times precision. Its numerator is a finite sum of bounded ratios
(`averagePrecision_summand_bounds`) and at most the case probability, so (15) applies at both
levels (`expectation_averagePrecision_eq_tsum`, `expectation_averagePrecisionSummand_eq_tsum`).

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
  have hunit := PThresholdTrainingLaw.comparison_bounds (score first) (score second)
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

/-! ### Score groups of a finite score alphabet -/

section ScoreGroups

variable {Score : Type*} [Fintype Score]

/-- The population mass `q_s` of one score group: the score takes the given value, whatever the
outcome. -/
def scoreGroupMass (law : FiniteReportLaw (Score × Bool)) (group : Score) : ℝ :=
  law.mass (group, false) + law.mass (group, true)

/-- For a binary score the score group mass is the corpus score cell mass. -/
theorem scoreGroupMass_eq_scoreCellMass (law : FiniteReportLaw (Bool × Bool)) (allele : Bool) :
    scoreGroupMass law allele = ChronologyReportLaw.scoreCellMass law allele :=
  (ChronologyReportLaw.scoreCellMass_eq_cells law allele).symm

/-- For a binary score the score group mass is the four-cell score marginal
`EmpiricalCorrelationDefinedness.scoreMass` of NOTE1 (31), and the score-group mass of the
uniform-penetrance example of NOTE2 section 9.1. -/
theorem scoreGroupMass_bool_eq_scoreMass (law : FiniteReportLaw (Bool × Bool)) (group : Bool) :
    scoreGroupMass law group = EmpiricalCorrelationDefinedness.scoreMass law group ∧
      scoreGroupMass law group = UniformPenetranceArchitecture.scoreGroupMass law group :=
  ⟨rfl, rfl⟩

/-- A score group mass is nonnegative. -/
theorem scoreGroupMass_nonneg (law : FiniteReportLaw (Score × Bool)) (group : Score) :
    0 ≤ scoreGroupMass law group :=
  add_nonneg (law.mass_nonneg (group, false)) (law.mass_nonneg (group, true))

/-- The case mass `a_s` of a score group never exceeds the group mass `q_s`. -/
theorem caseMass_le_scoreGroupMass (law : FiniteReportLaw (Score × Bool)) (group : Score) :
    law.mass (group, true) ≤ scoreGroupMass law group :=
  le_add_of_nonneg_left (law.mass_nonneg (group, false))

/-- A score group mass is at most one. -/
theorem scoreGroupMass_le_one (law : FiniteReportLaw (Score × Bool)) (group : Score) :
    scoreGroupMass law group ≤ 1 := by
  calc scoreGroupMass law group = ∑ outcome : Bool, law.mass (group, outcome) := by
        rw [Fintype.sum_bool, scoreGroupMass, add_comm]
    _ ≤ ∑ other : Score, ∑ outcome : Bool, law.mass (other, outcome) :=
        Finset.single_le_sum
          (fun other _ ↦ Finset.sum_nonneg fun outcome _ ↦ law.mass_nonneg (other, outcome))
          (Finset.mem_univ group)
    _ = 1 := by rw [← law.mass_sum, Fintype.sum_prod_type]

/-- **NOTE 2 section 5.4.** Every summand of the repaired Brier loss is a bounded ratio: the
squared case mass of a score group is at most the group mass, which is at most one. -/
theorem squaredCaseMass_le_scoreGroupMass (law : FiniteReportLaw (Score × Bool))
    (group : Score) :
    0 ≤ law.mass (group, true) ^ 2 ∧ law.mass (group, true) ^ 2 ≤ scoreGroupMass law group ∧
      scoreGroupMass law group ≤ 1 := by
  have hcase := law.mass_nonneg (group, true)
  have hbelow := caseMass_le_scoreGroupMass law group
  have hone := hbelow.trans (scoreGroupMass_le_one law group)
  refine ⟨sq_nonneg _, ?_, scoreGroupMass_le_one law group⟩
  nlinarith [mul_nonneg hcase (sub_nonneg.mpr hone)]

end ScoreGroups

/-! ### The repaired Brier loss -/

section RepairedBrier

variable {Score : Type*} [Fintype Score]

/-- **NOTE 2 equation (23).** The population-optimal score-conditional repaired Brier loss: the
case probability minus the sum over score groups of the squared case mass over the group mass,
each summand read as zero on an empty group. -/
def conditionalRepairedBrier (law : FiniteReportLaw (Score × Bool)) : ℝ :=
  law.expectation (fun report ↦ ChronologyReportLaw.alleleValue report.2) -
    ∑ group, ratioOnDefined (fun other ↦ law.mass (other, true) ^ 2) (scoreGroupMass law) group

/-- **NOTE 2 equation (23), literally.** The repaired Brier loss is the case probability minus
the sum of `a_s ^ 2 / q_s` over the score groups with `q_s > 0`: empty groups contribute zero
and do not make the loss undefined. -/
theorem conditionalRepairedBrier_eq_sum_filter (law : FiniteReportLaw (Score × Bool)) :
    conditionalRepairedBrier law =
      law.expectation (fun report ↦ ChronologyReportLaw.alleleValue report.2) -
        ∑ group ∈ Finset.univ.filter (fun group ↦ 0 < scoreGroupMass law group),
          law.mass (group, true) ^ 2 / scoreGroupMass law group := by
  rw [conditionalRepairedBrier, Finset.sum_filter]
  rfl

/-- The mean squared error of any score recalibration decomposes over the score groups into the
case probability plus `q_s g_s ^ 2 - 2 a_s g_s` per group. -/
theorem meanSquaredError_recalibration (law : FiniteReportLaw (Score × Bool))
    (recalibration : Score → ℝ) :
    law.meanSquaredError (fun report ↦ recalibration report.1)
        (fun report ↦ ChronologyReportLaw.alleleValue report.2) =
      law.expectation (fun report ↦ ChronologyReportLaw.alleleValue report.2) +
        ∑ group, (scoreGroupMass law group * recalibration group ^ 2 -
          2 * law.mass (group, true) * recalibration group) := by
  simp only [FiniteReportLaw.meanSquaredError, FiniteReportLaw.expectation, Fintype.sum_prod_type,
    Fintype.sum_bool, scoreGroupMass, ChronologyReportLaw.alleleValue_true,
    ChronologyReportLaw.alleleValue_false]
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun group _ ↦ by ring

/-- **NOTE 2 equation (23), population optimality.** No recalibration of the score achieves a
smaller Brier loss than the repaired Brier loss. -/
theorem conditionalRepairedBrier_le_meanSquaredError (law : FiniteReportLaw (Score × Bool))
    (recalibration : Score → ℝ) :
    conditionalRepairedBrier law ≤
      law.meanSquaredError (fun report ↦ recalibration report.1)
        (fun report ↦ ChronologyReportLaw.alleleValue report.2) := by
  have hgroup : ∀ group, -ratioOnDefined (fun other ↦ law.mass (other, true) ^ 2)
      (scoreGroupMass law) group ≤
        scoreGroupMass law group * recalibration group ^ 2 -
          2 * law.mass (group, true) * recalibration group := by
    intro group
    unfold ratioOnDefined
    split_ifs with hpos
    · have hsquare : 0 ≤ scoreGroupMass law group *
          (recalibration group - law.mass (group, true) / scoreGroupMass law group) ^ 2 :=
        mul_nonneg hpos.le (sq_nonneg _)
      have hexpand : scoreGroupMass law group *
          (recalibration group - law.mass (group, true) / scoreGroupMass law group) ^ 2 =
            scoreGroupMass law group * recalibration group ^ 2 -
              2 * law.mass (group, true) * recalibration group +
                law.mass (group, true) ^ 2 / scoreGroupMass law group := by
        linear_combination (-(2 * recalibration group * law.mass (group, true)) +
          law.mass (group, true) ^ 2 * (scoreGroupMass law group)⁻¹) *
            mul_inv_cancel₀ hpos.ne'
      linarith
    · have hzero : scoreGroupMass law group = 0 :=
        le_antisymm (not_lt.mp hpos) (scoreGroupMass_nonneg law group)
      have hcase : law.mass (group, true) = 0 :=
        le_antisymm (by linarith [caseMass_le_scoreGroupMass law group]) (law.mass_nonneg _)
      rw [hzero, hcase]
      norm_num
  have hsum : 0 ≤ ∑ group, (scoreGroupMass law group * recalibration group ^ 2 -
      2 * law.mass (group, true) * recalibration group +
        ratioOnDefined (fun other ↦ law.mass (other, true) ^ 2) (scoreGroupMass law) group) :=
    Finset.sum_nonneg fun group _ ↦ by linarith [hgroup group]
  rw [Finset.sum_add_distrib] at hsum
  rw [meanSquaredError_recalibration, conditionalRepairedBrier]
  linarith

/-- **NOTE 2 equation (23), attainment.** Recalibrating every score group to its conditional
case probability, read as zero on an empty group, attains the repaired Brier loss. -/
theorem meanSquaredError_conditionalMean (law : FiniteReportLaw (Score × Bool)) :
    law.meanSquaredError
        (fun report ↦ ratioOnDefined (fun other ↦ law.mass (other, true)) (scoreGroupMass law)
          report.1)
        (fun report ↦ ChronologyReportLaw.alleleValue report.2) =
      conditionalRepairedBrier law := by
  have hsum : ∑ group, (scoreGroupMass law group *
        ratioOnDefined (fun other ↦ law.mass (other, true)) (scoreGroupMass law) group ^ 2 -
      2 * law.mass (group, true) *
        ratioOnDefined (fun other ↦ law.mass (other, true)) (scoreGroupMass law) group) =
      -∑ group, ratioOnDefined (fun other ↦ law.mass (other, true) ^ 2) (scoreGroupMass law)
        group := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun group _ ↦ ?_
    unfold ratioOnDefined
    split_ifs with hpos
    · linear_combination (law.mass (group, true) ^ 2 * (scoreGroupMass law group)⁻¹) *
        mul_inv_cancel₀ hpos.ne'
    · ring
  rw [meanSquaredError_recalibration law
      (ratioOnDefined (fun other ↦ law.mass (other, true)) (scoreGroupMass law)),
    conditionalRepairedBrier, hsum]
  ring

/-- **NOTE 2 equation (15) for the repaired Brier loss.** Over a finite law of study contexts,
the expected repaired Brier loss is the expected case probability minus, for every score group,
the series of expectations of `a_s ^ 2 * (1 - q_s) ^ power`. -/
theorem expectation_conditionalRepairedBrier_eq_tsum (law : FiniteReportLaw Context)
    (population : Context → FiniteReportLaw (Score × Bool)) :
    law.expectation (fun context ↦ conditionalRepairedBrier (population context)) =
      law.expectation (fun context ↦ (population context).expectation
          (fun report ↦ ChronologyReportLaw.alleleValue report.2)) -
        ∑ group, ∑' power : ℕ, law.expectation (fun context ↦
          (population context).mass (group, true) ^ 2 *
            (1 - scoreGroupMass (population context) group) ^ power) := by
  have hgroup : ∀ group, law.expectation (fun context ↦
      ratioOnDefined (fun other ↦ (population context).mass (other, true) ^ 2)
        (scoreGroupMass (population context)) group) =
        ∑' power : ℕ, law.expectation (fun context ↦
          (population context).mass (group, true) ^ 2 *
            (1 - scoreGroupMass (population context) group) ^ power) := fun group ↦
    expectation_ratioOnDefined_eq_tsum law
      (fun context ↦ (population context).mass (group, true) ^ 2)
      (fun context ↦ scoreGroupMass (population context) group)
      (fun context ↦ (squaredCaseMass_le_scoreGroupMass (population context) group).1)
      (fun context ↦ (squaredCaseMass_le_scoreGroupMass (population context) group).2.1)
      (fun context ↦ (squaredCaseMass_le_scoreGroupMass (population context) group).2.2)
  calc law.expectation (fun context ↦ conditionalRepairedBrier (population context))
      = law.expectation (fun context ↦ (population context).expectation
            (fun report ↦ ChronologyReportLaw.alleleValue report.2)) -
          law.expectation (fun context ↦ ∑ group, ratioOnDefined
            (fun other ↦ (population context).mass (other, true) ^ 2)
            (scoreGroupMass (population context)) group) := by
        simp only [FiniteReportLaw.expectation, ← Finset.sum_sub_distrib, ← mul_sub]
        rfl
    _ = _ := by
        rw [FiniteIndependentMoments.expectation_sum law (fun group context ↦ ratioOnDefined
          (fun other ↦ (population context).mass (other, true) ^ 2)
          (scoreGroupMass (population context)) group)]
        congr 1
        exact Finset.sum_congr rfl fun group _ ↦ hgroup group

/-- **NOTE 2 section 5.4 and NOTE 1 section 6.2.** For a binary score whose two score cells both
carry mass, the affinely repaired Brier loss of the corpus equals the score-conditional repaired
Brier loss: with two score groups the affine recalibration is already the group mean. -/
theorem repairedBrier_eq_conditionalRepairedBrier (law : FiniteReportLaw (Bool × Bool))
    (hrecipient : 0 < ChronologyReportLaw.scoreCellMass law false)
    (hdonor : 0 < ChronologyReportLaw.scoreCellMass law true) :
    ChronologyReportLaw.repairedBrier law = conditionalRepairedBrier law := by
  rw [ChronologyReportLaw.scoreCellMass_eq_cells] at hrecipient hdonor
  have hsum : law.mass (false, false) + law.mass (false, true) + law.mass (true, false) +
      law.mass (true, true) = 1 := by
    have htotal := law.mass_sum
    simp only [Fintype.sum_prod_type, Fintype.sum_bool] at htotal
    linarith
  have hscore : law.variance ChronologyReportLaw.scoreOf =
      (law.mass (false, false) + law.mass (false, true)) *
        (law.mass (true, false) + law.mass (true, true)) := by
    rw [FiniteReportLaw.variance_eq_rawMoments, ChronologyReportLaw.expectation_cells,
      ChronologyReportLaw.expectation_cells]
    simp only [ChronologyReportLaw.scoreOf_true, ChronologyReportLaw.scoreOf_false]
    linear_combination (-(law.mass (true, false) + law.mass (true, true))) * hsum
  have houtcome : law.variance ChronologyReportLaw.outcomeOf =
      (law.mass (false, false) + law.mass (true, false)) *
        (law.mass (false, true) + law.mass (true, true)) := by
    rw [FiniteReportLaw.variance_eq_rawMoments, ChronologyReportLaw.expectation_cells,
      ChronologyReportLaw.expectation_cells]
    simp only [ChronologyReportLaw.outcomeOf_true, ChronologyReportLaw.outcomeOf_false]
    linear_combination (-(law.mass (false, true) + law.mass (true, true))) * hsum
  have hcovariance : law.covariance ChronologyReportLaw.scoreOf ChronologyReportLaw.outcomeOf =
      law.mass (false, false) * law.mass (true, true) -
        law.mass (false, true) * law.mass (true, false) := by
    rw [FiniteReportLaw.covariance_eq_rawMoments, ChronologyReportLaw.expectation_cells,
      ChronologyReportLaw.expectation_cells, ChronologyReportLaw.expectation_cells]
    simp only [ChronologyReportLaw.scoreOf_true, ChronologyReportLaw.scoreOf_false,
      ChronologyReportLaw.outcomeOf_true, ChronologyReportLaw.outcomeOf_false]
    linear_combination (-law.mass (true, true)) * hsum
  have hcase : law.expectation (fun report ↦ ChronologyReportLaw.alleleValue report.2) =
      law.mass (false, true) + law.mass (true, true) := by
    rw [ChronologyReportLaw.expectation_cells]
    simp only [ChronologyReportLaw.alleleValue_true, ChronologyReportLaw.alleleValue_false]
    ring
  have hgroups : ∑ group, ratioOnDefined (fun other ↦ law.mass (other, true) ^ 2)
      (scoreGroupMass law) group =
        law.mass (true, true) ^ 2 / (law.mass (true, false) + law.mass (true, true)) +
          law.mass (false, true) ^ 2 / (law.mass (false, false) + law.mass (false, true)) := by
    rw [Fintype.sum_bool]
    simp only [ratioOnDefined, scoreGroupMass, if_pos hdonor, if_pos hrecipient]
  unfold ChronologyReportLaw.repairedBrier conditionalRepairedBrier
  rw [hscore, houtcome, hcovariance, hcase, hgroups]
  have hne0 : law.mass (false, false) + law.mass (false, true) ≠ 0 := hrecipient.ne'
  have hne1 : law.mass (true, false) + law.mass (true, true) ≠ 0 := hdonor.ne'
  have hkey : (law.mass (false, false) + law.mass (true, false)) *
        (law.mass (false, true) + law.mass (true, true)) -
      (law.mass (false, false) * law.mass (true, true) -
        law.mass (false, true) * law.mass (true, false)) ^ 2 /
          ((law.mass (false, false) + law.mass (false, true)) *
            (law.mass (true, false) + law.mass (true, true))) -
      (law.mass (false, true) + law.mass (true, true) -
        (law.mass (true, true) ^ 2 / (law.mass (true, false) + law.mass (true, true)) +
          law.mass (false, true) ^ 2 / (law.mass (false, false) + law.mass (false, true)))) =
      (law.mass (false, false) + law.mass (false, true) + law.mass (true, false) +
          law.mass (true, true) - 1) *
        ((law.mass (false, true) + law.mass (true, true)) *
            (law.mass (false, false) + law.mass (false, true)) *
              (law.mass (true, false) + law.mass (true, true)) -
          (law.mass (false, true) + law.mass (true, true)) ^ 2 *
            (law.mass (true, false) + law.mass (true, true)) +
          law.mass (true, true) ^ 2 -
          2 * law.mass (true, true) * (law.mass (true, true) -
            (law.mass (true, false) + law.mass (true, true)) *
              (law.mass (false, true) + law.mass (true, true))) -
          law.mass (true, true) ^ 2 * (law.mass (false, false) + law.mass (false, true) +
            law.mass (true, false) + law.mass (true, true) - 1)) /
        ((law.mass (false, false) + law.mass (false, true)) *
          (law.mass (true, false) + law.mass (true, true))) := by
    field_simp
    ring
  rw [hsum, sub_self, zero_mul, zero_div, sub_eq_zero] at hkey
  exact hkey

end RepairedBrier

/-! ### Discrete calibration error -/

section CalibrationError

variable {Score : Type*} [Fintype Score]

/-- **NOTE 2 equation (22), one group.** The calibration residual `a_s - s q_s` of a score
group, for a numeric value `s` attached to the group. -/
def calibrationResidual (law : FiniteReportLaw (Score × Bool)) (value : Score → ℝ)
    (group : Score) : ℝ :=
  law.mass (group, true) - value group * scoreGroupMass law group

/-- **NOTE 2 equation (22).** The exact discrete-score calibration error `∑_s |a_s - s q_s|`. -/
def calibrationError (law : FiniteReportLaw (Score × Bool)) (value : Score → ℝ) : ℝ :=
  ∑ group, |calibrationResidual law value group|

/-- For a binary score the calibration error of NOTE 2 (22) is the corpus discrete calibration
error of NOTE 1 section 6.2, including where a score cell is empty. -/
theorem discreteECE_eq_calibrationError (law : FiniteReportLaw (Bool × Bool)) :
    ChronologyReportLaw.discreteECE law =
      calibrationError law ChronologyReportLaw.alleleValue := by
  unfold ChronologyReportLaw.discreteECE calibrationError
  refine Finset.sum_congr rfl fun allele _ ↦ ?_
  unfold ChronologyReportLaw.conditionalOutcomeMean calibrationResidual
  rw [← scoreGroupMass_eq_scoreCellMass]
  rcases eq_or_lt_of_le (scoreGroupMass_nonneg law allele) with hzero | hpos
  · have hcase : law.mass (allele, true) = 0 :=
      le_antisymm (by linarith [caseMass_le_scoreGroupMass law allele]) (law.mass_nonneg _)
    rw [← hzero, hcase]
    norm_num
  · have hfactor : law.mass (allele, true) -
        ChronologyReportLaw.alleleValue allele * scoreGroupMass law allele =
          scoreGroupMass law allele * (law.mass (allele, true) / scoreGroupMass law allele -
            ChronologyReportLaw.alleleValue allele) := by
      linear_combination (-law.mass (allele, true)) * mul_inv_cancel₀ hpos.ne'
    rw [hfactor, abs_mul, abs_of_pos hpos]

/-- The sign pattern of a law: which score groups have a nonnegative calibration residual. -/
def residualPattern (law : FiniteReportLaw (Score × Bool)) (value : Score → ℝ) :
    Score → Bool :=
  fun group ↦ decide (0 ≤ calibrationResidual law value group)

/-- **NOTE 2 section 5.4, one sign stratum.** The signed residual of a sign pattern: the sum of
the residuals with the signs of the pattern. It is linear in the population law. -/
def signedResidual (law : FiniteReportLaw (Score × Bool)) (value : Score → ℝ)
    (pattern : Score → Bool) : ℝ :=
  ∑ group, (if pattern group then 1 else -1) * calibrationResidual law value group

/-- The signed residual of a pattern is a one-replica moment: the expectation of the signed
difference between the outcome and the score value. -/
theorem signedResidual_eq_expectation (law : FiniteReportLaw (Score × Bool))
    (value : Score → ℝ) (pattern : Score → Bool) :
    signedResidual law value pattern =
      law.expectation (fun report ↦ (if pattern report.1 then 1 else -1) *
        (ChronologyReportLaw.alleleValue report.2 - value report.1)) := by
  simp only [signedResidual, calibrationResidual, scoreGroupMass, FiniteReportLaw.expectation,
    Fintype.sum_prod_type, Fintype.sum_bool, ChronologyReportLaw.alleleValue_true,
    ChronologyReportLaw.alleleValue_false]
  exact Finset.sum_congr rfl fun group _ ↦ by ring

/-- Every sign pattern gives a lower bound on the calibration error. -/
theorem signedResidual_le_calibrationError (law : FiniteReportLaw (Score × Bool))
    (value : Score → ℝ) (pattern : Score → Bool) :
    signedResidual law value pattern ≤ calibrationError law value := by
  refine Finset.sum_le_sum fun group _ ↦ ?_
  split_ifs
  · rw [one_mul]
    exact le_abs_self _
  · rw [neg_one_mul]
    exact neg_le_abs _

/-- **NOTE 2 section 5.4, exact sign strata.** The calibration error is the signed residual of
the law's own sign pattern. -/
theorem calibrationError_eq_signedResidual (law : FiniteReportLaw (Score × Bool))
    (value : Score → ℝ) :
    calibrationError law value = signedResidual law value (residualPattern law value) := by
  refine Finset.sum_congr rfl fun group _ ↦ ?_
  simp only [residualPattern, decide_eq_true_eq]
  by_cases hsign : 0 ≤ calibrationResidual law value group
  · rw [if_pos hsign, one_mul, abs_of_nonneg hsign]
  · rw [if_neg hsign, neg_one_mul, abs_of_neg (not_le.mp hsign)]

/-- **NOTE 2 section 5.4.** The calibration error is the largest of the finitely many linear
signed residuals, attained at the law's own sign pattern. -/
theorem calibrationError_isGreatest (law : FiniteReportLaw (Score × Bool)) (value : Score → ℝ) :
    IsGreatest (Set.range (signedResidual law value)) (calibrationError law value) :=
  ⟨⟨residualPattern law value, (calibrationError_eq_signedResidual law value).symm⟩,
    by
      rintro _ ⟨pattern, rfl⟩
      exact signedResidual_le_calibrationError law value pattern⟩

/-- **NOTE 2 section 5.4, sign-strata expansion over study contexts.** The expected calibration
error is the sum over sign patterns of the expectation of the stratum indicator times the linear
signed residual of that pattern. -/
theorem expectation_calibrationError_eq_strata [DecidableEq Score]
    (law : FiniteReportLaw Context) (population : Context → FiniteReportLaw (Score × Bool))
    (value : Score → ℝ) :
    law.expectation (fun context ↦ calibrationError (population context) value) =
      ∑ pattern : Score → Bool, law.expectation (fun context ↦
        definedIndicator (fun other ↦ residualPattern (population other) value = pattern)
            context *
          signedResidual (population context) value pattern) := by
  rw [← FiniteIndependentMoments.expectation_sum]
  congr 1
  funext context
  rw [calibrationError_eq_signedResidual]
  simp [definedIndicator]

/-- **NOTE 2 section 5.4, continuity.** The calibration error is the value at the mass vector of
a continuous functional of that vector. -/
theorem calibrationError_continuous (value : Score → ℝ) :
    Continuous (fun mass : Score × Bool → ℝ ↦
        ∑ group, |mass (group, true) - value group * (mass (group, false) + mass (group, true))|) ∧
      ∀ law : FiniteReportLaw (Score × Bool), calibrationError law value =
        ∑ group, |law.mass (group, true) -
          value group * (law.mass (group, false) + law.mass (group, true))| :=
  ⟨continuous_finset_sum _ fun _ _ ↦ continuous_abs.comp
      ((continuous_apply _).sub
        (continuous_const.mul ((continuous_apply _).add (continuous_apply _)))),
    fun _ ↦ rfl⟩

/-- A difference of two terms weighted by complementary unit-interval weights is bounded by the
sum of the absolute values of the terms. -/
theorem abs_convex_difference_le (first second weight : ℝ) (hlow : 0 ≤ weight)
    (hhigh : weight ≤ 1) :
    |(1 - weight) * first - weight * second| ≤ |first| + |second| := by
  have hgap := sub_nonneg.mpr hhigh
  have hfirst := abs_nonneg first
  have hsecond := abs_nonneg second
  rw [abs_le]
  constructor
  · nlinarith [mul_nonneg hgap (by linarith [neg_abs_le first] : 0 ≤ first + |first|),
      mul_nonneg hlow (by linarith [le_abs_self second] : 0 ≤ |second| - second),
      mul_nonneg hlow hfirst, mul_nonneg hgap hsecond]
  · nlinarith [mul_nonneg hgap (by linarith [le_abs_self first] : 0 ≤ |first| - first),
      mul_nonneg hlow (by linarith [neg_abs_le second] : 0 ≤ second + |second|),
      mul_nonneg hlow hfirst, mul_nonneg hgap hsecond]

/-- **NOTE 2 section 5.4 and equation (31).** For score values in the unit interval the
calibration error is Lipschitz in total variation: two laws whose total variation distance is
`t` have calibration errors within `2 t`. -/
theorem abs_calibrationError_sub_le (first second : FiniteReportLaw (Score × Bool))
    (value : Score → ℝ) (hlow : ∀ group, 0 ≤ value group) (hhigh : ∀ group, value group ≤ 1) :
    |calibrationError first value - calibrationError second value| ≤
      2 * first.totalVariation second := by
  have hgroup : ∀ group, |calibrationResidual first value group -
      calibrationResidual second value group| ≤
        ∑ outcome : Bool, |first.mass (group, outcome) - second.mass (group, outcome)| := by
    intro group
    have hsplit : calibrationResidual first value group -
        calibrationResidual second value group =
          (1 - value group) * (first.mass (group, true) - second.mass (group, true)) -
            value group * (first.mass (group, false) - second.mass (group, false)) := by
      unfold calibrationResidual scoreGroupMass
      ring
    rw [hsplit, Fintype.sum_bool]
    exact abs_convex_difference_le _ _ _ (hlow group) (hhigh group)
  rw [FiniteReportLaw.totalVariation_eq_half_sum_abs, Fintype.sum_prod_type]
  unfold calibrationError
  rw [← Finset.sum_sub_distrib]
  calc |∑ group, (|calibrationResidual first value group| -
        |calibrationResidual second value group|)|
      ≤ ∑ group, |(|calibrationResidual first value group| -
          |calibrationResidual second value group|)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ group, |calibrationResidual first value group -
          calibrationResidual second value group| :=
        Finset.sum_le_sum fun group _ ↦ abs_abs_sub_abs_le_abs_sub _ _
    _ ≤ ∑ group, ∑ outcome : Bool, |first.mass (group, outcome) - second.mass (group, outcome)| :=
        Finset.sum_le_sum fun group _ ↦ hgroup group
    _ = 2 * ((∑ group, ∑ outcome : Bool,
          |first.mass (group, outcome) - second.mass (group, outcome)|) / 2) := by ring

end CalibrationError

/-! ### Confusion-matrix rates, threshold curves and average precision -/

section ScoreRules

variable {Score : Type*} [Fintype Score]

/-- The mass of the report cells of one outcome class whose score group a rule calls
positive. -/
def calledMass (law : FiniteReportLaw (Score × Bool)) (called : Score → Bool)
    (outcome : Bool) : ℝ :=
  ∑ group, if called group then law.mass (group, outcome) else 0

/-- The mass of the report cells of one outcome class whose score group a rule clears. -/
def clearedMass (law : FiniteReportLaw (Score × Bool)) (called : Score → Bool)
    (outcome : Bool) : ℝ :=
  ∑ group, if called group then 0 else law.mass (group, outcome)

/-- The called and the cleared mass of one outcome class partition that class. -/
theorem calledMass_add_clearedMass (law : FiniteReportLaw (Score × Bool))
    (called : Score → Bool) (outcome : Bool) :
    calledMass law called outcome + clearedMass law called outcome =
      ∑ group, law.mass (group, outcome) := by
  rw [calledMass, clearedMass, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun group _ ↦ by split_ifs <;> ring

/-- The called mass is nonnegative. -/
theorem calledMass_nonneg (law : FiniteReportLaw (Score × Bool)) (called : Score → Bool)
    (outcome : Bool) : 0 ≤ calledMass law called outcome :=
  Finset.sum_nonneg fun group _ ↦ by
    split_ifs
    · exact law.mass_nonneg _
    · exact le_refl 0

/-- The cleared mass is nonnegative. -/
theorem clearedMass_nonneg (law : FiniteReportLaw (Score × Bool)) (called : Score → Bool)
    (outcome : Bool) : 0 ≤ clearedMass law called outcome :=
  Finset.sum_nonneg fun group _ ↦ by
    split_ifs
    · exact le_refl 0
    · exact law.mass_nonneg _

/-- The called mass of an outcome class is the one-replica probability of the event that the
rule calls the score group and the outcome is that class. -/
theorem calledMass_eq_expectation (law : FiniteReportLaw (Score × Bool))
    (called : Score → Bool) (outcome : Bool) :
    calledMass law called outcome =
      law.expectation (fun report ↦
        if called report.1 = true ∧ report.2 = outcome then 1 else 0) := by
  simp only [calledMass, FiniteReportLaw.expectation, Fintype.sum_prod_type, Fintype.sum_bool]
  refine Finset.sum_congr rfl fun group _ ↦ ?_
  cases hcall : called group <;> cases outcome <;> simp

/-- **NOTE 2 section 5.4, confusion-matrix rates.** The corpus confusion matrix of a score rule
on a population law: true positives are called cases, false positives called controls, true
negatives cleared controls and false negatives cleared cases. -/
def ruleConfusion (law : FiniteReportLaw (Score × Bool)) (called : Score → Bool) :
    Foundations.ConfusionMatrix where
  tp := calledMass law called true
  fp := calledMass law called false
  tn := clearedMass law called false
  fn := clearedMass law called true
  tp_nonneg := calledMass_nonneg law called true
  fp_nonneg := calledMass_nonneg law called false
  tn_nonneg := clearedMass_nonneg law called false
  fn_nonneg := clearedMass_nonneg law called true
  mass_one := by
    have hcases := calledMass_add_clearedMass law called true
    have hcontrols := calledMass_add_clearedMass law called false
    have htotal := law.mass_sum
    rw [Fintype.sum_prod_type] at htotal
    simp only [Fintype.sum_bool, Finset.sum_add_distrib] at htotal
    linarith

/-- The corpus case probability of a law on score groups and outcomes is the total case mass of
the groups. -/
theorem binaryCaseMass_snd_eq_sum (law : FiniteReportLaw (Score × Bool)) :
    law.binaryCaseMass Prod.snd = ∑ group, law.mass (group, true) := by
  simp only [FiniteReportLaw.binaryCaseMass, FiniteReportLaw.expectation, Fintype.sum_prod_type,
    Fintype.sum_bool]
  exact Finset.sum_congr rfl fun group _ ↦ by simp

/-- The prevalence of the confusion matrix of any score rule is the case probability of the
population law. -/
theorem prevalence_ruleConfusion (law : FiniteReportLaw (Score × Bool))
    (called : Score → Bool) :
    (ruleConfusion law called).prevalence = law.binaryCaseMass Prod.snd := by
  show calledMass law called true + clearedMass law called true = _
  rw [calledMass_add_clearedMass, binaryCaseMass_snd_eq_sum]

/-- **NOTE 2 section 5.4.** The three rates of a confusion matrix are bounded ratios: the recall
numerator `tp`, the false positive numerator `fp` and the precision numerator `tp` are each at
most their denominators `tp + fn`, `fp + tn` and `tp + fp`, which are at most one. -/
theorem confusion_rate_bounds (matrix : Foundations.ConfusionMatrix) :
    (matrix.tp ≤ matrix.tp + matrix.fn ∧ matrix.tp + matrix.fn ≤ 1) ∧
      (matrix.fp ≤ matrix.fp + matrix.tn ∧ matrix.fp + matrix.tn ≤ 1) ∧
      (matrix.tp ≤ matrix.tp + matrix.fp ∧ matrix.tp + matrix.fp ≤ 1) := by
  have htotal := matrix.mass_one
  have htp := matrix.tp_nonneg
  have hfp := matrix.fp_nonneg
  have htn := matrix.tn_nonneg
  have hfn := matrix.fn_nonneg
  exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩

/-- **NOTE 2 equation (15) for a quotient.** When `0 ≤ num ≤ den ≤ 1`, the expectation of the
quotient `num / den`, which Lean reads as zero where `den` vanishes, is the series of
expectations of `num * (1 - den) ^ power`. -/
theorem expectation_div_eq_tsum (law : FiniteReportLaw Context) (num den : Context → ℝ)
    (hnum : ∀ context, 0 ≤ num context) (hle : ∀ context, num context ≤ den context)
    (hden : ∀ context, den context ≤ 1) :
    law.expectation (fun context ↦ num context / den context) =
      ∑' power : ℕ, law.expectation (fun context ↦ num context * (1 - den context) ^ power) := by
  have hratio : (fun context ↦ num context / den context) = ratioOnDefined num den := by
    funext context
    unfold ratioOnDefined
    split_ifs with hpos
    · rfl
    · rw [le_antisymm (not_lt.mp hpos) ((hnum context).trans (hle context)), div_zero]
  rw [hratio]
  exact expectation_ratioOnDefined_eq_tsum law num den hnum hle hden

/-- **NOTE 2 section 5.4, true positive rate.** Over a finite law of study contexts, the expected
corpus recall of context-dependent confusion matrices, such as `ruleConfusion` of a
`thresholdRule` at one point of a threshold curve, is the series of expectations of
`tp * (1 - (tp + fn)) ^ power`. -/
theorem expectation_recallRate_eq_tsum (law : FiniteReportLaw Context)
    (matrix : Context → Foundations.ConfusionMatrix) :
    law.expectation (fun context ↦ (matrix context).recallRate) =
      ∑' power : ℕ, law.expectation (fun context ↦
        (matrix context).tp * (1 - ((matrix context).tp + (matrix context).fn)) ^ power) :=
  expectation_div_eq_tsum law (fun context ↦ (matrix context).tp)
    (fun context ↦ (matrix context).tp + (matrix context).fn)
    (fun context ↦ (matrix context).tp_nonneg)
    (fun context ↦ (confusion_rate_bounds (matrix context)).1.1)
    (fun context ↦ (confusion_rate_bounds (matrix context)).1.2)

/-- **NOTE 2 section 5.4, false positive rate.** The expected corpus false positive rate of
context-dependent confusion matrices is the series of expectations of
`fp * (1 - (fp + tn)) ^ power`. -/
theorem expectation_fpr_eq_tsum (law : FiniteReportLaw Context)
    (matrix : Context → Foundations.ConfusionMatrix) :
    law.expectation (fun context ↦ (matrix context).fpr) =
      ∑' power : ℕ, law.expectation (fun context ↦
        (matrix context).fp * (1 - ((matrix context).fp + (matrix context).tn)) ^ power) :=
  expectation_div_eq_tsum law (fun context ↦ (matrix context).fp)
    (fun context ↦ (matrix context).fp + (matrix context).tn)
    (fun context ↦ (matrix context).fp_nonneg)
    (fun context ↦ (confusion_rate_bounds (matrix context)).2.1.1)
    (fun context ↦ (confusion_rate_bounds (matrix context)).2.1.2)

/-- **NOTE 2 section 5.4, positive predictive value.** The expected corpus precision of
context-dependent confusion matrices is the series of expectations of
`tp * (1 - (tp + fp)) ^ power`. -/
theorem expectation_precision_eq_tsum (law : FiniteReportLaw Context)
    (matrix : Context → Foundations.ConfusionMatrix) :
    law.expectation (fun context ↦ (matrix context).precision) =
      ∑' power : ℕ, law.expectation (fun context ↦
        (matrix context).tp * (1 - ((matrix context).tp + (matrix context).fp)) ^ power) :=
  expectation_div_eq_tsum law (fun context ↦ (matrix context).tp)
    (fun context ↦ (matrix context).tp + (matrix context).fp)
    (fun context ↦ (matrix context).tp_nonneg)
    (fun context ↦ (confusion_rate_bounds (matrix context)).2.2.1)
    (fun context ↦ (confusion_rate_bounds (matrix context)).2.2.2)

/-- **NOTE 2 section 5.4, ROC curve.** The recall, the false positive rate and the precision of
any confusion matrix lie in the unit interval, so every point of a ROC or precision-recall
curve lies in the unit square. -/
theorem rates_mem_unit (matrix : Foundations.ConfusionMatrix) :
    (0 ≤ matrix.recallRate ∧ matrix.recallRate ≤ 1) ∧ (0 ≤ matrix.fpr ∧ matrix.fpr ≤ 1) ∧
      (0 ≤ matrix.precision ∧ matrix.precision ≤ 1) := by
  obtain ⟨⟨hrecall, _⟩, ⟨hfalse, _⟩, ⟨hprecision, _⟩⟩ := confusion_rate_bounds matrix
  have htp := matrix.tp_nonneg
  have hfp := matrix.fp_nonneg
  exact ⟨⟨div_nonneg htp (htp.trans hrecall), div_le_one_of_le₀ hrecall (htp.trans hrecall)⟩,
    ⟨div_nonneg hfp (hfp.trans hfalse), div_le_one_of_le₀ hfalse (hfp.trans hfalse)⟩,
    ⟨div_nonneg htp (htp.trans hprecision),
      div_le_one_of_le₀ hprecision (htp.trans hprecision)⟩⟩

/-- The strict threshold rule: a score group is called positive exactly when its value exceeds
the threshold, so a value tied with the threshold is cleared. -/
def thresholdRule (value : Score → ℝ) (threshold : ℝ) : Score → Bool :=
  fun group ↦ decide (threshold < value group)

/-- **NOTE 2 section 5.4, threshold curves.** Raising the threshold never increases the called
mass of either outcome class: the true and the false positive masses along the threshold curve
are antitone in the threshold. -/
theorem calledMass_thresholdRule_antitone (law : FiniteReportLaw (Score × Bool))
    (value : Score → ℝ) (outcome : Bool) :
    Antitone fun threshold ↦ calledMass law (thresholdRule value threshold) outcome := by
  intro lower upper hle
  simp only [calledMass]
  refine Finset.sum_le_sum fun group _ ↦ ?_
  by_cases hupper : upper < value group
  · have hlower : lower < value group := lt_of_le_of_lt hle hupper
    simp [thresholdRule, hupper, hlower]
  · by_cases hlower : lower < value group
    · simp [thresholdRule, hupper, hlower, law.mass_nonneg]
    · simp [thresholdRule, hupper, hlower]

/-- The rule calling every score group whose value is at least the value of a cutoff group, so
every group tied with the cutoff is called together with it. -/
def atLeastRule (value : Score → ℝ) (cutoff : Score) : Score → Bool :=
  fun group ↦ decide (value cutoff ≤ value group)

/-- **NOTE 2 section 5.4, average precision under a fixed finite-score definition.** Every
score group contributes its case mass times the precision of the rule calling every group that
scores at least as high, and the sum is divided by the case probability. Tied score values
enter together through the rule, and the quotient is Lean's zero when the law has no cases. -/
def averagePrecision (law : FiniteReportLaw (Score × Bool)) (value : Score → ℝ) : ℝ :=
  (∑ group, law.mass (group, true) * (ruleConfusion law (atLeastRule value group)).precision) /
    law.binaryCaseMass Prod.snd

/-- **NOTE 2 section 5.4, average precision.** Average precision is the sum over score groups
of the recall increment `a_s / p` that the group contributes times the precision at the
group's cutoff. -/
theorem averagePrecision_eq_sum_recall_increment (law : FiniteReportLaw (Score × Bool))
    (value : Score → ℝ) :
    averagePrecision law value =
      ∑ group, law.mass (group, true) / law.binaryCaseMass Prod.snd *
        (ruleConfusion law (atLeastRule value group)).precision := by
  rw [averagePrecision, Finset.sum_div]
  exact Finset.sum_congr rfl fun group _ ↦ by ring

/-- **NOTE 2 section 5.4.** Every average-precision summand is a bounded ratio: the case mass of
the group times the true positive mass at its cutoff is at most the called mass at that cutoff,
which is at most one. -/
theorem averagePrecision_summand_bounds (law : FiniteReportLaw (Score × Bool))
    (value : Score → ℝ) (group : Score) :
    0 ≤ law.mass (group, true) * calledMass law (atLeastRule value group) true ∧
      law.mass (group, true) * calledMass law (atLeastRule value group) true ≤
        calledMass law (atLeastRule value group) true +
          calledMass law (atLeastRule value group) false ∧
      calledMass law (atLeastRule value group) true +
          calledMass law (atLeastRule value group) false ≤ 1 := by
  have hcase := law.mass_nonneg (group, true)
  have hcalled := calledMass_nonneg law (atLeastRule value group) true
  have hprecision : calledMass law (atLeastRule value group) true ≤
      calledMass law (atLeastRule value group) true +
        calledMass law (atLeastRule value group) false ∧
      calledMass law (atLeastRule value group) true +
        calledMass law (atLeastRule value group) false ≤ 1 :=
    (confusion_rate_bounds (ruleConfusion law (atLeastRule value group))).2.2
  have hself : law.mass (group, true) ≤ calledMass law (atLeastRule value group) true := by
    unfold calledMass
    refine le_trans (le_of_eq ?_) (Finset.single_le_sum
      (f := fun other ↦ if atLeastRule value group other then law.mass (other, true) else 0)
      (fun other _ ↦ ?_) (Finset.mem_univ group))
    · simp [atLeastRule]
    · dsimp only
      split_ifs
      · exact law.mass_nonneg _
      · exact le_refl 0
  have htpOne : calledMass law (atLeastRule value group) true ≤ 1 := by
    linarith [hprecision.1, hprecision.2]
  have hscaled := mul_le_mul_of_nonneg_right (hself.trans htpOne) hcalled
  refine ⟨mul_nonneg hcase hcalled, ?_, hprecision.2⟩
  linarith [hprecision.1]

/-- **NOTE 2 section 5.4.** The average-precision numerator is at least zero and at most the
case probability, which is at most one, so average precision is a bounded ratio. -/
theorem averagePrecision_numerator_bounds (law : FiniteReportLaw (Score × Bool))
    (value : Score → ℝ) :
    0 ≤ ∑ group, law.mass (group, true) *
        (ruleConfusion law (atLeastRule value group)).precision ∧
      ∑ group, law.mass (group, true) *
          (ruleConfusion law (atLeastRule value group)).precision ≤
        law.binaryCaseMass Prod.snd ∧
      law.binaryCaseMass Prod.snd ≤ 1 := by
  have hunit : ∀ group, 0 ≤ (ruleConfusion law (atLeastRule value group)).precision ∧
      (ruleConfusion law (atLeastRule value group)).precision ≤ 1 := fun group ↦
    (rates_mem_unit (ruleConfusion law (atLeastRule value group))).2.2
  refine ⟨Finset.sum_nonneg fun group _ ↦ mul_nonneg (law.mass_nonneg _) (hunit group).1, ?_,
    (binaryCaseMass_mem_unit law Prod.snd).2⟩
  rw [binaryCaseMass_snd_eq_sum]
  exact Finset.sum_le_sum fun group _ ↦
    mul_le_of_le_one_right (law.mass_nonneg _) (hunit group).2

/-- **NOTE 2 section 5.4.** Average precision lies in the unit interval. -/
theorem averagePrecision_mem_unit (law : FiniteReportLaw (Score × Bool)) (value : Score → ℝ) :
    0 ≤ averagePrecision law value ∧ averagePrecision law value ≤ 1 := by
  obtain ⟨hnum, hle, _⟩ := averagePrecision_numerator_bounds law value
  exact ⟨div_nonneg hnum (hnum.trans hle), div_le_one_of_le₀ hle (hnum.trans hle)⟩

/-- **NOTE 2 equation (15) for average precision.** Over a finite law of study contexts, the
expected average precision is the series of expectations of the precision-weighted case mass
times `(1 - p) ^ power`. -/
theorem expectation_averagePrecision_eq_tsum (law : FiniteReportLaw Context)
    (population : Context → FiniteReportLaw (Score × Bool)) (value : Score → ℝ) :
    law.expectation (fun context ↦ averagePrecision (population context) value) =
      ∑' power : ℕ, law.expectation (fun context ↦
        (∑ group, (population context).mass (group, true) *
            (ruleConfusion (population context) (atLeastRule value group)).precision) *
          (1 - (population context).binaryCaseMass Prod.snd) ^ power) :=
  expectation_div_eq_tsum law
    (fun context ↦ ∑ group, (population context).mass (group, true) *
      (ruleConfusion (population context) (atLeastRule value group)).precision)
    (fun context ↦ (population context).binaryCaseMass Prod.snd)
    (fun context ↦ (averagePrecision_numerator_bounds (population context) value).1)
    (fun context ↦ (averagePrecision_numerator_bounds (population context) value).2.1)
    (fun context ↦ (averagePrecision_numerator_bounds (population context) value).2.2)

/-- **NOTE 2 equation (15) for one average-precision summand.** The expected case mass of a
score group times the precision at its cutoff is the series of expectations of
`a_s tp_s * (1 - (tp_s + fp_s)) ^ power`, a bounded ratio of polynomial functionals. -/
theorem expectation_averagePrecisionSummand_eq_tsum (law : FiniteReportLaw Context)
    (population : Context → FiniteReportLaw (Score × Bool)) (value : Score → ℝ)
    (group : Score) :
    law.expectation (fun context ↦ (population context).mass (group, true) *
        (ruleConfusion (population context) (atLeastRule value group)).precision) =
      ∑' power : ℕ, law.expectation (fun context ↦
        (population context).mass (group, true) *
            calledMass (population context) (atLeastRule value group) true *
          (1 - (calledMass (population context) (atLeastRule value group) true +
            calledMass (population context) (atLeastRule value group) false)) ^ power) := by
  have hsummand : (fun context ↦ (population context).mass (group, true) *
      (ruleConfusion (population context) (atLeastRule value group)).precision) =
        fun context ↦ (population context).mass (group, true) *
            calledMass (population context) (atLeastRule value group) true /
          (calledMass (population context) (atLeastRule value group) true +
            calledMass (population context) (atLeastRule value group) false) :=
    funext fun context ↦ (mul_div_assoc _ _ _).symm
  rw [hsummand]
  exact expectation_div_eq_tsum law
    (fun context ↦ (population context).mass (group, true) *
      calledMass (population context) (atLeastRule value group) true)
    (fun context ↦ calledMass (population context) (atLeastRule value group) true +
      calledMass (population context) (atLeastRule value group) false)
    (fun context ↦ (averagePrecision_summand_bounds (population context) value group).1)
    (fun context ↦ (averagePrecision_summand_bounds (population context) value group).2.1)
    (fun context ↦ (averagePrecision_summand_bounds (population context) value group).2.2)

end ScoreRules

/-! ### Degree accounting -/

section PopulationPolynomials

open MvPolynomial

variable {State : Type*} [Fintype State]

/-- The linear polynomial `∑_s f(s) X_s` in the population probability vector, whose value at a
law is the expectation of the observable `f`. -/
def expectationPolynomial (value : State → ℝ) : MvPolynomial State ℝ :=
  ∑ state, C (value state) * X state

/-- The expectation polynomial evaluates at the mass vector to the corpus expectation. -/
theorem eval_expectationPolynomial (law : FiniteReportLaw State) (value : State → ℝ) :
    eval law.mass (expectationPolynomial value) = law.expectation value := by
  simp only [expectationPolynomial, map_sum, map_mul, eval_C, eval_X,
    FiniteReportLaw.expectation]
  exact Finset.sum_congr rfl fun state _ ↦ mul_comm _ _

/-- The expectation polynomial has total degree at most one. -/
theorem totalDegree_expectationPolynomial_le (value : State → ℝ) :
    (expectationPolynomial value).totalDegree ≤ 1 := by
  refine (totalDegree_finset_sum _ _).trans (Finset.sup_le fun state _ ↦ ?_)
  calc (C (value state) * X state : MvPolynomial State ℝ).totalDegree
      ≤ (C (value state) : MvPolynomial State ℝ).totalDegree +
          (X state : MvPolynomial State ℝ).totalDegree := totalDegree_mul _ _
    _ = 1 := by rw [totalDegree_C, totalDegree_X, zero_add]

/-- The quadratic polynomial `∑_{s,t} g(s, t) X_s X_t`, whose value at a law is the expectation
of `g` over two independent draws. -/
def pairPolynomial (credit : State → State → ℝ) : MvPolynomial State ℝ :=
  ∑ first, ∑ second, C (credit first second) * (X first * X second)

/-- The pair polynomial evaluates at the mass vector to the double expectation. -/
theorem eval_pairPolynomial (law : FiniteReportLaw State) (credit : State → State → ℝ) :
    eval law.mass (pairPolynomial credit) =
      law.expectation (fun first ↦ law.expectation (fun second ↦ credit first second)) := by
  simp only [pairPolynomial, map_sum, map_mul, eval_C, eval_X, FiniteReportLaw.expectation,
    Finset.mul_sum]
  exact Finset.sum_congr rfl fun first _ ↦ Finset.sum_congr rfl fun second _ ↦ by ring

/-- The pair polynomial has total degree at most two. -/
theorem totalDegree_pairPolynomial_le (credit : State → State → ℝ) :
    (pairPolynomial credit).totalDegree ≤ 2 := by
  refine (totalDegree_finset_sum _ _).trans (Finset.sup_le fun first _ ↦ ?_)
  refine (totalDegree_finset_sum _ _).trans (Finset.sup_le fun second _ ↦ ?_)
  calc (C (credit first second) * (X first * X second) : MvPolynomial State ℝ).totalDegree
      ≤ (C (credit first second) : MvPolynomial State ℝ).totalDegree +
          (X first * X second : MvPolynomial State ℝ).totalDegree := totalDegree_mul _ _
    _ ≤ 0 + (1 + 1) := by
        rw [totalDegree_C]
        exact Nat.add_le_add_left ((totalDegree_mul _ _).trans (by
          rw [totalDegree_X, totalDegree_X])) 0
    _ = 2 := rfl

/-- The covariance polynomial: the expectation polynomial of the product minus the product of
the expectation polynomials. -/
def covariancePolynomial (score outcome : State → ℝ) : MvPolynomial State ℝ :=
  expectationPolynomial (fun state ↦ score state * outcome state) -
    expectationPolynomial score * expectationPolynomial outcome

/-- The covariance polynomial evaluates at the mass vector to the corpus covariance. -/
theorem eval_covariancePolynomial (law : FiniteReportLaw State) (score outcome : State → ℝ) :
    eval law.mass (covariancePolynomial score outcome) = law.covariance score outcome := by
  rw [covariancePolynomial, map_sub, map_mul, eval_expectationPolynomial,
    eval_expectationPolynomial, eval_expectationPolynomial,
    FiniteReportLaw.covariance_eq_rawMoments]

/-- The covariance polynomial has total degree at most two. -/
theorem totalDegree_covariancePolynomial_le (score outcome : State → ℝ) :
    (covariancePolynomial score outcome).totalDegree ≤ 2 := by
  have hproduct := totalDegree_expectationPolynomial_le (fun state ↦ score state * outcome state)
  have hscore := totalDegree_expectationPolynomial_le score
  have houtcome := totalDegree_expectationPolynomial_le outcome
  refine (totalDegree_sub _ _).trans (max_le (hproduct.trans (by norm_num)) ?_)
  exact (totalDegree_mul _ _).trans (by omega)

/-- The numerator polynomial `16 C²` of NOTE 2 (21). -/
def correlationNumeratorPolynomial (score outcome : State → ℝ) : MvPolynomial State ℝ :=
  C 16 * covariancePolynomial score outcome ^ 2

/-- The denominator polynomial `16 V_S V_Y` of NOTE 2 (21). -/
def correlationDenominatorPolynomial (score outcome : State → ℝ) : MvPolynomial State ℝ :=
  C 16 * (covariancePolynomial score score * covariancePolynomial outcome outcome)

/-- **NOTE 2 section 5.4.** The numerator polynomial evaluates to the correlation numerator. -/
theorem eval_correlationNumeratorPolynomial (law : FiniteReportLaw State)
    (score outcome : State → ℝ) :
    eval law.mass (correlationNumeratorPolynomial score outcome) =
      correlationNumerator law score outcome := by
  rw [correlationNumeratorPolynomial, map_mul, map_pow, eval_C, eval_covariancePolynomial,
    correlationNumerator]

/-- **NOTE 2 section 5.4.** The denominator polynomial evaluates to the correlation
denominator. -/
theorem eval_correlationDenominatorPolynomial (law : FiniteReportLaw State)
    (score outcome : State → ℝ) :
    eval law.mass (correlationDenominatorPolynomial score outcome) =
      correlationDenominator law score outcome := by
  rw [correlationDenominatorPolynomial, map_mul, map_mul, eval_C, eval_covariancePolynomial,
    eval_covariancePolynomial, correlationDenominator]
  rfl

/-- **NOTE 2 section 5.4, degree four.** The correlation numerator polynomial has total degree at
most four. -/
theorem totalDegree_correlationNumeratorPolynomial_le (score outcome : State → ℝ) :
    (correlationNumeratorPolynomial score outcome).totalDegree ≤ 4 := by
  have hcovariance := totalDegree_covariancePolynomial_le score outcome
  refine (totalDegree_mul _ _).trans ?_
  rw [totalDegree_C, zero_add]
  exact (totalDegree_pow _ _).trans (by omega)

/-- **NOTE 2 section 5.4, degree four.** The correlation denominator polynomial has total degree
at most four. -/
theorem totalDegree_correlationDenominatorPolynomial_le (score outcome : State → ℝ) :
    (correlationDenominatorPolynomial score outcome).totalDegree ≤ 4 := by
  have hscore := totalDegree_covariancePolynomial_le score score
  have houtcome := totalDegree_covariancePolynomial_le outcome outcome
  refine (totalDegree_mul _ _).trans ?_
  rw [totalDegree_C, zero_add]
  exact (totalDegree_mul _ _).trans (by omega)

omit [Fintype State] in
/-- **NOTE 2 section 5.4, degree accounting.** If a numerator polynomial has degree at most `a`
and a denominator polynomial degree at most `b`, the `power`-th expansion term
`num * (1 - den) ^ power` has degree at most `a + power * b`. -/
theorem totalDegree_expansionTerm_le (num den : MvPolynomial State ℝ)
    (numDegree denDegree power : ℕ) (hnum : num.totalDegree ≤ numDegree)
    (hden : den.totalDegree ≤ denDegree) :
    (num * (1 - den) ^ power).totalDegree ≤ numDegree + power * denDegree := by
  refine (totalDegree_mul _ _).trans (Nat.add_le_add hnum ?_)
  refine (totalDegree_pow _ _).trans (Nat.mul_le_mul_left power ?_)
  refine (totalDegree_sub _ _).trans (max_le ?_ hden)
  rw [totalDegree_one]
  exact Nat.zero_le _

/-- **NOTE 2 section 5.4.** The `power`-th term of the squared-correlation expansion is a
polynomial of total degree at most `4 * (power + 1)` in the population probability vector. -/
theorem totalDegree_correlationTerm_le (score outcome : State → ℝ) (power : ℕ) :
    (correlationNumeratorPolynomial score outcome *
      (1 - correlationDenominatorPolynomial score outcome) ^ power).totalDegree ≤
        4 * (power + 1) := by
  have hterm := totalDegree_expansionTerm_le _ _ 4 4 power
    (totalDegree_correlationNumeratorPolynomial_le score outcome)
    (totalDegree_correlationDenominatorPolynomial_le score outcome)
  calc _ ≤ 4 + power * 4 := hterm
    _ = 4 * (power + 1) := by ring

/-- The expansion term polynomial evaluates to the squared-correlation expansion term. -/
theorem eval_correlationTerm (law : FiniteReportLaw State) (score outcome : State → ℝ)
    (power : ℕ) :
    eval law.mass (correlationNumeratorPolynomial score outcome *
        (1 - correlationDenominatorPolynomial score outcome) ^ power) =
      correlationNumerator law score outcome *
        (1 - correlationDenominator law score outcome) ^ power := by
  rw [map_mul, map_pow, map_sub, map_one, eval_correlationNumeratorPolynomial,
    eval_correlationDenominatorPolynomial]

/-- The AUC numerator polynomial `4A`: four times the pair polynomial of the ranking credit. -/
def aucNumeratorPolynomial (score : State → ℝ) (outcome : State → Bool) :
    MvPolynomial State ℝ :=
  C 4 * pairPolynomial fun first second ↦
    if outcome first && !outcome second then
      empiricalAUCComparison (score first) (score second) else 0

/-- The AUC denominator polynomial `4p(1 - p)`. -/
def aucDenominatorPolynomial (outcome : State → Bool) : MvPolynomial State ℝ :=
  C 4 * (expectationPolynomial (fun state ↦ if outcome state then 1 else 0) *
    (1 - expectationPolynomial (fun state ↦ if outcome state then 1 else 0)))

/-- **NOTE 2 section 5.4.** The AUC expansion term polynomial evaluates to the AUC expansion
term. -/
theorem eval_aucTerm (law : FiniteReportLaw State) (score : State → ℝ)
    (outcome : State → Bool) (power : ℕ) :
    eval law.mass (aucNumeratorPolynomial score outcome *
        (1 - aucDenominatorPolynomial outcome) ^ power) =
      aucNumerator law score outcome * (1 - aucDenominator law outcome) ^ power := by
  simp only [aucNumeratorPolynomial, aucDenominatorPolynomial, map_mul, map_pow, map_sub,
    map_one, eval_C, eval_pairPolynomial, eval_expectationPolynomial, aucNumerator,
    aucDenominator]
  rfl

/-- **NOTE 2 section 5.4, degree two.** The `power`-th term of the AUC expansion is a polynomial
of total degree at most `2 * (power + 1)` in the population probability vector. -/
theorem totalDegree_aucTerm_le (score : State → ℝ) (outcome : State → Bool) (power : ℕ) :
    (aucNumeratorPolynomial score outcome *
      (1 - aucDenominatorPolynomial outcome) ^ power).totalDegree ≤ 2 * (power + 1) := by
  have hcase := totalDegree_expectationPolynomial_le
    (fun state : State ↦ if outcome state then (1 : ℝ) else 0)
  have hnum : (aucNumeratorPolynomial score outcome).totalDegree ≤ 2 := by
    refine (totalDegree_mul _ _).trans ?_
    rw [totalDegree_C, zero_add]
    exact totalDegree_pairPolynomial_le _
  have hden : (aucDenominatorPolynomial outcome).totalDegree ≤ 2 := by
    refine (totalDegree_mul _ _).trans ?_
    rw [totalDegree_C, zero_add]
    refine (totalDegree_mul _ _).trans ?_
    have hcomplement := (totalDegree_sub (1 : MvPolynomial State ℝ)
      (expectationPolynomial fun state : State ↦ if outcome state then (1 : ℝ) else 0))
    rw [totalDegree_one] at hcomplement
    omega
  calc _ ≤ 2 + power * 2 := totalDegree_expansionTerm_le _ _ 2 2 power hnum hden
    _ = 2 * (power + 1) := by ring

end PopulationPolynomials

section ReplicaReadout

open MvPolynomial

variable {m : ℕ}

/-- The tie between the two corpus product laws: `FiniteGeneticTransition.piLaw` of identical
coordinates is `HWEInteractionLaw.independentLaw`. -/
theorem piLaw_eq_independentLaw {Slot Letter : Type*} [Fintype Slot] [DecidableEq Slot]
    [Fintype Letter] (law : Slot → FiniteReportLaw Letter) :
    FiniteGeneticTransition.piLaw law = HWEInteractionLaw.independentLaw law :=
  FiniteReportLaw.ext fun _ ↦ rfl

/-- **NOTE 2 section 5.4, replica event of a monomial.** The event on a cohort of `size`
replicas that the first `∑_a e_a` slots read out the letters of the corpus exponent listing of
`e`, every later slot being free. -/
def monomialEvent (size : ℕ) (exponent : Fin m → ℕ) (replica : Fin size → Fin m) : Prop :=
  ∀ (slot : Fin size) (hslot : (slot : ℕ) < ∑ letter, exponent letter),
    replica slot = ReplicaMomentCompleteness.exponentListing m exponent ⟨slot, hslot⟩

instance (size : ℕ) (exponent : Fin m → ℕ) : DecidablePred (monomialEvent size exponent) :=
  fun replica ↦ by
    unfold monomialEvent
    infer_instance

/-- The indicator of one slot of a monomial event: the listed letter is read on a listed slot,
and a free slot always passes. -/
def slotIndicator {size : ℕ} (exponent : Fin m → ℕ) (slot : Fin size) (letter : Fin m) : ℝ :=
  if hslot : (slot : ℕ) < ∑ index, exponent index then
    (if letter = ReplicaMomentCompleteness.exponentListing m exponent ⟨slot, hslot⟩ then 1
      else 0)
  else 1

/-- The indicator of a monomial event is the product of its slot indicators. -/
theorem definedIndicator_monomialEvent (size : ℕ) (exponent : Fin m → ℕ)
    (replica : Fin size → Fin m) :
    definedIndicator (monomialEvent size exponent) replica =
      ∏ slot, slotIndicator exponent slot (replica slot) := by
  unfold definedIndicator
  by_cases hevent : monomialEvent size exponent replica
  · rw [if_pos hevent]
    refine (Finset.prod_eq_one fun slot _ ↦ ?_).symm
    unfold slotIndicator
    split_ifs with hslot hmatch
    · rfl
    · exact absurd (hevent slot hslot) hmatch
    · rfl
  · rw [if_neg hevent]
    unfold monomialEvent at hevent
    push_neg at hevent
    obtain ⟨slot, hslot, hmismatch⟩ := hevent
    refine (Finset.prod_eq_zero (Finset.mem_univ slot) ?_).symm
    unfold slotIndicator
    rw [dif_pos hslot, if_neg hmismatch]

/-- A product over `size` slots whose factor is one beyond the first `bound` slots is the
product over the first `bound` slots. -/
theorem prod_dite_lt (size bound : ℕ) (hbound : bound ≤ size) (factor : Fin bound → ℝ) :
    ∏ slot : Fin size, (if hslot : (slot : ℕ) < bound then factor ⟨slot, hslot⟩ else 1) =
      ∏ index, factor index := by
  calc ∏ slot : Fin size, (if hslot : (slot : ℕ) < bound then factor ⟨slot, hslot⟩ else 1)
      = ∏ j ∈ Finset.range size, (if hj : j < bound then factor ⟨j, hj⟩ else 1) :=
        Fin.prod_univ_eq_prod_range (fun j ↦ if hj : j < bound then factor ⟨j, hj⟩ else 1) size
    _ = (∏ j ∈ Finset.range bound, (if hj : j < bound then factor ⟨j, hj⟩ else 1)) *
          ∏ j ∈ Finset.Ico bound size, (if hj : j < bound then factor ⟨j, hj⟩ else 1) :=
        (Finset.prod_range_mul_prod_Ico _ hbound).symm
    _ = ∏ j ∈ Finset.range bound, (if hj : j < bound then factor ⟨j, hj⟩ else 1) := by
        rw [Finset.prod_eq_one (s := Finset.Ico bound size)
          (f := fun j ↦ if hj : j < bound then factor ⟨j, hj⟩ else 1)
          fun j hj ↦ dif_neg (not_lt.mpr (Finset.mem_Ico.mp hj).1), mul_one]
    _ = ∏ index : Fin bound, factor index := by
        rw [← Fin.prod_univ_eq_prod_range]
        exact Finset.prod_congr rfl fun index _ ↦ dif_pos index.isLt

/-- **NOTE 2 section 5.4, monomial moments as replica events.** A monomial `∏_a q_a ^ e_a` of
degree at most `size` in a population probability vector is the probability of the monomial
event under the corpus product law of `size` independent replicas. -/
theorem expectation_monomialEvent (law : FiniteReportLaw (Fin m)) (size : ℕ)
    (exponent : Fin m → ℕ) (hdegree : ∑ letter, exponent letter ≤ size) :
    (FiniteGeneticTransition.piLaw fun _ : Fin size ↦ law).expectation
        (definedIndicator (monomialEvent size exponent)) =
      ∏ letter, law.mass letter ^ exponent letter := by
  have hindicator : definedIndicator (monomialEvent size exponent) = fun replica ↦
      ∏ slot, slotIndicator exponent slot (replica slot) :=
    funext fun replica ↦ definedIndicator_monomialEvent size exponent replica
  have hfactor : ∀ slot : Fin size, law.expectation (slotIndicator exponent slot) =
      if hslot : (slot : ℕ) < ∑ letter, exponent letter then
        law.mass (ReplicaMomentCompleteness.exponentListing m exponent ⟨slot, hslot⟩) else 1 := by
    intro slot
    by_cases hslot : (slot : ℕ) < ∑ letter, exponent letter
    · have hslotIndicator : slotIndicator exponent slot = fun letter ↦
          if letter = ReplicaMomentCompleteness.exponentListing m exponent ⟨slot, hslot⟩ then
            (1 : ℝ) else 0 :=
        funext fun letter ↦ dif_pos hslot
      rw [hslotIndicator, dif_pos hslot]
      simp [FiniteReportLaw.expectation]
    · have hslotIndicator : slotIndicator exponent slot = fun _ ↦ (1 : ℝ) :=
        funext fun _ ↦ dif_neg hslot
      rw [hslotIndicator, dif_neg hslot]
      exact FiniteIndependentMoments.expectation_const law 1
  rw [hindicator, piLaw_eq_independentLaw,
    HWEInteractionLaw.expectation_independent_product (fun _ : Fin size ↦ law)
      (slotIndicator exponent)]
  simp only [hfactor]
  rw [prod_dite_lt size _ hdegree
    (fun index ↦ law.mass (ReplicaMomentCompleteness.exponentListing m exponent index))]
  exact (ReplicaMomentCompleteness.prod_exponentListing m exponent
    (ReplicaMomentCompleteness.simplexPoint m law)).trans
      (ReplicaMomentCompleteness.monomialMap_simplexPoint m law exponent)

/-- **NOTE 2 section 5.4, finite-replica readout.** Over a finite law of study contexts, the
expectation of any polynomial functional of total degree at most `size` in the population
probability vector is the expectation, under the replica cohort law of `size` conditionally
independent replicas, of the signed combination of monomial-event indicators with the
polynomial's coefficients. -/
theorem expectation_eval_eq_replicaReadout (law : FiniteReportLaw Context)
    (population : Context → FiniteReportLaw (Fin m)) (polynomial : MvPolynomial (Fin m) ℝ)
    (size : ℕ) (hdegree : polynomial.totalDegree ≤ size) :
    law.expectation (fun context ↦ eval (population context).mass polynomial) =
      (replicaCohortLaw law population size).expectation (fun replica ↦
        ∑ exponent ∈ polynomial.support, polynomial.coeff exponent *
          definedIndicator (monomialEvent size exponent) replica) := by
  rw [replicaCohortLaw, FiniteReportLaw.expectation_bind]
  congr 1
  funext context
  have hlinear : (FiniteGeneticTransition.piLaw fun _ : Fin size ↦ population context).expectation
      (fun replica ↦ ∑ exponent ∈ polynomial.support, polynomial.coeff exponent *
        definedIndicator (monomialEvent size exponent) replica) =
        ∑ exponent ∈ polynomial.support, polynomial.coeff exponent *
          (FiniteGeneticTransition.piLaw fun _ : Fin size ↦ population context).expectation
            (definedIndicator (monomialEvent size exponent)) := by
    simp only [FiniteReportLaw.expectation, Finset.mul_sum]
    exact Finset.sum_comm.trans
      (Finset.sum_congr rfl fun exponent _ ↦ Finset.sum_congr rfl fun replica _ ↦ by ring)
  rw [hlinear, eval_eq']
  refine Finset.sum_congr rfl fun exponent hexponent ↦ ?_
  have hsupport := le_totalDegree hexponent
  rw [Finsupp.sum_fintype exponent (fun _ degree ↦ degree) fun _ ↦ rfl] at hsupport
  rw [expectation_monomialEvent (population context) size exponent
    (hsupport.trans hdegree)]

/-- **NOTE 2 section 5.4, squared correlation.** The `power`-th coefficient of the positive ratio
expansion of the squared correlation is an exact readout of `4 * (power + 1)` conditionally
independent replicas: the expectation of a signed combination of monomial-event indicators. -/
theorem expectation_correlationTerm_eq_replicaReadout (law : FiniteReportLaw Context)
    (population : Context → FiniteReportLaw (Fin m)) (score outcome : Fin m → ℝ) (power : ℕ) :
    law.expectation (fun context ↦ correlationNumerator (population context) score outcome *
        (1 - correlationDenominator (population context) score outcome) ^ power) =
      (replicaCohortLaw law population (4 * (power + 1))).expectation (fun replica ↦
        ∑ exponent ∈ (correlationNumeratorPolynomial score outcome *
            (1 - correlationDenominatorPolynomial score outcome) ^ power).support,
          (correlationNumeratorPolynomial score outcome *
            (1 - correlationDenominatorPolynomial score outcome) ^ power).coeff exponent *
            definedIndicator (monomialEvent (4 * (power + 1)) exponent) replica) := by
  rw [← expectation_eval_eq_replicaReadout law population _ _
    (totalDegree_correlationTerm_le score outcome power)]
  simp only [eval_correlationTerm]

/-- **NOTE 2 section 5.4, AUC.** The `power`-th coefficient of the positive ratio expansion of
the AUC is an exact readout of `2 * (power + 1)` conditionally independent replicas. -/
theorem expectation_aucTerm_eq_replicaReadout (law : FiniteReportLaw Context)
    (population : Context → FiniteReportLaw (Fin m)) (score : Fin m → ℝ)
    (outcome : Fin m → Bool) (power : ℕ) :
    law.expectation (fun context ↦ aucNumerator (population context) score outcome *
        (1 - aucDenominator (population context) outcome) ^ power) =
      (replicaCohortLaw law population (2 * (power + 1))).expectation (fun replica ↦
        ∑ exponent ∈ (aucNumeratorPolynomial score outcome *
            (1 - aucDenominatorPolynomial outcome) ^ power).support,
          (aucNumeratorPolynomial score outcome *
            (1 - aucDenominatorPolynomial outcome) ^ power).coeff exponent *
            definedIndicator (monomialEvent (2 * (power + 1)) exponent) replica) := by
  rw [← expectation_eval_eq_replicaReadout law population _ _
    (totalDegree_aucTerm_le score outcome power)]
  simp only [eval_aucTerm]

end ReplicaReadout

end

end Descent.Portability.ReplicaMetricInstances
