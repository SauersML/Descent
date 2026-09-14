/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.EndToEndBrierLaw

assert_below Descent.Decision Descent.Program

/-!
# The end-to-end law of clinical decision metrics

`EndToEndDiscriminationLaw` carries the AUC of a score through a neutral demographic history, and
`EndToEndBrierLaw` carries the repaired Brier loss and the calibration error.  This module carries
the threshold-rule metrics of `ReplicaMetricInstances`, built on the confusion matrix
`ruleConfusion` of any rule `called : Score → Bool`, threshold rules included, through every kernel
with dual moments (`EndToEndDiscriminationLaw.HasDualMoments`), in particular the history kernels.

The confusion report.  A report map `hap ↦ (s, b)` and a rule give the confusion report
`hap ↦ (called s, b)` (`confusionReport`).  Its four cells are the true positives `(true, true)`,
the false positives `(true, false)`, the true negatives `(false, false)` and the false negatives
`(false, true)` of the corpus confusion matrix (`calledMass_pushforward`,
`clearedMass_pushforward`, `ruleConfusion_pushforward`).  Every cell mass is a linear polynomial in
the haplotype frequencies (`EndToEndBrierLaw.cellPolynomial`).

The confusion table at budget one.  Under a kernel with budget-1 dual moments the expected
confusion table (`expectedConfusion`) is the moment confusion table (`momentConfusion`) of the
propagated budget-1 moments (`expectedConfusion_eq_momentConfusion`,
`expectedConfusion_historyEventKernel`, `expectedConfusion_rateHistoryKernel`).  Its cells are the
expected corpus confusion masses (`integral_ruleConfusion`).  The expected prevalence, which is the
case probability for every rule, and the expected called fraction are sums of two cells
(`integral_prevalence_calledFraction_eq_momentConfusion`).  Two kernels whose propagated budget-1
moments agree have equal expected confusion tables (`expectedConfusion_eq_of_moments_eq`).  So do
two histories whose propagated moments agree at any budget `n ≥ 1`, the AUC budget two included
(`expectedConfusion_historyEventKernel_eq_of_moments_eq`).

Net benefit.  `ruleNetBenefit` is `TP - FP · t / (1 - t)` at a threshold probability `t`, the value
of the linear polynomial `netBenefitPolynomial` (`eval_netBenefitPolynomial`,
`totalDegree_netBenefitPolynomial_le`).  The expected net benefit is one budget-1 dot product
(`expectedNetBenefit_eq_dotProduct`, `expectedNetBenefit_historyEventKernel`,
`expectedNetBenefit_rateHistoryKernel`).  It is the net benefit of the expected confusion table, so
the expectation query and the ratio-of-expectations query coincide
(`expectedNetBenefit_eq_expectedConfusion`).  Treating no one has net benefit zero and treating
everyone has `p - (1 - p) · t / (1 - t)` for the case probability `p` (`ruleNetBenefit_treatNone`,
`ruleNetBenefit_treatAll`, `expectedNetBenefit_treatNone_treatAll`).  The decision-curve comparison
of a rule with treating everyone is one budget-1 dot product
(`expectedNetBenefit_sub_treatAll_eq_dotProduct`).

Ratio metrics.  Sensitivity, specificity, positive and negative predictive value, F1, Youden's J
and the relative risk of the called group are rational functions of a confusion table
(`tableSensitivity`, `tableSpecificity`, `tablePPV`, `tableNPV`, `tableF1`, `tableYouden`,
`tableRelativeRisk`).  On the confusion report law the sensitivity and the positive predictive
value are the corpus recall and precision (`tableSensitivity_tablePPV_pushforward`).  In
ratio-of-expectations form every metric of the expected table is the same metric of the moment
table, a rational function of the budget-1 propagated moments, and so is its target-over-source
portability (`expectedMetricPortability`, `expectedMetricPortability_eq_momentConfusion`,
`expectedMetricPortability_historyEventKernel`, `expectedMetricPortability_rateHistoryKernel`).
Two histories agreeing at any budget `n ≥ 1` have equal portability of every such metric
(`expectedMetricPortability_eq_of_moments_eq`, `decisionMetricPortabilities_eq_of_moments_eq`).

Expected sensitivity and predictive value.  The expected per-population recall `E[TP / p]` and
precision `E[TP / (TP + FP)]`, read by Lean as zero at a vanishing denominator, are expected
positive quotients `E[TP / (TP + c)]` for a cell `c` (`expectedPositiveQuotient`,
`integral_recallRate_precision`).  Since `0 ≤ TP ≤ TP + c ≤ 1` for every rule, the geometric
expansion of `PositiveRatioExpansion` gives the series of the expectations of `TP (1 - (TP + c))ᵏ`
(`integral_boundedQuotient_eq_tsum`, `expectedPositiveQuotient_eq_tsum`), a polynomial of total
degree at most `k + 1` (`positiveTermPolynomial`, `totalDegree_positiveTermPolynomial_le`).
Through the propagated moments the expectation is a series of budget-`(k + 1)` dot products
(`expectedPositiveQuotient_eq_tsum_dotProduct`, `expectedPositiveQuotient_historyEventKernel`,
`expectedPositiveQuotient_rateHistoryKernel`, `integral_recallRate_precision_historyEventKernel`).
Two histories agreeing at every budget `k + 1` have equal expected recall and precision
(`integral_recallRate_precision_eq_of_moments_eq`).

Prevalence shift.  With equal positive recall and equal positive false positive rate, precision
ports exactly when prevalence ports (`precision_eq_iff_prevalence_eq`).  The explicit report laws
`witnessSourceLaw` and `witnessTargetLaw` move the prevalence from one half to one fifth.  The
identity rule keeps recall four fifths and false positive rate one fifth, so sensitivity and
specificity port exactly, while the precision falls from four fifths to one half
(`prevalenceShift_witness`).

Significance.  Every threshold metric a clinical polygenic score is reported by, in its
ratio-of-expectations form and as expected net benefit, runs from the demographic process law
through one budget-1 matrix computation.  That is below the budget two of AUC and the budget four
of the squared correlation.  Only the expectations of the per-population ratios need the whole
budget family.

Scope.  Score groups form a finite alphabet, outcomes are binary and the rule is deterministic;
one chromosome is sampled per individual.  No pair of histories with equal budget-1 moments and
different expected recall is constructed here, and truncation certificates for the series are not
restated.

## Empirical status

None.  The bodies here are polynomial identities, a pointwise geometric series, arithmetic on
explicit finite laws and integrals of polynomials against Markov kernels whose moments are matrix
computations of supplied rates, so no measurement can bear on them.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.EndToEndDecisionLaw

open MeasureTheory ProbabilityTheory MvPolynomial Descent.Coalescent PartialHaplotypeCarrier
  PartialHaplotypeDualGenerator PartialHaplotypeDualSemigroup NeutralFellerGenerator
  NeutralPolynomialSemigroup PartialHaplotypeMicroscopicApproximation PartialHaplotypePulseKernel
  NeutralPulseHistoryKernel NeutralRateHistoryRealization NeutralRateHistoryKernel
  ReplicaMetricInstances PositiveRatioExpansion EndToEndPortabilityLaw EndToEndDiscriminationLaw
  EndToEndBrierLaw
open scoped Matrix NNReal

noncomputable section

/-! ## The confusion report of a rule -/

section ConfusionReport

/-- The confusion report of a rule: a state whose report is `(s, b)` goes to the pair of the call
`called s` and the outcome `b`.  Its cells are the true positives `(true, true)`, the false
positives `(true, false)`, the true negatives `(false, false)` and the false negatives
`(false, true)`. -/
def confusionReport {State Score : Type*} (report : State → Score × Bool)
    (called : Score → Bool) (state : State) : Bool × Bool :=
  (called (report state).1, (report state).2)

variable {State : Type*} [Fintype State] {Score : Type*} [Fintype Score]

/-- The cleared mass of an outcome class is the one-replica probability of the event that the
rule clears the score group and the outcome is that class. -/
theorem clearedMass_eq_expectation (law : FiniteReportLaw (Score × Bool))
    (called : Score → Bool) (outcome : Bool) :
    clearedMass law called outcome
      = law.expectation fun report ↦
          if called report.1 = false ∧ report.2 = outcome then 1 else 0 := by
  simp only [clearedMass, FiniteReportLaw.expectation, Fintype.sum_prod_type, Fintype.sum_bool]
  refine Finset.sum_congr rfl fun group _ ↦ ?_
  cases hcall : called group <;> cases outcome <;> simp

/-- **The called mass of a pushed-forward law is a cell of the confusion report law.** -/
theorem calledMass_pushforward (law : FiniteReportLaw State) (report : State → Score × Bool)
    (called : Score → Bool) (outcome : Bool) :
    calledMass (law.pushforward report) called outcome
      = (law.pushforward (confusionReport report called)).mass (true, outcome) := by
  simp only [calledMass_eq_expectation, FiniteReportLaw.expectation_pushforward,
    pushforwardMass_eq_expectation, confusionReport, Prod.mk.injEq]

/-- **The cleared mass of a pushed-forward law is a cell of the confusion report law.** -/
theorem clearedMass_pushforward (law : FiniteReportLaw State) (report : State → Score × Bool)
    (called : Score → Bool) (outcome : Bool) :
    clearedMass (law.pushforward report) called outcome
      = (law.pushforward (confusionReport report called)).mass (false, outcome) := by
  simp only [clearedMass_eq_expectation, FiniteReportLaw.expectation_pushforward,
    pushforwardMass_eq_expectation, confusionReport, Prod.mk.injEq]

/-- **The corpus confusion matrix of a pushed-forward law is its confusion report law.**  The true
positives, false positives, true negatives and false negatives of a rule are the masses of the
cells `(true, true)`, `(true, false)`, `(false, false)` and `(false, true)`. -/
theorem ruleConfusion_pushforward (law : FiniteReportLaw State)
    (report : State → Score × Bool) (called : Score → Bool) :
    (ruleConfusion (law.pushforward report) called).tp
        = (law.pushforward (confusionReport report called)).mass (true, true)
      ∧ (ruleConfusion (law.pushforward report) called).fp
        = (law.pushforward (confusionReport report called)).mass (true, false)
      ∧ (ruleConfusion (law.pushforward report) called).tn
        = (law.pushforward (confusionReport report called)).mass (false, false)
      ∧ (ruleConfusion (law.pushforward report) called).fn
        = (law.pushforward (confusionReport report called)).mass (false, true) :=
  ⟨calledMass_pushforward law report called true,
    calledMass_pushforward law report called false,
    clearedMass_pushforward law report called false,
    clearedMass_pushforward law report called true⟩

/-- Two distinct cells of a finite law carry mass at most one together. -/
theorem cellMass_add_le_one {Report : Type*} [Fintype Report] [DecidableEq Report]
    (law : FiniteReportLaw Report) {first second : Report} (hne : first ≠ second) :
    law.mass first + law.mass second ≤ 1 := by
  have hpair : ∑ report ∈ ({first, second} : Finset Report), law.mass report
      = law.mass first + law.mass second := Finset.sum_pair hne
  rw [← hpair]
  exact (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
    fun report _ _ ↦ law.mass_nonneg report).trans_eq law.mass_sum

/-- The `k`-th term `TP (1 - (TP + c))ᵏ` of the positive ratio expansion of `TP / (TP + c)`, for a
cell `c` of the confusion report, as a polynomial in the population probability vector. -/
def positiveTermPolynomial (report : State → Score × Bool) (called : Score → Bool)
    (other : Bool × Bool) (k : ℕ) : MvPolynomial State ℝ :=
  cellPolynomial (confusionReport report called) (true, true)
    * (1 - (cellPolynomial (confusionReport report called) (true, true)
      + cellPolynomial (confusionReport report called) other)) ^ k

/-- The positive term polynomial evaluates to `TP (1 - (TP + c))ᵏ` of the confusion report law. -/
theorem eval_positiveTermPolynomial (law : FiniteReportLaw State)
    (report : State → Score × Bool) (called : Score → Bool) (other : Bool × Bool) (k : ℕ) :
    eval law.mass (positiveTermPolynomial report called other k)
      = (law.pushforward (confusionReport report called)).mass (true, true)
        * (1 - ((law.pushforward (confusionReport report called)).mass (true, true)
          + (law.pushforward (confusionReport report called)).mass other)) ^ k := by
  simp only [positiveTermPolynomial, map_mul, map_pow, map_sub, map_one, map_add,
    eval_cellPolynomial]

/-- The positive term polynomial has total degree at most `k + 1`: one cell against `k` powers of
the complement of two cells. -/
theorem totalDegree_positiveTermPolynomial_le (report : State → Score × Bool)
    (called : Score → Bool) (other : Bool × Bool) (k : ℕ) :
    (positiveTermPolynomial report called other k).totalDegree ≤ k + 1 := by
  have hden : (cellPolynomial (confusionReport report called) (true, true)
      + cellPolynomial (confusionReport report called) other).totalDegree ≤ 1 :=
    (totalDegree_add _ _).trans
      (max_le (totalDegree_cellPolynomial_le _ _) (totalDegree_cellPolynomial_le _ _))
  exact (totalDegree_expansionTerm_le _ _ 1 1 k (totalDegree_cellPolynomial_le _ _) hden).trans
    (by omega)

/-- **Net benefit** of a rule at a threshold probability `t`, `NB = TP - FP · t / (1 - t)`: the
true positive mass minus the false positive mass weighted by the threshold odds. -/
def ruleNetBenefit (law : FiniteReportLaw (Score × Bool)) (called : Score → Bool) (t : ℝ) : ℝ :=
  calledMass law called true - calledMass law called false * (t / (1 - t))

/-- The net benefit polynomial `TP - FP · t / (1 - t)` of a rule, a linear polynomial in the
population probability vector. -/
def netBenefitPolynomial (report : State → Score × Bool) (called : Score → Bool) (t : ℝ) :
    MvPolynomial State ℝ :=
  cellPolynomial (confusionReport report called) (true, true)
    - cellPolynomial (confusionReport report called) (true, false) * C (t / (1 - t))

/-- The net benefit polynomial evaluates to the net benefit of the pushed-forward law. -/
theorem eval_netBenefitPolynomial (law : FiniteReportLaw State) (report : State → Score × Bool)
    (called : Score → Bool) (t : ℝ) :
    eval law.mass (netBenefitPolynomial report called t)
      = ruleNetBenefit (law.pushforward report) called t := by
  simp only [netBenefitPolynomial, ruleNetBenefit, map_sub, map_mul, eval_C, eval_cellPolynomial,
    calledMass_pushforward]

/-- The net benefit polynomial has total degree at most one. -/
theorem totalDegree_netBenefitPolynomial_le (report : State → Score × Bool)
    (called : Score → Bool) (t : ℝ) :
    (netBenefitPolynomial report called t).totalDegree ≤ 1 := by
  have hscaled := totalDegree_mul (cellPolynomial (confusionReport report called) (true, false))
    (C (t / (1 - t)))
  rw [totalDegree_C, add_zero] at hscaled
  exact (totalDegree_sub _ _).trans (max_le (totalDegree_cellPolynomial_le _ _)
    (hscaled.trans (totalDegree_cellPolynomial_le _ _)))

/-- The rule that calls every score group calls the whole of each outcome class. -/
theorem calledMass_treatAll (law : FiniteReportLaw (Score × Bool)) (outcome : Bool) :
    calledMass law (fun _ ↦ true) outcome = ∑ group, law.mass (group, outcome) := by
  simp [calledMass]

/-- **Treating no one has net benefit zero**, at every threshold. -/
theorem ruleNetBenefit_treatNone (law : FiniteReportLaw (Score × Bool)) (t : ℝ) :
    ruleNetBenefit law (fun _ ↦ false) t = 0 := by
  simp [ruleNetBenefit, calledMass]

/-- **Treating everyone has net benefit `p - (1 - p) · t / (1 - t)`**, for the case probability
`p` of the law: the upper baseline of a decision curve. -/
theorem ruleNetBenefit_treatAll (law : FiniteReportLaw (Score × Bool)) (t : ℝ) :
    ruleNetBenefit law (fun _ ↦ true) t
      = law.binaryCaseMass Prod.snd - (1 - law.binaryCaseMass Prod.snd) * (t / (1 - t)) := by
  have htotal : ∑ group, law.mass (group, true) + ∑ group, law.mass (group, false) = 1 := by
    simpa only [Fintype.sum_prod_type, Fintype.sum_bool, Finset.sum_add_distrib] using
      law.mass_sum
  rw [ruleNetBenefit, calledMass_treatAll, calledMass_treatAll, binaryCaseMass_snd_eq_sum,
    show ∑ group, law.mass (group, false) = 1 - ∑ group, law.mass (group, true) by linarith]

/-- Sensitivity `TP / (TP + FN)` of a confusion table indexed by call and outcome. -/
def tableSensitivity (table : Bool × Bool → ℝ) : ℝ :=
  table (true, true) / (table (true, true) + table (false, true))

/-- Specificity `TN / (TN + FP)` of a confusion table indexed by call and outcome. -/
def tableSpecificity (table : Bool × Bool → ℝ) : ℝ :=
  table (false, false) / (table (false, false) + table (true, false))

/-- Positive predictive value `TP / (TP + FP)` of a confusion table indexed by call and
outcome. -/
def tablePPV (table : Bool × Bool → ℝ) : ℝ :=
  table (true, true) / (table (true, true) + table (true, false))

/-- Negative predictive value `TN / (TN + FN)` of a confusion table indexed by call and
outcome. -/
def tableNPV (table : Bool × Bool → ℝ) : ℝ :=
  table (false, false) / (table (false, false) + table (false, true))

/-- The F1 score `2 TP / (2 TP + FP + FN)` of a confusion table indexed by call and outcome. -/
def tableF1 (table : Bool × Bool → ℝ) : ℝ :=
  2 * table (true, true) / (2 * table (true, true) + table (true, false) + table (false, true))

/-- Youden's J of a confusion table: sensitivity plus specificity minus one. -/
def tableYouden (table : Bool × Bool → ℝ) : ℝ :=
  tableSensitivity table + tableSpecificity table - 1

/-- The relative risk of the called group, `(TP / (TP + FP)) / (FN / (FN + TN))`: the case
probability among the called over the case probability among the cleared. -/
def tableRelativeRisk (table : Bool × Bool → ℝ) : ℝ :=
  tablePPV table / (table (false, true) / (table (false, true) + table (false, false)))

/-- **The table sensitivity and predictive value of the confusion report law are the corpus
rates.**  They are the recall and the precision of the corpus confusion matrix of the rule on the
pushed-forward law. -/
theorem tableSensitivity_tablePPV_pushforward (law : FiniteReportLaw State)
    (report : State → Score × Bool) (called : Score → Bool) :
    tableSensitivity (law.pushforward (confusionReport report called)).mass
        = (ruleConfusion (law.pushforward report) called).recallRate
      ∧ tablePPV (law.pushforward (confusionReport report called)).mass
        = (ruleConfusion (law.pushforward report) called).precision := by
  refine ⟨?_, ?_⟩ <;>
    simp only [tableSensitivity, tablePPV, Foundations.ConfusionMatrix.recallRate,
      Foundations.ConfusionMatrix.precision, ruleConfusion, calledMass_pushforward,
      clearedMass_pushforward]

end ConfusionReport

/-- **NOTE 2 (15) for a quotient under a probability measure.**  When `0 ≤ num ≤ den ≤ 1`, the
integral of `num / den`, read by Lean as zero where `den` vanishes, is the series of the integrals
of `num (1 - den)ᵏ`. -/
theorem integral_boundedQuotient_eq_tsum {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (num den : Ω → ℝ) (hnumMeasurable : Measurable num)
    (hdenMeasurable : Measurable den) (hnum : ∀ point, 0 ≤ num point)
    (hle : ∀ point, num point ≤ den point) (hden : ∀ point, den point ≤ 1) :
    ∫ point, num point / den point ∂μ
      = ∑' k : ℕ, ∫ point, num point * (1 - den point) ^ k ∂μ := by
  have hquotient : (fun point ↦ num point / den point) = ratioOnDefined num den :=
    funext fun point ↦ by
      unfold ratioOnDefined
      rcases eq_or_lt_of_le ((hnum point).trans (hle point)) with hzero | hpos
      · rw [if_neg hzero.ge.not_lt, ← hzero, div_zero]
      · rw [if_pos hpos]
  rw [hquotient]
  exact integral_ratioOnDefined_eq_tsum μ num den hnumMeasurable hdenMeasurable hnum hle hden

end

end Descent.Portability.EndToEndDecisionLaw
