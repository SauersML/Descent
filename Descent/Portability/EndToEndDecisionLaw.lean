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
(`expectedMetricPortability_eq_of_moments_eq`).  In particular the budget-2 agreement that fixes
AUC portability already fixes the portability of every threshold metric
(`expectedAUCPortability_and_expectedMetricPortability_eq_of_moments_eq`).

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

variable {Deme Locus : Type*} {Allele : Locus → Type*}
variable [Fintype Deme] [DecidableEq Deme] [Fintype Locus] [DecidableEq Locus]
  [∀ ℓ, Fintype (Allele ℓ)] [∀ ℓ, DecidableEq (Allele ℓ)]
variable {Score : Type*} [Fintype Score]

/-! ## The expected confusion table -/

/-- **Expected confusion table**: the expected mass of each cell of the confusion report law of a
rule in a deme, under a kernel started at `x₀`. -/
def expectedConfusion
    (κ : Kernel (FrequencyState Deme Locus Allele) (FrequencyState Deme Locus Allele))
    (x0 : FrequencyState Deme Locus Allele) (deme : Deme)
    (report : FullHaplotype Locus Allele → Score × Bool) (called : Score → Bool)
    (cell : Bool × Bool) : ℝ :=
  ∫ y, ((stateLaw y deme).pushforward (confusionReport report called)).mass cell ∂(κ x0)

/-- **The confusion table of a budget-1 moment vector**: the coefficient vector of every cell
polynomial of the confusion report, copied into a deme, dotted with the vector. -/
def momentConfusion (ℓ₀ : Locus) (deme : Deme)
    (report : FullHaplotype Locus Allele → Score × Bool) (called : Score → Bool)
    (v : BudgetConfiguration Deme Locus Allele (fun _ ↦ 1) → ℝ) (cell : Bool × Bool) : ℝ :=
  budgetCoefficients ℓ₀ (fun _ ↦ 1)
      (demePolynomial deme (cellPolynomial (confusionReport report called) cell)) ⬝ᵥ v

/-- The mass of a cell of the confusion report law of a deme is integrable under every Markov
kernel. -/
theorem integrable_confusionMass
    (κ : Kernel (FrequencyState Deme Locus Allele) (FrequencyState Deme Locus Allele))
    [IsMarkovKernel κ] (x0 : FrequencyState Deme Locus Allele) (deme : Deme)
    (report : FullHaplotype Locus Allele → Score × Bool) (called : Score → Bool)
    (cell : Bool × Bool) :
    Integrable
      (fun y ↦ ((stateLaw y deme).pushforward (confusionReport report called)).mass cell)
      (κ x0) :=
  integrable_continuousObservable κ x0
    (continuous_pushforwardMass deme (confusionReport report called) cell)

/-- **The confusion table through the budget-1 moments.**  Under a Markov kernel with budget-1
dual moments along `M`, the expected confusion table of every rule in a deme is the moment
confusion table of the propagated budget-1 moments.

Assumes: `HasDualMoments κ 1 M`. -/
theorem expectedConfusion_eq_momentConfusion (ℓ₀ : Locus)
    (κ : Kernel (FrequencyState Deme Locus Allele) (FrequencyState Deme Locus Allele))
    [IsMarkovKernel κ] (M : BudgetMatrix Deme Locus Allele 1) (hmoment : HasDualMoments κ 1 M)
    (x0 : FrequencyState Deme Locus Allele) (deme : Deme)
    (report : FullHaplotype Locus Allele → Score × Bool) (called : Score → Bool) :
    expectedConfusion κ x0 deme report called
      = momentConfusion ℓ₀ deme report called (M *ᵥ budgetMomentFeature (fun _ ↦ 1) x0) := by
  funext cell
  simpa only [expectedConfusion, momentConfusion, eval_cellPolynomial] using
    integral_eval_stateLaw_eq_dotProduct ℓ₀ 1 κ M hmoment deme
      (cellPolynomial (confusionReport report called) cell) (totalDegree_cellPolynomial_le _ _) x0

/-- **The confusion table along a history of epochs, splits and pulses.** -/
theorem expectedConfusion_historyEventKernel (ℓ₀ : Locus) (hap₀ : FullHaplotype Locus Allele)
    (events : List ((NeutralRates Deme Locus Allele × ℝ≥0) ⊕ PulseMatrix Deme))
    (x0 : FrequencyState Deme Locus Allele) (deme : Deme)
    (report : FullHaplotype Locus Allele → Score × Bool) (called : Score → Bool) :
    expectedConfusion (historyEventKernel ℓ₀ hap₀ events) x0 deme report called
      = momentConfusion ℓ₀ deme report called
          (historyEventPropagator (fun _ ↦ 1) events *ᵥ budgetMomentFeature (fun _ ↦ 1) x0) := by
  haveI := isMarkovKernel_historyEventKernel ℓ₀ hap₀ events
  exact expectedConfusion_eq_momentConfusion ℓ₀ _ _
    (hasDualMoments_historyEventKernel ℓ₀ hap₀ events 1) x0 deme report called

/-- **The confusion table along a time-varying rate history.** -/
theorem expectedConfusion_rateHistoryKernel {rates : ℝ → NeutralRates Deme Locus Allele} {T : ℝ}
    (hT : 0 ≤ T) (hcontinuous : ∀ capacity : Locus → ℕ,
      ContinuousOn (fun t ↦ dualGenerator (rates t) capacity) (Set.Icc 0 T))
    (ℓ₀ : Locus) (hap₀ : FullHaplotype Locus Allele) (x0 : FrequencyState Deme Locus Allele)
    (deme : Deme) (report : FullHaplotype Locus Allele → Score × Bool) (called : Score → Bool) :
    expectedConfusion (rateHistoryKernel rates ℓ₀ hap₀ hT hcontinuous) x0 deme report called
      = momentConfusion ℓ₀ deme report called
          (rateHistoryDualPropagator rates (fun _ ↦ 1) T
            *ᵥ budgetMomentFeature (fun _ ↦ 1) x0) := by
  haveI := isMarkovKernel_rateHistoryKernel hT hcontinuous ℓ₀ hap₀
  exact expectedConfusion_eq_momentConfusion ℓ₀ _ _
    (hasDualMoments_rateHistoryKernel hT hcontinuous ℓ₀ hap₀ 1) x0 deme report called

/-- **The confusion table sees a kernel only through its budget-1 moments.**  Two Markov kernels
with budget-1 dual moments, from two initial states, whose propagated budget-1 moments agree have
equal expected confusion tables for every rule, report map and deme.

Assumes: `HasDualMoments κ₁ 1 M₁` and `HasDualMoments κ₂ 1 M₂`. -/
theorem expectedConfusion_eq_of_moments_eq (ℓ₀ : Locus)
    {κ₁ κ₂ : Kernel (FrequencyState Deme Locus Allele) (FrequencyState Deme Locus Allele)}
    [IsMarkovKernel κ₁] [IsMarkovKernel κ₂] {M₁ M₂ : BudgetMatrix Deme Locus Allele 1}
    (hmoment₁ : HasDualMoments κ₁ 1 M₁) (hmoment₂ : HasDualMoments κ₂ 1 M₂)
    {x₁ x₂ : FrequencyState Deme Locus Allele}
    (hmoments : M₁ *ᵥ budgetMomentFeature (fun _ ↦ 1) x₁
      = M₂ *ᵥ budgetMomentFeature (fun _ ↦ 1) x₂)
    (deme : Deme) (report : FullHaplotype Locus Allele → Score × Bool) (called : Score → Bool) :
    expectedConfusion κ₁ x₁ deme report called = expectedConfusion κ₂ x₂ deme report called := by
  rw [expectedConfusion_eq_momentConfusion ℓ₀ κ₁ M₁ hmoment₁,
    expectedConfusion_eq_momentConfusion ℓ₀ κ₂ M₂ hmoment₂, hmoments]

/-- **Agreement at any budget fixes the confusion table.**  Two histories of epochs, splits and
pulses, from two initial states, whose propagated moments agree at a budget `n ≥ 1`, in particular
at the AUC budget two or at the squared-correlation budget four, have equal expected confusion
tables. -/
theorem expectedConfusion_historyEventKernel_eq_of_moments_eq (ℓ₀ : Locus)
    (hap₀ : FullHaplotype Locus Allele) {n : ℕ} (hn : 1 ≤ n)
    {first second : List ((NeutralRates Deme Locus Allele × ℝ≥0) ⊕ PulseMatrix Deme)}
    {x₁ x₂ : FrequencyState Deme Locus Allele}
    (hmoments : historyEventPropagator (fun _ ↦ n) first *ᵥ budgetMomentFeature (fun _ ↦ n) x₁
      = historyEventPropagator (fun _ ↦ n) second *ᵥ budgetMomentFeature (fun _ ↦ n) x₂)
    (deme : Deme) (report : FullHaplotype Locus Allele → Score × Bool) (called : Score → Bool) :
    expectedConfusion (historyEventKernel ℓ₀ hap₀ first) x₁ deme report called
      = expectedConfusion (historyEventKernel ℓ₀ hap₀ second) x₂ deme report called := by
  rw [expectedConfusion_historyEventKernel, expectedConfusion_historyEventKernel,
    historyEventMoments_eq_of_le ℓ₀ hap₀ hn hmoments]

/-- **The expected confusion table is the expected corpus confusion matrix.**  Its cells are the
expected true positive, false positive, true negative and false negative masses of the rule on
the report law of the deme. -/
theorem integral_ruleConfusion
    (κ : Kernel (FrequencyState Deme Locus Allele) (FrequencyState Deme Locus Allele))
    (x0 : FrequencyState Deme Locus Allele) (deme : Deme)
    (report : FullHaplotype Locus Allele → Score × Bool) (called : Score → Bool) :
    ∫ y, (ruleConfusion ((stateLaw y deme).pushforward report) called).tp ∂(κ x0)
        = expectedConfusion κ x0 deme report called (true, true)
      ∧ ∫ y, (ruleConfusion ((stateLaw y deme).pushforward report) called).fp ∂(κ x0)
        = expectedConfusion κ x0 deme report called (true, false)
      ∧ ∫ y, (ruleConfusion ((stateLaw y deme).pushforward report) called).tn ∂(κ x0)
        = expectedConfusion κ x0 deme report called (false, false)
      ∧ ∫ y, (ruleConfusion ((stateLaw y deme).pushforward report) called).fn ∂(κ x0)
        = expectedConfusion κ x0 deme report called (false, true) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp only [expectedConfusion, ruleConfusion, calledMass_pushforward, clearedMass_pushforward]

/-- **Prevalence and called fraction through the budget-1 moments.**  The expected prevalence of a
deme, which is its expected case probability `E[TP + FN]` for every rule, and the expected called
fraction `E[TP + FP]` of a rule are sums of two cells of the moment confusion table of the
propagated budget-1 moments.

Assumes: `HasDualMoments κ 1 M`. -/
theorem integral_prevalence_calledFraction_eq_momentConfusion (ℓ₀ : Locus)
    (κ : Kernel (FrequencyState Deme Locus Allele) (FrequencyState Deme Locus Allele))
    [IsMarkovKernel κ] (M : BudgetMatrix Deme Locus Allele 1) (hmoment : HasDualMoments κ 1 M)
    (x0 : FrequencyState Deme Locus Allele) (deme : Deme)
    (report : FullHaplotype Locus Allele → Score × Bool) (called : Score → Bool) :
    ∫ y, ((stateLaw y deme).pushforward report).binaryCaseMass Prod.snd ∂(κ x0)
        = momentConfusion ℓ₀ deme report called (M *ᵥ budgetMomentFeature (fun _ ↦ 1) x0)
            (true, true)
          + momentConfusion ℓ₀ deme report called (M *ᵥ budgetMomentFeature (fun _ ↦ 1) x0)
            (false, true)
      ∧ ∫ y, calledMass ((stateLaw y deme).pushforward report) called true
          + calledMass ((stateLaw y deme).pushforward report) called false ∂(κ x0)
        = momentConfusion ℓ₀ deme report called (M *ᵥ budgetMomentFeature (fun _ ↦ 1) x0)
            (true, true)
          + momentConfusion ℓ₀ deme report called (M *ᵥ budgetMomentFeature (fun _ ↦ 1) x0)
            (true, false) := by
  have hcase : ∀ y : FrequencyState Deme Locus Allele,
      ((stateLaw y deme).pushforward report).binaryCaseMass Prod.snd
        = ((stateLaw y deme).pushforward (confusionReport report called)).mass (true, true)
          + ((stateLaw y deme).pushforward (confusionReport report called)).mass (false, true) :=
    fun y ↦ by
      rw [← prevalence_ruleConfusion _ called]
      simp only [Foundations.ConfusionMatrix.prevalence, ruleConfusion, calledMass_pushforward,
        clearedMass_pushforward]
  rw [← expectedConfusion_eq_momentConfusion ℓ₀ κ M hmoment x0 deme report called]
  simp only [hcase, calledMass_pushforward]
  rw [integral_add (integrable_confusionMass κ x0 deme report called (true, true))
      (integrable_confusionMass κ x0 deme report called (false, true)),
    integral_add (integrable_confusionMass κ x0 deme report called (true, true))
      (integrable_confusionMass κ x0 deme report called (true, false))]
  exact ⟨rfl, rfl⟩

/-! ## Net benefit -/

/-- **Expected net benefit** of a rule in a deme at a threshold probability `t`, under a kernel
started at `x₀`. -/
def expectedNetBenefit
    (κ : Kernel (FrequencyState Deme Locus Allele) (FrequencyState Deme Locus Allele))
    (x0 : FrequencyState Deme Locus Allele) (deme : Deme)
    (report : FullHaplotype Locus Allele → Score × Bool) (called : Score → Bool) (t : ℝ) : ℝ :=
  ∫ y, ruleNetBenefit ((stateLaw y deme).pushforward report) called t ∂(κ x0)

/-- The net benefit of a rule in the report law of a deme is integrable under every Markov
kernel. -/
theorem integrable_ruleNetBenefit
    (κ : Kernel (FrequencyState Deme Locus Allele) (FrequencyState Deme Locus Allele))
    [IsMarkovKernel κ] (x0 : FrequencyState Deme Locus Allele) (deme : Deme)
    (report : FullHaplotype Locus Allele → Score × Bool) (called : Score → Bool) (t : ℝ) :
    Integrable (fun y ↦ ruleNetBenefit ((stateLaw y deme).pushforward report) called t)
      (κ x0) := by
  have hcontinuous : Continuous fun y : FrequencyState Deme Locus Allele ↦
      ruleNetBenefit ((stateLaw y deme).pushforward report) called t := by
    simpa only [eval_netBenefitPolynomial] using
      continuous_eval_stateLaw deme (netBenefitPolynomial report called t)
  exact integrable_continuousObservable κ x0 hcontinuous

/-- **Net benefit is exact at budget one.**  Under a Markov kernel with budget-1 dual moments
along `M`, the expected net benefit of a rule in a deme is the coefficient vector of the net
benefit polynomial dotted with the budget-1 propagated moments.

Assumes: `HasDualMoments κ 1 M`. -/
theorem expectedNetBenefit_eq_dotProduct (ℓ₀ : Locus)
    (κ : Kernel (FrequencyState Deme Locus Allele) (FrequencyState Deme Locus Allele))
    [IsMarkovKernel κ] (M : BudgetMatrix Deme Locus Allele 1) (hmoment : HasDualMoments κ 1 M)
    (x0 : FrequencyState Deme Locus Allele) (deme : Deme)
    (report : FullHaplotype Locus Allele → Score × Bool) (called : Score → Bool) (t : ℝ) :
    expectedNetBenefit κ x0 deme report called t
      = budgetCoefficients ℓ₀ (fun _ ↦ 1)
          (demePolynomial deme (netBenefitPolynomial report called t))
        ⬝ᵥ (M *ᵥ budgetMomentFeature (fun _ ↦ 1) x0) := by
  simpa only [expectedNetBenefit, eval_netBenefitPolynomial] using
    integral_eval_stateLaw_eq_dotProduct ℓ₀ 1 κ M hmoment deme _
      (totalDegree_netBenefitPolynomial_le report called t) x0

/-- **The expected net benefit along a history of epochs, splits and pulses.** -/
theorem expectedNetBenefit_historyEventKernel (ℓ₀ : Locus) (hap₀ : FullHaplotype Locus Allele)
    (events : List ((NeutralRates Deme Locus Allele × ℝ≥0) ⊕ PulseMatrix Deme))
    (x0 : FrequencyState Deme Locus Allele) (deme : Deme)
    (report : FullHaplotype Locus Allele → Score × Bool) (called : Score → Bool) (t : ℝ) :
    expectedNetBenefit (historyEventKernel ℓ₀ hap₀ events) x0 deme report called t
      = budgetCoefficients ℓ₀ (fun _ ↦ 1)
          (demePolynomial deme (netBenefitPolynomial report called t))
        ⬝ᵥ (historyEventPropagator (fun _ ↦ 1) events *ᵥ budgetMomentFeature (fun _ ↦ 1) x0) := by
  haveI := isMarkovKernel_historyEventKernel ℓ₀ hap₀ events
  exact expectedNetBenefit_eq_dotProduct ℓ₀ _ _
    (hasDualMoments_historyEventKernel ℓ₀ hap₀ events 1) x0 deme report called t

/-- **The expected net benefit along a time-varying rate history.** -/
theorem expectedNetBenefit_rateHistoryKernel {rates : ℝ → NeutralRates Deme Locus Allele} {T : ℝ}
    (hT : 0 ≤ T) (hcontinuous : ∀ capacity : Locus → ℕ,
      ContinuousOn (fun t ↦ dualGenerator (rates t) capacity) (Set.Icc 0 T))
    (ℓ₀ : Locus) (hap₀ : FullHaplotype Locus Allele) (x0 : FrequencyState Deme Locus Allele)
    (deme : Deme) (report : FullHaplotype Locus Allele → Score × Bool) (called : Score → Bool)
    (t : ℝ) :
    expectedNetBenefit (rateHistoryKernel rates ℓ₀ hap₀ hT hcontinuous) x0 deme report called t
      = budgetCoefficients ℓ₀ (fun _ ↦ 1)
          (demePolynomial deme (netBenefitPolynomial report called t))
        ⬝ᵥ (rateHistoryDualPropagator rates (fun _ ↦ 1) T
          *ᵥ budgetMomentFeature (fun _ ↦ 1) x0) := by
  haveI := isMarkovKernel_rateHistoryKernel hT hcontinuous ℓ₀ hap₀
  exact expectedNetBenefit_eq_dotProduct ℓ₀ _ _
    (hasDualMoments_rateHistoryKernel hT hcontinuous ℓ₀ hap₀ 1) x0 deme report called t

/-- **Expectation and ratio-of-expectations net benefit coincide.**  Under every Markov kernel the
expected net benefit of a rule is the net benefit `E TP - E FP · t / (1 - t)` of the expected
confusion table. -/
theorem expectedNetBenefit_eq_expectedConfusion
    (κ : Kernel (FrequencyState Deme Locus Allele) (FrequencyState Deme Locus Allele))
    [IsMarkovKernel κ] (x0 : FrequencyState Deme Locus Allele) (deme : Deme)
    (report : FullHaplotype Locus Allele → Score × Bool) (called : Score → Bool) (t : ℝ) :
    expectedNetBenefit κ x0 deme report called t
      = expectedConfusion κ x0 deme report called (true, true)
        - expectedConfusion κ x0 deme report called (true, false) * (t / (1 - t)) := by
  simp only [expectedNetBenefit, ruleNetBenefit, calledMass_pushforward]
  rw [integral_sub (integrable_confusionMass κ x0 deme report called (true, true))
      ((integrable_confusionMass κ x0 deme report called (true, false)).mul_const (t / (1 - t))),
    integral_mul_const]
  rfl

/-- **The decision-curve baselines.**  Under every Markov kernel the expected net benefit of
treating no one is zero, and that of treating everyone is `E p - (1 - E p) · t / (1 - t)`, a
function of the expected case probability `E p` of the deme alone. -/
theorem expectedNetBenefit_treatNone_treatAll
    (κ : Kernel (FrequencyState Deme Locus Allele) (FrequencyState Deme Locus Allele))
    [IsMarkovKernel κ] (x0 : FrequencyState Deme Locus Allele) (deme : Deme)
    (report : FullHaplotype Locus Allele → Score × Bool) (t : ℝ) :
    expectedNetBenefit κ x0 deme report (fun _ ↦ false) t = 0
      ∧ expectedNetBenefit κ x0 deme report (fun _ ↦ true) t
        = (∫ y, ((stateLaw y deme).pushforward report).binaryCaseMass Prod.snd ∂(κ x0))
          - (1 - ∫ y, ((stateLaw y deme).pushforward report).binaryCaseMass Prod.snd ∂(κ x0))
            * (t / (1 - t)) := by
  have hcontinuous : Continuous fun y : FrequencyState Deme Locus Allele ↦
      ((stateLaw y deme).pushforward report).binaryCaseMass Prod.snd := by
    simpa only [FiniteReportLaw.binaryCaseMass, FiniteReportLaw.expectation_pushforward,
      eval_expectationPolynomial] using continuous_eval_stateLaw deme
        (expectationPolynomial fun hap ↦ if (report hap).2 then 1 else 0)
  have hcase := integrable_continuousObservable κ x0 hcontinuous
  have hcomplement : Integrable (fun y ↦
      (1 - ((stateLaw y deme).pushforward report).binaryCaseMass Prod.snd) * (t / (1 - t)))
      (κ x0) :=
    integrable_continuousObservable κ x0 ((continuous_const.sub hcontinuous).mul continuous_const)
  refine ⟨by simp only [expectedNetBenefit, ruleNetBenefit_treatNone, integral_zero], ?_⟩
  simp only [expectedNetBenefit, ruleNetBenefit_treatAll]
  rw [integral_sub hcase hcomplement, integral_mul_const, integral_sub (integrable_const 1) hcase,
    integral_const, measureReal_univ_eq_one, one_smul]

/-- **Decision-curve comparisons are budget-1 computations.**  The expected net benefit of a rule
minus that of treating everyone is the coefficient vector of the difference of the two net benefit
polynomials dotted with the budget-1 propagated moments.  Against treating no one the comparison
is `expectedNetBenefit_eq_dotProduct` itself, since that baseline is zero.

Assumes: `HasDualMoments κ 1 M`. -/
theorem expectedNetBenefit_sub_treatAll_eq_dotProduct (ℓ₀ : Locus)
    (κ : Kernel (FrequencyState Deme Locus Allele) (FrequencyState Deme Locus Allele))
    [IsMarkovKernel κ] (M : BudgetMatrix Deme Locus Allele 1) (hmoment : HasDualMoments κ 1 M)
    (x0 : FrequencyState Deme Locus Allele) (deme : Deme)
    (report : FullHaplotype Locus Allele → Score × Bool) (called : Score → Bool) (t : ℝ) :
    expectedNetBenefit κ x0 deme report called t
        - expectedNetBenefit κ x0 deme report (fun _ ↦ true) t
      = budgetCoefficients ℓ₀ (fun _ ↦ 1) (demePolynomial deme
          (netBenefitPolynomial report called t - netBenefitPolynomial report (fun _ ↦ true) t))
        ⬝ᵥ (M *ᵥ budgetMomentFeature (fun _ ↦ 1) x0) := by
  have hdegree := (totalDegree_sub (netBenefitPolynomial report called t)
    (netBenefitPolynomial report (fun _ ↦ true) t)).trans
      (max_le (totalDegree_netBenefitPolynomial_le report called t)
        (totalDegree_netBenefitPolynomial_le report (fun _ ↦ true) t))
  rw [← integral_eval_stateLaw_eq_dotProduct ℓ₀ 1 κ M hmoment deme _ hdegree x0]
  simp only [map_sub, eval_netBenefitPolynomial]
  rw [integral_sub (integrable_ruleNetBenefit κ x0 deme report called t)
    (integrable_ruleNetBenefit κ x0 deme report (fun _ ↦ true) t)]
  rfl

/-! ## Ratio metrics of the expected confusion table -/

/-- **Metric portability of expectations**: the target-over-source ratio of a metric of the
expected confusion tables of a rule, under a kernel started at `x₀`.  The metric is any function
of a confusion table, in particular `tableSensitivity`, `tableSpecificity`, `tablePPV`,
`tableNPV`, `tableF1`, `tableYouden` or `tableRelativeRisk`. -/
def expectedMetricPortability
    (κ : Kernel (FrequencyState Deme Locus Allele) (FrequencyState Deme Locus Allele))
    (x0 : FrequencyState Deme Locus Allele) (source target : Deme)
    (report : FullHaplotype Locus Allele → Score × Bool) (called : Score → Bool)
    (metric : (Bool × Bool → ℝ) → ℝ) : ℝ :=
  metric (expectedConfusion κ x0 target report called)
    / metric (expectedConfusion κ x0 source report called)

/-- **Decision-metric portability through the budget-1 moments.**  Under a Markov kernel with
budget-1 dual moments along `M`, the portability of every metric of the expected confusion table
is the ratio of that metric at the target and the source moment confusion tables of the
propagated budget-1 moments.  For sensitivity, specificity, the predictive values, F1, Youden's J
and the relative risk of the called group it is a rational function of the propagated moments.

Assumes: `HasDualMoments κ 1 M`. -/
theorem expectedMetricPortability_eq_momentConfusion (ℓ₀ : Locus)
    (κ : Kernel (FrequencyState Deme Locus Allele) (FrequencyState Deme Locus Allele))
    [IsMarkovKernel κ] (M : BudgetMatrix Deme Locus Allele 1) (hmoment : HasDualMoments κ 1 M)
    (x0 : FrequencyState Deme Locus Allele) (source target : Deme)
    (report : FullHaplotype Locus Allele → Score × Bool) (called : Score → Bool)
    (metric : (Bool × Bool → ℝ) → ℝ) :
    expectedMetricPortability κ x0 source target report called metric
      = metric (momentConfusion ℓ₀ target report called
          (M *ᵥ budgetMomentFeature (fun _ ↦ 1) x0))
        / metric (momentConfusion ℓ₀ source report called
          (M *ᵥ budgetMomentFeature (fun _ ↦ 1) x0)) := by
  rw [expectedMetricPortability,
    expectedConfusion_eq_momentConfusion ℓ₀ κ M hmoment x0 target report called,
    expectedConfusion_eq_momentConfusion ℓ₀ κ M hmoment x0 source report called]

/-- **Decision-metric portability along a history of epochs, splits and pulses.** -/
theorem expectedMetricPortability_historyEventKernel (ℓ₀ : Locus)
    (hap₀ : FullHaplotype Locus Allele)
    (events : List ((NeutralRates Deme Locus Allele × ℝ≥0) ⊕ PulseMatrix Deme))
    (x0 : FrequencyState Deme Locus Allele) (source target : Deme)
    (report : FullHaplotype Locus Allele → Score × Bool) (called : Score → Bool)
    (metric : (Bool × Bool → ℝ) → ℝ) :
    expectedMetricPortability (historyEventKernel ℓ₀ hap₀ events) x0 source target report called
        metric
      = metric (momentConfusion ℓ₀ target report called
          (historyEventPropagator (fun _ ↦ 1) events
            *ᵥ budgetMomentFeature (fun _ ↦ 1) x0))
        / metric (momentConfusion ℓ₀ source report called
          (historyEventPropagator (fun _ ↦ 1) events
            *ᵥ budgetMomentFeature (fun _ ↦ 1) x0)) := by
  haveI := isMarkovKernel_historyEventKernel ℓ₀ hap₀ events
  exact expectedMetricPortability_eq_momentConfusion ℓ₀ _ _
    (hasDualMoments_historyEventKernel ℓ₀ hap₀ events 1) x0 source target report called metric

/-- **Decision-metric portability along a time-varying rate history.** -/
theorem expectedMetricPortability_rateHistoryKernel
    {rates : ℝ → NeutralRates Deme Locus Allele} {T : ℝ} (hT : 0 ≤ T)
    (hcontinuous : ∀ capacity : Locus → ℕ,
      ContinuousOn (fun t ↦ dualGenerator (rates t) capacity) (Set.Icc 0 T))
    (ℓ₀ : Locus) (hap₀ : FullHaplotype Locus Allele) (x0 : FrequencyState Deme Locus Allele)
    (source target : Deme) (report : FullHaplotype Locus Allele → Score × Bool)
    (called : Score → Bool) (metric : (Bool × Bool → ℝ) → ℝ) :
    expectedMetricPortability (rateHistoryKernel rates ℓ₀ hap₀ hT hcontinuous) x0 source target
        report called metric
      = metric (momentConfusion ℓ₀ target report called
          (rateHistoryDualPropagator rates (fun _ ↦ 1) T
            *ᵥ budgetMomentFeature (fun _ ↦ 1) x0))
        / metric (momentConfusion ℓ₀ source report called
          (rateHistoryDualPropagator rates (fun _ ↦ 1) T
            *ᵥ budgetMomentFeature (fun _ ↦ 1) x0)) := by
  haveI := isMarkovKernel_rateHistoryKernel hT hcontinuous ℓ₀ hap₀
  exact expectedMetricPortability_eq_momentConfusion ℓ₀ _ _
    (hasDualMoments_rateHistoryKernel hT hcontinuous ℓ₀ hap₀ 1) x0 source target report called
      metric

/-- **Decision-metric portability sees the history only through the budget-1 moments.**  Two
histories of epochs, splits and pulses, from two initial states, whose propagated moments agree at
a budget `n ≥ 1` have equal portability of every metric of the expected confusion table. -/
theorem expectedMetricPortability_eq_of_moments_eq (ℓ₀ : Locus)
    (hap₀ : FullHaplotype Locus Allele) {n : ℕ} (hn : 1 ≤ n)
    {first second : List ((NeutralRates Deme Locus Allele × ℝ≥0) ⊕ PulseMatrix Deme)}
    {x₁ x₂ : FrequencyState Deme Locus Allele}
    (hmoments : historyEventPropagator (fun _ ↦ n) first *ᵥ budgetMomentFeature (fun _ ↦ n) x₁
      = historyEventPropagator (fun _ ↦ n) second *ᵥ budgetMomentFeature (fun _ ↦ n) x₂)
    (source target : Deme) (report : FullHaplotype Locus Allele → Score × Bool)
    (called : Score → Bool) (metric : (Bool × Bool → ℝ) → ℝ) :
    expectedMetricPortability (historyEventKernel ℓ₀ hap₀ first) x₁ source target report called
        metric
      = expectedMetricPortability (historyEventKernel ℓ₀ hap₀ second) x₂ source target report
        called metric := by
  rw [expectedMetricPortability, expectedMetricPortability,
    expectedConfusion_historyEventKernel_eq_of_moments_eq ℓ₀ hap₀ hn hmoments target report
      called,
    expectedConfusion_historyEventKernel_eq_of_moments_eq ℓ₀ hap₀ hn hmoments source report
      called]

/-- **The AUC budget already fixes every threshold metric.**  Two histories of epochs, splits and
pulses whose propagated budget-2 moments agree have equal AUC portability of the score
`hap ↦ value s` against the outcome `b` of a report map `hap ↦ (s, b)`, and equal portability of
every metric of the expected confusion table of every rule on the score groups.  No pair of
histories agrees at the AUC budget and disagrees on sensitivity, specificity, the predictive
values, F1, Youden's J or the relative risk of the called group. -/
theorem expectedAUCPortability_and_expectedMetricPortability_eq_of_moments_eq (ℓ₀ : Locus)
    (hap₀ : FullHaplotype Locus Allele)
    {first second : List ((NeutralRates Deme Locus Allele × ℝ≥0) ⊕ PulseMatrix Deme)}
    {x₁ x₂ : FrequencyState Deme Locus Allele}
    (hmoments : historyEventPropagator (fun _ ↦ 2) first *ᵥ budgetMomentFeature (fun _ ↦ 2) x₁
      = historyEventPropagator (fun _ ↦ 2) second *ᵥ budgetMomentFeature (fun _ ↦ 2) x₂)
    (source target : Deme) (report : FullHaplotype Locus Allele → Score × Bool)
    (value : Score → ℝ) (called : Score → Bool) (metric : (Bool × Bool → ℝ) → ℝ) :
    expectedAUCPortability (historyEventKernel ℓ₀ hap₀ first) x₁ source target
        (fun hap ↦ value (report hap).1) (fun hap ↦ (report hap).2)
      = expectedAUCPortability (historyEventKernel ℓ₀ hap₀ second) x₂ source target
        (fun hap ↦ value (report hap).1) (fun hap ↦ (report hap).2)
    ∧ expectedMetricPortability (historyEventKernel ℓ₀ hap₀ first) x₁ source target report called
        metric
      = expectedMetricPortability (historyEventKernel ℓ₀ hap₀ second) x₂ source target report
        called metric :=
  ⟨expectedAUCPortability_eq_of_moments_eq ℓ₀ hap₀ hmoments source target _ _,
    expectedMetricPortability_eq_of_moments_eq ℓ₀ hap₀ (by norm_num) hmoments source target report
      called metric⟩

/-! ## Expected sensitivity and predictive value -/

/-- **Expected positive quotient**: the expectation of `TP / (TP + c)` for a cell `c` of the
confusion report law of a rule in a deme, read by Lean as zero where the denominator vanishes,
under a kernel started at `x₀`. -/
def expectedPositiveQuotient
    (κ : Kernel (FrequencyState Deme Locus Allele) (FrequencyState Deme Locus Allele))
    (x0 : FrequencyState Deme Locus Allele) (deme : Deme)
    (report : FullHaplotype Locus Allele → Score × Bool) (called : Score → Bool)
    (other : Bool × Bool) : ℝ :=
  ∫ y, ((stateLaw y deme).pushforward (confusionReport report called)).mass (true, true)
      / (((stateLaw y deme).pushforward (confusionReport report called)).mass (true, true)
        + ((stateLaw y deme).pushforward (confusionReport report called)).mass other) ∂(κ x0)

/-- **The expected recall and precision are positive quotients.**  The expected corpus recall
`E[TP / (TP + FN)]` of a rule in a deme is the positive quotient of the false negative cell, and
the expected corpus precision `E[TP / (TP + FP)]` is that of the false positive cell. -/
theorem integral_recallRate_precision
    (κ : Kernel (FrequencyState Deme Locus Allele) (FrequencyState Deme Locus Allele))
    (x0 : FrequencyState Deme Locus Allele) (deme : Deme)
    (report : FullHaplotype Locus Allele → Score × Bool) (called : Score → Bool) :
    ∫ y, (ruleConfusion ((stateLaw y deme).pushforward report) called).recallRate ∂(κ x0)
        = expectedPositiveQuotient κ x0 deme report called (false, true)
      ∧ ∫ y, (ruleConfusion ((stateLaw y deme).pushforward report) called).precision ∂(κ x0)
        = expectedPositiveQuotient κ x0 deme report called (true, false) := by
  refine ⟨?_, ?_⟩ <;>
    simp only [expectedPositiveQuotient, Foundations.ConfusionMatrix.recallRate,
      Foundations.ConfusionMatrix.precision, ruleConfusion, calledMass_pushforward,
      clearedMass_pushforward]

/-- **NOTE 2 (15) for the positive quotients under a Markov kernel.**  For every cell `c` other
than the true positives, the expected positive quotient `E[TP / (TP + c)]` is the series over `k`
of the expectations of the positive term polynomials `TP (1 - (TP + c))ᵏ`.  No hypothesis on the
rule is needed: `0 ≤ TP ≤ TP + c ≤ 1` holds for every rule. -/
theorem expectedPositiveQuotient_eq_tsum
    (κ : Kernel (FrequencyState Deme Locus Allele) (FrequencyState Deme Locus Allele))
    [IsMarkovKernel κ] (x0 : FrequencyState Deme Locus Allele) (deme : Deme)
    (report : FullHaplotype Locus Allele → Score × Bool) (called : Score → Bool)
    (other : Bool × Bool) (hother : (true, true) ≠ other) :
    expectedPositiveQuotient κ x0 deme report called other
      = ∑' k : ℕ, ∫ y, eval (stateLaw y deme).mass (positiveTermPolynomial report called other k)
          ∂(κ x0) := by
  simp only [expectedPositiveQuotient, eval_positiveTermPolynomial]
  exact integral_boundedQuotient_eq_tsum (κ x0) _ _
    (continuous_pushforwardMass deme (confusionReport report called) (true, true)).measurable
    ((continuous_pushforwardMass deme (confusionReport report called) (true, true)).add
      (continuous_pushforwardMass deme (confusionReport report called) other)).measurable
    (fun _ ↦ FiniteReportLaw.mass_nonneg _ _)
    (fun _ ↦ le_add_of_nonneg_right (FiniteReportLaw.mass_nonneg _ _))
    (fun _ ↦ cellMass_add_le_one _ hother)

/-- **The expected positive quotients through the propagated moments.**  For every cell `c` other
than the true positives, the expected positive quotient is the series over `k` of the coefficient
vectors of `TP (1 - (TP + c))ᵏ` dotted with the budget-`(k + 1)` propagated moments.

Assumes: `∀ n, HasDualMoments κ n (M n)`. -/
theorem expectedPositiveQuotient_eq_tsum_dotProduct (ℓ₀ : Locus)
    (κ : Kernel (FrequencyState Deme Locus Allele) (FrequencyState Deme Locus Allele))
    [IsMarkovKernel κ] (M : ∀ n : ℕ, BudgetMatrix Deme Locus Allele n)
    (hmoment : ∀ n : ℕ, HasDualMoments κ n (M n)) (x0 : FrequencyState Deme Locus Allele)
    (deme : Deme) (report : FullHaplotype Locus Allele → Score × Bool) (called : Score → Bool)
    (other : Bool × Bool) (hother : (true, true) ≠ other) :
    expectedPositiveQuotient κ x0 deme report called other
      = ∑' k : ℕ, budgetCoefficients ℓ₀ (fun _ ↦ k + 1)
          (demePolynomial deme (positiveTermPolynomial report called other k))
        ⬝ᵥ (M (k + 1) *ᵥ budgetMomentFeature (fun _ ↦ k + 1) x0) := by
  rw [expectedPositiveQuotient_eq_tsum κ x0 deme report called other hother]
  exact tsum_congr fun k ↦ integral_eval_stateLaw_eq_dotProduct ℓ₀ (k + 1) κ (M (k + 1))
    (hmoment (k + 1)) deme _ (totalDegree_positiveTermPolynomial_le report called other k) x0

/-- **The expected positive quotients along a history of epochs, splits and pulses.** -/
theorem expectedPositiveQuotient_historyEventKernel (ℓ₀ : Locus)
    (hap₀ : FullHaplotype Locus Allele)
    (events : List ((NeutralRates Deme Locus Allele × ℝ≥0) ⊕ PulseMatrix Deme))
    (x0 : FrequencyState Deme Locus Allele) (deme : Deme)
    (report : FullHaplotype Locus Allele → Score × Bool) (called : Score → Bool)
    (other : Bool × Bool) (hother : (true, true) ≠ other) :
    expectedPositiveQuotient (historyEventKernel ℓ₀ hap₀ events) x0 deme report called other
      = ∑' k : ℕ, budgetCoefficients ℓ₀ (fun _ ↦ k + 1)
          (demePolynomial deme (positiveTermPolynomial report called other k))
        ⬝ᵥ (historyEventPropagator (fun _ ↦ k + 1) events
          *ᵥ budgetMomentFeature (fun _ ↦ k + 1) x0) := by
  haveI := isMarkovKernel_historyEventKernel ℓ₀ hap₀ events
  exact expectedPositiveQuotient_eq_tsum_dotProduct ℓ₀ (historyEventKernel ℓ₀ hap₀ events)
    (fun n ↦ historyEventPropagator (fun _ ↦ n) events)
    (hasDualMoments_historyEventKernel ℓ₀ hap₀ events) x0 deme report called other hother

/-- **The expected positive quotients along a time-varying rate history.** -/
theorem expectedPositiveQuotient_rateHistoryKernel {rates : ℝ → NeutralRates Deme Locus Allele}
    {T : ℝ} (hT : 0 ≤ T) (hcontinuous : ∀ capacity : Locus → ℕ,
      ContinuousOn (fun t ↦ dualGenerator (rates t) capacity) (Set.Icc 0 T))
    (ℓ₀ : Locus) (hap₀ : FullHaplotype Locus Allele) (x0 : FrequencyState Deme Locus Allele)
    (deme : Deme) (report : FullHaplotype Locus Allele → Score × Bool) (called : Score → Bool)
    (other : Bool × Bool) (hother : (true, true) ≠ other) :
    expectedPositiveQuotient (rateHistoryKernel rates ℓ₀ hap₀ hT hcontinuous) x0 deme
        report called other
      = ∑' k : ℕ, budgetCoefficients ℓ₀ (fun _ ↦ k + 1)
          (demePolynomial deme (positiveTermPolynomial report called other k))
        ⬝ᵥ (rateHistoryDualPropagator rates (fun _ ↦ k + 1) T
          *ᵥ budgetMomentFeature (fun _ ↦ k + 1) x0) := by
  haveI := isMarkovKernel_rateHistoryKernel hT hcontinuous ℓ₀ hap₀
  exact expectedPositiveQuotient_eq_tsum_dotProduct ℓ₀
    (rateHistoryKernel rates ℓ₀ hap₀ hT hcontinuous)
    (fun n ↦ rateHistoryDualPropagator rates (fun _ ↦ n) T)
    (hasDualMoments_rateHistoryKernel hT hcontinuous ℓ₀ hap₀) x0 deme report called other hother

/-- **The expected recall and precision along a history of epochs, splits and pulses.**  The
expected per-population sensitivity `E[TP / (TP + FN)]` and positive predictive value
`E[TP / (TP + FP)]` of a rule in a deme are series over `k` of budget-`(k + 1)` dot products. -/
theorem integral_recallRate_precision_historyEventKernel (ℓ₀ : Locus)
    (hap₀ : FullHaplotype Locus Allele)
    (events : List ((NeutralRates Deme Locus Allele × ℝ≥0) ⊕ PulseMatrix Deme))
    (x0 : FrequencyState Deme Locus Allele) (deme : Deme)
    (report : FullHaplotype Locus Allele → Score × Bool) (called : Score → Bool) :
    ∫ y, (ruleConfusion ((stateLaw y deme).pushforward report) called).recallRate
        ∂(historyEventKernel ℓ₀ hap₀ events x0)
        = ∑' k : ℕ, budgetCoefficients ℓ₀ (fun _ ↦ k + 1)
            (demePolynomial deme (positiveTermPolynomial report called (false, true) k))
          ⬝ᵥ (historyEventPropagator (fun _ ↦ k + 1) events
            *ᵥ budgetMomentFeature (fun _ ↦ k + 1) x0)
      ∧ ∫ y, (ruleConfusion ((stateLaw y deme).pushforward report) called).precision
          ∂(historyEventKernel ℓ₀ hap₀ events x0)
        = ∑' k : ℕ, budgetCoefficients ℓ₀ (fun _ ↦ k + 1)
            (demePolynomial deme (positiveTermPolynomial report called (true, false) k))
          ⬝ᵥ (historyEventPropagator (fun _ ↦ k + 1) events
            *ᵥ budgetMomentFeature (fun _ ↦ k + 1) x0) := by
  obtain ⟨hrecall, hprecision⟩ :=
    integral_recallRate_precision (historyEventKernel ℓ₀ hap₀ events) x0 deme report called
  rw [hrecall, hprecision]
  exact ⟨expectedPositiveQuotient_historyEventKernel ℓ₀ hap₀ events x0 deme report called _
      (by decide),
    expectedPositiveQuotient_historyEventKernel ℓ₀ hap₀ events x0 deme report called _
      (by decide)⟩

/-- **The expected recall and precision see the history only through propagated moments.**  Two
histories of epochs, splits and pulses, from two initial states, whose propagated moments agree at
every budget `k + 1` have equal expected recall and equal expected precision for every rule. -/
theorem integral_recallRate_precision_eq_of_moments_eq (ℓ₀ : Locus)
    (hap₀ : FullHaplotype Locus Allele)
    {first second : List ((NeutralRates Deme Locus Allele × ℝ≥0) ⊕ PulseMatrix Deme)}
    {x₁ x₂ : FrequencyState Deme Locus Allele}
    (hmoments : ∀ k : ℕ, historyEventPropagator (fun _ ↦ k + 1) first
        *ᵥ budgetMomentFeature (fun _ ↦ k + 1) x₁
      = historyEventPropagator (fun _ ↦ k + 1) second
        *ᵥ budgetMomentFeature (fun _ ↦ k + 1) x₂)
    (deme : Deme) (report : FullHaplotype Locus Allele → Score × Bool) (called : Score → Bool) :
    ∫ y, (ruleConfusion ((stateLaw y deme).pushforward report) called).recallRate
        ∂(historyEventKernel ℓ₀ hap₀ first x₁)
        = ∫ y, (ruleConfusion ((stateLaw y deme).pushforward report) called).recallRate
          ∂(historyEventKernel ℓ₀ hap₀ second x₂)
      ∧ ∫ y, (ruleConfusion ((stateLaw y deme).pushforward report) called).precision
          ∂(historyEventKernel ℓ₀ hap₀ first x₁)
        = ∫ y, (ruleConfusion ((stateLaw y deme).pushforward report) called).precision
          ∂(historyEventKernel ℓ₀ hap₀ second x₂) := by
  obtain ⟨hrecall₁, hprecision₁⟩ :=
    integral_recallRate_precision_historyEventKernel ℓ₀ hap₀ first x₁ deme report called
  obtain ⟨hrecall₂, hprecision₂⟩ :=
    integral_recallRate_precision_historyEventKernel ℓ₀ hap₀ second x₂ deme report called
  rw [hrecall₁, hrecall₂, hprecision₁, hprecision₂]
  exact ⟨tsum_congr fun k ↦ by rw [hmoments k], tsum_congr fun k ↦ by rw [hmoments k]⟩

/-! ## Prevalence shift: rates port, predictive value does not -/

/-- **Precision ports exactly when prevalence ports.**  Two confusion matrices with equal recall,
positive, and equal false positive rate, positive, have equal precision if and only if they have
equal prevalence: precision is `π r / (π r + (1 - π) f)` at prevalence `π`, recall `r` and false
positive rate `f`. -/
theorem precision_eq_iff_prevalence_eq (first second : Foundations.ConfusionMatrix)
    (hrecall : first.recallRate = second.recallRate) (hfpr : first.fpr = second.fpr)
    (hrecallPos : 0 < second.recallRate) (hfprPos : 0 < second.fpr) :
    first.precision = second.precision ↔ first.prevalence = second.prevalence := by
  have hden : ∀ matrix : Foundations.ConfusionMatrix,
      0 < matrix.prevalence * second.recallRate + (1 - matrix.prevalence) * second.fpr := by
    intro matrix
    have hlow : 0 ≤ matrix.prevalence := add_nonneg matrix.tp_nonneg matrix.fn_nonneg
    have hhigh : matrix.prevalence ≤ 1 := (confusion_rate_bounds matrix).1.2
    rcases le_total second.recallRate second.fpr with hle | hle
    · nlinarith [mul_nonneg (sub_nonneg.mpr hhigh) (sub_nonneg.mpr hle)]
    · nlinarith [mul_nonneg hlow (sub_nonneg.mpr hle)]
  rw [Foundations.ConfusionMatrix.precision_eq_prevalence_recall_fpr first,
    Foundations.ConfusionMatrix.precision_eq_prevalence_recall_fpr second, hrecall, hfpr,
    div_eq_div_iff (hden first).ne' (hden second).ne']
  constructor
  · intro hcross
    have hkey : second.recallRate * second.fpr * (first.prevalence - second.prevalence) = 0 := by
      linear_combination hcross
    exact sub_eq_zero.mp ((mul_eq_zero.mp hkey).resolve_left (mul_pos hrecallPos hfprPos).ne')
  · intro hprevalence
    rw [hprevalence]

/-- The source report law of the prevalence-shift witness, on score groups `Bool` under the
identity rule: prevalence one half, mass two fifths on each correct call and one tenth on each
error. -/
def witnessSourceLaw : FiniteReportLaw (Bool × Bool) where
  mass := fun report ↦ if report.2 then (if report.1 then 2 / 5 else 1 / 10)
    else (if report.1 then 1 / 10 else 2 / 5)
  mass_nonneg := by intro report; split_ifs <;> norm_num
  mass_sum := by norm_num [Fintype.sum_prod_type, Fintype.sum_bool]

/-- The target report law of the prevalence-shift witness, on score groups `Bool` under the
identity rule: prevalence one fifth, mass four twenty-fifths on true and on false positives,
sixteen twenty-fifths on true negatives and one twenty-fifth on false negatives. -/
def witnessTargetLaw : FiniteReportLaw (Bool × Bool) where
  mass := fun report ↦ if report.2 then (if report.1 then 4 / 25 else 1 / 25)
    else (if report.1 then 4 / 25 else 16 / 25)
  mass_nonneg := by intro report; split_ifs <;> norm_num
  mass_sum := by norm_num [Fintype.sum_prod_type, Fintype.sum_bool]

/-- **A prevalence shift that ports sensitivity and specificity but not predictive value.**  Under
the identity rule both witness laws have recall four fifths and false positive rate one fifth, so
sensitivity and specificity port exactly.  The prevalence moves from one half to one fifth, and
the precision falls from four fifths to one half. -/
theorem prevalenceShift_witness :
    (ruleConfusion witnessTargetLaw id).recallRate = (ruleConfusion witnessSourceLaw id).recallRate
      ∧ (ruleConfusion witnessTargetLaw id).fpr = (ruleConfusion witnessSourceLaw id).fpr
      ∧ (ruleConfusion witnessSourceLaw id).prevalence = 1 / 2
      ∧ (ruleConfusion witnessTargetLaw id).prevalence = 1 / 5
      ∧ (ruleConfusion witnessSourceLaw id).precision = 4 / 5
      ∧ (ruleConfusion witnessTargetLaw id).precision = 1 / 2 := by
  norm_num [Foundations.ConfusionMatrix.recallRate, Foundations.ConfusionMatrix.fpr,
    Foundations.ConfusionMatrix.prevalence, Foundations.ConfusionMatrix.precision, ruleConfusion,
    calledMass, clearedMass, witnessSourceLaw, witnessTargetLaw, Fintype.sum_bool]

end

end Descent.Portability.EndToEndDecisionLaw
