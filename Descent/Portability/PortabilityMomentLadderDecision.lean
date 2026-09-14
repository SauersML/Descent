/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.PortabilityMomentLadder
import Descent.Portability.EndToEndDecisionLaw

assert_below Descent.Decision Descent.Program

/-!
# The decision rung of the moment ladder under any process law

`EndToEndDecisionLaw` proves four laws along the two history kernels.  The expected confusion table
of a threshold rule, its expected net benefit and the portability of every metric of the table go
through the budget-1 propagated moments.  The expected per-population recall and precision are
series of budget-`(k + 1)` dot products.  This module lifts those laws to every process law, in the
language of `PortabilityMomentLadder`: all they use of a kernel is the expectation of frequency
polynomials.

The report.  `decisionReport` collects, for a report map `hap ↦ (s, b)` and a rule
`called : Score → Bool`, in every deme: the expected confusion table, the expected case probability,
the expected called fraction and the expected net benefit at every threshold.  It also collects the
portability of every metric of the confusion table between every source and target.

The rungs.
* Degree one fixes the whole decision report (`decisionReport_eq_of_polynomialsAgreeAt_one`).
  Every cell, the case probability, the called fraction and the net benefit are frequency
  polynomials of total degree at most one (`EndToEndBrierLaw.cellPolynomial`,
  `ReplicaMetricInstances.expectationPolynomial`, `EndToEndDecisionLaw.netBenefitPolynomial`), and
  every portability is a function of two tables.
* So the budget-4 rung carries the portability report and the decision report together
  (`portabilityReport_and_decisionReport_eq_of_polynomialsAgreeAt_four`).
* Agreement at every degree fixes the expected per-population recall and precision
  (`expectedRecallPrecision_eq_of_polynomialsAgreeAt_all`), term by term in the positive ratio
  series of `EndToEndDecisionLaw.expectedPositiveQuotient_eq_tsum`.

Event and rate histories.  Take a history of epochs, splits and pulses and a continuous rate
history.  If their propagated budget-1 moments agree, every rule has the same decision report under
both (`decisionReport_historyEvent_eq_rateHistory`).  If their propagated moments agree at every
budget, every rule has the same expected recall and precision
(`expectedRecallPrecision_historyEvent_eq_rateHistory`).

Significance.  The threshold metrics a clinical report is built on sit on the lowest rung of the
ladder.  A demography contributes to them only the expected haplotype frequencies of its demes,
whichever process carries it; only the expected per-population ratios climb the whole ladder.

Scope.  The report uses the ratio-of-expectations queries of the confusion table and the expected
net benefit.  Whether a finite degree fixes the expected recall or precision is not settled here.

## Empirical status

None.  The bodies here are comparisons of integrals of frequency polynomials against Markov kernels
and termwise comparisons of convergent series of them, so no measurement can bear on them.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.PortabilityMomentLadderDecision

open MeasureTheory ProbabilityTheory MvPolynomial Descent.Coalescent PartialHaplotypeCarrier
  PartialHaplotypeDualGenerator PartialHaplotypeDualSemigroup NeutralFellerGenerator
  NeutralPolynomialSemigroup PartialHaplotypeMicroscopicApproximation PartialHaplotypePulseKernel
  NeutralPulseHistoryKernel NeutralRateHistoryRealization NeutralRateHistoryKernel
  ReplicaMetricInstances EndToEndPortabilityLaw EndToEndDiscriminationLaw EndToEndBrierLaw
  EndToEndDecisionLaw PortabilityMomentLadder
open scoped Matrix NNReal

noncomputable section

/-- **A decision report**: for a rule on a report map under a process law, the expected confusion
table, case probability, called fraction and net benefit at every threshold of every population,
and the portability of every metric of the confusion table between every source and target. -/
structure DecisionReport (Population : Type*) where
  /-- The expected confusion table of each population, indexed by call and outcome. -/
  table : Population → Bool × Bool → ℝ
  /-- The expected case probability of each population. -/
  prevalence : Population → ℝ
  /-- The expected called fraction of each population. -/
  calledFraction : Population → ℝ
  /-- The expected net benefit of each population at each threshold probability. -/
  netBenefit : Population → ℝ → ℝ
  /-- The portability of each metric of the confusion table from each source to each target. -/
  portability : Population → Population → ((Bool × Bool → ℝ) → ℝ) → ℝ

variable {Deme Locus : Type*} {Allele : Locus → Type*}
variable [Fintype Deme] [DecidableEq Deme] [Fintype Locus] [DecidableEq Locus]
  [∀ ℓ, Fintype (Allele ℓ)] [∀ ℓ, DecidableEq (Allele ℓ)]

attribute [local instance] isMarkovKernel_historyEventKernel isMarkovKernel_rateHistoryKernel

/-- **The decision report** of a rule `called` on a report map `hap ↦ (s, b)` under a kernel
started at `x₀`. -/
def decisionReport
    (κ : Kernel (FrequencyState Deme Locus Allele) (FrequencyState Deme Locus Allele))
    (x0 : FrequencyState Deme Locus Allele) {Score : Type*} [Fintype Score]
    (report : FullHaplotype Locus Allele → Score × Bool) (called : Score → Bool) :
    DecisionReport Deme where
  table deme := expectedConfusion κ x0 deme report called
  prevalence deme :=
    ∫ y, ((stateLaw y deme).pushforward report).binaryCaseMass Prod.snd ∂(κ x0)
  calledFraction deme :=
    ∫ y, calledMass ((stateLaw y deme).pushforward report) called true
      + calledMass ((stateLaw y deme).pushforward report) called false ∂(κ x0)
  netBenefit deme t := expectedNetBenefit κ x0 deme report called t
  portability source target metric :=
    expectedMetricPortability κ x0 source target report called metric

/-- **Degree one fixes the decision report under any process law.**  Two process laws that agree,
from their initial states, on every frequency polynomial of total degree at most one give every
rule on every report map the same decision report.  That is the same expected confusion table,
case probability, called fraction and net benefit in every deme, and the same portability of every
metric of the confusion table.

Assumes: agreement up to degree one. -/
theorem decisionReport_eq_of_polynomialsAgreeAt_one
    {κ₁ κ₂ : Kernel (FrequencyState Deme Locus Allele) (FrequencyState Deme Locus Allele)}
    {x₁ x₂ : FrequencyState Deme Locus Allele} (h : PolynomialsAgreeAt 1 κ₁ κ₂ x₁ x₂)
    {Score : Type*} [Fintype Score] (report : FullHaplotype Locus Allele → Score × Bool)
    (called : Score → Bool) :
    decisionReport κ₁ x₁ report called = decisionReport κ₂ x₂ report called := by
  have hterm : ∀ (deme : Deme) (p : MvPolynomial (FullHaplotype Locus Allele) ℝ),
      p.totalDegree ≤ 1 → ∫ y, eval (stateLaw y deme).mass p ∂(κ₁ x₁)
        = ∫ y, eval (stateLaw y deme).mass p ∂(κ₂ x₂) :=
    fun deme p hp ↦ by
      simpa only [polynomialFunction_apply, eval_demePolynomial] using
        h (demePolynomial deme p) ((totalDegree_rename_le _ _).trans hp)
  have hconfusion : ∀ deme : Deme,
      expectedConfusion κ₁ x₁ deme report called = expectedConfusion κ₂ x₂ deme report called :=
    fun deme ↦ funext fun cell ↦ by
      simpa only [expectedConfusion, eval_cellPolynomial] using
        hterm deme (cellPolynomial (confusionReport report called) cell)
          (totalDegree_cellPolynomial_le _ _)
  simp only [decisionReport, DecisionReport.mk.injEq]
  refine ⟨funext hconfusion, funext fun deme ↦ ?_, funext fun deme ↦ ?_,
    funext fun deme ↦ funext fun t ↦ ?_,
    funext fun source ↦ funext fun target ↦ funext fun metric ↦ ?_⟩
  · simpa only [FiniteReportLaw.binaryCaseMass, FiniteReportLaw.expectation_pushforward,
      eval_expectationPolynomial] using
      hterm deme (expectationPolynomial fun hap ↦ if (report hap).2 then 1 else 0)
        (totalDegree_expectationPolynomial_le _)
  · simpa only [map_add, eval_cellPolynomial, calledMass_pushforward] using
      hterm deme (cellPolynomial (confusionReport report called) (true, true)
          + cellPolynomial (confusionReport report called) (true, false))
        ((totalDegree_add _ _).trans
          (max_le (totalDegree_cellPolynomial_le _ _) (totalDegree_cellPolynomial_le _ _)))
  · simpa only [expectedNetBenefit, eval_netBenefitPolynomial] using
      hterm deme (netBenefitPolynomial report called t)
        (totalDegree_netBenefitPolynomial_le report called t)
  · rw [expectedMetricPortability, expectedMetricPortability, hconfusion target,
      hconfusion source]

/-- **The budget-4 rung carries the decision report.**  Two Markov kernels that agree, from their
initial states, on every frequency polynomial of total degree at most four give the same
portability report and, for every rule on every report map, the same decision report.

Assumes: agreement up to degree four. -/
theorem portabilityReport_and_decisionReport_eq_of_polynomialsAgreeAt_four
    {κ₁ κ₂ : Kernel (FrequencyState Deme Locus Allele) (FrequencyState Deme Locus Allele)}
    [IsMarkovKernel κ₁] [IsMarkovKernel κ₂] {x₁ x₂ : FrequencyState Deme Locus Allele}
    (h : PolynomialsAgreeAt 4 κ₁ κ₂ x₁ x₂) (source target : Deme)
    (score outcome : FullHaplotype Locus Allele → ℝ) (case : FullHaplotype Locus Allele → Bool)
    {Score : Type*} [Fintype Score] (report : FullHaplotype Locus Allele → Score × Bool)
    (called : Score → Bool) :
    portabilityReport κ₁ x₁ source target score outcome case
        = portabilityReport κ₂ x₂ source target score outcome case
      ∧ decisionReport κ₁ x₁ report called = decisionReport κ₂ x₂ report called :=
  ⟨portabilityReport_eq_of_polynomialsAgreeAt_four h source target score outcome case,
    decisionReport_eq_of_polynomialsAgreeAt_one (PolynomialsAgreeAt.mono (by norm_num) h) report
      called⟩

/-- **Every degree fixes the expected recall and precision under any process law.**  Two Markov
kernels that agree, from their initial states, on the expectation of every frequency polynomial
give every rule on every report map, in every deme, the same expected per-population recall
`E[TP / (TP + FN)]` and the same expected per-population precision `E[TP / (TP + FP)]`.

Assumes: agreement at every degree. -/
theorem expectedRecallPrecision_eq_of_polynomialsAgreeAt_all
    {κ₁ κ₂ : Kernel (FrequencyState Deme Locus Allele) (FrequencyState Deme Locus Allele)}
    [IsMarkovKernel κ₁] [IsMarkovKernel κ₂] {x₁ x₂ : FrequencyState Deme Locus Allele}
    (h : ∀ n : ℕ, PolynomialsAgreeAt n κ₁ κ₂ x₁ x₂) (deme : Deme) {Score : Type*}
    [Fintype Score] (report : FullHaplotype Locus Allele → Score × Bool)
    (called : Score → Bool) :
    ∫ y, (ruleConfusion ((stateLaw y deme).pushforward report) called).recallRate ∂(κ₁ x₁)
        = ∫ y, (ruleConfusion ((stateLaw y deme).pushforward report) called).recallRate
          ∂(κ₂ x₂)
      ∧ ∫ y, (ruleConfusion ((stateLaw y deme).pushforward report) called).precision ∂(κ₁ x₁)
        = ∫ y, (ruleConfusion ((stateLaw y deme).pushforward report) called).precision
          ∂(κ₂ x₂) := by
  have hquotient : ∀ other : Bool × Bool, (true, true) ≠ other →
      expectedPositiveQuotient κ₁ x₁ deme report called other
        = expectedPositiveQuotient κ₂ x₂ deme report called other := fun other hother ↦ by
    rw [expectedPositiveQuotient_eq_tsum κ₁ x₁ deme report called other hother,
      expectedPositiveQuotient_eq_tsum κ₂ x₂ deme report called other hother]
    exact tsum_congr fun k ↦ by
      simpa only [polynomialFunction_apply, eval_demePolynomial] using
        h (k + 1) (demePolynomial deme (positiveTermPolynomial report called other k))
          ((totalDegree_rename_le _ _).trans
            (totalDegree_positiveTermPolynomial_le report called other k))
  obtain ⟨hrecall₁, hprecision₁⟩ := integral_recallRate_precision κ₁ x₁ deme report called
  obtain ⟨hrecall₂, hprecision₂⟩ := integral_recallRate_precision κ₂ x₂ deme report called
  rw [hrecall₁, hrecall₂, hprecision₁, hprecision₂]
  exact ⟨hquotient _ (by decide), hquotient _ (by decide)⟩

/-- **An event history and a rate history with equal budget-1 moments give one decision report.**
If a history of epochs, splits and pulses from `x₁` and a rate history with continuous dual
generator from `x₂` have equal propagated budget-1 moments, every rule on every report map has the
same decision report under both.

Assumes: equal propagated budget-1 moments. -/
theorem decisionReport_historyEvent_eq_rateHistory (ℓ₀ : Locus)
    (hap₀ : FullHaplotype Locus Allele)
    (events : List ((NeutralRates Deme Locus Allele × ℝ≥0) ⊕ PulseMatrix Deme))
    {rates : ℝ → NeutralRates Deme Locus Allele} {T : ℝ} (hT : 0 ≤ T)
    (hcontinuous : ∀ capacity : Locus → ℕ,
      ContinuousOn (fun t ↦ dualGenerator (rates t) capacity) (Set.Icc 0 T))
    {x₁ x₂ : FrequencyState Deme Locus Allele}
    (hmoments : historyEventPropagator (fun _ ↦ 1) events *ᵥ budgetMomentFeature (fun _ ↦ 1) x₁
      = rateHistoryDualPropagator rates (fun _ ↦ 1) T *ᵥ budgetMomentFeature (fun _ ↦ 1) x₂)
    {Score : Type*} [Fintype Score] (report : FullHaplotype Locus Allele → Score × Bool)
    (called : Score → Bool) :
    decisionReport (historyEventKernel ℓ₀ hap₀ events) x₁ report called
      = decisionReport (rateHistoryKernel rates ℓ₀ hap₀ hT hcontinuous) x₂ report called :=
  decisionReport_eq_of_polynomialsAgreeAt_one
    (polynomialsAgreeAt_of_hasDualMoments ℓ₀ (hasDualMoments_historyEventKernel ℓ₀ hap₀ events 1)
      (hasDualMoments_rateHistoryKernel hT hcontinuous ℓ₀ hap₀ 1) hmoments)
    report called

/-- **An event history and a rate history with equal moment sequences give one expected recall
and precision.**  If a history of epochs, splits and pulses from `x₁` and a rate history with
continuous dual generator from `x₂` have equal propagated moments at every budget, every rule on
every report map has the same expected per-population recall and precision in every deme.

Assumes: equal propagated moments at every budget. -/
theorem expectedRecallPrecision_historyEvent_eq_rateHistory (ℓ₀ : Locus)
    (hap₀ : FullHaplotype Locus Allele)
    (events : List ((NeutralRates Deme Locus Allele × ℝ≥0) ⊕ PulseMatrix Deme))
    {rates : ℝ → NeutralRates Deme Locus Allele} {T : ℝ} (hT : 0 ≤ T)
    (hcontinuous : ∀ capacity : Locus → ℕ,
      ContinuousOn (fun t ↦ dualGenerator (rates t) capacity) (Set.Icc 0 T))
    {x₁ x₂ : FrequencyState Deme Locus Allele}
    (hmoments : ∀ n : ℕ,
      historyEventPropagator (fun _ ↦ n) events *ᵥ budgetMomentFeature (fun _ ↦ n) x₁
        = rateHistoryDualPropagator rates (fun _ ↦ n) T *ᵥ budgetMomentFeature (fun _ ↦ n) x₂)
    (deme : Deme) {Score : Type*} [Fintype Score]
    (report : FullHaplotype Locus Allele → Score × Bool) (called : Score → Bool) :
    ∫ y, (ruleConfusion ((stateLaw y deme).pushforward report) called).recallRate
        ∂(historyEventKernel ℓ₀ hap₀ events x₁)
        = ∫ y, (ruleConfusion ((stateLaw y deme).pushforward report) called).recallRate
          ∂(rateHistoryKernel rates ℓ₀ hap₀ hT hcontinuous x₂)
      ∧ ∫ y, (ruleConfusion ((stateLaw y deme).pushforward report) called).precision
          ∂(historyEventKernel ℓ₀ hap₀ events x₁)
        = ∫ y, (ruleConfusion ((stateLaw y deme).pushforward report) called).precision
          ∂(rateHistoryKernel rates ℓ₀ hap₀ hT hcontinuous x₂) :=
  expectedRecallPrecision_eq_of_polynomialsAgreeAt_all
    (fun n ↦ polynomialsAgreeAt_of_hasDualMoments ℓ₀
      (hasDualMoments_historyEventKernel ℓ₀ hap₀ events n)
      (hasDualMoments_rateHistoryKernel hT hcontinuous ℓ₀ hap₀ n) (hmoments n))
    deme report called

end

end Descent.Portability.PortabilityMomentLadderDecision
