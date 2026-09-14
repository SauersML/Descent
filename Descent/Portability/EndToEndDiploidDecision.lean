/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.PortabilityMomentLadderDecision
import Descent.Portability.EndToEndDiploidHistoryLaw

assert_below Descent.Decision Descent.Program

/-!
# The diploid decision law under any process law

`EndToEndDecisionLaw` carries the threshold-rule metrics of a report that reads one haplotype per
individual, and `PortabilityMomentLadderDecision` shows that agreement up to degree one fixes them
under any process law.  Polygenic scores read two haplotypes.  This module carries threshold rules
on genotypes.

The genotype.  An individual is an ordered gamete pair formed in its deme by
`EndToEndDiploidLaw.inbredMating`: identical by descent with probability `F`, and otherwise two
independent draws from the deme's haplotype law.  A diploid report map sends a genotype to a score
group and a binary outcome, and a rule `called` calls score groups.

The report.  `diploidDecisionReport` collects, in every deme at its own inbreeding coefficient, the
expected confusion table (`expectedDiploidConfusion`), the expected case probability, the expected
called fraction and the expected net benefit at every threshold.  It also collects the portability
of every metric of the table between every source and target.

Degree two.
* Every entry of the report is the expectation of one genotype observable.  The called fraction is
  the probability of a call (`calledMass_add_calledMass_pushforward`), and the net benefit
  `TP - FP · t / (1 - t)` is the expectation of one observable (`ruleNetBenefit_pushforward`).
* The expected genotype observable is `(1 - F) Σ_{h,h'} p(h) p(h') φ(h, h') + F Σ_h p(h) φ(h, h)`,
  a frequency polynomial of total degree at most two
  (`polynomialFunction_genotypeExpectationPolynomial`).  So agreement up to degree two fixes it
  under any process law (`integral_genotypeExpectation_eq_of_polynomialsAgreeAt_two`).
* So agreement up to degree two fixes the whole diploid decision report
  (`diploidDecisionReport_eq_of_polynomialsAgreeAt_two`).  A history of epochs, splits and pulses
  and a continuous rate history whose propagated budget-2 moments agree give every rule on every
  genotype report map one diploid decision report
  (`diploidDecisionReport_historyEvent_eq_rateHistory`).

The contrast.  The haploid decision report is fixed at degree one and the diploid report at degree
two, and degree two carries both
(`decisionReport_and_diploidDecisionReport_eq_of_polynomialsAgreeAt_two`).  The second degree
comes from the independent gamete pairs.  Under full autozygosity, `F = 1` in every deme, every
report map of the pair has the law of its diagonal (`pushforward_inbredMating_one`).  So the
diploid report is the haploid report of the diagonal report map
(`diploidDecisionReport_inbreeding_one`), and degree one fixes it
(`diploidDecisionReport_inbreeding_one_eq_of_polynomialsAgreeAt_one`).

Significance.  The clinical threshold metrics of a genotype-level report sit on the second rung of
the moment ladder, dominance and interaction between the two gametes included.  That is below the
budget four of the additive squared correlation.  A demography contributes to them only the
expected haplotype frequencies of its demes and their expected pairwise products.

Scope.  The gamete pair is the one of `EndToEndDiploidLaw`: both gametes are drawn from the deme's
own haplotype law, and identity by descent is one whole-haplotype event with a coefficient supplied
per deme.  Score groups form a finite alphabet, outcomes are binary and the rule is deterministic.
The report uses the ratio-of-expectations queries of the confusion table and the expected net
benefit.  No pair of process laws that agree up to degree one and give different diploid reports is
constructed here, so whether degree one fails below full autozygosity is not settled.

## Empirical status

None.  The bodies here are finite sums against constructed laws and comparisons of integrals of
frequency polynomials against Markov kernels, so no measurement can bear on them.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.EndToEndDiploidDecision

open MeasureTheory ProbabilityTheory MvPolynomial Descent.Coalescent PartialHaplotypeCarrier
  PartialHaplotypeDualGenerator PartialHaplotypeDualSemigroup NeutralFellerGenerator
  NeutralPolynomialSemigroup PartialHaplotypeMicroscopicApproximation PartialHaplotypePulseKernel
  NeutralPulseHistoryKernel NeutralRateHistoryRealization NeutralRateHistoryKernel
  ReplicaMetricInstances EndToEndPortabilityLaw EndToEndDiscriminationLaw EndToEndBrierLaw
  EndToEndDecisionLaw PortabilityMomentLadder PortabilityMomentLadderDecision EndToEndDiploidLaw
  EndToEndDiploidHistoryLaw
open scoped Matrix NNReal

noncomputable section

/-! ## Rules as expectations -/

section Rules

variable {State : Type*} [Fintype State] {Score : Type*} [Fintype Score]

/-- **The called fraction is the probability of a call.**  On a pushed-forward law, the called mass
of the cases plus that of the controls is the expectation of the indicator that the rule calls the
score group of the state. -/
theorem calledMass_add_calledMass_pushforward (law : FiniteReportLaw State)
    (report : State → Score × Bool) (called : Score → Bool) :
    calledMass (law.pushforward report) called true
        + calledMass (law.pushforward report) called false
      = law.expectation fun state ↦ if called (report state).1 then 1 else 0 := by
  rw [calledMass_eq_expectation, calledMass_eq_expectation,
    FiniteReportLaw.expectation_pushforward, FiniteReportLaw.expectation_pushforward]
  simp only [FiniteReportLaw.expectation]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun state _ ↦ ?_
  cases called (report state).1 <;> cases (report state).2 <;> simp

/-- **Net benefit is one expectation.**  On a pushed-forward law, the net benefit
`TP - FP · t / (1 - t)` of a rule is the expectation of the observable that is `1` on a called
case, `-t / (1 - t)` on a called control and `0` on a cleared state. -/
theorem ruleNetBenefit_pushforward (law : FiniteReportLaw State) (report : State → Score × Bool)
    (called : Score → Bool) (t : ℝ) :
    ruleNetBenefit (law.pushforward report) called t = law.expectation fun state ↦
      if called (report state).1 then (if (report state).2 then 1 else -(t / (1 - t))) else 0 := by
  rw [ruleNetBenefit, calledMass_eq_expectation, calledMass_eq_expectation,
    FiniteReportLaw.expectation_pushforward, FiniteReportLaw.expectation_pushforward]
  simp only [FiniteReportLaw.expectation]
  rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun state _ ↦ ?_
  cases called (report state).1 <;> cases (report state).2 <;> simp

end Rules

/-! ## Full autozygosity -/

section Genotypes

variable {H : Type*} [Fintype H] [DecidableEq H]

/-- **Full autozygosity reads one haplotype.**  At `F = 1` every report map of the gamete pair has
the law of its diagonal under the deme law. -/
theorem pushforward_inbredMating_one (law : FiniteReportLaw H) {Report : Type*} [Fintype Report]
    (report : H × H → Report) :
    (inbredMating law 1 zero_le_one le_rfl).pushforward report
      = law.pushforward fun haplotype ↦ report (haplotype, haplotype) := by
  classical
  refine FiniteReportLaw.ext fun cell ↦ ?_
  rw [pushforwardMass_eq_expectation, pushforwardMass_eq_expectation, expectation_inbredMating]
  ring

/-- **Full autozygosity reads one haplotype, for a rule.**  At `F = 1` the confusion report law of
a rule on a genotype report map is the confusion report law of the rule on its diagonal. -/
theorem pushforward_confusionReport_inbredMating_one (law : FiniteReportLaw H) {Score : Type*}
    (report : H × H → Score × Bool) (called : Score → Bool) :
    (inbredMating law 1 zero_le_one le_rfl).pushforward (confusionReport report called)
      = law.pushforward (confusionReport (fun haplotype ↦ report (haplotype, haplotype)) called) :=
  pushforward_inbredMating_one law (confusionReport report called)

end Genotypes

/-! ## The diploid decision report -/

section History

variable {Deme Locus : Type*} {Allele : Locus → Type*}
variable [Fintype Deme] [DecidableEq Deme] [Fintype Locus] [DecidableEq Locus]
  [∀ ℓ, Fintype (Allele ℓ)] [∀ ℓ, DecidableEq (Allele ℓ)]

attribute [local instance] isMarkovKernel_historyEventKernel isMarkovKernel_rateHistoryKernel

/-- **Expected diploid confusion table**: the expected mass of each cell of the confusion report
law of a rule on a genotype report map in a deme, the deme forming its gamete pairs at its own
inbreeding coefficient, under a kernel started at `x₀`. -/
def expectedDiploidConfusion
    (κ : Kernel (FrequencyState Deme Locus Allele) (FrequencyState Deme Locus Allele))
    (x0 : FrequencyState Deme Locus Allele) (deme : Deme) (inbreeding : Deme → ℝ)
    (hF0 : ∀ other, 0 ≤ inbreeding other) (hF1 : ∀ other, inbreeding other ≤ 1) {Score : Type*}
    (report : FullHaplotype Locus Allele × FullHaplotype Locus Allele → Score × Bool)
    (called : Score → Bool) (cell : Bool × Bool) : ℝ :=
  ∫ y, ((stateGenotypeLaw y deme inbreeding hF0 hF1).pushforward
    (confusionReport report called)).mass cell ∂(κ x0)

/-- **The diploid decision report** of a rule `called` on a genotype report map
`(h₁, h₂) ↦ (s, b)` under a kernel started at `x₀`, each deme forming its gamete pairs at its own
inbreeding coefficient: the expected confusion table, case probability, called fraction and net
benefit at every threshold of every deme, and the portability of every metric of the table. -/
def diploidDecisionReport
    (κ : Kernel (FrequencyState Deme Locus Allele) (FrequencyState Deme Locus Allele))
    (x0 : FrequencyState Deme Locus Allele) (inbreeding : Deme → ℝ)
    (hF0 : ∀ other, 0 ≤ inbreeding other) (hF1 : ∀ other, inbreeding other ≤ 1)
    {Score : Type*} [Fintype Score]
    (report : FullHaplotype Locus Allele × FullHaplotype Locus Allele → Score × Bool)
    (called : Score → Bool) : DecisionReport Deme where
  table deme := expectedDiploidConfusion κ x0 deme inbreeding hF0 hF1 report called
  prevalence deme :=
    ∫ y, ((stateGenotypeLaw y deme inbreeding hF0 hF1).pushforward report).binaryCaseMass Prod.snd
      ∂(κ x0)
  calledFraction deme :=
    ∫ y, calledMass ((stateGenotypeLaw y deme inbreeding hF0 hF1).pushforward report) called true
      + calledMass ((stateGenotypeLaw y deme inbreeding hF0 hF1).pushforward report) called false
      ∂(κ x0)
  netBenefit deme t :=
    ∫ y, ruleNetBenefit ((stateGenotypeLaw y deme inbreeding hF0 hF1).pushforward report) called t
      ∂(κ x0)
  portability source target metric :=
    metric (expectedDiploidConfusion κ x0 target inbreeding hF0 hF1 report called)
      / metric (expectedDiploidConfusion κ x0 source inbreeding hF0 hF1 report called)

/-- At a state, the genotype expectation polynomial of an observable in a deme is the expectation
of the observable under the deme's gamete-pair law. -/
theorem polynomialFunction_genotypeExpectationPolynomial (deme : Deme) (inbreeding : Deme → ℝ)
    (hF0 : ∀ other, 0 ≤ inbreeding other) (hF1 : ∀ other, inbreeding other ≤ 1)
    (φ : FullHaplotype Locus Allele × FullHaplotype Locus Allele → ℝ)
    (y : FrequencyState Deme Locus Allele) :
    polynomialFunction (demePolynomial deme (genotypeExpectationPolynomial (inbreeding deme) φ)) y
      = (stateGenotypeLaw y deme inbreeding hF0 hF1).expectation φ := by
  rw [stateGenotypeLaw, polynomialFunction_apply, eval_demePolynomial,
    eval_genotypeExpectationPolynomial (stateLaw y deme) (inbreeding deme) (hF0 deme) (hF1 deme)]

/-- **Degree two fixes every expected genotype observable under any process law.**  Two process
laws that agree, from their initial states, on every frequency polynomial of total degree at most
two give every observable of the gamete pair, in every deme and at every choice of inbreeding
coefficients, one expectation.

Assumes: agreement up to degree two. -/
theorem integral_genotypeExpectation_eq_of_polynomialsAgreeAt_two
    {κ₁ κ₂ : Kernel (FrequencyState Deme Locus Allele) (FrequencyState Deme Locus Allele)}
    {x₁ x₂ : FrequencyState Deme Locus Allele} (h : PolynomialsAgreeAt 2 κ₁ κ₂ x₁ x₂)
    (deme : Deme) (inbreeding : Deme → ℝ) (hF0 : ∀ other, 0 ≤ inbreeding other)
    (hF1 : ∀ other, inbreeding other ≤ 1)
    (φ : FullHaplotype Locus Allele × FullHaplotype Locus Allele → ℝ) :
    ∫ y, (stateGenotypeLaw y deme inbreeding hF0 hF1).expectation φ ∂(κ₁ x₁)
      = ∫ y, (stateGenotypeLaw y deme inbreeding hF0 hF1).expectation φ ∂(κ₂ x₂) := by
  simpa only [polynomialFunction_genotypeExpectationPolynomial deme inbreeding hF0 hF1 φ] using
    h (demePolynomial deme (genotypeExpectationPolynomial (inbreeding deme) φ))
      ((totalDegree_rename_le _ _).trans (totalDegree_genotypeExpectationPolynomial_le _ φ))

/-- **Degree two fixes the diploid decision report under any process law.**  Two process laws that
agree, from their initial states, on every frequency polynomial of total degree at most two give
every rule on every genotype report map, at every choice of inbreeding coefficients, the same
diploid decision report.  That is the same expected confusion table, case probability, called
fraction and net benefit in every deme, and the same portability of every metric of the table.

Assumes: agreement up to degree two. -/
theorem diploidDecisionReport_eq_of_polynomialsAgreeAt_two
    {κ₁ κ₂ : Kernel (FrequencyState Deme Locus Allele) (FrequencyState Deme Locus Allele)}
    {x₁ x₂ : FrequencyState Deme Locus Allele} (h : PolynomialsAgreeAt 2 κ₁ κ₂ x₁ x₂)
    (inbreeding : Deme → ℝ) (hF0 : ∀ other, 0 ≤ inbreeding other)
    (hF1 : ∀ other, inbreeding other ≤ 1) {Score : Type*} [Fintype Score]
    (report : FullHaplotype Locus Allele × FullHaplotype Locus Allele → Score × Bool)
    (called : Score → Bool) :
    diploidDecisionReport κ₁ x₁ inbreeding hF0 hF1 report called
      = diploidDecisionReport κ₂ x₂ inbreeding hF0 hF1 report called := by
  have hterm := integral_genotypeExpectation_eq_of_polynomialsAgreeAt_two h
  have hconfusion : ∀ deme : Deme,
      expectedDiploidConfusion κ₁ x₁ deme inbreeding hF0 hF1 report called
        = expectedDiploidConfusion κ₂ x₂ deme inbreeding hF0 hF1 report called :=
    fun deme ↦ funext fun cell ↦ by
      simpa only [expectedDiploidConfusion, pushforwardMass_eq_expectation] using
        hterm deme inbreeding hF0 hF1 fun pair ↦
          if confusionReport report called pair = cell then 1 else 0
  simp only [diploidDecisionReport, DecisionReport.mk.injEq]
  refine ⟨funext hconfusion, funext fun deme ↦ ?_, funext fun deme ↦ ?_,
    funext fun deme ↦ funext fun t ↦ ?_,
    funext fun source ↦ funext fun target ↦ funext fun metric ↦ ?_⟩
  · simpa only [FiniteReportLaw.binaryCaseMass, FiniteReportLaw.expectation_pushforward] using
      hterm deme inbreeding hF0 hF1 fun pair ↦ if (report pair).2 then 1 else 0
  · simpa only [calledMass_add_calledMass_pushforward] using
      hterm deme inbreeding hF0 hF1 fun pair ↦ if called (report pair).1 then 1 else 0
  · simpa only [ruleNetBenefit_pushforward] using
      hterm deme inbreeding hF0 hF1 fun pair ↦
        if called (report pair).1 then (if (report pair).2 then 1 else -(t / (1 - t))) else 0
  · rw [hconfusion target, hconfusion source]

/-- **Degree two carries the haploid and the diploid decision reports together.**  The haploid
decision report reads one haplotype per individual and is fixed by agreement up to degree one
(`PortabilityMomentLadderDecision.decisionReport_eq_of_polynomialsAgreeAt_one`); the diploid
report reads the gamete pair and is fixed at degree two.  Two process laws that agree up to degree
two give every rule the same haploid decision report on every haploid report map and the same
diploid decision report on every genotype report map.

Assumes: agreement up to degree two. -/
theorem decisionReport_and_diploidDecisionReport_eq_of_polynomialsAgreeAt_two
    {κ₁ κ₂ : Kernel (FrequencyState Deme Locus Allele) (FrequencyState Deme Locus Allele)}
    {x₁ x₂ : FrequencyState Deme Locus Allele} (h : PolynomialsAgreeAt 2 κ₁ κ₂ x₁ x₂)
    (inbreeding : Deme → ℝ) (hF0 : ∀ other, 0 ≤ inbreeding other)
    (hF1 : ∀ other, inbreeding other ≤ 1) {Score : Type*} [Fintype Score]
    (haploidReport : FullHaplotype Locus Allele → Score × Bool)
    (diploidReport : FullHaplotype Locus Allele × FullHaplotype Locus Allele → Score × Bool)
    (called : Score → Bool) :
    decisionReport κ₁ x₁ haploidReport called = decisionReport κ₂ x₂ haploidReport called
      ∧ diploidDecisionReport κ₁ x₁ inbreeding hF0 hF1 diploidReport called
        = diploidDecisionReport κ₂ x₂ inbreeding hF0 hF1 diploidReport called :=
  ⟨decisionReport_eq_of_polynomialsAgreeAt_one (PolynomialsAgreeAt.mono (by norm_num) h)
      haploidReport called,
    diploidDecisionReport_eq_of_polynomialsAgreeAt_two h inbreeding hF0 hF1 diploidReport called⟩

/-- **An event history and a rate history with equal budget-2 moments give one diploid decision
report.**  If a history of epochs, splits and pulses from `x₁` and a rate history with continuous
dual generator from `x₂` have equal propagated budget-2 moments, every rule on every genotype
report map has the same diploid decision report under both, at every choice of inbreeding
coefficients.

Assumes: equal propagated budget-2 moments. -/
theorem diploidDecisionReport_historyEvent_eq_rateHistory (ℓ₀ : Locus)
    (hap₀ : FullHaplotype Locus Allele)
    (events : List ((NeutralRates Deme Locus Allele × ℝ≥0) ⊕ PulseMatrix Deme))
    {rates : ℝ → NeutralRates Deme Locus Allele} {T : ℝ} (hT : 0 ≤ T)
    (hcontinuous : ∀ capacity : Locus → ℕ,
      ContinuousOn (fun t ↦ dualGenerator (rates t) capacity) (Set.Icc 0 T))
    {x₁ x₂ : FrequencyState Deme Locus Allele}
    (hmoments : historyEventPropagator (fun _ ↦ 2) events *ᵥ budgetMomentFeature (fun _ ↦ 2) x₁
      = rateHistoryDualPropagator rates (fun _ ↦ 2) T *ᵥ budgetMomentFeature (fun _ ↦ 2) x₂)
    (inbreeding : Deme → ℝ) (hF0 : ∀ other, 0 ≤ inbreeding other)
    (hF1 : ∀ other, inbreeding other ≤ 1) {Score : Type*} [Fintype Score]
    (report : FullHaplotype Locus Allele × FullHaplotype Locus Allele → Score × Bool)
    (called : Score → Bool) :
    diploidDecisionReport (historyEventKernel ℓ₀ hap₀ events) x₁ inbreeding hF0 hF1 report called
      = diploidDecisionReport (rateHistoryKernel rates ℓ₀ hap₀ hT hcontinuous) x₂ inbreeding hF0
          hF1 report called :=
  diploidDecisionReport_eq_of_polynomialsAgreeAt_two
    (polynomialsAgreeAt_of_hasDualMoments ℓ₀ (hasDualMoments_historyEventKernel ℓ₀ hap₀ events 2)
      (hasDualMoments_rateHistoryKernel hT hcontinuous ℓ₀ hap₀ 2) hmoments)
    inbreeding hF0 hF1 report called

/-- **Under full autozygosity the diploid decision report is haploid.**  When every deme has
inbreeding coefficient one, the diploid decision report of a rule on a genotype report map is,
under every kernel, the haploid decision report of the rule on the diagonal report map
`h ↦ report (h, h)`. -/
theorem diploidDecisionReport_inbreeding_one
    (κ : Kernel (FrequencyState Deme Locus Allele) (FrequencyState Deme Locus Allele))
    (x0 : FrequencyState Deme Locus Allele) {Score : Type*} [Fintype Score]
    (report : FullHaplotype Locus Allele × FullHaplotype Locus Allele → Score × Bool)
    (called : Score → Bool) :
    diploidDecisionReport κ x0 (fun _ ↦ 1) (fun _ ↦ zero_le_one) (fun _ ↦ le_rfl) report called
      = decisionReport κ x0 (fun haplotype ↦ report (haplotype, haplotype)) called := by
  have hconfusion : ∀ deme : Deme,
      expectedDiploidConfusion κ x0 deme (fun _ ↦ 1) (fun _ ↦ zero_le_one) (fun _ ↦ le_rfl)
          report called
        = expectedConfusion κ x0 deme (fun haplotype ↦ report (haplotype, haplotype)) called :=
    fun deme ↦ funext fun cell ↦ by
      simp only [expectedDiploidConfusion, expectedConfusion, stateGenotypeLaw,
        pushforward_confusionReport_inbredMating_one]
  simp only [diploidDecisionReport, decisionReport, DecisionReport.mk.injEq]
  refine ⟨funext hconfusion, ?_, ?_, ?_,
    funext fun source ↦ funext fun target ↦ funext fun metric ↦ ?_⟩
  · simp only [stateGenotypeLaw, pushforward_inbredMating_one]
  · simp only [stateGenotypeLaw, pushforward_inbredMating_one]
  · simp only [expectedNetBenefit, stateGenotypeLaw, pushforward_inbredMating_one]
  · rw [expectedMetricPortability, hconfusion target, hconfusion source]

/-- **Under full autozygosity degree one fixes the diploid decision report.**  Two process laws
that agree, from their initial states, on every frequency polynomial of total degree at most one
give every rule on every genotype report map the same diploid decision report when every deme has
inbreeding coefficient one.

Assumes: agreement up to degree one. -/
theorem diploidDecisionReport_inbreeding_one_eq_of_polynomialsAgreeAt_one
    {κ₁ κ₂ : Kernel (FrequencyState Deme Locus Allele) (FrequencyState Deme Locus Allele)}
    {x₁ x₂ : FrequencyState Deme Locus Allele} (h : PolynomialsAgreeAt 1 κ₁ κ₂ x₁ x₂)
    {Score : Type*} [Fintype Score]
    (report : FullHaplotype Locus Allele × FullHaplotype Locus Allele → Score × Bool)
    (called : Score → Bool) :
    diploidDecisionReport κ₁ x₁ (fun _ ↦ 1) (fun _ ↦ zero_le_one) (fun _ ↦ le_rfl) report called
      = diploidDecisionReport κ₂ x₂ (fun _ ↦ 1) (fun _ ↦ zero_le_one) (fun _ ↦ le_rfl) report
          called := by
  rw [diploidDecisionReport_inbreeding_one, diploidDecisionReport_inbreeding_one]
  exact decisionReport_eq_of_polynomialsAgreeAt_one h _ called

end History

end

end Descent.Portability.EndToEndDiploidDecision
