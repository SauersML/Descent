/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.PortabilityMomentLadder
import Descent.Portability.EndToEndDecisionLaw

assert_below Descent.Decision Descent.Program

/-!
# The end-to-end law of reclassification metrics

`EndToEndDecisionLaw` carries the confusion table of one rule through a process law, and
`PortabilityMomentLadderDecision` puts that table on the lowest rung of the moment ladder.  Adding a
polygenic score to a clinical model compares an old rule with a new one on the same individuals,
and the comparison is read from the joint table of the two calls: the net reclassification
improvement (NRI) and the integrated discrimination improvement (IDI).  This module carries the
joint table, the NRI and the IDI through every process law, in the language of
`PortabilityMomentLadder`.

The joint report.  A report map `hap ↦ ((s₁, s₂), b)` and two rules give the joint report
`hap ↦ ((called₁ s₁, called₂ s₂), b)` (`jointCallReport`).  Every cell mass is a linear frequency
polynomial (`EndToEndBrierLaw.cellPolynomial`), so under a kernel with budget-1 dual moments every
cell of the expected joint table (`expectedJointTable`) is one budget-1 dot product
(`expectedJointTable_eq_dotProduct`).  Each rule's own expected confusion table is a marginal of the
expected joint table (`oldTable_newTable_expectedJointTable`).

NRI.  `tableNRI` is `[P(up | case) - P(down | case)] + [P(down | control) - P(up | control)]` of a
joint table, where up is the cell `(false, true)` of a new call without an old one and down is the
cell `(true, false)`.  With two categories per rule it is the gain in Youden's J of the marginal
tables (`tableNRI_eq_tableYouden_sub`).  So the NRI of the expected joint table is Youden's J of the
new rule's expected confusion table minus that of the old rule's (`tableNRI_expectedJointTable`).

IDI.  `expectedDiscriminationSlope` of a forecast is the expected case-weighted forecast over the
expected case mass minus the expected control-weighted forecast over the expected control mass,
and `expectedIDI` is the slope of the new forecast minus that of the old.  Each of the four
expectations of a slope is a linear frequency polynomial (`expectedForecastMass`).

The rung.  `reclassificationReport` collects, in every deme, the expected joint table and the NRI
and IDI of expectations.  It also collects the portability of every function of the joint table
between every source and target.  Degree one fixes the whole report under any process law
(`reclassificationReport_eq_of_polynomialsAgreeAt_one`).  If a history of epochs, splits and pulses
and a continuous rate history have equal propagated budget-1 moments, every pair of rules and every
pair of forecasts has the same reclassification report under both
(`reclassificationReport_historyEvent_eq_rateHistory`).

A witness.  The explicit joint laws `witnessSourceJoint` and `witnessTargetJoint` give both rules
sensitivity one half.  The old rule's specificity falls from one to one half, and the NRI rises from
zero to one half (`nriShift_witness`).  Porting each rule's sensitivity does not port the NRI.

Significance.  Reclassification, the statistic by which a polygenic score earns a place in a
clinical model, sits on the same lowest rung as the threshold metrics of one rule.  A demography
contributes to it only the expected haplotype frequencies of its demes, whichever process carries
it.

Scope.  Two categories per rule, binary outcomes, deterministic rules and forecasts of the score
groups, one chromosome per individual, and the ratio-of-expectations queries.  The expected
per-population NRI and IDI, with the ratios inside the expectation, the multi-category NRI and the
category-free NRI are not treated here.

## Empirical status

None.  The bodies here are polynomial identities, arithmetic on explicit finite laws and integrals
of linear frequency polynomials against Markov kernels, so no measurement can bear on them.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.EndToEndReclassificationLaw

open MeasureTheory ProbabilityTheory MvPolynomial Descent.Coalescent PartialHaplotypeCarrier
  PartialHaplotypeDualGenerator PartialHaplotypeDualSemigroup NeutralFellerGenerator
  NeutralPolynomialSemigroup PartialHaplotypeMicroscopicApproximation PartialHaplotypePulseKernel
  NeutralPulseHistoryKernel NeutralRateHistoryRealization NeutralRateHistoryKernel
  ReplicaMetricInstances EndToEndPortabilityLaw EndToEndDiscriminationLaw EndToEndBrierLaw
  EndToEndDecisionLaw PortabilityMomentLadder
open scoped Matrix NNReal

noncomputable section

/-! ## The joint table of two rules -/

section JointTable

variable {State Score₁ Score₂ : Type*}

/-- The joint report of two rules: a state whose report is `((s₁, s₂), b)` goes to the pair of the
old call `called₁ s₁` and the new call `called₂ s₂`, with the outcome `b`. -/
def jointCallReport (report : State → (Score₁ × Score₂) × Bool) (called₁ : Score₁ → Bool)
    (called₂ : Score₂ → Bool) (state : State) : (Bool × Bool) × Bool :=
  ((called₁ (report state).1.1, called₂ (report state).1.2), (report state).2)

/-- The mass of one outcome class in a joint table indexed by the old call, the new call and the
outcome: the sum over its four call pairs. -/
def jointOutcomeMass (table : (Bool × Bool) × Bool → ℝ) (outcome : Bool) : ℝ :=
  table ((true, true), outcome) + table ((true, false), outcome)
    + table ((false, true), outcome) + table ((false, false), outcome)

/-- **Net reclassification improvement** of a joint table indexed by the old call, the new call
and the outcome: `[P(up | case) - P(down | case)] + [P(down | control) - P(up | control)]`.  Up is
a new call without an old one, the cell `(false, true)`; down is an old call without a new one, the
cell `(true, false)`. -/
def tableNRI (table : (Bool × Bool) × Bool → ℝ) : ℝ :=
  (table ((false, true), true) - table ((true, false), true)) / jointOutcomeMass table true
    + (table ((true, false), false) - table ((false, true), false)) / jointOutcomeMass table false

/-- The confusion table of the old rule, indexed by call and outcome: a marginal of a joint
table. -/
def oldTable (table : (Bool × Bool) × Bool → ℝ) (cell : Bool × Bool) : ℝ :=
  table ((cell.1, true), cell.2) + table ((cell.1, false), cell.2)

/-- The confusion table of the new rule, indexed by call and outcome: a marginal of a joint
table. -/
def newTable (table : (Bool × Bool) × Bool → ℝ) (cell : Bool × Bool) : ℝ :=
  table ((true, cell.1), cell.2) + table ((false, cell.1), cell.2)

/-- **Two-category NRI is the gain in Youden's J.**  For every joint table the net
reclassification improvement is Youden's J of the new rule's marginal table minus that of the old
rule's.  Up minus down among cases is the gain in sensitivity, and down minus up among controls is
the gain in specificity, over the outcome masses the two marginal tables share. -/
theorem tableNRI_eq_tableYouden_sub (table : (Bool × Bool) × Bool → ℝ) :
    tableNRI table = tableYouden (newTable table) - tableYouden (oldTable table) := by
  have hsensitivity : tableSensitivity (newTable table) - tableSensitivity (oldTable table)
      = (table ((false, true), true) - table ((true, false), true))
        / jointOutcomeMass table true := by
    have hnew : newTable table (true, true) + newTable table (false, true)
        = jointOutcomeMass table true := by
      simp only [newTable, jointOutcomeMass]
      ring
    have hold : oldTable table (true, true) + oldTable table (false, true)
        = jointOutcomeMass table true := by
      simp only [oldTable, jointOutcomeMass]
      ring
    rw [tableSensitivity, tableSensitivity, hnew, hold, ← sub_div]
    congr 1
    simp only [newTable, oldTable]
    ring
  have hspecificity : tableSpecificity (newTable table) - tableSpecificity (oldTable table)
      = (table ((true, false), false) - table ((false, true), false))
        / jointOutcomeMass table false := by
    have hnew : newTable table (false, false) + newTable table (true, false)
        = jointOutcomeMass table false := by
      simp only [newTable, jointOutcomeMass]
      ring
    have hold : oldTable table (false, false) + oldTable table (true, false)
        = jointOutcomeMass table false := by
      simp only [oldTable, jointOutcomeMass]
      ring
    rw [tableSpecificity, tableSpecificity, hnew, hold, ← sub_div]
    congr 1
    simp only [newTable, oldTable]
    ring
  rw [tableNRI, ← hsensitivity, ← hspecificity, tableYouden, tableYouden]
  ring

/-- The joint masses of one old call and one outcome, summed over the new call, are the mass of
that cell in the confusion report law of the old rule. -/
theorem jointMass_add_old [Fintype State] (law : FiniteReportLaw State)
    (report : State → (Score₁ × Score₂) × Bool) (called₁ : Score₁ → Bool)
    (called₂ : Score₂ → Bool) (call outcome : Bool) :
    (law.pushforward (jointCallReport report called₁ called₂)).mass ((call, true), outcome)
        + (law.pushforward (jointCallReport report called₁ called₂)).mass ((call, false), outcome)
      = (law.pushforward (confusionReport report fun score ↦ called₁ score.1)).mass
          (call, outcome) := by
  rw [pushforwardMass_eq_expectation, pushforwardMass_eq_expectation,
    pushforwardMass_eq_expectation]
  simp only [FiniteReportLaw.expectation, ← Finset.sum_add_distrib, ← mul_add]
  refine Finset.sum_congr rfl fun state _ ↦ ?_
  congr 1
  simp only [jointCallReport, confusionReport, Prod.mk.injEq]
  cases called₂ (report state).1.2 <;> simp

/-- The joint masses of one new call and one outcome, summed over the old call, are the mass of
that cell in the confusion report law of the new rule. -/
theorem jointMass_add_new [Fintype State] (law : FiniteReportLaw State)
    (report : State → (Score₁ × Score₂) × Bool) (called₁ : Score₁ → Bool)
    (called₂ : Score₂ → Bool) (call outcome : Bool) :
    (law.pushforward (jointCallReport report called₁ called₂)).mass ((true, call), outcome)
        + (law.pushforward (jointCallReport report called₁ called₂)).mass ((false, call), outcome)
      = (law.pushforward (confusionReport report fun score ↦ called₂ score.2)).mass
          (call, outcome) := by
  rw [pushforwardMass_eq_expectation, pushforwardMass_eq_expectation,
    pushforwardMass_eq_expectation]
  simp only [FiniteReportLaw.expectation, ← Finset.sum_add_distrib, ← mul_add]
  refine Finset.sum_congr rfl fun state _ ↦ ?_
  congr 1
  simp only [jointCallReport, confusionReport, Prod.mk.injEq]
  cases called₁ (report state).1.1 <;> simp

end JointTable

variable {Deme Locus : Type*} {Allele : Locus → Type*}
variable [Fintype Deme] [DecidableEq Deme] [Fintype Locus] [DecidableEq Locus]
  [∀ ℓ, Fintype (Allele ℓ)] [∀ ℓ, DecidableEq (Allele ℓ)]
variable {Score₁ Score₂ : Type*}

attribute [local instance] isMarkovKernel_historyEventKernel isMarkovKernel_rateHistoryKernel

/-! ## The expected joint table -/

/-- **Expected joint table**: the expected mass of each cell of the joint report law of two rules
in a deme, under a kernel started at `x₀`. -/
def expectedJointTable
    (κ : Kernel (FrequencyState Deme Locus Allele) (FrequencyState Deme Locus Allele))
    (x0 : FrequencyState Deme Locus Allele) (deme : Deme)
    (report : FullHaplotype Locus Allele → (Score₁ × Score₂) × Bool) (called₁ : Score₁ → Bool)
    (called₂ : Score₂ → Bool) (cell : (Bool × Bool) × Bool) : ℝ :=
  ∫ y, ((stateLaw y deme).pushforward (jointCallReport report called₁ called₂)).mass cell ∂(κ x0)

/-- The mass of a cell of the joint report law of a deme is integrable under every Markov
kernel. -/
theorem integrable_jointMass
    (κ : Kernel (FrequencyState Deme Locus Allele) (FrequencyState Deme Locus Allele))
    [IsMarkovKernel κ] (x0 : FrequencyState Deme Locus Allele) (deme : Deme)
    (report : FullHaplotype Locus Allele → (Score₁ × Score₂) × Bool) (called₁ : Score₁ → Bool)
    (called₂ : Score₂ → Bool) (cell : (Bool × Bool) × Bool) :
    Integrable
      (fun y ↦ ((stateLaw y deme).pushforward (jointCallReport report called₁ called₂)).mass cell)
      (κ x0) :=
  integrable_continuousObservable κ x0
    (continuous_pushforwardMass deme (jointCallReport report called₁ called₂) cell)

/-- **The joint table through the budget-1 moments.**  Under a Markov kernel with budget-1 dual
moments along `M`, every cell of the expected joint table of two rules in a deme is the coefficient
vector of its cell polynomial, copied into the deme, dotted with the propagated budget-1 moments.

Assumes: `HasDualMoments κ 1 M`. -/
theorem expectedJointTable_eq_dotProduct (ℓ₀ : Locus)
    (κ : Kernel (FrequencyState Deme Locus Allele) (FrequencyState Deme Locus Allele))
    [IsMarkovKernel κ] (M : BudgetMatrix Deme Locus Allele 1) (hmoment : HasDualMoments κ 1 M)
    (x0 : FrequencyState Deme Locus Allele) (deme : Deme)
    (report : FullHaplotype Locus Allele → (Score₁ × Score₂) × Bool) (called₁ : Score₁ → Bool)
    (called₂ : Score₂ → Bool) (cell : (Bool × Bool) × Bool) :
    expectedJointTable κ x0 deme report called₁ called₂ cell
      = budgetCoefficients ℓ₀ (fun _ ↦ 1)
          (demePolynomial deme (cellPolynomial (jointCallReport report called₁ called₂) cell))
        ⬝ᵥ (M *ᵥ budgetMomentFeature (fun _ ↦ 1) x0) := by
  simpa only [expectedJointTable, eval_cellPolynomial] using
    integral_eval_stateLaw_eq_dotProduct ℓ₀ 1 κ M hmoment deme
      (cellPolynomial (jointCallReport report called₁ called₂) cell)
      (totalDegree_cellPolynomial_le _ _) x0

/-- **Each rule's own table is a marginal of the joint table.**  Under every Markov kernel the
expected confusion table of the old rule in a deme is the old marginal of the expected joint table,
and the expected confusion table of the new rule is the new marginal. -/
theorem oldTable_newTable_expectedJointTable [Fintype Score₁] [Fintype Score₂]
    (κ : Kernel (FrequencyState Deme Locus Allele) (FrequencyState Deme Locus Allele))
    [IsMarkovKernel κ] (x0 : FrequencyState Deme Locus Allele) (deme : Deme)
    (report : FullHaplotype Locus Allele → (Score₁ × Score₂) × Bool) (called₁ : Score₁ → Bool)
    (called₂ : Score₂ → Bool) :
    oldTable (expectedJointTable κ x0 deme report called₁ called₂)
        = expectedConfusion κ x0 deme report (fun score ↦ called₁ score.1)
      ∧ newTable (expectedJointTable κ x0 deme report called₁ called₂)
        = expectedConfusion κ x0 deme report (fun score ↦ called₂ score.2) := by
  refine ⟨funext fun cell ↦ ?_, funext fun cell ↦ ?_⟩
  · obtain ⟨call, outcome⟩ := cell
    simp only [oldTable, expectedJointTable, expectedConfusion]
    rw [← integral_add
      (integrable_jointMass κ x0 deme report called₁ called₂ ((call, true), outcome))
      (integrable_jointMass κ x0 deme report called₁ called₂ ((call, false), outcome))]
    simp only [jointMass_add_old]
  · obtain ⟨call, outcome⟩ := cell
    simp only [newTable, expectedJointTable, expectedConfusion]
    rw [← integral_add
      (integrable_jointMass κ x0 deme report called₁ called₂ ((true, call), outcome))
      (integrable_jointMass κ x0 deme report called₁ called₂ ((false, call), outcome))]
    simp only [jointMass_add_new]

/-- **The NRI of expectations is the gain in Youden's J of the two own tables.**  Under every
Markov kernel the net reclassification improvement of the expected joint table of two rules in a
deme is Youden's J of the new rule's expected confusion table minus that of the old rule's. -/
theorem tableNRI_expectedJointTable [Fintype Score₁] [Fintype Score₂]
    (κ : Kernel (FrequencyState Deme Locus Allele) (FrequencyState Deme Locus Allele))
    [IsMarkovKernel κ] (x0 : FrequencyState Deme Locus Allele) (deme : Deme)
    (report : FullHaplotype Locus Allele → (Score₁ × Score₂) × Bool) (called₁ : Score₁ → Bool)
    (called₂ : Score₂ → Bool) :
    tableNRI (expectedJointTable κ x0 deme report called₁ called₂)
      = tableYouden (expectedConfusion κ x0 deme report fun score ↦ called₂ score.2)
        - tableYouden (expectedConfusion κ x0 deme report fun score ↦ called₁ score.1) := by
  obtain ⟨hold, hnew⟩ := oldTable_newTable_expectedJointTable κ x0 deme report called₁ called₂
  rw [tableNRI_eq_tableYouden_sub, hold, hnew]

/-! ## Integrated discrimination improvement -/

/-- **Expected outcome-weighted forecast**: the expected mass of a forecast of the score groups
over one outcome class, `E[Σ_hap p(hap) f(s) 1{b = o}]`, in a deme under a kernel started at `x₀`.
The forecast `1` gives the expected mass of the outcome class. -/
def expectedForecastMass
    (κ : Kernel (FrequencyState Deme Locus Allele) (FrequencyState Deme Locus Allele))
    (x0 : FrequencyState Deme Locus Allele) (deme : Deme)
    (report : FullHaplotype Locus Allele → (Score₁ × Score₂) × Bool)
    (forecast : Score₁ × Score₂ → ℝ) (outcome : Bool) : ℝ :=
  ∫ y, (stateLaw y deme).expectation
    (fun hap ↦ if (report hap).2 = outcome then forecast (report hap).1 else 0) ∂(κ x0)

/-- **Discrimination slope of expectations** of a forecast in a deme: the expected case-weighted
forecast over the expected case mass, minus the expected control-weighted forecast over the
expected control mass. -/
def expectedDiscriminationSlope
    (κ : Kernel (FrequencyState Deme Locus Allele) (FrequencyState Deme Locus Allele))
    (x0 : FrequencyState Deme Locus Allele) (deme : Deme)
    (report : FullHaplotype Locus Allele → (Score₁ × Score₂) × Bool)
    (forecast : Score₁ × Score₂ → ℝ) : ℝ :=
  expectedForecastMass κ x0 deme report forecast true
      / expectedForecastMass κ x0 deme report (fun _ ↦ 1) true
    - expectedForecastMass κ x0 deme report forecast false
      / expectedForecastMass κ x0 deme report (fun _ ↦ 1) false

/-- **Integrated discrimination improvement of expectations** in a deme: the discrimination slope
of the new forecast `forecast₂ s₂` minus that of the old forecast `forecast₁ s₁`. -/
def expectedIDI
    (κ : Kernel (FrequencyState Deme Locus Allele) (FrequencyState Deme Locus Allele))
    (x0 : FrequencyState Deme Locus Allele) (deme : Deme)
    (report : FullHaplotype Locus Allele → (Score₁ × Score₂) × Bool) (forecast₁ : Score₁ → ℝ)
    (forecast₂ : Score₂ → ℝ) : ℝ :=
  expectedDiscriminationSlope κ x0 deme report (fun score ↦ forecast₂ score.2)
    - expectedDiscriminationSlope κ x0 deme report (fun score ↦ forecast₁ score.1)

/-! ## The reclassification rung -/

/-- **A reclassification report**: for two rules and two forecasts on a report map under a process
law, the expected joint table and the NRI and IDI of expectations of every population, and the
portability of every function of the joint table between every source and target. -/
structure ReclassificationReport (Population : Type*) where
  /-- The expected joint table of each population, indexed by the two calls and the outcome. -/
  table : Population → (Bool × Bool) × Bool → ℝ
  /-- The net reclassification improvement of expectations of each population. -/
  nri : Population → ℝ
  /-- The integrated discrimination improvement of expectations of each population. -/
  idi : Population → ℝ
  /-- The portability of each function of the joint table from each source to each target. -/
  portability : Population → Population → (((Bool × Bool) × Bool → ℝ) → ℝ) → ℝ

/-- **The reclassification report** of two rules and two forecasts on a report map
`hap ↦ ((s₁, s₂), b)` under a kernel started at `x₀`. -/
def reclassificationReport
    (κ : Kernel (FrequencyState Deme Locus Allele) (FrequencyState Deme Locus Allele))
    (x0 : FrequencyState Deme Locus Allele)
    (report : FullHaplotype Locus Allele → (Score₁ × Score₂) × Bool) (called₁ : Score₁ → Bool)
    (called₂ : Score₂ → Bool) (forecast₁ : Score₁ → ℝ) (forecast₂ : Score₂ → ℝ) :
    ReclassificationReport Deme where
  table deme := expectedJointTable κ x0 deme report called₁ called₂
  nri deme := tableNRI (expectedJointTable κ x0 deme report called₁ called₂)
  idi deme := expectedIDI κ x0 deme report forecast₁ forecast₂
  portability source target metric :=
    metric (expectedJointTable κ x0 target report called₁ called₂)
      / metric (expectedJointTable κ x0 source report called₁ called₂)

/-- **Degree one fixes the reclassification report under any process law.**  Two process laws
that agree, from their initial states, on every frequency polynomial of total degree at most one
give every pair of rules and every pair of forecasts on every report map the same reclassification
report.  That is the same expected joint table, NRI and IDI of expectations in every deme, and the
same portability of every function of the joint table.

Assumes: agreement up to degree one. -/
theorem reclassificationReport_eq_of_polynomialsAgreeAt_one
    {κ₁ κ₂ : Kernel (FrequencyState Deme Locus Allele) (FrequencyState Deme Locus Allele)}
    {x₁ x₂ : FrequencyState Deme Locus Allele} (h : PolynomialsAgreeAt 1 κ₁ κ₂ x₁ x₂)
    (report : FullHaplotype Locus Allele → (Score₁ × Score₂) × Bool) (called₁ : Score₁ → Bool)
    (called₂ : Score₂ → Bool) (forecast₁ : Score₁ → ℝ) (forecast₂ : Score₂ → ℝ) :
    reclassificationReport κ₁ x₁ report called₁ called₂ forecast₁ forecast₂
      = reclassificationReport κ₂ x₂ report called₁ called₂ forecast₁ forecast₂ := by
  have hterm : ∀ (deme : Deme) (p : MvPolynomial (FullHaplotype Locus Allele) ℝ),
      p.totalDegree ≤ 1 → ∫ y, eval (stateLaw y deme).mass p ∂(κ₁ x₁)
        = ∫ y, eval (stateLaw y deme).mass p ∂(κ₂ x₂) :=
    fun deme p hp ↦ by
      simpa only [polynomialFunction_apply, eval_demePolynomial] using
        h (demePolynomial deme p) ((totalDegree_rename_le _ _).trans hp)
  have htable : ∀ deme : Deme, expectedJointTable κ₁ x₁ deme report called₁ called₂
      = expectedJointTable κ₂ x₂ deme report called₁ called₂ :=
    fun deme ↦ funext fun cell ↦ by
      simpa only [expectedJointTable, eval_cellPolynomial] using
        hterm deme (cellPolynomial (jointCallReport report called₁ called₂) cell)
          (totalDegree_cellPolynomial_le _ _)
  have hforecast : ∀ (deme : Deme) (forecast : Score₁ × Score₂ → ℝ) (outcome : Bool),
      expectedForecastMass κ₁ x₁ deme report forecast outcome
        = expectedForecastMass κ₂ x₂ deme report forecast outcome :=
    fun deme forecast outcome ↦ by
      simpa only [expectedForecastMass, eval_expectationPolynomial] using
        hterm deme
          (expectationPolynomial fun hap ↦
            if (report hap).2 = outcome then forecast (report hap).1 else 0)
          (totalDegree_expectationPolynomial_le _)
  have hslope : ∀ (deme : Deme) (forecast : Score₁ × Score₂ → ℝ),
      expectedDiscriminationSlope κ₁ x₁ deme report forecast
        = expectedDiscriminationSlope κ₂ x₂ deme report forecast :=
    fun deme forecast ↦ by simp only [expectedDiscriminationSlope, hforecast]
  simp only [reclassificationReport, ReclassificationReport.mk.injEq]
  refine ⟨funext htable, funext fun deme ↦ by rw [htable], funext fun deme ↦ ?_,
    funext fun source ↦ funext fun target ↦ funext fun metric ↦ by rw [htable, htable]⟩
  simp only [expectedIDI, hslope]

/-- **An event history and a rate history with equal budget-1 moments give one reclassification
report.**  If a history of epochs, splits and pulses from `x₁` and a rate history with continuous
dual generator from `x₂` have equal propagated budget-1 moments, every pair of rules and every pair
of forecasts on every report map has the same reclassification report under both.

Assumes: equal propagated budget-1 moments. -/
theorem reclassificationReport_historyEvent_eq_rateHistory (ℓ₀ : Locus)
    (hap₀ : FullHaplotype Locus Allele)
    (events : List ((NeutralRates Deme Locus Allele × ℝ≥0) ⊕ PulseMatrix Deme))
    {rates : ℝ → NeutralRates Deme Locus Allele} {T : ℝ} (hT : 0 ≤ T)
    (hcontinuous : ∀ capacity : Locus → ℕ,
      ContinuousOn (fun t ↦ dualGenerator (rates t) capacity) (Set.Icc 0 T))
    {x₁ x₂ : FrequencyState Deme Locus Allele}
    (hmoments : historyEventPropagator (fun _ ↦ 1) events *ᵥ budgetMomentFeature (fun _ ↦ 1) x₁
      = rateHistoryDualPropagator rates (fun _ ↦ 1) T *ᵥ budgetMomentFeature (fun _ ↦ 1) x₂)
    (report : FullHaplotype Locus Allele → (Score₁ × Score₂) × Bool) (called₁ : Score₁ → Bool)
    (called₂ : Score₂ → Bool) (forecast₁ : Score₁ → ℝ) (forecast₂ : Score₂ → ℝ) :
    reclassificationReport (historyEventKernel ℓ₀ hap₀ events) x₁ report called₁ called₂
        forecast₁ forecast₂
      = reclassificationReport (rateHistoryKernel rates ℓ₀ hap₀ hT hcontinuous) x₂ report
          called₁ called₂ forecast₁ forecast₂ :=
  reclassificationReport_eq_of_polynomialsAgreeAt_one
    (polynomialsAgreeAt_of_hasDualMoments ℓ₀ (hasDualMoments_historyEventKernel ℓ₀ hap₀ events 1)
      (hasDualMoments_rateHistoryKernel hT hcontinuous ℓ₀ hap₀ 1) hmoments)
    report called₁ called₂ forecast₁ forecast₂

/-! ## Sensitivities port, NRI does not -/

/-- The source joint law of the reclassification witness, on cells `((old call, new call),
outcome)`.  The cases put one quarter on each concordant call pair, and every control is cleared by
both rules. -/
def witnessSourceJoint : FiniteReportLaw ((Bool × Bool) × Bool) where
  mass := fun cell ↦ if cell.2 then (if cell.1.1 = cell.1.2 then 1 / 4 else 0)
    else (if cell.1.1 = false ∧ cell.1.2 = false then 1 / 2 else 0)
  mass_nonneg := by intro cell; split_ifs <;> norm_num
  mass_sum := by norm_num [Fintype.sum_prod_type, Fintype.sum_bool]

/-- The target joint law of the reclassification witness.  The cases are those of the source law;
the controls put one quarter on the cell cleared by both rules and one quarter on the cell called
by the old rule alone. -/
def witnessTargetJoint : FiniteReportLaw ((Bool × Bool) × Bool) where
  mass := fun cell ↦ if cell.2 then (if cell.1.1 = cell.1.2 then 1 / 4 else 0)
    else (if cell.1.2 = false then 1 / 4 else 0)
  mass_nonneg := by intro cell; split_ifs <;> norm_num
  mass_sum := by norm_num [Fintype.sum_prod_type, Fintype.sum_bool]

/-- **Sensitivities port, NRI does not.**  Under both witness laws each rule has sensitivity one
half.  The old rule's specificity falls from one to one half and the NRI rises from zero to one
half, the gain in Youden's J that `tableNRI_eq_tableYouden_sub` names. -/
theorem nriShift_witness :
    tableSensitivity (oldTable witnessSourceJoint.mass) = 1 / 2
      ∧ tableSensitivity (oldTable witnessTargetJoint.mass) = 1 / 2
      ∧ tableSensitivity (newTable witnessSourceJoint.mass) = 1 / 2
      ∧ tableSensitivity (newTable witnessTargetJoint.mass) = 1 / 2
      ∧ tableSpecificity (oldTable witnessSourceJoint.mass) = 1
      ∧ tableSpecificity (oldTable witnessTargetJoint.mass) = 1 / 2
      ∧ tableNRI witnessSourceJoint.mass = 0
      ∧ tableNRI witnessTargetJoint.mass = 1 / 2 := by
  norm_num [tableSensitivity, tableSpecificity, oldTable, newTable, tableNRI, jointOutcomeMass,
    witnessSourceJoint, witnessTargetJoint]

end

end Descent.Portability.EndToEndReclassificationLaw
