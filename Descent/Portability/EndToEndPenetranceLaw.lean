/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.PortabilityMomentLadder
import Descent.Portability.EndToEndDecisionLaw

assert_below Descent.Decision Descent.Program

/-!
# The end-to-end law of penetrance outcomes

`EndToEndDecisionLaw`, `EndToEndDiscriminationLaw` and `EndToEndBrierLaw` carry the binary-outcome
metrics of a score through a demographic process law for a deterministic outcome, a report map
`hap ↦ (s, b)` with `b : Bool`.  A real outcome is random given the genotype.  This module carries
the same metrics for penetrance outcomes: a haplotype `h` with score `s(h)` is a case with
probability `π(h)` and a control otherwise.

The finite law.  For a rule `called` on the scores, the penetrance confusion table
(`penetranceConfusion`) weights the called or cleared mass of each haplotype by `π(h)` in the case
column and by `1 - π(h)` in the control column (`penetranceCellWeight`).  Its cells sum to one
(`sum_penetranceConfusion`) and are nonnegative when `0 ≤ π ≤ 1` (`penetranceConfusion_nonneg`).
The net benefit at a threshold `t` (`penetranceNetBenefit`) is `TP - FP · t / (1 - t)` of that
table (`penetranceNetBenefit_eq_confusion`).  The Brier loss of a forecast `f`,
`Σ_h mass(h) (π(h) (1 - f(h))² + (1 - π(h)) f(h)²)` (`penetranceBrier`), is the mean squared
distance of the forecast from the penetrance plus the Bernoulli variance `π (1 - π)`
(`penetranceBrier_eq_add`).  The AUC numerator `N = 4 E[π(h) (1 - π(h')) c(h, h')]`, for the
half-credit concordance `c` of two independent draws, and the denominator `D = 4 p (1 - p)`, for
the prevalence `p = E π`, are pair expectations (`penetrancePairMass`, `penetranceAUCNumerator`,
`penetranceAUCDenominator`, `penetranceAUCDenominator_eq`).

Deterministic outcomes are the special case `π ∈ {0, 1}`.  For the indicator of an outcome `b`, the
penetrance table is the confusion report law of `hap ↦ (s, b)` (`penetranceConfusion_indicator`),
the AUC components are the corpus `aucNumerator` and `aucDenominator`
(`penetranceAUCNumerator_indicator`, `penetranceAUCDenominator_indicator`), and the Brier loss is
the corpus mean squared error (`penetranceBrier_indicator`).  Under a process law, a penetrance with
values in `{0, 1}` has the expected confusion table of the report `hap ↦ (s, decide (π = 1))`
(`expectedPenetranceConfusion_eq_expectedConfusion`).  An indicator penetrance has the AUC
portability `EndToEndDiscriminationLaw.expectedAUCPortability`
(`expectedPenetranceAUCPortability_indicator`).

The rungs.
* Every cell, the prevalence, the net benefit and the Brier loss are expectations over one draw, so
  degree one fixes them (`integral_expectation_eq_of_polynomialsAgreeAt_one`) and with them the
  whole penetrance decision report (`penetranceReport_eq_of_polynomialsAgreeAt_one`).
* The AUC components are expectations over two independent draws, so degree two fixes them
  (`integral_penetrancePairMass_eq_of_polynomialsAgreeAt_two`,
  `integral_penetranceAUC_eq_of_polynomialsAgreeAt_two`) and the AUC portability of expectations
  (`expectedPenetranceAUCPortability_eq_of_polynomialsAgreeAt_two`).  Degree two carries both
  (`penetranceReport_and_aucPortability_eq_of_polynomialsAgreeAt_two`).

Event and rate histories.  Take a history of epochs, splits and pulses and a continuous rate
history.  If their propagated budget-1 moments agree, every rule on every penetrance has the same
penetrance report under both (`penetranceReport_historyEvent_eq_rateHistory`).  If their budget-2
moments agree, the penetrance AUC portability agrees as well
(`penetranceReport_and_aucPortability_historyEvent_eq_rateHistory`).

Significance.  Making the outcome random given the genotype moves none of these metrics up the
moment ladder.  The penetrance enters as fixed weights on the haplotype frequencies, so the
decision metrics and the Brier loss stay at degree one and the AUC stays at degree two.

Scope.  The penetrance is a fixed function of the haplotype, one chromosome is sampled per
individual, and the outcomes of different individuals are independent given their haplotypes.  The
table metrics are in ratio-of-expectations form.  Expected per-population recall, precision and AUC
under penetrance outcomes are not treated here.

## Empirical status

None.  The bodies here are finite-sum identities and comparisons of integrals of polynomials in the
haplotype frequencies against Markov kernels, so no measurement can bear on them.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.EndToEndPenetranceLaw

open MeasureTheory ProbabilityTheory MvPolynomial Descent.Coalescent PartialHaplotypeCarrier
  PartialHaplotypeDualGenerator PartialHaplotypeDualSemigroup NeutralFellerGenerator
  NeutralPolynomialSemigroup PartialHaplotypeMicroscopicApproximation PartialHaplotypePulseKernel
  NeutralPulseHistoryKernel NeutralRateHistoryRealization NeutralRateHistoryKernel
  ReplicaMetricInstances EndToEndPortabilityLaw EndToEndDiscriminationLaw EndToEndBrierLaw
  EndToEndDecisionLaw PortabilityMomentLadder
open scoped Matrix NNReal

noncomputable section

/-! ## Weights of one state -/

section Weights

variable {State Score : Type*}

/-- The weight of one state in the cell `(c, b)` of a penetrance confusion table: one when the rule
calls the state's score `c`, times the probability that its outcome is `b`, which is the penetrance
for a case and its complement for a control. -/
def penetranceCellWeight (score : State → Score) (penetrance : State → ℝ)
    (called : Score → Bool) (cell : Bool × Bool) (state : State) : ℝ :=
  (if called (score state) = cell.1 then 1 else 0)
    * (if cell.2 then penetrance state else 1 - penetrance state)

/-- The weight of one state in the net benefit of a rule at a threshold probability `t`: when the
rule calls the state, its penetrance minus the threshold odds times its complement. -/
def penetranceNetBenefitWeight (score : State → Score) (penetrance : State → ℝ)
    (called : Score → Bool) (t : ℝ) (state : State) : ℝ :=
  (if called (score state) then 1 else 0)
    * (penetrance state - (1 - penetrance state) * (t / (1 - t)))

/-- The weight of one state in the Brier loss of a forecast: the squared miss `(1 - f)²` of a case
weighted by the penetrance, plus the squared miss `f²` of a control weighted by its complement. -/
def penetranceBrierWeight (penetrance forecast : State → ℝ) (state : State) : ℝ :=
  penetrance state * (1 - forecast state) ^ 2 + (1 - penetrance state) * forecast state ^ 2

end Weights

/-! ## Penetrance metrics of a finite law -/

section FiniteLaw

variable {State : Type*} [Fintype State] {Score : Type*}

/-- **The penetrance confusion table** of a rule on a finite law: the expected mass of each cell
`(call, outcome)` when a state is a case with probability `penetrance state`. -/
def penetranceConfusion (law : FiniteReportLaw State) (score : State → Score)
    (penetrance : State → ℝ) (called : Score → Bool) (cell : Bool × Bool) : ℝ :=
  law.expectation (penetranceCellWeight score penetrance called cell)

/-- **Net benefit of a rule under penetrance outcomes** at a threshold probability `t`. -/
def penetranceNetBenefit (law : FiniteReportLaw State) (score : State → Score)
    (penetrance : State → ℝ) (called : Score → Bool) (t : ℝ) : ℝ :=
  law.expectation (penetranceNetBenefitWeight score penetrance called t)

/-- **The Brier loss of a forecast under penetrance outcomes.** -/
def penetranceBrier (law : FiniteReportLaw State) (penetrance forecast : State → ℝ) : ℝ :=
  law.expectation (penetranceBrierWeight penetrance forecast)

/-- **The penetrance pair mass** of a credit: over two independent draws, the probability that the
first is a case and the second a control, weighted by the credit of the pair. -/
def penetrancePairMass (law : FiniteReportLaw State) (penetrance : State → ℝ)
    (credit : State → State → ℝ) : ℝ :=
  law.expectation fun first ↦ law.expectation fun second ↦
    penetrance first * (1 - penetrance second) * credit first second

/-- **The AUC numerator of penetrance outcomes**, `N = 4A`: four times the pair mass of the
half-credit concordance of the score. -/
def penetranceAUCNumerator (law : FiniteReportLaw State) (score penetrance : State → ℝ) : ℝ :=
  4 * penetrancePairMass law penetrance fun first second ↦
    empiricalAUCComparison (score first) (score second)

/-- **The AUC denominator of penetrance outcomes**: four times the pair mass of the unit credit. -/
def penetranceAUCDenominator (law : FiniteReportLaw State) (penetrance : State → ℝ) : ℝ :=
  4 * penetrancePairMass law penetrance fun _ _ ↦ 1

/-- **The penetrance confusion table partitions the population.**  Its four cells sum to one for
every rule and every penetrance. -/
theorem sum_penetranceConfusion (law : FiniteReportLaw State) (score : State → Score)
    (penetrance : State → ℝ) (called : Score → Bool) :
    ∑ cell, penetranceConfusion law score penetrance called cell = 1 := by
  have hpoint : ∀ state, ∑ cell, penetranceCellWeight score penetrance called cell state = 1 :=
    fun state ↦ by
      have hcall : ∀ call : Bool, penetranceCellWeight score penetrance called (call, true) state
          + penetranceCellWeight score penetrance called (call, false) state
          = if called (score state) = call then 1 else 0 := fun call ↦
        show (if called (score state) = call then (1 : ℝ) else 0) * penetrance state
            + (if called (score state) = call then 1 else 0) * (1 - penetrance state) = _ by
          ring
      simp only [Fintype.sum_prod_type, Fintype.sum_bool, hcall]
      cases called (score state) <;> norm_num
  simp only [penetranceConfusion, FiniteReportLaw.expectation]
  rw [Finset.sum_comm]
  simp only [← Finset.mul_sum, hpoint, mul_one, law.mass_sum]

/-- **Every cell of the penetrance confusion table is nonnegative** when the penetrance is a
probability.

Assumes: `0 ≤ penetrance state ≤ 1` for every state. -/
theorem penetranceConfusion_nonneg (law : FiniteReportLaw State) (score : State → Score)
    (penetrance : State → ℝ) (hlower : ∀ state, 0 ≤ penetrance state)
    (hupper : ∀ state, penetrance state ≤ 1) (called : Score → Bool) (cell : Bool × Bool) :
    0 ≤ penetranceConfusion law score penetrance called cell := by
  simp only [penetranceConfusion, FiniteReportLaw.expectation, penetranceCellWeight]
  refine Finset.sum_nonneg fun state _ ↦ mul_nonneg (law.mass_nonneg state) (mul_nonneg ?_ ?_)
  · split_ifs <;> norm_num
  · split_ifs
    · exact hlower state
    · linarith [hupper state]

/-- **Net benefit is true positives minus threshold-weighted false positives.**  The penetrance net
benefit of a rule is `TP - FP · t / (1 - t)` of its penetrance confusion table. -/
theorem penetranceNetBenefit_eq_confusion (law : FiniteReportLaw State) (score : State → Score)
    (penetrance : State → ℝ) (called : Score → Bool) (t : ℝ) :
    penetranceNetBenefit law score penetrance called t
      = penetranceConfusion law score penetrance called (true, true)
        - penetranceConfusion law score penetrance called (true, false) * (t / (1 - t)) := by
  have hcase : ∀ state, penetranceCellWeight score penetrance called (true, true) state
      = (if called (score state) then 1 else 0) * penetrance state := fun _ ↦ rfl
  have hcontrol : ∀ state, penetranceCellWeight score penetrance called (true, false) state
      = (if called (score state) then 1 else 0) * (1 - penetrance state) := fun _ ↦ rfl
  simp only [penetranceNetBenefit, penetranceConfusion, FiniteReportLaw.expectation,
    Finset.sum_mul, ← Finset.sum_sub_distrib, hcase, hcontrol]
  refine Finset.sum_congr rfl fun state _ ↦ ?_
  simp only [penetranceNetBenefitWeight]
  split_ifs <;> ring

/-- **The penetrance Brier loss is a squared distance plus Bernoulli noise.**  For every forecast it
is the corpus mean squared error of the forecast against the penetrance plus the expected variance
`π (1 - π)` of the outcome. -/
theorem penetranceBrier_eq_add (law : FiniteReportLaw State) (penetrance forecast : State → ℝ) :
    penetranceBrier law penetrance forecast
      = law.meanSquaredError forecast penetrance
        + law.expectation fun state ↦ penetrance state * (1 - penetrance state) := by
  simp only [penetranceBrier, penetranceBrierWeight, FiniteReportLaw.meanSquaredError,
    FiniteReportLaw.expectation, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun state _ ↦ by ring

/-- The pair expectation of a product of one-draw observables is the product of their
expectations. -/
theorem expectation_pair_product (law : FiniteReportLaw State) (first second : State → ℝ) :
    (law.expectation fun a ↦ law.expectation fun b ↦ first a * second b)
      = law.expectation first * law.expectation second := by
  simp only [FiniteReportLaw.expectation]
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  rw [Finset.mul_sum, Finset.mul_sum]
  exact Finset.sum_congr rfl fun b _ ↦ by ring

/-- **The penetrance AUC denominator is `4 p (1 - p)`**, for the prevalence `p`, the expected
penetrance. -/
theorem penetranceAUCDenominator_eq (law : FiniteReportLaw State) (penetrance : State → ℝ) :
    penetranceAUCDenominator law penetrance
      = 4 * (law.expectation penetrance * (1 - law.expectation penetrance)) := by
  rw [← law.expectation_complement penetrance, ← expectation_pair_product]
  simp only [penetranceAUCDenominator, penetrancePairMass, mul_one]

/-- **Deterministic outcomes: the penetrance table is the confusion report law.**  When the
penetrance is the indicator of a binary outcome, each cell of the penetrance confusion table is the
mass of that cell under the confusion report law of the report `state ↦ (score, outcome)`. -/
theorem penetranceConfusion_indicator (law : FiniteReportLaw State) (score : State → Score)
    (outcome : State → Bool) (called : Score → Bool) (cell : Bool × Bool) :
    penetranceConfusion law score (fun state ↦ if outcome state then 1 else 0) called cell
      = (law.pushforward
          (confusionReport (fun state ↦ (score state, outcome state)) called)).mass cell := by
  obtain ⟨call, result⟩ := cell
  rw [pushforwardMass_eq_expectation]
  simp only [penetranceConfusion, penetranceCellWeight, FiniteReportLaw.expectation,
    confusionReport]
  refine Finset.sum_congr rfl fun state _ ↦ congrArg (law.mass state * ·) ?_
  cases called (score state) <;> cases outcome state <;> cases call <;> cases result <;> simp

/-- **Deterministic outcomes: the penetrance Brier loss is the mean squared error.**  When the
penetrance is the indicator of a binary outcome, the penetrance Brier loss of a forecast is the
corpus mean squared error of the forecast against that indicator. -/
theorem penetranceBrier_indicator (law : FiniteReportLaw State) (outcome : State → Bool)
    (forecast : State → ℝ) :
    penetranceBrier law (fun state ↦ if outcome state then 1 else 0) forecast
      = law.meanSquaredError forecast fun state ↦ if outcome state then 1 else 0 := by
  simp only [penetranceBrier, penetranceBrierWeight, FiniteReportLaw.meanSquaredError,
    FiniteReportLaw.expectation]
  refine Finset.sum_congr rfl fun state _ ↦ ?_
  split_ifs <;> ring

/-- **Deterministic outcomes: the penetrance AUC numerator is the corpus numerator.**  When the
penetrance is the indicator of a binary outcome, the penetrance AUC numerator of a score is the
corpus AUC numerator `4A` of that score and outcome. -/
theorem penetranceAUCNumerator_indicator (law : FiniteReportLaw State) (score : State → ℝ)
    (outcome : State → Bool) :
    penetranceAUCNumerator law score (fun state ↦ if outcome state then 1 else 0)
      = aucNumerator law score outcome := by
  simp only [penetranceAUCNumerator, penetrancePairMass, aucNumerator,
    FiniteReportLaw.binaryAUCNumerator, FiniteReportLaw.expectation]
  congr 1
  refine Finset.sum_congr rfl fun first _ ↦
    congrArg (law.mass first * ·) (Finset.sum_congr rfl fun second _ ↦ ?_)
  cases outcome first <;> cases outcome second <;> simp

/-- **Deterministic outcomes: the penetrance AUC denominator is the corpus denominator.**  When the
penetrance is the indicator of a binary outcome, the penetrance AUC denominator is the corpus AUC
denominator `4p(1 - p)` of that outcome. -/
theorem penetranceAUCDenominator_indicator (law : FiniteReportLaw State)
    (outcome : State → Bool) :
    penetranceAUCDenominator law (fun state ↦ if outcome state then 1 else 0)
      = aucDenominator law outcome := by
  simp only [penetranceAUCDenominator_eq, aucDenominator, FiniteReportLaw.binaryCaseMass]

end FiniteLaw

variable {Deme Locus : Type*} {Allele : Locus → Type*}
variable [Fintype Deme] [DecidableEq Deme] [Fintype Locus] [DecidableEq Locus]
  [∀ ℓ, Fintype (Allele ℓ)] [∀ ℓ, DecidableEq (Allele ℓ)]

attribute [local instance] isMarkovKernel_historyEventKernel isMarkovKernel_rateHistoryKernel

/-! ## Penetrance metrics under a process law -/

/-- **The expected penetrance confusion table** of a rule in a deme, under a kernel started at
`x₀`. -/
def expectedPenetranceConfusion
    (κ : Kernel (FrequencyState Deme Locus Allele) (FrequencyState Deme Locus Allele))
    (x0 : FrequencyState Deme Locus Allele) (deme : Deme) {Score : Type*}
    (score : FullHaplotype Locus Allele → Score) (penetrance : FullHaplotype Locus Allele → ℝ)
    (called : Score → Bool) (cell : Bool × Bool) : ℝ :=
  ∫ y, penetranceConfusion (stateLaw y deme) score penetrance called cell ∂(κ x0)

/-- **AUC portability of expectations under penetrance outcomes**: the target-over-source ratio
`(E N_t · E D_s) / (E D_t · E N_s)` of expected penetrance AUC numerators and denominators, under a
kernel started at `x₀`. -/
def expectedPenetranceAUCPortability
    (κ : Kernel (FrequencyState Deme Locus Allele) (FrequencyState Deme Locus Allele))
    (x0 : FrequencyState Deme Locus Allele) (source target : Deme)
    (score penetrance : FullHaplotype Locus Allele → ℝ) : ℝ :=
  ((∫ y, penetranceAUCNumerator (stateLaw y target) score penetrance ∂(κ x0))
      * ∫ y, penetranceAUCDenominator (stateLaw y source) penetrance ∂(κ x0))
    / ((∫ y, penetranceAUCDenominator (stateLaw y target) penetrance ∂(κ x0))
      * ∫ y, penetranceAUCNumerator (stateLaw y source) score penetrance ∂(κ x0))

/-- **A penetrance decision report**: for a rule on a score under penetrance outcomes, the expected
confusion table, prevalence, net benefit at every threshold and Brier loss of every forecast in
every population, and the portability of every metric of the table between every source and
target. -/
structure PenetranceReport (Population Hap : Type*) where
  /-- The expected penetrance confusion table of each population, indexed by call and outcome. -/
  table : Population → Bool × Bool → ℝ
  /-- The expected prevalence of each population. -/
  prevalence : Population → ℝ
  /-- The expected net benefit of each population at each threshold probability. -/
  netBenefit : Population → ℝ → ℝ
  /-- The expected Brier loss of each forecast in each population. -/
  brier : Population → (Hap → ℝ) → ℝ
  /-- The portability of each metric of the table from each source to each target. -/
  portability : Population → Population → ((Bool × Bool → ℝ) → ℝ) → ℝ

/-- **The penetrance decision report** of a rule `called` on a score `hap ↦ s` with penetrance
`hap ↦ π`, under a kernel started at `x₀`. -/
def penetranceReport
    (κ : Kernel (FrequencyState Deme Locus Allele) (FrequencyState Deme Locus Allele))
    (x0 : FrequencyState Deme Locus Allele) {Score : Type*}
    (score : FullHaplotype Locus Allele → Score) (penetrance : FullHaplotype Locus Allele → ℝ)
    (called : Score → Bool) : PenetranceReport Deme (FullHaplotype Locus Allele) where
  table deme := expectedPenetranceConfusion κ x0 deme score penetrance called
  prevalence deme := ∫ y, (stateLaw y deme).expectation penetrance ∂(κ x0)
  netBenefit deme t :=
    ∫ y, penetranceNetBenefit (stateLaw y deme) score penetrance called t ∂(κ x0)
  brier deme forecast := ∫ y, penetranceBrier (stateLaw y deme) penetrance forecast ∂(κ x0)
  portability source target metric :=
    metric (expectedPenetranceConfusion κ x0 target score penetrance called)
      / metric (expectedPenetranceConfusion κ x0 source score penetrance called)

/-- **Deterministic outcomes: the expected penetrance table is the expected confusion table.**
Under every kernel, the expected penetrance confusion table of an indicator penetrance is the
expected confusion table of the report `hap ↦ (s, b)`. -/
theorem expectedPenetranceConfusion_indicator
    (κ : Kernel (FrequencyState Deme Locus Allele) (FrequencyState Deme Locus Allele))
    (x0 : FrequencyState Deme Locus Allele) (deme : Deme) {Score : Type*} [Fintype Score]
    (score : FullHaplotype Locus Allele → Score) (outcome : FullHaplotype Locus Allele → Bool)
    (called : Score → Bool) :
    expectedPenetranceConfusion κ x0 deme score (fun hap ↦ if outcome hap then 1 else 0) called
      = expectedConfusion κ x0 deme (fun hap ↦ (score hap, outcome hap)) called := by
  funext cell
  simp only [expectedPenetranceConfusion, expectedConfusion, penetranceConfusion_indicator]

/-- **The deterministic laws are the case `π ∈ {0, 1}`.**  Under every kernel, a penetrance that
takes only the values zero and one has the expected confusion table of the deterministic report
`hap ↦ (s, decide (π = 1))` of `EndToEndDecisionLaw`.

Assumes: the penetrance takes only the values zero and one. -/
theorem expectedPenetranceConfusion_eq_expectedConfusion
    (κ : Kernel (FrequencyState Deme Locus Allele) (FrequencyState Deme Locus Allele))
    (x0 : FrequencyState Deme Locus Allele) (deme : Deme) {Score : Type*} [Fintype Score]
    (score : FullHaplotype Locus Allele → Score) (penetrance : FullHaplotype Locus Allele → ℝ)
    (hvalues : ∀ hap, penetrance hap = 0 ∨ penetrance hap = 1) (called : Score → Bool) :
    expectedPenetranceConfusion κ x0 deme score penetrance called
      = expectedConfusion κ x0 deme (fun hap ↦ (score hap, decide (penetrance hap = 1)))
          called := by
  have hindicator : penetrance = fun hap ↦ if decide (penetrance hap = 1) then 1 else 0 :=
    funext fun hap ↦ by rcases hvalues hap with hvalue | hvalue <;> norm_num [hvalue]
  calc expectedPenetranceConfusion κ x0 deme score penetrance called
      = expectedPenetranceConfusion κ x0 deme score
          (fun hap ↦ if decide (penetrance hap = 1) then 1 else 0) called :=
        congrArg (fun rate ↦ expectedPenetranceConfusion κ x0 deme score rate called) hindicator
    _ = expectedConfusion κ x0 deme (fun hap ↦ (score hap, decide (penetrance hap = 1)))
          called :=
        expectedPenetranceConfusion_indicator κ x0 deme score
          (fun hap ↦ decide (penetrance hap = 1)) called

/-- **Deterministic outcomes: the penetrance AUC portability is the AUC portability.**  Under every
kernel, the penetrance AUC portability of an indicator penetrance is the AUC portability of
expectations of `EndToEndDiscriminationLaw` for that outcome. -/
theorem expectedPenetranceAUCPortability_indicator
    (κ : Kernel (FrequencyState Deme Locus Allele) (FrequencyState Deme Locus Allele))
    (x0 : FrequencyState Deme Locus Allele) (source target : Deme)
    (score : FullHaplotype Locus Allele → ℝ) (outcome : FullHaplotype Locus Allele → Bool) :
    expectedPenetranceAUCPortability κ x0 source target score
        (fun hap ↦ if outcome hap then 1 else 0)
      = expectedAUCPortability κ x0 source target score outcome := by
  simp only [expectedPenetranceAUCPortability, expectedAUCPortability,
    penetranceAUCNumerator_indicator, penetranceAUCDenominator_indicator]

/-! ## The rungs -/

/-- **Degree one fixes every expected one-draw expectation.**  Two process laws that agree up to
degree one give every observable of a haplotype, in every deme, one expected expectation.

Assumes: agreement up to degree one. -/
theorem integral_expectation_eq_of_polynomialsAgreeAt_one
    {κ₁ κ₂ : Kernel (FrequencyState Deme Locus Allele) (FrequencyState Deme Locus Allele)}
    {x₁ x₂ : FrequencyState Deme Locus Allele} (h : PolynomialsAgreeAt 1 κ₁ κ₂ x₁ x₂)
    (deme : Deme) (value : FullHaplotype Locus Allele → ℝ) :
    ∫ y, (stateLaw y deme).expectation value ∂(κ₁ x₁)
      = ∫ y, (stateLaw y deme).expectation value ∂(κ₂ x₂) := by
  simpa only [polynomialFunction_apply, eval_demePolynomial, eval_expectationPolynomial] using
    h (demePolynomial deme (expectationPolynomial value))
      ((totalDegree_rename_le _ _).trans (totalDegree_expectationPolynomial_le value))

/-- **Degree two fixes every expected pair mass.**  Two process laws that agree up to degree two
give every penetrance and every credit of a pair of haplotypes, in every deme, one expected pair
mass.

Assumes: agreement up to degree two. -/
theorem integral_penetrancePairMass_eq_of_polynomialsAgreeAt_two
    {κ₁ κ₂ : Kernel (FrequencyState Deme Locus Allele) (FrequencyState Deme Locus Allele)}
    {x₁ x₂ : FrequencyState Deme Locus Allele} (h : PolynomialsAgreeAt 2 κ₁ κ₂ x₁ x₂)
    (deme : Deme) (penetrance : FullHaplotype Locus Allele → ℝ)
    (credit : FullHaplotype Locus Allele → FullHaplotype Locus Allele → ℝ) :
    ∫ y, penetrancePairMass (stateLaw y deme) penetrance credit ∂(κ₁ x₁)
      = ∫ y, penetrancePairMass (stateLaw y deme) penetrance credit ∂(κ₂ x₂) := by
  simpa only [penetrancePairMass, polynomialFunction_apply, eval_demePolynomial,
    eval_pairPolynomial] using
    h (demePolynomial deme (pairPolynomial fun first second ↦
        penetrance first * (1 - penetrance second) * credit first second))
      ((totalDegree_rename_le _ _).trans (totalDegree_pairPolynomial_le _))

/-- **Degree two fixes the expected penetrance AUC components.**  Two process laws that agree up to
degree two give every score and every penetrance, in every deme, the same expected penetrance AUC
numerator and denominator.

Assumes: agreement up to degree two. -/
theorem integral_penetranceAUC_eq_of_polynomialsAgreeAt_two
    {κ₁ κ₂ : Kernel (FrequencyState Deme Locus Allele) (FrequencyState Deme Locus Allele)}
    {x₁ x₂ : FrequencyState Deme Locus Allele} (h : PolynomialsAgreeAt 2 κ₁ κ₂ x₁ x₂)
    (deme : Deme) (score penetrance : FullHaplotype Locus Allele → ℝ) :
    ∫ y, penetranceAUCNumerator (stateLaw y deme) score penetrance ∂(κ₁ x₁)
        = ∫ y, penetranceAUCNumerator (stateLaw y deme) score penetrance ∂(κ₂ x₂)
      ∧ ∫ y, penetranceAUCDenominator (stateLaw y deme) penetrance ∂(κ₁ x₁)
        = ∫ y, penetranceAUCDenominator (stateLaw y deme) penetrance ∂(κ₂ x₂) := by
  simp only [penetranceAUCNumerator, penetranceAUCDenominator, integral_const_mul]
  exact ⟨congrArg (4 * ·) (integral_penetrancePairMass_eq_of_polynomialsAgreeAt_two h deme
      penetrance _),
    congrArg (4 * ·) (integral_penetrancePairMass_eq_of_polynomialsAgreeAt_two h deme
      penetrance _)⟩

/-- **Degree one fixes the penetrance decision report under any process law.**  Two process laws
that agree, from their initial states, on every frequency polynomial of total degree at most one
give every rule on every score and every penetrance the same penetrance report.  That is the same
expected confusion table, prevalence, net benefit and Brier loss in every deme, and the same
portability of every metric of the table.

Assumes: agreement up to degree one. -/
theorem penetranceReport_eq_of_polynomialsAgreeAt_one
    {κ₁ κ₂ : Kernel (FrequencyState Deme Locus Allele) (FrequencyState Deme Locus Allele)}
    {x₁ x₂ : FrequencyState Deme Locus Allele} (h : PolynomialsAgreeAt 1 κ₁ κ₂ x₁ x₂)
    {Score : Type*} (score : FullHaplotype Locus Allele → Score)
    (penetrance : FullHaplotype Locus Allele → ℝ) (called : Score → Bool) :
    penetranceReport κ₁ x₁ score penetrance called
      = penetranceReport κ₂ x₂ score penetrance called := by
  have htable : ∀ deme : Deme, expectedPenetranceConfusion κ₁ x₁ deme score penetrance called
      = expectedPenetranceConfusion κ₂ x₂ deme score penetrance called := fun deme ↦
    funext fun cell ↦ integral_expectation_eq_of_polynomialsAgreeAt_one h deme
      (penetranceCellWeight score penetrance called cell)
  simp only [penetranceReport, PenetranceReport.mk.injEq]
  refine ⟨funext htable,
    funext fun deme ↦ integral_expectation_eq_of_polynomialsAgreeAt_one h deme penetrance,
    funext fun deme ↦ funext fun t ↦ integral_expectation_eq_of_polynomialsAgreeAt_one h deme
      (penetranceNetBenefitWeight score penetrance called t),
    funext fun deme ↦ funext fun forecast ↦ integral_expectation_eq_of_polynomialsAgreeAt_one h
      deme (penetranceBrierWeight penetrance forecast),
    funext fun source ↦ funext fun target ↦ funext fun metric ↦ ?_⟩
  rw [htable source, htable target]

/-- **Degree two fixes AUC portability under penetrance outcomes.**  Two process laws that agree,
from their initial states, on every frequency polynomial of total degree at most two give every
score and every penetrance, between every source and target, the same penetrance AUC portability of
expectations.

Assumes: agreement up to degree two. -/
theorem expectedPenetranceAUCPortability_eq_of_polynomialsAgreeAt_two
    {κ₁ κ₂ : Kernel (FrequencyState Deme Locus Allele) (FrequencyState Deme Locus Allele)}
    {x₁ x₂ : FrequencyState Deme Locus Allele} (h : PolynomialsAgreeAt 2 κ₁ κ₂ x₁ x₂)
    (source target : Deme) (score penetrance : FullHaplotype Locus Allele → ℝ) :
    expectedPenetranceAUCPortability κ₁ x₁ source target score penetrance
      = expectedPenetranceAUCPortability κ₂ x₂ source target score penetrance := by
  obtain ⟨hsourceNumerator, hsourceDenominator⟩ :=
    integral_penetranceAUC_eq_of_polynomialsAgreeAt_two h source score penetrance
  obtain ⟨htargetNumerator, htargetDenominator⟩ :=
    integral_penetranceAUC_eq_of_polynomialsAgreeAt_two h target score penetrance
  rw [expectedPenetranceAUCPortability, expectedPenetranceAUCPortability, hsourceNumerator,
    hsourceDenominator, htargetNumerator, htargetDenominator]

/-- **Degree two carries the penetrance report and AUC portability together.**  Two process laws
that agree up to degree two give every rule on every score group the same penetrance report, and
every real-valued risk score the same penetrance AUC portability, for one penetrance.

Assumes: agreement up to degree two. -/
theorem penetranceReport_and_aucPortability_eq_of_polynomialsAgreeAt_two
    {κ₁ κ₂ : Kernel (FrequencyState Deme Locus Allele) (FrequencyState Deme Locus Allele)}
    {x₁ x₂ : FrequencyState Deme Locus Allele} (h : PolynomialsAgreeAt 2 κ₁ κ₂ x₁ x₂)
    {Score : Type*} (score : FullHaplotype Locus Allele → Score)
    (penetrance : FullHaplotype Locus Allele → ℝ) (called : Score → Bool) (source target : Deme)
    (risk : FullHaplotype Locus Allele → ℝ) :
    penetranceReport κ₁ x₁ score penetrance called
        = penetranceReport κ₂ x₂ score penetrance called
      ∧ expectedPenetranceAUCPortability κ₁ x₁ source target risk penetrance
        = expectedPenetranceAUCPortability κ₂ x₂ source target risk penetrance :=
  ⟨penetranceReport_eq_of_polynomialsAgreeAt_one (PolynomialsAgreeAt.mono (by norm_num) h) score
      penetrance called,
    expectedPenetranceAUCPortability_eq_of_polynomialsAgreeAt_two h source target risk penetrance⟩

/-! ## Event and rate histories -/

/-- **An event history and a rate history with equal budget-1 moments give one penetrance
report.**  If a history of epochs, splits and pulses from `x₁` and a rate history with continuous
dual generator from `x₂` have equal propagated budget-1 moments, every rule on every score and every
penetrance has the same penetrance report under both.

Assumes: equal propagated budget-1 moments. -/
theorem penetranceReport_historyEvent_eq_rateHistory {Score : Type*}
    (score : FullHaplotype Locus Allele → Score) (penetrance : FullHaplotype Locus Allele → ℝ)
    (called : Score → Bool) (ℓ₀ : Locus) (hap₀ : FullHaplotype Locus Allele)
    (events : List ((NeutralRates Deme Locus Allele × ℝ≥0) ⊕ PulseMatrix Deme))
    {rates : ℝ → NeutralRates Deme Locus Allele} {T : ℝ} (hT : 0 ≤ T)
    (hcontinuous : ∀ capacity : Locus → ℕ,
      ContinuousOn (fun t ↦ dualGenerator (rates t) capacity) (Set.Icc 0 T))
    {x₁ x₂ : FrequencyState Deme Locus Allele}
    (hmoments : historyEventPropagator (fun _ ↦ 1) events *ᵥ budgetMomentFeature (fun _ ↦ 1) x₁
      = rateHistoryDualPropagator rates (fun _ ↦ 1) T *ᵥ budgetMomentFeature (fun _ ↦ 1) x₂) :
    penetranceReport (historyEventKernel ℓ₀ hap₀ events) x₁ score penetrance called
      = penetranceReport (rateHistoryKernel rates ℓ₀ hap₀ hT hcontinuous) x₂ score penetrance
          called :=
  penetranceReport_eq_of_polynomialsAgreeAt_one
    (polynomialsAgreeAt_of_hasDualMoments ℓ₀ (hasDualMoments_historyEventKernel ℓ₀ hap₀ events 1)
      (hasDualMoments_rateHistoryKernel hT hcontinuous ℓ₀ hap₀ 1) hmoments)
    score penetrance called

/-- **An event history and a rate history with equal budget-2 moments give one penetrance report
and one penetrance AUC portability.**  If a history of epochs, splits and pulses from `x₁` and a
rate history with continuous dual generator from `x₂` have equal propagated budget-2 moments, every
rule has the same penetrance report and every risk score the same penetrance AUC portability under
both.

Assumes: equal propagated budget-2 moments. -/
theorem penetranceReport_and_aucPortability_historyEvent_eq_rateHistory {Score : Type*}
    (score : FullHaplotype Locus Allele → Score) (penetrance : FullHaplotype Locus Allele → ℝ)
    (called : Score → Bool) (source target : Deme) (risk : FullHaplotype Locus Allele → ℝ)
    (ℓ₀ : Locus) (hap₀ : FullHaplotype Locus Allele)
    (events : List ((NeutralRates Deme Locus Allele × ℝ≥0) ⊕ PulseMatrix Deme))
    {rates : ℝ → NeutralRates Deme Locus Allele} {T : ℝ} (hT : 0 ≤ T)
    (hcontinuous : ∀ capacity : Locus → ℕ,
      ContinuousOn (fun t ↦ dualGenerator (rates t) capacity) (Set.Icc 0 T))
    {x₁ x₂ : FrequencyState Deme Locus Allele}
    (hmoments : historyEventPropagator (fun _ ↦ 2) events *ᵥ budgetMomentFeature (fun _ ↦ 2) x₁
      = rateHistoryDualPropagator rates (fun _ ↦ 2) T *ᵥ budgetMomentFeature (fun _ ↦ 2) x₂) :
    penetranceReport (historyEventKernel ℓ₀ hap₀ events) x₁ score penetrance called
        = penetranceReport (rateHistoryKernel rates ℓ₀ hap₀ hT hcontinuous) x₂ score penetrance
          called
      ∧ expectedPenetranceAUCPortability (historyEventKernel ℓ₀ hap₀ events) x₁ source target risk
          penetrance
        = expectedPenetranceAUCPortability (rateHistoryKernel rates ℓ₀ hap₀ hT hcontinuous) x₂
          source target risk penetrance :=
  penetranceReport_and_aucPortability_eq_of_polynomialsAgreeAt_two
    (polynomialsAgreeAt_of_hasDualMoments ℓ₀ (hasDualMoments_historyEventKernel ℓ₀ hap₀ events 2)
      (hasDualMoments_rateHistoryKernel hT hcontinuous ℓ₀ hap₀ 2) hmoments)
    score penetrance called source target risk

end

end Descent.Portability.EndToEndPenetranceLaw
