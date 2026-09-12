/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.EndToEndCorrelationSeries

assert_below Descent.Decision Descent.Program

/-!
# The end-to-end AUC law: discrimination from demography

`EndToEndPortabilityLaw` and `EndToEndCorrelationSeries` carry the squared correlation of a score
through a neutral demographic history.  This module carries the binary AUC through the same
history kernels, and compares the moment budgets the two metrics need.

The input.  A neutral history runs from a frequency state `x₀`: a list of epochs, splits and
admixture pulses (`NeutralPulseHistoryKernel.historyEventKernel`), or a rate path whose dual
generator is continuous on the horizon (`NeutralRateHistoryKernel.rateHistoryKernel`).  A score
and a binary outcome are functions of the haplotype.  In deme `j` the corpus population AUC
`FiniteReportLaw.binaryAUC` is the guarded ratio `N_j / D_j` of the numerator `N = 4A`
(`ReplicaMetricInstances.aucNumerator`) and the denominator `D = 4p(1 - p)`
(`ReplicaMetricInstances.aucDenominator`) of the deme's haplotype law
(`ReplicaMetricInstances.binaryAUC_eq_guardedRatio`).

Polynomials through a kernel.  `HasDualMoments κ n M` says that the expected budget-`n`
configuration moments under `κ` are `M` applied to the initial moments, NOTE1 (20); both history
kernels have it at every budget (`hasDualMoments_historyEventKernel`,
`hasDualMoments_rateHistoryKernel`).  Under it a polynomial of total degree at most `n` in the
haplotype frequencies of one deme integrates to the coefficient vector of its deme copy dotted
with `M` applied to the budget-`n` moments of `x₀` (`integral_eval_stateLaw_eq_dotProduct`,
`integral_eval_stateLaw_historyEventKernel`, `integral_eval_stateLaw_rateHistoryKernel`).

AUC in ratio-of-expectations form.  `N` and `D` have total degree at most two
(`totalDegree_aucNumeratorPolynomial_le`, `totalDegree_aucDenominatorPolynomial_le`), so the
expected numerator and denominator are coefficient vectors dotted with the budget-2 propagated
moments (`integral_aucNumerator_eq_dotProduct`, `integral_aucDenominator_eq_dotProduct`,
`integral_aucNumerator_historyEventKernel`, `integral_aucDenominator_historyEventKernel`).  The
AUC portability of expectations `(E N_t · E D_s) / (E D_t · E N_s)` (`expectedAUCPortability`) is
the rational function `momentAUCPortability` of the budget-2 propagated moments
(`expectedAUCPortability_eq_momentAUCPortability`, `expectedAUCPortability_historyEventKernel`,
`expectedAUCPortability_rateHistoryKernel`).  Two histories whose propagated budget-2 moments
agree have equal AUC portability (`expectedAUCPortability_eq_of_moments_eq`).

The expected AUC.  `N (1 - D)ᵏ` has total degree at most `2 (k + 1)`
(`ReplicaMetricInstances.totalDegree_aucTerm_le`).  Under every Markov kernel the expected AUC,
read as zero where it is undefined, is `Σₖ E[N (1 - D)ᵏ]` (`expectedAUC_eq_tsum`), with no
unit-interval hypothesis, because `0 ≤ N ≤ D ≤ 1` holds for every score.  Along a history it is
`Σₖ cₖ ⬝ (U_{2(k+1)} · H_{2(k+1)}(x₀))` (`expectedAUC_eq_tsum_dotProduct`,
`expectedAUC_historyEventKernel`, `expectedAUC_rateHistoryKernel`), and two histories whose
propagated moments agree at every budget `2 (k + 1)` have equal expected AUC
(`expectedAUC_eq_of_moments_eq`).

Budgets.  The propagated moments of one history at a budget `m` are its propagated moments at any
larger budget `n`, read at the same configurations (`widenConfiguration`,
`historyEventPropagator_mulVec_widenConfiguration`), because both are integrals of one
configuration moment under one process law.  So agreement at a budget is agreement at every
smaller budget (`historyEventMoments_eq_of_le`).  AUC needs the smaller budget: the budget-4
agreement that fixes squared-correlation portability already fixes AUC portability
(`expectedPortability_and_expectedAUCPortability_eq_of_moments_eq`).  The separation first posed
for this module, two histories agreeing on the budget-4 moments but not on the AUC budget, is
therefore impossible for the ratio form, and the theorems just named are its corrected law.  For
the expected metrics the budget families `4 (k + 1)` and `2 (k + 1)` are one family
(`moments_forall_four_iff_forall_two`), so one hypothesis fixes both the expected squared
correlation and the expected AUC
(`expectedSquaredCorrelation_and_expectedAUC_eq_of_moments_eq`).

Significance.  The metric clinical polygenic scores are judged by runs from the demographic
process law to the corpus population AUC through one finite matrix computation at budget two for
the ratio form, or through a convergent series of such computations for the expected AUC.

Scope.  One chromosome is sampled per individual, and the AUC is the corpus half-credit AUC of a
deterministic score.  The converse budget question, whether two histories can agree at budget
two and differ at budget four, is not settled here: no explicit pair of histories is
constructed.  Truncation certificates for the series are not restated.

## Empirical status

None.  The bodies here are polynomial identities, a pointwise geometric series and integrals of
polynomials against Markov kernels whose moments are matrix computations of supplied rates, so
no measurement can bear on them.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.EndToEndDiscriminationLaw

open MeasureTheory ProbabilityTheory MvPolynomial Descent.Coalescent PartialHaplotypeCarrier
  PartialHaplotypeDualGenerator PartialHaplotypeDualSemigroup NeutralFellerGenerator
  NeutralPolynomialSemigroup PartialHaplotypeMicroscopicApproximation PartialHaplotypePulseKernel
  NeutralPulseHistoryKernel NeutralRateHistoryRealization NeutralRateHistoryKernel
  ReplicaMetricInstances PositiveRatioExpansion EndToEndPortabilityLaw EndToEndCorrelationSeries
open scoped Matrix NNReal

noncomputable section

/-! ## The AUC components as population polynomials -/

section PopulationPolynomials

variable {State : Type*} [Fintype State]

/-- The AUC numerator polynomial evaluates to the AUC numerator `N = 4A`. -/
theorem eval_aucNumeratorPolynomial (law : FiniteReportLaw State) (score : State → ℝ)
    (outcome : State → Bool) :
    eval law.mass (aucNumeratorPolynomial score outcome) = aucNumerator law score outcome := by
  simpa only [pow_zero, mul_one] using eval_aucTerm law score outcome 0

/-- The AUC denominator polynomial evaluates to the AUC denominator `D = 4p(1 - p)`. -/
theorem eval_aucDenominatorPolynomial (law : FiniteReportLaw State) (outcome : State → Bool) :
    eval law.mass (aucDenominatorPolynomial outcome) = aucDenominator law outcome := by
  have hcase : eval law.mass (expectationPolynomial fun state : State ↦
      if outcome state then (1 : ℝ) else 0) = law.binaryCaseMass outcome :=
    eval_expectationPolynomial law _
  simp only [aucDenominatorPolynomial, map_mul, map_sub, map_one, eval_C, hcase, aucDenominator]

/-- The AUC numerator polynomial has total degree at most two. -/
theorem totalDegree_aucNumeratorPolynomial_le (score : State → ℝ) (outcome : State → Bool) :
    (aucNumeratorPolynomial score outcome).totalDegree ≤ 2 := by
  simpa only [pow_zero, mul_one, zero_add] using totalDegree_aucTerm_le score outcome 0

/-- The AUC denominator polynomial has total degree at most two: four times the linear case
polynomial against one power of its complement. -/
theorem totalDegree_aucDenominatorPolynomial_le (outcome : State → Bool) :
    (aucDenominatorPolynomial outcome).totalDegree ≤ 2 := by
  have hcase := totalDegree_expectationPolynomial_le fun state : State ↦
    if outcome state then (1 : ℝ) else 0
  have hscaled : (C 4 * expectationPolynomial fun state : State ↦
      if outcome state then (1 : ℝ) else 0).totalDegree ≤ 1 :=
    (totalDegree_mul _ _).trans (by rw [totalDegree_C, zero_add]; exact hcase)
  have hterm := totalDegree_expansionTerm_le _ _ 1 1 1 hscaled hcase
  rw [pow_one, mul_assoc] at hterm
  exact hterm

end PopulationPolynomials

/-- The moment matrices of the uniform budget `n`: square matrices over the budget-`n`
configurations of the dual chain. -/
abbrev BudgetMatrix (Deme Locus : Type*) (Allele : Locus → Type*) [Fintype Deme]
    [DecidableEq Deme] [Fintype Locus] [DecidableEq Locus] [∀ ℓ, Fintype (Allele ℓ)]
    [∀ ℓ, DecidableEq (Allele ℓ)] (n : ℕ) :=
  Matrix (BudgetConfiguration Deme Locus Allele (fun _ ↦ n))
    (BudgetConfiguration Deme Locus Allele (fun _ ↦ n)) ℝ

variable {Deme Locus : Type*} {Allele : Locus → Type*}
variable [Fintype Deme] [DecidableEq Deme] [Fintype Locus] [DecidableEq Locus]
  [∀ ℓ, Fintype (Allele ℓ)] [∀ ℓ, DecidableEq (Allele ℓ)]

/-! ## Population polynomials through a kernel with dual moments -/

/-- **Dual moments at one budget.**  A kernel has budget-`n` dual moments along a matrix `M` when
its expected configuration moments of the uniform budget `n` are `M` applied to the
configuration moments of the initial state, NOTE1 (20). -/
def HasDualMoments
    (κ : Kernel (FrequencyState Deme Locus Allele) (FrequencyState Deme Locus Allele)) (n : ℕ)
    (M : BudgetMatrix Deme Locus Allele n) : Prop :=
  ∀ (x : FrequencyState Deme Locus Allele)
    (ξ : BudgetConfiguration Deme Locus Allele (fun _ ↦ n)),
    ∫ y, polynomialFunction (momentPolynomial ξ.1) y ∂(κ x)
      = (M *ᵥ budgetMomentFeature (fun _ ↦ n) x) ξ

/-- The history kernel of epochs, splits and pulses has dual moments at every budget, along its
chronological propagator. -/
theorem hasDualMoments_historyEventKernel (ℓ₀ : Locus) (hap₀ : FullHaplotype Locus Allele)
    (events : List ((NeutralRates Deme Locus Allele × ℝ≥0) ⊕ PulseMatrix Deme)) (n : ℕ) :
    HasDualMoments (historyEventKernel ℓ₀ hap₀ events) n
      (historyEventPropagator (fun _ ↦ n) events) :=
  integral_momentPolynomial_historyEventKernel ℓ₀ hap₀ (fun _ ↦ n) events

/-- The kernel of a rate history with continuous dual generator has dual moments at every budget,
along the propagator of the rate history. -/
theorem hasDualMoments_rateHistoryKernel {rates : ℝ → NeutralRates Deme Locus Allele} {T : ℝ}
    (hT : 0 ≤ T) (hcontinuous : ∀ capacity : Locus → ℕ,
      ContinuousOn (fun t ↦ dualGenerator (rates t) capacity) (Set.Icc 0 T))
    (ℓ₀ : Locus) (hap₀ : FullHaplotype Locus Allele) (n : ℕ) :
    HasDualMoments (rateHistoryKernel rates ℓ₀ hap₀ hT hcontinuous) n
      (rateHistoryDualPropagator rates (fun _ ↦ n) T) :=
  integral_momentPolynomial_rateHistoryKernel hT hcontinuous ℓ₀ hap₀ (fun _ ↦ n)

/-- A polynomial in the haplotype frequencies of one deme is a continuous observable of the
frequency state. -/
theorem continuous_eval_stateLaw (deme : Deme) (p : MvPolynomial (FullHaplotype Locus Allele) ℝ) :
    Continuous fun y : FrequencyState Deme Locus Allele ↦ eval (stateLaw y deme).mass p :=
  (polynomialFunction (demePolynomial deme p)).continuous.congr fun y ↦
    eval_demePolynomial deme p y

/-- **A population polynomial integrates through the propagated moments.**  Under a Markov kernel
with budget-`n` dual moments along `M`, a polynomial of total degree at most `n` in the haplotype
frequencies of one deme integrates to the coefficient vector of its deme copy dotted with `M`
applied to the budget-`n` configuration moments of the initial state.

Assumes: `HasDualMoments κ n M`. -/
theorem integral_eval_stateLaw_eq_dotProduct (ℓ₀ : Locus) (n : ℕ)
    (κ : Kernel (FrequencyState Deme Locus Allele) (FrequencyState Deme Locus Allele))
    [IsMarkovKernel κ] (M : BudgetMatrix Deme Locus Allele n) (hmoment : HasDualMoments κ n M)
    (deme : Deme) (p : MvPolynomial (FullHaplotype Locus Allele) ℝ) (hp : p.totalDegree ≤ n)
    (x0 : FrequencyState Deme Locus Allele) :
    ∫ y, eval (stateLaw y deme).mass p ∂(κ x0)
      = budgetCoefficients ℓ₀ (fun _ ↦ n) (demePolynomial deme p)
        ⬝ᵥ (M *ᵥ budgetMomentFeature (fun _ ↦ n) x0) := by
  have hdotProduct := integral_polynomial_eq_dotProduct ℓ₀ (fun _ ↦ n) κ M hmoment
    (demePolynomial deme p)
    (withinBudget_of_totalDegree_le ℓ₀ _ ((totalDegree_rename_le _ _).trans hp)) x0
  simpa only [polynomialFunction_apply, eval_demePolynomial] using hdotProduct

/-- **A population polynomial along a history of epochs, splits and pulses.** -/
theorem integral_eval_stateLaw_historyEventKernel (ℓ₀ : Locus) (hap₀ : FullHaplotype Locus Allele)
    (events : List ((NeutralRates Deme Locus Allele × ℝ≥0) ⊕ PulseMatrix Deme)) (n : ℕ)
    (x0 : FrequencyState Deme Locus Allele) (deme : Deme)
    (p : MvPolynomial (FullHaplotype Locus Allele) ℝ) (hp : p.totalDegree ≤ n) :
    ∫ y, eval (stateLaw y deme).mass p ∂(historyEventKernel ℓ₀ hap₀ events x0)
      = budgetCoefficients ℓ₀ (fun _ ↦ n) (demePolynomial deme p)
        ⬝ᵥ (historyEventPropagator (fun _ ↦ n) events
          *ᵥ budgetMomentFeature (fun _ ↦ n) x0) := by
  haveI := isMarkovKernel_historyEventKernel ℓ₀ hap₀ events
  exact integral_eval_stateLaw_eq_dotProduct ℓ₀ n _ _
    (hasDualMoments_historyEventKernel ℓ₀ hap₀ events n) deme p hp x0

/-- **A population polynomial along a time-varying rate history.** -/
theorem integral_eval_stateLaw_rateHistoryKernel {rates : ℝ → NeutralRates Deme Locus Allele}
    {T : ℝ} (hT : 0 ≤ T) (hcontinuous : ∀ capacity : Locus → ℕ,
      ContinuousOn (fun t ↦ dualGenerator (rates t) capacity) (Set.Icc 0 T))
    (ℓ₀ : Locus) (hap₀ : FullHaplotype Locus Allele) (n : ℕ)
    (x0 : FrequencyState Deme Locus Allele) (deme : Deme)
    (p : MvPolynomial (FullHaplotype Locus Allele) ℝ) (hp : p.totalDegree ≤ n) :
    ∫ y, eval (stateLaw y deme).mass p ∂(rateHistoryKernel rates ℓ₀ hap₀ hT hcontinuous x0)
      = budgetCoefficients ℓ₀ (fun _ ↦ n) (demePolynomial deme p)
        ⬝ᵥ (rateHistoryDualPropagator rates (fun _ ↦ n) T
          *ᵥ budgetMomentFeature (fun _ ↦ n) x0) := by
  haveI := isMarkovKernel_rateHistoryKernel hT hcontinuous ℓ₀ hap₀
  exact integral_eval_stateLaw_eq_dotProduct ℓ₀ n _ _
    (hasDualMoments_rateHistoryKernel hT hcontinuous ℓ₀ hap₀ n) deme p hp x0

/-! ## AUC in ratio-of-expectations form -/

/-- **Expected AUC numerator through the budget-2 moments.**  The expected AUC numerator `E N` of
a deme is the coefficient vector of `N = 4A` dotted with the budget-2 propagated moments.

Assumes: `HasDualMoments κ 2 M`. -/
theorem integral_aucNumerator_eq_dotProduct (ℓ₀ : Locus)
    (κ : Kernel (FrequencyState Deme Locus Allele) (FrequencyState Deme Locus Allele))
    [IsMarkovKernel κ] (M : BudgetMatrix Deme Locus Allele 2) (hmoment : HasDualMoments κ 2 M)
    (x0 : FrequencyState Deme Locus Allele) (deme : Deme)
    (score : FullHaplotype Locus Allele → ℝ) (outcome : FullHaplotype Locus Allele → Bool) :
    ∫ y, aucNumerator (stateLaw y deme) score outcome ∂(κ x0)
      = budgetCoefficients ℓ₀ (fun _ ↦ 2)
          (demePolynomial deme (aucNumeratorPolynomial score outcome))
        ⬝ᵥ (M *ᵥ budgetMomentFeature (fun _ ↦ 2) x0) := by
  simpa only [eval_aucNumeratorPolynomial] using integral_eval_stateLaw_eq_dotProduct ℓ₀ 2 κ M
    hmoment deme _ (totalDegree_aucNumeratorPolynomial_le score outcome) x0

/-- **Expected AUC denominator through the budget-2 moments.**  The expected AUC denominator
`E D` of a deme is the coefficient vector of `D = 4p(1 - p)` dotted with the budget-2 propagated
moments.

Assumes: `HasDualMoments κ 2 M`. -/
theorem integral_aucDenominator_eq_dotProduct (ℓ₀ : Locus)
    (κ : Kernel (FrequencyState Deme Locus Allele) (FrequencyState Deme Locus Allele))
    [IsMarkovKernel κ] (M : BudgetMatrix Deme Locus Allele 2) (hmoment : HasDualMoments κ 2 M)
    (x0 : FrequencyState Deme Locus Allele) (deme : Deme)
    (outcome : FullHaplotype Locus Allele → Bool) :
    ∫ y, aucDenominator (stateLaw y deme) outcome ∂(κ x0)
      = budgetCoefficients ℓ₀ (fun _ ↦ 2) (demePolynomial deme (aucDenominatorPolynomial outcome))
        ⬝ᵥ (M *ᵥ budgetMomentFeature (fun _ ↦ 2) x0) := by
  simpa only [eval_aucDenominatorPolynomial] using integral_eval_stateLaw_eq_dotProduct ℓ₀ 2 κ M
    hmoment deme _ (totalDegree_aucDenominatorPolynomial_le outcome) x0

/-- **Expected AUC numerator along a history of epochs, splits and pulses.** -/
theorem integral_aucNumerator_historyEventKernel (ℓ₀ : Locus) (hap₀ : FullHaplotype Locus Allele)
    (events : List ((NeutralRates Deme Locus Allele × ℝ≥0) ⊕ PulseMatrix Deme))
    (x0 : FrequencyState Deme Locus Allele) (deme : Deme)
    (score : FullHaplotype Locus Allele → ℝ) (outcome : FullHaplotype Locus Allele → Bool) :
    ∫ y, aucNumerator (stateLaw y deme) score outcome ∂(historyEventKernel ℓ₀ hap₀ events x0)
      = budgetCoefficients ℓ₀ (fun _ ↦ 2)
          (demePolynomial deme (aucNumeratorPolynomial score outcome))
        ⬝ᵥ (historyEventPropagator (fun _ ↦ 2) events *ᵥ budgetMomentFeature (fun _ ↦ 2) x0) := by
  haveI := isMarkovKernel_historyEventKernel ℓ₀ hap₀ events
  exact integral_aucNumerator_eq_dotProduct ℓ₀ _ _
    (hasDualMoments_historyEventKernel ℓ₀ hap₀ events 2) x0 deme score outcome

/-- **Expected AUC denominator along a history of epochs, splits and pulses.** -/
theorem integral_aucDenominator_historyEventKernel (ℓ₀ : Locus)
    (hap₀ : FullHaplotype Locus Allele)
    (events : List ((NeutralRates Deme Locus Allele × ℝ≥0) ⊕ PulseMatrix Deme))
    (x0 : FrequencyState Deme Locus Allele) (deme : Deme)
    (outcome : FullHaplotype Locus Allele → Bool) :
    ∫ y, aucDenominator (stateLaw y deme) outcome ∂(historyEventKernel ℓ₀ hap₀ events x0)
      = budgetCoefficients ℓ₀ (fun _ ↦ 2) (demePolynomial deme (aucDenominatorPolynomial outcome))
        ⬝ᵥ (historyEventPropagator (fun _ ↦ 2) events *ᵥ budgetMomentFeature (fun _ ↦ 2) x0) := by
  haveI := isMarkovKernel_historyEventKernel ℓ₀ hap₀ events
  exact integral_aucDenominator_eq_dotProduct ℓ₀ _ _
    (hasDualMoments_historyEventKernel ℓ₀ hap₀ events 2) x0 deme outcome

/-- **AUC portability of expectations**: the target-over-source ratio
`(E N_t · E D_s) / (E D_t · E N_s)` of expected AUC numerators and denominators under a kernel
started at `x₀`. -/
def expectedAUCPortability
    (κ : Kernel (FrequencyState Deme Locus Allele) (FrequencyState Deme Locus Allele))
    (x0 : FrequencyState Deme Locus Allele) (source target : Deme)
    (score : FullHaplotype Locus Allele → ℝ) (outcome : FullHaplotype Locus Allele → Bool) : ℝ :=
  ((∫ y, aucNumerator (stateLaw y target) score outcome ∂(κ x0))
      * ∫ y, aucDenominator (stateLaw y source) outcome ∂(κ x0))
    / ((∫ y, aucDenominator (stateLaw y target) outcome ∂(κ x0))
      * ∫ y, aucNumerator (stateLaw y source) score outcome ∂(κ x0))

/-- **The rational AUC portability function** of a budget-2 moment vector, with written-out
coefficients. -/
def momentAUCPortability (ℓ₀ : Locus) (source target : Deme)
    (score : FullHaplotype Locus Allele → ℝ) (outcome : FullHaplotype Locus Allele → Bool)
    (v : BudgetConfiguration Deme Locus Allele (fun _ ↦ 2) → ℝ) : ℝ :=
  ((budgetCoefficients ℓ₀ (fun _ ↦ 2)
        (demePolynomial target (aucNumeratorPolynomial score outcome)) ⬝ᵥ v)
      * (budgetCoefficients ℓ₀ (fun _ ↦ 2)
        (demePolynomial source (aucDenominatorPolynomial outcome)) ⬝ᵥ v))
    / ((budgetCoefficients ℓ₀ (fun _ ↦ 2)
        (demePolynomial target (aucDenominatorPolynomial outcome)) ⬝ᵥ v)
      * (budgetCoefficients ℓ₀ (fun _ ↦ 2)
        (demePolynomial source (aucNumeratorPolynomial score outcome)) ⬝ᵥ v))

/-- **The AUC portability law through the budget-2 moments.**  The AUC portability of expectations
is the rational function `momentAUCPortability` of the budget-2 propagated moments.

Assumes: `HasDualMoments κ 2 M`. -/
theorem expectedAUCPortability_eq_momentAUCPortability (ℓ₀ : Locus)
    (κ : Kernel (FrequencyState Deme Locus Allele) (FrequencyState Deme Locus Allele))
    [IsMarkovKernel κ] (M : BudgetMatrix Deme Locus Allele 2) (hmoment : HasDualMoments κ 2 M)
    (x0 : FrequencyState Deme Locus Allele) (source target : Deme)
    (score : FullHaplotype Locus Allele → ℝ) (outcome : FullHaplotype Locus Allele → Bool) :
    expectedAUCPortability κ x0 source target score outcome
      = momentAUCPortability ℓ₀ source target score outcome
          (M *ᵥ budgetMomentFeature (fun _ ↦ 2) x0) := by
  rw [expectedAUCPortability,
    integral_aucNumerator_eq_dotProduct ℓ₀ κ M hmoment x0 target score outcome,
    integral_aucNumerator_eq_dotProduct ℓ₀ κ M hmoment x0 source score outcome,
    integral_aucDenominator_eq_dotProduct ℓ₀ κ M hmoment x0 target outcome,
    integral_aucDenominator_eq_dotProduct ℓ₀ κ M hmoment x0 source outcome]
  rfl

/-- **The end-to-end AUC portability law along a history of epochs, splits and pulses.**  The AUC
portability of expectations is the rational function `momentAUCPortability` of the chronological
propagator applied to the budget-2 configuration moments of the initial state. -/
theorem expectedAUCPortability_historyEventKernel (ℓ₀ : Locus)
    (hap₀ : FullHaplotype Locus Allele)
    (events : List ((NeutralRates Deme Locus Allele × ℝ≥0) ⊕ PulseMatrix Deme))
    (x0 : FrequencyState Deme Locus Allele) (source target : Deme)
    (score : FullHaplotype Locus Allele → ℝ) (outcome : FullHaplotype Locus Allele → Bool) :
    expectedAUCPortability (historyEventKernel ℓ₀ hap₀ events) x0 source target score outcome
      = momentAUCPortability ℓ₀ source target score outcome
          (historyEventPropagator (fun _ ↦ 2) events *ᵥ budgetMomentFeature (fun _ ↦ 2) x0) := by
  haveI := isMarkovKernel_historyEventKernel ℓ₀ hap₀ events
  exact expectedAUCPortability_eq_momentAUCPortability ℓ₀ _ _
    (hasDualMoments_historyEventKernel ℓ₀ hap₀ events 2) x0 source target score outcome

/-- **The end-to-end AUC portability law along a time-varying rate history.** -/
theorem expectedAUCPortability_rateHistoryKernel {rates : ℝ → NeutralRates Deme Locus Allele}
    {T : ℝ} (hT : 0 ≤ T) (hcontinuous : ∀ capacity : Locus → ℕ,
      ContinuousOn (fun t ↦ dualGenerator (rates t) capacity) (Set.Icc 0 T))
    (ℓ₀ : Locus) (hap₀ : FullHaplotype Locus Allele) (x0 : FrequencyState Deme Locus Allele)
    (source target : Deme) (score : FullHaplotype Locus Allele → ℝ)
    (outcome : FullHaplotype Locus Allele → Bool) :
    expectedAUCPortability (rateHistoryKernel rates ℓ₀ hap₀ hT hcontinuous) x0 source target
        score outcome
      = momentAUCPortability ℓ₀ source target score outcome
          (rateHistoryDualPropagator rates (fun _ ↦ 2) T *ᵥ budgetMomentFeature (fun _ ↦ 2) x0) := by
  haveI := isMarkovKernel_rateHistoryKernel hT hcontinuous ℓ₀ hap₀
  exact expectedAUCPortability_eq_momentAUCPortability ℓ₀ _ _
    (hasDualMoments_rateHistoryKernel hT hcontinuous ℓ₀ hap₀ 2) x0 source target score outcome

/-- **AUC portability sees the history only through the budget-2 moments.**  Two histories, from
two initial states, whose propagated budget-2 configuration moments agree have equal AUC
portability of expectations for every score, binary outcome, source and target. -/
theorem expectedAUCPortability_eq_of_moments_eq (ℓ₀ : Locus) (hap₀ : FullHaplotype Locus Allele)
    {first second : List ((NeutralRates Deme Locus Allele × ℝ≥0) ⊕ PulseMatrix Deme)}
    {x₁ x₂ : FrequencyState Deme Locus Allele}
    (hmoments : historyEventPropagator (fun _ ↦ 2) first *ᵥ budgetMomentFeature (fun _ ↦ 2) x₁
      = historyEventPropagator (fun _ ↦ 2) second *ᵥ budgetMomentFeature (fun _ ↦ 2) x₂)
    (source target : Deme) (score : FullHaplotype Locus Allele → ℝ)
    (outcome : FullHaplotype Locus Allele → Bool) :
    expectedAUCPortability (historyEventKernel ℓ₀ hap₀ first) x₁ source target score outcome
      = expectedAUCPortability (historyEventKernel ℓ₀ hap₀ second) x₂ source target score
          outcome := by
  rw [expectedAUCPortability_historyEventKernel, expectedAUCPortability_historyEventKernel,
    hmoments]

/-! ## Moment budgets -/

/-- A configuration within the uniform budget `m` lies within every larger uniform budget. -/
def widenConfiguration {m n : ℕ} (hmn : m ≤ n)
    (ξ : BudgetConfiguration Deme Locus Allele (fun _ ↦ m)) :
    BudgetConfiguration Deme Locus Allele (fun _ ↦ n) :=
  ⟨ξ.1, fun ℓ ↦ (ξ.2 ℓ).trans hmn⟩

/-- **Propagated moments restrict along budgets.**  The chronological propagator of a history at
a budget `m`, applied to the budget-`m` moments of a state, reads at a configuration what the
propagator at any larger budget `n` reads at the same configuration: both are the expectation of
one configuration moment under the history kernel, for any retained locus `ℓ₀` and seed `hap₀`
of the kernel. -/
theorem historyEventPropagator_mulVec_widenConfiguration (ℓ₀ : Locus)
    (hap₀ : FullHaplotype Locus Allele) {m n : ℕ} (hmn : m ≤ n)
    (events : List ((NeutralRates Deme Locus Allele × ℝ≥0) ⊕ PulseMatrix Deme))
    (x : FrequencyState Deme Locus Allele)
    (ξ : BudgetConfiguration Deme Locus Allele (fun _ ↦ m)) :
    (historyEventPropagator (fun _ ↦ m) events *ᵥ budgetMomentFeature (fun _ ↦ m) x) ξ
      = (historyEventPropagator (fun _ ↦ n) events *ᵥ budgetMomentFeature (fun _ ↦ n) x)
          (widenConfiguration hmn ξ) :=
  (hasDualMoments_historyEventKernel ℓ₀ hap₀ events m x ξ).symm.trans
    (hasDualMoments_historyEventKernel ℓ₀ hap₀ events n x (widenConfiguration hmn ξ))

/-- **Agreement at a budget is agreement at every smaller budget.**  Two histories, from two
initial states, whose propagated moments agree at a budget `n` agree at every budget `m ≤ n`. -/
theorem historyEventMoments_eq_of_le (ℓ₀ : Locus) (hap₀ : FullHaplotype Locus Allele)
    {m n : ℕ} (hmn : m ≤ n)
    {first second : List ((NeutralRates Deme Locus Allele × ℝ≥0) ⊕ PulseMatrix Deme)}
    {x₁ x₂ : FrequencyState Deme Locus Allele}
    (hmoments : historyEventPropagator (fun _ ↦ n) first *ᵥ budgetMomentFeature (fun _ ↦ n) x₁
      = historyEventPropagator (fun _ ↦ n) second *ᵥ budgetMomentFeature (fun _ ↦ n) x₂) :
    historyEventPropagator (fun _ ↦ m) first *ᵥ budgetMomentFeature (fun _ ↦ m) x₁
      = historyEventPropagator (fun _ ↦ m) second *ᵥ budgetMomentFeature (fun _ ↦ m) x₂ := by
  funext ξ
  rw [historyEventPropagator_mulVec_widenConfiguration ℓ₀ hap₀ hmn first x₁ ξ,
    historyEventPropagator_mulVec_widenConfiguration ℓ₀ hap₀ hmn second x₂ ξ, hmoments]

/-- **The squared-correlation budget already fixes AUC portability.**  If two histories agree on
the propagated budget-4 moments, which fix the portability of expected squared-correlation
components of a score against the indicator of a binary outcome, they also agree on the
budget-2 moments and hence on the AUC portability of expectations.  No pair of histories agrees
at budget four and disagrees at the AUC budget. -/
theorem expectedPortability_and_expectedAUCPortability_eq_of_moments_eq (ℓ₀ : Locus)
    (hap₀ : FullHaplotype Locus Allele)
    {first second : List ((NeutralRates Deme Locus Allele × ℝ≥0) ⊕ PulseMatrix Deme)}
    {x₁ x₂ : FrequencyState Deme Locus Allele}
    (hmoments : historyEventPropagator (fun _ ↦ 4) first *ᵥ budgetMomentFeature (fun _ ↦ 4) x₁
      = historyEventPropagator (fun _ ↦ 4) second *ᵥ budgetMomentFeature (fun _ ↦ 4) x₂)
    (source target : Deme) (score : FullHaplotype Locus Allele → ℝ)
    (outcome : FullHaplotype Locus Allele → Bool) :
    expectedPortability (historyEventKernel ℓ₀ hap₀ first) x₁ source target score
        (fun hap ↦ if outcome hap then 1 else 0)
      = expectedPortability (historyEventKernel ℓ₀ hap₀ second) x₂ source target score
        (fun hap ↦ if outcome hap then 1 else 0)
    ∧ expectedAUCPortability (historyEventKernel ℓ₀ hap₀ first) x₁ source target score outcome
      = expectedAUCPortability (historyEventKernel ℓ₀ hap₀ second) x₂ source target score
        outcome :=
  ⟨expectedPortability_eq_of_moments_eq ℓ₀ hap₀ hmoments source target score _,
    expectedAUCPortability_eq_of_moments_eq ℓ₀ hap₀
      (historyEventMoments_eq_of_le ℓ₀ hap₀ (by norm_num) hmoments) source target score outcome⟩

/-- **The two expected-metric budget families are one family.**  Agreement of two histories at
every budget `4 (k + 1)`, the hypothesis of the expected squared-correlation law, is equivalent
to agreement at every budget `2 (k + 1)`, the hypothesis of the expected AUC law. -/
theorem moments_forall_four_iff_forall_two (ℓ₀ : Locus) (hap₀ : FullHaplotype Locus Allele)
    {first second : List ((NeutralRates Deme Locus Allele × ℝ≥0) ⊕ PulseMatrix Deme)}
    {x₁ x₂ : FrequencyState Deme Locus Allele} :
    (∀ k : ℕ, historyEventPropagator (fun _ ↦ 4 * (k + 1)) first
        *ᵥ budgetMomentFeature (fun _ ↦ 4 * (k + 1)) x₁
      = historyEventPropagator (fun _ ↦ 4 * (k + 1)) second
        *ᵥ budgetMomentFeature (fun _ ↦ 4 * (k + 1)) x₂)
    ↔ ∀ k : ℕ, historyEventPropagator (fun _ ↦ 2 * (k + 1)) first
        *ᵥ budgetMomentFeature (fun _ ↦ 2 * (k + 1)) x₁
      = historyEventPropagator (fun _ ↦ 2 * (k + 1)) second
        *ᵥ budgetMomentFeature (fun _ ↦ 2 * (k + 1)) x₂ :=
  ⟨fun hfour k ↦ historyEventMoments_eq_of_le ℓ₀ hap₀ (by omega) (hfour k),
    fun htwo k ↦ historyEventMoments_eq_of_le ℓ₀ hap₀ (by omega) (htwo (2 * k + 1))⟩

/-! ## The expected AUC -/

/-- **Expected AUC**: the population AUC of a deme, read as zero where it is undefined, averaged
under a kernel started at `x₀`. -/
def expectedAUC
    (κ : Kernel (FrequencyState Deme Locus Allele) (FrequencyState Deme Locus Allele))
    (x0 : FrequencyState Deme Locus Allele) (deme : Deme)
    (score : FullHaplotype Locus Allele → ℝ) (outcome : FullHaplotype Locus Allele → Bool) : ℝ :=
  ∫ y, ((stateLaw y deme).binaryAUC score outcome).getD 0 ∂(κ x0)

/-- **NOTE2 (15) for AUC under a Markov kernel.**  The expected AUC of a deme is the series of
expectations of `N (1 - D)ᵏ`.  No hypothesis on the score is needed: `0 ≤ N ≤ D ≤ 1` holds for
every score and every binary outcome. -/
theorem expectedAUC_eq_tsum
    (κ : Kernel (FrequencyState Deme Locus Allele) (FrequencyState Deme Locus Allele))
    [IsMarkovKernel κ] (x0 : FrequencyState Deme Locus Allele) (deme : Deme)
    (score : FullHaplotype Locus Allele → ℝ) (outcome : FullHaplotype Locus Allele → Bool) :
    expectedAUC κ x0 deme score outcome
      = ∑' k : ℕ, ∫ y, aucNumerator (stateLaw y deme) score outcome
          * (1 - aucDenominator (stateLaw y deme) outcome) ^ k ∂(κ x0) := by
  have hratio : (fun y : FrequencyState Deme Locus Allele ↦
      ((stateLaw y deme).binaryAUC score outcome).getD 0)
      = ratioOnDefined (fun z ↦ aucNumerator (stateLaw z deme) score outcome)
        (fun z ↦ aucDenominator (stateLaw z deme) outcome) :=
    funext fun y ↦ by
      rw [binaryAUC_eq_guardedRatio]
      exact getD_guardedRatio _ _ y
  have hnumerator : Measurable fun z : FrequencyState Deme Locus Allele ↦
      aucNumerator (stateLaw z deme) score outcome := by
    simpa only [eval_aucNumeratorPolynomial] using
      (continuous_eval_stateLaw deme (aucNumeratorPolynomial score outcome)).measurable
  have hdenominator : Measurable fun z : FrequencyState Deme Locus Allele ↦
      aucDenominator (stateLaw z deme) outcome := by
    simpa only [eval_aucDenominatorPolynomial] using
      (continuous_eval_stateLaw deme (aucDenominatorPolynomial outcome)).measurable
  rw [expectedAUC, hratio]
  exact integral_ratioOnDefined_eq_tsum (κ x0) _ _ hnumerator hdenominator
    (fun z ↦ aucNumerator_nonneg _ score outcome)
    (fun z ↦ aucNumerator_le_denominator _ score outcome)
    (fun z ↦ aucDenominator_le_one _ outcome)

/-- **The expected AUC through the propagated moments.**  The expected AUC of a deme is the series
over `k` of the coefficient vectors of `N (1 - D)ᵏ` dotted with the budget-`2 (k + 1)` propagated
moments.

Assumes: `∀ n, HasDualMoments κ n (M n)`. -/
theorem expectedAUC_eq_tsum_dotProduct (ℓ₀ : Locus)
    (κ : Kernel (FrequencyState Deme Locus Allele) (FrequencyState Deme Locus Allele))
    [IsMarkovKernel κ] (M : ∀ n : ℕ, BudgetMatrix Deme Locus Allele n)
    (hmoment : ∀ n : ℕ, HasDualMoments κ n (M n)) (x0 : FrequencyState Deme Locus Allele)
    (deme : Deme) (score : FullHaplotype Locus Allele → ℝ)
    (outcome : FullHaplotype Locus Allele → Bool) :
    expectedAUC κ x0 deme score outcome
      = ∑' k : ℕ, budgetCoefficients ℓ₀ (fun _ ↦ 2 * (k + 1))
          (demePolynomial deme
            (aucNumeratorPolynomial score outcome * (1 - aucDenominatorPolynomial outcome) ^ k))
        ⬝ᵥ (M (2 * (k + 1)) *ᵥ budgetMomentFeature (fun _ ↦ 2 * (k + 1)) x0) := by
  rw [expectedAUC_eq_tsum]
  refine tsum_congr fun k ↦ ?_
  simpa only [eval_aucTerm] using integral_eval_stateLaw_eq_dotProduct ℓ₀ (2 * (k + 1)) κ
    (M (2 * (k + 1))) (hmoment (2 * (k + 1))) deme _ (totalDegree_aucTerm_le score outcome k) x0

/-- **The expected AUC along a history of epochs, splits and pulses.**  It is the series over `k`
of the coefficient vectors of `N (1 - D)ᵏ` dotted with the chronological propagator applied to the
budget-`2 (k + 1)` configuration moments of the initial state. -/
theorem expectedAUC_historyEventKernel (ℓ₀ : Locus) (hap₀ : FullHaplotype Locus Allele)
    (events : List ((NeutralRates Deme Locus Allele × ℝ≥0) ⊕ PulseMatrix Deme))
    (x0 : FrequencyState Deme Locus Allele) (deme : Deme)
    (score : FullHaplotype Locus Allele → ℝ) (outcome : FullHaplotype Locus Allele → Bool) :
    expectedAUC (historyEventKernel ℓ₀ hap₀ events) x0 deme score outcome
      = ∑' k : ℕ, budgetCoefficients ℓ₀ (fun _ ↦ 2 * (k + 1))
          (demePolynomial deme
            (aucNumeratorPolynomial score outcome * (1 - aucDenominatorPolynomial outcome) ^ k))
        ⬝ᵥ (historyEventPropagator (fun _ ↦ 2 * (k + 1)) events
          *ᵥ budgetMomentFeature (fun _ ↦ 2 * (k + 1)) x0) := by
  haveI := isMarkovKernel_historyEventKernel ℓ₀ hap₀ events
  exact expectedAUC_eq_tsum_dotProduct ℓ₀ (historyEventKernel ℓ₀ hap₀ events)
    (fun n ↦ historyEventPropagator (fun _ ↦ n) events)
    (hasDualMoments_historyEventKernel ℓ₀ hap₀ events) x0 deme score outcome

/-- **The expected AUC along a time-varying rate history.** -/
theorem expectedAUC_rateHistoryKernel {rates : ℝ → NeutralRates Deme Locus Allele} {T : ℝ}
    (hT : 0 ≤ T) (hcontinuous : ∀ capacity : Locus → ℕ,
      ContinuousOn (fun t ↦ dualGenerator (rates t) capacity) (Set.Icc 0 T))
    (ℓ₀ : Locus) (hap₀ : FullHaplotype Locus Allele) (x0 : FrequencyState Deme Locus Allele)
    (deme : Deme) (score : FullHaplotype Locus Allele → ℝ)
    (outcome : FullHaplotype Locus Allele → Bool) :
    expectedAUC (rateHistoryKernel rates ℓ₀ hap₀ hT hcontinuous) x0 deme score outcome
      = ∑' k : ℕ, budgetCoefficients ℓ₀ (fun _ ↦ 2 * (k + 1))
          (demePolynomial deme
            (aucNumeratorPolynomial score outcome * (1 - aucDenominatorPolynomial outcome) ^ k))
        ⬝ᵥ (rateHistoryDualPropagator rates (fun _ ↦ 2 * (k + 1)) T
          *ᵥ budgetMomentFeature (fun _ ↦ 2 * (k + 1)) x0) := by
  haveI := isMarkovKernel_rateHistoryKernel hT hcontinuous ℓ₀ hap₀
  exact expectedAUC_eq_tsum_dotProduct ℓ₀ (rateHistoryKernel rates ℓ₀ hap₀ hT hcontinuous)
    (fun n ↦ rateHistoryDualPropagator rates (fun _ ↦ n) T)
    (hasDualMoments_rateHistoryKernel hT hcontinuous ℓ₀ hap₀) x0 deme score outcome

/-- **The expected AUC sees the history only through propagated moments.**  Two histories, from
two initial states, whose propagated configuration moments agree at every budget `2 (k + 1)`
have equal expected AUC for every score and binary outcome. -/
theorem expectedAUC_eq_of_moments_eq (ℓ₀ : Locus) (hap₀ : FullHaplotype Locus Allele)
    {first second : List ((NeutralRates Deme Locus Allele × ℝ≥0) ⊕ PulseMatrix Deme)}
    {x₁ x₂ : FrequencyState Deme Locus Allele}
    (hmoments : ∀ k : ℕ,
      historyEventPropagator (fun _ ↦ 2 * (k + 1)) first
          *ᵥ budgetMomentFeature (fun _ ↦ 2 * (k + 1)) x₁
        = historyEventPropagator (fun _ ↦ 2 * (k + 1)) second
          *ᵥ budgetMomentFeature (fun _ ↦ 2 * (k + 1)) x₂)
    (deme : Deme) (score : FullHaplotype Locus Allele → ℝ)
    (outcome : FullHaplotype Locus Allele → Bool) :
    expectedAUC (historyEventKernel ℓ₀ hap₀ first) x₁ deme score outcome
      = expectedAUC (historyEventKernel ℓ₀ hap₀ second) x₂ deme score outcome := by
  rw [expectedAUC_historyEventKernel, expectedAUC_historyEventKernel]
  exact tsum_congr fun k ↦ by rw [hmoments k]

/-- **One moment hypothesis fixes both expected metrics.**  Two histories whose propagated moments
agree at every budget `4 (k + 1)` have equal expected squared correlation of a score in the unit
interval against the indicator of a binary outcome, and equal expected AUC of that score for that
outcome. -/
theorem expectedSquaredCorrelation_and_expectedAUC_eq_of_moments_eq (ℓ₀ : Locus)
    (hap₀ : FullHaplotype Locus Allele)
    {first second : List ((NeutralRates Deme Locus Allele × ℝ≥0) ⊕ PulseMatrix Deme)}
    {x₁ x₂ : FrequencyState Deme Locus Allele}
    (hmoments : ∀ k : ℕ,
      historyEventPropagator (fun _ ↦ 4 * (k + 1)) first
          *ᵥ budgetMomentFeature (fun _ ↦ 4 * (k + 1)) x₁
        = historyEventPropagator (fun _ ↦ 4 * (k + 1)) second
          *ᵥ budgetMomentFeature (fun _ ↦ 4 * (k + 1)) x₂)
    (deme : Deme) (score : FullHaplotype Locus Allele → ℝ)
    (outcome : FullHaplotype Locus Allele → Bool)
    (hscore0 : ∀ hap, 0 ≤ score hap) (hscore1 : ∀ hap, score hap ≤ 1) :
    expectedSquaredCorrelation (historyEventKernel ℓ₀ hap₀ first) x₁ deme score
        (fun hap ↦ if outcome hap then 1 else 0)
      = expectedSquaredCorrelation (historyEventKernel ℓ₀ hap₀ second) x₂ deme score
        (fun hap ↦ if outcome hap then 1 else 0)
    ∧ expectedAUC (historyEventKernel ℓ₀ hap₀ first) x₁ deme score outcome
      = expectedAUC (historyEventKernel ℓ₀ hap₀ second) x₂ deme score outcome := by
  have hindicator : ∀ hap, 0 ≤ (if outcome hap then (1 : ℝ) else 0)
      ∧ (if outcome hap then (1 : ℝ) else 0) ≤ 1 := fun hap ↦ by
    by_cases hcase : outcome hap <;> simp [hcase]
  exact ⟨expectedSquaredCorrelation_eq_of_moments_eq ℓ₀ hap₀ hmoments deme score _ hscore0
      hscore1 (fun hap ↦ (hindicator hap).1) (fun hap ↦ (hindicator hap).2),
    expectedAUC_eq_of_moments_eq ℓ₀ hap₀
      ((moments_forall_four_iff_forall_two ℓ₀ hap₀).mp hmoments) deme score outcome⟩

end

end Descent.Portability.EndToEndDiscriminationLaw
