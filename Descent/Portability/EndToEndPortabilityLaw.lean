/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.NeutralPulseHistoryKernel
import Descent.Portability.NeutralRateHistoryKernel
import Descent.Portability.ReplicaMetricInstances

assert_below Descent.Decision Descent.Program

/-!
# The end-to-end law of polygenic-score portability

This module states and proves one law from demography to the portability of a polygenic score,
with nothing assumed in between.

The input.  A neutral demographic history runs from a frequency state `x₀`: a list of epochs,
splits and admixture pulses (`NeutralPulseHistoryKernel.historyEventKernel`), or a rate path whose
dual generator is continuous on the horizon (`NeutralRateHistoryKernel.rateHistoryKernel`).  Both
are Markov process laws on multi-deme haplotype frequencies built from the neutral diffusion
(NOTE1 §4.2a).  A score `S` and an outcome `Y` are functions of the haplotype, for instance fixed
effects on `L` loci rescaled into the unit interval.  In deme `j` the population squared
correlation of NOTE2 (21) is the guarded ratio `N_j / D_j` of the corpus metrics
`ReplicaMetricInstances.correlationNumerator` `N_j = 16 C_SY²` and
`ReplicaMetricInstances.correlationDenominator` `D_j = 16 V_S V_Y` of the deme's haplotype law.

The law.  `N_j` and `D_j` are polynomials of total degree at most four in the haplotype frequencies
of deme `j` (`numeratorPolynomial`, `denominatorPolynomial`,
`polynomialFunction_numeratorPolynomial`, `totalDegree_numeratorPolynomial_le`), so every monomial
is a configuration of the budget-4 space
(`withinBudget_of_totalDegree_le`).  Under any kernel whose configuration moments obey NOTE1 (20),
a polynomial of the budget space integrates to its coefficient vector dotted with the propagated
moments (`integral_polynomial_eq_dotProduct`).  So the expected numerators and denominators are
`c ⬝ (U · H₄(x₀))`, with the explicit coefficient vectors `budgetCoefficients` and the history
propagator `U` (`integral_correlationNumerator_historyEventKernel`,
`integral_correlationDenominator_historyEventKernel`, and the `rateHistoryKernel` forms).  The
portability of expected accuracies `P̄ = (E N_t · E D_s) / (E D_t · E N_s)` (`expectedPortability`)
is the rational function `momentPortability` of `U · H₄(x₀)`
(`expectedPortability_historyEventKernel`, `expectedPortability_rateHistoryKernel`).  NOTE2 (27)
keeps source and target joint; its ratio of joint expectations `E[N_t D_s] / E[D_t N_s]`
(`expectedJointPortability`) is the rational function `jointMomentPortability` of the budget-8
moments `U · H₈(x₀)` (`expectedJointPortability_historyEventKernel`).

Consequences.  Portability depends on the demographic history and the initial state only through
finitely many propagated configuration moments: two histories whose propagated budget-4 moments
agree have equal portability (`expectedPortability_eq_of_moments_eq`), and likewise at budget 8
for the joint form (`expectedJointPortability_eq_of_moments_eq`).

Significance.  The demography enters as a process law, not as a summary statistic; the metrics are
the corpus population metrics, not restatements; and the passage from one to the other is a
finite matrix computation, the exponentials and pulse substitution kernels of the dual chain
applied to the initial moments, followed by one rational function with written-out coefficients.

Scope.  The portability here is formed from expectations of the numerator and denominator
polynomials, one of the four distinct queries NOTE2 §6.2 separates.  The expected squared
correlation `E[N/D]` and the mean of (27) are not rational in finitely many moments; NOTE2 (15)
expands them as series of higher-budget moments, which this module does not state.  One chromosome
is sampled per individual; diploid genotypes, integrable rate paths and the Lipschitz dependence
on the rate path are not covered here.

## Empirical status

None.  The bodies here are polynomial identities and integrals of polynomials against Markov
kernels whose moments are matrix computations of supplied rates, so no measurement can bear on
them.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.EndToEndPortabilityLaw

open MeasureTheory ProbabilityTheory MvPolynomial Descent.Coalescent PartialHaplotypeCarrier
  PartialHaplotypeDualGenerator PartialHaplotypeDualSemigroup NeutralFellerGenerator
  NeutralPolynomialSemigroup PartialHaplotypeMicroscopicApproximation PartialHaplotypePulseKernel
  NeutralPulseHistoryKernel NeutralRateHistoryRealization NeutralRateHistoryKernel
  ReplicaMetricInstances
open scoped Matrix NNReal

noncomputable section

variable {Deme Locus : Type*} {Allele : Locus → Type*}
variable [Fintype Deme] [DecidableEq Deme] [Fintype Locus] [DecidableEq Locus]
  [∀ ℓ, Fintype (Allele ℓ)] [∀ ℓ, DecidableEq (Allele ℓ)]

/-! ## Population metrics as frequency polynomials -/

/-- A polynomial in the haplotype frequencies of one deme, read as a frequency polynomial. -/
def demePolynomial (deme : Deme) (p : MvPolynomial (FullHaplotype Locus Allele) ℝ) :
    FrequencyPolynomial Deme Locus Allele :=
  rename (fun hap ↦ (deme, hap)) p

/-- A deme polynomial evaluates at a state to the polynomial at the deme's haplotype law. -/
theorem eval_demePolynomial (deme : Deme) (p : MvPolynomial (FullHaplotype Locus Allele) ℝ)
    (x : FrequencyState Deme Locus Allele) :
    eval x.1 (demePolynomial deme p) = eval (stateLaw x deme).mass p := by
  rw [demePolynomial, eval_rename]
  rfl

/-- The correlation numerator `N = 16 C_SY²` of NOTE2 (21) in one deme, as a frequency
polynomial. -/
def numeratorPolynomial (deme : Deme) (score outcome : FullHaplotype Locus Allele → ℝ) :
    FrequencyPolynomial Deme Locus Allele :=
  demePolynomial deme (correlationNumeratorPolynomial score outcome)

/-- The correlation denominator `D = 16 V_S V_Y` of NOTE2 (21) in one deme, as a frequency
polynomial. -/
def denominatorPolynomial (deme : Deme) (score outcome : FullHaplotype Locus Allele → ℝ) :
    FrequencyPolynomial Deme Locus Allele :=
  demePolynomial deme (correlationDenominatorPolynomial score outcome)

/-- At a state, the numerator polynomial is the corpus correlation numerator of the deme's
haplotype law. -/
theorem polynomialFunction_numeratorPolynomial (deme : Deme)
    (score outcome : FullHaplotype Locus Allele → ℝ) (y : FrequencyState Deme Locus Allele) :
    polynomialFunction (numeratorPolynomial deme score outcome) y
      = correlationNumerator (stateLaw y deme) score outcome := by
  rw [polynomialFunction_apply, numeratorPolynomial, eval_demePolynomial,
    eval_correlationNumeratorPolynomial]

/-- At a state, the denominator polynomial is the corpus correlation denominator of the deme's
haplotype law. -/
theorem polynomialFunction_denominatorPolynomial (deme : Deme)
    (score outcome : FullHaplotype Locus Allele → ℝ) (y : FrequencyState Deme Locus Allele) :
    polynomialFunction (denominatorPolynomial deme score outcome) y
      = correlationDenominator (stateLaw y deme) score outcome := by
  rw [polynomialFunction_apply, denominatorPolynomial, eval_demePolynomial,
    eval_correlationDenominatorPolynomial]

/-- The numerator polynomial has total degree at most four. -/
theorem totalDegree_numeratorPolynomial_le (deme : Deme)
    (score outcome : FullHaplotype Locus Allele → ℝ) :
    (numeratorPolynomial deme score outcome).totalDegree ≤ 4 :=
  (totalDegree_rename_le _ _).trans (totalDegree_correlationNumeratorPolynomial_le score outcome)

/-- The denominator polynomial has total degree at most four. -/
theorem totalDegree_denominatorPolynomial_le (deme : Deme)
    (score outcome : FullHaplotype Locus Allele → ℝ) :
    (denominatorPolynomial deme score outcome).totalDegree ≤ 4 :=
  (totalDegree_rename_le _ _).trans
    (totalDegree_correlationDenominatorPolynomial_le score outcome)

/-- Every monomial of a frequency polynomial of total degree at most `n` is a configuration of the
budget in which every locus may carry `n` copies. -/
theorem withinBudget_of_totalDegree_le (ℓ₀ : Locus) {n : ℕ}
    (p : FrequencyPolynomial Deme Locus Allele) (hp : p.totalDegree ≤ n) :
    ∀ β ∈ p.support, WithinBudget (fun _ ↦ n) (monomialConfiguration ℓ₀ β) := by
  intro β hβ ℓ
  have hcard : Multiset.card (monomialConfiguration ℓ₀ β) = β.sum fun _ e ↦ e := by
    rw [monomialConfiguration, Multiset.card_sum]
    simp only [Multiset.card_replicate]
    symm
    exact Finset.sum_subset (Finset.subset_univ _) fun c _ hc ↦
      Classical.byContradiction fun hne ↦ hc (Finsupp.mem_support_iff.mpr hne)
  have hdegree : Multiset.card (monomialConfiguration ℓ₀ β) ≤ n := by
    rw [hcard]
    exact (le_totalDegree hβ).trans hp
  exact (Multiset.countP_le_card _ _).trans hdegree

/-! ## Integrating polynomials against a kernel with the dual moments -/

/-- The coefficient vector of a frequency polynomial over the configurations of a budget. -/
def budgetCoefficients (ℓ₀ : Locus) (capacity : Locus → ℕ)
    (p : FrequencyPolynomial Deme Locus Allele) :
    BudgetConfiguration Deme Locus Allele capacity → ℝ :=
  fun η ↦ ∑ β ∈ p.support, if monomialConfiguration ℓ₀ β = η.1 then coeff β p else 0

/-- **Polynomials integrate through the moments.**  Under a Markov kernel whose configuration
moments of a budget are a matrix applied to the initial moments, a polynomial whose monomials lie
in the budget integrates to its coefficient vector dotted with the propagated moments. -/
theorem integral_polynomial_eq_dotProduct (ℓ₀ : Locus) (capacity : Locus → ℕ)
    (κ : Kernel (FrequencyState Deme Locus Allele) (FrequencyState Deme Locus Allele))
    [IsMarkovKernel κ]
    (M : Matrix (BudgetConfiguration Deme Locus Allele capacity)
      (BudgetConfiguration Deme Locus Allele capacity) ℝ)
    (hmoment : ∀ (x : FrequencyState Deme Locus Allele)
      (ξ : BudgetConfiguration Deme Locus Allele capacity),
      ∫ y, polynomialFunction (momentPolynomial ξ.1) y ∂(κ x)
        = (M *ᵥ budgetMomentFeature capacity x) ξ)
    (p : FrequencyPolynomial Deme Locus Allele)
    (hp : ∀ β ∈ p.support, WithinBudget capacity (monomialConfiguration ℓ₀ β))
    (x0 : FrequencyState Deme Locus Allele) :
    ∫ y, polynomialFunction p y ∂(κ x0)
      = budgetCoefficients ℓ₀ capacity p ⬝ᵥ (M *ᵥ budgetMomentFeature capacity x0) := by
  have hpoint : ∀ y : FrequencyState Deme Locus Allele, polynomialFunction p y
      = ∑ η, budgetCoefficients ℓ₀ capacity p η * polynomialFunction (momentPolynomial η.1) y :=
    fun y ↦ NeutralPolynomialSemigroup.eval_eq_dotProduct ℓ₀ capacity p hp y
  have hint : ∀ η : BudgetConfiguration Deme Locus Allele capacity,
      Integrable (fun y ↦ polynomialFunction (momentPolynomial η.1) y) (κ x0) := fun η ↦
    (BoundedContinuousFunction.mkOfCompact
      (polynomialFunction (momentPolynomial η.1))).integrable _
  simp only [hpoint]
  rw [integral_finset_sum Finset.univ fun η _ ↦
    (hint η).const_mul (budgetCoefficients ℓ₀ capacity p η)]
  simp only [integral_const_mul, hmoment]
  rfl

/-! ## The law along a history of epochs, splits and pulses -/

/-- **Expected squared-correlation numerator along a history.**  The expected correlation
numerator of a deme under the history kernel is the coefficient vector of the numerator
polynomial dotted with the chronological propagator applied to the budget-4 moments of `x₀`. -/
theorem integral_correlationNumerator_historyEventKernel (ℓ₀ : Locus)
    (hap₀ : FullHaplotype Locus Allele)
    (events : List ((NeutralRates Deme Locus Allele × ℝ≥0) ⊕ PulseMatrix Deme))
    (x0 : FrequencyState Deme Locus Allele) (deme : Deme)
    (score outcome : FullHaplotype Locus Allele → ℝ) :
    ∫ y, correlationNumerator (stateLaw y deme) score outcome
        ∂(historyEventKernel ℓ₀ hap₀ events x0)
      = budgetCoefficients ℓ₀ (fun _ ↦ 4) (numeratorPolynomial deme score outcome)
        ⬝ᵥ (historyEventPropagator (fun _ ↦ 4) events
          *ᵥ budgetMomentFeature (fun _ ↦ 4) x0) := by
  haveI := isMarkovKernel_historyEventKernel ℓ₀ hap₀ events
  have h := integral_polynomial_eq_dotProduct ℓ₀ (fun _ ↦ 4)
    (historyEventKernel ℓ₀ hap₀ events) (historyEventPropagator (fun _ ↦ 4) events)
    (integral_momentPolynomial_historyEventKernel ℓ₀ hap₀ (fun _ ↦ 4) events)
    (numeratorPolynomial deme score outcome)
    (withinBudget_of_totalDegree_le ℓ₀ _ (totalDegree_numeratorPolynomial_le deme score outcome))
    x0
  simp only [polynomialFunction_numeratorPolynomial] at h
  exact h

/-- **Expected squared-correlation denominator along a history.** -/
theorem integral_correlationDenominator_historyEventKernel (ℓ₀ : Locus)
    (hap₀ : FullHaplotype Locus Allele)
    (events : List ((NeutralRates Deme Locus Allele × ℝ≥0) ⊕ PulseMatrix Deme))
    (x0 : FrequencyState Deme Locus Allele) (deme : Deme)
    (score outcome : FullHaplotype Locus Allele → ℝ) :
    ∫ y, correlationDenominator (stateLaw y deme) score outcome
        ∂(historyEventKernel ℓ₀ hap₀ events x0)
      = budgetCoefficients ℓ₀ (fun _ ↦ 4) (denominatorPolynomial deme score outcome)
        ⬝ᵥ (historyEventPropagator (fun _ ↦ 4) events
          *ᵥ budgetMomentFeature (fun _ ↦ 4) x0) := by
  haveI := isMarkovKernel_historyEventKernel ℓ₀ hap₀ events
  have h := integral_polynomial_eq_dotProduct ℓ₀ (fun _ ↦ 4)
    (historyEventKernel ℓ₀ hap₀ events) (historyEventPropagator (fun _ ↦ 4) events)
    (integral_momentPolynomial_historyEventKernel ℓ₀ hap₀ (fun _ ↦ 4) events)
    (denominatorPolynomial deme score outcome)
    (withinBudget_of_totalDegree_le ℓ₀ _
      (totalDegree_denominatorPolynomial_le deme score outcome))
    x0
  simp only [polynomialFunction_denominatorPolynomial] at h
  exact h

/-- **Expected portability**: the target-over-source ratio `(E N_t · E D_s) / (E D_t · E N_s)` of
expected squared-correlation numerators and denominators under a kernel started at `x₀`. -/
def expectedPortability
    (κ : Kernel (FrequencyState Deme Locus Allele) (FrequencyState Deme Locus Allele))
    (x0 : FrequencyState Deme Locus Allele) (source target : Deme)
    (score outcome : FullHaplotype Locus Allele → ℝ) : ℝ :=
  ((∫ y, correlationNumerator (stateLaw y target) score outcome ∂(κ x0))
      * ∫ y, correlationDenominator (stateLaw y source) score outcome ∂(κ x0))
    / ((∫ y, correlationDenominator (stateLaw y target) score outcome ∂(κ x0))
      * ∫ y, correlationNumerator (stateLaw y source) score outcome ∂(κ x0))

/-- **The rational portability function** of a budget-4 moment vector, with written-out
coefficients. -/
def momentPortability (ℓ₀ : Locus) (source target : Deme)
    (score outcome : FullHaplotype Locus Allele → ℝ)
    (v : BudgetConfiguration Deme Locus Allele (fun _ ↦ 4) → ℝ) : ℝ :=
  ((budgetCoefficients ℓ₀ (fun _ ↦ 4) (numeratorPolynomial target score outcome) ⬝ᵥ v)
      * (budgetCoefficients ℓ₀ (fun _ ↦ 4) (denominatorPolynomial source score outcome) ⬝ᵥ v))
    / ((budgetCoefficients ℓ₀ (fun _ ↦ 4) (denominatorPolynomial target score outcome) ⬝ᵥ v)
      * (budgetCoefficients ℓ₀ (fun _ ↦ 4) (numeratorPolynomial source score outcome) ⬝ᵥ v))

/-- **The end-to-end portability law along a history of epochs, splits and pulses.**  The
expected portability of a score is the rational function `momentPortability` of the chronological
propagator applied to the budget-4 configuration moments of the initial state. -/
theorem expectedPortability_historyEventKernel (ℓ₀ : Locus) (hap₀ : FullHaplotype Locus Allele)
    (events : List ((NeutralRates Deme Locus Allele × ℝ≥0) ⊕ PulseMatrix Deme))
    (x0 : FrequencyState Deme Locus Allele) (source target : Deme)
    (score outcome : FullHaplotype Locus Allele → ℝ) :
    expectedPortability (historyEventKernel ℓ₀ hap₀ events) x0 source target score outcome
      = momentPortability ℓ₀ source target score outcome
          (historyEventPropagator (fun _ ↦ 4) events *ᵥ budgetMomentFeature (fun _ ↦ 4) x0) := by
  rw [expectedPortability, integral_correlationNumerator_historyEventKernel,
    integral_correlationNumerator_historyEventKernel,
    integral_correlationDenominator_historyEventKernel,
    integral_correlationDenominator_historyEventKernel]
  rfl

/-- **Portability sees the history only through finitely many moments.**  Two histories, from two
initial states, whose propagated budget-4 configuration moments agree have equal expected
portability for every score, outcome, source and target. -/
theorem expectedPortability_eq_of_moments_eq (ℓ₀ : Locus) (hap₀ : FullHaplotype Locus Allele)
    {first second : List ((NeutralRates Deme Locus Allele × ℝ≥0) ⊕ PulseMatrix Deme)}
    {x₁ x₂ : FrequencyState Deme Locus Allele}
    (hmoments : historyEventPropagator (fun _ ↦ 4) first *ᵥ budgetMomentFeature (fun _ ↦ 4) x₁
      = historyEventPropagator (fun _ ↦ 4) second *ᵥ budgetMomentFeature (fun _ ↦ 4) x₂)
    (source target : Deme) (score outcome : FullHaplotype Locus Allele → ℝ) :
    expectedPortability (historyEventKernel ℓ₀ hap₀ first) x₁ source target score outcome
      = expectedPortability (historyEventKernel ℓ₀ hap₀ second) x₂ source target score
          outcome := by
  rw [expectedPortability_historyEventKernel, expectedPortability_historyEventKernel, hmoments]

/-! ## The joint form of NOTE2 (27) -/

/-- The joint numerator `N_t D_s` of NOTE2 (27), as a frequency polynomial. -/
def jointNumeratorPolynomial (source target : Deme)
    (score outcome : FullHaplotype Locus Allele → ℝ) : FrequencyPolynomial Deme Locus Allele :=
  numeratorPolynomial target score outcome * denominatorPolynomial source score outcome

/-- The joint denominator `D_t N_s` of NOTE2 (27), as a frequency polynomial. -/
def jointDenominatorPolynomial (source target : Deme)
    (score outcome : FullHaplotype Locus Allele → ℝ) : FrequencyPolynomial Deme Locus Allele :=
  denominatorPolynomial target score outcome * numeratorPolynomial source score outcome

/-- At a state, the joint numerator polynomial is `N_t D_s`. -/
theorem polynomialFunction_jointNumeratorPolynomial (source target : Deme)
    (score outcome : FullHaplotype Locus Allele → ℝ) (y : FrequencyState Deme Locus Allele) :
    polynomialFunction (jointNumeratorPolynomial source target score outcome) y
      = correlationNumerator (stateLaw y target) score outcome
        * correlationDenominator (stateLaw y source) score outcome := by
  rw [polynomialFunction_apply, jointNumeratorPolynomial, map_mul, ← polynomialFunction_apply,
    ← polynomialFunction_apply, polynomialFunction_numeratorPolynomial,
    polynomialFunction_denominatorPolynomial]

/-- At a state, the joint denominator polynomial is `D_t N_s`. -/
theorem polynomialFunction_jointDenominatorPolynomial (source target : Deme)
    (score outcome : FullHaplotype Locus Allele → ℝ) (y : FrequencyState Deme Locus Allele) :
    polynomialFunction (jointDenominatorPolynomial source target score outcome) y
      = correlationDenominator (stateLaw y target) score outcome
        * correlationNumerator (stateLaw y source) score outcome := by
  rw [polynomialFunction_apply, jointDenominatorPolynomial, map_mul, ← polynomialFunction_apply,
    ← polynomialFunction_apply, polynomialFunction_denominatorPolynomial,
    polynomialFunction_numeratorPolynomial]

/-- The joint numerator polynomial has total degree at most eight. -/
theorem totalDegree_jointNumeratorPolynomial_le (source target : Deme)
    (score outcome : FullHaplotype Locus Allele → ℝ) :
    (jointNumeratorPolynomial source target score outcome).totalDegree ≤ 8 := by
  have h1 := totalDegree_numeratorPolynomial_le target score outcome
  have h2 := totalDegree_denominatorPolynomial_le source score outcome
  exact (totalDegree_mul _ _).trans (by omega)

/-- The joint denominator polynomial has total degree at most eight. -/
theorem totalDegree_jointDenominatorPolynomial_le (source target : Deme)
    (score outcome : FullHaplotype Locus Allele → ℝ) :
    (jointDenominatorPolynomial source target score outcome).totalDegree ≤ 8 := by
  have h1 := totalDegree_denominatorPolynomial_le target score outcome
  have h2 := totalDegree_numeratorPolynomial_le source score outcome
  exact (totalDegree_mul _ _).trans (by omega)

/-- **Expected joint portability**: the ratio `E[N_t D_s] / E[D_t N_s]` of joint expectations of
NOTE2 (27) under a kernel started at `x₀`. -/
def expectedJointPortability
    (κ : Kernel (FrequencyState Deme Locus Allele) (FrequencyState Deme Locus Allele))
    (x0 : FrequencyState Deme Locus Allele) (source target : Deme)
    (score outcome : FullHaplotype Locus Allele → ℝ) : ℝ :=
  (∫ y, correlationNumerator (stateLaw y target) score outcome
      * correlationDenominator (stateLaw y source) score outcome ∂(κ x0))
    / ∫ y, correlationDenominator (stateLaw y target) score outcome
      * correlationNumerator (stateLaw y source) score outcome ∂(κ x0)

/-- **The rational joint portability function** of a budget-8 moment vector. -/
def jointMomentPortability (ℓ₀ : Locus) (source target : Deme)
    (score outcome : FullHaplotype Locus Allele → ℝ)
    (v : BudgetConfiguration Deme Locus Allele (fun _ ↦ 8) → ℝ) : ℝ :=
  (budgetCoefficients ℓ₀ (fun _ ↦ 8) (jointNumeratorPolynomial source target score outcome) ⬝ᵥ v)
    / (budgetCoefficients ℓ₀ (fun _ ↦ 8) (jointDenominatorPolynomial source target score outcome)
      ⬝ᵥ v)

/-- **The end-to-end joint portability law along a history.**  The ratio of joint expectations of
NOTE2 (27) is the rational function `jointMomentPortability` of the chronological propagator
applied to the budget-8 configuration moments of the initial state. -/
theorem expectedJointPortability_historyEventKernel (ℓ₀ : Locus)
    (hap₀ : FullHaplotype Locus Allele)
    (events : List ((NeutralRates Deme Locus Allele × ℝ≥0) ⊕ PulseMatrix Deme))
    (x0 : FrequencyState Deme Locus Allele) (source target : Deme)
    (score outcome : FullHaplotype Locus Allele → ℝ) :
    expectedJointPortability (historyEventKernel ℓ₀ hap₀ events) x0 source target score outcome
      = jointMomentPortability ℓ₀ source target score outcome
          (historyEventPropagator (fun _ ↦ 8) events *ᵥ budgetMomentFeature (fun _ ↦ 8) x0) := by
  haveI := isMarkovKernel_historyEventKernel ℓ₀ hap₀ events
  have hnumerator := integral_polynomial_eq_dotProduct ℓ₀ (fun _ ↦ 8)
    (historyEventKernel ℓ₀ hap₀ events) (historyEventPropagator (fun _ ↦ 8) events)
    (integral_momentPolynomial_historyEventKernel ℓ₀ hap₀ (fun _ ↦ 8) events)
    (jointNumeratorPolynomial source target score outcome)
    (withinBudget_of_totalDegree_le ℓ₀ _
      (totalDegree_jointNumeratorPolynomial_le source target score outcome)) x0
  have hdenominator := integral_polynomial_eq_dotProduct ℓ₀ (fun _ ↦ 8)
    (historyEventKernel ℓ₀ hap₀ events) (historyEventPropagator (fun _ ↦ 8) events)
    (integral_momentPolynomial_historyEventKernel ℓ₀ hap₀ (fun _ ↦ 8) events)
    (jointDenominatorPolynomial source target score outcome)
    (withinBudget_of_totalDegree_le ℓ₀ _
      (totalDegree_jointDenominatorPolynomial_le source target score outcome)) x0
  simp only [polynomialFunction_jointNumeratorPolynomial] at hnumerator
  simp only [polynomialFunction_jointDenominatorPolynomial] at hdenominator
  rw [expectedJointPortability, hnumerator, hdenominator]
  rfl

/-- **Joint portability sees the history only through finitely many moments.** -/
theorem expectedJointPortability_eq_of_moments_eq (ℓ₀ : Locus)
    (hap₀ : FullHaplotype Locus Allele)
    {first second : List ((NeutralRates Deme Locus Allele × ℝ≥0) ⊕ PulseMatrix Deme)}
    {x₁ x₂ : FrequencyState Deme Locus Allele}
    (hmoments : historyEventPropagator (fun _ ↦ 8) first *ᵥ budgetMomentFeature (fun _ ↦ 8) x₁
      = historyEventPropagator (fun _ ↦ 8) second *ᵥ budgetMomentFeature (fun _ ↦ 8) x₂)
    (source target : Deme) (score outcome : FullHaplotype Locus Allele → ℝ) :
    expectedJointPortability (historyEventKernel ℓ₀ hap₀ first) x₁ source target score outcome
      = expectedJointPortability (historyEventKernel ℓ₀ hap₀ second) x₂ source target score
          outcome := by
  rw [expectedJointPortability_historyEventKernel, expectedJointPortability_historyEventKernel,
    hmoments]

/-! ## The law along a time-varying rate history -/

/-- **Expected squared-correlation numerator along a rate history.** -/
theorem integral_correlationNumerator_rateHistoryKernel
    {rates : ℝ → NeutralRates Deme Locus Allele} {T : ℝ} (hT : 0 ≤ T)
    (hcontinuous : ∀ capacity : Locus → ℕ,
      ContinuousOn (fun t ↦ dualGenerator (rates t) capacity) (Set.Icc 0 T))
    (ℓ₀ : Locus) (hap₀ : FullHaplotype Locus Allele) (x0 : FrequencyState Deme Locus Allele)
    (deme : Deme) (score outcome : FullHaplotype Locus Allele → ℝ) :
    ∫ y, correlationNumerator (stateLaw y deme) score outcome
        ∂(rateHistoryKernel rates ℓ₀ hap₀ hT hcontinuous x0)
      = budgetCoefficients ℓ₀ (fun _ ↦ 4) (numeratorPolynomial deme score outcome)
        ⬝ᵥ (rateHistoryDualPropagator rates (fun _ ↦ 4) T
          *ᵥ budgetMomentFeature (fun _ ↦ 4) x0) := by
  haveI := isMarkovKernel_rateHistoryKernel hT hcontinuous ℓ₀ hap₀
  have h := integral_polynomial_eq_dotProduct ℓ₀ (fun _ ↦ 4)
    (rateHistoryKernel rates ℓ₀ hap₀ hT hcontinuous) (rateHistoryDualPropagator rates (fun _ ↦ 4) T)
    (integral_momentPolynomial_rateHistoryKernel hT hcontinuous ℓ₀ hap₀ (fun _ ↦ 4))
    (numeratorPolynomial deme score outcome)
    (withinBudget_of_totalDegree_le ℓ₀ _ (totalDegree_numeratorPolynomial_le deme score outcome))
    x0
  simp only [polynomialFunction_numeratorPolynomial] at h
  exact h

/-- **Expected squared-correlation denominator along a rate history.** -/
theorem integral_correlationDenominator_rateHistoryKernel
    {rates : ℝ → NeutralRates Deme Locus Allele} {T : ℝ} (hT : 0 ≤ T)
    (hcontinuous : ∀ capacity : Locus → ℕ,
      ContinuousOn (fun t ↦ dualGenerator (rates t) capacity) (Set.Icc 0 T))
    (ℓ₀ : Locus) (hap₀ : FullHaplotype Locus Allele) (x0 : FrequencyState Deme Locus Allele)
    (deme : Deme) (score outcome : FullHaplotype Locus Allele → ℝ) :
    ∫ y, correlationDenominator (stateLaw y deme) score outcome
        ∂(rateHistoryKernel rates ℓ₀ hap₀ hT hcontinuous x0)
      = budgetCoefficients ℓ₀ (fun _ ↦ 4) (denominatorPolynomial deme score outcome)
        ⬝ᵥ (rateHistoryDualPropagator rates (fun _ ↦ 4) T
          *ᵥ budgetMomentFeature (fun _ ↦ 4) x0) := by
  haveI := isMarkovKernel_rateHistoryKernel hT hcontinuous ℓ₀ hap₀
  have h := integral_polynomial_eq_dotProduct ℓ₀ (fun _ ↦ 4)
    (rateHistoryKernel rates ℓ₀ hap₀ hT hcontinuous) (rateHistoryDualPropagator rates (fun _ ↦ 4) T)
    (integral_momentPolynomial_rateHistoryKernel hT hcontinuous ℓ₀ hap₀ (fun _ ↦ 4))
    (denominatorPolynomial deme score outcome)
    (withinBudget_of_totalDegree_le ℓ₀ _
      (totalDegree_denominatorPolynomial_le deme score outcome))
    x0
  simp only [polynomialFunction_denominatorPolynomial] at h
  exact h

/-- **The end-to-end portability law along a time-varying rate history.**  The expected
portability of a score is the rational function `momentPortability` of the propagator of the rate
history applied to the budget-4 configuration moments of the initial state. -/
theorem expectedPortability_rateHistoryKernel {rates : ℝ → NeutralRates Deme Locus Allele}
    {T : ℝ} (hT : 0 ≤ T)
    (hcontinuous : ∀ capacity : Locus → ℕ,
      ContinuousOn (fun t ↦ dualGenerator (rates t) capacity) (Set.Icc 0 T))
    (ℓ₀ : Locus) (hap₀ : FullHaplotype Locus Allele) (x0 : FrequencyState Deme Locus Allele)
    (source target : Deme) (score outcome : FullHaplotype Locus Allele → ℝ) :
    expectedPortability (rateHistoryKernel rates ℓ₀ hap₀ hT hcontinuous) x0 source target score
        outcome
      = momentPortability ℓ₀ source target score outcome
          (rateHistoryDualPropagator rates (fun _ ↦ 4) T
            *ᵥ budgetMomentFeature (fun _ ↦ 4) x0) := by
  rw [expectedPortability, integral_correlationNumerator_rateHistoryKernel,
    integral_correlationNumerator_rateHistoryKernel,
    integral_correlationDenominator_rateHistoryKernel,
    integral_correlationDenominator_rateHistoryKernel]
  rfl

end

end Descent.Portability.EndToEndPortabilityLaw
