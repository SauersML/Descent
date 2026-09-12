/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.SelectionHistoryMoments
import Descent.Portability.EndToEndPortabilityLaw
import Descent.Portability.PortabilityMetricCompilation

assert_below Descent.Decision Descent.Program

/-!
# The end-to-end portability law under selection along a demographic history

`EndToEndPortabilityLaw` computes the expected squared-correlation numerators and denominators of a
score, and their portability, along a neutral history of epochs, splits and admixture pulses: they
are coefficient vectors dotted with the chronological propagator applied to the budget-4 moments of
the initial state. This module carries haploid selection at one locus along the same histories and
measures how far it moves those quantities.

The selected history. `SelectedOnHistory` asks of a list of expectation families over per-deme
haplotype laws, one family per event, what a selected process run through the events satisfies.
During an epoch the expected budget-respecting configuration moments are continuous and obey the
forward moment equation with selection of `SelectionHistoryMoments`, and the next family starts
where the epoch ends. Across a split or a pulse the next family starts from the pulsed moments,
which `PartialHaplotypePulseKernel.pulseKernel_mulVec_expectedMoment` computes exactly.

The moment error bar. An epoch of length `d` moves the moments from the neutral epoch propagator
by at most `B σ d` (`SelectionHistoryMoments.norm_expectedMomentVector_sub_propagator_le`), a
pulse moves them by nothing, and every later propagator is substochastic
(`norm_sub_mulVec_le`). So along a history with total epoch duration `T` (`epochDuration`) the
selected moments end within `B σ T` in sup norm of the neutral chronological propagator applied to
the initial moments (`norm_selectedHistory_sub_propagator_le`), with `B = Σ_ℓ n_ℓ`.

The metrics. Under any expectation functional over per-deme laws, a polynomial whose monomials fit
a budget has expectation equal to its budget coefficients dotted with the expected moments
(`expectation_polynomial_eq_dotProduct`, through the state `lawState` of the laws). Starting from
the moments of a state `x₀`, such a polynomial differs from its integral under the neutral history
kernel by at most `‖c‖₁ B σ T`, with `c` its coefficient vector
(`abs_selectedPolynomial_sub_neutral_le`). For the correlation numerator and denominator of a deme,
of degree four, this is `‖c‖₁ 4 |L| σ T` with `|L|` the number of loci
(`abs_selectedNumerator_sub_neutral_le`, `abs_selectedDenominator_sub_neutral_le`). The
portability of expected accuracies of the selected history (`selectedPortability`) is the rational
function `momentPortability` of the selected moments (`selectedPortability_eq_momentPortability`).
Where the target denominator and the source numerator are at least `δ` under both laws it differs
from the neutral end-to-end portability by at most `4 ‖a‖₁ ‖b‖₁ ‖c‖₁ ‖d‖₁ / δ⁴ · 4 |L| σ T`
(`abs_selectedPortability_sub_neutral_le`). The analysis of the cross ratio is
`PortabilityMetricCompilation.abs_crossRatio_sub_le` on the unit box, which holds both moment
vectors.

Significance. `SelectionPortabilityBound` bounds weak selection inside one panmictic window, with
source and target two times of one population. Here source and target are demes of an arbitrary
history of epochs, splits and pulses, fitness may differ between demes, and the bound is additive
over epochs.

Nonclosure. Under selection the budget-4 moments do not determine their own future, so no finite
matrix law replaces the neutral one. One deme at one biallelic locus is enough. The allele
frequencies `{0, 4, 8, 16, 17}/18` and `{1, 2, 10, 14, 18}/18` have equal power sums through the
fourth power and different fifth power sums (`sum_frequencies_pow_eq`,
`sum_frequencies_pow_five_ne`). So their uniform mixtures (`frequencyMixture`) agree on every
budget-4 configuration moment (`configurationMoment_frequencyLaw_sum_eq`,
`frequencyMixture_moments_eq`). The selection term of four carriers of one allele is
`4 (s(true) - s(false)) q⁴ (1 - q)` (`eval_selectionGenerator_fourCarriers`), of degree five, and
the two mixtures give it different expectations (`frequencyMixture_selection_ne`). Hence no
coefficient vector over the budget-4 configurations reproduces it
(`not_exists_budgetFour_selectionClosure`), and two selected families started from the mixtures
agree on no initial time interval (`not_budgetFour_moments_eq_of_selection`). Neutral families
started from the same mixtures agree for all time (`budgetFour_moments_eq_of_neutral`).

Scope. Selection is haploid at one locus, with one fitness table for the whole history. The
constant carries the coefficient masses of the metric polynomials, not a sup norm over sampled
genomes. The forward moment equation with selection is a hypothesis on the families; the selected
diffusion is not constructed.

## Empirical status

None. The bodies here are norm inequalities for matrix products and linear functionals of supplied
expectation families, so no measurement can bear on them.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.EndToEndSelectionLaw

open MeasureTheory ProbabilityTheory MvPolynomial Descent.Coalescent Descent.Foundations
  PartialHaplotypeCarrier PartialHaplotypeDualGenerator PartialHaplotypeDualSemigroup
  SubstochasticGeneratorSemigroup PartialHaplotypePulseKernel NeutralFellerGenerator
  NeutralPolynomialSemigroup NeutralMomentSemigroup PartialHaplotypeMicroscopicApproximation
  NeutralPulseHistoryKernel ReplicaMetricInstances EndToEndPortabilityLaw
  PortabilityMetricCompilation SelectionHistoryMoments
open scoped Matrix NNReal

noncomputable section

variable {Deme Locus : Type*} {Allele : Locus → Type*}
variable [Fintype Deme] [DecidableEq Deme] [Fintype Locus] [DecidableEq Locus]
  [∀ ℓ, Fintype (Allele ℓ)] [∀ ℓ, DecidableEq (Allele ℓ)]

/-! ## Selected moments along a history -/

/-- **A substochastic step after an approximation**: if `x` is within `a` of `P y` and `y` is
within `b` of `z`, then `x` is within `a + b` of `P z`. -/
theorem norm_sub_mulVec_le {ι : Type*} [Fintype ι] {P : Matrix ι ι ℝ}
    (hP : SubstochasticMatrix P) {x y z : ι → ℝ} {a b : ℝ} (hx : ‖x - P *ᵥ y‖ ≤ a)
    (hy : ‖y - z‖ ≤ b) : ‖x - P *ᵥ z‖ ≤ a + b := by
  have hsplit : x - P *ᵥ z = (x - P *ᵥ y) + P *ᵥ (y - z) := by
    rw [Matrix.mulVec_sub]
    abel
  rw [hsplit]
  exact (norm_add_le _ _).trans (add_le_add hx ((norm_mulVec_le_of_substochastic hP _).trans hy))

/-- The total duration of the epochs of a history; splits and pulses take no time. -/
def epochDuration : List ((NeutralRates Deme Locus Allele × ℝ≥0) ⊕ PulseMatrix Deme) → ℝ
  | [] => 0
  | Sum.inl epoch :: rest => epoch.2 + epochDuration rest
  | Sum.inr _ :: rest => epochDuration rest

/-- The total epoch duration of a history is nonnegative. -/
theorem epochDuration_nonneg :
    ∀ events : List ((NeutralRates Deme Locus Allele × ℝ≥0) ⊕ PulseMatrix Deme),
      0 ≤ epochDuration events
  | [] => le_rfl
  | Sum.inl epoch :: rest => add_nonneg (NNReal.coe_nonneg epoch.2) (epochDuration_nonneg rest)
  | Sum.inr _ :: rest => epochDuration_nonneg rest

/-- **Selection along a history of epochs, splits and pulses.** `family k` is the expectation
family over per-deme haplotype laws during the `k`-th event, on its own clock. During an epoch its
expected budget-respecting configuration moments are continuous on `[0, d]` and obey the forward
moment equation with selection at the epoch's neutral rates there, and the next family starts from
the moments at `d`. Across a split or a pulse the next family starts from the pulsed moments.

Assumes: the families are the moment tables of a selected process run through the events in
chronological order. -/
def SelectedOnHistory (model : SelectionModel Deme Locus Allele) (capacity : Locus → ℕ)
    (family : ℕ → ℝ → ExpFunctional (Deme → FiniteReportLaw (FullHaplotype Locus Allele))) :
    List ((NeutralRates Deme Locus Allele × ℝ≥0) ⊕ PulseMatrix Deme) → ℕ → Prop
  | [], _ => True
  | Sum.inl epoch :: rest, k =>
      (ContinuousOn (expectedMomentVector capacity (family k)) (Set.Icc 0 (epoch.2 : ℝ))
        ∧ (∀ ξ : BudgetConfiguration Deme Locus Allele capacity, ∀ t ∈ Set.Ico 0 (epoch.2 : ℝ),
          HasDerivWithinAt (fun s ↦ expectedMomentVector capacity (family k) s ξ)
            (family k t fun law ↦
              eval (lawPoint law) (selectedGenerator epoch.1 model (momentPolynomial ξ.1)))
            (Set.Ici t) t)
        ∧ expectedMomentVector capacity (family (k + 1)) 0
          = expectedMomentVector capacity (family k) epoch.2)
      ∧ SelectedOnHistory model capacity family rest (k + 1)
  | Sum.inr pulse :: rest, k =>
      (∀ ξ : BudgetConfiguration Deme Locus Allele capacity,
        expectedMomentVector capacity (family (k + 1)) 0 ξ
          = family k 0 fun law ↦ configurationMoment (pulsedLaw pulse law) ξ.1)
      ∧ SelectedOnHistory model capacity family rest (k + 1)

/-- The empty history carries no obligation, so `SelectedOnHistory` is inhabited. -/
theorem selectedOnHistory_nil (model : SelectionModel Deme Locus Allele) (capacity : Locus → ℕ)
    (family : ℕ → ℝ → ExpFunctional (Deme → FiniteReportLaw (FullHaplotype Locus Allele)))
    (k : ℕ) : SelectedOnHistory model capacity family [] k :=
  trivial

/-- **Selection moves the moments of a whole history by at most `B σ T`.** Along a history of
epochs, splits and pulses with total epoch duration `T`, selected families with fitnesses in
`[0, σ]` end with expected budget-respecting configuration moments within `B σ T` in sup norm of
the neutral chronological propagator applied to their initial moments, with `B = Σ_ℓ n_ℓ`.

Assumes: `SelectedOnHistory model capacity family events k`. -/
theorem norm_selectedHistory_sub_propagator_le (model : SelectionModel Deme Locus Allele)
    {σ : ℝ} (hσ : 0 ≤ σ) (hfit : ∀ i b, 0 ≤ model.fitness i b ∧ model.fitness i b ≤ σ)
    (capacity : Locus → ℕ)
    (family : ℕ → ℝ → ExpFunctional (Deme → FiniteReportLaw (FullHaplotype Locus Allele))) :
    ∀ (events : List ((NeutralRates Deme Locus Allele × ℝ≥0) ⊕ PulseMatrix Deme)) (k : ℕ),
      SelectedOnHistory model capacity family events k →
      ‖expectedMomentVector capacity (family (k + events.length)) 0
          - historyEventPropagator capacity events *ᵥ expectedMomentVector capacity (family k) 0‖
        ≤ (∑ ℓ, capacity ℓ : ℕ) * σ * epochDuration events
  | [], k, _ => by
    simp [historyEventPropagator, epochDuration]
  | Sum.inl epoch :: rest, k, hhistory => by
    obtain ⟨⟨hcont, hforward, hnext⟩, hrest⟩ := hhistory
    have hepoch := norm_expectedMomentVector_sub_propagator_le epoch.1 model hσ hfit capacity
      (family k) (NNReal.coe_nonneg epoch.2) hcont hforward
    rw [sub_zero, ← hnext] at hepoch
    have hlength : k + (Sum.inl epoch :: rest).length = k + 1 + rest.length := by
      rw [List.length_cons]
      omega
    rw [hlength, historyEventPropagator, eventPropagator, ← Matrix.mulVec_mulVec]
    refine (norm_sub_mulVec_le (historyEventPropagator_substochastic capacity rest)
      (norm_selectedHistory_sub_propagator_le model hσ hfit capacity family rest (k + 1) hrest)
      hepoch).trans_eq ?_
    simp only [epochDuration]
    ring
  | Sum.inr pulse :: rest, k, hhistory => by
    obtain ⟨hnext, hrest⟩ := hhistory
    have hpulse : expectedMomentVector capacity (family (k + 1)) 0
        = pulseKernel pulse capacity *ᵥ expectedMomentVector capacity (family k) 0 := by
      funext ξ
      rw [hnext ξ, pulseKernel_mulVec_expectedMoment]
      rfl
    have hlength : k + (Sum.inr pulse :: rest).length = k + 1 + rest.length := by
      rw [List.length_cons]
      omega
    have h := norm_selectedHistory_sub_propagator_le model hσ hfit capacity family rest (k + 1)
      hrest
    rw [hpulse] at h
    rw [hlength, historyEventPropagator, eventPropagator, ← Matrix.mulVec_mulVec]
    simpa only [epochDuration] using h

/-! ## The metrics under selection -/

/-- The frequency state of per-deme haplotype laws. -/
def lawState (law : Deme → FiniteReportLaw (FullHaplotype Locus Allele)) :
    FrequencyState Deme Locus Allele :=
  ⟨lawPoint law, fun c ↦ (law c.1).mass_nonneg c.2, fun i ↦ (law i).mass_sum⟩

/-- The moment vector of the state of per-deme laws is their configuration moments. -/
theorem momentVector_lawState (capacity : Locus → ℕ)
    (law : Deme → FiniteReportLaw (FullHaplotype Locus Allele)) :
    momentVector capacity (lawState law) = fun η ↦ configurationMoment law η.1 :=
  funext fun η ↦ eval_momentPolynomial law η.1

/-- **An expected budget polynomial is its coefficient vector on the expected moments.** Under
every expectation functional over per-deme laws, a polynomial whose monomials fit a budget has
expectation `c ⬝ v`, with `c` its budget coefficients and `v` the expected configuration
moments. -/
theorem expectation_polynomial_eq_dotProduct (ℓ₀ : Locus) (capacity : Locus → ℕ)
    (p : FrequencyPolynomial Deme Locus Allele)
    (hp : ∀ β ∈ p.support, WithinBudget capacity (monomialConfiguration ℓ₀ β))
    (expectation : ExpFunctional (Deme → FiniteReportLaw (FullHaplotype Locus Allele))) :
    (expectation fun law ↦ eval (lawPoint law) p)
      = budgetCoefficients ℓ₀ capacity p
        ⬝ᵥ fun η ↦ expectation fun law ↦ configurationMoment law η.1 := by
  have hpoint : (fun law ↦ eval (lawPoint law) p)
      = ∑ η, budgetCoefficients ℓ₀ capacity p η • fun law ↦ configurationMoment law η.1 := by
    funext law
    have h : eval (lawPoint law) p
        = ∑ η, budgetCoefficients ℓ₀ capacity p η * momentVector capacity (lawState law) η :=
      eval_eq_dotProduct ℓ₀ capacity p hp (lawState law)
    rw [h, momentVector_lawState, Finset.sum_apply]
    simp only [Pi.smul_apply, smul_eq_mul]
  rw [hpoint, ExpFunctional.eval_sum]
  simp only [ExpFunctional.smul_eval, dotProduct]

/-- At the frequency point of per-deme laws the numerator polynomial of a deme is the corpus
correlation numerator of that deme's law. -/
theorem eval_numeratorPolynomial (law : Deme → FiniteReportLaw (FullHaplotype Locus Allele))
    (deme : Deme) (score outcome : FullHaplotype Locus Allele → ℝ) :
    eval (lawPoint law) (numeratorPolynomial deme score outcome)
      = correlationNumerator (law deme) score outcome := by
  rw [numeratorPolynomial, demePolynomial, eval_rename]
  exact eval_correlationNumeratorPolynomial (law deme) score outcome

/-- At the frequency point of per-deme laws the denominator polynomial of a deme is the corpus
correlation denominator of that deme's law. -/
theorem eval_denominatorPolynomial (law : Deme → FiniteReportLaw (FullHaplotype Locus Allele))
    (deme : Deme) (score outcome : FullHaplotype Locus Allele → ℝ) :
    eval (lawPoint law) (denominatorPolynomial deme score outcome)
      = correlationDenominator (law deme) score outcome := by
  rw [denominatorPolynomial, demePolynomial, eval_rename]
  exact eval_correlationDenominatorPolynomial (law deme) score outcome

/-- The expected correlation numerator of a deme is the coefficient vector of the numerator
polynomial dotted with the expected budget-4 moments. -/
theorem expectation_correlationNumerator (ℓ₀ : Locus)
    (expectation : ExpFunctional (Deme → FiniteReportLaw (FullHaplotype Locus Allele)))
    (deme : Deme) (score outcome : FullHaplotype Locus Allele → ℝ) :
    (expectation fun law ↦ correlationNumerator (law deme) score outcome)
      = budgetCoefficients ℓ₀ (fun _ ↦ 4) (numeratorPolynomial deme score outcome)
        ⬝ᵥ fun η ↦ expectation fun law ↦ configurationMoment law η.1 := by
  have h := expectation_polynomial_eq_dotProduct ℓ₀ (fun _ ↦ 4)
    (numeratorPolynomial deme score outcome)
    (withinBudget_of_totalDegree_le ℓ₀ _ (totalDegree_numeratorPolynomial_le deme score outcome))
    expectation
  simpa only [eval_numeratorPolynomial] using h

/-- The expected correlation denominator of a deme is the coefficient vector of the denominator
polynomial dotted with the expected budget-4 moments. -/
theorem expectation_correlationDenominator (ℓ₀ : Locus)
    (expectation : ExpFunctional (Deme → FiniteReportLaw (FullHaplotype Locus Allele)))
    (deme : Deme) (score outcome : FullHaplotype Locus Allele → ℝ) :
    (expectation fun law ↦ correlationDenominator (law deme) score outcome)
      = budgetCoefficients ℓ₀ (fun _ ↦ 4) (denominatorPolynomial deme score outcome)
        ⬝ᵥ fun η ↦ expectation fun law ↦ configurationMoment law η.1 := by
  have h := expectation_polynomial_eq_dotProduct ℓ₀ (fun _ ↦ 4)
    (denominatorPolynomial deme score outcome)
    (withinBudget_of_totalDegree_le ℓ₀ _
      (totalDegree_denominatorPolynomial_le deme score outcome))
    expectation
  simpa only [eval_denominatorPolynomial] using h

/-- **A budget polynomial under selection, against the neutral end-to-end law.** Along a selected
history started from the moments of a state `x₀`, with fitnesses in `[0, σ]` and total epoch
duration `T`, the expected value of a polynomial whose monomials fit the budget differs from its
integral under the neutral history kernel by at most `‖c‖₁ B σ T`, with `c` its budget
coefficients and `B = Σ_ℓ n_ℓ`.

Assumes: `SelectedOnHistory model capacity family events 0`. -/
theorem abs_selectedPolynomial_sub_neutral_le (ℓ₀ : Locus) (hap₀ : FullHaplotype Locus Allele)
    (model : SelectionModel Deme Locus Allele) {σ : ℝ} (hσ : 0 ≤ σ)
    (hfit : ∀ i b, 0 ≤ model.fitness i b ∧ model.fitness i b ≤ σ) (capacity : Locus → ℕ)
    (family : ℕ → ℝ → ExpFunctional (Deme → FiniteReportLaw (FullHaplotype Locus Allele)))
    (events : List ((NeutralRates Deme Locus Allele × ℝ≥0) ⊕ PulseMatrix Deme))
    (hhistory : SelectedOnHistory model capacity family events 0)
    (x0 : FrequencyState Deme Locus Allele)
    (hinitial : expectedMomentVector capacity (family 0) 0 = budgetMomentFeature capacity x0)
    (p : FrequencyPolynomial Deme Locus Allele)
    (hp : ∀ β ∈ p.support, WithinBudget capacity (monomialConfiguration ℓ₀ β)) :
    |(family events.length 0 fun law ↦ eval (lawPoint law) p)
        - ∫ y, polynomialFunction p y ∂(historyEventKernel ℓ₀ hap₀ events x0)|
      ≤ (∑ i, |budgetCoefficients ℓ₀ capacity p i|)
        * ((∑ ℓ, capacity ℓ : ℕ) * σ * epochDuration events) := by
  haveI := isMarkovKernel_historyEventKernel ℓ₀ hap₀ events
  have hmoments := norm_selectedHistory_sub_propagator_le model hσ hfit capacity family events 0
    hhistory
  rw [zero_add, hinitial] at hmoments
  rw [expectation_polynomial_eq_dotProduct ℓ₀ capacity p hp,
    integral_polynomial_eq_dotProduct ℓ₀ capacity (historyEventKernel ℓ₀ hap₀ events)
      (historyEventPropagator capacity events)
      (integral_momentPolynomial_historyEventKernel ℓ₀ hap₀ capacity events) p hp x0]
  exact (abs_dotProduct_sub_le _ _ _).trans
    (mul_le_mul_of_nonneg_left hmoments (Finset.sum_nonneg fun i _ ↦ abs_nonneg _))

/-- The total size of the budget-4 space is four copies per locus. -/
theorem sum_four_capacity :
    ((∑ ℓ : Locus, (fun _ : Locus ↦ (4 : ℕ)) ℓ : ℕ) : ℝ) = 4 * Fintype.card Locus := by
  simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul, Nat.cast_mul, Nat.cast_ofNat]
  ring

/-- **The expected correlation numerator under selection, against the neutral end-to-end law**:
it differs by at most `‖c‖₁ 4 |L| σ T`.

Assumes: `SelectedOnHistory model (fun _ ↦ 4) family events 0`. -/
theorem abs_selectedNumerator_sub_neutral_le (ℓ₀ : Locus) (hap₀ : FullHaplotype Locus Allele)
    (model : SelectionModel Deme Locus Allele) {σ : ℝ} (hσ : 0 ≤ σ)
    (hfit : ∀ i b, 0 ≤ model.fitness i b ∧ model.fitness i b ≤ σ)
    (family : ℕ → ℝ → ExpFunctional (Deme → FiniteReportLaw (FullHaplotype Locus Allele)))
    (events : List ((NeutralRates Deme Locus Allele × ℝ≥0) ⊕ PulseMatrix Deme))
    (hhistory : SelectedOnHistory model (fun _ ↦ 4) family events 0)
    (x0 : FrequencyState Deme Locus Allele)
    (hinitial : expectedMomentVector (fun _ ↦ 4) (family 0) 0
      = budgetMomentFeature (fun _ ↦ 4) x0)
    (deme : Deme) (score outcome : FullHaplotype Locus Allele → ℝ) :
    |(family events.length 0 fun law ↦ correlationNumerator (law deme) score outcome)
        - ∫ y, correlationNumerator (stateLaw y deme) score outcome
          ∂(historyEventKernel ℓ₀ hap₀ events x0)|
      ≤ (∑ i, |budgetCoefficients ℓ₀ (fun _ ↦ 4) (numeratorPolynomial deme score outcome) i|)
        * (4 * Fintype.card Locus * σ * epochDuration events) := by
  have h := abs_selectedPolynomial_sub_neutral_le ℓ₀ hap₀ model hσ hfit (fun _ ↦ 4) family events
    hhistory x0 hinitial (numeratorPolynomial deme score outcome)
    (withinBudget_of_totalDegree_le ℓ₀ _ (totalDegree_numeratorPolynomial_le deme score outcome))
  simp only [eval_numeratorPolynomial, polynomialFunction_numeratorPolynomial] at h
  rw [sum_four_capacity] at h
  exact h

/-- **The expected correlation denominator under selection, against the neutral end-to-end law**:
it differs by at most `‖c‖₁ 4 |L| σ T`.

Assumes: `SelectedOnHistory model (fun _ ↦ 4) family events 0`. -/
theorem abs_selectedDenominator_sub_neutral_le (ℓ₀ : Locus) (hap₀ : FullHaplotype Locus Allele)
    (model : SelectionModel Deme Locus Allele) {σ : ℝ} (hσ : 0 ≤ σ)
    (hfit : ∀ i b, 0 ≤ model.fitness i b ∧ model.fitness i b ≤ σ)
    (family : ℕ → ℝ → ExpFunctional (Deme → FiniteReportLaw (FullHaplotype Locus Allele)))
    (events : List ((NeutralRates Deme Locus Allele × ℝ≥0) ⊕ PulseMatrix Deme))
    (hhistory : SelectedOnHistory model (fun _ ↦ 4) family events 0)
    (x0 : FrequencyState Deme Locus Allele)
    (hinitial : expectedMomentVector (fun _ ↦ 4) (family 0) 0
      = budgetMomentFeature (fun _ ↦ 4) x0)
    (deme : Deme) (score outcome : FullHaplotype Locus Allele → ℝ) :
    |(family events.length 0 fun law ↦ correlationDenominator (law deme) score outcome)
        - ∫ y, correlationDenominator (stateLaw y deme) score outcome
          ∂(historyEventKernel ℓ₀ hap₀ events x0)|
      ≤ (∑ i, |budgetCoefficients ℓ₀ (fun _ ↦ 4) (denominatorPolynomial deme score outcome) i|)
        * (4 * Fintype.card Locus * σ * epochDuration events) := by
  have h := abs_selectedPolynomial_sub_neutral_le ℓ₀ hap₀ model hσ hfit (fun _ ↦ 4) family events
    hhistory x0 hinitial (denominatorPolynomial deme score outcome)
    (withinBudget_of_totalDegree_le ℓ₀ _
      (totalDegree_denominatorPolynomial_le deme score outcome))
  simp only [eval_denominatorPolynomial, polynomialFunction_denominatorPolynomial] at h
  rw [sum_four_capacity] at h
  exact h

/-- **The expected portability of a selected history**: the target-over-source ratio
`(E N_t · E D_s) / (E D_t · E N_s)` of expected squared-correlation numerators and denominators
under the family at the end of the history. -/
def selectedPortability
    (family : ℕ → ℝ → ExpFunctional (Deme → FiniteReportLaw (FullHaplotype Locus Allele)))
    (n : ℕ) (source target : Deme) (score outcome : FullHaplotype Locus Allele → ℝ) : ℝ :=
  ((family n 0 fun law ↦ correlationNumerator (law target) score outcome)
      * family n 0 fun law ↦ correlationDenominator (law source) score outcome)
    / ((family n 0 fun law ↦ correlationDenominator (law target) score outcome)
      * family n 0 fun law ↦ correlationNumerator (law source) score outcome)

/-- **The selected portability is the rational portability function of the selected moments.** -/
theorem selectedPortability_eq_momentPortability (ℓ₀ : Locus)
    (family : ℕ → ℝ → ExpFunctional (Deme → FiniteReportLaw (FullHaplotype Locus Allele)))
    (n : ℕ) (source target : Deme) (score outcome : FullHaplotype Locus Allele → ℝ) :
    selectedPortability family n source target score outcome
      = momentPortability ℓ₀ source target score outcome
          (expectedMomentVector (fun _ ↦ 4) (family n) 0) := by
  rw [selectedPortability, expectation_correlationNumerator ℓ₀,
    expectation_correlationNumerator ℓ₀, expectation_correlationDenominator ℓ₀,
    expectation_correlationDenominator ℓ₀]
  rfl

/-- **Portability under selection along a history, with an explicit error bar.** Along a selected
history started from the moments of a state `x₀`, with fitnesses in `[0, σ]` and total epoch
duration `T`, where the expected target denominator and source numerator are at least `δ > 0`
under both the selected families and the neutral history kernel, the two portabilities differ by
at most `4 ‖a‖₁ ‖b‖₁ ‖c‖₁ ‖d‖₁ / δ⁴ · 4 |L| σ T`, with `a, b, c, d` the coefficient vectors of the
target numerator, source denominator, target denominator and source numerator.

Assumes: `SelectedOnHistory model (fun _ ↦ 4) family events 0`. -/
theorem abs_selectedPortability_sub_neutral_le (ℓ₀ : Locus) (hap₀ : FullHaplotype Locus Allele)
    (model : SelectionModel Deme Locus Allele) {σ : ℝ} (hσ : 0 ≤ σ)
    (hfit : ∀ i b, 0 ≤ model.fitness i b ∧ model.fitness i b ≤ σ)
    (family : ℕ → ℝ → ExpFunctional (Deme → FiniteReportLaw (FullHaplotype Locus Allele)))
    (events : List ((NeutralRates Deme Locus Allele × ℝ≥0) ⊕ PulseMatrix Deme))
    (hhistory : SelectedOnHistory model (fun _ ↦ 4) family events 0)
    (x0 : FrequencyState Deme Locus Allele)
    (hinitial : expectedMomentVector (fun _ ↦ 4) (family 0) 0
      = budgetMomentFeature (fun _ ↦ 4) x0)
    (source target : Deme) (score outcome : FullHaplotype Locus Allele → ℝ) {δ : ℝ}
    (hδ : 0 < δ)
    (htarget : δ ≤ family events.length 0 fun law ↦
      correlationDenominator (law target) score outcome)
    (hsource : δ ≤ family events.length 0 fun law ↦
      correlationNumerator (law source) score outcome)
    (htarget₀ : δ ≤ ∫ y, correlationDenominator (stateLaw y target) score outcome
      ∂(historyEventKernel ℓ₀ hap₀ events x0))
    (hsource₀ : δ ≤ ∫ y, correlationNumerator (stateLaw y source) score outcome
      ∂(historyEventKernel ℓ₀ hap₀ events x0)) :
    |selectedPortability family events.length source target score outcome
        - expectedPortability (historyEventKernel ℓ₀ hap₀ events) x0 source target score
          outcome|
      ≤ 4 * (∑ i, |budgetCoefficients ℓ₀ (fun _ ↦ 4) (numeratorPolynomial target score outcome) i|)
          * (∑ i, |budgetCoefficients ℓ₀ (fun _ ↦ 4)
              (denominatorPolynomial source score outcome) i|)
          * (∑ i, |budgetCoefficients ℓ₀ (fun _ ↦ 4)
              (denominatorPolynomial target score outcome) i|)
          * (∑ i, |budgetCoefficients ℓ₀ (fun _ ↦ 4) (numeratorPolynomial source score outcome) i|)
          / δ ^ 4 * (4 * Fintype.card Locus * σ * epochDuration events) := by
  have hmoments := norm_selectedHistory_sub_propagator_le model hσ hfit (fun _ ↦ 4) family
    events 0 hhistory
  rw [zero_add, hinitial, sum_four_capacity] at hmoments
  rw [expectation_correlationDenominator ℓ₀] at htarget
  rw [expectation_correlationNumerator ℓ₀] at hsource
  rw [integral_correlationDenominator_historyEventKernel] at htarget₀
  rw [integral_correlationNumerator_historyEventKernel] at hsource₀
  have hbox : ∀ η, |expectedMomentVector (fun _ ↦ 4) (family events.length) 0 η| ≤ 1 := by
    intro η
    show |family events.length 0 fun law ↦ configurationMoment law η.1| ≤ 1
    have h0 := (family events.length 0).eval_mono (f := fun _ ↦ (0 : ℝ))
      (g := fun law ↦ configurationMoment law η.1) fun law ↦
        PartialHaplotypeCarrier.configurationMoment_nonneg law η.1
    have h1 := (family events.length 0).eval_mono (f := fun law ↦ configurationMoment law η.1)
      (g := fun _ ↦ (1 : ℝ)) fun law ↦ configurationMoment_le_one law η.1
    simp only [ExpFunctional.eval_const] at h0 h1
    exact abs_le.mpr ⟨by linarith, h1⟩
  have hbox₀ : ∀ η, |(historyEventPropagator (fun _ ↦ 4) events
      *ᵥ budgetMomentFeature (fun _ ↦ 4) x0) η| ≤ 1 := by
    intro η
    have hfeature : ‖budgetMomentFeature (Allele := Allele) (fun _ ↦ 4) x0‖ ≤ 1 := by
      refine (pi_norm_le_iff_of_nonneg zero_le_one).mpr fun ζ ↦ ?_
      show ‖eval x0.1 (momentPolynomial ζ.1)‖ ≤ 1
      rw [Real.norm_eq_abs, ← lawPoint_stateLaw x0, eval_momentPolynomial]
      have hnonneg := PartialHaplotypeCarrier.configurationMoment_nonneg (stateLaw x0) ζ.1
      exact abs_le.mpr ⟨by linarith, configurationMoment_le_one _ _⟩
    have h := (norm_le_pi_norm _ η).trans ((norm_mulVec_le_of_substochastic
      (historyEventPropagator_substochastic (fun _ ↦ 4) events) _).trans hfeature)
    rwa [Real.norm_eq_abs] at h
  have hcross := abs_crossRatio_sub_le
    (fun w : {w : BudgetConfiguration Deme Locus Allele (fun _ ↦ 4) → ℝ // ∀ i, |w i| ≤ 1} ↦
      w.1) hδ (fun w i ↦ w.2 i)
    (budgetCoefficients ℓ₀ (fun _ ↦ 4) (numeratorPolynomial target score outcome))
    (budgetCoefficients ℓ₀ (fun _ ↦ 4) (denominatorPolynomial source score outcome))
    (budgetCoefficients ℓ₀ (fun _ ↦ 4) (denominatorPolynomial target score outcome))
    (budgetCoefficients ℓ₀ (fun _ ↦ 4) (numeratorPolynomial source score outcome))
    (RealizationBody.mem_realizationBody_of_range _ ⟨_, hbox⟩)
    (RealizationBody.mem_realizationBody_of_range _ ⟨_, hbox₀⟩) htarget hsource htarget₀ hsource₀
  rw [selectedPortability_eq_momentPortability ℓ₀, expectedPortability_historyEventKernel]
  refine hcross.trans ?_
  rw [one_pow, mul_one]
  exact mul_le_mul_of_nonneg_left hmoments (by positivity)

/-! ## Why finitely many moments give no exact law under selection -/

section Nonclosure

open Filter Topology

/-- A sum over the haplotypes of one biallelic locus is a sum over its two alleles. -/
theorem sum_unitHaplotype (g : FullHaplotype Unit (fun _ : Unit ↦ Bool) → ℝ) :
    ∑ hap, g hap = g (fun _ ↦ true) + g (fun _ ↦ false) :=
  (Fintype.sum_equiv (Equiv.funUnique Unit Bool) g (fun b ↦ g fun _ ↦ b)
    fun hap ↦ congrArg g (funext fun _ ↦ rfl)).trans (Fintype.sum_bool _)

/-- The law of one deme at one biallelic locus carrying allele `true` at frequency `q`. -/
def frequencyLaw (q : ℝ) (hq : 0 ≤ q ∧ q ≤ 1) :
    Unit → FiniteReportLaw (FullHaplotype Unit fun _ : Unit ↦ Bool) :=
  fun _ ↦
    { mass := fun hap ↦ if hap () then q else 1 - q
      mass_nonneg := fun hap ↦ by
        split_ifs
        · exact hq.1
        · linarith [hq.2]
      mass_sum := by
        rw [sum_unitHaplotype]
        simp }

/-- **A carrier of the biallelic locus counts `q` or `1 - q`**, by the allele it retains. -/
theorem marginalFrequency_frequencyLaw (q : ℝ) (hq : 0 ≤ q ∧ q ≤ 1)
    (τ : PartialType Unit Unit fun _ : Unit ↦ Bool) :
    marginalFrequency (frequencyLaw q hq) τ = if τ.allele () = some true then q else 1 - q := by
  obtain ⟨u, hu⟩ := τ.retained
  obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp hu
  have hagree : ∀ c : Bool, Agrees τ (fun _ ↦ c) ↔ b = c := by
    intro c
    constructor
    · intro h
      rcases h u with h0 | h0
      · rw [hb] at h0
        exact absurd h0 (by simp)
      · rw [hb] at h0
        exact Option.some.inj h0
    · rintro rfl v
      exact Or.inr (by cases u; cases v; exact hb)
  rw [marginalFrequency, Finset.sum_filter, sum_unitHaplotype]
  cases u
  cases b <;> simp [hagree, hb, frequencyLaw]

/-- The allele frequencies `0, 4/18, 8/18, 16/18, 17/18`. -/
def firstFrequencies : Fin 5 → ℝ :=
  ![0, 4 / 18, 8 / 18, 16 / 18, 17 / 18]

/-- The allele frequencies `1/18, 2/18, 10/18, 14/18, 1`. Their power sums agree with those of
`firstFrequencies` through the fourth power and differ at the fifth, as the Prouhet–Tarry–Escott
sets `{0, 4, 8, 16, 17}` and `{1, 2, 10, 14, 18}` do. -/
def secondFrequencies : Fin 5 → ℝ :=
  ![1 / 18, 2 / 18, 10 / 18, 14 / 18, 1]

/-- The first frequencies lie in the unit interval. -/
theorem firstFrequencies_mem (k : Fin 5) : 0 ≤ firstFrequencies k ∧ firstFrequencies k ≤ 1 := by
  fin_cases k <;> norm_num [firstFrequencies]

/-- The second frequencies lie in the unit interval. -/
theorem secondFrequencies_mem (k : Fin 5) :
    0 ≤ secondFrequencies k ∧ secondFrequencies k ≤ 1 := by
  fin_cases k <;> norm_num [secondFrequencies]

/-- The two sets of frequencies have equal power sums through the fourth power. -/
theorem sum_frequencies_pow_eq {m : ℕ} (hm : m ≤ 4) :
    ∑ k, firstFrequencies k ^ m = ∑ k, secondFrequencies k ^ m := by
  interval_cases m <;> norm_num [Fin.sum_univ_succ, firstFrequencies, secondFrequencies]

/-- The two sets of frequencies have different fifth power sums. -/
theorem sum_frequencies_pow_five_ne :
    ∑ k, firstFrequencies k ^ 5 ≠ ∑ k, secondFrequencies k ^ 5 := by
  norm_num [Fin.sum_univ_succ, firstFrequencies, secondFrequencies]

/-- The uniform mixture of the laws at five frequencies, as an expectation functional over
per-deme laws: a random initial state. -/
def frequencyMixture (q : Fin 5 → ℝ) (hq : ∀ k, 0 ≤ q k ∧ q k ≤ 1) :
    ExpFunctional (Unit → FiniteReportLaw (FullHaplotype Unit fun _ : Unit ↦ Bool)) where
  eval f := (∑ k, f (frequencyLaw (q k) (hq k))) / 5
  add_eval f g := by simp only [Pi.add_apply, Finset.sum_add_distrib, add_div]
  smul_eval c f := by simp only [Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum, mul_div_assoc]
  const_one := by norm_num
  nonneg_eval f hf := div_nonneg (Finset.sum_nonneg fun k _ ↦ hf _) (by norm_num)

/-- **Configuration moments of the biallelic locus see only powers of the frequency.** If two
sets of five frequencies have equal power sums through the fourth power, then the sums of
`H_ζ q^m` over them agree whenever `ζ` has `n` carriers and `n + m ≤ 4`. -/
theorem configurationMoment_frequencyLaw_sum_eq (q₁ q₂ : Fin 5 → ℝ)
    (hq₁ : ∀ k, 0 ≤ q₁ k ∧ q₁ k ≤ 1) (hq₂ : ∀ k, 0 ≤ q₂ k ∧ q₂ k ≤ 1)
    (hpow : ∀ m ≤ 4, ∑ k, q₁ k ^ m = ∑ k, q₂ k ^ m) :
    ∀ (ζ : Multiset (PartialType Unit Unit fun _ : Unit ↦ Bool)) (m : ℕ),
      Multiset.card ζ + m ≤ 4 →
      ∑ k, configurationMoment (frequencyLaw (q₁ k) (hq₁ k)) ζ * q₁ k ^ m
        = ∑ k, configurationMoment (frequencyLaw (q₂ k) (hq₂ k)) ζ * q₂ k ^ m := by
  intro ζ
  induction ζ using Multiset.induction_on with
  | empty =>
    intro m hm
    simpa [configurationMoment] using hpow m (by simpa using hm)
  | cons τ ζ ih =>
    intro m hm
    rw [Multiset.card_cons] at hm
    simp only [configurationMoment_cons, marginalFrequency_frequencyLaw]
    split_ifs
    · have hshift : ∀ (q H : Fin 5 → ℝ),
          ∑ k, q k * H k * q k ^ m = ∑ k, H k * q k ^ (m + 1) :=
        fun q H ↦ Finset.sum_congr rfl fun k _ ↦ by ring
      rw [hshift, hshift]
      exact ih (m + 1) (by omega)
    · have hsplit : ∀ (q H : Fin 5 → ℝ),
          ∑ k, (1 - q k) * H k * q k ^ m = ∑ k, H k * q k ^ m - ∑ k, H k * q k ^ (m + 1) := by
        intro q H
        rw [← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun k _ ↦ by ring
      rw [hsplit, hsplit, ih m (by omega), ih (m + 1) (by omega)]

/-- **The two mixtures agree through budget four**: every budget-4 configuration moment has the
same expectation under both. -/
theorem frequencyMixture_moments_eq
    (ξ : BudgetConfiguration Unit Unit (fun _ : Unit ↦ Bool) (fun _ ↦ 4)) :
    (frequencyMixture firstFrequencies firstFrequencies_mem fun law ↦
        configurationMoment law ξ.1)
      = frequencyMixture secondFrequencies secondFrequencies_mem fun law ↦
        configurationMoment law ξ.1 := by
  have hcard : Multiset.card ξ.1 + 0 ≤ 4 := by
    simpa using card_le_capacity_total (fun _ : Unit ↦ 4) ξ.1 ξ.2
  have h := configurationMoment_frequencyLaw_sum_eq firstFrequencies secondFrequencies
    firstFrequencies_mem secondFrequencies_mem (fun m hm ↦ sum_frequencies_pow_eq hm) ξ.1 0 hcard
  simp only [pow_zero, mul_one] at h
  show (∑ k, configurationMoment (frequencyLaw (firstFrequencies k) (firstFrequencies_mem k))
      ξ.1) / 5
    = (∑ k, configurationMoment (frequencyLaw (secondFrequencies k) (secondFrequencies_mem k))
      ξ.1) / 5
  rw [h]

/-- Four copies of the one-locus carrier of allele `true`. -/
def fourCarriers : Multiset (PartialType Unit Unit fun _ : Unit ↦ Bool) :=
  Multiset.replicate 4 (singleLocusType () () true)

/-- The four carriers respect the budget of four copies. -/
theorem withinBudget_fourCarriers : WithinBudget (fun _ : Unit ↦ 4) fourCarriers :=
  fun _ ↦ (Multiset.countP_le_card _ _).trans (by simp [fourCarriers])

/-- The four carriers as a budget-4 configuration: the fourth power of the allele frequency. -/
def fourCarrierConfiguration : BudgetConfiguration Unit Unit (fun _ : Unit ↦ Bool) (fun _ ↦ 4) :=
  ⟨fourCarriers, withinBudget_fourCarriers⟩

/-- **The selection term of four carriers** at frequency `q` is `4 (s(true) - s(false)) q⁴ (1 - q)`:
a polynomial of degree five in the frequency. -/
theorem eval_selectionGenerator_fourCarriers (model : SelectionModel Unit Unit fun _ : Unit ↦ Bool)
    (q : ℝ) (hq : 0 ≤ q ∧ q ≤ 1) :
    eval (lawPoint (frequencyLaw q hq)) (selectionGenerator model (momentPolynomial fourCarriers))
      = 4 * (model.fitness () true - model.fitness () false) * (q ^ 4 * (1 - q)) := by
  have hlaw : ∀ (i : Unit) (hap : FullHaplotype Unit fun _ : Unit ↦ Bool),
      lawPoint (frequencyLaw q hq) (i, hap) = if hap () then q else 1 - q := fun _ _ ↦ rfl
  have hdeme : (singleLocusType () () true : PartialType Unit Unit fun _ : Unit ↦ Bool).deme = () :=
    rfl
  have hallele :
      (singleLocusType () () true : PartialType Unit Unit fun _ : Unit ↦ Bool).allele ()
        = some true := by
    simp [singleLocusType]
  have hmean : ∀ i : Unit, eval (lawPoint (frequencyLaw q hq)) (meanFitnessPolynomial model i)
      = q * model.fitness () true + (1 - q) * model.fitness () false := by
    intro i
    rw [eval_meanFitnessPolynomial, sum_unitHaplotype]
    cases i
    simp [hlaw]
  have hcarrier : eval (lawPoint (frequencyLaw q hq))
      (selectionGenerator model (marginalPolynomial (singleLocusType () () true)))
      = q * (1 - q) * (model.fitness () true - model.fitness () false) := by
    rw [eval_selectionGenerator_marginal, Finset.sum_filter, sum_unitHaplotype, hmean]
    simp [satisfies_singleLocusType_iff, hlaw, hdeme]
    ring
  have hrest : eval (lawPoint (frequencyLaw q hq))
      (momentPolynomial (Multiset.replicate 3 (singleLocusType () () true))) = q ^ 3 := by
    rw [eval_momentPolynomial]
    simp [configurationMoment, Multiset.prod_replicate, marginalFrequency_frequencyLaw, hallele]
    ring
  rw [eval_selectionGenerator_momentPolynomial, fourCarriers, Multiset.map_replicate,
    Multiset.sum_replicate, Multiset.replicate_succ, Multiset.erase_cons_head, hcarrier, hrest]
  simp only [nsmul_eq_mul, Nat.cast_ofNat]
  ring

/-- **The two mixtures differ in their expected selection term** of four carriers whenever the
two alleles differ in fitness: the term reads the fifth power sum. -/
theorem frequencyMixture_selection_ne (model : SelectionModel Unit Unit fun _ : Unit ↦ Bool)
    (hfit : model.fitness () true ≠ model.fitness () false) :
    (frequencyMixture firstFrequencies firstFrequencies_mem fun law ↦
        eval (lawPoint law) (selectionGenerator model (momentPolynomial fourCarriers)))
      ≠ frequencyMixture secondFrequencies secondFrequencies_mem fun law ↦
        eval (lawPoint law) (selectionGenerator model (momentPolynomial fourCarriers)) := by
  show (∑ k, eval (lawPoint (frequencyLaw (firstFrequencies k) (firstFrequencies_mem k)))
      (selectionGenerator model (momentPolynomial fourCarriers))) / 5
    ≠ (∑ k, eval (lawPoint (frequencyLaw (secondFrequencies k) (secondFrequencies_mem k)))
      (selectionGenerator model (momentPolynomial fourCarriers))) / 5
  simp only [eval_selectionGenerator_fourCarriers]
  intro h
  have hsum : ∀ q : Fin 5 → ℝ,
      ∑ k, 4 * (model.fitness () true - model.fitness () false) * (q k ^ 4 * (1 - q k))
        = 4 * (model.fitness () true - model.fitness () false) * ∑ k, q k ^ 4
          - 4 * (model.fitness () true - model.fitness () false) * ∑ k, q k ^ 5 := by
    intro q
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun k _ ↦ by ring
  rw [hsum, hsum, sum_frequencies_pow_eq (m := 4) le_rfl,
    div_left_inj' (by norm_num : (5 : ℝ) ≠ 0), sub_right_inj] at h
  exact sum_frequencies_pow_five_ne
    (mul_left_cancel₀ (mul_ne_zero four_ne_zero (sub_ne_zero.mpr hfit)) h)

/-- **The selection term closes on no budget-4 table.** For one deme at one biallelic locus with
unequal fitnesses, no coefficient vector over the budget-4 configurations reproduces the selection
generator of four carriers at every per-deme law. -/
theorem not_exists_budgetFour_selectionClosure
    (model : SelectionModel Unit Unit fun _ : Unit ↦ Bool)
    (hfit : model.fitness () true ≠ model.fitness () false) :
    ¬ ∃ c : BudgetConfiguration Unit Unit (fun _ : Unit ↦ Bool) (fun _ ↦ 4) → ℝ,
      ∀ law : Unit → FiniteReportLaw (FullHaplotype Unit fun _ : Unit ↦ Bool),
        eval (lawPoint law) (selectionGenerator model (momentPolynomial fourCarriers))
          = c ⬝ᵥ fun η ↦ configurationMoment law η.1 := by
  rintro ⟨c, hc⟩
  have hlinear :
      ∀ E : ExpFunctional (Unit → FiniteReportLaw (FullHaplotype Unit fun _ : Unit ↦ Bool)),
        (E fun law ↦ eval (lawPoint law) (selectionGenerator model (momentPolynomial fourCarriers)))
          = c ⬝ᵥ fun η ↦ E fun law ↦ configurationMoment law η.1 := by
    intro E
    have hpoint : (fun law ↦
        eval (lawPoint law) (selectionGenerator model (momentPolynomial fourCarriers)))
        = ∑ η, c η • fun law ↦ configurationMoment law η.1 := by
      funext law
      rw [hc law, Finset.sum_apply]
      simp only [dotProduct, Pi.smul_apply, smul_eq_mul]
    rw [hpoint, ExpFunctional.eval_sum]
    simp only [ExpFunctional.smul_eval, dotProduct]
  apply frequencyMixture_selection_ne model hfit
  rw [hlinear, hlinear]
  congr 1
  funext η
  exact frequencyMixture_moments_eq η

/-- Families started from the two mixtures have equal budget-4 moments at time zero. -/
theorem expectedMomentVector_zero_eq_of_mixtures
    (first second :
      ℝ → ExpFunctional (Unit → FiniteReportLaw (FullHaplotype Unit fun _ : Unit ↦ Bool)))
    (hfirst0 : first 0 = frequencyMixture firstFrequencies firstFrequencies_mem)
    (hsecond0 : second 0 = frequencyMixture secondFrequencies secondFrequencies_mem) :
    expectedMomentVector (fun _ ↦ 4) first 0 = expectedMomentVector (fun _ ↦ 4) second 0 := by
  funext ξ
  show (first 0 fun law ↦ configurationMoment law ξ.1)
    = second 0 fun law ↦ configurationMoment law ξ.1
  rw [hfirst0, hsecond0]
  exact frequencyMixture_moments_eq ξ

/-- **Finitely many moments give no exact law under selection.** For one deme at one biallelic
locus with unequal fitnesses and any neutral rates, two expectation families started from the two
mixtures agree on every budget-4 moment at time zero. If both obey the forward moment equation with
selection for the four carriers at time zero, their budget-4 moments agree on no interval
`[0, ε)`: the budget-4 moments at later times are not a function of those at time zero.

Assumes: `first` and `second` have right derivatives at time zero given by the expected generator
with selection. -/
theorem not_budgetFour_moments_eq_of_selection
    (rates : NeutralRates Unit Unit fun _ : Unit ↦ Bool)
    (model : SelectionModel Unit Unit fun _ : Unit ↦ Bool)
    (hfit : model.fitness () true ≠ model.fitness () false)
    (first second :
      ℝ → ExpFunctional (Unit → FiniteReportLaw (FullHaplotype Unit fun _ : Unit ↦ Bool)))
    (hfirst0 : first 0 = frequencyMixture firstFrequencies firstFrequencies_mem)
    (hsecond0 : second 0 = frequencyMixture secondFrequencies secondFrequencies_mem)
    (hfirst : HasDerivWithinAt
      (fun s ↦ expectedMomentVector (fun _ ↦ 4) first s fourCarrierConfiguration)
      (first 0 fun law ↦ eval (lawPoint law)
        (selectedGenerator rates model (momentPolynomial fourCarrierConfiguration.1)))
      (Set.Ici 0) 0)
    (hsecond : HasDerivWithinAt
      (fun s ↦ expectedMomentVector (fun _ ↦ 4) second s fourCarrierConfiguration)
      (second 0 fun law ↦ eval (lawPoint law)
        (selectedGenerator rates model (momentPolynomial fourCarrierConfiguration.1)))
      (Set.Ici 0) 0) :
    ¬ ∃ ε > 0, ∀ t ∈ Set.Ico (0 : ℝ) ε,
      expectedMomentVector (fun _ ↦ 4) first t = expectedMomentVector (fun _ ↦ 4) second t := by
  rintro ⟨ε, hε, hagree⟩
  have heq : (fun s ↦ expectedMomentVector (fun _ ↦ 4) first s fourCarrierConfiguration)
      =ᶠ[𝓝[≥] 0] fun s ↦ expectedMomentVector (fun _ ↦ 4) second s fourCarrierConfiguration :=
    Filter.eventually_of_mem (Ico_mem_nhdsGE hε) fun t ht ↦ congrFun (hagree t ht) _
  have hderiv := (uniqueDiffWithinAt_Ici 0).eq_deriv _ hfirst
    (hsecond.congr_of_eventuallyEq heq (congrFun (hagree 0 ⟨le_rfl, hε⟩) _))
  rw [expectedSelectedGenerator_eq rates model (fun _ ↦ 4) first 0 fourCarrierConfiguration,
    expectedSelectedGenerator_eq rates model (fun _ ↦ 4) second 0 fourCarrierConfiguration,
    expectedMomentVector_zero_eq_of_mixtures first second hfirst0 hsecond0, add_right_inj]
    at hderiv
  apply frequencyMixture_selection_ne model hfit
  rw [← hfirst0, ← hsecond0]
  exact hderiv

/-- **Under neutrality the two mixtures give equal budget-4 moments for all time**: the neutral
forward moment equation closes on budget four, so the moments are `e^{tQ}` of the equal initial
moments. -/
theorem budgetFour_moments_eq_of_neutral (rates : NeutralRates Unit Unit fun _ : Unit ↦ Bool)
    (first second :
      ℝ → ExpFunctional (Unit → FiniteReportLaw (FullHaplotype Unit fun _ : Unit ↦ Bool)))
    (hfirst0 : first 0 = frequencyMixture firstFrequencies firstFrequencies_mem)
    (hsecond0 : second 0 = frequencyMixture secondFrequencies secondFrequencies_mem)
    (hfirst : ∀ ξ : BudgetConfiguration Unit Unit (fun _ : Unit ↦ Bool) (fun _ ↦ 4),
      ∀ t ∈ Set.Ici (0 : ℝ),
        HasDerivWithinAt (fun s ↦ expectedMomentVector (fun _ ↦ 4) first s ξ)
          (first t fun law ↦ eval (lawPoint law) (neutralGenerator rates (momentPolynomial ξ.1)))
          (Set.Ici 0) t)
    (hsecond : ∀ ξ : BudgetConfiguration Unit Unit (fun _ : Unit ↦ Bool) (fun _ ↦ 4),
      ∀ t ∈ Set.Ici (0 : ℝ),
        HasDerivWithinAt (fun s ↦ expectedMomentVector (fun _ ↦ 4) second s ξ)
          (second t fun law ↦ eval (lawPoint law) (neutralGenerator rates (momentPolynomial ξ.1)))
          (Set.Ici 0) t)
    {t : ℝ} (ht : 0 ≤ t) :
    expectedMomentVector (fun _ ↦ 4) first t = expectedMomentVector (fun _ ↦ 4) second t := by
  rw [expectedMomentVector_eq_matrixExponential rates (fun _ ↦ 4) first hfirst t ht,
    expectedMomentVector_eq_matrixExponential rates (fun _ ↦ 4) second hsecond t ht,
    expectedMomentVector_zero_eq_of_mixtures first second hfirst0 hsecond0]

end Nonclosure

end

end Descent.Portability.EndToEndSelectionLaw
