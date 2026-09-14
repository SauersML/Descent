/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.SelectionHistoryFirstOrder

assert_below Descent.Decision Descent.Program

/-!
# Selection whose fitness table changes between epochs

`EndToEndSelectionLaw` and `SelectionHistoryFirstOrder` carry haploid selection along a history of
epochs, splits and pulses with one fitness table for the whole history. Selection that changes
with the environment, or a sweep confined to one epoch, needs a table per epoch. This module gives
every event of a history its own selection model and bounds the moments and portability by the
time-weighted total selection.

The selected history. `VaryingSelectedOnHistory` asks of the families, one event at a time, what
`SelectedOnHistory` asks of a one-event history with the model `models k` of the `k`-th event:
during an epoch the expected moments are continuous and obey the forward moment equation with
selection at the epoch's rates and table, and the next family starts where the epoch ends; across
a split or a pulse the next family starts from the pulsed moments. With one model for every event
it is `SelectedOnHistory` (`varyingSelectedOnHistory_const_iff`).

Zero order. One event moves the moments from its neutral propagator by at most `B σ_k d_k`, with
`d_k` its duration, zero for a split or pulse (`norm_event_sub_propagator_le`, the one-event case
of `EndToEndSelectionLaw.norm_selectedHistory_sub_propagator_le`). Every later propagator is
substochastic, so along the history the selected moments end within `B Σ_k σ_k d_k` in sup norm
of the neutral chronological propagation of the initial moments
(`norm_varyingHistory_sub_propagator_le`), with `B = Σ_ℓ n_ℓ`. The time-weighted total selection
`weightedSelection` is at most `(max_k σ_k) T` (`weightedSelection_le`) and is `σ T` for a
constant bound (`weightedSelection_const`), so the one-table bound `B σ T` is the constant case
(`norm_selectedHistory_sub_propagator_le_of_const`).

Portability. Where the target denominator and the source numerator are at least `δ > 0` under the
selected family and at the neutral moments, the portability of expected accuracies of the selected
history differs from the portability of the neutral propagation by at most
`4 ‖a‖₁ ‖b‖₁ ‖c‖₁ ‖d‖₁ / δ⁴ · 4 |L| Σ_k σ_k d_k`, with `a, b, c, d` the coefficient vectors of the
target numerator, source denominator, target denominator and source numerator
(`abs_varyingPortability_sub_neutral_le`).

Significance. The error bar charges every epoch its own strength for its own duration. An epoch
without fitness differences costs nothing, and a sweep confined to one epoch costs its strength
times that epoch's length, where the one-table law charges the largest strength for the whole
history.

Scope. The forward moment equation with selection is a hypothesis on the families during every
epoch, at that epoch's table, as in `EndToEndSelectionLaw`; the selected diffusion is not
constructed. Selection is haploid at one locus per epoch, and the locus may change between epochs.
The constant carries the coefficient masses of the metric polynomials. The first-order correction
along a history with changing tables is not stated.

## Empirical status

None. The bodies here are norm inequalities for matrix products and finite sums of supplied
bounds, so no measurement can bear on them.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.SelectionHistoryVaryingFitness

open MvPolynomial Descent.Coalescent Descent.Foundations PartialHaplotypeCarrier
  PartialHaplotypeDualGenerator PartialHaplotypeDualSemigroup SubstochasticGeneratorSemigroup
  PartialHaplotypePulseKernel NeutralPulseHistoryKernel ReplicaMetricInstances
  EndToEndPortabilityLaw PortabilityMetricCompilation SelectionHistoryMoments EndToEndSelectionLaw
  SelectionHistoryFirstOrder
open scoped Matrix NNReal

noncomputable section

variable {Deme Locus : Type*} {Allele : Locus → Type*}
variable [Fintype Deme] [DecidableEq Deme] [Fintype Locus] [DecidableEq Locus]
  [∀ ℓ, Fintype (Allele ℓ)] [∀ ℓ, DecidableEq (Allele ℓ)]

/-! ## The time-weighted total selection -/

/-- **The time-weighted total selection** `Σ_k σ_k d_k` of a history, with `σ_k` the fitness bound
of the `k`-th event and `d_k` its duration; splits and pulses take no time. -/
def weightedSelection (σ : ℕ → ℝ) :
    List ((NeutralRates Deme Locus Allele × ℝ≥0) ⊕ PulseMatrix Deme) → ℕ → ℝ
  | [], _ => 0
  | event :: rest, k => σ k * epochDuration [event] + weightedSelection σ rest (k + 1)

/-- With one bound `σ` for every event the time-weighted total selection is `σ T`. -/
theorem weightedSelection_const (σ : ℝ) :
    ∀ (events : List ((NeutralRates Deme Locus Allele × ℝ≥0) ⊕ PulseMatrix Deme)) (k : ℕ),
      weightedSelection (fun _ ↦ σ) events k = σ * epochDuration events
  | [], _ => by simp only [weightedSelection, epochDuration, mul_zero]
  | Sum.inl epoch :: rest, k => by
    simp only [weightedSelection, weightedSelection_const σ rest (k + 1), epochDuration]
    ring
  | Sum.inr pulse :: rest, k => by
    simp only [weightedSelection, weightedSelection_const σ rest (k + 1), epochDuration]
    ring

/-- **The time-weighted total selection is at most the largest bound times the total epoch
duration.** -/
theorem weightedSelection_le {σ : ℕ → ℝ} {σmax : ℝ} (hσ : ∀ k, σ k ≤ σmax) :
    ∀ (events : List ((NeutralRates Deme Locus Allele × ℝ≥0) ⊕ PulseMatrix Deme)) (k : ℕ),
      weightedSelection σ events k ≤ σmax * epochDuration events
  | [], _ => by simp only [weightedSelection, epochDuration, mul_zero, le_refl]
  | Sum.inl epoch :: rest, k => by
    simp only [weightedSelection, epochDuration, add_zero, mul_add]
    exact add_le_add (mul_le_mul_of_nonneg_right (hσ k) (NNReal.coe_nonneg epoch.2))
      (weightedSelection_le hσ rest (k + 1))
  | Sum.inr pulse :: rest, k => by
    simp only [weightedSelection, epochDuration, mul_zero, zero_add]
    exact weightedSelection_le hσ rest (k + 1)

/-! ## Selected moments along a history with a table per event -/

/-- **Selection along a history with a fitness table per event.** `family k` is the expectation
family over per-deme haplotype laws during the `k`-th event, on its own clock, and `models k` is the
selection model of that event. Every event is a one-event selected history for its own model:
during an epoch the expected moments are continuous and obey the forward moment equation with
selection at the epoch's rates and table, and the next family starts from the moments at the end
of the epoch; across a split or a pulse the next family starts from the pulsed moments.

Assumes: the families are the moment tables of a process run through the events in chronological
order and selected during the `k`-th event with the table of `models k`. -/
def VaryingSelectedOnHistory (models : ℕ → SelectionModel Deme Locus Allele)
    (capacity : Locus → ℕ)
    (family : ℕ → ℝ → ExpFunctional (Deme → FiniteReportLaw (FullHaplotype Locus Allele))) :
    List ((NeutralRates Deme Locus Allele × ℝ≥0) ⊕ PulseMatrix Deme) → ℕ → Prop
  | [], _ => True
  | event :: rest, k =>
      SelectedOnHistory (models k) capacity family [event] k
        ∧ VaryingSelectedOnHistory models capacity family rest (k + 1)

/-- The empty history carries no obligation, so `VaryingSelectedOnHistory` is inhabited. -/
theorem varyingSelectedOnHistory_nil (models : ℕ → SelectionModel Deme Locus Allele)
    (capacity : Locus → ℕ)
    (family : ℕ → ℝ → ExpFunctional (Deme → FiniteReportLaw (FullHaplotype Locus Allele)))
    (k : ℕ) : VaryingSelectedOnHistory models capacity family [] k :=
  trivial

/-- **With one model for every event the history is selected with one table**:
`VaryingSelectedOnHistory` at a constant model is `SelectedOnHistory`. -/
theorem varyingSelectedOnHistory_const_iff (model : SelectionModel Deme Locus Allele)
    (capacity : Locus → ℕ)
    (family : ℕ → ℝ → ExpFunctional (Deme → FiniteReportLaw (FullHaplotype Locus Allele))) :
    ∀ (events : List ((NeutralRates Deme Locus Allele × ℝ≥0) ⊕ PulseMatrix Deme)) (k : ℕ),
      VaryingSelectedOnHistory (fun _ ↦ model) capacity family events k
        ↔ SelectedOnHistory model capacity family events k
  | [], _ => Iff.rfl
  | Sum.inl epoch :: rest, k => by
    rw [VaryingSelectedOnHistory,
      varyingSelectedOnHistory_const_iff model capacity family rest (k + 1)]
    simp only [SelectedOnHistory, and_true, iff_self]
  | Sum.inr pulse :: rest, k => by
    rw [VaryingSelectedOnHistory,
      varyingSelectedOnHistory_const_iff model capacity family rest (k + 1)]
    simp only [SelectedOnHistory, and_true, iff_self]

/-- **One event moves the selected moments by at most `B σ d`**, with `d` the duration of the event,
zero for a split or pulse: the one-event case of
`EndToEndSelectionLaw.norm_selectedHistory_sub_propagator_le`.

Assumes: `SelectedOnHistory model capacity family [event] k`. -/
theorem norm_event_sub_propagator_le (model : SelectionModel Deme Locus Allele) {σ : ℝ}
    (hσ : 0 ≤ σ) (hfit : ∀ i b, 0 ≤ model.fitness i b ∧ model.fitness i b ≤ σ)
    (capacity : Locus → ℕ)
    (family : ℕ → ℝ → ExpFunctional (Deme → FiniteReportLaw (FullHaplotype Locus Allele)))
    (event : (NeutralRates Deme Locus Allele × ℝ≥0) ⊕ PulseMatrix Deme) (k : ℕ)
    (hevent : SelectedOnHistory model capacity family [event] k) :
    ‖expectedMomentVector capacity (family (k + 1)) 0
        - eventPropagator capacity event *ᵥ expectedMomentVector capacity (family k) 0‖
      ≤ (∑ ℓ, capacity ℓ : ℕ) * σ * epochDuration [event] := by
  have h := norm_selectedHistory_sub_propagator_le model hσ hfit capacity family [event] k hevent
  rwa [List.length_singleton, historyEventPropagator, historyEventPropagator, Matrix.one_mul] at h

/-- **Selection with a table per event moves the moments of a history by at most
`B Σ_k σ_k d_k`.** Along a history of epochs, splits and pulses, families selected during the
`k`-th event with fitnesses in `[0, σ_k]` end with expected budget-respecting configuration moments
within `B Σ_k σ_k d_k` in sup norm of the neutral chronological propagator applied to their initial
moments, with `B = Σ_ℓ n_ℓ` and `d_k` the duration of the `k`-th event.

Assumes: `VaryingSelectedOnHistory models capacity family events k`. -/
theorem norm_varyingHistory_sub_propagator_le (models : ℕ → SelectionModel Deme Locus Allele)
    {σ : ℕ → ℝ} (hσ : ∀ k, 0 ≤ σ k)
    (hfit : ∀ k i b, 0 ≤ (models k).fitness i b ∧ (models k).fitness i b ≤ σ k)
    (capacity : Locus → ℕ)
    (family : ℕ → ℝ → ExpFunctional (Deme → FiniteReportLaw (FullHaplotype Locus Allele))) :
    ∀ (events : List ((NeutralRates Deme Locus Allele × ℝ≥0) ⊕ PulseMatrix Deme)) (k : ℕ),
      VaryingSelectedOnHistory models capacity family events k →
      ‖expectedMomentVector capacity (family (k + events.length)) 0
          - historyEventPropagator capacity events *ᵥ expectedMomentVector capacity (family k) 0‖
        ≤ (∑ ℓ, capacity ℓ : ℕ) * weightedSelection σ events k
  | [], k, _ => by
    simp [historyEventPropagator, weightedSelection]
  | event :: rest, k, hhistory => by
    obtain ⟨hevent, hrest⟩ := hhistory
    have hlength : k + (event :: rest).length = k + 1 + rest.length := by
      rw [List.length_cons]
      omega
    rw [hlength, historyEventPropagator, ← Matrix.mulVec_mulVec, weightedSelection]
    exact (norm_sub_mulVec_le (historyEventPropagator_substochastic capacity rest)
      (norm_varyingHistory_sub_propagator_le models hσ hfit capacity family rest (k + 1) hrest)
      (norm_event_sub_propagator_le (models k) (hσ k) (hfit k) capacity family event k
        hevent)).trans_eq (by ring)

/-- **The one-table law is the constant case.** With one model for every event, fitnesses in
`[0, σ]` and total epoch duration `T`, `norm_varyingHistory_sub_propagator_le` gives the bound
`B σ T` of `EndToEndSelectionLaw.norm_selectedHistory_sub_propagator_le`.

Assumes: `SelectedOnHistory model capacity family events k`. -/
theorem norm_selectedHistory_sub_propagator_le_of_const (model : SelectionModel Deme Locus Allele)
    {σ : ℝ} (hσ : 0 ≤ σ) (hfit : ∀ i b, 0 ≤ model.fitness i b ∧ model.fitness i b ≤ σ)
    (capacity : Locus → ℕ)
    (family : ℕ → ℝ → ExpFunctional (Deme → FiniteReportLaw (FullHaplotype Locus Allele)))
    (events : List ((NeutralRates Deme Locus Allele × ℝ≥0) ⊕ PulseMatrix Deme)) (k : ℕ)
    (hhistory : SelectedOnHistory model capacity family events k) :
    ‖expectedMomentVector capacity (family (k + events.length)) 0
        - historyEventPropagator capacity events *ᵥ expectedMomentVector capacity (family k) 0‖
      ≤ (∑ ℓ, capacity ℓ : ℕ) * σ * epochDuration events := by
  have h := norm_varyingHistory_sub_propagator_le (fun _ ↦ model) (σ := fun _ ↦ σ) (fun _ ↦ hσ)
    (fun _ ↦ hfit) capacity family events k
    ((varyingSelectedOnHistory_const_iff model capacity family events k).mpr hhistory)
  rwa [weightedSelection_const, ← mul_assoc] at h

/-! ## Portability -/

/-- **Portability under selection with a table per event, with an explicit error bar.** Along a
history selected during the `k`-th event with fitnesses in `[0, σ_k]`, where the expected target
denominator and source numerator are at least `δ > 0` under the selected family and at the neutral
chronological propagation `m₀` of the initial budget-4 moments, the portability of expected
accuracies differs from the portability of `m₀` by at most
`4 ‖a‖₁ ‖b‖₁ ‖c‖₁ ‖d‖₁ / δ⁴ · 4 |L| Σ_k σ_k d_k`, with `a, b, c, d` the coefficient vectors of the
target numerator, source denominator, target denominator and source numerator.

Assumes: `VaryingSelectedOnHistory models (fun _ ↦ 4) family events 0`. -/
theorem abs_varyingPortability_sub_neutral_le (ℓ₀ : Locus)
    (models : ℕ → SelectionModel Deme Locus Allele) {σ : ℕ → ℝ} (hσ : ∀ k, 0 ≤ σ k)
    (hfit : ∀ k i b, 0 ≤ (models k).fitness i b ∧ (models k).fitness i b ≤ σ k)
    (family : ℕ → ℝ → ExpFunctional (Deme → FiniteReportLaw (FullHaplotype Locus Allele)))
    (events : List ((NeutralRates Deme Locus Allele × ℝ≥0) ⊕ PulseMatrix Deme))
    (hhistory : VaryingSelectedOnHistory models (fun _ ↦ 4) family events 0)
    (source target : Deme) (score outcome : FullHaplotype Locus Allele → ℝ) {δ : ℝ}
    (hδ : 0 < δ)
    (htarget : δ ≤ family events.length 0 fun law ↦
      correlationDenominator (law target) score outcome)
    (hsource : δ ≤ family events.length 0 fun law ↦
      correlationNumerator (law source) score outcome)
    (htarget₀ : δ ≤ budgetCoefficients ℓ₀ (fun _ ↦ 4) (denominatorPolynomial target score outcome)
      ⬝ᵥ (historyEventPropagator (fun _ ↦ 4) events
        *ᵥ expectedMomentVector (fun _ ↦ 4) (family 0) 0))
    (hsource₀ : δ ≤ budgetCoefficients ℓ₀ (fun _ ↦ 4) (numeratorPolynomial source score outcome)
      ⬝ᵥ (historyEventPropagator (fun _ ↦ 4) events
        *ᵥ expectedMomentVector (fun _ ↦ 4) (family 0) 0)) :
    |selectedPortability family events.length source target score outcome
        - momentPortability ℓ₀ source target score outcome
          (historyEventPropagator (fun _ ↦ 4) events
            *ᵥ expectedMomentVector (fun _ ↦ 4) (family 0) 0)|
      ≤ 4 * (∑ i, |budgetCoefficients ℓ₀ (fun _ ↦ 4) (numeratorPolynomial target score outcome) i|)
          * (∑ i, |budgetCoefficients ℓ₀ (fun _ ↦ 4)
              (denominatorPolynomial source score outcome) i|)
          * (∑ i, |budgetCoefficients ℓ₀ (fun _ ↦ 4)
              (denominatorPolynomial target score outcome) i|)
          * (∑ i, |budgetCoefficients ℓ₀ (fun _ ↦ 4) (numeratorPolynomial source score outcome) i|)
          / δ ^ 4 * (4 * Fintype.card Locus * weightedSelection σ events 0) := by
  have hmoments := norm_varyingHistory_sub_propagator_le models hσ hfit (fun _ ↦ 4) family events
    0 hhistory
  rw [zero_add, sum_four_capacity] at hmoments
  rw [expectation_correlationDenominator ℓ₀] at htarget
  rw [expectation_correlationNumerator ℓ₀] at hsource
  have hbox : ∀ v : BudgetConfiguration Deme Locus Allele (fun _ ↦ 4) → ℝ, ‖v‖ ≤ 1 →
      ∀ η, |v η| ≤ 1 := fun v hv η ↦ by
    simpa only [Real.norm_eq_abs] using (norm_le_pi_norm v η).trans hv
  have hV := norm_expectedMomentVector_le_one (fun _ ↦ 4) (family events.length) 0
  have hm₀ := (norm_mulVec_le_of_substochastic
    (historyEventPropagator_substochastic (fun _ ↦ 4) events)
      (expectedMomentVector (fun _ ↦ 4) (family 0) 0)).trans
        (norm_expectedMomentVector_le_one (fun _ ↦ 4) (family 0) 0)
  have hcross := abs_crossRatio_sub_le
    (fun w : {w : BudgetConfiguration Deme Locus Allele (fun _ ↦ 4) → ℝ // ∀ i, |w i| ≤ 1} ↦
      w.1) hδ (fun w i ↦ w.2 i)
    (budgetCoefficients ℓ₀ (fun _ ↦ 4) (numeratorPolynomial target score outcome))
    (budgetCoefficients ℓ₀ (fun _ ↦ 4) (denominatorPolynomial source score outcome))
    (budgetCoefficients ℓ₀ (fun _ ↦ 4) (denominatorPolynomial target score outcome))
    (budgetCoefficients ℓ₀ (fun _ ↦ 4) (numeratorPolynomial source score outcome))
    (RealizationBody.mem_realizationBody_of_range _ ⟨_, hbox _ hV⟩)
    (RealizationBody.mem_realizationBody_of_range _ ⟨_, hbox _ hm₀⟩) htarget hsource htarget₀
    hsource₀
  rw [selectedPortability_eq_momentPortability ℓ₀]
  refine hcross.trans ?_
  rw [one_pow, mul_one]
  exact mul_le_mul_of_nonneg_left hmoments (by positivity)

end

end Descent.Portability.SelectionHistoryVaryingFitness
