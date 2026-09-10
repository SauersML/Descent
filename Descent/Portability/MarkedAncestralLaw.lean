/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.AncestralEpochLaw

assert_below Descent.Decision Descent.Program

/-!
Ancestry proposal histories retaining the actual migration, common-ancestor,
and recombination channels. Every event carries the membership and material
conditions required by its current ancestral state. The history probability
is constructed from the demographic rates, including explicit null proposals.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.MarkedAncestralLaw

open Coalescent.FiniteGenomeAncestry AncestralEventLaw AncestralEpochLaw FiniteReportLaw

variable {D L n : ℕ}

def Trace : ℕ → State D L n → Type
  | 0, _ => PUnit
  | count + 1, start =>
      (event : Option (Channel start)) × Trace count (proposalNext start event)

noncomputable instance traceFintype : (count : ℕ) → (start : State D L n) →
    Fintype (Trace count start)
  | 0, _ => inferInstanceAs (Fintype PUnit)
  | count + 1, start => by
      letI : ∀ event : Option (Channel start), Fintype (Trace count (proposalNext start event)) :=
        fun event ↦ traceFintype count (proposalNext start event)
      exact inferInstanceAs (Fintype ((event : Option (Channel start)) ×
        Trace count (proposalNext start event)))

noncomputable def traceMass (rates : Rates D L) : {count : ℕ} →
    (start : State D L n) → Trace count start → ℝ
  | 0, _, _ => 1
  | _count + 1, start, ⟨event, rest⟩ =>
      (proposalLaw rates start).mass event * traceMass rates (proposalNext start event) rest

theorem traceMass_nonneg (rates : Rates D L) {count : ℕ}
    (start : State D L n) (trace : Trace count start) : 0 ≤ traceMass rates start trace := by
  induction count generalizing start with
  | zero => exact zero_le_one
  | succ count ih =>
      exact mul_nonneg ((proposalLaw rates start).mass_nonneg trace.1)
        (ih (proposalNext start trace.1) trace.2)

theorem traceMass_sum (rates : Rates D L) (count : ℕ) (start : State D L n) :
    (∑ trace : Trace count start, traceMass rates start trace) = 1 := by
  induction count generalizing start with
  | zero => simp [Trace, traceMass]
  | succ count ih =>
      change (∑ trace : (event : Option (Channel start)) ×
        Trace count (proposalNext start event),
        (proposalLaw rates start).mass trace.1 *
          traceMass rates (proposalNext start trace.1) trace.2) = 1
      rw [Fintype.sum_sigma]
      simp only [← Finset.mul_sum, ih, mul_one, FiniteReportLaw.mass_sum]

noncomputable def traceLaw (rates : Rates D L) (count : ℕ) (start : State D L n) :
    FiniteReportLaw (Trace count start) where
  mass := traceMass rates start
  mass_nonneg := traceMass_nonneg rates start
  mass_sum := traceMass_sum rates count start

noncomputable def terminal : {count : ℕ} → {start : State D L n} → Trace count start →
    State D L n
  | 0, start, _ => start
  | _count + 1, _start, ⟨_event, rest⟩ => terminal rest

/-- Summing marked histories reconstructs the same next-event mixture as the
ancestry kernel, including event types with the same resulting configuration. -/
theorem trace_expectation_succ (rates : Rates D L) (count : ℕ) (start : State D L n)
    (readout : Trace (count + 1) start → ℝ) :
    (traceLaw rates (count + 1) start).expectation readout =
      (proposalLaw rates start).expectation (fun event ↦
        (traceLaw rates count (proposalNext start event)).expectation
          (fun rest ↦ readout ⟨event, rest⟩)) := by
  unfold expectation traceLaw
  change (∑ trace : (event : Option (Channel start)) ×
    Trace count (proposalNext start event),
    ((proposalLaw rates start).mass trace.1 *
      traceMass rates (proposalNext start trace.1) trace.2) * readout trace) = _
  rw [Fintype.sum_sigma]
  simp only [Finset.mul_sum, mul_assoc]

private theorem backward_eq_iterate (rates : Rates D L) (count : ℕ)
    (readout : State D L n → ℝ) :
    ExactFiniteHistoryLaw.backwardReadout (fun _ ↦ proposalKernel rates) count readout =
      (fun f s ↦ (proposalKernel rates s).expectation f)^[count] readout := by
  induction count generalizing readout with
  | zero => rfl
  | succ count ih =>
      rw [ExactFiniteHistoryLaw.backwardReadout, ih, Function.iterate_succ_apply]

private theorem trace_terminal_iterate (rates : Rates D L) (count : ℕ)
    (start : State D L n) (readout : State D L n → ℝ) :
    (traceLaw rates count start).expectation (fun trace ↦ readout (terminal trace)) =
      (fun f s ↦ (proposalKernel rates s).expectation f)^[count] readout start := by
  induction count generalizing start with
  | zero => simp [traceLaw, expectation, Trace, traceMass, terminal]
  | succ count ih =>
      rw [trace_expectation_succ, Function.iterate_succ_apply']
      change (proposalLaw rates start).expectation (fun event ↦
        (traceLaw rates count (proposalNext start event)).expectation
          (fun rest ↦ readout (terminal rest))) = _
      simp_rw [ih]
      exact (expectation_pushforward (proposalLaw rates start) (proposalNext start) _).symm

/-- Forgetting the event marks recovers exactly the previously constructed
ancestral configuration law. Marks add genealogy information without changing
any terminal configuration probabilities. -/
theorem trace_terminal_expectation (rates : Rates D L) (count : ℕ)
    (start : State D L n) (readout : State D L n → ℝ) :
    (traceLaw rates count start).expectation (fun trace ↦ readout (terminal trace)) =
      (steps rates start count).expectation readout := by
  rw [steps, ExactFiniteHistoryLaw.expectation_propagate, expectation_pointMass,
    backward_eq_iterate, trace_terminal_iterate]

/-- Complete marked histories have total Poisson-weighted probability one. -/
theorem marked_epoch_mass_sum (rates : Rates D L) (start : State D L n)
    (duration : NNReal) :
    (∑' count, ∑ trace : Trace count start,
      ProbabilityTheory.poissonPMFReal (poissonParameter (n := n) rates duration) count *
        traceMass rates start trace) = 1 := by
  simp only [← Finset.mul_sum, traceMass_sum, mul_one]
  exact (ProbabilityTheory.poissonPMFRealSum _).tsum_eq

end Descent.Portability.MarkedAncestralLaw
