/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.AncestralEventLaw
import Mathlib.Probability.Distributions.Poisson

assert_below Descent.Decision Descent.Program

/-!
Uniformized finite-duration ancestry epochs. The Poisson mixture is normalized
from the rate-derived ancestral kernel, and its expectation is an absolutely
convergent series. The series evaluates the active ancestral configuration;
mutation and genealogy-dependent readouts require retaining the event history.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.AncestralEpochLaw

open Coalescent.FiniteGenomeAncestry AncestralEventLaw FiniteReportLaw ProbabilityTheory
open scoped NNReal

variable {D L n : ℕ}

noncomputable def steps (rates : Rates D L) (start : State D L n) (count : ℕ) :
    FiniteReportLaw (State D L n) :=
  ExactFiniteHistoryLaw.propagate (pointMass start) (fun _ ↦ proposalKernel rates) count

noncomputable def poissonParameter (rates : Rates D L) (duration : ℝ≥0) : ℝ≥0 :=
  ⟨dominatingRate (n := n) rates * duration,
    mul_nonneg (dominatingRate_pos rates).le duration.property⟩

private theorem mass_le_one {A : Type*} [Fintype A] (p : FiniteReportLaw A) (a : A) :
    p.mass a ≤ 1 := by
  rw [← p.mass_sum]
  exact Finset.single_le_sum (fun a _ ↦ p.mass_nonneg a) (Finset.mem_univ a)

private theorem coordinate_summable (rates : Rates D L) (start : State D L n)
    (duration : ℝ≥0) (target : State D L n) :
    Summable (fun count ↦ poissonPMFReal (poissonParameter (n := n) rates duration) count *
      (steps rates start count).mass target) := by
  apply (poissonPMFRealSum (poissonParameter (n := n) rates duration)).summable.of_nonneg_of_le
  · intro count
    exact mul_nonneg poissonPMFReal_nonneg ((steps rates start count).mass_nonneg target)
  · intro count
    exact mul_le_of_le_one_right poissonPMFReal_nonneg (mass_le_one _ target)

noncomputable def epochLaw (rates : Rates D L) (start : State D L n) (duration : ℝ≥0) :
    FiniteReportLaw (State D L n) where
  mass := fun target ↦ ∑' count,
    poissonPMFReal (poissonParameter (n := n) rates duration) count *
      (steps rates start count).mass target
  mass_nonneg := fun target ↦ tsum_nonneg (fun count ↦
    mul_nonneg poissonPMFReal_nonneg ((steps rates start count).mass_nonneg target))
  mass_sum := by
    rw [← Summable.tsum_finsetSum (fun target _ ↦ coordinate_summable rates start duration target)]
    simp only [← Finset.mul_sum, FiniteReportLaw.mass_sum, mul_one]
    exact (poissonPMFRealSum _).tsum_eq

/-- The duration-dependent probability law is evaluated after ancestral events
have been applied, preserving the dependence of the readout on the configuration. -/
theorem epoch_expectation (rates : Rates D L) (start : State D L n)
    (duration : ℝ≥0) (readout : State D L n → ℝ) :
    (epochLaw rates start duration).expectation readout =
      ∑' count, poissonPMFReal (poissonParameter (n := n) rates duration) count *
        (steps rates start count).expectation readout := by
  unfold expectation epochLaw
  simp only [← tsum_mul_right]
  rw [← Summable.tsum_finsetSum
    (fun target _ ↦ (coordinate_summable rates start duration target).mul_right (readout target))]
  apply tsum_congr
  intro count
  simp only [Finset.mul_sum, mul_assoc]

private theorem expectation_bounds {A : Type*} [Fintype A]
    (p : FiniteReportLaw A) (readout : A → ℝ) (bound : ℝ)
    (hb : ∀ a, 0 ≤ readout a ∧ readout a ≤ bound) :
    0 ≤ p.expectation readout ∧ p.expectation readout ≤ bound := by
  constructor
  · exact Finset.sum_nonneg (fun a _ ↦ mul_nonneg (p.mass_nonneg a) (hb a).1)
  · calc
      p.expectation readout ≤ ∑ a, p.mass a * bound :=
        Finset.sum_le_sum (fun a _ ↦ mul_le_mul_of_nonneg_left (hb a).2 (p.mass_nonneg a))
      _ = bound := by rw [← Finset.sum_mul, p.mass_sum, one_mul]

/-- This includes any fixed finite-sample accuracy readout in `[0,1]`; a ratio
readout needs its own bound before the same certificate can be used. -/
theorem epoch_expectation_bounds (rates : Rates D L) (start : State D L n)
    (duration : ℝ≥0) (readout : State D L n → ℝ) (bound : ℝ)
    (hb : ∀ target, 0 ≤ readout target ∧ readout target ≤ bound) :
    0 ≤ (epochLaw rates start duration).expectation readout ∧
      (epochLaw rates start duration).expectation readout ≤ bound :=
  expectation_bounds _ readout bound hb

private theorem readout_summable (rates : Rates D L) (start : State D L n)
    (duration : ℝ≥0) (readout : State D L n → ℝ) :
    Summable (fun count ↦ poissonPMFReal (poissonParameter (n := n) rates duration) count *
      (steps rates start count).expectation readout) := by
  have h := hasSum_sum (fun target (_ : target ∈ (Finset.univ : Finset (State D L n))) ↦
    ((coordinate_summable rates start duration target).mul_right (readout target)).hasSum)
  simpa only [expectation, Finset.mul_sum, mul_assoc] using h.summable

/-- Exact missing mass after retaining proposal counts strictly below `cutoff`. -/
noncomputable def tailProbability (rates : Rates D L) (duration : ℝ≥0) (cutoff : ℕ) : ℝ :=
  ∑' count, poissonPMFReal (poissonParameter (n := n) rates duration) (count + cutoff)

theorem tailProbability_eq_one_sub (rates : Rates D L) (duration : ℝ≥0) (cutoff : ℕ) :
    tailProbability (n := n) rates duration cutoff = 1 -
      ∑ count ∈ Finset.range cutoff,
        poissonPMFReal (poissonParameter (n := n) rates duration) count := by
  have hs := (poissonPMFRealSum (poissonParameter (n := n) rates duration)).summable
  have h := hs.sum_add_tsum_nat_add cutoff
  rw [(poissonPMFRealSum _).tsum_eq] at h
  unfold tailProbability
  linarith

/-- A rigorous expectation interval from finitely many proposal-count terms.
The remainder is controlled by an explicit Poisson tail, without replacing
linked ancestry by independent loci or low-order moments. -/
theorem epoch_expectation_truncation (rates : Rates D L) (start : State D L n)
    (duration : ℝ≥0) (readout : State D L n → ℝ) (bound : ℝ)
    (hb : ∀ target, 0 ≤ readout target ∧ readout target ≤ bound) (cutoff : ℕ) :
    let partialSum := ∑ count ∈ Finset.range cutoff,
      poissonPMFReal (poissonParameter (n := n) rates duration) count *
        (steps rates start count).expectation readout
    0 ≤ (epochLaw rates start duration).expectation readout - partialSum ∧
      (epochLaw rates start duration).expectation readout - partialSum ≤
        tailProbability (n := n) rates duration cutoff * bound := by
  dsimp only
  rw [epoch_expectation]
  have hs := readout_summable rates start duration readout
  have hsplit := hs.sum_add_tsum_nat_add cutoff
  rw [← hsplit]
  simp only [add_sub_cancel_left]
  constructor
  · exact tsum_nonneg (fun count ↦ mul_nonneg poissonPMFReal_nonneg
      (expectation_bounds (steps rates start (count + cutoff)) readout bound hb).1)
  · unfold tailProbability
    rw [← tsum_mul_right]
    apply Summable.tsum_le_tsum
    · intro count
      exact mul_le_mul_of_nonneg_left
        (expectation_bounds (steps rates start (count + cutoff)) readout bound hb).2
        poissonPMFReal_nonneg
    · exact (summable_nat_add_iff (f := fun count ↦
        poissonPMFReal (poissonParameter (n := n) rates duration) count *
          (steps rates start count).expectation readout) cutoff).mpr hs
    · exact ((summable_nat_add_iff
        (f := poissonPMFReal (poissonParameter (n := n) rates duration)) cutoff).mpr
          (poissonPMFRealSum (poissonParameter (n := n) rates duration)).summable).mul_right bound

/-- The Poisson generating function, used to identify the waiting law after
null proposals are suppressed. -/
theorem poisson_generating_function (parameter : ℝ≥0) (z : ℝ) :
    (∑' count, poissonPMFReal parameter count * z ^ count) =
      Real.exp ((parameter : ℝ) * (z - 1)) := by
  calc
    (∑' count, poissonPMFReal parameter count * z ^ count) =
        Real.exp (-(parameter : ℝ)) *
          ∑' count, ((parameter : ℝ) * z) ^ count / (Nat.factorial count : ℝ) := by
      rw [← tsum_mul_left]
      apply tsum_congr
      intro count
      simp only [poissonPMFReal, mul_pow]
      ring
    _ = Real.exp (-(parameter : ℝ)) * Real.exp ((parameter : ℝ) * z) := by
      rw [Real.exp_eq_exp_ℝ]
      rw [(NormedSpace.expSeries_div_hasSum_exp ℝ ((parameter : ℝ) * z)).tsum_eq]
    _ = Real.exp ((parameter : ℝ) * (z - 1)) := by
      rw [← Real.exp_add]
      congr 1
      ring

/-- Suppressing null proposals recovers the exponential waiting probability
with the total ancestral event rate, including the zero-rate absorbing case. -/
theorem no_event_probability (rates : Rates D L) (start : State D L n)
    (duration : ℝ≥0) :
    (∑' count, poissonPMFReal (poissonParameter (n := n) rates duration) count *
      (1 - totalRate rates start / dominatingRate (n := n) rates) ^ count) =
      Real.exp (-totalRate rates start * (duration : ℝ)) := by
  rw [poisson_generating_function]
  congr 1
  change (dominatingRate (n := n) rates * (duration : ℝ)) *
    (1 - totalRate rates start / dominatingRate (n := n) rates - 1) = _
  have hn := ne_of_gt (dominatingRate_pos (n := n) rates)
  field_simp
  ring

/-- Complete proposal histories retain ancestral configurations that an endpoint
alone would discard. Waiting times are a separate part of the genealogy law. -/
noncomputable def proposalHistoryMass (rates : Rates D L) (start : State D L n)
    {count : ℕ} (path : ExactFiniteHistoryLaw.Path (State D L n) count) : ℝ :=
  ExactFiniteHistoryLaw.pathMass (pointMass start) (fun _ ↦ proposalKernel rates) path

theorem proposalHistoryMass_nonneg (rates : Rates D L) (start : State D L n)
    {count : ℕ} (path : ExactFiniteHistoryLaw.Path (State D L n) count) :
    0 ≤ proposalHistoryMass rates start path := by
  induction count with
  | zero => exact (pointMass start).mass_nonneg path
  | succ count ih =>
    exact mul_nonneg (ih path.1)
      ((proposalKernel rates (ExactFiniteHistoryLaw.terminal path.1)).mass_nonneg path.2)

theorem proposalHistoryMass_sum (rates : Rates D L) (start : State D L n) (count : ℕ) :
    (∑ path : ExactFiniteHistoryLaw.Path (State D L n) count,
      proposalHistoryMass rates start path) = 1 :=
  ExactFiniteHistoryLaw.path_mass_sum_one (pointMass start) (fun _ ↦ proposalKernel rates) count

/-- Explicit normalization of the countable distribution of complete proposal
histories, rather than assuming a supplied probability law on genealogies. -/
theorem epoch_history_mass_sum (rates : Rates D L) (start : State D L n) (duration : ℝ≥0) :
    (∑' count, ∑ path : ExactFiniteHistoryLaw.Path (State D L n) count,
      poissonPMFReal (poissonParameter (n := n) rates duration) count *
        proposalHistoryMass rates start path) = 1 := by
  simp only [← Finset.mul_sum, proposalHistoryMass_sum, mul_one]
  exact (poissonPMFRealSum _).tsum_eq

theorem epoch_history_terminal_expectation (rates : Rates D L) (start : State D L n)
    (duration : ℝ≥0) (readout : State D L n → ℝ) :
    (∑' count, ∑ path : ExactFiniteHistoryLaw.Path (State D L n) count,
      poissonPMFReal (poissonParameter (n := n) rates duration) count *
        (proposalHistoryMass rates start path * readout (ExactFiniteHistoryLaw.terminal path))) =
      (epochLaw rates start duration).expectation readout := by
  rw [epoch_expectation]
  apply tsum_congr
  intro count
  rw [← Finset.mul_sum]
  congr 1
  exact ExactFiniteHistoryLaw.path_sum_eq_expectation
    (pointMass start) (fun _ ↦ proposalKernel rates) count readout

inductive Instruction (D L : ℕ) where
  | epoch (rates : Rates D L) (duration : ℝ≥0)
  | relocate (destination : Fin D → Fin D)

/-- Backward-time demographic instructions, with rates and durations explicit.
No transition probability law is supplied by the caller. -/
noncomputable def historyLaw : List (Instruction D L) → State D L n →
    FiniteReportLaw (State D L n)
  | [], start => pointMass start
  | .epoch rates duration :: rest, start =>
      (epochLaw rates start duration).bind (historyLaw rest)
  | .relocate destination :: rest, start => historyLaw rest (relabelDemes start destination)

noncomputable def historyExpectation : List (Instruction D L) →
    (State D L n → ℝ) → State D L n → ℝ
  | [], readout, start => readout start
  | .epoch rates duration :: rest, readout, start =>
      ∑' count, poissonPMFReal (poissonParameter (n := n) rates duration) count *
        (steps rates start count).expectation (historyExpectation rest readout)
  | .relocate destination :: rest, readout, start =>
      historyExpectation rest readout (relabelDemes start destination)

/-- The normalized ancestry law and the explicit nested Poisson series give
identical expectations for any finite sequence of these demographic events. -/
theorem history_expectation (instructions : List (Instruction D L))
    (start : State D L n) (readout : State D L n → ℝ) :
    (historyLaw instructions start).expectation readout =
      historyExpectation instructions readout start := by
  induction instructions generalizing start with
  | nil => exact expectation_pointMass start readout
  | cons instruction rest ih =>
    cases instruction with
    | epoch rates duration =>
      rw [historyLaw, expectation_bind]
      simp_rw [ih]
      exact epoch_expectation rates start duration (historyExpectation rest readout)
    | relocate destination => exact ih (relabelDemes start destination)

end Descent.Portability.AncestralEpochLaw
