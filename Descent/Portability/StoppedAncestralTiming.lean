/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.AncestralAbsorptionLaw
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Probability.Distributions.Exponential

assert_below Descent.Decision Descent.Program

/-!
Timing of genuinely stopped ancestral histories. Conditional on the proposal
marks and their first-completion index, waiting increments have the independent
exponential law at the dominating proposal rate. The completion time is random;
it is not a fixed-horizon ordered-uniform time draw.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.StoppedAncestralTiming

open Coalescent.FiniteGenomeAncestry AncestralEventLaw MarkedAncestralLaw
open AncestralAbsorptionLaw MeasureTheory ProbabilityTheory
open scoped NNReal

variable {D L n count : ℕ}

noncomputable def proposalWait (rates : Rates D L) : Measure ℝ :=
  expMeasure (dominatingRate (n := n) rates)

instance proposalWait_probability (rates : Rates D L) :
    IsProbabilityMeasure (proposalWait (n := n) rates) :=
  isProbabilityMeasure_expMeasure (dominatingRate_pos rates)

noncomputable def waitingLaw (rates : Rates D L) (count : ℕ) : Measure (Fin count → ℝ) :=
  Measure.pi fun _ ↦ proposalWait (n := n) rates

instance waitingLaw_probability (rates : Rates D L) (count : ℕ) :
    IsProbabilityMeasure (waitingLaw (n := n) rates count) := by
  unfold waitingLaw
  infer_instance

theorem proposalWait_nonneg (rates : Rates D L) :
    ∀ᵐ wait ∂proposalWait (n := n) rates, 0 ≤ wait := by
  apply ae_iff.mpr
  simp only [not_le]
  change proposalWait (n := n) rates (Set.Iio 0) = 0
  rw [proposalWait, expMeasure, gammaMeasure,
    withDensity_apply _ measurableSet_Iio]
  exact lintegral_gammaPDF_of_nonpos le_rfl

theorem waitingLaw_nonneg (rates : Rates D L) (count : ℕ) :
    ∀ᵐ waits ∂waitingLaw (n := n) rates count, ∀ i, 0 ≤ waits i := by
  rw [ae_all_iff]
  intro i
  have h := proposalWait_nonneg (n := n) rates
  have hm := measurePreserving_eval (fun _ : Fin count ↦ proposalWait (n := n) rates) i
  rw [← hm.map_eq] at h
  exact ae_of_ae_map hm.measurable.aemeasurable h

noncomputable def arrivalTimes (waits : Fin count → ℝ) (i : Fin count) : ℝ :=
  ∑ j ∈ Finset.Iic i, waits j

noncomputable def completionTime (waits : Fin count → ℝ) : ℝ := ∑ j, waits j

theorem arrivalTimes_measurable : Measurable (arrivalTimes (count := count)) := by
  apply measurable_pi_lambda
  intro i
  exact Finset.measurable_sum _ (fun j _ ↦ measurable_pi_apply j)

theorem completionTime_measurable : Measurable (completionTime (count := count)) :=
  Finset.measurable_sum _ (fun j _ ↦ measurable_pi_apply j)

theorem arrivalTimes_support (waits : Fin count → ℝ) (hw : ∀ i, 0 ≤ waits i) :
    Monotone (arrivalTimes waits) ∧
      ∀ i, arrivalTimes waits i ∈ Set.Icc 0 (completionTime waits) := by
  constructor
  · intro i j hij
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.Iic_subset_Iic.mpr hij)
    intro k _ _
    exact hw k
  · intro i
    constructor
    · exact Finset.sum_nonneg (fun j _ ↦ hw j)
    · exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun j _ _ ↦ hw j)

theorem waitingLaw_arrivals (rates : Rates D L) (count : ℕ) :
    ∀ᵐ waits ∂waitingLaw (n := n) rates count,
      0 ≤ completionTime waits ∧ Monotone (arrivalTimes waits) ∧
        ∀ i, arrivalTimes waits i ∈ Set.Icc 0 (completionTime waits) := by
  filter_upwards [waitingLaw_nonneg (n := n) rates count] with waits hw
  exact ⟨Finset.sum_nonneg (fun j _ ↦ hw j), arrivalTimes_support waits hw⟩

private theorem stoppingIndicator_pos_terminal {start : State D L n}
    (trace : Trace count start) (h : 0 < stoppingIndicator start trace) :
    (terminal trace).val = ∅ := by
  induction count generalizing start with
  | zero =>
      by_contra hne
      change start.val ≠ ∅ at hne
      simp [stoppingIndicator, unfinished, hne] at h
  | succ count ih =>
      rcases trace with ⟨event, rest⟩
      exact ih rest (pos_of_mul_pos_right h (unfinished_nonneg start))

/-- Histories that receive positive stopped probability really end at complete
ancestry; incomplete traces do not enter the complete-genotype expectation. -/
theorem stoppingTraceMass_pos_terminal (rates : Rates D L) {start : State D L n}
    (trace : Trace count start) (h : 0 < stoppingTraceMass rates start trace) :
    (terminal trace).val = ∅ :=
  stoppingIndicator_pos_terminal trace (pos_of_mul_pos_right h (traceMass_nonneg rates start trace))

/-- This count contribution is a subprobability expectation: its mass is the
probability of first completion at this count, not one. -/
noncomputable def stoppedCountExpectation (rates : Rates D L) (start : State D L n)
    (count : ℕ) (readout : Trace count start → (Fin count → ℝ) → ℝ) : ℝ :=
  ∑ trace, stoppingTraceMass rates start trace *
    ∫ waits, readout trace waits ∂waitingLaw (n := n) rates count

theorem stoppedCountExpectation_one (rates : Rates D L) (start : State D L n) (count : ℕ) :
    stoppedCountExpectation rates start count (fun _ _ ↦ 1) = completionMass rates start count := by
  simp only [stoppedCountExpectation, integral_const, measureReal_univ_eq_one, one_smul, mul_one]
  exact stoppingTraceMass_sum rates count start

noncomputable def stoppedExpectation (rates : Rates D L) (start : State D L n)
    (readout : (count : ℕ) → Trace count start → (Fin count → ℝ) → ℝ) : ℝ :=
  ∑' count, stoppedCountExpectation rates start count (readout count)

/-- A normalized marked-and-timed law for complete ancestry in an isolated
final population, retaining the original deme type and recombination rates. -/
theorem stoppedExpectation_one (rates : Rates D L) (deme : Fin D) (start : State D L n)
    (hs : SampleComplete start) (hsupported : SupportedAt deme start)
    (hisolated : ∀ destination, rates.migration deme destination = 0) :
    stoppedExpectation rates start (fun _ _ _ ↦ 1) = 1 := by
  simp only [stoppedExpectation, stoppedCountExpectation_one]
  exact (completionMass_hasSum rates deme start hs hsupported hisolated).tsum_eq

theorem stoppedCountExpectation_bounds (rates : Rates D L) (start : State D L n) (count : ℕ)
    (readout : Trace count start → (Fin count → ℝ) → ℝ)
    (hmeas : ∀ trace, Measurable (readout trace)) (bound : ℝ)
    (hb : ∀ trace, ∀ᵐ waits ∂waitingLaw (n := n) rates count,
      0 ≤ readout trace waits ∧ readout trace waits ≤ bound) :
    0 ≤ stoppedCountExpectation rates start count readout ∧
      stoppedCountExpectation rates start count readout ≤
        completionMass rates start count * bound := by
  have hi (trace : Trace count start) :
      Integrable (readout trace) (waitingLaw (n := n) rates count) := by
    apply (integrable_const bound).mono' (hmeas trace).aestronglyMeasurable
    filter_upwards [hb trace] with waits h
    simpa only [Real.norm_eq_abs, abs_of_nonneg h.1] using h.2
  have hbounds (trace : Trace count start) :
      0 ≤ (∫ waits, readout trace waits ∂waitingLaw (n := n) rates count) ∧
        (∫ waits, readout trace waits ∂waitingLaw (n := n) rates count) ≤ bound := by
    constructor
    · exact integral_nonneg_of_ae ((hb trace).mono (fun _ h ↦ h.1))
    · simpa using integral_mono_ae (hi trace) (integrable_const bound)
        ((hb trace).mono (fun _ h ↦ h.2))
  constructor
  · exact Finset.sum_nonneg (fun trace _ ↦
      mul_nonneg (stoppingTraceMass_nonneg rates start trace) (hbounds trace).1)
  · calc
      stoppedCountExpectation rates start count readout ≤
          ∑ trace, stoppingTraceMass rates start trace * bound :=
        Finset.sum_le_sum (fun trace _ ↦ mul_le_mul_of_nonneg_left
          (hbounds trace).2 (stoppingTraceMass_nonneg rates start trace))
      _ = completionMass rates start count * bound := by
        rw [← Finset.sum_mul, stoppingTraceMass_sum]

theorem stoppedExpectation_summable (rates : Rates D L) (deme : Fin D) (start : State D L n)
    (hs : SampleComplete start) (hsupported : SupportedAt deme start)
    (hisolated : ∀ destination, rates.migration deme destination = 0)
    (readout : (count : ℕ) → Trace count start → (Fin count → ℝ) → ℝ)
    (hmeas : ∀ count trace, Measurable (readout count trace)) (bound : ℝ)
    (hb : ∀ count trace, ∀ᵐ waits ∂waitingLaw (n := n) rates count,
      0 ≤ readout count trace waits ∧ readout count trace waits ≤ bound) :
    Summable (fun count ↦ stoppedCountExpectation rates start count (readout count)) := by
  apply ((completionMass_hasSum rates deme start hs hsupported hisolated).summable.mul_right
    bound).of_nonneg_of_le
  · intro count
    exact (stoppedCountExpectation_bounds rates start count _ (hmeas count) bound (hb count)).1
  · intro count
    exact (stoppedCountExpectation_bounds rates start count _ (hmeas count) bound (hb count)).2

/-- Exact tail mass after first-completion indices through `cutoff` are kept. -/
theorem completion_tail (rates : Rates D L) (deme : Fin D) (start : State D L n)
    (hs : SampleComplete start) (hsupported : SupportedAt deme start)
    (hisolated : ∀ destination, rates.migration deme destination = 0) (cutoff : ℕ) :
    (∑' count, completionMass rates start (count + (cutoff + 1))) =
      survival rates cutoff start := by
  have hsum := completionMass_hasSum rates deme start hs hsupported hisolated
  have hsplit := hsum.summable.sum_add_tsum_nat_add (cutoff + 1)
  rw [hsum.tsum_eq, completionMass_partial_sum] at hsplit
  linarith

/-- Complete ancestral histories can be truncated with a demographic-rate
certificate. The uncertainty is bounded by the readout bound times the exact
unfinished-ancestry probability, which has a proved geometric upper bound. -/
theorem stoppedExpectation_truncation (rates : Rates D L) (deme : Fin D) (start : State D L n)
    (hs : SampleComplete start) (hsupported : SupportedAt deme start)
    (hisolated : ∀ destination, rates.migration deme destination = 0)
    (readout : (count : ℕ) → Trace count start → (Fin count → ℝ) → ℝ)
    (hmeas : ∀ count trace, Measurable (readout count trace)) (bound : ℝ)
    (hb : ∀ count trace, ∀ᵐ waits ∂waitingLaw (n := n) rates count,
      0 ≤ readout count trace waits ∧ readout count trace waits ≤ bound) (cutoff : ℕ) :
    let partialSum := ∑ count ∈ Finset.range (cutoff + 1),
      stoppedCountExpectation rates start count (readout count)
    0 ≤ stoppedExpectation rates start readout - partialSum ∧
      stoppedExpectation rates start readout - partialSum ≤
        survival rates cutoff start * bound := by
  dsimp only
  have hsum := stoppedExpectation_summable rates deme start hs hsupported hisolated
    readout hmeas bound hb
  rw [stoppedExpectation, ← hsum.sum_add_tsum_nat_add (cutoff + 1)]
  simp only [add_sub_cancel_left]
  constructor
  · exact tsum_nonneg (fun count ↦
      (stoppedCountExpectation_bounds rates start (count + (cutoff + 1)) _
        (hmeas _) bound (hb _)).1)
  · rw [← completion_tail rates deme start hs hsupported hisolated cutoff, ← tsum_mul_right]
    apply Summable.tsum_le_tsum
    · intro count
      exact (stoppedCountExpectation_bounds rates start (count + (cutoff + 1)) _
        (hmeas _) bound (hb _)).2
    · exact (summable_nat_add_iff (f := fun count ↦
        stoppedCountExpectation rates start count (readout count)) (cutoff + 1)).mpr hsum
    · exact ((summable_nat_add_iff (f := completionMass rates start) (cutoff + 1)).mpr
        (completionMass_hasSum rates deme start hs hsupported hisolated).summable).mul_right bound

end Descent.Portability.StoppedAncestralTiming
