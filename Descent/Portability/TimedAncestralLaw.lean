/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.MarkedAncestralLaw
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

assert_below Descent.Decision Descent.Program

/-!
Proposal times in a finite ancestry epoch. Independent uniform draws are
sorted and scaled by the epoch duration. This retains event times alongside
the discrete ancestral histories, including zero-duration epochs.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.TimedAncestralLaw

open MeasureTheory ProbabilityTheory AncestralEpochLaw FiniteReportLaw
open scoped NNReal

variable {count : ℕ}

noncomputable def sortedValues (values : Fin count → ℝ) : Fin count → ℝ :=
  values ∘ Tuple.sort values

theorem sortedValues_monotone (values : Fin count → ℝ) : Monotone (sortedValues values) :=
  Tuple.monotone_sort values

private theorem sortedValues_le_iff (values : Fin count → ℝ) (i : Fin count) (a : ℝ) :
    sortedValues values i ≤ a ↔
      i.val < ∑ j : Fin count, if values j ≤ a then (1 : ℕ) else 0 := by
  classical
  have hcard : Fintype.card {j : Fin count // sortedValues values j ≤ a} =
      Fintype.card {j : Fin count // values j ≤ a} := by
    exact Fintype.card_congr (Equiv.subtypeEquiv (Tuple.sort values) (fun _ ↦ Iff.rfl))
  rw [← Tuple.lt_card_le_iff_apply_le_of_monotone
    (sortedValues values) a (sortedValues_monotone values) i, hcard]
  simp only [Fintype.card_subtype, Finset.card_eq_sum_ones, Finset.sum_filter]

/-- Sorting times is measurable even at ties; tie-breaking does not change the
ordered values. No unproved measurability premise is attached to the time law. -/
theorem sortedValues_measurable : Measurable (sortedValues (count := count)) := by
  classical
  apply measurable_pi_lambda
  intro i
  apply measurable_of_Iic
  intro a
  have hcount : Measurable (fun values : Fin count → ℝ ↦
      ∑ j : Fin count, if values j ≤ a then (1 : ℕ) else 0) := by
    apply Finset.measurable_sum
    intro j _
    exact Measurable.ite (measurableSet_le (measurable_pi_apply j) measurable_const)
      measurable_const measurable_const
  have heq : (fun values : Fin count → ℝ ↦ sortedValues values i) ⁻¹' Set.Iic a =
      {values | i.val < ∑ j : Fin count, if values j ≤ a then (1 : ℕ) else 0} := by
    ext values
    exact sortedValues_le_iff values i a
  rw [heq]
  exact measurableSet_lt measurable_const hcount

noncomputable def unitTimeLaw : Measure ℝ := volume.restrict (Set.Icc 0 1)

instance unitTimeLaw_probability : IsProbabilityMeasure unitTimeLaw := by
  constructor
  simp [unitTimeLaw, Real.volume_Icc]

noncomputable def cubeTimeLaw (count : ℕ) : Measure (Fin count → ℝ) :=
  Measure.pi fun _ ↦ unitTimeLaw

instance cubeTimeLaw_probability (count : ℕ) : IsProbabilityMeasure (cubeTimeLaw count) := by
  unfold cubeTimeLaw
  infer_instance

noncomputable def orderedTimes (duration : ℝ≥0) (values : Fin count → ℝ) : Fin count → ℝ :=
  fun i ↦ (duration : ℝ) * sortedValues values i

theorem orderedTimes_measurable (duration : ℝ≥0) :
    Measurable (orderedTimes (count := count) duration) := by
  apply measurable_pi_lambda
  intro i
  exact ((measurable_pi_apply i).comp sortedValues_measurable).const_mul duration

theorem orderedTimes_monotone (duration : ℝ≥0) (values : Fin count → ℝ) :
    Monotone (orderedTimes duration values) := by
  intro i j hij
  exact mul_le_mul_of_nonneg_left (sortedValues_monotone values hij) duration.property

noncomputable def timeLaw (duration : ℝ≥0) (count : ℕ) : Measure (Fin count → ℝ) :=
  (cubeTimeLaw count).map (orderedTimes duration)

instance timeLaw_probability (duration : ℝ≥0) (count : ℕ) :
    IsProbabilityMeasure (timeLaw duration count) := by
  unfold timeLaw
  exact Measure.isProbabilityMeasure_map (orderedTimes_measurable duration).aemeasurable

theorem timeLaw_integral (duration : ℝ≥0) (readout : (Fin count → ℝ) → ℝ)
    (hreadout : Measurable readout) :
    (∫ times, readout times ∂timeLaw duration count) =
      ∫ values, readout (orderedTimes duration values) ∂cubeTimeLaw count := by
  exact integral_map (orderedTimes_measurable duration).aemeasurable
    hreadout.aestronglyMeasurable

theorem orderedTimes_bounds (duration : ℝ≥0) (values : Fin count → ℝ)
    (hvalues : ∀ i, values i ∈ Set.Icc 0 1) (i : Fin count) :
    orderedTimes duration values i ∈ Set.Icc 0 (duration : ℝ) := by
  have h := hvalues (Tuple.sort values i)
  exact ⟨mul_nonneg duration.property h.1, mul_le_of_le_one_right duration.property h.2⟩

theorem cubeTimeLaw_bounds (count : ℕ) :
    ∀ᵐ values ∂cubeTimeLaw count, ∀ i, values i ∈ Set.Icc (0 : ℝ) 1 := by
  rw [ae_all_iff]
  intro i
  have h : ∀ᵐ x ∂unitTimeLaw, x ∈ Set.Icc (0 : ℝ) 1 :=
    ae_restrict_mem measurableSet_Icc
  have hm := measurePreserving_eval (fun _ : Fin count ↦ unitTimeLaw) i
  rw [← hm.map_eq] at h
  exact ae_of_ae_map hm.measurable.aemeasurable h

/-- Proposal times are ordered and belong to the epoch, with probability one. -/
theorem timeLaw_support (duration : ℝ≥0) (count : ℕ) :
    ∀ᵐ times ∂timeLaw duration count,
      Monotone times ∧ ∀ i, times i ∈ Set.Icc 0 (duration : ℝ) := by
  apply (ae_map_iff (orderedTimes_measurable duration).aemeasurable ?_).mpr
  · filter_upwards [cubeTimeLaw_bounds count] with values hvalues
    exact ⟨orderedTimes_monotone duration values, orderedTimes_bounds duration values hvalues⟩
  · apply MeasurableSet.inter
    · change MeasurableSet {times : Fin count → ℝ | ∀ i j, i ≤ j → times i ≤ times j}
      simp only [Set.setOf_forall]
      apply MeasurableSet.iInter
      intro i
      apply MeasurableSet.iInter
      intro j
      apply MeasurableSet.iInter
      intro _
      exact measurableSet_le (measurable_pi_apply i) (measurable_pi_apply j)
    · change MeasurableSet {times : Fin count → ℝ | ∀ i, times i ∈ Set.Icc 0 (duration : ℝ)}
      simp only [Set.setOf_forall]
      exact MeasurableSet.iInter (fun i ↦
        measurableSet_Icc.preimage (measurable_pi_apply i))

open Coalescent.FiniteGenomeAncestry AncestralEventLaw MarkedAncestralLaw

variable {D L n : ℕ}

/-- Conditional on the proposal count, integrate times and actual event marks.
The time law is independent of marks because proposals use a constant rate. -/
noncomputable def countExpectation (rates : Rates D L) (start : State D L n)
    (duration : ℝ≥0) (count : ℕ)
    (readout : Trace count start → (Fin count → ℝ) → ℝ) : ℝ :=
  (traceLaw rates count start).expectation (fun trace ↦
    ∫ times, readout trace times ∂timeLaw duration count)

theorem countExpectation_one (rates : Rates D L) (start : State D L n)
    (duration : ℝ≥0) (count : ℕ) :
    countExpectation rates start duration count (fun _ _ ↦ 1) = 1 := by
  simp [countExpectation, expectation, FiniteReportLaw.mass_sum]

theorem countExpectation_terminal (rates : Rates D L) (start : State D L n)
    (duration : ℝ≥0) (count : ℕ) (readout : State D L n → ℝ) :
    countExpectation rates start duration count (fun trace _ ↦ readout (terminal trace)) =
      (steps rates start count).expectation readout := by
  simp only [countExpectation, integral_const, measureReal_univ_eq_one, one_smul]
  exact trace_terminal_expectation rates count start readout

theorem time_integrable (duration : ℝ≥0) (readout : (Fin count → ℝ) → ℝ)
    (hmeas : Measurable readout) (bound : ℝ)
    (hb : ∀ᵐ times ∂timeLaw duration count, 0 ≤ readout times ∧ readout times ≤ bound) :
    Integrable readout (timeLaw duration count) := by
  apply (integrable_const bound).mono' hmeas.aestronglyMeasurable
  filter_upwards [hb] with times h
  simpa only [Real.norm_eq_abs, abs_of_nonneg h.1] using h.2

theorem countExpectation_bounds (rates : Rates D L) (start : State D L n)
    (duration : ℝ≥0) (count : ℕ) (readout : Trace count start → (Fin count → ℝ) → ℝ)
    (hmeas : ∀ trace, Measurable (readout trace)) (bound : ℝ)
    (hb : ∀ trace, ∀ᵐ times ∂timeLaw duration count,
      0 ≤ readout trace times ∧ readout trace times ≤ bound) :
    0 ≤ countExpectation rates start duration count readout ∧
      countExpectation rates start duration count readout ≤ bound := by
  have hi (trace : Trace count start) := time_integrable duration _ (hmeas trace) bound (hb trace)
  have hbounds (trace : Trace count start) :
      0 ≤ (∫ times, readout trace times ∂timeLaw duration count) ∧
        (∫ times, readout trace times ∂timeLaw duration count) ≤ bound := by
    constructor
    · exact integral_nonneg_of_ae ((hb trace).mono (fun _ h ↦ h.1))
    · simpa using integral_mono_ae (hi trace) (integrable_const bound)
        ((hb trace).mono (fun _ h ↦ h.2))
  constructor
  · exact Finset.sum_nonneg (fun trace _ ↦
      mul_nonneg ((traceLaw rates count start).mass_nonneg trace) (hbounds trace).1)
  · calc
      countExpectation rates start duration count readout ≤
          ∑ trace, (traceLaw rates count start).mass trace * bound :=
        Finset.sum_le_sum (fun trace _ ↦ mul_le_mul_of_nonneg_left
          (hbounds trace).2 ((traceLaw rates count start).mass_nonneg trace))
      _ = bound := by rw [← Finset.sum_mul, FiniteReportLaw.mass_sum, one_mul]

/-- The expectation series retains the complete marked and timed epoch. This
is a genealogy-input law, not yet a theorem about the P+T simulation output. -/
noncomputable def timedExpectation (rates : Rates D L) (start : State D L n)
    (duration : ℝ≥0)
    (readout : (count : ℕ) → Trace count start → (Fin count → ℝ) → ℝ) : ℝ :=
  ∑' count, poissonPMFReal (poissonParameter (n := n) rates duration) count *
    countExpectation rates start duration count (readout count)

theorem timedExpectation_one (rates : Rates D L) (start : State D L n)
    (duration : ℝ≥0) : timedExpectation rates start duration (fun _ _ _ ↦ 1) = 1 := by
  simp only [timedExpectation, countExpectation_one, mul_one]
  exact (poissonPMFRealSum _).tsum_eq

theorem timedExpectation_terminal (rates : Rates D L) (start : State D L n)
    (duration : ℝ≥0) (readout : State D L n → ℝ) :
    timedExpectation rates start duration (fun _ trace _ ↦ readout (terminal trace)) =
      (epochLaw rates start duration).expectation readout := by
  simp only [timedExpectation, countExpectation_terminal, epoch_expectation]

/-- Bounded measurable genealogy readouts give a convergent expectation series.
Ratios require a separate justified bound; squared correlations have bound one. -/
theorem timedExpectation_summable (rates : Rates D L) (start : State D L n)
    (duration : ℝ≥0)
    (readout : (count : ℕ) → Trace count start → (Fin count → ℝ) → ℝ)
    (hmeas : ∀ count trace, Measurable (readout count trace)) (bound : ℝ)
    (hb : ∀ count trace, ∀ᵐ times ∂timeLaw duration count,
      0 ≤ readout count trace times ∧ readout count trace times ≤ bound) :
    Summable (fun count ↦ poissonPMFReal (poissonParameter (n := n) rates duration) count *
      countExpectation rates start duration count (readout count)) := by
  apply ((poissonPMFRealSum _).summable.mul_right bound).of_nonneg_of_le
  · intro count
    exact mul_nonneg poissonPMFReal_nonneg
      (countExpectation_bounds rates start duration count _ (hmeas count) bound (hb count)).1
  · intro count
    exact mul_le_mul_of_nonneg_left
      (countExpectation_bounds rates start duration count _ (hmeas count) bound (hb count)).2
      poissonPMFReal_nonneg

/-- An explicit Poisson-tail error bound while preserving dependence on event
marks and times. No mutation or training readout is replaced by its mean. -/
theorem timedExpectation_truncation (rates : Rates D L) (start : State D L n)
    (duration : ℝ≥0)
    (readout : (count : ℕ) → Trace count start → (Fin count → ℝ) → ℝ)
    (hmeas : ∀ count trace, Measurable (readout count trace)) (bound : ℝ)
    (hb : ∀ count trace, ∀ᵐ times ∂timeLaw duration count,
      0 ≤ readout count trace times ∧ readout count trace times ≤ bound) (cutoff : ℕ) :
    let partialSum := ∑ count ∈ Finset.range cutoff,
      poissonPMFReal (poissonParameter (n := n) rates duration) count *
        countExpectation rates start duration count (readout count)
    0 ≤ timedExpectation rates start duration readout - partialSum ∧
      timedExpectation rates start duration readout - partialSum ≤
        tailProbability (n := n) rates duration cutoff * bound := by
  dsimp only
  have hs := timedExpectation_summable rates start duration readout hmeas bound hb
  rw [timedExpectation, ← hs.sum_add_tsum_nat_add cutoff]
  simp only [add_sub_cancel_left]
  constructor
  · exact tsum_nonneg (fun count ↦ mul_nonneg poissonPMFReal_nonneg
      (countExpectation_bounds rates start duration (count + cutoff) _
        (hmeas _) bound (hb _)).1)
  · unfold tailProbability
    rw [← tsum_mul_right]
    apply Summable.tsum_le_tsum
    · intro count
      exact mul_le_mul_of_nonneg_left
        (countExpectation_bounds rates start duration (count + cutoff) _
          (hmeas _) bound (hb _)).2 poissonPMFReal_nonneg
    · exact (summable_nat_add_iff (f := fun count ↦
        poissonPMFReal (poissonParameter (n := n) rates duration) count *
          countExpectation rates start duration count (readout count)) cutoff).mpr hs
    · exact ((summable_nat_add_iff
        (f := poissonPMFReal (poissonParameter (n := n) rates duration)) cutoff).mpr
          (poissonPMFRealSum _).summable).mul_right bound

end Descent.Portability.TimedAncestralLaw

