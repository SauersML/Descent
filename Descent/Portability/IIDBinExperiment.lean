/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.FiniteDiscreteMeasure
import Descent.Portability.FiniteIndependentMoments
import Descent.Portability.FixedBinHoeffdingLaw

assert_below Descent.Decision Descent.Program

/-!
An actual iid finite bin/label experiment. Conditional label independence is
derived from its product law; summing over every assignment removes conditioning
and yields the simultaneous confidence bound with random realized bin counts.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.IIDBinExperiment

open scoped BigOperators
open MeasureTheory ProbabilityTheory HWEInteractionLaw FiniteDiscreteMeasure
open FixedBinHoeffdingLaw

/-- Binary outcomes with their original event probability. -/
noncomputable def labelLaw (η : ℝ) (hη : 0 ≤ η ∧ η ≤ 1) : FiniteReportLaw Bool where
  mass b := if b then η else 1 - η
  mass_nonneg b := by cases b <;> simp <;> linarith [hη.1, hη.2]
  mass_sum := by simp

def label (b : Bool) : ℝ := if b then 1 else 0

theorem label_mean (η : ℝ) (hη : 0 ≤ η ∧ η ≤ 1) :
    (labelLaw η hη).expectation label = η := by
  simp [FiniteReportLaw.expectation, labelLaw, label]

/-- One observation records both its bin and its binary outcome. -/
noncomputable def rowLaw {K : ℕ} (π : FiniteReportLaw (Fin K)) (η : Fin K → ℝ)
    (hη : ∀ j, 0 ≤ η j ∧ η j ≤ 1) : FiniteReportLaw (Fin K × Bool) where
  mass x := π.mass x.1 * (labelLaw (η x.1) (hη x.1)).mass x.2
  mass_nonneg x := mul_nonneg (π.mass_nonneg _) ((labelLaw _ _).mass_nonneg _)
  mass_sum := by
    rw [Fintype.sum_prod_type]
    simp_rw [← Finset.mul_sum]
    have hs (j : Fin K) : ∑ b, (labelLaw (η j) (hη j)).mass b = 1 :=
      (labelLaw (η j) (hη j)).mass_sum
    simp only [hs, mul_one]
    exact π.mass_sum

variable {I : Type*} [Fintype I] [DecidableEq I] {K : ℕ}

/-- The validation rows are independent draws from the same specified joint distribution. -/
noncomputable def sampleLaw (π : FiniteReportLaw (Fin K)) (η : Fin K → ℝ)
    (hη : ∀ j, 0 ≤ η j ∧ η j ≤ 1) : FiniteReportLaw (I → Fin K × Bool) :=
  independentLaw (fun _ ↦ rowLaw π η hη)

/-- The conditional labels for a fixed assignment form an actual product experiment. -/
noncomputable def assignedLaw (assignment : I → Fin K) (η : Fin K → ℝ)
    (hη : ∀ j, 0 ≤ η j ∧ η j ≤ 1) : FiniteReportLaw (I → Bool) :=
  independentLaw (fun i ↦ labelLaw (η (assignment i)) (hη (assignment i)))

/-- Exact removal of the bin-assignment conditioning for every realized statistic. -/
theorem expectation_assignments (π : FiniteReportLaw (Fin K)) (η : Fin K → ℝ)
    (hη : ∀ j, 0 ≤ η j ∧ η j ≤ 1) (f : (I → Fin K × Bool) → ℝ) :
    (sampleLaw π η hη).expectation f =
      (independentLaw (fun _ : I ↦ π)).expectation (fun assignment ↦
        (assignedLaw assignment η hη).expectation (fun outcomes ↦
          f (fun i ↦ (assignment i, outcomes i)))) := by
  let e := Equiv.arrowProdEquivProdArrow I (fun _ ↦ Fin K) (fun _ ↦ Bool)
  have he := e.symm.sum_comp (fun x ↦ (sampleLaw π η hη).mass x * f x)
  rw [FiniteReportLaw.expectation, ← he, Fintype.sum_prod_type]
  simp only [FiniteReportLaw.expectation, sampleLaw, assignedLaw, independentLaw, rowLaw,
    e, Equiv.arrowProdEquivProdArrow_symm_apply, Finset.prod_mul_distrib,
    Finset.mul_sum, mul_assoc]
  rfl

/-- Failure means at least one nonempty bin misses its stated confidence radius. -/
def Miss (assignment : I → Fin K) (η : Fin K → ℝ) (α : ℝ) (outcomes : I → Bool) : Prop :=
  ∃ j : Fin K, 0 < (binRows assignment j).card ∧
    radius K (binRows assignment j).card α <
      |(∑ i ∈ binRows assignment j, label (outcomes i)) / (binRows assignment j).card - η j|

/-- Conditional independence, boundedness and means all follow from the supplied label law. -/
theorem assigned_confidence (hK : 0 < K) (assignment : I → Fin K) (η : Fin K → ℝ)
    (hη : ∀ j, 0 ≤ η j ∧ η j ≤ 1) (α : ℝ) (hα : 0 < α ∧ α < 1) :
    (FiniteDiscreteMeasure.measure (assignedLaw assignment η hη)).real
      {outcomes | Miss assignment η α outcomes} ≤ α := by
  apply fixed_assignment_confidence
    (μ := FiniteDiscreteMeasure.measure (assignedLaw assignment η hη))
    hK assignment η (fun i outcomes ↦ label (outcomes i))
  · exact independent_observables _ (fun _ ↦ label)
  · intro i
    exact (measurable_of_finite _).aemeasurable
  · intro i
    apply Filter.Eventually.of_forall
    intro outcomes
    cases outcomes i <;> norm_num [label]
  · intro i
    rw [integral_observable]
    change (independentLaw _).expectation (fun outcomes ↦ label (outcomes i)) = _
    rw [FiniteIndependentMoments.coordinate_expectation, label_mean]
  · exact hα

/-- With random bin counts, the unconditional probability of any miss is at most α. -/
theorem iid_confidence (hK : 0 < K) (π : FiniteReportLaw (Fin K)) (η : Fin K → ℝ)
    (hη : ∀ j, 0 ≤ η j ∧ η j ≤ 1) (α : ℝ) (hα : 0 < α ∧ α < 1) :
    (FiniteDiscreteMeasure.measure (sampleLaw π η hη)).real
      {sample : I → Fin K × Bool | Miss (fun i ↦ (sample i).1) η α (fun i ↦ (sample i).2)} ≤ α := by
  classical
  rw [real_event, expectation_assignments]
  have hbound (assignment : I → Fin K) :
      (assignedLaw assignment η hη).expectation (fun outcomes ↦
        if Miss assignment η α outcomes then 1 else 0) ≤ α := by
    simpa only [real_event, Set.indicator_apply, Set.mem_setOf_eq] using
      assigned_confidence hK assignment η hη α hα
  simp only [Set.indicator_apply, Set.mem_setOf_eq, FiniteReportLaw.expectation]
  calc
    _ ≤ ∑ assignment : I → Fin K, (independentLaw (fun _ : I ↦ π)).mass assignment * α := by
      apply Finset.sum_le_sum
      intro assignment _
      exact mul_le_mul_of_nonneg_left (hbound assignment)
        ((independentLaw (fun _ : I ↦ π)).mass_nonneg assignment)
    _ = α := by rw [← Finset.sum_mul, FiniteReportLaw.mass_sum, one_mul]

end Descent.Portability.IIDBinExperiment
