import Calibrator.PCCorrectability.Threshold
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

namespace Calibrator

/-!
# Frequency-resolved correctability diagnostic

Recent structure need not have the same differentiation in common, rare, and
IBD-derived marker classes. The quantities below keep effective independent
marker counts and differentiation separate by class.
-/

structure FrequencyResolvedCohort (classes : ℕ) where
  sampleSize : ℝ
  subgroupSize : ℝ
  effectiveMarkers : Fin classes → ℝ
  differentiation : Fin classes → ℝ
  sampleSize_pos : 0 < sampleSize
  subgroupSize_pos : 0 < subgroupSize
  effectiveMarkers_pos : ∀ i, 0 < effectiveMarkers i
  differentiation_nonneg : ∀ i, 0 ≤ differentiation i

noncomputable def FrequencyResolvedCohort.classMargin {classes : ℕ}
    (cohort : FrequencyResolvedCohort classes) (i : Fin classes) : ℝ :=
  pcCorrectabilityMargin cohort.sampleSize (cohort.effectiveMarkers i)
    (cohort.differentiation i) cohort.subgroupSize

noncomputable def FrequencyResolvedCohort.correctableClasses {classes : ℕ}
    (cohort : FrequencyResolvedCohort classes) : Finset (Fin classes) :=
  Finset.univ.filter (fun i => 0 < cohort.classMargin i)

theorem FrequencyResolvedCohort.mem_correctableClasses_iff {classes : ℕ}
    (cohort : FrequencyResolvedCohort classes) (i : Fin classes) :
    i ∈ cohort.correctableClasses ↔ 0 < cohort.classMargin i := by
  simp [FrequencyResolvedCohort.correctableClasses]

/-- Information contribution `M_c F_c²` of one marker class. -/
noncomputable def FrequencyResolvedCohort.classInformation {classes : ℕ}
    (cohort : FrequencyResolvedCohort classes) (i : Fin classes) : ℝ :=
  cohort.effectiveMarkers i * cohort.differentiation i ^ 2

/-- Differentiation-matched GRM weight `M_c F_c`. -/
noncomputable def FrequencyResolvedCohort.informationMatchedWeight {classes : ℕ}
    (cohort : FrequencyResolvedCohort classes) (i : Fin classes) : ℝ :=
  cohort.effectiveMarkers i * cohort.differentiation i

theorem FrequencyResolvedCohort.weight_mul_differentiation_eq_information
    {classes : ℕ} (cohort : FrequencyResolvedCohort classes) (i : Fin classes) :
    cohort.informationMatchedWeight i * cohort.differentiation i =
      cohort.classInformation i := by
  unfold FrequencyResolvedCohort.informationMatchedWeight
    FrequencyResolvedCohort.classInformation
  ring

noncomputable def FrequencyResolvedCohort.totalInformation {classes : ℕ}
    (cohort : FrequencyResolvedCohort classes) : ℝ :=
  ∑ i, cohort.classInformation i

theorem FrequencyResolvedCohort.classInformation_nonneg {classes : ℕ}
    (cohort : FrequencyResolvedCohort classes) (i : Fin classes) :
    0 ≤ cohort.classInformation i := by
  exact mul_nonneg (le_of_lt (cohort.effectiveMarkers_pos i)) (sq_nonneg _)

theorem adding_informative_frequency_class_increases_information
    (baseInformation markers differentiation : ℝ)
    (hmarkers : 0 < markers) (hdifferentiation : differentiation ≠ 0) :
    baseInformation < baseInformation + markers * differentiation ^ 2 := by
  exact lt_add_of_pos_right _
    (mul_pos hmarkers (sq_pos_of_ne_zero hdifferentiation))

theorem FrequencyResolvedCohort.totalInformation_nonneg {classes : ℕ}
    (cohort : FrequencyResolvedCohort classes) :
    0 ≤ cohort.totalInformation := by
  unfold FrequencyResolvedCohort.totalInformation
  exact Finset.sum_nonneg (fun i _ => cohort.classInformation_nonneg i)

noncomputable def FrequencyResolvedCohort.weightedSignal {classes : ℕ}
    (cohort : FrequencyResolvedCohort classes) (weight : Fin classes → ℝ) : ℝ :=
  ∑ i, weight i * cohort.differentiation i

noncomputable def FrequencyResolvedCohort.weightedNoise {classes : ℕ}
    (cohort : FrequencyResolvedCohort classes) (weight : Fin classes → ℝ) : ℝ :=
  ∑ i, weight i ^ 2 / cohort.effectiveMarkers i

noncomputable def FrequencyResolvedCohort.weightedInformation {classes : ℕ}
    (cohort : FrequencyResolvedCohort classes) (weight : Fin classes → ℝ) : ℝ :=
  cohort.weightedSignal weight ^ 2 / cohort.weightedNoise weight

/-- Cauchy--Schwarz gives the sharp independent-class information ceiling. -/
theorem FrequencyResolvedCohort.weightedSignal_sq_le_information_mul_noise
    {classes : ℕ} (cohort : FrequencyResolvedCohort classes)
    (weight : Fin classes → ℝ) :
    cohort.weightedSignal weight ^ 2 ≤
      cohort.totalInformation * cohort.weightedNoise weight := by
  let signalVector : Fin classes → ℝ := fun i =>
    Real.sqrt (cohort.effectiveMarkers i) * cohort.differentiation i
  let weightVector : Fin classes → ℝ := fun i =>
    weight i / Real.sqrt (cohort.effectiveMarkers i)
  have hproduct : (∑ i, signalVector i * weightVector i) =
      cohort.weightedSignal weight := by
    unfold FrequencyResolvedCohort.weightedSignal signalVector weightVector
    apply Finset.sum_congr rfl
    intro i _
    have hsqrt_pos : 0 < Real.sqrt (cohort.effectiveMarkers i) :=
      Real.sqrt_pos.2 (cohort.effectiveMarkers_pos i)
    field_simp [ne_of_gt hsqrt_pos]
  have hsignal_sq : (∑ i, signalVector i ^ 2) = cohort.totalInformation := by
    unfold FrequencyResolvedCohort.totalInformation
      FrequencyResolvedCohort.classInformation signalVector
    apply Finset.sum_congr rfl
    intro i _
    rw [mul_pow, Real.sq_sqrt (le_of_lt (cohort.effectiveMarkers_pos i))]
  have hweight_sq : (∑ i, weightVector i ^ 2) = cohort.weightedNoise weight := by
    unfold FrequencyResolvedCohort.weightedNoise weightVector
    apply Finset.sum_congr rfl
    intro i _
    rw [div_pow, Real.sq_sqrt (le_of_lt (cohort.effectiveMarkers_pos i))]
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin classes))
    signalVector weightVector
  rw [hproduct, hsignal_sq, hweight_sq] at hcs
  exact hcs

theorem FrequencyResolvedCohort.matched_weight_signal_and_noise
    {classes : ℕ} (cohort : FrequencyResolvedCohort classes) :
    cohort.weightedSignal cohort.informationMatchedWeight = cohort.totalInformation ∧
      cohort.weightedNoise cohort.informationMatchedWeight = cohort.totalInformation := by
  constructor
  · unfold FrequencyResolvedCohort.weightedSignal
      FrequencyResolvedCohort.totalInformation
    exact Finset.sum_congr rfl fun i _ =>
      cohort.weight_mul_differentiation_eq_information i
  · unfold FrequencyResolvedCohort.weightedNoise
      FrequencyResolvedCohort.informationMatchedWeight
      FrequencyResolvedCohort.totalInformation
      FrequencyResolvedCohort.classInformation
    apply Finset.sum_congr rfl
    intro i _
    field_simp [ne_of_gt (cohort.effectiveMarkers_pos i)]

/-- `w_c ∝ M_c F_c` maximizes independent-class signal-to-noise information. -/
theorem FrequencyResolvedCohort.informationMatchedWeight_optimal
    {classes : ℕ} (cohort : FrequencyResolvedCohort classes)
    (weight : Fin classes → ℝ)
    (hnoise : 0 < cohort.weightedNoise weight)
    (hinfo : 0 < cohort.totalInformation) :
    cohort.weightedInformation weight ≤
      cohort.weightedInformation cohort.informationMatchedWeight := by
  have hbound : cohort.weightedInformation weight ≤ cohort.totalInformation := by
    unfold FrequencyResolvedCohort.weightedInformation
    rw [div_le_iff₀ hnoise]
    exact cohort.weightedSignal_sq_le_information_mul_noise weight
  have hmatched := cohort.matched_weight_signal_and_noise
  have hmatched_info :
      cohort.weightedInformation cohort.informationMatchedWeight =
        cohort.totalInformation := by
    rw [FrequencyResolvedCohort.weightedInformation, hmatched.1, hmatched.2]
    field_simp [ne_of_gt hinfo]
  rw [hmatched_info]
  exact hbound

end Calibrator
