/-
Released under AGPL-3.0-or-later as described in the file LICENSE.
-/
import Descent.PCCorrectability.Threshold
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring

namespace Descent

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

/-- **The class is inhabited.**  A theorem quantified over an uninhabited structure is
true and empty: kernel-checked, clean axiom report, no content.  This is the witness that
makes the theorems below statements about something. -/
noncomputable def FrequencyResolvedCohort.witness (classes : ℕ) :
    FrequencyResolvedCohort classes where
  sampleSize := 1
  subgroupSize := 1
  effectiveMarkers := fun _ ↦ 1
  differentiation := fun _ ↦ 0
  sampleSize_pos := by norm_num
  subgroupSize_pos := by norm_num
  effectiveMarkers_pos := fun _ ↦ by norm_num
  differentiation_nonneg := fun _ ↦ by norm_num

noncomputable def FrequencyResolvedCohort.classMargin {classes : ℕ}
    (cohort : FrequencyResolvedCohort classes) (i : Fin classes) : ℝ :=
  pcCorrectabilityMargin cohort.sampleSize (cohort.effectiveMarkers i)
    (cohort.differentiation i) cohort.subgroupSize

/-- The frequency-resolved diagnostic is exactly the shared rank-one
correctability margin evaluated with the marker count and differentiation of
one frequency class.  This theorem is the cross-module contract: changing the
global threshold changes every class diagnostic rather than leaving a parallel
formula behind. -/
theorem FrequencyResolvedCohort.classMargin_eq_pcCorrectabilityMargin
    {classes : ℕ} (cohort : FrequencyResolvedCohort classes) (i : Fin classes) :
    cohort.classMargin i =
      pcCorrectabilityMargin cohort.sampleSize (cohort.effectiveMarkers i)
        (cohort.differentiation i) cohort.subgroupSize := rfl

noncomputable def FrequencyResolvedCohort.correctableClasses {classes : ℕ}
    (cohort : FrequencyResolvedCohort classes) : Finset (Fin classes) :=
  Finset.univ.filter (fun i ↦ 0 < cohort.classMargin i)

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
  exact Finset.sum_nonneg (fun i _ ↦ cohort.classInformation_nonneg i)

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
  let signalVector : Fin classes → ℝ := fun i ↦
    Real.sqrt (cohort.effectiveMarkers i) * cohort.differentiation i
  let weightVector : Fin classes → ℝ := fun i ↦
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
    exact Finset.sum_congr rfl fun i _ ↦
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

/-!
### The combined information index

`map/correctability.rs` reports one whole-design summary,
`combined_information_index = 4 · effectiveSubgroupSize · √(ΣM_cF_c² / n)`, that had no
definition anywhere in this corpus: a shipped number with no stated meaning.  Differential
testing over a 1010-design sweep confirmed the body byte-for-byte and, more usefully, found
what it *is*: for a single marker class it is exactly the spike-to-threshold ratio, so the
familiar `> 1` reading is the BBP detectability test in disguise.
-/

/-- Whole-design detectability index reported by the shipped calculator. -/
noncomputable def FrequencyResolvedCohort.combinedInformationIndex {classes : ℕ}
    (cohort : FrequencyResolvedCohort classes) : ℝ :=
  4 * effectiveSubgroupSize cohort.sampleSize cohort.subgroupSize *
    Real.sqrt (cohort.totalInformation / cohort.sampleSize)

/-- **The index is the spike measured in threshold units.**  Multiplying it back by the BBP
threshold returns the rank-one spike exactly, so `combinedInformationIndex > 1` is
`demographicSpike > bbpProxyThreshold` — the same detectability test the per-class report
runs — whenever the design has one marker class. -/
theorem combinedInformationIndex_mul_threshold_eq_spike
    (n M F m : ℝ) (hn : 0 < n) (hM : 0 < M) (hF : 0 ≤ F) :
    4 * effectiveSubgroupSize n m * Real.sqrt ((M * F ^ 2) / n) * bbpProxyThreshold n M =
      demographicSpike n F m := by
  have hinfo : (0 : ℝ) ≤ M * F ^ 2 / n :=
    div_nonneg (mul_nonneg (le_of_lt hM) (sq_nonneg F)) (le_of_lt hn)
  have hn' : n ≠ 0 := ne_of_gt hn
  have hM' : M ≠ 0 := ne_of_gt hM
  have hproduct : M * F ^ 2 / n * (n / M) = F ^ 2 := by
    field_simp
  have hsqrt : Real.sqrt (M * F ^ 2 / n) * bbpProxyThreshold n M = F := by
    unfold bbpProxyThreshold
    rw [← Real.sqrt_mul hinfo, hproduct, Real.sqrt_sq hF]
  unfold demographicSpike
  calc
    4 * effectiveSubgroupSize n m * Real.sqrt (M * F ^ 2 / n) * bbpProxyThreshold n M
        = 4 * effectiveSubgroupSize n m *
            (Real.sqrt (M * F ^ 2 / n) * bbpProxyThreshold n M) := by ring
    _ = 4 * effectiveSubgroupSize n m * F := by rw [hsqrt]
    _ = 4 * F * effectiveSubgroupSize n m := by ring

/-- The one-class specialization, stated on the structure the calculator's input maps onto. -/
theorem FrequencyResolvedCohort.combinedInformationIndex_mul_threshold_eq_spike
    (cohort : FrequencyResolvedCohort 1) :
    cohort.combinedInformationIndex *
        bbpProxyThreshold cohort.sampleSize (cohort.effectiveMarkers 0) =
      demographicSpike cohort.sampleSize (cohort.differentiation 0) cohort.subgroupSize := by
  have htotal : cohort.totalInformation =
      cohort.effectiveMarkers 0 * cohort.differentiation 0 ^ 2 := by
    unfold FrequencyResolvedCohort.totalInformation FrequencyResolvedCohort.classInformation
    simp
  unfold FrequencyResolvedCohort.combinedInformationIndex
  rw [htotal]
  exact _root_.Descent.combinedInformationIndex_mul_threshold_eq_spike cohort.sampleSize
    (cohort.effectiveMarkers 0) (cohort.differentiation 0) cohort.subgroupSize
    cohort.sampleSize_pos (cohort.effectiveMarkers_pos 0) (cohort.differentiation_nonneg 0)

/-!
### Admissibility gap against the shipped validator

`map/correctability.rs::validate` rejects designs this structure accepts.  It requires
`subgroup_size < sample_size` and `differentiation ≤ 1` (the Hudson `F_ST` scale); the fields
above require only positivity and nonnegativity.  Every theorem stated over
`FrequencyResolvedCohort` therefore also quantifies over designs the shipped calculator
refuses to score, and the next result shows those designs are not harmless — the effective
subgroup size, which the whole spike scale is built on, goes nonpositive there.
-/

/-- The extra admissibility conditions the shipped validator enforces. -/
def FrequencyResolvedCohort.CalculatorAdmissible {classes : ℕ}
    (cohort : FrequencyResolvedCohort classes) : Prop :=
  cohort.subgroupSize < cohort.sampleSize ∧ ∀ i, cohort.differentiation i ≤ 1

/-- **A cohort the shipped validator accepts.**  `FrequencyResolvedCohort.witness` above is
*not* admissible — it has `subgroupSize = sampleSize = 1`, which `validate` rejects — so
without this second witness `CalculatorAdmissible` would be a property only ever assumed.
This one splits a two-person panel and carries the maximal legal differentiation. -/
noncomputable def FrequencyResolvedCohort.admissibleWitness (classes : ℕ) :
    FrequencyResolvedCohort classes where
  sampleSize := 2
  subgroupSize := 1
  effectiveMarkers := fun _ ↦ 1
  differentiation := fun _ ↦ 1
  sampleSize_pos := by norm_num
  subgroupSize_pos := by norm_num
  effectiveMarkers_pos := fun _ ↦ by norm_num
  differentiation_nonneg := fun _ ↦ by norm_num

/-- On admissible designs the effective subgroup size is positive, which is what makes the
spike, the margin, and every downstream overlap a statement about a real contrast. -/
theorem FrequencyResolvedCohort.effectiveSubgroupSize_pos_of_admissible {classes : ℕ}
    (cohort : FrequencyResolvedCohort classes) (hadmissible : cohort.CalculatorAdmissible) :
    0 < effectiveSubgroupSize cohort.sampleSize cohort.subgroupSize := by
  unfold effectiveSubgroupSize
  exact div_pos (mul_pos cohort.subgroupSize_pos (sub_pos.mpr hadmissible.1))
    cohort.sampleSize_pos

/-- The admissible witness is admissible, so the property is established and not merely
assumed. -/
theorem FrequencyResolvedCohort.admissibleWitness_calculatorAdmissible (classes : ℕ) :
    (FrequencyResolvedCohort.admissibleWitness classes).CalculatorAdmissible := by
  constructor
  · show (1 : ℝ) < 2
    norm_num
  · intro i
    show (1 : ℝ) ≤ 1
    norm_num

/-- **The gap is not vacuous.**  A cohort satisfying every field of the structure but violating
the shipped validator's `subgroup_size < sample_size` has nonpositive effective subgroup size,
hence a nonpositive spike for every nonnegative differentiation: the margin is then negative for
purely arithmetic reasons and reports "uncorrectable" for a design the calculator would have
refused to accept at all. -/
theorem FrequencyResolvedCohort.effectiveSubgroupSize_nonpos_of_inadmissible {classes : ℕ}
    (cohort : FrequencyResolvedCohort classes)
    (hsubgroup : cohort.sampleSize ≤ cohort.subgroupSize) :
    effectiveSubgroupSize cohort.sampleSize cohort.subgroupSize ≤ 0 := by
  unfold effectiveSubgroupSize
  apply div_nonpos_of_nonpos_of_nonneg _ (le_of_lt cohort.sampleSize_pos)
  exact mul_nonpos_of_nonneg_of_nonpos (le_of_lt cohort.subgroupSize_pos) (by linarith)

end Descent
