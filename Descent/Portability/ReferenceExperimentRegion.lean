/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.ReferenceExperimentEarlyMomentCorners
import Descent.Portability.ReferenceExperimentEarlyLossCorners
import Descent.Portability.ReferenceExperimentLateMomentCorners
import Descent.Portability.ReferenceExperimentLateLossCorners

assert_below Descent.Decision Descent.Program

/-!
# The full-square range table of the NOTE2 section 9 reference experiment

NOTE2 section 9 closes with the exact ranges, over every independent architecture and
environment law in the whole square, of two conditional expected population outputs: the
target squared correlation and the target to source squared-correlation ratio. This module
proves both ranges for both migration histories through the corpus independent-mixture region
`ArchitectureEnvironmentRegion`.

A history report is the context-mass average of its four corner accumulators, and at the
reference probabilities `(3/5, 2/3)` the corpus mixed numerator of those accumulators is exactly
the history report (`early_mixtureNumerator_reference`, `late_mixtureNumerator_reference`). The
corner accumulators of the weighted numerators and definedness masses are the corner
certificates of `ReferenceExperimentEarlyMomentCorners`, `ReferenceExperimentEarlyLossCorners`,
`ReferenceExperimentLateMomentCorners` and `ReferenceExperimentLateLossCorners`, so nothing here
runs a kernel computation. The corpus
theorem `conditionalMean_eq_corner_combination` makes the reported conditional mean on the square
a convex combination of the four corner ratios with weights `π_ae d_ae`, so `le_conditionalMean`
and `conditionalMean_le` bound it by the least and the greatest corner ratio, and
`conditionalMean_corner` shows both bounds are attained at the displayed corners.

Proved here, for both histories: the range theorems on the whole square, their attainment at
the corners, and the rounding of the exact endpoints to the nine-digit decimals of the section 9
table, stated as rational bounds.

## Empirical status

None. The bodies here are exact rational arithmetic on a completely specified finite model
and a convex-combination inequality, so no measurement can bear on these ranges.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.ReferenceExperimentRegion

open RationalReportClosure ReferenceExperimentLaw ReferenceExperimentTable
  ReferenceExperimentCorners ReferenceExperimentEarlyMomentCorners
  ReferenceExperimentEarlyLossCorners ReferenceExperimentLateMomentCorners
  ReferenceExperimentLateLossCorners

/-! ## Corner accumulators in the real numbers -/

/-- A corner accumulator of a tabled terminal law carried to the real numbers, the input of the
independent-mixture region of `ArchitectureEnvironmentRegion`. -/
noncomputable def cornerAccumulator (entries : List ((Bool × Bool) × TerminalTypes × ℚ))
    (report : Bool × Bool → LearnerAtom → TerminalTypes → ℚ) (context : Bool × Bool) : ℝ :=
  (tableCornerReport entries report context : ℝ)

/-- At the reference probabilities `(3/5, 2/3)` the corpus mixed numerator of the corner
accumulators is the tabled history report. -/
theorem mixtureNumerator_reference (entries : List ((Bool × Bool) × TerminalTypes × ℚ))
    (report : Bool × Bool → LearnerAtom → TerminalTypes → ℚ) :
    ArchitectureEnvironmentRegion.mixtureNumerator (cornerAccumulator entries report)
        (3 / 5) (2 / 3) = (tableReport entries report : ℝ) := by
  rw [tableReport_eq_corners, Rat.cast_sum]
  unfold ArchitectureEnvironmentRegion.mixtureNumerator
  refine Finset.sum_congr rfl fun context _ ↦ ?_
  rw [Rat.cast_mul, contextMass_eq_cellWeight]
  rfl

/-- At the reference probabilities the mixed numerator is the early migration report. -/
theorem early_mixtureNumerator_reference
    (report : Bool × Bool → LearnerAtom → TerminalTypes → ℚ) :
    ArchitectureEnvironmentRegion.mixtureNumerator
        (cornerAccumulator earlyTerminalEntries report) (3 / 5) (2 / 3) =
      (historyReport earlyMigration report : ℝ) := by
  rw [early_historyReport_table]
  exact mixtureNumerator_reference earlyTerminalEntries report

/-- At the reference probabilities the mixed numerator is the late migration report. -/
theorem late_mixtureNumerator_reference
    (report : Bool × Bool → LearnerAtom → TerminalTypes → ℚ) :
    ArchitectureEnvironmentRegion.mixtureNumerator
        (cornerAccumulator lateTerminalEntries report) (3 / 5) (2 / 3) =
      (historyReport lateMigration report : ℝ) := by
  rw [late_historyReport_table]
  exact mixtureNumerator_reference lateTerminalEntries report

/-- The weighted numerator of the population target squared correlation. -/
def r2Weighted : Bool × Bool → LearnerAtom → TerminalTypes → ℚ :=
  fun context atom terminal ↦ weightedValue (targetR2 context atom terminal)

/-- The definedness indicator of the population target squared correlation. -/
def r2Defined : Bool × Bool → LearnerAtom → TerminalTypes → ℚ :=
  fun context atom terminal ↦ bitValue (targetR2 context atom terminal).isSome

/-- The weighted numerator of the target to source squared-correlation ratio. -/
def ratioWeighted : Bool × Bool → LearnerAtom → TerminalTypes → ℚ :=
  fun context atom terminal ↦ weightedValue (r2Portability context atom terminal)

/-- The definedness indicator of the target to source squared-correlation ratio. -/
def ratioDefined : Bool × Bool → LearnerAtom → TerminalTypes → ℚ :=
  fun context atom terminal ↦ definedIndicator (r2Portability context atom terminal)

theorem r2Weighted_eq :
    r2Weighted = fun context atom terminal ↦ weightedValue (targetR2 context atom terminal) :=
  rfl

theorem r2Defined_eq :
    r2Defined = fun context atom terminal ↦ bitValue (targetR2 context atom terminal).isSome :=
  rfl

theorem ratioWeighted_eq :
    ratioWeighted =
      fun context atom terminal ↦ weightedValue (r2Portability context atom terminal) :=
  rfl

theorem ratioDefined_eq :
    ratioDefined =
      fun context atom terminal ↦ definedIndicator (r2Portability context atom terminal) :=
  rfl

/-! ## The ranges on the whole square -/

/-- NOTE2 section 9, early migration: over every independent architecture and environment law
the conditional expected population target squared correlation lies between its corner ratios
at `(A, E) = (1, 0)` and `(0, 1)`. -/
theorem early_target_r2_range (α η : ℝ) (h0a : 0 ≤ α) (h1a : α ≤ 1) (h0e : 0 ≤ η)
    (h1e : η ≤ 1) :
    cornerAccumulator earlyTerminalEntries r2Weighted (true, false) /
        cornerAccumulator earlyTerminalEntries r2Defined (true, false) ≤
      ArchitectureEnvironmentRegion.conditionalMean
        (cornerAccumulator earlyTerminalEntries r2Weighted)
        (cornerAccumulator earlyTerminalEntries r2Defined) α η ∧
    ArchitectureEnvironmentRegion.conditionalMean
        (cornerAccumulator earlyTerminalEntries r2Weighted)
        (cornerAccumulator earlyTerminalEntries r2Defined) α η ≤
      cornerAccumulator earlyTerminalEntries r2Weighted (false, true) /
        cornerAccumulator earlyTerminalEntries r2Defined (false, true) := by
  have hden : ∀ context, 0 < cornerAccumulator earlyTerminalEntries r2Defined context := by
    rintro ⟨architecture, environment⟩
    cases architecture <;> cases environment <;>
      simp only [cornerAccumulator, r2Defined_eq, early_r2Defined_corner_zero_zero,
        early_r2Defined_corner_zero_one, early_r2Defined_corner_one_zero,
        early_r2Defined_corner_one_one] <;> norm_num
  constructor
  · refine ArchitectureEnvironmentRegion.le_conditionalMean _ _ hden α η h0a h1a h0e h1e _
      fun context ↦ ?_
    obtain ⟨architecture, environment⟩ := context
    cases architecture <;> cases environment <;>
      simp only [cornerAccumulator, r2Weighted_eq, r2Defined_eq,
        early_r2Weighted_corner_zero_zero, early_r2Weighted_corner_zero_one,
        early_r2Weighted_corner_one_zero, early_r2Weighted_corner_one_one,
        early_r2Defined_corner_zero_zero, early_r2Defined_corner_zero_one,
        early_r2Defined_corner_one_zero, early_r2Defined_corner_one_one] <;> norm_num
  · refine ArchitectureEnvironmentRegion.conditionalMean_le _ _ hden α η h0a h1a h0e h1e _
      fun context ↦ ?_
    obtain ⟨architecture, environment⟩ := context
    cases architecture <;> cases environment <;>
      simp only [cornerAccumulator, r2Weighted_eq, r2Defined_eq,
        early_r2Weighted_corner_zero_zero, early_r2Weighted_corner_zero_one,
        early_r2Weighted_corner_one_zero, early_r2Weighted_corner_one_one,
        early_r2Defined_corner_zero_zero, early_r2Defined_corner_zero_one,
        early_r2Defined_corner_one_zero, early_r2Defined_corner_one_one] <;> norm_num

/-- NOTE2 section 9, early migration: over every independent architecture and environment law
the conditional expected target to source squared-correlation ratio lies between its corner
ratios at `(A, E) = (0, 1)` and `(0, 0)`. -/
theorem early_r2Portability_range (α η : ℝ) (h0a : 0 ≤ α) (h1a : α ≤ 1) (h0e : 0 ≤ η)
    (h1e : η ≤ 1) :
    cornerAccumulator earlyTerminalEntries ratioWeighted (false, true) /
        cornerAccumulator earlyTerminalEntries ratioDefined (false, true) ≤
      ArchitectureEnvironmentRegion.conditionalMean
        (cornerAccumulator earlyTerminalEntries ratioWeighted)
        (cornerAccumulator earlyTerminalEntries ratioDefined) α η ∧
    ArchitectureEnvironmentRegion.conditionalMean
        (cornerAccumulator earlyTerminalEntries ratioWeighted)
        (cornerAccumulator earlyTerminalEntries ratioDefined) α η ≤
      cornerAccumulator earlyTerminalEntries ratioWeighted (false, false) /
        cornerAccumulator earlyTerminalEntries ratioDefined (false, false) := by
  have hden : ∀ context, 0 < cornerAccumulator earlyTerminalEntries ratioDefined context := by
    rintro ⟨architecture, environment⟩
    cases architecture <;> cases environment <;>
      simp only [cornerAccumulator, ratioDefined_eq, early_ratioDefined_corner_zero_zero,
        early_ratioDefined_corner_zero_one, early_ratioDefined_corner_one_zero,
        early_ratioDefined_corner_one_one] <;> norm_num
  constructor
  · refine ArchitectureEnvironmentRegion.le_conditionalMean _ _ hden α η h0a h1a h0e h1e _
      fun context ↦ ?_
    obtain ⟨architecture, environment⟩ := context
    cases architecture <;> cases environment <;>
      simp only [cornerAccumulator, ratioWeighted_eq, ratioDefined_eq,
        early_ratioWeighted_corner_zero_zero, early_ratioWeighted_corner_zero_one,
        early_ratioWeighted_corner_one_zero, early_ratioWeighted_corner_one_one,
        early_ratioDefined_corner_zero_zero, early_ratioDefined_corner_zero_one,
        early_ratioDefined_corner_one_zero, early_ratioDefined_corner_one_one] <;> norm_num
  · refine ArchitectureEnvironmentRegion.conditionalMean_le _ _ hden α η h0a h1a h0e h1e _
      fun context ↦ ?_
    obtain ⟨architecture, environment⟩ := context
    cases architecture <;> cases environment <;>
      simp only [cornerAccumulator, ratioWeighted_eq, ratioDefined_eq,
        early_ratioWeighted_corner_zero_zero, early_ratioWeighted_corner_zero_one,
        early_ratioWeighted_corner_one_zero, early_ratioWeighted_corner_one_one,
        early_ratioDefined_corner_zero_zero, early_ratioDefined_corner_zero_one,
        early_ratioDefined_corner_one_zero, early_ratioDefined_corner_one_one] <;> norm_num

/-- NOTE2 section 9, late migration: over every independent architecture and environment law
the conditional expected population target squared correlation lies between its corner ratios
at `(A, E) = (1, 0)` and `(0, 1)`. -/
theorem late_target_r2_range (α η : ℝ) (h0a : 0 ≤ α) (h1a : α ≤ 1) (h0e : 0 ≤ η)
    (h1e : η ≤ 1) :
    cornerAccumulator lateTerminalEntries r2Weighted (true, false) /
        cornerAccumulator lateTerminalEntries r2Defined (true, false) ≤
      ArchitectureEnvironmentRegion.conditionalMean
        (cornerAccumulator lateTerminalEntries r2Weighted)
        (cornerAccumulator lateTerminalEntries r2Defined) α η ∧
    ArchitectureEnvironmentRegion.conditionalMean
        (cornerAccumulator lateTerminalEntries r2Weighted)
        (cornerAccumulator lateTerminalEntries r2Defined) α η ≤
      cornerAccumulator lateTerminalEntries r2Weighted (false, true) /
        cornerAccumulator lateTerminalEntries r2Defined (false, true) := by
  have hden : ∀ context, 0 < cornerAccumulator lateTerminalEntries r2Defined context := by
    rintro ⟨architecture, environment⟩
    cases architecture <;> cases environment <;>
      simp only [cornerAccumulator, r2Defined_eq, late_r2Defined_corner_zero_zero,
        late_r2Defined_corner_zero_one, late_r2Defined_corner_one_zero,
        late_r2Defined_corner_one_one] <;> norm_num
  constructor
  · refine ArchitectureEnvironmentRegion.le_conditionalMean _ _ hden α η h0a h1a h0e h1e _
      fun context ↦ ?_
    obtain ⟨architecture, environment⟩ := context
    cases architecture <;> cases environment <;>
      simp only [cornerAccumulator, r2Weighted_eq, r2Defined_eq,
        late_r2Weighted_corner_zero_zero, late_r2Weighted_corner_zero_one,
        late_r2Weighted_corner_one_zero, late_r2Weighted_corner_one_one,
        late_r2Defined_corner_zero_zero, late_r2Defined_corner_zero_one,
        late_r2Defined_corner_one_zero, late_r2Defined_corner_one_one] <;> norm_num
  · refine ArchitectureEnvironmentRegion.conditionalMean_le _ _ hden α η h0a h1a h0e h1e _
      fun context ↦ ?_
    obtain ⟨architecture, environment⟩ := context
    cases architecture <;> cases environment <;>
      simp only [cornerAccumulator, r2Weighted_eq, r2Defined_eq,
        late_r2Weighted_corner_zero_zero, late_r2Weighted_corner_zero_one,
        late_r2Weighted_corner_one_zero, late_r2Weighted_corner_one_one,
        late_r2Defined_corner_zero_zero, late_r2Defined_corner_zero_one,
        late_r2Defined_corner_one_zero, late_r2Defined_corner_one_one] <;> norm_num

/-- NOTE2 section 9, late migration: over every independent architecture and environment law
the conditional expected target to source squared-correlation ratio lies between its corner
ratios at `(A, E) = (0, 1)` and `(1, 0)`. -/
theorem late_r2Portability_range (α η : ℝ) (h0a : 0 ≤ α) (h1a : α ≤ 1) (h0e : 0 ≤ η)
    (h1e : η ≤ 1) :
    cornerAccumulator lateTerminalEntries ratioWeighted (false, true) /
        cornerAccumulator lateTerminalEntries ratioDefined (false, true) ≤
      ArchitectureEnvironmentRegion.conditionalMean
        (cornerAccumulator lateTerminalEntries ratioWeighted)
        (cornerAccumulator lateTerminalEntries ratioDefined) α η ∧
    ArchitectureEnvironmentRegion.conditionalMean
        (cornerAccumulator lateTerminalEntries ratioWeighted)
        (cornerAccumulator lateTerminalEntries ratioDefined) α η ≤
      cornerAccumulator lateTerminalEntries ratioWeighted (true, false) /
        cornerAccumulator lateTerminalEntries ratioDefined (true, false) := by
  have hden : ∀ context, 0 < cornerAccumulator lateTerminalEntries ratioDefined context := by
    rintro ⟨architecture, environment⟩
    cases architecture <;> cases environment <;>
      simp only [cornerAccumulator, ratioDefined_eq, late_ratioDefined_corner_zero_zero,
        late_ratioDefined_corner_zero_one, late_ratioDefined_corner_one_zero,
        late_ratioDefined_corner_one_one] <;> norm_num
  constructor
  · refine ArchitectureEnvironmentRegion.le_conditionalMean _ _ hden α η h0a h1a h0e h1e _
      fun context ↦ ?_
    obtain ⟨architecture, environment⟩ := context
    cases architecture <;> cases environment <;>
      simp only [cornerAccumulator, ratioWeighted_eq, ratioDefined_eq,
        late_ratioWeighted_corner_zero_zero, late_ratioWeighted_corner_zero_one,
        late_ratioWeighted_corner_one_zero, late_ratioWeighted_corner_one_one,
        late_ratioDefined_corner_zero_zero, late_ratioDefined_corner_zero_one,
        late_ratioDefined_corner_one_zero, late_ratioDefined_corner_one_one] <;> norm_num
  · refine ArchitectureEnvironmentRegion.conditionalMean_le _ _ hden α η h0a h1a h0e h1e _
      fun context ↦ ?_
    obtain ⟨architecture, environment⟩ := context
    cases architecture <;> cases environment <;>
      simp only [cornerAccumulator, ratioWeighted_eq, ratioDefined_eq,
        late_ratioWeighted_corner_zero_zero, late_ratioWeighted_corner_zero_one,
        late_ratioWeighted_corner_one_zero, late_ratioWeighted_corner_one_one,
        late_ratioDefined_corner_zero_zero, late_ratioDefined_corner_zero_one,
        late_ratioDefined_corner_one_zero, late_ratioDefined_corner_one_one] <;> norm_num

/-! ## Attainment and the displayed decimals -/

/-- NOTE2 section 9: every range above is attained, since the reported conditional mean at a
corner of the square is the corner ratio. -/
theorem range_attained (entries : List ((Bool × Bool) × TerminalTypes × ℚ))
    (report defined : Bool × Bool → LearnerAtom → TerminalTypes → ℚ)
    (architecture environment : Bool) :
    ArchitectureEnvironmentRegion.conditionalMean (cornerAccumulator entries report)
        (cornerAccumulator entries defined) (if architecture then 1 else 0)
        (if environment then 1 else 0) =
      cornerAccumulator entries report (architecture, environment) /
        cornerAccumulator entries defined (architecture, environment) :=
  ArchitectureEnvironmentRegion.conditionalMean_corner _ _ architecture environment

/-- NOTE2 section 9, early migration: the exact range endpoints round to the displayed
`[0.068002053, 0.127845382]` and `[0.656051142, 0.886234435]`. -/
theorem early_range_decimals :
    |cornerAccumulator earlyTerminalEntries r2Weighted (true, false) /
        cornerAccumulator earlyTerminalEntries r2Defined (true, false) - 68002053 / 10 ^ 9| ≤
      1 / (2 * 10 ^ 9) ∧
    |cornerAccumulator earlyTerminalEntries r2Weighted (false, true) /
        cornerAccumulator earlyTerminalEntries r2Defined (false, true) - 127845382 / 10 ^ 9| ≤
      1 / (2 * 10 ^ 9) ∧
    |cornerAccumulator earlyTerminalEntries ratioWeighted (false, true) /
        cornerAccumulator earlyTerminalEntries ratioDefined (false, true) -
          656051142 / 10 ^ 9| ≤
      1 / (2 * 10 ^ 9) ∧
    |cornerAccumulator earlyTerminalEntries ratioWeighted (false, false) /
        cornerAccumulator earlyTerminalEntries ratioDefined (false, false) -
          886234435 / 10 ^ 9| ≤
      1 / (2 * 10 ^ 9) := by
  simp only [cornerAccumulator, r2Weighted_eq, r2Defined_eq, ratioWeighted_eq, ratioDefined_eq,
    early_r2Weighted_corner_one_zero, early_r2Defined_corner_one_zero,
    early_r2Weighted_corner_zero_one, early_r2Defined_corner_zero_one,
    early_ratioWeighted_corner_zero_one, early_ratioDefined_corner_zero_one,
    early_ratioWeighted_corner_zero_zero, early_ratioDefined_corner_zero_zero]
  norm_num [abs_le]

/-- NOTE2 section 9, late migration: the exact range endpoints round to the displayed
`[0.079956608, 0.140641522]` and `[0.743653435, 1.035331073]`. -/
theorem late_range_decimals :
    |cornerAccumulator lateTerminalEntries r2Weighted (true, false) /
        cornerAccumulator lateTerminalEntries r2Defined (true, false) - 79956608 / 10 ^ 9| ≤
      1 / (2 * 10 ^ 9) ∧
    |cornerAccumulator lateTerminalEntries r2Weighted (false, true) /
        cornerAccumulator lateTerminalEntries r2Defined (false, true) - 140641522 / 10 ^ 9| ≤
      1 / (2 * 10 ^ 9) ∧
    |cornerAccumulator lateTerminalEntries ratioWeighted (false, true) /
        cornerAccumulator lateTerminalEntries ratioDefined (false, true) -
          743653435 / 10 ^ 9| ≤
      1 / (2 * 10 ^ 9) ∧
    |cornerAccumulator lateTerminalEntries ratioWeighted (true, false) /
        cornerAccumulator lateTerminalEntries ratioDefined (true, false) -
          1035331073 / 10 ^ 9| ≤
      1 / (2 * 10 ^ 9) := by
  simp only [cornerAccumulator, r2Weighted_eq, r2Defined_eq, ratioWeighted_eq, ratioDefined_eq,
    late_r2Weighted_corner_one_zero, late_r2Defined_corner_one_zero,
    late_r2Weighted_corner_zero_one, late_r2Defined_corner_zero_one,
    late_ratioWeighted_corner_zero_one, late_ratioDefined_corner_zero_one,
    late_ratioWeighted_corner_one_zero, late_ratioDefined_corner_one_zero]
  norm_num [abs_le]

end Descent.Portability.ReferenceExperimentRegion
