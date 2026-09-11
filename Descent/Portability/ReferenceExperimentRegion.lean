/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.ReferenceExperimentTable

assert_below Descent.Decision Descent.Program

/-!
# The full-square range table of the NOTE2 section 9 reference experiment

NOTE2 section 9 closes with the exact ranges, over every independent architecture and
environment law in the whole square, of two conditional expected population outputs: the
target squared correlation and the target to source squared-correlation ratio. This module
proves both ranges for both migration histories through the corpus independent-mixture region
`ArchitectureEnvironmentRegion`.

A report of the reference experiment is a context-mass average of four corner accumulators,
one for each architecture and environment context (`historyReport_eq_corners`), and at the
reference probabilities `(3/5, 2/3)` the corpus mixed numerator is exactly the history report
(`mixtureNumerator_reference`). The corner accumulators of the weighted numerator and of the
definedness mass are decided in the kernel from the concrete model. The corpus theorem
`conditionalMean_eq_corner_combination` makes the reported conditional mean on the square a
convex combination of the four corner ratios with weights `π_ae d_ae`, so
`le_conditionalMean` and `conditionalMean_le` bound it by the least and the greatest corner
ratio, and `conditionalMean_corner` shows both bounds are attained at the displayed corners.

Proved here, for both histories: the exact corner accumulators; the range theorems on the
whole square; the attainment at the corners `(A, E) = (1, 0)` and `(0, 1)` for the squared
correlation, and at the corners of the ratio; and the rounding of the exact endpoints to the
nine-digit decimals of the section 9 table, stated as rational bounds.

## Empirical status

None. The bodies here are exact rational arithmetic on a completely specified finite model
and a convex-combination inequality, so no measurement can bear on these ranges.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.ReferenceExperimentRegion

open RationalReportClosure ReferenceExperimentLaw ReferenceExperimentTable

/-! ## Corner accumulators -/

/-- The corner accumulator of a report in one architecture and environment context: the report
weighted by the learner-atom and terminal-census masses of that context. -/
def cornerReport (history : History)
    (report : Bool × Bool → LearnerAtom → TerminalTypes → ℚ) (context : Bool × Bool) : ℚ :=
  ∑ atom, if atomMass context atom = 0 then 0
    else atomMass context atom * ∑ terminal, terminalMass history context terminal *
      report context atom terminal

/-- A history report is the context-mass average of its corner accumulators. -/
theorem historyReport_eq_corners (history : History)
    (report : Bool × Bool → LearnerAtom → TerminalTypes → ℚ) :
    historyReport history report =
      ∑ context, contextMass context * cornerReport history report context := rfl

/-- A corner accumulator carried to the real numbers, the input of the independent-mixture
region of `ArchitectureEnvironmentRegion`. -/
noncomputable def cornerAccumulator (history : History)
    (report : Bool × Bool → LearnerAtom → TerminalTypes → ℚ) (context : Bool × Bool) : ℝ :=
  (cornerReport history report context : ℝ)

/-- At the reference probabilities `(3/5, 2/3)` the corpus mixed numerator of the corner
accumulators is the history report. -/
theorem mixtureNumerator_reference (history : History)
    (report : Bool × Bool → LearnerAtom → TerminalTypes → ℚ) :
    ArchitectureEnvironmentRegion.mixtureNumerator (cornerAccumulator history report)
        (3 / 5) (2 / 3) = (historyReport history report : ℝ) := by
  rw [historyReport_eq_corners, Rat.cast_sum]
  unfold ArchitectureEnvironmentRegion.mixtureNumerator
  refine Finset.sum_congr rfl fun context _ ↦ ?_
  rw [Rat.cast_mul, contextMass_eq_cellWeight]
  rfl

/-- The weighted numerator of the population target squared correlation. -/
def r2Weighted (context : Bool × Bool) (atom : LearnerAtom) (terminal : TerminalTypes) : ℚ :=
  weightedValue (targetR2 context atom terminal)

/-- The definedness indicator of the population target squared correlation. -/
def r2Defined (context : Bool × Bool) (atom : LearnerAtom) (terminal : TerminalTypes) : ℚ :=
  definedIndicator (targetR2 context atom terminal)

/-- The weighted numerator of the target to source squared-correlation ratio. -/
def ratioWeighted (context : Bool × Bool) (atom : LearnerAtom) (terminal : TerminalTypes) :
    ℚ :=
  weightedValue (r2Portability context atom terminal)

/-- The definedness indicator of the target to source squared-correlation ratio. -/
def ratioDefined (context : Bool × Bool) (atom : LearnerAtom) (terminal : TerminalTypes) :
    ℚ :=
  definedIndicator (r2Portability context atom terminal)

/-- A corner accumulator computed from a tabled terminal law. -/
def cornerTableReport (entries : List ((Bool × Bool) × TerminalTypes × ℚ))
    (report : Bool × Bool → LearnerAtom → TerminalTypes → ℚ) (context : Bool × Bool) : ℚ :=
  ∑ atom, if atomMass context atom = 0 then 0
    else atomMass context atom * ∑ terminal, terminalTable entries context terminal *
      report context atom terminal

/-- Every early migration corner accumulator is computed from the tabled early terminal law. -/
theorem early_cornerReport_table (report : Bool × Bool → LearnerAtom → TerminalTypes → ℚ)
    (context : Bool × Bool) :
    cornerReport earlyMigration report context =
      cornerTableReport earlyTerminalEntries report context := by
  simp only [cornerReport, cornerTableReport, early_terminalMass_table]

/-- Every late migration corner accumulator is computed from the tabled late terminal law. -/
theorem late_cornerReport_table (report : Bool × Bool → LearnerAtom → TerminalTypes → ℚ)
    (context : Bool × Bool) :
    cornerReport lateMigration report context =
      cornerTableReport lateTerminalEntries report context := by
  simp only [cornerReport, cornerTableReport, late_terminalMass_table]

/-- NOTE2 section 9, early migration: the exact corner accumulators of the target squared
correlation and of the target to source ratio, context by context. -/
theorem early_corner_values :
    cornerReport earlyMigration r2Weighted (false, false) =
      82739716563576554120212289717 / 5102838200229873204649682534400 ∧
    cornerReport earlyMigration r2Defined (false, false) =
      17749001596142659 / 132801140411596800 ∧
    cornerReport earlyMigration ratioWeighted (false, false) =
      24176450189676116616122240117 / 204113528009194928185987301376 ∧
    cornerReport earlyMigration ratioDefined (false, false) =
      17749001596142659 / 132801140411596800 ∧
    cornerReport earlyMigration r2Weighted (false, true) =
      36007959895639501574471981286619 / 1998138274887992945085039771648000 ∧
    cornerReport earlyMigration r2Defined (false, true) =
      5161535759051312863 / 36617695446800793600 ∧
    cornerReport earlyMigration ratioWeighted (false, true) =
      4199508752136724317099778106735813 / 45412233520181657842841812992000000 ∧
    cornerReport earlyMigration ratioDefined (false, true) =
      5161535759051312863 / 36617695446800793600 ∧
    cornerReport earlyMigration r2Weighted (true, false) =
      14937859607027033112107892349 / 1791289360311594241095421132800 ∧
    cornerReport earlyMigration r2Defined (true, false) =
      337222347318642229 / 2749892668560506880 ∧
    cornerReport earlyMigration ratioWeighted (true, false) =
      1204447361564081895670839434267 / 12056755309789576622757642240000 ∧
    cornerReport earlyMigration ratioDefined (true, false) =
      337222347318642229 / 2749892668560506880 ∧
    cornerReport earlyMigration r2Weighted (true, true) =
      72628546319475248438835091715 / 5354033484707493284149349842944 ∧
    cornerReport earlyMigration r2Defined (true, true) =
      4892584425047299 / 37737506808004608 ∧
    cornerReport earlyMigration ratioWeighted (true, true) =
      61277721092998762608592682195 / 585597412389882077953835139072 ∧
    cornerReport earlyMigration ratioDefined (true, true) =
      4892584425047299 / 37737506808004608 := by
  simp only [early_cornerReport_table]
  decide +kernel

/-- NOTE2 section 9, late migration: the exact corner accumulators of the target squared
correlation and of the target to source ratio, context by context. -/
theorem late_corner_values :
    cornerReport lateMigration r2Weighted (false, false) =
      8626505700564460991087856179419 / 272434861690050452759352495308800 ∧
    cornerReport lateMigration r2Defined (false, false) =
      887086120860564100859 / 3743575614109306060800 ∧
    cornerReport lateMigration ratioWeighted (false, false) =
      2667595541796680609872091120219 / 10897394467602018110374099812352 ∧
    cornerReport lateMigration ratioDefined (false, false) =
      887086120860564100859 / 3743575614109306060800 ∧
    cornerReport lateMigration r2Weighted (false, true) =
      210717142033005539647679254987981 / 6044368281536178658882245309235200 ∧
    cornerReport lateMigration r2Defined (false, true) =
      386593398281726697861601 / 1559620884470139401011200 ∧
    cornerReport lateMigration ratioWeighted (false, true) =
      126611812445030139896090128355079391 / 686860031992747574872982421504000000 ∧
    cornerReport lateMigration ratioDefined (false, true) =
      386593398281726697861601 / 1559620884470139401011200 ∧
    cornerReport lateMigration r2Weighted (true, false) =
      46632437564670815344455156841 / 2820214498823908790296064819200 ∧
    cornerReport lateMigration r2Defined (true, false) =
      401108410080243106183 / 1939590962224677519360 ∧
    cornerReport lateMigration ratioWeighted (true, false) =
      580603522530829031822949686009 / 2711744710407604606053908480000 ∧
    cornerReport lateMigration ratioDefined (true, false) =
      401108410080243106183 / 1939590962224677519360 ∧
    cornerReport lateMigration r2Weighted (true, true) =
      30715138556525215845240192566305 / 1165506164202262444293261593935872 ∧
    cornerReport lateMigration r2Defined (true, true) =
      53938343310218201845309 / 248683980913633853964288 ∧
    cornerReport lateMigration ratioWeighted (true, true) =
      26734360594894384452151930418545 / 127477236709622454844575486836736 ∧
    cornerReport lateMigration ratioDefined (true, true) =
      53938343310218201845309 / 248683980913633853964288 := by
  simp only [late_cornerReport_table]
  decide +kernel

/-! ## The ranges on the whole square -/

/-- NOTE2 section 9, early migration: over every independent architecture and environment law
the conditional expected population target squared correlation lies between its corner ratios
at `(A, E) = (1, 0)` and `(0, 1)`. -/
theorem early_target_r2_range (α η : ℝ) (h0a : 0 ≤ α) (h1a : α ≤ 1) (h0e : 0 ≤ η)
    (h1e : η ≤ 1) :
    cornerAccumulator earlyMigration r2Weighted (true, false) /
        cornerAccumulator earlyMigration r2Defined (true, false) ≤
      ArchitectureEnvironmentRegion.conditionalMean (cornerAccumulator earlyMigration r2Weighted)
        (cornerAccumulator earlyMigration r2Defined) α η ∧
    ArchitectureEnvironmentRegion.conditionalMean (cornerAccumulator earlyMigration r2Weighted)
        (cornerAccumulator earlyMigration r2Defined) α η ≤
      cornerAccumulator earlyMigration r2Weighted (false, true) /
        cornerAccumulator earlyMigration r2Defined (false, true) := by
  obtain ⟨h00w, h00d, -, -, h01w, h01d, -, -, h10w, h10d, -, -, h11w, h11d, -, -⟩ :=
    early_corner_values
  have hden : ∀ context, 0 < cornerAccumulator earlyMigration r2Defined context := by
    rintro ⟨architecture, environment⟩
    cases architecture <;> cases environment <;>
      simp only [cornerAccumulator, h00d, h01d, h10d, h11d] <;> norm_num
  constructor
  · refine ArchitectureEnvironmentRegion.le_conditionalMean _ _ hden α η h0a h1a h0e h1e _
      fun context ↦ ?_
    obtain ⟨architecture, environment⟩ := context
    cases architecture <;> cases environment <;>
      simp only [cornerAccumulator, h00w, h00d, h01w, h01d, h10w, h10d, h11w, h11d] <;> norm_num
  · refine ArchitectureEnvironmentRegion.conditionalMean_le _ _ hden α η h0a h1a h0e h1e _
      fun context ↦ ?_
    obtain ⟨architecture, environment⟩ := context
    cases architecture <;> cases environment <;>
      simp only [cornerAccumulator, h00w, h00d, h01w, h01d, h10w, h10d, h11w, h11d] <;> norm_num

/-- NOTE2 section 9, early migration: over every independent architecture and environment law
the conditional expected target to source squared-correlation ratio lies between its corner
ratios at `(A, E) = (0, 1)` and `(0, 0)`. -/
theorem early_r2Portability_range (α η : ℝ) (h0a : 0 ≤ α) (h1a : α ≤ 1) (h0e : 0 ≤ η)
    (h1e : η ≤ 1) :
    cornerAccumulator earlyMigration ratioWeighted (false, true) /
        cornerAccumulator earlyMigration ratioDefined (false, true) ≤
      ArchitectureEnvironmentRegion.conditionalMean
        (cornerAccumulator earlyMigration ratioWeighted)
        (cornerAccumulator earlyMigration ratioDefined) α η ∧
    ArchitectureEnvironmentRegion.conditionalMean (cornerAccumulator earlyMigration ratioWeighted)
        (cornerAccumulator earlyMigration ratioDefined) α η ≤
      cornerAccumulator earlyMigration ratioWeighted (false, false) /
        cornerAccumulator earlyMigration ratioDefined (false, false) := by
  obtain ⟨-, -, h00w, h00d, -, -, h01w, h01d, -, -, h10w, h10d, -, -, h11w, h11d⟩ :=
    early_corner_values
  have hden : ∀ context, 0 < cornerAccumulator earlyMigration ratioDefined context := by
    rintro ⟨architecture, environment⟩
    cases architecture <;> cases environment <;>
      simp only [cornerAccumulator, h00d, h01d, h10d, h11d] <;> norm_num
  constructor
  · refine ArchitectureEnvironmentRegion.le_conditionalMean _ _ hden α η h0a h1a h0e h1e _
      fun context ↦ ?_
    obtain ⟨architecture, environment⟩ := context
    cases architecture <;> cases environment <;>
      simp only [cornerAccumulator, h00w, h00d, h01w, h01d, h10w, h10d, h11w, h11d] <;> norm_num
  · refine ArchitectureEnvironmentRegion.conditionalMean_le _ _ hden α η h0a h1a h0e h1e _
      fun context ↦ ?_
    obtain ⟨architecture, environment⟩ := context
    cases architecture <;> cases environment <;>
      simp only [cornerAccumulator, h00w, h00d, h01w, h01d, h10w, h10d, h11w, h11d] <;> norm_num

/-- NOTE2 section 9, late migration: over every independent architecture and environment law
the conditional expected population target squared correlation lies between its corner ratios
at `(A, E) = (1, 0)` and `(0, 1)`. -/
theorem late_target_r2_range (α η : ℝ) (h0a : 0 ≤ α) (h1a : α ≤ 1) (h0e : 0 ≤ η)
    (h1e : η ≤ 1) :
    cornerAccumulator lateMigration r2Weighted (true, false) /
        cornerAccumulator lateMigration r2Defined (true, false) ≤
      ArchitectureEnvironmentRegion.conditionalMean (cornerAccumulator lateMigration r2Weighted)
        (cornerAccumulator lateMigration r2Defined) α η ∧
    ArchitectureEnvironmentRegion.conditionalMean (cornerAccumulator lateMigration r2Weighted)
        (cornerAccumulator lateMigration r2Defined) α η ≤
      cornerAccumulator lateMigration r2Weighted (false, true) /
        cornerAccumulator lateMigration r2Defined (false, true) := by
  obtain ⟨h00w, h00d, -, -, h01w, h01d, -, -, h10w, h10d, -, -, h11w, h11d, -, -⟩ :=
    late_corner_values
  have hden : ∀ context, 0 < cornerAccumulator lateMigration r2Defined context := by
    rintro ⟨architecture, environment⟩
    cases architecture <;> cases environment <;>
      simp only [cornerAccumulator, h00d, h01d, h10d, h11d] <;> norm_num
  constructor
  · refine ArchitectureEnvironmentRegion.le_conditionalMean _ _ hden α η h0a h1a h0e h1e _
      fun context ↦ ?_
    obtain ⟨architecture, environment⟩ := context
    cases architecture <;> cases environment <;>
      simp only [cornerAccumulator, h00w, h00d, h01w, h01d, h10w, h10d, h11w, h11d] <;> norm_num
  · refine ArchitectureEnvironmentRegion.conditionalMean_le _ _ hden α η h0a h1a h0e h1e _
      fun context ↦ ?_
    obtain ⟨architecture, environment⟩ := context
    cases architecture <;> cases environment <;>
      simp only [cornerAccumulator, h00w, h00d, h01w, h01d, h10w, h10d, h11w, h11d] <;> norm_num

/-- NOTE2 section 9, late migration: over every independent architecture and environment law
the conditional expected target to source squared-correlation ratio lies between its corner
ratios at `(A, E) = (0, 1)` and `(1, 0)`. -/
theorem late_r2Portability_range (α η : ℝ) (h0a : 0 ≤ α) (h1a : α ≤ 1) (h0e : 0 ≤ η)
    (h1e : η ≤ 1) :
    cornerAccumulator lateMigration ratioWeighted (false, true) /
        cornerAccumulator lateMigration ratioDefined (false, true) ≤
      ArchitectureEnvironmentRegion.conditionalMean (cornerAccumulator lateMigration ratioWeighted)
        (cornerAccumulator lateMigration ratioDefined) α η ∧
    ArchitectureEnvironmentRegion.conditionalMean (cornerAccumulator lateMigration ratioWeighted)
        (cornerAccumulator lateMigration ratioDefined) α η ≤
      cornerAccumulator lateMigration ratioWeighted (true, false) /
        cornerAccumulator lateMigration ratioDefined (true, false) := by
  obtain ⟨-, -, h00w, h00d, -, -, h01w, h01d, -, -, h10w, h10d, -, -, h11w, h11d⟩ :=
    late_corner_values
  have hden : ∀ context, 0 < cornerAccumulator lateMigration ratioDefined context := by
    rintro ⟨architecture, environment⟩
    cases architecture <;> cases environment <;>
      simp only [cornerAccumulator, h00d, h01d, h10d, h11d] <;> norm_num
  constructor
  · refine ArchitectureEnvironmentRegion.le_conditionalMean _ _ hden α η h0a h1a h0e h1e _
      fun context ↦ ?_
    obtain ⟨architecture, environment⟩ := context
    cases architecture <;> cases environment <;>
      simp only [cornerAccumulator, h00w, h00d, h01w, h01d, h10w, h10d, h11w, h11d] <;> norm_num
  · refine ArchitectureEnvironmentRegion.conditionalMean_le _ _ hden α η h0a h1a h0e h1e _
      fun context ↦ ?_
    obtain ⟨architecture, environment⟩ := context
    cases architecture <;> cases environment <;>
      simp only [cornerAccumulator, h00w, h00d, h01w, h01d, h10w, h10d, h11w, h11d] <;> norm_num

/-! ## Attainment and the displayed decimals -/

/-- NOTE2 section 9: every range above is attained, since the reported conditional mean at a
corner of the square is the corner ratio. -/
theorem range_attained (history : History)
    (report defined : Bool × Bool → LearnerAtom → TerminalTypes → ℚ)
    (architecture environment : Bool) :
    ArchitectureEnvironmentRegion.conditionalMean (cornerAccumulator history report)
        (cornerAccumulator history defined) (if architecture then 1 else 0)
        (if environment then 1 else 0) =
      cornerAccumulator history report (architecture, environment) /
        cornerAccumulator history defined (architecture, environment) :=
  ArchitectureEnvironmentRegion.conditionalMean_corner _ _ architecture environment

/-- NOTE2 section 9, early migration: the exact range endpoints round to the displayed
`[0.068002053, 0.127845382]` and `[0.656051142, 0.886234435]`. -/
theorem early_range_decimals :
    |cornerAccumulator earlyMigration r2Weighted (true, false) /
        cornerAccumulator earlyMigration r2Defined (true, false) - 68002053 / 10 ^ 9| ≤
      1 / (2 * 10 ^ 9) ∧
    |cornerAccumulator earlyMigration r2Weighted (false, true) /
        cornerAccumulator earlyMigration r2Defined (false, true) - 127845382 / 10 ^ 9| ≤
      1 / (2 * 10 ^ 9) ∧
    |cornerAccumulator earlyMigration ratioWeighted (false, true) /
        cornerAccumulator earlyMigration ratioDefined (false, true) - 656051142 / 10 ^ 9| ≤
      1 / (2 * 10 ^ 9) ∧
    |cornerAccumulator earlyMigration ratioWeighted (false, false) /
        cornerAccumulator earlyMigration ratioDefined (false, false) - 886234435 / 10 ^ 9| ≤
      1 / (2 * 10 ^ 9) := by
  obtain ⟨h00w, h00d, h00q, h00e, h01w, h01d, h01q, h01e, h10w, h10d, -, -, -, -, -, -⟩ :=
    early_corner_values
  simp only [cornerAccumulator, h00q, h00e, h01w, h01d, h01q, h01e, h10w, h10d]
  norm_num [abs_le]

/-- NOTE2 section 9, late migration: the exact range endpoints round to the displayed
`[0.079956608, 0.140641522]` and `[0.743653435, 1.035331073]`. -/
theorem late_range_decimals :
    |cornerAccumulator lateMigration r2Weighted (true, false) /
        cornerAccumulator lateMigration r2Defined (true, false) - 79956608 / 10 ^ 9| ≤
      1 / (2 * 10 ^ 9) ∧
    |cornerAccumulator lateMigration r2Weighted (false, true) /
        cornerAccumulator lateMigration r2Defined (false, true) - 140641522 / 10 ^ 9| ≤
      1 / (2 * 10 ^ 9) ∧
    |cornerAccumulator lateMigration ratioWeighted (false, true) /
        cornerAccumulator lateMigration ratioDefined (false, true) - 743653435 / 10 ^ 9| ≤
      1 / (2 * 10 ^ 9) ∧
    |cornerAccumulator lateMigration ratioWeighted (true, false) /
        cornerAccumulator lateMigration ratioDefined (true, false) - 1035331073 / 10 ^ 9| ≤
      1 / (2 * 10 ^ 9) := by
  obtain ⟨-, -, -, -, h01w, h01d, h01q, h01e, h10w, h10d, h10q, h10e, -, -, -, -⟩ :=
    late_corner_values
  simp only [cornerAccumulator, h01w, h01d, h01q, h01e, h10w, h10d, h10q, h10e]
  norm_num [abs_le]

end Descent.Portability.ReferenceExperimentRegion
