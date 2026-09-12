/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.ReferenceExperimentRows
import Descent.Portability.ReferenceExperimentRegion
import Descent.Portability.PortabilityMinimaxLowerBound

assert_below Descent.Decision Descent.Program

/-!
# Two migration histories that no source panel tells apart

The NOTE2 section 9 reference experiment runs one source study and two histories of the target
deme. This module reads that design as the explicit two-point instance of the minimax lower bound
for portability estimation (research front F2).

The parameter is the history of the target deme: early migration at `false`, late migration at
`true` (`twoPointHistory`). The complete experiment of a setting is the joint law of a source
draw and the terminal target census in the draw's context (`experimentLaw`). Under either history
its source marginal is the source law itself (`sum_experimentMass_terminal`). So the two settings
have one source-panel report law (`sourcePanelLaw_toReal`), at total variation distance zero
(`totalVariation_sourcePanelLaw`). This holds for the pooled source study `studyLaw`, context
included, and for the panel of one architecture and environment context (`contextPanelLaw`),
whose learner law is the learner-atom law of the experiment (`atomMass_eq_sum_panelMass`).

The floor comes from the two-point bound of `PortabilityMinimaxLowerBound` at total variation
zero. Take any number `n` of replicate source panels. Every estimator that reads them has worst
expected absolute error over the two settings of at least half the separation of the target
values (`half_separation_le_worstRisk`), and the estimator that reports the midpoint attains it
(`worstRisk_midpoint`). So half the separation is the exact minimax risk (`isLeast_worstRisk`),
and no amount of source data lowers it.

The target functionals differ:
- Pooled over the reference context law, half the separation between the settings is
  `0.00725001…` for the expected target squared correlation given definedness
  (`half_separation_r2`, floor `minimax_floor_r2`), and `0.0736082…` for the target to source
  squared-correlation ratio (`half_separation_r2Portability`, floor
  `minimax_floor_r2Portability`).
- Within one context, the separations are taken at the corners where
  `ReferenceExperimentRegion` attains its full-square ranges:
  - at `(A, E) = (0, 1)`, the upper endpoint of both squared-correlation ranges, half the
    separation is `0.00639807…` (`half_separation_r2_zero_one`, floor
    `minimax_floor_r2_zero_one`);
  - at `(1, 0)`, the lower endpoint of both, it is `0.00597727…` (`half_separation_r2_one_zero`,
    floor `minimax_floor_r2_one_zero`);
  - at `(0, 1)`, the lower endpoint of both ratio ranges, it is `0.0438011…`
    (`half_separation_r2Portability_zero_one`, floor `minimax_floor_r2Portability_zero_one`).

Every separation is an exact rational taken from the corner certificates and the population rows;
nothing here simulates.

## Empirical status

None. The bodies here are exact rational arithmetic on a completely specified finite model and a
two-point inequality, so no measurement can bear on these values.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.PortabilityTwoHistoryInstance

open RationalReportClosure ReferenceExperimentLaw ReferenceExperimentTable
  ReferenceExperimentEarlyMomentCorners ReferenceExperimentEarlyLossCorners
  ReferenceExperimentLateMomentCorners ReferenceExperimentLateLossCorners ReferenceExperimentRows
  ReferenceExperimentRegion
open FourCellCohortLaw (cohortLaw)

/-! ## The two settings -/

/-- NOTE2 section 9: the two parameter settings, early migration at `false` and late migration
at `true`. -/
def twoPointHistory : Bool → History
  | false => earlyMigration
  | true => lateMigration

/-- The tabled terminal law of a parameter setting. -/
def twoPointEntries : Bool → List ((Bool × Bool) × TerminalTypes × ℚ)
  | false => earlyTerminalEntries
  | true => lateTerminalEntries

/-- The terminal law of a setting is its tabled terminal law. -/
theorem terminalMass_twoPointHistory (late : Bool) (context : Bool × Bool)
    (terminal : TerminalTypes) :
    terminalMass (twoPointHistory late) context terminal =
      terminalTable (twoPointEntries late) context terminal := by
  cases late
  · exact early_terminalMass_table context terminal
  · exact late_terminalMass_table context terminal

theorem terminalTable_nonneg :
    ∀ late context terminal, 0 ≤ terminalTable (twoPointEntries late) context terminal := by
  decide +kernel

/-- Each tabled terminal law is a probability law. -/
theorem terminalTable_sum :
    ∀ late context, ∑ terminal, terminalTable (twoPointEntries late) context terminal = 1 := by
  decide +kernel

/-! ## The complete experiment, its source marginal and the two-point floor -/

section Experiment

variable {Source : Type*} [Fintype Source] (source : RationalReportLaw Source)
  (contextOf : Source → Bool × Bool)

/-- The joint mass of a source draw and the terminal target census under a setting: the source
law times the terminal law of the target deme in the draw's context. -/
def experimentMass (late : Bool) (outcome : Source × TerminalTypes) : ℚ :=
  source.mass outcome.1 * terminalMass (twoPointHistory late) (contextOf outcome.1) outcome.2

theorem experimentMass_nonneg (late : Bool) (outcome : Source × TerminalTypes) :
    0 ≤ experimentMass source contextOf late outcome := by
  rw [experimentMass, terminalMass_twoPointHistory]
  exact mul_nonneg (source.mass_nonneg _) (terminalTable_nonneg late _ _)

/-- NOTE2 section 9: the source marginal of the complete experiment is the source law, under
either history. -/
theorem sum_experimentMass_terminal (late : Bool) (draw : Source) :
    ∑ terminal, experimentMass source contextOf late (draw, terminal) = source.mass draw := by
  simp only [experimentMass, terminalMass_twoPointHistory, ← Finset.mul_sum, terminalTable_sum,
    mul_one]

theorem sum_experimentMass (late : Bool) :
    ∑ outcome, experimentMass source contextOf late outcome = 1 := by
  rw [Fintype.sum_prod_type]
  simp only [sum_experimentMass_terminal, source.mass_sum]

/-- The complete experiment of a setting as a finite report law. -/
def experimentLaw (late : Bool) : RationalReportLaw (Source × TerminalTypes) where
  mass := experimentMass source contextOf late
  mass_nonneg := experimentMass_nonneg source contextOf late
  mass_sum := sum_experimentMass source contextOf late

/-- The source-panel report law of a setting: the source marginal of its complete experiment,
the law of everything a source-side estimator sees. -/
def sourcePanelLaw (late : Bool) : RationalReportLaw Source where
  mass := fun draw ↦ ∑ terminal, (experimentLaw source contextOf late).mass (draw, terminal)
  mass_nonneg := fun draw ↦
    Finset.sum_nonneg fun terminal _ ↦ experimentMass_nonneg source contextOf late _
  mass_sum := by simp only [experimentLaw, sum_experimentMass_terminal, source.mass_sum]

/-- NOTE2 section 9: the source-panel report law of either setting is the source law. -/
theorem sourcePanelLaw_toReal (late : Bool) :
    (sourcePanelLaw source contextOf late).toReal = source.toReal :=
  FiniteReportLaw.ext fun draw ↦ by
    show ((∑ terminal, experimentMass source contextOf late (draw, terminal) : ℚ) : ℝ) =
      (source.mass draw : ℝ)
    rw [sum_experimentMass_terminal]

/-- The two settings have one source-panel report law. -/
theorem sourcePanelLaw_false_eq_true :
    (sourcePanelLaw source contextOf false).toReal =
      (sourcePanelLaw source contextOf true).toReal := by
  rw [sourcePanelLaw_toReal, sourcePanelLaw_toReal]

/-- The source-panel report laws of the two settings are at total variation distance zero. -/
theorem totalVariation_sourcePanelLaw :
    (sourcePanelLaw source contextOf false).toReal.totalVariation
      (sourcePanelLaw source contextOf true).toReal = 0 := by
  simp only [sourcePanelLaw_false_eq_true, FiniteReportLaw.totalVariation, sub_self, max_self,
    Finset.sum_const_zero]

/-- The worst expected absolute error over the two settings of an estimator that reads `n`
replicate source panels, against the target values `τ`. -/
noncomputable def worstRisk (τ : Bool → ℝ) (n : ℕ) (estimator : (Fin n → Source) → ℝ) : ℝ :=
  max ((cohortLaw (sourcePanelLaw source contextOf false).toReal n).expectation
      fun sample ↦ |estimator sample - τ false|)
    ((cohortLaw (sourcePanelLaw source contextOf true).toReal n).expectation
      fun sample ↦ |estimator sample - τ true|)

/-- F2 with one source-panel report law: every estimator that reads `n` replicate source panels
has worst risk at least half the separation of the target values, for every `n`. -/
theorem half_separation_le_worstRisk (τ : Bool → ℝ) (n : ℕ)
    (estimator : (Fin n → Source) → ℝ) :
    |τ true - τ false| / 2 ≤ worstRisk source contextOf τ n estimator := by
  have h := PortabilityMinimaxLowerBound.lowerBound_cohortLaw_totalVariation
    (sourcePanelLaw source contextOf false).toReal (sourcePanelLaw source contextOf true).toReal
    n (τ false) (τ true) estimator
  rw [totalVariation_sourcePanelLaw, mul_zero, sub_zero,
    max_eq_right (zero_le_one : (0 : ℝ) ≤ 1), mul_one, abs_sub_comm] at h
  exact h

/-- Every bound below half the separation is a strict floor on the worst risk. -/
theorem lt_worstRisk_of_lt_half_separation (τ : Bool → ℝ) (bound : ℝ)
    (hbound : bound < (τ true - τ false) / 2) (n : ℕ) (estimator : (Fin n → Source) → ℝ) :
    bound < worstRisk source contextOf τ n estimator := by
  refine hbound.trans_le
    (le_trans ?_ (half_separation_le_worstRisk source contextOf τ n estimator))
  linarith [le_abs_self (τ true - τ false)]

/-- The floor is attained: the estimator that ignores the panels and reports the midpoint of the
two target values has worst risk exactly half the separation. -/
theorem worstRisk_midpoint (τ : Bool → ℝ) (n : ℕ) :
    worstRisk source contextOf τ n (fun _ ↦ (τ false + τ true) / 2) =
      |τ true - τ false| / 2 := by
  have hconst : ∀ (law : FiniteReportLaw (Fin n → Source)) (value : ℝ),
      law.expectation (fun _ ↦ value) = value := fun law value ↦ by
    rw [FiniteReportLaw.expectation, ← Finset.sum_mul, law.mass_sum, one_mul]
  simp only [worstRisk]
  rw [hconst, hconst, show (τ false + τ true) / 2 - τ false = (τ true - τ false) / 2 by ring,
    show (τ false + τ true) / 2 - τ true = -((τ true - τ false) / 2) by ring, abs_neg, max_self,
    abs_div, abs_two]

/-- Half the separation of the target values is the exact minimax risk of the two-point problem,
for every number of replicate source panels. -/
theorem isLeast_worstRisk (τ : Bool → ℝ) (n : ℕ) :
    IsLeast (Set.range (worstRisk source contextOf τ n)) (|τ true - τ false| / 2) := by
  refine ⟨⟨fun _ ↦ (τ false + τ true) / 2, worstRisk_midpoint source contextOf τ n⟩, ?_⟩
  rintro _ ⟨estimator, rfl⟩
  exact half_separation_le_worstRisk source contextOf τ n estimator

end Experiment

/-! ## The panel of one context -/

/-- The source panel of one architecture and environment context: two training draws and the
validation draw, independent draws from the source population of the context. -/
def panelMass (context : Bool × Bool) (draws : Training × (Fin 3 × Bool)) : ℚ :=
  drawMass context draws.1.1 * drawMass context draws.1.2 * drawMass context draws.2

theorem panelMass_sum : ∀ context, ∑ draws, panelMass context draws = 1 := by
  decide +kernel

/-- The source-panel law of one context. -/
def contextPanelLaw (context : Bool × Bool) : RationalReportLaw (Training × (Fin 3 × Bool)) where
  mass := panelMass context
  mass_nonneg := fun _ ↦
    mul_nonneg (mul_nonneg (drawMass_nonneg _ _) (drawMass_nonneg _ _)) (drawMass_nonneg _ _)
  mass_sum := panelMass_sum context

/-- The learner-atom law of a context is the law of the learner under the context panel. -/
theorem atomMass_eq_sum_panelMass (context : Bool × Bool) (atom : LearnerAtom) :
    atomMass context atom =
      ∑ draws : Training × (Fin 3 × Bool),
        if learnerAtom draws.1 draws.2 = atom then (contextPanelLaw context).mass draws else 0 :=
  rfl

/-! ## The target functionals and their separations -/

/-- The conditional mean of a partial population report given that it is defined, under a
setting and pooled over the reference context law. -/
def givenDefined (late : Bool)
    (weighted defined : Bool × Bool → LearnerAtom → TerminalTypes → ℚ) : ℚ :=
  historyReport (twoPointHistory late) weighted / historyReport (twoPointHistory late) defined

/-- The conditional mean of a partial population report given that it is defined, under a
setting and within one context: the corner ratio of `ReferenceExperimentRegion`. -/
noncomputable def contextGivenDefined (late : Bool)
    (weighted defined : Bool × Bool → LearnerAtom → TerminalTypes → ℚ) (context : Bool × Bool) :
    ℝ :=
  cornerAccumulator (twoPointEntries late) weighted context /
    cornerAccumulator (twoPointEntries late) defined context

/-- NOTE2 section 9: pooled over the reference context law, half the separation of the expected
target squared correlation given definedness between the two settings, `0.00725001…`. -/
theorem half_separation_r2 :
    (7250008 / 10 ^ 9 : ℝ) <
        ((givenDefined true r2Weighted r2Defined : ℝ) -
          givenDefined false r2Weighted r2Defined) / 2 ∧
      ((givenDefined true r2Weighted r2Defined : ℝ) -
          givenDefined false r2Weighted r2Defined) / 2 <
        7250014 / 10 ^ 9 := by
  rw [show givenDefined false r2Weighted r2Defined = _ from early_target_r2_givenDefined,
    show givenDefined true r2Weighted r2Defined = _ from late_target_r2_givenDefined]
  norm_num

/-- NOTE2 section 9: pooled over the reference context law, half the separation of the expected
target to source squared-correlation ratio given definedness, `0.0736082…`. -/
theorem half_separation_r2Portability :
    (73608238 / 10 ^ 9 : ℝ) <
        ((givenDefined true ratioWeighted ratioDefined : ℝ) -
          givenDefined false ratioWeighted ratioDefined) / 2 ∧
      ((givenDefined true ratioWeighted ratioDefined : ℝ) -
          givenDefined false ratioWeighted ratioDefined) / 2 <
        73608244 / 10 ^ 9 := by
  rw [show givenDefined false ratioWeighted ratioDefined = _ from
      early_r2Portability_givenDefined,
    show givenDefined true ratioWeighted ratioDefined = _ from late_r2Portability_givenDefined]
  norm_num

/-- NOTE2 section 9: at `(A, E) = (0, 1)`, where both squared-correlation ranges of
`ReferenceExperimentRegion` attain their upper endpoints, half the separation of the target
squared correlation given definedness, `0.00639807…`. -/
theorem half_separation_r2_zero_one :
    6398067 / 10 ^ 9 <
        (contextGivenDefined true r2Weighted r2Defined (false, true) -
          contextGivenDefined false r2Weighted r2Defined (false, true)) / 2 ∧
      (contextGivenDefined true r2Weighted r2Defined (false, true) -
          contextGivenDefined false r2Weighted r2Defined (false, true)) / 2 <
        6398073 / 10 ^ 9 := by
  simp only [contextGivenDefined, twoPointEntries, cornerAccumulator, r2Weighted_eq,
    r2Defined_eq, early_r2Weighted_corner_zero_one, early_r2Defined_corner_zero_one,
    late_r2Weighted_corner_zero_one, late_r2Defined_corner_zero_one]
  norm_num

/-- NOTE2 section 9: at `(A, E) = (1, 0)`, where both squared-correlation ranges attain their
lower endpoints, half the separation of the target squared correlation given definedness,
`0.00597727…`. -/
theorem half_separation_r2_one_zero :
    5977274 / 10 ^ 9 <
        (contextGivenDefined true r2Weighted r2Defined (true, false) -
          contextGivenDefined false r2Weighted r2Defined (true, false)) / 2 ∧
      (contextGivenDefined true r2Weighted r2Defined (true, false) -
          contextGivenDefined false r2Weighted r2Defined (true, false)) / 2 <
        5977281 / 10 ^ 9 := by
  simp only [contextGivenDefined, twoPointEntries, cornerAccumulator, r2Weighted_eq,
    r2Defined_eq, early_r2Weighted_corner_one_zero, early_r2Defined_corner_one_zero,
    late_r2Weighted_corner_one_zero, late_r2Defined_corner_one_zero]
  norm_num

/-- NOTE2 section 9: at `(A, E) = (0, 1)`, where both ratio ranges attain their lower endpoints,
half the separation of the target to source squared-correlation ratio given definedness,
`0.0438011…`. -/
theorem half_separation_r2Portability_zero_one :
    43801143 / 10 ^ 9 <
        (contextGivenDefined true ratioWeighted ratioDefined (false, true) -
          contextGivenDefined false ratioWeighted ratioDefined (false, true)) / 2 ∧
      (contextGivenDefined true ratioWeighted ratioDefined (false, true) -
          contextGivenDefined false ratioWeighted ratioDefined (false, true)) / 2 <
        43801150 / 10 ^ 9 := by
  simp only [contextGivenDefined, twoPointEntries, cornerAccumulator, ratioWeighted_eq,
    ratioDefined_eq, early_ratioWeighted_corner_zero_one, early_ratioDefined_corner_zero_one,
    late_ratioWeighted_corner_zero_one, late_ratioDefined_corner_zero_one]
  norm_num

/-! ## The F2 floors of the reference experiment -/

/-- F2 at NOTE2 section 9, pooled over the reference context law: from any number of replicate
source studies, every estimator of the expected target squared correlation given definedness has
worst risk above `0.00725`. -/
theorem minimax_floor_r2 (n : ℕ) (estimator : (Fin n → SourceStudy) → ℝ) :
    (7250008 / 10 ^ 9 : ℝ) <
      worstRisk studyLaw Prod.fst (fun late ↦ (givenDefined late r2Weighted r2Defined : ℝ)) n
        estimator :=
  lt_worstRisk_of_lt_half_separation studyLaw Prod.fst
    (fun late ↦ (givenDefined late r2Weighted r2Defined : ℝ)) _ half_separation_r2.1 n estimator

/-- F2 at NOTE2 section 9, pooled over the reference context law: from any number of replicate
source studies, every estimator of the expected target to source squared-correlation ratio given
definedness has worst risk above `0.0736`. -/
theorem minimax_floor_r2Portability (n : ℕ) (estimator : (Fin n → SourceStudy) → ℝ) :
    (73608238 / 10 ^ 9 : ℝ) <
      worstRisk studyLaw Prod.fst
        (fun late ↦ (givenDefined late ratioWeighted ratioDefined : ℝ)) n estimator :=
  lt_worstRisk_of_lt_half_separation studyLaw Prod.fst
    (fun late ↦ (givenDefined late ratioWeighted ratioDefined : ℝ)) _
    half_separation_r2Portability.1 n estimator

/-- F2 at NOTE2 section 9 within the context `(A, E) = (0, 1)`: from any number of replicate
panels of that context, every estimator of the target squared correlation given definedness has
worst risk above `0.00639`. -/
theorem minimax_floor_r2_zero_one (n : ℕ)
    (estimator : (Fin n → Training × (Fin 3 × Bool)) → ℝ) :
    (6398067 / 10 ^ 9 : ℝ) <
      worstRisk (contextPanelLaw (false, true)) (fun _ ↦ (false, true))
        (fun late ↦ contextGivenDefined late r2Weighted r2Defined (false, true)) n estimator :=
  lt_worstRisk_of_lt_half_separation (contextPanelLaw (false, true)) (fun _ ↦ (false, true))
    (fun late ↦ contextGivenDefined late r2Weighted r2Defined (false, true)) _
    half_separation_r2_zero_one.1 n estimator

/-- F2 at NOTE2 section 9 within the context `(A, E) = (1, 0)`: from any number of replicate
panels of that context, every estimator of the target squared correlation given definedness has
worst risk above `0.00597`. -/
theorem minimax_floor_r2_one_zero (n : ℕ)
    (estimator : (Fin n → Training × (Fin 3 × Bool)) → ℝ) :
    (5977274 / 10 ^ 9 : ℝ) <
      worstRisk (contextPanelLaw (true, false)) (fun _ ↦ (true, false))
        (fun late ↦ contextGivenDefined late r2Weighted r2Defined (true, false)) n estimator :=
  lt_worstRisk_of_lt_half_separation (contextPanelLaw (true, false)) (fun _ ↦ (true, false))
    (fun late ↦ contextGivenDefined late r2Weighted r2Defined (true, false)) _
    half_separation_r2_one_zero.1 n estimator

/-- F2 at NOTE2 section 9 within the context `(A, E) = (0, 1)`: from any number of replicate
panels of that context, every estimator of the target to source squared-correlation ratio given
definedness has worst risk above `0.0438`. -/
theorem minimax_floor_r2Portability_zero_one (n : ℕ)
    (estimator : (Fin n → Training × (Fin 3 × Bool)) → ℝ) :
    (43801143 / 10 ^ 9 : ℝ) <
      worstRisk (contextPanelLaw (false, true)) (fun _ ↦ (false, true))
        (fun late ↦ contextGivenDefined late ratioWeighted ratioDefined (false, true)) n
        estimator :=
  lt_worstRisk_of_lt_half_separation (contextPanelLaw (false, true)) (fun _ ↦ (false, true))
    (fun late ↦ contextGivenDefined late ratioWeighted ratioDefined (false, true)) _
    half_separation_r2Portability_zero_one.1 n estimator

end Descent.Portability.PortabilityTwoHistoryInstance
