/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.EndToEndScoreLaw

assert_below Descent.Decision Descent.Program

/-!
# Hypothesis-free inhabitants of the pipeline structures

`Descent.Portability.EndToEndScoreLaw` bundles the visible inputs of the end-to-end score law in
structures that carry their domain facts as fields: `PipelineRateState`,
`PipelineDemographicHistory`, `PipelineStudyDesign` and `VisiblePipelineInput`.  A theorem that
takes one of these structures as an argument is only as meaningful as the structure is
satisfiable, so this module constructs an inhabitant of each from a deme count alone.

`constantRateState demeCount` is the rate state with unit effective sizes, no migration, and zero
mutation and recombination rates.  `constantHistory demeCount` is a history of `demeCount + 1`
demes that never splits and never changes its rates: every deme is active from the start, the
event list is empty, and the terminal epoch has zero length.  `constantStudyDesign demeCount` has
one GWAS individual, a single selection threshold, one causal locus, one individual per
evaluation cohort, and heritability and prevalence of one half, and `constantVisibleInput
demeCount` pairs it with the constant history.  `constantHistory_initialRateState` and
`constantVisibleInput_demography` tie the witnesses to the corpus readouts
`PipelineDemographicHistory.initialRateState` and `VisiblePipelineInput.demography`.

These are inhabitation witnesses, not demographic models; nothing here describes a population.

## Empirical status

None.  The bodies here are constant structures whose fields are proved by arithmetic on
literals, so no measurement can bear on them.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.PipelineWitnesses

noncomputable section

/-- The rate state with unit effective sizes, no migration, and zero mutation and recombination
rates, for any number of demes. -/
def constantRateState (demeCount : ℕ) : PipelineRateState demeCount where
  effectiveSize := fun _ ↦ 1
  effectiveSize_pos := fun _ ↦ one_pos
  migration := fun _ _ ↦ 0
  migration_nonneg := fun _ _ ↦ le_rfl
  migration_self := fun _ ↦ rfl
  mutationRate := 0
  mutationRate_nonneg := le_rfl
  recombinationRate := 0
  recombinationRate_nonneg := le_rfl

/-- A history of `demeCount + 1` demes that never splits and never changes its rates: unit
effective sizes, no migration, zero mutation and recombination rates, no events, and a terminal
epoch of zero length. -/
def constantHistory (demeCount : ℕ) : PipelineDemographicHistory (demeCount + 1) where
  ancestralDeme := 0
  initialEffectiveSize := fun _ ↦ 1
  initialEffectiveSize_pos := fun _ ↦ one_pos
  initialMigration := fun _ _ ↦ 0
  initialMigration_nonneg := fun _ _ ↦ le_rfl
  initialMigration_self := fun _ ↦ rfl
  initialMutationRate := 0
  initialMutationRate_nonneg := le_rfl
  initialRecombinationRate := 0
  initialRecombinationRate_nonneg := le_rfl
  events := []
  ancestralDeme_active := rfl
  events_wellFormed := trivial
  finalElapsed := 0
  finalElapsed_nonneg := le_rfl

/-- A study design for `demeCount + 1` demes with one GWAS individual in the first deme, the
single selection threshold one half, no clumping, one causal locus, heritability and prevalence
of one half, and one individual in every evaluation cohort. -/
def constantStudyDesign (demeCount : ℕ) : PipelineStudyDesign (demeCount + 1) where
  gwasDeme := 0
  gwasSampleSize := 1
  gwasSampleSize_pos := Nat.one_pos
  selectionThresholds := [1 / 2]
  selectionThresholds_nonempty := List.cons_ne_nil _ _
  selectionThresholds_nonneg := by
    intro threshold hthreshold
    rw [List.mem_singleton] at hthreshold
    rw [hthreshold]
    norm_num
  selectionThresholds_le_one := by
    intro threshold hthreshold
    rw [List.mem_singleton] at hthreshold
    rw [hthreshold]
    norm_num
  clumpR2Threshold := 0
  clumpR2Threshold_nonneg := le_rfl
  clumpR2Threshold_lt_one := zero_lt_one
  clumpWindowBp := 0
  causalLocusCount := 1
  causalLocusCount_pos := Nat.one_pos
  heritability := 1 / 2
  heritability_pos := by norm_num
  heritability_lt_one := by norm_num
  prevalence := 1 / 2
  prevalence_pos := by norm_num
  prevalence_lt_one := by norm_num
  cohortSize := fun _ ↦ 1
  cohortSize_pos := fun _ ↦ Nat.one_pos

/-- The visible input pairing the constant history with the constant study design. -/
def constantVisibleInput (demeCount : ℕ) : VisiblePipelineInput (demeCount + 1) where
  demography := constantHistory demeCount
  studyDesign := constantStudyDesign demeCount

/-- The constant history starts from the constant rate state. -/
theorem constantHistory_initialRateState (demeCount : ℕ) :
    (constantHistory demeCount).initialRateState = constantRateState (demeCount + 1) :=
  rfl

/-- The constant visible input reads the constant history as its demography. -/
theorem constantVisibleInput_demography (demeCount : ℕ) :
    (constantVisibleInput demeCount).demography = constantHistory demeCount :=
  rfl

end

end Descent.Portability.PipelineWitnesses
