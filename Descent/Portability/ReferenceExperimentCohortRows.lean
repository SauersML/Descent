/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.ReferenceExperimentTable

assert_below Descent.Decision Descent.Program

/-!
# The size-three cohort rows of the NOTE2 section 9 reference experiment

The two rows of the section 9 table that read a size-three evaluation cohort of independent
target population draws, decided exactly in the kernel from the tabled terminal laws of
`ReferenceExperimentTable`: for both migration histories, the probability that the empirical
target squared correlation of the cohort is defined, its weighted numerator, and their
quotient, the reported conditional mean of NOTE2 (2).

## Empirical status

None. The bodies here are exact rational arithmetic on a completely specified finite model:
every mass and metric is a finite sum of products of the supplied rationals, so no
measurement can bear on these values.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.ReferenceExperimentCohortRows

open RationalReportClosure ReferenceExperimentLaw ReferenceExperimentTable

/-- NOTE2 section 9, early migration: the probability that the size-three empirical target
squared correlation is defined, `0.070854469…`. -/
theorem early_cohort_r2_definedProbability :
    historyReport earlyMigration
        (fun context atom terminal ↦ cohortDefinedMass context atom terminal) =
      2622808655603568101589881171237344566748039 /
        37016841404766089074607937488631921377280000 := by
  rw [early_historyReport_table]
  decide +kernel

/-- NOTE2 section 9, early migration: the weighted numerator of the size-three empirical target
squared correlation. -/
theorem early_cohort_r2_weightedNumerator :
    historyReport earlyMigration
        (fun context atom terminal ↦ cohortWeightedR2 context atom terminal) =
      8868146603782821480477967380455098332442037 /
        218735881028163253622683266978279535411200000 := by
  rw [early_historyReport_table]
  decide +kernel

/-- NOTE2 section 9, late migration: the probability that the size-three empirical target
squared correlation is defined, `0.125309857…`. -/
theorem late_cohort_r2_definedProbability :
    historyReport lateMigration
        (fun context atom terminal ↦ cohortDefinedMass context atom terminal) =
      4629489007808721611581847193695585961360948528887668663 /
        36944332527415893085479923110366961409819942303301632000 := by
  rw [late_historyReport_table]
  decide +kernel

/-- NOTE2 section 9, late migration: the weighted numerator of the size-three empirical target
squared correlation. -/
theorem late_cohort_r2_weightedNumerator :
    historyReport lateMigration
        (fun context atom terminal ↦ cohortWeightedR2 context atom terminal) =
      201309347462493699395313125940107393567746924890805006589 /
        2770824939556191981410994233277522105736495672747622400000 := by
  rw [late_historyReport_table]
  decide +kernel

/-- NOTE2 section 9, early migration: the expected size-three empirical target squared
correlation given that it is defined, `0.572197010…`. -/
theorem early_cohort_r2_givenDefined :
    historyReport earlyMigration
        (fun context atom terminal ↦ cohortWeightedR2 context atom terminal) /
      historyReport earlyMigration
        (fun context atom terminal ↦ cohortDefinedMass context atom terminal) =
      97549612641611036285257641185006081656862407 /
        170482562614231926603342276130427396838622535 := by
  rw [early_cohort_r2_weightedNumerator, early_cohort_r2_definedProbability]
  norm_num

/-- NOTE2 section 9, late migration: the expected size-three empirical target squared
correlation given that it is defined, `0.579788531…`. -/
theorem late_cohort_r2_givenDefined :
    historyReport lateMigration
        (fun context atom terminal ↦ cohortWeightedR2 context atom terminal) /
      historyReport lateMigration
        (fun context atom terminal ↦ cohortDefinedMass context atom terminal) =
      201309347462493699395313125940107393567746924890805006589 /
        347211675585654120868638539527168947102071139666575149725 := by
  rw [late_cohort_r2_weightedNumerator, late_cohort_r2_definedProbability]
  norm_num

end Descent.Portability.ReferenceExperimentCohortRows
