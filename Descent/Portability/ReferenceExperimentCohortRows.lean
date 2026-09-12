/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.ReferenceExperimentTable
import Descent.Portability.SmallCohortConditionalMeans

assert_below Descent.Decision Descent.Program

/-!
# The size-three cohort rows of the NOTE2 section 9 reference experiment

The two rows of the section 9 table that read a size-three evaluation cohort of independent
target population draws, for both migration histories: the probability that the empirical
target squared correlation of the cohort is defined, its weighted numerator, and their quotient,
the reported conditional mean of NOTE2 (2).

The rows are not decided by enumerating cohorts inside the history report, which would repeat
the empirical correlation of all 64 draw sequences for every context, learner atom and terminal
census. The cohort is certified once, and each row reduces to a cubic polynomial in the four
cell masses of one draw.

1. The certificate. When the two census members carry distinct score indices, the empirical
   squared correlation of a cohort is defined exactly when the draws vary in their census member
   and in their outcome (`cohortDefinedValue`), and it is `1/4` when the draws occupy three
   distinct cells and `1` when they occupy two (`cohortWeightedValue`); when the indices agree
   the score is constant and the correlation is undefined. `cohortReports_zero` through
   `cohortReports_four` decide this for each first index, and `definedIndicator_cohortR2` and
   `weightedValue_cohortR2` assemble them.
2. The cohort law. Summing the certified values against three independent draws with any cell
   masses `m` gives `6 T(m) + 3 D(m)` for the definedness probability
   (`sum_cohortDefinedValue`) and `3/2 T(m) + 3 D(m)` for the weighted numerator
   (`sum_cohortWeightedValue`), where `T = threeCellMass` sums the products of three distinct
   cell masses and `D = twoCellMass` sums `m_c² m_c' + m_c m_c'²` over the two pairs of cells
   that differ in both the member and the outcome. The weighted polynomial is the corpus census
   polynomial `SmallCohortConditionalMeans.cohortCorrelationThree`
   (`cast_weightedCellPolynomial`).
3. The rows. `cohortDefinedMass_eq_poly` and `cohortWeightedR2_eq_poly` rewrite the two cohort
   reports to these polynomials at the target population law, and each row is then decided in
   the kernel from the tabled terminal law with one polynomial evaluation per context, learner
   atom and terminal census.

## Empirical status

None. The bodies here are exact rational arithmetic on a completely specified finite model:
every mass and metric is a finite sum of products of the supplied rationals, so no
measurement can bear on these values.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.ReferenceExperimentCohortRows

open RationalReportClosure ReferenceExperimentLaw ReferenceExperimentTable

/-! ## The certificate -/

/-- The definedness value of the empirical squared correlation of a size-three cohort whose two
census members carry distinct scores: `1` when the draws vary in their census member and in
their outcome, `0` otherwise. -/
def cohortDefinedValue (cohort : Cohort) : ℚ :=
  if (cohort.1.1 ≠ cohort.2.1.1 ∨ cohort.1.1 ≠ cohort.2.2.1) ∧
      (cohort.1.2 ≠ cohort.2.1.2 ∨ cohort.1.2 ≠ cohort.2.2.2) then 1 else 0

/-- The weighted value of the empirical squared correlation of a size-three cohort whose two
census members carry distinct scores: `1/4` when it is defined and the draws occupy three
distinct cells, `1` when it is defined and they occupy two, `0` when it is undefined. -/
def cohortWeightedValue (cohort : Cohort) : ℚ :=
  cohortDefinedValue cohort *
    (if cohort.1 ≠ cohort.2.1 ∧ cohort.1 ≠ cohort.2.2 ∧ cohort.2.1 ≠ cohort.2.2 then 1 / 4
      else 1)

/-- The size-three cohort reports with first score index `0`, decided for every second index
and cohort. -/
theorem cohortReports_zero : ∀ (secondIndex : Fin 5) (cohort : Cohort),
    definedIndicator (cohortR2 0 secondIndex cohort) =
        (if (0 : Fin 5) = secondIndex then 0 else cohortDefinedValue cohort) ∧
      weightedValue (cohortR2 0 secondIndex cohort) =
        (if (0 : Fin 5) = secondIndex then 0 else cohortWeightedValue cohort) := by
  decide +kernel

/-- The size-three cohort reports with first score index `1`. -/
theorem cohortReports_one : ∀ (secondIndex : Fin 5) (cohort : Cohort),
    definedIndicator (cohortR2 1 secondIndex cohort) =
        (if (1 : Fin 5) = secondIndex then 0 else cohortDefinedValue cohort) ∧
      weightedValue (cohortR2 1 secondIndex cohort) =
        (if (1 : Fin 5) = secondIndex then 0 else cohortWeightedValue cohort) := by
  decide +kernel

/-- The size-three cohort reports with first score index `2`. -/
theorem cohortReports_two : ∀ (secondIndex : Fin 5) (cohort : Cohort),
    definedIndicator (cohortR2 2 secondIndex cohort) =
        (if (2 : Fin 5) = secondIndex then 0 else cohortDefinedValue cohort) ∧
      weightedValue (cohortR2 2 secondIndex cohort) =
        (if (2 : Fin 5) = secondIndex then 0 else cohortWeightedValue cohort) := by
  decide +kernel

/-- The size-three cohort reports with first score index `3`. -/
theorem cohortReports_three : ∀ (secondIndex : Fin 5) (cohort : Cohort),
    definedIndicator (cohortR2 3 secondIndex cohort) =
        (if (3 : Fin 5) = secondIndex then 0 else cohortDefinedValue cohort) ∧
      weightedValue (cohortR2 3 secondIndex cohort) =
        (if (3 : Fin 5) = secondIndex then 0 else cohortWeightedValue cohort) := by
  decide +kernel

/-- The size-three cohort reports with first score index `4`. -/
theorem cohortReports_four : ∀ (secondIndex : Fin 5) (cohort : Cohort),
    definedIndicator (cohortR2 4 secondIndex cohort) =
        (if (4 : Fin 5) = secondIndex then 0 else cohortDefinedValue cohort) ∧
      weightedValue (cohortR2 4 secondIndex cohort) =
        (if (4 : Fin 5) = secondIndex then 0 else cohortWeightedValue cohort) := by
  decide +kernel

/-- The definedness indicator of the size-three empirical squared correlation: `0` when the two
census members share a score index, the certified value otherwise. -/
theorem definedIndicator_cohortR2 (firstIndex secondIndex : Fin 5) (cohort : Cohort) :
    definedIndicator (cohortR2 firstIndex secondIndex cohort) =
      if firstIndex = secondIndex then 0 else cohortDefinedValue cohort := by
  fin_cases firstIndex
  exacts [(cohortReports_zero secondIndex cohort).1, (cohortReports_one secondIndex cohort).1,
    (cohortReports_two secondIndex cohort).1, (cohortReports_three secondIndex cohort).1,
    (cohortReports_four secondIndex cohort).1]

/-- The weighted value of the size-three empirical squared correlation: `0` when the two census
members share a score index, the certified value otherwise. -/
theorem weightedValue_cohortR2 (firstIndex secondIndex : Fin 5) (cohort : Cohort) :
    weightedValue (cohortR2 firstIndex secondIndex cohort) =
      if firstIndex = secondIndex then 0 else cohortWeightedValue cohort := by
  fin_cases firstIndex
  exacts [(cohortReports_zero secondIndex cohort).2, (cohortReports_one secondIndex cohort).2,
    (cohortReports_two secondIndex cohort).2, (cohortReports_three secondIndex cohort).2,
    (cohortReports_four secondIndex cohort).2]

/-! ## The size-three cohort law of any cell masses -/

/-- The products of three distinct cell masses, one ordering each: up to the six orderings, the
mass of the size-three cohorts that occupy three distinct cells. -/
def threeCellMass (m : Bool × Bool → ℚ) : ℚ :=
  m (false, false) * m (false, true) * m (true, false) +
    m (false, false) * m (false, true) * m (true, true) +
    m (false, false) * m (true, false) * m (true, true) +
    m (false, true) * m (true, false) * m (true, true)

/-- The products `m_c² m_c' + m_c m_c'²` over the two pairs of cells that differ in both the
census member and the outcome: up to the three orderings, the mass of the size-three cohorts
that occupy two such cells. -/
def twoCellMass (m : Bool × Bool → ℚ) : ℚ :=
  m (false, false) * m (true, true) * (m (false, false) + m (true, true)) +
    m (false, true) * m (true, false) * (m (false, true) + m (true, false))

/-- The definedness probability of the size-three empirical squared correlation under three
independent draws with cell masses `m`, when the two census members carry distinct scores. -/
theorem sum_cohortDefinedValue (m : Bool × Bool → ℚ) :
    ∑ cohort : Cohort, m cohort.1 * m cohort.2.1 * m cohort.2.2 * cohortDefinedValue cohort =
      6 * threeCellMass m + 3 * twoCellMass m := by
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, cohortDefinedValue, threeCellMass,
    twoCellMass]
  norm_num
  ring

/-- The weighted numerator of the size-three empirical squared correlation under three
independent draws with cell masses `m`, when the two census members carry distinct scores. -/
theorem sum_cohortWeightedValue (m : Bool × Bool → ℚ) :
    ∑ cohort : Cohort, m cohort.1 * m cohort.2.1 * m cohort.2.2 * cohortWeightedValue cohort =
      3 / 2 * threeCellMass m + 3 * twoCellMass m := by
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, cohortWeightedValue, cohortDefinedValue,
    threeCellMass, twoCellMass]
  norm_num
  ring

/-- The weighted cell polynomial is the corpus census polynomial of a cohort of three,
`SmallCohortConditionalMeans.cohortCorrelationThree`, read at the rational cell masses. -/
theorem cast_weightedCellPolynomial (m : Bool × Bool → ℚ) :
    ((3 / 2 * threeCellMass m + 3 * twoCellMass m : ℚ) : ℝ) =
      SmallCohortConditionalMeans.cohortCorrelationThree (m (false, false)) (m (false, true))
        (m (true, false)) (m (true, true)) := by
  rw [threeCellMass, twoCellMass, SmallCohortConditionalMeans.cohortCorrelationThree]
  push_cast
  ring

/-! ## The cohort reports at the target population law -/

/-- The probability that the size-three empirical target squared correlation is defined, within
one study context and terminal census, is the definedness polynomial at the target population
law. -/
theorem cohortDefinedMass_eq (context : Bool × Bool) (atom : LearnerAtom)
    (terminal : TerminalTypes) :
    cohortDefinedMass context atom terminal =
      if atomScoreIndex atom terminal.1 = atomScoreIndex atom terminal.2 then 0
      else 6 * threeCellMass (targetMass context terminal) +
        3 * twoCellMass (targetMass context terminal) := by
  rw [cohortDefinedMass, ← sum_cohortDefinedValue]
  simp only [definedIndicator_cohortR2]
  by_cases hindex : atomScoreIndex atom terminal.1 = atomScoreIndex atom terminal.2
  · simp [hindex]
  · simp only [hindex, ↓reduceIte, cohortMass]

/-- The weighted numerator of the size-three empirical target squared correlation, within one
study context and terminal census, is the weighted polynomial at the target population law. -/
theorem cohortWeightedR2_eq (context : Bool × Bool) (atom : LearnerAtom)
    (terminal : TerminalTypes) :
    cohortWeightedR2 context atom terminal =
      if atomScoreIndex atom terminal.1 = atomScoreIndex atom terminal.2 then 0
      else 3 / 2 * threeCellMass (targetMass context terminal) +
        3 * twoCellMass (targetMass context terminal) := by
  rw [cohortWeightedR2, ← sum_cohortWeightedValue]
  simp only [weightedValue_cohortR2]
  by_cases hindex : atomScoreIndex atom terminal.1 = atomScoreIndex atom terminal.2
  · simp [hindex]
  · simp only [hindex, ↓reduceIte, cohortMass]

/-- The definedness report of the size-three cohort as a function of the study context. -/
theorem cohortDefinedMass_eq_poly :
    cohortDefinedMass = fun context atom terminal ↦
      if atomScoreIndex atom terminal.1 = atomScoreIndex atom terminal.2 then 0
      else 6 * threeCellMass (targetMass context terminal) +
        3 * twoCellMass (targetMass context terminal) := by
  funext context atom terminal
  exact cohortDefinedMass_eq context atom terminal

/-- The weighted report of the size-three cohort as a function of the study context. -/
theorem cohortWeightedR2_eq_poly :
    cohortWeightedR2 = fun context atom terminal ↦
      if atomScoreIndex atom terminal.1 = atomScoreIndex atom terminal.2 then 0
      else 3 / 2 * threeCellMass (targetMass context terminal) +
        3 * twoCellMass (targetMass context terminal) := by
  funext context atom terminal
  exact cohortWeightedR2_eq context atom terminal

/-! ## The section 9 cohort rows -/

/-- NOTE2 section 9, early migration: the probability that the size-three empirical target
squared correlation is defined, `0.070854469…`. -/
theorem early_cohort_r2_definedProbability :
    historyReport earlyMigration
        (fun context atom terminal ↦ cohortDefinedMass context atom terminal) =
      2622808655603568101589881171237344566748039 /
        37016841404766089074607937488631921377280000 := by
  rw [early_historyReport_table, cohortDefinedMass_eq_poly]
  decide +kernel

/-- NOTE2 section 9, early migration: the weighted numerator of the size-three empirical target
squared correlation. -/
theorem early_cohort_r2_weightedNumerator :
    historyReport earlyMigration
        (fun context atom terminal ↦ cohortWeightedR2 context atom terminal) =
      8868146603782821480477967380455098332442037 /
        218735881028163253622683266978279535411200000 := by
  rw [early_historyReport_table, cohortWeightedR2_eq_poly]
  decide +kernel

/-- NOTE2 section 9, late migration: the probability that the size-three empirical target
squared correlation is defined, `0.125309857…`. -/
theorem late_cohort_r2_definedProbability :
    historyReport lateMigration
        (fun context atom terminal ↦ cohortDefinedMass context atom terminal) =
      4629489007808721611581847193695585961360948528887668663 /
        36944332527415893085479923110366961409819942303301632000 := by
  rw [late_historyReport_table, cohortDefinedMass_eq_poly]
  decide +kernel

/-- NOTE2 section 9, late migration: the weighted numerator of the size-three empirical target
squared correlation. -/
theorem late_cohort_r2_weightedNumerator :
    historyReport lateMigration
        (fun context atom terminal ↦ cohortWeightedR2 context atom terminal) =
      201309347462493699395313125940107393567746924890805006589 /
        2770824939556191981410994233277522105736495672747622400000 := by
  rw [late_historyReport_table, cohortWeightedR2_eq_poly]
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
