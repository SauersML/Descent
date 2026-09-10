/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.SimulationDemographyLaw
import Descent.Portability.SamplingDesignLaw

assert_below Descent.Decision Descent.Program

/-!
Actual cohort row maps and 50/50 splits for the simulation's source-dependent
sample allocation. Evaluation laws live on the common cohort row type, so every
deme uses the same learned score and genetic effects. The source fit rows are
sorted before the fixed inner training permutation is applied.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.SimulationCohortLaw

open FiniteReportLaw ReservoirSamplingLaw SamplingDesignLaw SourceDesignLaw SimulationDemographyLaw

variable {demes : ℕ}

abbrev Individuals (demes : ℕ) := Fin (cohortSize demes)

def fitCount (source deme : Fin demes) : ℕ := sampleSize source deme / 2

def testCount (source deme : Fin demes) : ℕ := sampleSize source deme - fitCount source deme

theorem fitCount_pos (source deme : Fin demes) : 0 < fitCount source deme := by
  unfold fitCount sampleSize
  split_ifs <;> norm_num

theorem testCount_pos (source deme : Fin demes) : 0 < testCount source deme := by
  unfold testCount fitCount sampleSize
  split_ifs <;> norm_num

theorem fitCount_le (source deme : Fin demes) : fitCount source deme ≤ sampleSize source deme :=
  Nat.div_le_self _ _

/-- Both actual sample sizes are even, so rounding half the size gives this
integer exactly; no rounding convention affects either default population size. -/
theorem split_exact_half (source deme : Fin demes) :
    2 * fitCount source deme = sampleSize source deme ∧
      testCount source deme = fitCount source deme := by
  unfold testCount fitCount sampleSize
  split_ifs <;> norm_num

theorem source_split_counts (source : Fin demes) :
    fitCount source source = 2500 ∧ testCount source source = 2500 := by
  simp [fitCount, testCount, sampleSize]

theorem target_split_counts (source deme : Fin demes) (h : deme ≠ source) :
    fitCount source deme = 125 ∧ testCount source deme = 125 := by
  simp [fitCount, testCount, sampleSize, h]

noncomputable def demeEmbedding (source deme : Fin demes) :
    Fin (sampleSize source deme) ↪ Individuals demes :=
  (Function.Embedding.sigmaMk deme).trans (individualIndex source).toEmbedding

noncomputable def individualDeme (source : Fin demes) (individual : Individuals demes) :
    Fin demes := ((individualIndex source).symm individual).1

theorem demeEmbedding_location (source deme : Fin demes) (i : Fin (sampleSize source deme)) :
    individualDeme source (demeEmbedding source deme i) = deme := by
  simp [individualDeme, demeEmbedding]

theorem demeEmbedding_strictMono (source deme : Fin demes) :
    StrictMono (demeEmbedding source deme) := by
  intro i j hij
  change individualIndex source ⟨deme, i⟩ < individualIndex source ⟨deme, j⟩
  rw [Fin.lt_def, individualIndex_val, individualIndex_val]
  exact Nat.add_lt_add_left hij _

variable (source : Fin demes)
  (permutations : ∀ deme, Equiv.Perm (Fin (sampleSize source deme)))

noncomputable def trainingIndex : Slots (fitCount source source) (cohortSize demes) :=
  (sortedFit (fitCount_le source source) (permutations source)).trans
    (demeEmbedding source source)

noncomputable def evaluationIndex (deme : Fin demes) :
    Slots (testCount source deme) (cohortSize demes) :=
  (testRows (fitCount_le source deme) (permutations deme)).trans (demeEmbedding source deme)

theorem trainingIndex_location (i : Fin (fitCount source source)) :
    individualDeme source (trainingIndex source permutations i) = source :=
  demeEmbedding_location _ _ _

theorem evaluationIndex_location (deme : Fin demes) (i : Fin (testCount source deme)) :
    individualDeme source (evaluationIndex source permutations deme i) = deme :=
  demeEmbedding_location _ _ _

theorem trainingIndex_strictMono : StrictMono (trainingIndex source permutations) := by
  apply (demeEmbedding_strictMono source source).comp
  exact ((fitSet (fitCount_le source source) (permutations source)).orderEmbOfFin
    (fitSet_card (fitCount_le source source) (permutations source))).strictMono

/-- No source training label belongs to any held-out evaluation cohort. -/
theorem training_evaluation_disjoint (deme : Fin demes)
    (i : Fin (fitCount source source)) (j : Fin (testCount source deme)) :
    trainingIndex source permutations i ≠ evaluationIndex source permutations deme j := by
  intro heq
  have hd := congrArg (individualDeme source) heq
  rw [trainingIndex_location, evaluationIndex_location] at hd
  subst deme
  have hlocal := (demeEmbedding source source).injective heq
  obtain ⟨k, hk⟩ := sortedFit_mem (fitCount_le source source) (permutations source) i
  exact fit_test_disjoint (fitCount_le source source) (permutations source) k j (hk.trans hlocal)

noncomputable def cohortLaw : FiniteReportLaw (Individuals demes) := by
  have h : 0 < cohortSize demes := by unfold cohortSize; omega
  letI : NeZero (cohortSize demes) := ⟨Nat.ne_zero_of_lt h⟩
  exact uniform _

noncomputable def evaluationLaw (deme : Fin demes) : FiniteReportLaw (Individuals demes) := by
  letI : NeZero (testCount source deme) := ⟨Nat.ne_zero_of_lt (testCount_pos source deme)⟩
  exact (uniform (Fin (testCount source deme))).pushforward
    (evaluationIndex source permutations deme)

theorem evaluationLaw_expectation (deme : Fin demes) (readout : Individuals demes → ℝ) :
    (evaluationLaw source permutations deme).expectation readout =
      (∑ row : Fin (testCount source deme),
        readout (evaluationIndex source permutations deme row)) /
        testCount source deme := by
  letI : NeZero (testCount source deme) := ⟨Nat.ne_zero_of_lt (testCount_pos source deme)⟩
  rw [evaluationLaw, expectation_pushforward, uniform_expectation]
  simp

end Descent.Portability.SimulationCohortLaw
