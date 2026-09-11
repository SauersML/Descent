/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.EmpiricalAUCUnbiasedness

assert_below Descent.Decision Descent.Program

/-!
# The empirical AUC and slope of a cohort are corpus metrics of its empirical table law

NOTE1 (42) states the finite-cohort unbiasedness of the empirical AUC and of the empirical
calibration slope. `EmpiricalAUCUnbiasedness` proves both for statistics built on the cohort
sample: the ordered case-control average `empiricalAUC` of the corpus comparison rule, and the
difference `empiricalSlope` of the two score-group outcome means. This module shows that those
two statistics are not a second convention. Each is the corresponding corpus metric of the
cohort's empirical table law, the four-cell law with masses `count / n` of
`EmpiricalCorrelationDefinedness.tableLaw`, and each metric is defined exactly on the event on
which the statistic is.

`tableLaw_binaryAUC` shows that the corpus `FiniteReportLaw.binaryAUC` of the table law, with
the score read by `scoreOf` and the case indicator by `caseOf`, is `some (empiricalAUC sample)`
exactly when the cohort carries a case and a control, and `none` otherwise.
`tableLaw_calibrationSlope` shows the same for the corpus `FiniteReportLaw.calibrationSlope`
and `empiricalSlope`, on the event that the cohort score varies. Both follow the pattern of
`EmpiricalCorrelationDefinedness.tableLaw_squaredCorrelation` for the squared correlation: the
table-law moments are sample averages (`expectation_tableLaw_cellCount`), and the definedness
branch of the corpus metric is the positivity of a product of two class counts.

`conditional_tableLaw_binaryAUC` and `conditional_tableLaw_calibrationSlope` then restate NOTE1
(42) about the corpus metrics themselves: evaluated on the empirical table law of an independent
cohort, read as zero where undefined, and divided by the definedness probability, they return
the population AUC and the population least-squares slope.

Not formalised here: the finite-cohort intercept and accuracy.

## Empirical status

None. The bodies here are algebra: each identity compares two ways of writing one finite sum
over a cohort sample, so no measurement on any cohort can bear on them.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.EmpiricalTableLawMetrics

open FourCellCohortLaw EmpiricalCorrelationDefinedness ChronologyReportLaw
  EmpiricalAUCUnbiasedness

/-- The two classes of a Boolean vector over a cohort of size `n` together count `n`
members. -/
theorem scoreGroupSize_add {n : ℕ} (values : Fin n → Bool) :
    scoreGroupSize values true + scoreGroupSize values false = n := by
  simp only [scoreGroupSize, ← Finset.sum_add_distrib]
  have hterm : ∀ member : Fin n, ((if values member = true then (1 : ℝ) else 0) +
      if values member = false then (1 : ℝ) else 0) = 1 := by
    intro member
    cases values member <;> simp
  rw [Finset.sum_congr rfl fun member _ ↦ hterm member, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, mul_one]

/-- Both score groups of a cohort are nonempty exactly when the cohort score varies: the pair
count of the cohort with score and outcome exchanged. -/
theorem scoreCount_mul_pos_iff {n : ℕ} (sample : Fin n → Bool × Bool) :
    0 < scoreCount sample true * scoreCount sample false ↔
      (¬ ∀ member, (sample member).1 = false) ∧ ¬ ∀ member, (sample member).1 = true :=
  empiricalPairMass_pos_iff fun member ↦ ((sample member).2, (sample member).1)

/-- The empirical AUC of a cohort is the corpus binary AUC of the cohort's empirical table law:
the corpus metric is defined exactly when the cohort carries a case and a control, and there it
equals the ordered case-control average of the comparison rule. -/
theorem tableLaw_binaryAUC {n : ℕ} (sample : Fin n → Bool × Bool)
    (hpos : 0 < ∑ cell, cellCount sample cell) :
    (tableLaw (cellCount sample) hpos).binaryAUC scoreOf caseOf =
      if (¬ ∀ member, caseOf (sample member) = false) ∧
          ¬ ∀ member, caseOf (sample member) = true then some (empiricalAUC sample)
      else none := by
  have hn : (0 : ℝ) < n := Nat.cast_pos.mpr (lt_of_lt_of_eq hpos (sum_cellCount sample))
  have hne : (n : ℝ) ≠ 0 := ne_of_gt hn
  have htotal : outcomeCount sample true + outcomeCount sample false = n :=
    scoreGroupSize_add fun member ↦ caseOf (sample member)
  have hcase : (tableLaw (cellCount sample) hpos).binaryCaseMass caseOf =
      outcomeCount sample true / n := by
    rw [FiniteReportLaw.binaryCaseMass, expectation_tableLaw_cellCount]
    rfl
  have hnumerator : (tableLaw (cellCount sample) hpos).binaryAUCNumerator scoreOf caseOf =
      empiricalAUCNumerator sample / n / n := by
    simp only [FiniteReportLaw.binaryAUCNumerator, expectation_tableLaw_cellCount,
      ← Finset.sum_div, empiricalAUCNumerator]
  have hcomplement : 1 - outcomeCount sample true / n = outcomeCount sample false / n := by
    rw [show outcomeCount sample false = n - outcomeCount sample true by linarith, sub_div,
      div_self hne]
  have hcondition : (0 < outcomeCount sample true / n ∧ outcomeCount sample true / n < 1) ↔
      (¬ ∀ member, caseOf (sample member) = false) ∧
        ¬ ∀ member, caseOf (sample member) = true := by
    rw [← empiricalPairMass_pos_iff sample, empiricalPairMass,
      mul_pos_iff_of_nonneg _ _ (outcomeCount_nonneg sample true)
        (outcomeCount_nonneg sample false), lt_div_iff₀ hn, zero_mul, div_lt_iff₀ hn, one_mul]
    constructor
    · rintro ⟨htrue, hlow⟩
      exact ⟨htrue, by linarith⟩
    · rintro ⟨htrue, hfalse⟩
      exact ⟨htrue, by linarith⟩
  simp only [FiniteReportLaw.binaryAUC, hcase, hnumerator]
  by_cases hdefined : (¬ ∀ member, caseOf (sample member) = false) ∧
      ¬ ∀ member, caseOf (sample member) = true
  · obtain ⟨htrue, hfalse⟩ := (mul_pos_iff_of_nonneg _ _ (outcomeCount_nonneg sample true)
      (outcomeCount_nonneg sample false)).mp ((empiricalPairMass_pos_iff sample).mpr hdefined)
    rw [if_pos (hcondition.mpr hdefined), if_pos hdefined, hcomplement, empiricalAUC,
      empiricalPairMass]
    congr 1
    rw [div_eq_div_iff (ne_of_gt (mul_pos (div_pos htrue hn) (div_pos hfalse hn)))
      (ne_of_gt (mul_pos htrue hfalse))]
    ring
  · rw [if_neg fun hcond ↦ hdefined (hcondition.mp hcond), if_neg hdefined]

/-- The empirical least-squares slope of a cohort is the corpus calibration slope of the
cohort's empirical table law: the corpus metric is defined exactly when the cohort score
varies, and there it equals the difference of the two score-group outcome means. -/
theorem tableLaw_calibrationSlope {n : ℕ} (sample : Fin n → Bool × Bool)
    (hpos : 0 < ∑ cell, cellCount sample cell) :
    (tableLaw (cellCount sample) hpos).calibrationSlope scoreOf outcomeOf =
      if (¬ ∀ member, (sample member).1 = false) ∧ ¬ ∀ member, (sample member).1 = true then
        some (empiricalSlope sample)
      else none := by
  have hn : (0 : ℝ) < n := Nat.cast_pos.mpr (lt_of_lt_of_eq hpos (sum_cellCount sample))
  have hne : (n : ℝ) ≠ 0 := ne_of_gt hn
  have hsize : scoreCount sample true + scoreCount sample false = n :=
    scoreGroupSize_add fun member ↦ (sample member).1
  have hscore : (∑ member, scoreOf (sample member)) = scoreCount sample true := rfl
  have hproduct : (∑ member, scoreOf (sample member) * outcomeOf (sample member)) =
      outcomeTotal sample true := rfl
  have hsquare : (∑ member, scoreOf (sample member) ^ 2) = scoreCount sample true := by
    rw [← hscore]
    refine Finset.sum_congr rfl fun member _ ↦ ?_
    simp only [scoreOf, alleleValue]
    split_ifs <;> norm_num
  have houtcome : (∑ member, outcomeOf (sample member)) =
      outcomeTotal sample true + outcomeTotal sample false := by
    simp only [outcomeTotal, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun member _ ↦ ?_
    cases (sample member).1 <;> simp
  have hvariance : (tableLaw (cellCount sample) hpos).variance scoreOf =
      scoreCount sample true * scoreCount sample false / (n : ℝ) ^ 2 := by
    rw [FiniteReportLaw.variance_eq_rawMoments, expectation_tableLaw_cellCount,
      expectation_tableLaw_cellCount, hsquare, hscore,
      show scoreCount sample false = n - scoreCount sample true by linarith]
    field_simp
    ring
  have hcovariance : (tableLaw (cellCount sample) hpos).covariance scoreOf outcomeOf =
      (scoreCount sample false * outcomeTotal sample true -
        scoreCount sample true * outcomeTotal sample false) / (n : ℝ) ^ 2 := by
    rw [FiniteReportLaw.covariance_eq_rawMoments, expectation_tableLaw_cellCount,
      expectation_tableLaw_cellCount, expectation_tableLaw_cellCount, hproduct, hscore,
      houtcome, show scoreCount sample false = n - scoreCount sample true by linarith]
    field_simp
    ring
  unfold FiniteReportLaw.calibrationSlope
  rw [hvariance, hcovariance]
  by_cases hdefined : (¬ ∀ member, (sample member).1 = false) ∧
      ¬ ∀ member, (sample member).1 = true
  · have hdonor : 0 < scoreCount sample true :=
      scoreGroupSize_pos_of_defined (fun member ↦ (sample member).1) hdefined true
    have hrecipient : 0 < scoreCount sample false :=
      scoreGroupSize_pos_of_defined (fun member ↦ (sample member).1) hdefined false
    have hvariancePos : 0 < scoreCount sample true * scoreCount sample false / (n : ℝ) ^ 2 :=
      div_pos (mul_pos hdonor hrecipient) (pow_pos hn 2)
    rw [if_pos hvariancePos, if_pos hdefined, empiricalSlope,
      div_sub_div _ _ (ne_of_gt hdonor) (ne_of_gt hrecipient)]
    congr 1
    rw [div_eq_div_iff (ne_of_gt hvariancePos) (ne_of_gt (mul_pos hdonor hrecipient))]
    ring
  · have hvarianceZero :
        ¬ 0 < scoreCount sample true * scoreCount sample false / (n : ℝ) ^ 2 := by
      rw [lt_div_iff₀ (pow_pos hn 2), zero_mul, scoreCount_mul_pos_iff]
      exact hdefined
    rw [if_neg hvarianceZero, if_neg hdefined]

/-- NOTE1 (42) about the corpus metric itself: for an independent cohort of size `n > 0`, the
corpus binary AUC of the cohort's empirical table law, read as zero where it is undefined, has
conditional expectation given definedness equal to the population AUC.

Assumes: both outcome classes carry positive mass, and definedness has positive probability. -/
theorem conditional_tableLaw_binaryAUC (law : FiniteReportLaw (Bool × Bool)) (n : ℕ)
    (hn : 0 < n) (hcase : 0 < outcomeMass law true) (hcontrol : 0 < outcomeMass law false)
    (hdefined : 0 < (cohortLaw law n).expectation aucDefinedIndicator) :
    (cohortLaw law n).expectation (fun sample ↦
        ((tableLaw (cellCount sample) (lt_of_lt_of_eq hn (sum_cellCount sample).symm)).binaryAUC
          scoreOf caseOf).getD 0) /
      (cohortLaw law n).expectation aucDefinedIndicator = populationAUC law := by
  have hintegrand : (fun sample : Fin n → Bool × Bool ↦
      ((tableLaw (cellCount sample) (lt_of_lt_of_eq hn (sum_cellCount sample).symm)).binaryAUC
        scoreOf caseOf).getD 0) =
      fun sample ↦ empiricalAUC sample * aucDefinedIndicator sample := by
    funext sample
    rw [tableLaw_binaryAUC, aucDefinedIndicator]
    split_ifs <;> simp
  rw [hintegrand]
  exact conditional_empiricalAUC law n hcase hcontrol hdefined

/-- NOTE1 (42) about the corpus metric itself: for an independent cohort of size `n > 0`, the
corpus calibration slope of the cohort's empirical table law, read as zero where it is
undefined, has conditional expectation given that the score varies equal to the population
least-squares slope.

Assumes: both score classes carry positive mass, and a varying score has positive
probability. -/
theorem conditional_tableLaw_calibrationSlope (law : FiniteReportLaw (Bool × Bool)) (n : ℕ)
    (hn : 0 < n) (hdonor : 0 < scoreMass law true) (hrecipient : 0 < scoreMass law false)
    (hdefined : 0 < (cohortLaw law n).expectation slopeDefinedIndicator) :
    (cohortLaw law n).expectation (fun sample ↦
        ((tableLaw (cellCount sample)
            (lt_of_lt_of_eq hn (sum_cellCount sample).symm)).calibrationSlope
          scoreOf outcomeOf).getD 0) /
      (cohortLaw law n).expectation slopeDefinedIndicator = linearSlope law := by
  have hintegrand : (fun sample : Fin n → Bool × Bool ↦
      ((tableLaw (cellCount sample)
          (lt_of_lt_of_eq hn (sum_cellCount sample).symm)).calibrationSlope
        scoreOf outcomeOf).getD 0) =
      fun sample ↦ empiricalSlope sample * slopeDefinedIndicator sample := by
    funext sample
    rw [tableLaw_calibrationSlope, slopeDefinedIndicator]
    split_ifs <;> simp
  rw [hintegrand]
  exact conditional_empiricalSlope law n hdonor hrecipient hdefined

end Descent.Portability.EmpiricalTableLawMetrics
