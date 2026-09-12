/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.EmpiricalAUCUnbiasedness
import Descent.Portability.SmallCohortConditionalMeans

assert_below Descent.Decision Descent.Program

/-!
# Finite-cohort metrics are corpus metrics of the cohort's empirical table law

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

The same holds for the remaining metrics of the NOTE1 section 6.2 table that a cohort reports.
`tableLaw_linearIntercept` shows that on the event that the score varies, the corpus
least-squares intercept of the table law is the mean outcome of the score-zero group, since the
fitted line passes through both group means. `conditional_tableLaw_linearIntercept` shows that
this intercept, weighted by that event and divided by its probability, returns the population
intercept, which is `p (1 − C)` at the chronology cells
(`conditional_tableLaw_linearIntercept_chronologyLaw`). The threshold accuracy and the Brier
score of the table law are sample means over the cohort members, and
`expectation_tableLaw_expectation` shows that every table-law expectation of a cell metric is
unbiased for the population one with no definedness event. So the finite-cohort accuracy
(`expectation_tableLaw_thresholdAccuracy`, `1 − 2h(1 − C)` at the chronology cells) and Brier
score (`expectation_tableLaw_meanSquaredError`) have exact means.

## Empirical status

None. The bodies here are algebra: each identity compares two ways of writing one finite sum
over a cohort sample, so no measurement on any cohort can bear on them.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.EmpiricalTableLawMetrics

open FourCellCohortLaw EmpiricalCorrelationDefinedness ChronologyReportLaw
  EmpiricalAUCUnbiasedness SmallCohortConditionalMeans

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

/-- The total outcome of a cohort splits into the outcome totals of its two score groups. -/
theorem sum_outcomeOf_split {n : ℕ} (sample : Fin n → Bool × Bool) :
    (∑ member, outcomeOf (sample member)) =
      outcomeTotal sample true + outcomeTotal sample false := by
  simp only [outcomeTotal, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun member _ ↦ ?_
  cases (sample member).1 <;> simp

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
    simp only [scoreOf]
    cases (sample member).1 <;> simp
  have hvariance : (tableLaw (cellCount sample) hpos).variance scoreOf =
      scoreCount sample true * scoreCount sample false / (n : ℝ) ^ 2 := by
    rw [FiniteReportLaw.variance_eq_rawMoments, expectation_tableLaw_cellCount,
      expectation_tableLaw_cellCount, hsquare, hscore,
      show scoreCount sample false = n - scoreCount sample true by linarith]
    field_simp
  have hcovariance : (tableLaw (cellCount sample) hpos).covariance scoreOf outcomeOf =
      (scoreCount sample false * outcomeTotal sample true -
        scoreCount sample true * outcomeTotal sample false) / (n : ℝ) ^ 2 := by
    rw [FiniteReportLaw.covariance_eq_rawMoments, expectation_tableLaw_cellCount,
      expectation_tableLaw_cellCount, expectation_tableLaw_cellCount, hproduct, hscore,
      sum_outcomeOf_split sample,
      show scoreCount sample false = n - scoreCount sample true by linarith]
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

/-- On the event that the cohort score varies, the corpus least-squares intercept of the
cohort's empirical table law is the mean outcome of the score-zero group: the fitted line
passes through both group means. -/
theorem tableLaw_linearIntercept {n : ℕ} (sample : Fin n → Bool × Bool)
    (hpos : 0 < ∑ cell, cellCount sample cell)
    (hdefined : (¬ ∀ member, (sample member).1 = false) ∧
      ¬ ∀ member, (sample member).1 = true) :
    linearIntercept (tableLaw (cellCount sample) hpos) =
      outcomeTotal sample false / scoreCount sample false := by
  have hslope := tableLaw_calibrationSlope sample hpos
  rw [if_pos hdefined] at hslope
  have hvariance : 0 < (tableLaw (cellCount sample) hpos).variance scoreOf := by
    by_contra hnot
    rw [FiniteReportLaw.calibrationSlope, if_neg hnot] at hslope
    cases hslope
  rw [calibrationSlope_eq_some_linearSlope _ hvariance] at hslope
  have hdonor : 0 < scoreCount sample true :=
    scoreGroupSize_pos_of_defined (fun member ↦ (sample member).1) hdefined true
  have hrecipient : 0 < scoreCount sample false :=
    scoreGroupSize_pos_of_defined (fun member ↦ (sample member).1) hdefined false
  have hsize : scoreCount sample true + scoreCount sample false = n :=
    scoreGroupSize_add fun member ↦ (sample member).1
  have hscore : (∑ member, scoreOf (sample member)) = scoreCount sample true := rfl
  have hdonorNe : scoreCount sample true ≠ 0 := ne_of_gt hdonor
  have hrecipientNe : scoreCount sample false ≠ 0 := ne_of_gt hrecipient
  have hsizeNe : scoreCount sample true + scoreCount sample false ≠ 0 :=
    ne_of_gt (add_pos hdonor hrecipient)
  rw [linearIntercept, Option.some.inj hslope, expectation_tableLaw_cellCount,
    expectation_tableLaw_cellCount, sum_outcomeOf_split sample, hscore, empiricalSlope, ← hsize]
  field_simp <;> ring

/-- The intercept form of NOTE1 (42), cleared: the definedness-weighted mean outcome of the
score-zero group of an independent cohort carries exactly the joint mass of a recipient score
and a donor outcome. -/
theorem intercept_numerator_identity (law : FiniteReportLaw (Bool × Bool)) (n : ℕ) :
    scoreMass law false *
        (cohortLaw law n).expectation
          (fun sample ↦ outcomeTotal sample false / scoreCount sample false *
            slopeDefinedIndicator sample) =
      law.mass (false, true) * (cohortLaw law n).expectation slopeDefinedIndicator := by
  simp only [cohort_expectation_split_score]
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun scores _ ↦ ?_
  by_cases hdefined : (¬ ∀ member, scores member = false) ∧ ¬ ∀ member, scores member = true
  · have hindicator : ∀ outcomes : Fin n → Bool,
        slopeDefinedIndicator (fun member ↦ (scores member, outcomes member)) = 1 := by
      intro outcomes
      rw [slopeDefinedIndicator_split, scoreDefinedIndicator, outcomeDefinedIndicator,
        if_pos hdefined]
    simp only [hindicator, mul_one, scoreCount_split]
    rw [score_fiber_mean law scores false
        (ne_of_gt (scoreGroupSize_pos_of_defined scores hdefined false)),
      sum_prod_mass_score law scores]
  · have hindicator : ∀ outcomes : Fin n → Bool,
        slopeDefinedIndicator (fun member ↦ (scores member, outcomes member)) = 0 := by
      intro outcomes
      rw [slopeDefinedIndicator_split, scoreDefinedIndicator, outcomeDefinedIndicator,
        if_neg hdefined]
    simp only [hindicator, mul_zero, Finset.sum_const_zero]

/-- The population least-squares intercept of a four-cell law, in cleared form: the intercept
times the recipient score mass is the joint mass of a recipient score and a donor outcome. -/
theorem linearIntercept_cleared (law : FiniteReportLaw (Bool × Bool))
    (hdonor : 0 < scoreMass law true) (hrecipient : 0 < scoreMass law false) :
    linearIntercept law * scoreMass law false = law.mass (false, true) := by
  have hcleared := linearSlope_cleared law hdonor hrecipient
  have htotal := law.mass_sum
  simp only [Fintype.sum_prod_type, Fintype.sum_bool] at htotal
  have houtcome : law.expectation outcomeOf =
      law.mass (false, true) + law.mass (true, true) := by
    simp only [expectation_cells, outcomeOf_false, outcomeOf_true]
    ring
  have hscore : law.expectation scoreOf = scoreMass law true := by
    simp only [expectation_cells, scoreOf_false, scoreOf_true, scoreMass]
    ring
  rw [linearIntercept, houtcome, hscore]
  simp only [scoreMass] at hcleared ⊢
  linear_combination (-1 : ℝ) * hcleared + law.mass (false, true) * htotal

/-- NOTE1 (42) for the intercept: conditional on the cohort score varying, the mean outcome of
the score-zero group of an independent cohort has expectation the population least-squares
intercept.

Assumes: both score classes carry positive mass, and a varying score has positive
probability. -/
theorem conditional_empiricalIntercept (law : FiniteReportLaw (Bool × Bool)) (n : ℕ)
    (hdonor : 0 < scoreMass law true) (hrecipient : 0 < scoreMass law false)
    (hdefined : 0 < (cohortLaw law n).expectation slopeDefinedIndicator) :
    (cohortLaw law n).expectation
          (fun sample ↦ outcomeTotal sample false / scoreCount sample false *
            slopeDefinedIndicator sample) /
        (cohortLaw law n).expectation slopeDefinedIndicator = linearIntercept law := by
  have hkey := intercept_numerator_identity law n
  have hcleared := linearIntercept_cleared law hdonor hrecipient
  rw [div_eq_iff (ne_of_gt hdefined)]
  apply mul_left_cancel₀ (ne_of_gt hrecipient)
  linear_combination hkey - (cohortLaw law n).expectation slopeDefinedIndicator * hcleared

/-- NOTE1 (42) for the intercept, about the corpus metric itself: for an independent cohort of
size `n > 0`, the corpus least-squares intercept of the cohort's empirical table law, weighted
by the event that the score varies, has conditional expectation the population intercept.

Assumes: both score classes carry positive mass, and a varying score has positive
probability. -/
theorem conditional_tableLaw_linearIntercept (law : FiniteReportLaw (Bool × Bool)) (n : ℕ)
    (hn : 0 < n) (hdonor : 0 < scoreMass law true) (hrecipient : 0 < scoreMass law false)
    (hdefined : 0 < (cohortLaw law n).expectation slopeDefinedIndicator) :
    (cohortLaw law n).expectation (fun sample ↦
        linearIntercept (tableLaw (cellCount sample)
            (lt_of_lt_of_eq hn (sum_cellCount sample).symm)) *
          slopeDefinedIndicator sample) /
      (cohortLaw law n).expectation slopeDefinedIndicator = linearIntercept law := by
  have hintegrand : (fun sample : Fin n → Bool × Bool ↦
      linearIntercept (tableLaw (cellCount sample)
          (lt_of_lt_of_eq hn (sum_cellCount sample).symm)) *
        slopeDefinedIndicator sample) =
      fun sample ↦ outcomeTotal sample false / scoreCount sample false *
        slopeDefinedIndicator sample := by
    funext sample
    by_cases hsample : (¬ ∀ member, (sample member).1 = false) ∧
        ¬ ∀ member, (sample member).1 = true
    · rw [tableLaw_linearIntercept sample _ hsample]
    · rw [slopeDefinedIndicator, if_neg hsample, mul_zero, mul_zero]
  rw [hintegrand]
  exact conditional_empiricalIntercept law n hdonor hrecipient hdefined

/-- NOTE1 (42) for the intercept at the chronology cells of NOTE1 (31): for every cohort of at
least two, the corpus least-squares intercept of the empirical table law, weighted by the event
that the score varies, has conditional expectation `p (1 − C)`. -/
theorem conditional_tableLaw_linearIntercept_chronologyLaw (p C : ℝ) (hp0 : 0 ≤ p)
    (hp1 : p ≤ 1) (hC0 : 0 ≤ C) (hC1 : C ≤ 1) (hlow : 0 < p) (hhigh : p < 1) (n : ℕ)
    (hn : 2 ≤ n) :
    (cohortLaw (chronologyLaw p C hp0 hp1 hC0 hC1) n).expectation (fun sample ↦
        linearIntercept (tableLaw (cellCount sample)
            (lt_of_lt_of_eq (by omega) (sum_cellCount sample).symm)) *
          slopeDefinedIndicator sample) /
      (cohortLaw (chronologyLaw p C hp0 hp1 hC0 hC1) n).expectation slopeDefinedIndicator =
      p * (1 - C) := by
  obtain ⟨hdonor, hrecipient⟩ := scoreMass_chronologyLaw p C hp0 hp1 hC0 hC1
  have hdefined : 0 < (cohortLaw (chronologyLaw p C hp0 hp1 hC0 hC1) n).expectation
      slopeDefinedIndicator := by
    rw [slope_definedness_probability_chronologyLaw p C hp0 hp1 hC0 hC1 n (by omega)]
    exact constant_class_gap p hlow hhigh n hn
  rw [conditional_tableLaw_linearIntercept (chronologyLaw p C hp0 hp1 hC0 hC1) n (by omega)
      (by rw [hdonor]; exact hlow) (by rw [hrecipient]; linarith) hdefined,
    linearIntercept_chronologyLaw p C hp0 hp1 hC0 hC1 hlow hhigh]

/-- The expectation of any cell metric under the empirical table law of an independent cohort
of size `n > 0` is unbiased for its expectation under the individual-level law: the table-law
expectation is the sample mean of the metric over the cohort members. -/
theorem expectation_tableLaw_expectation (law : FiniteReportLaw (Bool × Bool)) (n : ℕ)
    (hn : 0 < n) (metric : Bool × Bool → ℝ) :
    (cohortLaw law n).expectation (fun sample ↦
        (tableLaw (cellCount sample)
          (lt_of_lt_of_eq hn (sum_cellCount sample).symm)).expectation metric) =
      law.expectation metric := by
  have hnR : (n : ℝ) ≠ 0 := ne_of_gt (Nat.cast_pos.mpr hn)
  have hsum := FiniteIndependentMoments.independent_sum_mean (fun _ : Fin n ↦ law)
    fun (_ : Fin n) (cell : Bool × Bool) ↦ metric cell
  have hconst : (∑ _member : Fin n, law.expectation metric) = n * law.expectation metric := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [hconst] at hsum
  have htotal : (∑ sample, (cohortLaw law n).mass sample * ∑ member, metric (sample member)) =
      n * law.expectation metric := hsum
  have hstep : (∑ sample, (cohortLaw law n).mass sample *
      ((∑ member, metric (sample member)) / n)) =
      (∑ sample, (cohortLaw law n).mass sample * ∑ member, metric (sample member)) / n := by
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl fun sample _ ↦ (mul_div_assoc _ _ _).symm
  show (∑ sample, (cohortLaw law n).mass sample *
    (tableLaw (cellCount sample) (lt_of_lt_of_eq hn (sum_cellCount sample).symm)).expectation
      metric) = _
  simp only [expectation_tableLaw_cellCount]
  rw [hstep, htotal, mul_comm, mul_div_assoc, div_self hnR, mul_one]

/-- The correct-classification indicator at a threshold: the outcome when the score exceeds the
threshold, and its complement otherwise. -/
noncomputable def correctIndicator (threshold : ℝ) (report : Bool × Bool) : ℝ :=
  if threshold < scoreOf report then outcomeOf report else 1 - outcomeOf report

/-- The corpus threshold accuracy is the expectation of the correct-classification indicator. -/
theorem thresholdAccuracy_eq_expectation_correctIndicator (law : FiniteReportLaw (Bool × Bool))
    (threshold : ℝ) :
    thresholdAccuracy law threshold = law.expectation (correctIndicator threshold) :=
  rfl

/-- The corpus threshold accuracy of the empirical table law of a cohort is the sample mean of
the correct-classification indicator over the cohort members. -/
theorem tableLaw_thresholdAccuracy {n : ℕ} (sample : Fin n → Bool × Bool)
    (hpos : 0 < ∑ cell, cellCount sample cell) (threshold : ℝ) :
    thresholdAccuracy (tableLaw (cellCount sample) hpos) threshold =
      (∑ member, correctIndicator threshold (sample member)) / n :=
  expectation_tableLaw_cellCount sample hpos (correctIndicator threshold)

/-- The finite-cohort accuracy law: for an independent cohort of size `n > 0`, the corpus
threshold accuracy of the empirical table law is unbiased for the population accuracy at every
threshold, with no definedness event. -/
theorem expectation_tableLaw_thresholdAccuracy (law : FiniteReportLaw (Bool × Bool)) (n : ℕ)
    (hn : 0 < n) (threshold : ℝ) :
    (cohortLaw law n).expectation (fun sample ↦
        thresholdAccuracy (tableLaw (cellCount sample)
          (lt_of_lt_of_eq hn (sum_cellCount sample).symm)) threshold) =
      thresholdAccuracy law threshold :=
  expectation_tableLaw_expectation law n hn fun report ↦
    if threshold < scoreOf report then outcomeOf report else 1 - outcomeOf report

/-- The finite-cohort accuracy law at the chronology cells of NOTE1 (31): for every threshold
strictly between zero and one, the corpus threshold accuracy of the empirical table law of an
independent cohort has expectation `1 − 2h(1 − C)`. -/
theorem expectation_tableLaw_thresholdAccuracy_chronologyLaw (p C threshold : ℝ)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hC0 : 0 ≤ C) (hC1 : C ≤ 1) (ht0 : 0 < threshold)
    (ht1 : threshold < 1) (n : ℕ) (hn : 0 < n) :
    (cohortLaw (chronologyLaw p C hp0 hp1 hC0 hC1) n).expectation (fun sample ↦
        thresholdAccuracy (tableLaw (cellCount sample)
          (lt_of_lt_of_eq hn (sum_cellCount sample).symm)) threshold) =
      1 - 2 * (p * (1 - p)) * (1 - C) := by
  rw [expectation_tableLaw_thresholdAccuracy _ n hn threshold,
    thresholdAccuracy_chronologyLaw p C threshold hp0 hp1 hC0 hC1 ht0 ht1]

/-- The corpus mean squared error of the empirical table law of a cohort is the empirical
Brier score of the cohort, so the Brier identity of NOTE1 (42) is a statement about the corpus
metric. -/
theorem tableLaw_meanSquaredError {n : ℕ} (sample : Fin n → Bool × Bool)
    (hpos : 0 < ∑ cell, cellCount sample cell) :
    (tableLaw (cellCount sample) hpos).meanSquaredError scoreOf outcomeOf =
      empiricalBrier sample :=
  expectation_tableLaw_cellCount sample hpos fun report ↦
    (scoreOf report - outcomeOf report) ^ 2

/-- The finite-cohort Brier law about the corpus metric: for an independent cohort of size
`n > 0`, the corpus mean squared error of the empirical table law is unbiased for the
population mean squared error. -/
theorem expectation_tableLaw_meanSquaredError (law : FiniteReportLaw (Bool × Bool)) (n : ℕ)
    (hn : 0 < n) :
    (cohortLaw law n).expectation (fun sample ↦
        (tableLaw (cellCount sample)
          (lt_of_lt_of_eq hn (sum_cellCount sample).symm)).meanSquaredError scoreOf outcomeOf) =
      law.meanSquaredError scoreOf outcomeOf :=
  expectation_tableLaw_expectation law n hn fun report ↦ (scoreOf report - outcomeOf report) ^ 2

end Descent.Portability.EmpiricalTableLawMetrics
