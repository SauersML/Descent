/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.EmpiricalCorrelationDefinedness
import Descent.Portability.ChronologyReportLaw

assert_below Descent.Decision Descent.Program

/-!
# Exact finite-cohort AUC and Brier laws

NOTE1 (42) records three exact finite-cohort statements for an independent cohort of size `n`
drawn from a four-cell law on score and outcome: the empirical AUC is defined with probability
`1 − P_Y(1)ⁿ − P_Y(0)ⁿ`, its conditional expectation given definedness is the population AUC,
and the empirical Brier score is unbiased for the population one.

This module builds the empirical statistics on a cohort sample and proves the definedness
probability and the Brier identity, then specialises both to the chronology cells of NOTE1
(31). The empirical AUC is the ordered case-control average of the corpus
`empiricalAUCComparison`, the same half-credit ranking rule the corpus population AUC uses, so
`empiricalAUC` and `ChronologyReportLaw.populationAUC` are two instances of one rule rather
than two conventions. The empirical Brier score is the sample mean of `(S − Y)²` and the
population one is the corpus `FiniteReportLaw.meanSquaredError`.

Several quantities introduced for the cohort duplicate population quantities the corpus
already carries under other names; each such pair is tied here by an explicit identity
(`scoreValue_eq_scoreOf`, `scoreMass_eq_scoreCellMass`, `binaryCaseMass_eq_outcomeMass`) so
that no second convention is introduced.

Not formalised in this module: the conditional expectation of the empirical AUC given
definedness, and the empirical calibration slope. Those require the conditioning on the label
vector described in NOTE1 (42) and are stated and proved separately.

## Empirical status

None. The bodies here are algebra: the definedness probability is inclusion–exclusion on a
finite product law, and the Brier identity is the mean of a sum of identically distributed
coordinates. No measurement on any cohort can bear on either.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.EmpiricalAUCUnbiasedness

open FourCellCohortLaw EmpiricalCorrelationDefinedness ChronologyReportLaw

/-- The cohort score reading and the chronology score reading are the same function. -/
theorem scoreValue_eq_scoreOf (cell : Bool × Bool) : scoreValue cell = scoreOf cell := rfl

/-- The cohort outcome reading and the chronology outcome reading are the same function. -/
theorem outcomeValue_eq_outcomeOf (cell : Bool × Bool) : outcomeValue cell = outcomeOf cell :=
  rfl

/-- The score marginal of a four-cell law is the corpus score cell mass. -/
theorem scoreMass_eq_scoreCellMass (law : FiniteReportLaw (Bool × Bool)) (value : Bool) :
    scoreMass law value = scoreCellMass law value := (scoreCellMass_eq_cells law value).symm

/-- The corpus case mass is the outcome marginal at the donor outcome. -/
theorem binaryCaseMass_eq_outcomeMass (law : FiniteReportLaw (Bool × Bool)) :
    law.binaryCaseMass caseOf = outcomeMass law true := by
  simp [FiniteReportLaw.binaryCaseMass, expectation_cells, outcomeMass, caseOf]

/-- The two outcome marginals of a four-cell law add to one. -/
theorem outcomeMass_add_eq_one (law : FiniteReportLaw (Bool × Bool)) :
    outcomeMass law false + outcomeMass law true = 1 := by
  have htotal := law.mass_sum
  simp only [Fintype.sum_prod_type, Fintype.sum_bool] at htotal
  simp only [outcomeMass]
  linarith

/-- The number of cohort members carrying a given outcome, as a real number. -/
noncomputable def outcomeCount {n : ℕ} (sample : Fin n → Bool × Bool) (value : Bool) : ℝ :=
  ∑ member, if caseOf (sample member) = value then 1 else 0

/-- The number of ordered case-control pairs in a cohort. -/
noncomputable def empiricalPairMass {n : ℕ} (sample : Fin n → Bool × Bool) : ℝ :=
  outcomeCount sample true * outcomeCount sample false

/-- The unnormalised empirical ranking credit of a cohort: the ordered case-control sum of the
corpus comparison rule, with half credit for ties. -/
noncomputable def empiricalAUCNumerator {n : ℕ} (sample : Fin n → Bool × Bool) : ℝ :=
  ∑ caseMember, ∑ controlMember,
    if caseOf (sample caseMember) && !caseOf (sample controlMember) then
      empiricalAUCComparison (scoreOf (sample caseMember)) (scoreOf (sample controlMember))
    else 0

/-- The empirical AUC of a cohort: the average of the comparison rule over ordered
case-control pairs. -/
noncomputable def empiricalAUC {n : ℕ} (sample : Fin n → Bool × Bool) : ℝ :=
  empiricalAUCNumerator sample / empiricalPairMass sample

/-- The empirical AUC is defined exactly when the cohort contains a case and a control. -/
noncomputable def aucDefinedIndicator {n : ℕ} (sample : Fin n → Bool × Bool) : ℝ :=
  if (¬ ∀ member, caseOf (sample member) = false) ∧
      (¬ ∀ member, caseOf (sample member) = true) then 1 else 0

/-- The pair count is the ordered case-control sum of the constant one, so it normalises the
ranking credit over exactly the pairs the credit runs over. -/
theorem empiricalPairMass_eq_sum {n : ℕ} (sample : Fin n → Bool × Bool) :
    empiricalPairMass sample =
      ∑ caseMember, ∑ controlMember,
        if caseOf (sample caseMember) && !caseOf (sample controlMember) then (1 : ℝ) else 0 := by
  simp only [empiricalPairMass, outcomeCount, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun caseMember _ ↦ Finset.sum_congr rfl fun controlMember _ ↦ ?_
  cases hcase : caseOf (sample caseMember) <;> cases hcontrol : caseOf (sample controlMember) <;>
    simp [hcase, hcontrol]

/-- An outcome count is positive exactly when some member carries that outcome. -/
theorem outcomeCount_pos {n : ℕ} (sample : Fin n → Bool × Bool) (value : Bool) :
    0 < outcomeCount sample value ↔ ∃ member, caseOf (sample member) = value := by
  rw [outcomeCount, Finset.sum_boole, Nat.cast_pos, Finset.card_pos,
    Finset.filter_nonempty_iff]
  constructor
  · rintro ⟨member, _, hmember⟩
    exact ⟨member, hmember⟩
  · rintro ⟨member, hmember⟩
    exact ⟨member, Finset.mem_univ member, hmember⟩

/-- An outcome count is never negative. -/
theorem outcomeCount_nonneg {n : ℕ} (sample : Fin n → Bool × Bool) (value : Bool) :
    0 ≤ outcomeCount sample value :=
  Finset.sum_nonneg fun _ _ ↦ by positivity

/-- The empirical AUC is defined exactly when its denominator is positive. -/
theorem empiricalPairMass_pos_iff {n : ℕ} (sample : Fin n → Bool × Bool) :
    0 < empiricalPairMass sample ↔
      (¬ ∀ member, caseOf (sample member) = false) ∧
        ¬ ∀ member, caseOf (sample member) = true := by
  rw [empiricalPairMass, mul_pos_iff_of_nonneg _ _ (outcomeCount_nonneg sample true)
    (outcomeCount_nonneg sample false), outcomeCount_pos, outcomeCount_pos]
  constructor
  · rintro ⟨⟨member, hmember⟩, ⟨other, hother⟩⟩
    exact ⟨fun hall ↦ by simp [hall member] at hmember, fun hall ↦ by simp [hall other] at hother⟩
  · rintro ⟨hcase, hcontrol⟩
    refine ⟨?_, ?_⟩
    · by_contra hnone
      exact hcase fun member ↦ by
        cases hvalue : caseOf (sample member)
        · rfl
        · exact absurd ⟨member, hvalue⟩ hnone
    · by_contra hnone
      exact hcontrol fun member ↦ by
        cases hvalue : caseOf (sample member)
        · exact absurd ⟨member, hvalue⟩ hnone
        · rfl

/-- The definedness indicator of the empirical AUC splits into the two constant-outcome
indicators, which are mutually exclusive on a nonempty cohort. -/
theorem aucDefinedIndicator_expand {n : ℕ} (hn : 0 < n) (sample : Fin n → Bool × Bool) :
    aucDefinedIndicator sample =
      1 - (∏ member, outcomeIndicator false (sample member)) -
        ∏ member, outcomeIndicator true (sample member) := by
  have hprodOutcome : ∀ value : Bool, (∏ member, outcomeIndicator value (sample member)) =
      if ∀ member, (sample member).2 = value then (1 : ℝ) else 0 := by
    intro value
    simp only [outcomeIndicator]
    exact prod_member_indicator fun member ↦ (sample member).2 = value
  have hexclusive : ¬((∀ member, (sample member).2 = false) ∧
      ∀ member, (sample member).2 = true) := by
    rintro ⟨hfalse, htrue⟩
    exact Bool.false_ne_true ((hfalse ⟨0, hn⟩).symm.trans (htrue ⟨0, hn⟩))
  rw [aucDefinedIndicator, hprodOutcome false, hprodOutcome true]
  by_cases hfalse : ∀ member, (sample member).2 = false <;>
    by_cases htrue : ∀ member, (sample member).2 = true <;>
    simp_all [caseOf]

/-- NOTE1 (42): the exact probability that the empirical AUC of an independent cohort of size
`n` is defined. -/
theorem auc_definedness_probability (law : FiniteReportLaw (Bool × Bool)) (n : ℕ) (hn : 0 < n) :
    (cohortLaw law n).expectation aucDefinedIndicator =
      1 - outcomeMass law true ^ n - outcomeMass law false ^ n := by
  have hstep : (∑ sample, (cohortLaw law n).mass sample * aucDefinedIndicator sample) =
      ∑ sample, ((cohortLaw law n).mass sample * 1 -
        (cohortLaw law n).mass sample * ∏ member, outcomeIndicator true (sample member) -
        (cohortLaw law n).mass sample * ∏ member, outcomeIndicator false (sample member)) := by
    refine Finset.sum_congr rfl fun sample _ ↦ ?_
    rw [aucDefinedIndicator_expand hn sample]
    ring
  have hone : (∑ sample : Fin n → Bool × Bool, (cohortLaw law n).mass sample * 1) = 1 := by
    simpa using (cohortLaw law n).mass_sum
  have htrue : (∑ sample, (cohortLaw law n).mass sample *
      ∏ member, outcomeIndicator true (sample member)) = outcomeMass law true ^ n := by
    have hprod := cohort_expectation_prod law n (outcomeIndicator true)
    rw [expectation_outcomeIndicator] at hprod
    exact hprod
  have hfalse : (∑ sample, (cohortLaw law n).mass sample *
      ∏ member, outcomeIndicator false (sample member)) = outcomeMass law false ^ n := by
    have hprod := cohort_expectation_prod law n (outcomeIndicator false)
    rw [expectation_outcomeIndicator] at hprod
    exact hprod
  show (∑ sample, (cohortLaw law n).mass sample * aucDefinedIndicator sample) = _
  rw [hstep, Finset.sum_sub_distrib, Finset.sum_sub_distrib, hone, htrue, hfalse]

/-- The empirical Brier score of a cohort: the sample mean of the squared score-outcome
difference. -/
noncomputable def empiricalBrier {n : ℕ} (sample : Fin n → Bool × Bool) : ℝ :=
  (∑ member, (scoreOf (sample member) - outcomeOf (sample member)) ^ 2) / n

/-- NOTE1 (42): the empirical Brier score of an independent cohort is unbiased for the
population Brier score of the individual-level law. -/
theorem expectation_empiricalBrier (law : FiniteReportLaw (Bool × Bool)) (n : ℕ) (hn : 0 < n) :
    (cohortLaw law n).expectation empiricalBrier =
      law.meanSquaredError scoreOf outcomeOf := by
  have hcast : ((n : ℝ)) ≠ 0 := by
    have : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    exact ne_of_gt this
  have hsum := FiniteIndependentMoments.independent_sum_mean (fun _ : Fin n ↦ law)
    fun (_ : Fin n) (cell : Bool × Bool) ↦ (scoreOf cell - outcomeOf cell) ^ 2
  have hconst : (∑ _member : Fin n, law.expectation
      fun cell ↦ (scoreOf cell - outcomeOf cell) ^ 2) =
      (n : ℝ) * law.meanSquaredError scoreOf outcomeOf := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rfl
  rw [hconst] at hsum
  have htotal : (∑ sample, (cohortLaw law n).mass sample *
      ∑ member, (scoreOf (sample member) - outcomeOf (sample member)) ^ 2) =
      (n : ℝ) * law.meanSquaredError scoreOf outcomeOf := hsum
  show (∑ sample, (cohortLaw law n).mass sample * empiricalBrier sample) = _
  have hstep : (∑ sample, (cohortLaw law n).mass sample * empiricalBrier sample) =
      (∑ sample, (cohortLaw law n).mass sample *
        ∑ member, (scoreOf (sample member) - outcomeOf (sample member)) ^ 2) / (n : ℝ) := by
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl fun sample _ ↦ by rw [empiricalBrier]; ring
  rw [hstep, htotal, mul_comm, mul_div_assoc, div_self hcast, mul_one]

/-- The outcome marginals of the chronology law of NOTE1 (31) are the donor ancestry fraction
and its complement. -/
theorem outcomeMass_chronologyLaw (p C : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hC0 : 0 ≤ C)
    (hC1 : C ≤ 1) :
    outcomeMass (chronologyLaw p C hp0 hp1 hC0 hC1) true = p ∧
      outcomeMass (chronologyLaw p C hp0 hp1 hC0 hC1) false = 1 - p := by
  constructor <;> · simp only [outcomeMass, chronologyLaw_mass, chronologyMass_false_false,
                      chronologyMass_false_true, chronologyMass_true_false,
                      chronologyMass_true_true]
                    ring

/-- NOTE1 (42) for the chronology cells: the empirical AUC of a cohort of size `n` is defined
with probability `1 − pⁿ − (1 − p)ⁿ`. -/
theorem auc_definedness_probability_chronologyLaw (p C : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hC0 : 0 ≤ C) (hC1 : C ≤ 1) (n : ℕ) (hn : 0 < n) :
    (cohortLaw (chronologyLaw p C hp0 hp1 hC0 hC1) n).expectation aucDefinedIndicator =
      1 - p ^ n - (1 - p) ^ n := by
  obtain ⟨hcase, hcontrol⟩ := outcomeMass_chronologyLaw p C hp0 hp1 hC0 hC1
  rw [auc_definedness_probability _ n hn, hcase, hcontrol]

/-- NOTE1 (42) for the chronology cells: the expected empirical Brier score of a cohort is
`2 h (1 − C)`. -/
theorem expectation_empiricalBrier_chronologyLaw (p C : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hC0 : 0 ≤ C) (hC1 : C ≤ 1) (n : ℕ) (hn : 0 < n) :
    (cohortLaw (chronologyLaw p C hp0 hp1 hC0 hC1) n).expectation empiricalBrier =
      2 * (p * (1 - p)) * (1 - C) := by
  rw [expectation_empiricalBrier _ n hn, meanSquaredError_chronologyLaw]

end Descent.Portability.EmpiricalAUCUnbiasedness
