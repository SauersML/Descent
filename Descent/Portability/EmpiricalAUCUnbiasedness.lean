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

The conditional expectation of the empirical AUC given definedness is
`conditional_empiricalAUC`. Its proof is the conditioning on the outcome vector described in
NOTE1 (42), carried out as a finite rearrangement rather than through conditional laws: the
cohort sum is reindexed as a sum over outcome vectors of a sum over score vectors
(`cohort_expectation_split`), the pair count is constant on each outcome fibre, and inside a
fibre every ordered case-control pair contributes the same two-replica moment
(`outcome_fiber_numerator`). The identity is proved in cleared form,
`auc_numerator_identity`, so that no positivity premise is needed until the ratio is taken.

Not formalised in this module: the empirical calibration slope of NOTE1 (42), which needs the
same conditioning on the score vector instead of the outcome vector.

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

/-- A member is a case paired against a control exactly when the corpus Boolean guard holds. -/
theorem caseControl_iff (first second : Bool) :
    (first && !second) = true ↔ first = true ∧ second = false := by
  cases first <;> cases second <;> simp

/-- The pair count is the ordered case-control sum of the constant one, so it normalises the
ranking credit over exactly the pairs the credit runs over. -/
theorem empiricalPairMass_eq_sum {n : ℕ} (sample : Fin n → Bool × Bool) :
    empiricalPairMass sample =
      ∑ caseMember, ∑ controlMember,
        if caseOf (sample caseMember) && !caseOf (sample controlMember) then (1 : ℝ) else 0 := by
  have hterm : ∀ caseMember controlMember : Fin n,
      (if caseOf (sample caseMember) = true then (1 : ℝ) else 0) *
          (if caseOf (sample controlMember) = false then (1 : ℝ) else 0) =
        if caseOf (sample caseMember) && !caseOf (sample controlMember) then (1 : ℝ) else 0 := by
    intro caseMember controlMember
    simp only [caseControl_iff]
    by_cases hcase : caseOf (sample caseMember) = true <;>
      by_cases hcontrol : caseOf (sample controlMember) = false <;>
      simp [hcase, hcontrol]
  simp only [empiricalPairMass, outcomeCount]
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun caseMember _ ↦ ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun controlMember _ ↦ hterm caseMember controlMember

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
      if ∀ member, caseOf (sample member) = value then (1 : ℝ) else 0 := by
    intro value
    simp only [outcomeIndicator, caseOf]
    exact prod_member_indicator fun member ↦ (sample member).2 = value
  have hexclusive : ¬((∀ member, caseOf (sample member) = false) ∧
      ∀ member, caseOf (sample member) = true) := by
    rintro ⟨hfalse, htrue⟩
    exact Bool.false_ne_true ((hfalse ⟨0, hn⟩).symm.trans (htrue ⟨0, hn⟩))
  unfold aucDefinedIndicator
  rw [hprodOutcome false, hprodOutcome true]
  by_cases hfalse : ∀ member, caseOf (sample member) = false
  · rw [if_neg fun hdefined ↦ hdefined.1 hfalse, if_pos hfalse,
      if_neg fun htrue ↦ hexclusive ⟨hfalse, htrue⟩]
    ring
  · by_cases htrue : ∀ member, caseOf (sample member) = true
    · rw [if_neg fun hdefined ↦ hdefined.2 htrue, if_neg hfalse, if_pos htrue]
      ring
    · rw [if_pos ⟨hfalse, htrue⟩, if_neg hfalse, if_neg htrue]
      ring

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

/-- The score marginal sum of a four-cell law at a fixed outcome is the outcome marginal. -/
theorem sum_mass_eq_outcomeMass (law : FiniteReportLaw (Bool × Bool)) (value : Bool) :
    (∑ score : Bool, law.mass (score, value)) = outcomeMass law value := by
  rw [Fintype.sum_bool, outcomeMass]
  ring

/-- The corpus population ranking credit written as a sum over the two score values of the
case and of the control. -/
theorem binaryAUCNumerator_eq_pairSum (law : FiniteReportLaw (Bool × Bool)) :
    law.binaryAUCNumerator scoreOf caseOf =
      ∑ caseScore : Bool, ∑ controlScore : Bool,
        law.mass (caseScore, true) * law.mass (controlScore, false) *
          empiricalAUCComparison (alleleValue caseScore) (alleleValue controlScore) := by
  simp only [FiniteReportLaw.binaryAUCNumerator, expectation_cells, Fintype.sum_bool,
    caseOf_mk, scoreOf_false, scoreOf_true, alleleValue_false, alleleValue_true]
  norm_num [empiricalAUCComparison]
  ring

/-- Splitting a cohort sample into its outcome vector and its score vector. -/
def splitEquiv (n : ℕ) : ((Fin n → Bool) × (Fin n → Bool)) ≃ (Fin n → Bool × Bool) where
  toFun pair := fun member ↦ (pair.2 member, pair.1 member)
  invFun sample := (fun member ↦ (sample member).2, fun member ↦ (sample member).1)
  left_inv _ := rfl
  right_inv _ := rfl

/-- The cohort expectation as an iterated sum over outcome vectors and score vectors. -/
theorem cohort_expectation_split (law : FiniteReportLaw (Bool × Bool)) (n : ℕ)
    (statistic : (Fin n → Bool × Bool) → ℝ) :
    (cohortLaw law n).expectation statistic =
      ∑ outcomes : Fin n → Bool, ∑ scores : Fin n → Bool,
        (∏ member, law.mass (scores member, outcomes member)) *
          statistic fun member ↦ (scores member, outcomes member) := by
  have hequiv := Fintype.sum_equiv (splitEquiv n)
    (fun pair : (Fin n → Bool) × (Fin n → Bool) ↦
      (∏ member, law.mass (pair.2 member, pair.1 member)) *
        statistic fun member ↦ (pair.2 member, pair.1 member))
    (fun sample ↦ (cohortLaw law n).mass sample * statistic sample) fun _ ↦ rfl
  show (∑ sample, (cohortLaw law n).mass sample * statistic sample) = _
  rw [← hequiv, Fintype.sum_prod_type]

/-- Marginalising the four-cell masses over all score vectors at a fixed outcome vector
leaves the product of the outcome marginals. -/
theorem sum_prod_mass (law : FiniteReportLaw (Bool × Bool)) {n : ℕ} (outcomes : Fin n → Bool) :
    (∑ scores : Fin n → Bool, ∏ member, law.mass (scores member, outcomes member)) =
      ∏ member, outcomeMass law (outcomes member) := by
  have hexpand := Finset.prod_univ_sum (fun _ : Fin n ↦ (Finset.univ : Finset Bool))
    fun (member : Fin n) (value : Bool) ↦ law.mass (value, outcomes member)
  rw [Fintype.piFinset_univ] at hexpand
  rw [← hexpand]
  exact Finset.prod_congr rfl fun member _ ↦ sum_mass_eq_outcomeMass law (outcomes member)

/-- A product over the cohort splits off two distinct members. -/
theorem prod_split_two {n : ℕ} (first second : Fin n) (hne : first ≠ second)
    (weight : Fin n → ℝ) :
    (∏ member, weight member) =
      weight first * weight second *
        ∏ member ∈ (Finset.univ.erase first).erase second, weight member := by
  rw [← Finset.mul_prod_erase Finset.univ weight (Finset.mem_univ first),
    ← Finset.mul_prod_erase (Finset.univ.erase first) weight
      (Finset.mem_erase.mpr ⟨hne.symm, Finset.mem_univ second⟩)]
  ring

/-- Two products over the cohort that agree away from two distinct members are exchanged by
their values at those members. -/
theorem prod_exchange_two {n : ℕ} (first second : Fin n) (hne : first ≠ second)
    (base modified : Fin n → ℝ)
    (hagree : ∀ member, member ≠ first → member ≠ second → modified member = base member) :
    (∏ member, modified member) * (base first * base second) =
      (∏ member, base member) * (modified first * modified second) := by
  have hrest : (∏ member ∈ (Finset.univ.erase first).erase second, modified member) =
      ∏ member ∈ (Finset.univ.erase first).erase second, base member :=
    Finset.prod_congr rfl fun member hmember ↦ hagree member
      (Finset.mem_erase.mp (Finset.mem_erase.mp hmember).2).1 (Finset.mem_erase.mp hmember).1
  rw [prod_split_two first second hne modified, prod_split_two first second hne base, hrest]
  ring

/-- The zero-one marker that pins two cohort coordinates to prescribed score values. -/
def pinMarker {n : ℕ} (first second : Fin n) (firstValue secondValue : Bool) (member : Fin n)
    (value : Bool) : ℝ :=
  if member = first then (if value = firstValue then 1 else 0)
  else if member = second then (if value = secondValue then 1 else 0) else 1

/-- At the first pinned member the marker tests the first prescribed value. -/
theorem pinMarker_first {n : ℕ} (first second : Fin n) (firstValue secondValue value : Bool) :
    pinMarker first second firstValue secondValue first value =
      if value = firstValue then 1 else 0 := if_pos rfl

/-- At the second pinned member the marker tests the second prescribed value. -/
theorem pinMarker_second {n : ℕ} (first second : Fin n) (hne : first ≠ second)
    (firstValue secondValue value : Bool) :
    pinMarker first second firstValue secondValue second value =
      if value = secondValue then 1 else 0 := by
  rw [pinMarker, if_neg hne.symm, if_pos rfl]

/-- Away from the two pinned members the marker is one. -/
theorem pinMarker_other {n : ℕ} (first second member : Fin n) (hfirst : member ≠ first)
    (hsecond : member ≠ second) (firstValue secondValue value : Bool) :
    pinMarker first second firstValue secondValue member value = 1 := by
  rw [pinMarker, if_neg hfirst, if_neg hsecond]

/-- The marker product over the cohort collapses to the two pinned tests. -/
theorem prod_pinMarker {n : ℕ} (first second : Fin n) (hne : first ≠ second)
    (firstValue secondValue : Bool) (scores : Fin n → Bool) :
    (∏ member, pinMarker first second firstValue secondValue member (scores member)) =
      (if scores first = firstValue then (1 : ℝ) else 0) *
        if scores second = secondValue then (1 : ℝ) else 0 := by
  have hexchange := prod_exchange_two first second hne (fun _ ↦ (1 : ℝ))
    (fun member ↦ pinMarker first second firstValue secondValue member (scores member))
    fun member hfirst hsecond ↦ pinMarker_other first second member hfirst hsecond _ _ _
  rw [Finset.prod_const_one, pinMarker_first, pinMarker_second first second hne] at hexchange
  simpa using hexchange

/-- Marginalising a coordinatewise weight over all score vectors with two distinct
coordinates pinned, in cleared form. -/
theorem sum_prod_pinned {n : ℕ} (first second : Fin n) (hne : first ≠ second)
    (weight : Fin n → Bool → ℝ) (firstValue secondValue : Bool) :
    (∑ scores : Fin n → Bool, (∏ member, weight member (scores member)) *
          ((if scores first = firstValue then (1 : ℝ) else 0) *
            if scores second = secondValue then (1 : ℝ) else 0)) *
        ((∑ value : Bool, weight first value) * ∑ value : Bool, weight second value) =
      (∏ member, ∑ value : Bool, weight member value) *
        (weight first firstValue * weight second secondValue) := by
  have hpointwise : ∀ scores : Fin n → Bool,
      (∏ member, weight member (scores member)) *
          ((if scores first = firstValue then (1 : ℝ) else 0) *
            if scores second = secondValue then (1 : ℝ) else 0) =
        ∏ member, weight member (scores member) *
          pinMarker first second firstValue secondValue member (scores member) := by
    intro scores
    rw [Finset.prod_mul_distrib, prod_pinMarker first second hne]
  have hmarginal : (∑ scores : Fin n → Bool, ∏ member, weight member (scores member) *
      pinMarker first second firstValue secondValue member (scores member)) =
      ∏ member, ∑ value : Bool,
        weight member value * pinMarker first second firstValue secondValue member value := by
    have hexpand := Finset.prod_univ_sum (fun _ : Fin n ↦ (Finset.univ : Finset Bool))
      fun (member : Fin n) (value : Bool) ↦ weight member value *
        pinMarker first second firstValue secondValue member value
    rw [Fintype.piFinset_univ] at hexpand
    exact hexpand.symm
  have hpinnedFirst : (∑ value : Bool, weight first value *
      pinMarker first second firstValue secondValue first value) = weight first firstValue := by
    simp only [pinMarker_first]
    cases firstValue <;> simp
  have hpinnedSecond : (∑ value : Bool, weight second value *
      pinMarker first second firstValue secondValue second value) =
      weight second secondValue := by
    simp only [pinMarker_second first second hne]
    cases secondValue <;> simp
  have hexchange := prod_exchange_two first second hne
    (fun member ↦ ∑ value : Bool, weight member value)
    (fun member ↦ ∑ value : Bool,
      weight member value * pinMarker first second firstValue secondValue member value)
    (fun member hfirst hsecond ↦ Finset.sum_congr rfl fun value _ ↦ by
      rw [pinMarker_other first second member hfirst hsecond, mul_one])
  rw [hpinnedFirst, hpinnedSecond] at hexchange
  rw [Finset.sum_congr rfl fun scores _ ↦ hpointwise scores, hmarginal]
  exact hexchange

/-- Marginalising a coordinatewise weight against a statistic of two distinct coordinates,
in cleared form. -/
theorem sum_prod_pair {n : ℕ} (first second : Fin n) (hne : first ≠ second)
    (weight : Fin n → Bool → ℝ) (pairValue : Bool → Bool → ℝ) :
    (∑ scores : Fin n → Bool, (∏ member, weight member (scores member)) *
          pairValue (scores first) (scores second)) *
        ((∑ value : Bool, weight first value) * ∑ value : Bool, weight second value) =
      (∏ member, ∑ value : Bool, weight member value) *
        ∑ u : Bool, ∑ v : Bool, weight first u * weight second v * pairValue u v := by
  have hexpand : ∀ scores : Fin n → Bool,
      pairValue (scores first) (scores second) =
        ∑ u : Bool, ∑ v : Bool,
          ((if scores first = u then (1 : ℝ) else 0) *
            (if scores second = v then (1 : ℝ) else 0)) * pairValue u v := by
    intro scores
    cases hfirst : scores first <;> cases hsecond : scores second <;> simp
  have hswap : (∑ scores : Fin n → Bool, (∏ member, weight member (scores member)) *
      pairValue (scores first) (scores second)) =
      ∑ u : Bool, ∑ v : Bool, (∑ scores : Fin n → Bool,
        (∏ member, weight member (scores member)) *
          ((if scores first = u then (1 : ℝ) else 0) *
            if scores second = v then (1 : ℝ) else 0)) * pairValue u v := by
    simp only [hexpand, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun u _ ↦ ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun v _ ↦ ?_
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun scores _ ↦ by ring
  rw [hswap, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun u _ ↦ ?_
  rw [Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun v _ ↦ ?_
  have hpinned := sum_prod_pinned first second hne weight u v
  calc (∑ scores : Fin n → Bool, (∏ member, weight member (scores member)) *
          ((if scores first = u then (1 : ℝ) else 0) *
            if scores second = v then (1 : ℝ) else 0)) * pairValue u v *
        ((∑ value : Bool, weight first value) * ∑ value : Bool, weight second value)
      = ((∑ scores : Fin n → Bool, (∏ member, weight member (scores member)) *
            ((if scores first = u then (1 : ℝ) else 0) *
              if scores second = v then (1 : ℝ) else 0)) *
          ((∑ value : Bool, weight first value) * ∑ value : Bool, weight second value)) *
          pairValue u v := by ring
    _ = ((∏ member, ∑ value : Bool, weight member value) *
          (weight first u * weight second v)) * pairValue u v := by rw [hpinned]
    _ = (∏ member, ∑ value : Bool, weight member value) *
          (weight first u * weight second v * pairValue u v) := by ring

/-- The pair count determined by the outcome vector of a cohort. -/
noncomputable def outcomePairMass {n : ℕ} (outcomes : Fin n → Bool) : ℝ :=
  (∑ member, if outcomes member = true then (1 : ℝ) else 0) *
    ∑ member, if outcomes member = false then (1 : ℝ) else 0

/-- The definedness indicator determined by the outcome vector of a cohort. -/
noncomputable def outcomeDefinedIndicator {n : ℕ} (outcomes : Fin n → Bool) : ℝ :=
  if (¬ ∀ member, outcomes member = false) ∧ ¬ ∀ member, outcomes member = true then 1 else 0

/-- The cohort pair count reads only the outcome vector. -/
theorem empiricalPairMass_eq_outcomePairMass {n : ℕ} (sample : Fin n → Bool × Bool) :
    empiricalPairMass sample = outcomePairMass fun member ↦ caseOf (sample member) := rfl

/-- The cohort definedness indicator reads only the outcome vector. -/
theorem aucDefinedIndicator_eq_outcomeDefinedIndicator {n : ℕ}
    (sample : Fin n → Bool × Bool) :
    aucDefinedIndicator sample = outcomeDefinedIndicator fun member ↦ caseOf (sample member) :=
  rfl

/-- An outcome vector has a positive pair count exactly when it carries a case and a
control. -/
theorem outcomePairMass_pos_iff {n : ℕ} (outcomes : Fin n → Bool) :
    0 < outcomePairMass outcomes ↔
      (¬ ∀ member, outcomes member = false) ∧ ¬ ∀ member, outcomes member = true :=
  empiricalPairMass_pos_iff fun member ↦ ((false : Bool), outcomes member)

/-- Inside one outcome fibre every ordered case-control pair contributes the same two-replica
moment, so the marginalised ranking credit is the population credit times the pair count.
This is the conditioning step of NOTE1 (42), in cleared form. -/
theorem outcome_fiber_numerator (law : FiniteReportLaw (Bool × Bool)) {n : ℕ}
    (outcomes : Fin n → Bool) :
    outcomeMass law true * outcomeMass law false *
        ∑ scores : Fin n → Bool, (∏ member, law.mass (scores member, outcomes member)) *
          empiricalAUCNumerator fun member ↦ (scores member, outcomes member) =
      law.binaryAUCNumerator scoreOf caseOf * outcomePairMass outcomes *
        ∏ member, outcomeMass law (outcomes member) := by
  have hterm : ∀ caseMember controlMember : Fin n,
      outcomeMass law true * outcomeMass law false *
          ∑ scores : Fin n → Bool, (∏ member, law.mass (scores member, outcomes member)) *
            (if outcomes caseMember && !outcomes controlMember then
              empiricalAUCComparison (alleleValue (scores caseMember))
                (alleleValue (scores controlMember))
            else 0) =
        (if outcomes caseMember && !outcomes controlMember then (1 : ℝ) else 0) *
          (law.binaryAUCNumerator scoreOf caseOf *
            ∏ member, outcomeMass law (outcomes member)) := by
    intro caseMember controlMember
    by_cases hpair : outcomes caseMember && !outcomes controlMember = true
    · obtain ⟨hcase, hcontrol⟩ := (caseControl_iff _ _).mp hpair
      have hne : caseMember ≠ controlMember := by
        intro heq
        rw [heq, hcontrol] at hcase
        exact Bool.false_ne_true hcase
      have hpaired := sum_prod_pair caseMember controlMember hne
        (fun member value ↦ law.mass (value, outcomes member))
        fun u v ↦ empiricalAUCComparison (alleleValue u) (alleleValue v)
      rw [hcase, hcontrol] at hpaired
      rw [sum_mass_eq_outcomeMass, sum_mass_eq_outcomeMass] at hpaired
      have hmarginal : ∀ member : Fin n,
          (∑ value : Bool, law.mass (value, outcomes member)) =
            outcomeMass law (outcomes member) :=
        fun member ↦ sum_mass_eq_outcomeMass law (outcomes member)
      rw [Finset.prod_congr rfl fun member _ ↦ hmarginal member,
        ← binaryAUCNumerator_eq_pairSum] at hpaired
      rw [if_pos hpair, one_mul]
      rw [Finset.sum_congr rfl fun scores _ ↦ by rw [if_pos hpair]]
      rw [← hpaired]
      ring
    · rw [if_neg hpair, zero_mul]
      rw [Finset.sum_congr rfl fun scores _ ↦ by rw [if_neg hpair, mul_zero]]
      rw [Finset.sum_const_zero, mul_zero]
  have hnumerator : ∀ scores : Fin n → Bool,
      empiricalAUCNumerator (fun member ↦ (scores member, outcomes member)) =
        ∑ caseMember, ∑ controlMember,
          if outcomes caseMember && !outcomes controlMember then
            empiricalAUCComparison (alleleValue (scores caseMember))
              (alleleValue (scores controlMember))
          else 0 := fun _ ↦ rfl
  have hcount : (∑ caseMember : Fin n, ∑ controlMember : Fin n,
      if outcomes caseMember && !outcomes controlMember then (1 : ℝ) else 0) =
      outcomePairMass outcomes :=
    (empiricalPairMass_eq_sum fun member ↦ ((false : Bool), outcomes member)).symm
  have hswap : (∑ scores : Fin n → Bool,
      (∏ member, law.mass (scores member, outcomes member)) *
        empiricalAUCNumerator fun member ↦ (scores member, outcomes member)) =
      ∑ caseMember : Fin n, ∑ controlMember : Fin n,
        ∑ scores : Fin n → Bool, (∏ member, law.mass (scores member, outcomes member)) *
          (if outcomes caseMember && !outcomes controlMember then
            empiricalAUCComparison (alleleValue (scores caseMember))
              (alleleValue (scores controlMember))
          else 0) := by
    simp only [hnumerator, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun caseMember _ ↦ ?_
    rw [Finset.sum_comm]
  rw [hswap, Finset.mul_sum]
  rw [Finset.sum_congr rfl fun caseMember _ ↦ by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun controlMember _ ↦ hterm caseMember controlMember]
  rw [← Finset.sum_mul, ← Finset.sum_congr rfl fun caseMember _ ↦ Finset.sum_mul _ _ _]
  rw [hcount]
  ring

/-- The fibrewise form of NOTE1 (42): on one outcome fibre the definedness-weighted empirical
AUC carries exactly the population credit. -/
theorem outcome_fiber_identity (law : FiniteReportLaw (Bool × Bool)) {n : ℕ}
    (outcomes : Fin n → Bool) :
    outcomeMass law true * outcomeMass law false *
        ∑ scores : Fin n → Bool, (∏ member, law.mass (scores member, outcomes member)) *
          (empiricalAUC (fun member ↦ (scores member, outcomes member)) *
            aucDefinedIndicator fun member ↦ (scores member, outcomes member)) =
      law.binaryAUCNumerator scoreOf caseOf *
        ((∏ member, outcomeMass law (outcomes member)) * outcomeDefinedIndicator outcomes) := by
  have hindicator : ∀ scores : Fin n → Bool,
      aucDefinedIndicator (fun member ↦ (scores member, outcomes member)) =
        outcomeDefinedIndicator outcomes := fun _ ↦ rfl
  have hauc : ∀ scores : Fin n → Bool,
      empiricalAUC (fun member ↦ (scores member, outcomes member)) =
        empiricalAUCNumerator (fun member ↦ (scores member, outcomes member)) /
          outcomePairMass outcomes := fun _ ↦ rfl
  by_cases hdefined : (¬ ∀ member, outcomes member = false) ∧
      ¬ ∀ member, outcomes member = true
  · have hpositive : 0 < outcomePairMass outcomes :=
      (outcomePairMass_pos_iff outcomes).mpr hdefined
    have hnonzero : outcomePairMass outcomes ≠ 0 := ne_of_gt hpositive
    rw [outcomeDefinedIndicator, if_pos hdefined, mul_one]
    have hfactor : (∑ scores : Fin n → Bool,
        (∏ member, law.mass (scores member, outcomes member)) *
          (empiricalAUC (fun member ↦ (scores member, outcomes member)) *
            aucDefinedIndicator fun member ↦ (scores member, outcomes member))) =
        (∑ scores : Fin n → Bool, (∏ member, law.mass (scores member, outcomes member)) *
          empiricalAUCNumerator fun member ↦ (scores member, outcomes member)) /
          outcomePairMass outcomes := by
      rw [Finset.sum_div]
      refine Finset.sum_congr rfl fun scores _ ↦ ?_
      rw [hindicator, outcomeDefinedIndicator, if_pos hdefined, mul_one, hauc]
      field_simp
    rw [hfactor, mul_div_assoc', outcome_fiber_numerator law outcomes]
    field_simp
    ring
  · rw [outcomeDefinedIndicator, if_neg hdefined, mul_zero, mul_zero]
    have hzero : ∀ scores : Fin n → Bool,
        (∏ member, law.mass (scores member, outcomes member)) *
          (empiricalAUC (fun member ↦ (scores member, outcomes member)) *
            aucDefinedIndicator fun member ↦ (scores member, outcomes member)) = 0 := by
      intro scores
      rw [hindicator, outcomeDefinedIndicator, if_neg hdefined, mul_zero, mul_zero]
    rw [Finset.sum_congr rfl fun scores _ ↦ hzero scores, Finset.sum_const_zero, mul_zero]

/-- NOTE1 (42) in cleared form: the definedness-weighted empirical AUC of an independent
cohort carries exactly the population ranking credit, with no positivity premise. -/
theorem auc_numerator_identity (law : FiniteReportLaw (Bool × Bool)) (n : ℕ) :
    outcomeMass law true * outcomeMass law false *
        (cohortLaw law n).expectation
          (fun sample ↦ empiricalAUC sample * aucDefinedIndicator sample) =
      law.binaryAUCNumerator scoreOf caseOf *
        (cohortLaw law n).expectation aucDefinedIndicator := by
  rw [cohort_expectation_split law n
      fun sample ↦ empiricalAUC sample * aucDefinedIndicator sample,
    cohort_expectation_split law n aucDefinedIndicator, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun outcomes _ ↦ ?_
  have hdelta : (∑ scores : Fin n → Bool,
      (∏ member, law.mass (scores member, outcomes member)) *
        aucDefinedIndicator fun member ↦ (scores member, outcomes member)) =
      (∏ member, outcomeMass law (outcomes member)) * outcomeDefinedIndicator outcomes := by
    rw [← sum_prod_mass law outcomes, Finset.sum_mul]
    rfl
  rw [hdelta]
  exact outcome_fiber_identity law outcomes

/-- NOTE1 (42): conditional on being defined, the empirical AUC of an independent cohort is
exactly the population AUC of the individual-level law.

Assumes: both outcome classes carry positive mass, and the cohort size makes definedness
possible. -/
theorem conditional_empiricalAUC (law : FiniteReportLaw (Bool × Bool)) (n : ℕ)
    (hcase : 0 < outcomeMass law true) (hcontrol : 0 < outcomeMass law false)
    (hdefined : 0 < (cohortLaw law n).expectation aucDefinedIndicator) :
    (cohortLaw law n).expectation
          (fun sample ↦ empiricalAUC sample * aucDefinedIndicator sample) /
        (cohortLaw law n).expectation aucDefinedIndicator = populationAUC law := by
  have hmass : law.binaryCaseMass caseOf = outcomeMass law true :=
    binaryCaseMass_eq_outcomeMass law
  have hcomplement : 1 - law.binaryCaseMass caseOf = outcomeMass law false := by
    rw [hmass]
    have := outcomeMass_add_eq_one law
    linarith
  have hkey := auc_numerator_identity law n
  rw [populationAUC, hmass, hcomplement]
  rw [div_eq_div_iff (ne_of_gt hdefined) (ne_of_gt (mul_pos hcase hcontrol))]
  linarith [hkey]

/-- NOTE1 (42) for the chronology cells: conditional on being defined, the empirical AUC of an
independent cohort is `(1 + C) / 2`. -/
theorem conditional_empiricalAUC_chronologyLaw (p C : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hC0 : 0 ≤ C) (hC1 : C ≤ 1) (hlow : 0 < p) (hhigh : p < 1) (n : ℕ)
    (hdefined : 0 < (cohortLaw (chronologyLaw p C hp0 hp1 hC0 hC1) n).expectation
      aucDefinedIndicator) :
    (cohortLaw (chronologyLaw p C hp0 hp1 hC0 hC1) n).expectation
          (fun sample ↦ empiricalAUC sample * aucDefinedIndicator sample) /
        (cohortLaw (chronologyLaw p C hp0 hp1 hC0 hC1) n).expectation aucDefinedIndicator =
      (1 + C) / 2 := by
  obtain ⟨hcase, hcontrol⟩ := outcomeMass_chronologyLaw p C hp0 hp1 hC0 hC1
  rw [conditional_empiricalAUC _ n (by rw [hcase]; exact hlow)
      (by rw [hcontrol]; linarith),
    populationAUC_chronologyLaw p C hp0 hp1 hC0 hC1 hlow hhigh]

end Descent.Portability.EmpiricalAUCUnbiasedness
