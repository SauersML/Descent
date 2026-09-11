/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.EmpiricalCorrelationDefinedness
import Descent.Portability.ChronologyReportLaw

assert_below Descent.Decision Descent.Program

/-!
# Small independent cohorts: the exact conditional empirical correlation

NOTE1 Corollary 7.1 records what the empirical squared correlation of a small independent
cohort actually reports. At `n = 2` it reports one whatever the underlying law is (40); at
`n = 3` with equal marginals at one half the definedness probability is `3(C² + 3)/16` and the
conditional mean is `(5C² + 3)/(2(C² + 3))` (41); and at `p = C = 1/2` the definedness
probabilities at `n = 2, 3, 4` are `5/16`, `39/64` and `809/1024`.

This module proves the `n = 2` statement and every definedness value. The `n = 2` statement is
proved pointwise rather than by enumerating the law: a two-member cohort whose table is
defined has all four marginal totals equal to one, so its table is `(1,0,0,1)` or `(0,1,1,0)`
and its empirical squared correlation is one. The conclusion therefore holds for every
four-cell law with positive definedness mass, which is the content of (40): two observations
with nonzero sample variance have sample correlation of modulus one, so the statistic carries
no information about the population correlation at all.

The definedness values come from the general inclusion–exclusion probability of NOTE1 (39),
specialised to the chronology cells of NOTE1 (31). `definedness_probability_chronologyLaw` is
the general `(p, C)` form, `definedness_probability_half` is the `p = 1/2` form of (41), and
`definedness_probability_halvedCoupling` gives the three numerical values at `p = C = 1/2`.

Not formalised here: the conditional mean `(5C² + 3)/(2(C² + 3))` at `n = 3` and the values
`17/26` and `419/809` at `n = 3, 4`. They require summing the empirical squared correlation
against the multinomial masses over the defined count vectors; that enumeration is carried out
downstream, in `SmallCohortConditionalMeans`.

## Empirical status

None. The bodies here are algebra: the `n = 2` statement is a case analysis on four natural
numbers summing to two, and the definedness values are the inclusion–exclusion probability
evaluated at particular cells. No measurement on any cohort can bear on them.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.SmallCohortCorrelation

open FourCellCohortLaw EmpiricalCorrelationDefinedness ChronologyReportLaw

/-- A two-member cohort with a defined table has all four marginal totals equal to one, so its
empirical squared correlation is one. This is NOTE1 (40). -/
theorem empiricalR2_eq_one_of_two (a b c d : ℕ) (htotal : a + b + c + d = 2)
    (hdefined : Defined a b c d) : empiricalR2 a b c d = 1 := by
  obtain ⟨hab, hcd, hac, hbd⟩ := hdefined
  have hcases : (a = 1 ∧ b = 0 ∧ c = 0 ∧ d = 1) ∨ (a = 0 ∧ b = 1 ∧ c = 1 ∧ d = 0) := by omega
  rcases hcases with ⟨ha, hb, hc, hd⟩ | ⟨ha, hb, hc, hd⟩ <;>
    · subst ha
      subst hb
      subst hc
      subst hd
      norm_num [empiricalR2]

/-- The empirical squared correlation of a cohort, read off its four cell counts. -/
noncomputable def cohortCorrelation {n : ℕ} (sample : Fin n → Bool × Bool) : ℝ :=
  empiricalR2 (cellCount sample (false, false)) (cellCount sample (false, true))
    (cellCount sample (true, false)) (cellCount sample (true, true))

/-- On every two-member cohort the empirical squared correlation weighted by definedness is
the definedness indicator itself. -/
theorem cohortCorrelation_mul_definedIndicator (sample : Fin 2 → Bool × Bool) :
    cohortCorrelation sample * definedIndicator sample = definedIndicator sample := by
  unfold definedIndicator
  by_cases hdefined : Defined (cellCount sample (false, false)) (cellCount sample (false, true))
      (cellCount sample (true, false)) (cellCount sample (true, true))
  · rw [if_pos hdefined, mul_one, cohortCorrelation,
      empiricalR2_eq_one_of_two _ _ _ _ (fourCell_sum_cellCount sample) hdefined]
  · rw [if_neg hdefined, mul_zero]

/-- NOTE1 (40) at the level of the cohort law: the definedness-weighted empirical squared
correlation of a two-member cohort carries exactly the definedness mass, for every four-cell
law. -/
theorem expectation_cohortCorrelation_two (law : FiniteReportLaw (Bool × Bool)) :
    (cohortLaw law 2).expectation
        (fun sample ↦ cohortCorrelation sample * definedIndicator sample) =
      (cohortLaw law 2).expectation definedIndicator := by
  congr 1
  funext sample
  exact cohortCorrelation_mul_definedIndicator sample

/-- NOTE1 (40): conditional on being defined, the empirical squared correlation of a
two-member cohort is one whatever the underlying four-cell law is. -/
theorem conditional_cohortCorrelation_two (law : FiniteReportLaw (Bool × Bool))
    (hpositive : 0 < (cohortLaw law 2).expectation definedIndicator) :
    (cohortLaw law 2).expectation
          (fun sample ↦ cohortCorrelation sample * definedIndicator sample) /
        (cohortLaw law 2).expectation definedIndicator = 1 := by
  rw [expectation_cohortCorrelation_two, div_self (ne_of_gt hpositive)]

/-- The score and outcome marginals of the chronology law of NOTE1 (31) agree, both equal to
the donor ancestry fraction. -/
theorem scoreMass_eq_outcomeMass_chronologyLaw (p C : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hC0 : 0 ≤ C) (hC1 : C ≤ 1) (value : Bool) :
    scoreMass (chronologyLaw p C hp0 hp1 hC0 hC1) value =
      outcomeMass (chronologyLaw p C hp0 hp1 hC0 hC1) value := by
  cases value <;>
    simp only [scoreMass, outcomeMass, chronologyLaw_mass, chronologyMass_false_false,
      chronologyMass_false_true, chronologyMass_true_false, chronologyMass_true_true]

/-- The score marginal of the chronology law at the donor allele is the ancestry fraction. -/
theorem scoreMass_chronologyLaw_true (p C : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hC0 : 0 ≤ C)
    (hC1 : C ≤ 1) : scoreMass (chronologyLaw p C hp0 hp1 hC0 hC1) true = p := by
  simp only [scoreMass, chronologyLaw_mass, chronologyMass_true_false,
    chronologyMass_true_true]
  ring

/-- The score marginal of the chronology law at the recipient allele is its complement. -/
theorem scoreMass_chronologyLaw_false (p C : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hC0 : 0 ≤ C)
    (hC1 : C ≤ 1) : scoreMass (chronologyLaw p C hp0 hp1 hC0 hC1) false = 1 - p := by
  simp only [scoreMass, chronologyLaw_mass, chronologyMass_false_false,
    chronologyMass_false_true]
  ring

/-- NOTE1 (39) at the chronology cells of NOTE1 (31): the exact probability that the empirical
squared correlation of an independent cohort of size `n` is defined. -/
theorem definedness_probability_chronologyLaw (p C : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hC0 : 0 ≤ C) (hC1 : C ≤ 1) (n : ℕ) (hn : 0 < n) :
    (cohortLaw (chronologyLaw p C hp0 hp1 hC0 hC1) n).expectation definedIndicator =
      1 - 2 * (p ^ n + (1 - p) ^ n) + (((1 - p) ^ 2 + p * (1 - p) * C) ^ n +
        2 * (p * (1 - p) * (1 - C)) ^ n + (p ^ 2 + p * (1 - p) * C) ^ n) := by
  rw [definedness_probability_of_equal_marginals _ n hn
      (scoreMass_eq_outcomeMass_chronologyLaw p C hp0 hp1 hC0 hC1),
    scoreMass_chronologyLaw_true, scoreMass_chronologyLaw_false]
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, chronologyLaw_mass,
    chronologyMass_false_false, chronologyMass_false_true, chronologyMass_true_false,
    chronologyMass_true_true]
  ring

/-- NOTE1 (41): at `p = 1/2` an independent cohort of three individuals has a defined
empirical squared correlation with probability `3(C² + 3)/16`. -/
theorem definedness_probability_half (C : ℝ) (hC0 : 0 ≤ C) (hC1 : C ≤ 1) :
    (cohortLaw (chronologyLaw (1 / 2) C (by norm_num) (by norm_num) hC0 hC1) 3).expectation
        definedIndicator = 3 * (C ^ 2 + 3) / 16 := by
  rw [definedness_probability_chronologyLaw (1 / 2) C _ _ hC0 hC1 3 (by norm_num)]
  ring

/-- The three definedness probabilities of the NOTE1 section 7 table at `p = C = 1/2`: the
empirical squared correlation of a cohort of two, three or four individuals is defined with
probability `5/16`, `39/64` and `809/1024`. -/
theorem definedness_probability_halvedCoupling :
    (cohortLaw halvedCouplingLaw 2).expectation definedIndicator = 5 / 16 ∧
      (cohortLaw halvedCouplingLaw 3).expectation definedIndicator = 39 / 64 ∧
        (cohortLaw halvedCouplingLaw 4).expectation definedIndicator = 809 / 1024 := by
  unfold halvedCouplingLaw
  refine ⟨?_, ?_, ?_⟩
  · rw [definedness_probability_chronologyLaw (1 / 2) (1 / 2) _ _ _ _ 2 (by norm_num)]
    norm_num
  · rw [definedness_probability_chronologyLaw (1 / 2) (1 / 2) _ _ _ _ 3 (by norm_num)]
    norm_num
  · rw [definedness_probability_chronologyLaw (1 / 2) (1 / 2) _ _ _ _ 4 (by norm_num)]
    norm_num

end Descent.Portability.SmallCohortCorrelation
