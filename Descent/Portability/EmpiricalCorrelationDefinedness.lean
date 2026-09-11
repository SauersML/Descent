/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.FourCellCohortLaw
import Descent.Portability.ExactMetricEvaluation
import Descent.Portability.FiniteIndependentMoments

assert_below Descent.Decision Descent.Program

/-!
# The empirical squared correlation of a two-by-two table and its definedness probability

NOTE1 (38) writes the empirical squared correlation of a cohort in terms of the four cell
counts `(a, b, c, d) = (N₀₀, N₀₁, N₁₀, N₁₁)` as `(ad − bc)² / ((a+b)(c+d)(a+c)(b+d))`, defined
exactly when all four marginal totals are positive. NOTE1 (39) gives the exact probability that
it is defined for an independent cohort of size `n`.

Both are proved here. The first is proved as an identification rather than a redefinition: the
empirical distribution of a two-by-two table is a `FiniteReportLaw (Bool × Bool)` (`tableLaw`),
and `tableLaw_squaredCorrelation` shows that the corpus `FiniteReportLaw.squaredCorrelation` of
that law, with the score read by `Prod.fst` and the outcome by `Prod.snd`, is `some` of the
NOTE1 (38) expression exactly when the table is `Defined`, and `none` otherwise. The corpus
definition is the sample Pearson correlation squared, and `expectation_tableLaw_cellCount`
records that the empirical law of a cohort sample averages over the cohort members, so the
statement is about the two Boolean sequences and not about a separate formula.

The definedness probability is `definedness_probability`. It is the general form of NOTE1 (39),
with the two marginals kept separate: `1 − P_S(0)ⁿ − P_S(1)ⁿ − P_Y(0)ⁿ − P_Y(1)ⁿ + Σ P_sy ⁿ`.
The proof is the inclusion–exclusion of the NOTE: a cohort fails definedness exactly when all
scores agree or all outcomes agree, those two events intersect in the four all-in-one-cell
events, and each such event has probability a single cell or marginal mass to the power `n`
because the cohort law is a product. `definedness_probability_of_equal_marginals` is the
displayed form of (39), `1 − 2[pⁿ + (1−p)ⁿ] + Σ P_sy ⁿ`, under the hypothesis that the score
and outcome marginals agree, which is what the chronology law of NOTE1 (31) delivers.

Not formalised here: the conditional expectation of the empirical squared correlation, which is
the subject of the small-cohort module, and any claim about which tables arise from a
demographic history.

## Empirical status

None. The bodies here are algebra: the correlation formula is an identity between two ways of
writing one finite sum, and the definedness probability is inclusion–exclusion on a finite
product law. No measurement on any cohort can bear on either.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.EmpiricalCorrelationDefinedness

open FourCellCohortLaw

/-- The empirical squared correlation of a two-by-two table of counts, NOTE1 (38). -/
noncomputable def empiricalR2 (a b c d : ℕ) : ℝ :=
  ((a : ℝ) * d - (b : ℝ) * c) ^ 2 /
    (((a : ℝ) + b) * ((c : ℝ) + d) * (((a : ℝ) + c) * ((b : ℝ) + d)))

/-- All four marginal totals of a two-by-two table are positive. NOTE1 (38) is defined exactly
under this condition. -/
def Defined (a b c d : ℕ) : Prop := 0 < a + b ∧ 0 < c + d ∧ 0 < a + c ∧ 0 < b + d

instance instDecidableDefined (a b c d : ℕ) : Decidable (Defined a b c d) :=
  inferInstanceAs (Decidable (0 < a + b ∧ 0 < c + d ∧ 0 < a + c ∧ 0 < b + d))

/-- The Boolean score of a cell, read as a real number. -/
def scoreValue (cell : Bool × Bool) : ℝ := if cell.1 = true then 1 else 0

/-- The Boolean outcome of a cell, read as a real number. -/
def outcomeValue (cell : Bool × Bool) : ℝ := if cell.2 = true then 1 else 0

/-- The empirical law of a two-by-two table of counts with a positive total. -/
noncomputable def tableLaw (count : Bool × Bool → ℕ) (hpos : 0 < ∑ cell, count cell) :
    FiniteReportLaw (Bool × Bool) where
  mass cell := (count cell : ℝ) / ((∑ cell', count cell' : ℕ) : ℝ)
  mass_nonneg _ := by positivity
  mass_sum := by
    have hposR : (0 : ℝ) < ((∑ cell, count cell : ℕ) : ℝ) := by exact_mod_cast hpos
    rw [← Finset.sum_div, ← Nat.cast_sum, div_self (ne_of_gt hposR)]

/-- The total of a two-by-two table is the sum of its four entries. -/
theorem sum_count_eq (count : Bool × Bool → ℕ) :
    ((∑ cell, count cell : ℕ) : ℝ) =
      (count (false, false) : ℝ) + count (false, true) + count (true, false) +
        count (true, true) := by
  rw [Nat.cast_sum]
  simp only [Fintype.sum_prod_type, Fintype.sum_bool]
  ring

/-- Every expectation under the empirical law of a table is the count-weighted average of the
four cell values. -/
theorem expectation_tableLaw (count : Bool × Bool → ℕ) (hpos : 0 < ∑ cell, count cell)
    (weight : Bool × Bool → ℝ) :
    (tableLaw count hpos).expectation weight =
      ((count (false, false) : ℝ) * weight (false, false) +
        (count (false, true) : ℝ) * weight (false, true) +
        (count (true, false) : ℝ) * weight (true, false) +
        (count (true, true) : ℝ) * weight (true, true)) /
        ((∑ cell, count cell : ℕ) : ℝ) := by
  have hposR : (0 : ℝ) < ((∑ cell, count cell : ℕ) : ℝ) := by exact_mod_cast hpos
  have hne : ((∑ cell, count cell : ℕ) : ℝ) ≠ 0 := ne_of_gt hposR
  simp only [FiniteReportLaw.expectation, tableLaw, Fintype.sum_prod_type, Fintype.sum_bool]
  field_simp
  ring

/-- A sample average over the cohort members is the count-weighted average over the cells. -/
theorem sum_eq_sum_cellCount {n : ℕ} (weight : Bool × Bool → ℝ)
    (sample : Fin n → Bool × Bool) :
    (∑ member, weight (sample member)) = ∑ cell, (cellCount sample cell : ℝ) * weight cell := by
  rw [← Finset.sum_fiberwise' (Finset.univ : Finset (Fin n)) sample weight]
  refine Finset.sum_congr rfl fun cell _ ↦ ?_
  rw [Finset.sum_const]
  exact nsmul_eq_mul _ _

/-- The empirical law of a cohort sample averages exactly over the cohort members, so the
moments below are the sample moments of the two Boolean sequences. -/
theorem expectation_tableLaw_cellCount {n : ℕ} (sample : Fin n → Bool × Bool)
    (hpos : 0 < ∑ cell, cellCount sample cell) (weight : Bool × Bool → ℝ) :
    (tableLaw (cellCount sample) hpos).expectation weight =
      (∑ member, weight (sample member)) / (n : ℝ) := by
  have hn : (∑ cell, cellCount sample cell) = n := sum_cellCount sample
  rw [sum_eq_sum_cellCount]
  simp only [FiniteReportLaw.expectation, tableLaw, hn]
  rw [Finset.sum_div]
  exact Finset.sum_congr rfl fun cell _ ↦ by ring

/-- The sample variance of the Boolean score of a table is `(a+b)(c+d)/n²`. -/
theorem tableLaw_variance_scoreValue (count : Bool × Bool → ℕ)
    (hpos : 0 < ∑ cell, count cell) :
    (tableLaw count hpos).variance scoreValue =
      (((count (false, false) : ℝ) + count (false, true)) *
          ((count (true, false) : ℝ) + count (true, true))) /
        ((∑ cell, count cell : ℕ) : ℝ) ^ 2 := by
  have hposR : (0 : ℝ) < ((∑ cell, count cell : ℕ) : ℝ) := by exact_mod_cast hpos
  have hne : ((count (false, false) : ℝ) + count (false, true) + count (true, false) +
      count (true, true)) ≠ 0 := by
    rw [← sum_count_eq]
    exact ne_of_gt hposR
  rw [FiniteReportLaw.variance_eq_rawMoments, expectation_tableLaw, expectation_tableLaw,
    sum_count_eq]
  norm_num [scoreValue]
  field_simp
  ring

/-- The sample variance of the Boolean outcome of a table is `(a+c)(b+d)/n²`. -/
theorem tableLaw_variance_outcomeValue (count : Bool × Bool → ℕ)
    (hpos : 0 < ∑ cell, count cell) :
    (tableLaw count hpos).variance outcomeValue =
      (((count (false, false) : ℝ) + count (true, false)) *
          ((count (false, true) : ℝ) + count (true, true))) /
        ((∑ cell, count cell : ℕ) : ℝ) ^ 2 := by
  have hposR : (0 : ℝ) < ((∑ cell, count cell : ℕ) : ℝ) := by exact_mod_cast hpos
  have hne : ((count (false, false) : ℝ) + count (false, true) + count (true, false) +
      count (true, true)) ≠ 0 := by
    rw [← sum_count_eq]
    exact ne_of_gt hposR
  rw [FiniteReportLaw.variance_eq_rawMoments, expectation_tableLaw, expectation_tableLaw,
    sum_count_eq]
  norm_num [outcomeValue]
  field_simp
  ring

/-- The sample covariance of the Boolean score and outcome of a table is `(ad − bc)/n²`. -/
theorem tableLaw_covariance (count : Bool × Bool → ℕ) (hpos : 0 < ∑ cell, count cell) :
    (tableLaw count hpos).covariance scoreValue outcomeValue =
      ((count (false, false) : ℝ) * count (true, true) -
          (count (false, true) : ℝ) * count (true, false)) /
        ((∑ cell, count cell : ℕ) : ℝ) ^ 2 := by
  have hposR : (0 : ℝ) < ((∑ cell, count cell : ℕ) : ℝ) := by exact_mod_cast hpos
  have hne : ((count (false, false) : ℝ) + count (false, true) + count (true, false) +
      count (true, true)) ≠ 0 := by
    rw [← sum_count_eq]
    exact ne_of_gt hposR
  rw [FiniteReportLaw.covariance_eq_rawMoments, expectation_tableLaw, expectation_tableLaw,
    expectation_tableLaw, sum_count_eq]
  norm_num [scoreValue, outcomeValue]
  field_simp
  ring

/-- A sum of two natural numbers is positive exactly when its real cast is. -/
theorem cast_add_pos (first second : ℕ) :
    (0 : ℝ) < (first : ℝ) + second ↔ 0 < first + second := by
  rw [← Nat.cast_add, Nat.cast_pos]

/-- A product of two nonnegative reals is positive exactly when both factors are. -/
theorem mul_pos_iff_of_nonneg (first second : ℝ) (hfirst : 0 ≤ first) (hsecond : 0 ≤ second) :
    0 < first * second ↔ 0 < first ∧ 0 < second := by
  constructor
  · intro hprod
    refine ⟨?_, ?_⟩
    · rcases hfirst.lt_or_eq with hlt | heq
      · exact hlt
      · rw [← heq, zero_mul] at hprod
        exact absurd hprod (lt_irrefl 0)
    · rcases hsecond.lt_or_eq with hlt | heq
      · exact hlt
      · rw [← heq, mul_zero] at hprod
        exact absurd hprod (lt_irrefl 0)
  · rintro ⟨hfirstpos, hsecondpos⟩
    exact mul_pos hfirstpos hsecondpos

/-- NOTE1 (38): the corpus squared Pearson correlation of the empirical law of a two-by-two
table is the empirical squared correlation, and it is defined exactly when all four marginal
totals of the table are positive. -/
theorem tableLaw_squaredCorrelation (count : Bool × Bool → ℕ)
    (hpos : 0 < ∑ cell, count cell) :
    (tableLaw count hpos).squaredCorrelation scoreValue outcomeValue =
      if Defined (count (false, false)) (count (false, true)) (count (true, false))
          (count (true, true)) then
        some (empiricalR2 (count (false, false)) (count (false, true)) (count (true, false))
          (count (true, true)))
      else none := by
  have hposR : (0 : ℝ) < ((∑ cell, count cell : ℕ) : ℝ) := by exact_mod_cast hpos
  have hsq : (0 : ℝ) < ((∑ cell, count cell : ℕ) : ℝ) ^ 2 := by positivity
  have hvarS := tableLaw_variance_scoreValue count hpos
  have hvarY := tableLaw_variance_outcomeValue count hpos
  have hcov := tableLaw_covariance count hpos
  have hcondS : 0 < (tableLaw count hpos).variance scoreValue ↔
      0 < count (false, false) + count (false, true) ∧
        0 < count (true, false) + count (true, true) := by
    rw [hvarS, lt_div_iff₀ hsq, zero_mul,
      mul_pos_iff_of_nonneg _ _ (by positivity) (by positivity), cast_add_pos, cast_add_pos]
  have hcondY : 0 < (tableLaw count hpos).variance outcomeValue ↔
      0 < count (false, false) + count (true, false) ∧
        0 < count (false, true) + count (true, true) := by
    rw [hvarY, lt_div_iff₀ hsq, zero_mul,
      mul_pos_iff_of_nonneg _ _ (by positivity) (by positivity), cast_add_pos, cast_add_pos]
  have hequiv : (0 < (tableLaw count hpos).variance scoreValue ∧
      0 < (tableLaw count hpos).variance outcomeValue) ↔
      Defined (count (false, false)) (count (false, true)) (count (true, false))
        (count (true, true)) := by
    rw [hcondS, hcondY, Defined]
    tauto
  unfold FiniteReportLaw.squaredCorrelation
  by_cases hdef : Defined (count (false, false)) (count (false, true)) (count (true, false))
      (count (true, true))
  · obtain ⟨hab, hcd, hac, hbd⟩ := hdef
    have habR : ((count (false, false) : ℝ) + count (false, true)) ≠ 0 :=
      ne_of_gt ((cast_add_pos _ _).mpr hab)
    have hcdR : ((count (true, false) : ℝ) + count (true, true)) ≠ 0 :=
      ne_of_gt ((cast_add_pos _ _).mpr hcd)
    have hacR : ((count (false, false) : ℝ) + count (true, false)) ≠ 0 :=
      ne_of_gt ((cast_add_pos _ _).mpr hac)
    have hbdR : ((count (false, true) : ℝ) + count (true, true)) ≠ 0 :=
      ne_of_gt ((cast_add_pos _ _).mpr hbd)
    rw [if_pos (hequiv.mpr ⟨hab, hcd, hac, hbd⟩), if_pos ⟨hab, hcd, hac, hbd⟩]
    congr 1
    rw [hvarS, hvarY, hcov, empiricalR2]
    field_simp
  · rw [if_neg fun hboth ↦ hdef (hequiv.mp hboth), if_neg hdef]

/-- The score marginal of a four-cell law, NOTE1 (31). -/
noncomputable def scoreMass (law : FiniteReportLaw (Bool × Bool)) (value : Bool) : ℝ :=
  law.mass (value, false) + law.mass (value, true)

/-- The outcome marginal of a four-cell law, NOTE1 (31). -/
noncomputable def outcomeMass (law : FiniteReportLaw (Bool × Bool)) (value : Bool) : ℝ :=
  law.mass (false, value) + law.mass (true, value)

/-- The indicator that a cell carries a given score. -/
def scoreIndicator (value : Bool) (cell : Bool × Bool) : ℝ :=
  if cell.1 = value then 1 else 0

/-- The indicator that a cell carries a given outcome. -/
def outcomeIndicator (value : Bool) (cell : Bool × Bool) : ℝ :=
  if cell.2 = value then 1 else 0

/-- The indicator of one cell. -/
def cellIndicator (target cell : Bool × Bool) : ℝ := if cell = target then 1 else 0

/-- A product of zero-one member indicators over the cohort is one exactly when every member
satisfies the test, and zero otherwise. -/
theorem prod_member_indicator {n : ℕ} (test : Fin n → Prop) [DecidablePred test] :
    (∏ member, if test member then (1 : ℝ) else 0) =
      if ∀ member, test member then 1 else 0 := by
  by_cases hall : ∀ member, test member
  · rw [if_pos hall]
    exact Finset.prod_eq_one fun member _ ↦ if_pos (hall member)
  · rw [if_neg hall]
    push_neg at hall
    obtain ⟨member, hmember⟩ := hall
    exact Finset.prod_eq_zero (Finset.mem_univ member) (if_neg hmember)

/-- The definedness indicator of a cohort sample, from its four cell counts. -/
noncomputable def definedIndicator {n : ℕ} (sample : Fin n → Bool × Bool) : ℝ :=
  if Defined (cellCount sample (false, false)) (cellCount sample (false, true))
      (cellCount sample (true, false)) (cellCount sample (true, true)) then 1 else 0

theorem expectation_scoreIndicator (law : FiniteReportLaw (Bool × Bool)) (value : Bool) :
    law.expectation (scoreIndicator value) = scoreMass law value := by
  cases value <;>
    simp [FiniteReportLaw.expectation, scoreIndicator, scoreMass, Fintype.sum_prod_type]
  all_goals ring

theorem expectation_outcomeIndicator (law : FiniteReportLaw (Bool × Bool)) (value : Bool) :
    law.expectation (outcomeIndicator value) = outcomeMass law value := by
  cases value <;>
    simp [FiniteReportLaw.expectation, outcomeIndicator, outcomeMass, Fintype.sum_prod_type]
  all_goals ring

theorem expectation_cellIndicator (law : FiniteReportLaw (Bool × Bool))
    (target : Bool × Bool) : law.expectation (cellIndicator target) = law.mass target := by
  simp [FiniteReportLaw.expectation, cellIndicator, Finset.sum_ite_eq']

/-- Under the independent cohort law the expectation of a product over the members is the
member expectation raised to the cohort size. -/
theorem cohort_expectation_prod (law : FiniteReportLaw (Bool × Bool)) (n : ℕ)
    (weight : Bool × Bool → ℝ) :
    (cohortLaw law n).expectation (fun sample ↦ ∏ member, weight (sample member)) =
      law.expectation weight ^ n := by
  have hlaw : cohortLaw law n = HWEInteractionLaw.independentLaw fun _ : Fin n ↦ law := rfl
  rw [hlaw, HWEInteractionLaw.expectation_independent_product (fun _ : Fin n ↦ law)
    (fun _ ↦ weight), Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- A cohort has a positive count in a score column exactly when some member carries that
score. -/
theorem cellCount_score_pos {n : ℕ} (sample : Fin n → Bool × Bool) (value : Bool) :
    0 < cellCount sample (value, false) + cellCount sample (value, true) ↔
      ∃ member, (sample member).1 = value := by
  constructor
  · intro hpos
    have hcases : 0 < cellCount sample (value, false) ∨ 0 < cellCount sample (value, true) := by
      omega
    rcases hcases with hcase | hcase
    · obtain ⟨member, hmember⟩ := Finset.card_pos.mp hcase
      exact ⟨member, by rw [(Finset.mem_filter.mp hmember).2]⟩
    · obtain ⟨member, hmember⟩ := Finset.card_pos.mp hcase
      exact ⟨member, by rw [(Finset.mem_filter.mp hmember).2]⟩
  · rintro ⟨member, hmember⟩
    have hcell : sample member = (value, (sample member).2) :=
      Prod.ext_iff.mpr ⟨hmember, rfl⟩
    have hmem : member ∈ Finset.univ.filter fun other ↦
        sample other = (value, (sample member).2) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ member, hcell⟩
    have hcount : 0 < cellCount sample (value, (sample member).2) :=
      Finset.card_pos.mpr ⟨member, hmem⟩
    cases hvalue : (sample member).2 <;> rw [hvalue] at hcount <;> omega

/-- A cohort has a positive count in an outcome row exactly when some member carries that
outcome. -/
theorem cellCount_outcome_pos {n : ℕ} (sample : Fin n → Bool × Bool) (value : Bool) :
    0 < cellCount sample (false, value) + cellCount sample (true, value) ↔
      ∃ member, (sample member).2 = value := by
  constructor
  · intro hpos
    have hcases : 0 < cellCount sample (false, value) ∨ 0 < cellCount sample (true, value) := by
      omega
    rcases hcases with hcase | hcase
    · obtain ⟨member, hmember⟩ := Finset.card_pos.mp hcase
      exact ⟨member, by rw [(Finset.mem_filter.mp hmember).2]⟩
    · obtain ⟨member, hmember⟩ := Finset.card_pos.mp hcase
      exact ⟨member, by rw [(Finset.mem_filter.mp hmember).2]⟩
  · rintro ⟨member, hmember⟩
    have hcell : sample member = ((sample member).1, value) :=
      Prod.ext_iff.mpr ⟨rfl, hmember⟩
    have hmem : member ∈ Finset.univ.filter fun other ↦
        sample other = ((sample member).1, value) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ member, hcell⟩
    have hcount : 0 < cellCount sample ((sample member).1, value) :=
      Finset.card_pos.mpr ⟨member, hmem⟩
    cases hvalue : (sample member).1 <;> rw [hvalue] at hcount <;> omega

/-- A cohort is defined exactly when neither the scores nor the outcomes are constant. -/
theorem defined_iff_not_constant {n : ℕ} (sample : Fin n → Bool × Bool) :
    Defined (cellCount sample (false, false)) (cellCount sample (false, true))
        (cellCount sample (true, false)) (cellCount sample (true, true)) ↔
      (¬ ∀ member, (sample member).1 = false) ∧ (¬ ∀ member, (sample member).1 = true) ∧
        (¬ ∀ member, (sample member).2 = false) ∧ (¬ ∀ member, (sample member).2 = true) := by
  have hnotall : ∀ (values : Fin n → Bool) (value : Bool),
      (∃ member, values member = value) ↔ ¬ ∀ member, values member = !value := by
    intro values value
    cases value <;> simp
  rw [Defined, cellCount_score_pos, cellCount_score_pos, cellCount_outcome_pos,
    cellCount_outcome_pos, hnotall, hnotall, hnotall, hnotall]
  simp only [Bool.not_false, Bool.not_true]
  tauto

/-- The inclusion–exclusion identity behind NOTE1 (39), for two mutually exclusive pairs of
events. -/
theorem inclusion_exclusion_two_pairs (first second third fourth : Prop) [Decidable first]
    [Decidable second] [Decidable third] [Decidable fourth] (hpair : ¬(first ∧ second))
    (hother : ¬(third ∧ fourth)) :
    (if ¬first ∧ ¬second ∧ ¬third ∧ ¬fourth then (1 : ℝ) else 0) =
      1 - (if first then (1 : ℝ) else 0) - (if second then (1 : ℝ) else 0) -
          (if third then (1 : ℝ) else 0) - (if fourth then (1 : ℝ) else 0) +
        ((if first then (1 : ℝ) else 0) + (if second then (1 : ℝ) else 0)) *
          ((if third then (1 : ℝ) else 0) + (if fourth then (1 : ℝ) else 0)) := by
  by_cases hfirst : first <;> by_cases hsecond : second <;> by_cases hthird : third <;>
    by_cases hfourth : fourth <;> simp_all

/-- The definedness indicator of a cohort expands into the four constant-report indicators and
the four all-in-one-cell indicators, exactly as in the inclusion–exclusion of NOTE1 (39). -/
theorem definedIndicator_expand {n : ℕ} (hn : 0 < n) (sample : Fin n → Bool × Bool) :
    definedIndicator sample =
      1 - (∏ member, scoreIndicator false (sample member)) -
          (∏ member, scoreIndicator true (sample member)) -
          (∏ member, outcomeIndicator false (sample member)) -
          (∏ member, outcomeIndicator true (sample member)) +
        ∑ cell, ∏ member, cellIndicator cell (sample member) := by
  have hprodScore : ∀ value : Bool, (∏ member, scoreIndicator value (sample member)) =
      if ∀ member, (sample member).1 = value then (1 : ℝ) else 0 := by
    intro value
    simp only [scoreIndicator]
    exact prod_member_indicator fun member ↦ (sample member).1 = value
  have hprodOutcome : ∀ value : Bool, (∏ member, outcomeIndicator value (sample member)) =
      if ∀ member, (sample member).2 = value then (1 : ℝ) else 0 := by
    intro value
    simp only [outcomeIndicator]
    exact prod_member_indicator fun member ↦ (sample member).2 = value
  have hprodCell : ∀ target : Bool × Bool, (∏ member, cellIndicator target (sample member)) =
      if ∀ member, sample member = target then (1 : ℝ) else 0 := by
    intro target
    simp only [cellIndicator]
    exact prod_member_indicator fun member ↦ sample member = target
  have hcellSplit : ∀ first second : Bool, (∀ member, sample member = (first, second)) ↔
      (∀ member, (sample member).1 = first) ∧ (∀ member, (sample member).2 = second) := by
    intro first second
    constructor
    · intro hall
      exact ⟨fun member ↦ by rw [hall member], fun member ↦ by rw [hall member]⟩
    · rintro ⟨hfirst, hsecond⟩ member
      exact Prod.ext_iff.mpr ⟨hfirst member, hsecond member⟩
  have hcellSum : (∑ cell, ∏ member, cellIndicator cell (sample member)) =
      ((if ∀ member, (sample member).1 = false then (1 : ℝ) else 0) +
          (if ∀ member, (sample member).1 = true then (1 : ℝ) else 0)) *
        ((if ∀ member, (sample member).2 = false then (1 : ℝ) else 0) +
          (if ∀ member, (sample member).2 = true then (1 : ℝ) else 0)) := by
    have hempty : (∀ _member : Fin n, False) ↔ False :=
      ⟨fun hall ↦ hall ⟨0, hn⟩, False.elim⟩
    simp only [hprodCell, hcellSplit, Fintype.sum_prod_type, Fintype.sum_bool]
    by_cases hzero : ∀ member, (sample member).1 = false <;>
      by_cases hone : ∀ member, (sample member).1 = true <;>
      by_cases htwo : ∀ member, (sample member).2 = false <;>
      by_cases hthree : ∀ member, (sample member).2 = true <;>
      simp [hzero, hone, htwo, hthree, hempty]
  have hscoreExclusive : ¬((∀ member, (sample member).1 = false) ∧
      ∀ member, (sample member).1 = true) := by
    rintro ⟨hfalse, htrue⟩
    exact Bool.false_ne_true ((hfalse ⟨0, hn⟩).symm.trans (htrue ⟨0, hn⟩))
  have houtcomeExclusive : ¬((∀ member, (sample member).2 = false) ∧
      ∀ member, (sample member).2 = true) := by
    rintro ⟨hfalse, htrue⟩
    exact Bool.false_ne_true ((hfalse ⟨0, hn⟩).symm.trans (htrue ⟨0, hn⟩))
  have hindicator : definedIndicator sample =
      if (¬ ∀ member, (sample member).1 = false) ∧ (¬ ∀ member, (sample member).1 = true) ∧
          (¬ ∀ member, (sample member).2 = false) ∧ (¬ ∀ member, (sample member).2 = true) then
        (1 : ℝ) else 0 := by
    unfold definedIndicator
    by_cases hd : Defined (cellCount sample (false, false)) (cellCount sample (false, true))
        (cellCount sample (true, false)) (cellCount sample (true, true))
    · rw [if_pos hd, if_pos ((defined_iff_not_constant sample).mp hd)]
    · rw [if_neg hd, if_neg fun hc ↦ hd ((defined_iff_not_constant sample).mpr hc)]
  rw [hindicator, hprodScore false, hprodScore true, hprodOutcome false, hprodOutcome true,
    hcellSum]
  exact inclusion_exclusion_two_pairs _ _ _ _ hscoreExclusive houtcomeExclusive

/-- NOTE1 (39): the exact probability that the empirical squared correlation of an independent
cohort of size `n` is defined. -/
theorem definedness_probability (law : FiniteReportLaw (Bool × Bool)) (n : ℕ) (hn : 0 < n) :
    (cohortLaw law n).expectation definedIndicator =
      1 - scoreMass law false ^ n - scoreMass law true ^ n - outcomeMass law false ^ n -
        outcomeMass law true ^ n + ∑ cell, law.mass cell ^ n := by
  have hstep : (∑ sample, (cohortLaw law n).mass sample * definedIndicator sample) =
      ∑ sample, ((cohortLaw law n).mass sample * 1 -
        (cohortLaw law n).mass sample * ∏ member, scoreIndicator false (sample member) -
        (cohortLaw law n).mass sample * ∏ member, scoreIndicator true (sample member) -
        (cohortLaw law n).mass sample * ∏ member, outcomeIndicator false (sample member) -
        (cohortLaw law n).mass sample * ∏ member, outcomeIndicator true (sample member) +
        (cohortLaw law n).mass sample *
          ∑ cell, ∏ member, cellIndicator cell (sample member)) := by
    refine Finset.sum_congr rfl fun sample _ ↦ ?_
    rw [definedIndicator_expand hn sample]
    ring
  have hone : (∑ sample : Fin n → Bool × Bool, (cohortLaw law n).mass sample * 1) = 1 := by
    simpa using (cohortLaw law n).mass_sum
  have hscoreFalse : (∑ sample, (cohortLaw law n).mass sample *
      ∏ member, scoreIndicator false (sample member)) = scoreMass law false ^ n := by
    have hprod := cohort_expectation_prod law n (scoreIndicator false)
    rw [expectation_scoreIndicator] at hprod
    exact hprod
  have hscoreTrue : (∑ sample, (cohortLaw law n).mass sample *
      ∏ member, scoreIndicator true (sample member)) = scoreMass law true ^ n := by
    have hprod := cohort_expectation_prod law n (scoreIndicator true)
    rw [expectation_scoreIndicator] at hprod
    exact hprod
  have houtcomeFalse : (∑ sample, (cohortLaw law n).mass sample *
      ∏ member, outcomeIndicator false (sample member)) = outcomeMass law false ^ n := by
    have hprod := cohort_expectation_prod law n (outcomeIndicator false)
    rw [expectation_outcomeIndicator] at hprod
    exact hprod
  have houtcomeTrue : (∑ sample, (cohortLaw law n).mass sample *
      ∏ member, outcomeIndicator true (sample member)) = outcomeMass law true ^ n := by
    have hprod := cohort_expectation_prod law n (outcomeIndicator true)
    rw [expectation_outcomeIndicator] at hprod
    exact hprod
  have hcells : (∑ sample, (cohortLaw law n).mass sample *
      ∑ cell, ∏ member, cellIndicator cell (sample member)) = ∑ cell, law.mass cell ^ n := by
    have hsum := FiniteIndependentMoments.expectation_sum (cohortLaw law n)
      fun (cell : Bool × Bool) (sample : Fin n → Bool × Bool) ↦
        ∏ member, cellIndicator cell (sample member)
    have hterm : ∀ cell : Bool × Bool, (cohortLaw law n).expectation
        (fun sample ↦ ∏ member, cellIndicator cell (sample member)) = law.mass cell ^ n := by
      intro cell
      rw [cohort_expectation_prod, expectation_cellIndicator]
    rw [Finset.sum_congr rfl fun cell _ ↦ hterm cell] at hsum
    exact hsum
  show (∑ sample, (cohortLaw law n).mass sample * definedIndicator sample) = _
  rw [hstep, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib,
    Finset.sum_sub_distrib, Finset.sum_sub_distrib, hone, hscoreFalse, hscoreTrue,
    houtcomeFalse, houtcomeTrue, hcells]

/-- NOTE1 (39) as displayed: when the score and outcome marginals agree, the definedness
probability is `1 − 2[pⁿ + (1−p)ⁿ] + Σ P_sy ⁿ`. -/
theorem definedness_probability_of_equal_marginals (law : FiniteReportLaw (Bool × Bool))
    (n : ℕ) (hn : 0 < n) (hmarginal : ∀ value : Bool, scoreMass law value = outcomeMass law value) :
    (cohortLaw law n).expectation definedIndicator =
      1 - 2 * (scoreMass law true ^ n + scoreMass law false ^ n) + ∑ cell, law.mass cell ^ n := by
  rw [definedness_probability law n hn, ← hmarginal false, ← hmarginal true]
  ring

end Descent.Portability.EmpiricalCorrelationDefinedness
