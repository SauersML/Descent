/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.SmallCohortCorrelation
import Descent.Portability.EmpiricalAUCUnbiasedness

assert_below Descent.Decision Descent.Program

/-!
# Small independent cohorts: conditional means of the empirical squared correlation

NOTE1 Corollary 7.1 gives the conditional mean of the empirical squared correlation of a small
independent cohort: `(5C² + 3)/(2(C² + 3))` at `n = 3` with both marginals at one half (41),
and, at `p = C = 1/2`, the values `1`, `17/26` and `419/809` at `n = 2, 3, 4`, beside a
conditional empirical AUC of `3/4` at all three sizes. `SmallCohortCorrelation` proves the
`n = 2` value and every definedness probability; this module proves the remaining conditional
means.

The route is an explicit census enumeration. `cohort_expectation_censusIndex` writes the
expectation of any census report of an independent cohort of size `n` as a finite sum, over the
census vectors indexed by their first three counts, of the multinomial mass times the report,
the mass in the `n!/(a! b! c! d!)` form of `FourCellCohortLaw.fourCell_census_mass`
(`multinomialLaw_mass_eq_censusWeight`). It is derived from
`FourCellCohortLaw.cohortReport_expectation` by reindexing the corpus count type along an
explicit bijection (`censusOf`), so no second counting argument is introduced. Evaluating
that sum at `n = 3` and `n = 4` gives the definedness-weighted empirical squared correlation
of an arbitrary four-cell law as an explicit polynomial in its four cell masses
(`expectation_cohortCorrelation_three`, `expectation_cohortCorrelation_four`); dividing
by the definedness probabilities of `SmallCohortCorrelation` at the chronology cells of NOTE1
(31) gives (41) and the tabulated values.

The module also removes the definedness premise from the chronology forms of NOTE1 (42) for
every cohort of at least two whenever `0 < p < 1`. `slope_definedness_probability` is the exact
probability `1 − P_S(1)ⁿ − P_S(0)ⁿ` that the cohort score varies, `constant_class_gap` shows
`1 − pⁿ − (1 − p)ⁿ > 0`, and `conditional_empiricalAUC_chronologyLaw_of_two_le` and
`conditional_empiricalSlope_chronologyLaw_of_two_le` state `(1 + C) / 2` and `C` with no
further premise. The tabulated conditional AUC `3/4` is the first of these at `p = C = 1/2`.

Not formalised here: closed forms for the conditional mean at `n ≥ 5`, or at `n = 3` away from
`p = 1/2`. The enumeration theorem holds for every `n`, and the `n = 3` and `n = 4` polynomials
hold for every four-cell law, but only those two sizes are evaluated.

## Empirical status

None. The bodies here are algebra: each value is a finite sum of multinomial masses times a
rational function of four counts, so no measurement on any cohort can bear on them.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.SmallCohortConditionalMeans

open FiniteReproductiveKernel FourCellCohortLaw EmpiricalCorrelationDefinedness
  ChronologyReportLaw SmallCohortCorrelation EmpiricalAUCUnbiasedness

/-- The two-by-two table with counts `(N₀₀, N₀₁, N₁₀, N₁₁) = (a, b, c, d)`, as a census on the
four cells of NOTE1 (31). -/
def tableCounts (a b c d : ℕ) : Bool × Bool → ℕ
  | (false, false) => a
  | (false, true) => b
  | (true, false) => c
  | (true, true) => d

/-- The census of a cohort of size `n` whose first three counts are `index`, the fourth count
filling the cohort. -/
def censusOf (n : ℕ) (index : ℕ × ℕ × ℕ) : Bool × Bool → ℕ :=
  tableCounts index.1 index.2.1 index.2.2 (n - index.1 - index.2.1 - index.2.2)

/-- The census vectors of a cohort of size `n`, indexed by their first three counts. -/
def censusIndex (n : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  (Finset.range (n + 1) ×ˢ Finset.range (n + 1) ×ˢ Finset.range (n + 1)).filter
    fun index ↦ index.1 + index.2.1 + index.2.2 ≤ n

/-- The total of a census on the four cells is the sum of its four counts. -/
theorem sum_census_cells (census : Bool × Bool → ℕ) :
    (∑ cell, census cell) =
      census (false, false) + census (false, true) + census (true, false) +
        census (true, true) := by
  simp only [Fintype.sum_prod_type, Fintype.sum_bool]
  ring

/-- A census of a cohort of size `n` is recovered from its first three counts. -/
theorem censusOf_counts (n : ℕ) (census : Bool × Bool → ℕ)
    (hcensus : census ∈ Finset.piAntidiag (Finset.univ : Finset (Bool × Bool)) n) :
    censusOf n (census (false, false), census (false, true), census (true, false)) = census := by
  have htotal := (Finset.mem_piAntidiag.mp hcensus).1
  rw [sum_census_cells] at htotal
  funext cell
  rcases cell with ⟨_ | _, _ | _⟩
  · rfl
  · rfl
  · rfl
  · show n - census (false, false) - census (false, true) - census (true, false) =
      census (true, true)
    omega

/-- The first three counts of a census of a cohort of size `n` lie in the index set. -/
theorem counts_mem_censusIndex (n : ℕ) (census : Bool × Bool → ℕ)
    (hcensus : census ∈ Finset.piAntidiag (Finset.univ : Finset (Bool × Bool)) n) :
    (census (false, false), census (false, true), census (true, false)) ∈ censusIndex n := by
  have htotal := (Finset.mem_piAntidiag.mp hcensus).1
  rw [sum_census_cells] at htotal
  simp only [censusIndex, Finset.mem_filter, Finset.mem_product, Finset.mem_range]
  omega

/-- Every index yields a census of a cohort of size `n`. -/
theorem censusOf_mem_piAntidiag (n : ℕ) (index : ℕ × ℕ × ℕ) (hindex : index ∈ censusIndex n) :
    censusOf n index ∈ Finset.piAntidiag (Finset.univ : Finset (Bool × Bool)) n := by
  simp only [censusIndex, Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hindex
  refine Finset.mem_piAntidiag.mpr ⟨?_, fun cell _ ↦ Finset.mem_univ cell⟩
  rw [sum_census_cells]
  show index.1 + index.2.1 + index.2.2 + (n - index.1 - index.2.1 - index.2.2) = n
  omega

/-- The census of an index reads back the index. -/
theorem censusOf_index (n : ℕ) (index : ℕ × ℕ × ℕ) :
    (censusOf n index (false, false), censusOf n index (false, true),
      censusOf n index (true, false)) = index := rfl

/-- The multinomial mass of a census of a cohort of size `n`, in the `n!/(a! b! c! d!)` form of
NOTE1 (37). -/
noncomputable def censusWeight (law : FiniteReportLaw (Bool × Bool)) (n : ℕ)
    (census : Bool × Bool → ℕ) : ℝ :=
  (Nat.factorial n : ℝ) /
      ((Nat.factorial (census (false, false)) : ℝ) * (Nat.factorial (census (false, true)) : ℝ) *
        (Nat.factorial (census (true, false)) : ℝ) * (Nat.factorial (census (true, true)) : ℝ)) *
    (law.mass (false, false) ^ census (false, false) *
      law.mass (false, true) ^ census (false, true) *
      law.mass (true, false) ^ census (true, false) * law.mass (true, true) ^ census (true, true))

/-- The census weight is the corpus multinomial mass of the census. -/
theorem multinomialLaw_mass_eq_censusWeight (law : FiniteReportLaw (Bool × Bool)) (n : ℕ)
    (census : Counts (Bool × Bool) n) :
    (multinomialLaw law n).mass census = censusWeight law n census.val :=
  fourCell_census_mass law n census

/-- NOTE1 (37) as an explicit finite sum: the expectation of a census report of an independent
cohort of size `n` is the multinomial-weighted sum of the report over the census vectors, each
indexed by its first three cell counts. -/
theorem cohort_expectation_censusIndex (law : FiniteReportLaw (Bool × Bool)) (n : ℕ)
    (report : (Bool × Bool → ℕ) → ℝ) :
    (cohortLaw law n).expectation (fun sample ↦ report (cellCount sample)) =
      ∑ index ∈ censusIndex n, censusWeight law n (censusOf n index) *
        report (censusOf n index) := by
  calc (cohortLaw law n).expectation (fun sample ↦ report (cellCount sample))
      = (multinomialLaw law n).expectation (fun census ↦ report census.val) :=
        cohortReport_expectation law n fun census ↦ report census.val
    _ = ∑ census : Counts (Bool × Bool) n, censusWeight law n census.val * report census.val :=
        Finset.sum_congr rfl fun census _ ↦ by
          simp only [multinomialLaw_mass_eq_censusWeight]
    _ = ∑ census ∈ Finset.piAntidiag (Finset.univ : Finset (Bool × Bool)) n,
          censusWeight law n census * report census :=
        Finset.sum_coe_sort (Finset.piAntidiag Finset.univ n) fun census ↦
          censusWeight law n census * report census
    _ = _ :=
        Finset.sum_nbij'
          (fun census ↦ (census (false, false), census (false, true), census (true, false)))
          (censusOf n) (counts_mem_censusIndex n) (censusOf_mem_piAntidiag n)
          (censusOf_counts n) (fun index _ ↦ censusOf_index n index)
          fun census hcensus ↦ by rw [censusOf_counts n census hcensus]

/-- The definedness-weighted empirical squared correlation read off a census. -/
noncomputable def censusCorrelation (census : Bool × Bool → ℕ) : ℝ :=
  empiricalR2 (census (false, false)) (census (false, true)) (census (true, false))
      (census (true, true)) *
    if Defined (census (false, false)) (census (false, true)) (census (true, false))
        (census (true, true)) then 1 else 0

/-- The definedness-weighted empirical squared correlation of a cohort reads only its
census. -/
theorem cohortCorrelation_mul_definedIndicator_eq {n : ℕ} (sample : Fin n → Bool × Bool) :
    cohortCorrelation sample * definedIndicator sample = censusCorrelation (cellCount sample) :=
  rfl

/-- The census polynomial of the definedness-weighted empirical squared correlation of a cohort
of three, in the cell masses `w, x, y, z = P₀₀, P₀₁, P₁₀, P₁₁`. -/
noncomputable def cohortCorrelationThree (w x y z : ℝ) : ℝ :=
  3 * w * z * (w + z) + 3 * x * y * (x + y) +
    3 / 2 * (w * x * z + w * y * z + w * x * y + x * y * z)

/-- The census polynomial of the definedness-weighted empirical squared correlation of a cohort
of four, in the cell masses `w, x, y, z = P₀₀, P₀₁, P₁₀, P₁₁`. -/
noncomputable def cohortCorrelationFour (w x y z : ℝ) : ℝ :=
  6 * (w ^ 2 * z ^ 2 + x ^ 2 * y ^ 2) + 4 * (w ^ 3 * z + w * z ^ 3 + x ^ 3 * y + x * y ^ 3) +
    4 * (w ^ 2 * y * z + w ^ 2 * x * z + w * y * z ^ 2 + w * x * z ^ 2) +
    4 * (x ^ 2 * y * z + x * y ^ 2 * z + w * x ^ 2 * y + w * x * y ^ 2) +
    4 / 3 * (w ^ 2 * x * y + w * y ^ 2 * z + w * x ^ 2 * z + x * y * z ^ 2)

/-- The definedness-weighted empirical squared correlation of an independent cohort of three,
for every four-cell law: the numerator of NOTE1 (41) before the cells are specialised. -/
theorem expectation_cohortCorrelation_three (law : FiniteReportLaw (Bool × Bool)) :
    (cohortLaw law 3).expectation
        (fun sample ↦ cohortCorrelation sample * definedIndicator sample) =
      cohortCorrelationThree (law.mass (false, false)) (law.mass (false, true))
        (law.mass (true, false)) (law.mass (true, true)) := by
  have hcensus : (cohortLaw law 3).expectation
      (fun sample ↦ cohortCorrelation sample * definedIndicator sample) =
      (cohortLaw law 3).expectation (fun sample ↦ censusCorrelation (cellCount sample)) := rfl
  rw [hcensus, cohort_expectation_censusIndex]
  simp only [censusIndex, Finset.sum_filter, Finset.sum_product, Finset.sum_range_succ,
    Finset.sum_range_zero, censusOf, tableCounts, censusWeight, censusCorrelation]
  norm_num [empiricalR2, Defined, Nat.factorial, cohortCorrelationThree]
  ring

/-- The definedness-weighted empirical squared correlation of an independent cohort of four,
for every four-cell law. -/
theorem expectation_cohortCorrelation_four (law : FiniteReportLaw (Bool × Bool)) :
    (cohortLaw law 4).expectation
        (fun sample ↦ cohortCorrelation sample * definedIndicator sample) =
      cohortCorrelationFour (law.mass (false, false)) (law.mass (false, true))
        (law.mass (true, false)) (law.mass (true, true)) := by
  have hcensus : (cohortLaw law 4).expectation
      (fun sample ↦ cohortCorrelation sample * definedIndicator sample) =
      (cohortLaw law 4).expectation (fun sample ↦ censusCorrelation (cellCount sample)) := rfl
  rw [hcensus, cohort_expectation_censusIndex]
  simp only [censusIndex, Finset.sum_filter, Finset.sum_product, Finset.sum_range_succ,
    Finset.sum_range_zero, censusOf, tableCounts, censusWeight, censusCorrelation]
  norm_num [empiricalR2, Defined, Nat.factorial, cohortCorrelationFour]
  ring

/-- The numerator of NOTE1 (41): at `p = 1/2` the definedness-weighted empirical squared
correlation of an independent cohort of three has expectation `3(5C² + 3)/32`. -/
theorem expectation_cohortCorrelation_three_half (C : ℝ) (hC0 : 0 ≤ C) (hC1 : C ≤ 1) :
    (cohortLaw (chronologyLaw (1 / 2) C (by norm_num) (by norm_num) hC0 hC1) 3).expectation
        (fun sample ↦ cohortCorrelation sample * definedIndicator sample) =
      3 * (5 * C ^ 2 + 3) / 32 := by
  rw [expectation_cohortCorrelation_three]
  simp only [chronologyLaw_mass, chronologyMass_false_false, chronologyMass_false_true,
    chronologyMass_true_false, chronologyMass_true_true, cohortCorrelationThree]
  ring

/-- NOTE1 (41): at `p = 1/2`, conditional on being defined, the empirical squared correlation of
an independent cohort of three has expectation `(5C² + 3)/(2(C² + 3))`. -/
theorem conditional_cohortCorrelation_three_half (C : ℝ) (hC0 : 0 ≤ C) (hC1 : C ≤ 1) :
    (cohortLaw (chronologyLaw (1 / 2) C (by norm_num) (by norm_num) hC0 hC1) 3).expectation
          (fun sample ↦ cohortCorrelation sample * definedIndicator sample) /
        (cohortLaw (chronologyLaw (1 / 2) C (by norm_num) (by norm_num) hC0 hC1) 3).expectation
          definedIndicator =
      (5 * C ^ 2 + 3) / (2 * (C ^ 2 + 3)) := by
  have hdefined : (3 * (C ^ 2 + 3) / 16 : ℝ) ≠ 0 := by positivity
  have htarget : (2 * (C ^ 2 + 3) : ℝ) ≠ 0 := by positivity
  rw [expectation_cohortCorrelation_three_half C hC0 hC1, definedness_probability_half C hC0 hC1,
    div_eq_div_iff hdefined htarget]
  ring

/-- The NOTE1 section 7 table at `p = C = 1/2`, `n = 3`: conditional on being defined, the
empirical squared correlation has expectation `17/26`, against a population value of `1/4`. -/
theorem conditional_cohortCorrelation_halvedCoupling_three :
    (cohortLaw halvedCouplingLaw 3).expectation
          (fun sample ↦ cohortCorrelation sample * definedIndicator sample) /
        (cohortLaw halvedCouplingLaw 3).expectation definedIndicator = 17 / 26 := by
  unfold halvedCouplingLaw
  rw [conditional_cohortCorrelation_three_half (1 / 2) (by norm_num) (by norm_num)]
  norm_num

/-- At `p = C = 1/2` the definedness-weighted empirical squared correlation of an independent
cohort of four has expectation `419/1024`. -/
theorem expectation_cohortCorrelation_halvedCoupling_four :
    (cohortLaw halvedCouplingLaw 4).expectation
        (fun sample ↦ cohortCorrelation sample * definedIndicator sample) = 419 / 1024 := by
  rw [expectation_cohortCorrelation_four]
  simp only [halvedCouplingLaw, chronologyLaw_mass, chronologyMass_false_false,
    chronologyMass_false_true, chronologyMass_true_false, chronologyMass_true_true,
    cohortCorrelationFour]
  norm_num

/-- The NOTE1 section 7 table at `p = C = 1/2`, `n = 4`: conditional on being defined, the
empirical squared correlation has expectation `419/809`. -/
theorem conditional_cohortCorrelation_halvedCoupling_four :
    (cohortLaw halvedCouplingLaw 4).expectation
          (fun sample ↦ cohortCorrelation sample * definedIndicator sample) /
        (cohortLaw halvedCouplingLaw 4).expectation definedIndicator = 419 / 809 := by
  rw [expectation_cohortCorrelation_halvedCoupling_four,
    definedness_probability_halvedCoupling.2.2]
  norm_num

/-- For `0 < p < 1` and a cohort of at least two, the two constant-class probabilities `pⁿ` and
`(1 − p)ⁿ` leave positive mass. -/
theorem constant_class_gap (p : ℝ) (hlow : 0 < p) (hhigh : p < 1) (n : ℕ) (hn : 2 ≤ n) :
    0 < 1 - p ^ n - (1 - p) ^ n := by
  have hfirst : p ^ n ≤ p ^ 2 := pow_le_pow_of_le_one hlow.le hhigh.le hn
  have hsecond : (1 - p) ^ n ≤ (1 - p) ^ 2 :=
    pow_le_pow_of_le_one (by linarith) (by linarith) hn
  nlinarith [mul_pos hlow (sub_pos.mpr hhigh)]

/-- NOTE1 (42) for the chronology cells: the empirical AUC of a cohort of at least two is defined
with positive probability whenever `0 < p < 1`. -/
theorem aucDefinedIndicator_pos_chronologyLaw (p C : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hC0 : 0 ≤ C) (hC1 : C ≤ 1) (hlow : 0 < p) (hhigh : p < 1) (n : ℕ) (hn : 2 ≤ n) :
    0 < (cohortLaw (chronologyLaw p C hp0 hp1 hC0 hC1) n).expectation aucDefinedIndicator := by
  rw [auc_definedness_probability_chronologyLaw p C hp0 hp1 hC0 hC1 n (by omega)]
  exact constant_class_gap p hlow hhigh n hn

/-- NOTE1 (42) for the chronology cells with no definedness premise: for every cohort of at
least two, conditional on being defined, the empirical AUC has expectation `(1 + C) / 2`. -/
theorem conditional_empiricalAUC_chronologyLaw_of_two_le (p C : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hC0 : 0 ≤ C) (hC1 : C ≤ 1) (hlow : 0 < p) (hhigh : p < 1) (n : ℕ) (hn : 2 ≤ n) :
    (cohortLaw (chronologyLaw p C hp0 hp1 hC0 hC1) n).expectation
          (fun sample ↦ empiricalAUC sample * aucDefinedIndicator sample) /
        (cohortLaw (chronologyLaw p C hp0 hp1 hC0 hC1) n).expectation aucDefinedIndicator =
      (1 + C) / 2 :=
  conditional_empiricalAUC_chronologyLaw p C hp0 hp1 hC0 hC1 hlow hhigh n
    (aucDefinedIndicator_pos_chronologyLaw p C hp0 hp1 hC0 hC1 hlow hhigh n hn)

/-- The slope definedness indicator of a cohort splits into the two constant-score indicators:
it is the AUC definedness indicator of the cohort with score and outcome exchanged. -/
theorem slopeDefinedIndicator_expand {n : ℕ} (hn : 0 < n) (sample : Fin n → Bool × Bool) :
    slopeDefinedIndicator sample =
      1 - (∏ member, scoreIndicator false (sample member)) -
        ∏ member, scoreIndicator true (sample member) :=
  aucDefinedIndicator_expand hn fun member ↦ ((sample member).2, (sample member).1)

/-- NOTE1 (42): the exact probability that the empirical least-squares slope of an independent
cohort of size `n` is defined, that is, that the cohort score varies. -/
theorem slope_definedness_probability (law : FiniteReportLaw (Bool × Bool)) (n : ℕ)
    (hn : 0 < n) :
    (cohortLaw law n).expectation slopeDefinedIndicator =
      1 - scoreMass law true ^ n - scoreMass law false ^ n := by
  have hstep : (∑ sample, (cohortLaw law n).mass sample * slopeDefinedIndicator sample) =
      ∑ sample, ((cohortLaw law n).mass sample * 1 -
        (cohortLaw law n).mass sample * ∏ member, scoreIndicator true (sample member) -
        (cohortLaw law n).mass sample * ∏ member, scoreIndicator false (sample member)) := by
    refine Finset.sum_congr rfl fun sample _ ↦ ?_
    rw [slopeDefinedIndicator_expand hn sample]
    ring
  have hone : (∑ sample : Fin n → Bool × Bool, (cohortLaw law n).mass sample * 1) = 1 := by
    simpa using (cohortLaw law n).mass_sum
  show (∑ sample, (cohortLaw law n).mass sample * slopeDefinedIndicator sample) = _
  rw [hstep, Finset.sum_sub_distrib, Finset.sum_sub_distrib, hone,
    sum_mass_all_score law n true, sum_mass_all_score law n false]

/-- NOTE1 (42) for the chronology cells: the empirical slope of a cohort of size `n` is defined
with probability `1 − pⁿ − (1 − p)ⁿ`. -/
theorem slope_definedness_probability_chronologyLaw (p C : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hC0 : 0 ≤ C) (hC1 : C ≤ 1) (n : ℕ) (hn : 0 < n) :
    (cohortLaw (chronologyLaw p C hp0 hp1 hC0 hC1) n).expectation slopeDefinedIndicator =
      1 - p ^ n - (1 - p) ^ n := by
  obtain ⟨hdonor, hrecipient⟩ := scoreMass_chronologyLaw p C hp0 hp1 hC0 hC1
  rw [slope_definedness_probability _ n hn, hdonor, hrecipient]

/-- NOTE1 (42) for the chronology cells with no definedness premise: for every cohort of at
least two, conditional on the score varying, the empirical slope has expectation `C`. -/
theorem conditional_empiricalSlope_chronologyLaw_of_two_le (p C : ℝ) (hp0 : 0 ≤ p)
    (hp1 : p ≤ 1) (hC0 : 0 ≤ C) (hC1 : C ≤ 1) (hlow : 0 < p) (hhigh : p < 1) (n : ℕ)
    (hn : 2 ≤ n) :
    (cohortLaw (chronologyLaw p C hp0 hp1 hC0 hC1) n).expectation
          (fun sample ↦ empiricalSlope sample * slopeDefinedIndicator sample) /
        (cohortLaw (chronologyLaw p C hp0 hp1 hC0 hC1) n).expectation
          slopeDefinedIndicator = C := by
  have hdefined : 0 < (cohortLaw (chronologyLaw p C hp0 hp1 hC0 hC1) n).expectation
      slopeDefinedIndicator := by
    rw [slope_definedness_probability_chronologyLaw p C hp0 hp1 hC0 hC1 n (by omega)]
    exact constant_class_gap p hlow hhigh n hn
  exact conditional_empiricalSlope_chronologyLaw p C hp0 hp1 hC0 hC1 hlow hhigh n hdefined

/-- The NOTE1 section 7 table at `p = C = 1/2`: for every cohort of at least two, conditional on
being defined, the empirical AUC has expectation `3/4`, equal to the population AUC. -/
theorem conditional_empiricalAUC_halvedCoupling (n : ℕ) (hn : 2 ≤ n) :
    (cohortLaw halvedCouplingLaw n).expectation
          (fun sample ↦ empiricalAUC sample * aucDefinedIndicator sample) /
        (cohortLaw halvedCouplingLaw n).expectation aucDefinedIndicator = 3 / 4 := by
  unfold halvedCouplingLaw
  rw [conditional_empiricalAUC_chronologyLaw_of_two_le (1 / 2) (1 / 2) _ _ _ _ (by norm_num)
    (by norm_num) n hn]
  norm_num

end Descent.Portability.SmallCohortConditionalMeans
