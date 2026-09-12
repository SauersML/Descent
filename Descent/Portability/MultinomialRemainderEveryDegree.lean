/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.MultinomialJetCertificate

assert_below Descent.Decision Descent.Program

/-!
# The multinomial expansion (10) at every fixed degree

NOTE1 (10) expands the expected polynomial of multinomial census proportions,
`E f(Z/N) = f(x) + (1/2N) Σ (x_a δ_ab - x_a x_b) ∂_ab f(x) + O(N⁻²)`, for `f` of degree at most
four, and NOTE1 §4.2a says the same expansion "has an O(N⁻²) remainder at every fixed finite
degree, not only at degree four". `MultinomialMomentExpansion` proves the degree-four case, where
its two descending-factorial bounds are checked degree by degree. This module removes the degree
restriction.

The descending factorial ratio `r_B = (N)_B / N^B` obeys `r_{B+1} = r_B (1 - B/N)`
(`descFactorial_div_pow_succ`), and induction on `B` gives the second-order Bonferroni bounds
`1 - s ≤ r_B ≤ 1 - s + s²/2` with `s = C(B, 2)/N`, for every `B` and every `N ≥ 1`
(`descFactorial_div_pow_bounds`); past `B > N` the ratio vanishes and the bounds still hold. So
`|r_B - 1 + C(B, 2)/N| ≤ C(B, 2)²/2 / N²` (`abs_descFactorial_div_pow_sub_le_choose_sq`), and
the subleading ratio `(N)_{B-1}/N^B` is `1/N` to within `C(B - 1, 2)/N²`
(`abs_descFactorial_pred_div_pow_sub_le_choose`). The monomial argument of
`MultinomialMomentExpansion` then goes through at every degree
(`abs_expectation_monomial_sub_le_every`), and so does the polynomial one
(`abs_expectation_eval_sub_le_every`), with no hypothesis on the degree: each monomial `s`
contributes `C(|s|, 2)²/2 + (C(|s| - 1, 2) + 1) · totalStirlingWeight s` to the remainder
constant.

A constant depending on the degree alone follows from a Bell bound. The Bell numbers satisfy
`B(k) ≤ k!` at every order (`sum_stirlingSecond_le_factorial`), so the total Stirling weight of a
multi-index is at most the factorial of its degree (`totalStirlingWeight_le_factorial`). For
every polynomial of total degree at most `d`, (10) holds with remainder
`(C(d, 2)²/2 + (C(d - 1, 2) + 1) · d!) · coefficientMass f / N²`, uniformly over the category law
(`abs_expectation_eval_sub_le_of_totalDegree_le`).

Scope. The constants are the ones this proof yields. At degree four they are weaker than the
constant `71` of `MultinomialRemainderConstant`, which uses the exact degree-four ratios.

## Empirical status

None. The bodies here are finite combinatorics and inequalities between descending factorials,
Stirling numbers and powers, so no measurement can bear on them.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.MultinomialRemainderEveryDegree

open FiniteReproductiveKernel MultinomialMomentExpansion MultinomialJetCertificate

/-! ## The descending factorial ratio at every degree -/

/-- **One step of the descending factorial ratio.**
`(N)_{B+1} / N^{B+1} = (N)_B / N^B · (1 - B/N)`. -/
theorem descFactorial_div_pow_succ (N B : ℕ) (hN : 1 ≤ N) :
    (N.descFactorial (B + 1) : ℝ) / (N : ℝ) ^ (B + 1)
      = (N.descFactorial B : ℝ) / (N : ℝ) ^ B * (1 - (B : ℝ) / N) := by
  have hNne : (N : ℝ) ≠ 0 := by
    have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
    exact hNpos.ne'
  rw [cast_descFactorial_succ, pow_succ, one_sub_div hNne, div_mul_div_comm,
    mul_comm ((N : ℝ) - B)]

/-- **Second-order Bonferroni bounds for the descending factorial ratio.** For every `N ≥ 1` and
every `B`, with `s = C(B, 2) / N`, `1 - s ≤ (N)_B / N^B ≤ 1 - s + s² / 2`. -/
theorem descFactorial_div_pow_bounds (N : ℕ) (hN : 1 ≤ N) (B : ℕ) :
    1 - (B.choose 2 : ℝ) / N ≤ (N.descFactorial B : ℝ) / (N : ℝ) ^ B ∧
      (N.descFactorial B : ℝ) / (N : ℝ) ^ B
        ≤ 1 - (B.choose 2 : ℝ) / N + ((B.choose 2 : ℝ) / N) ^ 2 / 2 := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  induction B with
  | zero => simp [Nat.choose]
  | succ B ih =>
    obtain ⟨hlow, hhigh⟩ := ih
    have hr0 : 0 ≤ (N.descFactorial B : ℝ) / (N : ℝ) ^ B := by positivity
    have hr1 : (N.descFactorial B : ℝ) / (N : ℝ) ^ B ≤ 1 := by
      rw [div_le_one (by positivity)]
      exact_mod_cast Nat.descFactorial_le_pow N B
    have hchoose : (((B + 1).choose 2 : ℕ) : ℝ) = (B.choose 2 : ℝ) + B := by
      have h : (B + 1).choose 2 = B.choose 2 + B := by
        rw [Nat.choose_succ_succ', Nat.choose_one_right, add_comm]
      exact_mod_cast h
    have hS : 0 ≤ (B.choose 2 : ℝ) / N := by positivity
    have hu : 0 ≤ (B : ℝ) / N := by positivity
    rw [descFactorial_div_pow_succ N B hN, hchoose, add_div]
    by_cases hu1 : (B : ℝ) / N ≤ 1
    · have hmul_low := mul_le_mul_of_nonneg_right hlow (sub_nonneg.mpr hu1)
      have hmul_high := mul_le_mul_of_nonneg_right hhigh (sub_nonneg.mpr hu1)
      constructor
      · nlinarith [mul_nonneg hS hu]
      · nlinarith [mul_nonneg hu (sq_nonneg ((B.choose 2 : ℝ) / N)), sq_nonneg ((B : ℝ) / N)]
    · have hneg : (1 : ℝ) - B / N < 0 := by linarith
      constructor
      · nlinarith [mul_nonneg (sub_nonneg.mpr hr1) (le_of_lt (neg_pos.mpr hneg))]
      · nlinarith [mul_nonneg hr0 (le_of_lt (neg_pos.mpr hneg)),
          sq_nonneg ((B.choose 2 : ℝ) / N + B / N - 1)]

/-- **The leading descending factorial ratio at every degree.** For every `N ≥ 1` and every `B`,
`(N)_B / N^B` is `1 - C(B, 2)/N` to within `C(B, 2)² / 2 / N²`. -/
theorem abs_descFactorial_div_pow_sub_le_choose_sq (N B : ℕ) (hN : 1 ≤ N) :
    |(N.descFactorial B : ℝ) / (N : ℝ) ^ B - 1 + (B.choose 2 : ℝ) / N|
      ≤ (B.choose 2 : ℝ) ^ 2 / 2 / (N : ℝ) ^ 2 := by
  obtain ⟨hlow, hhigh⟩ := descFactorial_div_pow_bounds N hN B
  have hform : ((B.choose 2 : ℝ) / N) ^ 2 / 2 = (B.choose 2 : ℝ) ^ 2 / 2 / (N : ℝ) ^ 2 := by
    rw [div_pow]
    ring
  have hnonneg : 0 ≤ (B.choose 2 : ℝ) ^ 2 / 2 / (N : ℝ) ^ 2 := by positivity
  rw [abs_le]
  constructor <;> linarith

/-- **The subleading descending factorial ratio at every degree.** For `N ≥ 1` and `B ≥ 1`,
`(N)_{B-1} / N^B` is `1/N` to within `C(B - 1, 2) / N²`. -/
theorem abs_descFactorial_pred_div_pow_sub_le_choose (N B : ℕ) (hN : 1 ≤ N) (hB1 : 1 ≤ B) :
    |(N.descFactorial (B - 1) : ℝ) / (N : ℝ) ^ B - 1 / N|
      ≤ ((B - 1).choose 2 : ℝ) / (N : ℝ) ^ 2 := by
  obtain ⟨k, rfl⟩ : ∃ k, B = k + 1 := ⟨B - 1, by omega⟩
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  rw [Nat.add_sub_cancel]
  obtain ⟨hlow, -⟩ := descFactorial_div_pow_bounds N hN k
  have hr1 : (N.descFactorial k : ℝ) / (N : ℝ) ^ k ≤ 1 := by
    rw [div_le_one (by positivity)]
    exact_mod_cast Nat.descFactorial_le_pow N k
  have hS : 0 ≤ (k.choose 2 : ℝ) / N := by positivity
  have habs : |(N.descFactorial k : ℝ) / (N : ℝ) ^ k - 1| ≤ (k.choose 2 : ℝ) / N := by
    rw [abs_le]
    constructor <;> linarith
  have hsplit : (N.descFactorial k : ℝ) / (N : ℝ) ^ (k + 1) - 1 / N
      = ((N.descFactorial k : ℝ) / (N : ℝ) ^ k - 1) / N := by
    rw [pow_succ, div_mul_eq_div_div, sub_div]
  have hstep : (k.choose 2 : ℝ) / N / N = (k.choose 2 : ℝ) / (N : ℝ) ^ 2 := by
    rw [div_div, pow_two]
  rw [hsplit, abs_div, abs_of_pos hNpos, ← hstep]
  exact div_le_div_of_nonneg_right habs hNpos.le

/-! ## The expansion (10) for monomials and polynomials of every degree -/

/-- **NOTE1 (10) for monomials of every degree.** Under the multinomial census with `N ≥ 1`
draws from the category law `x`, the expected monomial of the census proportions is
`x ^ b + monomialFirstOrder x b / N` up to
`(C(|b|, 2)² / 2 + (C(|b| - 1, 2) + 1) · totalStirlingWeight b) / N²`, uniformly in `x`. -/
theorem abs_expectation_monomial_sub_le_every {H : Type*} [Fintype H] [DecidableEq H]
    (offspring : FiniteReportLaw H) (N : ℕ) (hN : 1 ≤ N) (b : H → ℕ) :
    |(multinomialLaw offspring N).expectation
          (fun counts ↦ ∏ a, ((counts.val a : ℝ) / N) ^ b a)
        - ∏ a, offspring.mass a ^ b a - monomialFirstOrder offspring.mass b / N|
      ≤ (((∑ a, b a).choose 2 : ℝ) ^ 2 / 2
          + (((∑ a, b a - 1).choose 2 : ℝ) + 1) * totalStirlingWeight b) / (N : ℝ) ^ 2 := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hm0 := categoryMonomial_nonneg offspring b
  have hm1 := categoryMonomial_le_one offspring b
  have hF0 := firstOrderStirlingSum_nonneg offspring b
  have hF1 := firstOrderStirlingSum_le offspring b
  have hG0 := lowOrderStirlingSum_nonneg offspring N b
  have hG1 := lowOrderStirlingSum_mul_sq_le offspring N hN b
  have hT1 := abs_descFactorial_div_pow_sub_le_choose_sq N (∑ a, b a) hN
  have hT2 : |(N.descFactorial (∑ a, b a - 1) : ℝ) / (N : ℝ) ^ (∑ a, b a) - 1 / N|
        * firstOrderStirlingSum offspring.mass b
      ≤ ((∑ a, b a - 1).choose 2 : ℝ) / (N : ℝ) ^ 2 * totalStirlingWeight b := by
    by_cases hB0 : ∑ a, b a = 0
    · rw [firstOrderStirlingSum_of_sum_eq_zero offspring.mass b hB0, mul_zero]
      exact mul_nonneg (by positivity) (hF0.trans hF1)
    · exact mul_le_mul (abs_descFactorial_pred_div_pow_sub_le_choose N _ hN
        (Nat.one_le_iff_ne_zero.mpr hB0)) hF1 hF0 (by positivity)
  have hG : lowOrderStirlingSum offspring.mass N b / (N : ℝ) ^ (∑ a, b a)
      ≤ totalStirlingWeight b / (N : ℝ) ^ 2 := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    exact hG1
  have hidentity : (multinomialLaw offspring N).expectation
          (fun counts ↦ ∏ a, ((counts.val a : ℝ) / N) ^ b a)
        - ∏ a, offspring.mass a ^ b a - monomialFirstOrder offspring.mass b / N
      = ((N.descFactorial (∑ a, b a) : ℝ) / (N : ℝ) ^ (∑ a, b a) - 1
            + ((∑ a, b a).choose 2 : ℝ) / N) * ∏ a, offspring.mass a ^ b a
        + ((N.descFactorial (∑ a, b a - 1) : ℝ) / (N : ℝ) ^ (∑ a, b a) - 1 / N)
            * firstOrderStirlingSum offspring.mass b
        + lowOrderStirlingSum offspring.mass N b / (N : ℝ) ^ (∑ a, b a) := by
    rw [expectation_monomial_eq, sum_subIndices_split, monomialFirstOrder]
    ring
  rw [hidentity]
  refine (abs_add_le _ _).trans ?_
  refine (add_le_add_right (abs_add_le _ _) _).trans ?_
  rw [abs_mul, abs_mul, abs_of_nonneg hm0, abs_of_nonneg hF0,
    abs_of_nonneg (div_nonneg hG0 (by positivity))]
  calc |(N.descFactorial (∑ a, b a) : ℝ) / (N : ℝ) ^ (∑ a, b a) - 1
          + ((∑ a, b a).choose 2 : ℝ) / N| * ∏ a, offspring.mass a ^ b a
        + |(N.descFactorial (∑ a, b a - 1) : ℝ) / (N : ℝ) ^ (∑ a, b a) - 1 / N|
          * firstOrderStirlingSum offspring.mass b
        + lowOrderStirlingSum offspring.mass N b / (N : ℝ) ^ (∑ a, b a)
      ≤ ((∑ a, b a).choose 2 : ℝ) ^ 2 / 2 / (N : ℝ) ^ 2 * 1
          + ((∑ a, b a - 1).choose 2 : ℝ) / (N : ℝ) ^ 2 * totalStirlingWeight b
          + totalStirlingWeight b / (N : ℝ) ^ 2 :=
        add_le_add (add_le_add (mul_le_mul hT1 hm1 hm0 (by positivity)) hT2) hG
    _ = (((∑ a, b a).choose 2 : ℝ) ^ 2 / 2
          + (((∑ a, b a - 1).choose 2 : ℝ) + 1) * totalStirlingWeight b) / (N : ℝ) ^ 2 := by
        ring

/-- **NOTE1 (10) for every polynomial, degree by degree.** Under the multinomial census with
`N ≥ 1` draws from the category law `x`, the expected value of a polynomial `f` at the census
proportions is `f(x) + resamplingOperator x f / N`, up to
`Σ_s |f_s| (C(|s|, 2)²/2 + (C(|s| - 1, 2) + 1) totalStirlingWeight s) / N²`, uniformly in `x`,
with no hypothesis on the degree of `f`. -/
theorem abs_expectation_eval_sub_le_every {H : Type*} [Fintype H] [DecidableEq H]
    (offspring : FiniteReportLaw H) (N : ℕ) (hN : 1 ≤ N) (f : MvPolynomial H ℝ) :
    |(multinomialLaw offspring N).expectation
          (fun counts ↦ MvPolynomial.eval (fun a ↦ (counts.val a : ℝ) / N) f)
        - MvPolynomial.eval offspring.mass f - resamplingOperator offspring.mass f / N|
      ≤ (∑ s ∈ f.support, |f.coeff s| * (((∑ a, s a).choose 2 : ℝ) ^ 2 / 2
          + (((∑ a, s a - 1).choose 2 : ℝ) + 1) * totalStirlingWeight ⇑s)) / (N : ℝ) ^ 2 := by
  have hsum : (multinomialLaw offspring N).expectation
          (fun counts ↦ MvPolynomial.eval (fun a ↦ (counts.val a : ℝ) / N) f)
        - MvPolynomial.eval offspring.mass f - resamplingOperator offspring.mass f / N
      = ∑ s ∈ f.support, (f.coeff s * (multinomialLaw offspring N).expectation
            (fun counts ↦ ∏ a, ((counts.val a : ℝ) / N) ^ s a)
          - f.coeff s * ∏ a, offspring.mass a ^ s a
          - f.coeff s * monomialFirstOrder offspring.mass ⇑s / N) := by
    rw [expectation_eval_eq_sum_coeff, MvPolynomial.eval_eq', resamplingOperator_eq_sum_coeff,
      Finset.sum_div, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  rw [hsum, Finset.sum_div]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun s _ ↦ ?_)
  have hbound := abs_expectation_monomial_sub_le_every offspring N hN ⇑s
  have hfactor : f.coeff s * (multinomialLaw offspring N).expectation
          (fun counts ↦ ∏ a, ((counts.val a : ℝ) / N) ^ s a)
        - f.coeff s * ∏ a, offspring.mass a ^ s a
        - f.coeff s * monomialFirstOrder offspring.mass ⇑s / N
      = f.coeff s * ((multinomialLaw offspring N).expectation
          (fun counts ↦ ∏ a, ((counts.val a : ℝ) / N) ^ s a)
        - ∏ a, offspring.mass a ^ s a - monomialFirstOrder offspring.mass ⇑s / N) := by
    ring
  rw [hfactor, abs_mul, mul_div_assoc]
  exact mul_le_mul_of_nonneg_left hbound (abs_nonneg _)

/-! ## A remainder constant depending on the degree alone -/

/-- **The Bell bound.** The Bell number `B(k) = Σ_{i ≤ k} S(k, i)` is at most `k!`: the
recurrence `S(k + 1, i + 1) = (i + 1) S(k, i + 1) + S(k, i)` gives `B(k + 1) ≤ (k + 1) B(k)`. -/
theorem sum_stirlingSecond_le_factorial (k : ℕ) :
    ∑ i ∈ Finset.range (k + 1), Nat.stirlingSecond k i ≤ k.factorial := by
  induction k with
  | zero => simp [Nat.stirlingSecond]
  | succ k ih =>
    have hshift : ∑ i ∈ Finset.range (k + 1), Nat.stirlingSecond k (i + 1)
        ≤ ∑ i ∈ Finset.range (k + 1), Nat.stirlingSecond k i := by
      have h1 : ∑ i ∈ Finset.range (k + 1 + 1), Nat.stirlingSecond k i
          = ∑ i ∈ Finset.range (k + 1), Nat.stirlingSecond k (i + 1)
            + Nat.stirlingSecond k 0 :=
        Finset.sum_range_succ' _ _
      have h2 : ∑ i ∈ Finset.range (k + 1 + 1), Nat.stirlingSecond k i
          = ∑ i ∈ Finset.range (k + 1), Nat.stirlingSecond k i
            + Nat.stirlingSecond k (k + 1) :=
        Finset.sum_range_succ _ _
      rw [Nat.stirlingSecond_eq_zero_of_lt (by omega : k < k + 1), add_zero] at h2
      omega
    have hterm : ∀ i ∈ Finset.range (k + 1),
        (i + 1) * Nat.stirlingSecond k (i + 1) ≤ k * Nat.stirlingSecond k (i + 1) := by
      intro i _
      by_cases hi : i + 1 ≤ k
      · exact Nat.mul_le_mul_right _ hi
      · rw [Nat.stirlingSecond_eq_zero_of_lt (by omega), mul_zero, mul_zero]
    have h0 : Nat.stirlingSecond (k + 1) 0 = 0 := Nat.stirlingSecond_succ_zero k
    rw [Finset.sum_range_succ', h0, add_zero]
    simp only [Nat.stirlingSecond_succ_succ]
    rw [Finset.sum_add_distrib, Nat.factorial_succ]
    calc ∑ i ∈ Finset.range (k + 1), (i + 1) * Nat.stirlingSecond k (i + 1)
          + ∑ i ∈ Finset.range (k + 1), Nat.stirlingSecond k i
        ≤ k * ∑ i ∈ Finset.range (k + 1), Nat.stirlingSecond k i
          + ∑ i ∈ Finset.range (k + 1), Nat.stirlingSecond k i := by
          refine Nat.add_le_add_right ((Finset.sum_le_sum hterm).trans ?_) _
          rw [← Finset.mul_sum]
          exact Nat.mul_le_mul_left _ hshift
      _ = (k + 1) * ∑ i ∈ Finset.range (k + 1), Nat.stirlingSecond k i := by ring
      _ ≤ (k + 1) * k.factorial := Nat.mul_le_mul_left _ ih

/-- **The Stirling weight at every degree.** The total Stirling weight of a multi-index is at most
the factorial of its degree: each Bell number is at most the factorial, and
`∏_a b_a! ≤ (Σ_a b_a)!`. -/
theorem totalStirlingWeight_le_factorial {H : Type*} [Fintype H] [DecidableEq H] (b : H → ℕ) :
    totalStirlingWeight b ≤ ((∑ a, b a).factorial : ℝ) := by
  have hprodle : ∏ a, ∑ i ∈ Finset.range (b a + 1), Nat.stirlingSecond (b a) i
      ≤ ∏ a, (b a).factorial :=
    Finset.prod_le_prod (fun _ _ ↦ Nat.zero_le _) fun a _ ↦ sum_stirlingSecond_le_factorial (b a)
  have hmulti : ∏ a, (b a).factorial ≤ (∑ a, b a).factorial :=
    calc ∏ a, (b a).factorial
        ≤ (∏ a, (b a).factorial) * Nat.multinomial Finset.univ b :=
          Nat.le_mul_of_pos_right _ (Nat.multinomial_pos Finset.univ b)
      _ = (∑ a, b a).factorial := Nat.multinomial_spec Finset.univ b
  rw [totalStirlingWeight_eq_prod]
  exact_mod_cast hprodle.trans hmulti

/-- **NOTE1 §4.2a: the expansion (10) has an `O(N⁻²)` remainder at every fixed finite degree.**
Under the multinomial census with `N ≥ 1` draws from the category law `x`, every polynomial `f`
of total degree at most `d` satisfies
`|E f(Z/N) - f(x) - resamplingOperator x f / N| ≤ K_d · coefficientMass f / N²` with
`K_d = C(d, 2)²/2 + (C(d - 1, 2) + 1) · d!`, uniformly in `x`. -/
theorem abs_expectation_eval_sub_le_of_totalDegree_le {H : Type*} [Fintype H] [DecidableEq H]
    (offspring : FiniteReportLaw H) (N : ℕ) (hN : 1 ≤ N) (d : ℕ) (f : MvPolynomial H ℝ)
    (hf : f.totalDegree ≤ d) :
    |(multinomialLaw offspring N).expectation
          (fun counts ↦ MvPolynomial.eval (fun a ↦ (counts.val a : ℝ) / N) f)
        - MvPolynomial.eval offspring.mass f - resamplingOperator offspring.mass f / N|
      ≤ ((d.choose 2 : ℝ) ^ 2 / 2 + (((d - 1).choose 2 : ℝ) + 1) * d.factorial)
          * coefficientMass f / (N : ℝ) ^ 2 := by
  have hconstant : ∀ s ∈ f.support,
      ((∑ a, s a).choose 2 : ℝ) ^ 2 / 2
          + (((∑ a, s a - 1).choose 2 : ℝ) + 1) * totalStirlingWeight ⇑s
        ≤ (d.choose 2 : ℝ) ^ 2 / 2 + (((d - 1).choose 2 : ℝ) + 1) * d.factorial := by
    intro s hs
    have hdeg : ∑ a, s a ≤ d := by
      have hle := MvPolynomial.le_totalDegree hs
      rw [Finsupp.sum_fintype s (fun _ e ↦ e) (fun _ ↦ rfl)] at hle
      omega
    have hc1 : ((∑ a, s a).choose 2 : ℝ) ≤ d.choose 2 := by
      exact_mod_cast Nat.choose_le_choose 2 hdeg
    have hc2 : ((∑ a, s a - 1).choose 2 : ℝ) ≤ (d - 1).choose 2 := by
      exact_mod_cast Nat.choose_le_choose 2 (by omega)
    have hT : totalStirlingWeight ⇑s ≤ d.factorial :=
      (totalStirlingWeight_le_factorial ⇑s).trans (by exact_mod_cast Nat.factorial_le hdeg)
    have hT0 : 0 ≤ totalStirlingWeight ⇑s :=
      Finset.sum_nonneg fun j _ ↦ stirlingWeight_nonneg _ j
    have hc0 : (0 : ℝ) ≤ ((∑ a, s a).choose 2 : ℝ) := Nat.cast_nonneg _
    have hsq : ((∑ a, s a).choose 2 : ℝ) ^ 2 ≤ (d.choose 2 : ℝ) ^ 2 := by
      rw [pow_two, pow_two]
      exact mul_le_mul hc1 hc1 hc0 (hc0.trans hc1)
    have hprod : (((∑ a, s a - 1).choose 2 : ℝ) + 1) * totalStirlingWeight ⇑s
        ≤ (((d - 1).choose 2 : ℝ) + 1) * d.factorial :=
      mul_le_mul (by linarith) hT hT0 (by positivity)
    linarith
  refine (abs_expectation_eval_sub_le_every offspring N hN f).trans ?_
  refine div_le_div_of_nonneg_right ?_ (by positivity)
  calc ∑ s ∈ f.support, |f.coeff s| * (((∑ a, s a).choose 2 : ℝ) ^ 2 / 2
          + (((∑ a, s a - 1).choose 2 : ℝ) + 1) * totalStirlingWeight ⇑s)
      ≤ ∑ s ∈ f.support, |f.coeff s| * ((d.choose 2 : ℝ) ^ 2 / 2
          + (((d - 1).choose 2 : ℝ) + 1) * d.factorial) :=
        Finset.sum_le_sum fun s hs ↦ mul_le_mul_of_nonneg_left (hconstant s hs) (abs_nonneg _)
    _ = ((d.choose 2 : ℝ) ^ 2 / 2 + (((d - 1).choose 2 : ℝ) + 1) * d.factorial)
          * coefficientMass f := by
        rw [← Finset.sum_mul, mul_comm, coefficientMass]

end Descent.Portability.MultinomialRemainderEveryDegree
