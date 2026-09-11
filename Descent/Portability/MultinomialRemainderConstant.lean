/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.MultinomialJetCertificate

assert_below Descent.Decision Descent.Program

/-!
# The uniform remainder constant 71 of the multinomial expansion (10)

`MultinomialMomentExpansion.abs_expectation_monomial_sub_le` proves NOTE1 (10) for a monomial of
degree at most four with remainder `(11 + 4 · totalStirlingWeight b) / N ^ 2`, and
`MultinomialJetCertificate.totalStirlingWeight_le` bounds that weight by `24` through
`B(k) ≤ k!` and `∏_a b_a! ≤ (Σ_a b_a)!`, giving the constant `107`. This module computes the
true maximum of the weight at degree at most four, which is `15`, and derives the constant `71`.

The weight is the product over categories of the Bell numbers `B(b_a) = Σ_i S(b_a, i)`
(`MultinomialJetCertificate.totalStirlingWeight_eq_prod`). The Bell numbers of orders zero to
four are `1, 1, 2, 5, 15`, so they are at most `15` (`bell_le_fifteen`) and supermultiplicative,
`B(m) B(n) ≤ B(m + n)` for `m + n ≤ 4` (`bell_mul_le_bell_add`); both are finite case checks
decided by evaluating Stirling numbers. Induction over the categories gives
`∏_a B(b_a) ≤ B(Σ_a b_a)` whenever the degree is at most four (`prod_bell_le_bell_sum`), hence
`totalStirlingWeight_le_fifteen`. The bound is attained by the pure fourth power of one category
(`totalStirlingWeight_single_four`), so `15` is the maximum weight, not only a bound.

The remainder constant follows: `11 + 4 · 15 = 71`. `abs_expectation_monomial_sub_le_seventyOne`
is (10) for every monomial of degree at most four with remainder `71 / N ^ 2`,
`sum_coeff_remainder_le_seventyOne` bounds the coefficient-weighted remainder of a polynomial of
total degree at most four by `71` times its `MultinomialJetCertificate.coefficientMass`, and
`abs_expectation_eval_sub_le_seventyOne` is (10) for such a polynomial with remainder
`71 · coefficientMass f / N ^ 2`, uniformly over the category law.

Scope. The constant `71` is the one this proof method yields: the remainder of the descending
factorial ratios is bounded by `11 / N ^ 2` and `3 / N ^ 2` and every Stirling-weighted term by
its weight. NOTE1 reports that a script found the largest monomial remainder coefficient to be
`62`; that sharper per-monomial audit value is not proved here.

## Empirical status

None. The bodies here are finite combinatorics: Stirling numbers of order at most four, their
sums and products, and an inequality between remainder constants, so no measurement can bear on
them.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.MultinomialRemainderConstant

open FiniteReproductiveKernel MultinomialMomentExpansion MultinomialJetCertificate

/-- The Bell numbers `B(k) = Σ_{i ≤ k} S(k, i)` of order at most four are at most `15`. -/
theorem bell_le_fifteen (k : ℕ) (hk : k ≤ 4) :
    ∑ i ∈ Finset.range (k + 1), Nat.stirlingSecond k i ≤ 15 := by
  interval_cases k <;> simp [Finset.sum_range_succ, Nat.stirlingSecond]

/-- **Supermultiplicativity of the Bell numbers up to order four.** For `m + n ≤ 4`,
`B(m) B(n) ≤ B(m + n)`, where `B(k) = Σ_{i ≤ k} S(k, i)`. -/
theorem bell_mul_le_bell_add (m n : ℕ) (hmn : m + n ≤ 4) :
    (∑ i ∈ Finset.range (m + 1), Nat.stirlingSecond m i) *
        ∑ i ∈ Finset.range (n + 1), Nat.stirlingSecond n i ≤
      ∑ i ∈ Finset.range (m + n + 1), Nat.stirlingSecond (m + n) i := by
  have hm : m ≤ 4 := by omega
  have hn : n ≤ 4 := by omega
  interval_cases m <;> interval_cases n <;>
    first | omega | simp [Finset.sum_range_succ, Nat.stirlingSecond]

/-- Over any finite set of categories, the product of the Bell numbers of a multi-index of total
degree at most four is at most the Bell number of its total degree. -/
theorem prod_bell_le_bell_sum {H : Type*} [DecidableEq H] (b : H → ℕ) (s : Finset H)
    (hs : ∑ a ∈ s, b a ≤ 4) :
    ∏ a ∈ s, ∑ i ∈ Finset.range (b a + 1), Nat.stirlingSecond (b a) i ≤
      ∑ i ∈ Finset.range (∑ a ∈ s, b a + 1), Nat.stirlingSecond (∑ a ∈ s, b a) i := by
  revert hs
  refine Finset.induction_on s ?_ ?_
  · intro _
    simp [Nat.stirlingSecond]
  · intro a s ha ih hs
    rw [Finset.sum_insert ha] at hs
    rw [Finset.prod_insert ha, Finset.sum_insert ha]
    exact (Nat.mul_le_mul le_rfl (ih (by omega))).trans
      (bell_mul_le_bell_add (b a) (∑ c ∈ s, b c) hs)

/-- **The Stirling weight of NOTE1 (10) at degree at most four.** For a multi-index of total
degree at most four the total Stirling weight is at most `15`: it is the product of the Bell
numbers of the coordinates, which is at most the Bell number of the degree, at most `B(4) = 15`. -/
theorem totalStirlingWeight_le_fifteen {H : Type*} [Fintype H] [DecidableEq H] (b : H → ℕ)
    (hb : ∑ a, b a ≤ 4) : totalStirlingWeight b ≤ 15 := by
  have hnat : ∏ a, ∑ i ∈ Finset.range (b a + 1), Nat.stirlingSecond (b a) i ≤ 15 :=
    (prod_bell_le_bell_sum b Finset.univ hb).trans (bell_le_fifteen _ hb)
  rw [totalStirlingWeight_eq_prod]
  exact_mod_cast hnat

/-- The weight bound `15` is attained: the pure fourth power of one category has total Stirling
weight `B(4) = 15`, so `15` is the maximum weight at degree at most four. -/
theorem totalStirlingWeight_single_four {H : Type*} [Fintype H] [DecidableEq H] (a : H) :
    totalStirlingWeight (Pi.single a 4 : H → ℕ) = 15 := by
  rw [totalStirlingWeight_eq_prod, Finset.prod_eq_single a]
  · simp [Finset.sum_range_succ, Nat.stirlingSecond]
    norm_num
  · intro c _ hc
    simp [Pi.single_eq_of_ne hc, Nat.stirlingSecond]
  · intro hnot
    exact absurd (Finset.mem_univ a) hnot

/-- **NOTE1 (10) for monomials with remainder `71 / N ^ 2`.** Under the multinomial census with
`N ≥ 1` draws from the category law `x`, the expected monomial of degree at most four of the
census proportions is `x ^ b + monomialFirstOrder x b / N` up to `71 / N ^ 2`, uniformly in
`x`. -/
theorem abs_expectation_monomial_sub_le_seventyOne {H : Type*} [Fintype H] [DecidableEq H]
    (offspring : FiniteReportLaw H) (N : ℕ) (hN : 1 ≤ N) (b : H → ℕ) (hb : ∑ a, b a ≤ 4) :
    |(multinomialLaw offspring N).expectation
          (fun counts ↦ ∏ a, ((counts.val a : ℝ) / N) ^ b a)
        - ∏ a, offspring.mass a ^ b a - monomialFirstOrder offspring.mass b / N|
      ≤ 71 / (N : ℝ) ^ 2 :=
  (abs_expectation_monomial_sub_le offspring N hN b hb).trans
    (div_le_div_of_nonneg_right (by linarith [totalStirlingWeight_le_fifteen b hb])
      (by positivity))

/-- The coefficient-weighted remainder constant of (10) on a polynomial of total degree at most
four is at most `71` times its coefficient mass. -/
theorem sum_coeff_remainder_le_seventyOne {H : Type*} [Fintype H] [DecidableEq H]
    (p : MvPolynomial H ℝ) (hp : p.totalDegree ≤ 4) :
    ∑ s ∈ p.support, |p.coeff s| * (11 + 4 * totalStirlingWeight ⇑s)
      ≤ 71 * coefficientMass p := by
  have hconstant : ∀ s ∈ p.support, 11 + 4 * totalStirlingWeight ⇑s ≤ 71 := by
    intro s hs
    have hdegree := MvPolynomial.le_totalDegree hs
    rw [Finsupp.sum_fintype s (fun _ e ↦ e) (fun _ ↦ rfl)] at hdegree
    linarith [totalStirlingWeight_le_fifteen (⇑s) (hdegree.trans hp)]
  calc ∑ s ∈ p.support, |p.coeff s| * (11 + 4 * totalStirlingWeight ⇑s)
      ≤ ∑ s ∈ p.support, |p.coeff s| * 71 :=
        Finset.sum_le_sum fun s hs ↦ mul_le_mul_of_nonneg_left (hconstant s hs) (abs_nonneg _)
    _ = 71 * coefficientMass p := by
        rw [← Finset.sum_mul, mul_comm, coefficientMass]

/-- **NOTE1 (10) for every polynomial of degree at most four, remainder `71 / N ^ 2`.** Under
the multinomial census with `N ≥ 1` draws from the category law `x`, the expected value of a
polynomial `f` of total degree at most four at the census proportions is
`f(x) + resamplingOperator x f / N`, up to `71 · coefficientMass f / N ^ 2`, uniformly in `x`. -/
theorem abs_expectation_eval_sub_le_seventyOne {H : Type*} [Fintype H] [DecidableEq H]
    (offspring : FiniteReportLaw H) (N : ℕ) (hN : 1 ≤ N) (f : MvPolynomial H ℝ)
    (hf : f.totalDegree ≤ 4) :
    |(multinomialLaw offspring N).expectation
          (fun counts ↦ MvPolynomial.eval (fun a ↦ (counts.val a : ℝ) / N) f)
        - MvPolynomial.eval offspring.mass f - resamplingOperator offspring.mass f / N|
      ≤ 71 * coefficientMass f / (N : ℝ) ^ 2 :=
  (abs_expectation_eval_sub_le offspring N hN f hf).trans
    (div_le_div_of_nonneg_right (sum_coeff_remainder_le_seventyOne f hf) (by positivity))

end Descent.Portability.MultinomialRemainderConstant
