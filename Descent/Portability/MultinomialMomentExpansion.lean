/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.FiniteReproductiveKernel
import Mathlib.Combinatorics.Enumerative.Stirling

assert_below Descent.Decision Descent.Program

/-!
# Factorial moments of the multinomial law

NOTE1 §2.3 builds its drift stage from multinomial resampling and reads the expansion (10) off
the exact factorial-moment identity of the multinomial law: for `Z ~ Multinomial(N, x)` and
any multi-index `b`,

  `E ∏_a (Z_a)_{b_a} = (N)_{Σ_a b_a} ∏_a x_a ^ b_a`,

where `(n)_k = n (n - 1) ⋯ (n - k + 1)` is the descending factorial, `Nat.descFactorial`. This
module proves that identity for the corpus multinomial census law
`FiniteReproductiveKernel.multinomialLaw`, on an arbitrary finite type of categories, with no
restriction on `N` or `b`.

The proof is a reindexing of the multinomial theorem, not a generating-function argument.
`multinomial_mul_prod_descFactorial` is the arithmetic core: when `b ≤ z` pointwise the
multinomial coefficient of `z` times the descending factorials `(z_a)_{b_a}` equals
`(Σ z)_{Σ b}` times the multinomial coefficient of `z - b`, checked by clearing the factorials
of `z - b`. `sum_piAntidiag_prod_descFactorial` then evaluates the moment sum for an arbitrary
real vector `x`: census vectors with some `z_a < b_a` contribute zero because a descending
factorial vanishes, the remaining ones are shifted by `b` onto the census vectors of total
`N - Σ b`, and the multinomial theorem `Finset.sum_pow_eq_sum_piAntidiag` sums them to
`(Σ x) ^ (N - Σ b)`. When `Σ b > N` both sides are zero. `expectation_prod_descFactorial` is the
statement for the probability law, where `Σ x = 1`.

Power moments follow. `pow_eq_sum_stirlingSecond_mul_descFactorial` writes a power of a
natural number as the Stirling-weighted sum of its descending factorials,
`n ^ k = Σ_{j ≤ k} S(k, j) (n)_j` with `S = Nat.stirlingSecond`, by induction on `k` through the
recurrence `S(k + 1, j + 1) = (j + 1) S(k, j + 1) + S(k, j)`. `expectation_prod_pow` then gives
every mixed power moment of the census exactly,
`E ∏_a Z_a ^ b_a = Σ_{j ≤ b} (∏_a S(b_a, j_a)) (N)_{Σ j} ∏_a x_a ^ j_a`, an explicit polynomial in
`N` and `x` with no remainder.

The expansion (10) is proved for every monomial of degree at most four.
`expectation_monomial_eq` reads the moment of `∏_a (Z_a / N) ^ b_a` off the power moments, and
`sum_subIndices_split` separates the sub-multi-indices `j ≤ b` by degree: `j = b` itself, the
Stirling-weighted monomials one degree below (`firstOrderStirlingSum`), and those at least two
degrees below (`lowOrderStirlingSum`). When `|b| ≤ 4` the descending factorial ratios
`(N)_{|b|} / N ^ |b|` and `(N)_{|b| - 1} / N ^ |b|` agree with `1 - C(|b|, 2) / N` and `1 / N` to
within `11 / N ^ 2` and `3 / N ^ 2` (`abs_descFactorial_div_pow_sub_le`,
`abs_descFactorial_pred_div_pow_sub_le`), so `abs_expectation_monomial_sub_le` gives
`|E (Z / N) ^ b - x ^ b - monomialFirstOrder x b / N| ≤ (11 + 4 totalStirlingWeight b) / N ^ 2`
uniformly over the category law, with the constant read off the Stirling weights of `b`.

The first-order coefficient has the closed form (10) predicts.
`firstOrderStirlingSum_eq_sum_choose` shows that the sub-multi-indices exactly one degree below `b`
are `b` with a single coordinate lowered by one, and that lowering coordinate `a` carries the
Stirling weight `S(b_a, b_a - 1) = C(b_a, 2)`; hence `monomialFirstOrder_eq_sum_choose`,
`monomialFirstOrder x b = Σ_a C(b_a, 2) x ^ (b - e_a) - C(|b|, 2) x ^ b`.

What is NOT proved in this module: that this closed form is the second-order operator
`(1 / 2) Σ_{a, c} (x_a δ_ac - x_a x_c) ∂_a ∂_c x ^ b` computed from the partial derivatives of the
polynomial, the extension to linear combinations of monomials, and the multinomial drift stage
that would replace the single-draw drift stage of the microscopic kernel.

## Empirical status

None. The bodies here are finite combinatorics: a multinomial theorem, factorial arithmetic and
a reindexing of census vectors. No measurement can bear on a moment identity of a named law.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.MultinomialMomentExpansion

open Descent.Portability.FiniteReproductiveKernel

noncomputable section

/-- **The multinomial coefficient absorbs descending factorials.** If `b ≤ z` pointwise, the
multinomial coefficient of `z` times the descending factorials `(z_a)_{b_a}` is the descending
factorial `(Σ z)_{Σ b}` times the multinomial coefficient of `z - b`. -/
theorem multinomial_mul_prod_descFactorial {H : Type*} [Fintype H] [DecidableEq H]
    (z b : H → ℕ) (hle : ∀ a, b a ≤ z a) :
    Nat.multinomial Finset.univ z * ∏ a, (z a).descFactorial (b a)
      = (∑ a, z a).descFactorial (∑ a, b a) * Nat.multinomial Finset.univ (z - b) := by
  have hpos : 0 < ∏ a, (z a - b a).factorial :=
    Finset.prod_pos fun a _ ↦ Nat.factorial_pos _
  have hsum : ∑ a, (z a - b a) = ∑ a, z a - ∑ a, b a := by
    refine Nat.eq_sub_of_add_eq ?_
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun a _ ↦ Nat.sub_add_cancel (hle a)
  have hprod : (∏ a, (z a).descFactorial (b a)) * ∏ a, (z a - b a).factorial
      = ∏ a, (z a).factorial := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun a _ ↦ ?_
    rw [mul_comm]
    exact Nat.factorial_mul_descFactorial (hle a)
  have hspec := Nat.multinomial_spec Finset.univ (z - b)
  simp only [Pi.sub_apply] at hspec
  rw [hsum] at hspec
  have hdesc : (∑ a, z a - ∑ a, b a).factorial * (∑ a, z a).descFactorial (∑ a, b a)
      = (∑ a, z a).factorial :=
    Nat.factorial_mul_descFactorial (Finset.sum_le_sum fun a _ ↦ hle a)
  refine Nat.eq_of_mul_eq_mul_right hpos ?_
  calc Nat.multinomial Finset.univ z * (∏ a, (z a).descFactorial (b a))
        * ∏ a, (z a - b a).factorial
      = (∏ a, (z a).factorial) * Nat.multinomial Finset.univ z := by
        rw [mul_assoc, hprod, mul_comm]
    _ = (∑ a, z a).factorial := Nat.multinomial_spec Finset.univ z
    _ = (∑ a, z a).descFactorial (∑ a, b a) * Nat.multinomial Finset.univ (z - b)
        * ∏ a, (z a - b a).factorial := by
        rw [← hdesc, ← hspec]
        ring

/-- **The descending factorial moment sum.** For any real vector `x`, summing the multinomial
weights of the census vectors of total `N` against the descending factorials `(z_a)_{b_a}`
gives `(N)_{Σ b} ∏ x_a ^ b_a (Σ x) ^ (N - Σ b)`. Census vectors below `b` contribute zero, the
rest are shifted onto census vectors of total `N - Σ b`, and the multinomial theorem sums
those. -/
theorem sum_piAntidiag_prod_descFactorial {H : Type*} [Fintype H] [DecidableEq H]
    (x : H → ℝ) (N : ℕ) (b : H → ℕ) :
    ∑ z ∈ Finset.piAntidiag Finset.univ N,
        (Nat.multinomial Finset.univ z : ℝ) * (∏ a, x a ^ z a)
          * ∏ a, ((z a).descFactorial (b a) : ℝ)
      = (N.descFactorial (∑ a, b a) : ℝ) * (∏ a, x a ^ b a)
          * (∑ a, x a) ^ (N - ∑ a, b a) := by
  classical
  by_cases hB : ∑ a, b a ≤ N
  · have hterm : ∀ z ∈ Finset.piAntidiag Finset.univ N,
        (Nat.multinomial Finset.univ z : ℝ) * (∏ a, x a ^ z a)
            * ∏ a, ((z a).descFactorial (b a) : ℝ) ≠ 0 → ∀ a, b a ≤ z a := by
      intro z _ hne a
      by_contra hlt
      apply hne
      refine mul_eq_zero_of_right _ (Finset.prod_eq_zero (Finset.mem_univ a) ?_)
      exact_mod_cast Nat.descFactorial_eq_zero_iff_lt.mpr (not_le.mp hlt)
    rw [← Finset.sum_filter_of_ne hterm, Finset.sum_pow_eq_sum_piAntidiag, Finset.mul_sum]
    refine Finset.sum_bij' (fun z _ ↦ z - b) (fun w _ ↦ w + b) ?_ ?_ ?_ ?_ ?_
    · intro z hz
      dsimp only
      obtain ⟨hmem, hle⟩ := Finset.mem_filter.mp hz
      have hsumz := (Finset.mem_piAntidiag.mp hmem).1
      refine Finset.mem_piAntidiag.mpr ⟨Nat.eq_sub_of_add_eq ?_, fun a _ ↦ Finset.mem_univ a⟩
      calc Finset.univ.sum (z - b) + ∑ a, b a = ∑ a, (z a - b a + b a) :=
            Finset.sum_add_distrib.symm
        _ = Finset.univ.sum z := Finset.sum_congr rfl fun a _ ↦ Nat.sub_add_cancel (hle a)
        _ = N := hsumz
    · intro w hw
      have hsumw := (Finset.mem_piAntidiag.mp hw).1
      refine Finset.mem_filter.mpr ⟨Finset.mem_piAntidiag.mpr ⟨?_, fun a _ ↦ Finset.mem_univ a⟩,
        fun a ↦ Nat.le_add_left (b a) (w a)⟩
      calc Finset.univ.sum (w + b) = ∑ a, w a + ∑ a, b a := Finset.sum_add_distrib
        _ = N := by rw [hsumw, Nat.sub_add_cancel hB]
    · intro z hz
      funext a
      exact Nat.sub_add_cancel ((Finset.mem_filter.mp hz).2 a)
    · intro w _
      funext a
      exact Nat.add_sub_cancel (w a) (b a)
    · intro z hz
      dsimp only
      have hle := (Finset.mem_filter.mp hz).2
      have hsumz := (Finset.mem_piAntidiag.mp (Finset.mem_filter.mp hz).1).1
      have hnat := multinomial_mul_prod_descFactorial z b hle
      rw [hsumz] at hnat
      have hreal : (Nat.multinomial Finset.univ z : ℝ) * ∏ a, ((z a).descFactorial (b a) : ℝ)
          = (N.descFactorial (∑ a, b a) : ℝ) * (Nat.multinomial Finset.univ (z - b) : ℝ) := by
        exact_mod_cast hnat
      have hpow : ∏ a, x a ^ z a = (∏ a, x a ^ b a) * ∏ a, x a ^ (z - b) a := by
        rw [← Finset.prod_mul_distrib]
        refine Finset.prod_congr rfl fun a _ ↦ ?_
        rw [← pow_add]
        congr 1
        exact (Nat.add_sub_of_le (hle a)).symm
      calc (Nat.multinomial Finset.univ z : ℝ) * (∏ a, x a ^ z a)
            * ∏ a, ((z a).descFactorial (b a) : ℝ)
          = ((Nat.multinomial Finset.univ z : ℝ) * ∏ a, ((z a).descFactorial (b a) : ℝ))
            * ∏ a, x a ^ z a := by ring
        _ = (N.descFactorial (∑ a, b a) : ℝ) * (∏ a, x a ^ b a)
            * ((Nat.multinomial Finset.univ (z - b) : ℝ) * ∏ a, x a ^ (z - b) a) := by
          rw [hreal, hpow]
          ring
  · have hlt : N < ∑ a, b a := not_le.mp hB
    rw [Nat.descFactorial_eq_zero_iff_lt.mpr hlt, Nat.cast_zero, zero_mul, zero_mul]
    refine Finset.sum_eq_zero fun z hz ↦ ?_
    have hsumz := (Finset.mem_piAntidiag.mp hz).1
    obtain ⟨a, ha⟩ : ∃ a, z a < b a := by
      by_contra hnone
      push_neg at hnone
      have hle : ∑ a, b a ≤ ∑ a, z a := Finset.sum_le_sum fun a _ ↦ hnone a
      rw [hsumz] at hle
      omega
    refine mul_eq_zero_of_right _ (Finset.prod_eq_zero (Finset.mem_univ a) ?_)
    exact_mod_cast Nat.descFactorial_eq_zero_iff_lt.mpr ha

/-- **NOTE1 §2.3, the factorial-moment identity.** Under the multinomial census law with `N`
draws from the category law `offspring`, the expectation of `∏_a (Z_a)_{b_a}` is
`(N)_{Σ b} ∏_a offspring_a ^ b_a`, for every multi-index `b`. -/
theorem expectation_prod_descFactorial {H : Type*} [Fintype H] [DecidableEq H]
    (offspring : FiniteReportLaw H) (N : ℕ) (b : H → ℕ) :
    (multinomialLaw offspring N).expectation
        (fun counts ↦ ∏ a, ((counts.val a).descFactorial (b a) : ℝ))
      = (N.descFactorial (∑ a, b a) : ℝ) * ∏ a, offspring.mass a ^ b a := by
  have hsum := sum_piAntidiag_prod_descFactorial offspring.mass N b
  rw [offspring.mass_sum, one_pow, mul_one] at hsum
  rw [← hsum]
  exact Finset.sum_coe_sort (Finset.piAntidiag Finset.univ N)
    (fun z : H → ℕ ↦ (Nat.multinomial Finset.univ z : ℝ) * (∏ a, offspring.mass a ^ z a)
      * ∏ a, ((z a).descFactorial (b a) : ℝ))

/-- **Powers as Stirling sums of descending factorials.** For natural numbers,
`n ^ k = Σ_{j ≤ k} S(k, j) (n)_j`, with `S` the Stirling numbers of the second kind. -/
theorem pow_eq_sum_stirlingSecond_mul_descFactorial (n k : ℕ) :
    n ^ k = ∑ j ∈ Finset.range (k + 1), Nat.stirlingSecond k j * n.descFactorial j := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hmul : ∀ j, n.descFactorial j * n
        = n.descFactorial (j + 1) + j * n.descFactorial j := by
      intro j
      rw [Nat.descFactorial_succ]
      by_cases hj : j ≤ n
      · rw [← add_mul, Nat.sub_add_cancel hj, mul_comm]
      · rw [Nat.descFactorial_eq_zero_iff_lt.mpr (not_le.mp hj)]
        simp
    have hshift : ∑ j ∈ Finset.range (k + 1), Nat.stirlingSecond k j * (j * n.descFactorial j)
        = ∑ j ∈ Finset.range (k + 1),
            (j + 1) * Nat.stirlingSecond k (j + 1) * n.descFactorial (j + 1) := by
      rw [Finset.sum_range_succ', Finset.sum_range_succ,
        Nat.stirlingSecond_eq_zero_of_lt (Nat.lt_add_one k)]
      simp only [zero_mul, mul_zero, add_zero]
      exact Finset.sum_congr rfl fun j _ ↦ by ring
    calc n ^ (k + 1) = n ^ k * n := pow_succ n k
      _ = ∑ j ∈ Finset.range (k + 1), Nat.stirlingSecond k j * (n.descFactorial j * n) := by
        rw [ih, Finset.sum_mul]
        exact Finset.sum_congr rfl fun j _ ↦ by ring
      _ = ∑ j ∈ Finset.range (k + 1), Nat.stirlingSecond k j * n.descFactorial (j + 1)
          + ∑ j ∈ Finset.range (k + 1), Nat.stirlingSecond k j * (j * n.descFactorial j) := by
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun j _ ↦ by rw [hmul]; ring
      _ = ∑ j ∈ Finset.range (k + 1),
            Nat.stirlingSecond (k + 1) (j + 1) * n.descFactorial (j + 1) := by
        rw [hshift, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun j _ ↦ ?_
        rw [Nat.stirlingSecond_succ_succ]
        ring
      _ = ∑ j ∈ Finset.range (k + 1 + 1), Nat.stirlingSecond (k + 1) j * n.descFactorial j := by
        rw [Finset.sum_range_succ' _ (k + 1), Nat.stirlingSecond_succ_zero, zero_mul, add_zero]

/-- **Exact power moments of the multinomial census.** The expectation of `∏_a Z_a ^ b_a` is the
Stirling-weighted sum of descending factorial moments,
`Σ_{j ≤ b} (∏_a S(b_a, j_a)) (N)_{Σ j} ∏_a x_a ^ j_a`. -/
theorem expectation_prod_pow {H : Type*} [Fintype H] [DecidableEq H]
    (offspring : FiniteReportLaw H) (N : ℕ) (b : H → ℕ) :
    (multinomialLaw offspring N).expectation (fun counts ↦ ∏ a, (counts.val a : ℝ) ^ b a)
      = ∑ j ∈ Fintype.piFinset fun a ↦ Finset.range (b a + 1),
          (∏ a, (Nat.stirlingSecond (b a) (j a) : ℝ)) * (N.descFactorial (∑ a, j a) : ℝ)
            * ∏ a, offspring.mass a ^ j a := by
  have hpoint : ∀ counts : Counts H N, ∏ a, (counts.val a : ℝ) ^ b a
      = ∑ j ∈ Fintype.piFinset fun a ↦ Finset.range (b a + 1),
          (∏ a, (Nat.stirlingSecond (b a) (j a) : ℝ))
            * ∏ a, ((counts.val a).descFactorial (j a) : ℝ) := by
    intro counts
    have hfactor : ∀ a, (counts.val a : ℝ) ^ b a
        = ∑ i ∈ Finset.range (b a + 1),
            (Nat.stirlingSecond (b a) i : ℝ) * ((counts.val a).descFactorial i : ℝ) := by
      intro a
      exact_mod_cast pow_eq_sum_stirlingSecond_mul_descFactorial (counts.val a) (b a)
    simp only [hfactor]
    rw [Finset.prod_univ_sum]
    exact Finset.sum_congr rfl fun j _ ↦ Finset.prod_mul_distrib
  calc (multinomialLaw offspring N).expectation (fun counts ↦ ∏ a, (counts.val a : ℝ) ^ b a)
      = ∑ counts, (multinomialLaw offspring N).mass counts
          * ∑ j ∈ Fintype.piFinset fun a ↦ Finset.range (b a + 1),
              (∏ a, (Nat.stirlingSecond (b a) (j a) : ℝ))
                * ∏ a, ((counts.val a).descFactorial (j a) : ℝ) :=
        Finset.sum_congr rfl fun counts _ ↦ by simp only [hpoint]
    _ = ∑ j ∈ Fintype.piFinset fun a ↦ Finset.range (b a + 1),
          (∏ a, (Nat.stirlingSecond (b a) (j a) : ℝ))
            * (multinomialLaw offspring N).expectation
                (fun counts ↦ ∏ a, ((counts.val a).descFactorial (j a) : ℝ)) := by
        simp only [Finset.mul_sum, FiniteReportLaw.expectation]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun j _ ↦ Finset.sum_congr rfl fun counts _ ↦ by ring
    _ = _ := Finset.sum_congr rfl fun j _ ↦ by rw [expectation_prod_descFactorial]; ring

/-! ## The expansion (10) for monomials of degree at most four -/

/-- The descending factorial one step further, read in the reals: `(n)_{k + 1} = (n - k) (n)_k`
with genuine subtraction. When `n < k` both sides vanish. -/
theorem cast_descFactorial_succ (n k : ℕ) :
    (n.descFactorial (k + 1) : ℝ) = ((n : ℝ) - k) * n.descFactorial k := by
  rw [Nat.descFactorial_succ, Nat.cast_mul]
  by_cases hk : k ≤ n
  · rw [Nat.cast_sub hk]
  · rw [Nat.descFactorial_eq_zero_iff_lt.mpr (not_le.mp hk)]
    simp

/-- The third descending factorial as a real polynomial. -/
theorem cast_descFactorial_three (n : ℕ) :
    (n.descFactorial 3 : ℝ) = n * (n - 1) * (n - 2) := by
  have hstep : (n.descFactorial 3 : ℝ) = ((n : ℝ) - (2 : ℕ)) * n.descFactorial 2 :=
    cast_descFactorial_succ n 2
  rw [hstep, Nat.cast_descFactorial_two]
  push_cast
  ring

/-- The fourth descending factorial as a real polynomial. -/
theorem cast_descFactorial_four (n : ℕ) :
    (n.descFactorial 4 : ℝ) = n * (n - 1) * (n - 2) * (n - 3) := by
  have hstep : (n.descFactorial 4 : ℝ) = ((n : ℝ) - (3 : ℕ)) * n.descFactorial 3 :=
    cast_descFactorial_succ n 3
  rw [hstep, cast_descFactorial_three]
  push_cast
  ring

/-- **The leading descending factorial ratio.** For `N ≥ 1` and `B ≤ 4`, the ratio
`(N)_B / N ^ B` is `1 - C(B, 2) / N` to within `11 / N ^ 2`. -/
theorem abs_descFactorial_div_pow_sub_le (N B : ℕ) (hN : 1 ≤ N) (hB : B ≤ 4) :
    |(N.descFactorial B : ℝ) / (N : ℝ) ^ B - 1 + (B.choose 2 : ℝ) / N|
      ≤ 11 / (N : ℝ) ^ 2 := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hNne : (N : ℝ) ≠ 0 := hNpos.ne'
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hbound : (0 : ℝ) ≤ 11 / (N : ℝ) ^ 2 := by positivity
  interval_cases B
  · simpa using hbound
  · simpa [hNne] using hbound
  · have hval : (N.descFactorial 2 : ℝ) / (N : ℝ) ^ 2 - 1 + ((Nat.choose 2 2 : ℕ) : ℝ) / N
        = 0 := by
      rw [Nat.cast_descFactorial_two, Nat.choose_self, Nat.cast_one]
      field_simp
      ring
    rw [hval, abs_zero]
    exact hbound
  · have hval : (N.descFactorial 3 : ℝ) / (N : ℝ) ^ 3 - 1 + ((Nat.choose 3 2 : ℕ) : ℝ) / N
        = 2 / (N : ℝ) ^ 2 := by
      rw [cast_descFactorial_three, show Nat.choose 3 2 = 3 by decide]
      push_cast
      field_simp
      ring
    rw [hval, abs_of_nonneg (by positivity), div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [sq_nonneg (N : ℝ)]
  · have hval : (N.descFactorial 4 : ℝ) / (N : ℝ) ^ 4 - 1 + ((Nat.choose 4 2 : ℕ) : ℝ) / N
        = (11 * (N : ℝ) - 6) / (N : ℝ) ^ 3 := by
      rw [cast_descFactorial_four, show Nat.choose 4 2 = 6 by decide]
      push_cast
      field_simp
      ring
    rw [hval, abs_of_nonneg (div_nonneg (by linarith) (by positivity)),
      div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [sq_nonneg (N : ℝ)]

/-- **The subleading descending factorial ratio.** For `N ≥ 1` and `1 ≤ B ≤ 4`, the ratio
`(N)_{B - 1} / N ^ B` is `1 / N` to within `3 / N ^ 2`. -/
theorem abs_descFactorial_pred_div_pow_sub_le (N B : ℕ) (hN : 1 ≤ N) (hB1 : 1 ≤ B)
    (hB : B ≤ 4) :
    |(N.descFactorial (B - 1) : ℝ) / (N : ℝ) ^ B - 1 / N| ≤ 3 / (N : ℝ) ^ 2 := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hNne : (N : ℝ) ≠ 0 := hNpos.ne'
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hbound : (0 : ℝ) ≤ 3 / (N : ℝ) ^ 2 := by positivity
  interval_cases B
  · simpa using hbound
  · have hval : (N.descFactorial (2 - 1) : ℝ) / (N : ℝ) ^ 2 - 1 / N = 0 := by
      rw [show 2 - 1 = 1 by rfl, Nat.descFactorial_one]
      field_simp
      ring
    rw [hval, abs_zero]
    exact hbound
  · have hval : (N.descFactorial (3 - 1) : ℝ) / (N : ℝ) ^ 3 - 1 / N = -(1 / (N : ℝ) ^ 2) := by
      rw [show 3 - 1 = 2 by rfl, Nat.cast_descFactorial_two]
      field_simp
      ring
    rw [hval, abs_neg, abs_of_nonneg (by positivity),
      div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [sq_nonneg (N : ℝ)]
  · have hval : (N.descFactorial (4 - 1) : ℝ) / (N : ℝ) ^ 4 - 1 / N
        = -((3 * (N : ℝ) - 2) / (N : ℝ) ^ 3) := by
      rw [show 4 - 1 = 3 by rfl, cast_descFactorial_three]
      field_simp
      ring
    rw [hval, abs_neg, abs_of_nonneg (div_nonneg (by linarith) (by positivity)),
      div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [sq_nonneg (N : ℝ)]

/-- The sub-multi-indices `j ≤ b`, over which the power moment of `b` is summed. -/
def subIndices {H : Type*} [Fintype H] [DecidableEq H] (b : H → ℕ) : Finset (H → ℕ) :=
  Fintype.piFinset fun a ↦ Finset.range (b a + 1)

/-- The Stirling weight `∏_a S(b_a, j_a)` of a sub-multi-index `j` of `b`. -/
def stirlingWeight {H : Type*} [Fintype H] (b j : H → ℕ) : ℝ :=
  ∏ a, (Nat.stirlingSecond (b a) (j a) : ℝ)

/-- The total Stirling weight below `b`, which controls the uniform remainder constant. -/
def totalStirlingWeight {H : Type*} [Fintype H] [DecidableEq H] (b : H → ℕ) : ℝ :=
  ∑ j ∈ subIndices b, stirlingWeight b j

/-- The Stirling-weighted monomials exactly one degree below `b`. -/
def firstOrderStirlingSum {H : Type*} [Fintype H] [DecidableEq H] (x : H → ℝ)
    (b : H → ℕ) : ℝ :=
  ∑ j ∈ (subIndices b).filter (fun j ↦ ∑ a, j a + 1 = ∑ a, b a),
    stirlingWeight b j * ∏ a, x a ^ j a

/-- The Stirling-weighted descending factorial moments at least two degrees below `b`. -/
def lowOrderStirlingSum {H : Type*} [Fintype H] [DecidableEq H] (x : H → ℝ) (N : ℕ)
    (b : H → ℕ) : ℝ :=
  ∑ j ∈ ((subIndices b).filter (fun j ↦ ¬ ∑ a, j a + 1 = ∑ a, b a)).filter
      (fun j ↦ ¬ ∑ a, j a = ∑ a, b a),
    stirlingWeight b j * (N.descFactorial (∑ a, j a) : ℝ) * ∏ a, x a ^ j a

/-- The first-order coefficient of the multinomial expansion of the monomial `x ^ b`: the
Stirling-weighted monomials one degree below `b`, less `C(|b|, 2) x ^ b`. -/
def monomialFirstOrder {H : Type*} [Fintype H] [DecidableEq H] (x : H → ℝ) (b : H → ℕ) :
    ℝ :=
  firstOrderStirlingSum x b - ((∑ a, b a).choose 2 : ℝ) * ∏ a, x a ^ b a

/-- A sub-multi-index lies below its multi-index coordinatewise. -/
theorem subIndices_le {H : Type*} [Fintype H] [DecidableEq H] {b j : H → ℕ}
    (hj : j ∈ subIndices b) (a : H) : j a ≤ b a :=
  Nat.lt_succ_iff.mp (Finset.mem_range.mp (Fintype.mem_piFinset.mp hj a))

/-- A multi-index is one of its own sub-multi-indices. -/
theorem mem_subIndices_self {H : Type*} [Fintype H] [DecidableEq H] (b : H → ℕ) :
    b ∈ subIndices b :=
  Fintype.mem_piFinset.mpr fun a ↦ Finset.mem_range.mpr (Nat.lt_succ_self (b a))

/-- Stirling weights are nonnegative. -/
theorem stirlingWeight_nonneg {H : Type*} [Fintype H] (b j : H → ℕ) :
    0 ≤ stirlingWeight b j :=
  Finset.prod_nonneg fun _ _ ↦ Nat.cast_nonneg _

/-- The Stirling weight of a multi-index against itself is one. -/
theorem stirlingWeight_self {H : Type*} [Fintype H] (b : H → ℕ) : stirlingWeight b b = 1 := by
  simp [stirlingWeight, Nat.stirlingSecond_self]

/-- A monomial in the category probabilities is nonnegative. -/
theorem categoryMonomial_nonneg {H : Type*} [Fintype H] (offspring : FiniteReportLaw H)
    (j : H → ℕ) : 0 ≤ ∏ a, offspring.mass a ^ j a :=
  Finset.prod_nonneg fun a _ ↦ pow_nonneg (offspring.mass_nonneg a) _

/-- A monomial in the category probabilities is at most one. -/
theorem categoryMonomial_le_one {H : Type*} [Fintype H] (offspring : FiniteReportLaw H)
    (j : H → ℕ) : ∏ a, offspring.mass a ^ j a ≤ 1 := by
  refine Finset.prod_le_one (fun a _ ↦ pow_nonneg (offspring.mass_nonneg a) _) fun a _ ↦ ?_
  refine pow_le_one₀ (offspring.mass_nonneg a) ?_
  rw [← offspring.mass_sum]
  exact Finset.single_le_sum (fun c _ ↦ offspring.mass_nonneg c) (Finset.mem_univ a)

/-- The first-order Stirling sum is nonnegative. -/
theorem firstOrderStirlingSum_nonneg {H : Type*} [Fintype H] [DecidableEq H]
    (offspring : FiniteReportLaw H) (b : H → ℕ) :
    0 ≤ firstOrderStirlingSum offspring.mass b :=
  Finset.sum_nonneg fun j _ ↦
    mul_nonneg (stirlingWeight_nonneg b j) (categoryMonomial_nonneg offspring j)

/-- The first-order Stirling sum is at most the total Stirling weight. -/
theorem firstOrderStirlingSum_le {H : Type*} [Fintype H] [DecidableEq H]
    (offspring : FiniteReportLaw H) (b : H → ℕ) :
    firstOrderStirlingSum offspring.mass b ≤ totalStirlingWeight b := by
  calc firstOrderStirlingSum offspring.mass b
      ≤ ∑ j ∈ (subIndices b).filter (fun j ↦ ∑ a, j a + 1 = ∑ a, b a), stirlingWeight b j :=
        Finset.sum_le_sum fun j _ ↦ mul_le_of_le_one_right (stirlingWeight_nonneg b j)
          (categoryMonomial_le_one offspring j)
    _ ≤ totalStirlingWeight b :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          fun j _ _ ↦ stirlingWeight_nonneg b j

/-- A multi-index of degree zero has no sub-multi-index one degree below it. -/
theorem firstOrderStirlingSum_of_sum_eq_zero {H : Type*} [Fintype H] [DecidableEq H]
    (x : H → ℝ) (b : H → ℕ) (hb : ∑ a, b a = 0) : firstOrderStirlingSum x b = 0 := by
  refine Finset.sum_eq_zero fun j hj ↦ ?_
  have hsucc := (Finset.mem_filter.mp hj).2
  exfalso
  omega

/-- The low-order Stirling sum is nonnegative. -/
theorem lowOrderStirlingSum_nonneg {H : Type*} [Fintype H] [DecidableEq H]
    (offspring : FiniteReportLaw H) (N : ℕ) (b : H → ℕ) :
    0 ≤ lowOrderStirlingSum offspring.mass N b :=
  Finset.sum_nonneg fun j _ ↦ mul_nonneg (mul_nonneg (stirlingWeight_nonneg b j)
    (Nat.cast_nonneg _)) (categoryMonomial_nonneg offspring j)

/-- Every term of the low-order Stirling sum is at least two degrees below `b`, so the sum is at
most `N ^ (|b| - 2)` times the total Stirling weight. -/
theorem lowOrderStirlingSum_mul_sq_le {H : Type*} [Fintype H] [DecidableEq H]
    (offspring : FiniteReportLaw H) (N : ℕ) (hN : 1 ≤ N) (b : H → ℕ) :
    lowOrderStirlingSum offspring.mass N b * (N : ℝ) ^ 2
      ≤ totalStirlingWeight b * (N : ℝ) ^ (∑ a, b a) := by
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNnn : (0 : ℝ) ≤ N := by linarith
  rw [lowOrderStirlingSum, totalStirlingWeight, Finset.sum_mul, Finset.sum_mul]
  refine (Finset.sum_le_sum fun j hj ↦ ?_).trans
    (Finset.sum_le_sum_of_subset_of_nonneg
      ((Finset.filter_subset _ _).trans (Finset.filter_subset _ _))
      fun j _ _ ↦ mul_nonneg (stirlingWeight_nonneg b j) (pow_nonneg hNnn _))
  obtain ⟨hj', hjB⟩ := Finset.mem_filter.mp hj
  obtain ⟨hjP, hj1⟩ := Finset.mem_filter.mp hj'
  have hjle : ∑ a, j a ≤ ∑ a, b a := Finset.sum_le_sum fun a _ ↦ subIndices_le hjP a
  have hj2 : ∑ a, j a + 2 ≤ ∑ a, b a := by omega
  have hdesc : (N.descFactorial (∑ a, j a) : ℝ) ≤ (N : ℝ) ^ (∑ a, j a) := by
    exact_mod_cast Nat.descFactorial_le_pow N _
  calc stirlingWeight b j * (N.descFactorial (∑ a, j a) : ℝ) * (∏ a, offspring.mass a ^ j a)
        * (N : ℝ) ^ 2
      ≤ stirlingWeight b j * (N : ℝ) ^ (∑ a, j a) * 1 * (N : ℝ) ^ 2 := by
        refine mul_le_mul_of_nonneg_right (mul_le_mul (mul_le_mul_of_nonneg_left hdesc
          (stirlingWeight_nonneg b j)) (categoryMonomial_le_one offspring j)
          (categoryMonomial_nonneg offspring j)
          (mul_nonneg (stirlingWeight_nonneg b j) (pow_nonneg hNnn _))) (pow_nonneg hNnn _)
    _ = stirlingWeight b j * (N : ℝ) ^ (∑ a, j a + 2) := by
        rw [pow_add]
        ring
    _ ≤ stirlingWeight b j * (N : ℝ) ^ (∑ a, b a) :=
        mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hN1 hj2) (stirlingWeight_nonneg b j)

/-- The monomial moment of the census proportions is the power moment divided by `N ^ |b|`. -/
theorem expectation_monomial_eq {H : Type*} [Fintype H] [DecidableEq H]
    (offspring : FiniteReportLaw H) (N : ℕ) (b : H → ℕ) :
    (multinomialLaw offspring N).expectation
        (fun counts ↦ ∏ a, ((counts.val a : ℝ) / N) ^ b a)
      = (∑ j ∈ subIndices b, stirlingWeight b j * (N.descFactorial (∑ a, j a) : ℝ)
          * ∏ a, offspring.mass a ^ j a) / (N : ℝ) ^ (∑ a, b a) := by
  have hpoint : ∀ counts : Counts H N, ∏ a, ((counts.val a : ℝ) / N) ^ b a
      = (∏ a, (counts.val a : ℝ) ^ b a) / (N : ℝ) ^ (∑ a, b a) := by
    intro counts
    rw [← Finset.prod_pow_eq_pow_sum, ← Finset.prod_div_distrib]
    exact Finset.prod_congr rfl fun a _ ↦ div_pow _ _ _
  calc (multinomialLaw offspring N).expectation
        (fun counts ↦ ∏ a, ((counts.val a : ℝ) / N) ^ b a)
      = (multinomialLaw offspring N).expectation
          (fun counts ↦ ∏ a, (counts.val a : ℝ) ^ b a) / (N : ℝ) ^ (∑ a, b a) := by
        simp only [FiniteReportLaw.expectation, hpoint, Finset.sum_div, mul_div_assoc]
    _ = _ := by
        rw [expectation_prod_pow]
        rfl

/-- The power moment sum separated by degree: the multi-index itself, the sub-multi-indices one
degree below it, and the rest. -/
theorem sum_subIndices_split {H : Type*} [Fintype H] [DecidableEq H] (x : H → ℝ) (N : ℕ)
    (b : H → ℕ) :
    ∑ j ∈ subIndices b, stirlingWeight b j * (N.descFactorial (∑ a, j a) : ℝ)
        * ∏ a, x a ^ j a
      = (N.descFactorial (∑ a, b a - 1) : ℝ) * firstOrderStirlingSum x b
        + ((N.descFactorial (∑ a, b a) : ℝ) * ∏ a, x a ^ b a + lowOrderStirlingSum x N b) := by
  rw [← Finset.sum_filter_add_sum_filter_not (subIndices b)
      (fun j ↦ ∑ a, j a + 1 = ∑ a, b a),
    ← Finset.sum_filter_add_sum_filter_not
      ((subIndices b).filter (fun j ↦ ¬ ∑ a, j a + 1 = ∑ a, b a))
      (fun j ↦ ∑ a, j a = ∑ a, b a)]
  refine congrArg₂ (· + ·) ?_ (congrArg₂ (· + ·) ?_ rfl)
  · rw [firstOrderStirlingSum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j hj ↦ ?_
    have hj1 : ∑ a, j a = ∑ a, b a - 1 := by
      have hsucc := (Finset.mem_filter.mp hj).2
      omega
    rw [hj1]
    ring
  · rw [Finset.sum_eq_single_of_mem b]
    · rw [stirlingWeight_self, one_mul]
    · refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨mem_subIndices_self b, ?_⟩, rfl⟩
      omega
    · intro j hj hne
      exfalso
      obtain ⟨hj', hjB⟩ := Finset.mem_filter.mp hj
      have hjP := (Finset.mem_filter.mp hj').1
      have heq := (Finset.sum_eq_sum_iff_of_le fun a _ ↦ subIndices_le hjP a).mp hjB
      exact hne (funext fun a ↦ heq a (Finset.mem_univ a))

/-- **NOTE1 (10) for monomials of degree at most four.** Under the multinomial census with `N`
draws from the category law `x`, the expected monomial of the census proportions is
`x ^ b + monomialFirstOrder x b / N` up to `(11 + 4 · totalStirlingWeight b) / N ^ 2`, uniformly
in `x`, for every multi-index `b` of degree at most four. -/
theorem abs_expectation_monomial_sub_le {H : Type*} [Fintype H] [DecidableEq H]
    (offspring : FiniteReportLaw H) (N : ℕ) (hN : 1 ≤ N) (b : H → ℕ) (hb : ∑ a, b a ≤ 4) :
    |(multinomialLaw offspring N).expectation
          (fun counts ↦ ∏ a, ((counts.val a : ℝ) / N) ^ b a)
        - ∏ a, offspring.mass a ^ b a - monomialFirstOrder offspring.mass b / N|
      ≤ (11 + 4 * totalStirlingWeight b) / (N : ℝ) ^ 2 := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hm0 := categoryMonomial_nonneg offspring b
  have hm1 := categoryMonomial_le_one offspring b
  have hF0 := firstOrderStirlingSum_nonneg offspring b
  have hF1 := firstOrderStirlingSum_le offspring b
  have hG0 := lowOrderStirlingSum_nonneg offspring N b
  have hG1 := lowOrderStirlingSum_mul_sq_le offspring N hN b
  have hT1 := abs_descFactorial_div_pow_sub_le N (∑ a, b a) hN hb
  have hT2 : |(N.descFactorial (∑ a, b a - 1) : ℝ) / (N : ℝ) ^ (∑ a, b a) - 1 / N|
        * firstOrderStirlingSum offspring.mass b
      ≤ 3 / (N : ℝ) ^ 2 * totalStirlingWeight b := by
    by_cases hB0 : ∑ a, b a = 0
    · rw [firstOrderStirlingSum_of_sum_eq_zero offspring.mass b hB0, mul_zero]
      exact mul_nonneg (by positivity) (hF0.trans hF1)
    · exact mul_le_mul (abs_descFactorial_pred_div_pow_sub_le N _ hN
        (Nat.one_le_iff_ne_zero.mpr hB0) hb) hF1 hF0 (by positivity)
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
      ≤ 11 / (N : ℝ) ^ 2 * 1 + 3 / (N : ℝ) ^ 2 * totalStirlingWeight b
        + totalStirlingWeight b / (N : ℝ) ^ 2 :=
        add_le_add (add_le_add (mul_le_mul hT1 hm1 hm0 (by positivity)) hT2) hG
    _ = (11 + 4 * totalStirlingWeight b) / (N : ℝ) ^ 2 := by ring

/-- **The first-order Stirling sum is the diagonal term of (10).** The sub-multi-indices exactly
one degree below `b` are `b` with one coordinate lowered by one, and lowering coordinate `a` has
Stirling weight `S(b_a, b_a - 1) = C(b_a, 2)`. -/
theorem firstOrderStirlingSum_eq_sum_choose {H : Type*} [Fintype H] [DecidableEq H]
    (x : H → ℝ) (b : H → ℕ) :
    firstOrderStirlingSum x b
      = ∑ a, ((b a).choose 2 : ℝ) * ∏ c, x c ^ Function.update b a (b a - 1) c := by
  have hzero : ∀ a ∈ (Finset.univ : Finset H),
      ((b a).choose 2 : ℝ) * ∏ c, x c ^ Function.update b a (b a - 1) c ≠ 0 → 1 ≤ b a := by
    intro a _ hne
    by_contra hlt
    apply hne
    have hb0 : b a = 0 := by omega
    rw [hb0]
    simp
  have hweight : ∀ a, 1 ≤ b a →
      stirlingWeight b (Function.update b a (b a - 1)) = ((b a).choose 2 : ℝ) := by
    intro a ha
    rw [stirlingWeight, ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ a)]
    have hrest : ∏ c ∈ Finset.univ.erase a,
        (Nat.stirlingSecond (b c) (Function.update b a (b a - 1) c) : ℝ) = 1 := by
      refine Finset.prod_eq_one fun c hc ↦ ?_
      rw [Function.update_of_ne (Finset.ne_of_mem_erase hc), Nat.stirlingSecond_self,
        Nat.cast_one]
    rw [hrest, mul_one, Function.update_self]
    obtain ⟨n, hn⟩ : ∃ n, b a = n + 1 := ⟨b a - 1, by omega⟩
    rw [hn, Nat.add_sub_cancel, Nat.stirlingSecond_succ_self_left]
  have hinj : ∀ a ∈ Finset.univ.filter (fun a ↦ 1 ≤ b a),
      ∀ a' ∈ Finset.univ.filter (fun a ↦ 1 ≤ b a),
        Function.update b a (b a - 1) = Function.update b a' (b a' - 1) → a = a' := by
    intro a ha a' _ heq
    by_contra hne
    have hval := congrFun heq a
    rw [Function.update_self, Function.update_of_ne hne] at hval
    have hpos := (Finset.mem_filter.mp ha).2
    omega
  have himage : (Finset.univ.filter (fun a ↦ 1 ≤ b a)).image
        (fun a ↦ Function.update b a (b a - 1))
      = (subIndices b).filter (fun j ↦ ∑ a, j a + 1 = ∑ a, b a) := by
    ext j
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨a, ha, rfl⟩
      refine ⟨Fintype.mem_piFinset.mpr fun c ↦ Finset.mem_range.mpr ?_, ?_⟩
      · by_cases hc : c = a
        · subst hc
          rw [Function.update_self]
          omega
        · rw [Function.update_of_ne hc]
          omega
      · rw [Finset.sum_update_of_mem (Finset.mem_univ a), Finset.sdiff_singleton_eq_erase,
          ← Finset.add_sum_erase Finset.univ b (Finset.mem_univ a)]
        omega
    · rintro ⟨hjP, hjsum⟩
      have hjle : ∀ c, j c ≤ b c := subIndices_le hjP
      obtain ⟨a, ha⟩ : ∃ a, j a < b a := by
        by_contra hnone
        push_neg at hnone
        have heq : ∑ c, j c = ∑ c, b c :=
          Finset.sum_congr rfl fun c _ ↦ le_antisymm (hjle c) (hnone c)
        omega
      have hj := Finset.add_sum_erase Finset.univ j (Finset.mem_univ a)
      have hb := Finset.add_sum_erase Finset.univ b (Finset.mem_univ a)
      have hle' : ∑ c ∈ Finset.univ.erase a, j c ≤ ∑ c ∈ Finset.univ.erase a, b c :=
        Finset.sum_le_sum fun c _ ↦ hjle c
      have hrest : ∑ c ∈ Finset.univ.erase a, j c = ∑ c ∈ Finset.univ.erase a, b c := by
        omega
      have hja : j a = b a - 1 := by omega
      have heqc : ∀ c ∈ Finset.univ.erase a, j c = b c :=
        (Finset.sum_eq_sum_iff_of_le fun c _ ↦ hjle c).mp hrest
      refine ⟨a, by omega, ?_⟩
      funext c
      by_cases hc : c = a
      · subst hc
        rw [Function.update_self, hja]
      · rw [Function.update_of_ne hc, heqc c (Finset.mem_erase.mpr ⟨hc, Finset.mem_univ c⟩)]
  calc firstOrderStirlingSum x b
      = ∑ j ∈ (Finset.univ.filter (fun a ↦ 1 ≤ b a)).image
            (fun a ↦ Function.update b a (b a - 1)),
          stirlingWeight b j * ∏ c, x c ^ j c := by
        rw [firstOrderStirlingSum, himage]
    _ = ∑ a ∈ Finset.univ.filter (fun a ↦ 1 ≤ b a),
          stirlingWeight b (Function.update b a (b a - 1))
            * ∏ c, x c ^ Function.update b a (b a - 1) c :=
        Finset.sum_image hinj
    _ = ∑ a ∈ Finset.univ.filter (fun a ↦ 1 ≤ b a),
          ((b a).choose 2 : ℝ) * ∏ c, x c ^ Function.update b a (b a - 1) c :=
        Finset.sum_congr rfl fun a ha ↦ by rw [hweight a (Finset.mem_filter.mp ha).2]
    _ = ∑ a, ((b a).choose 2 : ℝ) * ∏ c, x c ^ Function.update b a (b a - 1) c :=
        Finset.sum_filter_of_ne hzero

/-- **The closed form of the first-order coefficient.** The first-order coefficient of the
multinomial expansion of `x ^ b` is `Σ_a C(b_a, 2) x ^ (b - e_a) - C(|b|, 2) x ^ b`. -/
theorem monomialFirstOrder_eq_sum_choose {H : Type*} [Fintype H] [DecidableEq H]
    (x : H → ℝ) (b : H → ℕ) :
    monomialFirstOrder x b
      = ∑ a, ((b a).choose 2 : ℝ) * ∏ c, x c ^ Function.update b a (b a - 1) c
        - ((∑ a, b a).choose 2 : ℝ) * ∏ a, x a ^ b a := by
  rw [monomialFirstOrder, firstOrderStirlingSum_eq_sum_choose]

end

end Descent.Portability.MultinomialMomentExpansion
