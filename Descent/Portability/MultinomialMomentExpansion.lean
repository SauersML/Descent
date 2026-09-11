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

What is NOT proved in this module: the expansion (10) of `E f(Z / N)` for polynomials `f` of
degree at most four with its `O(N⁻²)` remainder, and the multinomial drift stage that would
replace the single-draw drift stage of the microscopic kernel. The exact power moments here are
the input both of those need.

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

end

end Descent.Portability.MultinomialMomentExpansion
