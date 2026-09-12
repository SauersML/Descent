/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Pangenome.GraphCoalescent.LeadingCoefficient

assert_below Descent.PopGen Descent.Spectral Descent.Blindness Descent.Conditionals
assert_below Descent.Portability Descent.Decision Descent.Program

/-!
# What a compressed pangenome reveals about its hidden fiber sizes

A graph built at an interface with `w` fibers of sizes `c = (c_1, …, c_w)` on `n` individuals
reports the connection time `τ_q`. Its law is determined by the connectivity cumulant `C_c(z)`
(Theorem D of the hidden-clock note), and conversely the numbers `F_k` of (D5) recover `C_c`.
The panel size `n` and the width `w` are observed. The question is which functions of the hidden
multiset `{c_1, …, c_w}` the report identifies.

## Statement

Write `K_c(u) = u^n C_c(1/u)` for the reversed cumulant (`deficitCumulant`), so that
`[u^d] K_c = [z^{n-d}] C_c`.

- **Every width.** `C_c` determines `∏_i c_i`, through the top coefficient
  `[z^{n-w+1}] C_c = 2 (∏_i c_i) (2n - w)!/(2n - 2w + 2)!` of (E1)
  (`prod_eq_of_cumulantOfSizes_eq`).
- **Two fibers.** `[u] K_c = 2 c_1 c_2` and
  `[u^2] K_c = c_1 c_2 ((c_1 - 1)^2 + (c_2 - 1)^2 + (n - 1)(n - 2))`
  (`coeff_one_deficitCumulant_pair`, `coeff_two_deficitCumulant_pair`).
- **Three fibers.** `[u^2] K_c = 2 e_3 (2n - 3)` and
  `[u^3] K_c = 2 e_3 (2n³ - 11n² + 21n - 16 - 2(n - 3) e_2 - 2 e_3)`, with `e_2, e_3` the
  elementary symmetric polynomials of `c` (`coeff_two_deficitCumulant_card_three`,
  `coeff_three_deficitCumulant_card_three`, `coeff_three_deficitCumulant_triple`). For `n ≥ 4`
  the second coefficient is affine in `e_2` with nonzero slope, so `C_c` determines `e_2` and
  `e_3`; with the common sum `e_1 = n`, the multiset of fiber sizes is determined
  (`esymm_eq_of_cumulantOfSizes_eq_three`).

## Why it matters

A study sees the graph and its connection clock, not the fibers. The theorem says that at width
three the clock is a complete invariant of the hidden sizes: no two different fiber profiles on
the same panel produce the same report law. It is not a consequence of the leading coefficient
alone: `(6, 6, 1)` and `(9, 2, 2)` on `n = 13` have the same product and are separated only by
`e_2`.

## The mechanism

`[u^d] K_c · d!` counts, with rates, the sequences of `d` mergers from the loads `c` to one
component: a hidden merger inside fiber `i` at rate `c_i (c_i - 1)` and a visible merger of `i` and
`j` at rate `c_i c_j`, fusing them into the load `c_i + c_j - 1`. This is
`LeadingCoefficient.derivative_deficitCumulant`, read one degree above the top
(`coeff_card_deficitCumulant`).

## Scope

Identifiability of the multiset is proved for `w ≤ 3`; for general `w` only the product is proved
here. The second coefficient at general width mixes the power sums `p_2, …, p_w` of the excesses
`c_i - 1`, and no counterexample is known.

## Empirical status

None. Every declaration here is a coefficient of a polynomial with rational coefficients indexed by
the partitions of a finite set, or an equality of finite multisets of natural numbers.
-/

namespace Descent.Pangenome.GraphCoalescent

open Finset Polynomial

noncomputable section

variable {ι : Type*} [DecidableEq ι]

/-! ### One degree past the top -/

/-- **One fiber.** `[u] K_{(m)} = m (m - 1)`. -/
theorem coeff_one_deficitCumulant_singleton (x : ι) (c : ι → ℕ) (hx : 1 ≤ c x) :
    (deficitCumulant {x} c).coeff 1 = (c x : ℚ) * ((c x : ℚ) - 1) := by
  have hc : ∀ i ∈ ({x} : Finset ι), 1 ≤ c i := fun i hi ↦ by
    rw [mem_singleton.mp hi]
    exact hx
  have h := congrArg (fun p ↦ p.coeff 0) (derivative_deficitCumulant {x} c hc)
  simp only [coeff_derivative, coeff_C_mul, sum_singleton, erase_singleton, sum_empty, add_zero,
    Nat.cast_zero, zero_add, mul_one] at h
  rw [h]
  by_cases hx1 : c x = 1
  · simp [hx1]
  · rw [coeff_zero_deficitCumulant _ _ (singleton_nonempty x)
      (update_pred_pos hc (mem_singleton_self x) hx1), if_pos (card_singleton x), mul_one]

/-- **One step past the top.** The coefficient of `u^w` on `w` fibers, from the derivative
identity: hidden mergers keep the fibers, visible mergers fuse two of them. -/
theorem coeff_card_deficitCumulant (T : Finset ι) (c : ι → ℕ) (hc : ∀ i ∈ T, 1 ≤ c i)
    (hT : 1 ≤ #T) :
    (deficitCumulant T c).coeff #T * (#T : ℚ) =
      ∑ i ∈ T, (c i : ℚ) * ((c i : ℚ) - 1) *
          (deficitCumulant T (Function.update c i (c i - 1))).coeff (#T - 1) +
        ∑ i ∈ T, ∑ j ∈ T.erase i, (c i : ℚ) * (c j : ℚ) *
          (deficitCumulant (T.erase j) (Function.update c i (c i + c j - 1))).coeff (#T - 1) := by
  have h := congrArg (fun p ↦ p.coeff (#T - 1)) (derivative_deficitCumulant T c hc)
  simp only [coeff_derivative, finset_sum_coeff, coeff_add, coeff_C_mul] at h
  have hindex : #T - 1 + 1 = #T := by omega
  have hcast : ((#T - 1 : ℕ) : ℚ) + 1 = (#T : ℚ) := by
    rw [Nat.cast_sub hT]
    push_cast
    ring
  rw [hindex, hcast] at h
  exact h

/-! ### Two fibers -/

theorem pair_erase_left {i j : ι} (hij : i ≠ j) : ({i, j} : Finset ι).erase i = {j} :=
  erase_insert (notMem_singleton.mpr hij)

theorem pair_erase_right {i j : ι} (hij : i ≠ j) : ({i, j} : Finset ι).erase j = {i} := by
  rw [erase_insert_of_ne hij, erase_singleton, insert_empty]

theorem pair_pos {i j : ι} {c : ι → ℕ} (hi : 1 ≤ c i) (hj : 1 ≤ c j) :
    ∀ k ∈ ({i, j} : Finset ι), 1 ≤ c k := by
  intro k hk
  rcases mem_insert.mp hk with rfl | hk
  · exact hi
  · rw [mem_singleton.mp hk]
    exact hj

/-- **Two fibers, the top.** `[u] K_{(c_i, c_j)} = 2 c_i c_j`. -/
theorem coeff_one_deficitCumulant_pair {i j : ι} (hij : i ≠ j) (c : ι → ℕ) (hi : 1 ≤ c i)
    (hj : 1 ≤ c j) : (deficitCumulant {i, j} c).coeff 1 = 2 * (c i : ℚ) * (c j : ℚ) := by
  have h := coeff_deficitCumulant_recursion {i, j} c (pair_pos hi hj) (by rw [card_pair hij])
  rw [sum_pair hij, pair_erase_left hij, pair_erase_right hij, sum_singleton, sum_singleton,
    card_pair hij, pair_erase_left hij, pair_erase_right hij,
    show (2 : ℕ) - 2 = 0 from rfl, show (2 : ℕ) - 1 = 1 from rfl] at h
  have hone : ∀ (k : ι) (f : ι → ℕ), 1 ≤ f k → (deficitCumulant {k} f).coeff 0 = 1 := by
    intro k f hf
    have hpos : ∀ x ∈ ({k} : Finset ι), 1 ≤ f x := fun x hx ↦ by
      rw [mem_singleton.mp hx]
      exact hf
    rw [coeff_zero_deficitCumulant _ _ (singleton_nonempty k) hpos, if_pos (card_singleton k)]
  have hfi : 1 ≤ Function.update c i (c i + c j - 1) i := by
    rw [Function.update_self]
    omega
  have hfj : 1 ≤ Function.update c j (c j + c i - 1) j := by
    rw [Function.update_self]
    omega
  rw [hone i _ hfi, hone j _ hfj] at h
  push_cast at h
  linear_combination h

/-- **Two fibers, one past the top.**
`[u^2] K_{(c_i, c_j)} = c_i c_j ((c_i - 1)^2 + (c_j - 1)^2 + (n - 1)(n - 2))`. -/
theorem coeff_two_deficitCumulant_pair {i j : ι} (hij : i ≠ j) (c : ι → ℕ) (hi : 1 ≤ c i)
    (hj : 1 ≤ c j) :
    (deficitCumulant {i, j} c).coeff 2 = (c i : ℚ) * (c j : ℚ) *
      (((c i : ℚ) - 1) ^ 2 + ((c j : ℚ) - 1) ^ 2 +
        ((c i : ℚ) + (c j : ℚ) - 1) * ((c i : ℚ) + (c j : ℚ) - 2)) := by
  have h := coeff_card_deficitCumulant {i, j} c (pair_pos hi hj) (by rw [card_pair hij]; omega)
  rw [sum_pair hij, sum_pair hij, pair_erase_left hij, pair_erase_right hij, sum_singleton,
    sum_singleton, card_pair hij, pair_erase_left hij, pair_erase_right hij,
    show (2 : ℕ) - 1 = 1 from rfl] at h
  have hpred : ∀ (k l : ι), k ≠ l → 1 ≤ c k → 1 ≤ c l →
      (c k : ℚ) * ((c k : ℚ) - 1) * (deficitCumulant {k, l} (Function.update c k (c k - 1))).coeff 1
        = 2 * (c k : ℚ) * ((c k : ℚ) - 1) ^ 2 * (c l : ℚ) := by
    intro k l hkl hk hl
    by_cases hk1 : c k = 1
    · simp [hk1]
    · have hfk : 1 ≤ Function.update c k (c k - 1) k := by
        rw [Function.update_self]
        omega
      have hfl : 1 ≤ Function.update c k (c k - 1) l := by
        rw [Function.update_of_ne hkl.symm]
        exact hl
      rw [coeff_one_deficitCumulant_pair hkl (Function.update c k (c k - 1)) hfk hfl,
        Function.update_self, Function.update_of_ne hkl.symm, Nat.cast_sub hk]
      push_cast
      ring
  rw [hpred i j hij hi hj, pair_comm i j, hpred j i hij.symm hj hi, pair_comm j i,
    coeff_one_deficitCumulant_singleton, coeff_one_deficitCumulant_singleton,
    Function.update_self, Function.update_self] at h
  · push_cast [Nat.cast_sub (show 1 ≤ c i + c j by omega),
      Nat.cast_sub (show 1 ≤ c j + c i by omega)] at h
    linear_combination h / 2
  · rw [Function.update_self]
    omega
  · rw [Function.update_self]
    omega

/-- **Two fibers, the top, symmetric form.** `[u] K_c = 2 ∏_i c_i`. -/
theorem coeff_one_deficitCumulant_card_two {T : Finset ι} (hT : #T = 2) (c : ι → ℕ)
    (hc : ∀ i ∈ T, 1 ≤ c i) : (deficitCumulant T c).coeff 1 = 2 * ∏ k ∈ T, (c k : ℚ) := by
  obtain ⟨x, y, hxy, rfl⟩ := card_eq_two.mp hT
  rw [coeff_one_deficitCumulant_pair hxy c (hc x (mem_insert_self x {y}))
    (hc y (mem_insert_of_mem (mem_singleton_self y))), prod_pair hxy]
  ring

/-- **Two fibers, one past the top, symmetric form.**
`[u^2] K_c = (∏_i c_i) (∑_i (c_i - 1)^2 + (n - 1)(n - 2))`. -/
theorem coeff_two_deficitCumulant_card_two {T : Finset ι} (hT : #T = 2) (c : ι → ℕ)
    (hc : ∀ i ∈ T, 1 ≤ c i) :
    (deficitCumulant T c).coeff 2 = (∏ k ∈ T, (c k : ℚ)) *
      (∑ k ∈ T, ((c k : ℚ) - 1) ^ 2 +
        (∑ k ∈ T, (c k : ℚ) - 1) * (∑ k ∈ T, (c k : ℚ) - 2)) := by
  obtain ⟨x, y, hxy, rfl⟩ := card_eq_two.mp hT
  rw [coeff_two_deficitCumulant_pair hxy c (hc x (mem_insert_self x {y}))
    (hc y (mem_insert_of_mem (mem_singleton_self y))), prod_pair hxy, sum_pair hxy, sum_pair hxy]

/-! ### Three fibers -/

/-- A hidden merger in fiber `i` replaces the factor `c_i` of the product by `c_i - 1`. -/
theorem prod_update_pred {T : Finset ι} {c : ι → ℕ} {i : ι} (hi : i ∈ T) (hci : 1 ≤ c i) :
    (c i : ℚ) * ∏ k ∈ T, (Function.update c i (c i - 1) k : ℚ) =
      ((c i : ℚ) - 1) * ∏ k ∈ T, (c k : ℚ) := by
  rw [prod_eq_mul_prod_diff_singleton hi, prod_eq_mul_prod_diff_singleton hi (fun k ↦ (c k : ℚ)),
    Function.update_self]
  have hrest : ∏ k ∈ T \ {i}, (Function.update c i (c i - 1) k : ℚ) =
      ∏ k ∈ T \ {i}, (c k : ℚ) :=
    prod_congr rfl fun k hk ↦ by
      rw [Function.update_of_ne fun hki ↦ (mem_sdiff.mp hk).2 (mem_singleton.mpr hki)]
  rw [hrest, Nat.cast_sub hci, Nat.cast_one]
  ring

/-- A hidden merger lowers the total size by one. -/
theorem sum_update_pred {T : Finset ι} {c : ι → ℕ} {i : ι} (hi : i ∈ T) (hci : 1 ≤ c i) :
    ∑ k ∈ T, (Function.update c i (c i - 1) k : ℚ) = ∑ k ∈ T, (c k : ℚ) - 1 := by
  rw [sum_eq_add_sum_diff_singleton hi, sum_eq_add_sum_diff_singleton hi (fun k ↦ (c k : ℚ)),
    Function.update_self]
  have hrest : ∑ k ∈ T \ {i}, (Function.update c i (c i - 1) k : ℚ) =
      ∑ k ∈ T \ {i}, (c k : ℚ) :=
    sum_congr rfl fun k hk ↦ by
      rw [Function.update_of_ne fun hki ↦ (mem_sdiff.mp hk).2 (mem_singleton.mpr hki)]
  rw [hrest, Nat.cast_sub hci, Nat.cast_one]
  ring

/-- Fusing fibers `i` and `j` changes the sum of squared excesses by `2 (c_i - 1)(c_j - 1)`. -/
theorem sum_sq_fused {T : Finset ι} {c : ι → ℕ} {i j : ι} (hi : i ∈ T.erase j) (hj : j ∈ T)
    (hci : 1 ≤ c i) :
    ∑ k ∈ T.erase j, ((Function.update c i (c i + c j - 1) k : ℚ) - 1) ^ 2 =
      ∑ k ∈ T, ((c k : ℚ) - 1) ^ 2 - ((c i : ℚ) - 1) ^ 2 - ((c j : ℚ) - 1) ^ 2 +
        ((c i : ℚ) + (c j : ℚ) - 2) ^ 2 := by
  rw [sum_eq_add_sum_diff_singleton hi, ← add_sum_erase T (fun k ↦ ((c k : ℚ) - 1) ^ 2) hj,
    sum_eq_add_sum_diff_singleton hi (fun k ↦ ((c k : ℚ) - 1) ^ 2), Function.update_self]
  have hrest : ∑ k ∈ T.erase j \ {i}, ((Function.update c i (c i + c j - 1) k : ℚ) - 1) ^ 2 =
      ∑ k ∈ T.erase j \ {i}, ((c k : ℚ) - 1) ^ 2 :=
    sum_congr rfl fun k hk ↦ by
      rw [Function.update_of_ne fun hki ↦ (mem_sdiff.mp hk).2 (mem_singleton.mpr hki)]
  rw [hrest, Nat.cast_sub (by omega), Nat.cast_add, Nat.cast_one]
  ring

/-- Fusing fibers lowers the total size by one, in `ℚ`. -/
theorem sum_fused_sizes_cast {T : Finset ι} {c : ι → ℕ} {i j : ι} (hi : i ∈ T.erase j)
    (hj : j ∈ T) (hci : 1 ≤ c i) :
    ∑ k ∈ T.erase j, (Function.update c i (c i + c j - 1) k : ℚ) = ∑ k ∈ T, (c k : ℚ) - 1 := by
  have hsum := sum_fused_sizes hi hj hci
  have hn : 1 ≤ ∑ k ∈ T, c k := (hci.trans (single_le_sum (fun _ _ ↦ Nat.zero_le _)
    (mem_of_mem_erase hi)))
  rw [← Nat.cast_sum, hsum, Nat.cast_sub hn, Nat.cast_sum, Nat.cast_one]

/-- **Three fibers, the top.** `[u^2] K_c = 2 e_3 (2n - 3)`. -/
theorem coeff_two_deficitCumulant_card_three {T : Finset ι} (hT : #T = 3) (c : ι → ℕ)
    (hc : ∀ i ∈ T, 1 ≤ c i) :
    (deficitCumulant T c).coeff 2 = 2 * (∏ k ∈ T, (c k : ℚ)) * (2 * ∑ k ∈ T, (c k : ℚ) - 3) := by
  have hn : 3 ≤ ∑ k ∈ T, c k := by
    have := card_le_sum_sizes hc
    omega
  have htop := coeff_deficitCumulant_top 2 T c hT hc
  rw [hT, show (3 : ℕ) - 1 = 2 from rfl] at htop
  rw [htop, leadingCoefficient, hT,
    show 2 * ∑ k ∈ T, c k - 3 = (2 * ∑ k ∈ T, c k - 4) + 1 by omega,
    show 2 * ∑ k ∈ T, c k - 2 * 3 + 2 = 2 * ∑ k ∈ T, c k - 4 by omega, Nat.factorial_succ]
  have hfact : ((2 * ∑ k ∈ T, c k - 4).factorial : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.factorial_pos _).ne'
  push_cast [Nat.cast_sub (show 4 ≤ 2 * ∑ k ∈ T, c k by omega)]
  field_simp
  ring

/-- **Three fibers, one past the top, symmetric form.** Hidden mergers contribute
`2 (2n - 5) (c_i - 1)^2 ∏ c`; the visible merger of `i` and `j` contributes `(c_i + c_j - 1) ∏ c`
times the second coefficient of the fused pair. -/
theorem coeff_three_deficitCumulant_card_three {T : Finset ι} (hT : #T = 3) (c : ι → ℕ)
    (hc : ∀ i ∈ T, 1 ≤ c i) :
    (deficitCumulant T c).coeff 3 * 3 = (∏ k ∈ T, (c k : ℚ)) *
      (2 * (2 * ∑ k ∈ T, (c k : ℚ) - 5) * ∑ k ∈ T, ((c k : ℚ) - 1) ^ 2 +
        ∑ i ∈ T, ∑ j ∈ T.erase i, ((c i : ℚ) + (c j : ℚ) - 1) *
          (∑ k ∈ T, ((c k : ℚ) - 1) ^ 2 - ((c i : ℚ) - 1) ^ 2 - ((c j : ℚ) - 1) ^ 2 +
            ((c i : ℚ) + (c j : ℚ) - 2) ^ 2 +
            (∑ k ∈ T, (c k : ℚ) - 2) * (∑ k ∈ T, (c k : ℚ) - 3))) := by
  have h := coeff_card_deficitCumulant T c hc (by omega)
  rw [hT, show (3 : ℕ) - 1 = 2 from rfl] at h
  have hA : ∀ i ∈ T, (c i : ℚ) * ((c i : ℚ) - 1) *
      (deficitCumulant T (Function.update c i (c i - 1))).coeff 2 =
        (∏ k ∈ T, (c k : ℚ)) * (2 * (2 * ∑ k ∈ T, (c k : ℚ) - 5)) * ((c i : ℚ) - 1) ^ 2 := by
    intro i hi
    by_cases hci : c i = 1
    · simp [hci]
    · rw [coeff_two_deficitCumulant_card_three hT _ (update_pred_pos hc hi hci),
        sum_update_pred hi (hc i hi)]
      linear_combination (2 * ((c i : ℚ) - 1) * (2 * ∑ k ∈ T, (c k : ℚ) - 5)) *
        prod_update_pred hi (hc i hi)
  have hB : ∀ i ∈ T, ∀ j ∈ T.erase i, (c i : ℚ) * (c j : ℚ) *
      (deficitCumulant (T.erase j) (Function.update c i (c i + c j - 1))).coeff 2 =
        (∏ k ∈ T, (c k : ℚ)) * (((c i : ℚ) + (c j : ℚ) - 1) *
          (∑ k ∈ T, ((c k : ℚ) - 1) ^ 2 - ((c i : ℚ) - 1) ^ 2 - ((c j : ℚ) - 1) ^ 2 +
            ((c i : ℚ) + (c j : ℚ) - 2) ^ 2 +
            (∑ k ∈ T, (c k : ℚ) - 2) * (∑ k ∈ T, (c k : ℚ) - 3))) := by
    intro i hi j hj
    have hjT : j ∈ T := mem_of_mem_erase hj
    have hij : i ∈ T.erase j := mem_erase.mpr ⟨(ne_of_mem_erase hj).symm, hi⟩
    rw [coeff_two_deficitCumulant_card_two (by rw [card_erase_of_mem hjT, hT]) _
        (update_fuse_pos hc hi hjT), sum_sq_fused hij hjT (hc i hi),
      sum_fused_sizes_cast hij hjT (hc i hi)]
    linear_combination (∑ k ∈ T, ((c k : ℚ) - 1) ^ 2 - ((c i : ℚ) - 1) ^ 2 -
        ((c j : ℚ) - 1) ^ 2 + ((c i : ℚ) + (c j : ℚ) - 2) ^ 2 +
        (∑ k ∈ T, (c k : ℚ) - 2) * (∑ k ∈ T, (c k : ℚ) - 3)) *
      prod_fused_sizes hij hjT (hc i hi)
  rw [sum_congr rfl hA, sum_congr rfl fun i hi ↦ sum_congr rfl (hB i hi)] at h
  simp only [← mul_sum] at h
  push_cast at h
  rw [h]
  ring

/-- **Three fibers, one past the top, in elementary symmetric polynomials.**
`[u^3] K_c = 2 e_3 (2n³ - 11n² + 21n - 16 - 2(n - 3) e_2 - 2 e_3)`. -/
theorem coeff_three_deficitCumulant_triple {x y z : ι} (hxy : x ≠ y) (hxz : x ≠ z)
    (hyz : y ≠ z) (c : ι → ℕ) (hc : ∀ i ∈ ({x, y, z} : Finset ι), 1 ≤ c i) :
    (deficitCumulant {x, y, z} c).coeff 3 =
      2 * ((c x : ℚ) * c y * c z) *
        (2 * ((c x : ℚ) + c y + c z) ^ 3 - 11 * ((c x : ℚ) + c y + c z) ^ 2 +
          21 * ((c x : ℚ) + c y + c z) - 16 -
          2 * (((c x : ℚ) + c y + c z) - 3) * ((c x : ℚ) * c y + c x * c z + c y * c z) -
          2 * ((c x : ℚ) * c y * c z)) := by
  have hT : #({x, y, z} : Finset ι) = 3 := card_eq_three.mpr ⟨x, y, z, hxy, hxz, hyz, rfl⟩
  have h := coeff_three_deficitCumulant_card_three hT c hc
  have hx : x ∉ ({y, z} : Finset ι) := by simp [hxy, hxz]
  have ex : ({x, y, z} : Finset ι).erase x = {y, z} := erase_insert hx
  have ey : ({x, y, z} : Finset ι).erase y = {x, z} := by
    rw [erase_insert_of_ne hxy, erase_insert (notMem_singleton.mpr hyz)]
  have ez : ({x, y, z} : Finset ι).erase z = {x, y} := by
    rw [erase_insert_of_ne hxz, erase_insert_of_ne hyz, erase_singleton, insert_empty]
  simp only [sum_insert hx, sum_pair hyz, prod_insert hx, prod_pair hyz, ex, ey, ez,
    sum_pair hxz, sum_pair hxy] at h
  linear_combination h / 3

/-! ### Identifiability -/

/-- **Every width: the report determines the product of the fiber sizes.** Two interfaces with
the same number `w ≥ 2` of fibers on the same panel size and one connectivity cumulant have the
same `∏_i c_i`.

Assumes: every fiber size is positive, the widths and panel sizes agree, and `w ≥ 2`. -/
theorem prod_eq_of_cumulantOfSizes_eq {κ : Type*} [DecidableEq κ] {T : Finset ι}
    {T' : Finset κ} {c : ι → ℕ} {c' : κ → ℕ} (hc : ∀ i ∈ T, 1 ≤ c i)
    (hc' : ∀ i ∈ T', 1 ≤ c' i) (hw : #T = #T') (hw2 : 2 ≤ #T)
    (hn : ∑ i ∈ T, c i = ∑ i ∈ T', c' i) (hC : cumulantOfSizes T c = cumulantOfSizes T' c') :
    ∏ i ∈ T, c i = ∏ i ∈ T', c' i := by
  have h1 := coeff_cumulantOfSizes T c hw2 hc
  have h2 := coeff_cumulantOfSizes T' c' (hw ▸ hw2) hc'
  rw [hC, hn, hw] at h1
  have hL := h1.symm.trans h2
  simp only [leadingCoefficient, hn, hw] at hL
  have hf1 : ((2 * ∑ i ∈ T', c' i - #T').factorial : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.factorial_pos _).ne'
  have hf2 : ((2 * ∑ i ∈ T', c' i - 2 * #T' + 2).factorial : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.factorial_pos _).ne'
  rw [div_left_inj' hf2, mul_left_inj' hf1, mul_right_inj' two_ne_zero] at hL
  exact_mod_cast hL

/-- **Three fibers: the report determines `e_2` and `e_3` of the fiber sizes.** Two interfaces
with three fibers on the same panel size `n ≥ 4` and one connectivity cumulant have the same
product and the same sum of pairwise products of fiber sizes; with the common sum `n`, the three
elementary symmetric polynomials agree, so the multisets of fiber sizes agree.

Assumes: every fiber size is positive, the panel sizes agree, and `n ≥ 4`. -/
theorem esymm_eq_of_cumulantOfSizes_eq_three {κ : Type*} [DecidableEq κ] {x y z : ι}
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) {x' y' z' : κ} (hxy' : x' ≠ y') (hxz' : x' ≠ z')
    (hyz' : y' ≠ z') {c : ι → ℕ} {c' : κ → ℕ} (hc : ∀ i ∈ ({x, y, z} : Finset ι), 1 ≤ c i)
    (hc' : ∀ i ∈ ({x', y', z'} : Finset κ), 1 ≤ c' i)
    (hn : c x + c y + c z = c' x' + c' y' + c' z') (hn4 : 4 ≤ c x + c y + c z)
    (hC : cumulantOfSizes {x, y, z} c = cumulantOfSizes {x', y', z'} c') :
    c x * c y * c z = c' x' * c' y' * c' z' ∧
      c x * c y + c x * c z + c y * c z = c' x' * c' y' + c' x' * c' z' + c' y' * c' z' := by
  have hx : x ∉ ({y, z} : Finset ι) := by simp [hxy, hxz]
  have hx' : x' ∉ ({y', z'} : Finset κ) := by simp [hxy', hxz']
  have hsum : ∑ i ∈ ({x, y, z} : Finset ι), c i = c x + c y + c z := by
    rw [sum_insert hx, sum_pair hyz, add_assoc]
  have hsum' : ∑ i ∈ ({x', y', z'} : Finset κ), c' i = c' x' + c' y' + c' z' := by
    rw [sum_insert hx', sum_pair hyz', add_assoc]
  have hcard : #({x, y, z} : Finset ι) = 3 := card_eq_three.mpr ⟨x, y, z, hxy, hxz, hyz, rfl⟩
  have hcard' : #({x', y', z'} : Finset κ) = 3 :=
    card_eq_three.mpr ⟨x', y', z', hxy', hxz', hyz', rfl⟩
  have hprod := prod_eq_of_cumulantOfSizes_eq hc hc' (hcard.trans hcard'.symm) (by omega)
    (by rw [hsum, hsum', hn]) hC
  rw [prod_insert hx, prod_pair hyz, prod_insert hx', prod_pair hyz', ← mul_assoc,
    ← mul_assoc] at hprod
  refine ⟨hprod, ?_⟩
  have h1 := map_cumulantOfSizes _ c hc
  have h2 := map_cumulantOfSizes _ c' hc'
  rw [hC, h2, hsum, hsum', ← hn] at h1
  have h3 := congrArg (fun p ↦ p.coeff (c x + c y + c z - 3)) h1
  simp only [coeff_reflect, revAt_le (show c x + c y + c z - 3 ≤ c x + c y + c z by omega),
    show c x + c y + c z - (c x + c y + c z - 3) = 3 by omega] at h3
  rw [coeff_three_deficitCumulant_triple hxy' hxz' hyz' c' hc',
    coeff_three_deficitCumulant_triple hxy hxz hyz c hc] at h3
  have hn' : ((c' x' : ℚ) + c' y' + c' z') = (c x : ℚ) + c y + c z := by exact_mod_cast hn.symm
  have hp' : ((c' x' : ℚ) * c' y' * c' z') = (c x : ℚ) * c y * c z := by
    exact_mod_cast hprod.symm
  rw [hn', hp'] at h3
  have hcx : 0 < c x := hc x (mem_insert_self x _)
  have hcy : 0 < c y := hc y (mem_insert_of_mem (mem_insert_self y _))
  have hcz : 0 < c z := hc z (mem_insert_of_mem (mem_insert_of_mem (mem_singleton_self z)))
  have hpos : (0 : ℚ) < (c x : ℚ) * c y * c z :=
    mul_pos (mul_pos (by exact_mod_cast hcx) (by exact_mod_cast hcy)) (by exact_mod_cast hcz)
  have hn3 : (0 : ℚ) < (c x : ℚ) + c y + c z - 3 := by
    have : (4 : ℚ) ≤ (c x : ℚ) + c y + c z := by exact_mod_cast hn4
    linarith
  have hkey : (4 * ((c x : ℚ) * c y * c z) * ((c x : ℚ) + c y + c z - 3)) *
      (((c x : ℚ) * c y + c x * c z + c y * c z) -
        ((c' x' : ℚ) * c' y' + c' x' * c' z' + c' y' * c' z')) = 0 := by
    linear_combination h3
  rcases mul_eq_zero.mp hkey with hzero | hzero
  · exact absurd hzero (mul_pos (mul_pos (by norm_num) hpos) hn3).ne'
  · exact_mod_cast sub_eq_zero.mp hzero

end

end Descent.Pangenome.GraphCoalescent
