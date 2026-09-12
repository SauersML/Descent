/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Pangenome.GraphCoalescent.ConnectivityCumulant
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Degree.Lemmas

assert_below Descent.PopGen Descent.Spectral Descent.Blindness Descent.Conditionals
assert_below Descent.Portability Descent.Decision Descent.Program

/-!
# Theorem E: the leading coefficient of the connectivity cumulant

The hidden-clock note (§7, Theorem E) gives the top coefficient of the connectivity cumulant of
fibers of sizes `c_1, …, c_w` with `n = ∑ c_i` and `w ≥ 2`:

  (E1)  `[z^{n - w + 1}] C_c(z) = 2 (∏_i c_i) (2n - w)! / (2n - 2w + 2)!`.

`ConnectivityCumulantDegree` proves that no higher coefficient survives; this module proves
(E1) for the corpus polynomial `cumulantOfSizes` of `ConnectivityCumulant`, which is the note's
(D2) over the partitions of the fiber set with the Lah polynomials of `LahWeights`, for every
finite fiber set with `w ≥ 2` fibers and every positive fiber size (`coeff_cumulantOfSizes`).
`coeff_connectivityCumulant_top` reads it at an interface, through
`connectivityCumulant_eq_cumulantOfSizes`. `leadingCoefficient` is the right-hand side of (E1).

The proof does not pass through the ranked-history law of the note. It reads the cumulant from
its top degree. `deficitPolynomial m` is `a_m(u) = ∑_{d < m} L(m, m − d) u^d`, the Lah polynomial
`A_m(z) = z^m a_m(1/z)` of `LahWeights` reflected (`reflect_deficitPolynomial`, derived from
`lahNumber_mul_factorial`), and `deficitCumulant` is the same Möbius sum with `a` in place of `A`,
so that `C_c(z) = z^n K_c(1/z)` (`map_cumulantOfSizes`) and (E1) is the coefficient of
`u^{w - 1}` in `K_c`.

1. The Lah derivative. `derivative_deficitPolynomial` is `a_m' = m (m − 1) a_{m − 1}`: choosing
   two individuals of a block and merging them.
2. The cumulant derivative. `derivative_deficitCumulant` is
   `K_c' = ∑_i c_i (c_i − 1) K_{c − e_i} + ∑_{i ≠ j} c_i c_j K_{c^{(ij)}}`, where `c^{(ij)}`
   fuses fibers `i` and `j` into one fiber of size `c_i + c_j − 1`. The fused term is the
   insertion bijection of `LahWeights`: partitions of the fibers with `i` and `j` in one block
   are the partitions of the other fibers with `j` inserted into the block of `i`
   (`sum_part_eq_part`), and the block sizes match (`fused_product`).
3. The vanishing order. `coeff_zero_deficitCumulant` is the Möbius identity
   `sum_mobiusCoefficient_finpartition` of `ConnectivityCumulant`, and the derivative identity
   carries it upward: `K_c` has no term of degree below `w − 1`
   (`coeff_deficitCumulant_eq_zero`), which is the degree bound `n − w + 1` of (D3) again, on the
   side of the Möbius sum.
4. The recursion. Reading the derivative identity at `u^{w − 2}` leaves only the fused terms:
   `(w − 1) L_w(c) = ∑_{i ≠ j} c_i c_j L_{w − 1}(c^{(ij)})` (`coeff_deficitCumulant_recursion`),
   the note's history recursion for `H_w`, obtained here from the Möbius sum.
5. The closed form. `sum_pairs_sizes` gives `∑_{i ≠ j} (c_i + c_j − 1) = (w − 1)(2n − w)`, and
   `sum_pairs_leadingCoefficient` shows that (E1) solves the recursion from `L_1 = 1`
   (`coeff_deficitCumulant_top`).

Scope. Not formalized here: the short-time law (E2), `Pr(τ_q ≤ t) = H_w(c) t^{w-1}/(w-1)! +
O(t^w)`, which needs the stopping law (D4)-(D5); the history sum `H_w(c)` of the note is not
defined, only the recursion it obeys. The table rows `(1,2)`, `(1,3)`, `(2,2)` and `(2,2,2)` are
checked against (E1) in `validation/code/CheckLeadingCoefficient.lean`.

## Empirical status

None. The bodies here are finite combinatorics on partitions of a finite set and algebra of
polynomials with rational coefficients, so no measurement can bear on them.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Pangenome.GraphCoalescent

open Finset Polynomial

noncomputable section

variable {ι : Type*} [DecidableEq ι]

/-! ## The cumulant read from its top degree -/

/-- The Lah weight counted from the top degree: `L(m, m − d) = C(m − 1, d) · m (m − 1) ⋯ (m − d + 1)`,
the weighted number of partitions of `m` individuals with `m − d` blocks. -/
def deficitWeight (m d : ℕ) : ℕ :=
  (m - 1).choose d * m.descFactorial d

/-- **NOTE (D1) from its top degree.** `a_m(u) = ∑_{d < m} L(m, m − d) u^d`, so that the Lah
polynomial is `A_m(z) = z^m a_m(1 / z)`. -/
def deficitPolynomial (m : ℕ) : ℚ[X] :=
  ∑ d ∈ range m, C (deficitWeight m d : ℚ) * X ^ d

/-- **NOTE (D2) from its top degree.** `K_c(u) = ∑_ρ μ(ρ, ⊤) ∏_{U ∈ ρ} a_{c(U)}(u)`, the Möbius sum
of the connectivity cumulant with `a` in place of `A`, so that `C_c(z) = z^n K_c(1 / z)`. -/
def deficitCumulant (T : Finset ι) (c : ι → ℕ) : ℚ[X] :=
  ∑ ρ : Finpartition T, C (mobiusCoefficient #ρ.parts : ℚ) *
    ∏ U ∈ ρ.parts, deficitPolynomial (∑ i ∈ U, c i)

/-- **NOTE (E1), the value.** `2 (∏_i c_i) (2n − w)! / (2n − 2w + 2)!` for the fibers `T` of sizes
`c`, with `n = ∑_i c_i` and `w = |T|`. -/
def leadingCoefficient (T : Finset ι) (c : ι → ℕ) : ℚ :=
  2 * (∏ i ∈ T, (c i : ℚ)) * ((2 * (∑ i ∈ T, c i) - #T).factorial : ℚ) /
    ((2 * (∑ i ∈ T, c i) - 2 * #T + 2).factorial : ℚ)

/-- The coefficients of `a_m`. -/
theorem deficitPolynomial_coeff (m d : ℕ) :
    (deficitPolynomial m).coeff d = if d < m then (deficitWeight m d : ℚ) else 0 := by
  simp [deficitPolynomial, finset_sum_coeff, coeff_C_mul, coeff_X_pow]

/-- `a_m(0) = 1` for `m ≥ 1`: one partition has every individual in its own block. -/
theorem deficitPolynomial_coeff_zero {m : ℕ} (hm : 1 ≤ m) : (deficitPolynomial m).coeff 0 = 1 := by
  rw [deficitPolynomial_coeff, if_pos (show 0 < m by omega)]
  simp [deficitWeight]

/-- `a_m` has degree at most `m`. -/
theorem natDegree_deficitPolynomial_le (m : ℕ) : (deficitPolynomial m).natDegree ≤ m := by
  rw [natDegree_le_iff_coeff_eq_zero]
  intro N hN
  rw [deficitPolynomial_coeff, if_neg (show ¬ N < m by omega)]

/-- **The Lah derivative.** `a_m' = m (m − 1) a_{m − 1}`: merging an ordered pair of individuals of
one block shortens that block by one. -/
theorem derivative_deficitPolynomial (m : ℕ) :
    derivative (deficitPolynomial m) =
      C ((m : ℚ) * ((m : ℚ) - 1)) * deficitPolynomial (m - 1) := by
  ext d
  rw [coeff_derivative, coeff_C_mul, deficitPolynomial_coeff, deficitPolynomial_coeff]
  rcases m with _ | m
  · simp
  rcases m with _ | k
  · simp
  by_cases hd : d < k + 1
  · rw [if_pos (show d + 1 < k + 1 + 1 by omega), if_pos (show d < k + 1 + 1 - 1 by omega)]
    have hchoose : ((k : ℚ) + 1) * (k.choose d : ℚ) =
        ((k + 1).choose (d + 1) : ℚ) * ((d : ℚ) + 1) := by
      exact_mod_cast Nat.succ_mul_choose_eq k d
    simp only [deficitWeight, Nat.add_sub_cancel, Nat.succ_descFactorial_succ]
    push_cast
    linear_combination (-((k : ℚ) + 1 + 1) * ((k + 1).descFactorial d : ℚ)) * hchoose
  · rw [if_neg (show ¬ d + 1 < k + 1 + 1 by omega), if_neg (show ¬ d < k + 1 + 1 - 1 by omega)]
    simp

/-- **`a_m` is the reflected Lah polynomial.** `z^m a_m(1 / z) = A_m(z)` for `m ≥ 1`, from the
closed form `L(m, j) j! = m! C(m − 1, j − 1)` of `LahWeights`. -/
theorem reflect_deficitPolynomial {m : ℕ} (hm : 1 ≤ m) :
    reflect m (deficitPolynomial m) = lahPolynomial ℚ m := by
  ext j
  rw [coeff_reflect, deficitPolynomial_coeff, coeff_lahPolynomial]
  by_cases hjm : j ≤ m
  · rw [revAt_le hjm]
    by_cases hj : 1 ≤ j
    · rw [if_pos (show m - j < m by omega)]
      have hclosed := lahNumber_mul_factorial m j hm hj
      have hdesc := Nat.factorial_mul_descFactorial (show m - j ≤ m by omega)
      rw [show m - (m - j) = j by omega] at hdesc
      have hchoose : (m - 1).choose (m - j) = (m - 1).choose (j - 1) := by
        rw [show m - j = m - 1 - (j - 1) by omega, Nat.choose_symm (by omega)]
      have hweight : deficitWeight m (m - j) = lahNumber m j := by
        unfold deficitWeight
        rw [hchoose]
        apply Nat.eq_of_mul_eq_mul_right (Nat.factorial_pos j)
        rw [hclosed, ← hdesc]
        ring
      rw [hweight]
    · rw [if_neg (show ¬ m - j < m by omega)]
      obtain rfl : j = 0 := by omega
      obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
      rw [lahNumber_succ_zero]
      simp
  · rw [show revAt m j = j from if_neg hjm, if_neg (show ¬ j < m by omega),
      lahNumber_eq_zero_of_lt (by omega)]
    simp

/-- Reflection is additive over finite sums. -/
theorem reflect_finset_sum {κ : Type*} (t : Finset κ) (f : κ → ℚ[X]) (N : ℕ) :
    reflect N (∑ b ∈ t, f b) = ∑ b ∈ t, reflect N (f b) := by
  classical
  induction t using Finset.induction_on with
  | empty =>
      ext i
      simp [coeff_reflect]
  | insert b t hb ih =>
      rw [sum_insert hb, reflect_add, ih, sum_insert hb]

/-- The block products of `a` reflect to the block products of `A`. -/
theorem reflect_prod_deficitPolynomial (t : Finset (Finset ι)) (c : ι → ℕ)
    (ht : ∀ U ∈ t, 1 ≤ ∑ i ∈ U, c i) :
    reflect (∑ U ∈ t, ∑ i ∈ U, c i) (∏ U ∈ t, deficitPolynomial (∑ i ∈ U, c i)) =
      ∏ U ∈ t, lahPolynomial ℚ (∑ i ∈ U, c i) := by
  induction t using Finset.induction_on with
  | empty =>
      ext i
      rw [sum_empty, prod_empty, prod_empty, coeff_reflect]
      rcases i with _ | i
      · rfl
      · show (1 : ℚ[X]).coeff (if i + 1 ≤ 0 then 0 - (i + 1) else i + 1) =
          (1 : ℚ[X]).coeff (i + 1)
        rw [if_neg (show ¬ i + 1 ≤ 0 by omega)]
  | insert U t hU ih =>
      rw [sum_insert hU, prod_insert hU, prod_insert hU,
        reflect_mul _ _ (natDegree_deficitPolynomial_le _)
          ((natDegree_prod_le (s := t) (f := fun V ↦ deficitPolynomial (∑ i ∈ V, c i))).trans
            (sum_le_sum fun V _ ↦ natDegree_deficitPolynomial_le _)),
        ih fun V hV ↦ ht V (mem_insert_of_mem hV),
        reflect_deficitPolynomial (ht U (mem_insert_self U t))]

/-- Summing over the blocks of a partition and then within each block is summing over the whole
set, each point read at its own block. -/
theorem sum_parts_sum {R : Type*} [AddCommMonoid R] {T : Finset ι} (ρ : Finpartition T)
    (F : Finset ι → ι → R) :
    ∑ U ∈ ρ.parts, ∑ i ∈ U, F U i = ∑ i ∈ T, F (ρ.part i) i := by
  calc ∑ U ∈ ρ.parts, ∑ i ∈ U, F U i = ∑ U ∈ ρ.parts, ∑ i ∈ id U, F (ρ.part i) i :=
        sum_congr rfl fun U hU ↦ sum_congr rfl fun i hi ↦ by rw [ρ.part_eq_of_mem hU hi]
    _ = ∑ i ∈ ρ.parts.biUnion id, F (ρ.part i) i := (sum_biUnion ρ.disjoint).symm
    _ = ∑ i ∈ T, F (ρ.part i) i := by rw [ρ.biUnion_parts]

/-- A block of a partition of positive fiber sizes has positive total size. -/
theorem one_le_block_size {T : Finset ι} {c : ι → ℕ} (hc : ∀ i ∈ T, 1 ≤ c i)
    (ρ : Finpartition T) {U : Finset ι} (hU : U ∈ ρ.parts) : 1 ≤ ∑ i ∈ U, c i := by
  obtain ⟨k, hk⟩ := ρ.nonempty_of_mem_parts hU
  exact (hc k (ρ.le hU hk)).trans (single_le_sum (fun _ _ ↦ Nat.zero_le _) hk)

/-- **`C_c(z) = z^n K_c(1 / z)`.** The corpus connectivity cumulant of the fiber sizes, with
rational coefficients, is the reflection of the cumulant read from its top degree. -/
theorem map_cumulantOfSizes (T : Finset ι) (c : ι → ℕ) (hc : ∀ i ∈ T, 1 ≤ c i) :
    (cumulantOfSizes T c).map (Int.castRingHom ℚ) =
      reflect (∑ i ∈ T, c i) (deficitCumulant T c) := by
  unfold cumulantOfSizes deficitCumulant
  rw [reflect_finset_sum, Polynomial.map_sum]
  refine sum_congr rfl fun ρ _ ↦ ?_
  have hsizes : ∑ U ∈ ρ.parts, ∑ i ∈ U, c i = ∑ i ∈ T, c i := sum_parts_sum ρ fun _ i ↦ c i
  rw [reflect_C_mul, ← hsizes,
    reflect_prod_deficitPolynomial _ c fun U hU ↦ one_le_block_size hc ρ hU,
    Polynomial.map_mul, Polynomial.map_C, Polynomial.map_prod]
  congr 1
  · simp
  · refine prod_congr rfl fun U _ ↦ ?_
    simp [lahPolynomial, Polynomial.map_sum]

/-! ## The Möbius identity at the bottom degree -/

/-- **The bottom coefficient.** `K_c(0) = ∑_ρ μ(ρ, ⊤)`, which is one on a single fiber and zero on
two or more, by the Möbius identity of `ConnectivityCumulant`. -/
theorem coeff_zero_deficitCumulant (T : Finset ι) (c : ι → ℕ) (hT : T.Nonempty)
    (hc : ∀ i ∈ T, 1 ≤ c i) : (deficitCumulant T c).coeff 0 = if #T = 1 then 1 else 0 := by
  rw [coeff_zero_eq_eval_zero]
  unfold deficitCumulant
  rw [eval_finset_sum]
  have hone : ∀ ρ : Finpartition T, (C (mobiusCoefficient #ρ.parts : ℚ) *
      ∏ U ∈ ρ.parts, deficitPolynomial (∑ i ∈ U, c i)).eval 0 =
        (mobiusCoefficient #ρ.parts : ℚ) := by
    intro ρ
    have hblock : ∀ U ∈ ρ.parts, (deficitPolynomial (∑ i ∈ U, c i)).eval 0 = 1 := by
      intro U hU
      rw [← coeff_zero_eq_eval_zero]
      exact deficitPolynomial_coeff_zero (one_le_block_size hc ρ hU)
    rw [eval_mul, eval_C, eval_prod, prod_eq_one hblock, mul_one]
  rw [sum_congr rfl fun ρ _ ↦ hone ρ, ← Int.cast_sum, sum_mobiusCoefficient_finpartition T hT]
  split_ifs <;> simp

/-! ## The derivative of the cumulant -/

/-- The derivative of a finite product. -/
theorem derivative_finset_prod {κ : Type*} [DecidableEq κ] (t : Finset κ) (f : κ → ℚ[X]) :
    derivative (∏ b ∈ t, f b) = ∑ b ∈ t, (∏ a ∈ t.erase b, f a) * derivative (f b) := by
  induction t using Finset.induction_on with
  | empty => simp
  | insert x t hx ih =>
      rw [prod_insert hx, derivative_mul, ih, sum_insert hx, erase_insert hx, mul_sum]
      congr 1
      · ring
      · refine sum_congr rfl fun b hb ↦ ?_
        have hxb : x ≠ b := fun hxb ↦ hx (hxb ▸ hb)
        rw [erase_insert_of_ne hxb, prod_insert fun hxt ↦ hx (mem_of_mem_erase hxt)]
        ring

/-- The number of ordered pairs of individuals in a block splits into the pairs inside one fiber
and the pairs across two fibers. -/
theorem cast_sum_mul_sub_one (U : Finset ι) (c : ι → ℕ) :
    ((∑ i ∈ U, c i : ℕ) : ℚ) * (((∑ i ∈ U, c i : ℕ) : ℚ) - 1) =
      ∑ i ∈ U, (c i : ℚ) * ((c i : ℚ) - 1) + ∑ i ∈ U, ∑ j ∈ U.erase i, (c i : ℚ) * (c j : ℚ) := by
  have hsquare : (∑ k ∈ U, (c k : ℚ)) * (∑ k ∈ U, (c k : ℚ)) =
      ∑ i ∈ U, (c i : ℚ) * (c i : ℚ) + ∑ i ∈ U, ∑ j ∈ U.erase i, (c i : ℚ) * (c j : ℚ) := by
    rw [sum_mul, ← sum_add_distrib]
    refine sum_congr rfl fun i hi ↦ ?_
    rw [← mul_sum, ← mul_add, add_sum_erase U (fun k ↦ (c k : ℚ)) hi]
  push_cast
  simp only [mul_sub, mul_one, sum_sub_distrib]
  rw [hsquare]
  ring

/-- A block other than the block of `i` does not contain `i`. -/
theorem notMem_of_mem_erase_part {T : Finset ι} (ρ : Finpartition T) {i : ι} {U : Finset ι}
    (hU : U ∈ ρ.parts.erase (ρ.part i)) : i ∉ U := fun hiU ↦
  ne_of_mem_erase hU (ρ.part_eq_of_mem (mem_of_mem_erase hU) hiU).symm

/-- Lowering the size of fiber `i` by one lowers exactly the size of its block. -/
theorem prod_parts_update_pred {T : Finset ι} (ρ : Finpartition T) (c : ι → ℕ) (f : ℕ → ℚ[X])
    {i : ι} (hi : i ∈ T) (hci : 1 ≤ c i) :
    ∏ U ∈ ρ.parts, f (∑ k ∈ U, Function.update c i (c i - 1) k) =
      (∏ U ∈ ρ.parts.erase (ρ.part i), f (∑ k ∈ U, c k)) * f (∑ k ∈ ρ.part i, c k - 1) := by
  rw [← prod_erase_mul ρ.parts (fun U ↦ f (∑ k ∈ U, Function.update c i (c i - 1) k))
    (ρ.part_mem.mpr hi)]
  congr 1
  · refine prod_congr rfl fun U hU ↦ ?_
    have hiU := notMem_of_mem_erase_part ρ hU
    congr 1
    exact sum_congr rfl fun k hk ↦ Function.update_of_ne (fun hki ↦ hiU (hki ▸ hk)) _ _
  · congr 1
    rw [sum_update_of_mem (ρ.mem_part hi), sum_eq_add_sum_diff_singleton (ρ.mem_part hi) c]
    omega

/-- Reading the block of `i` one size lower is the same product. -/
theorem prod_parts_ite_pred {T : Finset ι} (ρ : Finpartition T) (c : ι → ℕ) (f : ℕ → ℚ[X])
    {i : ι} (hi : i ∈ T) :
    ∏ U ∈ ρ.parts, (if i ∈ U then f (∑ k ∈ U, c k - 1) else f (∑ k ∈ U, c k)) =
      (∏ U ∈ ρ.parts.erase (ρ.part i), f (∑ k ∈ U, c k)) * f (∑ k ∈ ρ.part i, c k - 1) := by
  rw [← prod_erase_mul ρ.parts
    (fun U ↦ if i ∈ U then f (∑ k ∈ U, c k - 1) else f (∑ k ∈ U, c k)) (ρ.part_mem.mpr hi)]
  congr 1
  · exact prod_congr rfl fun U hU ↦ if_neg (notMem_of_mem_erase_part ρ hU)
  · exact if_pos (ρ.mem_part hi)

/-- **The derivative of one block product.** Differentiating `∏_U a_{c(U)}` picks a block and an
ordered pair of individuals in it, either inside one fiber `i` or across two fibers `i ≠ j`. -/
theorem derivative_prod_parts {T : Finset ι} (ρ : Finpartition T) (c : ι → ℕ) :
    derivative (∏ U ∈ ρ.parts, deficitPolynomial (∑ i ∈ U, c i)) =
      ∑ i ∈ T, (C ((c i : ℚ) * ((c i : ℚ) - 1)) *
          ((∏ A ∈ ρ.parts.erase (ρ.part i), deficitPolynomial (∑ k ∈ A, c k)) *
            deficitPolynomial (∑ k ∈ ρ.part i, c k - 1)) +
        ∑ j ∈ (ρ.part i).erase i, C ((c i : ℚ) * (c j : ℚ)) *
          ((∏ A ∈ ρ.parts.erase (ρ.part i), deficitPolynomial (∑ k ∈ A, c k)) *
            deficitPolynomial (∑ k ∈ ρ.part i, c k - 1))) := by
  rw [derivative_finset_prod]
  refine (sum_congr rfl fun U _ ↦ ?_).trans (sum_parts_sum ρ fun U i ↦
    C ((c i : ℚ) * ((c i : ℚ) - 1)) *
        ((∏ A ∈ ρ.parts.erase U, deficitPolynomial (∑ k ∈ A, c k)) *
          deficitPolynomial (∑ k ∈ U, c k - 1)) +
      ∑ j ∈ U.erase i, C ((c i : ℚ) * (c j : ℚ)) *
        ((∏ A ∈ ρ.parts.erase U, deficitPolynomial (∑ k ∈ A, c k)) *
          deficitPolynomial (∑ k ∈ U, c k - 1)))
  rw [derivative_deficitPolynomial, cast_sum_mul_sub_one]
  simp only [map_add, map_sum, add_mul, mul_add, sum_mul, mul_sum, sum_add_distrib]
  congr 1
  · exact sum_congr rfl fun i _ ↦ by ring
  · exact sum_congr rfl fun i _ ↦ sum_congr rfl fun j _ ↦ by ring

/-- Summing over the partitions of equal sets. -/
theorem sum_finpartition_eq_of_eq {M : Type*} [AddCommMonoid M] {T T' : Finset ι} (h : T' = T)
    (F : Finpartition T → M) : ∑ ρ : Finpartition T, F ρ = ∑ σ : Finpartition T', F (σ.copy h) := by
  subst h
  rfl

/-- Copying a partition to an equal set keeps every block. -/
theorem part_copy {T T' : Finset ι} (h : T' = T) (σ : Finpartition T') (a : ι) :
    (σ.copy h).part a = σ.part a := by
  subst h
  rfl

/-- **Fusing two fibers.** The partitions of the fibers in which `i` and `j` share a block are the
partitions of the other fibers with `j` inserted into the block of `i`, by the insertion
bijection of `LahWeights`. -/
theorem sum_part_eq_part {M : Type*} [AddCommMonoid M] {T : Finset ι} {i j : ι} (hi : i ∈ T)
    (hj : j ∈ T) (hij : i ≠ j) (F : Finpartition T → M) :
    ∑ ρ : Finpartition T with ρ.part i = ρ.part j, F ρ =
      ∑ σ : Finpartition (T.erase j),
        F ((insertIntoPart σ (notMem_erase j T)
          (σ.part_mem.mpr (mem_erase.mpr ⟨hij, hi⟩))).copy (insert_erase hj)) := by
  have hi' : i ∈ T.erase j := mem_erase.mpr ⟨hij, hi⟩
  rw [sum_filter, sum_finpartition_eq_of_eq (insert_erase hj),
    sum_finpartition_insert (notMem_erase j T)]
  refine sum_congr rfl fun σ _ ↦ ?_
  rw [sum_eq_single (σ.part i)]
  · rw [insertAt, dif_pos (σ.part_mem.mpr hi')]
    split_ifs with hcond
    · rfl
    · exfalso
      apply hcond
      rw [part_copy, part_copy]
      have hmem : insert j (σ.part i) ∈
          (insertIntoPart σ (notMem_erase j T) (σ.part_mem.mpr hi')).parts := by
        rw [insertIntoPart_parts]
        exact mem_insert_self _ _
      rw [Finpartition.part_eq_of_mem _ hmem (mem_insert_of_mem (σ.mem_part hi')),
        Finpartition.part_eq_of_mem _ hmem (mem_insert_self j _)]
  · intro u hu hne
    split_ifs with hcond
    · exfalso
      rw [part_copy, part_copy] at hcond
      have herase := part_insertAt_erase σ (notMem_erase j T) hu
      have hiu : i ∈ u := by
        rw [← herase, ← hcond]
        exact mem_erase.mpr ⟨hij, (insertAt σ (notMem_erase j T) u).mem_part
          (mem_insert_of_mem hi')⟩
      rcases mem_insert.mp hu with hu0 | huP
      · rw [hu0] at hiu
        exact notMem_empty i hiu
      · exact hne (σ.part_eq_of_mem huP hiu).symm
    · rfl
  · intro hnot
    exact absurd (mem_insert_of_mem (σ.part_mem.mpr hi')) hnot

/-- **The block sizes of a fused configuration.** Inserting `j` into the block of `i`, reading that
block one size lower, gives the block products of the configuration in which fiber `i` has size
`c_i + c_j − 1` and fiber `j` is gone. -/
theorem fused_product (c : ι → ℕ) {T : Finset ι} {i j : ι} (hi : i ∈ T.erase j) (hci : 1 ≤ c i)
    (σ : Finpartition (T.erase j)) (hσ : σ.part i ∈ σ.parts) :
    ∏ U ∈ (insertIntoPart σ (notMem_erase j T) hσ).parts,
        (if i ∈ U then deficitPolynomial (∑ k ∈ U, c k - 1)
          else deficitPolynomial (∑ k ∈ U, c k)) =
      ∏ V ∈ σ.parts, deficitPolynomial (∑ k ∈ V, Function.update c i (c i + c j - 1) k) := by
  have hjpart : j ∉ σ.part i := notMem_of_mem_parts σ (notMem_erase j T) hσ
  have hnew : insert j (σ.part i) ∉ σ.parts.erase (σ.part i) := fun h ↦
    notMem_of_mem_parts σ (notMem_erase j T) (mem_of_mem_erase h) (mem_insert_self j _)
  rw [insertIntoPart_parts, prod_insert hnew, ← mul_prod_erase σ.parts _ hσ]
  congr 1
  · rw [if_pos (mem_insert_of_mem (σ.mem_part hi)), sum_insert hjpart,
      sum_update_of_mem (σ.mem_part hi), sum_eq_add_sum_diff_singleton (σ.mem_part hi) c]
    congr 1
    omega
  · refine prod_congr rfl fun U hU ↦ ?_
    have hiU := notMem_of_mem_erase_part σ hU
    rw [if_neg hiU]
    congr 1
    exact (sum_congr rfl fun k hk ↦ Function.update_of_ne (fun hki ↦ hiU (hki ▸ hk)) _ _).symm

/-- **The derivative of the cumulant.**
`K_c' = ∑_i c_i (c_i − 1) K_{c − e_i} + ∑_{i ≠ j} c_i c_j K_{c^{(ij)}}`, where `c − e_i` lowers
fiber `i` by one and `c^{(ij)}` fuses fibers `i` and `j` into one fiber of size `c_i + c_j − 1`. -/
theorem derivative_deficitCumulant (T : Finset ι) (c : ι → ℕ) (hc : ∀ i ∈ T, 1 ≤ c i) :
    derivative (deficitCumulant T c) =
      ∑ i ∈ T, C ((c i : ℚ) * ((c i : ℚ) - 1)) *
          deficitCumulant T (Function.update c i (c i - 1)) +
        ∑ i ∈ T, ∑ j ∈ T.erase i, C ((c i : ℚ) * (c j : ℚ)) *
          deficitCumulant (T.erase j) (Function.update c i (c i + c j - 1)) := by
  unfold deficitCumulant
  simp only [derivative_sum, derivative_C_mul, derivative_prod_parts, mul_sum, mul_add,
    sum_add_distrib]
  congr 1
  · refine sum_comm.trans (sum_congr rfl fun i hi ↦ sum_congr rfl fun ρ _ ↦ ?_)
    rw [prod_parts_update_pred ρ c deficitPolynomial hi (hc i hi)]
    ring
  · refine sum_comm.trans (sum_congr rfl fun i hi ↦ ?_)
    have hfilter : ∀ ρ : Finpartition T,
        (T.erase i).filter (fun j ↦ ρ.part i = ρ.part j) = (ρ.part i).erase i := by
      intro ρ
      ext j
      simp only [mem_filter, mem_erase]
      constructor
      · rintro ⟨⟨hji, hjT⟩, hpart⟩
        exact ⟨hji, hpart ▸ ρ.mem_part hjT⟩
      · rintro ⟨hji, hjpart⟩
        exact ⟨⟨hji, ρ.part_subset i hjpart⟩, (ρ.part_eq_of_mem (ρ.part_mem.mpr hi) hjpart).symm⟩
    calc _ = ∑ ρ : Finpartition T, ∑ j ∈ T.erase i,
          if ρ.part i = ρ.part j then C (mobiusCoefficient #ρ.parts : ℚ) *
            (C ((c i : ℚ) * (c j : ℚ)) *
              ((∏ A ∈ ρ.parts.erase (ρ.part i), deficitPolynomial (∑ k ∈ A, c k)) *
                deficitPolynomial (∑ k ∈ ρ.part i, c k - 1))) else 0 :=
          sum_congr rfl fun ρ _ ↦ by rw [← hfilter ρ, sum_filter]
      _ = ∑ j ∈ T.erase i, ∑ ρ : Finpartition T with ρ.part i = ρ.part j,
          C ((c i : ℚ) * (c j : ℚ)) * (C (mobiusCoefficient #ρ.parts : ℚ) *
            ∏ U ∈ ρ.parts, (if i ∈ U then deficitPolynomial (∑ k ∈ U, c k - 1)
              else deficitPolynomial (∑ k ∈ U, c k))) := by
          rw [sum_comm]
          refine sum_congr rfl fun j _ ↦ ?_
          rw [sum_filter]
          refine sum_congr rfl fun ρ _ ↦ ?_
          split_ifs
          · rw [prod_parts_ite_pred ρ c deficitPolynomial hi]
            ring
          · rfl
      _ = _ := sum_congr rfl fun j hj ↦
          (sum_part_eq_part hi (mem_of_mem_erase hj) (ne_of_mem_erase hj).symm _).trans
            (sum_congr rfl fun σ _ ↦ by
              dsimp only
              rw [Finpartition.copy_parts,
                (blockWeight_insertIntoPart σ (notMem_erase j T) _).2,
                fused_product c (mem_erase.mpr ⟨(ne_of_mem_erase hj).symm, hi⟩) (hc i hi) σ _])

/-! ## The vanishing order and the recursion -/

/-- Lowering a fiber of size at least two keeps every size positive. -/
theorem update_pred_pos {T : Finset ι} {c : ι → ℕ} (hc : ∀ i ∈ T, 1 ≤ c i) {i : ι} (hi : i ∈ T)
    (hci : c i ≠ 1) : ∀ k ∈ T, 1 ≤ Function.update c i (c i - 1) k := by
  intro k hk
  by_cases hki : k = i
  · rw [hki, Function.update_self]
    have := hc i hi
    omega
  · rw [Function.update_of_ne hki]
    exact hc k hk

/-- Fusing two fibers keeps every size positive. -/
theorem update_fuse_pos {T : Finset ι} {c : ι → ℕ} (hc : ∀ i ∈ T, 1 ≤ c i) {i : ι} (hi : i ∈ T)
    (j : ι) : ∀ k ∈ T.erase j, 1 ≤ Function.update c i (c i + c j - 1) k := by
  intro k hk
  by_cases hki : k = i
  · rw [hki, Function.update_self]
    have := hc i hi
    omega
  · rw [Function.update_of_ne hki]
    exact hc k (mem_of_mem_erase hk)

/-- **The vanishing order.** On `w ≥ 2` fibers of positive size, `K_c` has no term of degree
below `w − 1`: the connectivity cumulant has degree at most `n − w + 1`. -/
theorem coeff_deficitCumulant_eq_zero :
    ∀ (d : ℕ) (T : Finset ι) (c : ι → ℕ), (∀ i ∈ T, 1 ≤ c i) → d + 1 < #T →
      (deficitCumulant T c).coeff d = 0
  | 0, T, c, hc, hT => by
      rw [coeff_zero_deficitCumulant T c (card_pos.mp (by omega)) hc, if_neg (by omega)]
  | d + 1, T, c, hc, hT => by
      have hderivative := congrArg (fun p ↦ p.coeff d) (derivative_deficitCumulant T c hc)
      simp only [coeff_derivative, finset_sum_coeff, coeff_add, coeff_C_mul] at hderivative
      have hfirst : ∑ i ∈ T, (c i : ℚ) * ((c i : ℚ) - 1) *
          (deficitCumulant T (Function.update c i (c i - 1))).coeff d = 0 :=
        sum_eq_zero fun i hi ↦ by
          by_cases hci : c i = 1
          · simp [hci]
          · rw [coeff_deficitCumulant_eq_zero d T _ (update_pred_pos hc hi hci) (by omega),
              mul_zero]
      have hsecond : ∑ i ∈ T, ∑ j ∈ T.erase i, (c i : ℚ) * (c j : ℚ) *
          (deficitCumulant (T.erase j) (Function.update c i (c i + c j - 1))).coeff d = 0 :=
        sum_eq_zero fun i hi ↦ sum_eq_zero fun j hj ↦ by
          rw [coeff_deficitCumulant_eq_zero d (T.erase j) _ (update_fuse_pos hc hi j)
            (by rw [card_erase_of_mem (mem_of_mem_erase hj)]; omega), mul_zero]
      rw [hfirst, hsecond, add_zero] at hderivative
      exact (mul_eq_zero.mp hderivative).resolve_right (by positivity)

/-- **The recursion.** On `w ≥ 2` fibers,
`(w − 1) L_w(c) = ∑_{i ≠ j} c_i c_j L_{w − 1}(c^{(ij)})` for the top coefficients
`L_w(c) = [u^{w − 1}] K_c`. -/
theorem coeff_deficitCumulant_recursion (T : Finset ι) (c : ι → ℕ) (hc : ∀ i ∈ T, 1 ≤ c i)
    (hT : 2 ≤ #T) :
    (deficitCumulant T c).coeff (#T - 1) * ((#T : ℚ) - 1) =
      ∑ i ∈ T, ∑ j ∈ T.erase i, (c i : ℚ) * (c j : ℚ) *
        (deficitCumulant (T.erase j) (Function.update c i (c i + c j - 1))).coeff (#T - 2) := by
  have hderivative := congrArg (fun p ↦ p.coeff (#T - 2)) (derivative_deficitCumulant T c hc)
  simp only [coeff_derivative, finset_sum_coeff, coeff_add, coeff_C_mul] at hderivative
  have hfirst : ∑ i ∈ T, (c i : ℚ) * ((c i : ℚ) - 1) *
      (deficitCumulant T (Function.update c i (c i - 1))).coeff (#T - 2) = 0 :=
    sum_eq_zero fun i hi ↦ by
      by_cases hci : c i = 1
      · simp [hci]
      · rw [coeff_deficitCumulant_eq_zero (#T - 2) T _ (update_pred_pos hc hi hci) (by omega),
          mul_zero]
  have hindex : #T - 2 + 1 = #T - 1 := by omega
  have hcast : ((#T - 2 : ℕ) : ℚ) + 1 = (#T : ℚ) - 1 := by
    rw [Nat.cast_sub hT]
    push_cast
    ring
  rw [hfirst, zero_add, hindex, hcast] at hderivative
  exact hderivative

/-! ## The closed form -/

/-- Positive fiber sizes total at least the number of fibers. -/
theorem card_le_sum_sizes {T : Finset ι} {c : ι → ℕ} (hc : ∀ i ∈ T, 1 ≤ c i) :
    #T ≤ ∑ i ∈ T, c i := by
  simpa using card_nsmul_le_sum T c 1 hc

/-- Fusing two fibers lowers the total size by one. -/
theorem sum_fused_sizes {T : Finset ι} {c : ι → ℕ} {i j : ι} (hi : i ∈ T.erase j) (hj : j ∈ T)
    (hci : 1 ≤ c i) :
    ∑ k ∈ T.erase j, Function.update c i (c i + c j - 1) k = ∑ k ∈ T, c k - 1 := by
  rw [sum_update_of_mem hi, ← add_sum_erase T c hj, sum_eq_add_sum_diff_singleton hi c]
  omega

/-- Fusing two fibers replaces the factor `c_i c_j` of the product of sizes by `c_i + c_j − 1`. -/
theorem prod_fused_sizes {T : Finset ι} {c : ι → ℕ} {i j : ι} (hi : i ∈ T.erase j) (hj : j ∈ T)
    (hci : 1 ≤ c i) :
    (c i : ℚ) * (c j : ℚ) * ∏ k ∈ T.erase j, (Function.update c i (c i + c j - 1) k : ℚ) =
      ((c i : ℚ) + (c j : ℚ) - 1) * ∏ k ∈ T, (c k : ℚ) := by
  rw [prod_eq_mul_prod_diff_singleton hi, ← mul_prod_erase T (fun k ↦ (c k : ℚ)) hj,
    prod_eq_mul_prod_diff_singleton hi (fun k ↦ (c k : ℚ)), Function.update_self]
  have hrest : ∏ k ∈ T.erase j \ {i}, (Function.update c i (c i + c j - 1) k : ℚ) =
      ∏ k ∈ T.erase j \ {i}, (c k : ℚ) :=
    prod_congr rfl fun k hk ↦ by
      rw [Function.update_of_ne fun hki ↦ (mem_sdiff.mp hk).2 (mem_singleton.mpr hki)]
  rw [hrest, Nat.cast_sub (by omega), Nat.cast_add, Nat.cast_one]
  ring

/-- **The sizes over ordered pairs of fibers.** `∑_{i ≠ j} (c_i + c_j − 1) = (w − 1)(2n − w)`. -/
theorem sum_pairs_sizes {T : Finset ι} (c : ι → ℕ) (hT : 1 ≤ #T) :
    ∑ i ∈ T, ∑ j ∈ T.erase i, ((c i : ℚ) + (c j : ℚ) - 1) =
      ((#T : ℚ) - 1) * (2 * ∑ k ∈ T, (c k : ℚ) - #T) := by
  have hinner : ∀ i ∈ T, ∑ j ∈ T.erase i, ((c i : ℚ) + (c j : ℚ) - 1) =
      ((#T : ℚ) - 1) * (c i : ℚ) + (∑ k ∈ T, (c k : ℚ) - (c i : ℚ)) - ((#T : ℚ) - 1) := by
    intro i hi
    rw [sum_sub_distrib, sum_add_distrib, sum_erase_eq_sub hi]
    simp only [sum_const, card_erase_of_mem hi, nsmul_eq_mul, mul_one]
    rw [Nat.cast_sub hT, Nat.cast_one]
  rw [sum_congr rfl hinner]
  simp only [sum_sub_distrib, sum_add_distrib, sum_const, nsmul_eq_mul, ← mul_sum]
  ring

/-- **The closed form solves the recursion.** Summing the fused values of (E1) over ordered pairs
of fibers gives `(w − 1)` times the value of (E1). -/
theorem sum_pairs_leadingCoefficient (T : Finset ι) (c : ι → ℕ) (hc : ∀ i ∈ T, 1 ≤ c i)
    (hT : 2 ≤ #T) :
    ∑ i ∈ T, ∑ j ∈ T.erase i, (c i : ℚ) * (c j : ℚ) *
        leadingCoefficient (T.erase j) (Function.update c i (c i + c j - 1)) =
      ((#T : ℚ) - 1) * leadingCoefficient T c := by
  have hn := card_le_sum_sizes hc
  have hterm : ∀ i ∈ T, ∀ j ∈ T.erase i, (c i : ℚ) * (c j : ℚ) *
      leadingCoefficient (T.erase j) (Function.update c i (c i + c j - 1)) =
        2 * (∏ k ∈ T, (c k : ℚ)) * ((2 * (∑ k ∈ T, c k) - #T - 1).factorial : ℚ) /
          ((2 * (∑ k ∈ T, c k) - 2 * #T + 2).factorial : ℚ) * ((c i : ℚ) + (c j : ℚ) - 1) := by
    intro i hi j hj
    have hjT : j ∈ T := mem_of_mem_erase hj
    have hij : i ∈ T.erase j := mem_erase.mpr ⟨(ne_of_mem_erase hj).symm, hi⟩
    have hproduct := prod_fused_sizes hij hjT (hc i hi)
    unfold leadingCoefficient
    rw [sum_fused_sizes hij hjT (hc i hi), card_erase_of_mem hjT,
      show 2 * (∑ k ∈ T, c k - 1) - (#T - 1) = 2 * (∑ k ∈ T, c k) - #T - 1 by omega,
      show 2 * (∑ k ∈ T, c k - 1) - 2 * (#T - 1) + 2 = 2 * (∑ k ∈ T, c k) - 2 * #T + 2 by omega]
    linear_combination (2 * ((2 * (∑ k ∈ T, c k) - #T - 1).factorial : ℚ) /
      ((2 * (∑ k ∈ T, c k) - 2 * #T + 2).factorial : ℚ)) * hproduct
  rw [sum_congr rfl fun i hi ↦ sum_congr rfl (hterm i hi)]
  simp only [← mul_sum]
  rw [sum_pairs_sizes c (by omega)]
  unfold leadingCoefficient
  rw [← Nat.mul_factorial_pred (show 2 * (∑ k ∈ T, c k) - #T ≠ 0 by omega)]
  push_cast [Nat.cast_sub (show #T ≤ 2 * ∑ k ∈ T, c k by omega)]
  ring

/-- **NOTE (E1) from the top degree.** On `w ≥ 1` fibers of positive size, the coefficient of
`u^{w − 1}` in `K_c` is `2 (∏_i c_i) (2n − w)! / (2n − 2w + 2)!`. -/
theorem coeff_deficitCumulant_top :
    ∀ (w : ℕ) (T : Finset ι) (c : ι → ℕ), #T = w + 1 → (∀ i ∈ T, 1 ≤ c i) →
      (deficitCumulant T c).coeff (#T - 1) = leadingCoefficient T c
  | 0, T, c, hT, hc => by
      obtain ⟨x, rfl⟩ := card_eq_one.mp hT
      have hx : 1 ≤ c x := hc x (mem_singleton_self x)
      rw [card_singleton, Nat.sub_self, coeff_zero_deficitCumulant _ c (singleton_nonempty x) hc,
        if_pos (card_singleton x)]
      unfold leadingCoefficient
      rw [card_singleton, sum_singleton, prod_singleton,
        show 2 * c x - 2 * 1 + 2 = 2 * c x by omega,
        ← Nat.mul_factorial_pred (show 2 * c x ≠ 0 by omega)]
      have hcx : (c x : ℚ) ≠ 0 := by exact_mod_cast (show c x ≠ 0 by omega)
      have hfactorial : ((2 * c x - 1).factorial : ℚ) ≠ 0 := by
        exact_mod_cast (Nat.factorial_pos _).ne'
      push_cast
      rw [div_self (mul_ne_zero (mul_ne_zero two_ne_zero hcx) hfactorial)]
  | w + 1, T, c, hT, hc => by
      have htwo : 2 ≤ #T := by omega
      have hrecursion := coeff_deficitCumulant_recursion T c hc htwo
      have hfused : ∀ i ∈ T, ∀ j ∈ T.erase i,
          (deficitCumulant (T.erase j) (Function.update c i (c i + c j - 1))).coeff (#T - 2) =
            leadingCoefficient (T.erase j) (Function.update c i (c i + c j - 1)) := by
        intro i hi j hj
        have hjT : j ∈ T := mem_of_mem_erase hj
        have hcard : #(T.erase j) = w + 1 := by
          rw [card_erase_of_mem hjT]
          omega
        rw [show #T - 2 = #(T.erase j) - 1 by rw [hcard]; omega]
        exact coeff_deficitCumulant_top w (T.erase j) _ hcard (update_fuse_pos hc hi j)
      have hsum : ∑ i ∈ T, ∑ j ∈ T.erase i, (c i : ℚ) * (c j : ℚ) *
          (deficitCumulant (T.erase j) (Function.update c i (c i + c j - 1))).coeff (#T - 2) =
            ∑ i ∈ T, ∑ j ∈ T.erase i, (c i : ℚ) * (c j : ℚ) *
              leadingCoefficient (T.erase j) (Function.update c i (c i + c j - 1)) :=
        sum_congr rfl fun i hi ↦ sum_congr rfl fun j hj ↦ by rw [hfused i hi j hj]
      rw [hsum, sum_pairs_leadingCoefficient T c hc htwo] at hrecursion
      have hne : (#T : ℚ) - 1 ≠ 0 :=
        sub_ne_zero.mpr (by exact_mod_cast (show #T ≠ 1 by omega))
      exact mul_right_cancel₀ hne (hrecursion.trans (mul_comm _ _))

/-! ## Theorem E -/

/-- **NOTE Theorem E, (E1).** For `w ≥ 2` fibers of positive sizes `c` with total `n`, the top
coefficient of the connectivity cumulant is
`[z^{n − w + 1}] C_c(z) = 2 (∏_i c_i) (2n − w)! / (2n − 2w + 2)!`. -/
theorem coeff_cumulantOfSizes (T : Finset ι) (c : ι → ℕ) (hT : 2 ≤ #T) (hc : ∀ i ∈ T, 1 ≤ c i) :
    ((cumulantOfSizes T c).coeff (∑ i ∈ T, c i - #T + 1) : ℚ) = leadingCoefficient T c := by
  have hn := card_le_sum_sizes hc
  have hmap := congrArg (fun p ↦ p.coeff (∑ i ∈ T, c i - #T + 1)) (map_cumulantOfSizes T c hc)
  simp only [coeff_map, coeff_reflect, Int.coe_castRingHom] at hmap
  rw [hmap, revAt_le (by omega), show ∑ i ∈ T, c i - (∑ i ∈ T, c i - #T + 1) = #T - 1 by omega]
  exact coeff_deficitCumulant_top (#T - 1) T c (by omega) hc

/-- **NOTE Theorem E at an interface.** For an interface `q` of `w ≥ 2` fibers on `n` individuals,
the coefficient of `z^{n − w + 1}` in the corpus connectivity cumulant is
`2 (∏_C |C|) (2n − w)! / (2n − 2w + 2)!`. -/
theorem coeff_connectivityCumulant_top {α : Type*} [DecidableEq α] {s : Finset α}
    (q : Finpartition s) (hq : 2 ≤ #q.parts) :
    ((connectivityCumulant q).coeff (#s - #q.parts + 1) : ℚ) =
      leadingCoefficient q.parts fun t ↦ #t := by
  rw [connectivityCumulant_eq_cumulantOfSizes, ← q.sum_card_parts]
  exact coeff_cumulantOfSizes q.parts (fun t ↦ #t) hq fun t ht ↦
    card_pos.mpr (q.nonempty_of_mem_parts ht)

end

end Descent.Pangenome.GraphCoalescent
