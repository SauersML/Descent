/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Pangenome.GraphCoalescent.HiddenLoads
import Mathlib.Algebra.Order.BigOperators.Group.Finset

assert_below Descent.PopGen Descent.Spectral Descent.Blindness Descent.Conditionals
assert_below Descent.Portability Descent.Decision Descent.Program

/-!
# Balanced fiber sizes maximize the product of the fiber sizes

Theorem E of the hidden-clock note gives the leading short-time coefficient of the connection law
as `2 (∏_i c_i) (2n - w)! / (2n - 2w + 2)!`, where the `c_i` are the fiber sizes of the interface.
At fixed `n` and `w` the factorial factor is fixed, so the coefficient is largest exactly when the
product of the fiber sizes is.  The note says that product is maximized by fiber sizes as equal as
possible.  This module proves that statement for positive integer sizes over any finite set of
fibers, by a finite exchange argument.

`IsBalancedFibers c` says any two sizes differ by at most one.  `exchangeFibers c i j` moves one
unit from fiber `i` to fiber `j`.  When `c i ≥ c j + 2` the exchange keeps every size positive
(`exchangeFibers_pos`), keeps the total (`sum_exchangeFibers`), and strictly raises the product
(`prod_lt_prod_exchangeFibers`), because `(a - 1)(b + 1) = ab + (a - b - 1) > ab`.  Hence a
profile with the largest product among positive profiles of its total is balanced
(`isBalancedFibers_of_prod_maximal`).  Two balanced profiles with the same total have the same
minimum and the same number of sizes one above it, hence the same product
(`prod_eq_of_isBalancedFibers`).  The positive profiles of a fixed total are finitely many
(`positiveProfiles`), so a maximal one exists, and every balanced profile attains its product
(`prod_le_prod_of_isBalancedFibers`).  `prod_maximal_iff_isBalancedFibers` states both
directions.  `prod_hiddenLoad_bot_le_of_isBalancedFibers` reads the statement at the fiber sizes
of an interface, the loads `hiddenLoad s ⊥` of `HiddenLoads`.

Scope.  The extremal statement is about the product of the sizes.  The corollary for the leading
coefficient waits for the Theorem E module that defines the coefficient; at fixed `n` and `w` the
coefficient is the product times a fixed factor.  Early-time extremal statement only, as in the
note.

## Empirical status

None.  The bodies here are arithmetic on finite profiles of natural numbers, so no measurement can
bear on them.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Pangenome.GraphCoalescent

open Coalescent Finset
open scoped Classical

noncomputable section

section Profiles

variable {ι : Type*} [Fintype ι]

/-- Fiber sizes are balanced when any two of them differ by at most one. -/
def IsBalancedFibers (c : ι → ℕ) : Prop :=
  ∀ i j, c i ≤ c j + 1

/-- Move one unit of size from fiber `i` to fiber `j`. -/
def exchangeFibers (c : ι → ℕ) (i j : ι) : ι → ℕ :=
  Function.update (Function.update c i (c i - 1)) j (c j + 1)

/-- The source fiber of an exchange loses one unit. -/
theorem exchangeFibers_left (c : ι → ℕ) {i j : ι} (hij : i ≠ j) :
    exchangeFibers c i j i = c i - 1 := by
  simp [exchangeFibers, hij]

/-- The target fiber of an exchange gains one unit. -/
theorem exchangeFibers_right (c : ι → ℕ) (i j : ι) : exchangeFibers c i j j = c j + 1 := by
  simp [exchangeFibers]

/-- Every other fiber is unchanged by an exchange. -/
theorem exchangeFibers_of_ne (c : ι → ℕ) {i j k : ι} (hki : k ≠ i) (hkj : k ≠ j) :
    exchangeFibers c i j k = c k := by
  simp [exchangeFibers, hki, hkj]

/-- An exchange from a fiber at least two larger than the target keeps every size positive. -/
theorem exchangeFibers_pos (c : ι → ℕ) {i j : ι} (hij : i ≠ j) (hpos : ∀ k, 1 ≤ c k)
    (hgap : c j + 2 ≤ c i) (k : ι) : 1 ≤ exchangeFibers c i j k := by
  by_cases hki : k = i
  · subst hki
    rw [exchangeFibers_left c hij]
    omega
  · by_cases hkj : k = j
    · subst hkj
      rw [exchangeFibers_right]
      omega
    · rw [exchangeFibers_of_ne c hki hkj]
      exact hpos k

/-- A fiber outside two removed fibers is neither of them. -/
theorem ne_of_mem_erase_erase {i j k : ι} (hk : k ∈ (univ.erase i).erase j) : k ≠ i ∧ k ≠ j :=
  ⟨(mem_erase.mp (mem_erase.mp hk).2).1, (mem_erase.mp hk).1⟩

/-- **The exchange keeps the total.** -/
theorem sum_exchangeFibers (c : ι → ℕ) {i j : ι} (hij : i ≠ j) (hi : 1 ≤ c i) :
    ∑ k, exchangeFibers c i j k = ∑ k, c k := by
  have hj : j ∈ univ.erase i := mem_erase.mpr ⟨Ne.symm hij, mem_univ j⟩
  have hrest : ∑ k ∈ (univ.erase i).erase j, exchangeFibers c i j k =
      ∑ k ∈ (univ.erase i).erase j, c k :=
    sum_congr rfl fun k hk ↦
      exchangeFibers_of_ne c (ne_of_mem_erase_erase hk).1 (ne_of_mem_erase_erase hk).2
  rw [← add_sum_erase univ (exchangeFibers c i j) (mem_univ i),
    ← add_sum_erase (univ.erase i) (exchangeFibers c i j) hj, hrest,
    exchangeFibers_left c hij, exchangeFibers_right, ← add_sum_erase univ c (mem_univ i),
    ← add_sum_erase (univ.erase i) c hj]
  omega

/-- **The exchange raises the product.**  Moving one unit from a fiber at least two larger than
another strictly raises the product of positive sizes. -/
theorem prod_lt_prod_exchangeFibers (c : ι → ℕ) {i j : ι} (hij : i ≠ j) (hpos : ∀ k, 1 ≤ c k)
    (hgap : c j + 2 ≤ c i) : ∏ k, c k < ∏ k, exchangeFibers c i j k := by
  have hj : j ∈ univ.erase i := mem_erase.mpr ⟨Ne.symm hij, mem_univ j⟩
  have hrest : ∏ k ∈ (univ.erase i).erase j, exchangeFibers c i j k =
      ∏ k ∈ (univ.erase i).erase j, c k :=
    prod_congr rfl fun k hk ↦
      exchangeFibers_of_ne c (ne_of_mem_erase_erase hk).1 (ne_of_mem_erase_erase hk).2
  have hrestpos : 0 < ∏ k ∈ (univ.erase i).erase j, c k := prod_pos fun k _ ↦ hpos k
  have hkey : c i * c j < (c i - 1) * (c j + 1) := by
    obtain ⟨d, hd⟩ : ∃ d, c i = c j + 2 + d := ⟨c i - (c j + 2), by omega⟩
    rw [hd, show c j + 2 + d - 1 = c j + 1 + d by omega]
    have hexpand : (c j + 1 + d) * (c j + 1) = (c j + 2 + d) * c j + (1 + d) := by ring
    rw [hexpand]
    exact Nat.lt_add_of_pos_right (by omega)
  rw [← mul_prod_erase univ c (mem_univ i), ← mul_prod_erase (univ.erase i) c hj,
    ← mul_prod_erase univ (exchangeFibers c i j) (mem_univ i),
    ← mul_prod_erase (univ.erase i) (exchangeFibers c i j) hj, hrest,
    exchangeFibers_left c hij, exchangeFibers_right, ← mul_assoc, ← mul_assoc]
  exact Nat.mul_lt_mul_of_pos_right hkey hrestpos

/-- **A maximal profile is balanced.**  A positive profile whose product is at least that of
every positive profile with the same total has any two sizes within one of each other. -/
theorem isBalancedFibers_of_prod_maximal (m : ι → ℕ) (hm : ∀ k, 1 ≤ m k)
    (hmax : ∀ c : ι → ℕ, (∀ k, 1 ≤ c k) → ∑ k, c k = ∑ k, m k → ∏ k, c k ≤ ∏ k, m k) :
    IsBalancedFibers m := by
  intro i j
  by_contra hunbalanced
  have hgap : m j + 2 ≤ m i := by omega
  have hij : i ≠ j := by
    rintro rfl
    omega
  have hle := hmax (exchangeFibers m i j) (exchangeFibers_pos m hij hm hgap)
    (sum_exchangeFibers m hij (by omega))
  exact absurd hle (not_le.mpr (prod_lt_prod_exchangeFibers m hij hm hgap))

/-- In a balanced profile every size is the minimum or one above it. -/
theorem isBalancedFibers_values (c : ι → ℕ) (hc : IsBalancedFibers c) {p : ι}
    (hp : ∀ k, c p ≤ c k) (k : ι) : c k = c p ∨ c k = c p + 1 := by
  have hlow := hp k
  have hhigh := hc k p
  omega

/-- A profile whose sizes are a value or one above it has product `(v + 1)^A v^B`, with `A` and
`B` the numbers of sizes at `v + 1` and at `v`. -/
theorem prod_eq_pow_mul_pow (c : ι → ℕ) (v : ℕ) (hvalues : ∀ k, c k = v ∨ c k = v + 1) :
    ∏ k, c k = (v + 1) ^ (univ.filter fun k ↦ c k = v + 1).card *
      v ^ (univ.filter fun k ↦ ¬c k = v + 1).card := by
  have hpoint : ∀ k, c k = if c k = v + 1 then v + 1 else v := by
    intro k
    split_ifs with h
    · exact h
    · exact (hvalues k).resolve_right h
  calc ∏ k, c k = ∏ k, (if c k = v + 1 then v + 1 else v) :=
        prod_congr rfl fun k _ ↦ hpoint k
    _ = _ := by rw [prod_ite, prod_const, prod_const]

/-- The same profile has total `A (v + 1) + B v`. -/
theorem sum_eq_card_mul_add_card_mul (c : ι → ℕ) (v : ℕ)
    (hvalues : ∀ k, c k = v ∨ c k = v + 1) :
    ∑ k, c k = (univ.filter fun k ↦ c k = v + 1).card * (v + 1) +
      (univ.filter fun k ↦ ¬c k = v + 1).card * v := by
  have hpoint : ∀ k, c k = if c k = v + 1 then v + 1 else v := by
    intro k
    split_ifs with h
    · exact h
    · exact (hvalues k).resolve_right h
  calc ∑ k, c k = ∑ k, (if c k = v + 1 then v + 1 else v) :=
        sum_congr rfl fun k _ ↦ hpoint k
    _ = _ := by rw [sum_ite, sum_const, sum_const, smul_eq_mul, smul_eq_mul]

/-- **Balanced profiles with one total have one product.** -/
theorem prod_eq_of_isBalancedFibers (c m : ι → ℕ) (i0 : ι) (hc : IsBalancedFibers c)
    (hm : IsBalancedFibers m) (hsum : ∑ k, c k = ∑ k, m k) : ∏ k, c k = ∏ k, m k := by
  obtain ⟨p, -, hp⟩ := exists_min_image univ c ⟨i0, mem_univ i0⟩
  obtain ⟨q, -, hq⟩ := exists_min_image univ m ⟨i0, mem_univ i0⟩
  have hpmin : ∀ k, c p ≤ c k := fun k ↦ hp k (mem_univ k)
  have hqmin : ∀ k, m q ≤ m k := fun k ↦ hq k (mem_univ k)
  have hmin : c p = m q := by
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
    · have hstrict : ∑ k, c k < ∑ k, m k :=
        sum_lt_sum (fun k _ ↦ by have h1 := hc k p; have h2 := hqmin k; omega)
          ⟨p, mem_univ p, by have h2 := hqmin p; omega⟩
      omega
    · have hstrict : ∑ k, m k < ∑ k, c k :=
        sum_lt_sum (fun k _ ↦ by have h1 := hm k q; have h2 := hpmin k; omega)
          ⟨q, mem_univ q, by have h2 := hpmin q; omega⟩
      omega
  have hcvalues : ∀ k, c k = c p ∨ c k = c p + 1 := isBalancedFibers_values c hc hpmin
  have hmvalues : ∀ k, m k = c p ∨ m k = c p + 1 := by
    rw [hmin]
    exact isBalancedFibers_values m hm hqmin
  have hccard := filter_card_add_filter_neg_card_eq_card (s := univ) fun k ↦ c k = c p + 1
  have hmcard := filter_card_add_filter_neg_card_eq_card (s := univ) fun k ↦ m k = c p + 1
  have hcsum := sum_eq_card_mul_add_card_mul c (c p) hcvalues
  have hmsum := sum_eq_card_mul_add_card_mul m (c p) hmvalues
  have hcsplit : (univ.filter fun k ↦ c k = c p + 1).card * (c p + 1) +
      (univ.filter fun k ↦ ¬c k = c p + 1).card * c p =
      ((univ.filter fun k ↦ c k = c p + 1).card +
        (univ.filter fun k ↦ ¬c k = c p + 1).card) * c p +
        (univ.filter fun k ↦ c k = c p + 1).card := by ring
  have hmsplit : (univ.filter fun k ↦ m k = c p + 1).card * (c p + 1) +
      (univ.filter fun k ↦ ¬m k = c p + 1).card * c p =
      ((univ.filter fun k ↦ m k = c p + 1).card +
        (univ.filter fun k ↦ ¬m k = c p + 1).card) * c p +
        (univ.filter fun k ↦ m k = c p + 1).card := by ring
  rw [hcsplit, hccard] at hcsum
  rw [hmsplit, hmcard] at hmsum
  have hhigh : (univ.filter fun k ↦ c k = c p + 1).card =
      (univ.filter fun k ↦ m k = c p + 1).card := by omega
  have hlow : (univ.filter fun k ↦ ¬c k = c p + 1).card =
      (univ.filter fun k ↦ ¬m k = c p + 1).card := by omega
  rw [prod_eq_pow_mul_pow c (c p) hcvalues, prod_eq_pow_mul_pow m (c p) hmvalues, hhigh, hlow]

/-- The positive profiles over the fibers with total `n`. -/
def positiveProfiles (n : ℕ) : Finset (ι → ℕ) :=
  (Fintype.piFinset fun _ ↦ range (n + 1)).filter fun c ↦ (∀ k, 1 ≤ c k) ∧ ∑ k, c k = n

/-- A profile is a positive profile of total `n` exactly when its sizes are positive and add up
to `n`. -/
theorem mem_positiveProfiles {n : ℕ} {c : ι → ℕ} :
    c ∈ positiveProfiles n ↔ (∀ k, 1 ≤ c k) ∧ ∑ k, c k = n := by
  constructor
  · intro h
    exact (mem_filter.mp h).2
  · rintro ⟨hpos, hsum⟩
    refine mem_filter.mpr ⟨Fintype.mem_piFinset.mpr fun k ↦ mem_range.mpr ?_, hpos, hsum⟩
    have hle : c k ≤ ∑ j, c j := single_le_sum (fun j _ ↦ Nat.zero_le (c j)) (mem_univ k)
    omega

/-- **Balanced profiles maximize the product.**  Among positive profiles with the same total, a
balanced profile has the largest product. -/
theorem prod_le_prod_of_isBalancedFibers (c m : ι → ℕ) (i0 : ι) (hc : ∀ k, 1 ≤ c k)
    (hm : ∀ k, 1 ≤ m k) (hbal : IsBalancedFibers m) (hsum : ∑ k, c k = ∑ k, m k) :
    ∏ k, c k ≤ ∏ k, m k := by
  obtain ⟨top, htop, hmaxtop⟩ := exists_max_image (positiveProfiles (∑ k, m k))
    (fun f ↦ ∏ k, f k) ⟨m, mem_positiveProfiles.mpr ⟨hm, rfl⟩⟩
  obtain ⟨htoppos, htopsum⟩ := mem_positiveProfiles.mp htop
  have htopbal : IsBalancedFibers top := isBalancedFibers_of_prod_maximal top htoppos
    fun f hf hfsum ↦ hmaxtop f (mem_positiveProfiles.mpr ⟨hf, hfsum.trans htopsum⟩)
  rw [← prod_eq_of_isBalancedFibers top m i0 htopbal hbal htopsum]
  exact hmaxtop c (mem_positiveProfiles.mpr ⟨hc, hsum⟩)

/-- **Theorem E extremal statement.**  A positive profile has the largest product among positive
profiles with its total exactly when its sizes are as equal as possible. -/
theorem prod_maximal_iff_isBalancedFibers (m : ι → ℕ) (i0 : ι) (hm : ∀ k, 1 ≤ m k) :
    (∀ c : ι → ℕ, (∀ k, 1 ≤ c k) → ∑ k, c k = ∑ k, m k → ∏ k, c k ≤ ∏ k, m k) ↔
      IsBalancedFibers m :=
  ⟨isBalancedFibers_of_prod_maximal m hm, fun hbal c hc hsum ↦
    prod_le_prod_of_isBalancedFibers c m i0 hc hm hbal hsum⟩

end Profiles

/-- **Theorem E extremal statement at an interface.**  The fiber sizes of an interface, the loads
`hiddenLoad s ⊥` of its report components, have product at most that of any balanced positive
profile over the same components with the same total. -/
theorem prod_hiddenLoad_bot_le_of_isBalancedFibers {n : ℕ} (s : Fin n → Fin n)
    (m : Quotient (observed s ⊥) → ℕ) (C0 : Quotient (observed s ⊥)) (hm : ∀ C, 1 ≤ m C)
    (hbal : IsBalancedFibers m) (hsum : ∑ C, m C = blocks (⊥ : ER n)) :
    ∏ C, hiddenLoad s ⊥ C ≤ ∏ C, m C :=
  prod_le_prod_of_isBalancedFibers _ m C0 (fun C ↦ hiddenLoad_pos s ⊥ C) hm hbal
    ((sum_hiddenLoad s ⊥).trans hsum.symm)

end

end Descent.Pangenome.GraphCoalescent
