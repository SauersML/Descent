/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Pangenome.GraphCoalescent.LeadingCoefficient
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import Mathlib.RingTheory.Polynomial.Vieta

assert_below Descent.PopGen Descent.Spectral Descent.Blindness Descent.Conditionals
assert_below Descent.Portability Descent.Decision Descent.Program

/-!
# Recovering a multiset of fiber sizes from its symmetric functions

The fiber-size identifiability question for the pangenome hidden-clock note reads elementary
symmetric functions of the fiber sizes `c_1, …, c_w` off the connectivity cumulant. This file
supplies the last step: the symmetric functions determine the multiset of sizes.

- `multiset_eq_of_esymm_eq`: two multisets of integers with the same cardinality and the same
  elementary symmetric functions are equal. By Vieta, `∏_{a ∈ s} (X - a)` is
  `∑_j (-1)^j e_j(s) X^{|s| - j}`, so the two products are one polynomial, and its roots are both
  multisets (`Polynomial.roots_multiset_prod_X_sub_C`).
- `multiset_nat_eq_of_esymm_eq`: the same for multisets of natural numbers, through the cast to
  `ℤ`, which commutes with `esymm` (`esymm_map_natCast`).
- `map_val_eq_of_sum_powersetCard_prod_eq`: for sizes indexed by finite sets, equal sums
  `∑_{|p| = j} ∏_{i ∈ p} c_i` for every `j` give equal multisets of sizes.
- `pair_eq_of_esymm_eq` and `values_eq_of_esymm_eq`: two values from `e_1, e_2`, and three values
  from `e_1, e_2, e_3`, with the symmetric functions written out.
- `exists_map_val_eq_pair` and `exists_map_val_eq_triple`: an index set with two or three elements
  lists its multiset of sizes as `{c i, c j}` or `{c i, c j, c k}`.

## Empirical status

None. The bodies are statements about polynomials and multisets of numbers, so no measurement can
bear on them.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Pangenome.GraphCoalescent.FiberSizeSymmetricRecovery

/-- **The elementary symmetric functions determine a multiset of integers.** -/
theorem multiset_eq_of_esymm_eq {s t : Multiset ℤ} (hcard : Multiset.card s = Multiset.card t)
    (h : ∀ j, s.esymm j = t.esymm j) : s = t := by
  have hprod : (s.map fun a ↦ Polynomial.X - Polynomial.C a).prod
      = (t.map fun a ↦ Polynomial.X - Polynomial.C a).prod := by
    rw [Multiset.prod_X_sub_X_eq_sum_esymm, Multiset.prod_X_sub_X_eq_sum_esymm, hcard]
    simp only [h]
  have hroots := congrArg Polynomial.roots hprod
  rwa [Polynomial.roots_multiset_prod_X_sub_C, Polynomial.roots_multiset_prod_X_sub_C] at hroots

/-- Casting a multiset of natural numbers to `ℤ` commutes with its symmetric functions. -/
theorem esymm_map_natCast (s : Multiset ℕ) (j : ℕ) :
    (s.map (Nat.cast : ℕ → ℤ)).esymm j = (s.esymm j : ℤ) := by
  unfold Multiset.esymm
  rw [Multiset.powersetCard_map, Nat.cast_multiset_sum, Multiset.map_map, Multiset.map_map]
  refine congrArg Multiset.sum (Multiset.map_congr rfl fun p _ ↦ ?_)
  simp only [Function.comp_apply, Nat.cast_multiset_prod]

/-- **The elementary symmetric functions determine a multiset of natural numbers.** -/
theorem multiset_nat_eq_of_esymm_eq {s t : Multiset ℕ}
    (hcard : Multiset.card s = Multiset.card t) (h : ∀ j, s.esymm j = t.esymm j) : s = t := by
  refine Multiset.map_injective (Nat.cast_injective : Function.Injective (Nat.cast : ℕ → ℤ))
    (multiset_eq_of_esymm_eq ?_ fun j ↦ ?_)
  · rw [Multiset.card_map, Multiset.card_map, hcard]
  · rw [esymm_map_natCast, esymm_map_natCast, h j]

/-- **Sizes indexed by finite sets.** If the two index sets have one size and
`∑_{|p| = j} ∏_{i ∈ p} c_i` agrees for every `j`, the multisets of sizes agree. -/
theorem map_val_eq_of_sum_powersetCard_prod_eq {ι κ : Type*} {T : Finset ι} {T' : Finset κ}
    {c : ι → ℕ} {c' : κ → ℕ} (hcard : T.card = T'.card)
    (h : ∀ j, ∑ p ∈ T.powersetCard j, ∏ i ∈ p, c i = ∑ p ∈ T'.powersetCard j, ∏ i ∈ p, c' i) :
    Multiset.map c T.val = Multiset.map c' T'.val := by
  refine multiset_nat_eq_of_esymm_eq ?_ fun j ↦ ?_
  · rw [Multiset.card_map, Multiset.card_map]
    exact hcard
  · rw [Finset.esymm_map_val, Finset.esymm_map_val]
    exact h j

/-- **Two values from their sum and product.** -/
theorem pair_eq_of_esymm_eq {a b a' b' : ℕ} (h1 : a + b = a' + b') (h2 : a * b = a' * b') :
    ({a, b} : Multiset ℕ) = {a', b'} := by
  have hquad : ∀ x y : ℕ,
      ((({x, y} : Multiset ℕ).map (Nat.cast : ℕ → ℤ)).map
          fun t ↦ Polynomial.X - Polynomial.C t).prod
        = Polynomial.X ^ 2 - Polynomial.C ((x : ℤ) + y) * Polynomial.X
          + Polynomial.C ((x : ℤ) * y) := by
    intro x y
    simp only [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton,
      Multiset.prod_cons, Multiset.prod_singleton, map_add, map_mul]
    ring
  have hz1 : (a : ℤ) + b = a' + b' := by exact_mod_cast h1
  have hz2 : (a : ℤ) * b = a' * b' := by exact_mod_cast h2
  have hprod : ((({a, b} : Multiset ℕ).map (Nat.cast : ℕ → ℤ)).map
        fun t ↦ Polynomial.X - Polynomial.C t).prod
      = ((({a', b'} : Multiset ℕ).map (Nat.cast : ℕ → ℤ)).map
        fun t ↦ Polynomial.X - Polynomial.C t).prod := by
    rw [hquad, hquad, hz1, hz2]
  have hroots := congrArg Polynomial.roots hprod
  rw [Polynomial.roots_multiset_prod_X_sub_C, Polynomial.roots_multiset_prod_X_sub_C] at hroots
  exact Multiset.map_injective (Nat.cast_injective : Function.Injective (Nat.cast : ℕ → ℤ)) hroots

/-- **Three values from their elementary symmetric functions**
`e_1 = a + b + c`, `e_2 = ab + bc + ca` and `e_3 = abc`. -/
theorem values_eq_of_esymm_eq {a b c a' b' c' : ℕ} (h1 : a + b + c = a' + b' + c')
    (h2 : a * b + b * c + c * a = a' * b' + b' * c' + c' * a')
    (h3 : a * b * c = a' * b' * c') :
    ({a, b, c} : Multiset ℕ) = {a', b', c'} := by
  have hcubic : ∀ x y z : ℕ,
      ((({x, y, z} : Multiset ℕ).map (Nat.cast : ℕ → ℤ)).map
          fun t ↦ Polynomial.X - Polynomial.C t).prod
        = Polynomial.X ^ 3 - Polynomial.C ((x : ℤ) + y + z) * Polynomial.X ^ 2
          + Polynomial.C ((x : ℤ) * y + y * z + z * x) * Polynomial.X
          - Polynomial.C ((x : ℤ) * y * z) := by
    intro x y z
    simp only [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton,
      Multiset.prod_cons, Multiset.prod_singleton, map_add, map_mul]
    ring
  have hz1 : (a : ℤ) + b + c = a' + b' + c' := by exact_mod_cast h1
  have hz2 : (a : ℤ) * b + b * c + c * a = a' * b' + b' * c' + c' * a' := by exact_mod_cast h2
  have hz3 : (a : ℤ) * b * c = a' * b' * c' := by exact_mod_cast h3
  have hprod : ((({a, b, c} : Multiset ℕ).map (Nat.cast : ℕ → ℤ)).map
        fun t ↦ Polynomial.X - Polynomial.C t).prod
      = ((({a', b', c'} : Multiset ℕ).map (Nat.cast : ℕ → ℤ)).map
        fun t ↦ Polynomial.X - Polynomial.C t).prod := by
    rw [hcubic, hcubic, hz1, hz2, hz3]
  have hroots := congrArg Polynomial.roots hprod
  rw [Polynomial.roots_multiset_prod_X_sub_C, Polynomial.roots_multiset_prod_X_sub_C] at hroots
  exact Multiset.map_injective (Nat.cast_injective : Function.Injective (Nat.cast : ℕ → ℤ)) hroots

/-- An index set with two elements lists its sizes as `{c i, c j}`. -/
theorem exists_map_val_eq_pair {ι : Type*} [DecidableEq ι] {T : Finset ι} (hT : T.card = 2)
    (c : ι → ℕ) : ∃ i j, i ≠ j ∧ T = {i, j} ∧ Multiset.map c T.val = {c i, c j} := by
  obtain ⟨i, j, hij, rfl⟩ := Finset.card_eq_two.mp hT
  refine ⟨i, j, hij, rfl, ?_⟩
  have hi : i ∉ ({j} : Finset ι) := by simpa using hij
  rw [Finset.insert_val_of_notMem hi, Finset.singleton_val]
  simp only [Multiset.map_cons, Multiset.map_singleton, Multiset.insert_eq_cons]

/-- An index set with three elements lists its sizes as `{c i, c j, c k}`. -/
theorem exists_map_val_eq_triple {ι : Type*} [DecidableEq ι] {T : Finset ι} (hT : T.card = 3)
    (c : ι → ℕ) : ∃ i j k, i ≠ j ∧ i ≠ k ∧ j ≠ k ∧ T = {i, j, k} ∧
      Multiset.map c T.val = {c i, c j, c k} := by
  obtain ⟨i, j, k, hij, hik, hjk, rfl⟩ := Finset.card_eq_three.mp hT
  refine ⟨i, j, k, hij, hik, hjk, rfl, ?_⟩
  have hj : j ∉ ({k} : Finset ι) := by simpa using hjk
  have hi : i ∉ ({j, k} : Finset ι) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨hij, hik⟩
  rw [Finset.insert_val_of_notMem hi, Finset.insert_val_of_notMem hj, Finset.singleton_val]
  simp only [Multiset.map_cons, Multiset.map_singleton, Multiset.insert_eq_cons]

end Descent.Pangenome.GraphCoalescent.FiberSizeSymmetricRecovery
