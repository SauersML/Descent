/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Pangenome.GraphCoalescent.FiberSizeIdentifiability

assert_below Descent.PopGen Descent.Spectral Descent.Blindness Descent.Conditionals
assert_below Descent.Portability Descent.Decision Descent.Program

/-!
# Fiber sizes at width four: the second coefficient of the cumulant

`FiberSizeIdentifiability` shows that the connectivity cumulant `C_c(z)` of the fiber sizes
determines the multiset of sizes at widths two and three. This file computes the next coefficient
at width four. With `K_c(u) = u^n C_c(1/u)` the reversed cumulant, `e_2, e_3, e_4` the elementary
symmetric polynomials of the four sizes and `n = e_1`:

- `coeff_three_deficitCumulant_card_four`: `[u^3] K_c = 2 e_4 (2n - 4)(2n - 5)`, the top.
- `coeff_four_deficitCumulant_quad`: one past the top,
  `[u^4] K_c = 2 e_4 (4n⁴ - 40n³ + 149n² - 257n + 192 - 2(2n² - 15n + 29) e_2 - 2(2n - 9) e_3
  - 8 e_4)` (`quadSecond`).

The second coefficient is affine in `(e_2, e_3)`: given `n` and `e_4`, it fixes the single linear
form `(2n² - 15n + 29) e_2 + (2n - 9) e_3`, where width three fixed `e_2` itself.

## The mechanism

The merge recursion one degree past the top (`coeff_card_deficitCumulant`) sums a hidden merger in
each fiber, followed by the top coefficient of four fibers of total `n - 1`
(`hidden_term_card_four`), and a visible merger of each ordered pair, followed by the second
coefficient of the fused three fibers (`coeff_three_fused`, from
`coeff_three_deficitCumulant_triple`).

## Scope

Only the two top coefficients at width four are computed. Whether the cumulant determines the
multiset of fiber sizes at width four is open, and nothing here asserts either answer.

## Empirical status

None. Every declaration here is a coefficient of a polynomial with rational coefficients indexed
by the partitions of a finite set, or a polynomial in four rational numbers.
-/

namespace Descent.Pangenome.GraphCoalescent

open Finset Polynomial

noncomputable section

variable {ι : Type*} [DecidableEq ι]

/-- **The second coefficient of three fibers**, as a polynomial in the three sizes:
`2 e_3 (2n³ - 11n² + 21n - 16 - 2(n - 3) e_2 - 2 e_3)`.

Empirical status: NOT AN EMPIRICAL CLAIM.  A polynomial in three rational numbers. -/
def tripleSecond (a b c : ℚ) : ℚ :=
  2 * (a * b * c) * (2 * (a + b + c) ^ 3 - 11 * (a + b + c) ^ 2 + 21 * (a + b + c) - 16 -
    2 * ((a + b + c) - 3) * (a * b + a * c + b * c) - 2 * (a * b * c))

/-- **The second coefficient of four fibers**, as a polynomial in the four sizes:
`2 e_4 (4n⁴ - 40n³ + 149n² - 257n + 192 - 2(2n² - 15n + 29) e_2 - 2(2n - 9) e_3 - 8 e_4)`.

Empirical status: NOT AN EMPIRICAL CLAIM.  A polynomial in four rational numbers. -/
def quadSecond (a b c d : ℚ) : ℚ :=
  2 * (a * b * c * d) * (4 * (a + b + c + d) ^ 4 - 40 * (a + b + c + d) ^ 3 +
    149 * (a + b + c + d) ^ 2 - 257 * (a + b + c + d) + 192 -
    2 * (2 * (a + b + c + d) ^ 2 - 15 * (a + b + c + d) + 29) *
      (a * b + a * c + a * d + b * c + b * d + c * d) -
    2 * (2 * (a + b + c + d) - 9) * (a * b * c + a * b * d + a * c * d + b * c * d) -
    8 * (a * b * c * d))

/-- **Four fibers, the top.** `[u^3] K_c = 2 e_4 (2n - 4)(2n - 5)`.

Assumes: four fibers of positive size. -/
theorem coeff_three_deficitCumulant_card_four {T : Finset ι} (hT : #T = 4) (c : ι → ℕ)
    (hc : ∀ i ∈ T, 1 ≤ c i) :
    (deficitCumulant T c).coeff 3 = 2 * (∏ k ∈ T, (c k : ℚ)) *
      (2 * ∑ k ∈ T, (c k : ℚ) - 4) * (2 * ∑ k ∈ T, (c k : ℚ) - 5) := by
  have hn : 4 ≤ ∑ k ∈ T, c k := by
    have := card_le_sum_sizes hc
    omega
  have htop := coeff_deficitCumulant_top 3 T c hT hc
  rw [hT, show (4 : ℕ) - 1 = 3 from rfl] at htop
  rw [htop, leadingCoefficient, hT,
    show 2 * ∑ k ∈ T, c k - 4 = (2 * ∑ k ∈ T, c k - 6) + 1 + 1 by omega,
    show 2 * ∑ k ∈ T, c k - 2 * 4 + 2 = 2 * ∑ k ∈ T, c k - 6 by omega, Nat.factorial_succ,
    Nat.factorial_succ]
  have hfact : ((2 * ∑ k ∈ T, c k - 6).factorial : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.factorial_pos _).ne'
  push_cast [Nat.cast_sub (show 6 ≤ 2 * ∑ k ∈ T, c k by omega)]
  field_simp
  ring

/-- **A hidden merger among four fibers**, followed by the top coefficient of the sizes after it:
`c_i (c_i - 1) [u^3] K_{c - e_i} = 2 (c_i - 1)² e_4 (2n - 6)(2n - 7)`.

Assumes: four fibers of positive size, and `i` is one of them. -/
theorem hidden_term_card_four {T : Finset ι} (hT : #T = 4) {c : ι → ℕ} (hc : ∀ i ∈ T, 1 ≤ c i)
    {i : ι} (hi : i ∈ T) :
    (c i : ℚ) * ((c i : ℚ) - 1) * (deficitCumulant T (Function.update c i (c i - 1))).coeff 3 =
      2 * ((c i : ℚ) - 1) ^ 2 * (∏ k ∈ T, (c k : ℚ)) * (2 * ∑ k ∈ T, (c k : ℚ) - 6) *
        (2 * ∑ k ∈ T, (c k : ℚ) - 7) := by
  by_cases hci : c i = 1
  · simp [hci]
  · rw [coeff_three_deficitCumulant_card_four hT _ (update_pred_pos hc hi hci),
      sum_update_pred hi (hc i hi)]
    linear_combination (2 * ((c i : ℚ) - 1) * (2 * (∑ k ∈ T, (c k : ℚ) - 1) - 4) *
      (2 * (∑ k ∈ T, (c k : ℚ) - 1) - 5)) * prod_update_pred hi (hc i hi)

/-- **A visible merger followed by three fibers.** The second coefficient of the three fibers
`{i, k, l}` after fusing `j` into `i`, in the sizes before the merger.

Assumes: the three remaining labels are distinct, and the four sizes involved are positive. -/
theorem coeff_three_fused {S : Finset ι} {i j k l : ι} (hS : S = {i, k, l}) (hik : i ≠ k)
    (hil : i ≠ l) (hkl : k ≠ l) (c : ι → ℕ) (hi : 1 ≤ c i) (hj : 1 ≤ c j) (hk : 1 ≤ c k)
    (hl : 1 ≤ c l) :
    (deficitCumulant S (Function.update c i (c i + c j - 1))).coeff 3 =
      tripleSecond ((c i : ℚ) + c j - 1) (c k) (c l) := by
  subst hS
  have hpos : ∀ m ∈ ({i, k, l} : Finset ι), 1 ≤ Function.update c i (c i + c j - 1) m := by
    intro m hm
    simp only [mem_insert, mem_singleton] at hm
    rcases hm with rfl | rfl | rfl
    · rw [Function.update_self]
      omega
    · rw [Function.update_of_ne hik.symm]
      exact hk
    · rw [Function.update_of_ne hil.symm]
      exact hl
  rw [coeff_three_deficitCumulant_triple hik hil hkl _ hpos, Function.update_self,
    Function.update_of_ne hik.symm, Function.update_of_ne hil.symm,
    Nat.cast_sub (show 1 ≤ c i + c j by omega), Nat.cast_add, Nat.cast_one]
  unfold tripleSecond
  ring

/-- **Four fibers, one past the top.**
`[u^4] K_c = 2 e_4 (4n⁴ - 40n³ + 149n² - 257n + 192 - 2(2n² - 15n + 29) e_2 - 2(2n - 9) e_3
- 8 e_4)`.

Assumes: four distinct labels, every size positive. -/
theorem coeff_four_deficitCumulant_quad {x y z t : ι} (hxy : x ≠ y) (hxz : x ≠ z) (hxt : x ≠ t)
    (hyz : y ≠ z) (hyt : y ≠ t) (hzt : z ≠ t) (c : ι → ℕ)
    (hc : ∀ i ∈ ({x, y, z, t} : Finset ι), 1 ≤ c i) :
    (deficitCumulant {x, y, z, t} c).coeff 4 = quadSecond (c x) (c y) (c z) (c t) := by
  have hcx : 1 ≤ c x := hc x (by simp)
  have hcy : 1 ≤ c y := hc y (by simp)
  have hcz : 1 ≤ c z := hc z (by simp)
  have hct : 1 ≤ c t := hc t (by simp)
  have hx : x ∉ ({y, z, t} : Finset ι) := by simp [hxy, hxz, hxt]
  have hy : y ∉ ({z, t} : Finset ι) := by simp [hyz, hyt]
  have hx2 : x ∉ ({z, t} : Finset ι) := by simp [hxz, hxt]
  have hx3 : x ∉ ({y, t} : Finset ι) := by simp [hxy, hxt]
  have hx4 : x ∉ ({y, z} : Finset ι) := by simp [hxy, hxz]
  have hT : #({x, y, z, t} : Finset ι) = 4 := by
    rw [card_insert_of_notMem hx, card_insert_of_notMem hy, card_pair hzt]
  have ex : ({x, y, z, t} : Finset ι).erase x = {y, z, t} := erase_insert hx
  have ey : ({x, y, z, t} : Finset ι).erase y = {x, z, t} := by
    rw [erase_insert_of_ne hxy, erase_insert hy]
  have ez : ({x, y, z, t} : Finset ι).erase z = {x, y, t} := by
    rw [erase_insert_of_ne hxz, erase_insert_of_ne hyz, erase_insert (notMem_singleton.mpr hzt)]
  have et : ({x, y, z, t} : Finset ι).erase t = {x, y, z} := by
    rw [erase_insert_of_ne hxt, erase_insert_of_ne hyt, erase_insert_of_ne hzt, erase_singleton,
      insert_empty]
  have h := coeff_card_deficitCumulant {x, y, z, t} c hc (by omega)
  rw [hT, show (4 : ℕ) - 1 = 3 from rfl] at h
  rw [sum_congr rfl fun i hi ↦ hidden_term_card_four hT hc hi] at h
  simp only [sum_insert hx, sum_insert hy, sum_pair hzt, ex, ey, ez, et, sum_insert hx2,
    sum_insert hx3, sum_insert hx4, sum_pair hyt, sum_pair hyz, prod_insert hx, prod_insert hy,
    prod_pair hzt] at h
  have hperm : ∀ a b d : ι, ({a, b, d} : Finset ι) = {b, a, d} := fun a b d ↦ insert_comm a b {d}
  have hrot : ∀ a b d : ι, ({a, b, d} : Finset ι) = {d, a, b} := fun a b d ↦ by
    ext m
    simp only [mem_insert, mem_singleton]
    tauto
  have Kyx := coeff_three_fused (j := x) rfl hyz hyt hzt c hcy hcx hcz hct
  have Kzx := coeff_three_fused (j := x) (hperm y z t) hyz.symm hzt hyt c hcz hcx hcy hct
  have Ktx := coeff_three_fused (j := x) (hrot y z t) hyt.symm hzt.symm hyz c hct hcx hcy hcz
  have Kxy := coeff_three_fused (j := y) rfl hxz hxt hzt c hcx hcy hcz hct
  have Kzy := coeff_three_fused (j := y) (hperm x z t) hxz.symm hzt hxt c hcz hcy hcx hct
  have Kty := coeff_three_fused (j := y) (hrot x z t) hxt.symm hzt.symm hxz c hct hcy hcx hcz
  have Kxz := coeff_three_fused (j := z) rfl hxy hxt hyt c hcx hcz hcy hct
  have Kyz := coeff_three_fused (j := z) (hperm x y t) hxy.symm hyt hxt c hcy hcz hcx hct
  have Ktz := coeff_three_fused (j := z) (hrot x y t) hxt.symm hyt.symm hxy c hct hcz hcx hcy
  have Kxt := coeff_three_fused (j := t) rfl hxy hxz hyz c hcx hct hcy hcz
  have Kyt := coeff_three_fused (j := t) (hperm x y z) hxy.symm hyz hxz c hcy hct hcx hcz
  have Kzt := coeff_three_fused (j := t) (hrot x y z) hxz.symm hyz.symm hxy c hcz hct hcx hcy
  simp only [tripleSecond] at Kyx Kzx Ktx Kxy Kzy Kty Kxz Kyz Ktz Kxt Kyt Kzt
  unfold quadSecond
  linear_combination (1 / 4 : ℚ) * h +
    (1 / 4 : ℚ) * ((c x : ℚ) * c y) * Kxy + (1 / 4 : ℚ) * ((c x : ℚ) * c z) * Kxz +
    (1 / 4 : ℚ) * ((c x : ℚ) * c t) * Kxt + (1 / 4 : ℚ) * ((c y : ℚ) * c x) * Kyx +
    (1 / 4 : ℚ) * ((c y : ℚ) * c z) * Kyz + (1 / 4 : ℚ) * ((c y : ℚ) * c t) * Kyt +
    (1 / 4 : ℚ) * ((c z : ℚ) * c x) * Kzx + (1 / 4 : ℚ) * ((c z : ℚ) * c y) * Kzy +
    (1 / 4 : ℚ) * ((c z : ℚ) * c t) * Kzt + (1 / 4 : ℚ) * ((c t : ℚ) * c x) * Ktx +
    (1 / 4 : ℚ) * ((c t : ℚ) * c y) * Kty + (1 / 4 : ℚ) * ((c t : ℚ) * c z) * Ktz

end

end Descent.Pangenome.GraphCoalescent
