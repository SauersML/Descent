/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Pangenome.GraphCoalescent.LeadingCoefficient
import Descent.Pangenome.GraphCoalescent.ConnectivityClockTable

assert_below Descent.PopGen Descent.Spectral Descent.Blindness Descent.Conditionals
assert_below Descent.Portability Descent.Decision Descent.Program

/-!
# Corollaries of Theorem E: the extremal profiles and the table

Theorem E (`LeadingCoefficient.coeff_cumulantOfSizes`) gives the top coefficient of the
connectivity cumulant as `2 (∏_i c_i) (2n − w)! / (2n − 2w + 2)!`. This module draws the two
consequences the note states around it.

The extremal statement. At a fixed total size `n` and a fixed number `w` of fibers the factorial
factor is fixed and positive, so the leading coefficient of one profile is at most that of another
exactly when its product of sizes is (`leadingCoefficient_le_iff_prod_le`, through
`leadingCoefficient_eq_mul_prod`). With `BalancedFiberExtremum.prod_maximal_iff_isBalancedFibers`
this gives `leadingCoefficient_maximal_iff_isBalancedFibers`: a positive profile has the largest
leading coefficient among positive profiles of its total exactly when its sizes are as equal as
possible, and `coeff_cumulantOfSizes_maximal_iff_isBalancedFibers` states the same for the top
coefficient of the corpus cumulant itself. As in the note, this is an early-time statement only.

The table. `ConnectivityClockTable` computes the cumulants of the rows `(1,2)`, `(1,3)`, `(2,2)`
and `(2,2,2)` of §6 by expanding the Lah polynomials, independently of Theorem E.
`table_one_two`, `table_one_three`, `table_two_two` and `table_two_two_two` read the top
coefficients `4`, `6`, `8` and `144` off those rows and evaluate the closed form of (E1) at the
same fiber sizes to the same numbers, so the two computations agree row by row without invoking
Theorem E.

## Empirical status

None. The bodies here are arithmetic on explicit polynomials and on products of natural numbers,
so no measurement can bear on them.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Pangenome.GraphCoalescent

open Finset Polynomial

noncomputable section

/-! ## The extremal profiles -/

/-- The leading coefficient is the product of the fiber sizes times a factor fixed by the total
size and the number of fibers. -/
theorem leadingCoefficient_eq_mul_prod {ι : Type*} [DecidableEq ι] (T : Finset ι) (c : ι → ℕ) :
    leadingCoefficient T c =
      2 * ((2 * (∑ i ∈ T, c i) - #T).factorial : ℚ) /
        ((2 * (∑ i ∈ T, c i) - 2 * #T + 2).factorial : ℚ) * ∏ i ∈ T, (c i : ℚ) := by
  unfold leadingCoefficient
  ring

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

/-- **At a fixed total, the leading coefficient orders profiles by their products.** -/
theorem leadingCoefficient_le_iff_prod_le (c m : κ → ℕ) (hsum : ∑ k, c k = ∑ k, m k) :
    leadingCoefficient (univ : Finset κ) c ≤ leadingCoefficient univ m ↔
      ∏ k, c k ≤ ∏ k, m k := by
  rw [leadingCoefficient_eq_mul_prod, leadingCoefficient_eq_mul_prod, hsum]
  have hfactor : (0 : ℚ) < 2 * ((2 * (∑ k, m k) - #(univ : Finset κ)).factorial : ℚ) /
      ((2 * (∑ k, m k) - 2 * #(univ : Finset κ) + 2).factorial : ℚ) := by
    positivity
  constructor
  · intro h
    have hprod : (∏ k, (c k : ℚ)) ≤ ∏ k, (m k : ℚ) := by
      by_contra hlt
      push_neg at hlt
      nlinarith
    exact_mod_cast hprod
  · intro h
    have hprod : (∏ k, (c k : ℚ)) ≤ ∏ k, (m k : ℚ) := by
      exact_mod_cast h
    exact mul_le_mul_of_nonneg_left hprod hfactor.le

/-- **NOTE §7, the extremal statement.** A positive fiber profile has the largest leading
coefficient among positive profiles with its total exactly when its sizes are balanced. -/
theorem leadingCoefficient_maximal_iff_isBalancedFibers (m : κ → ℕ) (k0 : κ)
    (hm : ∀ k, 1 ≤ m k) :
    (∀ c : κ → ℕ, (∀ k, 1 ≤ c k) → ∑ k, c k = ∑ k, m k →
        leadingCoefficient (univ : Finset κ) c ≤ leadingCoefficient univ m) ↔
      IsBalancedFibers m := by
  rw [← prod_maximal_iff_isBalancedFibers m k0 hm]
  exact forall_congr' fun c ↦ imp_congr_right fun _ ↦ imp_congr_right fun hsum ↦
    leadingCoefficient_le_iff_prod_le c m hsum

/-- **NOTE §7, the extremal statement for the cumulant.** For `w ≥ 2` fibers, a positive profile
has the largest top coefficient `[z^{n − w + 1}] C_c(z)` among positive profiles with its total
exactly when its sizes are balanced. -/
theorem coeff_cumulantOfSizes_maximal_iff_isBalancedFibers (m : κ → ℕ) (k0 : κ)
    (hm : ∀ k, 1 ≤ m k) (hw : 2 ≤ #(univ : Finset κ)) :
    (∀ c : κ → ℕ, (∀ k, 1 ≤ c k) → ∑ k, c k = ∑ k, m k →
        ((cumulantOfSizes (univ : Finset κ) c).coeff (∑ k, c k - #(univ : Finset κ) + 1) : ℚ) ≤
          ((cumulantOfSizes (univ : Finset κ) m).coeff
            (∑ k, m k - #(univ : Finset κ) + 1) : ℚ)) ↔
      IsBalancedFibers m := by
  rw [← leadingCoefficient_maximal_iff_isBalancedFibers m k0 hm]
  refine forall_congr' fun c ↦ imp_congr_right fun hc ↦ imp_congr_right fun _ ↦ ?_
  rw [coeff_cumulantOfSizes univ c hw fun k _ ↦ hc k,
    coeff_cumulantOfSizes univ m hw fun k _ ↦ hm k]

/-! ## The table of §6 against the closed form -/

/-- **Row `(1, 2)`.** The top coefficient of `C_{(1,2)}(z) = 6z + 4z²` is `4`, the value of the
closed form of (E1). -/
theorem table_one_two :
    (cumulantOfSizes (univ : Finset (Fin 2)) ![1, 2]).coeff 2 = 4 ∧
      leadingCoefficient (univ : Finset (Fin 2)) ![1, 2] = 4 := by
  have hfour : Nat.factorial 4 = 24 := rfl
  refine ⟨?_, ?_⟩
  · rw [ConnectivityClockTable.connectivityCumulant_one_two]
    norm_num [Polynomial.coeff_X, Polynomial.coeff_X_pow]
  · norm_num [leadingCoefficient, Fin.sum_univ_two, Fin.prod_univ_two, hfour]

/-- **Row `(1, 3)`.** The top coefficient of `C_{(1,3)}(z) = 24z + 30z² + 6z³` is `6`, the value
of the closed form of (E1). -/
theorem table_one_three :
    (cumulantOfSizes (univ : Finset (Fin 2)) ![1, 3]).coeff 3 = 6 ∧
      leadingCoefficient (univ : Finset (Fin 2)) ![1, 3] = 6 := by
  have hsix : Nat.factorial 6 = 720 := rfl
  refine ⟨?_, ?_⟩
  · rw [ConnectivityClockTable.connectivityCumulant_one_three]
    norm_num [Polynomial.coeff_X, Polynomial.coeff_X_pow]
  · norm_num [leadingCoefficient, Fin.sum_univ_two, Fin.prod_univ_two, hsix]

/-- **Row `(2, 2)`.** The top coefficient of `C_{(2,2)}(z) = 24z + 32z² + 8z³` is `8`, the value
of the closed form of (E1). -/
theorem table_two_two :
    (cumulantOfSizes (univ : Finset (Fin 2)) ![2, 2]).coeff 3 = 8 ∧
      leadingCoefficient (univ : Finset (Fin 2)) ![2, 2] = 8 := by
  have hsix : Nat.factorial 6 = 720 := rfl
  refine ⟨?_, ?_⟩
  · rw [ConnectivityClockTable.connectivityCumulant_two_two]
    norm_num [Polynomial.coeff_X, Polynomial.coeff_X_pow]
  · norm_num [leadingCoefficient, Fin.sum_univ_two, Fin.prod_univ_two, hsix]

/-- **Row `(2, 2, 2)`.** The top coefficient of `C_{(2,2,2)}(z) = 720z + 1656z² + 928z³ + 144z⁴`
is `144`, the value of the closed form of (E1). -/
theorem table_two_two_two :
    (cumulantOfSizes (univ : Finset (Fin 3)) ![2, 2, 2]).coeff 4 = 144 ∧
      leadingCoefficient (univ : Finset (Fin 3)) ![2, 2, 2] = 144 := by
  have height : Nat.factorial 8 = 40320 := rfl
  have hnine : Nat.factorial 9 = 362880 := rfl
  have hsizes : (![2, 2, 2] : Fin 3 → ℕ) = fun _ ↦ 2 := by
    funext i
    fin_cases i <;> rfl
  refine ⟨?_, ?_⟩
  · rw [ConnectivityClockTable.connectivityCumulant_two_two_two]
    norm_num [Polynomial.coeff_X, Polynomial.coeff_X_pow]
  · rw [hsizes]
    norm_num [leadingCoefficient, Finset.sum_const, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin, height, hnine]

end

end Descent.Pangenome.GraphCoalescent
