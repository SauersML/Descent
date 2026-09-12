/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Pangenome.GraphCoalescent.LeadingCoefficient

/-! Axiom audit of LeadingCoefficient, and the table rows of NOTE §6 read against (E1). -/

open Descent.Pangenome.GraphCoalescent

#print axioms deficitPolynomial_coeff
#print axioms deficitPolynomial_coeff_zero
#print axioms natDegree_deficitPolynomial_le
#print axioms derivative_deficitPolynomial
#print axioms reflect_deficitPolynomial
#print axioms reflect_finset_sum
#print axioms reflect_prod_deficitPolynomial
#print axioms sum_parts_sum
#print axioms one_le_block_size
#print axioms map_cumulantOfSizes
#print axioms coeff_zero_deficitCumulant
#print axioms derivative_finset_prod
#print axioms cast_sum_mul_sub_one
#print axioms notMem_of_mem_erase_part
#print axioms prod_parts_update_pred
#print axioms prod_parts_ite_pred
#print axioms derivative_prod_parts
#print axioms sum_finpartition_eq_of_eq
#print axioms part_copy
#print axioms sum_part_eq_part
#print axioms fused_product
#print axioms derivative_deficitCumulant
#print axioms update_pred_pos
#print axioms update_fuse_pos
#print axioms coeff_deficitCumulant_eq_zero
#print axioms coeff_deficitCumulant_recursion
#print axioms card_le_sum_sizes
#print axioms sum_fused_sizes
#print axioms prod_fused_sizes
#print axioms sum_pairs_sizes
#print axioms sum_pairs_leadingCoefficient
#print axioms coeff_deficitCumulant_top
#print axioms coeff_cumulantOfSizes
#print axioms coeff_connectivityCumulant_top

theorem factorial_four : Nat.factorial 4 = 24 := rfl
theorem factorial_six : Nat.factorial 6 = 720 := rfl
theorem factorial_eight : Nat.factorial 8 = 40320 := rfl
theorem factorial_nine : Nat.factorial 9 = 362880 := rfl

/-- Table row `(1, 2)`: `C_c(z) = 6z + 4z^2`, top coefficient `4`. -/
example : ((cumulantOfSizes (Finset.univ : Finset (Fin 2)) ![1, 2]).coeff 2 : ℚ) = 4 := by
  have h := coeff_cumulantOfSizes (Finset.univ : Finset (Fin 2)) ![1, 2] (by simp)
    (by intro i _; fin_cases i <;> simp)
  norm_num [leadingCoefficient, Fin.sum_univ_two, Fin.prod_univ_two, factorial_four] at h
  exact h

/-- Table row `(1, 3)`: `C_c(z) = 24z + 30z^2 + 6z^3`, top coefficient `6`. -/
example : ((cumulantOfSizes (Finset.univ : Finset (Fin 2)) ![1, 3]).coeff 3 : ℚ) = 6 := by
  have h := coeff_cumulantOfSizes (Finset.univ : Finset (Fin 2)) ![1, 3] (by simp)
    (by intro i _; fin_cases i <;> simp)
  norm_num [leadingCoefficient, Fin.sum_univ_two, Fin.prod_univ_two, factorial_six] at h
  exact h

/-- Table row `(2, 2)`: `C_c(z) = 24z + 32z^2 + 8z^3`, top coefficient `8`. -/
example : ((cumulantOfSizes (Finset.univ : Finset (Fin 2)) ![2, 2]).coeff 3 : ℚ) = 8 := by
  have h := coeff_cumulantOfSizes (Finset.univ : Finset (Fin 2)) ![2, 2] (by simp)
    (by intro i _; fin_cases i <;> simp)
  norm_num [leadingCoefficient, Fin.sum_univ_two, Fin.prod_univ_two, factorial_six] at h
  exact h

/-- Table row `(2, 2, 2)`: `C_c(z) = 720z + 1656z^2 + 928z^3 + 144z^4`, top coefficient `144`. -/
example : ((cumulantOfSizes (Finset.univ : Finset (Fin 3)) fun _ ↦ 2).coeff 4 : ℚ) = 144 := by
  have h := coeff_cumulantOfSizes (Finset.univ : Finset (Fin 3)) (fun _ ↦ 2) (by simp)
    (fun _ _ ↦ by norm_num)
  norm_num [leadingCoefficient, Finset.sum_const, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin, factorial_eight, factorial_nine] at h
  exact h
