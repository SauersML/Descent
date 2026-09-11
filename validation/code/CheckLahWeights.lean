/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Pangenome.GraphCoalescent.LahWeights

/-! Axiom audit of LahWeights. -/

open Descent.Pangenome.GraphCoalescent

#print axioms lahNumber_succ_succ
#print axioms lahNumber_succ_zero
#print axioms lahNumber_eq_zero_of_lt
#print axioms lahNumber_succ_mul_factorial
#print axioms lahNumber_mul_factorial
#print axioms coeff_lahPolynomial
#print axioms insertNewPart_parts
#print axioms insertIntoPart_parts
#print axioms mem_removeElement_parts
#print axioms notMem_of_mem_parts
#print axioms not_subset_singleton_of_notMem
#print axioms removeElement_insertAt
#print axioms part_insertAt_erase
#print axioms insertAt_removeElement
#print axioms sum_finpartition_insert
#print axioms blockWeight_insertNewPart
#print axioms blockWeight_insertIntoPart
#print axioms sum_card_add_one_parts
#print axioms finpartition_empty_eq_bot
#print axioms sum_blockWeight_card_eq_lahNumber
#print axioms sum_blockWeight_X_pow_eq_lahPolynomial
#print axioms card_parts_ofSetoid
