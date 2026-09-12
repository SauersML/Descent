/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Pangenome.GraphCoalescent.ConnectivityCumulantDegree

/-! Axiom audit of ConnectivityCumulantDegree. -/

open Descent.Pangenome.GraphCoalescent

#print axioms card_parts_mergeParts
#print axioms le_mergeParts
#print axioms erase_part_mem_insert_parts
#print axioms part_insertAt
#print axioms card_parts_insertAt_empty
#print axioms card_parts_insertAt_of_mem
#print axioms insertAt_le
#print axioms card_parts_add_card_parts_le
#print axioms card_parts_add_card_parts_le_of_connected
#print axioms coeff_connectivityCumulant_eq_zero
#print axioms natDegree_connectivityCumulant_le
