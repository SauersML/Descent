/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Pangenome.GraphCoalescent.ConnectivityCumulant

/-! Axiom audit of ConnectivityCumulant. -/

open Descent.Pangenome.GraphCoalescent

#print axioms mobiusCoefficient_one
#print axioms mobiusCoefficient_succ_add
#print axioms sum_mobiusCoefficient_finpartition
#print axioms existsUnique_part_superset
#print axioms biUnion_partsWithin
#print axioms partsWithin_biUnion
#print axioms le_partitionCoarsening
#print axioms partitionCoarsening_coarseningPartition
#print axioms coarseningPartition_partitionCoarsening
#print axioms biUnion_injOn
#print axioms card_parts_partitionCoarsening
#print axioms sum_filter_le_eq_sum_partitionCoarsening
#print axioms sum_mobiusCoefficient_upper
#print axioms le_commonCoarsening_iff
#print axioms reportConnected_iff
#print axioms card_parts_eq_one_iff
#print axioms sum_mobiusCoefficient_common
#print axioms bind_le
#print axioms bind_restrictToPart
#print axioms restrictToPart_bind
#print axioms blockWeight_bind
#print axioms sum_le_eq_prod_lahPolynomial
#print axioms connectivityCumulant_eq_sum_connected
#print axioms connectivityCumulant_eq_map_nat
#print axioms coeff_connectivityCumulant_nonneg
#print axioms connectivityCumulant_eq_cumulantOfSizes
