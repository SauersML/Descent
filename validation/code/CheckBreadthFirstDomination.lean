/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Pangenome.AncestralLocality.BreadthFirstDomination

/-! Axiom audit of BreadthFirstDomination. -/

open Descent.Pangenome.AncestralLocality

#print axioms graphExpect_eq_subsetExpect
#print axioms subsetExpect_const
#print axioms subsetExpect_mono
#print axioms subsetExpect_insert
#print axioms subsetExpect_split
#print axioms subsetExpect_eq_of_local
#print axioms subsetExpect_pow_card
#print axioms subsetExpect_card
#print axioms graphProb_nonneg
#print axioms layer_succ'
#print axioms unexplored_succ
#print axioms layer_eq_empty_of_le
#print axioms mem_layers_of_adj
#print axioms reach_subset_biUnion_layer
#print axioms crossEdges_subset_potentialEdges
#print axioms card_crossEdges_le
#print axioms card_nextLayer_le
#print axioms layer_congr
#print axioms graphExpect_nextLayer
#print axioms gwExtinct_mem_Icc
#print axioms gwExtinct_pow_le_graphProb_layer_eq_empty
#print axioms graphExpect_card_layer_le
#print axioms graphProb_card_reach_ge_le
