/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Pangenome.AncestralLocality.LocalityTransition

/-! Axiom audit of LocalityTransition. -/

open Descent.Pangenome.AncestralLocality

#print axioms card_potentialEdges
#print axioms edgeWeight_eq_prod
#print axioms graphExpect_indicator_subset
#print axioms graphExpect_const_one
#print axioms graphExpect_mono
#print axioms graphExpect_sum
#print axioms reach_eq_biUnion
#print axioms card_reach_le_sum
#print axioms card_pathEdges
#print axioms pathEdges_subset
#print axioms reach_singleton_subset_biUnion
#print axioms card_reach_singleton_le_sum
#print axioms graphExpect_card_presentPaths
#print axioms descFactorial_mul_div_pow_le
#print axioms graphExpect_card_reach_singleton_le
#print axioms graphExpect_card_reach_le
#print axioms degreeRate_pos
#print axioms degreeRate_eq_zero
#print axioms sum_degreeRate
#print axioms iSup_sum_degreeRate_le
#print axioms lt_survivalMap_of_lt
#print axioms survivalMap_lt_self
#print axioms exists_survivalMap_eq_self
#print axioms survivalMap_root_unique
#print axioms eq_giantFraction
#print axioms existsUnique_survival_root
