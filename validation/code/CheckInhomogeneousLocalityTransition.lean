/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Pangenome.AncestralLocality.InhomogeneousLocalityTransition

/-! Axiom audit of InhomogeneousLocalityTransition. -/

open Descent.Pangenome.AncestralLocality

#print axioms productExpect_const
#print axioms productExpect_indicator_subset
#print axioms productExpect_const_one
#print axioms productExpect_mono
#print axioms productExpect_sum
#print axioms graphExpect_eq_productExpect
#print axioms rankOneKernel_const
#print axioms rankOneRatio_const
#print axioms mean_le_rankOneRatio
#print axioms chungLuProb_nonneg
#print axioms chungLuProb_le_one
#print axioms chungLuProb_le_rankOneKernel
#print axioms productExpect_card_adj_le
#print axioms walkProduct_cons
#print axioms sum_walkProduct_eq_walkWeight
#print axioms walkWeight_succ
#print axioms pathStep_injective
#print axioms prod_pathEdges_eq
#print axioms productExpect_card_presentPaths
#print axioms productExpect_card_presentPaths_le
#print axioms productExpect_card_reach_singleton_le
#print axioms productExpect_card_reach_le
#print axioms productExpect_card_reach_le_of_lt_one
#print axioms sum_productExpect_card_reach_singleton_le
#print axioms productExpect_card_directedReach_le
#print axioms chungLu_card_reach_le_of_lt_one
#print axioms graphExpect_card_reach_le_constantWeight
