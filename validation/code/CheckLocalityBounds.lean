/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Pangenome.AncestralLocality.LocalityBounds

/-! Axiom audit of LocalityBounds. -/

open Descent.Pangenome.AncestralLocality

#print axioms weightedCount_branchSupports_le
#print axioms weightedCount_coalesceSupports_le
#print axioms supportGenerator_weightedCount_le
#print axioms supportGenerator_supportSize_le
#print axioms supportDecisionRate_le
#print axioms lightDepth_le_succ
#print axioms lightWeight_le_mul
#print axioms supportGenerator_lightWeight_le
#print axioms pow_le_weightedCount_of_mem_escapeSet
#print axioms replicate_not_mem_escapeSet
#print axioms branchSupports_mem_escapeSet
#print axioms coalesceSupports_mem_escapeSet
#print axioms weightedCount_map_univ
#print axioms supportSize_map_univ
#print axioms supportDecisionRate_map_univ
#print axioms le_mul_exp_of_hasDerivWithinAt
#print axioms le_div_three_mul_exp_sub_one
#print axioms integral_le_mul_exp_of_supportGenerator_le
#print axioms integral_supportSize_le
#print axioms integral_branchings_le
#print axioms integral_lightWeight_le
#print axioms measureReal_escapeSet_le
#print axioms measureReal_escapeSet_le_exp
#print axioms exp_div_pow_eq_of_radius
#print axioms eq_zero_of_forall_le_div_pow
#print axioms eq_zero_of_forall_escape_bound
#print axioms measureReal_preimage_sub_eq
#print axioms abs_measureReal_preimage_sub_le
#print axioms totalVariation_measureReal_fiber_le
