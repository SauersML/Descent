/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Pangenome.AncestralLocality.SelectionLightCone

/-! Axiom audit of SelectionLightCone. -/

open Descent.Pangenome.AncestralLocality

#print axioms tagWeight_selectionChainBranch_le
#print axioms selectionChainBranch_count_le
#print axioms selectionChainRate_zero
#print axioms selectionChainRate_nonneg
#print axioms selectionChainGenerator_apply_nonneg
#print axioms selectionChainGenerator_mulVec
#print axioms selectionChainGenerator_tagWeight_le
#print axioms selectionChainGenerator_count_le
#print axioms selectionChainLaw_zero
#print axioms hasDerivAt_sum_selectionChainLaw_mul
#print axioms selectionChainLaw_nonneg
#print axioms sum_selectionChainLaw
#print axioms sum_selectionChainLaw_mul_tagCount_le
#print axioms le_mul_div_mul_exp_sub_one
#print axioms sum_selectionChainLaw_mul_count_le
#print axioms sum_selectionChainLaw_mul_lightWeight_le
#print axioms sum_selectionChainLaw_escape_le
#print axioms sum_selectionChainLaw_escape_le_shift
#print axioms sum_selectionChainLaw_escape_le_radius
#print axioms sum_selectionChainLaw_escape_eq_zero
