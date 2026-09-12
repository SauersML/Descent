/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Pangenome.AncestralLocality.RootExchangeability

/-! Axiom audit of RootExchangeability. -/

open Descent.Pangenome.AncestralLocality

#print axioms mapEdges_symm_mapEdges
#print axioms mapEdges_mapEdges_symm
#print axioms mapEdges_subset
#print axioms card_mapEdges
#print axioms graphExpect_comp_mapEdges
#print axioms reach_mapEdges
#print axioms mem_bigSet_iff
#print axioms bigSet_mapEdges
#print axioms exists_perm_image_eq
#print axioms graphProb_disjoint_bigSet_eq
#print axioms sum_powersetCard_indicator_disjoint
#print axioms choose_mul_graphProb_disjoint_bigSet
#print axioms choose_div_choose_eq
#print axioms descFactorial_mul_pow_le
#print axioms descFactorial_cast_pos
#print axioms choose_div_choose_le
#print axioms pow_le_choose_div_choose
#print axioms abs_choose_div_choose_sub_pow_le
