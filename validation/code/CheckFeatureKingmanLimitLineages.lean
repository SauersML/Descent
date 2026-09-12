/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Pangenome.AncestralLocality.FeatureKingmanLimitLineages

/-! Axiom audit of FeatureKingmanLimitLineages. -/

open Descent.Pangenome.AncestralLocality

#print axioms one_sub_sum_le_prod_range
#print axioms prod_range_le_one_sub_add_sq
#print axioms sum_range_cast_eq_choose_two
#print axioms one_sub_pow_le_choose_two
#print axioms sum_prod_mul_comp_injective
#print axioms sum_uniformSources_const
#print axioms card_image_univ_eq_iff_injective
#print axioms sum_uniformSources_injective
#print axioms sum_uniformSources_card_image
#print axioms uniformSources_indicator_add_le
#print axioms blockTransition_self
#print axioms blockMergeProb_eq
#print axioms blockMergeProb_bounds
#print axioms abs_blockMergeProb_sub_le
#print axioms blockMultiMergeProb_le
#print axioms blockTransition_pred
#print axioms tendsto_mul_blockMergeProb
#print axioms tendsto_mul_blockMultiMergeProb
#print axioms tendsto_mul_blockTransition_pred
#print axioms tendsto_mul_blockTransition_of_add_two_le
#print axioms sum_prod_annotatedLaw_sources
#print axioms sum_prod_annotatedLaw_blockCount
#print axioms sum_prod_annotatedLaw_blockTransition
#print axioms sum_prod_annotatedLaw_blockMergeProb
