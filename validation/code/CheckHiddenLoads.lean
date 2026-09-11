/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Pangenome.GraphCoalescent.HiddenLoads

/-! Axiom audit of HiddenLoads. -/

open Descent.Pangenome.GraphCoalescent

#print axioms reportComponent_mk
#print axioms mk_mem_hiddenBlocks_iff
#print axioms sum_hiddenLoad
#print axioms hiddenLoad_pos
#print axioms hiddenLoad_bot
#print axioms observed_merge_of_rel
#print axioms observed_merge_of_not_rel
#print axioms observed_eq_or_covers
#print axioms hiddenBlocks_mk
#print axioms card_image_mk_merge
#print axioms card_image_mergeMap
#print axioms merge_rel_iff_of_not_rel
#print axioms hiddenLoad_merge_of_rel_self
#print axioms hiddenLoad_merge_of_rel_of_not_rel
#print axioms hiddenLoad_merge_of_not_rel_self
#print axioms hiddenLoad_merge_of_not_rel_of_not_rel
#print axioms card_merges_of_subset
#print axioms card_merges_across
#print axioms covers_observed_eq_of_mem_invisibleCovers
#print axioms covers_covers_of_mem_visibleCovers
#print axioms card_invisibleCovers
#print axioms card_visibleCovers
#print axioms card_visibleCovers_bot
#print axioms sum_choose_two_add_sum_pairs
#print axioms sum_choose_two_hiddenLoad_add_sum_pairs
