/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Pangenome.AncestralLocality.ClosureReachability

/-! Axiom audit of ClosureReachability. -/

open Descent.Pangenome.AncestralLocality

#print axioms refinementStep_rel_of_autonomous
#print axioms sum_eq_of_forall_block
#print axioms sum_checkKernel_coord
#print axioms autonomous_coord
#print axioms sum_checkKernel_congr
#print axioms sum_eventKernel_mixedBlocks
#print axioms sum_checkKernel_mixedBlocks_sub
#print axioms mixedBlocks_sub_pos
#print axioms refinementStep_agreeOn
#print axioms refinementStep_agreeOn_empty
#print axioms refinementStep_agreeOn_singleton
#print axioms refinementStep_agreeOn_of_card_le_one
#print axioms iterate_refinementStep_agreeOn_of_card_le_one
#print axioms iterate_grow_eq_reach
#print axioms iterate_refinementStep_agreeOn
#print axioms iterate_refinementStep_agreeOn_eq_reach
#print axioms refinementStep_agreeOn_reach
#print axioms reach_eq_univ_of_connected
#print axioms iterate_refinementStep_eq_univ_of_connected
#print axioms iterate_refinementStep_eq_univ_path
#print axioms not_autonomous_pair
#print axioms not_autonomous_pair_path
#print axioms sum_edgeRates_mul
#print axioms exchange_eq_orderedChild
#print axioms eventKernel_eq_exchangeKernel
#print axioms checkKernel_edgeRates
#print axioms refinementStep_compatibilityKernel_agreeOn
#print axioms iterate_refinementStep_compatibilityKernel_eq_reach
