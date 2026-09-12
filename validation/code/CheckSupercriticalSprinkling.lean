/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Pangenome.AncestralLocality.SupercriticalSprinkling

/-! Axiom audit of SupercriticalSprinkling. -/

open Descent.Pangenome.AncestralLocality

#print axioms subsetExpect_union
#print axioms graphExpect_union
#print axioms card_pairsBetween
#print axioms graphProb_disjoint_pairsBetween
#print axioms reachable_union_of_not_disjoint
#print axioms graphProb_not_joined_le
#print axioms graphProb_not_exists_card_reach_ge_le
#print axioms tendsto_sq_mul_exp_neg_rpow
#print axioms tendsto_graphProb_exists_card_reach_ge
