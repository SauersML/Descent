/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Pangenome.AncestralLocality.SupercriticalUpperBound

/-! Axiom audit of SupercriticalUpperBound. -/

open Descent.Pangenome.AncestralLocality

#print axioms poissonExtinct_mem
#print axioms poissonExtinct_monotone
#print axioms tendsto_poissonExtinct
#print axioms eventually_poissonExtinct_sub_le_gwExtinct
#print axioms pow_sub_pow_le_mul_sub
#print axioms eventually_forall_graphProb_card_reach_ge_le
#print axioms eventually_graphProb_card_reach_ge_le
#print axioms eventually_forall_graphProb_card_reach_singleton_ge_le
#print axioms eventually_graphProb_card_reach_singleton_ge_le
#print axioms limsup_graphProb_card_reach_ge_le
#print axioms limsup_graphProb_card_reach_singleton_ge_le
