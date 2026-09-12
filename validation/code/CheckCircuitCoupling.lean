/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Pangenome.AncestralLocality.CircuitCoupling

/-! Axiom audit of Corollary 8.1 for the circuit's own laws. -/

open Descent.Pangenome.AncestralLocality

#print axioms Descent.Pangenome.AncestralLocality.unfilledSlotsEmpty_supportChainStart
#print axioms Descent.Pangenome.AncestralLocality.unfilledSlotsEmpty_supportChainStep
#print axioms Descent.Pangenome.AncestralLocality.mem_escapeSet_map_iff
#print axioms Descent.Pangenome.AncestralLocality.mem_lightBall_of_not_escaped
#print axioms Descent.Pangenome.AncestralLocality.supportChainStep_escaped
#print axioms Descent.Pangenome.AncestralLocality.foldl_supportChainStep_escaped
#print axioms Descent.Pangenome.AncestralLocality.truncatedSupportChainStep_eq
#print axioms Descent.Pangenome.AncestralLocality.foldl_truncatedSupportChainStep_eq
#print axioms Descent.Pangenome.AncestralLocality.totalVariation_supportChainLaw_inputs_le
#print axioms
  Descent.Pangenome.AncestralLocality.totalVariation_supportChainLaw_inputs_le_radius
#print axioms Descent.Pangenome.AncestralLocality.totalVariation_truncatedSupportChain_le
#print axioms Descent.Pangenome.AncestralLocality.totalVariation_truncatedSupportChain_le_exp
