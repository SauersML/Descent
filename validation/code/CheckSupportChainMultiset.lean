/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Pangenome.AncestralLocality.SupportChainMultiset

/-! Axiom audit of SupportChainMultiset. -/

open Descent.Pangenome.AncestralLocality

#print axioms map_univ_update
#print axioms sum_powersetCard_two_eq_sum_lt
#print axioms sum_slot_pairs_eq_sum_powersetCard
#print axioms weightedCount_supportsOf
#print axioms slotsVacant_supportChainStart
#print axioms slotsVacant_supportChainBranch
#print axioms slotsVacant_coalesceTags
#print axioms supportsOf_supportChainBranch
#print axioms supportsOf_coalesceTags
#print axioms supportsOf_mem_escapeSet_iff
#print axioms supportChainGenerator_mulVec_comp_supportsOf
#print axioms supportChainLaw_eq_zero_of_not_slotsVacant
#print axioms hasDerivAt_sum_supportChainLaw_mul_supportsOf
#print axioms sum_supportChainLaw_frozen_le
#print axioms tendsto_sum_supportChainLaw_frozen
#print axioms isProbabilityMeasure_supportChainMeasure
#print axioms measureReal_supportChainMeasure_escapeSet
#print axioms norm_operator_sub_le_lightConeEscape_of_supportChain
#print axioms InfiniteGenomeLimit.LightConeApproximation.ofSupportChain
