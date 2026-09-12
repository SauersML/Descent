/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Pangenome.GraphCoalescent.RankedHistoryLaw

/-! Axiom closure of the ranked-history law of the Kingman jump chain, (D4). -/

#print axioms Descent.Pangenome.GraphCoalescent.mem_sampleClass
#print axioms Descent.Pangenome.GraphCoalescent.mem_sampleClass_self
#print axioms Descent.Pangenome.GraphCoalescent.sampleClass_eq_of_rel
#print axioms Descent.Pangenome.GraphCoalescent.prod_card_filter_le
#print axioms Descent.Pangenome.GraphCoalescent.rankWeight_eq_prod_classSize
#print axioms Descent.Pangenome.GraphCoalescent.rankWeight_eq_blockWeight
#print axioms Descent.Pangenome.GraphCoalescent.splitRel_rel_iff
#print axioms Descent.Pangenome.GraphCoalescent.exists_mem_notMem_of_ne
#print axioms Descent.Pangenome.GraphCoalescent.sampleClass_splitRel_of_mem
#print axioms Descent.Pangenome.GraphCoalescent.sampleClass_splitRel_of_mem_sdiff
#print axioms Descent.Pangenome.GraphCoalescent.sampleClass_splitRel_of_notMem
#print axioms Descent.Pangenome.GraphCoalescent.rankWeight_splitRel_mul
#print axioms Descent.Pangenome.GraphCoalescent.covers_splitRel
#print axioms Descent.Pangenome.GraphCoalescent.mem_classMinima
#print axioms Descent.Pangenome.GraphCoalescent.classMinOf_rel
#print axioms Descent.Pangenome.GraphCoalescent.classMinOf_le
#print axioms Descent.Pangenome.GraphCoalescent.classMinOf_mem_classMinima
#print axioms Descent.Pangenome.GraphCoalescent.classMinOf_eq_iff
#print axioms Descent.Pangenome.GraphCoalescent.card_classMinima
#print axioms Descent.Pangenome.GraphCoalescent.sum_card_sampleClass_classMinima
#print axioms Descent.Pangenome.GraphCoalescent.splitRel_merge
#print axioms Descent.Pangenome.GraphCoalescent.exists_canonical_split
#print axioms Descent.Pangenome.GraphCoalescent.splitRel_injective
#print axioms Descent.Pangenome.GraphCoalescent.two_mul_sum_range_succ
#print axioms Descent.Pangenome.GraphCoalescent.two_mul_sum_split_factorial
#print axioms Descent.Pangenome.GraphCoalescent.two_mul_sum_splitIndex
#print axioms Descent.Pangenome.GraphCoalescent.sum_rankWeight_splitRel
#print axioms Descent.Pangenome.GraphCoalescent.two_mul_sum_rankWeight_covers
#print axioms Descent.Pangenome.GraphCoalescent.blockLaw_eq_map
#print axioms Descent.Pangenome.GraphCoalescent.chainLaw_map_getD
#print axioms Descent.Pangenome.GraphCoalescent.blockLaw_succ
#print axioms Descent.Pangenome.GraphCoalescent.jumpLaw_toReal
#print axioms Descent.Pangenome.GraphCoalescent.jumpCoeff_self
#print axioms Descent.Pangenome.GraphCoalescent.rankWeight_bot
#print axioms Descent.Pangenome.GraphCoalescent.blockLaw_toReal
#print axioms Descent.Pangenome.GraphCoalescent.rankedHistoryLaw
#print axioms Descent.Pangenome.GraphCoalescent.blockLaw_toReal_eq_absoluteProb
#print axioms Descent.Pangenome.GraphCoalescent.jumpCoeff_mul_sum_blockWeight
#print axioms Descent.Pangenome.GraphCoalescent.jumpCoeff_mul_lahNumber
#print axioms Descent.Pangenome.GraphCoalescent.sum_blockWeight_ofSetoid_eq_lahNumber
