/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Pangenome.GraphCoalescent.LambdaLoadClosure

/-! Axiom audit of the Λ-coalescent load closure. -/

open Descent.Pangenome.GraphCoalescent.LambdaLoadClosure

#print axioms subsetProfile
#print axioms subsetProfile_univ
#print axioms sum_subsetProfile
#print axioms filter_biUnion_of_subset_components
#print axioms card_subsets_with_profile
#print axioms boundedProfiles
#print axioms subsetProfile_mem_boundedProfiles
#print axioms sum_prod_choose_eq_choose
#print axioms lumpedLambdaRate
#print axioms filter_mergers_with_profile
#print axioms sum_mergerRates_eq_lumpedLambdaRate
#print axioms sum_mergerRates_eq_of_cellLoad_eq
#print axioms joinedLoad
#print axioms card_touchedBlocks_after_merger
