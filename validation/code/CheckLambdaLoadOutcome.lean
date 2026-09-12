/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Pangenome.GraphCoalescent.LambdaLoadOutcome

/-! Axiom audit of LambdaLoadOutcome. -/

open Descent.Pangenome.GraphCoalescent.LambdaLoadOutcome

#print axioms mergeSet_rel_iff
#print axioms le_mergeSet
#print axioms observed_mergeSet_eq
#print axioms sup_mergeSet_eq_of_cells
#print axioms card_image_mk_mergeSet
#print axioms card_image_foldSet
#print axioms cellLoadAt_mergeSet
#print axioms exists_mem_of_subsetProfile_eq
#print axioms multiState_mergeSet_eq_of_profile
#print axioms multiState_mergeSet_eq_lambdaOutcome
#print axioms sum_blockMergerRates_eq_lumpedLambdaRate
#print axioms card_blockMergers_eq_lumpedLambdaRate
