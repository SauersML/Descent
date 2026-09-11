/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Pangenome.GraphCoalescent.MultiInterfaceClosure

/-! Axiom audit of MultiInterfaceClosure. -/

open Descent.Pangenome.GraphCoalescent.MultiInterfaceClosure

#print axioms le_commonRefinement
#print axioms commonRefinement_le_observed
#print axioms observed_commonRefinement
#print axioms card_blockPairs_with_cells
#print axioms card_mergers_eq_lumpedMergerCount
#print axioms card_mergers_eq_of_cellLoad_eq
#print axioms card_blockMergers_eq
