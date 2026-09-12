/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Pangenome.GraphCoalescent.CompressionHiddenStateCount

/-! Axiom audit of the hidden-state count of a pangenome compression. -/

open Descent.Pangenome.GraphCoalescent.CompressionHiddenStateCount

#print axioms reportStateCount
#print axioms coarsestStateCount
#print axioms image_observed_eq_image_fst
#print axioms reportStateCount_le_coarsestStateCount
#print axioms graphKer_le_of_injective
#print axioms observed_of_injective
#print axioms hiddenLoad_of_injective
#print axioms coarsestStateCount_eq_reportStateCount_of_injective
#print axioms coarsestState_blocks_of_two
#print axioms reportStateCount_lt_coarsestStateCount
