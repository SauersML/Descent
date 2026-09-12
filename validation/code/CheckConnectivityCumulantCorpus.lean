/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Pangenome.GraphCoalescent.ConnectivityCumulantCorpus

/-! Axiom audit of ConnectivityCumulantCorpus. -/

open Descent.Pangenome.GraphCoalescent

#print axioms part_ofSetoid_eq_iff
#print axioms ker_part_ofSetoid
#print axioms ofSetoid_ker_part
#print axioms statePartitionEquiv
#print axioms ofSetoid_le_ofSetoid_iff
#print axioms ofSetoid_top
#print axioms observed_eq_top_iff_reportConnected
#print axioms connectivityCumulant_graphKer_eq_sum_observed
#print axioms natDegree_connectivityCumulant_graphKer_le
#print axioms coeff_connectivityCumulant_graphKer
