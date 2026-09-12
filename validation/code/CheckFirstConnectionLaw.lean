/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Pangenome.GraphCoalescent.FirstConnectionLaw

/-! Axiom audit of FirstConnectionLaw. -/

open Descent.Pangenome.GraphCoalescent

#print axioms reportConnectedProbability_eq_connectedByLevel
#print axioms reportConnectedProbability_one
#print axioms reportConnectedProbability_self
#print axioms reportConnectedProbability_eq_zero_of_degree_lt
#print axioms le_of_mem_support_jumpLaw
#print axioms firstConnectionProbability_eq_sub
#print axioms firstConnectionProbability_eq_firstConnectionLaw
#print axioms firstConnectionProbability_nonneg
#print axioms sum_firstConnectionProbability
