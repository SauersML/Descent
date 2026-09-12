/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Pangenome.GraphCoalescent.MultiplicativeConnectionPerturbation

/-! Axiom audit of MultiplicativeConnectionPerturbation. -/

open Descent.Pangenome.GraphCoalescent

#print axioms ite_blockMap_mul_blockMass_mass
#print axioms two_mul_sum_crossing_eq_mass
#print axioms two_mul_pairProductSum_blockMass_crossing
#print axioms sum_filter_le_massStep
#print axioms sum_filter_le_massStep_of_not_le
#print axioms massLaw
#print axioms multiplicativeLaw_eq_massLaw
#print axioms sum_filter_le_massLaw
#print axioms sum_massLaw_mul_top
#print axioms hasSum_poissonPMFReal_mul_massTop
#print axioms sum_massLaw_mul_eq_fst
#print axioms sum_massLaw_mul_eq_snd
#print axioms abs_sub_massConnection_le
#print axioms abs_reportConnectionProbability_sub_spread_le
