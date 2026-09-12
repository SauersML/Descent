/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Pangenome.GraphCoalescent.HiddenLoadFiltering

/-! Axiom audit of the exact filter and likelihood for the hidden loads. -/

open Descent.Pangenome.GraphCoalescent

#print axioms Descent.Pangenome.GraphCoalescent.visibleLikelihood_cons_apply
#print axioms Descent.Pangenome.GraphCoalescent.filterPosterior_dotProduct_one
#print axioms Descent.Pangenome.GraphCoalescent.filterPosterior_single_dotProduct_one
#print axioms Descent.Pangenome.GraphCoalescent.hasDerivAt_killedPropagator
#print axioms Descent.Pangenome.GraphCoalescent.hasDerivAt_killedPropagator_apply
#print axioms Descent.Pangenome.GraphCoalescent.killedPropagator_apply_eq_zero
#print axioms Descent.Pangenome.GraphCoalescent.killedPropagator_apply_eq_firstJump
#print axioms Descent.Pangenome.GraphCoalescent.transferMatrix_mulVec
#print axioms Descent.Pangenome.GraphCoalescent.choose_two_sum_sub_sum_choose_two
#print axioms Descent.Pangenome.GraphCoalescent.load_internalMerger
#print axioms Descent.Pangenome.GraphCoalescent.load_visibleMerger
#print axioms Descent.Pangenome.GraphCoalescent.loadReport_internalMerger
#print axioms Descent.Pangenome.GraphCoalescent.loadReport_visibleMerger_ne
#print axioms Descent.Pangenome.GraphCoalescent.loadGenerator_mulVec
#print axioms Descent.Pangenome.GraphCoalescent.killedGenerator_mulVec_loadGenerator
#print axioms Descent.Pangenome.GraphCoalescent.transferMatrix_mulVec_loadGenerator
#print axioms Descent.Pangenome.GraphCoalescent.killedGenerator_mulVec_one_loadGenerator
#print axioms Descent.Pangenome.GraphCoalescent.hasDerivAt_posteriorMass_loadGenerator
#print axioms Descent.Pangenome.GraphCoalescent.sum_posterior_mul_visibleRate
#print axioms Descent.Pangenome.GraphCoalescent.hasDerivAt_posteriorMass_observedIntensity
