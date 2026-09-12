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
#print axioms mem_loadStates
#print axioms sum_choose_two_add_loadVisibleIntensity
#print axioms choose_two_le_loadVisibleIntensity
#print axioms internalMerge_ne
#print axioms killedLoadGenerator_diag
#print axioms killedLoadGenerator_isMetzler
#print axioms sum_ite_val_eq
#print axioms sum_killedLoadGenerator_internal
#print axioms killedLoadGenerator_mulVec_one
#print axioms killedLoadGenerator_mulVec_one_add_sum_pairs
#print axioms mergedLoad_mem
#print axioms visibleTransfer_mulVec_one
#print axioms visibleTransfer_mulVec_one_eq_prod
#print axioms loadFilter_zero
#print axioms loadFilter_nonneg
#print axioms observedIntensity_eq_posteriorMean
#print axioms posteriorMean_loadVisibleIntensity
#print axioms sum_pairs_posteriorMean
#print axioms hiddenLoad_mem_loadStates
#print axioms sum_choose_two_hiddenLoad_add_loadVisibleIntensity
#print axioms choose_two_le_loadVisibleIntensity_hiddenLoad
