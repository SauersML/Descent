/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.StageCompositionKernel

/-! Axiom audit of StageCompositionKernel. -/

open Descent.Portability.StageCompositionKernel

#print axioms apply_compose
#print axioms apply_reindex
#print axioms apply_idleKernel
#print axioms apply_composeDependentStages_zero
#print axioms apply_composeDependentStages_succ
#print axioms apply_composeStages_zero
#print axioms apply_composeStages_succ
#print axioms apply_linearCombination
#print axioms abs_mulVec_le
#print axioms stageRow_le_totalMass
#print axioms sum_abs_slack_tendsto
#print axioms compose_expansion
#print axioms abs_compositeSlack_tendsto
#print axioms composeDependentStages_expansion
#print axioms composeStages_expansion
#print axioms composedMicroscopicApproximation
