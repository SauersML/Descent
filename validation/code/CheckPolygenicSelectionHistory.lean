/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.PolygenicSelectionHistory

/-! Axiom audit of PolygenicSelectionHistory. -/

open Descent.Portability.PolygenicSelectionHistory

#print axioms norm_sub_firstOrder_sum_step_le
#print axioms norm_duhamel_firstOrder_sum_le
#print axioms crossRatioDerivative_add
#print axioms crossRatioDerivative_sum
#print axioms locusModel
#print axioms additiveFitness
#print axioms additiveDrift
#print axioms eval_additiveDrift
#print axioms additiveSelectionGenerator
#print axioms additiveDrift_eq_sum
#print axioms additiveSelectionGenerator_eq_sum
#print axioms additiveSelectedGenerator
#print axioms expectedAdditiveSelectedGenerator_eq
#print axioms norm_expectedMomentVector_sub_propagator_le_additive
#print axioms AdditiveSelectedOnHistory
#print axioms additiveSelectedOnHistory_nil
#print axioms norm_additiveHistory_sub_propagator_le
#print axioms norm_expectedMomentVector_sub_firstOrder_le_additive
#print axioms expectedMomentVector_pulse
#print axioms additiveHistoryCorrection
#print axioms norm_additiveHistory_sub_firstOrder_le
#print axioms portabilityFirstOrder_sum
#print axioms portabilityFirstOrder_additiveHistoryCorrection
#print axioms abs_additivePortability_sub_firstOrder_le
#print axioms additivePortabilityFirstOrder_pos_iff
#print axioms additivePortabilityFirstOrder_pos_of_forall
