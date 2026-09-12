/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.TwoLocusPortabilityDecay

/-! Axiom audit of TwoLocusPortabilityDecay. -/

open Descent.Portability.TwoLocusPortabilityDecay

#print axioms sum_mul_matrixExponential_mulVec_of_left_eigen
#print axioms matrixExponential_mulVec_apply_of_row_eq
#print axioms splitHistoryState
#print axioms splitHistoryState_eq
#print axioms splitTransform_DD
#print axioms splitTransform_pi2
#print axioms augmentedLowOrderLDGenerator_DD_row
#print axioms augmentedLowOrderLDGenerator_pi2_row
#print axioms splitHistoryState_DD
#print axioms splitHistoryState_pi2
#print axioms portabilityDecay
#print axioms crossSquaredCorrelation
#print axioms ancestralSquaredCorrelation
#print axioms splitPortabilityRatio
#print axioms crossSquaredCorrelation_eq
#print axioms splitPortabilityRatio_eq
#print axioms portabilityDecay_antitone_duration
#print axioms portabilityDecay_antitone_rate
#print axioms tendsto_portabilityDecay_atTop
#print axioms portabilityDecay_zero_rate
