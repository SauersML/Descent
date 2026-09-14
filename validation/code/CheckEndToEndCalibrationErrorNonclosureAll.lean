/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.EndToEndCalibrationErrorNonclosureAll

/-! Axiom audit of EndToEndCalibrationErrorNonclosureAll. -/

open Descent.Portability.EndToEndCalibrationErrorNonclosureAll

#print axioms frequencyStep
#print axioms frequencyStep_pos
#print axioms frequencyStep_mul
#print axioms pointFrequency
#print axioms pointFrequency_mem
#print axioms pointState
#print axioms abs_pointFrequency_sub_half
#print axioms sum_parityMass_sub
#print axioms parityLaw
#print axioms integral_parityLaw
#print axioms isProbabilityMeasure_parityLaw
#print axioms parityKernel
#print axioms isMarkovKernel_parityKernel
#print axioms natDegree_frequencyProduct_le
#print axioms sum_parityMass_products_eq
#print axioms sum_parityMass_momentVector_eq
#print axioms eval_eq_budgetCoefficients_dotProduct_of_le
#print axioms dotProduct_weightedSum
#print axioms polynomialsAgreeAt_parityKernel
#print axioms expectedCalibrationError_parityKernel
#print axioms sum_alternating_abs
#print axioms expectedCalibrationError_parityKernel_sub
#print axioms expectedCalibrationError_parityKernel_ne
#print axioms polynomialsAgreeAt_and_expectedCalibrationError_ne
#print axioms not_forall_expectedCalibrationError_eq_of_polynomialsAgreeAt
