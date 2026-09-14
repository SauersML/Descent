/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.EndToEndCalibrationErrorNonclosure

/-! Axiom audit of EndToEndCalibrationErrorNonclosure. -/

open Descent.Portability.EndToEndCalibrationErrorNonclosure

#print axioms outcomeReport
#print axioms biallelicState
#print axioms caseMass_biallelicState
#print axioms controlMass_biallelicState
#print axioms calibrationError_biallelicState
#print axioms configurationMoment_frequencyLaw
#print axioms firstLaw
#print axioms secondLaw
#print axioms integral_smul_dirac
#print axioms integrable_smul_dirac
#print axioms integral_firstLaw
#print axioms integral_secondLaw
#print axioms firstLaw_isProbabilityMeasure
#print axioms secondLaw_isProbabilityMeasure
#print axioms firstKernel
#print axioms secondKernel
#print axioms isMarkovKernel_firstKernel
#print axioms isMarkovKernel_secondKernel
#print axioms frequencyProducts_mixtures_eq
#print axioms momentVector_mixtures_eq
#print axioms eval_eq_budgetCoefficients_dotProduct
#print axioms polynomialsAgreeAt_three
#print axioms continuous_outcomeCalibrationError
#print axioms expectedCalibrationError_firstKernel
#print axioms expectedCalibrationError_secondKernel
#print axioms polynomialsAgreeAt_three_and_expectedCalibrationError_ne
#print axioms not_forall_expectedCalibrationError_eq_of_polynomialsAgreeAt_three
