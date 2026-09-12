/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.EndToEndGWASTrainingLaw

/-! Axiom audit of EndToEndGWASTrainingLaw. -/

open Descent.Portability.EndToEndGWASTrainingLaw

#print axioms expectation_prod_reading
#print axioms expectation_four_eq_zero
#print axioms sampleCovariance_eq_diagonal_sub_offDiagonal
#print axioms expectation_sampleCovariance
#print axioms expectation_sampleCovariance_mul
#print axioms fourthCoMoment_eq_pairExpectation
#print axioms plugInCovariance_eq
#print axioms expectation_gwasWeights
#print axioms expectation_gwasWeights_mul
#print axioms expectation_quadraticForm_gwasWeights
#print axioms trainedNumerator_eq
#print axioms trainedDenominator_eq
#print axioms plugInAccuracy_eq_trainedAccuracy
#print axioms quadraticForm_weightPairing
#print axioms quadraticForm_weightExcess
#print axioms sum_denominatorMatrix_mul_nonneg
#print axioms samplingForm_antitone
#print axioms tendsto_samplingForm
#print axioms samplingForm_div_le_iff
#print axioms trainedNumerator_antitone
#print axioms trainedDenominator_antitone
#print axioms le_trainedNumerator
#print axioms le_trainedDenominator
#print axioms tendsto_trainedAccuracy
#print axioms trainedAccuracy_unique
#print axioms populationAccuracy_lt_trainedAccuracy
#print axioms trainingWitness_accuracy
