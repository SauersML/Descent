/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.EndToEndMultiAncestryGWAS

/-! Axiom audit of EndToEndMultiAncestryGWAS. -/

open Descent.Portability.EndToEndMultiAncestryGWAS

#print axioms mixtureLaw
#print axioms mixtureLaw_mass
#print axioms expectation_mixtureLaw
#print axioms covariance_mixtureLaw
#print axioms variance_mixtureLaw
#print axioms mixtureLaw_pointMass
#print axioms betweenWeights
#print axioms marginalWeights_mixtureLaw
#print axioms marginalEffect
#print axioms marginalEffect_mul_tagCovariance
#print axioms marginalEffect_mixtureLaw
#print axioms witnessGenotype
#print axioms witnessOutcome
#print axioms witnessDemeLaw
#print axioms witnessDemeLaw_mass
#print axioms stratificationWitness
#print axioms covariance_linearScore_mixtureWeights
#print axioms trainedCovariance_mixtureLaw
#print axioms tendsto_pooledTrainedCalibrationSlope
#print axioms targetShare
#print axioms expectation_targetShare
#print axioms covariance_targetShare
#print axioms marginalWeights_twoDemeMixture
#print axioms mixtureLaw_targetShare_one
#print axioms pooledMassPolynomial
#print axioms pooledPolynomial
#print axioms eval_pooledPolynomial
#print axioms totalDegree_pooledPolynomial_le
#print axioms pooledTrainedPolynomial
#print axioms polynomialFunction_pooledTrainedPolynomial
#print axioms totalDegree_pooledTrainedPolynomial_le
#print axioms pooledCovariancePolynomial
#print axioms totalDegree_pooledCovariancePolynomial_le
#print axioms expectation_quadraticForm_pooledStateLaw
#print axioms trainedCovariance_pooledStateLaw
#print axioms trainedVariance_pooledStateLaw
#print axioms trainedNumerator_pooledStateLaw
#print axioms trainedDenominator_pooledStateLaw
#print axioms expectedPooledCalibrationSlope
#print axioms expectedPooledAccuracy
#print axioms momentPooledCalibrationSlope
#print axioms momentPooledAccuracy
#print axioms expectedPooledAccuracy_pointMass
#print axioms expectedPooledCalibrationSlope_eq_momentPooledCalibrationSlope
#print axioms expectedPooledAccuracy_eq_momentPooledAccuracy
#print axioms expectedPooledCalibrationSlope_historyEventKernel
#print axioms expectedPooledAccuracy_historyEventKernel
#print axioms expectedPooledCalibrationSlope_eq_of_moments_eq
#print axioms expectedPooledAccuracy_eq_of_moments_eq
#print axioms expectedPooledCalibrationSlope_rateHistoryKernel
#print axioms expectedPooledAccuracy_rateHistoryKernel
