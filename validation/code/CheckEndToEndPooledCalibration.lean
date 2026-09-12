/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.EndToEndPooledCalibration

/-! Axiom audit of EndToEndPooledCalibration. -/

open Descent.Portability.EndToEndPooledCalibration

#print axioms expectation_pooledLaw
#print axioms pooledLaw_mass_historyEventKernel
#print axioms pooledLaw_eq_of_moments_eq
#print axioms covariance_pooledLaw
#print axioms variance_pooledLaw
#print axioms integral_mul_expectation_historyEventKernel
#print axioms momentsOf_pooledLaw_rateHistoryKernel
#print axioms abs_compiledSlope_pooledLaw_rateHistory_sub_le
#print axioms scoreVariance_replicatePopulation
#print axioms calibrationSlope_replicatePopulation
#print axioms expectedDeploymentSlope_eq
#print axioms expectedDeploymentIntercept_eq
#print axioms expectedMinimumRecalibratedMse_eq
#print axioms expectedDeploymentSlope_historyEventKernel
#print axioms expectedDeploymentIntercept_historyEventKernel
#print axioms expectedMinimumRecalibratedMse_historyEventKernel
#print axioms integral_expMse_replicatePopulation
#print axioms integral_deployedMse_eq_pooled
#print axioms integral_deployedMse_historyEventKernel
#print axioms integral_recalibratedMse_ge
#print axioms integral_bestAffineMse_eq
#print axioms pooledPopulation_eq_of_moments_eq
