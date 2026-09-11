/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.ExposureLaplaceConstraints

/-! Axiom audit of the spectral constraints on the admixture coupling. -/

open Descent.Portability.ExposureLaplaceConstraints

#print axioms Descent.Portability.ExposureLaplaceConstraints.exposureLaplace_zero
#print axioms
  Descent.Portability.ExposureLaplaceConstraints.exp_neg_mean_le_exposureLaplace
#print axioms Descent.Portability.ExposureLaplaceConstraints.exp_chord_bound
#print axioms Descent.Portability.ExposureLaplaceConstraints.exposureLaplace_le_chord
#print axioms Descent.Portability.ExposureLaplaceConstraints.exposureLaplace_pointMass
#print axioms Descent.Portability.ExposureLaplaceConstraints.expectation_endpointExposure
#print axioms
  Descent.Portability.ExposureLaplaceConstraints.exposureLaplace_endpointMixture
#print axioms
  Descent.Portability.ExposureLaplaceConstraints.iteratedDeriv_exposureLaplace
#print axioms
  Descent.Portability.ExposureLaplaceConstraints.sign_iteratedDeriv_exposureLaplace
#print axioms Descent.Portability.ExposureLaplaceConstraints.exposureLaplace_sq_le_mul
#print axioms Descent.Portability.ExposureLaplaceConstraints.exposureLaplace_joint_add
#print axioms Descent.Portability.ExposureLaplaceConstraints.exposureLaplace_zeroMixture
#print axioms
  Descent.Portability.ExposureLaplaceConstraints.populationAUC_eq_zeroMixture_laplace
#print axioms
  Descent.Portability.ExposureLaplaceConstraints.exposureLaplace_natCast_eq_sum_exposureMass
#print axioms
  Descent.Portability.ExposureLaplaceConstraints.exposureMass_eq_of_exposureLaplace_natCast_eq
#print axioms
  Descent.Portability.ExposureLaplaceConstraints.exposureMass_eq_of_exposureLaplace_eq
