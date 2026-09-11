/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.PoissonTruncationCertificate

/-! Axiom audit of PoissonTruncationCertificate. -/

open Descent.Portability.PoissonTruncationCertificate

#print axioms matrixExponential_smul_matrix
#print axioms matrixExponential_eq_poissonMixture
#print axioms partialSum_apply
#print axioms exponential_apply_tsum
#print axioms scaled_uniformization_nonneg
#print axioms poissonTruncation_nonneg
#print axioms poissonTruncation_le_exponential
#print axioms rowMass_mul
#print axioms rowMass_mul_of_constant
#print axioms poissonTruncation_rowSum_eq_series
#print axioms rowSum_deficit_le
#print axioms retainedPoissonMass_nonneg
#print axioms retainedPoissonMass_le_one
#print axioms poissonTruncation_rowSum_le_retained
#print axioms retainedMassCertificate_of_substochastic
#print axioms retainedMassCertificate_one
#print axioms RetainedMassCertificate.mul
#print axioms poissonTruncation_certificate
#print axioms poissonTruncation_epochProduct_certificate
#print axioms poissonTruncation_rowSum_eq_retained
#print axioms poissonTruncation_epochProduct_rowSum_eq
