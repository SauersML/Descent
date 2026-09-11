/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.PartialHaplotypeLinearFlow

/-! Axiom audit of PartialHaplotypeLinearFlow. -/

open Descent.Portability.PartialHaplotypeLinearFlow

#print axioms hasDerivAt_eval_path
#print axioms neutralGenerator_of_coalescence_zero
#print axioms migrationDriftMatrix_mulVec
#print axioms mutationDriftMatrix_mulVec
#print axioms eval_driftPolynomial_of_recombination_zero
#print axioms linearDriftMatrix_isMetzler
#print axioms demeTotals_linearDrift
#print axioms demeProjection_mulVec
#print axioms demeProjection_mul_linearDriftMatrix
#print axioms flowPoint_nonneg
#print axioms demeTotals_flowPoint
#print axioms lawPoint_flowLaw
#print axioms flowExpectation_forward
#print axioms flowMoments_eq_matrixExponential
#print axioms migrationMutationRates_moments
