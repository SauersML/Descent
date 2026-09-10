/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.FiniteNumericalCertificate

/-! Axiom audit of finite numerical and conditioning certificates. -/

open Descent.Portability.FiniteNumericalCertificate

#print axioms expectation_difference
#print axioms abs_expectation_le
#print axioms expectation_bounded
#print axioms residual
#print axioms backward_residual_identity
#print axioms backward_residual_bound
#print axioms totalVariation_symm
#print axioms totalVariation_triangle
#print axioms totalVariation_bind
#print axioms totalVariation_kernel_change
#print axioms propagation_perturbation
