/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.UnboundedSlopeExample

/-! Axiom audit of UnboundedSlopeExample. -/

open Descent.Portability.UnboundedSlopeExample

#print axioms outcomeExp_apply
#print axioms outcomeExp_mean_score
#print axioms outcomeExp_mean_outcome
#print axioms outcomeExp_variance_score
#print axioms outcomeExp_variance_outcome
#print axioms outcomeExp_covariance
#print axioms outcomeExp_squared_correlation
#print axioms replicaExp_apply
#print axioms rankAccuracy_eq_one
#print axioms conditionalSlope_closed
#print axioms conditionalSlope_eq_inv
#print axioms measurable_conditionalSlope
#print axioms conditionalSlope_not_integrableOn
#print axioms lintegral_conditionalSlope_eq_top
