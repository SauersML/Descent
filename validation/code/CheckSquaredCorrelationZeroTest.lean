/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.SquaredCorrelationZeroTest

/-! Axiom audit of SquaredCorrelationZeroTest. -/

open Descent.Portability.SquaredCorrelationZeroTest

#print axioms scoreVar_eq_signOf
#print axioms outcomeVar_eq_signOf_mul
#print axioms signPairLaw_apply
#print axioms signPairLaw_mean_score
#print axioms signPairLaw_mean_outcome
#print axioms signPairLaw_variance_score
#print axioms signPairLaw_variance_outcome
#print axioms signPairLaw_covariance
#print axioms signPairLaw_squared_correlation
#print axioms signPairLaw_squared_correlation_eq_zero_iff
