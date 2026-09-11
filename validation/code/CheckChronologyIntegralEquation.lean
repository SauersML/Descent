/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.ChronologyIntegralEquation

/-! Axiom audit of the chronology equations for integrable rates in integral form. -/

open Descent.Portability.ChronologyIntegralEquation

#print axioms exp_sub_exp_le_mul
#print axioms abs_exp_sub_exp_le_of_abs_le
#print axioms integral_norm_le_horizon
#print axioms abs_cumulativeRate_le
#print axioms intervalIntegrable_of_mem_horizon
#print axioms intervalIntegrable_of_locallyIntegrable
#print axioms continuousOn_cumulativeRate
#print axioms continuous_cumulativeRate_of_locallyIntegrable
#print axioms integratingFactorSolution
#print axioms integratingFactorSolution_zero
#print axioms intervalIntegrable_exp_mul
#print axioms continuousOn_integratingFactorSolution
#print axioms hasDerivAt_integratingFactorSolution
#print axioms integratingFactorSolution_eq_integral_of_continuous
#print axioms integratingFactorSolution_eq_integral
#print axioms eq_of_linear_integral_eq
#print axioms continuous_donorFraction
#print axioms continuous_admixtureLinkage
#print axioms donorFraction_eq_integral
#print axioms admixtureLinkage_eq_integral
#print axioms eq_donorFraction_of_integral_eq
#print axioms eq_admixtureLinkage_of_integral_eq
