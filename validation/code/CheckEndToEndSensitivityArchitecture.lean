/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.EndToEndSensitivityArchitecture

/-! Axiom audit of EndToEndSensitivityArchitecture. -/

open Descent.Portability.EndToEndSensitivityArchitecture

#print axioms hasDerivAt_quadraticForm_line
#print axioms hasDerivAt_correlationNumerator_linearScore
#print axioms hasDerivAt_correlationDenominator_linearScore
#print axioms hasDerivAt_portability_linearScore
#print axioms hasDerivAt_accuracy_environmentVariance
#print axioms accuracy_environmentVariance_derivative_neg
#print axioms hasDerivAt_portability_environmentVariance
#print axioms portability_environmentVariance_derivative_neg
