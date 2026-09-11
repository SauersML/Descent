/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.MechanismReportDerivative

/-! Axiom audit of MechanismReportDerivative. -/

open Descent.Portability.MechanismReportDerivative

#print axioms forwardLaw_shift
#print axioms hasDerivAt_backValue
#print axioms hasDerivAt_report
#print axioms dotProduct_backDeriv_eq_sum
#print axioms mechanism_to_report_derivative
#print axioms hasDerivAt_tiltedRow
#print axioms vecMul_dotProduct_expand
#print axioms centred_tilt_row
#print axioms tilt_term_eq_row_covariance
