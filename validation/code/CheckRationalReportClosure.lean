/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.RationalReportClosure

/-! Axiom audit of RationalReportClosure. -/

open Descent.Portability.RationalReportClosure

#print axioms rationalValue_ratCast
#print axioms rationalValue_zero
#print axioms rationalValue_one
#print axioms rationalValue_add
#print axioms rationalValue_neg
#print axioms rationalValue_sub
#print axioms rationalValue_mul
#print axioms rationalValue_div
#print axioms rationalValue_sum
#print axioms rationalValue_prod
#print axioms rationalLaw_pointMass
#print axioms rationalValue_expectation
#print axioms rationalLaw_bind
#print axioms rationalLaw_propagate
#print axioms rationalValue_pathMass
#print axioms rationalValue_conditionalMetric
#print axioms RationalReportLaw.rationalLaw_toReal
#print axioms RationalReportLaw.expectation_toReal
#print axioms RationalReportLaw.fairBinaryLaw_expectation
