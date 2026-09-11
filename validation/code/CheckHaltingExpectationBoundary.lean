/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.HaltingExpectationBoundary

/-! Axiom audit of HaltingExpectationBoundary. -/

open Descent.Portability.HaltingExpectationBoundary

#print axioms drawProbability_tsum
#print axioms firstHalt_iff
#print axioms isSome_evaln_mono
#print axioms firstHalt_unique
#print axioms exists_firstHalt
#print axioms dom_of_firstHalt
#print axioms drawProbability_mul_payout
#print axioms expectedPayout_eq_one_of_dom
#print axioms expectedPayout_eq_zero_of_not_dom
#print axioms expectedPayout_eq_one_iff
#print axioms expectedPayout_eq_pointMass_expectation
#print axioms dom_iff_half_lt_of_approximates
#print axioms not_computable_rational_approximation
