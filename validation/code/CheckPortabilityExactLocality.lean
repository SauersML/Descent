/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.PortabilityExactLocality

/-! Axiom audit of PortabilityExactLocality. -/

open Descent.Portability.PortabilityExactLocality

#print axioms lociWithin_univ
#print axioms dualTransitions_lociWithin
#print axioms dualGenerator_eq_zero_of_not_lociWithin
#print axioms localRestriction_mul_dualGenerator
#print axioms localRestriction_mul_matrixExponential
#print axioms matrixExponential_mulVec_eq_of_rows_eqOn
#print axioms expectedMomentVector_eq_of_rows_eqOn
#print axioms splits_congr
#print axioms splitValue_congr
#print axioms sum_map_recombinationMoves
#print axioms sum_recombination_mul_splitValue_eq
#print axioms mutationMoves_eq_of_agreeOn
#print axioms transitionSum_eq_of_agreeOn
#print axioms dualGenerator_eq_of_agreeOn
#print axioms expectedMomentVector_eq_of_agreeOn
