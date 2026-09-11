/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.EmpiricalAUCUnbiasedness

/-! Axiom audit of EmpiricalAUCUnbiasedness. -/

open Descent.Portability.EmpiricalAUCUnbiasedness

#print axioms scoreValue_eq_scoreOf
#print axioms outcomeValue_eq_outcomeOf
#print axioms scoreMass_eq_scoreCellMass
#print axioms binaryCaseMass_eq_outcomeMass
#print axioms outcomeMass_add_eq_one
#print axioms caseControl_iff
#print axioms empiricalPairMass_eq_sum
#print axioms outcomeCount_pos
#print axioms outcomeCount_nonneg
#print axioms empiricalPairMass_pos_iff
#print axioms aucDefinedIndicator_expand
#print axioms auc_definedness_probability
#print axioms expectation_empiricalBrier
#print axioms outcomeMass_chronologyLaw
#print axioms auc_definedness_probability_chronologyLaw
#print axioms expectation_empiricalBrier_chronologyLaw
