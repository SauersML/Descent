/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.CylinderHaltingLaw

/-! Axiom audit of CylinderHaltingLaw. -/

open Descent.Portability.CylinderHaltingLaw

#print axioms dyadicWeight_nonneg
#print axioms bitMeasure_real_cylinder_eq_dyadicWeight
#print axioms HaltingProgram.pairwiseDisjoint_cylinder
#print axioms HaltingProgram.law_apply
#print axioms HaltingProgram.isProbabilityMeasure_law
#print axioms HaltingProgram.hasSum_dyadicWeight
#print axioms HaltingProgram.missingMass_eq_tsum_compl
#print axioms HaltingProgram.missingMass_nonneg
#print axioms HaltingProgram.missingMass_eq_bitMeasure
#print axioms HaltingProgram.tendsto_missingMass
#print axioms HaltingProgram.tendsto_missingMass_enumeration
#print axioms HaltingProgram.enumeratedLaw_le_law
#print axioms HaltingProgram.enumeratedLaw_real_univ
#print axioms HaltingProgram.summable_weighted
#print axioms HaltingProgram.integral_law
#print axioms HaltingProgram.integral_law_eq_enumeratedTotal_add
#print axioms tsum_weighted_value_bounds
#print axioms HaltingProgram.expectation_bounds
#print axioms HaltingProgram.conditional_expectation_bounds
#print axioms HaltingProgram.prefixFree_enumeratedWords
#print axioms HaltingProgram.haltingSublaw_missingMass_eq
#print axioms waitingWords_prefixFree
#print axioms exists_waitingWord_cylinder
#print axioms waitingWords_halts_ae
#print axioms waitForTrue
#print axioms waitForTrue_law_singleton
