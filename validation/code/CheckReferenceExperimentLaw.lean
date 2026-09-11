/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.ReferenceExperimentLaw

/-! Axiom audit of ReferenceExperimentLaw. -/

open Descent.Portability.ReferenceExperimentLaw

#print axioms contextMass_eq_cellWeight
#print axioms contextMass_nonneg
#print axioms drawMass_nonneg
#print axioms drawMass_sum
#print axioms studyMass_nonneg
#print axioms studyMass_sum
#print axioms source_r2_definedProbability
#print axioms source_r2_weightedNumerator
#print axioms source_slope_weightedNumerator
#print axioms source_brier_expectation
#print axioms source_accuracy_expectation
#print axioms riskValue_groupRiskIndex
#print axioms fittedScore_eq_atomScore
#print axioms learnerAtom_count
#print axioms donorCensus_genotypes
#print axioms censusClass_count
#print axioms censusClassMass_pos
#print axioms stateCount_of_pos
#print axioms early_bottleneckMass_pos
#print axioms early_offspringMass_pos
#print axioms late_bottleneckMass_pos
#print axioms late_offspringMass_pos
#print axioms early_stateCount
#print axioms late_stateCount
#print axioms targetMass_nonneg
#print axioms targetMass_sum
#print axioms early_target_r2_definedProbability
