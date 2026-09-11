/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.PartialHaplotypeMicroscopicApproximation

/-! Axiom audit of PartialHaplotypeMicroscopicApproximation. -/

open Descent.Portability.PartialHaplotypeMicroscopicApproximation

#print axioms one_le_stageCount
#print axioms driftFraction_mem
#print axioms resamplingFraction_mem
#print axioms apply_neutralMicroscopicKernel
#print axioms sum_coalescence_nonneg
#print axioms smallStep_pos
#print axioms mul_denominator_le_one
#print axioms driftFraction_of_le
#print axioms resamplingFraction_of_le
#print axioms smallConstant_nonneg
#print axioms eval_neutralGenerator_eq
#print axioms expansion_small
#print axioms expansion_large
#print axioms momentBound_spec
#print axioms generatorBound_spec
#print axioms continuous_budgetMomentFeature
#print axioms dualPropagator_mem_realizationBody
#print axioms exists_realizedLaw
#print axioms realizedLaw_spec
#print axioms expectedMomentVector_realizedExpectation
#print axioms realizedExpectation_forward
