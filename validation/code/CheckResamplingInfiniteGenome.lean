/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.ResamplingInfiniteGenome

/-! Axiom audit of ResamplingInfiniteGenome. -/

open Descent.Portability.ResamplingInfiniteGenome

#print axioms precomposeContraction
#print axioms lawFrequencyVector
#print axioms lawFrequencyVector_mem
#print axioms lawFrequency
#print axioms lawFrequency_surjective
#print axioms lawFrequency_injective
#print axioms lawFrequencyHomeomorph
#print axioms lawOperator
#print axioms lawOperator_apply
#print axioms comp_symm_lawFrequency
#print axioms lawOperator_zero
#print axioms lawOperator_add
#print axioms lawOperator_one
#print axioms norm_lawOperator_le
#print axioms tendsto_lawOperator_zero
#print axioms lawFrequency_shrinkLaw
#print axioms lawOperator_shrinkPullback
#print axioms resamplingWindowFamily
#print axioms windowAlgebra_separatesPoints
#print axioms extendedOperator_windowPullback
#print axioms resamplingOperator
#print axioms resamplingOperator_windowPullback
#print axioms norm_resamplingOperator_le
#print axioms resamplingOperator_one
#print axioms resamplingOperator_nonneg
#print axioms resamplingOperator_zero
#print axioms resamplingOperator_add
#print axioms tendsto_resamplingOperator_zero
#print axioms resamplingFellerSemigroup
#print axioms operator_eq_resamplingFellerSemigroup
#print axioms resamplingApproximation
#print axioms infiniteGenomeSemigroup_resampling
#print axioms infiniteGenomeSemigroup_operator_resampling
