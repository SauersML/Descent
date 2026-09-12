/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Pangenome.AncestralLocality.SelectionDecisions

/-! Axiom audit of SelectionDecisions. -/

open Descent.Pangenome.AncestralLocality

#print axioms selectionKernel_nonneg
#print axioms sum_selectionKernel
#print axioms reproduce_selectionKernel
#print axioms kernelBranch_indicator
#print axioms kernelBranch_selectionKernel
#print axioms samplingObservable_kernelBranch
#print axioms samplingObservable_kernelBranch_eq_sum
#print axioms kernelDriftTerm_samplingObservable
#print axioms selectionGenerator_eq_drift
#print axioms selectionGenerator_samplingObservable
#print axioms dualExitRate_eq_branchingExitRate
#print axioms momentGenerator_eq_branchingMomentGenerator
#print axioms branchingMomentGenerator_sub
#print axioms hasDerivAt_duhamel_branching
#print axioms abs_moment_le_choose_mul_pow_branching
#print axioms moment_eq_zero_branching
#print axioms moments_eq_of_branchingEquation
#print axioms norm_kernelBranch_le
#print axioms norm_kernelBranchingGain_le
#print axioms kernelMomentGenerator_eq
#print axioms moments_eq_of_kernelMomentEquation
#print axioms fitnessDetermined_restrict
#print axioms selectionTags_castSucc
#print axioms selectionTags_last
#print axioms tagDetermined_selectionBranch
#print axioms tagWeight_selectionTags_le
#print axioms tagCount_selectionTags_le
#print axioms selectionWeightRate_le
#print axioms supportDrift_le
