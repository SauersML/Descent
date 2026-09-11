/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.SimplexResamplingKernel

/-! Axiom audit of the single-draw resampling kernel on the haplotype simplex. -/

open Descent.Portability.SimplexResamplingKernel

#print axioms haplotypeCoordinate_nonneg
#print axioms haplotypeCoordinate_le_one
#print axioms twoLocusHaplotypeIndicator_comm
#print axioms twoLocusHaplotypeMean_indicator
#print axioms twoLocusHaplotypeMean_sub
#print axioms twoLocusHaplotypeMean_sub_const
#print axioms twoLocusHaplotypeMean_abs_le
#print axioms twoLocusHaplotypeMean_centered_mul
#print axioms stepDirection_eq_centered_indicator
#print axioms abs_stepDirection_le_one
#print axioms twoLocusHaplotypeMean_stepDirection
#print axioms resampleStep_coordinate_nonneg
#print axioms resampleStep_coordinate
#print axioms resampleStep_zero_coordinate
#print axioms resampleStep_leftFrequency
#print axioms resampleStep_rightFrequency
#print axioms abs_linkageStepForm_le_two
#print axioms resampleStep_linkage
#print axioms twoLocusHaplotypeMean_linkageStepForm
#print axioms abs_twoLocusLinkageGradient_le_one
#print axioms abs_twoLocusLeftAlleleIndicator_le_one
#print axioms abs_twoLocusRightAlleleIndicator_le_one
#print axioms resampleStepAt_self
#print axioms resampleStepAt_of_ne
#print axioms resampleExpectation_const
