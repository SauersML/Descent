/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.RandomStageKernel

/-! Axiom audit of the resampling probability kernel and the random-stage assembly. -/

open Descent.Portability.RandomStageKernel

#print axioms sum_haplotype
#print axioms resamplingKernel
#print axioms apply_resamplingKernel
#print axioms one_le_driftChromosomeCount
#print axioms one_div_driftChromosomeCount_le
#print axioms abs_one_div_sq_sub_le
#print axioms driftStageSlack_tendsto
#print axioms apply_driftStageKernel_expansion
#print axioms apply_uniformStageMixture
