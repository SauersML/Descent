/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.KernelRealizationPreservation

/-! Axiom audit of KernelRealizationPreservation. -/

open Descent.Portability.KernelRealizationPreservation

namespace Descent.Portability.KernelRealizationPreservation

#print axioms abs_law_average_le
#print axioms mulVec_featureVector
#print axioms exp_mulVec_mem_realizationBody
#print axioms propagator_mulVec_mem_realizationBody
#print axioms split_mulVec_mem_realizationBody
#print axioms propagate_mem_realizationBody
#print axioms dd_quadraticForm_nonneg_of_mem
#print axioms dd_diagonal_nonneg_of_mem
#print axioms dd_cauchySchwarz_of_mem
#print axioms enlargedLowOrderLDFeature
#print axioms enlargedLowOrderLDFeature_none
#print axioms enlargedLowOrderLDFeature_inl
#print axioms enlargedLowOrderLDFeature_inr
#print axioms locusExchangeableRealizationOfLaw

end Descent.Portability.KernelRealizationPreservation
