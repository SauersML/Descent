/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.PortabilityMeasureQueries

/-! Axiom audit of PortabilityMeasureQueries. -/

open Descent.Portability.PortabilityMeasureQueries

#print axioms measurableSet_portabilityDomain
#print axioms portabilityRatio_eq_cross_at
#print axioms one_lt_portabilityRatio_iff_at
#print axioms portabilityRatio_small_source
#print axioms portabilityRatio_exceeds
#print axioms ratioExceedsOneProbability_eq
#print axioms targetExceedsMass_eq_mul
#print axioms ratioOfMeans_eq_setIntegral
#print axioms measurable_gatedTerm
#print axioms tsum_gatedTerm
#print axioms ratioMean_eq_tsum
#print axioms tsum_gatedTerm_eq_top
#print axioms lintegral_ungated_eq_top
#print axioms sourceTargetFamily_rel
#print axioms sourceTargetFamily_nonneg
#print axioms sourceTargetFamily_le
#print axioms sourceTargetFamily_le_one
#print axioms measurable_sourceTargetFamily
#print axioms mem_definedDomain_sourceTargetFamily
#print axioms measurable_sourceTargetVector
#print axioms portabilityDomain_eq_preimage
#print axioms targetExceedsEvent_eq_preimage
#print axioms portabilityRatio_eq_vector
#print axioms portabilityQueries_eq_sourceTargetLaw
#print axioms portabilityQueries_eq_of_expansion_eq
