/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.EndToEndLogLossBounds

/-! Axiom audit of EndToEndLogLossBounds. -/

open Descent.Portability.EndToEndLogLossBounds

#print axioms divergenceTerm
#print axioms divergenceTerm_eq_mul
#print axioms divergenceTerm_nonneg
#print axioms divergenceTerm_eq_zero_iff
#print axioms pushforward_snd_mass
#print axioms sum_scoreGroupMass
#print axioms mass_pos_marginals
#print axioms productMarginals_nonneg
#print axioms productMarginals_pos
#print axioms mass_mul_log_div_split
#print axioms mutualInformation_eq_sum_divergenceTerm
#print axioms mutualInformation_nonneg
#print axioms mutualInformation_le_outcomeEntropy
#print axioms mutualInformation_eq_zero_iff
#print axioms pseudoRSquared_mem
#print axioms continuous_mutualInformation
#print axioms expectedMutualInformation_nonneg
#print axioms expectedMutualInformation_le_expectedEntropy
#print axioms expectedPseudoRSquared_mem
#print axioms pseudoRSquaredPortability_nonneg
#print axioms expectedMutualInformation_eq_zero_iff
#print axioms logLossBounds_historyEventKernel
#print axioms logLossBounds_rateHistoryKernel
#print axioms mutualInformationSeries_mem_historyEventKernel
