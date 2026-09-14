/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.EndToEndLogLossLaw

/-! Axiom audit of EndToEndLogLossLaw. -/

open Descent.Portability.EndToEndLogLossLaw

#print axioms negMulLog_hasSum
#print axioms negMulLog_truncation_mem
#print axioms negMulLog_sub_partialSum_le_uniform
#print axioms reportMass_le_one
#print axioms reportEntropy
#print axioms reportEntropyTerm
#print axioms reportEntropyTerm_nonneg
#print axioms hasSum_reportEntropy
#print axioms reportEntropy_sub_truncation_mem
#print axioms reportEntropy_pushforward_pushforward
#print axioms conditionalEntropy
#print axioms mutualInformation
#print axioms pushforward_fst_mass
#print axioms conditionalEntropy_eq_reportEntropy_sub
#print axioms repairedGroupForecast
#print axioms repairedGroupForecast_mem
#print axioms repairedGroupLoss_eq
#print axioms expectation_neg_log_repairedGroupForecast
#print axioms conditionalEntropy_nonneg
#print axioms expectedLogLoss_eq_ofReal_of_pos
#print axioms expectedLogLoss_repairedGroupForecast
#print axioms repairedGroupForecast_eq_repairedForecast
#print axioms conditionalEntropy_eq_repairedLogLoss
#print axioms groupForecast
#print axioms forecastLogLoss
#print axioms expectedLogLoss_groupForecast
#print axioms expectedLogLoss_groupForecast_eq_top
#print axioms cellLoss_ge
#print axioms conditionalEntropy_le_forecastLogLoss
#print axioms entropyTermPolynomial
#print axioms eval_entropyTermPolynomial
#print axioms totalDegree_entropyTermPolynomial_le
#print axioms expectedEntropy
#print axioms continuous_reportEntropy
#print axioms continuous_reportEntropyTerm
#print axioms expectedEntropy_sub_truncation_mem
#print axioms hasSum_expectedEntropy
#print axioms expectedEntropy_eq_tsum_dotProduct
#print axioms expectedEntropy_historyEventKernel
#print axioms expectedEntropy_rateHistoryKernel
#print axioms expectedEntropy_eq_of_moments_eq
