/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Pangenome.GraphCoalescent.UniformizationIdentity

/-! Axiom audit of UniformizationIdentity. -/

open Descent.Pangenome.GraphCoalescent.UniformizationIdentity

#print axioms hasSum_poissonPMFReal_smul_pow
#print axioms hasSum_poissonPMFReal_mul_pow_apply
#print axioms skeletonLaw_eq_sum_pow
#print axioms hasSum_poissonPMFReal_mul_skeletonLaw
#print axioms poissonMixture_skeletonLaw
#print axioms continuousLaw_nonneg
#print axioms sum_continuousLaw
#print axioms sum_kingmanContinuousLaw
#print axioms sum_multiplicativeContinuousLaw
#print axioms hasSum_poissonPMFReal_mul_kingmanLaw
#print axioms hasSum_poissonPMFReal_mul_multiplicativeLaw
#print axioms hasSum_poissonPMFReal_mul_reportLaw
#print axioms reportConnectionProbability_eq
#print axioms multiplicativeContinuousLaw_top_eq
#print axioms abs_reportContinuousLaw_top_sub_le
#print axioms report_multiplicative_totalVariation_le_separationMass
#print axioms report_multiplicative_totalVariation_le
#print axioms report_multiplicative_totalVariation_le_one
#print axioms half_sum_abs_sub_le_poissonMixture
#print axioms report_multiplicative_continuousTotalVariation_le
