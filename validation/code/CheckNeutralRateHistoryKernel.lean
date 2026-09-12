/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.NeutralRateHistoryKernel

/-! Axiom audit of NeutralRateHistoryKernel. -/

open Descent.Portability.NeutralRateHistoryKernel

#print axioms historyOperator
#print axioms integral_neutralHistoryKernel_eq_historyOperator
#print axioms historyOperator_nonneg
#print axioms historyOperator_one
#print axioms norm_historyOperator_apply_le
#print axioms sampledOperator
#print axioms abs_dotProduct_mulVec_sub_le
#print axioms sampledOperator_polynomial
#print axioms cauchySeq_sampledOperator
#print axioms rateHistoryOperatorValue
#print axioms tendsto_rateHistoryOperatorValue
#print axioms rateHistoryOperatorValue_add
#print axioms rateHistoryOperatorValue_smul
#print axioms norm_rateHistoryOperatorValue_le
#print axioms rateHistoryOperator
#print axioms rateHistoryOperator_apply
#print axioms tendsto_rateHistoryOperator
#print axioms tendsto_sampledOperator_apply
#print axioms rateHistoryOperator_nonneg
#print axioms rateHistoryOperator_one
#print axioms rateHistoryKernel
#print axioms isMarkovKernel_rateHistoryKernel
#print axioms integral_rateHistoryKernel
#print axioms tendstoUniformly_integral_sampledHistoryKernel
#print axioms integral_momentPolynomial_rateHistoryKernel
#print axioms continuousOn_dualGenerator_const
#print axioms integral_panelReport_rateHistoryKernel
