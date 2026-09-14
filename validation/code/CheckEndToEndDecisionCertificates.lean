/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.EndToEndDecisionCertificates

/-! Axiom audit of EndToEndDecisionCertificates. -/

open Descent.Portability.EndToEndDecisionCertificates

#print axioms quotient_sub_partialSum_eq
#print axioms quotient_truncation_bounds
#print axioms integral_quotient_truncation
#print axioms tendsto_integral_pow_complement
#print axioms tendsto_integral_pow_complement_zero
#print axioms certificatePolynomial
#print axioms eval_certificatePolynomial
#print axioms totalDegree_certificatePolynomial_le
#print axioms expectedPositiveQuotient_truncation
#print axioms integral_recallRate_precision_truncation
#print axioms expectedPositiveQuotient_truncation_dotProduct
#print axioms expectedPositiveQuotient_truncation_historyEventKernel
#print axioms expectedPositiveQuotient_truncation_rateHistoryKernel
#print axioms tendsto_certificate
#print axioms tendsto_certificate_zero_of_ae_pos
#print axioms tendsto_recallCertificate_zero_of_ae_pos
