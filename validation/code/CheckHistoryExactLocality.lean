/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.HistoryExactLocality

/-! Axiom audit of HistoryExactLocality. -/

open Descent.Portability.HistoryExactLocality

#print axioms rowsLocal_one
#print axioms rowsAgreeOn_refl
#print axioms RowsLocal.mul
#print axioms RowsAgreeOn.mul
#print axioms mulVec_eq_of_rowsAgreeOn
#print axioms matrixExponential_apply_eq_local
#print axioms rowsLocal_matrixExponential
#print axioms rowsAgreeOn_matrixExponential
#print axioms lociWithin_relabelCarriers
#print axioms rowsLocal_pulseKernel
#print axioms RatesAgreeOn.refl
#print axioms eventAgreeOn_refl
#print axioms rowsLocal_eventPropagator
#print axioms rowsAgreeOn_eventPropagator
#print axioms rowsLocal_historyEventPropagator
#print axioms rowsAgreeOn_historyEventPropagator
#print axioms historyEventPropagator_mulVec_eq_of_agreeOn
#print axioms integral_momentPolynomial_historyEventKernel_eq_of_agreeOn
#print axioms readsLoci_const
#print axioms readsLoci_eval
#print axioms momentPolynomial_mem_localMomentSpan
#print axioms momentPolynomial_add
#print axioms localMomentSpan_mono
#print axioms mul_mem_localMomentSpan
#print axioms lociWithin_localType
#print axioms satisfies_localType_iff
#print axioms expectation_mem_localMomentSpan
#print axioms covariance_mem_localMomentSpan
#print axioms numeratorPolynomial_mem_localMomentSpan
#print axioms denominatorPolynomial_mem_localMomentSpan
#print axioms integral_eq_of_mem_localMomentSpan
#print axioms expectedPortability_eq_of_agreeOn
