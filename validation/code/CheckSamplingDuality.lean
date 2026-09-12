/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Pangenome.AncestralLocality.SamplingDuality

/-! Axiom audit of SamplingDuality. -/

open Descent.Pangenome.AncestralLocality

#print axioms hasDerivAt_prod_line
#print axioms hasDerivAt_samplingObservable_line
#print axioms lineDeriv_samplingObservable
#print axioms secondPartial_samplingObservable
#print axioms sum_sum_sum_comm
#print axioms sum_ite_lt_eq_sum_Iio
#print axioms sum_erase_eq_two_mul_sum_Iio
#print axioms resamplingGenerator_samplingObservable
#print axioms reproduce_ruleKernel
#print axioms samplingObservable_decisionBranch_eq_sum
#print axioms driftTerm_samplingObservable
#print axioms decisionGenerator_samplingObservable
#print axioms forwardGenerator_samplingObservable
#print axioms forwardGenerator_orderedChild
#print axioms sum_card_Iio_eq_deathRate
#print axioms dualExitRate_eq
#print axioms backwardGenerator_eq_jump
