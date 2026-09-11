/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.LogLossSeriesCertificate

/-! Axiom audit of LogLossSeriesCertificate. -/

open Descent.Portability.LogLossSeriesCertificate

#print axioms neg_log_hasSum
#print axioms log_series_term_nonneg
#print axioms partial_sum_le_neg_log
#print axioms neg_log_tail_bound
#print axioms expectedLogLoss_eq_top
#print axioms expectedLogLoss_eq_ofReal
#print axioms expectation_sub_eq
#print axioms expectation_log_loss_enclosure
