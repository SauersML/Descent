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
