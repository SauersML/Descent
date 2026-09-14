/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.EndToEndSensitivitySeriesBound

/-! Axiom audit of EndToEndSensitivitySeriesBound. -/

open Descent.Portability.EndToEndSensitivitySeriesBound

#print axioms one_div_four_mul_succ_le_expansion_term
#print axioms not_summable_of_expansion_term_le
#print axioms not_summable_of_tendsto_nhdsGT_zero
#print axioms hasDerivAt_witnessTerm
#print axioms tsum_witnessTerm
#print axioms hasDerivAt_tsum_witnessTerm
#print axioms abs_witnessTermDerivative_le
#print axioms summable_witnessLocalBound
#print axioms tsum_witnessTermDerivative
#print axioms tendsto_witnessTermDerivative
#print axioms not_summable_of_witnessTermDerivative_le
#print axioms witness_termwise_derivative_without_summable_bound
#print axioms hasDerivAt_truncatedSeries_segmentHistory
#print axioms expectedSquaredCorrelation_truncation
