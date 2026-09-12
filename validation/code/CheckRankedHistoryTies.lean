/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Pangenome.GraphCoalescent.RankedHistoryTies

/-! Axiom audit of the ranked-history ties of (D4), (D5) and (E1). -/

open Descent.Pangenome.GraphCoalescent.RankedHistoryTies

#print axioms rankedHistoryCount
#print axioms rankedHistoryCount_eq_zero_of_blocks_ne
#print axioms two_pow_mul_rankedHistoryCount
#print axioms blockLaw_toReal_eq_rankedHistoryCount
#print axioms reportConnectedProbability_eq_sum_rankedHistoryCount
#print axioms reportConnectedProbability_eq_jumpCoeff_mul_leadingCoefficient
#print axioms sum_rankedHistoryCount_mul_prod_eq_leadingCoefficient
