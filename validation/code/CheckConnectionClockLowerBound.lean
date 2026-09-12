/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Pangenome.GraphCoalescent.ConnectionClockLowerBound

/-! Axiom audit of (C4) as a stochastic order. -/

open Descent.Pangenome.GraphCoalescent.ConnectionClockLowerBound

#print axioms blocks_add_width_le_of_observed_eq_top
#print axioms stoppingLevel_add_width_le
#print axioms sum_top_levels_le_connectionTime
#print axioms ae_sum_top_levels_le_connectionTime
#print axioms kingmanClock_sum_top_levels_lt_le
