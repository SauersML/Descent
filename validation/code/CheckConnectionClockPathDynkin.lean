/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Pangenome.GraphCoalescent.ConnectionClockPathDynkin

/-! Axiom audit of ConnectionClockPathDynkin. -/

open Descent.Pangenome.GraphCoalescent

#print axioms integral_pathState_descentTime
#print axioms connectionTime_nonneg
#print axioms integral_clockCorrectionRate_pathState
#print axioms stoppingLevel_lt_iff
#print axioms unconnectedRate
#print axioms unconnectedRate_clockCorrectionRate_nonneg
#print axioms connectionValue_zero_eq
#print axioms connectionValue_eq_sum_jumpLaw
#print axioms sum_blockLaw_connectionValue_succ
#print axioms sum_blockLaw_connectionValue
#print axioms connectionValue_bot_eq_sum
#print axioms lintegral_integral_clockCorrectionRate
#print axioms clockDynkin_path
#print axioms clockDynkin_reportHittingTime
