/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Pangenome.GraphCoalescent.ConnectionClockHittingLaw

/-! Axiom audit of ConnectionClockHittingLaw. -/

open Descent.Pangenome.GraphCoalescent

#print axioms conv_finset_sum
#print axioms bind_jumpStep_eq_sum
#print axioms levelTransitLaw_pred
#print axioms map_sum_kingmanClock
#print axioms map_connectionTime_eq_sum
#print axioms stoppingLaw_eq_firstConnectionMass
#print axioms stoppingLaw_self_eq
#print axioms unconnectedMix_succ
#print axioms connectionTimeLaw_bot_unroll
#print axioms connectionTimeLaw_bot_eq_sum
#print axioms map_connectionTime_eq_connectionTimeLaw
#print axioms map_reportHittingTime_eq_connectionTimeLaw
#print axioms survivalAt_reportHittingTime
#print axioms survivalAt_reportHittingTime_le
