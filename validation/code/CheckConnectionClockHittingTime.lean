/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Pangenome.GraphCoalescent.ConnectionClockHittingTime

/-! Axiom audit of ConnectionClockHittingTime. -/

open Descent.Pangenome.GraphCoalescent

#print axioms observed_chainOfList_stoppingLevel
#print axioms isLeast_reportHittingSet
#print axioms reportHittingTime_eq
#print axioms descentTime_clockHold_eq_connectionTime
#print axioms reportHittingTime_clockHold
#print axioms ae_mem_support_nonneg
#print axioms ae_reportHittingTime_eq_connectionTime
#print axioms map_reportHittingTime_eq_map_connectionTime
#print axioms lintegral_reportHittingTime
