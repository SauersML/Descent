/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Pangenome.GraphCoalescent.ReportedConnectionClock

/-! Axiom audit of the reported connection clock, (D7)-(D9). -/

open Descent.Pangenome.GraphCoalescent.ReportedConnectionClock

#print axioms deathRate_eq_choose_two
#print axioms sum_one_div_deathRate_Ioc
#print axioms sum_one_div_choose_two_Ioc
#print axioms sum_one_div_deathRate_Ioc_eq_meanTransitTime_sub
#print axioms varTransitTime_succ
#print axioms sum_sq_one_div_deathRate_Ioc
#print axioms sum_one_div_choose_two_sq_Ioc
#print axioms kingmanLaplace_mul_prod_Ioc
#print axioms sum_mul_sum_one_div_deathRate_Ioc
#print axioms sum_mul_secondMoment_eq
