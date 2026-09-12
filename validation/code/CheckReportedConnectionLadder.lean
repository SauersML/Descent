/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Pangenome.GraphCoalescent.ReportedConnectionLadder

/-! Axiom audit of the Kingman ladder under the reported connection clock. -/

open Descent.Pangenome.GraphCoalescent.ReportedConnectionLadder

#print axioms deathRate_eq_choose_two
#print axioms sum_one_div_choose_two_Ioc
#print axioms sum_Ioc_one_div_deathRate_eq_meanTransitTime_sub
#print axioms varTransitTime_succ
#print axioms sum_sq_one_div_deathRate_Ioc
#print axioms sum_one_div_choose_two_sq_Ioc
#print axioms kingmanLaplace_mul_prod_Ioc
#print axioms kingmanLaplace_pos
#print axioms prod_Ioc_eq_kingmanLaplace_div
#print axioms connectionTime_laplace_eq_kingmanLaplace
#print axioms connectionTime_mean_eq_meanTransitTime
#print axioms connectionTime_secondMoment_eq_varTransitTime
