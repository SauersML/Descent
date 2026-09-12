/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Pangenome.GraphCoalescent.ReportedConnectionClock

/-! Axiom closure of the reported connection clock, equations (D5)-(D9). -/

#print axioms Descent.Pangenome.GraphCoalescent.connectedProb_nonneg
#print axioms Descent.Pangenome.GraphCoalescent.connectedProb_eq
#print axioms Descent.Pangenome.GraphCoalescent.connectedProb_one
#print axioms Descent.Pangenome.GraphCoalescent.connectedProb_self
#print axioms Descent.Pangenome.GraphCoalescent.chainLaw_getD_succ_le
#print axioms Descent.Pangenome.GraphCoalescent.chainLaw_getD_antitone
#print axioms Descent.Pangenome.GraphCoalescent.observed_chainOfList_mono
#print axioms Descent.Pangenome.GraphCoalescent.observed_chainOfList_one
#print axioms Descent.Pangenome.GraphCoalescent.stoppingLevel_eq_iff
#print axioms Descent.Pangenome.GraphCoalescent.stoppingLevel_eq_self_iff
#print axioms Descent.Pangenome.GraphCoalescent.stoppingLevel_mem_Icc
#print axioms Descent.Pangenome.GraphCoalescent.ofReal_connectedProb
#print axioms Descent.Pangenome.GraphCoalescent.stoppingLaw_apply
#print axioms Descent.Pangenome.GraphCoalescent.stoppingLaw_eq_zero
#print axioms Descent.Pangenome.GraphCoalescent.sum_stoppingProb
#print axioms Descent.Pangenome.GraphCoalescent.stoppingLaw_add_ofReal
#print axioms Descent.Pangenome.GraphCoalescent.stoppingProb_eq
#print axioms Descent.Pangenome.GraphCoalescent.stoppingProb_self
#print axioms Descent.Pangenome.GraphCoalescent.kingmanClock_isProbabilityMeasure
#print axioms Descent.Pangenome.GraphCoalescent.trajectoryClockLaw_prod
#print axioms Descent.Pangenome.GraphCoalescent.ico_succ_eq_ioc
#print axioms Descent.Pangenome.GraphCoalescent.sum_Ico_pred
#print axioms Descent.Pangenome.GraphCoalescent.prod_Ico_pred
#print axioms Descent.Pangenome.GraphCoalescent.connectionTime_of_stoppingLevel
#print axioms Descent.Pangenome.GraphCoalescent.lintegral_trajectoryClockLaw
#print axioms Descent.Pangenome.GraphCoalescent.kingmanClock_eval
#print axioms Descent.Pangenome.GraphCoalescent.lintegral_coord_kingmanClock
#print axioms Descent.Pangenome.GraphCoalescent.lintegral_exp_neg_sum_kingmanClock
#print axioms Descent.Pangenome.GraphCoalescent.holdMeasure_Iio_zero
#print axioms Descent.Pangenome.GraphCoalescent.ae_nonneg_kingmanClock
#print axioms Descent.Pangenome.GraphCoalescent.lintegral_sum_kingmanClock
#print axioms Descent.Pangenome.GraphCoalescent.lintegral_sq_holdMeasure
#print axioms Descent.Pangenome.GraphCoalescent.lintegral_mul_coords_kingmanClock
#print axioms Descent.Pangenome.GraphCoalescent.sum_sum_ofReal_add_ite
#print axioms Descent.Pangenome.GraphCoalescent.lintegral_sq_sum_kingmanClock
#print axioms Descent.Pangenome.GraphCoalescent.sum_Ioc_one_div_deathRate
#print axioms Descent.Pangenome.GraphCoalescent.connectionTime_laplace
#print axioms Descent.Pangenome.GraphCoalescent.connectionTime_mean
#print axioms Descent.Pangenome.GraphCoalescent.connectionTime_secondMoment
