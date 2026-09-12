/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Pangenome.GraphCoalescent.HiddenClockCorrection

/-! Axiom audit of HiddenClockCorrection. -/

open Descent.Pangenome.GraphCoalescent.HiddenClockCorrection

#print axioms panelTime_eq_connectionTime_add_residualTime
#print axioms lintegral_mul_sum_kingmanClock
#print axioms lintegral_block_mul_total
#print axioms lintegral_stoppingMix
#print axioms lintegral_panelTime
#print axioms lintegral_sq_panelTime
#print axioms lintegral_residualTime
#print axioms lintegral_sq_residualTime
#print axioms lintegral_inv_stoppingLevel
#print axioms lintegral_stoppingLevel
#print axioms lintegral_connectionTime_mul_panelTime
#print axioms inv_stoppingLevel_mean_eq
#print axioms one_le_mean_mul_mean_inv
#print axioms two_mul_div_le_mean_stoppingLevel
#print axioms residualTime_mean_eq
#print axioms panelTime_mean_eq_add
#print axioms covariance_connectionTime_panelTime
#print axioms variance_residualTime_eq
#print axioms connectionTime_mean_le_two_sub
#print axioms panelTime_mean_sub_two_sub
#print axioms observedIntensity_pointPrior
#print axioms loadVisibleIntensity_eq_choose_sub
#print axioms loadVisibleIntensity_fin_two
