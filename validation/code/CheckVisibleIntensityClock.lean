/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Pangenome.GraphCoalescent.VisibleIntensityClock

/-! Axiom audit of VisibleIntensityClock. -/

open Descent.Pangenome.GraphCoalescent

#print axioms exists_visible_cover
#print axioms visibleReport_surjective
#print axioms choose_two_le_visibleIntensity
#print axioms deathRate_le_visibleIntensity
#print axioms choose_two_lt_visibleIntensity
#print axioms deathRate_lt_visibleIntensity
#print axioms visibleIntensity_of_graphState
#print axioms sum_ite_visible
#print axioms meanTransitTime_succ_sub
#print axioms meanTransitTime_sub_of_covers
#print axioms kingmanGenerator_meanTransitTime_observed
#print axioms discountedStep_succ
#print axioms connectionValue_eq
#print axioms covers_induction
#print axioms deathRate_add_pos
#print axioms connectionValue_sub
#print axioms connectionValue_congr
#print axioms connectionValue_nonneg
#print axioms div_le_connectionValue
#print axioms connectionValue_generator
#print axioms meanConnectionTime_eq
#print axioms meanTransitTime_eq_zero_of_le_one
#print axioms meanTransitTime_sub_meanConnectionTime
#print axioms clockCorrectionRate_nonneg
#print axioms meanConnectionTime_le_meanTransitTime
#print axioms meanConnectionTime_bot_le
#print axioms meanConnectionTime_bot_le_two_sub
#print axioms meanConnectionTime_lt_meanTransitTime
#print axioms meanConnectionTime_bot_lt
#print axioms meanTransitTime_mono
#print axioms meanTransitTime_sub_le_meanConnectionTime
#print axioms two_div_sub_two_div_le_meanConnectionTime_bot
#print axioms meanConnectionTime_of_graphState
#print axioms meanConnectionTime_graphKer
#print axioms kingmanLaplace_nonneg
#print axioms kingmanLaplace_eq_one_of_le_one
#print axioms kingmanLaplace_succ
#print axioms kingmanLaplace_le_connectionLaplace
