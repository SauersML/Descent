/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Pangenome.GraphCoalescent.ConnectionClockStochasticOrder

/-! Axiom audit of ConnectionClockStochasticOrder. -/

open Descent.Pangenome.GraphCoalescent

#print axioms measurableSet_survival
#print axioms survivalAt_antitone
#print axioms survivalAt_of_neg
#print axioms survivalAt_conv
#print axioms survivalAt_bind_jumpStep
#print axioms kingmanTransitLaw_isProbabilityMeasure
#print axioms survivalAt_kingmanTransitLaw_le_succ
#print axioms holdMeasure_eq_expMeasure
#print axioms measurable_holdDensity
#print axioms holdMeasure_Iic
#print axioms holdMeasure_Ioi
#print axioms survivalAt_holdDuration
#print axioms holdDensity_mul_exp
#print axioms setLIntegral_Iic_holdDensity_mul_exp
#print axioms survivalAt_holdDuration_conv
#print axioms survivalAt_add_smul
#print axioms monotone_survivalAt_sub
#print axioms deathRate_le_deathRate
#print axioms holdDuration_thinning
#print axioms survivalAt_kingmanTransitLaw_thinning
#print axioms choose_two_eq_ofReal_deathRate
#print axioms choose_two_mul_inv_choose_two
#print axioms choose_two_sub_mul_inv_choose_two
#print axioms sum_survivalAt_kingmanTransitLaw_le
#print axioms survivalAt_connectionTimeLaw_le
#print axioms survivalAt_connectionTimeLaw_bot_le
