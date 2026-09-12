/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Pangenome.GraphCoalescent.ConnectionClockPathLaw

/-! Axiom audit of ConnectionClockPathLaw. -/

open Descent.Pangenome.GraphCoalescent

#print axioms ae_pos_holdMeasure
#print axioms holdDuration_isProbabilityMeasure
#print axioms lintegral_coe_holdDuration
#print axioms lintegral_exp_holdDuration
#print axioms measurableSingletonClass_ER
#print axioms lintegral_jumpStep
#print axioms isProbabilityMeasure_bind_jumpStep
#print axioms choose_two_blocks_eq_ofReal_deathRate
#print axioms sum_ofReal_mul_inv_choose_two
#print axioms two_le_blocks_of_not_le_one
#print axioms connectionTimeStep_succ
#print axioms connectionTimeLaw_eq
#print axioms connectionTimeLaw_isProbabilityMeasure
#print axioms lintegral_coe_connectionTimeLaw
#print axioms lintegral_exp_connectionTimeLaw
#print axioms lintegral_add_correction_bot
#print axioms lintegral_coe_connectionTimeLaw_bot_le
#print axioms lintegral_coe_connectionTimeLaw_bot_lt
#print axioms ofReal_le_lintegral_coe_connectionTimeLaw_bot
#print axioms kingmanLaplace_width_le_lintegral_exp_connectionTimeLaw_bot
#print axioms lintegral_coe_connectionTimeLaw_graphKer
#print axioms lintegral_exp_connectionTimeLaw_graphKer
