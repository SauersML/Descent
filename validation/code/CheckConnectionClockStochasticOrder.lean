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
