/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Pangenome.GraphCoalescent.HiddenLoadContinuousTime

/-! Axiom audit of HiddenLoadContinuousTime. -/

open Descent.Pangenome.GraphCoalescent

#print axioms lintegral_Icc_rate_exp
#print axioms measurable_sojourn_indicator
#print axioms lintegral_holdMeasure_window
#print axioms lintegral_rate_mul_measure_between
#print axioms descentTime_clockHold_eq_sum
#print axioms descentTime_clockHold_succ
#print axioms indepFun_descentTime_clockHold
#print axioms blockCountAt_clockHold_eq_iff
#print axioms kingmanClock_descentTime_le
#print axioms levelProb
#print axioms measurable_descentTime_clockHold
#print axioms measurable_blockCountAt_clockHold
#print axioms kingmanClock_descentTime_one_le
#print axioms kingmanClock_descentTime_succ_le
#print axioms levelTime
#print axioms levelTime_one
#print axioms levelProb_balance
#print axioms hiddenLoadAt
#print axioms hiddenHeadLaw
#print axioms toMeasure_hiddenState_chainOfList
#print axioms trajectoryClockLaw_hiddenLoadAt
#print axioms hiddenBlockCount
#print axioms hiddenBlockCount_hiddenState
#print axioms hiddenRate
#print axioms reachableHidden
#print axioms hiddenRate_invisibleTarget
#print axioms hiddenRate_visibleTarget
#print axioms sum_hiddenRate
#print axioms ofReal_deathRate_mul_hiddenHeadLaw
#print axioms sum_hiddenHeadLaw_mul_hiddenKernel
#print axioms measurable_levelProb
#print axioms levelProb_zero
#print axioms sum_hiddenLoadLaw_mul_hiddenRate
#print axioms hiddenLoadLaw_forward
