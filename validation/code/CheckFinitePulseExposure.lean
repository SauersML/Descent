/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.FinitePulseExposure

/-! Axiom audit of the finite migration-pulse realisation of an exposure law. -/

open Descent.Portability.FinitePulseExposure

#print axioms Descent.Portability.FinitePulseExposure.cumulativeMass_succ_sub
#print axioms Descent.Portability.FinitePulseExposure.cumulativeMass_le_donor
#print axioms Descent.Portability.FinitePulseExposure.one_sub_cumulativeMass_pos
#print axioms Descent.Portability.FinitePulseExposure.pulseFraction_nonneg
#print axioms Descent.Portability.FinitePulseExposure.pulseFraction_lt_one
#print axioms Descent.Portability.FinitePulseExposure.recipientFraction_eq
#print axioms Descent.Portability.FinitePulseExposure.recipientFraction_total
#print axioms Descent.Portability.FinitePulseExposure.exp_neg_pulseMigration
#print axioms Descent.Portability.FinitePulseExposure.sum_pulseMigration
#print axioms
  Descent.Portability.FinitePulseExposure.recipientFraction_mul_pulseFraction
#print axioms Descent.Portability.FinitePulseExposure.increment_div_donor
#print axioms Descent.Portability.FinitePulseExposure.stepEvent_migration_pulse
