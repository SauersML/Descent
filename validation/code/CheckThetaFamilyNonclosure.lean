/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.ThetaFamilyNonclosure

/-! Axiom audit of ThetaFamilyNonclosure. -/

open Descent.Portability.ThetaFamilyNonclosure

#print axioms thetaMass_nonneg
#print axioms thetaMass_sum
#print axioms thetaLaw_mass
#print axioms thetaExp_apply
#print axioms thetaExp_mean_score
#print axioms thetaExp_mean_outcome
#print axioms thetaExp_variance_score
#print axioms thetaExp_variance_outcome
#print axioms thetaExp_covariance
#print axioms thetaExp_squared_correlation
#print axioms thetaCellPoly_eval
#print axioms thetaCellPoly_natDegree_le
#print axioms cohortPoly_eval
#print axioms cohortPoly_natDegree_le
#print axioms cohortMass_eq_piLaw_mass
#print axioms cohort_mass_moments_match
#print axioms nodeProduct_succ
#print axioms nodeProduct_shift
#print axioms nodeProduct_ne_zero
#print axioms fwdDiff_iter_reciprocal
#print axioms nodeStep_pos
#print axioms node_mem_window
#print axioms node_denominator_pos
#print axioms alternating_thetaReport_sum
#print axioms parity_thetaReport_gap
#print axioms parity_thetaReport_gap_ne_zero
#print axioms parity_thetaReport_values_one
#print axioms parity_thetaReport_gap_one
#print axioms signPair_pooled_is_average
#print axioms signReport_pooled_values
