/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.TransportCoordinates

/-! Axiom audit of TransportCoordinates. -/

open Descent.Portability.TransportCoordinates

#print axioms exact_transport_coordinates
#print axioms crossMomentVector_eq_rawCrossMoment
#print axioms crossMoment_dot
#print axioms coordinate_secondMoment
#print axioms normal_equations_iff
#print axioms dot_self_eq_zero
#print axioms dot_add_left_pi
#print axioms dot_zero_right
#print axioms secondMoment_polarization
#print axioms kernel_score_null
#print axioms dot_kernel_range_zero
#print axioms kernel_orthogonal_crossMoment
#print axioms crossMoment_mem_range
#print axioms expMse_expand
#print axioms oracle_risk_eq
#print axioms training_risk_decomposition
#print axioms excess_risk_law
#print axioms expand_mul_sub
#print axioms oracle_value_unique
#print axioms linScore_mean_zero
#print axioms centered_score_variance
#print axioms centered_predictive_covariance
#print axioms centered_score_r2
#print axioms weightCovariance_symm
#print axioms quadratic_form_sum
#print axioms trace_mul_symm
#print axioms weight_second_moment
#print axioms expected_training_risk
