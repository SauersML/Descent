/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.SimultaneousRealization

/-! Axiom audit of SimultaneousRealization. -/

open Descent.Portability.SimultaneousRealization

#print axioms cellLaw_eval
#print axioms cellLaw_def
#print axioms cellResidual_eq
#print axioms shift_one
#print axioms shift_mul
#print axioms shift_sq
#print axioms shift_pow_four
#print axioms genotype_contrast_mean
#print axioms genotype_contrast_variance
#print axioms genotype_contrast_covariance
#print axioms deployedScore_variance
#print axioms contrast_first_moment
#print axioms contrast_second_moment
#print axioms contrast_fourth_moment
#print axioms contrast_score_cross
#print axioms cell_regression_function
#print axioms cellPhenotype_variance
#print axioms cell_genotype_fraction
#print axioms cell_score_accuracy
#print axioms fixed_background_curve_realized
#print axioms eval_add_const
#print axioms cell_loss_mean
#print axioms cell_loss_within
#print axioms loss_between_variance
#print axioms loss_total_variance
#print axioms noise_fourth_moment_ge
#print axioms minimalWithinVariance_nonneg
#print axioms lossExplainedFraction_eq
#print axioms loss_fraction_bounds
#print axioms spike_eval
#print axioms spike_scale
#print axioms spike_mean
#print axioms spike_second_moment
#print axioms spike_fourth_moment
#print axioms spike_loss_fraction
#print axioms spikeSign_eq_rademacherScore
#print axioms lossBudget_slack
#print axioms spikeParameter_mem_unit
#print axioms spike_realizes_fraction
#print axioms sharp_loss_fraction_interval
#print axioms simultaneous_curve_and_loss_fraction
#print axioms workedCurve_nonneg
#print axioms workedCurve_le
#print axioms lossMean_worked_zero
#print axioms lossMean_worked_one
#print axioms lossMean_worked_two
#print axioms lossMean_worked_three
#print axioms worked_lossMeanVariance
#print axioms worked_example_positive_variance
#print axioms worked_example_sharp_interval
