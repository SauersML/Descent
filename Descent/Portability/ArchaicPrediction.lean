/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.ArchaicPrediction.Transport
import Descent.Portability.ArchaicPrediction.Cube
import Descent.Portability.ArchaicPrediction.Debt
import Descent.Portability.ArchaicPrediction.Factorial
import Descent.Portability.ArchaicPrediction.Phase
import Descent.Portability.ArchaicPrediction.Moments
import Descent.Portability.ArchaicPrediction.PhaseRisk
import Descent.Portability.ArchaicPrediction.IdentifiedRisk
import Descent.Portability.ArchaicPrediction.Logistic
import Descent.Portability.ArchaicPrediction.Survival
import Descent.Portability.ArchaicPrediction.Contrast
import Descent.Portability.ArchaicPrediction.Pairing
import Descent.Portability.ArchaicPrediction.ResponseGraph
import Descent.Portability.ArchaicPrediction.Dimension
import Descent.Portability.ArchaicPrediction.DosageLoss
import Descent.Portability.ArchaicPrediction.ContrastWalk
import Descent.Portability.ArchaicPrediction.CycleResidual
import Descent.Portability.ArchaicPrediction.LDExport

/-!
# Beyond Ancestry Tags: formal mathematical core

Theorem map for the 10 September 2026 manuscript:

1. `response_transport`, `transport_comp`, `transport_inverse`, `evaluate_transport`.
2. `exact_transport_debt`, `centered_response_split`, `no_uniform_source_variance_bound`.
3. `factorial_recovery`, `degree_panel_identifies`, `factorial_panel_card`.
4. `phase_expansion_exists_unique`, `invariant_phase_expansion`, `phase_parseval`,
   `phase_mode_count`, `dosage_only_phase_minimum`.
5. `response_specific_mean`, `response_moment_error`, `phase_covariance`.
6. `four_pairwise_moments`, `four_mean_logit`, `pairwise_phase_risk_not_identified`.
7. `two_state_logistic_bound`.
8. `effectiveRate_derivative`, `effectiveRate_deriv_nonpos`, `marginal_hazard`.
9. `zero_cycles_iff_response_map`, `weighted_cycle_defect`, `exact_multiple_cycle_residual`.
10. `effective_resistance_variance`, `graph_contrast_precision`.
11. `pairing_identified_iff_odd`, `pairing_kernel_one_dimension`,
    `pairing_homozygote_identifies`.

`sharp_phase_risk_interval` proves the full identified interval from any fixed
finite family of phase moments. Statements use actual finite-state sums,
linear observation operators, or differentiated response models. Biological
effect invariance and clinically useful magnitudes are not inferred from
these algebraic results.

`arbitrary_ld_additive_optimum` and `arbitrary_ld_export_formula` establish
the correlated-feature export calculation. `four_pair_moment_risk_bounds`
specializes the identified interval to the four-locus counterexample.
-/
