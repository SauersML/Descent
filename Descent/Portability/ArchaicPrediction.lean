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
import Descent.Portability.ArchaicPrediction.ResponsePanels
import Descent.Portability.ArchaicPrediction.PairingPrecision
import Descent.Portability.ArchaicPrediction.TranslationAlgebra

/-!
# Beyond Ancestry Tags: formal mathematical core

Theorem map for the 10 September 2026 manuscript:

1. `binary_multilinear_representation`, `response_transport`, `transport_comp`,
   `transport_inverse`, `evaluate_transport`, `centered_multilinear_representation`,
   `lowerCoordinate_square_zero`, `lowerCoordinate_commute`.
2. `exact_transport_debt`, `centered_response_split`, `no_uniform_source_variance_bound`.
3. `factorial_recovery`, `degree_panel_identifies`, `factorial_panel_card`,
   `factorial_contrast_noise`.
4. `phase_expansion_exists_unique`, `invariant_phase_expansion`, `phase_parseval`,
   `phase_mode_count`, `dosage_only_phase_minimum`.
5. `response_specific_mean`, `response_moment_error`, `phase_covariance`.
6. `four_pairwise_moments`, `four_mean_logit`, `pairwise_phase_risk_not_identified`.
7. `two_state_logistic_bound`.
8. `effectiveRate_derivative`, `effectiveRate_deriv_nonpos`, `marginal_hazard`.
9. `zero_cycles_iff_response_map`, `weighted_cycle_defect`, `exact_multiple_cycle_residual`.
10. `effective_resistance_variance`, `integral_contrast_precision`,
    `graph_contrast_precision`.
11. `pairing_identified_iff_odd`, `pairing_kernel_one_dimension`,
    `pairing_homozygote_identifies`, `pairing_information_positive`,
    `triangle_contribution_variance`.

`sharp_phase_risk_interval` proves the full identified interval from any fixed
finite family of phase moments. Statements use actual finite-state sums,
linear observation operators, or differentiated response models. Biological
effect invariance and clinically useful magnitudes are not inferred from
these algebraic results.

`arbitrary_ld_additive_optimum` and `arbitrary_ld_export_formula` establish
the correlated-feature export calculation. `four_pair_moment_risk_bounds`
specializes the identified interval to the four-locus counterexample.

The phase formulas use binary representatives of unordered phases; invariance
under homolog exchange is proved. The graph inverse acts on the identifiable
zero-sum response subspace, which is the restriction of the Laplacian
pseudoinverse used in the manuscript. The pairing criterion uses odd closed
walks, an equivalent witness of non-bipartiteness that includes loops.
Finite phase distributions and general measurement-noise laws are kept
distinct. No numerical optimizer or simulation is used as proof evidence.
-/
