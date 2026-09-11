/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.AuditSelectionSafety
import Descent.Portability.AuditVarianceGeometry
import Descent.Portability.AugmentedAuditLaw
import Descent.Portability.BernoulliBudgetLaw
import Descent.Portability.BernsteinConfidence
import Descent.Portability.BoundedAuditCompletion
import Descent.Portability.BregmanAuditContrasts
import Descent.Portability.CertifiedFrameRepair
import Descent.Portability.ClippedFrameRepair
import Descent.Portability.ConditionalGuardError
import Descent.Portability.DecisionInformationRank
import Descent.Portability.DecisionLossContrasts
import Descent.Portability.DisagreementAuditPayoff
import Descent.Portability.FiniteAuditAllocationLaw
import Descent.Portability.FiniteAuditConfidence
import Descent.Portability.FrameConvexRepair
import Descent.Portability.FrameMeanImage
import Descent.Portability.FrameRepairSpans
import Descent.Portability.GramAuditGeometry
import Descent.Portability.GramConvexRepair
import Descent.Portability.GramRepairOptimality
import Descent.Portability.GramSafeRepair
import Descent.Portability.GuardedRepairDeployment
import Descent.Portability.HardBudgetAuditGuard
import Descent.Portability.IdenticalAuditCells
import Descent.Portability.JointAuditExperiment
import Descent.Portability.LossExplainabilitySeparation
import Descent.Portability.MatrixDecisionInformation
import Descent.Portability.MeanDriftRepair
import Descent.Portability.OperationalAuditConstraints
import Descent.Portability.OptimizedFrameRepairAudit
import Descent.Portability.PairedGainTailExperiment
import Descent.Portability.PairedMedianOfMeans
import Descent.Portability.SafeRepairGeometry
import Descent.Portability.SecondMomentAuditConfidence
import Descent.Portability.SecondMomentFrameRepair
import Descent.Portability.SharedAuditCompletion
import Descent.Portability.SpectralAuditAllocationLaw
import Descent.Portability.SpectralAuditConfidence
import Descent.Portability.SpectralAuditCost
import Descent.Portability.SpectralAuditDesign
import Descent.Portability.SpectralAuditDualCertificate
import Descent.Portability.SpectralAuditNumericalCertificate
import Descent.Portability.SpectralCostEquality
import Descent.Portability.SpectralRangeAuditDesign
import Descent.Portability.SubgroupFrameTransport
import Descent.Portability.SubgroupRepairGeometry

/-!
Combined statement and axiom audit of all 26 numbered mathematical results
in Decision-Directed Portability. Each entry checks the actual endpoint,
including its hypotheses, and the transitive axiom closure. This is not a
verification of the Python reference implementation or of biological input
identification. The associated run rebuilds the local source dependency closure.
-/

-- Result 1: Outcome-term cancellation.
#check Descent.Portability.DecisionLossContrasts.bregman_difference
#print axioms Descent.Portability.DecisionLossContrasts.bregman_difference
#check Descent.Portability.BregmanAuditContrasts.expected_risk_difference
#print axioms Descent.Portability.BregmanAuditContrasts.expected_risk_difference
#check Descent.Portability.BregmanAuditContrasts.binary_expected_contrast
#print axioms Descent.Portability.BregmanAuditContrasts.binary_expected_contrast

-- Result 2: Exact linear information requirement.
#check Descent.Portability.DecisionInformationRank.identifies_iff_kernel_of_interior
#print axioms Descent.Portability.DecisionInformationRank.identifies_iff_kernel_of_interior
#check Descent.Portability.MatrixDecisionInformation.report_identification_iff
#print axioms Descent.Portability.MatrixDecisionInformation.report_identification_iff
#check Descent.Portability.MatrixDecisionInformation.exact_matrix_summary_count
#print axioms Descent.Portability.MatrixDecisionInformation.exact_matrix_summary_count

-- Result 3: Loss predictability versus fixed useful repair.
#check Descent.Portability.LossExplainabilitySeparation.separation
#print axioms Descent.Portability.LossExplainabilitySeparation.separation
#check Descent.Portability.LossExplainabilitySeparation.explained_fraction_tendsto_zero
#print axioms Descent.Portability.LossExplainabilitySeparation.explained_fraction_tendsto_zero
#check Descent.Portability.PairedGainTailExperiment.score_translation
#print axioms Descent.Portability.PairedGainTailExperiment.score_translation

-- Result 4: Exact augmented-audit law.
#check Descent.Portability.JointAuditExperiment.observations_map
#print axioms Descent.Portability.JointAuditExperiment.observations_map
#check Descent.Portability.AugmentedAuditLaw.audit_mean
#print axioms Descent.Portability.AugmentedAuditLaw.audit_mean
#check Descent.Portability.AugmentedAuditLaw.audit_variance
#print axioms Descent.Portability.AugmentedAuditLaw.audit_variance
#check Descent.Portability.AugmentedAuditLaw.sampling_only_variance
#print axioms Descent.Portability.AugmentedAuditLaw.sampling_only_variance
#check Descent.Portability.SharedAuditCompletion.frame_covariance
#print axioms Descent.Portability.SharedAuditCompletion.frame_covariance

-- Result 5: Exact support and mean-band variance completion.
#check Descent.Portability.AuditVarianceGeometry.maximum_attained
#print axioms Descent.Portability.AuditVarianceGeometry.maximum_attained
#check Descent.Portability.BoundedAuditCompletion.worst_case_upper
#print axioms Descent.Portability.BoundedAuditCompletion.worst_case_upper
#check Descent.Portability.BoundedAuditCompletion.worst_case_attained
#print axioms Descent.Portability.BoundedAuditCompletion.worst_case_attained

-- Result 6: Closed-form minimax proxy.
#check Descent.Portability.AuditVarianceGeometry.minimax_proxy
#print axioms Descent.Portability.AuditVarianceGeometry.minimax_proxy
#check Descent.Portability.AuditVarianceGeometry.proxy_unique
#print axioms Descent.Portability.AuditVarianceGeometry.proxy_unique
#check Descent.Portability.AuditVarianceGeometry.full_observation
#print axioms Descent.Portability.AuditVarianceGeometry.full_observation
#check Descent.Portability.BoundedAuditCompletion.minimax_attaining_law
#print axioms Descent.Portability.BoundedAuditCompletion.minimax_attaining_law

-- Result 7: Simultaneously sharp covariance envelope.
#check Descent.Portability.SharedAuditCompletion.frame_variance_upper
#print axioms Descent.Portability.SharedAuditCompletion.frame_variance_upper
#check Descent.Portability.SharedAuditCompletion.simultaneous_attainment
#print axioms Descent.Portability.SharedAuditCompletion.simultaneous_attainment

-- Result 8: Bounded-increment Bernstein inequality.
#check Descent.Portability.BernsteinConfidence.bernstein
#print axioms Descent.Portability.BernsteinConfidence.bernstein

-- Result 9: Simultaneous finite decision library.
#check Descent.Portability.FiniteAuditConfidence.finite_library_exact_range
#print axioms Descent.Portability.FiniteAuditConfidence.finite_library_exact_range

-- Result 10: Uniform confidence ball for a continuous repair span.
#check Descent.Portability.SpectralAuditConfidence.confidence
#print axioms Descent.Portability.SpectralAuditConfidence.confidence
#check Descent.Portability.GramAuditGeometry.error_norm
#print axioms Descent.Portability.GramAuditGeometry.error_norm
#check Descent.Portability.CertifiedFrameRepair.estimate_confidence
#print axioms Descent.Portability.CertifiedFrameRepair.estimate_confidence

-- Result 11: Exact repair geometry and oracle.
#check Descent.Portability.DecisionLossContrasts.frame_gain
#print axioms Descent.Portability.DecisionLossContrasts.frame_gain
#check Descent.Portability.SafeRepairGeometry.gain_eq_oracle_sub_regret
#print axioms Descent.Portability.SafeRepairGeometry.gain_eq_oracle_sub_regret
#check Descent.Portability.FrameConvexRepair.oracle_gain
#print axioms Descent.Portability.FrameConvexRepair.oracle_gain
#check Descent.Portability.FrameConvexRepair.gain_upper
#print axioms Descent.Portability.FrameConvexRepair.gain_upper

-- Result 12: General compact convex confidence-set repair.
#check Descent.Portability.GramConvexRepair.compact_optimum
#print axioms Descent.Portability.GramConvexRepair.compact_optimum
#check Descent.Portability.GramConvexRepair.unique_least_signal
#print axioms Descent.Portability.GramConvexRepair.unique_least_signal
#check Descent.Portability.FrameMeanImage.attained
#print axioms Descent.Portability.FrameMeanImage.attained
#check Descent.Portability.FrameConvexRepair.compact_outcome_optimum
#print axioms Descent.Portability.FrameConvexRepair.compact_outcome_optimum

-- Result 13: Closed-form repair, oracle interval and regret.
#check Descent.Portability.GramRepairOptimality.soft_threshold
#print axioms Descent.Portability.GramRepairOptimality.soft_threshold
#check Descent.Portability.GramRepairOptimality.robust_optimum
#print axioms Descent.Portability.GramRepairOptimality.robust_optimum
#check Descent.Portability.GramSafeRepair.repair_certificate
#print axioms Descent.Portability.GramSafeRepair.repair_certificate
#check Descent.Portability.GramSafeRepair.oracle_interval
#print axioms Descent.Portability.GramSafeRepair.oracle_interval
#check Descent.Portability.GramRepairOptimality.certificate_vs_oracle
#print axioms Descent.Portability.GramRepairOptimality.certificate_vs_oracle
#check Descent.Portability.ClippedFrameRepair.false_gain_probability
#print axioms Descent.Portability.ClippedFrameRepair.false_gain_probability

-- Result 14: Convex audit design and attained dual allocation.
#check Descent.Portability.SpectralAuditDesign.objective_convex
#print axioms Descent.Portability.SpectralAuditDesign.objective_convex
#check Descent.Portability.SpectralAuditDualCertificate.weak_duality
#print axioms Descent.Portability.SpectralAuditDualCertificate.weak_duality
#check Descent.Portability.SpectralAuditAllocationLaw.attained_allocation_law
#print axioms Descent.Portability.SpectralAuditAllocationLaw.attained_allocation_law
#check Descent.Portability.FiniteAuditAllocationLaw.attained_allocation_law
#print axioms Descent.Portability.FiniteAuditAllocationLaw.attained_allocation_law

-- Result 15: Labeling-cost bound and complete equality conditions.
#check Descent.Portability.SpectralAuditCost.cost_lower_bound
#print axioms Descent.Portability.SpectralAuditCost.cost_lower_bound
#check Descent.Portability.SpectralCostEquality.cost_equality_complete
#print axioms Descent.Portability.SpectralCostEquality.cost_equality_complete

-- Result 16: Exact range-cap reduction and geometric approximation.
#check Descent.Portability.SpectralRangeAuditDesign.exact_cap_reduction
#print axioms Descent.Portability.SpectralRangeAuditDesign.exact_cap_reduction
#check Descent.Portability.SpectralRangeAuditDesign.finite_search_exists
#print axioms Descent.Portability.SpectralRangeAuditDesign.finite_search_exists
#check Descent.Portability.SpectralAuditNumericalCertificate.capped_radius_error
#print axioms Descent.Portability.SpectralAuditNumericalCertificate.capped_radius_error
#check Descent.Portability.OptimizedFrameRepairAudit.design_exists
#print axioms Descent.Portability.OptimizedFrameRepairAudit.design_exists

-- Result 17: Exact aggregation of identical decision cells.
#check Descent.Portability.IdenticalAuditCells.spectral_optimum_constant
#print axioms Descent.Portability.IdenticalAuditCells.spectral_optimum_constant
#check Descent.Portability.IdenticalAuditCells.capped_spectral_optimum_constant
#print axioms Descent.Portability.IdenticalAuditCells.capped_spectral_optimum_constant

-- Result 18: Linear operational requirements with defined denominators.
#check Descent.Portability.OperationalAuditConstraints.precision_requirement
#print axioms Descent.Portability.OperationalAuditConstraints.precision_requirement
#check Descent.Portability.OperationalAuditConstraints.recall_requirement
#print axioms Descent.Portability.OperationalAuditConstraints.recall_requirement
#check Descent.Portability.OperationalAuditConstraints.f1_requirement
#print axioms Descent.Portability.OperationalAuditConstraints.f1_requirement
#check Descent.Portability.OperationalAuditConstraints.false_positive_requirement
#print axioms Descent.Portability.OperationalAuditConstraints.false_positive_requirement
#check Descent.Portability.OperationalAuditConstraints.net_benefit_difference
#print axioms Descent.Portability.OperationalAuditConstraints.net_benefit_difference
#check Descent.Portability.OperationalAuditConstraints.f1_linear_target
#print axioms Descent.Portability.OperationalAuditConstraints.f1_linear_target

-- Result 19: Certified threshold selection after the audit.
#check Descent.Portability.AuditSelectionSafety.certified_selection
#print axioms Descent.Portability.AuditSelectionSafety.certified_selection

-- Result 20: Exact disagreement-region variance payoff.
#check Descent.Portability.DisagreementAuditPayoff.equal_expected_budgets
#print axioms Descent.Portability.DisagreementAuditPayoff.equal_expected_budgets
#check Descent.Portability.DisagreementAuditPayoff.prospective_bounds
#print axioms Descent.Portability.DisagreementAuditPayoff.prospective_bounds
#check Descent.Portability.DisagreementAuditPayoff.simultaneous_attainment
#print axioms Descent.Portability.DisagreementAuditPayoff.simultaneous_attainment
#check Descent.Portability.DisagreementAuditPayoff.variance_ratio
#print axioms Descent.Portability.DisagreementAuditPayoff.variance_ratio

-- Result 21: Exact value of expanding the repair span.
#check Descent.Portability.FrameRepairSpans.frame_oracle_attained
#print axioms Descent.Portability.FrameRepairSpans.frame_oracle_attained
#check Descent.Portability.FrameRepairSpans.frame_oracle_increment
#print axioms Descent.Portability.FrameRepairSpans.frame_oracle_increment

-- Result 22: Simultaneous subgroup safety and stable-mixture transport.
#check Descent.Portability.SubgroupRepairGeometry.safeSet_convex
#print axioms Descent.Portability.SubgroupRepairGeometry.safeSet_convex
#check Descent.Portability.SubgroupRepairGeometry.zero_mem_safeSet
#print axioms Descent.Portability.SubgroupRepairGeometry.zero_mem_safeSet
#check Descent.Portability.SubgroupFrameTransport.weighted_objective_concave
#print axioms Descent.Portability.SubgroupFrameTransport.weighted_objective_concave
#check Descent.Portability.SubgroupFrameTransport.certified_mixture_transport
#print axioms Descent.Portability.SubgroupFrameTransport.certified_mixture_transport

-- Result 23: Exact sensitivity to conditional-mean drift.
#check Descent.Portability.MeanDriftRepair.gain_change
#print axioms Descent.Portability.MeanDriftRepair.gain_change
#check Descent.Portability.MeanDriftRepair.same_mean_gain
#print axioms Descent.Portability.MeanDriftRepair.same_mean_gain
#check Descent.Portability.MeanDriftRepair.drift_lower
#print axioms Descent.Portability.MeanDriftRepair.drift_lower
#check Descent.Portability.MeanDriftRepair.attained_drift_penalty
#print axioms Descent.Portability.MeanDriftRepair.attained_drift_penalty

-- Result 24: Second-moment-only continuous repair confidence.
#check Descent.Portability.SecondMomentAuditConfidence.confidence
#print axioms Descent.Portability.SecondMomentAuditConfidence.confidence
#check Descent.Portability.SecondMomentFrameRepair.false_certificate_probability
#print axioms Descent.Portability.SecondMomentFrameRepair.false_certificate_probability

-- Result 25: Paired median-of-means certification.
#check Descent.Portability.PairedMedianOfMeans.simultaneous
#print axioms Descent.Portability.PairedMedianOfMeans.simultaneous

-- Result 26: Hard-budget guard and preserved error control.
#check Descent.Portability.BernoulliBudgetLaw.cost_tail
#print axioms Descent.Portability.BernoulliBudgetLaw.cost_tail
#check Descent.Portability.HardBudgetAuditGuard.spending_le_hard
#print axioms Descent.Portability.HardBudgetAuditGuard.spending_le_hard
#check Descent.Portability.HardBudgetAuditGuard.joint_abort_probability
#print axioms Descent.Portability.HardBudgetAuditGuard.joint_abort_probability
#check Descent.Portability.HardBudgetAuditGuard.guarded_repair_certificate
#print axioms Descent.Portability.HardBudgetAuditGuard.guarded_repair_certificate
#check Descent.Portability.ConditionalGuardError.conditional_repair_certificate
#print axioms Descent.Portability.ConditionalGuardError.conditional_repair_certificate
#check Descent.Portability.GuardedRepairDeployment.harm_probability
#print axioms Descent.Portability.GuardedRepairDeployment.harm_probability
