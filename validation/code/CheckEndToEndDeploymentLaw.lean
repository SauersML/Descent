/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.EndToEndDeploymentLaw

/-! Axiom audit of EndToEndDeploymentLaw. -/

open Descent.Portability.EndToEndDeploymentLaw

#print axioms DemeMoments.predictiveCovariance_eq_dot
#print axioms DemeMoments.metrics_ofPopulation
#print axioms DemeMoments.predictiveCovariance_sub_channels
#print axioms DemeMoments.scoreVariance_sub_channel
#print axioms DemeMoments.outcomeVariance_sub_channels
#print axioms ridgeWeights_normal
#print axioms dot_ridgeWeights_target
#print axioms pooledTrainedWeights_single
#print axioms predictiveCovariance_trainedWeights
#print axioms calibrationSlope_trainedWeights
#print axioms one_le_calibrationSlope_trainedWeights
#print axioms calibrationSlope_trainedWeights_zero
#print axioms r2_trainedWeights_zero
#print axioms expectedDemeMoments_historyEventKernel
#print axioms expectedDemeMoments_rateHistoryKernel
#print axioms expectedDemeMoments_eq_of_moments_eq
#print axioms transferReport_historyEventKernel
#print axioms transferReport_eq_of_moments_eq
