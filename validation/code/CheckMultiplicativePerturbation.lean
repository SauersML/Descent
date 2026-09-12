/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Pangenome.GraphCoalescent.MultiplicativePerturbation

/-! Axiom audit of MultiplicativePerturbation. -/

open Descent.Pangenome.GraphCoalescent

#print axioms massStep
#print axioms multiplicativeStep_eq_massStep
#print axioms sum_massStep
#print axioms blockMass_nonneg
#print axioms massStep_nonneg
#print axioms sum_abs_blockMass_sub_le
#print axioms pairProductSum_max_sub_min_le
#print axioms pairMinMass
#print axioms pairExcessMass
#print axioms pairMinMass_comm
#print axioms pairMinMass_nonneg
#print axioms pairExcessMass_nonneg
#print axioms pairExcessMass_add_le
#print axioms perturbedHold
#print axioms perturbedSep
#print axioms perturbedStep
#print axioms perturbedAgree
#print axioms perturbedHold_nonneg
#print axioms perturbedStep_nonneg
#print axioms sum_perturbedStep
#print axioms perturbedStep_absorb
#print axioms perturbedStep_hazard
#print axioms separationMass_le_mul
#print axioms sum_skeletonPathWeight
#print axioms poissonPMFReal_succ_mul
#print axioms hasSum_poissonPMFReal_mul_nat
#print axioms sum_perturbedStep_fst
#print axioms sum_perturbedStep_snd
#print axioms perturbedStartLaw
#print axioms perturbedStartLaw_nonneg
#print axioms sum_perturbedStartLaw
#print axioms separationMass_perturbedStart
#print axioms sum_filter_fst_perturbedStartLaw
#print axioms sum_filter_snd_perturbedStartLaw
#print axioms massPathLaw
#print axioms multiplicativePathLaw_eq_massPathLaw
#print axioms sum_filter_perturbed_fst_eq
#print axioms sum_filter_perturbed_snd_eq
#print axioms massPathTotalVariation_le
#print axioms reportPathLaw_nonneg
#print axioms sum_reportPathLaw
#print axioms massPathLaw_nonneg
#print axioms sum_massPathLaw
#print axioms report_mass_pathTotalVariation_le
#print axioms report_mass_pathTotalVariation_le_one
#print axioms report_mass_poissonTotalVariation_le
#print axioms fiberSize
#print axioms fiberSize_pos
#print axioms spreadMass
#print axioms spreadMass_nonneg
#print axioms blockMass_spreadMass_graphKer
#print axioms sum_spreadMass
#print axioms sum_abs_unitMass_sub_spreadMass
#print axioms report_spread_poissonTotalVariation_le
