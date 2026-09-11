/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.SimultaneousMigrationPulse

/-! Axiom audit of SimultaneousMigrationPulse. -/

open Descent.Portability.SimultaneousMigrationPulse

#print axioms linkage_eq_AB_sub_marginals
#print axioms totalMigration_nonneg
#print axioms migrationShare_nonneg
#print axioms sum_migrationShare_le_one
#print axioms sum_pair_migrationShare_le_one
#print axioms migrationWeight_nonneg
#print axioms retainedWeight_nonneg
#print axioms retainedMixture_eq_add_weightedDifferences
#print axioms migrantMixture_coordinate
#print axioms simultaneousMigrationPulse_leftFrequency
#print axioms simultaneousMigrationPulse_rightFrequency
#print axioms simultaneousMigrationPulse_linkage
#print axioms sum_pair_recipient
#print axioms abs_pairShareSum_le
#print axioms abs_recipientShareSum_le_one
#print axioms enlargedPulseExpansion_velocity
#print axioms enlargedTreeVelocity_sum
#print axioms enlargedStageExpansion_migration_velocity
#print axioms simultaneousMigrationExpansion_velocity
