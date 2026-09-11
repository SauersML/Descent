/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.PartialHaplotypeCarrier

/-! Axiom audit of PartialHaplotypeCarrier. -/

open Descent.Portability.PartialHaplotypeCarrier

#print axioms PartialType.eq_of_fields
#print axioms load_cons
#print axioms load_singleLocusType
#print axioms withinBudget_zero
#print axioms withinBudget_fullType
#print axioms withinBudget_of_le
#print axioms card_le_sum_load
#print axioms card_le_capacity_total
#print axioms withinBudget_finite
#print axioms partialTypeEquiv
#print axioms retains_iff_ne_empty
#print axioms card_retainingAssignment
#print axioms card_partialType
#print axioms padConfiguration
#print axioms card_padConfiguration
#print axioms count_some_padConfiguration
#print axioms padWithinBudget
#print axioms padWithinBudget_injective
#print axioms card_withinBudget_le_choose_card
#print axioms card_withinBudget_le_choose
#print axioms load_migrate
#print axioms withinBudget_migrate
#print axioms load_mutate
#print axioms withinBudget_mutate
#print axioms load_split
#print axioms withinBudget_split
#print axioms compatible_self
#print axioms compatible_of_disjoint
#print axioms coalesce_allele_eq_of_compatible
#print axioms load_coalesce_le
#print axioms withinBudget_coalesce
#print axioms agrees_fullType
#print axioms marginalFrequency_nonneg
#print axioms marginalFrequency_le_one
#print axioms marginalFrequency_fullType
#print axioms configurationMoment_cons
#print axioms configurationMoment_add
#print axioms configurationMoment_nonneg
#print axioms configurationMoment_le_one
