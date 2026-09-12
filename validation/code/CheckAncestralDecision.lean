/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Pangenome.AncestralLocality.AncestralDecision

/-! Axiom audit of AncestralDecision. -/

open Descent.Pangenome.AncestralLocality

#print axioms ruleKernel_orderedChild
#print axioms sampling_identity
#print axioms sampling_identity_exchangeKernel
#print axioms sum_tuple_snoc
#print axioms samplingObservable_decisionBranch
#print axioms sum_filter_update
#print axioms samplingObservable_coalesceArguments
#print axioms samplingObservable_coalesceArguments_comm
#print axioms samplingObservable_decisionBranch_of_agree
#print axioms orderedChild_of_ne
#print axioms tagDetermined_restrict
#print axioms coalesceTags_apply
#print axioms decisionTags_castSucc
#print axioms decisionTags_last
#print axioms tagDetermined_coalesceArguments
#print axioms tagDetermined_decisionBranch
#print axioms samplingObservable_decisionBranch_of_not_mem
#print axioms tagWeight_one
#print axioms sum_insert_le_add
#print axioms tagWeight_decisionTags
#print axioms tagWeight_decisionTags_of_not_mem
#print axioms tagWeight_decisionTags_le
#print axioms tagWeight_coalesceTags_le
#print axioms tagCount_decisionTags_le
#print axioms tagCount_coalesceTags_le
#print axioms decisionRate_le
#print axioms card_tagMaterial
#print axioms tagCount_le_mul
