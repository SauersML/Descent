/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.NeutralDemeRelabelKernel

/-! Axiom audit of NeutralDemeRelabelKernel. -/

open Descent.Portability.NeutralDemeRelabelKernel

#print axioms relabelCarrier
#print axioms load_map_relabelCarrier
#print axioms withinBudget_map_relabelCarrier
#print axioms relabelState
#print axioms stateLaw_relabelState
#print axioms continuous_relabelState
#print axioms relabelStateKernel
#print axioms isMarkovKernel_relabelStateKernel
#print axioms marginalFrequency_stateLaw_relabelState
#print axioms configurationMoment_stateLaw_relabelState
#print axioms budgetMomentFeature_relabelState
#print axioms relabelKernel
#print axioms relabelKernel_mulVec
#print axioms relabelKernel_rowSum
#print axioms relabelKernel_nonneg
#print axioms integral_momentPolynomial_relabelStateKernel
#print axioms integral_momentPolynomial_comp_hetero
#print axioms integral_momentPolynomial_splitHistoryKernel
