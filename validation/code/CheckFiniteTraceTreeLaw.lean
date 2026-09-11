/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.FiniteTraceTreeLaw

/-! Axiom audit of FiniteTraceTreeLaw. -/

open Descent.Portability.FiniteTraceTreeLaw

#print axioms TraceTree.traceWeight_eq_prod_edgeProbabilities
#print axioms TraceTree.traceWeight_nonneg
#print axioms TraceTree.sum_traceWeight_mul_eq_backwardValue
#print axioms TraceTree.backwardValue_const
#print axioms TraceTree.traceWeight_sum
#print axioms TraceTree.expectation_reportLaw
#print axioms TraceTree.reportLaw_event_eq_trace_sum
#print axioms TraceTree.reportLaw_eq_pushforward
#print axioms TraceTree.definedMass_reportLaw
#print axioms TraceTree.weightedDefinedMetric_reportLaw
#print axioms TraceTree.backwardValue_graft
#print axioms TraceTree.reportLaw_graft
#print axioms TraceTree.reportLaw_stagedTree
#print axioms TraceTree.propagate_expectation_eq_backwardReadout_eq_trace_sum
#print axioms TraceTree.reportLaw_transitionTree
#print axioms TraceTree.reportLaw_historyTree
#print axioms TraceTree.trace_sum_historyTree_eq_path_sum
#print axioms TraceTree.rationalValue_traceWeight
#print axioms TraceTree.rationalValue_backwardValue
#print axioms TraceTree.rationalLaw_reportLaw
#print axioms TraceTree.rationalValue_conditionalMetric_reportLaw
#print axioms RationalTraceTree.rationalTree_toReal
#print axioms RationalTraceTree.backwardValue_toReal
#print axioms RationalTraceTree.exampleTree_evaluate
#print axioms RationalTraceTree.exampleTree_backwardValue
