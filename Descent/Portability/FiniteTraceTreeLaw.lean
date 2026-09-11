/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.RationalReportClosure
import Mathlib.Data.Fintype.BigOperators

assert_below Descent.Decision Descent.Program

/-!
# Finite trace trees and the complete report law

NOTE2 Theorem 1 and equation (7). A fully specified finite experiment is a `TraceTree`. A leaf
carries the complete report. An internal node carries a finite branch type, the actual
conditional law of its branches (a corpus `FiniteReportLaw`), and the continuation after each
branch. The continuation after one branch may branch over a different type, and stop at a
different depth, than the continuation after another, so what can happen next depends on the
whole history so far. Nothing is forgotten: every node is reached by exactly one history, so
the law at a node is a function of that history, which is the note's `p_e(Θ, τ_<e)`. Every tree
is finite by construction and every branch type is a `Fintype`.

The complete report law (7) is the sum over complete traces of the product of edge
probabilities. `Trace` is the finite type of complete traces, `traceWeight` the chain-rule
product (the product of the list `edgeProbabilities`), and `traceReport` the report reached.
Proved by induction on the tree: positivity `traceWeight_nonneg`, normalization
`traceWeight_sum`, and enumeration equals backward evaluation
(`sum_traceWeight_mul_eq_backwardValue`). The recursive law of the note's proof (the point mass
at a leaf, the branch-law mixture of the children's laws at a node) has exactly these
expectations (`expectation_reportLaw`), is the pushforward of the trace law
(`reportLaw_eq_pushforward`), and gives (7) for every event (`reportLaw_event_eq_trace_sum`).

Forward propagation is stage composition. `graft` continues every leaf of an experiment, whose
leaf label is the retained memory, with a further experiment; `reportLaw_graft` shows the
composite report law is the corpus `FiniteReportLaw.bind`. Iterating, `reportLaw_stagedTree`
shows that the report law after `n` stages is the corpus forward propagation
`ExactFiniteHistoryLaw.propagate`, where each stage is an arbitrary dependent tree. Hence forward
propagation, backward evaluation (`ExactFiniteHistoryLaw.backwardReadout`) and complete-trace
enumeration agree (`propagate_expectation_eq_backwardReadout_eq_trace_sum`). The corpus
time-indexed kernels on one state type are the one-level stages of `historyTree`, whose trace
enumeration is the corpus path enumeration (`trace_sum_historyTree_eq_path_sum`).

The rational clause is transported from `RationalReportClosure`. If every branch law is rational
(`RationalTree`), then every trace weight, every expectation of a rational metric, every cell of
the report law, and every conditional expectation with positive definedness probability is
rational. The finite algorithm is literal: `RationalTraceTree.evaluate` is backward evaluation
in rational arithmetic, and `backwardValue_toReal` shows the real theory returns its cast.

Not formalized: any complexity claim (the note's count of census states), infinite or continuous
branch sets, and the correspondence between a tree and any executable pipeline.

## Empirical status

None. The bodies here are algebra: branch laws and report values are supplied inputs, and every
statement is an identity between finite sums and products of them.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.FiniteTraceTreeLaw

open RationalReportClosure

noncomputable section

/-- A finite experiment with all memory retained. A leaf carries the complete report. A node
carries a finite branch type, the actual conditional law of its branches, and the continuation
after each branch; different continuations may branch over different types. -/
inductive TraceTree (Report : Type) : Type 1
  | leaf (report : Report) : TraceTree Report
  | node (Branch : Type) [Fintype Branch] (law : FiniteReportLaw Branch)
      (child : Branch → TraceTree Report) : TraceTree Report

namespace TraceTree

variable {Report : Type}

/-- The complete traces of an experiment: one branch at every node on the way from the root to
a leaf. -/
def Trace : TraceTree Report → Type
  | .leaf _ => Unit
  | @TraceTree.node _ Branch _ _ child => Σ branch : Branch, Trace (child branch)

/-- An experiment has finitely many complete traces. -/
instance traceFintype : (tree : TraceTree Report) → Fintype (Trace tree)
  | .leaf _ => inferInstanceAs (Fintype Unit)
  | @TraceTree.node _ Branch _ _ child => by
      letI : ∀ branch, Fintype (Trace (child branch)) :=
        fun branch ↦ traceFintype (child branch)
      exact inferInstanceAs (Fintype (Σ branch : Branch, Trace (child branch)))

/-- The report at the end of a complete trace. -/
def traceReport : (tree : TraceTree Report) → Trace tree → Report
  | .leaf report, _ => report
  | @TraceTree.node _ _ _ _ child, trace => traceReport (child trace.1) trace.2

/-- The chain-rule weight of a complete trace: the conditional probability of its first branch
times the weight of the rest of the trace in the continuation that branch selected. -/
def traceWeight : (tree : TraceTree Report) → Trace tree → ℝ
  | .leaf _, _ => 1
  | @TraceTree.node _ _ _ law child, trace =>
      law.mass trace.1 * traceWeight (child trace.1) trace.2

/-- The edge probabilities along a complete trace, in the order the edges are taken. Each is
read at the node the preceding history reached. -/
def edgeProbabilities : (tree : TraceTree Report) → Trace tree → List ℝ
  | .leaf _, _ => []
  | @TraceTree.node _ _ _ law child, trace =>
      law.mass trace.1 :: edgeProbabilities (child trace.1) trace.2

/-- The chain-rule weight of a trace is the product of its edge probabilities, `∏_{e ∈ τ} p_e`
in NOTE2 (7). -/
theorem traceWeight_eq_prod_edgeProbabilities (tree : TraceTree Report) (trace : Trace tree) :
    traceWeight tree trace = (edgeProbabilities tree trace).prod := by
  induction tree with
  | leaf _ => rfl
  | node Branch law child ih =>
    change law.mass trace.1 * traceWeight (child trace.1) trace.2 =
      (law.mass trace.1 :: edgeProbabilities (child trace.1) trace.2).prod
    rw [List.prod_cons, ih trace.1 trace.2]

/-- **NOTE2 Theorem 1, positivity.** Every trace weight is nonnegative. -/
theorem traceWeight_nonneg (tree : TraceTree Report) (trace : Trace tree) :
    0 ≤ traceWeight tree trace := by
  induction tree with
  | leaf _ => exact zero_le_one
  | node Branch law child ih =>
    exact mul_nonneg (law.mass_nonneg trace.1) (ih trace.1 trace.2)

/-- Backward evaluation of a metric of the report: a leaf returns the metric at its report, and
a node returns the expectation, under its branch law, of the values of its continuations. -/
def backwardValue : TraceTree Report → (Report → ℝ) → ℝ
  | .leaf report, metric => metric report
  | @TraceTree.node _ _ _ law child, metric =>
      law.expectation fun branch ↦ backwardValue (child branch) metric

/-- **NOTE2 (7), enumeration equals backward evaluation.** Summing the chain-rule weight of
every complete trace against a metric of its report gives the backward value, for every real
metric, including zero-probability traces. -/
theorem sum_traceWeight_mul_eq_backwardValue (tree : TraceTree Report) (metric : Report → ℝ) :
    ∑ trace, traceWeight tree trace * metric (traceReport tree trace) =
      backwardValue tree metric := by
  induction tree with
  | leaf report =>
    change ∑ _trace : Unit, (1 : ℝ) * metric report = metric report
    simp
  | node Branch law child ih =>
    change ∑ trace : (Σ branch : Branch, Trace (child branch)),
        law.mass trace.1 * traceWeight (child trace.1) trace.2 *
          metric (traceReport (child trace.1) trace.2) =
      ∑ branch, law.mass branch * backwardValue (child branch) metric
    rw [Fintype.sum_sigma]
    refine Finset.sum_congr rfl fun branch _ ↦ ?_
    rw [← ih branch, Finset.mul_sum]
    exact Finset.sum_congr rfl fun trace _ ↦ mul_assoc _ _ _

/-- A constant metric has backward value equal to the constant. -/
theorem backwardValue_const (tree : TraceTree Report) (value : ℝ) :
    backwardValue tree (fun _ ↦ value) = value := by
  induction tree with
  | leaf _ => rfl
  | node Branch law child ih =>
    change ∑ branch, law.mass branch * backwardValue (child branch) (fun _ ↦ value) = value
    simp only [ih, ← Finset.sum_mul, law.mass_sum, one_mul]

/-- **NOTE2 Theorem 1, normalization.** The chain-rule weights of the complete traces sum to one,
derived from the normalization of every branch law. -/
theorem traceWeight_sum (tree : TraceTree Report) : ∑ trace, traceWeight tree trace = 1 := by
  have h := sum_traceWeight_mul_eq_backwardValue tree fun _ ↦ (1 : ℝ)
  rw [backwardValue_const] at h
  simpa only [mul_one] using h

/-- The law of the complete trace, with the chain-rule weights as cell masses. -/
def traceLaw (tree : TraceTree Report) : FiniteReportLaw (Trace tree) where
  mass := traceWeight tree
  mass_nonneg := traceWeight_nonneg tree
  mass_sum := traceWeight_sum tree

/-- The report law built by the recursion in the proof of NOTE2 Theorem 1: the point mass at a
leaf, and at a node the mixture of the continuations' laws by the branch law. -/
def reportLaw [Fintype Report] : TraceTree Report → FiniteReportLaw Report
  | .leaf report => FiniteReportLaw.pointMass report
  | @TraceTree.node _ _ _ law child => law.bind fun branch ↦ reportLaw (child branch)

/-- The recursively composed report law integrates every metric to its backward value. -/
theorem expectation_reportLaw [Fintype Report] (tree : TraceTree Report)
    (metric : Report → ℝ) : (reportLaw tree).expectation metric = backwardValue tree metric := by
  induction tree with
  | leaf report => exact FiniteReportLaw.expectation_pointMass report metric
  | node Branch law child ih =>
    change (law.bind fun branch ↦ reportLaw (child branch)).expectation metric =
      law.expectation fun branch ↦ backwardValue (child branch) metric
    rw [FiniteReportLaw.expectation_bind]
    simp only [ih]

/-- **NOTE2 (7).** For every event `B` of reports, its probability under the report law is the
sum over complete traces of the product of the edge probabilities times `1{R(τ) ∈ B}`. -/
theorem reportLaw_event_eq_trace_sum [Fintype Report] (tree : TraceTree Report)
    (event : Set Report) :
    (reportLaw tree).expectation (event.indicator 1) =
      ∑ trace, (edgeProbabilities tree trace).prod *
        event.indicator 1 (traceReport tree trace) := by
  rw [expectation_reportLaw, ← sum_traceWeight_mul_eq_backwardValue]
  simp only [traceWeight_eq_prod_edgeProbabilities]

/-- The recursively composed report law is the pushforward of the trace law along the report
map, so the complete report law is determined by the traces and their weights. -/
theorem reportLaw_eq_pushforward [Fintype Report] (tree : TraceTree Report) :
    reportLaw tree = (traceLaw tree).pushforward (traceReport tree) := by
  refine (FiniteReportLaw.eq_iff_singleton_expectations_eq _ _).mpr fun report ↦ ?_
  rw [FiniteReportLaw.expectation_pushforward, expectation_reportLaw,
    ← sum_traceWeight_mul_eq_backwardValue]
  rfl

/-- The definedness probability `d` of a partial metric as a trace enumeration. -/
theorem definedMass_reportLaw [Fintype Report] (tree : TraceTree Report)
    (metric : Report → Option ℝ) :
    (reportLaw tree).definedMass metric =
      ∑ trace, traceWeight tree trace *
        (if (metric (traceReport tree trace)).isSome then 1 else 0) := by
  rw [FiniteReportLaw.definedMass, expectation_reportLaw, ← sum_traceWeight_mul_eq_backwardValue]

/-- The zero-extended numerator `n` of a partial metric as a trace enumeration. -/
theorem weightedDefinedMetric_reportLaw [Fintype Report] (tree : TraceTree Report)
    (metric : Report → Option ℝ) :
    (reportLaw tree).weightedDefinedMetric metric =
      ∑ trace, traceWeight tree trace * (metric (traceReport tree trace)).getD 0 := by
  rw [FiniteReportLaw.weightedDefinedMetric, expectation_reportLaw,
    ← sum_traceWeight_mul_eq_backwardValue]

/-! ### Forward propagation as stage composition -/

/-- Continue an experiment after its leaves. The label of a leaf is the memory retained at the
end of the first stage, and the continuation it selects may be an arbitrary experiment. -/
def graft {Memory : Type} : TraceTree Memory → (Memory → TraceTree Report) → TraceTree Report
  | .leaf memory, continuation => continuation memory
  | @TraceTree.node _ Branch _ law child, continuation =>
      .node Branch law fun branch ↦ graft (child branch) continuation

/-- Backward evaluation of a composite experiment evaluates the continuations first, then the
first stage against their values. -/
theorem backwardValue_graft {Memory : Type} (tree : TraceTree Memory)
    (continuation : Memory → TraceTree Report) (metric : Report → ℝ) :
    backwardValue (graft tree continuation) metric =
      backwardValue tree fun memory ↦ backwardValue (continuation memory) metric := by
  induction tree with
  | leaf _ => rfl
  | node Branch law child ih =>
    change ∑ branch, law.mass branch * backwardValue (graft (child branch) continuation) metric =
      ∑ branch, law.mass branch *
        backwardValue (child branch) fun memory ↦ backwardValue (continuation memory) metric
    simp only [ih]

/-- **Forward propagation through one stage.** The report law of a composite experiment is the
corpus composition `FiniteReportLaw.bind` of the first stage's law of the retained memory with
the continuation laws. -/
theorem reportLaw_graft {Memory : Type} [Fintype Memory] [Fintype Report]
    (tree : TraceTree Memory) (continuation : Memory → TraceTree Report) :
    reportLaw (graft tree continuation) =
      (reportLaw tree).bind fun memory ↦ reportLaw (continuation memory) := by
  refine (FiniteReportLaw.eq_iff_singleton_expectations_eq _ _).mpr fun report ↦ ?_
  simp only [expectation_reportLaw, FiniteReportLaw.expectation_bind, backwardValue_graft]

/-- An experiment run in stages with retained memory: the first stage ends in a memory state,
and stage `k` continues from each state with its own dependent trace tree. -/
def stagedTree {State : Type} (initial : TraceTree State)
    (stage : ℕ → State → TraceTree State) : ℕ → TraceTree State
  | 0 => initial
  | n + 1 => graft (stagedTree initial stage n) (stage n)

/-- **NOTE2 Theorem 1, forward propagation.** The report law after `n` stages is the corpus
forward propagation of the first stage's law through the stage laws. -/
theorem reportLaw_stagedTree {State : Type} [Fintype State] (initial : TraceTree State)
    (stage : ℕ → State → TraceTree State) (n : ℕ) :
    reportLaw (stagedTree initial stage n) =
      ExactFiniteHistoryLaw.propagate (reportLaw initial)
        (fun step state ↦ reportLaw (stage step state)) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change reportLaw (graft (stagedTree initial stage n) (stage n)) = _
    rw [reportLaw_graft, ih]
    rfl

/-- **NOTE2 Theorem 1.** For an experiment run in stages, forward propagation, backward
evaluation, and complete-trace enumeration give the same expectation of every metric. -/
theorem propagate_expectation_eq_backwardReadout_eq_trace_sum {State : Type} [Fintype State]
    (initial : TraceTree State) (stage : ℕ → State → TraceTree State) (n : ℕ)
    (metric : State → ℝ) :
    (ExactFiniteHistoryLaw.propagate (reportLaw initial)
        (fun step state ↦ reportLaw (stage step state)) n).expectation metric =
        (reportLaw initial).expectation (ExactFiniteHistoryLaw.backwardReadout
          (fun step state ↦ reportLaw (stage step state)) n metric) ∧
      (ExactFiniteHistoryLaw.propagate (reportLaw initial)
        (fun step state ↦ reportLaw (stage step state)) n).expectation metric =
        ∑ trace, traceWeight (stagedTree initial stage n) trace *
          metric (traceReport (stagedTree initial stage n) trace) := by
  refine ⟨ExactFiniteHistoryLaw.expectation_propagate _ _ n metric, ?_⟩
  rw [← reportLaw_stagedTree, expectation_reportLaw, sum_traceWeight_mul_eq_backwardValue]

/-- One transition as a one-level experiment: branch on the next state and stop there. -/
def transitionTree {State : Type} [Fintype State] (law : FiniteReportLaw State) :
    TraceTree State :=
  .node State law fun state ↦ .leaf state

/-- A one-level experiment reports exactly its branch law. -/
theorem reportLaw_transitionTree {State : Type} [Fintype State] (law : FiniteReportLaw State) :
    reportLaw (transitionTree law) = law := by
  refine (FiniteReportLaw.eq_iff_singleton_expectations_eq _ _).mpr fun report ↦ ?_
  rw [expectation_reportLaw]
  rfl

/-- The corpus finite history with time-indexed kernels on one state type, as a staged trace
tree: the initial law, then one transition per step. -/
def historyTree {State : Type} [Fintype State] (initial : FiniteReportLaw State)
    (kernel : ℕ → State → FiniteReportLaw State) (n : ℕ) : TraceTree State :=
  stagedTree (transitionTree initial) (fun step state ↦ transitionTree (kernel step state)) n

/-- The history tree reports the corpus forward propagation `ExactFiniteHistoryLaw.propagate`. -/
theorem reportLaw_historyTree {State : Type} [Fintype State] (initial : FiniteReportLaw State)
    (kernel : ℕ → State → FiniteReportLaw State) (n : ℕ) :
    reportLaw (historyTree initial kernel n) =
      ExactFiniteHistoryLaw.propagate initial kernel n := by
  rw [historyTree, reportLaw_stagedTree]
  simp only [reportLaw_transitionTree]

/-- The complete-trace enumeration of the history tree is the corpus enumeration of complete
histories by `ExactFiniteHistoryLaw.pathMass`. -/
theorem trace_sum_historyTree_eq_path_sum {State : Type} [Fintype State]
    (initial : FiniteReportLaw State) (kernel : ℕ → State → FiniteReportLaw State) (n : ℕ)
    (metric : State → ℝ) :
    ∑ trace, traceWeight (historyTree initial kernel n) trace *
        metric (traceReport (historyTree initial kernel n) trace) =
      ∑ path : ExactFiniteHistoryLaw.Path State n,
        ExactFiniteHistoryLaw.pathMass initial kernel path *
          metric (ExactFiniteHistoryLaw.terminal path) := by
  rw [sum_traceWeight_mul_eq_backwardValue, ← expectation_reportLaw, reportLaw_historyTree,
    ExactFiniteHistoryLaw.path_sum_eq_expectation]

/-! ### The rational clause -/

/-- Every branch law of the experiment has rational cell masses. Assumes: the experiment
supplies its branch probabilities as exact rationals. -/
def RationalTree : TraceTree Report → Prop
  | .leaf _ => True
  | @TraceTree.node _ _ _ law child => RationalLaw law ∧ ∀ branch, RationalTree (child branch)

/-- **NOTE2 Theorem 1, rational clause.** Every trace weight of a rational experiment is
rational. Assumes: `RationalTree tree`. -/
theorem rationalValue_traceWeight (tree : TraceTree Report) (hrational : RationalTree tree)
    (trace : Trace tree) : RationalValue (traceWeight tree trace) := by
  induction tree with
  | leaf _ => exact rationalValue_one
  | node Branch law child ih =>
    exact rationalValue_mul (hrational.1 trace.1) (ih trace.1 (hrational.2 trace.1) trace.2)

/-- **NOTE2 Theorem 1, rational clause.** A rational experiment evaluates every rational metric
of its report at a rational number. Assumes: `RationalTree tree`. -/
theorem rationalValue_backwardValue (tree : TraceTree Report) (hrational : RationalTree tree)
    (metric : Report → ℝ) (hmetric : ∀ report, RationalValue (metric report)) :
    RationalValue (backwardValue tree metric) := by
  rw [← sum_traceWeight_mul_eq_backwardValue]
  exact rationalValue_sum _ fun trace ↦
    rationalValue_mul (rationalValue_traceWeight tree hrational trace) (hmetric _)

/-- **NOTE2 Theorem 1, rational clause.** The report law of a rational experiment is a rational
law, derived by the corpus closure of rational laws under point masses and `bind`. Assumes:
`RationalTree tree`. -/
theorem rationalLaw_reportLaw [Fintype Report] (tree : TraceTree Report)
    (hrational : RationalTree tree) : RationalLaw (reportLaw tree) := by
  induction tree with
  | leaf report => exact rationalLaw_pointMass report
  | node Branch law child ih =>
    exact rationalLaw_bind law hrational.1 (fun branch ↦ reportLaw (child branch))
      fun branch ↦ ih branch (hrational.2 branch)

/-- **NOTE2 Theorem 1, rational clause for conditional expectations.** With positive definedness
probability, the skip-undefined conditional mean of a rational partial metric under a rational
experiment is the named ratio, and that ratio is rational. Assumes: `RationalTree tree`. -/
theorem rationalValue_conditionalMetric_reportLaw [Fintype Report] (tree : TraceTree Report)
    (hrational : RationalTree tree) (metric : Report → Option ℝ)
    (hmetric : ∀ report, RationalValue ((metric report).getD 0))
    (hdefined : 0 < (reportLaw tree).definedMass metric) :
    (reportLaw tree).conditionalMetric metric =
        some ((reportLaw tree).weightedDefinedMetric metric /
          (reportLaw tree).definedMass metric) ∧
      RationalValue ((reportLaw tree).weightedDefinedMetric metric /
        (reportLaw tree).definedMass metric) :=
  rationalValue_conditionalMetric _ (rationalLaw_reportLaw tree hrational) metric hmetric
    hdefined.ne'

end TraceTree

/-! ### The finite rational algorithm -/

/-- The exact-arithmetic form of a trace tree: the same dependent branching, with every branch
law carried by rationals. -/
inductive RationalTraceTree (Report : Type) : Type 1
  | leaf (report : Report) : RationalTraceTree Report
  | node (Branch : Type) [Fintype Branch] (law : RationalReportLaw Branch)
      (child : Branch → RationalTraceTree Report) : RationalTraceTree Report

namespace RationalTraceTree

variable {Report : Type}

/-- Backward evaluation in rational arithmetic: the finite algorithm of NOTE2 Theorem 1. It runs
on rationals and never touches a real number. -/
def evaluate : RationalTraceTree Report → (Report → ℚ) → ℚ
  | .leaf report, metric => metric report
  | @RationalTraceTree.node _ _ _ law child, metric =>
      law.expectation fun branch ↦ evaluate (child branch) metric

/-- The real trace tree carried by a rational one. -/
def toReal : RationalTraceTree Report → TraceTree Report
  | .leaf report => .leaf report
  | @RationalTraceTree.node _ Branch _ law child =>
      .node Branch law.toReal fun branch ↦ toReal (child branch)

/-- A carried tree is rational, which inhabits `RationalTree` by every rational experiment. -/
theorem rationalTree_toReal (tree : RationalTraceTree Report) :
    TraceTree.RationalTree (toReal tree) := by
  induction tree with
  | leaf _ => trivial
  | node Branch law child ih => exact ⟨RationalReportLaw.rationalLaw_toReal law, ih⟩

/-- **NOTE2 Theorem 1, the algorithm.** Real backward evaluation of a carried tree at a carried
metric is the cast of the exact rational evaluation. -/
theorem backwardValue_toReal (tree : RationalTraceTree Report) (metric : Report → ℚ) :
    TraceTree.backwardValue (toReal tree) (fun report ↦ (metric report : ℝ)) =
      ((evaluate tree metric : ℚ) : ℝ) := by
  induction tree with
  | leaf _ => rfl
  | node Branch law child ih =>
    change law.toReal.expectation (fun branch ↦
        TraceTree.backwardValue (toReal (child branch)) fun report ↦ (metric report : ℝ)) =
      ((law.expectation fun branch ↦ evaluate (child branch) metric : ℚ) : ℝ)
    simp only [ih]
    exact RationalReportLaw.expectation_toReal law _

/-- The architecture draw of the concrete experiment: on with probability `1/3`. -/
def exampleArchitectureLaw : RationalReportLaw Bool where
  mass := fun architecture ↦ if architecture then 1 / 3 else 2 / 3
  mass_nonneg := fun architecture ↦ by cases architecture <;> norm_num
  mass_sum := by norm_num [Fintype.sum_bool]

/-- The three-way environment draw of the concrete experiment: absent with probability `1/2`,
and each of the two present states with probability `1/4`. -/
def exampleEnvironmentLaw : RationalReportLaw (Option Bool) where
  mass := fun environment ↦ if environment.isSome then 1 / 4 else 1 / 2
  mass_nonneg := fun environment ↦ by split_ifs <;> norm_num
  mass_sum := by norm_num [Fintype.sum_option, Fintype.sum_bool]

/-- A concrete dependent experiment: a binary architecture draw, and only when it is on, a
three-way environment draw. The branch type and the depth after the first draw depend on its
outcome. -/
def exampleTree : RationalTraceTree (Option Bool) :=
  .node Bool exampleArchitectureLaw fun architecture ↦
    if architecture then .node (Option Bool) exampleEnvironmentLaw fun environment ↦
      .leaf environment
    else .leaf none

/-- The algorithm running: the probability that the concrete experiment reports the present
state `some true`, computed by rational arithmetic alone, is `1/3 · 1/4 = 1/12`. -/
theorem exampleTree_evaluate :
    evaluate exampleTree (fun environment ↦ if environment = some true then 1 else 0) =
      1 / 12 := by
  norm_num [evaluate, exampleTree, exampleArchitectureLaw, exampleEnvironmentLaw,
    RationalReportLaw.expectation, Fintype.sum_bool, Fintype.sum_option]

/-- The real theory returns the same value on the carried experiment. -/
theorem exampleTree_backwardValue :
    TraceTree.backwardValue (toReal exampleTree)
        (fun environment ↦ if environment = some true then 1 else 0) = 1 / 12 := by
  have h := backwardValue_toReal exampleTree fun environment ↦
    if environment = some true then (1 : ℚ) else 0
  rw [exampleTree_evaluate] at h
  simpa using h

end RationalTraceTree

end

end Descent.Portability.FiniteTraceTreeLaw
