/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.UniversalMetricIdentification

assert_below Descent.Decision Descent.Program

namespace Descent.Portability

/-!
# Exact finite history to report law

An initial finite probability law and arbitrary time-dependent transition kernels determine
an exact terminal law. This module constructs that law, proves its normalization, and proves
that three evaluation methods agree exactly: forward propagation, backward metric evaluation,
and summing the probability of every complete finite history.

The transitions are supplied inputs. They can encode reproduction, migration, mutation,
phenotype generation, training, and reporting whenever the chosen finite state describes the
process. No independence across successive states is imposed beyond the supplied conditional
transition law. A process with memory can include its relevant history in its state.

This is an exact constructive composition theorem, not a derivation of transition kernels
from every biological demographic history, and not an assertion that continuous variables
are already represented exactly by a finite state space. The final report can include a
distinguished undefined outcome without assigning it a numeric metric value.
-/

namespace FiniteReportLaw

variable {State Next Report : Type*} [Fintype State] [Fintype Next] [Fintype Report]

/-- Exact marginalization of a conditional finite transition law. -/
noncomputable def bind (p : FiniteReportLaw State)
    (kernel : State → FiniteReportLaw Next) : FiniteReportLaw Next where
  mass := fun next ↦ ∑ state, p.mass state * (kernel state).mass next
  mass_nonneg := by
    intro next
    exact Finset.sum_nonneg (fun state _ ↦
      mul_nonneg (p.mass_nonneg state) ((kernel state).mass_nonneg next))
  mass_sum := by
    rw [Finset.sum_comm]
    simp only [← Finset.mul_sum, mass_sum, mul_one]

/-- Exact finite law of total expectation. The inner expectation remains inside the outer
one, so nonlinear realized metrics are integrated after they are evaluated. -/
theorem expectation_bind (p : FiniteReportLaw State)
    (kernel : State → FiniteReportLaw Next) (metric : Next → ℝ) :
    (p.bind kernel).expectation metric =
      p.expectation (fun state ↦ (kernel state).expectation metric) := by
  simp only [expectation, bind, Finset.sum_mul, Finset.mul_sum, mul_assoc]
  rw [Finset.sum_comm]

theorem expectation_pointMass (state : State) (metric : State → ℝ) :
    (pointMass state).expectation metric = metric state := by
  classical
  simp [expectation, pointMass]

/-- The exact distribution of a deterministic report computed from a random state. -/
noncomputable def pushforward (p : FiniteReportLaw State) (report : State → Report) :
    FiniteReportLaw Report :=
  p.bind (fun state ↦ pointMass (report state))

theorem expectation_pushforward (p : FiniteReportLaw State) (report : State → Report)
    (metric : Report → ℝ) :
    (p.pushforward report).expectation metric =
      p.expectation (fun state ↦ metric (report state)) := by
  rw [pushforward, expectation_bind]
  simp only [expectation_pointMass]

/-- Joint source state and conditional next state, retaining their dependence. -/
noncomputable def joint (p : FiniteReportLaw State)
    (kernel : State → FiniteReportLaw Next) : FiniteReportLaw (State × Next) :=
  p.bind (fun state ↦ (kernel state).pushforward (fun next ↦ (state, next)))

theorem expectation_joint (p : FiniteReportLaw State)
    (kernel : State → FiniteReportLaw Next) (metric : State × Next → ℝ) :
    (p.joint kernel).expectation metric =
      p.expectation (fun state ↦
        (kernel state).expectation (fun next ↦ metric (state, next))) := by
  rw [joint, expectation_bind]
  simp only [expectation_pushforward]

end FiniteReportLaw

namespace ExactFiniteHistoryLaw

universe u

variable {State Report : Type*} [Fintype State] [Fintype Report]

/-- Exact forward propagation through the first `n` time-dependent transitions. -/
noncomputable def propagate (initial : FiniteReportLaw State)
    (kernel : ℕ → State → FiniteReportLaw State) : ℕ → FiniteReportLaw State
  | 0 => initial
  | n + 1 => (propagate initial kernel n).bind (kernel n)

/-- Backward evaluation applies the final transition to the requested metric, then evaluates
the resulting state function through all earlier transitions. -/
noncomputable def backwardReadout (kernel : ℕ → State → FiniteReportLaw State) :
    ℕ → (State → ℝ) → State → ℝ
  | 0, metric => metric
  | n + 1, metric => backwardReadout kernel n
      (fun state ↦ (kernel n state).expectation metric)

/-- Forward propagation and backward evaluation give exactly the same metric expectation
for every finite history length and every real-valued terminal metric. -/
theorem expectation_propagate (initial : FiniteReportLaw State)
    (kernel : ℕ → State → FiniteReportLaw State) (n : ℕ) (metric : State → ℝ) :
    (propagate initial kernel n).expectation metric =
      initial.expectation (backwardReadout kernel n metric) := by
  induction n generalizing metric with
  | zero => rfl
  | succ n ih =>
    rw [propagate, FiniteReportLaw.expectation_bind, backwardReadout]
    exact ih _

/-- The exact final report law after all state transitions and deterministic reporting. -/
noncomputable def reportLaw (initial : FiniteReportLaw State)
    (kernel : ℕ → State → FiniteReportLaw State) (n : ℕ) (report : State → Report) :
    FiniteReportLaw Report :=
  (propagate initial kernel n).pushforward report

/-- Exact end-to-end expectation, preserving the order: generate state, compute report,
evaluate metric, then marginalize. -/
theorem expectation_reportLaw (initial : FiniteReportLaw State)
    (kernel : ℕ → State → FiniteReportLaw State) (n : ℕ) (report : State → Report)
    (metric : Report → ℝ) :
    (reportLaw initial kernel n report).expectation metric =
      initial.expectation
        (backwardReadout kernel n (fun state ↦ metric (report state))) := by
  rw [reportLaw, FiniteReportLaw.expectation_pushforward, expectation_propagate]

/-- A complete history contains the initial state and one new state for each transition.
Nested products expose the last transition without a choice of index encodings. -/
def Path (State : Type u) : ℕ → Type u
  | 0 => State
  | n + 1 => Path State n × State

instance pathFintype : (n : ℕ) → Fintype (Path State n)
  | 0 => inferInstanceAs (Fintype State)
  | n + 1 => by
      letI : Fintype (Path State n) := pathFintype n
      exact inferInstanceAs (Fintype (Path State n × State))

/-- The terminal state of a complete history. -/
def terminal : {n : ℕ} → Path State n → State
  | 0, state => state
  | _n + 1, path => path.2

/-- The probability of a complete history is the initial mass multiplied by its ordered
conditional transition probabilities. -/
noncomputable def pathMass (initial : FiniteReportLaw State)
    (kernel : ℕ → State → FiniteReportLaw State) : {n : ℕ} → Path State n → ℝ
  | 0, state => initial.mass state
  | n + 1, path =>
      pathMass initial kernel (n := n) path.1 *
        (kernel n (terminal (n := n) path.1)).mass path.2

/-- An explicit sum over every complete history agrees with forward propagation. This
identity includes zero-probability paths and arbitrary time-inhomogeneous kernels exactly. -/
theorem path_sum_eq_expectation (initial : FiniteReportLaw State)
    (kernel : ℕ → State → FiniteReportLaw State) (n : ℕ) (metric : State → ℝ) :
    (∑ path : Path State n, pathMass initial kernel path * metric (terminal path)) =
      (propagate initial kernel n).expectation metric := by
  induction n generalizing metric with
  | zero => rfl
  | succ n ih =>
    change (∑ path : Path State n × State,
        (pathMass initial kernel path.1 * (kernel n (terminal path.1)).mass path.2) *
          metric path.2) = _
    rw [Fintype.sum_prod_type]
    simp only [mul_assoc, ← Finset.mul_sum]
    rw [propagate, FiniteReportLaw.expectation_bind]
    exact ih (fun state ↦ (kernel n state).expectation metric)

/-- The complete path weights normalize to one, derived from the constructed transition
law rather than imposed as a separate hypothesis on histories. -/
theorem path_mass_sum_one (initial : FiniteReportLaw State)
    (kernel : ℕ → State → FiniteReportLaw State) (n : ℕ) :
    (∑ path : Path State n, pathMass initial kernel path) = 1 := by
  have h := path_sum_eq_expectation initial kernel n (fun _ ↦ 1)
  simpa only [mul_one, FiniteReportLaw.expectation, FiniteReportLaw.mass_sum] using h

omit [Fintype Report] in
/-- Every bounded report metric, as well as every finite real-valued report metric, has
the exact same output under path enumeration and backward evaluation. -/
theorem report_path_sum_eq_backward (initial : FiniteReportLaw State)
    (kernel : ℕ → State → FiniteReportLaw State) (n : ℕ)
    (report : State → Report) (metric : Report → ℝ) :
    (∑ path : Path State n,
      pathMass initial kernel path * metric (report (terminal path))) =
        initial.expectation
          (backwardReadout kernel n (fun state ↦ metric (report state))) := by
  exact (path_sum_eq_expectation initial kernel n
    (fun state ↦ metric (report state))).trans
      (expectation_propagate initial kernel n (fun state ↦ metric (report state)))

end ExactFiniteHistoryLaw

end Descent.Portability
