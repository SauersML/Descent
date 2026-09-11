/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.ObservableClosureLaw
import Descent.Portability.ExactMetricEvaluation

assert_below Descent.Decision Descent.Program

/-!
# Close finite evolution, stochastic scoring, and reported metrics

The state kernel specifies evolution and context; the reporting kernel specifies
conditional training, score construction, and evaluation. A report may contain a
whole cohort and its realized R², rather than averaging individuals across training
draws before computing R². Undefined reports remain explicit. Backward propagation
computes the exact report expectation from the primitives, and a concrete feature
invariance criterion characterizes when its three sufficient summaries evolve
autonomously. No trait-specific attenuation parameter is inserted between layers.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.EvolutionaryMetricClosure

open FiniteReportLaw ExactFiniteHistoryLaw ObservableClosureLaw
open scoped Matrix

noncomputable section

variable {S R : Type*} [Fintype S] [Fintype R]

/-- Features already integrate the stochastic training/evaluation law conditional
on each evolutionary state. Keeping definedness is essential for partial metrics. -/
def metricFeatures (report : S → FiniteReportLaw R) (metric : R → Option ℝ) :
    Matrix S (Fin 3) ℝ :=
  fun state ↦ ![1, (report state).definedMass metric, (report state).weightedDefinedMetric metric]

def transitionMatrix (evolve : S → FiniteReportLaw S) : Matrix S S ℝ :=
  fun state next ↦ (evolve state).mass next

/-- Exact expected reported metric, composing evolution and the reporting law.
The two propagated observables are explicitly determined by those primitives. -/
theorem metric_from_evolution_and_scoring (initial : FiniteReportLaw S)
    (evolve : ℕ → S → FiniteReportLaw S) (report : S → FiniteReportLaw R)
    (metric : R → Option ℝ) (n : ℕ) :
    ((propagate initial evolve n).bind report).conditionalMetric metric =
      let defined := initial.expectation (backwardReadout evolve n
        (fun state ↦ (report state).definedMass metric))
      if defined = 0 then none else some
        (initial.expectation (backwardReadout evolve n
          (fun state ↦ (report state).weightedDefinedMetric metric)) / defined) := by
  unfold conditionalMetric definedMass weightedDefinedMetric
  rw [expectation_bind, expectation_bind, expectation_propagate, expectation_propagate]

variable [DecidableEq S] [Nonempty S]

omit [Fintype S] [DecidableEq S] [Nonempty S] in
/-- A constant is retained by the actual metric feature matrix. -/
theorem metricFeatures_retain_mass (report : S → FiniteReportLaw R)
    (metric : R → Option ℝ) :
    metricFeatures report metric *ᵥ (![1, 0, 0] : Fin 3 → ℝ) = fun _ ↦ 1 := by
  ext state
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, metricFeatures,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]

/-- Necessary and sufficient closure for the features of this scoring pipeline,
even if the proposed autonomous update was allowed to be nonlinear. -/
theorem scoring_features_close_iff (evolve : S → FiniteReportLaw S)
    (report : S → FiniteReportLaw R) (metric : R → Option ℝ) :
    AutonomousOnLaws (metricFeatures report metric).transpose.toLin'
      ((transitionMatrix evolve * metricFeatures report metric).transpose.toLin') ↔
      ∃ B : Matrix (Fin 3) (Fin 3) ℝ,
        transitionMatrix evolve * metricFeatures report metric = metricFeatures report metric * B :=
  matrix_autonomy_iff _ _ ⟨![1, 0, 0], metricFeatures_retain_mass report metric⟩

/-- Failure of closure gives two actual probability laws with the same retained
metric summaries and different next-step summaries, not two draws from one law. -/
theorem failure_of_closure_witness (evolve : S → FiniteReportLaw S)
    (report : S → FiniteReportLaw R) (metric : R → Option ℝ)
    (hnot : ¬ ∃ B : Matrix (Fin 3) (Fin 3) ℝ,
      transitionMatrix evolve * metricFeatures report metric = metricFeatures report metric * B) :
    ∃ p q : FiniteReportLaw S,
      (metricFeatures report metric).transpose.toLin' p.mass =
        (metricFeatures report metric).transpose.toLin' q.mass ∧
      ((transitionMatrix evolve * metricFeatures report metric).transpose.toLin') p.mass ≠
        ((transitionMatrix evolve * metricFeatures report metric).transpose.toLin') q.mass := by
  have hn := mt (scoring_features_close_iff evolve report metric).mp hnot
  unfold AutonomousOnLaws at hn
  push_neg at hn
  exact hn

omit [Nonempty S] in
/-- When closure holds it propagates for every generation, with no additional
unexplained parameter or moment closure approximation. -/
theorem closed_features_all_generations (evolve : S → FiniteReportLaw S)
    (report : S → FiniteReportLaw R) (metric : R → Option ℝ)
    (B : Matrix (Fin 3) (Fin 3) ℝ)
    (hclose : transitionMatrix evolve * metricFeatures report metric =
      metricFeatures report metric * B) (n : ℕ) :
    transitionMatrix evolve ^ n * metricFeatures report metric =
      metricFeatures report metric * B ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, Matrix.mul_assoc, hclose, ← Matrix.mul_assoc, ih,
      Matrix.mul_assoc, ← pow_succ]

end

end Descent.Portability.EvolutionaryMetricClosure
