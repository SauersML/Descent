/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.BanachEulerExponential
import Descent.Portability.IndependentShiftOperator
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Analysis.SpecialFunctions.MulExpNegMulSqIntegral
import Mathlib.Topology.MetricSpace.Equicontinuity

assert_below Descent.Decision Descent.Program

/-!
Convergent probability test functions form a closed set in the uniform norm.
The uniform closure of a tested algebra also contains bounded Gaussian damping
of its elements, proved by the actual Banach Euler approximants.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.ProbabilityTestClosure

open scoped Topology BoundedContinuousFunction
open Filter MeasureTheory IndependentShiftOperator

/-- Probability integration is a contraction for bounded continuous real tests. -/
theorem integral_dist_le (μ : ProbabilityMeasure ℝ) (f g : Observable) :
    dist (∫ x, f x ∂(μ : Measure ℝ)) (∫ x, g x ∂(μ : Measure ℝ)) ≤ dist f g := by
  rw [dist_eq_norm, dist_eq_norm]
  have h := (f - g).norm_integral_le_norm (μ := (μ : Measure ℝ))
  simpa only [BoundedContinuousFunction.sub_apply,
    integral_sub (f.integrable _) (g.integrable _)] using h

/-- The family of all probability integration functionals is uniformly equicontinuous. -/
theorem integral_uniformEquicontinuous (μ : ℕ → ProbabilityMeasure ℝ) :
    UniformEquicontinuous (fun n (f : Observable) ↦ ∫ x, f x ∂(μ n : Measure ℝ)) := by
  apply Metric.uniformEquicontinuous_iff.mpr
  intro ε hε
  refine ⟨ε, hε, fun f g hfg n ↦ (integral_dist_le (μ n) f g).trans_lt hfg⟩

/-- A uniform limit of tests whose expectations converge is also a convergent test. -/
theorem convergent_tests_isClosed (μ : ℕ → ProbabilityMeasure ℝ) (ν : ProbabilityMeasure ℝ) :
    IsClosed {f : Observable | Tendsto (fun n ↦ ∫ x, f x ∂(μ n : Measure ℝ))
      atTop (nhds (∫ x, f x ∂(ν : Measure ℝ)))} := by
  apply (integral_uniformEquicontinuous μ).equicontinuous.isClosed_setOf_tendsto
  apply LipschitzWith.continuous (K := 1)
  apply LipschitzWith.of_dist_le_mul
  intro f g
  simpa only [NNReal.coe_one, one_mul] using integral_dist_le ν f g

/-- Convergence on an algebra extends to its full uniform closure. -/
theorem integral_tendsto_of_mem_closure (μ : ℕ → ProbabilityMeasure ℝ)
    (ν : ProbabilityMeasure ℝ) (A : Subalgebra ℝ Observable)
    (hA : ∀ f ∈ A, Tendsto (fun n ↦ ∫ x, f x ∂(μ n : Measure ℝ))
      atTop (nhds (∫ x, f x ∂(ν : Measure ℝ))))
    {f : Observable} (hf : f ∈ A.topologicalClosure) :
    Tendsto (fun n ↦ ∫ x, f x ∂(μ n : Measure ℝ))
      atTop (nhds (∫ x, f x ∂(ν : Measure ℝ))) := by
  exact (closure_minimal hA (convergent_tests_isClosed μ ν)) hf

/-- Bounded Gaussian damping, realized as an element of the bounded function algebra. -/
noncomputable def damp (ε : ℝ) (f : Observable) : Observable :=
  f * NormedSpace.exp ℝ (-(ε • f * f))

private def evalRing (x : ℝ) : Observable →+* ℝ where
  toFun f := f x
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

@[simp] theorem damp_apply (ε : ℝ) (f : Observable) (x : ℝ) :
    damp ε f x = Real.mulExpNegMulSq ε (f x) := by
  have h := NormedSpace.map_exp ℝ (evalRing x)
    (BoundedContinuousFunction.evalCLM ℝ x).continuous (-(ε • f * f))
  change f x * (evalRing x (NormedSpace.exp ℝ (-(ε • f * f)))) = _
  rw [h]
  simp only [evalRing, BoundedContinuousFunction.neg_apply,
    BoundedContinuousFunction.mul_apply, BoundedContinuousFunction.smul_apply,
    smul_eq_mul, ← Real.exp_eq_exp_ℝ, Real.mulExpNegMulSq]

/-- Damping belongs to the uniform closure because every Euler approximant belongs to the algebra. -/
theorem damp_mem_closure (A : Subalgebra ℝ Observable) (ε : ℝ) {f : Observable}
    (hf : f ∈ A) : damp ε f ∈ A.topologicalClosure := by
  apply A.isClosed_topologicalClosure.mem_of_tendsto
    ((BanachEulerExponential.euler_tends_exp (-(ε • f * f))).const_mul f)
  filter_upwards with n
  apply A.subset_topologicalClosure
  exact A.mul_mem hf (A.pow_mem (A.add_mem A.one_mem
    (A.smul_mem (A.neg_mem (A.mul_mem (A.smul_mem hf ε) hf)) (n : ℝ)⁻¹)) n)

/-- Every damped algebra test has convergent actual probability expectations. -/
theorem damped_integral_tendsto (μ : ℕ → ProbabilityMeasure ℝ) (ν : ProbabilityMeasure ℝ)
    (A : Subalgebra ℝ Observable)
    (hA : ∀ f ∈ A, Tendsto (fun n ↦ ∫ x, f x ∂(μ n : Measure ℝ))
      atTop (nhds (∫ x, f x ∂(ν : Measure ℝ))))
    (ε : ℝ) {f : Observable} (hf : f ∈ A) :
    Tendsto (fun n ↦ ∫ x, Real.mulExpNegMulSq ε (f x) ∂(μ n : Measure ℝ))
      atTop (nhds (∫ x, Real.mulExpNegMulSq ε (f x) ∂(ν : Measure ℝ))) := by
  simpa only [damp_apply] using
    integral_tendsto_of_mem_closure μ ν A hA (damp_mem_closure A ε hf)

end Descent.Portability.ProbabilityTestClosure
