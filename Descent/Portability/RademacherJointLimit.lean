/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.RademacherParityWeakLimit

assert_below Descent.Decision Descent.Program

/-!
Joint convergence of the product sign and weighted sum, expressed against every
pair of bounded continuous real test functions. The limiting product sign is
fair and independent of the Gaussian coordinate.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.RademacherJointLimit

open scoped BigOperators Topology NNReal BoundedContinuousFunction
open Filter MeasureTheory ProbabilityTheory HWEInteractionLaw BalancedHWEWeakLimit
open RademacherArrayWeakLimit RademacherParityLaw RademacherParityConditioning
open RademacherParityWeakLimit

/-- Exact decomposition of any statistic selected by the realized parity. -/
theorem parity_decomposition {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (f g : (ι → Bool) → ℝ) :
    (independentLaw (fun _ : ι ↦ signLaw)).expectation
      (fun x ↦ if parity x = 1 then f x else g x) =
        ((law true).expectation f + (law false).expectation g) / 2 := by
  classical
  simp only [FiniteReportLaw.expectation, law, ← Finset.sum_add_distrib, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro x _
  rcases sq_eq_one_iff.mp (parity_square x) with h | h <;>
    norm_num [h, signValue] <;> ring

/-- Both conditional classes converge against their own arbitrary bounded continuous tests. -/
theorem conditional_test_limit (a : (m : ℕ) → Fin m → ℝ) (ε : ℕ → ℝ)
    (ha : ∀ m i, |a m i| ≤ ε m) (hε : Tendsto ε atTop (𝓝 0)) (s : ℝ≥0)
    (hs : Tendsto (fun m ↦ ∑ i, a m i ^ 2) atTop (𝓝 (s : ℝ))) (b : Bool)
    (f : ℝ →ᵇ ℝ) :
    Tendsto (fun m ↦ (law b).expectation (fun x ↦ f (weightedSum (a (m + 1)) x))) atTop
      (𝓝 (∫ x, f x ∂gaussianReal 0 s)) := by
  have h := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp
    (conditional_gaussian_limit a ε ha hε s hs b) f
  change Tendsto (fun m ↦ ∫ x, f x ∂finiteMeasure (law b) (weightedSum (a (m + 1))))
    atTop (𝓝 (∫ x, f x ∂gaussianReal 0 s)) at h
  simpa only [integral_finiteMeasure] using h

/-- Full joint bounded-test limit: product sign and Gaussian coordinate become independent. -/
theorem joint_observable_limit (a : (m : ℕ) → Fin m → ℝ) (ε : ℕ → ℝ)
    (ha : ∀ m i, |a m i| ≤ ε m) (hε : Tendsto ε atTop (𝓝 0)) (s : ℝ≥0)
    (hs : Tendsto (fun m ↦ ∑ i, a m i ^ 2) atTop (𝓝 (s : ℝ))) (f : Bool → ℝ →ᵇ ℝ) :
    Tendsto (fun m ↦ (independentLaw (fun _ : Fin (m + 1) ↦ signLaw)).expectation
      (fun x ↦ if parity x = 1 then f true (weightedSum (a (m + 1)) x)
        else f false (weightedSum (a (m + 1)) x))) atTop
      (𝓝 (((∫ x, f true x ∂gaussianReal 0 s) + (∫ x, f false x ∂gaussianReal 0 s)) / 2)) := by
  have hp := conditional_test_limit a ε ha hε s hs true (f true)
  have hm := conditional_test_limit a ε ha hε s hs false (f false)
  simpa only [parity_decomposition] using (hp.add hm).div_const 2

end Descent.Portability.RademacherJointLimit
