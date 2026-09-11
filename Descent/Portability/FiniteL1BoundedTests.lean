/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.FiniteIndependentMoments
import Mathlib.Topology.ContinuousMap.Bounded.Normed

assert_below Descent.Decision Descent.Program

/-!
Vanishing absolute first moments imply convergence against every bounded
continuous real test, even when the finite sample spaces vary with the row.
The proof supplies an explicit linear modulus bound from continuity at zero.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.FiniteL1BoundedTests

open scoped BigOperators Topology BoundedContinuousFunction
open Filter FiniteIndependentMoments

/-- Every bounded continuous test has an arbitrarily small intercept linear modulus at zero. -/
theorem linear_modulus (f : ℝ →ᵇ ℝ) (η : ℝ) (hη : 0 < η) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, |f x - f 0| ≤ η + C * |x| := by
  obtain ⟨δ, hδ, hf⟩ := Metric.continuousAt_iff.1 f.continuous.continuousAt η hη
  refine ⟨2 * ‖f‖ / δ, by positivity, fun x ↦ ?_⟩
  by_cases hx : |x| < δ
  · have hh : |f x - f 0| < η := by
      simpa only [Real.dist_eq] using hf (by simpa only [Real.dist_eq, sub_zero] using hx)
    exact hh.le.trans (le_add_of_nonneg_right (by positivity))
  · have hglobal : |f x - f 0| ≤ 2 * ‖f‖ := by
      have h := abs_sub (f x) (f 0)
      have hx := f.norm_coe_le_norm x
      have h0 := f.norm_coe_le_norm 0
      simp only [Real.norm_eq_abs] at hx h0
      exact h.trans (by linarith)
    have hmul := mul_le_mul_of_nonneg_left (le_of_not_gt hx)
      (show 0 ≤ 2 * ‖f‖ / δ by positivity)
    have he : 2 * ‖f‖ / δ * δ = 2 * ‖f‖ := div_mul_cancel₀ _ hδ.ne'
    rw [he] at hmul
    linarith

/-- Finite expectation inherits the linear modulus with the actual first moment. -/
theorem expectation_bound {α : Type*} [Fintype α] (p : FiniteReportLaw α)
    (z : α → ℝ) (f : ℝ →ᵇ ℝ) (η C : ℝ)
    (hf : ∀ x : ℝ, |f x - f 0| ≤ η + C * |x|) :
    |p.expectation (fun x ↦ f (z x)) - f 0| ≤
      η + C * p.expectation (fun x ↦ |z x|) := by
  have he : p.expectation (fun x ↦ f (z x)) - f 0 =
      ∑ x, p.mass x * (f (z x) - f 0) := by
    simp only [FiniteReportLaw.expectation, mul_sub, Finset.sum_sub_distrib,
      ← Finset.sum_mul, p.mass_sum, one_mul]
  rw [he]
  calc
    _ ≤ ∑ x, |p.mass x * (f (z x) - f 0)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ x, p.mass x * (η + C * |z x|) := by
      apply Finset.sum_le_sum
      intro x _
      rw [abs_mul, abs_of_nonneg (p.mass_nonneg x)]
      exact mul_le_mul_of_nonneg_left (hf (z x)) (p.mass_nonneg x)
    _ = p.expectation (fun _ ↦ η) + C * p.expectation (fun x ↦ |z x|) := by
      simp only [FiniteReportLaw.expectation, mul_add, Finset.sum_add_distrib, Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro x _
      ring
    _ = _ := by rw [expectation_const]

/-- A varying finite experiment with vanishing L1 magnitude converges to zero in law. -/
theorem test_limit {α : ℕ → Type*} [∀ m, Fintype (α m)]
    (p : (m : ℕ) → FiniteReportLaw (α m)) (z : (m : ℕ) → α m → ℝ)
    (hL1 : Tendsto (fun m ↦ (p m).expectation (fun x ↦ |z m x|)) atTop (𝓝 0))
    (f : ℝ →ᵇ ℝ) :
    Tendsto (fun m ↦ (p m).expectation (fun x ↦ f (z m x))) atTop (𝓝 (f 0)) := by
  apply Metric.tendsto_atTop.2
  intro ε hε
  obtain ⟨C, hC, hf⟩ := linear_modulus f (ε / 2) (by positivity)
  have hc : Tendsto (fun m ↦ C * (p m).expectation (fun x ↦ |z m x|)) atTop (𝓝 0) := by
    simpa using hL1.const_mul C
  obtain ⟨N, hN⟩ := eventually_atTop.1
    (hc.eventually (gt_mem_nhds (show (0 : ℝ) < ε / 2 by positivity)))
  refine ⟨N, fun m hm ↦ ?_⟩
  rw [Real.dist_eq]
  have hb := expectation_bound (p m) (z m) f (ε / 2) C hf
  linarith [hN m hm]

end Descent.Portability.FiniteL1BoundedTests
