/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.ExactFiniteHistoryLaw

assert_below Descent.Decision Descent.Program

/-!
Backward residual and model perturbation certificates for specified finite
histories. Bounds on readouts may be restricted to positive-mass states.
These are analytic error certificates, not floating-point validation claims.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.FiniteNumericalCertificate

open FiniteReportLaw ExactFiniteHistoryLaw

variable {S T : Type*} [Fintype S] [Fintype T]

theorem expectation_difference (law : FiniteReportLaw S) (f g : S → ℝ) :
    law.expectation (fun state ↦ f state - g state) =
      law.expectation f - law.expectation g := by
  simp only [expectation, mul_sub, Finset.sum_sub_distrib]

theorem abs_expectation_le (law : FiniteReportLaw S) (f : S → ℝ) (bound : ℝ)
    (hbound : ∀ state, 0 < law.mass state → |f state| ≤ bound) :
    |law.expectation f| ≤ bound := by
  calc
    |law.expectation f| ≤ ∑ state, |law.mass state * f state| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ state, law.mass state * bound := by
      apply Finset.sum_le_sum
      intro state _
      rw [abs_mul, abs_of_nonneg (law.mass_nonneg state)]
      by_cases hp : 0 < law.mass state
      · exact mul_le_mul_of_nonneg_left (hbound state hp) (law.mass_nonneg state)
      · have hz : law.mass state = 0 := le_antisymm (le_of_not_gt hp) (law.mass_nonneg state)
        simp [hz]
    _ = bound := by rw [← Finset.sum_mul, law.mass_sum, one_mul]

theorem expectation_bounded (law : FiniteReportLaw S) (metric : S → ℝ)
    (hmetric : BoundedMetric metric) : 0 ≤ law.expectation metric ∧ law.expectation metric ≤ 1 := by
  constructor
  · exact Finset.sum_nonneg (fun state _ ↦ mul_nonneg (law.mass_nonneg state) (hmetric state).1)
  · calc
      law.expectation metric ≤ ∑ state, law.mass state * 1 := by
        exact Finset.sum_le_sum (fun state _ ↦
          mul_le_mul_of_nonneg_left (hmetric state).2 (law.mass_nonneg state))
      _ = 1 := by simp [law.mass_sum]

noncomputable def residual (kernel : ℕ → S → FiniteReportLaw S)
    (approximation : ℕ → S → ℝ) (time : ℕ) (state : S) : ℝ :=
  approximation time state - (kernel time state).expectation (approximation (time + 1))

/-- Exact signed error, including the terminal approximation error. -/
theorem backward_residual_identity (initial : FiniteReportLaw S)
    (kernel : ℕ → S → FiniteReportLaw S) (approximation : ℕ → S → ℝ)
    (terminal : S → ℝ) (horizon : ℕ) :
    initial.expectation (approximation 0) -
        (propagate initial kernel horizon).expectation terminal =
      (∑ time ∈ Finset.range horizon,
        (propagate initial kernel time).expectation (residual kernel approximation time)) +
      (propagate initial kernel horizon).expectation
        (fun state ↦ approximation horizon state - terminal state) := by
  have ht : ∀ time,
      (propagate initial kernel time).expectation (residual kernel approximation time) =
        (propagate initial kernel time).expectation (approximation time) -
          (propagate initial kernel (time + 1)).expectation (approximation (time + 1)) := by
    intro time
    rw [propagate, expectation_bind]
    exact expectation_difference _ _ _
  simp_rw [ht]
  rw [expectation_difference]
  have hsum : ∑ time ∈ Finset.range horizon,
      ((propagate initial kernel time).expectation (approximation time) -
        (propagate initial kernel (time + 1)).expectation (approximation (time + 1))) =
      initial.expectation (approximation 0) -
        (propagate initial kernel horizon).expectation (approximation horizon) := by
    induction horizon with
    | zero => simp [propagate]
    | succ horizon ih => rw [Finset.sum_range_succ, ih]; ring
  rw [hsum]
  ring

/-- A residual certificate only needs bounds on states with positive probability. -/
theorem backward_residual_bound (initial : FiniteReportLaw S)
    (kernel : ℕ → S → FiniteReportLaw S) (approximation : ℕ → S → ℝ)
    (terminal : S → ℝ) (horizon : ℕ) (errors : ℕ → ℝ) (terminalError : ℝ)
    (herrors : ∀ time < horizon, ∀ state, 0 < (propagate initial kernel time).mass state →
      |residual kernel approximation time state| ≤ errors time)
    (hterminal : ∀ state, 0 < (propagate initial kernel horizon).mass state →
      |approximation horizon state - terminal state| ≤ terminalError) :
    |initial.expectation (approximation 0) -
      (propagate initial kernel horizon).expectation terminal| ≤
        (∑ time ∈ Finset.range horizon, errors time) + terminalError := by
  rw [backward_residual_identity]
  refine (abs_add_le _ _).trans (add_le_add ?_ (abs_expectation_le _ _ _ hterminal))
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum ?_)
  intro time ht
  exact abs_expectation_le _ _ _ (herrors time (Finset.mem_range.mp ht))

theorem totalVariation_symm (p q : FiniteReportLaw S) :
    p.totalVariation q = q.totalVariation p := by
  simp only [totalVariation_eq_half_sum_abs, abs_sub_comm]

theorem totalVariation_triangle (p q r : FiniteReportLaw S) :
    p.totalVariation r ≤ p.totalVariation q + q.totalVariation r := by
  have h1 := expectation_sub_le_totalVariation p q (separatingMetric p r)
    (separatingMetric_bounded p r)
  have h2 := expectation_sub_le_totalVariation q r (separatingMetric p r)
    (separatingMetric_bounded p r)
  have he := separatingMetric_attains p r
  linarith

theorem totalVariation_bind (p q : FiniteReportLaw S) (kernel : S → FiniteReportLaw T) :
    (p.bind kernel).totalVariation (q.bind kernel) ≤ p.totalVariation q := by
  apply (all_bounded_metric_errors_le_iff _ _ _).mp
  intro metric hm
  rw [expectation_bind, expectation_bind]
  exact abs_expectation_sub_le_totalVariation p q _
    (fun state ↦ expectation_bounded (kernel state) metric hm)

theorem totalVariation_kernel_change (p : FiniteReportLaw S)
    (first second : S → FiniteReportLaw T) (error : ℝ)
    (herror : ∀ state, 0 < p.mass state → (first state).totalVariation (second state) ≤ error) :
    (p.bind first).totalVariation (p.bind second) ≤ error := by
  apply (all_bounded_metric_errors_le_iff _ _ _).mp
  intro metric hm
  rw [expectation_bind, expectation_bind, ← expectation_difference]
  apply abs_expectation_le
  intro state hp
  exact (abs_expectation_sub_le_totalVariation _ _ metric hm).trans (herror state hp)

/-- Model errors accumulate additively, with the trivial probability cap retained. -/
theorem propagation_perturbation (first second : FiniteReportLaw S)
    (firstKernel secondKernel : ℕ → S → FiniteReportLaw S)
    (initialError : ℝ) (errors : ℕ → ℝ) (horizon : ℕ)
    (hinitial : first.totalVariation second ≤ initialError)
    (herrors : ∀ time < horizon, ∀ state,
      0 < (propagate second secondKernel time).mass state →
      (firstKernel time state).totalVariation (secondKernel time state) ≤ errors time) :
    (propagate first firstKernel horizon).totalVariation
      (propagate second secondKernel horizon) ≤
        min 1 (initialError + ∑ time ∈ Finset.range horizon, errors time) := by
  apply le_min (totalVariation_le_one _ _)
  induction horizon with
  | zero => simpa [propagate] using hinitial
  | succ horizon ih =>
      have hi := ih (fun time ht ↦ herrors time (Nat.lt.step ht))
      rw [propagate, propagate, Finset.sum_range_succ]
      have hh := totalVariation_triangle
        ((propagate first firstKernel horizon).bind (firstKernel horizon))
        ((propagate second secondKernel horizon).bind (firstKernel horizon))
        ((propagate second secondKernel horizon).bind (secondKernel horizon))
      have h1 := totalVariation_bind (propagate first firstKernel horizon)
        (propagate second secondKernel horizon) (firstKernel horizon)
      have h2 := totalVariation_kernel_change (propagate second secondKernel horizon)
        (firstKernel horizon) (secondKernel horizon) (errors horizon)
        (herrors horizon (Nat.lt_succ_self horizon))
      linarith

end Descent.Portability.FiniteNumericalCertificate
