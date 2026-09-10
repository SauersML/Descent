/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.AncientPrediction.Risk
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

assert_below Descent.Decision Descent.Program

/-!
# Uniform moment-error certificates

The deterministic part of Theorem 8. Coordinatewise bounds imply a simultaneous
bound for every correction, including weights selected after seeing the moments.
The confidence radius is supplied by a separate sampling theorem; no correctness
of the ancient representation is assumed here.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.AncientPrediction

open scoped BigOperators

variable {I : Type*} [Fintype I]

/-- Coordinate form of the uncentered-moment risk difference. -/
def coordinateRisk (u : I → ℝ) (V : I → I → ℝ) (a : I → ℝ) : ℝ :=
  (∑ i, ∑ j, a i * V i j * a j) - 2 * ∑ i, u i * a i

/-- The confidence-inflated quadratic upper bound, equation (9.3). -/
def certifiedBound (u : I → ℝ) (V : I → I → ℝ) (εu εV : ℝ) (a : I → ℝ) : ℝ :=
  coordinateRisk u V a + (Fintype.card I : ℝ) * εV * (∑ i, a i ^ 2) +
    2 * εu * ∑ i, |a i|

lemma linear_moment_error (u uhat a : I → ℝ) (ε : ℝ)
    (h : ∀ i, |u i - uhat i| ≤ ε) :
    |(∑ i, u i * a i) - ∑ i, uhat i * a i| ≤ ε * ∑ i, |a i| := by
  rw [← Finset.sum_sub_distrib, Finset.mul_sum]
  calc
    _ ≤ ∑ i, |u i * a i - uhat i * a i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ _ := Finset.sum_le_sum fun i _ => by
      rw [← sub_mul, abs_mul]
      exact mul_le_mul_of_nonneg_right (h i) (abs_nonneg _)

lemma quadratic_moment_error (V Vhat : I → I → ℝ) (a : I → ℝ) (ε : ℝ)
    (hε : 0 ≤ ε) (h : ∀ i j, |V i j - Vhat i j| ≤ ε) :
    (∑ i, ∑ j, a i * V i j * a j) - (∑ i, ∑ j, a i * Vhat i j * a j) ≤
      (Fintype.card I : ℝ) * ε * ∑ i, a i ^ 2 := by
  have hentry (i j : I) :
      a i * V i j * a j - a i * Vhat i j * a j ≤ |a i| * ε * |a j| := by
    calc
      _ = a i * (V i j - Vhat i j) * a j := by ring
      _ ≤ |a i * (V i j - Vhat i j) * a j| := le_abs_self _
      _ = |a i| * |V i j - Vhat i j| * |a j| := by rw [abs_mul, abs_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (h i j) (abs_nonneg _)) (abs_nonneg _)
  have hcs : (∑ i, |a i|) ^ 2 ≤ (Fintype.card I : ℝ) * ∑ i, a i ^ 2 := by
    simpa using (Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun _ : I => (1 : ℝ))
      (fun i => |a i|))
  calc
    _ = ∑ i, ∑ j, (a i * V i j * a j - a i * Vhat i j * a j) := by
      simp only [Finset.sum_sub_distrib]
    _ ≤ ∑ i, ∑ j, |a i| * ε * |a j| :=
      Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hentry i j
    _ = ε * (∑ i, |a i|) ^ 2 := by
      simp only [← Finset.mul_sum, ← Finset.sum_mul]
      ring
    _ ≤ ε * ((Fintype.card I : ℝ) * ∑ i, a i ^ 2) := mul_le_mul_of_nonneg_left hcs hε
    _ = _ := by ring

/-- Uniform in all weights, so choosing the weights from the certification
sample does not require a second union bound over the parameter space. -/
theorem uniform_risk_bound (u uhat : I → ℝ) (V Vhat : I → I → ℝ)
    (εu εV : ℝ) (hV : 0 ≤ εV)
    (hu : ∀ i, |u i - uhat i| ≤ εu)
    (hv : ∀ i j, |V i j - Vhat i j| ≤ εV) :
    ∀ a, coordinateRisk u V a ≤ certifiedBound uhat Vhat εu εV a := by
  intro a
  have hl := (abs_le.mp (linear_moment_error u uhat a εu hu)).1
  have hq := quadratic_moment_error V Vhat a εV hV hv
  unfold certifiedBound coordinateRisk
  linarith

/-- A returned update with nonpositive bounds cannot worsen any represented
population on the joint moment-confidence event. -/
theorem simultaneous_no_worsening {G : Type*}
    (u uhat : G → I → ℝ) (V Vhat : G → I → I → ℝ)
    (εu εV : G → ℝ) (a : I → ℝ)
    (hV : ∀ g, 0 ≤ εV g)
    (hu : ∀ g i, |u g i - uhat g i| ≤ εu g)
    (hv : ∀ g i j, |V g i j - Vhat g i j| ≤ εV g)
    (hc : ∀ g, certifiedBound (uhat g) (Vhat g) (εu g) (εV g) a ≤ 0) :
    ∀ g, coordinateRisk (u g) (V g) a ≤ 0 := fun g =>
  (uniform_risk_bound (u g) (uhat g) (V g) (Vhat g) (εu g) (εV g)
    (hV g) (hu g) (hv g) a).trans (hc g)

/-- The unchanged prediction always satisfies the deterministic certificate. -/
@[simp] theorem certifiedBound_zero (u : I → ℝ) (V : I → I → ℝ) (εu εV : ℝ) :
    certifiedBound u V εu εV 0 = 0 := by simp [certifiedBound, coordinateRisk]

end Descent.Portability.AncientPrediction
