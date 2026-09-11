/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Layer
import Mathlib.Analysis.SpecialFunctions.Sigmoid
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Tactic

assert_below Descent.Decision Descent.Program

/-!
# Quantitative error from mixing logits before applying the link

Theorem 7. The curvature constant is proved algebraically, and the two-state
bound follows by convexifying the response in both directions. State weights
are explicitly required to lie in the probability interval.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.ArchaicPrediction

lemma convexified_response (f f' f'' : ℝ → ℝ) (M : ℝ)
    (h₁ : ∀ x, HasDerivAt f (f' x) x) (h₂ : ∀ x, HasDerivAt f' (f'' x) x)
    (hb : ∀ x, -M ≤ f'' x) : ConvexOn ℝ Set.univ (fun x => f x + M / 2 * x ^ 2) := by
  have hp₁ (x : ℝ) : HasDerivAt (fun x => f x + M / 2 * x ^ 2) (f' x + M * x) x := by
    convert (h₁ x).add (((hasDerivAt_id x).pow 2).const_mul (M / 2)) using 1 <;>
      simp only [id_eq] <;> ring
  have hp₂ (x : ℝ) : HasDerivAt (fun x => f' x + M * x) (f'' x + M) x := by
    simpa using (h₂ x).add ((hasDerivAt_id x).const_mul M)
  apply convexOn_of_hasDerivWithinAt2_nonneg convex_univ
    (fun x _ => (hp₁ x).continuousAt.continuousWithinAt)
    (fun x _ => (hp₁ x).hasDerivWithinAt)
    (fun x _ => (hp₂ x).hasDerivWithinAt)
  intro x _
  linarith [hb x]

/-- A global curvature bound controls the two-state Jensen gap. -/
theorem two_state_curvature_bound (f f' f'' : ℝ → ℝ) (M : ℝ)
    (h₁ : ∀ x, HasDerivAt f (f' x) x) (h₂ : ∀ x, HasDerivAt f' (f'' x) x)
    (hb : ∀ x, |f'' x| ≤ M) (η γ q : ℝ) (hq : q ∈ Set.Icc (0 : ℝ) 1) :
    |(1 - q) * f η + q * f (η + γ) - f (η + q * γ)| ≤ M / 2 * γ ^ 2 * q * (1 - q) := by
  have hp := convexified_response f f' f'' M h₁ h₂ (fun x => (abs_le.mp (hb x)).1)
  have hn := convexified_response (fun x => -f x) (fun x => -f' x) (fun x => -f'' x)
    M (fun x => (h₁ x).neg) (fun x => (h₂ x).neg)
    (fun x => by linarith [(abs_le.mp (hb x)).2])
  have hpq := hp.2 (show η ∈ Set.univ by trivial) (show η + γ ∈ Set.univ by trivial)
    (sub_nonneg.mpr hq.2) hq.1 (show 1 - q + q = 1 by ring)
  have hnq := hn.2 (show η ∈ Set.univ by trivial) (show η + γ ∈ Set.univ by trivial)
    (sub_nonneg.mpr hq.2) hq.1 (show 1 - q + q = 1 by ring)
  have hm : (1 - q) * η + q * (η + γ) = η + q * γ := by ring
  simp only [smul_eq_mul, hm] at hpq hnq
  rw [abs_le]
  constructor <;> nlinarith

lemma sigmoid_second_derivative (x : ℝ) :
    HasDerivAt (fun x => Real.sigmoid x * (1 - Real.sigmoid x))
      (Real.sigmoid x * (1 - Real.sigmoid x) * (1 - 2 * Real.sigmoid x)) x := by
  convert (Real.hasDerivAt_sigmoid x).mul
    ((hasDerivAt_const x (1 : ℝ)).sub (Real.hasDerivAt_sigmoid x)) using 1 <;>
    simp only [Pi.sub_apply] <;> ring

/-- Sharp uniform magnitude of the sigmoid's second derivative. -/
theorem sigmoid_curvature_bound (x : ℝ) :
    |Real.sigmoid x * (1 - Real.sigmoid x) * (1 - 2 * Real.sigmoid x)| ≤
      1 / (6 * Real.sqrt 3) := by
  let s := Real.sigmoid x
  let t := 1 - 2 * s
  have hs₀ : 0 ≤ s := (Real.sigmoid_pos x).le
  have hs₁ : s ≤ 1 := (Real.sigmoid_lt_one x).le
  have ht : t ^ 2 ≤ 1 := by dsimp [t]; nlinarith [mul_nonneg hs₀ (sub_nonneg.mpr hs₁)]
  have hpoly := mul_nonneg (sq_nonneg (3 * t ^ 2 - 1)) (show 0 ≤ 4 - 3 * t ^ 2 by linarith)
  have hbound : 108 * (s * (1 - s) * (1 - 2 * s)) ^ 2 ≤ 1 := by
    dsimp [t] at hpoly
    nlinarith
  have hsqrt : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hpos : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  have hM : (1 / (6 * Real.sqrt 3)) ^ 2 = (1 : ℝ) / 108 := by
    field_simp
    nlinarith [hsqrt]
  have ha : |s * (1 - s) * (1 - 2 * s)| ^ 2 ≤ (1 / (6 * Real.sqrt 3)) ^ 2 := by
    rw [sq_abs, hM]
    linarith
  exact (sq_le_sq₀ (abs_nonneg _) (by positivity)).mp ha

/-- Theorem 7, including the exact `1 / (12 √3)` coefficient. -/
theorem two_state_logistic_bound (η γ q : ℝ) (hq : q ∈ Set.Icc (0 : ℝ) 1) :
    |(1 - q) * Real.sigmoid η + q * Real.sigmoid (η + γ) - Real.sigmoid (η + q * γ)| ≤
      γ ^ 2 * q * (1 - q) / (12 * Real.sqrt 3) := by
  have h := two_state_curvature_bound Real.sigmoid
    (fun x => Real.sigmoid x * (1 - Real.sigmoid x))
    (fun x => Real.sigmoid x * (1 - Real.sigmoid x) * (1 - 2 * Real.sigmoid x))
    (1 / (6 * Real.sqrt 3)) Real.hasDerivAt_sigmoid sigmoid_second_derivative
    sigmoid_curvature_bound η γ q hq
  convert h using 1 <;> ring

end Descent.Portability.ArchaicPrediction
