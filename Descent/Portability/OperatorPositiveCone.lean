/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Layer
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Convex.Function
import Mathlib.Tactic

assert_below Descent.Decision Descent.Program

/-!
The open operator cone used to separate the spectral audit epigraph.
Strict positivity means a uniform positive quadratic lower bound. It is
open in operator norm, convex, and stable under nonnegative quadratic
increments. Symmetry is not imposed on the ambient space: the cone ignores
skew components, allowing separation in the full normed operator space.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.OperatorPositiveCone

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The quadratic cone, including operators with arbitrary skew components. -/
def Nonnegative (A : E →L[ℝ] E) : Prop := ∀ x, 0 ≤ inner ℝ x (A x)

/-- The strict cone has a uniform positive lower bound in every direction. -/
def StrictPositive (A : E →L[ℝ] E) : Prop :=
  ∃ e : ℝ, 0 < e ∧ ∀ x, e * ‖x‖ ^ 2 ≤ inner ℝ x (A x)

/-- Operator norm controls every quadratic form without a symmetry assumption. -/
theorem quadratic_norm_bound (A : E →L[ℝ] E) (x : E) :
    |inner ℝ x (A x)| ≤ ‖A‖ * ‖x‖ ^ 2 := by
  have hi : |inner ℝ x (A x)| ≤ ‖x‖ * ‖A x‖ := by
    simpa only [Real.norm_eq_abs] using norm_inner_le_norm (𝕜 := ℝ) x (A x)
  have hm := mul_le_mul_of_nonneg_left (A.le_opNorm x) (norm_nonneg x)
  nlinarith

/-- Perturbing an operator changes its quadratic form by at most the operator norm error. -/
theorem quadratic_difference (A B : E →L[ℝ] E) (x : E) :
    inner ℝ x (A x) - inner ℝ x (B x) ≤ ‖A - B‖ * ‖x‖ ^ 2 := by
  have hh := (le_abs_self (inner ℝ x ((A - B) x))).trans
    (quadratic_norm_bound (A - B) x)
  simpa only [ContinuousLinearMap.sub_apply, inner_sub_right] using hh

/-- Uniform positive definiteness is an open condition in the full operator space. -/
theorem strictPositive_open : IsOpen {A : E →L[ℝ] E | StrictPositive A} := by
  apply Metric.isOpen_iff.mpr
  rintro A ⟨e, he, hA⟩
  refine ⟨e / 2, by positivity, ?_⟩
  intro B hB
  refine ⟨e / 2, by positivity, ?_⟩
  intro x
  have hd : ‖A - B‖ < e / 2 := by
    simpa only [Metric.mem_ball, dist_eq_norm, norm_sub_rev] using hB
  have hq := quadratic_difference A B x
  have hm := mul_le_mul_of_nonneg_right hd.le (sq_nonneg ‖x‖)
  nlinarith [hA x]

/-- The strict operator cone is convex, including zero mixture weights. -/
theorem strictPositive_convex : Convex ℝ {A : E →L[ℝ] E | StrictPositive A} := by
  rintro A ⟨e, he, hA⟩ B ⟨d, hd, hB⟩ a b ha hb hab
  refine ⟨a * e + b * d, ?_, ?_⟩
  · rcases eq_or_lt_of_le ha with hz | hp
    · have ha0 : a = 0 := hz.symm
      have hb1 : b = 1 := by linarith
      simpa [ha0, hb1] using hd
    · exact add_pos_of_pos_of_nonneg (mul_pos hp he) (mul_nonneg hb hd.le)
  · intro x
    have h₁ := mul_le_mul_of_nonneg_left (hA x) ha
    have h₂ := mul_le_mul_of_nonneg_left (hB x) hb
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      inner_add_right, inner_smul_right]
    nlinarith

/-- Adding a nonnegative quadratic form preserves strict positivity. -/
theorem strict_add_nonnegative (A B : E →L[ℝ] E)
    (hA : StrictPositive A) (hB : Nonnegative B) : StrictPositive (A + B) := by
  obtain ⟨e, he, hq⟩ := hA
  refine ⟨e, he, ?_⟩
  intro x
  simp only [ContinuousLinearMap.add_apply, inner_add_right]
  exact (hq x).trans (le_add_of_nonneg_right (hB x))

/-- Nonnegative scalar multiples remain in the nonnegative quadratic cone. -/
theorem nonnegative_smul (A : E →L[ℝ] E) (hA : Nonnegative A)
    (t : ℝ) (ht : 0 ≤ t) : Nonnegative (t • A) := by
  intro x
  simpa only [ContinuousLinearMap.smul_apply, inner_smul_right] using mul_nonneg ht (hA x)

/-- A positive scalar identity belongs to the open cone. -/
theorem strict_identity (e : ℝ) (he : 0 < e) :
    StrictPositive (e • ContinuousLinearMap.id ℝ E) := by
  refine ⟨e, he, ?_⟩
  intro x
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply,
    inner_smul_right, real_inner_self_eq_norm_sq, le_refl]

/-- The identity is a nonnegative quadratic direction. -/
theorem identity_nonnegative : Nonnegative (ContinuousLinearMap.id ℝ E) := by
  intro x
  simp only [ContinuousLinearMap.id_apply, real_inner_self_eq_norm_sq]
  exact sq_nonneg _

/-- A strict operator is also nonnegative. -/
theorem strict_nonnegative (A : E →L[ℝ] E) (hA : StrictPositive A) : Nonnegative A := by
  obtain ⟨e, he, hq⟩ := hA
  exact fun x ↦ (mul_nonneg he.le (sq_nonneg _)).trans (hq x)

end Descent.Portability.OperatorPositiveCone
