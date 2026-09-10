/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.Deriv.Pow
import Descent.Layer

assert_below Descent.Decision Descent.Program

/-!
Analytic rigidity on a genuine open interval: vanishing second derivative makes
a C² field affine, and vanishing third derivative makes a C³ potential quadratic.
These derived interpolation facts are the analytic input to diploid field
compatibility, rather than an assumed polynomial representation.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.QuadraticRigidityLaw

open Set

/-- The affine representation is derived from the stated differential condition. -/
theorem affine_of_second_derivative_zero (f : ℝ → ℝ) {a b c : ℝ}
    (hc : c ∈ Ioo a b) (hf : ContDiffOn ℝ 2 f (Ioo a b))
    (hzero : ∀ x ∈ Ioo a b, deriv (deriv f) x = 0) :
    ∀ x ∈ Ioo a b, f x = f c + deriv f c * (x - c) := by
  have hd : ContDiffOn ℝ 1 (deriv f) (Ioo a b) :=
    hf.deriv_of_isOpen isOpen_Ioo (by norm_num)
  have hconst : ∀ x ∈ Ioo a b, deriv f x = deriv f c := by
    intro x hx
    exact isOpen_Ioo.is_const_of_deriv_eq_zero isPreconnected_Ioo
      hd.differentiableOn_one hzero hx hc
  have hg (x : ℝ) : HasDerivAt (fun t ↦ f c + deriv f c * (t - c)) (deriv f c) x := by
    convert (((hasDerivAt_id x).sub_const c).const_mul (deriv f c)).const_add (f c) using 1
    ring
  apply isOpen_Ioo.eqOn_of_deriv_eq isPreconnected_Ioo
    (hf.differentiableOn (by norm_num))
    (fun x _ ↦ (hg x).differentiableAt.differentiableWithinAt) _ hc (by simp)
  intro x hx
  rw [(hg x).deriv, hconst x hx]

/-- A C³ potential whose third derivative vanishes is exactly quadratic,
including its uniquely determined value and first two derivatives at the anchor. -/
theorem quadratic_of_third_derivative_zero (f : ℝ → ℝ) {a b c : ℝ}
    (hc : c ∈ Ioo a b) (hf : ContDiffOn ℝ 3 f (Ioo a b))
    (hzero : ∀ x ∈ Ioo a b, deriv (deriv (deriv f)) x = 0) :
    ∀ x ∈ Ioo a b, f x = f c + deriv f c * (x - c) +
      (deriv (deriv f) c / 2) * (x - c) ^ 2 := by
  have hd : ContDiffOn ℝ 2 (deriv f) (Ioo a b) :=
    hf.deriv_of_isOpen isOpen_Ioo (by norm_num)
  have hlin := affine_of_second_derivative_zero (deriv f) hc hd hzero
  have hg (x : ℝ) : HasDerivAt
      (fun t ↦ f c + deriv f c * (t - c) + (deriv (deriv f) c / 2) * (t - c) ^ 2)
      (deriv f c + deriv (deriv f) c * (x - c)) x := by
    convert ((((hasDerivAt_id x).sub_const c).const_mul (deriv f c)).const_add (f c)).add
      ((((hasDerivAt_id x).sub_const c).pow 2).const_mul (deriv (deriv f) c / 2)) using 1
    simp only [id_eq]
    ring
  apply isOpen_Ioo.eqOn_of_deriv_eq isPreconnected_Ioo
    (hf.differentiableOn (by norm_num))
    (fun x _ ↦ (hg x).differentiableAt.differentiableWithinAt) _ hc (by simp)
  intro x hx
  rw [(hg x).deriv, hlin x hx]

end Descent.Portability.QuadraticRigidityLaw
