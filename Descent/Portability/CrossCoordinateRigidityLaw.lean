/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.QuadraticRigidityLaw
import Mathlib.Tactic

assert_below Descent.Decision Descent.Program

/-!
The analytic bridge for multidimensional diploid compatibility. Closedness and
own-coordinate affinity force quadratic dependence in every other coordinate.
The argument differentiates a two-point interpolation identity and then uses
one-dimensional uniqueness of primitives. It does not assume a polynomial field
or an already existing potential, and it requires no third derivatives of the field.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.CrossCoordinateRigidityLaw

open Set QuadraticRigidityLaw

/-- A C² function with zero second derivative agrees exactly with its two-point interpolant. -/
theorem affine_two_point (f : ℝ → ℝ) {a b s t : ℝ}
    (hs : s ∈ Ioo a b) (ht : t ∈ Ioo a b) (hst : s ≠ t)
    (hf : ContDiffOn ℝ 2 f (Ioo a b))
    (hzero : ∀ y ∈ Ioo a b, deriv (deriv f) y = 0) (y : ℝ) (hy : y ∈ Ioo a b) :
    f y = (1 - (y - s) / (t - s)) * f s + ((y - s) / (t - s)) * f t := by
  have hlin := affine_of_second_derivative_zero f hs hf hzero
  have hyt := hlin y hy
  have htt := hlin t ht
  have hden : t - s ≠ 0 := sub_ne_zero.mpr hst.symm
  rw [hyt, htt]
  field_simp
  ring

/-- Differentiation in a second variable preserves an exact two-point interpolation identity. -/
theorem cross_derivative_interpolation (f : ℝ → ℝ → ℝ) {a b c d s t : ℝ}
    (hs : s ∈ Ioo c d) (ht : t ∈ Ioo c d) (hst : s ≠ t)
    (hfy : ∀ x ∈ Ioo a b, ContDiffOn ℝ 2 (f x) (Ioo c d))
    (hzero : ∀ x ∈ Ioo a b, ∀ y ∈ Ioo c d, deriv (deriv (f x)) y = 0)
    (hfx : ∀ y ∈ Ioo c d, DifferentiableOn ℝ (fun x ↦ f x y) (Ioo a b))
    (x : ℝ) (hx : x ∈ Ioo a b) (y : ℝ) (hy : y ∈ Ioo c d) :
    deriv (fun x ↦ f x y) x =
      (1 - (y - s) / (t - s)) * deriv (fun x ↦ f x s) x +
        ((y - s) / (t - s)) * deriv (fun x ↦ f x t) x := by
  have heq : EqOn (fun x ↦ f x y)
      (fun x ↦ (1 - (y - s) / (t - s)) * f x s +
        ((y - s) / (t - s)) * f x t) (Ioo a b) := by
    intro u hu
    exact affine_two_point (f u) hs ht hst (hfy u hu) (hzero u hu) y hy
  have hds := ((hfx s hs).differentiableAt (isOpen_Ioo.mem_nhds hx)).hasDerivAt
  have hdt := ((hfx t ht).differentiableAt (isOpen_Ioo.mem_nhds hx)).hasDerivAt
  have hd := heq.deriv isOpen_Ioo hx
  exact hd.trans (((hds.const_mul (1 - (y - s) / (t - s))).add
    (hdt.const_mul ((y - s) / (t - s)))).deriv)

/-- A field component is quadratic in a foreign coordinate: this follows from closedness
and affinity of the other component in its own coordinate, with no potential hypothesis. -/
theorem closed_field_foreign_quadratic (bi bj : ℝ → ℝ → ℝ) {a b c d s t : ℝ}
    (hs : s ∈ Ioo c d) (ht : t ∈ Ioo c d) (hst : s ≠ t)
    (hjy : ∀ x ∈ Ioo a b, ContDiffOn ℝ 2 (bj x) (Ioo c d))
    (hjzero : ∀ x ∈ Ioo a b, ∀ y ∈ Ioo c d, deriv (deriv (bj x)) y = 0)
    (hjx : ∀ y ∈ Ioo c d, DifferentiableOn ℝ (fun x ↦ bj x y) (Ioo a b))
    (hiy : ∀ x ∈ Ioo a b, DifferentiableOn ℝ (bi x) (Ioo c d))
    (hclosed : ∀ x ∈ Ioo a b, ∀ y ∈ Ioo c d,
      deriv (bi x) y = deriv (fun x ↦ bj x y) x)
    (x : ℝ) (hx : x ∈ Ioo a b) :
    ∀ y ∈ Ioo c d, bi x y = bi x s + deriv (bi x) s * (y - s) +
      ((deriv (bi x) t - deriv (bi x) s) / (2 * (t - s))) * (y - s) ^ 2 := by
  have hderiv : ∀ y ∈ Ioo c d, deriv (bi x) y =
      deriv (bi x) s + ((deriv (bi x) t - deriv (bi x) s) / (t - s)) * (y - s) := by
    intro y hy
    have h := cross_derivative_interpolation bj hs ht hst hjy hjzero hjx x hx y hy
    rw [← hclosed x hx y hy, ← hclosed x hx s hs, ← hclosed x hx t ht] at h
    rw [h]
    ring
  have hg (y : ℝ) : HasDerivAt
      (fun u ↦ bi x s + deriv (bi x) s * (u - s) +
        ((deriv (bi x) t - deriv (bi x) s) / (2 * (t - s))) * (u - s) ^ 2)
      (deriv (bi x) s + ((deriv (bi x) t - deriv (bi x) s) / (t - s)) * (y - s)) y := by
    convert ((((hasDerivAt_id y).sub_const s).const_mul (deriv (bi x) s)).const_add
      (bi x s)).add ((((hasDerivAt_id y).sub_const s).pow 2).const_mul
        ((deriv (bi x) t - deriv (bi x) s) / (2 * (t - s)))) using 1
    simp only [id_eq]
    have hden : t - s ≠ 0 := sub_ne_zero.mpr hst.symm
    field_simp
    ring
  apply isOpen_Ioo.eqOn_of_deriv_eq isPreconnected_Ioo (hiy x hx)
    (fun y _ ↦ (hg y).differentiableAt.differentiableWithinAt) _ hs (by simp)
  intro y hy
  rw [(hg y).deriv, hderiv y hy]

end Descent.Portability.CrossCoordinateRigidityLaw
