/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.FiniteSlaterSeparation

assert_below Descent.Decision Descent.Program

/-!
Decision-Directed Portability, the finite-constraint strong-duality step in
Theorem 14. A strict feasible point forces the objective coordinate of an
actual separating functional to be positive. Normalizing it constructs
nonnegative Lagrange multipliers, global Lagrangian optimality, and
complementary slackness at the supplied actual primal minimizer.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.FiniteSlaterMultipliers

open FiniteSlaterSeparation
open scoped BigOperators

variable {A J : Type*} [AddCommGroup A] [Module ℝ A] [Fintype J]

/-- Objective excess occupies the first coordinate; the remaining coordinates are constraints. -/
def residuals (f : A → ℝ) (g : J → A → ℝ) (v : ℝ) (x : A) : Option J → ℝ
  | none ↦ f x - v
  | some j ↦ g j x

/-- Convex objective and constraints give a coordinatewise convex residual map. -/
theorem residuals_convex (C : Set A) (f : A → ℝ) (g : J → A → ℝ) (v : ℝ)
    (hf : ConvexOn ℝ C f) (hg : ∀ j, ConvexOn ℝ C (g j)) (i : Option J) :
    ConvexOn ℝ C (fun x ↦ residuals f g v x i) := by
  cases i with
  | some j => exact hg j
  | none =>
    refine ⟨hf.1, ?_⟩
    intro x hx y hy α β hα hβ hsum
    have hh := hf.2 hx hy hα hβ hsum
    change f (α • x + β • y) ≤ α * f x + β * f y at hh
    change f (α • x + β • y) - v ≤ α * (f x - v) + β * (f y - v)
    have hv : α * v + β * v = v := by rw [← add_mul, hsum, one_mul]
    nlinarith

/-- Strict feasibility constructs normalized multipliers for the actual convex primal optimum. -/
theorem exists_multipliers (C : Set A) (f : A → ℝ) (g : J → A → ℝ) (xstar : A)
    (hf : ConvexOn ℝ C f) (hg : ∀ j, ConvexOn ℝ C (g j))
    (hstar : xstar ∈ C) (hfeasible : ∀ j, g j xstar ≤ 0)
    (hmin : ∀ x ∈ C, (∀ j, g j x ≤ 0) → f xstar ≤ f x)
    (hslater : ∃ x ∈ C, ∀ j, g j x < 0) :
    ∃ lam : J → ℝ, (∀ j, 0 ≤ lam j) ∧
      (∀ x ∈ C, f xstar ≤ f x + ∑ j, lam j * g j x) ∧
      (∀ j, lam j * g j xstar = 0) := by
  classical
  have hzero : (0 : Option J → ℝ) ∉ upperImage C (residuals f g (f xstar)) := by
    rintro ⟨x, hx, hres⟩
    have hv := hres none
    change f x - f xstar < 0 at hv
    have hcon (j : J) : g j x ≤ 0 := (hres (some j)).le
    linarith [hmin x hx hcon]
  obtain ⟨a, ha, ⟨i, hi⟩, hs⟩ := exists_nonnegative_separator C (residuals f g (f xstar))
    hf.1 ⟨xstar, hstar⟩ (residuals_convex C f g (f xstar) hf hg) hzero
  have hpos : 0 < a none := by
    by_contra hn
    have hz : a none = 0 := le_antisymm (not_lt.mp hn) (ha none)
    obtain ⟨x, hx, hstrict⟩ := hslater
    have hb := hs x hx
    simp only [Fintype.sum_option, residuals, hz, zero_mul, zero_add] at hb
    cases i with
    | none => rw [hz] at hi; exact (lt_irrefl 0) hi
    | some j =>
      have hneg : (∑ k, a (some k) * g k x) < 0 := by
        apply Finset.sum_neg'
        · intro k _
          exact mul_nonpos_of_nonneg_of_nonpos (ha (some k)) (hstrict k).le
        · exact ⟨j, Finset.mem_univ _, mul_neg_of_pos_of_neg hi (hstrict j)⟩
      exact (not_lt.mpr hb) hneg
  let lam (j : J) := a (some j) / a none
  have hlam (j : J) : 0 ≤ lam j := div_nonneg (ha (some j)) hpos.le
  have hsupport (x : A) (hx : x ∈ C) : f xstar ≤ f x + ∑ j, lam j * g j x := by
    have hb := hs x hx
    simp only [Fintype.sum_option, residuals] at hb
    have he : a none * (∑ j, lam j * g j x) = ∑ j, a (some j) * g j x := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      dsimp [lam]
      field_simp [hpos.ne']
    nlinarith
  refine ⟨lam, hlam, hsupport, ?_⟩
  have hb := hsupport xstar hstar
  have hn (j : J) : lam j * g j xstar ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (hlam j) (hfeasible j)
  have hz : (∑ j, lam j * g j xstar) = 0 :=
    le_antisymm (Finset.sum_nonpos (fun j _ ↦ hn j)) (by linarith)
  exact fun j ↦ (Finset.sum_eq_zero_iff_of_nonpos (fun j _ ↦ hn j)).mp hz j (Finset.mem_univ j)

end Descent.Portability.FiniteSlaterMultipliers
