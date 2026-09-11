/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.OperatorSlaterSeparation

assert_below Descent.Decision Descent.Program

/-!
Slater multipliers for a scalar budget and an operator inequality. The
objective coefficient is proved positive from an actual strict feasible
point, then normalized. This constructs a nonnegative budget multiplier
and a positive operator functional with global Lagrangian optimality and
both complementary-slackness equations.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.OperatorSlaterMultipliers

open OperatorPositiveCone OperatorSlaterSeparation

variable {X E : Type*} [AddCommGroup X] [Module ℝ X]
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Restriction of the actual separating functional to the operator coordinate. -/
noncomputable def operatorPart (L : ResidualSpace E →L[ℝ] ℝ) :
    (E →L[ℝ] E) →L[ℝ] ℝ where
  toFun A := L (0, 0, A)
  map_add' A B := by
    simpa using map_add L ((0, 0, A) : ResidualSpace E) (0, 0, B)
  map_smul' t A := by
    simpa using map_smul L t ((0, 0, A) : ResidualSpace E)
  cont := L.continuous.comp (continuous_const.prodMk (continuous_const.prodMk continuous_id))

/-- The separator splits exactly into its two scalar coefficients and operator functional. -/
theorem decomposition (L : ResidualSpace E →L[ℝ] ℝ) (y : ResidualSpace E) :
    L y = L (1, 0, 0) * y.1 + L (0, 1, 0) * y.2.1 + operatorPart L y.2.2 := by
  have he : y = y.1 • ((1, 0, 0) : ResidualSpace E) +
      y.2.1 • ((0, 1, 0) : ResidualSpace E) + (0, 0, y.2.2) := by
    ext <;> simp
  calc
    L y = L (y.1 • ((1, 0, 0) : ResidualSpace E) +
        y.2.1 • ((0, 1, 0) : ResidualSpace E) + (0, 0, y.2.2)) := congrArg L he
    _ = _ := by
      rw [map_add, map_add, map_smul, map_smul]
      change y.1 * L (1, 0, 0) + y.2.1 * L (0, 1, 0) + L (0, 0, y.2.2) = _
      dsimp [operatorPart]
      ring

/-- Strict feasibility gives actual normalized multipliers for the full operator inequality. -/
theorem exists_multipliers (C : Set X) (f g : X → ℝ) (H : X → E →L[ℝ] E) (xstar : X)
    (hf : ConvexOn ℝ C f) (hg : ConvexOn ℝ C g)
    (hH : ∀ v : E, ConvexOn ℝ C (fun x ↦ inner ℝ v (H x v)))
    (hstar : xstar ∈ C) (hbudget : g xstar ≤ 0) (hoperator : Nonnegative (-H xstar))
    (hmin : ∀ x ∈ C, g x ≤ 0 → Nonnegative (-H x) → f xstar ≤ f x)
    (hslater : ∃ x ∈ C, g x < 0 ∧ StrictPositive (-H x)) :
    ∃ (lam : ℝ) (R : (E →L[ℝ] E) →L[ℝ] ℝ), 0 ≤ lam ∧
      (∀ A, Nonnegative A → 0 ≤ R A) ∧
      (∀ x ∈ C, f xstar ≤ f x + lam * g x + R (H x)) ∧
      lam * g xstar = 0 ∧ R (H xstar) = 0 := by
  let F (x : X) : ResidualSpace E := (f x - f xstar, g x, H x)
  have hF : ConvexOn ℝ C (fun x ↦ (F x).1) := by
    refine ⟨hf.1, ?_⟩
    intro x hx y hy a b ha hb hab
    have hh := hf.2 hx hy ha hb hab
    change f (a • x + b • y) ≤ a * f x + b * f y at hh
    change f (a • x + b • y) - f xstar ≤ a * (f x - f xstar) + b * (f y - f xstar)
    have he : a * f xstar + b * f xstar = f xstar := by rw [← add_mul, hab, one_mul]
    nlinarith
  have hzero : (0 : ResidualSpace E) ∉ upperImage C F := by
    rintro ⟨x, hx, h₀, h₁, h₂⟩
    have hn : Nonnegative (-H x) := strict_nonnegative _ (by simpa [F] using h₂)
    have hh := hmin x hx h₁.le hn
    change f x - f xstar < 0 at h₀
    linarith
  obtain ⟨L, hL, hpos, hsupport⟩ := exists_separator C F hf.1 ⟨xstar, hstar⟩ hF hg hH hzero
  let a := L (1, 0, 0)
  have ha₀ : 0 ≤ a := hpos (1, 0, 0) zero_le_one (le_refl 0) (fun x ↦ by simp)
  have ha : 0 < a := by
    by_contra hn
    have hz : a = 0 := le_antisymm (not_lt.mp hn) ha₀
    obtain ⟨x, hx, hgb, hHB⟩ := hslater
    have hy : ((f x - f xstar + 1, 0, 0) : ResidualSpace E) ∈ upperImage C F := by
      refine ⟨x, hx, ?_, hgb, ?_⟩
      · change f x - f xstar < f x - f xstar + 1
        linarith
      · simpa [F] using hHB
    have hh := hL _ hy
    rw [decomposition] at hh
    change 0 < a * (f x - f xstar + 1) + L (0, 1, 0) * 0 + operatorPart L 0 at hh
    simp only [hz, zero_mul, mul_zero, map_zero, add_zero] at hh
    exact (lt_irrefl 0) hh
  let lam := L (0, 1, 0) / a
  let R : (E →L[ℝ] E) →L[ℝ] ℝ := (1 / a) • operatorPart L
  have hlam : 0 ≤ lam := div_nonneg
    (hpos (0, 1, 0) (le_refl 0) zero_le_one (fun x ↦ by simp)) ha.le
  have hR : ∀ A, Nonnegative A → 0 ≤ R A := by
    intro A hA
    have hh := hpos (0, 0, A) (le_refl 0) (le_refl 0) hA
    exact mul_nonneg (div_nonneg zero_le_one ha.le) hh
  have hscale (A : E →L[ℝ] E) : a * R A = operatorPart L A := by
    change a * ((1 / a) * operatorPart L A) = operatorPart L A
    field_simp [ha.ne']
  have hscalar : a * lam = L (0, 1, 0) := by
    dsimp [lam]
    field_simp [ha.ne']
  have hl : ∀ x ∈ C, f xstar ≤ f x + lam * g x + R (H x) := by
    intro x hx
    have hh := hsupport x hx
    rw [decomposition] at hh
    change 0 ≤ a * (f x - f xstar) + L (0, 1, 0) * g x + operatorPart L (H x) at hh
    rw [← hscale, ← hscalar] at hh
    nlinarith
  have hs := hl xstar hstar
  have hn₁ := mul_nonpos_of_nonneg_of_nonpos hlam hbudget
  have hn₂ := hR (-H xstar) hoperator
  rw [map_neg] at hn₂
  exact ⟨lam, R, hlam, hR, hl, by linarith, by linarith⟩

end Descent.Portability.OperatorSlaterMultipliers
