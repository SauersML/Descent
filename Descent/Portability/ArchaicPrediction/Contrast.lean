/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.AncientPrediction.Mixture
import Descent.Portability.ArchaicPrediction.Moments
import Mathlib.Analysis.InnerProductSpace.Adjoint

assert_below Descent.Decision Descent.Program

/-!
# Response-contrast consistency and measurement precision

Theorems 9 and 10 in finite-dimensional Hilbert coordinates. An incidence
operator maps response levels to measured contrasts; its adjoint kernel is
the circulation space. For estimation, the domain is the identifiable
subspace (the zero-sum response space of a connected graph), and observations
are whitened by their measurement precision. The inverse normal operator on
that subspace is the restriction of the Laplacian Moore--Penrose inverse.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.ArchaicPrediction

open scoped BigOperators RealInnerProductSpace
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ E]
  [FiniteDimensional ℝ F]

/-- A response map exists exactly when every circulation has zero defect. -/
theorem contrast_integrable_iff (B : E →L[ℝ] F) (d : F) :
    (∃ m, B m = d) ↔ ∀ c, B.adjoint c = 0 → ⟪c, d⟫ = 0 := by
  constructor
  · rintro ⟨m, rfl⟩ c hc
    rw [← B.adjoint_inner_left, hc, inner_zero_left]
  · intro h
    have hd : d ∈ (LinearMap.ker B.adjoint)ᗮ := by
      intro c hc
      exact h c hc
    rw [← B.orthogonal_range, Submodule.orthogonal_orthogonal] at hd
    exact hd

/-- The positive normal operator on the identifiable response space. -/
noncomputable def contrastNormal (B : E →L[ℝ] F) : E →L[ℝ] E := B.adjoint.comp B

lemma contrastNormal_inner (B : E →L[ℝ] F) (x y : E) :
    ⟪x, contrastNormal B y⟫ = ⟪B x, B y⟫ := by
  simp only [contrastNormal, ContinuousLinearMap.comp_apply, B.adjoint_inner_right]

lemma contrastNormal_symmetric (B : E →L[ℝ] F) (x y : E) :
    ⟪contrastNormal B x, y⟫ = ⟪x, contrastNormal B y⟫ := by
  simp only [contrastNormal, ContinuousLinearMap.comp_apply,
    B.adjoint_inner_left, B.adjoint_inner_right]

lemma contrastNormal_injective (B : E →L[ℝ] F) (hB : Function.Injective B) :
    Function.Injective (contrastNormal B) := by
  intro x y hxy
  have hz : contrastNormal B (x - y) = 0 := by simp [hxy]
  have hi := contrastNormal_inner B (x - y) (x - y)
  rw [hz, inner_zero_right] at hi
  have hb : B (x - y) = 0 := (inner_self_eq_zero).mp hi.symm
  have he : x - y = 0 := hB (by simpa using hb)
  exact sub_eq_zero.mp he

lemma contrastNormal_unit (B : E →L[ℝ] F) (hB : Function.Injective B) :
    IsUnit (contrastNormal B) := by
  have hi := contrastNormal_injective B hB
  exact ContinuousLinearMap.isUnit_iff_bijective.mpr
    ⟨hi, LinearMap.surjective_of_injective hi⟩

noncomputable def contrastInverse (B : E →L[ℝ] F) : E →L[ℝ] E := Ring.inverse (contrastNormal B)

lemma contrastInverse_right (B : E →L[ℝ] F) (hB : Function.Injective B) (x : E) :
    contrastNormal B (contrastInverse B x) = x :=
  AncientPrediction.normalSolution_equation x (contrastNormal B) (contrastNormal_unit B hB)

lemma contrastInverse_left (B : E →L[ℝ] F) (hB : Function.Injective B) (x : E) :
    contrastInverse B (contrastNormal B x) = x := by
  apply contrastNormal_injective B hB
  rw [contrastInverse_right]
  exact hB

lemma contrastInverse_symmetric (B : E →L[ℝ] F) (hB : Function.Injective B) (x y : E) :
    ⟪x, contrastInverse B y⟫ = ⟪contrastInverse B x, y⟫ := by
  calc
    _ = ⟪contrastNormal B (contrastInverse B x), contrastInverse B y⟫ := by
      rw [contrastInverse_right B hB]
    _ = ⟪contrastInverse B x, contrastNormal B (contrastInverse B y)⟫ :=
      contrastNormal_symmetric B _ _
    _ = _ := by rw [contrastInverse_right B hB]

noncomputable def contrastFit (B : E →L[ℝ] F) (d : F) : E := contrastInverse B (B.adjoint d)

theorem contrast_fit_error (B : E →L[ℝ] F) (hB : Function.Injective B) (m c : E) (ε : F) :
    ⟪c, contrastFit B (B m + ε) - m⟫ = ⟪B (contrastInverse B c), ε⟫ := by
  have he : contrastFit B (B m + ε) - m = contrastInverse B (B.adjoint ε) := by
    simp only [contrastFit, map_add]
    change contrastInverse B (contrastNormal B m) + contrastInverse B (B.adjoint ε) - m = _
    rw [contrastInverse_left B hB]
    abel
  rw [he, contrastInverse_symmetric B hB, B.adjoint_inner_right]

/-- Theorem 10: the variance of any estimable contrast is its resistance form.
The explicit noise assumptions are mean zero and identity covariance after
whitening; neither Gaussianity nor a fitted covariance conclusion is assumed. -/
theorem effective_resistance_variance {Ω : Type*} [Fintype Ω]
    (B : E →L[ℝ] F) (hB : Function.Injective B) (m c : E)
    (w : Ω → ℝ) (ε : Ω → F)
    (hmean : ∀ v : F, weightedMean w (fun ω => ⟪v, ε ω⟫) = 0)
    (hcov : ∀ v : F, weightedMean w (fun ω => ⟪v, ε ω⟫ ^ 2) = ⟪v, v⟫) :
    weightedMean w (fun ω => ⟪c, contrastFit B (B m + ε ω) - m⟫) = 0 ∧
    weightedMean w (fun ω => ⟪c, contrastFit B (B m + ε ω) - m⟫ ^ 2) =
      ⟪c, contrastInverse B c⟫ := by
  simp_rw [contrast_fit_error B hB]
  constructor
  · exact hmean _
  · rw [hcov, ← contrastNormal_inner, contrastInverse_right B hB]
    exact real_inner_comm _ _

section WeightedCycles
variable {A K : Type*} [Fintype A] [Fintype K]

lemma weighted_cauchy (w c r : A → ℝ) (hw : ∀ e, 0 < w e) :
    (∑ e, c e * r e) ^ 2 ≤ (∑ e, c e ^ 2 / w e) * ∑ e, w e * r e ^ 2 := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun e => c e / Real.sqrt (w e)) (fun e => Real.sqrt (w e) * r e)
  have hprod (e : A) : c e / Real.sqrt (w e) * (Real.sqrt (w e) * r e) = c e * r e := by
    have hp : Real.sqrt (w e) ≠ 0 := (Real.sqrt_pos.mpr (hw e)).ne'
    field_simp
  simpa only [hprod, div_pow, mul_pow, Real.sq_sqrt (hw _).le] using h

/-- Theorem 9's quantitative cycle-defect lower bound, for actual finite
incidence coordinates and strictly positive measurement precisions. -/
theorem weighted_cycle_defect (B : A → K → ℝ) (d c w : A → ℝ) (m : K → ℝ)
    (hw : ∀ e, 0 < w e) (hc : ∀ v, ∑ e, c e * B e v = 0) :
    (∑ e, c e * d e) ^ 2 / (∑ e, c e ^ 2 / w e) ≤
      ∑ e, w e * (d e - ∑ v, B e v * m v) ^ 2 := by
  have he : (∑ e, c e * (d e - ∑ v, B e v * m v)) = ∑ e, c e * d e := by
    simp only [mul_sub, Finset.sum_sub_distrib, Finset.mul_sum]
    have hz : (∑ e, ∑ v, c e * (B e v * m v)) = 0 := by
      rw [Finset.sum_comm]
      apply Finset.sum_eq_zero
      intro v _
      simp only [← mul_assoc, ← Finset.sum_mul, hc, zero_mul]
    rw [hz, sub_zero]
  have h := weighted_cauchy w c (fun e => d e - ∑ v, B e v * m v) hw
  rw [he] at h
  have hd : 0 ≤ ∑ e, c e ^ 2 / w e := Finset.sum_nonneg fun e _ => div_nonneg (sq_nonneg _) (hw e).le
  have hr : 0 ≤ ∑ e, w e * (d e - ∑ v, B e v * m v) ^ 2 :=
    Finset.sum_nonneg fun e _ => mul_nonneg (hw e).le (sq_nonneg _)
  exact div_le_of_le_mul₀ hd hr (by simpa only [mul_comm] using h)

end WeightedCycles
end Descent.Portability.ArchaicPrediction
