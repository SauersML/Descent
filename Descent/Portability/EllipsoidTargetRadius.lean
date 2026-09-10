/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.TargetUncertainty
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.Normed.Operator.NormedSpace

assert_below Descent.Decision Descent.Program

/-!
Exact target uncertainty on a norm-bounded affine observation fiber. The
minimum-norm center is constructed by orthogonal projection, and the residual
ball representation is derived by Pythagoras. A separate target weighting map
allows a singular quadratic loss and unrestricted unweighted predictions.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.EllipsoidTargetRadius

open TargetUncertainty

variable {E O F G : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup O] [NormedSpace ℝ O]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [InnerProductSpace ℝ G]

/-- Remove the invisible component of any solution to obtain the center. -/
noncomputable def fiberCenter (A : E →L[ℝ] O)
    [(LinearMap.ker A).HasOrthogonalProjection] (seed : E) : E :=
  seed - (LinearMap.ker A).starProjection seed

/-- The constructed center has exactly the same observed values. -/
theorem fiberCenter_observed (A : E →L[ℝ] O)
    [(LinearMap.ker A).HasOrthogonalProjection] (seed : E) : A (fiberCenter A seed) = A seed := by
  rw [fiberCenter, map_sub]
  have hz : A ((LinearMap.ker A).starProjection seed) = 0 :=
    (LinearMap.ker A).starProjection_apply_mem seed
  rw [hz, sub_zero]

/-- The constructed center is orthogonal to every invisible direction. -/
theorem fiberCenter_orthogonal (A : E →L[ℝ] O)
    [(LinearMap.ker A).HasOrthogonalProjection] (seed : E) (v : (LinearMap.ker A)) :
    inner ℝ (fiberCenter A seed) (v : E) = 0 :=
  (LinearMap.ker A).starProjection_inner_eq_zero seed v v.property

/-- Pythagoras converts the original radius into the residual radius. -/
theorem norm_fiber_iff (A : E →L[ℝ] O) (center : E)
    (horth : ∀ v : (LinearMap.ker A), inner ℝ center (v : E) = 0)
    (R : ℝ) (hR : 0 ≤ R) (hc : ‖center‖ ≤ R) (v : (LinearMap.ker A)) :
    ‖center + (v : E)‖ ≤ R ↔ ‖v‖ ≤ Real.sqrt (R ^ 2 - ‖center‖ ^ 2) := by
  have hp := norm_add_sq_eq_norm_sq_add_norm_sq_real (horth v)
  have hrad : 0 ≤ R ^ 2 - ‖center‖ ^ 2 := by
    nlinarith [mul_self_le_mul_self (norm_nonneg center) hc]
  rw [Real.le_sqrt (norm_nonneg v) hrad]
  constructor
  · intro h
    have hh := mul_self_le_mul_self (norm_nonneg (center + (v : E))) h
    change ‖(v : E)‖ ^ 2 ≤ R ^ 2 - ‖center‖ ^ 2
    nlinarith
  · intro h
    change ‖(v : E)‖ ^ 2 ≤ R ^ 2 - ‖center‖ ^ 2 at h
    nlinarith [norm_nonneg (center + (v : E))]

/-- Every feasible vector, and only a feasible vector, has the residual-ball form. -/
theorem feasible_iff (A : E →L[ℝ] O) (center : E)
    (horth : ∀ v : (LinearMap.ker A), inner ℝ center (v : E) = 0)
    (R : ℝ) (hR : 0 ≤ R) (hc : ‖center‖ ≤ R) (z : E) :
    (A z = A center ∧ ‖z‖ ≤ R) ↔
      ∃ v : (LinearMap.ker A), ‖v‖ ≤ Real.sqrt (R ^ 2 - ‖center‖ ^ 2) ∧ z = center + v := by
  constructor
  · rintro ⟨hobs, hnorm⟩
    have hker : z - center ∈ (LinearMap.ker A) := by change A (z - center) = 0; simp [hobs]
    let v : (LinearMap.ker A) := ⟨z - center, hker⟩
    have hz : z = center + (v : E) := by dsimp [v]; abel
    refine ⟨v, ?_, hz⟩
    exact (norm_fiber_iff A center horth R hR hc v).mp (hz ▸ hnorm)
  · rintro ⟨v, hv, rfl⟩
    refine ⟨?_, (norm_fiber_iff A center horth R hR hc v).mpr hv⟩
    rw [map_add, show A (v : E) = 0 from v.property, add_zero]

/-- The projection center is the minimum-norm solution, with equality only
when the invisible residual vanishes. -/
theorem fiberCenter_minimum_norm (A : E →L[ℝ] O)
    [(LinearMap.ker A).HasOrthogonalProjection] (seed z : E) (hz : A z = A seed) :
    ‖fiberCenter A seed‖ ≤ ‖z‖ := by
  have hk : z - fiberCenter A seed ∈ (LinearMap.ker A) := by
    change A (z - fiberCenter A seed) = 0
    rw [map_sub, fiberCenter_observed, hz, sub_self]
  have hp := norm_add_sq_eq_norm_sq_add_norm_sq_real
    (fiberCenter_orthogonal A seed (⟨z - fiberCenter A seed, hk⟩ : (LinearMap.ker A)))
  simp only [add_sub_cancel] at hp
  nlinarith [sq_nonneg ‖z - fiberCenter A seed‖,
    norm_nonneg (fiberCenter A seed), norm_nonneg z]

/-- Sharp report Theorem 6 on the whitened observation fiber. The target
weight may have a kernel; predictions range over the original target space. -/
theorem weighted_fiber_minimax (A : E →L[ℝ] O) (B : E →L[ℝ] F) (W : F →L[ℝ] G)
    (center : E) (horth : ∀ v : (LinearMap.ker A), inner ℝ center (v : E) = 0)
    (R : ℝ) (hR : 0 ≤ R) (hc : ‖center‖ ≤ R) :
    IsLeast {risk : ℝ | ∃ prediction : F, ∀ z : E,
      A z = A center → ‖z‖ ≤ R → ‖W (B z - prediction)‖ ^ 2 ≤ risk}
      ((R ^ 2 - ‖center‖ ^ 2) * ‖(W.comp B).comp (LinearMap.ker A).subtypeL‖ ^ 2) := by
  let r := Real.sqrt (R ^ 2 - ‖center‖ ^ 2)
  let L := (W.comp B).comp (LinearMap.ker A).subtypeL
  have hrad : 0 ≤ R ^ 2 - ‖center‖ ^ 2 := by
    nlinarith [mul_self_le_mul_self (norm_nonneg center) hc]
  have hrsq : r ^ 2 = R ^ 2 - ‖center‖ ^ 2 := Real.sq_sqrt hrad
  refine ⟨⟨B center, ?_⟩, ?_⟩
  · intro z hobs hz
    obtain ⟨v, hv, rfl⟩ := (feasible_iff A center horth R hR hc z).mp ⟨hobs, hz⟩
    have hb := center_upper_bound L r v hv
    simpa [UniformBound, L, map_add, hrsq] using hb
  · rintro risk ⟨prediction, h⟩
    have hl := uniform_bound_lower L r (Real.sqrt_nonneg _) (W (prediction - B center)) risk
    rw [hrsq] at hl
    apply hl
    intro v hv
    have hfeas := (feasible_iff A center horth R hR hc (center + (v : E))).mpr
      ⟨v, hv, rfl⟩
    have hh := h (center + (v : E)) hfeas.1 hfeas.2
    convert hh using 1
    simp only [L, ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply, map_sub, map_add]
    congr 2
    abel

/-- An invertible whitening map transports the exact minimax theorem to an
ellipsoid in the original parameter coordinates. Choosing the positive square
root of the declared covariance gives the report's ellipsoidal model. -/
theorem weighted_ellipsoid_minimax (A : E →L[ℝ] O) (B : E →L[ℝ] F)
    (W : F →L[ℝ] G) (whitening : E ≃L[ℝ] E) (center : E)
    (horth : ∀ v : LinearMap.ker (A.comp whitening.toContinuousLinearMap),
      inner ℝ center (v : E) = 0)
    (R : ℝ) (hR : 0 ≤ R) (hc : ‖center‖ ≤ R) :
    IsLeast {risk : ℝ | ∃ prediction : F, ∀ θ : E,
      A θ = A (whitening center) → ‖whitening.symm θ‖ ≤ R →
        ‖W (B θ - prediction)‖ ^ 2 ≤ risk}
      ((R ^ 2 - ‖center‖ ^ 2) *
        ‖(W.comp (B.comp whitening.toContinuousLinearMap)).comp
          (LinearMap.ker (A.comp whitening.toContinuousLinearMap)).subtypeL‖ ^ 2) := by
  have hbase := weighted_fiber_minimax (A.comp whitening.toContinuousLinearMap)
    (B.comp whitening.toContinuousLinearMap) W center horth R hR hc
  have hsets : {risk : ℝ | ∃ prediction : F, ∀ θ : E,
      A θ = A (whitening center) → ‖whitening.symm θ‖ ≤ R →
        ‖W (B θ - prediction)‖ ^ 2 ≤ risk} =
      {risk : ℝ | ∃ prediction : F, ∀ z : E,
        (A.comp whitening.toContinuousLinearMap) z =
          (A.comp whitening.toContinuousLinearMap) center → ‖z‖ ≤ R →
          ‖W ((B.comp whitening.toContinuousLinearMap) z - prediction)‖ ^ 2 ≤ risk} := by
    ext risk
    constructor
    · rintro ⟨prediction, h⟩
      refine ⟨prediction, ?_⟩
      intro z hz hnorm
      exact h (whitening z) hz (by simpa using hnorm)
    · rintro ⟨prediction, h⟩
      refine ⟨prediction, ?_⟩
      intro θ hθ hnorm
      simpa using h (whitening.symm θ) (by simpa using hθ) hnorm
  rw [hsets]
  exact hbase

/-- At positive residual radius the sharp target loss vanishes exactly when
the weighted target annihilates the observational kernel. -/
theorem zero_radius_iff_kernel (A : E →L[ℝ] O) (B : E →L[ℝ] F) (W : F →L[ℝ] G)
    (r : ℝ) (hr : 0 < r) :
    r ^ 2 * ‖(W.comp B).comp (LinearMap.ker A).subtypeL‖ ^ 2 = 0 ↔
      LinearMap.ker A ≤ LinearMap.ker (W.comp B) := by
  rw [mul_eq_zero, or_iff_right (pow_ne_zero _ hr.ne'), sq_eq_zero_iff,
    ContinuousLinearMap.opNorm_zero_iff]
  constructor
  · intro h v hv
    have hh := congrArg (fun f : (LinearMap.ker A) →L[ℝ] G ↦ f ⟨v, hv⟩) h
    exact hh
  · intro h
    ext v
    exact h v.property

end Descent.Portability.EllipsoidTargetRadius
