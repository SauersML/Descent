/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.NonreversibleLossExpansion

assert_below Descent.Decision Descent.Program

/-!
The general integrated-correlation resolvent identity. This is a different
endpoint from stale finite-horizon loss. Inverses are explicit bounded operators;
the quadratic identity and positivity are derived from their inverse equations.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.NonreversibleResolvent

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "⟪" x ", " y "⟫" => inner ℝ x y

/-- A real skew-adjoint operator has zero diagonal quadratic form. -/
theorem skew_inner_zero (circulation : E →L[ℝ] E)
    (hcirculation : star circulation = -circulation) (value : E) :
    ⟪value, circulation value⟫ = 0 := by
  have h := ContinuousLinearMap.adjoint_inner_right circulation value value
  change ⟪value, star circulation value⟫ = ⟪circulation value, value⟫ at h
  rw [hcirculation, ContinuousLinearMap.neg_apply, inner_neg_right,
    real_inner_comm (circulation value) value] at h
  linarith [real_inner_comm value (circulation value)]

/-- The exact difference from the reversible resolvent is the inverse-symmetric
energy of the circulating component. No simultaneous eigenbasis is assumed. -/
theorem resolvent_difference (symmetric circulation inverse resolvent : E →L[ℝ] E)
    (hsymmetric : star symmetric = symmetric) (hcirculation : star circulation = -circulation)
    (hinverse_left : inverse * symmetric = 1) (hinverse_right : symmetric * inverse = 1)
    (hresolvent : (symmetric - circulation) * resolvent = 1) (value : E) :
    ⟪value, inverse value⟫ - ⟪value, resolvent value⟫ =
      ⟪circulation (resolvent value), inverse (circulation (resolvent value))⟫ := by
  let vector := resolvent value
  have hsolve : symmetric vector - circulation vector = value := by
    have h := congrArg (fun operator : E →L[ℝ] E ↦ operator value) hresolvent
    simpa [vector, ContinuousLinearMap.mul_apply, ContinuousLinearMap.sub_apply] using h
  have hleft (input : E) : inverse (symmetric input) = input := by
    simpa [ContinuousLinearMap.mul_apply] using
      congrArg (fun operator : E →L[ℝ] E ↦ operator input) hinverse_left
  have hright (input : E) : symmetric (inverse input) = input := by
    simpa [ContinuousLinearMap.mul_apply] using
      congrArg (fun operator : E →L[ℝ] E ↦ operator input) hinverse_right
  have hcross : ⟪symmetric vector, inverse (circulation vector)⟫ = 0 := by
    rw [← ContinuousLinearMap.adjoint_inner_right symmetric]
    change ⟪vector, star symmetric (inverse (circulation vector))⟫ = 0
    rw [hsymmetric, hright, skew_inner_zero circulation hcirculation]
  have hinverse : inverse value = vector - inverse (circulation vector) := by
    rw [← hsolve, map_sub, hleft]
  change ⟪value, inverse value⟫ - ⟪value, vector⟫ = _
  rw [hinverse, inner_sub_right]
  have hpair : ⟪value, inverse (circulation vector)⟫ =
      -⟪circulation vector, inverse (circulation vector)⟫ := by
    rw [← hsolve, inner_sub_left, hcross, zero_sub]
  rw [hpair]
  ring

/-- Positive symmetric energy makes the reversible resolvent the larger quadratic
form. The nonreversible correction is derived explicitly, not postulated. -/
theorem resolvent_le_reversible (symmetric circulation inverse resolvent : E →L[ℝ] E)
    (hsymmetric : star symmetric = symmetric) (hcirculation : star circulation = -circulation)
    (hinverse_left : inverse * symmetric = 1) (hinverse_right : symmetric * inverse = 1)
    (hresolvent : (symmetric - circulation) * resolvent = 1)
    (hpositive : ∀ input, 0 ≤ ⟪input, symmetric input⟫) (value : E) :
    ⟪value, resolvent value⟫ ≤ ⟪value, inverse value⟫ := by
  have hright (input : E) : symmetric (inverse input) = input := by
    simpa [ContinuousLinearMap.mul_apply] using
      congrArg (fun operator : E →L[ℝ] E ↦ operator input) hinverse_right
  have hnonneg := hpositive (inverse (circulation (resolvent value)))
  rw [hright, real_inner_comm] at hnonneg
  have hid := resolvent_difference symmetric circulation inverse resolvent hsymmetric
    hcirculation hinverse_left hinverse_right hresolvent value
  linarith

/-- If a whitening factor satisfies `W*W = S⁻¹`, the same correction is exactly
its squared norm, as in the square-root form of the resolvent identity. -/
theorem resolvent_difference_norm (symmetric circulation inverse resolvent whitening : E →L[ℝ] E)
    (hsymmetric : star symmetric = symmetric) (hcirculation : star circulation = -circulation)
    (hinverse_left : inverse * symmetric = 1) (hinverse_right : symmetric * inverse = 1)
    (hresolvent : (symmetric - circulation) * resolvent = 1)
    (hwhitening : star whitening * whitening = inverse) (value : E) :
    ⟪value, inverse value⟫ - ⟪value, resolvent value⟫ =
      ‖whitening (circulation (resolvent value))‖ ^ 2 := by
  rw [resolvent_difference symmetric circulation inverse resolvent hsymmetric
    hcirculation hinverse_left hinverse_right hresolvent, ← hwhitening]
  change ⟪circulation (resolvent value),
    star whitening (whitening (circulation (resolvent value)))⟫ = _
  rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right,
    real_inner_self_eq_norm_sq]

end Descent.Portability.NonreversibleResolvent
