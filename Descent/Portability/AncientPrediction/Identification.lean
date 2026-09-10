/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Layer
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.LinearAlgebra.Prod
import Mathlib.Data.Real.Basic

assert_below Descent.Decision Descent.Program

/-!
# The prediction-relevant quotient of history

Linear identification from Section 4 of *Ancient DNA for Modern Polygenic
Prediction*. The observations and target are actual linear maps. Identification
means constancy on every observation fiber, without a prior or noise model.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.AncientPrediction

variable {E Z T B H A : Type*}
  [AddCommGroup E] [Module ℝ E] [AddCommGroup Z] [Module ℝ Z]
  [AddCommGroup T] [Module ℝ T] [AddCommGroup B] [Module ℝ B]
  [AddCommGroup H] [Module ℝ H] [AddCommGroup A] [Module ℝ A]

/-- The target is constant on each fiber of the observation map. -/
def Identifies (observation : E →ₗ[ℝ] Z) (target : E →ₗ[ℝ] T) : Prop :=
  ∀ x y, observation x = observation y → target x = target y

/-- Theorem 2: the exact observation-kernel criterion. -/
theorem identifies_iff_ker_le (M : E →ₗ[ℝ] Z) (N : E →ₗ[ℝ] T) :
    Identifies M N ↔ LinearMap.ker M ≤ LinearMap.ker N := by
  constructor
  · intro h x hx
    have := h x 0 (by simpa using hx)
    simpa using this
  · intro h x y hxy
    have hx : x - y ∈ LinearMap.ker M := by simp [LinearMap.mem_ker, hxy]
    have := h hx
    simpa [LinearMap.mem_ker, sub_eq_zero] using this

/-- Joint modern and ancient observations `(L β + H η, K η)`. -/
def referenceObservation (L : B →ₗ[ℝ] Z) (H₀ : H →ₗ[ℝ] Z) (K : H →ₗ[ℝ] A) :
    B × H →ₗ[ℝ] Z × A :=
  (L.coprod H₀).prod (K.comp (LinearMap.snd ℝ B H))

/-- Corollary 2.1: with invertible modern observation operator, only the
historical directions surviving `T L⁻¹ H` need to be identified. -/
theorem predictive_quotient (L : B ≃ₗ[ℝ] Z) (H₀ : H →ₗ[ℝ] Z)
    (K : H →ₗ[ℝ] A) (target : B →ₗ[ℝ] T) :
    Identifies (referenceObservation L.toLinearMap H₀ K)
      (target.comp (LinearMap.fst ℝ B H)) ↔
    LinearMap.ker K ≤ LinearMap.ker (target.comp (L.symm.toLinearMap.comp H₀)) := by
  rw [identifies_iff_ker_le]
  constructor
  · intro h η hη
    have hz : (-L.symm (H₀ η), η) ∈
        LinearMap.ker (referenceObservation L.toLinearMap H₀ K) := by
      simp [LinearMap.mem_ker, referenceObservation, show K η = 0 from hη]
    have := h hz
    simpa [LinearMap.mem_ker] using this
  · intro h x hx
    rcases x with ⟨β, η⟩
    have hm : L β + H₀ η = 0 ∧ K η = 0 := by
      simpa [LinearMap.mem_ker, referenceObservation, Prod.ext_iff] using hx
    have ht : target (L.symm (H₀ η)) = 0 := h hm.2
    have hβ : β = -L.symm (H₀ η) := by
      apply L.injective
      simpa using eq_neg_of_add_eq_zero_left hm.1
    simp [LinearMap.mem_ker, hβ, ht]

/-- The quotient by the target's kernel records exactly target-equivalent
histories. It need not distinguish the full demographic parameter. -/
theorem quotient_history_iff (F : H →ₗ[ℝ] T) (η₁ η₂ : H) :
    (Submodule.mkQ (LinearMap.ker F)) η₁ = (Submodule.mkQ (LinearMap.ker F)) η₂ ↔
      F η₁ = F η₂ := by
  rw [← sub_eq_zero, ← map_sub, ← LinearMap.mem_ker, Submodule.ker_mkQ]
  simp [LinearMap.mem_ker, sub_eq_zero]

end Descent.Portability.AncientPrediction
