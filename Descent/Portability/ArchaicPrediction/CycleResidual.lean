/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.ArchaicPrediction.Contrast

assert_below Descent.Decision Descent.Program

/-!
# Exact residual from multiple independent cycle defects

Equation (7.3). In whitened edge coordinates take `C = C₀ W⁻¹/²` and
`d = W¹/² d₀`; the normal operator below is `C₀ W⁻¹ C₀ᵀ`. The cycle
coordinates are independent (`C` is surjective), and their common kernel
is the gradient space. The minimizing residual is constructed explicitly.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.ArchaicPrediction

open scoped RealInnerProductSpace
variable {E F H : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]

lemma adjoint_injective_of_surjective (C : F →L[ℝ] H) (hC : Function.Surjective C) :
    Function.Injective C.adjoint := by
  intro x y hxy
  have hz : C.adjoint (x - y) = 0 := by simp [hxy]
  obtain ⟨v, hv⟩ := hC (x - y)
  have hi : ⟪x - y, x - y⟫ = 0 := by
    conv_lhs => rhs; rw [← hv]
    rw [← C.adjoint_inner_left, hz, inner_zero_left]
  exact sub_eq_zero.mp (inner_self_eq_zero.mp hi)

theorem minimum_norm_under_contrasts (B : H →L[ℝ] F) (hB : Function.Injective B) (t : H) :
    IsLeast {s : ℝ | ∃ r : F, B.adjoint r = t ∧ s = ‖r‖ ^ 2}
      ⟪t, contrastInverse B t⟫ := by
  let rstar := B (contrastInverse B t)
  have hfeas : B.adjoint rstar = t := contrastInverse_right B hB t
  have hnorm : ‖rstar‖ ^ 2 = ⟪t, contrastInverse B t⟫ := by
    rw [← real_inner_self_eq_norm_sq]
    change ⟪B (contrastInverse B t), B (contrastInverse B t)⟫ = _
    rw [← contrastNormal_inner, contrastInverse_right B hB]
    exact real_inner_comm _ _
  constructor
  · exact ⟨rstar, hfeas, hnorm.symm⟩
  · rintro s ⟨r, hr, rfl⟩
    have ho : ⟪r - rstar, rstar⟫ = 0 := by
      change ⟪r - rstar, B (contrastInverse B t)⟫ = 0
      rw [← B.adjoint_inner_left, map_sub, hr, hfeas, sub_self, inner_zero_left]
    have he : r = (r - rstar) + rstar := by abel
    rw [he, norm_add_sq_real, ho]
    rw [← hnorm]
    nlinarith [sq_nonneg ‖r - rstar‖]

/-- Exact minimum weighted residual, expressed through independent cycle coordinates. -/
theorem exact_multiple_cycle_residual (B : E →L[ℝ] F) (C : F →L[ℝ] H)
    (hC : Function.Surjective C) (hker : LinearMap.range B = LinearMap.ker C) (d : F) :
    IsLeast (Set.range (fun m : E => ‖d - B m‖ ^ 2))
      ⟪C d, contrastInverse C.adjoint (C d)⟫ := by
  have hi := adjoint_injective_of_surjective C hC
  have hmin := minimum_norm_under_contrasts C.adjoint hi (C d)
  have ha : C.adjoint.adjoint = C := ContinuousLinearMap.adjoint_adjoint C
  rw [ha] at hmin
  constructor
  · obtain ⟨r, hr, hv⟩ := hmin.1
    have hk : d - r ∈ LinearMap.ker C := by simp [LinearMap.mem_ker, hr]
    rw [← hker] at hk
    obtain ⟨m, hm⟩ := hk
    refine ⟨m, ?_⟩
    change ‖d - B m‖ ^ 2 = _
    rw [hm]
    simpa only [sub_sub_cancel] using hv.symm
  · rintro s ⟨m, rfl⟩
    apply hmin.2
    refine ⟨d - B m, ?_, rfl⟩
    have hk : B m ∈ LinearMap.ker C := hker ▸ LinearMap.mem_range_self B m
    simp only [map_sub, show C (B m) = 0 from hk, sub_zero]

end Descent.Portability.ArchaicPrediction
