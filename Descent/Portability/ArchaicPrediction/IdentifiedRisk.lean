/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.ArchaicPrediction.Moments
import Mathlib.Analysis.Convex.Topology

assert_below Descent.Decision Descent.Program

/-!
# Sharp risk bounds from unresolved finite phase distributions

Equation (6.7): normalization and the reported phase moments define a compact
convex set of probability vectors. The complete identified risk set is a
closed interval, with both endpoints attained by feasible distributions.
These are exact-moment identified sets, not sampling-confidence sets.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.ArchaicPrediction

open scoped BigOperators
variable {H J : Type*} [Fintype H]

noncomputable def riskFunctional (r : H → ℝ) : (H → ℝ) →ₗ[ℝ] ℝ where
  toFun w := ∑ h, w h * r h
  map_add' a b := by simp [add_mul, Finset.sum_add_distrib]
  map_smul' a w := by simp [Finset.mul_sum, mul_assoc]

def feasiblePhaseLaws (φ : J → H → ℝ) (m : J → ℝ) : Set (H → ℝ) :=
  stdSimplex ℝ H ∩ {w | ∀ j, riskFunctional (φ j) w = m j}

theorem feasiblePhaseLaws_compact (φ : J → H → ℝ) (m : J → ℝ) :
    IsCompact (feasiblePhaseLaws φ m) := by
  apply (isCompact_stdSimplex H).inter_right
  have he : {w : H → ℝ | ∀ j, riskFunctional (φ j) w = m j} =
      ⋂ j, {w | riskFunctional (φ j) w = m j} := by ext; simp
  rw [he]
  apply isClosed_iInter
  intro j
  exact isClosed_eq (riskFunctional (φ j)).continuous_of_finiteDimensional continuous_const

theorem feasiblePhaseLaws_convex (φ : J → H → ℝ) (m : J → ℝ) :
    Convex ℝ (feasiblePhaseLaws φ m) := by
  apply (convex_stdSimplex ℝ H).inter
  intro a ha b hb s t hs ht hst j
  simp only [map_add, map_smul, ha j, hb j, smul_eq_mul]
  rw [← add_mul, hst, one_mul]

/-- The sharp identified risk interval, including attainment of every interior value. -/
theorem sharp_phase_risk_interval (φ : J → H → ℝ) (m : J → ℝ) (r : H → ℝ)
    (hne : (feasiblePhaseLaws φ m).Nonempty) :
    ∃ lo hi : H → ℝ, lo ∈ feasiblePhaseLaws φ m ∧ hi ∈ feasiblePhaseLaws φ m ∧
      riskFunctional r '' feasiblePhaseLaws φ m =
        Set.Icc (riskFunctional r lo) (riskFunctional r hi) := by
  have hc := feasiblePhaseLaws_compact φ m
  have hr : ContinuousOn (riskFunctional r) (feasiblePhaseLaws φ m) :=
    (riskFunctional r).continuous_of_finiteDimensional.continuousOn
  obtain ⟨lo, hlo, hmin⟩ := hc.exists_isMinOn hne hr
  obtain ⟨hi, hhi, hmax⟩ := hc.exists_isMaxOn hne hr
  refine ⟨lo, hi, hlo, hhi, Set.Subset.antisymm ?_ ?_⟩
  · rintro y ⟨w, hw, rfl⟩
    exact ⟨hmin hw, hmax hw⟩
  · have hv := (feasiblePhaseLaws_convex φ m).linear_image (riskFunctional r)
    exact hv.ordConnected.out ⟨lo, hlo, rfl⟩ ⟨hi, hhi, rfl⟩

end Descent.Portability.ArchaicPrediction
