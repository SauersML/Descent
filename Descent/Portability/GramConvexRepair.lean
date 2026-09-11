/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.GramSafeRepair
import Mathlib.Analysis.Normed.Module.FiniteDimension

assert_below Descent.Decision Descent.Program

/-!
Decision-Directed Portability, Theorem 12 in the original Gram coordinates.
Every nonempty compact convex set of residual correlations has a unique
least inverse-quadratic signal. Its inverse-Gram coefficient attains the
exact robust gain over the entire confidence set, including nonspherical
sets. The coordinate change and its continuity are derived from the matrix.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.GramConvexRepair

open Matrix GramSafeRepair

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The inverse-Gram coordinate map into the actual induced inner-product space. -/
noncomputable def signalMap (G : Matrix ι ι ℝ) (hG : G.PosDef) :
    (ι → ℝ) →ₗ[ℝ] GramSpace G hG where
  toFun r := toGram G hG (G⁻¹ *ᵥ r)
  map_add' r s := by
    change G⁻¹ *ᵥ (r + s) = G⁻¹ *ᵥ r + G⁻¹ *ᵥ s
    exact mulVec_add _ _ _
  map_smul' a r := by
    change G⁻¹ *ᵥ (a • r) = a • (G⁻¹ *ᵥ r)
    exact mulVec_smul _ _ _

/-- The norm squared of the transformed signal is the actual inverse quadratic form. -/
theorem signalMap_norm_sq (G : Matrix ι ι ℝ) (hG : G.PosDef) (r : ι → ℝ) :
    ‖signalMap G hG r‖ ^ 2 = oracle G r := by
  change ‖toGram G hG (G⁻¹ *ᵥ r)‖ ^ 2 = oracle G r
  rw [induced_norm_sq G hG, toGram, normal_equation G hG]
  exact dotProduct_comm _ _

/-- Equal transformed signals imply equal original residual correlations. -/
theorem signalMap_injective (G : Matrix ι ι ℝ) (hG : G.PosDef) :
    Function.Injective (signalMap G hG) := by
  intro r s hrs
  have he := congrArg (fun v : GramSpace G hG ↦ G *ᵥ (v : ι → ℝ)) hrs
  change G *ᵥ (G⁻¹ *ᵥ r) = G *ᵥ (G⁻¹ *ᵥ s) at he
  simpa only [normal_equation G hG] using he

/-- A compact convex confidence set yields an attained exact robust matrix repair. -/
theorem compact_optimum (G : Matrix ι ι ℝ) (hG : G.PosDef) (C : Set (ι → ℝ))
    (hne : C.Nonempty) (hcompact : IsCompact C) (hconvex : Convex ℝ C) :
    ∃ r ∈ C, IsMinOn (oracle G) C r ∧
      (∀ s ∈ C, oracle G r ≤ gain G (G⁻¹ *ᵥ r) s) ∧
      IsGreatest {v : ℝ | ∃ θ : ι → ℝ, ∀ s ∈ C, v ≤ gain G θ s} (oracle G r) := by
  let T := signalMap G hG
  have hcont : Continuous T := T.continuous_of_finiteDimensional
  obtain ⟨u, ⟨r, hr, rfl⟩, hlower, hgreat⟩ := SafeRepairGeometry.compact_robust_optimum
    (T '' C) (hne.image T) (hcompact.image hcont) (hconvex.linear_image T)
  have hg (s : ι → ℝ) :
      SafeRepairGeometry.gain (T r) (T s) = gain G (G⁻¹ *ᵥ r) s :=
    induced_gain G hG (G⁻¹ *ᵥ r) s
  have hl : ∀ s ∈ C, oracle G r ≤ gain G (G⁻¹ *ᵥ r) s := by
    intro s hs
    have hh := hlower (T s) ⟨s, hs, rfl⟩
    rw [hg s, signalMap_norm_sq] at hh
    exact hh
  refine ⟨r, hr, ?_, hl, ⟨⟨G⁻¹ *ᵥ r, hl⟩, ?_⟩⟩
  · intro s hs
    have hh := SafeRepairGeometry.gain_le_oracle (T r) (T s)
    rw [hg s, signalMap_norm_sq] at hh
    exact (hl s hs).trans hh
  · rintro v ⟨θ, hθ⟩
    have hh : v ≤ ‖T r‖ ^ 2 := by
      apply hgreat.2
      refine ⟨toGram G hG θ, ?_⟩
      rintro s ⟨t, ht, rfl⟩
      change v ≤ SafeRepairGeometry.gain (toGram G hG θ) (toGram G hG (G⁻¹ *ᵥ t))
      rw [induced_gain G hG]
      exact hθ t ht
    simpa only [T, signalMap_norm_sq] using hh

/-- The least-signal residual correlation is unique, with no strictly convex set assumption. -/
theorem unique_least_signal (G : Matrix ι ι ℝ) (hG : G.PosDef) (C : Set (ι → ℝ))
    (r : ι → ℝ) (hlower : ∀ s ∈ C, oracle G r ≤ gain G (G⁻¹ *ᵥ r) s)
    (s : ι → ℝ) (hs : s ∈ C) (he : oracle G s = oracle G r) : s = r := by
  have hh := hlower s hs
  rw [← induced_gain G hG (G⁻¹ *ᵥ r) s,
    SafeRepairGeometry.gain_eq_oracle_sub_regret] at hh
  change oracle G r ≤ ‖signalMap G hG s‖ ^ 2 -
    ‖signalMap G hG r - signalMap G hG s‖ ^ 2 at hh
  rw [signalMap_norm_sq, he] at hh
  have hz : ‖signalMap G hG r - signalMap G hG s‖ = 0 := by
    nlinarith [norm_nonneg (signalMap G hG r - signalMap G hG s)]
  exact (signalMap_injective G hG (sub_eq_zero.mp (norm_eq_zero.mp hz))).symm

end Descent.Portability.GramConvexRepair
