/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.GramConvexRepair
import Descent.Portability.FrameMeanImage

assert_below Descent.Decision Descent.Program

/-!
Decision-Directed Portability, Theorem 12 as an optimization over actual
bounded outcome laws. A compact convex confidence set inside the attainable
mean image has an exact maximin repair for the separate expected frame
losses. Its least-favorable residual vector is realized by endpoint laws;
both the repair and the worst-case law attain the claimed value.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.FrameConvexRepair

open MeasureTheory Matrix GramSafeRepair DecisionLossContrasts FrameMeanImage

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]

/-- Outcome laws consistent with the registered support, mean bands and confidence set. -/
def Compatible (C : Set (κ → ℝ)) (w f L U lo hi : ι → ℝ) (φ : ι → κ → ℝ)
    (μ : ι → Measure ℝ) : Prop :=
  (∀ i, IsProbabilityMeasure (μ i)) ∧
    (∀ i, ∀ᵐ y ∂μ i, y ∈ Set.Icc (L i) (U i)) ∧
    (∀ i, lo i ≤ (∫ y, y ∂μ i) ∧ (∫ y, y ∂μ i) ≤ hi i) ∧ residual μ w f φ ∈ C

/-- Compatible bounded laws have defined separate risks and the exact matrix gain. -/
theorem compatible_gain (C : Set (κ → ℝ)) (w f L U lo hi : ι → ℝ)
    (φ : ι → κ → ℝ) (μ : ι → Measure ℝ) (hμ : Compatible C w f L U lo hi φ μ)
    (θ : κ → ℝ) :
    frameRisk μ w f - frameRisk μ w (predict f φ θ) =
      gain (gram w φ) θ (residual μ w f φ) := by
  letI (i : ι) := hμ.1 i
  exact frame_gain μ w f φ θ (fun i ↦ memLp_of_bounded
    (hμ.2.1 i) measurable_id.aestronglyMeasurable 2)

/-- The oracle coefficient attains its actual inverse-quadratic gain. -/
theorem oracle_gain (G : Matrix κ κ ℝ) (hG : G.PosDef) (r : κ → ℝ) :
    gain G (G⁻¹ *ᵥ r) r = oracle G r := by
  rw [← induced_gain G hG, SafeRepairGeometry.gain_self]
  exact GramConvexRepair.signalMap_norm_sq G hG r

/-- No coefficient can exceed the oracle gain at any fixed compatible residual vector. -/
theorem gain_upper (G : Matrix κ κ ℝ) (hG : G.PosDef) (θ r : κ → ℝ) :
    gain G θ r ≤ oracle G r := by
  rw [← induced_gain G hG]
  exact (SafeRepairGeometry.gain_le_oracle _ _).trans_eq
    (GramConvexRepair.signalMap_norm_sq G hG r)

/-- The compact confidence-set optimum is attained by both a repair and an actual outcome law. -/
theorem compact_outcome_optimum (C : Set (κ → ℝ)) (w f L U lo hi : ι → ℝ)
    (φ : ι → κ → ℝ) (hG : (gram w φ).PosDef)
    (hLU : ∀ i, L i < U i)
    (hband : ∀ i, L i ≤ lo i ∧ lo i ≤ hi i ∧ hi i ≤ U i)
    (hne : C.Nonempty) (hcompact : IsCompact C) (hconvex : Convex ℝ C)
    (himage : C ⊆ meanImage w f lo hi φ) :
    ∃ r ∈ C, IsMinOn (oracle (gram w φ)) C r ∧ ∃ ν : ι → Measure ℝ,
      Compatible C w f L U lo hi φ ν ∧ residual ν w f φ = r ∧
      (∀ μ, Compatible C w f L U lo hi φ μ →
        oracle (gram w φ) r ≤ frameRisk μ w f -
          frameRisk μ w (predict f φ ((gram w φ)⁻¹ *ᵥ r))) ∧
      frameRisk ν w f - frameRisk ν w (predict f φ ((gram w φ)⁻¹ *ᵥ r)) =
        oracle (gram w φ) r ∧
      IsGreatest {v : ℝ | ∃ θ : κ → ℝ, ∀ μ, Compatible C w f L U lo hi φ μ →
        v ≤ frameRisk μ w f - frameRisk μ w (predict f φ θ)} (oracle (gram w φ) r) := by
  obtain ⟨r, hr, hmin, hlower, _⟩ :=
    GramConvexRepair.compact_optimum (gram w φ) hG C hne hcompact hconvex
  obtain ⟨ν, hp, hs, hm, _, he⟩ := attained w f L U lo hi φ hLU hband r (himage hr)
  have hν : Compatible C w f L U lo hi φ ν := ⟨hp, hs, hm, by rw [he]; exact hr⟩
  have hl : ∀ μ, Compatible C w f L U lo hi φ μ →
      oracle (gram w φ) r ≤ frameRisk μ w f -
        frameRisk μ w (predict f φ ((gram w φ)⁻¹ *ᵥ r)) := by
    intro μ hμ
    rw [compatible_gain C w f L U lo hi φ μ hμ]
    exact hlower _ hμ.2.2.2
  refine ⟨r, hr, hmin, ν, hν, he, hl, ?_, ⟨⟨(gram w φ)⁻¹ *ᵥ r, hl⟩, ?_⟩⟩
  · rw [compatible_gain C w f L U lo hi φ ν hν, he, oracle_gain _ hG]
  · rintro v ⟨θ, hθ⟩
    have hh := hθ ν hν
    rw [compatible_gain C w f L U lo hi φ ν hν, he] at hh
    exact hh.trans (gain_upper (gram w φ) hG θ r)

end Descent.Portability.FrameConvexRepair
