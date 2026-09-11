/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.GramSafeRepair
import Mathlib.Analysis.Normed.Module.Convex

assert_below Descent.Decision Descent.Program

/-!
Decision-Directed Portability, Theorem 22. The subgroup lower gain uses the
actual positive-definite Gram geometry. It bounds the true gain uniformly
over the supplied confidence ball, is concave in the shared coefficient
vector, and defines a convex feasible set containing the baseline correction.
Different subgroups may use different Gram matrices and confidence radii.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.SubgroupRepairGeometry

open Matrix GramSafeRepair
open scoped BigOperators RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A squared Hilbert norm satisfies the convex combination inequality. -/
theorem norm_sq_convex (u v : E) (α β : ℝ) (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (hsum : α + β = 1) : ‖α • u + β • v‖ ^ 2 ≤ α * ‖u‖ ^ 2 + β * ‖v‖ ^ 2 := by
  have hn := (convexOn_norm (convex_univ : Convex ℝ (Set.univ : Set E))).2
    (Set.mem_univ u) (Set.mem_univ v) hα hβ hsum
  change ‖α • u + β • v‖ ≤ α * ‖u‖ + β * ‖v‖ at hn
  have hm : 0 ≤ α * ‖u‖ + β * ‖v‖ := by positivity
  have hs : ‖α • u + β • v‖ ^ 2 ≤ (α * ‖u‖ + β * ‖v‖) ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) hm).mpr hn
  have he : α * ‖u‖ ^ 2 + β * ‖v‖ ^ 2 - (α * ‖u‖ + β * ‖v‖) ^ 2 =
      α * β * (‖u‖ - ‖v‖) ^ 2 := by
    have hb : β = 1 - α := by linarith
    rw [hb]
    ring
  have hpos : 0 ≤ α * β * (‖u‖ - ‖v‖) ^ 2 := by positivity
  linarith

/-- The confidence-ball lower gain is concave in Hilbert coefficient coordinates. -/
theorem lower_concave (h : E) (ε : ℝ) (hε : 0 ≤ ε) :
    ConcaveOn ℝ Set.univ (fun u : E ↦ SafeRepairGeometry.gain u h - 2 * ε * ‖u‖) := by
  refine ⟨convex_univ, ?_⟩
  intro u _ v _ α β hα hβ hsum
  have hnorm := (convexOn_norm (convex_univ : Convex ℝ (Set.univ : Set E))).2
    (Set.mem_univ u) (Set.mem_univ v) hα hβ hsum
  change ‖α • u + β • v‖ ≤ α * ‖u‖ + β * ‖v‖ at hnorm
  have hsq := norm_sq_convex u v α β hα hβ hsum
  have hpen := mul_le_mul_of_nonneg_left hnorm (show 0 ≤ 2 * ε by positivity)
  simp only [SafeRepairGeometry.gain, inner_add_left, inner_smul_left, conj_trivial,
    smul_eq_mul]
  nlinarith

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The explicit lower gain in the manuscript's original coefficient coordinates. -/
noncomputable def lower (G : Matrix ι ι ℝ) (h θ : ι → ℝ) (ε : ℝ) : ℝ :=
  gain G θ h - 2 * ε * Real.sqrt (θ ⬝ᵥ (G *ᵥ θ))

/-- The coefficient norm is the square root of its actual Gram quadratic form. -/
theorem coefficient_norm (G : Matrix ι ι ℝ) (hG : G.PosDef) (θ : ι → ℝ) :
    ‖toGram G hG θ‖ = Real.sqrt (θ ⬝ᵥ (G *ᵥ θ)) := by
  have he := induced_norm_sq G hG (toGram G hG θ)
  change ‖toGram G hG θ‖ ^ 2 = θ ⬝ᵥ (G *ᵥ θ) at he
  rw [← he, Real.sqrt_sq (norm_nonneg _)]

/-- The explicit coefficient lower gain is exactly the lower objective in Gram space. -/
theorem induced_lower (G : Matrix ι ι ℝ) (hG : G.PosDef) (h θ : ι → ℝ) (ε : ℝ) :
    SafeRepairGeometry.gain (toGram G hG θ) (toGram G hG (G⁻¹ *ᵥ h)) -
      2 * ε * ‖toGram G hG θ‖ = lower G h θ ε := by
  rw [induced_gain G hG, coefficient_norm G hG]
  rfl

/-- Every coefficient vector satisfying the subgroup certificate has its true gain bounded below. -/
theorem true_gain_lower (G : Matrix ι ι ℝ) (hG : G.PosDef) (h r θ : ι → ℝ) (ε : ℝ)
    (hr : signal G (r - h) ≤ ε) : lower G h θ ε ≤ gain G θ r := by
  have hh := SafeRepairGeometry.ball_gain_lower (toGram G hG θ)
    (toGram G hG (G⁻¹ *ᵥ h)) (toGram G hG (G⁻¹ *ᵥ r)) ε
    (by rw [induced_error G hG]; exact hr)
  rwa [induced_lower G hG, induced_gain G hG] at hh

/-- The explicit lower gain is concave in the shared ordinary coefficient coordinates. -/
theorem coefficient_lower_concave (G : Matrix ι ι ℝ) (hG : G.PosDef)
    (h : ι → ℝ) (ε : ℝ) (hε : 0 ≤ ε) :
    ConcaveOn ℝ Set.univ (fun θ : ι → ℝ ↦ lower G h θ ε) := by
  refine ⟨convex_univ, ?_⟩
  intro θ _ ψ _ α β hα hβ hsum
  have hh := (lower_concave (toGram G hG (G⁻¹ *ᵥ h)) ε hε).2
    (Set.mem_univ (toGram G hG θ)) (Set.mem_univ (toGram G hG ψ)) hα hβ hsum
  change α * _ + β * _ ≤ _ at hh
  have he : α • toGram G hG θ + β • toGram G hG ψ = toGram G hG (α • θ + β • ψ) := rfl
  rw [he] at hh
  dsimp only at hh
  rw [induced_lower G hG, induced_lower G hG, induced_lower G hG] at hh
  exact hh

/-- Zero correction has a zero lower gain in every subgroup. -/
theorem lower_zero (G : Matrix ι ι ℝ) (h : ι → ℝ) (ε : ℝ) : lower G h 0 ε = 0 := by
  simp [lower, gain]

variable {J : Type*}

/-- A shared coefficient vector meets every registered subgroup lower-gain requirement. -/
def SafeSet (G : J → Matrix ι ι ℝ) (h : J → ι → ℝ) (ε : J → ℝ) : Set (ι → ℝ) :=
  {θ | ∀ j, 0 ≤ lower (G j) (h j) θ (ε j)}

/-- The shared subgroup-feasible set is convex, even when the subgroup metrics differ. -/
theorem safeSet_convex (G : J → Matrix ι ι ℝ) (h : J → ι → ℝ) (ε : J → ℝ)
    (hG : ∀ j, (G j).PosDef) (hε : ∀ j, 0 ≤ ε j) : Convex ℝ (SafeSet G h ε) := by
  intro θ hθ ψ hψ α β hα hβ hsum j
  have hh := (coefficient_lower_concave (G j) (hG j) (h j) (ε j) (hε j)).2
    (Set.mem_univ θ) (Set.mem_univ ψ) hα hβ hsum
  have hn : 0 ≤ α * lower (G j) (h j) θ (ε j) + β * lower (G j) (h j) ψ (ε j) :=
    add_nonneg (mul_nonneg hα (hθ j)) (mul_nonneg hβ (hψ j))
  exact hn.trans hh

/-- The unchanged baseline is always in the shared subgroup-feasible set. -/
theorem zero_mem_safeSet (G : J → Matrix ι ι ℝ) (h : J → ι → ℝ) (ε : J → ℝ) :
    (0 : ι → ℝ) ∈ SafeSet G h ε := by
  intro j
  rw [lower_zero]

/-- On simultaneous confidence coverage every certified subgroup's true gain is nonnegative. -/
theorem simultaneous_safety (G : J → Matrix ι ι ℝ) (h r : J → ι → ℝ) (ε : J → ℝ)
    (hG : ∀ j, (G j).PosDef) (hr : ∀ j, signal (G j) (r j - h j) ≤ ε j)
    (θ : ι → ℝ) (hθ : θ ∈ SafeSet G h ε) : ∀ j, 0 ≤ gain (G j) θ (r j) := by
  intro j
  exact (hθ j).trans (true_gain_lower (G j) (hG j) (h j) (r j) θ (ε j) (hr j))

end Descent.Portability.SubgroupRepairGeometry
