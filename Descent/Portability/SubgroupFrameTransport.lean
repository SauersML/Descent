/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.SubgroupRepairGeometry
import Descent.Portability.FrameOutcomeMeasure

assert_below Descent.Decision Descent.Program

/-!
Decision-Directed Portability, Theorem 22, with actual frame outcome laws.
The Gram matrices and residual vectors are calculated from the registered
subgroup weights, features, and phenotype kernels. The same coefficient
vector is safe in every certified subgroup and under every mixture of
these unchanged joint laws. Weighted lower-gain optimization is concave
on the shared convex feasible set and the baseline remains feasible.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.SubgroupFrameTransport

open Matrix MeasureTheory DecisionLossContrasts SubgroupRepairGeometry
open scoped BigOperators

variable {ι κ J : Type*} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
variable [Fintype κ] [DecidableEq κ] [Fintype J]

/-- A nonnegative weighted sum of subgroup lower gains is a concave optimization objective. -/
theorem weighted_objective_concave (G : J → Matrix κ κ ℝ) (h : J → κ → ℝ)
    (ε π : J → ℝ) (hG : ∀ j, (G j).PosDef) (hε : ∀ j, 0 ≤ ε j) (hπ : ∀ j, 0 ≤ π j) :
    ConcaveOn ℝ Set.univ (fun θ : κ → ℝ ↦ ∑ j, π j * lower (G j) (h j) θ (ε j)) := by
  refine ⟨convex_univ, ?_⟩
  intro θ _ ψ _ α β hα hβ hsum
  change α * (∑ j, π j * lower (G j) (h j) θ (ε j)) +
    β * (∑ j, π j * lower (G j) (h j) ψ (ε j)) ≤ _
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro j _
  have hh := (coefficient_lower_concave (G j) (hG j) (h j) (ε j) (hε j)).2
    (Set.mem_univ θ) (Set.mem_univ ψ) hα hβ hsum
  have hmul := mul_le_mul_of_nonneg_left hh (hπ j)
  simp only [smul_eq_mul] at hmul
  convert hmul using 1 <;> ring

/-- On simultaneous confidence coverage the shared subgroup certificate bounds actual frame risk. -/
theorem group_frame_lower (μ : ι → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    (w : J → ι → ℝ) (f : ι → ℝ) (φ : ι → κ → ℝ) (h : J → κ → ℝ) (ε : J → ℝ)
    (hY : ∀ i, MemLp (fun y : ℝ ↦ y) 2 (μ i))
    (hG : ∀ j, (gram (w j) φ).PosDef)
    (hr : ∀ j, GramSafeRepair.signal (gram (w j) φ) (residual μ (w j) f φ - h j) ≤ ε j)
    (θ : κ → ℝ) (j : J) :
    lower (gram (w j) φ) (h j) θ (ε j) ≤
      frameRisk μ (w j) f - frameRisk μ (w j) (predict f φ θ) := by
  rw [frame_gain μ (w j) f φ θ hY]
  exact true_gain_lower (gram (w j) φ) (hG j) (h j) (residual μ (w j) f φ) θ (ε j) (hr j)

/-- Every certified subgroup improves or preserves its actual prospective expected squared loss. -/
theorem group_frame_safety (μ : ι → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    (w : J → ι → ℝ) (f : ι → ℝ) (φ : ι → κ → ℝ) (h : J → κ → ℝ) (ε : J → ℝ)
    (hY : ∀ i, MemLp (fun y : ℝ ↦ y) 2 (μ i))
    (hG : ∀ j, (gram (w j) φ).PosDef)
    (hr : ∀ j, GramSafeRepair.signal (gram (w j) φ) (residual μ (w j) f φ - h j) ≤ ε j)
    (θ : κ → ℝ) (hθ : θ ∈ SafeSet (fun j ↦ gram (w j) φ) h ε) :
    ∀ j, frameRisk μ (w j) (predict f φ θ) ≤ frameRisk μ (w j) f := by
  intro j
  have hh := (hθ j).trans (group_frame_lower μ w f φ h ε hY hG hr θ j)
  linarith

/-- Actual subgroup joint laws reproduce the Gram gain of the shared coefficient correction. -/
theorem joint_group_gain (μ : ι → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    (w f : ι → ℝ) (φ : ι → κ → ℝ) (θ : κ → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hY : ∀ i, MemLp (fun y : ℝ ↦ y) 2 (μ i)) :
    FiniteMixtureRepair.gain (FrameOutcomeMeasure.frameLaw μ w) Prod.snd
      (fun z ↦ f z.1) (fun z ↦ φ z.1 ⬝ᵥ θ) =
      GramSafeRepair.gain (gram w φ) θ (residual μ w f φ) := by
  rw [FrameOutcomeMeasure.expected_gain μ w f (fun i ↦ φ i ⬝ᵥ θ) hw hY]
  exact frame_gain μ w f φ θ hY

/-- The weighted lower certificate bounds gain under the actual mixture of subgroup joint laws. -/
theorem mixture_lower_bound (μ : ι → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    (w : J → ι → ℝ) (f : ι → ℝ) (φ : ι → κ → ℝ) (h : J → κ → ℝ) (ε π : J → ℝ)
    (hw : ∀ j i, 0 ≤ w j i) (hπ : ∀ j, 0 ≤ π j)
    (hY : ∀ i, MemLp (fun y : ℝ ↦ y) 2 (μ i))
    (hG : ∀ j, (gram (w j) φ).PosDef)
    (hr : ∀ j, GramSafeRepair.signal (gram (w j) φ) (residual μ (w j) f φ - h j) ≤ ε j)
    (θ : κ → ℝ) :
    (∑ j, π j * lower (gram (w j) φ) (h j) θ (ε j)) ≤
      FiniteMixtureRepair.gain
        (FiniteMixtureRepair.mixture π (fun j ↦ FrameOutcomeMeasure.frameLaw μ (w j)))
        Prod.snd (fun z ↦ f z.1) (fun z ↦ φ z.1 ⬝ᵥ θ) := by
  rw [FiniteMixtureRepair.mixture_gain π _ Prod.snd (fun z ↦ f z.1)
    (fun z ↦ φ z.1 ⬝ᵥ θ) hπ
    (fun j ↦ FrameOutcomeMeasure.frame_loss_integrable μ (w j) f hY)
    (fun j ↦ FrameOutcomeMeasure.frame_loss_integrable μ (w j) (predict f φ θ) hY)]
  apply Finset.sum_le_sum
  intro j _
  rw [joint_group_gain μ (w j) f φ θ (hw j) hY]
  exact mul_le_mul_of_nonneg_left
    (true_gain_lower (gram (w j) φ) (hG j) (h j) (residual μ (w j) f φ) θ (ε j) (hr j)) (hπ j)

/-- Every mixture of unchanged registered subgroup laws inherits the shared safety guarantee. -/
theorem certified_mixture_transport (μ : ι → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    (w : J → ι → ℝ) (f : ι → ℝ) (φ : ι → κ → ℝ) (h : J → κ → ℝ) (ε π : J → ℝ)
    (hw : ∀ j i, 0 ≤ w j i) (hwSum : ∀ j, ∑ i, w j i = 1)
    (hπ : ∀ j, 0 ≤ π j) (hπSum : ∑ j, π j = 1)
    (hY : ∀ i, MemLp (fun y : ℝ ↦ y) 2 (μ i))
    (hG : ∀ j, (gram (w j) φ).PosDef)
    (hr : ∀ j, GramSafeRepair.signal (gram (w j) φ) (residual μ (w j) f φ - h j) ≤ ε j)
    (θ : κ → ℝ) (hθ : θ ∈ SafeSet (fun j ↦ gram (w j) φ) h ε) :
    IsProbabilityMeasure
        (FiniteMixtureRepair.mixture π (fun j ↦ FrameOutcomeMeasure.frameLaw μ (w j))) ∧
      0 ≤ FiniteMixtureRepair.gain
        (FiniteMixtureRepair.mixture π (fun j ↦ FrameOutcomeMeasure.frameLaw μ (w j)))
        Prod.snd (fun z ↦ f z.1) (fun z ↦ φ z.1 ⬝ᵥ θ) := by
  letI (j : J) := FrameOutcomeMeasure.frame_probability μ (w j) (hw j) (hwSum j)
  refine ⟨FiniteMixtureRepair.mixture_probability π _ hπ hπSum, ?_⟩
  exact (Finset.sum_nonneg (fun j _ ↦ mul_nonneg (hπ j) (hθ j))).trans
    (mixture_lower_bound μ w f φ h ε π hw hπ hY hG hr θ)

end Descent.Portability.SubgroupFrameTransport
