/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.NestedRepairSpans
import Descent.Portability.MeanDriftRepair
import Mathlib.Analysis.InnerProductSpace.PiL2

assert_below Descent.Decision Descent.Program

/-!
Decision-Directed Portability, Proposition 21, connected to actual outcome
laws and normalized expected frame risks. The phenotype means need not
belong to either correction span. Both oracle corrections are actual
orthogonal projections of the residual means, and their expected-loss
difference equals the exact value of the added orthogonal directions.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.FrameRepairSpans

open MeasureTheory DecisionLossContrasts
open scoped BigOperators RealInnerProductSpace

variable {ι : Type*} [Fintype ι] [Nonempty ι]

/-- Actual mean residuals in the Euclidean space of complete frame vectors. -/
noncomputable def meanResidual (μ : ι → Measure ℝ) (f : ι → ℝ) : EuclideanSpace ℝ ι :=
  WithLp.toLp 2 (fun i ↦ (∫ y, y ∂μ i) - f i)

/-- Expected squared-error gain on the normalized target frame. -/
noncomputable def frameGain (μ : ι → Measure ℝ) (f : ι → ℝ) (d : EuclideanSpace ℝ ι) : ℝ :=
  MeanDriftRepair.gain μ (fun _ ↦ 1 / Fintype.card ι) f (WithLp.ofLp d)

/-- The normalized squared norm defining recoverable signal on the target frame. -/
noncomputable def frameNormSq (d : EuclideanSpace ℝ ι) : ℝ := ‖d‖ ^ 2 / Fintype.card ι

/-- The Hilbert-space gain is obtained from the separate actual expected frame losses. -/
theorem frame_gain_identity (μ : ι → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    (f : ι → ℝ) (d : EuclideanSpace ℝ ι)
    (hY : ∀ i, MemLp (fun y : ℝ ↦ y) 2 (μ i)) :
    frameGain μ f d = SafeRepairGeometry.gain d (meanResidual μ f) / Fintype.card ι := by
  rw [frameGain, MeanDriftRepair.gain_identity μ _ f _ hY]
  unfold SafeRepairGeometry.gain
  rw [EuclideanSpace.inner_eq_star_dotProduct, EuclideanSpace.norm_sq_eq]
  simp only [meanResidual, WithLp.ofLp_toLp, star_trivial, dotProduct,
    Real.norm_eq_abs, sq_abs, PiLp.ofLp_apply]
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Every fixed correction span has an oracle attaining its full prospective frame gain. -/
theorem frame_oracle_attained (μ : ι → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    (f : ι → ℝ) (V : Submodule ℝ (EuclideanSpace ℝ ι))
    (hY : ∀ i, MemLp (fun y : ℝ ↦ y) 2 (μ i)) :
    frameGain μ f (V.starProjection (meanResidual μ f)) =
        frameNormSq (V.starProjection (meanResidual μ f)) ∧
      IsGreatest {v : ℝ | ∃ d ∈ V, frameGain μ f d = v}
        (frameNormSq (V.starProjection (meanResidual μ f))) := by
  obtain ⟨he, hmax⟩ := NestedRepairSpans.oracle_attained V (meanResidual μ f)
  have hN : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have he' : frameGain μ f (V.starProjection (meanResidual μ f)) =
      frameNormSq (V.starProjection (meanResidual μ f)) := by
    rw [frame_gain_identity μ f _ hY, he]
    rfl
  refine ⟨he', ⟨⟨V.starProjection (meanResidual μ f), V.starProjection_apply_mem _, he'⟩, ?_⟩⟩
  rintro v ⟨d, hd, rfl⟩
  rw [frame_gain_identity μ f d hY]
  exact div_le_div_of_nonneg_right (hmax.2 ⟨d, hd, rfl⟩) hN.le

/-- Adding correction directions has an exact value in actual expected-loss improvements. -/
theorem frame_oracle_increment (μ : ι → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    (f : ι → ℝ) (V U : Submodule ℝ (EuclideanSpace ℝ ι)) (hVU : V ≤ U)
    (hY : ∀ i, MemLp (fun y : ℝ ↦ y) 2 (μ i)) :
    frameGain μ f (U.starProjection (meanResidual μ f)) -
        frameGain μ f (V.starProjection (meanResidual μ f)) =
      frameNormSq ((U ⊓ Vᗮ).starProjection (meanResidual μ f)) := by
  rw [(frame_oracle_attained μ f U hY).1, (frame_oracle_attained μ f V hY).1]
  unfold frameNormSq
  rw [← sub_div, NestedRepairSpans.oracle_increment V U hVU]

/-- Enlarging a span cannot reduce the actual oracle's prospective expected gain. -/
theorem frame_oracle_monotone (μ : ι → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    (f : ι → ℝ) (V U : Submodule ℝ (EuclideanSpace ℝ ι)) (hVU : V ≤ U)
    (hY : ∀ i, MemLp (fun y : ℝ ↦ y) 2 (μ i)) :
    frameGain μ f (V.starProjection (meanResidual μ f)) ≤
      frameGain μ f (U.starProjection (meanResidual μ f)) := by
  have he := frame_oracle_increment μ f V U hVU hY
  have hn : 0 ≤ frameNormSq ((U ⊓ Vᗮ).starProjection (meanResidual μ f)) :=
    div_nonneg (sq_nonneg _) (Nat.cast_nonneg _)
  linarith

end Descent.Portability.FrameRepairSpans
