/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.AugmentedAuditLaw
import Descent.Portability.GramSafeRepair

assert_below Descent.Decision Descent.Program

/-!
Decision-Directed Portability, Theorems 1 and 11 and the deterministic risk
conclusion of Corollary 13. Actual outcome-law integrals generate the frame
risks and residual correlations. The Gram matrix is computed from the fixed
features. The repair certificate therefore applies to expected squared loss,
with finite second moments ensuring the separate risks are defined.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.DecisionLossContrasts

open MeasureTheory ProbabilityTheory Matrix AugmentedAuditLaw
open scoped BigOperators

/-- A Bregman expression, with its slope supplied explicitly. -/
noncomputable def bregman (F D : ℝ → ℝ) (y f : ℝ) : ℝ :=
  F y - F f - D f * (y - f)

/-- The outcome-only term cancels without requiring any moment of that term. -/
theorem bregman_difference (F D : ℝ → ℝ) (y f₀ f₁ : ℝ) :
    bregman F D y f₀ - bregman F D y f₁ =
      F f₁ - f₁ * D f₁ - F f₀ + f₀ * D f₀ + (D f₁ - D f₀) * y := by
  unfold bregman
  ring

/-- The paired squared-loss gain is affine in the outcome. -/
theorem squared_loss_difference (y f d : ℝ) :
    (y - f) ^ 2 - (y - f - d) ^ 2 = 2 * d * (y - f) - d ^ 2 := by
  ring

/-- Every binary fixed-action contrast is exactly affine in the label. -/
theorem binary_contrast (c : Bool → ℝ) (y : Bool) :
    c y = c false + (c true - c false) * (if y then (1 : ℝ) else 0) := by
  cases y <;> simp

/-- A finite first moment already makes the paired squared-loss contrast integrable. -/
theorem paired_gain_integrable (μ : Measure ℝ) [IsProbabilityMeasure μ] (f d : ℝ)
    (hY : Integrable (fun y : ℝ ↦ y) μ) :
    Integrable (fun y ↦ (y - f) ^ 2 - (y - f - d) ^ 2) μ := by
  simp only [squared_loss_difference]
  exact ((hY.sub (integrable_const f)).const_mul (2 * d)).sub (integrable_const (d ^ 2))

/-- The difference of the two genuine finite risks depends only on the outcome mean. -/
theorem expected_gain (μ : Measure ℝ) [IsProbabilityMeasure μ] (f d : ℝ)
    (hY : MemLp (fun y : ℝ ↦ y) 2 μ) :
    (∫ y, (y - f) ^ 2 ∂μ) - (∫ y, (y - (f + d)) ^ 2 ∂μ) =
      2 * d * ((∫ y, y ∂μ) - f) - d ^ 2 := by
  have h₀ := affine_second μ 1 (-f) hY
  have h₁ := affine_second μ 1 (-(f + d)) hY
  simp only [one_mul, one_pow, ← sub_eq_add_neg] at h₀ h₁
  rw [h₀, h₁]
  ring

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]

/-- Expected squared loss on the supplied finite frame; normalized weights give frame risk. -/
noncomputable def frameRisk (μ : ι → Measure ℝ) (w f : ι → ℝ) : ℝ :=
  ∑ i, w i * ∫ y, (y - f i) ^ 2 ∂μ i

/-- The observed-feature Gram matrix, computed without outcome labels. -/
noncomputable def gram (w : ι → ℝ) (φ : ι → κ → ℝ) : Matrix κ κ ℝ :=
  ∑ i, w i • vecMulVec (φ i) (φ i)

/-- The target residual-correlation vector, computed from the actual outcome laws. -/
noncomputable def residual (μ : ι → Measure ℝ) (w f : ι → ℝ) (φ : ι → κ → ℝ) : κ → ℝ :=
  ∑ i, (w i * ((∫ y, y ∂μ i) - f i)) • φ i

/-- A correction in the fixed feature span. -/
noncomputable def predict (f : ι → ℝ) (φ : ι → κ → ℝ) (θ : κ → ℝ) : ι → ℝ :=
  fun i ↦ f i + φ i ⬝ᵥ θ

/-- The computed Gram quadratic form is the average squared correction. -/
theorem gram_quadratic (w : ι → ℝ) (φ : ι → κ → ℝ) (θ : κ → ℝ) :
    θ ⬝ᵥ (gram w φ *ᵥ θ) = ∑ i, w i * (φ i ⬝ᵥ θ) ^ 2 := by
  unfold gram
  rw [sum_mulVec, dotProduct_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [smul_mulVec, vecMulVec_mulVec, dotProduct_smul, dotProduct_smul]
  rw [dotProduct_comm θ (φ i)]
  simp only [smul_eq_mul, op_smul_eq_mul]
  ring

/-- The computed residual vector gives exactly the linear correction term in the gain. -/
theorem residual_pairing (μ : ι → Measure ℝ) (w f : ι → ℝ)
    (φ : ι → κ → ℝ) (θ : κ → ℝ) :
    θ ⬝ᵥ residual μ w f φ =
      ∑ i, w i * (φ i ⬝ᵥ θ) * ((∫ y, y ∂μ i) - f i) := by
  unfold residual
  rw [dotProduct_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [dotProduct_smul, dotProduct_comm θ (φ i)]
  simp only [smul_eq_mul]
  ring

/-- The matrix gain is derived from finite-frame expected risk, not assumed as a risk model. -/
theorem frame_gain (μ : ι → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    (w f : ι → ℝ) (φ : ι → κ → ℝ) (θ : κ → ℝ)
    (hY : ∀ i, MemLp (fun y : ℝ ↦ y) 2 (μ i)) :
    frameRisk μ w f - frameRisk μ w (predict f φ θ) =
      GramSafeRepair.gain (gram w φ) θ (residual μ w f φ) := by
  unfold frameRisk predict GramSafeRepair.gain
  rw [gram_quadratic, residual_pairing, ← Finset.sum_sub_distrib, Finset.mul_sum,
    ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [← mul_sub, expected_gain (μ i) (f i) (φ i ⬝ᵥ θ) (hY i)]
  ring

/-- An honest confidence event yields the stated improvement in actual frame expected loss. -/
theorem frame_repair_certificate (μ : ι → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    (w f : ι → ℝ) (φ : ι → κ → ℝ) (h : κ → ℝ) (ε : ℝ)
    (hY : ∀ i, MemLp (fun y : ℝ ↦ y) 2 (μ i)) (hG : (gram w φ).PosDef)
    (hε : 0 ≤ ε) (hr : GramSafeRepair.signal (gram w φ) (residual μ w f φ - h) ≤ ε) :
    max 0 (GramSafeRepair.signal (gram w φ) h - ε) ^ 2 ≤
      frameRisk μ w f -
        frameRisk μ w (predict f φ (GramSafeRepair.repair (gram w φ) h ε)) := by
  rw [frame_gain μ w f φ _ hY]
  exact (GramSafeRepair.repair_certificate (gram w φ) hG h (residual μ w f φ) ε hε hr).1

end Descent.Portability.DecisionLossContrasts
