/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.DecisionLossContrasts

assert_below Descent.Decision Descent.Program

/-!
Decision-Directed Portability, Theorem 1 at the level of actual expectations.
The paired Bregman contrast is integrable under a finite first moment and
depends only on the outcome mean. When both separate risks exist their
difference has the same value. These statements do not subtract undefined
infinite risks. Binary fixed-action loss contrasts are treated directly too.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.BregmanAuditContrasts

open MeasureTheory DecisionLossContrasts

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The paired Bregman contrast is integrable under only a finite first outcome moment. -/
theorem contrast_integrable (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Y : Ω → ℝ) (hY : Integrable Y μ) (F D : ℝ → ℝ) (f₀ f₁ : ℝ) :
    Integrable (fun ω ↦ bregman F D (Y ω) f₀ - bregman F D (Y ω) f₁) μ := by
  simp only [bregman_difference]
  exact (integrable_const _).add (hY.const_mul _)

/-- The actual expected paired contrast depends on the outcome law only through its mean. -/
theorem expected_contrast (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Y : Ω → ℝ) (hY : Integrable Y μ) (F D : ℝ → ℝ) (f₀ f₁ : ℝ) :
    (∫ ω, bregman F D (Y ω) f₀ - bregman F D (Y ω) f₁ ∂μ) =
      F f₁ - f₁ * D f₁ - F f₀ + f₀ * D f₀ + (D f₁ - D f₀) * ∫ ω, Y ω ∂μ := by
  simp only [bregman_difference]
  rw [integral_add (integrable_const _) (hY.const_mul _), integral_const_mul, integral_const]
  simp

/-- Finite separate Bregman risks have exactly the same mean-based difference. -/
theorem expected_risk_difference (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Y : Ω → ℝ) (hY : Integrable Y μ) (F D : ℝ → ℝ) (f₀ f₁ : ℝ)
    (h₀ : Integrable (fun ω ↦ bregman F D (Y ω) f₀) μ)
    (h₁ : Integrable (fun ω ↦ bregman F D (Y ω) f₁) μ) :
    (∫ ω, bregman F D (Y ω) f₀ ∂μ) - (∫ ω, bregman F D (Y ω) f₁ ∂μ) =
      F f₁ - f₁ * D f₁ - F f₀ + f₀ * D f₀ + (D f₁ - D f₀) * ∫ ω, Y ω ∂μ := by
  rw [← integral_sub h₀ h₁]
  exact expected_contrast μ Y hY F D f₀ f₁

/-- Equal outcome means give equal expected contrasts even when the outcome distributions differ. -/
theorem same_mean_contrast (μ ν : Measure Ω) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (Y Z : Ω → ℝ) (hY : Integrable Y μ) (hZ : Integrable Z ν)
    (F D : ℝ → ℝ) (f₀ f₁ : ℝ) (hm : (∫ ω, Y ω ∂μ) = ∫ ω, Z ω ∂ν) :
    (∫ ω, bregman F D (Y ω) f₀ - bregman F D (Y ω) f₁ ∂μ) =
      ∫ ω, bregman F D (Z ω) f₀ - bregman F D (Z ω) f₁ ∂ν := by
  rw [expected_contrast μ Y hY, expected_contrast ν Z hZ, hm]

/-- Every binary fixed-action contrast is affine in the actual positive-label probability. -/
theorem binary_expected_contrast (μ : Measure Bool) [IsProbabilityMeasure μ] (c : Bool → ℝ) :
    (∫ b, c b ∂μ) = c false + (c true - c false) * μ.real {true} := by
  have he : c = fun b ↦ c false + (c true - c false) * (if b then (1 : ℝ) else 0) := by
    funext b
    exact binary_contrast c b
  calc
    (∫ b, c b ∂μ) = ∫ b, c false + (c true - c false) *
        (if b then (1 : ℝ) else 0) ∂μ := congrArg (fun f ↦ ∫ b, f b ∂μ) he
    _ = _ := by
      rw [integral_add (integrable_const _) Integrable.of_finite, integral_const_mul,
        integral_const]
      have hu : ({false, true} : Set Bool) = Set.univ := by
        ext b
        cases b <;> simp
      simp [integral_fintype, hu]

end Descent.Portability.BregmanAuditContrasts
