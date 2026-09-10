/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.AncientPrediction.Correction
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.MeasureTheory.Function.L2Space

assert_below Descent.Decision Descent.Program

/-!
# Actual squared-error risk and correction moments

The correction operator maps coefficients to random score differences in L².
Its adjoint applied to the contemporary residual is the phenotype anchor.
This connects the quadratic geometry to an integral risk, rather than naming
an arbitrary polynomial a risk. Orthogonality assumptions are explicit.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.AncientPrediction

open MeasureTheory
open scoped RealInnerProductSpace

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- Feature second moments are a Gram form of the correction operator. -/
noncomputable def operatorMoment (C : E →L[ℝ] F) : FeatureMoment E where
  form := (innerₗ F).compl₁₂ C.toLinearMap C.toLinearMap
  symmetric x y := real_inner_comm (C y) (C x)
  nonneg x := real_inner_self_nonneg (x := C x)

/-- Exact risk accounting before imposing any generative ancient model. -/
theorem operator_risk_change [CompleteSpace E] [CompleteSpace F]
    (C : E →L[ℝ] F) (residual : F) (a : E) :
    ‖residual - C a‖ ^ 2 - ‖residual‖ ^ 2 =
      riskChange (C.adjoint residual) (operatorMoment C) a := by
  rw [norm_sub_sq_real]
  simp only [riskChange, operatorMoment, LinearMap.compl₁₂_apply,
    innerₗ_apply, ContinuousLinearMap.coe_coe, ContinuousLinearMap.adjoint_inner_left,
    real_inner_self_eq_norm_sq]
  ring

/-- In L², the Hilbert loss is the integral of the squared scalar residual. -/
theorem l2_squared_risk {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (r : Lp ℝ 2 μ) : ‖r‖ ^ 2 = ∫ ω, (r ω) ^ 2 ∂μ := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  simp only [real_inner_self_eq_norm_sq, Real.norm_eq_abs, sq_abs]

/-- Equation E1 for actual random predictions and arbitrary finite second
moments. Neither centered features nor a correct ancient model is required. -/
theorem integral_risk_change {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [CompleteSpace E] (C : E →L[ℝ] Lp ℝ 2 μ) (residual : Lp ℝ 2 μ) (a : E) :
    (∫ ω, ((residual - C a) ω) ^ 2 ∂μ) - (∫ ω, (residual ω) ^ 2 ∂μ) =
      riskChange (C.adjoint residual) (operatorMoment C) a := by
  rw [← l2_squared_risk, ← l2_squared_risk]
  exact operator_risk_change C residual a

/-- Projection form of Theorem 3: the price of an implemented richer predictor
is its squared discrepancy minus the squared information increment. For
conditional expectations, the two premises follow from L² orthogonality. -/
theorem information_gain_budget (Y m₀ m₁ f : F)
    (hgain : ⟪Y - m₁, m₁ - m₀⟫ = 0)
    (himpl : ⟪Y - m₁, f - m₁⟫ = 0) :
    ‖Y - f‖ ^ 2 - ‖Y - m₀‖ ^ 2 = ‖f - m₁‖ ^ 2 - ‖m₁ - m₀‖ ^ 2 := by
  have h₀ : Y - m₀ = (Y - m₁) + (m₁ - m₀) := by abel
  have hf : Y - f = (Y - m₁) - (f - m₁) := by abel
  rw [h₀, hf, norm_add_sq_real, norm_sub_sq_real, hgain, himpl]
  ring

/-- Clipping an affine binary-outcome prediction preserves any squared-risk
upper bound: projection onto the probability interval reduces pointwise loss. -/
theorem clipped_squared_error (y p : ℝ) (hy : y ∈ Set.Icc (0 : ℝ) 1) :
    (y - max 0 (min 1 p)) ^ 2 ≤ (y - p) ^ 2 := by
  rcases le_total p 0 with hp | hp
  · rw [min_eq_right (hp.trans zero_le_one), max_eq_left hp]
    nlinarith [hy.1]
  · rcases le_total p 1 with hp1 | hp1
    · rw [min_eq_right hp1, max_eq_right hp]
    · rw [min_eq_left hp1, max_eq_right zero_le_one]
      nlinarith [hy.2]

end Descent.Portability.AncientPrediction
