/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
import Mathlib.MeasureTheory.Function.L2Space
import Descent.Layer

assert_below Descent.Decision Descent.Program

/-!
The research report's nonlinear risk decomposition on arbitrary probability
spaces and nested sigma fields. Conditional means are Mathlib conditional
expectations, not supplied finite-cell averages or postulated orthogonality.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.ReportConditionalRiskLaw

open MeasureTheory

variable {Ω : Type*} {m₀ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {m : MeasurableSpace Ω} {Y g : Ω → ℝ}

/-- A square-integrable conditional-mean residual is orthogonal to every
square-integrable predictor measurable in the retained information. -/
theorem residual_orthogonal (hm : m ≤ m₀) (hY : MemLp Y 2 μ) (hg : MemLp g 2 μ)
    (hgm : StronglyMeasurable[m] g) :
    (∫ ω, (Y ω - μ[Y | m] ω) * g ω ∂μ) = 0 := by
  have hr : MemLp (Y - μ[Y | m]) 2 μ := hY.sub hY.condExp
  have hri : Integrable (Y - μ[Y | m]) μ := hr.integrable (by norm_num)
  have hp := condExp_mul_of_stronglyMeasurable_right hgm (hr.integrable_mul hg) hri
  have hc : μ[Y - μ[Y | m] | m] =ᵐ[μ] (fun _ ↦ 0) := by
    have hs := condExp_sub (hY.integrable (by norm_num))
      (integrable_condExp (f := Y) (m := m)) m
    have he : μ[μ[Y | m] | m] = μ[Y | m] :=
      condExp_of_stronglyMeasurable hm stronglyMeasurable_condExp integrable_condExp
    simpa only [he, sub_self] using hs
  have hz : μ[(Y - μ[Y | m]) * g | m] =ᵐ[μ] (fun _ ↦ 0) := by
    filter_upwards [hp, hc] with ω hω hcω
    simpa only [Pi.mul_apply, hcω, zero_mul] using hω
  calc
    (∫ ω, (Y ω - μ[Y | m] ω) * g ω ∂μ) =
        ∫ ω, μ[(Y - μ[Y | m]) * g | m] ω ∂μ := (integral_condExp hm).symm
    _ = 0 := by rw [integral_congr_ae hz]; simp

/-- Conditional-mean Pythagoras, with all product integrability derived from L². -/
theorem risk_pythagoras (hm : m ≤ m₀) (hY : MemLp Y 2 μ) (hg : MemLp g 2 μ)
    (hgm : StronglyMeasurable[m] g) :
    (∫ ω, (Y ω - g ω) ^ 2 ∂μ) =
      (∫ ω, (Y ω - μ[Y | m] ω) ^ 2 ∂μ) +
        ∫ ω, (μ[Y | m] ω - g ω) ^ 2 ∂μ := by
  have hr : MemLp (Y - μ[Y | m]) 2 μ := hY.sub hY.condExp
  have hd : MemLp (μ[Y | m] - g) 2 μ := hY.condExp.sub hg
  have ho := residual_orthogonal hm hY hd (stronglyMeasurable_condExp.sub hgm)
  simp only [Pi.sub_apply] at ho
  have he (ω : Ω) : (Y ω - g ω) ^ 2 = (Y ω - μ[Y | m] ω) ^ 2 +
      (μ[Y | m] ω - g ω) ^ 2 + 2 * ((Y ω - μ[Y | m] ω) *
        (μ[Y | m] ω - g ω)) := by ring
  simp_rw [he]
  rw [integral_add, integral_add, integral_const_mul, ho, mul_zero, add_zero]
  · exact hr.integrable_sq
  · exact hd.integrable_sq
  · exact hr.integrable_sq.add hd.integrable_sq
  · exact (hr.integrable_mul hd).const_mul 2

/-- Theorem 2 of the report: outcome noise, information discarded by a smaller
sigma field, and repairable conditional-mean error add exactly. -/
theorem nonlinear_risk_decomposition {mX mT : MeasurableSpace Ω}
    (hTX : mT ≤ mX) (hX : mX ≤ m₀) (hY : MemLp Y 2 μ) (hg : MemLp g 2 μ)
    (hgm : StronglyMeasurable[mT] g) :
    (∫ ω, (Y ω - g ω) ^ 2 ∂μ) =
      (∫ ω, (Y ω - μ[Y | mX] ω) ^ 2 ∂μ) +
      (∫ ω, (μ[Y | mX] ω - μ[Y | mT] ω) ^ 2 ∂μ) +
        ∫ ω, (μ[Y | mT] ω - g ω) ^ 2 ∂μ := by
  rw [risk_pythagoras hX hY hg (hgm.mono hTX)]
  have hp := risk_pythagoras (hTX.trans hX) (hY.condExp (m := mX)) hg hgm
  have ht : μ[μ[Y | mX] | mT] =ᵐ[μ] μ[Y | mT] := condExp_condExp_of_le hTX hX
  have hfirst : (∫ ω, (μ[Y | mX] ω - μ[μ[Y | mX] | mT] ω) ^ 2 ∂μ) =
      ∫ ω, (μ[Y | mX] ω - μ[Y | mT] ω) ^ 2 ∂μ := by
    apply integral_congr_ae
    filter_upwards [ht] with ω hω
    rw [hω]
  have hsecond : (∫ ω, (μ[μ[Y | mX] | mT] ω - g ω) ^ 2 ∂μ) =
      ∫ ω, (μ[Y | mT] ω - g ω) ^ 2 ∂μ := by
    apply integral_congr_ae
    filter_upwards [ht] with ω hω
    rw [hω]
  rw [hfirst, hsecond] at hp
  rw [hp, add_assoc]

/-- The conditional-mean predictor minimizes risk on the retained sigma field. -/
theorem conditional_mean_minimizes (hm : m ≤ m₀) (hY : MemLp Y 2 μ)
    (hg : MemLp g 2 μ) (hgm : StronglyMeasurable[m] g) :
    (∫ ω, (Y ω - μ[Y | m] ω) ^ 2 ∂μ) ≤ ∫ ω, (Y ω - g ω) ^ 2 ∂μ := by
  rw [risk_pythagoras hm hY hg hgm]
  exact le_add_of_nonneg_right (integral_nonneg (fun _ ↦ sq_nonneg _))

/-- The same identity in the report's expected-conditional-variance notation. -/
theorem nonlinear_risk_decomposition_conditional_variance {mX mT : MeasurableSpace Ω}
    (hTX : mT ≤ mX) (hX : mX ≤ m₀) (hY : MemLp Y 2 μ) (hg : MemLp g 2 μ)
    (hgm : StronglyMeasurable[mT] g) :
    (∫ ω, (Y ω - g ω) ^ 2 ∂μ) =
      (∫ ω, μ[(fun x ↦ (Y x - μ[Y | mX] x) ^ 2) | mX] ω ∂μ) +
      (∫ ω, (μ[Y | mX] ω - μ[Y | mT] ω) ^ 2 ∂μ) +
        ∫ ω, (μ[Y | mT] ω - g ω) ^ 2 ∂μ := by
  rw [integral_condExp hX]
  exact nonlinear_risk_decomposition hTX hX hY hg hgm

end Descent.Portability.ReportConditionalRiskLaw
