/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Topology.Order.Compact
import Descent.Layer

assert_below Descent.Decision Descent.Program

/-!
Differentiating a parameter integral on a fixed compact interval. Joint continuity
of the integrand and its parameter derivative supplies the required domination
bound by the extreme value theorem; no extra domination hypothesis is assumed.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.CompactParameterIntegralLaw

open MeasureTheory Set Filter Metric
open scoped Topology

/-- Jointly continuous parameter derivatives can be integrated on [0,1]. -/
theorem hasDerivAt_interval_integral (F F' : ℝ → ℝ → ℝ)
    (hF : Continuous (fun xt : ℝ × ℝ ↦ F xt.1 xt.2))
    (hF' : Continuous (fun xt : ℝ × ℝ ↦ F' xt.1 xt.2))
    (hd : ∀ x t, HasDerivAt (fun u ↦ F u t) (F' x t) x) (x₀ : ℝ) :
    HasDerivAt (fun x ↦ ∫ t in (0 : ℝ)..1, F x t)
      (∫ t in (0 : ℝ)..1, F' x₀ t) x₀ := by
  let μ := volume.restrict (Ioc (0 : ℝ) 1)
  have hFi (x : ℝ) : Continuous (F x) :=
    hF.comp (continuous_const.prodMk continuous_id)
  have hDi (x : ℝ) : Continuous (F' x) :=
    hF'.comp (continuous_const.prodMk continuous_id)
  have hcompact : IsCompact ((Icc (x₀ - 1) (x₀ + 1)) ×ˢ (Icc (0 : ℝ) 1)) :=
    isCompact_Icc.prod isCompact_Icc
  obtain ⟨M, hM⟩ := hcompact.bddAbove_image hF'.norm.continuousOn
  have hb : ∀ᵐ t ∂μ, ∀ x ∈ ball x₀ (1 : ℝ), ‖F' x t‖ ≤ M := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    intro x hx
    have hx' : x ∈ Icc (x₀ - 1) (x₀ + 1) := by
      rw [mem_ball, Real.dist_eq] at hx
      have h := abs_lt.mp hx
      constructor <;> linarith
    exact hM ⟨(x, t), ⟨hx', ⟨ht.1.le, ht.2⟩⟩, rfl⟩
  have hdiff : ∀ᵐ t ∂μ, ∀ x ∈ ball x₀ (1 : ℝ),
      HasDerivAt (fun u ↦ F u t) (F' x t) x := by
    filter_upwards [] with t
    exact fun x _ ↦ hd x t
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := μ) (F := F) (F' := F') (bound := fun _ ↦ M) (by norm_num : (0 : ℝ) < 1)
    (Eventually.of_forall (fun x ↦ (hFi x).aestronglyMeasurable))
    ((hFi x₀).intervalIntegrable (0 : ℝ) 1).1 (hDi x₀).aestronglyMeasurable hb
    (integrable_const M) hdiff
  simpa only [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)] using h.2

end Descent.Portability.CompactParameterIntegralLaw
