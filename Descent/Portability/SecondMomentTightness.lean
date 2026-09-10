/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.TightAlgebraConvergence

assert_below Descent.Decision Descent.Program

/-!
A common finite second-moment bound supplies tightness of an actual family of
real probability measures. The compact set is explicit and the proof applies
Markov's inequality to the squared coordinate.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.SecondMomentTightness

open scoped Topology ENNReal
open Filter MeasureTheory

/-- Uniform second moments force uniform concentration on compact intervals. -/
theorem tight_of_second_moment_bound {ι : Type*} (μ : ι → ProbabilityMeasure ℝ)
    (B : ℝ) (hB : 0 ≤ B)
    (hI : ∀ i, Integrable (fun x : ℝ ↦ x ^ 2) (μ i : Measure ℝ))
    (hbound : ∀ i, ∫ x : ℝ, x ^ 2 ∂(μ i : Measure ℝ) ≤ B) :
    IsTightMeasureSet (Set.range (fun i ↦ (μ i : Measure ℝ))) := by
  apply IsTightMeasureSet_iff_exists_isCompact_measure_compl_le.mpr
  intro ε hε
  by_cases htop : ε = ∞
  · exact ⟨∅, isCompact_empty, fun _ _ ↦ by simp [htop]⟩
  let δ := ε.toReal
  have hδ : 0 < δ := ENNReal.toReal_pos hε.ne' htop
  let R := Real.sqrt (B / δ + 1)
  have hR : 0 < R := by dsimp [R]; positivity
  have hs : R ^ 2 = B / δ + 1 := Real.sq_sqrt (by positivity)
  have hbig : B < δ * R ^ 2 := by
    rw [hs, mul_add, mul_div_cancel₀ _ hδ.ne', mul_one]
    linarith
  refine ⟨Metric.closedBall 0 R, isCompact_closedBall _ _, ?_⟩
  rintro P ⟨i, rfl⟩
  have hm := mul_meas_ge_le_integral_of_nonneg
    (Filter.Eventually.of_forall (fun x : ℝ ↦ sq_nonneg x)) (hI i) (R ^ 2)
  have hreal : (μ i : Measure ℝ).real {x : ℝ | R ^ 2 ≤ x ^ 2} ≤ δ := by
    have hR2 : 0 < R ^ 2 := sq_pos_of_pos hR
    nlinarith [hbound i]
  have hsub : (Metric.closedBall (0 : ℝ) R)ᶜ ⊆ {x : ℝ | R ^ 2 ≤ x ^ 2} := by
    intro x hx
    have hx' : R < |x| := by
      simpa only [Set.mem_compl_iff, Metric.mem_closedBall, dist_zero_right,
        Real.norm_eq_abs, not_le] using hx
    have hh := (sq_le_sq₀ hR.le (abs_nonneg x)).mpr hx'.le
    simpa only [sq_abs] using hh
  apply (measure_mono hsub).trans
  apply (ENNReal.toReal_le_toReal (measure_ne_top _ _) htop).mp
  exact hreal

end Descent.Portability.SecondMomentTightness
