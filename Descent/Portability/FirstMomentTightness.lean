/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.TightAlgebraConvergence

assert_below Descent.Decision Descent.Program

/-!
Uniform integrable first absolute moments give tightness of real probability
laws. This permits rare-event count limits without assuming their second moments.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.FirstMomentTightness

open scoped Topology ENNReal
open Filter MeasureTheory

/-- The first-moment bound supplies an explicit compact interval by Markov's inequality. -/
theorem tight_of_first_moment_bound {ι : Type*} (μ : ι → ProbabilityMeasure ℝ)
    (B : ℝ) (hB : 0 ≤ B)
    (hI : ∀ i, Integrable (fun x : ℝ ↦ |x|) (μ i : Measure ℝ))
    (hbound : ∀ i, ∫ x : ℝ, |x| ∂(μ i : Measure ℝ) ≤ B) :
    IsTightMeasureSet (Set.range (fun i ↦ (μ i : Measure ℝ))) := by
  apply IsTightMeasureSet_iff_exists_isCompact_measure_compl_le.mpr
  intro ε hε
  by_cases htop : ε = ∞
  · exact ⟨∅, isCompact_empty, fun _ _ ↦ by simp [htop]⟩
  let δ := ε.toReal
  have hδ : 0 < δ := ENNReal.toReal_pos hε.ne' htop
  let R := B / δ + 1
  have hR : 0 < R := by dsimp [R]; positivity
  have hbig : B < δ * R := by
    dsimp [R]
    rw [mul_add, mul_div_cancel₀ _ hδ.ne', mul_one]
    linarith
  refine ⟨Metric.closedBall 0 R, isCompact_closedBall _ _, ?_⟩
  rintro P ⟨i, rfl⟩
  have hm := mul_meas_ge_le_integral_of_nonneg
    (Filter.Eventually.of_forall (fun x : ℝ ↦ abs_nonneg x)) (hI i) R
  have hreal : (μ i : Measure ℝ).real {x : ℝ | R ≤ |x|} ≤ δ := by
    nlinarith [hbound i]
  have hsub : (Metric.closedBall (0 : ℝ) R)ᶜ ⊆ {x : ℝ | R ≤ |x|} := by
    intro x hx
    have hx' : R < |x| := by
      simpa only [Set.mem_compl_iff, Metric.mem_closedBall, dist_zero_right,
        Real.norm_eq_abs, not_le] using hx
    exact hx'.le
  apply (measure_mono hsub).trans
  apply (ENNReal.toReal_le_toReal (measure_ne_top _ _) htop).mp
  exact hreal

end Descent.Portability.FirstMomentTightness
