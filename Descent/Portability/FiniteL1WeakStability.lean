/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.FiniteCharacteristicL1
import Descent.Portability.FirstMomentTightness
import Descent.Portability.TightCharacteristicConvergence

assert_below Descent.Decision Descent.Program

/-!
Weak limits of varying finite experiments are stable under vanishing actual L1
perturbations. Tightness is derived from a convergent absolute first moment, and
the characteristic error is bounded using the shared finite experiment.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.FiniteL1WeakStability

open scoped BigOperators Topology BoundedContinuousFunction RealInnerProductSpace
open Filter MeasureTheory ProbabilityTheory BalancedHWEWeakLimit FiniteAtomicReportMeasure
open BoundedContinuousFunction
open FirstMomentTightness TightCharacteristicConvergence FiniteCharacteristicL1

noncomputable def reportProbability {α : Type*} [Fintype α]
    (p : FiniteReportLaw α) (z : α → ℝ) : ProbabilityMeasure ℝ :=
  ⟨finiteMeasure p z, inferInstance⟩

/-- Convergent absolute first moments give tightness without a supplied compactness claim. -/
theorem reports_tight {α : ℕ → Type*} [∀ m, Fintype (α m)]
    (p : (m : ℕ) → FiniteReportLaw (α m)) (z : (m : ℕ) → α m → ℝ) (B : ℝ)
    (hB : Tendsto (fun m ↦ (p m).expectation (fun x ↦ |z m x|)) atTop (𝓝 B)) :
    IsTightMeasureSet (Set.range (fun m ↦ (reportProbability (p m) (z m) : Measure ℝ))) := by
  obtain ⟨C, hC⟩ := (Metric.isBounded_range_of_tendsto _ hB).exists_norm_le
  apply tight_of_first_moment_bound _ (max 0 C) (le_max_left _ _)
  · intro m
    exact finite_report_integrable _ _ _
  · intro m
    change (∫ x : ℝ, |x| ∂finiteMeasure (p m) (z m)) ≤ _
    rw [integral_finite_report]
    exact ((le_abs_self _).trans (hC _ ⟨m, rfl⟩)).trans (le_max_right _ _)

/-- Vanishing L1 change preserves the actual weak limit. -/
theorem weak_limit_of_L1 {α : ℕ → Type*} [∀ m, Fintype (α m)]
    (p : (m : ℕ) → FiniteReportLaw (α m)) (z y : (m : ℕ) → α m → ℝ)
    (ν : ProbabilityMeasure ℝ)
    (hz : Tendsto (fun m ↦ reportProbability (p m) (z m)) atTop (𝓝 ν))
    (hL1 : Tendsto (fun m ↦ (p m).expectation (fun x ↦ |y m x - z m x|)) atTop (𝓝 0))
    (B : ℝ) (hB : Tendsto (fun m ↦ (p m).expectation (fun x ↦ |y m x|)) atTop (𝓝 B)) :
    Tendsto (fun m ↦ reportProbability (p m) (y m)) atTop (𝓝 ν) := by
  apply weak_convergence_of_tight_characteristic _ ν
  · have ht := (isTightMeasureSet_singleton (μ := (ν : Measure ℝ))).union
      (reports_tight p y B hB)
    simpa only [Set.singleton_union] using ht
  · intro t
    have hc := (ProbabilityMeasure.tendsto_iff_forall_integral_rclike_tendsto ℂ).mp hz
      (innerProbChar t)
    simp only [← charFun_eq_integral_innerProbChar] at hc
    have he : Tendsto (fun m ↦ charFun (reportProbability (p m) (y m) : Measure ℝ) t -
        charFun (reportProbability (p m) (z m) : Measure ℝ) t) atTop (𝓝 0) := by
      apply tendsto_zero_iff_norm_tendsto_zero.mpr
      have hb : Tendsto (fun m ↦ 2 * |t| * (p m).expectation
          (fun x ↦ |y m x - z m x|)) atTop (𝓝 0) := by
        simpa using hL1.const_mul (2 * |t|)
      apply squeeze_zero (fun m ↦ norm_nonneg _) ?_ hb
      intro m
      simpa only [reportProbability, ProbabilityMeasure.coe_mk, charFun_finite_report] using
        characteristic_difference (p m) (y m) (z m) t
    simpa only [sub_add_cancel, zero_add] using he.add hc

/-- Changing a scalar normalization to a convergent sequence preserves its expected weak limit. -/
theorem varying_scale_limit {α : ℕ → Type*} [∀ m, Fintype (α m)]
    (p : (m : ℕ) → FiniteReportLaw (α m)) (z : (m : ℕ) → α m → ℝ)
    (a : ℕ → ℝ) (c : ℝ) (ha : Tendsto a atTop (𝓝 c)) (B : ℝ)
    (hB : Tendsto (fun m ↦ (p m).expectation (fun x ↦ |z m x|)) atTop (𝓝 B))
    (ν : ProbabilityMeasure ℝ)
    (hz : Tendsto (fun m ↦ reportProbability (p m) (fun x ↦ c * z m x)) atTop (𝓝 ν)) :
    Tendsto (fun m ↦ reportProbability (p m) (fun x ↦ a m * z m x)) atTop (𝓝 ν) := by
  have he (m : ℕ) (d : ℝ) : (p m).expectation (fun x ↦ |d * z m x|) =
      |d| * (p m).expectation (fun x ↦ |z m x|) := by
    simp only [FiniteReportLaw.expectation, abs_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    ring
  apply weak_limit_of_L1 p (fun m x ↦ c * z m x) (fun m x ↦ a m * z m x) ν hz
  · have hh := ((ha.sub_const c).abs).mul hB
    simpa only [← sub_mul, he, sub_self, abs_zero, zero_mul] using hh
  · simpa only [he] using ha.abs.mul hB

end Descent.Portability.FiniteL1WeakStability
