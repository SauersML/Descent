/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Layer
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Probability.Moments.Variance
import Mathlib.Tactic

assert_below Descent.Decision Descent.Program

/-!
Exact expectation and variance of an average under an actual finite product
sampling law. Independence and coordinate marginal laws are derived from
Measure.pi rather than supplied as estimator-specific assumptions.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.IIDAverageLaw

open scoped BigOperators
open MeasureTheory ProbabilityTheory

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The empirical average of a scalar statistic across a finite sample. -/
noncomputable def average (f : Ω → ℝ) (M : ℕ) (x : Fin M → Ω) : ℝ :=
  (1 / (M : ℝ)) * ∑ i, f (x i)

/-- The average is exactly unbiased for the one-observation expectation. -/
theorem average_integral (μ : Measure Ω) [IsProbabilityMeasure μ]
    (f : Ω → ℝ) (hf : Integrable f μ) (M : ℕ) (hM : 0 < M) :
    (∫ x, average f M x ∂Measure.pi (fun _ : Fin M ↦ μ)) = ∫ x, f x ∂μ := by
  unfold average
  rw [integral_const_mul, integral_finset_sum]
  · simp only [integral_comp_eval (μ := fun _ : Fin M ↦ μ)
      (f := f) hf.aestronglyMeasurable, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hm : (M : ℝ) ≠ 0 := by exact_mod_cast hM.ne'
    field_simp
  · intro i _
    exact integrable_comp_eval hf

/-- The variance of the actual independent sample sum is M times the marginal variance. -/
theorem sample_sum_variance (μ : Measure Ω) [IsProbabilityMeasure μ]
    (f : Ω → ℝ) (hf : MemLp f 2 μ) (M : ℕ) :
    variance (fun x : Fin M → Ω ↦ ∑ i, f (x i)) (Measure.pi (fun _ : Fin M ↦ μ)) =
      (M : ℝ) * variance f μ := by
  have hi := iIndepFun_pi (μ := fun _ : Fin M ↦ μ) (X := fun _ ↦ f)
    (fun _ ↦ hf.aemeasurable)
  have hp (i : Fin M) : MemLp (fun x : Fin M → Ω ↦ f (x i)) 2
      (Measure.pi (fun _ : Fin M ↦ μ)) :=
    hf.comp_measurePreserving (measurePreserving_eval (fun _ : Fin M ↦ μ) i)
  have hh := IndepFun.variance_sum (s := Finset.univ) (fun i _ ↦ hp i)
    (fun i _ j _ hij ↦ hi.indepFun hij)
  have he : (∑ i : Fin M, fun x : Fin M → Ω ↦ f (x i)) =
      (fun x : Fin M → Ω ↦ ∑ i, f (x i)) := by
    funext x
    simp
  rw [he] at hh
  simp only [(measurePreserving_eval (fun _ : Fin M ↦ μ) _).variance_fun_comp hf.aemeasurable,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hh
  exact hh

/-- Exact inverse-sample-size variance reduction under the actual product experiment. -/
theorem average_variance (μ : Measure Ω) [IsProbabilityMeasure μ]
    (f : Ω → ℝ) (hf : MemLp f 2 μ) (M : ℕ) (hM : 0 < M) :
    variance (average f M) (Measure.pi (fun _ : Fin M ↦ μ)) = variance f μ / (M : ℝ) := by
  unfold average
  rw [variance_mul, sample_sum_variance μ f hf M]
  have hm : (M : ℝ) ≠ 0 := by exact_mod_cast hM.ne'
  field_simp

end Descent.Portability.IIDAverageLaw
