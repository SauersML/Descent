/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.IIDAverageLaw

assert_below Descent.Decision Descent.Program

/-!
The mean and full covariance of linear contrasts under an actual finite
product probability law. The coordinate distributions may differ. These laws
supply the shared-audit covariance calculation without assuming zero cross
terms or replacing prospective variation by sampling-only variation.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.IndependentContrastLaw

open MeasureTheory ProbabilityTheory
open scoped BigOperators

variable {ι : Type*} [Fintype ι]

/-- A linear contrast, with any frame normalization already included in its coefficients. -/
noncomputable def contrast (w : ι → ℝ) (x : ι → ℝ) : ℝ := ∑ i, w i * x i

/-- Marginal second moments remain finite after evaluating a product coordinate. -/
theorem coordinate_memLp (μ : ι → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    (hY : ∀ i, MemLp (fun y : ℝ ↦ y) 2 (μ i)) (i : ι) :
    MemLp (fun x : ι → ℝ ↦ x i) 2 (Measure.pi μ) :=
  (hY i).comp_measurePreserving (measurePreserving_eval μ i)

/-- Every finite contrast has a finite second moment under the joint law. -/
theorem contrast_memLp (μ : ι → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    (hY : ∀ i, MemLp (fun y : ℝ ↦ y) 2 (μ i)) (w : ι → ℝ) :
    MemLp (contrast w) 2 (Measure.pi μ) := by
  exact memLp_finset_sum _ (fun i _ ↦ (coordinate_memLp μ hY i).const_mul (w i))

/-- A contrast expectation is exactly the corresponding contrast of marginal means. -/
theorem contrast_integral (μ : ι → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    (hY : ∀ i, Integrable (fun y : ℝ ↦ y) (μ i)) (w : ι → ℝ) :
    (∫ x, contrast w x ∂Measure.pi μ) = ∑ i, w i * ∫ y, y ∂μ i := by
  unfold contrast
  rw [integral_finset_sum]
  · apply Finset.sum_congr rfl
    intro i _
    rw [integral_const_mul (w i) (fun x : ι → ℝ ↦ x i)]
    congr 1
    exact integral_comp_eval (μ := μ) (f := fun y : ℝ ↦ y) (hY i).aestronglyMeasurable
  · intro i _
    have hi : Integrable (fun x : ι → ℝ ↦ x i) (Measure.pi μ) :=
      integrable_comp_eval (μ := μ) (f := fun y : ℝ ↦ y) (hY i)
    exact hi.const_mul (w i)

/-- Distinct product coordinates have zero covariance; diagonal covariance is marginal variance. -/
theorem coordinate_covariance [DecidableEq ι] (μ : ι → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    (hY : ∀ i, MemLp (fun y : ℝ ↦ y) 2 (μ i)) (i j : ι) :
    cov[fun x : ι → ℝ ↦ x i, fun x : ι → ℝ ↦ x j; Measure.pi μ] =
      if i = j then Var[fun y : ℝ ↦ y; μ i] else 0 := by
  classical
  by_cases hij : i = j
  · subst j
    rw [if_pos rfl, covariance_self (coordinate_memLp μ hY i).aemeasurable]
    exact (measurePreserving_eval μ i).variance_fun_comp (hY i).aemeasurable
  · rw [if_neg hij]
    have hi := iIndepFun_pi (μ := μ) (X := fun (_ : ι) (y : ℝ) ↦ y)
      (fun i ↦ (hY i).aemeasurable)
    exact (hi.indepFun hij).covariance_eq_zero
      (coordinate_memLp μ hY i) (coordinate_memLp μ hY j)

/-- Exact covariance between any two contrasts, so one law determines the whole matrix. -/
theorem contrast_covariance (μ : ι → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    (hY : ∀ i, MemLp (fun y : ℝ ↦ y) 2 (μ i)) (w v : ι → ℝ) :
    cov[contrast w, contrast v; Measure.pi μ] =
      ∑ i, w i * v i * Var[fun y : ℝ ↦ y; μ i] := by
  classical
  unfold contrast
  rw [covariance_fun_sum_fun_sum
    (fun i ↦ (coordinate_memLp μ hY i).const_mul (w i))
    (fun i ↦ (coordinate_memLp μ hY i).const_mul (v i))]
  apply Finset.sum_congr rfl
  intro i _
  simp only [covariance_mul_left, covariance_mul_right, coordinate_covariance μ hY]
  rw [Finset.sum_eq_single i]
  · simp [mul_assoc, mul_left_comm]
  · intro j _ hji
    simp [Ne.symm hji]
  · simp

/-- Variance is the corresponding quadratic form, with no unproved independence premise. -/
theorem contrast_variance (μ : ι → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    (hY : ∀ i, MemLp (fun y : ℝ ↦ y) 2 (μ i)) (w : ι → ℝ) :
    Var[contrast w; Measure.pi μ] = ∑ i, w i ^ 2 * Var[fun y : ℝ ↦ y; μ i] := by
  rw [← covariance_self (contrast_memLp μ hY w).aemeasurable, contrast_covariance μ hY]
  simp only [pow_two]

end Descent.Portability.IndependentContrastLaw
