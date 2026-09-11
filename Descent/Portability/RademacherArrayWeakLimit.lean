/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.CosineArrayLimit
import Descent.Portability.FiniteAtomicReportMeasure
import Descent.Portability.FiniteIndependentMoments
import Descent.Portability.SecondMomentTightness
import Descent.Portability.TightCharacteristicConvergence
import Mathlib.Probability.Distributions.Gaussian.Real

assert_below Descent.Decision Descent.Program

/-!
The actual heterogeneous triangular-array Gaussian limit for weighted independent
fair signs. Both characteristic convergence and tightness are derived from the
finite sample law; zero limiting variance is included.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.RademacherArrayWeakLimit

open scoped BigOperators Topology NNReal
open Filter MeasureTheory ProbabilityTheory HWEInteractionLaw BalancedHWEWeakLimit
open FiniteAtomicReportMeasure FiniteIndependentMoments
open SecondMomentTightness TightCharacteristicConvergence

/-- The observed weighted sum in one finite row of independent fair signs. -/
noncomputable def weightedSum {ι : Type*} [Fintype ι] (a : ι → ℝ) (x : ι → Bool) : ℝ :=
  ∑ i, a i * signValue (x i)

theorem sign_mean (a : ℝ) : signLaw.expectation (fun b ↦ a * signValue b) = 0 := by
  simp [FiniteReportLaw.expectation, signLaw, signValue]

theorem sign_second (a : ℝ) :
    signLaw.expectation (fun b ↦ (a * signValue b) ^ 2) = a ^ 2 := by
  simp [FiniteReportLaw.expectation, signLaw, signValue]

theorem sign_characteristic (a t : ℝ) :
    complexExpectation signLaw (fun b ↦ Complex.exp ((t * (a * signValue b) : ℝ) * Complex.I)) =
      (Real.cos (t * a) : ℂ) := by
  have h := Complex.two_cos ((t * a : ℝ) : ℂ)
  simp only [← Complex.ofReal_cos] at h
  simp only [complexExpectation, Fintype.sum_bool, signLaw, signValue,
    Bool.false_eq_true, if_false, if_true, mul_one, mul_neg, Complex.ofReal_neg]
  norm_num only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat]
  linear_combination -h / 2

/-- The exact variance of a row comes from independence and centered coordinates. -/
theorem row_second {ι : Type*} [Fintype ι] [DecidableEq ι] (a : ι → ℝ) :
    (independentLaw (fun _ : ι ↦ signLaw)).expectation (fun x ↦ weightedSum a x ^ 2) =
      ∑ i, a i ^ 2 := by
  unfold weightedSum
  rw [independent_sum_second (fun _ ↦ signLaw) (fun i b ↦ a i * signValue b)
    (fun i ↦ sign_mean (a i))]
  simp only [sign_second]

/-- The exact row characteristic function is its product of coordinate cosines. -/
theorem row_characteristic {ι : Type*} [Fintype ι] [DecidableEq ι] (a : ι → ℝ) (t : ℝ) :
    complexExpectation (independentLaw (fun _ : ι ↦ signLaw))
      (fun x ↦ Complex.exp ((t * weightedSum a x : ℝ) * Complex.I)) =
      ((∏ i, Real.cos (t * a i) : ℝ) : ℂ) := by
  unfold weightedSum
  rw [characteristic_independent_sum (fun _ ↦ signLaw) (fun i b ↦ a i * signValue b)]
  simp only [sign_characteristic, Complex.ofReal_prod]

noncomputable def rowProbability {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a : ι → ℝ) : ProbabilityMeasure ℝ :=
  ⟨finiteMeasure (independentLaw (fun _ : ι ↦ signLaw)) (weightedSum a), inferInstance⟩

noncomputable def centeredGaussian (s : ℝ≥0) : ProbabilityMeasure ℝ :=
  ⟨gaussianReal 0 s, inferInstance⟩

/-- Convergent row variances yield tightness of the actual report distributions. -/
theorem rows_tight (a : (m : ℕ) → Fin m → ℝ) (s : ℝ)
    (hs : Tendsto (fun m ↦ ∑ i, a m i ^ 2) atTop (𝓝 s)) :
    IsTightMeasureSet (Set.range (fun m ↦ (rowProbability (a m) : Measure ℝ))) := by
  obtain ⟨B, hB⟩ := (Metric.isBounded_range_of_tendsto _ hs).exists_norm_le
  apply tight_of_second_moment_bound (fun m ↦ rowProbability (a m)) (max 0 B) (le_max_left _ _)
  · intro m
    exact finite_report_integrable _ _ _
  · intro m
    change (∫ x : ℝ, x ^ 2 ∂finiteMeasure _ (weightedSum (a m))) ≤ _
    rw [integral_finite_report, row_second]
    exact ((le_abs_self _).trans (hB _ ⟨m, rfl⟩)).trans (le_max_right _ _)

/-- Heterogeneous small weights give the full Gaussian weak limit with their limiting variance. -/
theorem gaussian_weak_limit (a : (m : ℕ) → Fin m → ℝ) (ε : ℕ → ℝ)
    (ha : ∀ m i, |a m i| ≤ ε m) (hε : Tendsto ε atTop (𝓝 0)) (s : ℝ≥0)
    (hs : Tendsto (fun m ↦ ∑ i, a m i ^ 2) atTop (𝓝 (s : ℝ))) :
    Tendsto (fun m ↦ rowProbability (a m)) atTop (𝓝 (centeredGaussian s)) := by
  apply weak_convergence_of_tight_characteristic _ (centeredGaussian s)
  · have ht := (isTightMeasureSet_singleton (μ := (centeredGaussian s : Measure ℝ))).union
      (rows_tight a s hs)
    simpa only [Set.singleton_union] using ht
  · intro t
    have hg : charFun (gaussianReal 0 s) t = (Real.exp (-(t ^ 2 * (s : ℝ) / 2)) : ℂ) := by
      rw [charFun_gaussianReal]
      simp only [Complex.ofReal_zero, mul_zero, zero_mul, zero_sub,
        Complex.ofReal_exp, Complex.ofReal_neg, Complex.ofReal_div,
        Complex.ofReal_pow, Complex.ofReal_ofNat, Complex.ofReal_mul]
      congr 1
      ring
    change Tendsto (fun m ↦ charFun (finiteMeasure
      (independentLaw (fun _ : Fin m ↦ signLaw)) (weightedSum (a m))) t)
      atTop (𝓝 (charFun (gaussianReal 0 s) t))
    rw [hg]
    simpa only [charFun_finite_report, row_characteristic] using
      (CosineArrayLimit.cosine_product_limit a ε ha hε s hs t).ofReal

end Descent.Portability.RademacherArrayWeakLimit
