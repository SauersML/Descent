/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.TrainingNoiseAccuracy

assert_below Descent.Decision Descent.Program

/-!
Exact covariance-vector and covariance-matrix evaluation of a linear score
on a fixed evaluation cohort.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.TrainingNoiseAccuracy

open FiniteReportLaw

variable {S J : Type*} [Fintype S] [Fintype J]

theorem expectation_linearScore (p : FiniteReportLaw S)
    (genotype : S → J → ℝ) (weights : J → ℝ) :
    p.expectation (linearScore genotype weights) =
      ∑ j, weights j * p.expectation (fun s ↦ genotype s j) := by
  unfold expectation linearScore
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro s _
  ring

theorem covariance_symmetric (p : FiniteReportLaw S) (f g : S → ℝ) :
    p.covariance f g = p.covariance g f := by
  simp only [covariance, mul_comm]

theorem covariance_linearScore (p : FiniteReportLaw S)
    (genotype : S → J → ℝ) (weights : J → ℝ) (liability : S → ℝ) :
    p.covariance (linearScore genotype weights) liability =
      ∑ j, weights j * p.covariance (fun s ↦ genotype s j) liability := by
  have hraw : p.expectation (fun s ↦ linearScore genotype weights s * liability s) =
      ∑ j, weights j * p.expectation (fun s ↦ genotype s j * liability s) := by
    unfold expectation linearScore
    simp only [Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro s _
    ring
  simp only [covariance_eq_rawMoments]
  rw [hraw, expectation_linearScore, Finset.sum_mul, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem variance_linearScore (p : FiniteReportLaw S)
    (genotype : S → J → ℝ) (weights : J → ℝ) :
    p.variance (linearScore genotype weights) =
      ∑ j, ∑ k, weights j * weights k *
        p.covariance (fun s ↦ genotype s j) (fun s ↦ genotype s k) := by
  unfold variance
  rw [covariance_linearScore]
  apply Finset.sum_congr rfl
  intro j _
  rw [covariance_symmetric, covariance_linearScore, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [covariance_symmetric p (fun s ↦ genotype s k)]
  ring

/-- The score's accuracy can be evaluated from the genotype covariance matrix,
trait covariance vector, and learned weights. These quantities use the evaluation
cohort's own centering; no source covariance is substituted for a target covariance. -/
theorem squaredCorrelation_linearScore (p : FiniteReportLaw S)
    (genotype : S → J → ℝ) (weights : J → ℝ) (liability : S → ℝ)
    (hv : 0 < p.variance (linearScore genotype weights))
    (hl : 0 < p.variance liability) :
    p.squaredCorrelation (linearScore genotype weights) liability = some
      ((∑ j, weights j * p.covariance (fun s ↦ genotype s j) liability) ^ 2 /
        ((∑ j, ∑ k, weights j * weights k *
          p.covariance (fun s ↦ genotype s j) (fun s ↦ genotype s k)) *
          p.variance liability)) := by
  rw [squaredCorrelation, if_pos ⟨hv, hl⟩,
    covariance_linearScore, variance_linearScore]

end Descent.Portability.TrainingNoiseAccuracy
