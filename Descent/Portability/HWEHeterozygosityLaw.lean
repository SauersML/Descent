/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.HWEInteractionLaw
import Descent.Portability.FiniteIndependentMoments
import Descent.Portability.ComplexBernoulliProduct

assert_below Descent.Decision Descent.Program

/-!
The heterozygosity count in the square-biased HWE interaction law is an exact
Poisson-binomial variable. Its probabilities, mean, and characteristic function
are derived from the original standardized genotype and independent block law.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.HWEHeterozygosityLaw

open scoped BigOperators Topology
open Filter Foundations HWEInteractionLaw

/-- Indicator of the heterozygous diploid genotype. -/
def heterozygote : DiploidGenotype → ℝ
  | .homRef => 0
  | .het => 1
  | .homAlt => 0

/-- Number of heterozygous loci, viewed as a real observable. -/
noncomputable def count {ι : Type*} [Fintype ι] (x : ι → DiploidGenotype) : ℝ :=
  ∑ i, heterozygote (x i)

/-- The square-biased success probability, in the original frequency parameter. -/
def probability (h : HardyWeinbergModel) : ℝ := 4 * (h.altFreq - 1 / 2) ^ 2

theorem probability_nonneg (h : HardyWeinbergModel) : 0 ≤ probability h := by
  unfold probability
  positivity

theorem probability_le_one (h : HardyWeinbergModel)
    (h0 : 0 < h.altFreq) (h1 : h.altFreq < 1) : probability h ≤ 1 := by
  unfold probability
  nlinarith [mul_nonneg h0.le (show 0 ≤ 1 - h.altFreq by linarith)]

/-- The exact tilted single-locus indicator mean. -/
theorem locus_mean (h : HardyWeinbergModel)
    (h0 : 0 < h.altFreq) (h1 : h.altFreq < 1) :
    (squareBiasedLocus h h0 h1).expectation heterozygote = probability h := by
  rw [FiniteReportLaw.expectation, Core.Genotype.sum_univ]
  simp only [squareBiasedLocus_mass, heterozygote, mul_zero, mul_one, zero_add, add_zero]
  rfl

/-- The exact tilted single-locus characteristic factor. -/
theorem locus_characteristic (h : HardyWeinbergModel)
    (h0 : 0 < h.altFreq) (h1 : h.altFreq < 1) (t : ℝ) :
    complexExpectation (squareBiasedLocus h h0 h1)
      (fun x ↦ Complex.exp ((t * heterozygote x : ℝ) * Complex.I)) =
      1 + (probability h : ℂ) * (Complex.exp ((t : ℂ) * Complex.I) - 1) := by
  rw [complexExpectation, Core.Genotype.sum_univ]
  simp only [squareBiasedLocus_mass, heterozygote, mul_zero, mul_one,
    Complex.ofReal_zero, Complex.exp_zero, probability]
  push_cast
  ring

/-- The block count has exactly the sum of the locus intensities. -/
theorem count_mean {ι : Type*} [Fintype ι] [DecidableEq ι]
    (h : ι → HardyWeinbergModel)
    (h0 : ∀ i, 0 < (h i).altFreq) (h1 : ∀ i, (h i).altFreq < 1) :
    (independentLaw (fun i ↦ squareBiasedLocus (h i) (h0 i) (h1 i))).expectation
      count = ∑ i, probability (h i) := by
  rw [count, FiniteIndependentMoments.independent_sum_mean]
  simp only [locus_mean]

/-- Every count characteristic is the actual finite Bernoulli product. -/
theorem count_characteristic {ι : Type*} [Fintype ι] [DecidableEq ι]
    (h : ι → HardyWeinbergModel)
    (h0 : ∀ i, 0 < (h i).altFreq) (h1 : ∀ i, (h i).altFreq < 1) (t : ℝ) :
    complexExpectation (independentLaw (fun i ↦ squareBiasedLocus (h i) (h0 i) (h1 i)))
      (fun x ↦ Complex.exp ((t * count x : ℝ) * Complex.I)) =
      ∏ i, (1 + (probability (h i) : ℂ) * (Complex.exp ((t : ℂ) * Complex.I) - 1)) := by
  rw [count, characteristic_independent_sum]
  simp only [locus_characteristic]

/-- The count is nonnegative on every realized genotype vector. -/
theorem count_nonneg {ι : Type*} [Fintype ι] (x : ι → DiploidGenotype) :
    0 ≤ count x := by
  apply Finset.sum_nonneg
  intro i _
  cases x i <;> norm_num [heterozygote]

end Descent.Portability.HWEHeterozygosityLaw
