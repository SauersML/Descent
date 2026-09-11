/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.HWEHeterozygosityLaw

assert_below Descent.Decision Descent.Program

/-!
The near-balanced frequency assumptions imply the Poisson characteristic limit
for the actual square-biased heterozygosity count and the exact asymptotic mass
of the zero-heterozygote component. The product probabilities are derived from HWE.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.HWEHeterozygosityLimit

open scoped BigOperators Topology
open Filter Foundations HWEInteractionLaw HWEHeterozygosityLaw

/-- A product of homozygote indicators is exactly the zero-count event indicator. -/
theorem zero_indicator {ι : Type*} [Fintype ι] (x : ι → DiploidGenotype) :
    (if count x = 0 then (1 : ℝ) else 0) = ∏ i, (1 - heterozygote (x i)) := by
  classical
  have hn (i : ι) : 0 ≤ heterozygote (x i) := by cases x i <;> norm_num [heterozygote]
  by_cases hc : count x = 0
  · have hz : ∀ i, heterozygote (x i) = 0 := by
      have h := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ ↦ hn i)).mp hc
      exact fun i ↦ h i (Finset.mem_univ i)
    simp [hc, hz]
  · have he : ∃ i, heterozygote (x i) ≠ 0 := by
      by_contra h
      push_neg at h
      exact hc (by simp [count, h])
    obtain ⟨i, hi⟩ := he
    have hi1 : heterozygote (x i) = 1 := by
      cases hxi : x i <;> simp_all [heterozygote]
    rw [if_neg hc]
    symm
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by rw [hi1, sub_self])

/-- Exact mass of zero heterozygotes in the original square-biased block law. -/
theorem zero_count_probability {ι : Type*} [Fintype ι] [DecidableEq ι]
    (h : ι → HardyWeinbergModel)
    (h0 : ∀ i, 0 < (h i).altFreq) (h1 : ∀ i, (h i).altFreq < 1) :
    (independentLaw (fun i ↦ squareBiasedLocus (h i) (h0 i) (h1 i))).expectation
      (fun x ↦ if count x = 0 then 1 else 0) = ∏ i, (1 - probability (h i)) := by
  classical
  simp_rw [zero_indicator]
  rw [expectation_independent_product
    (fun i ↦ squareBiasedLocus (h i) (h0 i) (h1 i)) (fun _ x ↦ 1 - heterozygote x)]
  apply Finset.prod_congr rfl
  intro i _
  rw [FiniteReportLaw.expectation, Core.Genotype.sum_univ]
  simp only [squareBiasedLocus_mass, heterozygote, sub_zero, sub_self, mul_one, mul_zero]
  unfold probability
  ring

/-- Allele-frequency displacement controls every tilted Bernoulli success probability. -/
theorem probability_cap (h : HardyWeinbergModel) (ε : ℝ)
    (hcap : |h.altFreq - 1 / 2| ≤ ε) : probability h ≤ 4 * ε ^ 2 := by
  have hε : 0 ≤ ε := (abs_nonneg _).trans hcap
  have hs := (sq_le_sq₀ (abs_nonneg _) hε).mpr hcap
  unfold probability
  nlinarith [sq_abs (h.altFreq - 1 / 2)]

/-- The report's near-balanced assumptions imply the actual Poisson(4K) Fourier limit. -/
theorem count_characteristic_limit (h : (m : ℕ) → Fin m → HardyWeinbergModel)
    (h0 : ∀ m i, 0 < (h m i).altFreq) (h1 : ∀ m i, (h m i).altFreq < 1)
    (ε : ℕ → ℝ) (hcap : ∀ m i, |(h m i).altFreq - 1 / 2| ≤ ε m)
    (hε : Tendsto ε atTop (𝓝 0)) (K : ℝ)
    (hK : Tendsto (fun m ↦ ∑ i, ((h m i).altFreq - 1 / 2) ^ 2) atTop (𝓝 K))
    (t : ℝ) :
    Tendsto (fun m ↦ complexExpectation
      (independentLaw (fun i ↦ squareBiasedLocus (h m i) (h0 m i) (h1 m i)))
      (fun x ↦ Complex.exp ((t * count x : ℝ) * Complex.I))) atTop
      (𝓝 (Complex.exp ((4 * K : ℝ) * (Complex.exp ((t : ℂ) * Complex.I) - 1)))) := by
  simp_rw [count_characteristic]
  apply ComplexBernoulliProduct.bernoulli_product_limit
    (fun m i ↦ probability (h m i)) (fun m ↦ 4 * (ε m) ^ 2)
    (fun m i ↦ probability_nonneg _) (fun m i ↦ probability_le_one _ (h0 m i) (h1 m i))
    (fun m i ↦ probability_cap _ _ (hcap m i))
  · simpa using (hε.pow 2).const_mul 4
  · simpa only [probability, ← Finset.mul_sum] using hK.const_mul 4
  · simp [Complex.norm_exp]

/-- The mass of the zero-heterozygote component converges to exp(-4K). -/
theorem zero_count_probability_limit (h : (m : ℕ) → Fin m → HardyWeinbergModel)
    (h0 : ∀ m i, 0 < (h m i).altFreq) (h1 : ∀ m i, (h m i).altFreq < 1)
    (ε : ℕ → ℝ) (hcap : ∀ m i, |(h m i).altFreq - 1 / 2| ≤ ε m)
    (hε : Tendsto ε atTop (𝓝 0)) (K : ℝ)
    (hK : Tendsto (fun m ↦ ∑ i, ((h m i).altFreq - 1 / 2) ^ 2) atTop (𝓝 K)) :
    Tendsto (fun m ↦
      (independentLaw (fun i ↦ squareBiasedLocus (h m i) (h0 m i) (h1 m i))).expectation
        (fun x ↦ if count x = 0 then 1 else 0)) atTop (𝓝 (Real.exp (-4 * K))) := by
  have hc := ComplexBernoulliProduct.bernoulli_product_limit
    (fun m i ↦ probability (h m i)) (fun m ↦ 4 * (ε m) ^ 2)
    (fun m i ↦ probability_nonneg _) (fun m i ↦ probability_le_one _ (h0 m i) (h1 m i))
    (fun m i ↦ probability_cap _ _ (hcap m i))
    (by simpa using (hε.pow 2).const_mul 4) (4 * K)
    (by simpa only [probability, ← Finset.mul_sum] using hK.const_mul 4)
    0 (by simp)
  have hp (m : ℕ) :
      (∏ i, (1 + (probability (h m i) : ℂ) * (0 - 1))) =
        ((∏ i, (1 - probability (h m i)) : ℝ) : ℂ) := by
    push_cast
    apply Finset.prod_congr rfl
    intro i _
    ring
  simp_rw [hp] at hc
  simp only [zero_sub, mul_neg_one, ← Complex.ofReal_neg,
    ← Complex.ofReal_exp] at hc
  have hre := Complex.continuous_re.continuousAt.tendsto.comp hc
  simp_rw [zero_count_probability]
  simpa only [Function.comp_def, Complex.ofReal_re, neg_mul] using hre

end Descent.Portability.HWEHeterozygosityLimit
