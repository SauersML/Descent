/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.HWEAbsoluteLocusBounds

assert_below Descent.Decision Descent.Program

/-!
The actual absolute interaction moment on the event containing a heterozygote is
an exact difference of two products. Near balance this difference is bounded by
the sum of the cubic heterozygote contributions, without a tail approximation.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.HWEExceptionalAmplitude

open scoped BigOperators
open Foundations HWEInteractionLaw HWEHomozygoteLimit HWEAbsoluteLocusLaw
open HWEAbsoluteLocusBounds HWEHeterozygosityLaw HWEHeterozygosityLimit

/-- The balanced-normalized original interaction factors into normalized loci. -/
theorem normalized_product {ι : Type*} [Fintype ι] [DecidableEq ι]
    (h : ι → HardyWeinbergModel) (x : ι → DiploidGenotype) :
    normalized h x = ∏ i, locusAmplitude (h i) (x i) := by
  simp only [normalized, interaction, locusAmplitude, Finset.prod_div_distrib,
    Finset.prod_const, Finset.card_univ]

theorem absolute_product {ι : Type*} [Fintype ι] [DecidableEq ι]
    (h : ι → HardyWeinbergModel) (x : ι → DiploidGenotype) :
    |normalized h x| = ∏ i, |locusAmplitude (h i) (x i)| := by
  rw [normalized_product, Finset.abs_prod]

/-- Exact absolute moment of the entire square-biased interaction. -/
theorem total_absolute_product {ι : Type*} [Fintype ι] [DecidableEq ι]
    (h : ι → HardyWeinbergModel)
    (h0 : ∀ i, 0 < (h i).altFreq) (h1 : ∀ i, (h i).altFreq < 1) :
    (independentLaw (fun i ↦ squareBiasedLocus (h i) (h0 i) (h1 i))).expectation
      (fun x ↦ |normalized h x|) = ∏ i, (homoMass (h i) + heteroMass (h i)) := by
  simp_rw [absolute_product]
  rw [expectation_independent_product
    (fun i ↦ squareBiasedLocus (h i) (h0 i) (h1 i))
    (fun i g ↦ |locusAmplitude (h i) g|)]
  simp only [total_absolute]

/-- Exact absolute moment restricted to the zero-heterozygote component. -/
theorem homo_absolute_product {ι : Type*} [Fintype ι] [DecidableEq ι]
    (h : ι → HardyWeinbergModel)
    (h0 : ∀ i, 0 < (h i).altFreq) (h1 : ∀ i, (h i).altFreq < 1) :
    (independentLaw (fun i ↦ squareBiasedLocus (h i) (h0 i) (h1 i))).expectation
      (fun x ↦ if count x = 0 then |normalized h x| else 0) = ∏ i, homoMass (h i) := by
  classical
  have he (x : ι → DiploidGenotype) :
      (if count x = 0 then |normalized h x| else 0) =
        ∏ i, (if x i = .het then 0 else |locusAmplitude (h i) (x i)|) := by
    calc
      _ = (if count x = 0 then 1 else 0) * |normalized h x| := by
        by_cases hc : count x = 0 <;> simp [hc]
      _ = ∏ i, ((1 - heterozygote (x i)) * |locusAmplitude (h i) (x i)|) := by
        rw [zero_indicator, absolute_product, ← Finset.prod_mul_distrib]
      _ = _ := by
        apply Finset.prod_congr rfl
        intro i _
        cases x i <;> simp [heterozygote]
  simp_rw [he]
  rw [expectation_independent_product
    (fun i ↦ squareBiasedLocus (h i) (h0 i) (h1 i))
    (fun i g ↦ if g = .het then 0 else |locusAmplitude (h i) g|)]
  simp only [homo_absolute]

/-- Exact expected exceptional amplitude, not a supplied approximation error. -/
theorem exceptional_product_difference {ι : Type*} [Fintype ι] [DecidableEq ι]
    (h : ι → HardyWeinbergModel)
    (h0 : ∀ i, 0 < (h i).altFreq) (h1 : ∀ i, (h i).altFreq < 1) :
    (independentLaw (fun i ↦ squareBiasedLocus (h i) (h0 i) (h1 i))).expectation
      (fun x ↦ if count x = 0 then 0 else |normalized h x|) =
        (∏ i, (homoMass (h i) + heteroMass (h i))) - ∏ i, homoMass (h i) := by
  rw [← total_absolute_product h h0 h1, ← homo_absolute_product h h0 h1]
  simp only [FiniteReportLaw.expectation, ← Finset.sum_sub_distrib, ← mul_sub]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hc : count x = 0 <;> simp [hc]

/-- The exceptional absolute moment is bounded by the sum of the locus errors. -/
theorem exceptional_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    (h : ι → HardyWeinbergModel)
    (h0 : ∀ i, 0 < (h i).altFreq) (h1 : ∀ i, (h i).altFreq < 1)
    (hsmall : ∀ i, |(h i).altFreq - 1 / 2| ≤ 1 / 8) :
    (independentLaw (fun i ↦ squareBiasedLocus (h i) (h0 i) (h1 i))).expectation
      (fun x ↦ if count x = 0 then 0 else |normalized h x|) ≤ ∑ i, heteroMass (h i) := by
  have hc := ComplexBernoulliProduct.contraction_product_difference Finset.univ
    (fun i ↦ ((homoMass (h i) + heteroMass (h i) : ℝ) : ℂ))
    (fun i ↦ ((homoMass (h i) : ℝ) : ℂ))
    (fun i _ ↦ by
      rw [Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (add_nonneg (masses_nonneg _).1 (masses_nonneg _).2)]
      exact (near_balance_bounds _ (h0 i) (h1 i) (hsmall i)).2)
    (fun i _ ↦ by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (masses_nonneg _).1]
      exact homoMass_le_one _)
  have he (i : ι) : (homoMass (h i) + heteroMass (h i) : ℝ) - homoMass (h i) =
      heteroMass (h i) := by ring
  simp only [← Complex.ofReal_prod, ← Complex.ofReal_sub,
    Complex.norm_real, Real.norm_eq_abs, he, abs_of_nonneg (masses_nonneg _).2] at hc
  rw [exceptional_product_difference]
  exact (le_abs_self _).trans hc

end Descent.Portability.HWEExceptionalAmplitude
