/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Blindness.EpistaticChaos
import Descent.Portability.ExactFiniteHistoryLaw
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

assert_below Descent.Decision Descent.Program

/-!
Finite independent Hardy-Weinberg interaction experiments. The probability
law uses the existing genotype probabilities and the observable uses the
existing standardized genotype. Square biasing is derived at each genotype,
providing the exact homozygote/heterozygote probabilities used in critical laws.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.HWEInteractionLaw

open scoped BigOperators
open Foundations

/-- Independent coordinates with their full finite sample law. -/
noncomputable def independentLaw {ι α : Type*} [Fintype ι] [DecidableEq ι] [Fintype α]
    (p : ι → FiniteReportLaw α) : FiniteReportLaw (ι → α) where
  mass x := ∏ i, (p i).mass (x i)
  mass_nonneg x := Finset.prod_nonneg (fun i _ ↦ (p i).mass_nonneg (x i))
  mass_sum := by
    have h := Finset.prod_univ_sum (fun _ : ι ↦ (Finset.univ : Finset α))
      (fun i a ↦ (p i).mass a)
    simpa only [Fintype.piFinset_univ, FiniteReportLaw.mass_sum,
      Finset.prod_const_one] using h.symm

/-- Independence factorizes every product observable, not just its first two moments. -/
theorem expectation_independent_product {ι α : Type*} [Fintype ι] [DecidableEq ι] [Fintype α]
    (p : ι → FiniteReportLaw α) (f : ι → α → ℝ) :
    (independentLaw p).expectation (fun x ↦ ∏ i, f i (x i)) =
      ∏ i, (p i).expectation (f i) := by
  simp only [FiniteReportLaw.expectation, independentLaw, ← Finset.prod_mul_distrib]
  have h := Finset.prod_univ_sum (fun _ : ι ↦ (Finset.univ : Finset α))
    (fun i a ↦ (p i).mass a * f i a)
  simpa only [Fintype.piFinset_univ] using h.symm

/-- Complex expectation is used to identify the full distribution by Fourier transforms. -/
noncomputable def complexExpectation {α : Type*} [Fintype α]
    (p : FiniteReportLaw α) (f : α → ℂ) : ℂ := ∑ x, (p.mass x : ℂ) * f x

/-- The same independence law factorizes complex product observables. -/
theorem complexExpectation_independent_product {ι α : Type*} [Fintype ι] [DecidableEq ι] [Fintype α]
    (p : ι → FiniteReportLaw α) (f : ι → α → ℂ) :
    complexExpectation (independentLaw p) (fun x ↦ ∏ i, f i (x i)) =
      ∏ i, complexExpectation (p i) (f i) := by
  simp only [complexExpectation, independentLaw, Complex.ofReal_prod,
    ← Finset.prod_mul_distrib]
  have h := Finset.prod_univ_sum (fun _ : ι ↦ (Finset.univ : Finset α))
    (fun i a ↦ ((p i).mass a : ℂ) * f i a)
  simpa only [Fintype.piFinset_univ] using h.symm

/-- Characteristic functions of sums factorize under the concrete independent law. -/
theorem characteristic_independent_sum {ι α : Type*} [Fintype ι] [DecidableEq ι] [Fintype α]
    (p : ι → FiniteReportLaw α) (f : ι → α → ℝ) (t : ℝ) :
    complexExpectation (independentLaw p)
      (fun x ↦ Complex.exp ((t * ∑ i, f i (x i) : ℝ) * Complex.I)) =
      ∏ i, complexExpectation (p i)
        (fun x ↦ Complex.exp ((t * f i x : ℝ) * Complex.I)) := by
  simp only [Finset.mul_sum, Complex.ofReal_sum, Finset.sum_mul, Complex.exp_sum]
  exact complexExpectation_independent_product p
    (fun i x ↦ Complex.exp ((t * f i x : ℝ) * Complex.I))

/-- Real part of the finite characteristic function is the expected cosine. -/
theorem characteristic_re {α : Type*} [Fintype α]
    (p : FiniteReportLaw α) (f : α → ℝ) (t : ℝ) :
    (complexExpectation p (fun x ↦ Complex.exp ((t * f x : ℝ) * Complex.I))).re =
      p.expectation (fun x ↦ Real.cos (t * f x)) := by
  simp only [complexExpectation, Complex.re_sum, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero, Complex.exp_ofReal_mul_I_re,
    FiniteReportLaw.expectation]

/-- Imaginary part of the finite characteristic function is the expected sine. -/
theorem characteristic_im {α : Type*} [Fintype α]
    (p : FiniteReportLaw α) (f : α → ℝ) (t : ℝ) :
    (complexExpectation p (fun x ↦ Complex.exp ((t * f x : ℝ) * Complex.I))).im =
      p.expectation (fun x ↦ Real.sin (t * f x)) := by
  simp only [complexExpectation, Complex.im_sum, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, add_zero, Complex.exp_ofReal_mul_I_im,
    FiniteReportLaw.expectation]

/-- The existing single-locus Hardy-Weinberg probabilities form a normalized law. -/
noncomputable def locusLaw (h : HardyWeinbergModel) : FiniteReportLaw DiploidGenotype where
  mass := h.genotypeProb
  mass_nonneg := h.genotypeProb_nonneg
  mass_sum := h.genotypeProb_sum

/-- Linkage-equilibrium genotype vector for one interaction block. -/
noncomputable def blockLaw {ι : Type*} [Fintype ι] [DecidableEq ι] (h : ι → HardyWeinbergModel) :=
  independentLaw (fun i ↦ locusLaw (h i))

/-- The actual standardized HWE interaction, before the row normalization. -/
noncomputable def interaction {ι : Type*} [Fintype ι] [DecidableEq ι]
    (h : ι → HardyWeinbergModel) (x : ι → DiploidGenotype) : ℝ :=
  ∏ i, (h i).standardizedGenotype (x i)

/-- Nonempty interactions are exactly centered under linkage equilibrium. -/
theorem interaction_mean_zero {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (h : ι → HardyWeinbergModel) :
    (blockLaw h).expectation (interaction h) = 0 := by
  change (independentLaw (fun i ↦ locusLaw (h i))).expectation
    (fun x ↦ ∏ i, (h i).standardizedGenotype (x i)) = 0
  rw [expectation_independent_product]
  simp only [locusLaw, FiniteReportLaw.expectation,
    Blindness.standardizedGenotype_expectation_zero]
  simp

/-- Every polymorphic standardized interaction has exactly unit second moment. -/
theorem interaction_second_moment {ι : Type*} [Fintype ι] [DecidableEq ι]
    (h : ι → HardyWeinbergModel)
    (h0 : ∀ i, 0 < (h i).altFreq) (h1 : ∀ i, (h i).altFreq < 1) :
    (blockLaw h).expectation (fun x ↦ interaction h x ^ 2) = 1 := by
  simp only [interaction, ← Finset.prod_pow]
  rw [blockLaw, expectation_independent_product (fun i ↦ locusLaw (h i))
    (fun i g ↦ (h i).standardizedGenotype g ^ 2)]
  simp only [locusLaw, FiniteReportLaw.expectation,
    Blindness.standardizedGenotype_second_moment_one _ (h0 _) (h1 _), Finset.prod_const_one]

/-- Square biasing a standardized locus yields a probability law. -/
noncomputable def squareBiasedLocus (h : HardyWeinbergModel)
    (h0 : 0 < h.altFreq) (h1 : h.altFreq < 1) : FiniteReportLaw DiploidGenotype where
  mass g := h.genotypeProb g * h.standardizedGenotype g ^ 2
  mass_nonneg g := mul_nonneg (h.genotypeProb_nonneg g) (sq_nonneg _)
  mass_sum := Blindness.standardizedGenotype_second_moment_one h h0 h1

/-- Exact square-biased probabilities: the homozygote signs are fair and the
heterozygote mass is four times the squared displacement from balance. -/
theorem squareBiasedLocus_mass (h : HardyWeinbergModel)
    (h0 : 0 < h.altFreq) (h1 : h.altFreq < 1) (g : DiploidGenotype) :
    (squareBiasedLocus h h0 h1).mass g = match g with
      | .homRef => 2 * h.altFreq * (1 - h.altFreq)
      | .het => 4 * (h.altFreq - 1 / 2) ^ 2
      | .homAlt => 2 * h.altFreq * (1 - h.altFreq) := by
  have hv := h.genotypeVariance_pos h0 h1
  simp only [squareBiasedLocus, HardyWeinbergModel.standardizedGenotype, div_pow]
  rw [Real.sq_sqrt hv.le, HardyWeinbergModel.genotypeVariance_eq]
  have hp : h.altFreq ≠ 0 := h0.ne'
  have hq : 1 - h.altFreq ≠ 0 := by linarith
  cases g <;>
    simp [HardyWeinbergModel.genotypeProb, HardyWeinbergModel.centeredAltAlleleCount,
      HardyWeinbergModel.refFreq, HardyWeinbergModel.expectedAltAlleleCount_eq,
      altAlleleCount, Core.Genotype.dosage] <;>
    field_simp
  all_goals ring

/-- Product square bias preserves independence of loci, derived at every full genotype vector. -/
theorem squareBiasedBlock_mass {ι : Type*} [Fintype ι] [DecidableEq ι]
    (h : ι → HardyWeinbergModel)
    (h0 : ∀ i, 0 < (h i).altFreq) (h1 : ∀ i, (h i).altFreq < 1)
    (x : ι → DiploidGenotype) :
    (independentLaw (fun i ↦ squareBiasedLocus (h i) (h0 i) (h1 i))).mass x =
      (blockLaw h).mass x * interaction h x ^ 2 := by
  simp only [independentLaw, squareBiasedLocus, blockLaw, locusLaw, interaction,
    Finset.prod_mul_distrib, Finset.prod_pow]

end Descent.Portability.HWEInteractionLaw
