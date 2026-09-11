/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.RealVaryingEuler
import Mathlib.Analysis.Complex.Exponential

assert_below Descent.Decision Descent.Program

/-!
A quantitative law of small numbers for finite Bernoulli characteristic
products. Contractivity removes exponential prefactors: the product-to-Poisson
error is bounded by the sum of squared success probabilities.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.ComplexBernoulliProduct

open scoped BigOperators Topology
open Filter

/-- Products of contractions accumulate at most the sum of their factor errors. -/
theorem contraction_product_difference {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (f g : ι → ℂ) (hf : ∀ i ∈ s, ‖f i‖ ≤ 1) (hg : ∀ i ∈ s, ‖g i‖ ≤ 1) :
    ‖∏ i ∈ s, f i - ∏ i ∈ s, g i‖ ≤ ∑ i ∈ s, ‖f i - g i‖ := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s has ih =>
    have hfa := hf a (Finset.mem_insert_self _ _)
    have hgs : ∀ i ∈ s, ‖g i‖ ≤ 1 := fun i hi ↦ hg i (Finset.mem_insert_of_mem hi)
    have hprod : ‖∏ i ∈ s, g i‖ ≤ 1 :=
      (Finset.norm_prod_le s g).trans (Finset.prod_le_one (fun i _ ↦ norm_nonneg _) hgs)
    have hi := ih (fun i hi ↦ hf i (Finset.mem_insert_of_mem hi)) hgs
    rw [Finset.prod_insert has, Finset.prod_insert has, Finset.sum_insert has]
    calc
      _ = ‖f a * (∏ i ∈ s, f i - ∏ i ∈ s, g i) +
          (f a - g a) * ∏ i ∈ s, g i‖ := by congr 1; ring
      _ ≤ ‖f a‖ * ‖∏ i ∈ s, f i - ∏ i ∈ s, g i‖ +
          ‖f a - g a‖ * ‖∏ i ∈ s, g i‖ := by
        simpa only [norm_mul] using norm_add_le
          (f a * (∏ i ∈ s, f i - ∏ i ∈ s, g i)) ((f a - g a) * ∏ i ∈ s, g i)
      _ ≤ 1 * (∑ i ∈ s, ‖f i - g i‖) + ‖f a - g a‖ * 1 := by
        exact add_le_add (mul_le_mul hfa hi (norm_nonneg _) (by norm_num))
          (mul_le_mul_of_nonneg_left hprod (norm_nonneg _))
      _ = _ := by ring

/-- Every Bernoulli characteristic factor is a convex combination of contractions. -/
theorem bernoulli_factor_norm (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (w : ℂ) (hw : ‖w‖ ≤ 1) : ‖1 + (p : ℂ) * (w - 1)‖ ≤ 1 := by
  have heq : 1 + (p : ℂ) * (w - 1) = (1 - p) • (1 : ℂ) + p • w := by
    simp only [Complex.real_smul, Complex.ofReal_sub, Complex.ofReal_one]
    ring
  rw [heq]
  calc
    _ ≤ ‖(1 - p) • (1 : ℂ)‖ + ‖p • w‖ := norm_add_le _ _
    _ = (1 - p) + p * ‖w‖ := by
      simp only [norm_smul, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hp1),
        abs_of_nonneg hp0, norm_one, mul_one]
    _ ≤ 1 := by nlinarith

/-- Poisson characteristic factors are contractions as well. -/
theorem poisson_factor_norm (p : ℝ) (hp0 : 0 ≤ p) (w : ℂ) (hw : ‖w‖ ≤ 1) :
    ‖Complex.exp ((p : ℂ) * (w - 1))‖ ≤ 1 := by
  rw [Complex.norm_exp, Real.exp_le_one_iff]
  have hre : w.re - 1 ≤ 0 := by linarith [Complex.re_le_norm w]
  simpa only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.sub_re, Complex.one_re, zero_mul, sub_zero] using
      mul_nonpos_of_nonneg_of_nonpos hp0 hre

/-- The exact second-order Taylor bound for one small Bernoulli factor. -/
theorem factor_error (p : ℝ) (hp : 0 ≤ p) (z : ℂ) (hsmall : p * ‖z‖ ≤ 1) :
    ‖1 + (p : ℂ) * z - Complex.exp ((p : ℂ) * z)‖ ≤ p ^ 2 * ‖z‖ ^ 2 := by
  have hn : ‖(p : ℂ) * z‖ ≤ 1 := by
    simpa only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hp] using hsmall
  have heq : 1 + (p : ℂ) * z - Complex.exp ((p : ℂ) * z) =
      -(Complex.exp ((p : ℂ) * z) - 1 - (p : ℂ) * z) := by ring
  rw [heq, norm_neg]
  convert Complex.norm_exp_sub_one_sub_id_le hn using 1
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hp, mul_pow]

/-- Finite Poisson approximation with its exact probability-dependent error bound. -/
theorem bernoulli_product_error {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ι → ℝ) (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1)
    (w : ℂ) (hw : ‖w‖ ≤ 1) (hsmall : ∀ i, p i * ‖w - 1‖ ≤ 1) :
    ‖(∏ i, (1 + (p i : ℂ) * (w - 1))) -
      Complex.exp (((∑ i, p i : ℝ) : ℂ) * (w - 1))‖ ≤
      ‖w - 1‖ ^ 2 * ∑ i, p i ^ 2 := by
  have heq : Complex.exp (((∑ i, p i : ℝ) : ℂ) * (w - 1)) =
      ∏ i, Complex.exp ((p i : ℂ) * (w - 1)) := by
    rw [← Complex.exp_sum]
    congr 1
    simp only [Complex.ofReal_sum, Finset.sum_mul]
  rw [heq]
  calc
    _ ≤ ∑ i, ‖1 + (p i : ℂ) * (w - 1) - Complex.exp ((p i : ℂ) * (w - 1))‖ :=
      contraction_product_difference Finset.univ _ _
        (fun i _ ↦ bernoulli_factor_norm (p i) (hp0 i) (hp1 i) w hw)
        (fun i _ ↦ poisson_factor_norm (p i) (hp0 i) w hw)
    _ ≤ ∑ i, p i ^ 2 * ‖w - 1‖ ^ 2 :=
      Finset.sum_le_sum (fun i _ ↦ factor_error (p i) (hp0 i) (w - 1) (hsmall i))
    _ = _ := by rw [← Finset.sum_mul, mul_comm]

end Descent.Portability.ComplexBernoulliProduct
