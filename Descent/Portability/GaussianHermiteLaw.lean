/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.GaussianPolynomialMoments
import Mathlib.MeasureTheory.Integral.Pi

assert_below Descent.Decision Descent.Program

/-!
Low-order Hermite polynomials and their tensor products under an actual product
Gaussian law. Orthogonality and squared norms are derived from Gaussian moments.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.GaussianHermiteLaw

open MeasureTheory ProbabilityTheory GaussianPolynomialMoments Polynomial
open scoped BigOperators

theorem integrable_power (variance : NNReal) (n : ℕ) :
    Integrable (fun x : ℝ ↦ x ^ n) (gaussianReal 0 variance) := by
  simpa using integrable_pow_mul_exp_of_mem_interior_integrableExpSet
    (X := fun x : ℝ ↦ x) (μ := gaussianReal 0 variance) (v := 0) (by simp) n

theorem integrable_polynomial (variance : NNReal) (p : Polynomial ℝ) :
    Integrable (fun x ↦ p.eval x) (gaussianReal 0 variance) := by
  induction p using Polynomial.induction_on' with
  | monomial n a =>
    simpa only [eval_monomial] using (integrable_power variance n).const_mul a
  | add p q hp hq => simpa only [eval_add] using hp.add hq

noncomputable def integratePolynomial (variance : NNReal) : Polynomial ℝ →ₗ[ℝ] ℝ where
  toFun p := ∫ x, p.eval x ∂gaussianReal 0 variance
  map_add' p q := by
    simp only [eval_add]
    exact integral_add (integrable_polynomial variance p) (integrable_polynomial variance q)
  map_smul' scalar p := by simp [eval_smul, integral_const_mul]

theorem integratePolynomial_X_pow (variance : NNReal) (n : ℕ) :
    integratePolynomial variance (X ^ n) = (momentPolynomial variance n).eval 0 := by
  simpa only [integratePolynomial, LinearMap.coe_mk, AddHom.coe_mk, eval_pow, eval_X] using
    power_moment variance n

theorem integratePolynomial_C (variance : NNReal) (c : ℝ) :
    integratePolynomial variance (C c) = c := by
  simp [integratePolynomial]

theorem integratePolynomial_one (variance : NNReal) : integratePolynomial variance 1 = 1 := by
  simpa only [C_1] using integratePolynomial_C variance 1

theorem integratePolynomial_X (variance : NNReal) : integratePolynomial variance X = 0 := by
  simp [integratePolynomial]

noncomputable def hermitePolynomial (order : Fin 3) : Polynomial ℝ :=
  if order = 0 then 1 else if order = 1 then X else X ^ 2 - 1

noncomputable def hermite (order : Fin 3) (x : ℝ) : ℝ := (hermitePolynomial order).eval x

def hermiteWeight (order : Fin 3) : ℝ := if order = 2 then 2 else 1

theorem hermite_polynomial_inner (a b : Fin 3) :
    integratePolynomial 1 (hermitePolynomial a * hermitePolynomial b) =
      if a = b then hermiteWeight a else 0 := by
  fin_cases a <;> fin_cases b <;>
    norm_num [hermitePolynomial, hermiteWeight, mul_sub, sub_mul, ← pow_add,
      show (X : Polynomial ℝ) * X = X ^ 2 by ring,
      show (X : Polynomial ℝ) * X ^ 2 = X ^ 3 by ring,
      show (X : Polynomial ℝ) ^ 2 * X = X ^ 3 by ring,
      show (X : Polynomial ℝ) ^ 2 * X ^ 2 = X ^ 4 by ring,
      integratePolynomial_one, integratePolynomial_X, integratePolynomial_X_pow,
      integratePolynomial_C, momentPolynomial, derivative_mul]
  all_goals decide

theorem hermite_inner (a b : Fin 3) :
    (∫ x : ℝ, hermite a x * hermite b x ∂gaussianReal 0 1) =
      if a = b then hermiteWeight a else 0 := by
  simpa only [integratePolynomial, LinearMap.coe_mk, AddHom.coe_mk, eval_mul, hermite] using
    hermite_polynomial_inner a b

variable {D I : Type*} [Fintype D] [Fintype I]

noncomputable def tensorHermite (degree : D → Fin 3) (x : D → ℝ) : ℝ :=
  ∏ i, hermite (degree i) (x i)

noncomputable def productGaussian (D : Type*) [Fintype D] : Measure (D → ℝ) :=
  Measure.pi (fun _ : D ↦ gaussianReal 0 1)

theorem tensor_pair_integrable (a b : D → Fin 3) :
    Integrable (fun x ↦ tensorHermite a x * tensorHermite b x) (productGaussian D) := by
  have hi := Integrable.fintype_prod
    (fun i : D ↦ integrable_polynomial 1 (hermitePolynomial (a i) * hermitePolynomial (b i)))
  simpa only [eval_mul, ← Finset.prod_mul_distrib, hermite, tensorHermite, productGaussian] using hi

theorem tensor_inner (a b : D → Fin 3) :
    (∫ x, tensorHermite a x * tensorHermite b x ∂productGaussian D) =
      if a = b then ∏ i, hermiteWeight (a i) else 0 := by
  classical
  simp only [tensorHermite, ← Finset.prod_mul_distrib, productGaussian]
  rw [integral_fintype_prod_eq_prod (fun i x ↦ hermite (a i) x * hermite (b i) x)]
  simp only [hermite_inner]
  by_cases hab : a = b
  · simp [hab]
  · rw [if_neg hab]
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hab
    exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)

noncomputable def tensorCombination (degree : I → D → Fin 3) (coefficient : I → ℝ)
    (x : D → ℝ) : ℝ :=
  ∑ i, coefficient i * tensorHermite (degree i) x

theorem tensorCombination_squared_integral (degree : I → D → Fin 3)
    (hdegree : Function.Injective degree) (coefficient : I → ℝ) :
    (∫ x, tensorCombination degree coefficient x ^ 2 ∂productGaussian D) =
      ∑ i, coefficient i ^ 2 * ∏ j, hermiteWeight (degree i j) := by
  classical
  have he (x : D → ℝ) : tensorCombination degree coefficient x ^ 2 =
      ∑ i, ∑ j, (coefficient i * coefficient j) *
        (tensorHermite (degree i) x * tensorHermite (degree j) x) := by
    simp only [tensorCombination, pow_two, Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  simp_rw [he]
  rw [integral_finset_sum]
  · apply Finset.sum_congr rfl
    intro i _
    rw [integral_finset_sum]
    · simp only [integral_const_mul, tensor_inner, hdegree.eq_iff, mul_ite, mul_zero]
      simp [pow_two]
    · intro j _
      exact (tensor_pair_integrable (degree i) (degree j)).const_mul _
  · intro i _
    exact integrable_finset_sum _ (fun j _ ↦
      (tensor_pair_integrable (degree i) (degree j)).const_mul _)

end Descent.Portability.GaussianHermiteLaw
