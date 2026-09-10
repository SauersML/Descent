/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.DiploidEffectLaw

assert_below Descent.Decision Descent.Program

/-!
An explicit tensor Bernstein inverse for the diploid genotype-to-mean map.
Every coordinatewise quadratic polynomial is realized by one phenotype map,
and the realizing map is reconstructed exactly from the three-point tensor
frequency grid. This algebraic representation theorem is separate from the
analytic converse that converts differential field conditions on an open box
into a coordinatewise quadratic potential.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.DiploidBernsteinLaw

open DiploidEffectLaw

variable {D : Type*} [Fintype D] [DecidableEq D]

/-- Inverse of the degree-two Bernstein evaluation matrix at 0, 1/2, 1. -/
noncomputable def inverseEntry (g x : Fin 3) : ℝ :=
  if g.val = 0 then (if x.val = 0 then 1 else 0)
  else if g.val = 1 then (if x.val = 1 then 2 else -1 / 2)
  else (if x.val = 2 then 1 else 0)

theorem inverseEntry_contract (g h : Fin 3) :
    (∑ x : Fin 3, inverseEntry g x * hweMass ((x : ℝ) / 2) h) =
      if g = h then 1 else 0 := by
  fin_cases g <;> fin_cases h <;> norm_num [inverseEntry, hweMass, Fin.sum_univ_succ]

noncomputable def grid (x : D → Fin 3) : D → ℝ := fun i ↦ (x i : ℝ) / 2

noncomputable def recover (values : (D → Fin 3) → ℝ) (g : D → Fin 3) : ℝ :=
  ∑ x, (∏ i, inverseEntry (g i) (x i)) * values x

omit [DecidableEq D] in
private theorem tensor_delta (g h : D → Fin 3) :
    (∏ i, if g i = h i then (1 : ℝ) else 0) = if g = h then 1 else 0 := by
  classical
  by_cases he : g = h
  · subst h
    simp
  · have hn : ∃ i, g i ≠ h i := not_forall.mp (fun hall ↦ he (funext hall))
    obtain ⟨i, hi⟩ := hn
    rw [if_neg he]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)

/-- A product inverse remains an inverse in arbitrary finite dimension. -/
theorem tensor_inverse_contract (g h : D → Fin 3) :
    (∑ x : D → Fin 3, (∏ i, inverseEntry (g i) (x i)) * genotypeMass (grid x) h) =
      if g = h then 1 else 0 := by
  classical
  simp only [genotypeMass, grid, ← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun (i : D) (x : Fin 3) ↦
    inverseEntry (g i) x * hweMass ((x : ℝ) / 2) (h i))]
  simp_rw [inverseEntry_contract]
  exact tensor_delta g h

/-- Exact reconstruction of every fixed genotype-phenotype map from its mean surface. -/
theorem recover_phenotypeMean (f : (D → Fin 3) → ℝ) :
    recover (fun x ↦ phenotypeMean f (grid x)) = f := by
  classical
  funext g
  unfold recover phenotypeMean
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  calc
    (∑ h, ∑ x, (∏ i, inverseEntry (g i) (x i)) * (genotypeMass (grid x) h * f h)) =
        ∑ h, (∑ x, (∏ i, inverseEntry (g i) (x i)) * genotypeMass (grid x) h) * f h := by
      apply Finset.sum_congr rfl
      intro h _
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro x _
      ring
    _ = f g := by simp [tensor_inverse_contract]

/-- Two fixed mechanisms with the same complete mean surface coincide. -/
theorem phenotypeMean_injective : Function.Injective
    (fun f : (D → Fin 3) → ℝ ↦ phenotypeMean f) := by
  intro f h he
  change phenotypeMean f = phenotypeMean h at he
  have hg : (fun x ↦ phenotypeMean f (grid x)) = fun x ↦ phenotypeMean h (grid x) := by
    rw [he]
  have hr := congrArg recover hg
  simpa only [recover_phenotypeMean] using hr

/-- A monomial of degree zero, one or two in one frequency has these Bernstein coefficients. -/
noncomputable def monomialEntry (degree dosage : Fin 3) : ℝ :=
  if degree.val = 0 then 1 else if degree.val = 1 then (dosage : ℝ) / 2
  else if dosage.val = 2 then 1 else 0

theorem monomialEntry_reconstruct (degree : Fin 3) (p : ℝ) :
    (∑ g : Fin 3, hweMass p g * monomialEntry degree g) = p ^ degree.val := by
  fin_cases degree <;> norm_num [monomialEntry, hweMass, Fin.sum_univ_succ] <;> ring

/-- All tensor-product polynomials of degree at most two in each coordinate. -/
noncomputable def tensorQuadratic (coefficients : (D → Fin 3) → ℝ) (p : D → ℝ) : ℝ :=
  ∑ degree, coefficients degree * ∏ i, p i ^ (degree i).val

noncomputable def realizingMap (coefficients : (D → Fin 3) → ℝ) (g : D → Fin 3) : ℝ :=
  ∑ degree, coefficients degree * ∏ i, monomialEntry (degree i) (g i)

/-- Every coordinatewise quadratic potential has an explicit fixed diploid realization. -/
theorem realizingMap_mean (coefficients : (D → Fin 3) → ℝ) :
    phenotypeMean (realizingMap coefficients) = tensorQuadratic coefficients := by
  funext p
  unfold phenotypeMean realizingMap tensorQuadratic
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro degree _
  calc
    (∑ g, genotypeMass p g *
        (coefficients degree * ∏ i, monomialEntry (degree i) (g i))) =
      coefficients degree * ∑ g : D → Fin 3, ∏ i,
        hweMass (p i) (g i) * monomialEntry (degree i) (g i) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro g _
      simp only [genotypeMass, Finset.prod_mul_distrib]
      ring
    _ = coefficients degree * ∏ i, p i ^ (degree i).val := by
      rw [← Fintype.prod_sum (fun (i : D) (g : Fin 3) ↦
        hweMass (p i) g * monomialEntry (degree i) g)]
      simp_rw [monomialEntry_reconstruct]

/-- The explicit realization is unique, not just an existence witness. -/
theorem realizingMap_unique (coefficients : (D → Fin 3) → ℝ)
    (f : (D → Fin 3) → ℝ) (hf : phenotypeMean f = tensorQuadratic coefficients) :
    f = realizingMap coefficients := by
  apply phenotypeMean_injective
  change phenotypeMean f = phenotypeMean (realizingMap coefficients)
  rw [hf, realizingMap_mean]

/-- Monomial coefficients of each diploid Bernstein basis polynomial. -/
noncomputable def powerEntry (dosage degree : Fin 3) : ℝ :=
  if dosage.val = 0 then (if degree.val = 1 then -2 else 1)
  else if dosage.val = 1 then (if degree.val = 0 then 0 else if degree.val = 1 then 2 else -2)
  else if degree.val = 2 then 1 else 0

theorem powerEntry_expand (g : Fin 3) (p : ℝ) :
    hweMass p g = ∑ degree : Fin 3, powerEntry g degree * p ^ degree.val := by
  fin_cases g <;> norm_num [hweMass, powerEntry, Fin.sum_univ_succ] <;> ring

noncomputable def meanCoefficients (f : (D → Fin 3) → ℝ) (degree : D → Fin 3) : ℝ :=
  ∑ g, f g * ∏ i, powerEntry (g i) (degree i)

/-- Every fixed diploid mechanism has a coordinatewise degree-two mean polynomial. -/
theorem phenotypeMean_polynomial (f : (D → Fin 3) → ℝ) :
    phenotypeMean f = tensorQuadratic (meanCoefficients f) := by
  funext p
  unfold phenotypeMean genotypeMass
  simp_rw [powerEntry_expand, Fintype.prod_sum]
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  unfold tensorQuadratic meanCoefficients
  apply Finset.sum_congr rfl
  intro degree _
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro g _
  rw [Finset.prod_mul_distrib]
  ring

/-- Complete algebraic characterization of mean surfaces for the independent
HWE experiment. The analytic vector-field compatibility converse is separate. -/
theorem mean_surface_iff_tensor_quadratic (F : (D → ℝ) → ℝ) :
    (∃ f, phenotypeMean f = F) ↔ ∃ coefficients, tensorQuadratic coefficients = F := by
  constructor
  · rintro ⟨f, rfl⟩
    exact ⟨meanCoefficients f, (phenotypeMean_polynomial f).symm⟩
  · rintro ⟨coefficients, rfl⟩
    exact ⟨realizingMap coefficients, realizingMap_mean coefficients⟩

/-- Adding a constant to every genotype phenotype adds the same constant to the mean surface. -/
theorem phenotypeMean_add_constant (f : (D → Fin 3) → ℝ) (c : ℝ) (p : D → ℝ) :
    phenotypeMean (fun g ↦ f g + c) p = phenotypeMean f p + c := by
  simp only [phenotypeMean, mul_add, Finset.sum_add_distrib, ← Finset.sum_mul,
    genotypeMass_sum, one_mul]

/-- The additive constant of a mean potential is exactly the additive constant
of its realizing phenotype map; there are no further global ambiguities. -/
theorem mean_difference_constant_iff (f h : (D → Fin 3) → ℝ) (c : ℝ) :
    (∀ p, phenotypeMean f p = phenotypeMean h p + c) ↔ ∀ g, f g = h g + c := by
  constructor
  · intro he
    have hm : phenotypeMean f = phenotypeMean (fun g ↦ h g + c) := by
      funext p
      rw [phenotypeMean_add_constant, he]
    exact congrFun (phenotypeMean_injective hm)
  · intro he p
    rw [show f = (fun g ↦ h g + c) from funext he, phenotypeMean_add_constant]

end Descent.Portability.DiploidBernsteinLaw
