/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.ExactMetricEvaluation
import Mathlib.Analysis.Calculus.Deriv.Polynomial

assert_below Descent.Decision Descent.Program

/-!
The exact independent diploid HWE experiment underlying the effect-field
compatibility theorem. The derivative of its population phenotype mean is
computed from the actual genotype probabilities and identified with twice the
additive regression effect. This module does not postulate a covariance score
identity or identify arbitrary demographic change with linkage equilibrium.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.DiploidEffectLaw

open FiniteReportLaw

variable {D : Type*} [Fintype D] [DecidableEq D]

noncomputable def hweMass (p : ℝ) (g : Fin 3) : ℝ :=
  if g.val = 0 then (1 - p) ^ 2 else if g.val = 1 then 2 * p * (1 - p) else p ^ 2

noncomputable def hweDerivative (p : ℝ) (g : Fin 3) : ℝ :=
  if g.val = 0 then 2 * (p - 1) else if g.val = 1 then 2 - 4 * p else 2 * p

theorem hweMass_sum (p : ℝ) : ∑ g : Fin 3, hweMass p g = 1 := by
  norm_num [Fin.sum_univ_succ, hweMass]
  ring

theorem hweMass_mean (p : ℝ) : ∑ g : Fin 3, hweMass p g * (g : ℝ) = 2 * p := by
  norm_num [Fin.sum_univ_succ, hweMass]
  ring

theorem hweMass_second_moment (p : ℝ) :
    ∑ g : Fin 3, hweMass p g * (g : ℝ) ^ 2 = 2 * p + 2 * p ^ 2 := by
  norm_num [Fin.sum_univ_succ, hweMass]
  ring

theorem hweMass_nonneg (p : ℝ) (hp : 0 ≤ p ∧ p ≤ 1) (g : Fin 3) : 0 ≤ hweMass p g := by
  unfold hweMass
  split_ifs
  · exact sq_nonneg _
  · exact mul_nonneg (mul_nonneg (by norm_num) hp.1) (sub_nonneg.mpr hp.2)
  · exact sq_nonneg _

/-- Exact derivative of each HWE probability, including the boundary parameters. -/
theorem hweMass_hasDerivAt (p : ℝ) (g : Fin 3) :
    HasDerivAt (fun t ↦ hweMass t g) (hweDerivative p g) p := by
  fin_cases g
  · convert ((hasDerivAt_const p (1 : ℝ)).sub (hasDerivAt_id p)).pow 2 using 1
    simp [hweDerivative]
    ring
  · convert (((hasDerivAt_id p).const_mul 2).mul
      ((hasDerivAt_const p (1 : ℝ)).sub (hasDerivAt_id p))) using 1
    simp [hweDerivative]
    ring
  · convert (hasDerivAt_id p).pow 2 using 1
    simp [hweDerivative]

/-- Multiplication removes the score denominator without any interior assumption. -/
theorem hwe_score_identity (p : ℝ) (g : Fin 3) :
    p * (1 - p) * hweDerivative p g = ((g : ℝ) - 2 * p) * hweMass p g := by
  fin_cases g <;> norm_num [hweDerivative, hweMass] <;> ring

noncomputable def genotypeMass (p : D → ℝ) (g : D → Fin 3) : ℝ := ∏ i, hweMass (p i) (g i)

private theorem sum_product (a : D → Fin 3 → ℝ) :
    (∑ g : D → Fin 3, ∏ i, a i (g i)) = ∏ i, ∑ v : Fin 3, a i v := by
  simpa using Finset.sum_prod_piFinset (Finset.univ : Finset (Fin 3)) a

theorem genotypeMass_sum (p : D → ℝ) : ∑ g : D → Fin 3, genotypeMass p g = 1 := by
  unfold genotypeMass
  rw [sum_product]
  simp only [hweMass_sum, Finset.prod_const_one]

noncomputable def genotypeLaw (p : D → ℝ) (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1) :
    FiniteReportLaw (D → Fin 3) where
  mass := genotypeMass p
  mass_nonneg g := Finset.prod_nonneg (fun i _ ↦ hweMass_nonneg (p i) (hp i) (g i))
  mass_sum := genotypeMass_sum p

/-- Joint moments factor because the complete genotype law is a product law. -/
theorem genotype_product_moment (p : D → ℝ) (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1)
    (h : D → Fin 3 → ℝ) :
    (genotypeLaw p hp).expectation (fun g ↦ ∏ i, h i (g i)) =
      ∏ i, ∑ v : Fin 3, hweMass (p i) v * h i v := by
  simpa only [expectation, genotypeLaw, genotypeMass, Finset.prod_mul_distrib] using
    sum_product (fun i v ↦ hweMass (p i) v * h i v)

theorem genotype_mean (p : D → ℝ) (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1) (i : D) :
    (genotypeLaw p hp).expectation (fun g ↦ (g i : ℝ)) = 2 * p i := by
  have h := genotype_product_moment p hp (fun j v ↦ if j = i then (v : ℝ) else 1)
  simpa only [Fintype.prod_ite_eq', mul_ite, mul_one, Finset.sum_ite_irrel,
    hweMass_mean, hweMass_sum] using h

theorem genotype_second_moment (p : D → ℝ) (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1) (i : D) :
    (genotypeLaw p hp).expectation (fun g ↦ (g i : ℝ) ^ 2) = 2 * p i + 2 * p i ^ 2 := by
  have h := genotype_product_moment p hp (fun j v ↦ if j = i then (v : ℝ) ^ 2 else 1)
  simpa only [Fintype.prod_ite_eq', mul_ite, mul_one, Finset.sum_ite_irrel,
    hweMass_second_moment, hweMass_sum] using h

theorem genotype_variance (p : D → ℝ) (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1) (i : D) :
    (genotypeLaw p hp).variance (fun g ↦ (g i : ℝ)) = 2 * p i * (1 - p i) := by
  rw [variance_eq_rawMoments, genotype_mean, genotype_second_moment]
  ring

noncomputable def phenotypeMean (f : (D → Fin 3) → ℝ) (p : D → ℝ) : ℝ :=
  ∑ g, genotypeMass p g * f g

noncomputable def partialMean (f : (D → Fin 3) → ℝ) (p : D → ℝ) (i : D) : ℝ :=
  ∑ g, hweDerivative (p i) (g i) * (∏ j ∈ Finset.univ.erase i, hweMass (p j) (g j)) * f g

private theorem genotypeMass_update (p : D → ℝ) (i : D) (t : ℝ) (g : D → Fin 3) :
    genotypeMass (Function.update p i t) g =
      hweMass t (g i) * ∏ j ∈ Finset.univ.erase i, hweMass (p j) (g j) := by
  unfold genotypeMass
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
  simp only [Function.update_self]
  congr 1
  apply Finset.prod_congr rfl
  intro j hj
  rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]

/-- The exact coordinate derivative of the tensor-product phenotype expectation. -/
theorem phenotypeMean_hasDerivAt (f : (D → Fin 3) → ℝ) (p : D → ℝ) (i : D) :
    HasDerivAt (fun t ↦ phenotypeMean f (Function.update p i t)) (partialMean f p i) (p i) := by
  unfold phenotypeMean partialMean
  simp_rw [genotypeMass_update]
  apply HasDerivAt.fun_sum
  intro g _
  exact ((hweMass_hasDerivAt (p i) (g i)).mul_const _).mul_const _

/-- The derivative is the genotype/phenotype covariance divided by p(1-p),
proved by differentiating the law rather than assuming a regression identity. -/
theorem partialMean_covariance (f : (D → Fin 3) → ℝ) (p : D → ℝ)
    (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1) (i : D) :
    p i * (1 - p i) * partialMean f p i =
      (genotypeLaw p hp).covariance (fun g ↦ (g i : ℝ)) f := by
  rw [covariance_eq_rawMoments, genotype_mean]
  unfold partialMean expectation
  simp only [genotypeLaw]
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro g _
  have hs := hwe_score_identity (p i) (g i)
  have hm : genotypeMass p g =
      hweMass (p i) (g i) * ∏ j ∈ Finset.univ.erase i, hweMass (p j) (g j) := by
    simpa only [Function.update_eq_self] using genotypeMass_update p i (p i) g
  rw [hm]
  nlinarith [congrArg (fun x ↦ x *
    (∏ j ∈ Finset.univ.erase i, hweMass (p j) (g j)) * f g) hs]

noncomputable def additiveEffect (f : (D → Fin 3) → ℝ) (p : D → ℝ)
    (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1) (i : D) : ℝ :=
  (genotypeLaw p hp).covariance (fun g ↦ (g i : ℝ)) f / (2 * p i * (1 - p i))

/-- Equation (5.1) of the new report on its exact independent-HWE experiment. -/
theorem derivative_eq_twice_effect (f : (D → Fin 3) → ℝ) (p : D → ℝ)
    (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1) (i : D) (hi : 0 < p i ∧ p i < 1) :
    deriv (fun t ↦ phenotypeMean f (Function.update p i t)) (p i) =
      2 * additiveEffect f p hp i := by
  rw [(phenotypeMean_hasDerivAt f p i).deriv, additiveEffect,
    ← partialMean_covariance f p hp i]
  have hn : p i ≠ 0 := ne_of_gt hi.1
  have hc : 1 - p i ≠ 0 := ne_of_gt (sub_pos.mpr hi.2)
  field_simp

/-- Distinct dosage moments factor under the stipulated linkage-equilibrium law. -/
theorem genotype_cross_moment (p : D → ℝ) (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1)
    (i j : D) (hij : i ≠ j) :
    (genotypeLaw p hp).expectation (fun g ↦ (g i : ℝ) * (g j : ℝ)) =
      (2 * p i) * (2 * p j) := by
  have h := genotype_product_moment p hp (fun k v ↦
    (if k = i then (v : ℝ) else 1) * (if k = j then (v : ℝ) else 1))
  have hs (k : D) : (∑ v : Fin 3, hweMass (p k) v *
      ((if k = i then (v : ℝ) else 1) * (if k = j then (v : ℝ) else 1))) =
      (if k = i then 2 * p k else 1) * (if k = j then 2 * p k else 1) := by
    by_cases hi : k = i
    · subst k
      simp [hij, hweMass_mean]
    · by_cases hj : k = j
      · subst k
        simp [hi, hweMass_mean]
      · simp [hi, hj, hweMass_sum]
  simpa only [hs, Finset.prod_mul_distrib, Fintype.prod_ite_eq'] using h

/-- The entire joint dosage covariance matrix is diagonal with its exact HWE variance. -/
theorem genotype_covariance (p : D → ℝ) (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1) (i j : D) :
    (genotypeLaw p hp).covariance (fun g ↦ (g i : ℝ)) (fun g ↦ (g j : ℝ)) =
      if i = j then 2 * p i * (1 - p i) else 0 := by
  by_cases hij : i = j
  · subst j
    simpa only [if_pos rfl] using genotype_variance p hp i
  · rw [if_neg hij, covariance_eq_rawMoments, genotype_mean, genotype_mean,
      genotype_cross_moment p hp i j hij]
    ring

/-- These are the joint additive normal equations, derived from the genotype law. -/
theorem additiveEffect_normal_equations (f : (D → Fin 3) → ℝ) (p : D → ℝ)
    (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1) (hinterior : ∀ i, 0 < p i ∧ p i < 1) (i : D) :
    (∑ j, additiveEffect f p hp j *
      (genotypeLaw p hp).covariance (fun g ↦ (g j : ℝ)) (fun g ↦ (g i : ℝ))) =
      (genotypeLaw p hp).covariance (fun g ↦ (g i : ℝ)) f := by
  simp only [genotype_covariance, mul_ite, mul_zero, Finset.sum_ite_eq']
  simp only [Finset.mem_univ, ite_true, additiveEffect]
  exact div_mul_cancel₀ _ (ne_of_gt
    (mul_pos (mul_pos (by norm_num) (hinterior i).1) (sub_pos.mpr (hinterior i).2)))

/-- Interior allele frequencies make the normal-equation solution unique. Thus
these covariance quotients are the joint effects, not merely marginal summaries. -/
theorem additiveEffect_unique (f : (D → Fin 3) → ℝ) (p : D → ℝ)
    (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1) (hinterior : ∀ i, 0 < p i ∧ p i < 1)
    (weights : D → ℝ)
    (hnormal : ∀ i, (∑ j, weights j *
      (genotypeLaw p hp).covariance (fun g ↦ (g j : ℝ)) (fun g ↦ (g i : ℝ))) =
        (genotypeLaw p hp).covariance (fun g ↦ (g i : ℝ)) f) :
    weights = additiveEffect f p hp := by
  funext i
  have h := hnormal i
  simp only [genotype_covariance, mul_ite, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true] at h
  exact (eq_div_iff (ne_of_gt
    (mul_pos (mul_pos (by norm_num) (hinterior i).1) (sub_pos.mpr (hinterior i).2)))).mpr h

end Descent.Portability.DiploidEffectLaw
