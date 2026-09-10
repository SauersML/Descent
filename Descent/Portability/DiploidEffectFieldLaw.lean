/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.DiploidEffectLaw
import Mathlib.Analysis.Calculus.ContDiff.Operations

assert_below Descent.Decision Descent.Program

/-!
Differential compatibility conditions forced by one fixed independent-HWE
mechanism. The field is constructed from the derivative of the actual mean
surface, and mixed derivatives are computed explicitly from tensor probabilities.
The analytic converse on a general open rectangle is not assumed here.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.DiploidEffectFieldLaw

open DiploidEffectLaw
open scoped ContDiff

variable {D : Type*} [Fintype D] [DecidableEq D]

noncomputable def effectField (f : (D → Fin 3) → ℝ) (p : D → ℝ) (i : D) : ℝ :=
  partialMean f p i / 2

/-- The smooth field equals the joint additive effect throughout the probability interior. -/
theorem effectField_eq_additiveEffect (f : (D → Fin 3) → ℝ) (p : D → ℝ)
    (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1) (i : D) (hi : 0 < p i ∧ p i < 1) :
    effectField f p i = additiveEffect f p hp i := by
  have he := derivative_eq_twice_effect f p hp i hi
  rw [(phenotypeMean_hasDerivAt f p i).deriv] at he
  unfold effectField
  linarith

noncomputable def hweSecond (g : Fin 3) : ℝ := if g.val = 1 then -4 else 2

theorem hweDerivative_hasDerivAt (p : ℝ) (g : Fin 3) :
    HasDerivAt (fun t ↦ hweDerivative t g) (hweSecond g) p := by
  fin_cases g
  · convert ((hasDerivAt_id p).sub_const 1).const_mul 2 using 1
    simp [hweSecond]
  · convert (hasDerivAt_const p (2 : ℝ)).sub ((hasDerivAt_id p).const_mul 4) using 1
    simp [hweSecond]
  · convert (hasDerivAt_id p).const_mul 2 using 1
    simp [hweSecond]

private theorem erased_product_update (p : D → ℝ) (i j : D) (hij : i ≠ j)
    (t : ℝ) (g : D → Fin 3) :
    (∏ k ∈ Finset.univ.erase i, hweMass (Function.update p j t k) (g k)) =
      hweMass t (g j) * ∏ k ∈ (Finset.univ.erase i).erase j, hweMass (p k) (g k) := by
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_erase.mpr ⟨Ne.symm hij, Finset.mem_univ j⟩)]
  simp only [Function.update_self]
  congr 1
  apply Finset.prod_congr rfl
  intro k hk
  rw [Function.update_of_ne (Finset.ne_of_mem_erase hk)]

private theorem erased_product_self (p : D → ℝ) (i : D) (t : ℝ) (g : D → Fin 3) :
    (∏ k ∈ Finset.univ.erase i, hweMass (Function.update p i t k) (g k)) =
      ∏ k ∈ Finset.univ.erase i, hweMass (p k) (g k) := by
  apply Finset.prod_congr rfl
  intro k hk
  rw [Function.update_of_ne (Finset.ne_of_mem_erase hk)]

/-- Cross derivatives are explicit symmetric tensor sums. -/
theorem effectField_cross_hasDerivAt (f : (D → Fin 3) → ℝ) (p : D → ℝ)
    (i j : D) (hij : i ≠ j) :
    HasDerivAt (fun t ↦ effectField f (Function.update p j t) i)
      ((∑ g, hweDerivative (p i) (g i) * hweDerivative (p j) (g j) *
        (∏ k ∈ (Finset.univ.erase i).erase j, hweMass (p k) (g k)) * f g) / 2) (p j) := by
  unfold effectField partialMean
  simp_rw [Function.update_of_ne hij, erased_product_update p i j hij]
  apply HasDerivAt.div_const
  apply HasDerivAt.fun_sum
  intro g _
  convert (((hweMass_hasDerivAt (p j) (g j)).mul_const _).const_mul
    (hweDerivative (p i) (g i))).mul_const (f g) using 1
  ring

/-- The curl vanishes as a consequence of the fixed diploid mechanism. -/
theorem effectField_cross_derivatives (f : (D → Fin 3) → ℝ) (p : D → ℝ) (i j : D) :
    deriv (fun t ↦ effectField f (Function.update p j t) i) (p j) =
      deriv (fun t ↦ effectField f (Function.update p i t) j) (p i) := by
  by_cases hij : i = j
  · subst j
    rfl
  rw [(effectField_cross_hasDerivAt f p i j hij).deriv,
    (effectField_cross_hasDerivAt f p j i (Ne.symm hij)).deriv]
  congr 1
  apply Finset.sum_congr rfl
  intro g _
  rw [Finset.erase_right_comm]
  ring

/-- The field is affine in its own allele-frequency coordinate. -/
theorem effectField_self_hasDerivAt (f : (D → Fin 3) → ℝ) (p : D → ℝ)
    (i : D) (t : ℝ) :
    HasDerivAt (fun s ↦ effectField f (Function.update p i s) i)
      ((∑ g, hweSecond (g i) * (∏ k ∈ Finset.univ.erase i, hweMass (p k) (g k)) * f g) / 2) t := by
  unfold effectField partialMean
  simp_rw [Function.update_self, erased_product_self]
  apply HasDerivAt.div_const
  apply HasDerivAt.fun_sum
  intro g _
  exact ((hweDerivative_hasDerivAt t (g i)).mul_const _).mul_const _

/-- The second own-coordinate derivative condition in equation (5.2) is exact. -/
theorem effectField_own_second_derivative_zero (f : (D → Fin 3) → ℝ) (p : D → ℝ) (i : D) :
    deriv (fun t ↦ deriv (fun s ↦ effectField f (Function.update p i s) i) t) (p i) = 0 := by
  simp_rw [(effectField_self_hasDerivAt f p i _).deriv]
  exact deriv_const _ _

/-- Every realized field is smooth on the whole real frequency space. -/
theorem effectField_contDiff (f : (D → Fin 3) → ℝ) (i : D) :
    ContDiff ℝ ∞ (fun p : D → ℝ ↦ effectField f p i) := by
  have hm (g : D → Fin 3) (k : D) :
      ContDiff ℝ ∞ (fun p : D → ℝ ↦ hweMass (p k) (g k)) := by
    unfold hweMass
    split_ifs <;> fun_prop
  have hd (g : D → Fin 3) :
      ContDiff ℝ ∞ (fun p : D → ℝ ↦ hweDerivative (p i) (g i)) := by
    unfold hweDerivative
    split_ifs <;> fun_prop
  have hp (g : D → Fin 3) (s : Finset D) :
      ContDiff ℝ ∞ (fun p : D → ℝ ↦ ∏ k ∈ s, hweMass (p k) (g k)) := by
    induction s using Finset.induction_on with
    | empty => simpa only [Finset.prod_empty] using (contDiff_const (c := (1 : ℝ)))
    | @insert k s hk ih =>
        simpa only [Finset.prod_insert hk] using (hm g k).mul ih
  unfold effectField partialMean
  apply ContDiff.div_const
  apply ContDiff.sum
  intro g _
  exact ((hd g).mul (hp g _)).mul contDiff_const

end Descent.Portability.DiploidEffectFieldLaw
