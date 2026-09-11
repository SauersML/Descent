/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.DiploidBoxCompatibilityLaw

assert_below Descent.Decision Descent.Program

/-!
Uniqueness of a fixed diploid phenotype map from its actual additive-effect field
on an arbitrary nonempty open frequency box. Interior-node interpolation extends
the locally constant difference of mean surfaces globally before the exact
Bernstein inverse recovers uniqueness modulo an additive constant.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.DiploidBoxUniquenessLaw

open Set DiploidEffectLaw DiploidBernsteinLaw TensorInterpolationLaw
open BoxDifferentialLaw BoxPolynomialExtensionLaw

variable {n : ℕ}

/-- Three distinct frequencies reproduce the diploid mass polynomial exactly. -/
theorem hweMass_interpolation (q : Fin 3 → ℝ) (hq : Function.Injective q)
    (x : ℝ) (g : Fin 3) :
    hweMass x g = ∑ k : Fin 3, lagrange q x k * hweMass (q k) g := by
  have hpoly (t : ℝ) : hweMass t g =
      powerEntry g 0 + powerEntry g 1 * t + powerEntry g 2 * t ^ 2 := by
    fin_cases g <;> norm_num [hweMass, powerEntry] <;> ring
  simp_rw [hpoly]
  exact lagrange_quadratic q hq _ _ _ x

private theorem mass_update (p : Fin n → ℝ) (i : Fin n) (t : ℝ)
    (g : Fin n → Fin 3) :
    genotypeMass (Function.update p i t) g =
      hweMass t (g i) * ∏ j ∈ Finset.univ.erase i, hweMass (p j) (g j) := by
  unfold genotypeMass
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
  simp only [Function.update_self]
  congr 1
  apply Finset.prod_congr rfl
  intro j hj
  rw [Function.update_of_ne (Finset.mem_erase.mp hj).1]

/-- A mean surface is reproduced by changing a single frequency to three arbitrary nodes. -/
theorem phenotypeMean_coordinate_interpolation (f : (Fin n → Fin 3) → ℝ)
    (p : Fin n → ℝ) (i : Fin n) (q : Fin 3 → ℝ) (hq : Function.Injective q) :
    phenotypeMean f p =
      ∑ k : Fin 3, lagrange q (p i) k * phenotypeMean f (Function.update p i (q k)) := by
  have hp : phenotypeMean f p =
      ∑ g, (hweMass (p i) (g i) *
        ∏ j ∈ Finset.univ.erase i, hweMass (p j) (g j)) * f g := by
    unfold phenotypeMean
    apply Finset.sum_congr rfl
    intro g _
    congr 1
    simpa only [Function.update_eq_self] using mass_update p i (p i) g
  rw [hp]
  simp_rw [hweMass_interpolation q hq (p i), Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  simp only [phenotypeMean, mass_update, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro g _
  ring

/-- The complete mean surface is determined by any interior tensor grid of three distinct nodes. -/
theorem phenotypeMean_tensor_interpolation (f : (Fin n → Fin 3) → ℝ)
    (node : Fin n → Fin 3 → ℝ) (hinj : ∀ i, Function.Injective (node i))
    (p : Fin n → ℝ) :
    phenotypeMean f p = ∑ g : Fin n → Fin 3,
      (∏ i, lagrange (node i) (p i) (g i)) * phenotypeMean f (fun i ↦ node i (g i)) := by
  apply tensor_interpolation n (fun _ ↦ univ) node (fun _ _ ↦ mem_univ _)
    (fun i ↦ lagrange (node i)) (phenotypeMean f) _ p (fun _ ↦ mem_univ _)
  intro q _ i
  exact phenotypeMean_coordinate_interpolation f q i (node i) (hinj i)

/-- Coordinate-update invariance on a box implies constancy on that same box. -/
theorem constant_on_box_of_update_invariant {lo hi : Fin n → ℝ}
    (F : (Fin n → ℝ) → ℝ)
    (hF : ∀ p, InBox lo hi p → ∀ i v, v ∈ Ioo (lo i) (hi i) →
      F (Function.update p i v) = F p)
    (p a : Fin n → ℝ) (hp : InBox lo hi p) (ha : InBox lo hi a) : F p = F a := by
  classical
  let mix := fun (s : Finset (Fin n)) i ↦ if i ∈ s then p i else a i
  have hmemb (s : Finset (Fin n)) : InBox lo hi (mix s) := by
    intro i
    by_cases h : i ∈ s
    · simpa only [mix, if_pos h] using hp i
    · simpa only [mix, if_neg h] using ha i
  have hall : ∀ s : Finset (Fin n), F (mix s) = F a := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp [mix]
    | @insert i s hi ih =>
      have hm : mix (insert i s) = Function.update (mix s) i (p i) := by
        funext j
        by_cases hji : j = i
        · subst j
          simp [mix]
        · simp [mix, hji]
      rw [hm, hF _ (hmemb s) i (p i) (hp i), ih]
  simpa [mix] using hall Finset.univ

/-- Identical actual additive effects make the two mean surfaces differ by a constant on the box. -/
theorem equal_effects_mean_difference {lo hi : Fin n → ℝ}
    (hfreq : ∀ p, InBox lo hi p → ∀ i, 0 < p i ∧ p i < 1)
    (f g : (Fin n → Fin 3) → ℝ)
    (he : ∀ p (hp : InBox lo hi p) i,
      additiveEffect f p (fun j ↦ ⟨(hfreq p hp j).1.le, (hfreq p hp j).2.le⟩) i =
      additiveEffect g p (fun j ↦ ⟨(hfreq p hp j).1.le, (hfreq p hp j).2.le⟩) i)
    (p a : Fin n → ℝ) (hp : InBox lo hi p) (ha : InBox lo hi a) :
    phenotypeMean f p - phenotypeMean g p = phenotypeMean f a - phenotypeMean g a := by
  apply constant_on_box_of_update_invariant (lo := lo) (hi := hi)
    (fun q ↦ phenotypeMean f q - phenotypeMean g q) _ p a hp ha
  intro q hq i v hv
  have hd (x : ℝ) (hx : x ∈ Ioo (lo i) (hi i)) :
      HasDerivAt (fun t ↦ phenotypeMean f (Function.update q i t) -
        phenotypeMean g (Function.update q i t)) 0 x := by
    let r := Function.update q i x
    have hr : InBox lo hi r := update_mem_box hq i hx
    have hf := phenotypeMean_hasDerivAt f r i
    have hg := phenotypeMean_hasDerivAt g r i
    have hef := derivative_eq_twice_effect f r
      (fun j ↦ ⟨(hfreq r hr j).1.le, (hfreq r hr j).2.le⟩) i (hfreq r hr i)
    have heg := derivative_eq_twice_effect g r
      (fun j ↦ ⟨(hfreq r hr j).1.le, (hfreq r hr j).2.le⟩) i (hfreq r hr i)
    have heq : partialMean f r i = partialMean g r i := by
      rw [← hf.deriv, hef, ← hg.deriv, heg, he r hr i]
    have h := hf.sub hg
    rw [heq, sub_self] at h
    simpa only [r, Function.update_idem, Function.update_self] using h
  have h := isOpen_Ioo.is_const_of_deriv_eq_zero isPreconnected_Ioo
    (fun x hx ↦ (hd x hx).differentiableAt.differentiableWithinAt)
    (fun x hx ↦ (hd x hx).deriv) hv (hq i)
  simpa only [Function.update_eq_self] using h

/-- Equality up to a constant on an open box determines the fixed maps globally. -/
theorem box_mean_difference_determines_map {lo hi : Fin n → ℝ}
    (hwidth : ∀ i, lo i < hi i) (f g : (Fin n → Fin 3) → ℝ) (c : ℝ)
    (he : ∀ p, InBox lo hi p → phenotypeMean f p = phenotypeMean g p + c) :
    ∀ dosage, f dosage = g dosage + c := by
  apply (mean_difference_constant_iff f g c).mp
  intro p
  let node := interiorNodes lo hi
  have hn := interiorNodes_injective lo hi hwidth
  rw [phenotypeMean_tensor_interpolation f node hn p,
    phenotypeMean_tensor_interpolation g node hn p]
  have hgrid (d : Fin n → Fin 3) :
      phenotypeMean f (fun i ↦ node i (d i)) =
        phenotypeMean g (fun i ↦ node i (d i)) + c :=
    he _ (fun i ↦ interiorNodes_mem lo hi hwidth i (d i))
  simp_rw [hgrid, mul_add, Finset.sum_add_distrib]
  congr 1
  rw [← Finset.sum_mul]
  have hw : (∑ d : Fin n → Fin 3, ∏ i, lagrange (node i) (p i) (d i)) = 1 := by
    rw [← Fintype.prod_sum]
    have hi (i : Fin n) : (∑ k : Fin 3, lagrange (node i) (p i) k) = 1 := by
      simpa using (lagrange_quadratic (node i) (hn i) 1 0 0 (p i)).symm
    simp_rw [hi]
    simp
  rw [hw, one_mul]

/-- Equal actual regression fields on the original box force uniqueness modulo one constant. -/
theorem diploid_box_unique_modulo_constant {lo hi : Fin n → ℝ}
    (hwidth : ∀ i, lo i < hi i)
    (hfreq : ∀ p, InBox lo hi p → ∀ i, 0 < p i ∧ p i < 1)
    (f g : (Fin n → Fin 3) → ℝ)
    (he : ∀ p (hp : InBox lo hi p) i,
      additiveEffect f p (fun j ↦ ⟨(hfreq p hp j).1.le, (hfreq p hp j).2.le⟩) i =
      additiveEffect g p (fun j ↦ ⟨(hfreq p hp j).1.le, (hfreq p hp j).2.le⟩) i) :
    ∃ c : ℝ, ∀ dosage, f dosage = g dosage + c := by
  let a := fun i ↦ interiorNodes lo hi i 0
  have ha : InBox lo hi a := fun i ↦ interiorNodes_mem lo hi hwidth i 0
  refine ⟨phenotypeMean f a - phenotypeMean g a, ?_⟩
  apply box_mean_difference_determines_map hwidth f g
  intro p hp
  have h := equal_effects_mean_difference hfreq f g he p a hp ha
  linarith

end Descent.Portability.DiploidBoxUniquenessLaw
