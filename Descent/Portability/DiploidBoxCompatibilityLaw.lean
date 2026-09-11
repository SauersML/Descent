/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.BoxPolynomialExtensionLaw
import Descent.Portability.DiploidEffectFieldLaw

assert_below Descent.Decision Descent.Program

/-!
The analytic diploid-effect compatibility converse on a nonempty open box.
The potential is constructed by a justified radial integral, its coordinate
slices are proved quadratic, and interior tensor interpolation realizes it as
the mean of one fixed genotype-phenotype map under independent diploid HWE.
The endpoint is the actual additive regression coefficient, not a substitute field.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.DiploidBoxCompatibilityLaw

open Set BoxDifferentialLaw BoxPolynomialExtensionLaw RadialPotentialLaw TensorInterpolationLaw
open DiploidEffectLaw DiploidEffectFieldLaw

variable {n : ℕ}

/-- The constructed potential is separately quadratic by the original own-affinity condition. -/
theorem potential_separately_quadratic {lo hi : Fin n → ℝ} (hwidth : ∀ i, lo i < hi i)
    {b : Fin n → (Fin n → ℝ) → ℝ}
    (hb : ∀ i, ContDiffOn ℝ 2 (b i) (box lo hi))
    (hclosed : ClosedOnBox lo hi b) (hown : OwnAffineOnBox lo hi b)
    {a p : Fin n → ℝ} (ha : InBox lo hi a) (hp : InBox lo hi p) (j : Fin n) :
    ∃ A B C : ℝ, ∀ y ∈ Ioo (lo j) (hi j),
      potential (extension lo hi b) a (Function.update p j y) = A + B * y + C * y ^ 2 := by
  let P := potential (extension lo hi b) a
  let slope := deriv (fun x ↦ b j (Function.update p j x)) (p j)
  let Q := fun y ↦ P p + 2 * b j p * (y - p j) + slope * (y - p j) ^ 2
  have hP (y : ℝ) (hy : y ∈ Ioo (lo j) (hi j)) :
      HasDerivAt (fun x ↦ P (Function.update p j x)) (2 * b j (Function.update p j y)) y := by
    have h := box_potential_hasDerivAt hwidth hb hclosed hown ha (update_mem_box hp j hy) j
    simpa only [Function.update_idem, Function.update_self] using h
  have hQ (y : ℝ) : HasDerivAt Q (2 * b j p + 2 * slope * (y - p j)) y := by
    convert ((((hasDerivAt_id y).sub_const (p j)).const_mul (2 * b j p)).const_add
      (P p)).add ((((hasDerivAt_id y).sub_const (p j)).pow 2).const_mul slope) using 1
    simp only [id_eq]
    ring
  have heq : EqOn (fun y ↦ P (Function.update p j y)) Q (Ioo (lo j) (hi j)) := by
    apply isOpen_Ioo.eqOn_of_deriv_eq isPreconnected_Ioo
      (fun y hy ↦ (hP y hy).differentiableAt.differentiableWithinAt)
      (fun y _ ↦ (hQ y).differentiableAt.differentiableWithinAt) _ (hp j)
      (by simp [Q])
    intro y hy
    rw [(hP y hy).deriv, (hQ y).deriv]
    have hlin := own_slice_affine hb hown hp j (hp j) y hy
    simp only [Function.update_eq_self] at hlin
    rw [hlin]
    dsimp only [slope]
    ring
  refine ⟨P p - 2 * b j p * p j + slope * p j ^ 2,
    2 * b j p - 2 * slope * p j, slope, ?_⟩
  intro y hy
  change P (Function.update p j y) = _
  exact (heq hy).trans (by dsimp only [Q]; ring)

/-- A closed C² field with zero own second derivatives has an actual fixed diploid realization. -/
theorem compatible_field_realization {lo hi : Fin n → ℝ}
    (hwidth : ∀ i, lo i < hi i)
    (hfreq : ∀ p, InBox lo hi p → ∀ i, 0 < p i ∧ p i < 1)
    {b : Fin n → (Fin n → ℝ) → ℝ}
    (hb : ∀ i, ContDiffOn ℝ 2 (b i) (box lo hi))
    (hclosed : ClosedOnBox lo hi b) (hown : OwnAffineOnBox lo hi b) :
    ∃ f : (Fin n → Fin 3) → ℝ, ∀ p (hp : InBox lo hi p) i,
      b i p = additiveEffect f p (fun j ↦ ⟨(hfreq p hp j).1.le, (hfreq p hp j).2.le⟩) i := by
  let a := fun i ↦ interiorNodes lo hi i 0
  have ha : InBox lo hi a := fun i ↦ interiorNodes_mem lo hi hwidth i 0
  obtain ⟨f, hf⟩ := separately_quadratic_diploid_realization n
    (fun i ↦ Ioo (lo i) (hi i)) (interiorNodes lo hi) (interiorNodes_mem lo hi hwidth)
    (interiorNodes_injective lo hi hwidth) (potential (extension lo hi b) a)
    (fun p hp i ↦ potential_separately_quadratic hwidth hb hclosed hown ha hp i)
  refine ⟨f, ?_⟩
  intro p hp i
  have heq : EqOn (fun x ↦ potential (extension lo hi b) a (Function.update p i x))
      (fun x ↦ phenotypeMean f (Function.update p i x)) (Ioo (lo i) (hi i)) := by
    intro x hx
    exact hf _ (update_mem_box hp i hx)
  have hd := heq.deriv isOpen_Ioo (hp i)
  have hpot := (box_potential_hasDerivAt hwidth hb hclosed hown ha hp i).deriv
  have hmean := derivative_eq_twice_effect f p
    (fun j ↦ ⟨(hfreq p hp j).1.le, (hfreq p hp j).2.le⟩) i (hfreq p hp i)
  have htwice : 2 * b i p = 2 * additiveEffect f p
      (fun j ↦ ⟨(hfreq p hp j).1.le, (hfreq p hp j).2.le⟩) i :=
    hpot.symm.trans (hd.trans hmean)
  linarith

/-- Actual fixed-map realizability forces both differential compatibility conditions on the box. -/
theorem realized_field_conditions {lo hi : Fin n → ℝ}
    (hfreq : ∀ p, InBox lo hi p → ∀ i, 0 < p i ∧ p i < 1)
    {b : Fin n → (Fin n → ℝ) → ℝ} (f : (Fin n → Fin 3) → ℝ)
    (hf : ∀ p (hp : InBox lo hi p) i,
      b i p = additiveEffect f p (fun j ↦ ⟨(hfreq p hp j).1.le, (hfreq p hp j).2.le⟩) i) :
    ClosedOnBox lo hi b ∧ OwnAffineOnBox lo hi b := by
  have he : ∀ p, InBox lo hi p → ∀ i, b i p = effectField f p i := by
    intro p hp i
    exact (hf p hp i).trans (effectField_eq_additiveEffect f p _ i (hfreq p hp i)).symm
  constructor
  · intro p hp i j
    rw [coordinatePartial_eq_of_box_eq (fun q hq ↦ he q hq i) hp j,
      coordinatePartial_eq_of_box_eq (fun q hq ↦ he q hq j) hp i]
    exact effectField_cross_derivatives f p i j
  · intro p hp i
    have hslice : EqOn (fun x ↦ b i (Function.update p i x))
        (fun x ↦ effectField f (Function.update p i x) i) (Ioo (lo i) (hi i)) := by
      intro x hx
      exact he _ (update_mem_box hp i hx) i
    have hd := (hslice.deriv isOpen_Ioo).deriv isOpen_Ioo (hp i)
    exact hd.trans (effectField_own_second_derivative_zero f p i)

/-- Complete existence equivalence on every nonempty open frequency box, under the report's C²
hypothesis. The realizing coefficients are the actual joint additive regression effects. -/
theorem diploid_box_compatibility {lo hi : Fin n → ℝ}
    (hwidth : ∀ i, lo i < hi i)
    (hfreq : ∀ p, InBox lo hi p → ∀ i, 0 < p i ∧ p i < 1)
    (b : Fin n → (Fin n → ℝ) → ℝ)
    (hb : ∀ i, ContDiffOn ℝ 2 (b i) (box lo hi)) :
    (ClosedOnBox lo hi b ∧ OwnAffineOnBox lo hi b) ↔
      ∃ f : (Fin n → Fin 3) → ℝ, ∀ p (hp : InBox lo hi p) i,
        b i p = additiveEffect f p
          (fun j ↦ ⟨(hfreq p hp j).1.le, (hfreq p hp j).2.le⟩) i := by
  constructor
  · rintro ⟨hclosed, hown⟩
    exact compatible_field_realization hwidth hfreq hb hclosed hown
  · rintro ⟨f, hf⟩
    exact realized_field_conditions hfreq f hf

end Descent.Portability.DiploidBoxCompatibilityLaw
