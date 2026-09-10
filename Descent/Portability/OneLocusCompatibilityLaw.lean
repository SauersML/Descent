/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.DiploidEffectLaw
import Descent.Portability.QuadraticRigidityLaw

assert_below Descent.Decision Descent.Program

/-!
The complete one-locus analytic compatibility theorem on an open interval.
A C² average-effect field arises from a fixed diploid genotype map exactly when
its second derivative vanishes. The fixed map is unique up to a constant.
This is the analytic base case, not a claim to have closed the arbitrary-locus
curl-to-potential construction.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.OneLocusCompatibilityLaw

open DiploidEffectLaw QuadraticRigidityLaw FiniteReportLaw Set

noncomputable def hweLaw (p : ℝ) (hp : 0 ≤ p ∧ p ≤ 1) : FiniteReportLaw (Fin 3) where
  mass := hweMass p
  mass_nonneg := hweMass_nonneg p hp
  mass_sum := hweMass_sum p

noncomputable def scalarMean (values : Fin 3 → ℝ) (p : ℝ) : ℝ :=
  ∑ g, hweMass p g * values g

noncomputable def scalarEffect (values : Fin 3 → ℝ) (p : ℝ) : ℝ :=
  values 1 - values 0 + (values 0 - 2 * values 1 + values 2) * p

theorem scalarMean_polynomial (values : Fin 3 → ℝ) (p : ℝ) :
    scalarMean values p = values 0 + 2 * (values 1 - values 0) * p +
      (values 0 - 2 * values 1 + values 2) * p ^ 2 := by
  norm_num [scalarMean, hweMass, Fin.sum_univ_succ]
  ring

/-- The constructed field is the actual HWE covariance/variance regression coefficient. -/
theorem scalarEffect_covariance (values : Fin 3 → ℝ) (p : ℝ) (hp : 0 ≤ p ∧ p ≤ 1) :
    (hweLaw p hp).covariance (fun g ↦ (g : ℝ)) values =
      2 * p * (1 - p) * scalarEffect values p := by
  rw [covariance_eq_rawMoments]
  norm_num [expectation, hweLaw, hweMass, scalarEffect, Fin.sum_univ_succ]
  ring

theorem scalarEffect_regression (values : Fin 3 → ℝ) (p : ℝ) (hp : 0 < p ∧ p < 1) :
    (hweLaw p ⟨hp.1.le, hp.2.le⟩).covariance (fun g ↦ (g : ℝ)) values /
      (2 * p * (1 - p)) = scalarEffect values p := by
  rw [scalarEffect_covariance]
  exact mul_div_cancel_left₀ _
    (ne_of_gt (mul_pos (mul_pos (by norm_num) hp.1) (sub_pos.mpr hp.2)))

theorem scalarEffect_hasDerivAt (values : Fin 3 → ℝ) (p : ℝ) :
    HasDerivAt (scalarEffect values) (values 0 - 2 * values 1 + values 2) p := by
  convert ((hasDerivAt_id p).const_mul (values 0 - 2 * values 1 + values 2)).const_add
    (values 1 - values 0) using 1
  ring

theorem scalarEffect_deriv (values : Fin 3 → ℝ) :
    deriv (scalarEffect values) = fun _ ↦ values 0 - 2 * values 1 + values 2 := by
  funext p
  exact (scalarEffect_hasDerivAt values p).deriv

theorem scalarEffect_second_deriv (values : Fin 3 → ℝ) (p : ℝ) :
    deriv (deriv (scalarEffect values)) p = 0 := by
  rw [scalarEffect_deriv]
  exact deriv_const _ _

/-- A genuine analytic converse, in dimension one, on any nonempty open interval. -/
theorem one_locus_compatibility (effect : ℝ → ℝ) {a b c : ℝ}
    (hc : c ∈ Ioo a b) (heffect : ContDiffOn ℝ 2 effect (Ioo a b)) :
    (∃ values : Fin 3 → ℝ, ∀ p ∈ Ioo a b, effect p = scalarEffect values p) ↔
      ∀ p ∈ Ioo a b, deriv (deriv effect) p = 0 := by
  constructor
  · rintro ⟨values, hv⟩ p hp
    have he : EqOn effect (scalarEffect values) (Ioo a b) := hv
    rw [((he.deriv isOpen_Ioo).deriv isOpen_Ioo) hp, scalarEffect_second_deriv]
  · intro hz
    have hl := affine_of_second_derivative_zero effect hc heffect hz
    let A := effect c - deriv effect c * c
    let B := deriv effect c
    let values : Fin 3 → ℝ := fun g ↦
      if g.val = 0 then 0 else if g.val = 1 then A else B + 2 * A
    refine ⟨values, ?_⟩
    intro p hp
    rw [hl p hp]
    change effect c + deriv effect c * (p - c) = A - 0 + (0 - 2 * A + (B + 2 * A)) * p
    dsimp [A, B]
    ring

/-- Equality on the open interval fixes every genotype value up to a common constant. -/
theorem realizing_values_unique_mod_constant (values other : Fin 3 → ℝ) {a b c : ℝ}
    (hc : c ∈ Ioo a b)
    (he : EqOn (scalarEffect values) (scalarEffect other) (Ioo a b)) :
    ∃ shift : ℝ, ∀ g, values g = other g + shift := by
  have hd := he.deriv isOpen_Ioo hc
  rw [scalarEffect_deriv, scalarEffect_deriv] at hd
  dsimp only at hd
  have hv := he hc
  unfold scalarEffect at hv
  rw [hd] at hv
  refine ⟨values 0 - other 0, ?_⟩
  intro g
  fin_cases g <;> dsimp at * <;> nlinarith

end Descent.Portability.OneLocusCompatibilityLaw
