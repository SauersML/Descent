/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.ArchaicPrediction.Phase
import Mathlib.Data.Finset.SymmDiff

assert_below Descent.Decision Descent.Program

/-!
# Response-specific moments and nonuniform phase variance

Theorem 5 and the symmetric-difference covariance formula. A posterior law
may depend on arbitrary observed data; the identities apply separately at
every observation. Risk-scale and latent-score coefficients remain distinct.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.ArchaicPrediction

open scoped BigOperators symmDiff
variable {H J I : Type*} [Fintype H] [Fintype J] [Fintype I] [DecidableEq I]

noncomputable def weightedMean (w : H → ℝ) (f : H → ℝ) : ℝ := ∑ h, w h * f h

lemma weightedMean_add (w : H → ℝ) (f g : H → ℝ) :
    weightedMean w (fun h => f h + g h) = weightedMean w f + weightedMean w g := by
  simp [weightedMean, mul_add, Finset.sum_add_distrib]

lemma weightedMean_const (w : H → ℝ) (hw : ∑ h, w h = 1) (c : ℝ) :
    weightedMean w (fun _ => c) = c := by simp [weightedMean, ← Finset.sum_mul, hw]

lemma weightedMean_sub (w : H → ℝ) (f g : H → ℝ) :
    weightedMean w (fun h => f h - g h) = weightedMean w f - weightedMean w g := by
  simp [weightedMean, mul_sub, Finset.sum_sub_distrib]

lemma weightedMean_sum (w : H → ℝ) (f : J → H → ℝ) :
    weightedMean w (fun h => ∑ j, f j h) = ∑ j, weightedMean w (f j) := by
  simp only [weightedMean, Finset.mul_sum]
  exact Finset.sum_comm

lemma weightedMean_scale (w : H → ℝ) (c : ℝ) (f : H → ℝ) :
    weightedMean w (fun h => c * f h) = c * weightedMean w f := by
  simp [weightedMean, Finset.mul_sum, mul_left_comm]

/-- Response-specific moments suffice for the mean on that response's scale. -/
theorem response_specific_mean (w : H → ℝ) (c : J → ℝ) (φ : J → H → ℝ) :
    weightedMean w (fun h => ∑ j, c j * φ j h) = ∑ j, c j * weightedMean w (φ j) := by
  simp_rw [weightedMean_sum, weightedMean_scale]

theorem response_moment_error (c μ μhat : J → ℝ) :
    |(∑ j, c j * μhat j) - (∑ j, c j * μ j)| ≤ ∑ j, |c j| * |μhat j - μ j| := by
  rw [← Finset.sum_sub_distrib]
  simp_rw [← mul_sub]
  simpa only [abs_mul] using Finset.abs_sum_le_sum_abs (fun j => c j * (μhat j - μ j)) Finset.univ

/-- The exact cost of replacing a response by a single dosage-only constant. -/
theorem best_constant_risk (w : H → ℝ) (hw : ∑ h, w h = 1) (f : H → ℝ) (b : ℝ) :
    weightedMean w (fun h => (f h - b) ^ 2) =
      weightedMean w (fun h => (f h - weightedMean w f) ^ 2) + (weightedMean w f - b) ^ 2 := by
  have hex (c : ℝ) : weightedMean w (fun h => (f h - c) ^ 2) =
      weightedMean w (fun h => f h ^ 2) - 2 * c * weightedMean w f + c ^ 2 := by
    unfold weightedMean
    simp_rw [show ∀ h, w h * (f h - c) ^ 2 =
      w h * f h ^ 2 - 2 * c * (w h * f h) + c ^ 2 * w h by intro; ring]
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, hw]
    ring
  rw [hex, hex]
  ring

theorem variance_as_second_moment (w : H → ℝ) (hw : ∑ h, w h = 1) (f : H → ℝ) :
    weightedMean w (fun h => (f h - weightedMean w f) ^ 2) =
      weightedMean w (fun h => f h ^ 2) - weightedMean w f ^ 2 := by
  have h := best_constant_risk w hw f 0
  simp only [sub_zero] at h
  linarith

lemma weighted_product_expansion (w : H → ℝ) (c : J → ℝ) (φ : J → H → ℝ) :
    weightedMean w (fun h => (∑ j, c j * φ j h) ^ 2) =
      ∑ j, ∑ k, c j * c k * weightedMean w (fun h => φ j h * φ k h) := by
  simp_rw [pow_two, Finset.sum_mul, Finset.mul_sum, weightedMean_sum]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  rw [← weightedMean_scale]
  congr 1
  funext h
  ring

theorem response_covariance (w : H → ℝ) (hw : ∑ h, w h = 1)
    (c : J → ℝ) (φ : J → H → ℝ) :
    weightedMean w (fun h => ((∑ j, c j * φ j h) -
      weightedMean w (fun h => ∑ j, c j * φ j h)) ^ 2) =
      ∑ j, ∑ k, c j * c k * (weightedMean w (fun h => φ j h * φ k h) -
        weightedMean w (φ j) * weightedMean w (φ k)) := by
  rw [variance_as_second_moment w hw, weighted_product_expansion, response_specific_mean]
  simp only [pow_two, Finset.sum_mul, Finset.mul_sum, mul_sub, Finset.sum_sub_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intros; ring

/-- Products of phase characters are indexed by symmetric difference. -/
theorem phaseCharacter_mul (S T : Finset I) (x : I → Bool) :
    phaseCharacter S x * phaseCharacter T x = phaseCharacter (S ∆ T) x := by
  simp_rw [phaseCharacter_univ]
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  by_cases hS : i ∈ S <;> by_cases hT : i ∈ T <;> cases hx : x i <;>
    norm_num [hS, hT, Finset.mem_symmDiff, hx, allele]

theorem phaseCharacter_abs (S : Finset I) (x : I → Bool) : |phaseCharacter S x| = 1 := by
  simp only [phaseCharacter, Finset.abs_prod]
  apply Finset.prod_eq_one
  intro i _
  cases hx : x i <;> norm_num [allele, hx]

theorem phase_moment_abs_le_one (w : H → ℝ) (hw : ∑ h, w h = 1) (hpos : ∀ h, 0 ≤ w h)
    (z : H → I → Bool) (S : Finset I) :
    |weightedMean w (fun h => phaseCharacter S (z h))| ≤ 1 := by
  calc
    _ ≤ ∑ h, |w h * phaseCharacter S (z h)| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ h, w h := by simp only [abs_mul, phaseCharacter_abs, mul_one, abs_of_nonneg (hpos _)]
    _ = 1 := hw

/-- Equation (5.3), for an arbitrary nonuniform phase law. -/
theorem phase_covariance (w : (I → Bool) → ℝ) (hw : ∑ x, w x = 1) (c : Finset I → ℝ) :
    weightedMean w (fun x => (phaseExpansion c x - weightedMean w (phaseExpansion c)) ^ 2) =
      ∑ S, ∑ T, c S * c T * (weightedMean w (phaseCharacter (S ∆ T)) -
        weightedMean w (phaseCharacter S) * weightedMean w (phaseCharacter T)) := by
  simpa only [phaseExpansion, LinearMap.coe_mk, AddHom.coe_mk, phaseCharacter_mul] using
    response_covariance w hw c phaseCharacter

/-- The covariance expression is positive semidefinite for every probability law. -/
theorem phase_covariance_nonneg (w : (I → Bool) → ℝ) (hw : ∑ x, w x = 1)
    (hpos : ∀ x, 0 ≤ w x) (c : Finset I → ℝ) :
    0 ≤ ∑ S, ∑ T, c S * c T * (weightedMean w (phaseCharacter (S ∆ T)) -
      weightedMean w (phaseCharacter S) * weightedMean w (phaseCharacter T)) := by
  rw [← phase_covariance w hw]
  exact Finset.sum_nonneg fun x _ => mul_nonneg (hpos x) (sq_nonneg _)

end Descent.Portability.ArchaicPrediction
