/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.HWEHierarchyParameters
import Descent.Portability.GaussianCompoundMoments

assert_below Descent.Decision Descent.Program

/-!
Actual finite moments of the hierarchy's limit law. Its Gaussian and Poisson
variance components add to the inclusive Poisson count tail, while its fourth
cumulant is strictly positive. These are integrals under the constructed law,
not a claim that finite-array moments converge through the weak limit.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.HWEHierarchyMoments

open scoped BigOperators NNReal MeasureTheory
open MeasureTheory ProbabilityTheory HWEHierarchyLimitLaw HWEHierarchyParameters
open HWEHierarchySeries HWEFixedLayerInputs HWECriticalLimitLaw HWEJumpMoments
open GaussianCompoundMoments

/-- Probability that a Poisson count is at least the specified integer layer. -/
noncomputable def inclusiveMass (rate : ℝ≥0) (r : ℕ) : ℝ :=
  ∑' n : ℕ, if r ≤ n then poissonPMFReal rate n else 0

/-- The inclusive count tail splits into its boundary mass and strict upper tail. -/
theorem inclusiveMass_split (rate : ℝ≥0) (r : ℕ) :
    inclusiveMass rate r = tailMass rate (r : ℝ) + poissonPMFReal rate r := by
  have hs : Summable (fun n : ℕ ↦ if r ≤ n then poissonPMFReal rate n else 0) := by
    apply (poissonPMFRealSum rate).summable.of_norm_bounded
    intro n
    split_ifs
    · rw [Real.norm_eq_abs, abs_of_nonneg poissonPMFReal_nonneg]
    · simpa using (poissonPMFReal_nonneg (r := rate) (n := n))
  rw [inclusiveMass, hs.tsum_eq_add_tsum_ite r]
  simp only [le_refl, if_true]
  have hh : (∑' n : ℕ, if n = r then 0 else if r ≤ n then poissonPMFReal rate n else 0) =
      tailMass rate (r : ℝ) := by
    apply tsum_congr
    intro n
    have he : ((r : ℝ) < (n : ℝ)) ↔ r < n := Nat.cast_lt
    by_cases hn : n = r
    · subst n
      simp
    · by_cases hrn : r ≤ n
      · have hlt : r < n := lt_of_le_of_ne hrn (Ne.symm hn)
        simp [hn, hrn, he, hlt]
      · have hlt : ¬r < n := fun h ↦ hrn h.le
        simp [hn, hrn, he, hlt]
  rw [hh, add_comm]

/-- For a negative threshold the noninteger candidate is exactly the standard Gaussian. -/
theorem gaussianLaw_of_negative (κ α : ℝ) (hα : α < 0) :
    (gaussianLaw κ α : Measure ℝ) = gaussianReal 0 1 := by
  have ht : tailVariance κ α = 1 := NNReal.eq (tail_of_negative _ α hα)
  change gaussianReal 0 (tailVariance κ α) = _
  rw [ht]

/-- The actual integer-limit law has finite absolute moments through order four. -/
theorem integer_power_integrable (κ C : ℝ) (r n : ℕ) (hn : n ≤ 4) :
    Integrable (fun x : ℝ ↦ x ^ n) (integerLaw κ C r : Measure ℝ) :=
  gaussian_compound_power_integrable (tailVariance κ (r : ℝ)) (layerIntensity κ C r)
    (jumpLaw (energy κ) (layerAmplitude κ C r))
    (jump_power_integrable _ _) (jump_mean _ _) n hn

/-- The independent Gaussian and Poisson components yield a centered limit. -/
theorem integer_mean (κ C : ℝ) (r : ℕ) :
    (∫ x : ℝ, x ∂(integerLaw κ C r : Measure ℝ)) = 0 :=
  gaussian_compound_mean (tailVariance κ (r : ℝ)) (layerIntensity κ C r)
    (jumpLaw (energy κ) (layerAmplitude κ C r))
    (jump_power_integrable _ _) (jump_mean _ _)

/-- Exact second moment equals the inclusive Poisson tail at the retained layer. -/
theorem integer_second (κ C : ℝ) (hκ : κ ≠ 0) (hC : 0 < C) (r : ℕ) :
    (∫ x : ℝ, x ^ 2 ∂(integerLaw κ C r : Measure ℝ)) =
      inclusiveMass (4 * energy κ) r := by
  change (∫ x : ℝ, x ^ 2 ∂(gaussianReal 0 (tailVariance κ (r : ℝ)) ∗
    CompoundPoissonMarkLaw.compoundMeasure (layerIntensity κ C r)
      (jumpLaw (energy κ) (layerAmplitude κ C r)))) = _
  rw [gaussian_compound_second _ _ _ (jump_power_integrable _ _) (jump_mean _ _),
    layer_jump_variance κ C hκ hC r, inclusiveMass_split]
  rfl

/-- Actual variance of the identity under the complete limiting probability law. -/
theorem integer_variance (κ C : ℝ) (hκ : κ ≠ 0) (hC : 0 < C) (r : ℕ) :
    variance (fun x : ℝ ↦ x) (integerLaw κ C r : Measure ℝ) =
      inclusiveMass (4 * energy κ) r := by
  rw [variance_eq_integral (by fun_prop), integer_mean]
  simpa only [sub_zero] using integer_second κ C hκ hC r

/-- The full fourth cumulant is intensity times the fourth moment of an actual jump. -/
theorem integer_fourth_cumulant (κ C : ℝ) (r : ℕ) :
    (∫ x : ℝ, x ^ 4 ∂(integerLaw κ C r : Measure ℝ)) -
      3 * (∫ x : ℝ, x ^ 2 ∂(integerLaw κ C r : Measure ℝ)) ^ 2 =
        (layerIntensity κ C r : ℝ) * layerAmplitude κ C r ^ 4 := by
  have hh := gaussian_compound_fourth_cumulant (tailVariance κ (r : ℝ))
    (layerIntensity κ C r) (jumpLaw (energy κ) (layerAmplitude κ C r))
    (jump_power_integrable _ _) (jump_mean _ _)
  rw [jump_fourth] at hh
  exact hh

/-- Every integer-threshold limit has a strictly positive fourth cumulant. -/
theorem integer_fourth_cumulant_pos (κ C : ℝ) (hκ : κ ≠ 0) (hC : 0 < C) (r : ℕ) :
    0 < (∫ x : ℝ, x ^ 4 ∂(integerLaw κ C r : Measure ℝ)) -
      3 * (∫ x : ℝ, x ^ 2 ∂(integerLaw κ C r : Measure ℝ)) ^ 2 := by
  rw [integer_fourth_cumulant]
  have hp : 0 < layerAmplitude κ C r ^ 4 := by
    simpa only [← pow_mul] using
      pow_pos (sq_pos_of_ne_zero (layerAmplitude_ne_zero κ C hκ hC r)) 2
  exact mul_pos (layerIntensity_pos κ C hκ hC r) hp

/-- The integer-threshold law cannot equal any Gaussian distribution. -/
theorem integer_ne_gaussian (κ C : ℝ) (hκ : κ ≠ 0) (hC : 0 < C) (r : ℕ)
    (m : ℝ) (v : ℝ≥0) : (integerLaw κ C r : Measure ℝ) ≠ gaussianReal m v := by
  intro he
  have hm := integer_mean κ C r
  rw [he, integral_id_gaussianReal] at hm
  rw [hm] at he
  have hh := integer_fourth_cumulant_pos κ C hκ hC r
  rw [he, GaussianPolynomialMoments.fourth_moment,
    GaussianPolynomialMoments.second_moment] at hh
  nlinarith

end Descent.Portability.HWEHierarchyMoments
