/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.HWEHomozygoteConditioning
import Descent.Portability.RademacherJointLimit

assert_below Descent.Decision Descent.Program

/-!
Exact log-coordinate representation of the original standardized HWE interaction
on the zero-heterozygote event. The exponential amplitude is derived from the
allele-frequency normalization, rather than supplied as a replacement model.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.HWEHomozygoteAmplitude

open scoped BigOperators
open Foundations HWEInteractionLaw HWEHomozygoteConditioning HWELogCoordinates
open BalancedHWEWeakLimit RademacherArrayWeakLimit RademacherParityLaw

/-- The positive standardized homozygote magnitude in square-root coordinates. -/
theorem magnitude_identity (u v : ℝ) (hu : 0 < u) (hv : 0 < v) :
    2 * u / Real.sqrt (2 * u * v) = Real.sqrt 2 * Real.sqrt (u / v) := by
  have hd : 0 < 2 * u * v := by positivity
  apply (sq_eq_sq₀ (by positivity) (by positivity)).mp
  simp only [div_pow, mul_pow, Real.sq_sqrt hd.le, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2),
    Real.sq_sqrt (div_nonneg hu.le hv.le)]
  field_simp

/-- Exponentiating the exact HWE log coordinate gives the square root of the odds. -/
theorem exp_coordinate (h : HardyWeinbergModel)
    (h0 : 0 < h.altFreq) (h1 : h.altFreq < 1) :
    Real.exp (coordinate (h.altFreq - 1 / 2)) =
      Real.sqrt (h.altFreq / (1 - h.altFreq)) := by
  rw [coordinate_frequency h h0 h1, one_div_mul_eq_div, Real.exp_half,
    Real.exp_log (div_pos h0 (sub_pos.mpr h1))]

/-- The opposite exponent gives the reciprocal homozygote magnitude. -/
theorem exp_neg_coordinate (h : HardyWeinbergModel)
    (h0 : 0 < h.altFreq) (h1 : h.altFreq < 1) :
    Real.exp (-coordinate (h.altFreq - 1 / 2)) =
      Real.sqrt ((1 - h.altFreq) / h.altFreq) := by
  rw [Real.exp_neg, exp_coordinate h h0 h1, ← Real.sqrt_inv, inv_div]

/-- Exact signed exponential formula for either original standardized homozygote. -/
theorem standardized_homozygote (h : HardyWeinbergModel)
    (h0 : 0 < h.altFreq) (h1 : h.altFreq < 1) (b : Bool) :
    h.standardizedGenotype (homozygote b) = Real.sqrt 2 * signValue b *
      Real.exp (-coordinate (h.altFreq - 1 / 2) * signValue b) := by
  have hq : 0 < 1 - h.altFreq := sub_pos.mpr h1
  cases b
  · simp only [homozygote, signValue, Bool.false_eq_true, if_false, mul_neg_one, neg_neg]
    rw [exp_coordinate h h0 h1]
    simp only [HardyWeinbergModel.standardizedGenotype,
      HardyWeinbergModel.centeredAltAlleleCount,
      HardyWeinbergModel.expectedAltAlleleCount_eq, HardyWeinbergModel.genotypeVariance_eq,
      HardyWeinbergModel.refFreq,
      altAlleleCount, Core.Genotype.dosage]
    convert congrArg Neg.neg (magnitude_identity h.altFreq (1 - h.altFreq) h0 hq) using 1 <;>
      ring
  · simp only [homozygote, signValue, if_true, mul_one]
    rw [exp_neg_coordinate h h0 h1]
    simp only [HardyWeinbergModel.standardizedGenotype,
      HardyWeinbergModel.centeredAltAlleleCount,
      HardyWeinbergModel.expectedAltAlleleCount_eq, HardyWeinbergModel.genotypeVariance_eq,
      HardyWeinbergModel.refFreq,
      altAlleleCount, Core.Genotype.dosage]
    rw [show 2 * h.altFreq * (1 - h.altFreq) =
      2 * (1 - h.altFreq) * h.altFreq by ring]
    convert magnitude_identity (1 - h.altFreq) h.altFreq hq h0 using 1 <;> ring

/-- Exact block amplitude with the actual product sign and weighted log profile. -/
theorem interaction_homoVector {ι : Type*} [Fintype ι] [DecidableEq ι]
    (h : ι → HardyWeinbergModel)
    (h0 : ∀ i, 0 < (h i).altFreq) (h1 : ∀ i, (h i).altFreq < 1) (b : ι → Bool) :
    interaction h (homoVector b) = Real.sqrt 2 ^ Fintype.card ι * parity b *
      Real.exp (-weightedSum (fun i ↦ coordinate ((h i).altFreq - 1 / 2)) b) := by
  simp only [interaction, homoVector, standardized_homozygote _ (h0 _) (h1 _),
    Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, parity, weightedSum]
  rw [← Real.exp_sum, ← Finset.sum_neg_distrib]
  congr 2
  apply Finset.sum_congr rfl
  intro i _
  ring

end Descent.Portability.HWEHomozygoteAmplitude
