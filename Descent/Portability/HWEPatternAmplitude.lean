/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.HWEPatternConditioning
import Descent.Portability.HWEHomozygoteAmplitude

assert_below Descent.Decision Descent.Program

/-!
Exact original interaction amplitudes on every heterozygosity pattern. Each
heterozygous locus contributes its standardized dosage, while the remaining
homozygous signs contribute the already derived signed exponential log profile.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.HWEPatternAmplitude

open scoped BigOperators
open Foundations HWEInteractionLaw HWEPatternConditioning HWEHomozygoteConditioning
open HWEHomozygoteAmplitude HWELogCoordinates RademacherArrayWeakLimit RademacherParityLaw

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The actual interaction separates into heterozygous factors and remaining homozygous factors. -/
theorem interaction_pattern_split (h : ι → HardyWeinbergModel) (s : Finset ι)
    (b : {i // i ∉ s} → Bool) :
    interaction h (patternVector s b) =
      (∏ i : {i // i ∈ s}, (h i.val).standardizedGenotype .het) *
        interaction (fun i : {i // i ∉ s} ↦ h i.val) (homoVector b) := by
  unfold interaction
  rw [← Fintype.prod_subtype_mul_prod_subtype (fun i ↦ i ∈ s)]
  congr 1
  · apply Finset.prod_congr
    · ext i
      simp
    · intro i _
      simp [patternVector, i.property]
  · apply Finset.prod_congr rfl
    intro i _
    simp only [patternVector, dif_neg i.property, homoVector]

/-- Exact signed exponential representation on a nonzero heterozygosity layer. -/
theorem interaction_pattern_amplitude (h : ι → HardyWeinbergModel)
    (h0 : ∀ i, 0 < (h i).altFreq) (h1 : ∀ i, (h i).altFreq < 1)
    (s : Finset ι) (b : {i // i ∉ s} → Bool) :
    interaction h (patternVector s b) =
      (∏ i : {i // i ∈ s}, (h i.val).standardizedGenotype .het) *
        Real.sqrt 2 ^ Fintype.card {i // i ∉ s} * parity b *
          Real.exp (-weightedSum (fun i : {i // i ∉ s} ↦
            coordinate ((h i.val).altFreq - 1 / 2)) b) := by
  rw [interaction_pattern_split, interaction_homoVector (fun i : {i // i ∉ s} ↦ h i.val)
    (fun i ↦ h0 i.val) (fun i ↦ h1 i.val) b]
  ring

/-- Exact standardized heterozygote factor in the original allele-frequency coordinates. -/
theorem standardized_heterozygote (h : HardyWeinbergModel)
    (h0 : 0 < h.altFreq) (h1 : h.altFreq < 1) :
    h.standardizedGenotype .het = Real.sqrt 2 *
      (-(h.altFreq - 1 / 2) / Real.sqrt (h.altFreq * (1 - h.altFreq))) := by
  have hp : 0 < h.altFreq * (1 - h.altFreq) := mul_pos h0 (sub_pos.mpr h1)
  have hs : Real.sqrt (h.altFreq * (1 - h.altFreq)) ≠ 0 := Real.sqrt_ne_zero'.mpr hp
  have h2 : Real.sqrt (2 : ℝ) ≠ 0 := by positivity
  simp only [HardyWeinbergModel.standardizedGenotype,
    HardyWeinbergModel.centeredAltAlleleCount, HardyWeinbergModel.expectedAltAlleleCount_eq,
    HardyWeinbergModel.genotypeVariance_eq, HardyWeinbergModel.refFreq,
    altAlleleCount, Core.Genotype.dosage]
  rw [mul_assoc, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
  field_simp
  nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]

end Descent.Portability.HWEPatternAmplitude
