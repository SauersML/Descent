/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.HWEHomozygoteLimit

assert_below Descent.Decision Descent.Program

/-!
Exact absolute first moments of the balanced-normalized locus under its actual
square-biased HWE law. Separating homozygous and heterozygous contributions gives
a cubic small-frequency bound for the heterozygote contribution.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.HWEAbsoluteLocusLaw

open scoped BigOperators
open Foundations HWEInteractionLaw HWEHeterozygosityLaw

noncomputable def locusAmplitude (h : HardyWeinbergModel) (g : DiploidGenotype) : ℝ :=
  h.standardizedGenotype g / Real.sqrt 2

noncomputable def homoMass (h : HardyWeinbergModel) : ℝ :=
  2 * Real.sqrt (h.altFreq * (1 - h.altFreq))

noncomputable def heteroMass (h : HardyWeinbergModel) : ℝ :=
  4 * (h.altFreq - 1 / 2) ^ 2 * |h.altFreq - 1 / 2| /
    Real.sqrt (h.altFreq * (1 - h.altFreq))

/-- Exact normalized genotype amplitude with its original dosage. -/
theorem locusAmplitude_eq (h : HardyWeinbergModel) (g : DiploidGenotype) :
    locusAmplitude h g = (altAlleleCount g - 2 * h.altFreq) /
      (2 * Real.sqrt (h.altFreq * (1 - h.altFreq))) := by
  have hs : Real.sqrt (2 * h.altFreq * (1 - h.altFreq)) =
      Real.sqrt 2 * Real.sqrt (h.altFreq * (1 - h.altFreq)) := by
    rw [mul_assoc, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
  simp only [locusAmplitude, HardyWeinbergModel.standardizedGenotype,
    HardyWeinbergModel.centeredAltAlleleCount, HardyWeinbergModel.expectedAltAlleleCount_eq,
    HardyWeinbergModel.genotypeVariance_eq, HardyWeinbergModel.refFreq, hs, div_div]
  congr 1
  linear_combination Real.sqrt (h.altFreq * (1 - h.altFreq)) *
    (Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2))

/-- The entire homozygous absolute contribution is twice sqrt(p(1-p)). -/
theorem homo_absolute (h : HardyWeinbergModel)
    (h0 : 0 < h.altFreq) (h1 : h.altFreq < 1) :
    (squareBiasedLocus h h0 h1).expectation
      (fun g ↦ if g = .het then 0 else |locusAmplitude h g|) = homoMass h := by
  have hpq : 0 < h.altFreq * (1 - h.altFreq) := mul_pos h0 (sub_pos.mpr h1)
  have hs := Real.sqrt_pos.mpr hpq
  have hsq := Real.sq_sqrt hpq.le
  rw [FiniteReportLaw.expectation, Core.Genotype.sum_univ]
  simp only [squareBiasedLocus_mass, locusAmplitude_eq h, homoMass,
    altAlleleCount, Core.Genotype.dosage]
  norm_num only [show Core.Genotype.homRef ≠ Core.Genotype.het by decide,
    show Core.Genotype.homAlt ≠ Core.Genotype.het by decide,
    if_false, if_true, mul_zero, zero_add, add_zero,
    Nat.cast_ofNat, Nat.cast_zero, zero_sub, abs_div, abs_neg,
    abs_of_pos (mul_pos (by norm_num : (0 : ℝ) < 2) hs),
    abs_of_pos (mul_pos (by norm_num : (0 : ℝ) < 2) h0),
    abs_of_pos (show 0 < 2 - 2 * h.altFreq by linarith)]
  field_simp
  nlinarith

/-- The heterozygous absolute contribution is cubic in the frequency displacement. -/
theorem hetero_absolute (h : HardyWeinbergModel)
    (h0 : 0 < h.altFreq) (h1 : h.altFreq < 1) :
    (squareBiasedLocus h h0 h1).expectation
      (fun g ↦ if g = .het then |locusAmplitude h g| else 0) = heteroMass h := by
  have hs : 0 < Real.sqrt (h.altFreq * (1 - h.altFreq)) :=
    Real.sqrt_pos.mpr (mul_pos h0 (sub_pos.mpr h1))
  rw [FiniteReportLaw.expectation, Core.Genotype.sum_univ]
  simp only [squareBiasedLocus_mass, locusAmplitude_eq h, heteroMass,
    altAlleleCount, Core.Genotype.dosage]
  norm_num only [show Core.Genotype.homRef ≠ Core.Genotype.het by decide,
    show Core.Genotype.homAlt ≠ Core.Genotype.het by decide,
    if_false, if_true, mul_zero, zero_add, add_zero,
    Nat.cast_one]
  rw [show 1 - 2 * h.altFreq = -2 * (h.altFreq - 1 / 2) by ring,
    abs_div, abs_mul, abs_of_pos (mul_pos (by norm_num : (0 : ℝ) < 2) hs)]
  norm_num
  ring

/-- Exact sum of the two absolute contributions. -/
theorem total_absolute (h : HardyWeinbergModel)
    (h0 : 0 < h.altFreq) (h1 : h.altFreq < 1) :
    (squareBiasedLocus h h0 h1).expectation (fun g ↦ |locusAmplitude h g|) =
      homoMass h + heteroMass h := by
  rw [← homo_absolute h h0 h1, ← hetero_absolute h h0 h1]
  simp only [FiniteReportLaw.expectation, ← Finset.sum_add_distrib, ← mul_add]
  apply Finset.sum_congr rfl
  intro g _
  by_cases hg : g = .het <;> simp [hg]

/-- Both absolute contributions are nonnegative. -/
theorem masses_nonneg (h : HardyWeinbergModel) : 0 ≤ homoMass h ∧ 0 ≤ heteroMass h := by
  unfold homoMass heteroMass
  constructor <;> positivity

/-- The homozygous contribution never exceeds one. -/
theorem homoMass_le_one (h : HardyWeinbergModel) : homoMass h ≤ 1 := by
  have hpq : h.altFreq * (1 - h.altFreq) ≤ (1 / 2 : ℝ) ^ 2 := by
    nlinarith [sq_nonneg (h.altFreq - 1 / 2)]
  have hs := Real.sqrt_le_sqrt hpq
  norm_num at hs
  unfold homoMass
  linarith

end Descent.Portability.HWEAbsoluteLocusLaw
