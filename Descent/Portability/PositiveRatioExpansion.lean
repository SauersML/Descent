/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.UniversalMetricIdentification
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence

assert_below Descent.Decision Descent.Program

/-!
# The positive ratio expansion of a bounded nonlinear metric

A metric that is a ratio of two population functionals is not a moment of the population
vector, so it is not directly a finite-replica readout. NOTE 2 equation (15) removes the
division: when the numerator and the denominator satisfy `0 ≤ num ≤ den ≤ 1` pointwise, the
expectation of the ratio on the event where the denominator is positive equals the sum of
the series whose terms are the expectations of `num * (1 - den) ^ power`. Every term is a
polynomial in the two functionals, so every term is a finite-replica readout, and the metric
is the limit of finitely many of them.

`tsum_expansion_terms` is the pointwise identity and carries the whole content: where the
denominator is positive the geometric series converges to the ratio, and where it vanishes
the numerator vanishes with it so every term is zero and the ratio is read as zero. That
convention is the definition `ratioOnDefined`.

Two population versions are proved from it. `expectation_ratioOnDefined_eq_tsum` is the
finite report law version, which is the one the report laws of this corpus use: all sums are
finite and the exchange of the series with the report sum is summability of each coordinate.
`integral_ratioOnDefined_eq_tsum` is the measure version for a probability measure on an
arbitrary measurable space, proved by dominated convergence against the constant bound one,
using that every partial sum of the expansion is squeezed between zero and one.

Scope: the bounds `0 ≤ num ≤ den ≤ 1` are assumed everywhere, not almost everywhere, and the
numerator and denominator are assumed measurable rather than merely almost everywhere
measurable. The rate at which the partial sums approach the metric is not addressed here;
the certified remainder that turns this expansion into a finite computation is the business
of the replica-domain certificates.

## Empirical status

None. The bodies here are algebra and a convergence argument: the statements relate a series
of integrals to an integral of a ratio under pointwise inequalities, so no measurement can
bear on them.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.PositiveRatioExpansion

/-- A ratio read as zero where the denominator vanishes. This is the metric that is defined
only on the event where the denominator is positive, extended by zero elsewhere. -/
noncomputable def ratioOnDefined {Point : Type*} (num den : Point → ℝ) : Point → ℝ :=
  fun point ↦ if 0 < den point then num point / den point else 0

/-- A ratio of a nonnegative numerator is nonnegative wherever it is read. -/
theorem ratioOnDefined_nonneg {Point : Type*} (num den : Point → ℝ)
    (hnum : ∀ point, 0 ≤ num point) (point : Point) :
    0 ≤ ratioOnDefined num den point := by
  unfold ratioOnDefined
  split_ifs with hpos
  · exact div_nonneg (hnum point) hpos.le
  · exact le_refl 0

/-- A numerator dominated by its denominator gives a ratio at most one. -/
theorem ratioOnDefined_le_one {Point : Type*} (num den : Point → ℝ)
    (hle : ∀ point, num point ≤ den point) (point : Point) :
    ratioOnDefined num den point ≤ 1 := by
  unfold ratioOnDefined
  split_ifs with hpos
  · exact (div_le_one hpos).mpr (hle point)
  · exact zero_le_one

/-- The terms of the positive ratio expansion are summable, including at a vanishing
denominator, where the numerator vanishes and every term is zero. -/
theorem summable_expansion_terms (num den : ℝ) (hnum : 0 ≤ num) (hle : num ≤ den)
    (hden : den ≤ 1) : Summable (fun power : ℕ ↦ num * (1 - den) ^ power) := by
  rcases eq_or_lt_of_le (le_trans hnum hle) with hzero | hpos
  · have hnumzero : num = 0 := le_antisymm (by linarith) hnum
    simp only [hnumzero, zero_mul]
    exact summable_zero
  · have hdeficit : (0 : ℝ) ≤ 1 - den := by linarith
    have hcontract : (1 : ℝ) - den < 1 := by linarith
    exact (summable_geometric_of_lt_one hdeficit hcontract).mul_left num

/-- **NOTE 2 equation (15), pointwise.** The geometric series of the numerator against powers
of the denominator deficit sums to the ratio where the denominator is positive, and to zero
where the denominator vanishes, because the numerator vanishes there as well. -/
theorem tsum_expansion_terms (num den : ℝ) (hnum : 0 ≤ num) (hle : num ≤ den)
    (hden : den ≤ 1) :
    ∑' power : ℕ, num * (1 - den) ^ power = if 0 < den then num / den else 0 := by
  rcases eq_or_lt_of_le (le_trans hnum hle) with hzero | hpos
  · have hnumzero : num = 0 := le_antisymm (by linarith) hnum
    rw [if_neg (by linarith : ¬ (0 : ℝ) < den)]
    simp [hnumzero]
  · have hdeficit : (0 : ℝ) ≤ 1 - den := by linarith
    have hcontract : (1 : ℝ) - den < 1 := by linarith
    have hgeometric : Summable (fun power : ℕ ↦ (1 - den) ^ power) :=
      summable_geometric_of_lt_one hdeficit hcontract
    have hcomplement : (1 : ℝ) - (1 - den) = den := by ring
    rw [if_pos hpos, hgeometric.tsum_mul_left,
      tsum_geometric_of_lt_one hdeficit hcontract, hcomplement, div_eq_mul_inv]

section FiniteReport

variable {Report : Type*} [Fintype Report]

/-- **NOTE 2 equation (15) for a finite report law.** The expectation of a bounded ratio
metric, read as zero where the denominator vanishes, is the sum of the series of expectations
of `num * (1 - den) ^ power`. Each term is a polynomial functional of the report law, so the
metric is exhibited as a limit of finite-replica readouts with no division in any term. -/
theorem expectation_ratioOnDefined_eq_tsum (law : FiniteReportLaw Report)
    (num den : Report → ℝ) (hnum : ∀ report, 0 ≤ num report)
    (hle : ∀ report, num report ≤ den report) (hden : ∀ report, den report ≤ 1) :
    law.expectation (ratioOnDefined num den) =
      ∑' power : ℕ,
        law.expectation (fun report ↦ num report * (1 - den report) ^ power) := by
  have hcoordinate : ∀ report : Report, Summable (fun power : ℕ ↦
      law.mass report * (num report * (1 - den report) ^ power)) := fun report ↦
    (summable_expansion_terms (num report) (den report) (hnum report) (hle report)
      (hden report)).mul_left (law.mass report)
  simp only [FiniteReportLaw.expectation]
  rw [Summable.tsum_finsetSum fun report (_ : report ∈ Finset.univ) ↦ hcoordinate report]
  refine Finset.sum_congr rfl fun report _ ↦ ?_
  rw [(summable_expansion_terms (num report) (den report) (hnum report) (hle report)
      (hden report)).tsum_mul_left,
    tsum_expansion_terms (num report) (den report) (hnum report) (hle report) (hden report)]
  rfl

end FiniteReport

section ProbabilityMeasure

open MeasureTheory Filter Topology

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **NOTE 2 equation (15) for a probability measure.** The same expansion holds for an
arbitrary probability measure on a measurable space. The proof is dominated convergence
against the constant bound one: every partial sum of the expansion lies between zero and the
ratio itself, which is at most one because the numerator is dominated by the denominator. -/
theorem integral_ratioOnDefined_eq_tsum (μ : Measure Ω) [IsProbabilityMeasure μ]
    (num den : Ω → ℝ) (hnumMeasurable : Measurable num) (hdenMeasurable : Measurable den)
    (hnum : ∀ point, 0 ≤ num point) (hle : ∀ point, num point ≤ den point)
    (hden : ∀ point, den point ≤ 1) :
    ∫ point, ratioOnDefined num den point ∂μ =
      ∑' power : ℕ, ∫ point, num point * (1 - den point) ^ power ∂μ := by
  have hdenNonneg : ∀ point, 0 ≤ den point := fun point ↦ le_trans (hnum point) (hle point)
  have hdeficit : ∀ point, (0 : ℝ) ≤ 1 - den point := fun point ↦ by linarith [hden point]
  have htermMeasurable : ∀ power : ℕ,
      Measurable (fun point ↦ num point * (1 - den point) ^ power) := fun power ↦
    hnumMeasurable.mul ((measurable_const.sub hdenMeasurable).pow_const power)
  have htermNonneg : ∀ (power : ℕ) (point : Ω),
      0 ≤ num point * (1 - den point) ^ power := fun power point ↦
    mul_nonneg (hnum point) (pow_nonneg (hdeficit point) power)
  have htermLeOne : ∀ (power : ℕ) (point : Ω),
      num point * (1 - den point) ^ power ≤ 1 := by
    intro power point
    have hnumLeOne : num point ≤ 1 := le_trans (hle point) (hden point)
    have hpowLeOne : (1 - den point) ^ power ≤ 1 :=
      pow_le_one₀ (hdeficit point) (by linarith [hdenNonneg point])
    nlinarith [hnum point, pow_nonneg (hdeficit point) power]
  have htermIntegrable : ∀ power : ℕ,
      Integrable (fun point ↦ num point * (1 - den point) ^ power) μ := by
    intro power
    refine (integrable_const (1 : ℝ)).mono'
      (htermMeasurable power).aestronglyMeasurable (ae_of_all _ fun point ↦ ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (htermNonneg power point)]
    exact htermLeOne power point
  have hpartialNonneg : ∀ (power : ℕ) (point : Ω),
      0 ≤ ∑ index ∈ Finset.range power, num point * (1 - den point) ^ index :=
    fun power point ↦ Finset.sum_nonneg fun index _ ↦ htermNonneg index point
  have hpartialLeOne : ∀ (power : ℕ) (point : Ω),
      ∑ index ∈ Finset.range power, num point * (1 - den point) ^ index ≤ 1 := by
    intro power point
    have hsummable := summable_expansion_terms (num point) (den point) (hnum point)
      (hle point) (hden point)
    have hbelow := hsummable.sum_le_tsum (Finset.range power)
      (fun index _ ↦ htermNonneg index point)
    rw [tsum_expansion_terms (num point) (den point) (hnum point) (hle point)
      (hden point)] at hbelow
    have hratio := ratioOnDefined_le_one num den hle point
    unfold ratioOnDefined at hratio
    linarith
  have hpartialTendsto : ∀ point : Ω, Tendsto
      (fun power ↦ ∑ index ∈ Finset.range power, num point * (1 - den point) ^ index) atTop
      (𝓝 (ratioOnDefined num den point)) := by
    intro point
    have hsummable := summable_expansion_terms (num point) (den point) (hnum point)
      (hle point) (hden point)
    have hlimit := hsummable.hasSum.tendsto_sum_nat
    rw [tsum_expansion_terms (num point) (den point) (hnum point) (hle point)
      (hden point)] at hlimit
    unfold ratioOnDefined
    exact hlimit
  have hpartialIntegral : ∀ power : ℕ,
      ∫ point, (∑ index ∈ Finset.range power, num point * (1 - den point) ^ index) ∂μ =
        ∑ index ∈ Finset.range power, ∫ point, num point * (1 - den point) ^ index ∂μ :=
    fun power ↦ integral_finset_sum _ fun index _ ↦ htermIntegrable index
  have hdominated : Tendsto
      (fun power ↦ ∫ point,
        (∑ index ∈ Finset.range power, num point * (1 - den point) ^ index) ∂μ) atTop
      (𝓝 (∫ point, ratioOnDefined num den point ∂μ)) := by
    refine tendsto_integral_of_dominated_convergence (fun _ ↦ (1 : ℝ)) (fun power ↦ ?_)
      (integrable_const 1) (fun power ↦ ae_of_all _ fun point ↦ ?_)
      (ae_of_all _ hpartialTendsto)
    · exact (integrable_finset_sum _ fun index _ ↦ htermIntegrable index).aestronglyMeasurable
    · rw [Real.norm_eq_abs, abs_of_nonneg (hpartialNonneg power point)]
      exact hpartialLeOne power point
  have hseriesSummable : Summable (fun power : ℕ ↦
      ∫ point, num point * (1 - den point) ^ power ∂μ) := by
    refine summable_of_sum_range_le (c := 1)
      (fun power ↦ integral_nonneg fun point ↦ htermNonneg power point) fun power ↦ ?_
    rw [← hpartialIntegral power]
    have hbound : ∫ point,
        (∑ index ∈ Finset.range power, num point * (1 - den point) ^ index) ∂μ ≤
          ∫ _point : Ω, (1 : ℝ) ∂μ :=
      integral_mono (integrable_finset_sum _ fun index _ ↦ htermIntegrable index)
        (integrable_const 1) fun point ↦ hpartialLeOne power point
    simpa using hbound
  have hdominated' : Tendsto
      (fun power ↦ ∑ index ∈ Finset.range power,
        ∫ point, num point * (1 - den point) ^ index ∂μ) atTop
      (𝓝 (∫ point, ratioOnDefined num den point ∂μ)) := by
    simpa only [hpartialIntegral] using hdominated
  exact tendsto_nhds_unique hdominated' hseriesSummable.hasSum.tendsto_sum_nat

end ProbabilityMeasure

end Descent.Portability.PositiveRatioExpansion
