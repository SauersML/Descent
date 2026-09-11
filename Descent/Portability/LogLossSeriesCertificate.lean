/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.BellmanReportBounds
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.ENNReal.BigOperators

assert_below Descent.Decision Descent.Program

/-!
# Certified enclosures for the logarithmic metric, and its infinite branch

The logarithmic score is the one metric in the catalogue that is unbounded, so the bounded
ratio machinery does not reach it. NOTE 2 section 6.4 handles it by a series instead: for a
forecast probability in the half-open unit interval the negative logarithm is the sum of the
powers of the forecast deficit divided by their order, every partial sum is a lower bound,
and the discarded tail is controlled by comparison with a geometric series.

`neg_log_hasSum` is that series. `partial_sum_le_neg_log` and `neg_log_tail_bound` are the
two halves of NOTE 2 equation (30): the partial sums approach the negative logarithm from
below and the gap is at most the deficit raised to one more than the truncation order, over
that order plus one times the forecast probability. `expectation_log_loss_enclosure` carries
both to a finite forecast law, which is the rational enclosure the note asks for: the bounds
are finite sums of powers and quotients of the forecast probabilities and the outcome masses.

The infinite branch is not a limit of the finite one and has to be stated separately.
`expectedLogLoss` values the expected logarithmic loss in the extended nonnegative reals, with
an outcome the forecast rules out contributing an infinite term. `expectedLogLoss_eq_top`
shows that one outcome of positive probability assigned forecast probability zero makes the
whole expectation infinite, and `expectedLogLoss_eq_ofReal` shows that when no outcome is
ruled out the extended value is exactly the real expectation of the pointwise loss. The two
statements together say the extended-valued definition refines the real one rather than
replacing it.

Scope: the forecast is a function from a finite outcome type to the reals with values in the
unit interval, and no coherence between the forecast and the outcome law is assumed, so these
statements cover miscalibrated forecasts. The repaired logarithmic loss of NOTE 2 section 9.1,
which replaces the raw score by a population-level quantity, is not formalized here.

## Empirical status

None. The bodies here are analysis: a convergent power series for the logarithm, its
truncation error, and the extended-real value of a finite sum, so no measurement can bear
on them.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.LogLossSeriesCertificate

/-- The negative logarithm of a forecast probability in the half-open unit interval is the sum
of the powers of its deficit divided by their order. -/
theorem neg_log_hasSum (rate : ℝ) (hpos : 0 < rate) (hle : rate ≤ 1) :
    HasSum (fun index : ℕ ↦ (1 - rate) ^ (index + 1) / ((index : ℝ) + 1))
      (-Real.log rate) := by
  have habs : |1 - rate| < 1 := by
    rw [abs_lt]
    constructor <;> linarith
  have hseries := Real.hasSum_pow_div_log_of_abs_lt_one habs
  have hcomplement : (1 : ℝ) - (1 - rate) = rate := by ring
  rwa [hcomplement] at hseries

/-- The terms of the logarithmic series are nonnegative on the half-open unit interval. -/
theorem log_series_term_nonneg (rate : ℝ) (hpos : 0 < rate) (hle : rate ≤ 1) (index : ℕ) :
    0 ≤ (1 - rate) ^ (index + 1) / ((index : ℝ) + 1) := by
  have hdeficit : (0 : ℝ) ≤ 1 - rate := by linarith
  have horder : (0 : ℝ) < (index : ℝ) + 1 := by positivity
  exact div_nonneg (pow_nonneg hdeficit _) horder.le

/-- **NOTE 2 equation (30), lower half.** Every partial sum of the logarithmic series is a
lower bound for the negative logarithm. -/
theorem partial_sum_le_neg_log (rate : ℝ) (hpos : 0 < rate) (hle : rate ≤ 1) (terms : ℕ) :
    ∑ index ∈ Finset.range terms, (1 - rate) ^ (index + 1) / ((index : ℝ) + 1) ≤
      -Real.log rate := by
  have hseries := neg_log_hasSum rate hpos hle
  have hbelow := hseries.summable.sum_le_tsum (Finset.range terms)
    fun index _ ↦ log_series_term_nonneg rate hpos hle index
  rwa [hseries.tsum_eq] at hbelow

/-- **NOTE 2 equation (30), upper half.** The gap between the negative logarithm and its
truncated series is at most the forecast deficit raised to one more than the truncation
order, divided by that order plus one times the forecast probability. The proof compares the
discarded tail term by term with a geometric series whose common ratio is the deficit. -/
theorem neg_log_tail_bound (rate : ℝ) (hpos : 0 < rate) (hle : rate ≤ 1) (terms : ℕ) :
    -Real.log rate -
        ∑ index ∈ Finset.range terms, (1 - rate) ^ (index + 1) / ((index : ℝ) + 1) ≤
      (1 - rate) ^ (terms + 1) / (((terms : ℝ) + 1) * rate) := by
  have hdeficit : (0 : ℝ) ≤ 1 - rate := by linarith
  have hcontract : (1 : ℝ) - rate < 1 := by linarith
  have horder : (0 : ℝ) < (terms : ℝ) + 1 := by positivity
  have hseries := neg_log_hasSum rate hpos hle
  have hsplit := hseries.summable.sum_add_tsum_nat_add terms
  rw [hseries.tsum_eq] at hsplit
  have hmajorant : Summable (fun index : ℕ ↦
      (1 - rate) ^ index * ((1 - rate) ^ (terms + 1) / ((terms : ℝ) + 1))) :=
    (summable_geometric_of_lt_one hdeficit hcontract).mul_right _
  have hcompare : ∀ index : ℕ,
      (1 - rate) ^ (index + terms + 1) / ((↑(index + terms) : ℝ) + 1) ≤
        (1 - rate) ^ index * ((1 - rate) ^ (terms + 1) / ((terms : ℝ) + 1)) := by
    intro index
    have hmono : ((terms : ℝ) + 1) ≤ (↑(index + terms) : ℝ) + 1 := by
      push_cast
      linarith [Nat.cast_nonneg (α := ℝ) index]
    have hshifted : (0 : ℝ) < (↑(index + terms) : ℝ) + 1 := by positivity
    have hbase : (0 : ℝ) ≤ (1 - rate) ^ (terms + 1) := pow_nonneg hdeficit _
    have hlead : (0 : ℝ) ≤ (1 - rate) ^ index := pow_nonneg hdeficit _
    have hinner : (1 - rate) ^ (terms + 1) / ((↑(index + terms) : ℝ) + 1) ≤
        (1 - rate) ^ (terms + 1) / ((terms : ℝ) + 1) := by
      rw [div_le_div_iff₀ hshifted horder]
      exact mul_le_mul_of_nonneg_left hmono hbase
    have hfactor : (1 - rate) ^ (index + terms + 1) =
        (1 - rate) ^ index * (1 - rate) ^ (terms + 1) := by
      rw [← pow_add, Nat.add_assoc]
    rw [hfactor, mul_div_assoc]
    exact mul_le_mul_of_nonneg_left hinner hlead
  have htailNonneg : ∀ index : ℕ,
      0 ≤ (1 - rate) ^ (index + terms + 1) / ((↑(index + terms) : ℝ) + 1) := by
    intro index
    have hcast : (0 : ℝ) < (↑(index + terms) : ℝ) + 1 := by positivity
    exact div_nonneg (pow_nonneg hdeficit _) hcast.le
  have htailSummable : Summable (fun index : ℕ ↦
      (1 - rate) ^ (index + terms + 1) / ((↑(index + terms) : ℝ) + 1)) :=
    hmajorant.of_nonneg_of_le htailNonneg hcompare
  have htail := htailSummable.tsum_le_tsum hcompare hmajorant
  have hgeometric : ∑' index : ℕ,
      (1 - rate) ^ index * ((1 - rate) ^ (terms + 1) / ((terms : ℝ) + 1)) =
        rate⁻¹ * ((1 - rate) ^ (terms + 1) / ((terms : ℝ) + 1)) := by
    rw [(summable_geometric_of_lt_one hdeficit hcontract).tsum_mul_right,
      tsum_geometric_of_lt_one hdeficit hcontract]
    have hcomplement : (1 : ℝ) - (1 - rate) = rate := by ring
    rw [hcomplement]
  have hshape : rate⁻¹ * ((1 - rate) ^ (terms + 1) / ((terms : ℝ) + 1)) =
      (1 - rate) ^ (terms + 1) / (((terms : ℝ) + 1) * rate) := by
    simp only [div_eq_mul_inv, mul_inv]
    ring
  linarith

section ForecastLaw

open scoped ENNReal

variable {Outcome : Type*} [Fintype Outcome]

/-- The expected logarithmic loss of a finite forecast, valued in the extended nonnegative
reals so that an outcome the forecast rules out contributes an infinite term. -/
noncomputable def expectedLogLoss (law : FiniteReportLaw Outcome) (forecast : Outcome → ℝ) :
    ℝ≥0∞ :=
  ∑ outcome, ENNReal.ofReal (law.mass outcome) *
    (if 0 < forecast outcome then ENNReal.ofReal (-Real.log (forecast outcome)) else ⊤)

/-- **NOTE 2 section 6.4, infinite branch.** One outcome of positive probability that the
forecast rules out makes the expected logarithmic loss infinite. -/
theorem expectedLogLoss_eq_top (law : FiniteReportLaw Outcome) (forecast : Outcome → ℝ)
    (ruled : Outcome) (hmass : 0 < law.mass ruled) (hforecast : ¬ 0 < forecast ruled) :
    expectedLogLoss law forecast = ⊤ := by
  have hnonzero : ENNReal.ofReal (law.mass ruled) ≠ 0 :=
    (ENNReal.ofReal_pos.mpr hmass).ne'
  refine top_le_iff.mp ?_
  unfold expectedLogLoss
  calc (⊤ : ℝ≥0∞) = ENNReal.ofReal (law.mass ruled) *
        (if 0 < forecast ruled then ENNReal.ofReal (-Real.log (forecast ruled))
          else ⊤) := by rw [if_neg hforecast, ENNReal.mul_top hnonzero]
    _ ≤ ∑ outcome, ENNReal.ofReal (law.mass outcome) *
          (if 0 < forecast outcome then ENNReal.ofReal (-Real.log (forecast outcome))
            else ⊤) :=
        Finset.single_le_sum (f := fun outcome ↦ ENNReal.ofReal (law.mass outcome) *
          (if 0 < forecast outcome then ENNReal.ofReal (-Real.log (forecast outcome))
            else ⊤)) (fun outcome _ ↦ zero_le _) (Finset.mem_univ ruled)

/-- **NOTE 2 section 6.4, finite branch.** When no outcome is ruled out, the extended-valued
expected logarithmic loss is exactly the real expectation of the pointwise loss. -/
theorem expectedLogLoss_eq_ofReal (law : FiniteReportLaw Outcome) (forecast : Outcome → ℝ)
    (hpos : ∀ outcome, 0 < forecast outcome) (hle : ∀ outcome, forecast outcome ≤ 1) :
    expectedLogLoss law forecast =
      ENNReal.ofReal (law.expectation (fun outcome ↦ -Real.log (forecast outcome))) := by
  have hloss : ∀ outcome : Outcome, 0 ≤ -Real.log (forecast outcome) := fun outcome ↦
    neg_nonneg.mpr (Real.log_nonpos (hpos outcome).le (hle outcome))
  have hterm : ∀ outcome : Outcome,
      ENNReal.ofReal (law.mass outcome) *
          (if 0 < forecast outcome then ENNReal.ofReal (-Real.log (forecast outcome))
            else ⊤) =
        ENNReal.ofReal (law.mass outcome * -Real.log (forecast outcome)) := by
    intro outcome
    rw [if_pos (hpos outcome), ← ENNReal.ofReal_mul (law.mass_nonneg outcome)]
  unfold expectedLogLoss FiniteReportLaw.expectation
  rw [Finset.sum_congr rfl fun outcome _ ↦ hterm outcome,
    ← ENNReal.ofReal_sum_of_nonneg fun outcome _ ↦
      mul_nonneg (law.mass_nonneg outcome) (hloss outcome)]

/-- Expectation is additive, so a difference of expectations is the expectation of the
difference. -/
theorem expectation_sub_eq (law : FiniteReportLaw Outcome) (first second : Outcome → ℝ) :
    law.expectation first - law.expectation second =
      law.expectation (fun outcome ↦ first outcome - second outcome) := by
  simp only [FiniteReportLaw.expectation, mul_sub, Finset.sum_sub_distrib]

/-- **NOTE 2 equation (30) at the population level.** For a finite forecast law with no ruled
out outcome, the expected logarithmic loss is bracketed by the expectation of the truncated
series and that expectation increased by the expectation of the pointwise tail bound. Both
brackets are finite sums of powers and quotients of the forecast probabilities, so a rational
forecast law gives rational enclosures of any desired width. -/
theorem expectation_log_loss_enclosure (law : FiniteReportLaw Outcome)
    (forecast : Outcome → ℝ) (hpos : ∀ outcome, 0 < forecast outcome)
    (hle : ∀ outcome, forecast outcome ≤ 1) (terms : ℕ) :
    law.expectation (fun outcome ↦ ∑ index ∈ Finset.range terms,
          (1 - forecast outcome) ^ (index + 1) / ((index : ℝ) + 1)) ≤
        law.expectation (fun outcome ↦ -Real.log (forecast outcome)) ∧
      law.expectation (fun outcome ↦ -Real.log (forecast outcome)) -
          law.expectation (fun outcome ↦ ∑ index ∈ Finset.range terms,
            (1 - forecast outcome) ^ (index + 1) / ((index : ℝ) + 1)) ≤
        law.expectation (fun outcome ↦ (1 - forecast outcome) ^ (terms + 1) /
          (((terms : ℝ) + 1) * forecast outcome)) := by
  constructor
  · exact BellmanReportBounds.expectation_mono law _ _ fun outcome ↦
      partial_sum_le_neg_log (forecast outcome) (hpos outcome) (hle outcome) terms
  · rw [expectation_sub_eq]
    exact BellmanReportBounds.expectation_mono law _ _ fun outcome ↦
      neg_log_tail_bound (forecast outcome) (hpos outcome) (hle outcome) terms

end ForecastLaw

end Descent.Portability.LogLossSeriesCertificate
