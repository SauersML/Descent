/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.ReplicaDomainCertificate
import Mathlib.Analysis.SpecialFunctions.Pow.Real

assert_below Descent.Decision Descent.Program

/-!
# How fast the unresolved mass decays when the denominator can be small

The replica certificate needs a tolerance dominating the definedness mass a truncation leaves
unresolved. When the denominator is bounded below on its defined event that tolerance is
geometric, which is NOTE 2 equation (19) and is already proved in the replica-domain module.
NOTE 2 section 5.3 covers the harder case, where the denominator may come arbitrarily close to
zero and only the mass near zero is controlled.

`smallDenominatorMass` is the probability that the denominator is positive but no larger than
a threshold, the quantity NOTE 2 bounds by a power of the threshold.
`unresolvedMass_le_threshold` splits the unresolved mass at any threshold into that near-zero
mass plus the geometric decay above the threshold, exactly and with no rate assumption.
`unresolvedMass_le_rate` inserts a power-law bound on the near-zero mass and
`pow_le_exp_neg_mul` converts the geometric factor to an exponential in the truncation order,
so the certificate's tolerance is explicit in the truncation order and the threshold and can
be optimized over the threshold by the caller.

`unresolvedNumerator_le_of_floor` is the remainder bound of NOTE 2 equation (29) in the regime
that equation's proof also needs: a numerator bounded by a ceiling rather than by the
denominator, and a denominator bounded below on its defined event. It bounds the discarded
numerator by the ceiling over the floor times the geometric decay.

Elsewhere. NOTE 2 equation (20) states the sharp constant obtained by writing the unresolved
mass as a layer-cake integral against the density of the truncation order and then evaluating
a beta integral, giving a ratio of gamma values. What is proved here is the elementary threshold
split, which has the same content for choosing a truncation order but a larger constant. The
layer-cake identity, the beta evaluation and the sharp constant of (20), together with equation
(28), the finiteness of the expected inverse denominator under a power law with exponent above
one, and (29) are `Descent.Portability.SmallDenominatorLayerCake`.

## Empirical status

None. The bodies here are algebra and elementary inequalities on finite sums: near-zero mass,
geometric decay and their exchange, so no measurement can bear on them.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.SmallDenominatorRates

open SublawReportCertificate PositiveRatioExpansion ReplicaDomainCertificate

variable {Report : Type*} [Fintype Report]

/-- The mass sitting near the singularity of a ratio metric: the probability that the
denominator is positive but no larger than a threshold. -/
noncomputable def smallDenominatorMass (law : FiniteReportLaw Report) (den : Report → ℝ)
    (threshold : ℝ) : ℝ :=
  law.expectation (fun report ↦
    if 0 < den report ∧ den report ≤ threshold then 1 else 0)

/-- The near-zero mass is a probability, so it is nonnegative. -/
theorem smallDenominatorMass_nonneg (law : FiniteReportLaw Report) (den : Report → ℝ)
    (threshold : ℝ) : 0 ≤ smallDenominatorMass law den threshold := by
  unfold smallDenominatorMass
  refine expectation_nonneg law _ fun report ↦ ?_
  split_ifs <;> norm_num

/-- The near-zero mass is a probability, so it never exceeds one. This is also the power-law
bound of NOTE 2 section 5.3 at unit scale and zero exponent, so the rate hypothesis of
`unresolvedMass_le_rate` is never vacuous. -/
theorem smallDenominatorMass_le_one (law : FiniteReportLaw Report) (den : Report → ℝ)
    (threshold : ℝ) : smallDenominatorMass law den threshold ≤ 1 := by
  unfold smallDenominatorMass
  refine expectation_le_const law _ _ fun report ↦ ?_
  split_ifs <;> norm_num

/-- **NOTE 2 section 5.3, threshold split.** At any threshold the unresolved definedness mass
is at most the mass sitting below the threshold plus the geometric decay of the truncation
above it. The split is exact and assumes no rate at all. -/
theorem unresolvedMass_le_threshold (law : FiniteReportLaw Report) (den : Report → ℝ)
    (hnonneg : ∀ report, 0 ≤ den report) (hone : ∀ report, den report ≤ 1)
    (threshold : ℝ) (hthresholdNonneg : 0 ≤ threshold) (hthresholdOne : threshold ≤ 1)
    (terms : ℕ) :
    unresolvedMass law den terms ≤
      smallDenominatorMass law den threshold + (1 - threshold) ^ terms := by
  have hdeficit : (0 : ℝ) ≤ 1 - threshold := by linarith
  have hdecay : (0 : ℝ) ≤ (1 - threshold) ^ terms := pow_nonneg hdeficit terms
  have hpointwise : ∀ report : Report,
      definedIndicator (fun other ↦ 0 < den other) report * (1 - den report) ^ terms ≤
        (if 0 < den report ∧ den report ≤ threshold then 1 else 0) +
          (1 - threshold) ^ terms := by
    intro report
    by_cases hpos : 0 < den report
    · have hindicator : definedIndicator (fun other ↦ 0 < den other) report = 1 := by
        simp [definedIndicator, hpos]
      rw [hindicator, one_mul]
      by_cases hsmall : den report ≤ threshold
      · rw [if_pos ⟨hpos, hsmall⟩]
        have hunit : (1 - den report) ^ terms ≤ 1 :=
          pow_le_one₀ (by linarith [hone report]) (by linarith [hnonneg report])
        linarith
      · have hbig : threshold < den report := not_le.mp hsmall
        rw [if_neg fun hcontra ↦ hsmall hcontra.2, zero_add]
        exact pow_le_pow_left₀ (by linarith [hone report]) (by linarith) terms
    · have hindicator : definedIndicator (fun other ↦ 0 < den other) report = 0 := by
        simp [definedIndicator, hpos]
      have hselector : (0 : ℝ) ≤
          if 0 < den report ∧ den report ≤ threshold then 1 else 0 := by
        split_ifs <;> norm_num
      rw [hindicator, zero_mul]
      linarith
  have hexpectation : law.expectation (fun report ↦
      (if 0 < den report ∧ den report ≤ threshold then 1 else 0) +
        (1 - threshold) ^ terms) =
      smallDenominatorMass law den threshold + (1 - threshold) ^ terms := by
    simp only [smallDenominatorMass, FiniteReportLaw.expectation, mul_add,
      Finset.sum_add_distrib]
    congr 1
    rw [← Finset.sum_mul, law.mass_sum, one_mul]
  unfold unresolvedMass
  calc law.expectation (fun report ↦
        definedIndicator (fun other ↦ 0 < den other) report * (1 - den report) ^ terms)
      ≤ law.expectation (fun report ↦
          (if 0 < den report ∧ den report ≤ threshold then 1 else 0) +
            (1 - threshold) ^ terms) :=
        BellmanReportBounds.expectation_mono law _ _ hpointwise
    _ = smallDenominatorMass law den threshold + (1 - threshold) ^ terms := hexpectation

/-- The geometric decay above a threshold is an exponential decay in the truncation order. -/
theorem pow_le_exp_neg_mul (threshold : ℝ) (hnonneg : 0 ≤ threshold) (hone : threshold ≤ 1)
    (terms : ℕ) :
    (1 - threshold) ^ terms ≤ Real.exp (-((terms : ℝ) * threshold)) := by
  have hstep : 1 - threshold ≤ Real.exp (-threshold) := by
    have hexp := Real.add_one_le_exp (-threshold)
    linarith
  calc (1 - threshold) ^ terms ≤ Real.exp (-threshold) ^ terms :=
        pow_le_pow_left₀ (by linarith) hstep terms
    _ = Real.exp (-((terms : ℝ) * threshold)) := by
        rw [← Real.exp_nat_mul]
        congr 1
        ring

/-- **NOTE 2 section 5.3, derived rate.** Under a power-law bound on the near-zero mass at a
chosen threshold, the tolerance of the replica certificate is that power plus an exponential
decay in the truncation order. Optimizing the threshold against the truncation order is the
caller's choice and needs no further hypothesis. -/
theorem unresolvedMass_le_rate (law : FiniteReportLaw Report) (den : Report → ℝ)
    (hnonneg : ∀ report, 0 ≤ den report) (hone : ∀ report, den report ≤ 1)
    (scale exponent threshold : ℝ) (hthresholdPos : 0 < threshold)
    (hthresholdOne : threshold ≤ 1)
    (hrate : smallDenominatorMass law den threshold ≤ scale * threshold ^ exponent)
    (terms : ℕ) :
    unresolvedMass law den terms ≤
      scale * threshold ^ exponent + Real.exp (-((terms : ℝ) * threshold)) := by
  have hsplit := unresolvedMass_le_threshold law den hnonneg hone threshold
    hthresholdPos.le hthresholdOne terms
  have hexp := pow_le_exp_neg_mul threshold hthresholdPos.le hthresholdOne terms
  linarith

/-- **NOTE 2 equation (29), bounded-below regime.** When the numerator is bounded by a ceiling
rather than by the denominator, and the denominator is bounded below wherever it is defined,
the numerator a truncation discards is at most the ceiling over the floor times the geometric
decay. This is the remainder the replica certificate needs when the metric itself is not a
bounded ratio. -/
theorem unresolvedNumerator_le_of_floor (law : FiniteReportLaw Report) (num den : Report → ℝ)
    (hnum : ∀ report, 0 ≤ num report) (ceilingValue : ℝ) (hceilingNonneg : 0 ≤ ceilingValue)
    (hceiling : ∀ report, num report ≤ ceilingValue) (denFloor : ℝ) (hfloorPos : 0 < denFloor)
    (hfloorOne : denFloor ≤ 1) (hfloor : ∀ report, 0 < den report → denFloor ≤ den report)
    (hone : ∀ report, den report ≤ 1) (terms : ℕ) :
    unresolvedNumerator law num den terms ≤
      ceilingValue / denFloor * (1 - denFloor) ^ terms := by
  have hfloorDeficit : (0 : ℝ) ≤ 1 - denFloor := by linarith
  have hquotient : (0 : ℝ) ≤ ceilingValue / denFloor := div_nonneg hceilingNonneg hfloorPos.le
  unfold unresolvedNumerator
  refine expectation_le_const law _ _ fun report ↦ ?_
  by_cases hpos : 0 < den report
  · have hvalue : ratioOnDefined num den report = num report / den report := by
      simp [ratioOnDefined, hpos]
    have hmetric : ratioOnDefined num den report ≤ ceilingValue / denFloor := by
      rw [hvalue, div_le_div_iff₀ hpos hfloorPos]
      have hleft := mul_le_mul_of_nonneg_right (hceiling report) hfloorPos.le
      have hright := mul_le_mul_of_nonneg_left (hfloor report hpos) hceilingNonneg
      linarith
    have hdecay : (1 - den report) ^ terms ≤ (1 - denFloor) ^ terms :=
      pow_le_pow_left₀ (by linarith [hone report]) (by linarith [hfloor report hpos]) terms
    have hdecayNonneg : (0 : ℝ) ≤ (1 - den report) ^ terms :=
      pow_nonneg (by linarith [hone report]) terms
    calc ratioOnDefined num den report * (1 - den report) ^ terms
        ≤ ceilingValue / denFloor * (1 - den report) ^ terms :=
          mul_le_mul_of_nonneg_right hmetric hdecayNonneg
      _ ≤ ceilingValue / denFloor * (1 - denFloor) ^ terms :=
          mul_le_mul_of_nonneg_left hdecay hquotient
  · have hzero : ratioOnDefined num den report = 0 := by
      simp [ratioOnDefined, hpos]
    rw [hzero, zero_mul]
    exact mul_nonneg hquotient (pow_nonneg hfloorDeficit terms)

end Descent.Portability.SmallDenominatorRates
