/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.EndToEndAscertainedWitness
import Descent.Portability.EndToEndPooledCalibration

assert_below Descent.Decision Descent.Program

/-!
# The first rung of the moment ladder is sharp: fixation keeps the pooled law and erases calibration

`PortabilityMomentLadder` shows that the propagated budget-1 moments fix the pooled haplotype law
of every deme, and that budget 2 fixes the calibration slope of expectations.  This module shows
that the first rung cannot do the work of the second.

The event.  `EndToEndAscertainedWitness.founderEventLaw` draws a haplotype `g` of deme `source`
with its frequency and replaces a fraction `ε` of the deme by copies of `g`: the resampling stage of
the corpus microscopic neutral kernel.  At `ε = 0` nothing moves (`resamplingMove_zero`).  At
`ε = 1` the whole deme becomes `g`, so every expectation in `source` is the value at the founder
(`expectation_resamplingMove_one`) and every covariance there vanishes
(`covariance_resamplingMove_one`).

Budget one.  For every `ε ∈ [0, 1]` the expected frequency of every haplotype in every deme after
the event equals its frequency before (`integral_mass_founderEventLaw_self`,
`integral_mass_founderEventLaw`): resampling is a martingale for frequencies.  So the events at
`ε = 0` and `ε = 1` have the same expected frequencies, the propagated budget-1 moments, and every
metric of the pooled law agrees between them.

Budget two.  Take any score that varies in the source deme.  Its calibration slope of expectations
against itself there is `1` without the event (`calibrationSlope_founderEventLaw_zero`) and `0`
after complete fixation (`calibrationSlope_founderEventLaw_one`).  So two process laws with equal
expected frequencies in every deme give different calibration slopes
(`expectedFrequencies_eq_and_calibrationSlope_ne`): no function of the budget-1 moments determines
calibration.

Significance.  Everything a deployer can read off the pooled law is blind to fixation: the deployed
mean squared error, the best fixed recalibration, and every linear metric.  Calibration needs the
second moments, because it lives on the variance within each population, and fixation removes that
variance without moving any expected frequency.

Scope.  The two laws are single resampling stages, not neutral epochs of `historyEventKernel`.
Whether two histories of epochs separate the first two rungs is not settled here, and nor is the
separation of the higher rungs.

## Empirical status

None.  The bodies here are finite sums over the outcomes of one resampling stage and rational
arithmetic, so no measurement can bear on them.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.PortabilityMomentLadderSharpness

open MeasureTheory ProbabilityTheory MvPolynomial PartialHaplotypeDualGenerator
  NeutralFellerGenerator PartialHaplotypeMicroscopicStages ReplicaMetricInstances
  EndToEndPortabilityLaw
  EndToEndCalibrationLaw EndToEndPooledCalibration EndToEndAscertainedWitness

noncomputable section

variable {Deme Locus : Type*} {Allele : Locus → Type*}
variable [Fintype Deme] [DecidableEq Deme] [Fintype Locus] [DecidableEq Locus]
  [∀ ℓ, Fintype (Allele ℓ)] [∀ ℓ, DecidableEq (Allele ℓ)]

/-! ## Resampling at fractions zero and one -/

/-- A resampling stage at fraction zero moves nothing. -/
theorem resamplingMove_zero (source : Deme) (g : FullHaplotype Locus Allele)
    (hε0 : (0 : ℝ) ≤ 0) (hε1 : (0 : ℝ) ≤ 1) (x : FrequencyState Deme Locus Allele) :
    resamplingMove source g 0 hε0 hε1 x = x := by
  apply Subtype.ext
  show x.1 + (0 : ℝ) • resamplingDirection source g x.1 = x.1
  rw [zero_smul, add_zero]

/-- After complete fixation on `g` in deme `source`, every expectation there is the value at `g`. -/
theorem expectation_resamplingMove_one (source : Deme) (g : FullHaplotype Locus Allele)
    (x : FrequencyState Deme Locus Allele) (f : FullHaplotype Locus Allele → ℝ) :
    (stateLaw (resamplingMove source g 1 zero_le_one le_rfl x) source).expectation f = f g := by
  rw [expectation_resamplingMove_self]
  ring

/-- After complete fixation in deme `source`, every covariance there vanishes. -/
theorem covariance_resamplingMove_one (source : Deme) (g : FullHaplotype Locus Allele)
    (x : FrequencyState Deme Locus Allele) (first second : FullHaplotype Locus Allele → ℝ) :
    (stateLaw (resamplingMove source g 1 zero_le_one le_rfl x) source).covariance first second
      = 0 := by
  rw [FiniteReportLaw.covariance_eq_rawMoments]
  simp only [expectation_resamplingMove_one]
  ring

/-! ## Budget one: expected frequencies are unchanged -/

/-- **Resampling is a martingale for the frequencies of its own deme.**  For every fraction, the
expected frequency of a haplotype in deme `source` after the founder event is its frequency
before. -/
theorem integral_mass_founderEventLaw_self (source : Deme) (ε : ℝ) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (x : FrequencyState Deme Locus Allele) (hap : FullHaplotype Locus Allele) :
    ∫ y, (stateLaw y source).mass hap ∂(founderEventLaw source ε hε0 hε1 x)
      = (stateLaw x source).mass hap := by
  rw [integral_founderEventLaw source ε hε0 hε1 x (demePolynomial source (X hap)) _
    (polynomialFunction_demePolynomial_X source hap)]
  simp only [stateLaw_resamplingMove_mass]
  have hsum : ∑ g, x.1 (source, g) = 1 := x.2.2 source
  have hpick : ∑ g, x.1 (source, g) * (if hap = g then (1 : ℝ) else 0) = x.1 (source, hap) := by
    simp [mul_ite, Finset.sum_ite_eq]
  calc ∑ g, x.1 (source, g)
        * ((1 - ε) * (stateLaw x source).mass hap + ε * if hap = g then 1 else 0)
      = (1 - ε) * (stateLaw x source).mass hap * ∑ g, x.1 (source, g)
        + ε * ∑ g, x.1 (source, g) * (if hap = g then (1 : ℝ) else 0) := by
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun g _ ↦ by ring
    _ = (stateLaw x source).mass hap := by
        rw [hsum, hpick]
        show (1 - ε) * x.1 (source, hap) * 1 + ε * x.1 (source, hap) = x.1 (source, hap)
        ring

/-- **A founder event keeps every expected frequency.**  For every fraction, deme and haplotype, the
expected frequency after the founder event in deme `source` is the frequency before. -/
theorem integral_mass_founderEventLaw (source : Deme) (ε : ℝ) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (x : FrequencyState Deme Locus Allele) (deme : Deme) (hap : FullHaplotype Locus Allele) :
    ∫ y, (stateLaw y deme).mass hap ∂(founderEventLaw source ε hε0 hε1 x)
      = (stateLaw x deme).mass hap := by
  by_cases hdeme : deme = source
  · rw [hdeme]
    exact integral_mass_founderEventLaw_self source ε hε0 hε1 x hap
  · rw [integral_founderEventLaw source ε hε0 hε1 x (demePolynomial deme (X hap)) _
      (polynomialFunction_demePolynomial_X deme hap)]
    simp only [stateLaw_resamplingMove_of_ne source _ ε hε0 hε1 x hdeme]
    rw [← Finset.sum_mul, x.2.2 source, one_mul]

/-! ## Budget two: the calibration slope separates -/

/-- **Without the event, a varying score is calibrated against itself.** -/
theorem calibrationSlope_founderEventLaw_zero (source : Deme)
    (x : FrequencyState Deme Locus Allele) (score : FullHaplotype Locus Allele → ℝ)
    (hvariance : (stateLaw x source).variance score ≠ 0) :
    expectedCalibrationSlope (Kernel.const _ (founderEventLaw source 0 le_rfl zero_le_one x)) x
        source score score
      = 1 := by
  rw [expectedCalibrationSlope, Kernel.const_apply]
  simp only [FiniteReportLaw.variance]
  rw [integral_founderEventLaw source 0 le_rfl zero_le_one x
    (demeCovariancePolynomial source score score) _
    (polynomialFunction_demeCovariancePolynomial source score score)]
  simp only [resamplingMove_zero]
  rw [← Finset.sum_mul, x.2.2 source, one_mul]
  exact div_self hvariance

/-- **After complete fixation, the calibration slope of expectations is zero.** -/
theorem calibrationSlope_founderEventLaw_one (source : Deme)
    (x : FrequencyState Deme Locus Allele) (score : FullHaplotype Locus Allele → ℝ) :
    expectedCalibrationSlope (Kernel.const _ (founderEventLaw source 1 zero_le_one le_rfl x)) x
        source score score
      = 0 := by
  rw [expectedCalibrationSlope, Kernel.const_apply]
  simp only [FiniteReportLaw.variance]
  rw [integral_founderEventLaw source 1 zero_le_one le_rfl x
    (demeCovariancePolynomial source score score) _
    (polynomialFunction_demeCovariancePolynomial source score score)]
  simp only [covariance_resamplingMove_one, mul_zero, Finset.sum_const_zero, zero_div]

/-- **The budget-1 moments do not determine calibration.**  From any state where a score varies in
deme `source`, the founder events at fractions zero and one have equal expected frequencies of every
haplotype in every deme, and different calibration slopes of expectations of the score against
itself in `source`.

Assumes: the score has nonzero variance in the source deme. -/
theorem expectedFrequencies_eq_and_calibrationSlope_ne (source : Deme)
    (x₀ : FrequencyState Deme Locus Allele) (score : FullHaplotype Locus Allele → ℝ)
    (hvariance : (stateLaw x₀ source).variance score ≠ 0) :
    (∀ (deme : Deme) (hap : FullHaplotype Locus Allele),
      ∫ y, (stateLaw y deme).mass hap ∂(founderEventLaw source 0 le_rfl zero_le_one x₀)
        = ∫ y, (stateLaw y deme).mass hap ∂(founderEventLaw source 1 zero_le_one le_rfl x₀))
    ∧ expectedCalibrationSlope (Kernel.const _ (founderEventLaw source 0 le_rfl zero_le_one x₀))
        x₀ source score score
      ≠ expectedCalibrationSlope (Kernel.const _ (founderEventLaw source 1 zero_le_one le_rfl x₀))
        x₀ source score score := by
  refine ⟨fun deme hap ↦ ?_, ?_⟩
  · rw [integral_mass_founderEventLaw, integral_mass_founderEventLaw]
  · rw [calibrationSlope_founderEventLaw_zero source x₀ score hvariance,
      calibrationSlope_founderEventLaw_one]
    exact one_ne_zero

end

end Descent.Portability.PortabilityMomentLadderSharpness
