/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.PortabilityMomentLadderSharpness
import Descent.Portability.PortabilityMomentLadderDecision

assert_below Descent.Decision Descent.Program

/-!
# Expected recall is off the first rung: fixation keeps expected frequencies and moves recall

`PortabilityMomentLadderDecision` proves that agreement up to degree one fixes the decision report
of every rule (`decisionReport_eq_of_polynomialsAgreeAt_one`), and that agreement at every degree
fixes the expected per-population recall and precision.  This module separates the first rung from
the ratios: two process laws with equal expected frequencies of every haplotype in every deme give
different expected recall and different expected precision.

The events.  `EndToEndAscertainedWitness.founderEventLaw` draws a founder `g` of deme `source`
with its frequency and replaces a fraction `ε` of the deme by copies of `g`.  A strongly measurable
observable integrates against it to the frequency-weighted sum of its values after the event
(`integral_founderEventLaw_of_stronglyMeasurable`).  Every frequency coordinate is a martingale
(`sum_resamplingMove_coordinate`), so the events at fractions `0` and `1` have equal expected
frequencies (`PortabilityMomentLadderSharpness.integral_mass_founderEventLaw`).

Recall and precision.  Write `TP` for the true-positive cell of the confusion report law in
`source` and `c` for any other cell.  Without the event, the expected positive quotient
`E[TP / (TP + c)]` is `TP / (TP + c)` of the state
(`expectedPositiveQuotient_founderEventLaw_zero`).  After complete fixation every cell is the
indicator of the founder's cell (`pushforwardMass_resamplingMove_one`), so the quotient is one on a
called case and zero otherwise (`positiveQuotient_resamplingMove_one`), and its expectation is `TP`
of the state (`expectedPositiveQuotient_founderEventLaw_one`).  The two differ whenever `0 < TP`
and `TP + c < 1` (`expectedPositiveQuotient_founderEventLaw_ne`), because `TP / (TP + c) = TP`
forces `TP + c = 1`.  The false-negative cell gives recall and the false-positive cell precision:
two process laws with equal expected frequencies and different expected recall
(`expectedFrequencies_eq_and_expectedRecall_ne`) or different expected precision
(`expectedFrequencies_eq_and_expectedPrecision_ne`).

Significance.  The cells of the expected confusion table are expectations of functions linear in
the frequencies, so they see only the expected frequencies.  The expected per-population recall and
precision see more: an expected ratio is not the ratio of expected cells, and it depends on how the
cells vary between realizations of the process.

Scope.  The two laws are single resampling stages, not neutral epochs of `historyEventKernel`.  The
separation proved here is the fallback form: equal expected frequencies of every haplotype in every
deme.  That the two laws agree on every frequency polynomial of total degree at most one
(`PortabilityMomentLadder.PolynomialsAgreeAt` at degree one), and so give one decision report, is
not proved here.  Whether some finite degree fixes the expected recall or precision is not settled
here.

## Empirical status

None.  The bodies here are finite sums over the outcomes of one resampling stage and rational
arithmetic, so no measurement can bear on them.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.PortabilityMomentLadderDecisionSharpness

open MeasureTheory ProbabilityTheory MvPolynomial PartialHaplotypeDualGenerator
  NeutralFellerGenerator PartialHaplotypeMicroscopicStages ReplicaMetricInstances
  EndToEndPortabilityLaw EndToEndBrierLaw EndToEndDecisionLaw EndToEndPooledCalibration
  EndToEndAscertainedWitness PortabilityMomentLadderSharpness

noncomputable section

variable {Deme Locus : Type*} {Allele : Locus → Type*}
variable [Fintype Deme] [DecidableEq Deme] [Fintype Locus] [DecidableEq Locus]
  [∀ ℓ, Fintype (Allele ℓ)] [∀ ℓ, DecidableEq (Allele ℓ)]

/-! ## Integrals against a founder event -/

/-- **A measurable observable integrates against a founder event to its weighted values.**  The
integral is the frequency-weighted sum over founders of the observable after the event.  This
extends `EndToEndAscertainedWitness.integral_founderEventLaw` from polynomial observables to every
strongly measurable observable, such as a quotient of two report cells.

Assumes: the observable is strongly measurable. -/
theorem integral_founderEventLaw_of_stronglyMeasurable (source : Deme) (ε : ℝ) (hε0 : 0 ≤ ε)
    (hε1 : ε ≤ 1) (x : FrequencyState Deme Locus Allele)
    {observable : FrequencyState Deme Locus Allele → ℝ}
    (hobservable : StronglyMeasurable observable) :
    ∫ y, observable y ∂(founderEventLaw source ε hε0 hε1 x)
      = ∑ g, x.1 (source, g) * observable (resamplingMove source g ε hε0 hε1 x) := by
  have hpoint : ∀ g : FullHaplotype Locus Allele,
      Integrable observable
          (ENNReal.ofReal (x.1 (source, g)) • Measure.dirac (resamplingMove source g ε hε0 hε1 x))
        ∧ ∫ y, observable y
          ∂(ENNReal.ofReal (x.1 (source, g)) • Measure.dirac (resamplingMove source g ε hε0 hε1 x))
          = x.1 (source, g) * observable (resamplingMove source g ε hε0 hε1 x) := fun g ↦ by
    refine ⟨(integrable_dirac' hobservable (by simp)).smul_measure ENNReal.ofReal_ne_top, ?_⟩
    rw [integral_smul_measure, integral_dirac' _ _ hobservable, smul_eq_mul,
      ENNReal.toReal_ofReal (x.2.1 (source, g))]
  rw [founderEventLaw, integral_finset_sum_measure fun g _ ↦ (hpoint g).1]
  exact Finset.sum_congr rfl fun g _ ↦ (hpoint g).2

/-- **Every frequency coordinate is a martingale under a founder event.**  Averaged over the
founder, the frequency of every haplotype in every deme after the event is its frequency before. -/
theorem sum_resamplingMove_coordinate (source : Deme) (ε : ℝ) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (x : FrequencyState Deme Locus Allele) (v : FrequencyVariable Deme Locus Allele) :
    ∑ g, x.1 (source, g) * (resamplingMove source g ε hε0 hε1 x).1 v = x.1 v := by
  have hintegral := integral_mass_founderEventLaw source ε hε0 hε1 x v.1 v.2
  rw [integral_founderEventLaw source ε hε0 hε1 x (demePolynomial v.1 (X v.2)) _
    (polynomialFunction_demePolynomial_X v.1 v.2)] at hintegral
  exact hintegral

/-! ## Positive quotients at fractions zero and one -/

/-- The positive quotient `TP / (TP + c)` of a cell `c` of the confusion report law of a deme is a
strongly measurable observable of the state. -/
theorem stronglyMeasurable_positiveQuotient (deme : Deme) {Score : Type*} [Fintype Score]
    (report : FullHaplotype Locus Allele → Score × Bool) (called : Score → Bool)
    (other : Bool × Bool) :
    StronglyMeasurable fun y : FrequencyState Deme Locus Allele ↦
      ((stateLaw y deme).pushforward (confusionReport report called)).mass (true, true)
        / (((stateLaw y deme).pushforward (confusionReport report called)).mass (true, true)
          + ((stateLaw y deme).pushforward (confusionReport report called)).mass other) := by
  have hcell : ∀ cell : Bool × Bool, Measurable fun y : FrequencyState Deme Locus Allele ↦
      ((stateLaw y deme).pushforward (confusionReport report called)).mass cell :=
    fun cell ↦ (continuous_pushforwardMass deme (confusionReport report called) cell).measurable
  exact ((hcell (true, true)).div ((hcell (true, true)).add (hcell other))).stronglyMeasurable

/-- **After complete fixation, every report cell of the source deme is an indicator.**  Its mass
is one on the founder's report and zero elsewhere. -/
theorem pushforwardMass_resamplingMove_one (source : Deme) (g : FullHaplotype Locus Allele)
    (x : FrequencyState Deme Locus Allele) {Report : Type*} [Fintype Report] [DecidableEq Report]
    (report : FullHaplotype Locus Allele → Report) (selected : Report) :
    ((stateLaw (resamplingMove source g 1 zero_le_one le_rfl x) source).pushforward report).mass
        selected
      = if report g = selected then 1 else 0 := by
  rw [pushforwardMass_eq_expectation, expectation_resamplingMove_one]

/-- **After complete fixation, a positive quotient is the indicator of a called case.**  For a cell
`c` other than the true positives, `TP / (TP + c)` in the source deme is one when the founder is a
called case and zero otherwise, with Lean's `0 / 0 = 0`.

Assumes: `c` is not the true-positive cell. -/
theorem positiveQuotient_resamplingMove_one (source : Deme) (g : FullHaplotype Locus Allele)
    (x : FrequencyState Deme Locus Allele) {Score : Type*} [Fintype Score]
    (report : FullHaplotype Locus Allele → Score × Bool) (called : Score → Bool)
    (other : Bool × Bool) (hother : (true, true) ≠ other) :
    ((stateLaw (resamplingMove source g 1 zero_le_one le_rfl x) source).pushforward
          (confusionReport report called)).mass (true, true)
        / (((stateLaw (resamplingMove source g 1 zero_le_one le_rfl x) source).pushforward
            (confusionReport report called)).mass (true, true)
          + ((stateLaw (resamplingMove source g 1 zero_le_one le_rfl x) source).pushforward
            (confusionReport report called)).mass other)
      = if confusionReport report called g = (true, true) then 1 else 0 := by
  rw [pushforwardMass_resamplingMove_one, pushforwardMass_resamplingMove_one]
  by_cases htrue : confusionReport report called g = (true, true)
  · rw [if_pos htrue, if_neg fun hcell ↦ hother (htrue.symm.trans hcell)]
    norm_num
  · rw [if_neg htrue, zero_div]

/-- **Without the event, the expected positive quotient is the quotient of the state.** -/
theorem expectedPositiveQuotient_founderEventLaw_zero (source : Deme)
    (x : FrequencyState Deme Locus Allele) {Score : Type*} [Fintype Score]
    (report : FullHaplotype Locus Allele → Score × Bool) (called : Score → Bool)
    (other : Bool × Bool) :
    expectedPositiveQuotient (Kernel.const _ (founderEventLaw source 0 le_rfl zero_le_one x)) x
        source report called other
      = ((stateLaw x source).pushforward (confusionReport report called)).mass (true, true)
        / (((stateLaw x source).pushforward (confusionReport report called)).mass (true, true)
          + ((stateLaw x source).pushforward (confusionReport report called)).mass other) := by
  rw [expectedPositiveQuotient, Kernel.const_apply,
    integral_founderEventLaw_of_stronglyMeasurable source 0 le_rfl zero_le_one x
      (stronglyMeasurable_positiveQuotient source report called other)]
  simp only [resamplingMove_zero]
  rw [← Finset.sum_mul, x.2.2 source, one_mul]

/-- **After complete fixation, the expected positive quotient is the true-positive mass.**  For a
cell `c` other than the true positives, the expected `TP / (TP + c)` in the source deme after the
founder event at fraction one is `TP` of the state before.

Assumes: `c` is not the true-positive cell. -/
theorem expectedPositiveQuotient_founderEventLaw_one (source : Deme)
    (x : FrequencyState Deme Locus Allele) {Score : Type*} [Fintype Score]
    (report : FullHaplotype Locus Allele → Score × Bool) (called : Score → Bool)
    (other : Bool × Bool) (hother : (true, true) ≠ other) :
    expectedPositiveQuotient (Kernel.const _ (founderEventLaw source 1 zero_le_one le_rfl x)) x
        source report called other
      = ((stateLaw x source).pushforward (confusionReport report called)).mass (true, true) := by
  rw [expectedPositiveQuotient, Kernel.const_apply,
    integral_founderEventLaw_of_stronglyMeasurable source 1 zero_le_one le_rfl x
      (stronglyMeasurable_positiveQuotient source report called other),
    pushforwardMass_eq_expectation, FiniteReportLaw.expectation]
  refine Finset.sum_congr rfl fun g _ ↦ ?_
  exact congrArg (x.1 (source, g) * ·)
    (positiveQuotient_resamplingMove_one source g x report called other hother)

/-- **The founder events at fractions zero and one separate the expected positive quotient.**  For
a cell `c` other than the true positives, the expected `TP / (TP + c)` in the source deme is
`TP / (TP + c)` of the state without the event and `TP` after complete fixation, and these differ.

Assumes: `c` is not the true-positive cell, `0 < TP` and `TP + c < 1` in the source deme. -/
theorem expectedPositiveQuotient_founderEventLaw_ne (source : Deme)
    (x : FrequencyState Deme Locus Allele) {Score : Type*} [Fintype Score]
    (report : FullHaplotype Locus Allele → Score × Bool) (called : Score → Bool)
    (other : Bool × Bool) (hother : (true, true) ≠ other)
    (hpositive :
      0 < ((stateLaw x source).pushforward (confusionReport report called)).mass (true, true))
    (hbelow : ((stateLaw x source).pushforward (confusionReport report called)).mass (true, true)
      + ((stateLaw x source).pushforward (confusionReport report called)).mass other < 1) :
    expectedPositiveQuotient (Kernel.const _ (founderEventLaw source 0 le_rfl zero_le_one x)) x
        source report called other
      ≠ expectedPositiveQuotient (Kernel.const _ (founderEventLaw source 1 zero_le_one le_rfl x))
        x source report called other := by
  rw [expectedPositiveQuotient_founderEventLaw_zero,
    expectedPositiveQuotient_founderEventLaw_one source x report called other hother]
  intro hequal
  have hsumPositive := add_pos_of_pos_of_nonneg hpositive
    (((stateLaw x source).pushforward (confusionReport report called)).mass_nonneg other)
  rw [div_eq_iff hsumPositive.ne'] at hequal
  exact hbelow.ne (mul_left_cancel₀ hpositive.ne' (hequal.symm.trans (mul_one _).symm))

/-! ## Equal expected frequencies, different recall and precision -/

/-- **Equal expected frequencies do not fix the expected recall.**  From a state `x₀`, the founder
events at fractions zero and one in deme `source` give every haplotype in every deme one expected
frequency.  Yet the expected per-population recall `E[TP / (TP + FN)]` in the source deme is
`TP / (TP + FN)` of `x₀` under the first and `TP` of `x₀` under the second, and these differ.  The
conditions hold whenever the source deme carries called cases and controls with positive frequency.

Assumes: `0 < TP` and `TP + FN < 1` in the source deme at `x₀`. -/
theorem expectedFrequencies_eq_and_expectedRecall_ne (source : Deme)
    (x₀ : FrequencyState Deme Locus Allele) {Score : Type*} [Fintype Score]
    (report : FullHaplotype Locus Allele → Score × Bool) (called : Score → Bool)
    (hpositive :
      0 < ((stateLaw x₀ source).pushforward (confusionReport report called)).mass (true, true))
    (hcases : ((stateLaw x₀ source).pushforward (confusionReport report called)).mass (true, true)
      + ((stateLaw x₀ source).pushforward (confusionReport report called)).mass (false, true)
        < 1) :
    (∀ (deme : Deme) (hap : FullHaplotype Locus Allele),
      ∫ y, (stateLaw y deme).mass hap ∂(founderEventLaw source 0 le_rfl zero_le_one x₀)
        = ∫ y, (stateLaw y deme).mass hap ∂(founderEventLaw source 1 zero_le_one le_rfl x₀))
      ∧ ∫ y, (ruleConfusion ((stateLaw y source).pushforward report) called).recallRate
          ∂(Kernel.const (FrequencyState Deme Locus Allele)
            (founderEventLaw source 0 le_rfl zero_le_one x₀) x₀)
        ≠ ∫ y, (ruleConfusion ((stateLaw y source).pushforward report) called).recallRate
          ∂(Kernel.const (FrequencyState Deme Locus Allele)
            (founderEventLaw source 1 zero_le_one le_rfl x₀) x₀) := by
  refine ⟨fun deme hap ↦ ?_, ?_⟩
  · rw [integral_mass_founderEventLaw, integral_mass_founderEventLaw]
  · rw [(integral_recallRate_precision _ x₀ source report called).1,
      (integral_recallRate_precision _ x₀ source report called).1]
    exact expectedPositiveQuotient_founderEventLaw_ne source x₀ report called (false, true)
      (by decide) hpositive hcases

/-- **Equal expected frequencies do not fix the expected precision.**  From a state `x₀`, the
founder events at fractions zero and one in deme `source` give every haplotype in every deme one
expected frequency.  Yet the expected per-population precision `E[TP / (TP + FP)]` in the source
deme is `TP / (TP + FP)` of `x₀` under the first and `TP` of `x₀` under the second, and these
differ.  The conditions hold whenever the source deme carries called cases and uncalled haplotypes
with positive frequency.

Assumes: `0 < TP` and `TP + FP < 1` in the source deme at `x₀`. -/
theorem expectedFrequencies_eq_and_expectedPrecision_ne (source : Deme)
    (x₀ : FrequencyState Deme Locus Allele) {Score : Type*} [Fintype Score]
    (report : FullHaplotype Locus Allele → Score × Bool) (called : Score → Bool)
    (hpositive :
      0 < ((stateLaw x₀ source).pushforward (confusionReport report called)).mass (true, true))
    (hcalled : ((stateLaw x₀ source).pushforward (confusionReport report called)).mass (true, true)
      + ((stateLaw x₀ source).pushforward (confusionReport report called)).mass (true, false)
        < 1) :
    (∀ (deme : Deme) (hap : FullHaplotype Locus Allele),
      ∫ y, (stateLaw y deme).mass hap ∂(founderEventLaw source 0 le_rfl zero_le_one x₀)
        = ∫ y, (stateLaw y deme).mass hap ∂(founderEventLaw source 1 zero_le_one le_rfl x₀))
      ∧ ∫ y, (ruleConfusion ((stateLaw y source).pushforward report) called).precision
          ∂(Kernel.const (FrequencyState Deme Locus Allele)
            (founderEventLaw source 0 le_rfl zero_le_one x₀) x₀)
        ≠ ∫ y, (ruleConfusion ((stateLaw y source).pushforward report) called).precision
          ∂(Kernel.const (FrequencyState Deme Locus Allele)
            (founderEventLaw source 1 zero_le_one le_rfl x₀) x₀) := by
  refine ⟨fun deme hap ↦ ?_, ?_⟩
  · rw [integral_mass_founderEventLaw, integral_mass_founderEventLaw]
  · rw [(integral_recallRate_precision _ x₀ source report called).2,
      (integral_recallRate_precision _ x₀ source report called).2]
    exact expectedPositiveQuotient_founderEventLaw_ne source x₀ report called (true, false)
      (by decide) hpositive hcalled

end

end Descent.Portability.PortabilityMomentLadderDecisionSharpness
