/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.EndToEndCorrelationSeries
import Descent.Portability.FiniteDemographicSampling
import Descent.Portability.MeiosisGameteLaw
import Descent.Portability.ScoreMomentLaw

assert_below Descent.Decision Descent.Program

/-!
# The end-to-end portability law for diploid genotypes

`EndToEndPortabilityLaw` carries a demographic history to the portability of a score and an
outcome that read one haplotype per individual.  Polygenic scores read two.  This module joins the
diploid mating step to the history kernels and says exactly when the haploid law transfers.

The gamete pair.  Inside a deme with haplotype law `p`, the two gametes of an individual are
identical by descent with probability `F`, and otherwise are two independent draws from `p`
(`inbredMating`, built from the corpus Bernoulli law, the pushforward of `p` to the diagonal and
`FiniteReproductiveKernel.independentMating`).  `F = 0` is random union of gametes
(`inbredMating_zero`).  An observable `φ` of the pair integrates as
`(1 - F) E_a E_b φ(a, b) + F E_a φ(a, a)` (`expectation_inbredMating`).

Diploid moments.  Take the additive lifts `S_d = S(h₁) + S(h₂)` and `Y_d = Y(h₁) + Y(h₂)`
(`diploidSum`).  The mean doubles (`expectation_inbredMating_diploidSum`).  Within one gamete the
covariance is the haploid one, and across the two gametes it is `F` times it
(`covariance_inbredMating_gametes`).  So `Cov(S_d, Y_d) = 2 (1 + F) C_SY`, and each variance is
`2 (1 + F)` times the haploid one (`covariance_inbredMating_diploidSum`,
`variance_inbredMating_diploidSum`).  The correlation numerator and denominator of NOTE2 (21) both
scale by `4 (1 + F)²` (`correlationNumerator_inbredMating_diploidSum`,
`correlationDenominator_inbredMating_diploidSum`).

The transfer.  The diploid squared correlation therefore equals the haploid one for every `F` in
the unit interval (`squaredCorrelation_inbredMating_diploidSum`).  Under random union `C` and
each variance double (`covariance_independentMating_diploidSum`,
`variance_independentMating_diploidSum`) and the squared correlation is unchanged
(`squaredCorrelation_independentMating_diploidSum`).  The inbreeding correction factor between a
source at `F_s` and a target at `F_t` is exactly one.  The factors `1 + F_s` and `1 + F_t` enter
every moment and cancel from every squared correlation and from the portability of expected
accuracies, under any Markov kernel (`expectedDiploidPortability_diploidSum`).  Along a history of
epochs, splits and pulses, the expected diploid numerator and denominator are `4 (1 + F)²` times
the haploid coefficient vectors dotted with the propagated budget-4 moments
(`integral_diploidNumerator_historyEventKernel`,
`integral_diploidDenominator_historyEventKernel`).  Diploid expected portability is the haploid
rational function `momentPortability` of those moments, along an event history or a rate history
(`expectedDiploidPortability_historyEventKernel`, `expectedDiploidPortability_rateHistoryKernel`),
and two histories with equal propagated moments give equal diploid portability
(`expectedDiploidPortability_eq_of_moments_eq`).  The expected diploid squared correlation is the
haploid one, so the series of `EndToEndCorrelationSeries` expands it
(`integral_squaredCorrelation_stateGenotypeLaw`).

The boundary.  Dominance breaks the identity.  At one biallelic site with allele frequency one
half, the additive score and the recessive outcome `Y(h₁) Y(h₂)` (`diploidProduct`) have diploid
squared correlation `2 / (3 - F)` (`squaredCorrelation_inbredMating_diploidProduct`).  The allele
is perfectly correlated with itself in one haplotype (`squaredCorrelation_fairSwitch_alleleValue`).
Random union gives `2 / 3` and full autozygosity gives `1`, so for that outcome neither the ploidy
nor the inbreeding coefficient can be dropped (`diploidProduct_breaks_ploidy_transfer`).

Significance.  Human polygenic scores are sums over two haplotypes.  The transfer says the
haploid end-to-end law, its budget-4 moments and its rational portability function, applies to
them unchanged, under random union and under whole-haplotype inbreeding, provided score and
outcome are additive over the two gametes.  The witness says the proviso cannot be removed.

Scope.  The transfer assumes exactly three things.  Both gametes are drawn from the deme's own
haplotype law, so there are no sex-specific frequencies.  Identity by descent is one event shared
by every locus of the haplotype, with a coefficient in the unit interval supplied per deme rather
than derived from the history.  Score and outcome are the same haploid functions summed over the
two gametes.  Locus-dependent inbreeding coefficients, heterozygote excess, assortative mating, and
outcomes carrying variance not given by the genotype are not covered.  Non-additive diploid
observables along a history are carried at budget eight by `EndToEndDiploidHistoryLaw`.

## Empirical status

None.  The bodies here are finite sums against constructed laws and integrals of polynomials
against Markov kernels, so no measurement can bear on them.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.EndToEndDiploidLaw

open MeasureTheory ProbabilityTheory Descent.Coalescent PartialHaplotypeCarrier
  PartialHaplotypeDualGenerator PartialHaplotypeDualSemigroup NeutralFellerGenerator
  NeutralPolynomialSemigroup PartialHaplotypeMicroscopicApproximation PartialHaplotypePulseKernel
  NeutralPulseHistoryKernel NeutralRateHistoryRealization NeutralRateHistoryKernel
  ReplicaMetricInstances EndToEndPortabilityLaw
open scoped Matrix NNReal

noncomputable section

/-! ## The gamete pair of a deme -/

section Genotypes

variable {H : Type*} [Fintype H] [DecidableEq H]

/-- **The gamete pair with inbreeding coefficient `F`.**  With probability `F` the two gametes
carry one haplotype identical by descent, drawn from the deme law; otherwise they are two
independent draws from it. -/
def inbredMating (law : FiniteReportLaw H) (F : ℝ) (hF0 : 0 ≤ F) (hF1 : F ≤ 1) :
    FiniteReportLaw (H × H) :=
  (FiniteDemographicSampling.bernoulli F hF0 hF1).bind fun identical ↦
    cond identical (law.pushforward fun haplotype ↦ (haplotype, haplotype))
      (FiniteReproductiveKernel.independentMating law)

/-- Random union of gametes integrates an observable of the pair as two nested independent draws
from the deme law. -/
theorem expectation_independentMating (law : FiniteReportLaw H) (φ : H × H → ℝ) :
    (FiniteReproductiveKernel.independentMating law).expectation φ =
      law.expectation fun first ↦ law.expectation fun second ↦ φ (first, second) := by
  simp only [FiniteReportLaw.expectation, Fintype.sum_prod_type, Finset.mul_sum]
  exact Finset.sum_congr rfl fun first _ ↦ Finset.sum_congr rfl fun second _ ↦
    mul_assoc (law.mass first) (law.mass second) (φ (first, second))

/-- **An observable of the gamete pair integrates through the deme law**: independent draws with
weight `1 - F`, and the diagonal with weight `F`. -/
theorem expectation_inbredMating (law : FiniteReportLaw H) (F : ℝ) (hF0 : 0 ≤ F) (hF1 : F ≤ 1)
    (φ : H × H → ℝ) :
    (inbredMating law F hF0 hF1).expectation φ =
      (1 - F) * (law.expectation fun first ↦ law.expectation fun second ↦ φ (first, second))
        + F * law.expectation fun haplotype ↦ φ (haplotype, haplotype) := by
  rw [inbredMating, FiniteReportLaw.expectation_bind, FiniteReportLaw.expectation,
    Fintype.sum_bool]
  change F * (law.pushforward fun haplotype ↦ (haplotype, haplotype)).expectation φ
      + (1 - F) * (FiniteReproductiveKernel.independentMating law).expectation φ = _
  rw [FiniteReportLaw.expectation_pushforward, expectation_independentMating]
  ring

/-- **Random union is the gamete pair at `F = 0`.** -/
theorem inbredMating_zero (law : FiniteReportLaw H) :
    inbredMating law 0 le_rfl zero_le_one = FiniteReproductiveKernel.independentMating law := by
  refine FiniteReportLaw.ext fun pair ↦ ?_
  rw [inbredMating]
  change ∑ identical, (FiniteDemographicSampling.bernoulli 0 le_rfl zero_le_one).mass identical
      * (cond identical (law.pushforward fun haplotype ↦ (haplotype, haplotype))
        (FiniteReproductiveKernel.independentMating law)).mass pair = _
  rw [Fintype.sum_bool]
  change 0 * _ + (1 - 0) * (FiniteReproductiveKernel.independentMating law).mass pair = _
  ring

/-- **Each gamete carries the deme law.**  An observable of either gamete has its haploid
expectation, whatever the inbreeding coefficient. -/
theorem expectation_inbredMating_gametes (law : FiniteReportLaw H) (F : ℝ) (hF0 : 0 ≤ F)
    (hF1 : F ≤ 1) (value : H → ℝ) :
    (inbredMating law F hF0 hF1).expectation (fun pair ↦ value pair.1) = law.expectation value ∧
      (inbredMating law F hF0 hF1).expectation (fun pair ↦ value pair.2)
        = law.expectation value := by
  refine ⟨?_, ?_⟩ <;> rw [expectation_inbredMating] <;>
    simp only [FiniteIndependentMoments.expectation_const] <;> ring

/-- **The cross-gamete product moment**: the independent product with weight `1 - F` and the
within-haplotype product with weight `F`. -/
theorem expectation_inbredMating_cross (law : FiniteReportLaw H) (F : ℝ) (hF0 : 0 ≤ F)
    (hF1 : F ≤ 1) (first second : H → ℝ) :
    (inbredMating law F hF0 hF1).expectation (fun pair ↦ first pair.1 * second pair.2) =
      (1 - F) * (law.expectation first * law.expectation second)
        + F * law.expectation fun haplotype ↦ first haplotype * second haplotype := by
  have hproduct : (law.expectation fun a ↦ law.expectation fun b ↦ first a * second b)
      = law.expectation first * law.expectation second := by
    simp only [FiniteReportLaw.expectation]
    rw [Finset.sum_mul_sum]
    simp only [Finset.mul_sum]
    exact Finset.sum_congr rfl fun a _ ↦ Finset.sum_congr rfl fun b _ ↦ by ring
  rw [expectation_inbredMating]
  simp only [hproduct]

/-- **The gamete covariance kernel.**  Within one gamete the covariance of two observables is the
haploid covariance; across the two gametes it is `F` times it. -/
theorem covariance_inbredMating_gametes (law : FiniteReportLaw H) (F : ℝ) (hF0 : 0 ≤ F)
    (hF1 : F ≤ 1) (first second : H → ℝ) :
    (inbredMating law F hF0 hF1).covariance (fun pair ↦ first pair.1) (fun pair ↦ second pair.1)
        = law.covariance first second ∧
      (inbredMating law F hF0 hF1).covariance (fun pair ↦ first pair.2)
          (fun pair ↦ second pair.2) = law.covariance first second ∧
      (inbredMating law F hF0 hF1).covariance (fun pair ↦ first pair.1)
          (fun pair ↦ second pair.2) = F * law.covariance first second := by
  obtain ⟨hfirst1, hfirst2⟩ := expectation_inbredMating_gametes law F hF0 hF1 first
  obtain ⟨hsecond1, hsecond2⟩ := expectation_inbredMating_gametes law F hF0 hF1 second
  obtain ⟨hproduct1, hproduct2⟩ := expectation_inbredMating_gametes law F hF0 hF1
    fun haplotype ↦ first haplotype * second haplotype
  refine ⟨?_, ?_, ?_⟩
  · rw [FiniteReportLaw.covariance_eq_rawMoments, FiniteReportLaw.covariance_eq_rawMoments,
      hfirst1, hsecond1, hproduct1]
  · rw [FiniteReportLaw.covariance_eq_rawMoments, FiniteReportLaw.covariance_eq_rawMoments,
      hfirst2, hsecond2, hproduct2]
  · rw [FiniteReportLaw.covariance_eq_rawMoments, FiniteReportLaw.covariance_eq_rawMoments,
      hfirst1, hsecond2, expectation_inbredMating_cross]
    ring

/-! ## Additive diploid observables -/

/-- **The additive diploid lift** of a haplotype observable: its sum over the two gametes. -/
def diploidSum (value : H → ℝ) : H × H → ℝ := fun pair ↦ value pair.1 + value pair.2

/-- **The dominance lift** of a haplotype observable: its product over the two gametes.  For the
allele indicator it is the indicator of the recessive homozygote. -/
def diploidProduct (value : H → ℝ) : H × H → ℝ := fun pair ↦ value pair.1 * value pair.2

/-- The additive lift is the corpus linear score over the two gametes with unit weights. -/
theorem diploidSum_eq_linearScore (value : H → ℝ) :
    diploidSum value = TrainingNoiseAccuracy.linearScore
      (fun pair gamete ↦ value (cond gamete pair.2 pair.1)) fun _ ↦ 1 := by
  funext pair
  change value pair.1 + value pair.2 = ∑ gamete : Bool, 1 * value (cond gamete pair.2 pair.1)
  rw [Fintype.sum_bool]
  change value pair.1 + value pair.2 = 1 * value pair.2 + 1 * value pair.1
  ring

/-- Under any law of gamete pairs, the covariance with an additive diploid observable splits over
the two gametes. -/
theorem covariance_diploidSum_left (law : FiniteReportLaw (H × H)) (value : H → ℝ)
    (other : H × H → ℝ) :
    law.covariance (diploidSum value) other
      = law.covariance (fun pair ↦ value pair.1) other
        + law.covariance (fun pair ↦ value pair.2) other := by
  rw [diploidSum_eq_linearScore, TrainingNoiseAccuracy.covariance_linearScore, Fintype.sum_bool]
  change 1 * law.covariance (fun pair ↦ value pair.2) other
      + 1 * law.covariance (fun pair ↦ value pair.1) other = _
  ring

/-- **The diploid mean doubles.** -/
theorem expectation_inbredMating_diploidSum (law : FiniteReportLaw H) (F : ℝ) (hF0 : 0 ≤ F)
    (hF1 : F ≤ 1) (value : H → ℝ) :
    (inbredMating law F hF0 hF1).expectation (diploidSum value) = 2 * law.expectation value := by
  obtain ⟨hfirst, hsecond⟩ := expectation_inbredMating_gametes law F hF0 hF1 value
  rw [diploidSum_eq_linearScore, TrainingNoiseAccuracy.expectation_linearScore, Fintype.sum_bool]
  change 1 * (inbredMating law F hF0 hF1).expectation (fun pair ↦ value pair.2)
      + 1 * (inbredMating law F hF0 hF1).expectation (fun pair ↦ value pair.1) = _
  rw [hfirst, hsecond]
  ring

/-- **The diploid covariance is `2 (1 + F)` times the haploid covariance.**  Two within-gamete
terms and two cross-gamete terms, the latter weighted by `F`. -/
theorem covariance_inbredMating_diploidSum (law : FiniteReportLaw H) (F : ℝ) (hF0 : 0 ≤ F)
    (hF1 : F ≤ 1) (score outcome : H → ℝ) :
    (inbredMating law F hF0 hF1).covariance (diploidSum score) (diploidSum outcome)
      = 2 * (1 + F) * law.covariance score outcome := by
  obtain ⟨hsame1, hsame2, hcross⟩ := covariance_inbredMating_gametes law F hF0 hF1 outcome score
  obtain ⟨-, -, hcross'⟩ := covariance_inbredMating_gametes law F hF0 hF1 score outcome
  rw [covariance_diploidSum_left,
    TrainingNoiseAccuracy.covariance_symmetric _ (fun pair ↦ score pair.1),
    covariance_diploidSum_left,
    TrainingNoiseAccuracy.covariance_symmetric _ (fun pair ↦ score pair.2),
    covariance_diploidSum_left, hsame1, hsame2, hcross,
    TrainingNoiseAccuracy.covariance_symmetric _ (fun pair ↦ outcome pair.2), hcross',
    TrainingNoiseAccuracy.covariance_symmetric law outcome]
  ring

/-- **Each diploid variance is `2 (1 + F)` times the haploid variance.** -/
theorem variance_inbredMating_diploidSum (law : FiniteReportLaw H) (F : ℝ) (hF0 : 0 ≤ F)
    (hF1 : F ≤ 1) (value : H → ℝ) :
    (inbredMating law F hF0 hF1).variance (diploidSum value)
      = 2 * (1 + F) * law.variance value :=
  covariance_inbredMating_diploidSum law F hF0 hF1 value value

/-- **The diploid correlation numerator** `N_d = 16 Cov(S_d, Y_d)²` is `4 (1 + F)²` times the
haploid one. -/
theorem correlationNumerator_inbredMating_diploidSum (law : FiniteReportLaw H) (F : ℝ)
    (hF0 : 0 ≤ F) (hF1 : F ≤ 1) (score outcome : H → ℝ) :
    correlationNumerator (inbredMating law F hF0 hF1) (diploidSum score) (diploidSum outcome)
      = 4 * (1 + F) ^ 2 * correlationNumerator law score outcome := by
  rw [correlationNumerator, correlationNumerator, covariance_inbredMating_diploidSum]
  ring

/-- **The diploid correlation denominator** `D_d = 16 V_{S_d} V_{Y_d}` is `4 (1 + F)²` times the
haploid one. -/
theorem correlationDenominator_inbredMating_diploidSum (law : FiniteReportLaw H) (F : ℝ)
    (hF0 : 0 ≤ F) (hF1 : F ≤ 1) (score outcome : H → ℝ) :
    correlationDenominator (inbredMating law F hF0 hF1) (diploidSum score) (diploidSum outcome)
      = 4 * (1 + F) ^ 2 * correlationDenominator law score outcome := by
  rw [correlationDenominator, correlationDenominator, variance_inbredMating_diploidSum,
    variance_inbredMating_diploidSum]
  ring

/-- **The additive diploid squared correlation is the haploid one**, for every inbreeding
coefficient in the unit interval: the factor `2 (1 + F)` cancels, and it is positive, so the two
squared correlations are defined together. -/
theorem squaredCorrelation_inbredMating_diploidSum (law : FiniteReportLaw H) (F : ℝ)
    (hF0 : 0 ≤ F) (hF1 : F ≤ 1) (score outcome : H → ℝ) :
    (inbredMating law F hF0 hF1).squaredCorrelation (diploidSum score) (diploidSum outcome)
      = law.squaredCorrelation score outcome := by
  have hscale : 0 < 2 * (1 + F) := by linarith
  have hcondition : (0 < 2 * (1 + F) * law.variance score
      ∧ 0 < 2 * (1 + F) * law.variance outcome)
        ↔ (0 < law.variance score ∧ 0 < law.variance outcome) := by
    rw [mul_pos_iff_of_pos_left hscale, mul_pos_iff_of_pos_left hscale]
  have hratio : (2 * (1 + F) * law.covariance score outcome) ^ 2
      / (2 * (1 + F) * law.variance score * (2 * (1 + F) * law.variance outcome))
        = law.covariance score outcome ^ 2 / (law.variance score * law.variance outcome) := by
    rw [show (2 * (1 + F) * law.covariance score outcome) ^ 2
        = (2 * (1 + F)) ^ 2 * law.covariance score outcome ^ 2 by ring,
      show 2 * (1 + F) * law.variance score * (2 * (1 + F) * law.variance outcome)
        = (2 * (1 + F)) ^ 2 * (law.variance score * law.variance outcome) by ring]
    exact mul_div_mul_left _ _ (pow_ne_zero 2 hscale.ne')
  rw [FiniteReportLaw.squaredCorrelation, FiniteReportLaw.squaredCorrelation,
    variance_inbredMating_diploidSum, variance_inbredMating_diploidSum,
    covariance_inbredMating_diploidSum, hratio]
  exact if_congr hcondition rfl rfl

/-- **Random union doubles the covariance.** -/
theorem covariance_independentMating_diploidSum (law : FiniteReportLaw H)
    (score outcome : H → ℝ) :
    (FiniteReproductiveKernel.independentMating law).covariance (diploidSum score)
        (diploidSum outcome)
      = 2 * law.covariance score outcome := by
  rw [← inbredMating_zero, covariance_inbredMating_diploidSum]
  ring

/-- **Random union doubles each variance.** -/
theorem variance_independentMating_diploidSum (law : FiniteReportLaw H) (value : H → ℝ) :
    (FiniteReproductiveKernel.independentMating law).variance (diploidSum value)
      = 2 * law.variance value :=
  covariance_independentMating_diploidSum law value value

/-- **Under random union the additive diploid squared correlation is the haploid one.**  The
assumptions are exactly: gametes drawn independently from one deme law, and score and outcome
summed over the two gametes. -/
theorem squaredCorrelation_independentMating_diploidSum (law : FiniteReportLaw H)
    (score outcome : H → ℝ) :
    (FiniteReproductiveKernel.independentMating law).squaredCorrelation (diploidSum score)
        (diploidSum outcome)
      = law.squaredCorrelation score outcome := by
  rw [← inbredMating_zero]
  exact squaredCorrelation_inbredMating_diploidSum law 0 le_rfl zero_le_one score outcome

end Genotypes

/-! ## Dominance breaks the transfer -/

section Dominance

/-- The corpus fair switch integrates an observable of one allele as the average of its two
values. -/
theorem expectation_fairSwitch (value : Bool → ℝ) :
    MeiosisGameteLaw.fairSwitch.expectation value = (value true + value false) / 2 := by
  rw [FiniteReportLaw.expectation, Fintype.sum_bool]
  change 1 / 2 * value true + 1 / 2 * value false = _
  ring

/-- At the fair switch the allele indicator is perfectly correlated with itself in one
haplotype. -/
theorem squaredCorrelation_fairSwitch_alleleValue :
    MeiosisGameteLaw.fairSwitch.squaredCorrelation ChronologyReportLaw.alleleValue
      ChronologyReportLaw.alleleValue = some 1 := by
  have hcovariance : MeiosisGameteLaw.fairSwitch.covariance ChronologyReportLaw.alleleValue
      ChronologyReportLaw.alleleValue = 1 / 4 := by
    rw [FiniteReportLaw.covariance_eq_rawMoments, expectation_fairSwitch, expectation_fairSwitch]
    norm_num
  simp only [FiniteReportLaw.squaredCorrelation, FiniteReportLaw.variance, hcovariance]
  norm_num

/-- **The recessive outcome at one site.**  With allele frequency one half, the additive score and
the recessive homozygote indicator have diploid squared correlation `2 / (3 - F)`: the inbreeding
coefficient does not cancel. -/
theorem squaredCorrelation_inbredMating_diploidProduct (F : ℝ) (hF0 : 0 ≤ F) (hF1 : F ≤ 1) :
    (inbredMating MeiosisGameteLaw.fairSwitch F hF0 hF1).squaredCorrelation
        (diploidSum ChronologyReportLaw.alleleValue)
        (diploidProduct ChronologyReportLaw.alleleValue) = some (2 / (3 - F)) := by
  have hpair : ∀ φ : Bool × Bool → ℝ,
      (inbredMating MeiosisGameteLaw.fairSwitch F hF0 hF1).expectation φ
        = (1 - F) * ((φ (true, true) + φ (true, false) + (φ (false, true) + φ (false, false))) / 4)
          + F * ((φ (true, true) + φ (false, false)) / 2) := by
    intro φ
    rw [expectation_inbredMating]
    simp only [expectation_fairSwitch]
    ring
  have hscore : (inbredMating MeiosisGameteLaw.fairSwitch F hF0 hF1).variance
      (diploidSum ChronologyReportLaw.alleleValue) = (1 + F) / 2 := by
    rw [FiniteReportLaw.variance_eq_rawMoments]
    simp only [hpair, diploidSum, ChronologyReportLaw.alleleValue_true,
      ChronologyReportLaw.alleleValue_false]
    ring
  have houtcome : (inbredMating MeiosisGameteLaw.fairSwitch F hF0 hF1).variance
      (diploidProduct ChronologyReportLaw.alleleValue) = (1 + F) * (3 - F) / 16 := by
    rw [FiniteReportLaw.variance_eq_rawMoments]
    simp only [hpair, diploidProduct, ChronologyReportLaw.alleleValue_true,
      ChronologyReportLaw.alleleValue_false]
    ring
  have hcovariance : (inbredMating MeiosisGameteLaw.fairSwitch F hF0 hF1).covariance
      (diploidSum ChronologyReportLaw.alleleValue)
      (diploidProduct ChronologyReportLaw.alleleValue) = (1 + F) / 4 := by
    rw [FiniteReportLaw.covariance_eq_rawMoments]
    simp only [hpair, diploidSum, diploidProduct, ChronologyReportLaw.alleleValue_true,
      ChronologyReportLaw.alleleValue_false]
    ring
  have hscorePos : 0 < (1 + F) / 2 := by linarith
  have houtcomePos : 0 < (1 + F) * (3 - F) / 16 :=
    div_pos (mul_pos (by linarith) (by linarith)) (by norm_num)
  rw [FiniteReportLaw.squaredCorrelation, hscore, houtcome, hcovariance,
    if_pos ⟨hscorePos, houtcomePos⟩]
  congr 1
  rw [div_eq_div_iff (mul_pos hscorePos houtcomePos).ne' (by linarith : (0 : ℝ) < 3 - F).ne']
  ring

/-- **Dominance breaks the ploidy transfer.**  For the recessive outcome, the diploid squared
correlation under random union differs from the haploid squared correlation of the allele with
itself, and random union and full autozygosity give different squared correlations for the same
haplotype law. -/
theorem diploidProduct_breaks_ploidy_transfer :
    (FiniteReproductiveKernel.independentMating MeiosisGameteLaw.fairSwitch).squaredCorrelation
        (diploidSum ChronologyReportLaw.alleleValue)
        (diploidProduct ChronologyReportLaw.alleleValue)
      ≠ MeiosisGameteLaw.fairSwitch.squaredCorrelation ChronologyReportLaw.alleleValue
        ChronologyReportLaw.alleleValue ∧
    (inbredMating MeiosisGameteLaw.fairSwitch 0 le_rfl zero_le_one).squaredCorrelation
        (diploidSum ChronologyReportLaw.alleleValue)
        (diploidProduct ChronologyReportLaw.alleleValue)
      ≠ (inbredMating MeiosisGameteLaw.fairSwitch 1 zero_le_one le_rfl).squaredCorrelation
        (diploidSum ChronologyReportLaw.alleleValue)
        (diploidProduct ChronologyReportLaw.alleleValue) := by
  refine ⟨?_, ?_⟩
  · rw [← inbredMating_zero, squaredCorrelation_inbredMating_diploidProduct,
      squaredCorrelation_fairSwitch_alleleValue]
    norm_num
  · rw [squaredCorrelation_inbredMating_diploidProduct,
      squaredCorrelation_inbredMating_diploidProduct]
    norm_num

end Dominance

end

end Descent.Portability.EndToEndDiploidLaw
