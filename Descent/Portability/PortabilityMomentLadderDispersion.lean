/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.PortabilityMomentLadderDecision
import Mathlib.Probability.Moments.Variance

assert_below Descent.Decision Descent.Program

/-!
# The dispersion rung of the moment ladder: replicate variance and concentration

`PortabilityMomentLadder` and `PortabilityMomentLadderDecision` fix expected metrics, the means of
per-population metrics over replicate populations of one demography.  This module fixes how much a
per-population metric varies across those replicates, and bounds how far it strays from its mean.

The law.  Take a per-population metric that is a frequency polynomial `p`, under a Markov kernel.
Its replicate variance is the expectation of `p²` minus the square of the expectation of `p`
(`variance_polynomialFunction_eq`).  If `p` has total degree at most `d`, then `p²` has total
degree at most `2d`.  So two process laws that agree up to degree `2d` give `p` one replicate
variance (`variance_polynomialFunction_eq_of_polynomialsAgreeAt_two_mul`).

The instances.
* Degree two fixes the replicate dispersion of the decision report
  (`decisionDispersion_eq_of_polynomialsAgreeAt_two`): the replicate variance of every cell of the
  confusion table, of the case probability, of the called fraction and of the net benefit at every
  threshold, in every deme.  Each is a frequency polynomial of total degree at most one.
* Degree four fixes the replicate variance of the covariance of every two haplotype observables in
  every deme (`covarianceDispersion_eq_of_polynomialsAgreeAt_four`).  Each covariance is a
  frequency polynomial of total degree at most two.

Concentration.  Chebyshev's inequality bounds the probability that an observable of total degree
at most `d` strays from its expectation by at least `t > 0`.  The bound is `(E[p²] - E[p]²) / t²`,
and both expectations may be taken under any process law that agrees up to degree `2d`
(`deviation_le_of_polynomialsAgreeAt_two_mul`).  For a cell of the confusion table, the bound is
the replicate variance under any process law that agrees up to degree two
(`confusionDeviation_le_of_polynomialsAgreeAt_two`).

Event and rate histories.  If a history of epochs, splits and pulses and a continuous rate history
have equal propagated budget-2 moments, every rule has the same decision dispersion under both
(`decisionDispersion_historyEvent_eq_rateHistory`).

Significance.  A threshold metric measured in one population is one draw from the replicate law of
its demography.  How widely that draw scatters around the expected metric is fixed by the degree-2
moments, one rung above the expectation itself.

Scope.  The replicate variances here are those of per-population metrics that are polynomial in the
haplotype frequencies.  The replicate variance of a ratio metric such as recall or precision is not
settled here, and neither is a tail bound sharper than Chebyshev's.

## Empirical status

None.  The bodies here are integrals of squares of frequency polynomials against Markov kernels and
Chebyshev's inequality for them, so no measurement can bear on them.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.PortabilityMomentLadderDispersion

open MeasureTheory ProbabilityTheory MvPolynomial Descent.Coalescent PartialHaplotypeCarrier
  PartialHaplotypeDualGenerator PartialHaplotypeDualSemigroup NeutralFellerGenerator
  NeutralPolynomialSemigroup PartialHaplotypeMicroscopicApproximation PartialHaplotypePulseKernel
  NeutralPulseHistoryKernel NeutralRateHistoryRealization NeutralRateHistoryKernel
  ReplicaMetricInstances EndToEndPortabilityLaw EndToEndCalibrationLaw EndToEndDiscriminationLaw
  EndToEndBrierLaw EndToEndDecisionLaw PortabilityMomentLadder PortabilityMomentLadderDecision
open scoped Matrix NNReal

noncomputable section

/-- **A decision dispersion**: for a rule on a report map under a process law, the replicate
variance of every cell of the confusion table, of the case probability, of the called fraction and
of the net benefit at every threshold, in every population. -/
structure DecisionDispersion (Population : Type*) where
  /-- The replicate variance of each cell of the confusion table of each population. -/
  table : Population → Bool × Bool → ℝ
  /-- The replicate variance of the case probability of each population. -/
  prevalence : Population → ℝ
  /-- The replicate variance of the called fraction of each population. -/
  calledFraction : Population → ℝ
  /-- The replicate variance of the net benefit of each population at each threshold probability. -/
  netBenefit : Population → ℝ → ℝ

variable {Deme Locus : Type*} {Allele : Locus → Type*}
variable [Fintype Deme] [DecidableEq Deme] [Fintype Locus] [DecidableEq Locus]
  [∀ ℓ, Fintype (Allele ℓ)] [∀ ℓ, DecidableEq (Allele ℓ)]

attribute [local instance] isMarkovKernel_historyEventKernel isMarkovKernel_rateHistoryKernel

/-- **The decision dispersion** of a rule `called` on a report map `hap ↦ (s, b)` under a kernel
started at `x₀`: the replicate variances of the per-population metrics behind `decisionReport`. -/
def decisionDispersion
    (κ : Kernel (FrequencyState Deme Locus Allele) (FrequencyState Deme Locus Allele))
    (x0 : FrequencyState Deme Locus Allele) {Score : Type*} [Fintype Score]
    (report : FullHaplotype Locus Allele → Score × Bool) (called : Score → Bool) :
    DecisionDispersion Deme where
  table deme cell :=
    variance (fun y ↦ ((stateLaw y deme).pushforward (confusionReport report called)).mass cell)
      (κ x0)
  prevalence deme :=
    variance (fun y ↦ ((stateLaw y deme).pushforward report).binaryCaseMass Prod.snd) (κ x0)
  calledFraction deme :=
    variance (fun y ↦ calledMass ((stateLaw y deme).pushforward report) called true
      + calledMass ((stateLaw y deme).pushforward report) called false) (κ x0)
  netBenefit deme t :=
    variance (fun y ↦ ruleNetBenefit ((stateLaw y deme).pushforward report) called t) (κ x0)

/-- A polynomial observable of the state is square integrable under every Markov kernel. -/
theorem memLp_two_polynomialFunction
    (κ : Kernel (FrequencyState Deme Locus Allele) (FrequencyState Deme Locus Allele))
    [IsMarkovKernel κ] (x0 : FrequencyState Deme Locus Allele)
    (p : FrequencyPolynomial Deme Locus Allele) :
    MemLp (polynomialFunction p) 2 (κ x0) := by
  have hcontinuous := (polynomialFunction p).continuous
  exact (memLp_two_iff_integrable_sq
    (integrable_continuousObservable κ x0 hcontinuous).aestronglyMeasurable).mpr
    (integrable_continuousObservable κ x0 (hcontinuous.pow 2))

/-- **The replicate variance of a polynomial observable is two polynomial expectations.**  Under a
Markov kernel, the variance across replicate populations of a frequency polynomial `p` is the
expectation of `p²` minus the square of the expectation of `p`. -/
theorem variance_polynomialFunction_eq
    (κ : Kernel (FrequencyState Deme Locus Allele) (FrequencyState Deme Locus Allele))
    [IsMarkovKernel κ] (x0 : FrequencyState Deme Locus Allele)
    (p : FrequencyPolynomial Deme Locus Allele) :
    variance (polynomialFunction p) (κ x0)
      = ∫ y, polynomialFunction (p ^ 2) y ∂(κ x0) - (∫ y, polynomialFunction p y ∂(κ x0)) ^ 2 := by
  rw [variance_eq_sub (memLp_two_polynomialFunction κ x0 p)]
  simp only [Pi.pow_apply, polynomialFunction_apply, map_pow]

/-- **Degree `2d` fixes the replicate variance of a degree-`d` observable.**  Two Markov kernels
that agree, from their initial states, on every frequency polynomial of total degree at most `2d`
give every frequency polynomial of total degree at most `d` one replicate variance.

Assumes: agreement up to degree `2d`, and `p` of total degree at most `d`. -/
theorem variance_polynomialFunction_eq_of_polynomialsAgreeAt_two_mul
    {κ₁ κ₂ : Kernel (FrequencyState Deme Locus Allele) (FrequencyState Deme Locus Allele)}
    [IsMarkovKernel κ₁] [IsMarkovKernel κ₂] {x₁ x₂ : FrequencyState Deme Locus Allele} {d : ℕ}
    (h : PolynomialsAgreeAt (2 * d) κ₁ κ₂ x₁ x₂) {p : FrequencyPolynomial Deme Locus Allele}
    (hp : p.totalDegree ≤ d) :
    variance (polynomialFunction p) (κ₁ x₁) = variance (polynomialFunction p) (κ₂ x₂) := by
  rw [variance_polynomialFunction_eq κ₁ x₁ p, variance_polynomialFunction_eq κ₂ x₂ p,
    h (p ^ 2) ((totalDegree_pow p 2).trans (by omega)), h p (hp.trans (by omega))]

/-- **Degree two fixes the decision dispersion under any process law.**  Two Markov kernels that
agree, from their initial states, on every frequency polynomial of total degree at most two give
every rule on every report map the same decision dispersion.  That is the same replicate variance
of every cell of the confusion table, of the case probability, of the called fraction and of the
net benefit at every threshold, in every deme.

Assumes: agreement up to degree two. -/
theorem decisionDispersion_eq_of_polynomialsAgreeAt_two
    {κ₁ κ₂ : Kernel (FrequencyState Deme Locus Allele) (FrequencyState Deme Locus Allele)}
    [IsMarkovKernel κ₁] [IsMarkovKernel κ₂] {x₁ x₂ : FrequencyState Deme Locus Allele}
    (h : PolynomialsAgreeAt 2 κ₁ κ₂ x₁ x₂) {Score : Type*} [Fintype Score]
    (report : FullHaplotype Locus Allele → Score × Bool) (called : Score → Bool) :
    decisionDispersion κ₁ x₁ report called = decisionDispersion κ₂ x₂ report called := by
  have hterm : ∀ (deme : Deme) (p : MvPolynomial (FullHaplotype Locus Allele) ℝ),
      p.totalDegree ≤ 1 → variance (fun y ↦ eval (stateLaw y deme).mass p) (κ₁ x₁)
        = variance (fun y ↦ eval (stateLaw y deme).mass p) (κ₂ x₂) := fun deme p hp ↦ by
    have hfunction : (fun y : FrequencyState Deme Locus Allele ↦ eval (stateLaw y deme).mass p)
        = ⇑(polynomialFunction (demePolynomial deme p)) :=
      funext fun y ↦ by rw [polynomialFunction_apply, eval_demePolynomial]
    rw [hfunction]
    exact variance_polynomialFunction_eq_of_polynomialsAgreeAt_two_mul (d := 1)
      (PolynomialsAgreeAt.mono (by norm_num) h) ((totalDegree_rename_le _ _).trans hp)
  simp only [decisionDispersion, DecisionDispersion.mk.injEq]
  refine ⟨funext fun deme ↦ funext fun cell ↦ ?_, funext fun deme ↦ ?_,
    funext fun deme ↦ ?_, funext fun deme ↦ funext fun t ↦ ?_⟩
  · simpa only [eval_cellPolynomial] using
      hterm deme (cellPolynomial (confusionReport report called) cell)
        (totalDegree_cellPolynomial_le _ _)
  · simpa only [FiniteReportLaw.binaryCaseMass, FiniteReportLaw.expectation_pushforward,
      eval_expectationPolynomial] using
      hterm deme (expectationPolynomial fun hap ↦ if (report hap).2 then 1 else 0)
        (totalDegree_expectationPolynomial_le _)
  · simpa only [map_add, eval_cellPolynomial, calledMass_pushforward] using
      hterm deme (cellPolynomial (confusionReport report called) (true, true)
          + cellPolynomial (confusionReport report called) (true, false))
        ((totalDegree_add _ _).trans
          (max_le (totalDegree_cellPolynomial_le _ _) (totalDegree_cellPolynomial_le _ _)))
  · simpa only [eval_netBenefitPolynomial] using
      hterm deme (netBenefitPolynomial report called t)
        (totalDegree_netBenefitPolynomial_le report called t)

/-- **Degree four fixes the replicate variance of every deme covariance.**  Two Markov kernels that
agree, from their initial states, on every frequency polynomial of total degree at most four give
the covariance of every two haplotype observables in every deme one replicate variance.

Assumes: agreement up to degree four. -/
theorem covarianceDispersion_eq_of_polynomialsAgreeAt_four
    {κ₁ κ₂ : Kernel (FrequencyState Deme Locus Allele) (FrequencyState Deme Locus Allele)}
    [IsMarkovKernel κ₁] [IsMarkovKernel κ₂] {x₁ x₂ : FrequencyState Deme Locus Allele}
    (h : PolynomialsAgreeAt 4 κ₁ κ₂ x₁ x₂) (deme : Deme)
    (first second : FullHaplotype Locus Allele → ℝ) :
    variance (fun y ↦ (stateLaw y deme).covariance first second) (κ₁ x₁)
      = variance (fun y ↦ (stateLaw y deme).covariance first second) (κ₂ x₂) := by
  have hfunction :
      (fun y : FrequencyState Deme Locus Allele ↦ (stateLaw y deme).covariance first second)
        = ⇑(polynomialFunction (demeCovariancePolynomial deme first second)) :=
    funext fun y ↦ (polynomialFunction_demeCovariancePolynomial deme first second y).symm
  rw [hfunction]
  exact variance_polynomialFunction_eq_of_polynomialsAgreeAt_two_mul (d := 2)
    (PolynomialsAgreeAt.mono (by norm_num) h) (totalDegree_demeCovariancePolynomial_le deme first
      second)

/-- **Chebyshev's bound through the degree-`2d` moments.**  Take two Markov kernels that agree,
from their initial states, on every frequency polynomial of total degree at most `2d`, a frequency
polynomial `p` of total degree at most `d`, and `t > 0`.  Under the first kernel, the probability
that `p` strays from its expectation by at least `t` is at most `(E[p²] - E[p]²) / t²`, with both
expectations taken under the second kernel.

Assumes: agreement up to degree `2d`, `p` of total degree at most `d`, and `0 < t`. -/
theorem deviation_le_of_polynomialsAgreeAt_two_mul
    {κ₁ κ₂ : Kernel (FrequencyState Deme Locus Allele) (FrequencyState Deme Locus Allele)}
    [IsMarkovKernel κ₁] {x₁ x₂ : FrequencyState Deme Locus Allele} {d : ℕ}
    (h : PolynomialsAgreeAt (2 * d) κ₁ κ₂ x₁ x₂) {p : FrequencyPolynomial Deme Locus Allele}
    (hp : p.totalDegree ≤ d) {t : ℝ} (ht : 0 < t) :
    κ₁ x₁ {y | t ≤ |polynomialFunction p y - ∫ z, polynomialFunction p z ∂(κ₂ x₂)|}
      ≤ ENNReal.ofReal ((∫ z, polynomialFunction (p ^ 2) z ∂(κ₂ x₂)
        - (∫ z, polynomialFunction p z ∂(κ₂ x₂)) ^ 2) / t ^ 2) := by
  rw [← h p (hp.trans (by omega)), ← h (p ^ 2) ((totalDegree_pow p 2).trans (by omega)),
    ← variance_polynomialFunction_eq κ₁ x₁ p]
  exact meas_ge_le_variance_div_sq (memLp_two_polynomialFunction κ₁ x₁ p) ht

/-- **Chebyshev's bound for a confusion cell through the degree-2 moments.**  Take two Markov
kernels that agree, from their initial states, on every frequency polynomial of total degree at
most two, and `t > 0`.  Under the first kernel, the probability that the per-population mass of a
cell of the confusion table strays by at least `t` from the expected mass under the second kernel
is at most the replicate variance of that mass under the second kernel over `t²`.

Assumes: agreement up to degree two, and `0 < t`. -/
theorem confusionDeviation_le_of_polynomialsAgreeAt_two
    {κ₁ κ₂ : Kernel (FrequencyState Deme Locus Allele) (FrequencyState Deme Locus Allele)}
    [IsMarkovKernel κ₁] [IsMarkovKernel κ₂] {x₁ x₂ : FrequencyState Deme Locus Allele}
    (h : PolynomialsAgreeAt 2 κ₁ κ₂ x₁ x₂) (deme : Deme) {Score : Type*} [Fintype Score]
    (report : FullHaplotype Locus Allele → Score × Bool) (called : Score → Bool)
    (cell : Bool × Bool) {t : ℝ} (ht : 0 < t) :
    κ₁ x₁ {y | t ≤ |((stateLaw y deme).pushforward (confusionReport report called)).mass cell
        - expectedConfusion κ₂ x₂ deme report called cell|}
      ≤ ENNReal.ofReal ((decisionDispersion κ₂ x₂ report called).table deme cell / t ^ 2) := by
  have hmean : expectedConfusion κ₁ x₁ deme report called cell
      = expectedConfusion κ₂ x₂ deme report called cell := by
    simpa only [expectedConfusion, polynomialFunction_apply, eval_demePolynomial,
      eval_cellPolynomial] using
      h (demePolynomial deme (cellPolynomial (confusionReport report called) cell))
        ((totalDegree_rename_le _ _).trans
          ((totalDegree_cellPolynomial_le _ _).trans (by norm_num)))
  have hvariance := congrFun (congrFun (congrArg DecisionDispersion.table
    (decisionDispersion_eq_of_polynomialsAgreeAt_two h report called)) deme) cell
  have hcontinuous := continuous_pushforwardMass deme (confusionReport report called) cell
  rw [← hmean, ← hvariance]
  exact meas_ge_le_variance_div_sq ((memLp_two_iff_integrable_sq
    (integrable_continuousObservable κ₁ x₁ hcontinuous).aestronglyMeasurable).mpr
    (integrable_continuousObservable κ₁ x₁ (hcontinuous.pow 2))) ht

/-- **An event history and a rate history with equal budget-2 moments give one decision
dispersion.**  If a history of epochs, splits and pulses from `x₁` and a rate history with
continuous dual generator from `x₂` have equal propagated budget-2 moments, every rule on every
report map has the same decision dispersion under both.

Assumes: equal propagated budget-2 moments. -/
theorem decisionDispersion_historyEvent_eq_rateHistory (ℓ₀ : Locus)
    (hap₀ : FullHaplotype Locus Allele)
    (events : List ((NeutralRates Deme Locus Allele × ℝ≥0) ⊕ PulseMatrix Deme))
    {rates : ℝ → NeutralRates Deme Locus Allele} {T : ℝ} (hT : 0 ≤ T)
    (hcontinuous : ∀ capacity : Locus → ℕ,
      ContinuousOn (fun t ↦ dualGenerator (rates t) capacity) (Set.Icc 0 T))
    {x₁ x₂ : FrequencyState Deme Locus Allele}
    (hmoments : historyEventPropagator (fun _ ↦ 2) events *ᵥ budgetMomentFeature (fun _ ↦ 2) x₁
      = rateHistoryDualPropagator rates (fun _ ↦ 2) T *ᵥ budgetMomentFeature (fun _ ↦ 2) x₂)
    {Score : Type*} [Fintype Score] (report : FullHaplotype Locus Allele → Score × Bool)
    (called : Score → Bool) :
    decisionDispersion (historyEventKernel ℓ₀ hap₀ events) x₁ report called
      = decisionDispersion (rateHistoryKernel rates ℓ₀ hap₀ hT hcontinuous) x₂ report called :=
  decisionDispersion_eq_of_polynomialsAgreeAt_two
    (polynomialsAgreeAt_of_hasDualMoments ℓ₀ (hasDualMoments_historyEventKernel ℓ₀ hap₀ events 2)
      (hasDualMoments_rateHistoryKernel hT hcontinuous ℓ₀ hap₀ 2) hmoments)
    report called

end

end Descent.Portability.PortabilityMomentLadderDispersion
