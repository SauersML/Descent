/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.PortabilityMomentLadder
import Descent.Portability.EndToEndBrierLaw

assert_below Descent.Decision Descent.Program

/-!
# The Brier rung of the moment ladder under any process law

`EndToEndBrierLaw` writes the expected repaired Brier loss of a finite score alphabet with a binary
outcome under every Markov kernel as the expected case probability minus, for every score group,
the series of expectations of `a_s² (1 - q_s)ᵏ` (`EndToEndBrierLaw.expectedRepairedBrier_eq_tsum`).
This module shows that the repaired Brier loss, like the squared correlation, the AUC and the
entropies, depends on the process law only through polynomial expectations.

The terms.  The case probability is a frequency polynomial of degree one
(`ReplicaMetricInstances.expectationPolynomial`), and the order-`k` term of each score group is the
polynomial `brierTermPolynomial` of degree at most `k + 2`
(`EndToEndBrierLaw.eval_brierTermPolynomial`, `totalDegree_brierTermPolynomial_le`).

The rung.  Two Markov kernels that agree on the expectation of every frequency polynomial give
every report map, in every deme, the same expected repaired Brier loss
(`expectedRepairedBrier_eq_of_polynomialsAgreeAt_all`).  A history of epochs, splits and pulses and
a continuous rate history with equal propagated moments at every budget therefore agree on it
(`expectedRepairedBrier_historyEvent_eq_rateHistory`).

Significance.  The clinical calibration loss of a risk score, averaged over the populations a
demography produces, is fixed by the moment sequence of the process law, whichever kind of process
carries it.

Scope.  Agreement at every budget is the hypothesis.  The calibration error of `EndToEndBrierLaw`
is an absolute value of linear residuals, not a limit of polynomial expectations, and is not
treated here.

## Empirical status

None.  The bodies here are termwise comparisons of series of polynomial integrals against Markov
kernels, so no measurement can bear on them.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.PortabilityMomentLadderBrier

open MeasureTheory ProbabilityTheory MvPolynomial Descent.Coalescent PartialHaplotypeCarrier
  PartialHaplotypeDualGenerator PartialHaplotypeDualSemigroup NeutralFellerGenerator
  NeutralPolynomialSemigroup PartialHaplotypeMicroscopicApproximation PartialHaplotypePulseKernel
  NeutralPulseHistoryKernel NeutralRateHistoryRealization NeutralRateHistoryKernel
  ReplicaMetricInstances EndToEndPortabilityLaw EndToEndDiscriminationLaw EndToEndBrierLaw
  PortabilityMomentLadder
open scoped Matrix NNReal

noncomputable section

variable {Deme Locus : Type*} {Allele : Locus → Type*}
variable [Fintype Deme] [DecidableEq Deme] [Fintype Locus] [DecidableEq Locus]
  [∀ ℓ, Fintype (Allele ℓ)] [∀ ℓ, DecidableEq (Allele ℓ)]

attribute [local instance] isMarkovKernel_historyEventKernel isMarkovKernel_rateHistoryKernel

/-- **Every degree fixes the repaired Brier loss under any process law.**  Two Markov kernels that
agree, from their initial states, on the expectation of every frequency polynomial give every report
map of a score and a binary outcome, in every deme, the same expected repaired Brier loss.

Assumes: agreement at every degree. -/
theorem expectedRepairedBrier_eq_of_polynomialsAgreeAt_all
    {κ₁ κ₂ : Kernel (FrequencyState Deme Locus Allele) (FrequencyState Deme Locus Allele)}
    [IsMarkovKernel κ₁] [IsMarkovKernel κ₂] {x₁ x₂ : FrequencyState Deme Locus Allele}
    (h : ∀ n : ℕ, PolynomialsAgreeAt n κ₁ κ₂ x₁ x₂) (deme : Deme)
    {Score : Type*} [Fintype Score] [DecidableEq Score]
    (report : FullHaplotype Locus Allele → Score × Bool) :
    expectedRepairedBrier κ₁ x₁ deme report = expectedRepairedBrier κ₂ x₂ deme report := by
  have hterm : ∀ (p : MvPolynomial (FullHaplotype Locus Allele) ℝ) (d : ℕ), p.totalDegree ≤ d →
      ∫ y, eval (stateLaw y deme).mass p ∂(κ₁ x₁)
        = ∫ y, eval (stateLaw y deme).mass p ∂(κ₂ x₂) := by
    intro p d hp
    simpa only [polynomialFunction_apply, eval_demePolynomial] using
      h d (demePolynomial deme p) ((totalDegree_rename_le _ _).trans hp)
  rw [expectedRepairedBrier_eq_tsum κ₁ x₁ deme report,
    expectedRepairedBrier_eq_tsum κ₂ x₂ deme report]
  congr 1
  · simpa only [FiniteReportLaw.expectation_pushforward, eval_expectationPolynomial] using
      hterm (expectationPolynomial fun hap ↦ ChronologyReportLaw.alleleValue (report hap).2) 1
        (totalDegree_expectationPolynomial_le _)
  · refine Finset.sum_congr rfl fun group _ ↦ tsum_congr fun k ↦ ?_
    simpa only [eval_brierTermPolynomial] using
      hterm (brierTermPolynomial report group k) (k + 2)
        (totalDegree_brierTermPolynomial_le report group k)

/-- **An event history and a rate history with equal moment sequences have one repaired Brier
loss.**  If a history of epochs, splits and pulses from `x₁` and a rate history with continuous dual
generator from `x₂` have equal propagated moments at every budget, every report map has the same
expected repaired Brier loss in every deme under both.

Assumes: equal propagated moments at every budget. -/
theorem expectedRepairedBrier_historyEvent_eq_rateHistory (ℓ₀ : Locus)
    (hap₀ : FullHaplotype Locus Allele)
    (events : List ((NeutralRates Deme Locus Allele × ℝ≥0) ⊕ PulseMatrix Deme))
    {rates : ℝ → NeutralRates Deme Locus Allele} {T : ℝ} (hT : 0 ≤ T)
    (hcontinuous : ∀ capacity : Locus → ℕ,
      ContinuousOn (fun t ↦ dualGenerator (rates t) capacity) (Set.Icc 0 T))
    {x₁ x₂ : FrequencyState Deme Locus Allele}
    (hmoments : ∀ n : ℕ,
      historyEventPropagator (fun _ ↦ n) events *ᵥ budgetMomentFeature (fun _ ↦ n) x₁
        = rateHistoryDualPropagator rates (fun _ ↦ n) T *ᵥ budgetMomentFeature (fun _ ↦ n) x₂)
    (deme : Deme) {Score : Type*} [Fintype Score] [DecidableEq Score]
    (report : FullHaplotype Locus Allele → Score × Bool) :
    expectedRepairedBrier (historyEventKernel ℓ₀ hap₀ events) x₁ deme report
      = expectedRepairedBrier (rateHistoryKernel rates ℓ₀ hap₀ hT hcontinuous) x₂ deme report :=
  expectedRepairedBrier_eq_of_polynomialsAgreeAt_all
    (fun n ↦ polynomialsAgreeAt_of_hasDualMoments ℓ₀
      (hasDualMoments_historyEventKernel ℓ₀ hap₀ events n)
      (hasDualMoments_rateHistoryKernel hT hcontinuous ℓ₀ hap₀ n) (hmoments n))
    deme report

end

end Descent.Portability.PortabilityMomentLadderBrier
