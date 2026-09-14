/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.PortabilityMomentLadder
import Descent.Portability.EndToEndDeploymentLaw

assert_below Descent.Decision Descent.Program

/-!
# The deployment rung of the moment ladder: the accuracy calculator under any process law

`EndToEndDeploymentLaw` compiles a demography, a training procedure, a phenotype architecture and an
environment into the deployed `R²`, calibration slope, intercept and mean squared error of a score.
It proves that two histories of epochs with equal propagated budget-2 moments give equal reports
(`EndToEndDeploymentLaw.transferReport_eq_of_moments_eq`).  This module lifts that to every process
law with dual moments.

The moments.  The expected deployment moments of a deme (`expectedDemeMoments`) are integrals of the
tag and causal covariances, of degree two, and of the tag and causal means, of degree one.  So two
Markov kernels that agree on every frequency polynomial of total degree at most two give every deme
the same expected deployment moments (`expectedDemeMoments_eq_of_polynomialsAgreeAt_two`).

The report.  Take weights trained by ridge regression with any penalty in a source deme and
deployed in a target deme, under any architecture and environment of the two demes.  They have one
deployment report under both kernels (`transferReport_eq_of_polynomialsAgreeAt_two`).  In
particular a history of epochs, splits and pulses and a continuous rate history whose propagated
budget-2 moments agree give every ridge-trained score the same deployed `R²`, slope, intercept and
mean squared error (`transferReport_historyEvent_eq_rateHistory`).  One rung, budget four, fixes
both the portability report of `PortabilityMomentLadder` and the deployment report
(`reports_eq_of_polynomialsAgreeAt_four`).

Significance.  A deployer's calculator, demography in and deployed accuracy out, reads the process
law at budget two and nowhere else.  A continuous demography and a piecewise one that share their
propagated second moments cannot be told apart by any second-moment metric of any ridge-trained
score.

Scope.  The report gives the metrics of the expected second moments, the ratio-of-expectations
query.  Training is population ridge regression on those moments.  The environment enters through
its moments per deme, supplied rather than generated.

## Empirical status

None.  The bodies here are compositions of polynomial integrals against Markov kernels, so no
measurement can bear on them.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.PortabilityMomentLadderDeployment

open MeasureTheory ProbabilityTheory MvPolynomial Descent.Coalescent PartialHaplotypeCarrier
  PartialHaplotypeDualGenerator PartialHaplotypeDualSemigroup NeutralFellerGenerator
  NeutralPolynomialSemigroup PartialHaplotypeMicroscopicApproximation PartialHaplotypePulseKernel
  NeutralPulseHistoryKernel NeutralRateHistoryRealization NeutralRateHistoryKernel
  ReplicaMetricInstances EndToEndPortabilityLaw EndToEndCalibrationLaw EndToEndDiscriminationLaw
  EndToEndDeploymentLaw PortabilityMomentLadder
open scoped Matrix NNReal

noncomputable section

variable {Deme Locus : Type*} {Allele : Locus → Type*}
variable [Fintype Deme] [DecidableEq Deme] [Fintype Locus] [DecidableEq Locus]
  [∀ ℓ, Fintype (Allele ℓ)] [∀ ℓ, DecidableEq (Allele ℓ)]

attribute [local instance] isMarkovKernel_historyEventKernel isMarkovKernel_rateHistoryKernel

variable {J L : Type*}

/-- **Budget two fixes the expected deployment moments under any process law.**  Two Markov kernels
that agree, from their initial states, on every frequency polynomial of total degree at most two
give every deme the same expected tag, tag–causal and causal covariances and means.

Assumes: agreement up to degree two. -/
theorem expectedDemeMoments_eq_of_polynomialsAgreeAt_two
    {κ₁ κ₂ : Kernel (FrequencyState Deme Locus Allele) (FrequencyState Deme Locus Allele)}
    {x₁ x₂ : FrequencyState Deme Locus Allele} (h : PolynomialsAgreeAt 2 κ₁ κ₂ x₁ x₂)
    (deme : Deme) (X : FullHaplotype Locus Allele → J → ℝ)
    (C : FullHaplotype Locus Allele → L → ℝ) :
    expectedDemeMoments κ₁ x₁ deme X C = expectedDemeMoments κ₂ x₂ deme X C := by
  have hcovariance : ∀ first second : FullHaplotype Locus Allele → ℝ,
      ∫ y, (stateLaw y deme).covariance first second ∂(κ₁ x₁)
        = ∫ y, (stateLaw y deme).covariance first second ∂(κ₂ x₂) := fun first second ↦ by
    simpa only [polynomialFunction_demeCovariancePolynomial] using
      h (demeCovariancePolynomial deme first second)
        (totalDegree_demeCovariancePolynomial_le deme first second)
  have hmean : ∀ value : FullHaplotype Locus Allele → ℝ,
      ∫ y, (stateLaw y deme).expectation value ∂(κ₁ x₁)
        = ∫ y, (stateLaw y deme).expectation value ∂(κ₂ x₂) := fun value ↦ by
    simpa only [polynomialFunction_demeMeanPolynomial] using
      h (demeMeanPolynomial deme value)
        ((totalDegree_demeMeanPolynomial_le deme value).trans (by norm_num))
  simp only [expectedDemeMoments, DemeMoments.mk.injEq]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · ext i k
    simp only [Matrix.of_apply]
    exact hcovariance _ _
  · ext i l
    simp only [Matrix.of_apply]
    exact hcovariance _ _
  · ext l l'
    simp only [Matrix.of_apply]
    exact hcovariance _ _
  · funext i
    exact hmean _
  · funext l
    exact hmean _

variable [Fintype J] [DecidableEq J] [Fintype L] [DecidableEq L]

/-- **Budget two fixes the deployed report of every ridge-trained score under any process law.**
Two Markov kernels that agree up to degree two give weights trained with any penalty in a source
deme, deployed in a target deme under any architectures and environments, the same `R²`,
calibration slope, intercept and mean squared error.

Assumes: agreement up to degree two. -/
theorem transferReport_eq_of_polynomialsAgreeAt_two
    {κ₁ κ₂ : Kernel (FrequencyState Deme Locus Allele) (FrequencyState Deme Locus Allele)}
    {x₁ x₂ : FrequencyState Deme Locus Allele} (h : PolynomialsAgreeAt 2 κ₁ κ₂ x₁ x₂)
    (source target : Deme) (X : FullHaplotype Locus Allele → J → ℝ)
    (C : FullHaplotype Locus Allele → L → ℝ) (sourceArch targetArch : DemeArchitecture J L)
    (penalty : ℝ) :
    (expectedDemeMoments κ₁ x₁ target X C).report targetArch
        (trainedWeights (expectedDemeMoments κ₁ x₁ source X C) sourceArch penalty)
      = (expectedDemeMoments κ₂ x₂ target X C).report targetArch
          (trainedWeights (expectedDemeMoments κ₂ x₂ source X C) sourceArch penalty) := by
  rw [expectedDemeMoments_eq_of_polynomialsAgreeAt_two h target X C,
    expectedDemeMoments_eq_of_polynomialsAgreeAt_two h source X C]

/-- **An event history and a rate history with equal budget-2 moments deploy alike.**  If a history
of epochs, splits and pulses from `x₁` and a rate history with continuous dual generator from `x₂`
have equal propagated budget-2 moments, every ridge-trained score has the same deployment report
under both.

Assumes: equal propagated budget-2 moments. -/
theorem transferReport_historyEvent_eq_rateHistory (ℓ₀ : Locus)
    (hap₀ : FullHaplotype Locus Allele)
    (events : List ((NeutralRates Deme Locus Allele × ℝ≥0) ⊕ PulseMatrix Deme))
    {rates : ℝ → NeutralRates Deme Locus Allele} {T : ℝ} (hT : 0 ≤ T)
    (hcontinuous : ∀ capacity : Locus → ℕ,
      ContinuousOn (fun t ↦ dualGenerator (rates t) capacity) (Set.Icc 0 T))
    {x₁ x₂ : FrequencyState Deme Locus Allele}
    (hmoments : historyEventPropagator (fun _ ↦ 2) events *ᵥ budgetMomentFeature (fun _ ↦ 2) x₁
      = rateHistoryDualPropagator rates (fun _ ↦ 2) T *ᵥ budgetMomentFeature (fun _ ↦ 2) x₂)
    (source target : Deme) (X : FullHaplotype Locus Allele → J → ℝ)
    (C : FullHaplotype Locus Allele → L → ℝ) (sourceArch targetArch : DemeArchitecture J L)
    (penalty : ℝ) :
    (expectedDemeMoments (historyEventKernel ℓ₀ hap₀ events) x₁ target X C).report targetArch
        (trainedWeights (expectedDemeMoments (historyEventKernel ℓ₀ hap₀ events) x₁ source X C)
          sourceArch penalty)
      = (expectedDemeMoments (rateHistoryKernel rates ℓ₀ hap₀ hT hcontinuous) x₂ target X C).report
          targetArch
          (trainedWeights
            (expectedDemeMoments (rateHistoryKernel rates ℓ₀ hap₀ hT hcontinuous) x₂ source X C)
            sourceArch penalty) :=
  transferReport_eq_of_polynomialsAgreeAt_two
    (polynomialsAgreeAt_of_hasDualMoments ℓ₀ (hasDualMoments_historyEventKernel ℓ₀ hap₀ events 2)
      (hasDualMoments_rateHistoryKernel hT hcontinuous ℓ₀ hap₀ 2) hmoments)
    source target X C sourceArch targetArch penalty

/-- **One rung fixes both reports.**  Two Markov kernels that agree up to degree four have the same
portability report of every score, outcome and binary endpoint, and the same deployment report of
every ridge-trained score.

Assumes: agreement up to degree four. -/
theorem reports_eq_of_polynomialsAgreeAt_four
    {κ₁ κ₂ : Kernel (FrequencyState Deme Locus Allele) (FrequencyState Deme Locus Allele)}
    [IsMarkovKernel κ₁] [IsMarkovKernel κ₂] {x₁ x₂ : FrequencyState Deme Locus Allele}
    (h : PolynomialsAgreeAt 4 κ₁ κ₂ x₁ x₂) (source target : Deme)
    (score outcome : FullHaplotype Locus Allele → ℝ) (case : FullHaplotype Locus Allele → Bool)
    (X : FullHaplotype Locus Allele → J → ℝ) (C : FullHaplotype Locus Allele → L → ℝ)
    (sourceArch targetArch : DemeArchitecture J L) (penalty : ℝ) :
    portabilityReport κ₁ x₁ source target score outcome case
        = portabilityReport κ₂ x₂ source target score outcome case
      ∧ (expectedDemeMoments κ₁ x₁ target X C).report targetArch
          (trainedWeights (expectedDemeMoments κ₁ x₁ source X C) sourceArch penalty)
        = (expectedDemeMoments κ₂ x₂ target X C).report targetArch
          (trainedWeights (expectedDemeMoments κ₂ x₂ source X C) sourceArch penalty) :=
  ⟨portabilityReport_eq_of_polynomialsAgreeAt_four h source target score outcome case,
    transferReport_eq_of_polynomialsAgreeAt_two (h.mono (by norm_num : 2 ≤ 4)) source target X C
      sourceArch targetArch penalty⟩

end

end Descent.Portability.PortabilityMomentLadderDeployment
