/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.NeutralKernelPanelLikelihood

assert_below Descent.Decision Descent.Program

/-!
# Neutral Markov kernels along a demographic history

NOTE1 §4.2: a changing demographic history composes the corresponding generators in chronological
moment order.  `PartialHaplotypeDualSemigroup.expectedMomentVector_history` proves this for every
expectation family that satisfies the forward moment equation epoch by epoch.  This module proves
it for the process law itself.

A history is a list of epochs, each a neutral model with a nonnegative duration.  The history
kernel runs the neutral Markov kernel of each epoch in chronological order
(`neutralHistoryKernel`), and it is a Markov kernel (`isMarkovKernel_neutralHistoryKernel`).  For
every budget, its expected configuration moments are the chronological product of the epoch dual
propagators applied to the initial moments, `∫ H_ξ dK_history(x, ·) = (historyPropagator H(x))_ξ`
(`integral_momentPolynomial_neutralHistoryKernel`).  So the expected compiled report of an
independently sampled panel at the end of the history is the sum over genotypes of the readout
times the seed coordinate of the history propagator applied to the initial moments
(`integral_panelReport_neutralHistoryKernel`).

Scope.  The epochs are constant-rate neutral models.  Splits and admixture pulses are not composed
into the kernel here; their finite substitution kernels act on moment vectors in
`PartialHaplotypePulseKernel`.

## Empirical status

None.  The bodies here are integrals of polynomials against compositions of Markov kernels and
products of matrix exponentials of supplied rates, so no measurement can bear on them.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.NeutralHistoryKernel

open MeasureTheory ProbabilityTheory MvPolynomial Descent.Coalescent PartialHaplotypeCarrier
  PartialHaplotypeDualGenerator PartialHaplotypeDualSemigroup NeutralFellerGenerator
  NeutralPolynomialSemigroup PartialHaplotypeMicroscopicApproximation
  PartialHaplotypePanelLikelihood NeutralMicroscopicEulerLimit NeutralKernelPanelLikelihood
open scoped Matrix NNReal

noncomputable section

variable {Deme Locus Sample Report : Type*} {Allele : Locus → Type*}
variable [Fintype Deme] [DecidableEq Deme] [Fintype Locus] [DecidableEq Locus]
  [∀ ℓ, Fintype (Allele ℓ)] [∀ ℓ, DecidableEq (Allele ℓ)]

/-- **The neutral history kernel.**  The neutral Markov kernels of the epochs of a history, run in
chronological order: first the head epoch, then the rest of the history. -/
def neutralHistoryKernel (ℓ₀ : Locus) (hap₀ : FullHaplotype Locus Allele) :
    List (NeutralRates Deme Locus Allele × ℝ≥0) →
      Kernel (FrequencyState Deme Locus Allele) (FrequencyState Deme Locus Allele)
  | [] => Kernel.id
  | epoch :: rest =>
      neutralHistoryKernel ℓ₀ hap₀ rest ∘ₖ neutralMarkovKernel epoch.1 ℓ₀ hap₀ epoch.2

/-- The history kernel is a Markov kernel. -/
theorem isMarkovKernel_neutralHistoryKernel (ℓ₀ : Locus) (hap₀ : FullHaplotype Locus Allele) :
    ∀ epochs : List (NeutralRates Deme Locus Allele × ℝ≥0),
      IsMarkovKernel (neutralHistoryKernel ℓ₀ hap₀ epochs)
  | [] => by
    rw [neutralHistoryKernel]
    infer_instance
  | epoch :: rest => by
    haveI := isMarkovKernel_neutralHistoryKernel ℓ₀ hap₀ rest
    haveI := isMarkovKernel_neutralMarkovKernel epoch.1 ℓ₀ hap₀ epoch.2
    rw [neutralHistoryKernel]
    infer_instance

/-- **NOTE1 (20) along a history, under the process law.**  For every budget, the expected
configuration moments under the history kernel are the chronological product of the epoch dual
propagators applied to the moments of the initial state. -/
theorem integral_momentPolynomial_neutralHistoryKernel (ℓ₀ : Locus)
    (hap₀ : FullHaplotype Locus Allele) (capacity : Locus → ℕ) :
    ∀ (epochs : List (NeutralRates Deme Locus Allele × ℝ≥0))
      (x : FrequencyState Deme Locus Allele) (ξ : BudgetConfiguration Deme Locus Allele capacity),
      ∫ y, polynomialFunction (momentPolynomial ξ.1) y ∂(neutralHistoryKernel ℓ₀ hap₀ epochs x)
        = (historyPropagator capacity (epochs.map fun epoch ↦ (epoch.1, (epoch.2 : ℝ)))
            *ᵥ budgetMomentFeature capacity x) ξ
  | [], x, ξ => by
    rw [neutralHistoryKernel, Kernel.id_apply, integral_dirac' _ _
      (polynomialFunction (momentPolynomial ξ.1)).continuous.stronglyMeasurable]
    simp only [List.map_nil, historyPropagator, Matrix.one_mulVec]
    rfl
  | epoch :: rest, x, ξ => by
    haveI := isMarkovKernel_neutralHistoryKernel ℓ₀ hap₀ rest
    haveI := isMarkovKernel_neutralMarkovKernel epoch.1 ℓ₀ hap₀ epoch.2
    have hint : ∀ η : BudgetConfiguration Deme Locus Allele capacity,
        Integrable (fun y ↦ polynomialFunction (momentPolynomial η.1) y)
          (neutralMarkovKernel epoch.1 ℓ₀ hap₀ epoch.2 x) := fun η ↦
      (BoundedContinuousFunction.mkOfCompact
        (polynomialFunction (momentPolynomial η.1))).integrable _
    have hcomp : Integrable (fun y ↦ polynomialFunction (momentPolynomial ξ.1) y)
        ((neutralHistoryKernel ℓ₀ hap₀ rest ∘ₖ neutralMarkovKernel epoch.1 ℓ₀ hap₀ epoch.2) x) :=
      (BoundedContinuousFunction.mkOfCompact
        (polynomialFunction (momentPolynomial ξ.1))).integrable _
    rw [neutralHistoryKernel, Kernel.integral_comp hcomp]
    calc ∫ y, ∫ z, polynomialFunction (momentPolynomial ξ.1) z
            ∂(neutralHistoryKernel ℓ₀ hap₀ rest y) ∂(neutralMarkovKernel epoch.1 ℓ₀ hap₀ epoch.2 x)
        = ∫ y, ∑ η, historyPropagator capacity (rest.map fun epoch ↦ (epoch.1, (epoch.2 : ℝ))) ξ η
            * polynomialFunction (momentPolynomial η.1) y
            ∂(neutralMarkovKernel epoch.1 ℓ₀ hap₀ epoch.2 x) := by
          congr 1
          funext y
          rw [integral_momentPolynomial_neutralHistoryKernel ℓ₀ hap₀ capacity rest y ξ]
          simp only [Matrix.mulVec, dotProduct]
          rfl
      _ = ∑ η, historyPropagator capacity (rest.map fun epoch ↦ (epoch.1, (epoch.2 : ℝ))) ξ η
            * ∫ y, polynomialFunction (momentPolynomial η.1) y
              ∂(neutralMarkovKernel epoch.1 ℓ₀ hap₀ epoch.2 x) := by
          rw [integral_finset_sum Finset.univ fun η _ ↦ (hint η).const_mul
            (historyPropagator capacity (rest.map fun epoch ↦ (epoch.1, (epoch.2 : ℝ))) ξ η)]
          simp only [integral_const_mul]
      _ = _ := by
          simp only [integral_momentPolynomial_neutralMarkovKernel, List.map_cons,
            historyPropagator, ← Matrix.mulVec_mulVec]
          simp only [Matrix.mulVec, dotProduct]

variable [Fintype Sample] [DecidableEq Sample] [Fintype Report]

/-- **NOTE1 (20) with (22) along a history, under the process law.**  The expected compiled report
of an independently sampled panel at the end of a history, started at a frequency state, is the
sum over panel genotypes of the conditional readout times the seed coordinate of the history
propagator applied to the initial moments. -/
theorem integral_panelReport_neutralHistoryKernel (ℓ₀ : Locus)
    (hap₀ : FullHaplotype Locus Allele) (deme : Sample → Deme)
    (report : (Sample → FullHaplotype Locus Allele) → FiniteReportLaw Report)
    (metric : Report → ℝ) (epochs : List (NeutralRates Deme Locus Allele × ℝ≥0))
    (x0 : FrequencyState Deme Locus Allele) :
    ∫ y, ((FiniteGeneticTransition.piLaw fun draw ↦ stateLaw y (deme draw)).bind
        report).expectation metric ∂(neutralHistoryKernel ℓ₀ hap₀ epochs x0)
      = ∑ genotype : Sample → FullHaplotype Locus Allele,
          (report genotype).expectation metric *
            (historyPropagator (fun _ ↦ Fintype.card Sample)
                (epochs.map fun epoch ↦ (epoch.1, (epoch.2 : ℝ)))
              *ᵥ budgetMomentFeature (fun _ ↦ Fintype.card Sample) x0)
              (seedState deme genotype ℓ₀) := by
  haveI := isMarkovKernel_neutralHistoryKernel ℓ₀ hap₀ epochs
  have hint : ∀ genotype : Sample → FullHaplotype Locus Allele,
      Integrable (fun y ↦ (report genotype).expectation metric
        * polynomialFunction (momentPolynomial (seedState deme genotype ℓ₀).1) y)
        (neutralHistoryKernel ℓ₀ hap₀ epochs x0) := fun genotype ↦
    Integrable.const_mul ((BoundedContinuousFunction.mkOfCompact
      (polynomialFunction (momentPolynomial (seedState deme genotype ℓ₀).1))).integrable _) _
  calc ∫ y, ((FiniteGeneticTransition.piLaw fun draw ↦ stateLaw y (deme draw)).bind
          report).expectation metric ∂(neutralHistoryKernel ℓ₀ hap₀ epochs x0)
      = ∫ y, ∑ genotype : Sample → FullHaplotype Locus Allele,
          (report genotype).expectation metric
            * polynomialFunction (momentPolynomial (seedState deme genotype ℓ₀).1) y
          ∂(neutralHistoryKernel ℓ₀ hap₀ epochs x0) := by
        congr 1
        funext y
        exact panelReport_eq_sum_seedMoment deme report metric ℓ₀ y
    _ = ∑ genotype : Sample → FullHaplotype Locus Allele,
          ∫ y, (report genotype).expectation metric
            * polynomialFunction (momentPolynomial (seedState deme genotype ℓ₀).1) y
          ∂(neutralHistoryKernel ℓ₀ hap₀ epochs x0) :=
        integral_finset_sum Finset.univ fun genotype _ ↦ hint genotype
    _ = _ := by
        refine Finset.sum_congr rfl fun genotype _ ↦ ?_
        rw [integral_const_mul, integral_momentPolynomial_neutralHistoryKernel]

end

end Descent.Portability.NeutralHistoryKernel
