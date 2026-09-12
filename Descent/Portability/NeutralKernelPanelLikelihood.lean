/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.NeutralMicroscopicEulerLimit
import Descent.Portability.PartialHaplotypePanelLikelihood

assert_below Descent.Decision Descent.Program

/-!
# Exact panel likelihoods under the neutral Markov kernels

NOTE1 §4.2 states that (20) gives the exact sampled-genotype probabilities at the full-panel seed
configurations.  `PartialHaplotypeRealizedPanel` proves this for a realized expectation family
built at one fixed budget.  The neutral Markov kernels of `NeutralMicroscopicEulerLimit` are one
process for every budget, and the limit in law of the microscopic chain.  This module proves (20)
and (22) under them.

For every budget, the expected configuration moment of a budget-respecting configuration under
the neutral kernel at time `t` is the coordinate of the dual propagator applied to the initial
moments, `∫ H_ξ dK_t(x, ·) = (e^{tQ} H(x))_ξ` (`integral_momentPolynomial_neutralMarkovKernel`).
At a state, the compiled report of an independently sampled panel is the sum over genotypes of
the readout times the seed moment (`panelReport_eq_sum_seedMoment`).  So its expectation under
the kernel is the sum over genotypes of the readout times the seed coordinate of `e^{tQ} H(x₀)`
(`integral_panelReport_neutralMarkovKernel`).

Scope.  A locus `ℓ₀` and a haplotype `hap₀` are explicit arguments, as in
`NeutralPolynomialSemigroup`.

## Empirical status

None.  The bodies here are finite sums of supplied readouts against integrals of polynomials and
a matrix exponential of supplied rates, so no measurement can bear on them.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.NeutralKernelPanelLikelihood

open MeasureTheory ProbabilityTheory MvPolynomial Descent.Coalescent Descent.Foundations
  PartialHaplotypeCarrier PartialHaplotypeDualGenerator PartialHaplotypeDualSemigroup
  NeutralFellerGenerator NeutralPolynomialSemigroup PartialHaplotypeMicroscopicApproximation
  PartialHaplotypePanelLikelihood NeutralMicroscopicEulerLimit
open scoped Matrix NNReal

noncomputable section

variable {Deme Locus Sample Report : Type*} {Allele : Locus → Type*}
variable [Fintype Deme] [DecidableEq Deme] [Fintype Locus] [DecidableEq Locus]
  [∀ ℓ, Fintype (Allele ℓ)] [∀ ℓ, DecidableEq (Allele ℓ)]
  [Fintype Sample] [DecidableEq Sample] [Fintype Report]

/-- **NOTE1 (20) under the neutral Markov kernels.**  For every budget, the expected
configuration moment of a budget-respecting configuration under the neutral kernel at time `t` is
the coordinate of the dual propagator applied to the moments of the initial state. -/
theorem integral_momentPolynomial_neutralMarkovKernel (rates : NeutralRates Deme Locus Allele)
    (ℓ₀ : Locus) (hap₀ : FullHaplotype Locus Allele) (capacity : Locus → ℕ) (t : ℝ≥0)
    (x : FrequencyState Deme Locus Allele) (ξ : BudgetConfiguration Deme Locus Allele capacity) :
    ∫ y, polynomialFunction (momentPolynomial ξ.1) y ∂(neutralMarkovKernel rates ℓ₀ hap₀ t x)
      = (matrixExponential (dualGenerator rates capacity) t
          *ᵥ budgetMomentFeature capacity x) ξ :=
  (integral_neutralMarkovKernel_polynomial rates ℓ₀ hap₀ t x
    ⟨polynomialFunction (momentPolynomial ξ.1), polynomialFunction_mem _⟩).trans
    (neutralPolynomialSemigroup_momentPolynomial rates ℓ₀ hap₀ capacity t ξ x)

/-- At a state, the compiled report of an independently sampled panel is the sum over panel
genotypes of the conditional readout times the seed configuration moment. -/
theorem panelReport_eq_sum_seedMoment (deme : Sample → Deme)
    (report : (Sample → FullHaplotype Locus Allele) → FiniteReportLaw Report)
    (metric : Report → ℝ) (ℓ₀ : Locus) (y : FrequencyState Deme Locus Allele) :
    ((FiniteGeneticTransition.piLaw fun draw ↦ stateLaw y (deme draw)).bind report).expectation
        metric
      = ∑ genotype : Sample → FullHaplotype Locus Allele, (report genotype).expectation metric
          * polynomialFunction (momentPolynomial (seedState deme genotype ℓ₀).1) y := by
  rw [ConditionalReportCompilation.panel_compiled_expectation_eq_frequency_polynomial deme
    (stateLaw y) report metric]
  refine Finset.sum_congr rfl fun genotype _ ↦ ?_
  have hmoment : polynomialFunction (momentPolynomial (seedState deme genotype ℓ₀).1) y
      = configurationMoment (stateLaw y) (seedConfiguration deme genotype ℓ₀) :=
    eval_momentPolynomial (stateLaw y) _
  rw [hmoment, configurationMoment_seedConfiguration]
  exact mul_comm _ _

/-- **NOTE1 (20) with (22) under the neutral Markov kernels.**  Started at a frequency state, the
expected compiled report of an independently sampled panel under the neutral kernel at time `t`
is the sum over panel genotypes of the conditional readout times the seed coordinate of the dual
propagator applied to the initial moments. -/
theorem integral_panelReport_neutralMarkovKernel (rates : NeutralRates Deme Locus Allele)
    (ℓ₀ : Locus) (hap₀ : FullHaplotype Locus Allele) (deme : Sample → Deme)
    (report : (Sample → FullHaplotype Locus Allele) → FiniteReportLaw Report)
    (metric : Report → ℝ) (t : ℝ≥0) (x0 : FrequencyState Deme Locus Allele) :
    ∫ y, ((FiniteGeneticTransition.piLaw fun draw ↦ stateLaw y (deme draw)).bind
        report).expectation metric ∂(neutralMarkovKernel rates ℓ₀ hap₀ t x0)
      = ∑ genotype : Sample → FullHaplotype Locus Allele,
          (report genotype).expectation metric *
            (matrixExponential (dualGenerator rates (fun _ ↦ Fintype.card Sample)) t
              *ᵥ budgetMomentFeature (fun _ ↦ Fintype.card Sample) x0)
              (seedState deme genotype ℓ₀) := by
  haveI := isMarkovKernel_neutralMarkovKernel rates ℓ₀ hap₀ t
  have hint : ∀ genotype : Sample → FullHaplotype Locus Allele,
      Integrable (fun y ↦ (report genotype).expectation metric
        * polynomialFunction (momentPolynomial (seedState deme genotype ℓ₀).1) y)
        (neutralMarkovKernel rates ℓ₀ hap₀ t x0) := fun genotype ↦
    Integrable.const_mul ((BoundedContinuousFunction.mkOfCompact
      (polynomialFunction (momentPolynomial (seedState deme genotype ℓ₀).1))).integrable _) _
  calc ∫ y, ((FiniteGeneticTransition.piLaw fun draw ↦ stateLaw y (deme draw)).bind
          report).expectation metric ∂(neutralMarkovKernel rates ℓ₀ hap₀ t x0)
      = ∫ y, ∑ genotype : Sample → FullHaplotype Locus Allele,
          (report genotype).expectation metric
            * polynomialFunction (momentPolynomial (seedState deme genotype ℓ₀).1) y
          ∂(neutralMarkovKernel rates ℓ₀ hap₀ t x0) := by
        congr 1
        funext y
        exact panelReport_eq_sum_seedMoment deme report metric ℓ₀ y
    _ = ∑ genotype : Sample → FullHaplotype Locus Allele,
          ∫ y, (report genotype).expectation metric
            * polynomialFunction (momentPolynomial (seedState deme genotype ℓ₀).1) y
          ∂(neutralMarkovKernel rates ℓ₀ hap₀ t x0) :=
        integral_finset_sum Finset.univ fun genotype _ ↦ hint genotype
    _ = _ := by
        refine Finset.sum_congr rfl fun genotype _ ↦ ?_
        rw [integral_const_mul, integral_momentPolynomial_neutralMarkovKernel]

end

end Descent.Portability.NeutralKernelPanelLikelihood
