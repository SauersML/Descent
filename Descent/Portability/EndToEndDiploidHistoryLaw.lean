/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.EndToEndDiploidLaw

assert_below Descent.Decision Descent.Program

/-!
# The diploid portability law for every genotype observable

`EndToEndDiploidLaw` carries additive diploid scores and outcomes along a history at budget four,
and shows with a recessive outcome that the haploid law does not transfer under dominance.  This
module carries every observable of the gamete pair at budget eight, including dominance and
interaction between the two gametes.

Genotype polynomials.  At inbreeding coefficient `F` the expectation of a gamete-pair observable
`φ` is `1 - F` times the corpus pair polynomial of `φ` plus `F` times the expectation polynomial of
its diagonal (`genotypeExpectationPolynomial`, `eval_genotypeExpectationPolynomial`).  It has total
degree at most two.  The covariance polynomial has degree at most four, and the correlation
numerator `16 C²` and denominator `16 V_φ V_ψ` have degree at most eight
(`totalDegree_genotypeNumeratorPolynomial_le`, `totalDegree_genotypeDenominatorPolynomial_le`).
At the haplotype law of a deme each evaluates to the metric of the deme's gamete-pair law
(`eval_genotypeNumeratorPolynomial`, `polynomialFunction_diploidNumeratorPolynomial`, and the
denominator forms).

The law along a history.  A state observable that equals a frequency polynomial of total degree at
most `n` integrates against an event history or a rate history as the polynomial's coefficient
vector dotted with the propagated budget-`n` moments
(`integral_historyEventKernel_of_totalDegree_le`, `integral_rateHistoryKernel_of_totalDegree_le`).
So the expected diploid numerator and denominator are budget-eight dot products
(`integral_genotypeNumerator_historyEventKernel`, `integral_genotypeDenominator_historyEventKernel`
and the rate-history forms).  Diploid expected portability is the rational function
`diploidMomentPortability` of the propagated budget-eight moments
(`expectedDiploidPortability_historyEventKernel_budgetEight`,
`expectedDiploidPortability_rateHistoryKernel_budgetEight`).  Two histories with equal propagated
budget-eight moments give equal diploid portability for every pair of observables and every
choice of inbreeding coefficients (`expectedDiploidPortability_eq_of_budgetEight_moments_eq`).
For additive score and outcome, the budget-eight function of the budget-eight moments of a history
equals the haploid budget-four function of its budget-four moments, whatever the inbreeding
coefficients (`diploidMomentPortability_diploidSum_historyEventKernel`).

Significance.  Dominance breaks the transfer from the haploid law but not the finite-moment
structure.  The portability of a recessive outcome is still a rational function of finitely many
history moments.  The budget doubles, and the inbreeding coefficient of each deme enters the
coefficients instead of cancelling.

Scope.  The gamete pair is the one of `EndToEndDiploidLaw`: both gametes are drawn from the deme's
own haplotype law, and identity by descent is one whole-haplotype event with a coefficient supplied
per deme.  The observables are any real functions of the ordered gamete pair.  The budget-eight
moments are tied to the budget-four moments only through the additive case above.

## Empirical status

None.  The bodies are polynomial identities and integrals of polynomials against Markov kernels,
so no measurement can bear on them.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.EndToEndDiploidHistoryLaw

open MeasureTheory ProbabilityTheory MvPolynomial Descent.Coalescent PartialHaplotypeCarrier
  PartialHaplotypeDualGenerator PartialHaplotypeDualSemigroup NeutralFellerGenerator
  NeutralPolynomialSemigroup PartialHaplotypeMicroscopicApproximation PartialHaplotypePulseKernel
  NeutralPulseHistoryKernel NeutralRateHistoryRealization NeutralRateHistoryKernel
  ReplicaMetricInstances EndToEndPortabilityLaw EndToEndDiploidLaw
open scoped Matrix NNReal

noncomputable section

/-! ## Genotype polynomials -/

section Genotypes

variable {H : Type*} [Fintype H]

/-- **The expectation polynomial of a gamete-pair observable** at inbreeding coefficient `F`: the
pair polynomial with weight `1 - F`, and the expectation polynomial of the diagonal with weight
`F`. -/
def genotypeExpectationPolynomial (F : ℝ) (φ : H × H → ℝ) : MvPolynomial H ℝ :=
  C (1 - F) * pairPolynomial (fun first second ↦ φ (first, second))
    + C F * expectationPolynomial fun haplotype ↦ φ (haplotype, haplotype)

/-- The covariance polynomial of two gamete-pair observables. -/
def genotypeCovariancePolynomial (F : ℝ) (φ ψ : H × H → ℝ) : MvPolynomial H ℝ :=
  genotypeExpectationPolynomial F (fun pair ↦ φ pair * ψ pair)
    - genotypeExpectationPolynomial F φ * genotypeExpectationPolynomial F ψ

/-- The correlation numerator `16 C²` of two gamete-pair observables, as a polynomial. -/
def genotypeNumeratorPolynomial (F : ℝ) (φ ψ : H × H → ℝ) : MvPolynomial H ℝ :=
  C 16 * genotypeCovariancePolynomial F φ ψ ^ 2

/-- The correlation denominator `16 V_φ V_ψ` of two gamete-pair observables, as a polynomial. -/
def genotypeDenominatorPolynomial (F : ℝ) (φ ψ : H × H → ℝ) : MvPolynomial H ℝ :=
  C 16 * (genotypeCovariancePolynomial F φ φ * genotypeCovariancePolynomial F ψ ψ)

/-- **The expectation polynomial evaluates to the gamete-pair expectation.** -/
theorem eval_genotypeExpectationPolynomial [DecidableEq H] (law : FiniteReportLaw H) (F : ℝ)
    (hF0 : 0 ≤ F) (hF1 : F ≤ 1) (φ : H × H → ℝ) :
    eval law.mass (genotypeExpectationPolynomial F φ)
      = (inbredMating law F hF0 hF1).expectation φ := by
  rw [genotypeExpectationPolynomial, map_add, map_mul, map_mul, eval_C, eval_C,
    eval_pairPolynomial, eval_expectationPolynomial, expectation_inbredMating]

/-- The covariance polynomial evaluates to the gamete-pair covariance. -/
theorem eval_genotypeCovariancePolynomial [DecidableEq H] (law : FiniteReportLaw H) (F : ℝ)
    (hF0 : 0 ≤ F) (hF1 : F ≤ 1) (φ ψ : H × H → ℝ) :
    eval law.mass (genotypeCovariancePolynomial F φ ψ)
      = (inbredMating law F hF0 hF1).covariance φ ψ := by
  rw [genotypeCovariancePolynomial, map_sub, map_mul,
    eval_genotypeExpectationPolynomial law F hF0 hF1,
    eval_genotypeExpectationPolynomial law F hF0 hF1,
    eval_genotypeExpectationPolynomial law F hF0 hF1, FiniteReportLaw.covariance_eq_rawMoments]

/-- The numerator polynomial evaluates to the correlation numerator of the gamete-pair law. -/
theorem eval_genotypeNumeratorPolynomial [DecidableEq H] (law : FiniteReportLaw H) (F : ℝ)
    (hF0 : 0 ≤ F) (hF1 : F ≤ 1) (φ ψ : H × H → ℝ) :
    eval law.mass (genotypeNumeratorPolynomial F φ ψ)
      = correlationNumerator (inbredMating law F hF0 hF1) φ ψ := by
  rw [genotypeNumeratorPolynomial, map_mul, map_pow, eval_C,
    eval_genotypeCovariancePolynomial law F hF0 hF1, correlationNumerator]

/-- The denominator polynomial evaluates to the correlation denominator of the gamete-pair law. -/
theorem eval_genotypeDenominatorPolynomial [DecidableEq H] (law : FiniteReportLaw H) (F : ℝ)
    (hF0 : 0 ≤ F) (hF1 : F ≤ 1) (φ ψ : H × H → ℝ) :
    eval law.mass (genotypeDenominatorPolynomial F φ ψ)
      = correlationDenominator (inbredMating law F hF0 hF1) φ ψ := by
  rw [genotypeDenominatorPolynomial, map_mul, map_mul, eval_C,
    eval_genotypeCovariancePolynomial law F hF0 hF1,
    eval_genotypeCovariancePolynomial law F hF0 hF1, correlationDenominator]
  rfl

/-- The expectation polynomial has total degree at most two. -/
theorem totalDegree_genotypeExpectationPolynomial_le (F : ℝ) (φ : H × H → ℝ) :
    (genotypeExpectationPolynomial F φ).totalDegree ≤ 2 := by
  have hpair := totalDegree_pairPolynomial_le fun first second : H ↦ φ (first, second)
  have hdiagonal :=
    totalDegree_expectationPolynomial_le fun haplotype : H ↦ φ (haplotype, haplotype)
  have hleft :=
    totalDegree_mul (C (1 - F)) (pairPolynomial fun first second : H ↦ φ (first, second))
  have hright :=
    totalDegree_mul (C F) (expectationPolynomial fun haplotype : H ↦ φ (haplotype, haplotype))
  rw [totalDegree_C] at hleft hright
  rw [genotypeExpectationPolynomial]
  exact (totalDegree_add _ _).trans (max_le (by omega) (by omega))

/-- The covariance polynomial has total degree at most four. -/
theorem totalDegree_genotypeCovariancePolynomial_le (F : ℝ) (φ ψ : H × H → ℝ) :
    (genotypeCovariancePolynomial F φ ψ).totalDegree ≤ 4 := by
  have hproduct := totalDegree_genotypeExpectationPolynomial_le F fun pair ↦ φ pair * ψ pair
  have hfirst := totalDegree_genotypeExpectationPolynomial_le F φ
  have hsecond := totalDegree_genotypeExpectationPolynomial_le F ψ
  have hmul := totalDegree_mul (genotypeExpectationPolynomial F φ)
    (genotypeExpectationPolynomial F ψ)
  rw [genotypeCovariancePolynomial]
  exact (totalDegree_sub _ _).trans (max_le (by omega) (by omega))

/-- **The numerator polynomial has total degree at most eight.** -/
theorem totalDegree_genotypeNumeratorPolynomial_le (F : ℝ) (φ ψ : H × H → ℝ) :
    (genotypeNumeratorPolynomial F φ ψ).totalDegree ≤ 8 := by
  have hcovariance := totalDegree_genotypeCovariancePolynomial_le F φ ψ
  have hpow := totalDegree_pow (genotypeCovariancePolynomial F φ ψ) 2
  have hscaled := totalDegree_mul (C 16 : MvPolynomial H ℝ)
    (genotypeCovariancePolynomial F φ ψ ^ 2)
  rw [totalDegree_C] at hscaled
  rw [genotypeNumeratorPolynomial]
  exact hscaled.trans (by omega)

/-- **The denominator polynomial has total degree at most eight.** -/
theorem totalDegree_genotypeDenominatorPolynomial_le (F : ℝ) (φ ψ : H × H → ℝ) :
    (genotypeDenominatorPolynomial F φ ψ).totalDegree ≤ 8 := by
  have hfirst := totalDegree_genotypeCovariancePolynomial_le F φ φ
  have hsecond := totalDegree_genotypeCovariancePolynomial_le F ψ ψ
  have hproduct := totalDegree_mul (genotypeCovariancePolynomial F φ φ)
    (genotypeCovariancePolynomial F ψ ψ)
  have hscaled := totalDegree_mul (C 16 : MvPolynomial H ℝ)
    (genotypeCovariancePolynomial F φ φ * genotypeCovariancePolynomial F ψ ψ)
  rw [totalDegree_C] at hscaled
  rw [genotypeDenominatorPolynomial]
  exact hscaled.trans (by omega)

end Genotypes

/-! ## The frequency polynomials of a deme -/

section History

variable {Deme Locus : Type*} {Allele : Locus → Type*}
variable [Fintype Deme] [DecidableEq Deme] [Fintype Locus] [DecidableEq Locus]
  [∀ ℓ, Fintype (Allele ℓ)] [∀ ℓ, DecidableEq (Allele ℓ)]

/-- The diploid correlation numerator of one deme, at that deme's inbreeding coefficient, as a
frequency polynomial. -/
def diploidNumeratorPolynomial (deme : Deme) (inbreeding : Deme → ℝ)
    (φ ψ : FullHaplotype Locus Allele × FullHaplotype Locus Allele → ℝ) :
    FrequencyPolynomial Deme Locus Allele :=
  demePolynomial deme (genotypeNumeratorPolynomial (inbreeding deme) φ ψ)

/-- The diploid correlation denominator of one deme, as a frequency polynomial. -/
def diploidDenominatorPolynomial (deme : Deme) (inbreeding : Deme → ℝ)
    (φ ψ : FullHaplotype Locus Allele × FullHaplotype Locus Allele → ℝ) :
    FrequencyPolynomial Deme Locus Allele :=
  demePolynomial deme (genotypeDenominatorPolynomial (inbreeding deme) φ ψ)

/-- At a state, the diploid numerator polynomial is the correlation numerator of the deme's
gamete-pair law. -/
theorem polynomialFunction_diploidNumeratorPolynomial (deme : Deme) (inbreeding : Deme → ℝ)
    (hF0 : ∀ other, 0 ≤ inbreeding other) (hF1 : ∀ other, inbreeding other ≤ 1)
    (φ ψ : FullHaplotype Locus Allele × FullHaplotype Locus Allele → ℝ)
    (y : FrequencyState Deme Locus Allele) :
    polynomialFunction (diploidNumeratorPolynomial deme inbreeding φ ψ) y
      = correlationNumerator (stateGenotypeLaw y deme inbreeding hF0 hF1) φ ψ := by
  rw [stateGenotypeLaw, polynomialFunction_apply, diploidNumeratorPolynomial,
    eval_demePolynomial,
    eval_genotypeNumeratorPolynomial (stateLaw y deme) (inbreeding deme) (hF0 deme) (hF1 deme)]

/-- At a state, the diploid denominator polynomial is the correlation denominator of the deme's
gamete-pair law. -/
theorem polynomialFunction_diploidDenominatorPolynomial (deme : Deme) (inbreeding : Deme → ℝ)
    (hF0 : ∀ other, 0 ≤ inbreeding other) (hF1 : ∀ other, inbreeding other ≤ 1)
    (φ ψ : FullHaplotype Locus Allele × FullHaplotype Locus Allele → ℝ)
    (y : FrequencyState Deme Locus Allele) :
    polynomialFunction (diploidDenominatorPolynomial deme inbreeding φ ψ) y
      = correlationDenominator (stateGenotypeLaw y deme inbreeding hF0 hF1) φ ψ := by
  rw [stateGenotypeLaw, polynomialFunction_apply, diploidDenominatorPolynomial,
    eval_demePolynomial,
    eval_genotypeDenominatorPolynomial (stateLaw y deme) (inbreeding deme) (hF0 deme) (hF1 deme)]

/-- The diploid numerator polynomial has total degree at most eight. -/
theorem totalDegree_diploidNumeratorPolynomial_le (deme : Deme) (inbreeding : Deme → ℝ)
    (φ ψ : FullHaplotype Locus Allele × FullHaplotype Locus Allele → ℝ) :
    (diploidNumeratorPolynomial deme inbreeding φ ψ).totalDegree ≤ 8 :=
  (totalDegree_rename_le _ _).trans (totalDegree_genotypeNumeratorPolynomial_le _ φ ψ)

/-- The diploid denominator polynomial has total degree at most eight. -/
theorem totalDegree_diploidDenominatorPolynomial_le (deme : Deme) (inbreeding : Deme → ℝ)
    (φ ψ : FullHaplotype Locus Allele × FullHaplotype Locus Allele → ℝ) :
    (diploidDenominatorPolynomial deme inbreeding φ ψ).totalDegree ≤ 8 :=
  (totalDegree_rename_le _ _).trans (totalDegree_genotypeDenominatorPolynomial_le _ φ ψ)

/-! ## Polynomial observables along a history -/

/-- **A polynomial observable integrates through the moments of its degree.**  A state observable
equal to a frequency polynomial of total degree at most `n` integrates against a history of epochs,
splits and pulses as the polynomial's coefficient vector dotted with the propagated budget-`n`
moments of `x₀`. -/
theorem integral_historyEventKernel_of_totalDegree_le (ℓ₀ : Locus)
    (hap₀ : FullHaplotype Locus Allele)
    (events : List ((NeutralRates Deme Locus Allele × ℝ≥0) ⊕ PulseMatrix Deme))
    (x0 : FrequencyState Deme Locus Allele) {n : ℕ} (p : FrequencyPolynomial Deme Locus Allele)
    (hp : p.totalDegree ≤ n) (observable : FrequencyState Deme Locus Allele → ℝ)
    (hobservable : ∀ y, polynomialFunction p y = observable y) :
    ∫ y, observable y ∂(historyEventKernel ℓ₀ hap₀ events x0)
      = budgetCoefficients ℓ₀ (fun _ ↦ n) p
        ⬝ᵥ (historyEventPropagator (fun _ ↦ n) events *ᵥ budgetMomentFeature (fun _ ↦ n) x0) := by
  haveI := isMarkovKernel_historyEventKernel ℓ₀ hap₀ events
  obtain rfl : observable = fun y ↦ polynomialFunction p y :=
    funext fun y ↦ (hobservable y).symm
  exact integral_polynomial_eq_dotProduct ℓ₀ (fun _ ↦ n) (historyEventKernel ℓ₀ hap₀ events)
    (historyEventPropagator (fun _ ↦ n) events)
    (integral_momentPolynomial_historyEventKernel ℓ₀ hap₀ (fun _ ↦ n) events) p
    (withinBudget_of_totalDegree_le ℓ₀ p hp) x0

/-- **A polynomial observable integrates through the moments of its degree along a rate
history.** -/
theorem integral_rateHistoryKernel_of_totalDegree_le {rates : ℝ → NeutralRates Deme Locus Allele}
    {T : ℝ} (hT : 0 ≤ T)
    (hcontinuous : ∀ capacity : Locus → ℕ,
      ContinuousOn (fun t ↦ dualGenerator (rates t) capacity) (Set.Icc 0 T))
    (ℓ₀ : Locus) (hap₀ : FullHaplotype Locus Allele) (x0 : FrequencyState Deme Locus Allele)
    {n : ℕ} (p : FrequencyPolynomial Deme Locus Allele) (hp : p.totalDegree ≤ n)
    (observable : FrequencyState Deme Locus Allele → ℝ)
    (hobservable : ∀ y, polynomialFunction p y = observable y) :
    ∫ y, observable y ∂(rateHistoryKernel rates ℓ₀ hap₀ hT hcontinuous x0)
      = budgetCoefficients ℓ₀ (fun _ ↦ n) p
        ⬝ᵥ (rateHistoryDualPropagator rates (fun _ ↦ n) T
          *ᵥ budgetMomentFeature (fun _ ↦ n) x0) := by
  haveI := isMarkovKernel_rateHistoryKernel hT hcontinuous ℓ₀ hap₀
  obtain rfl : observable = fun y ↦ polynomialFunction p y :=
    funext fun y ↦ (hobservable y).symm
  exact integral_polynomial_eq_dotProduct ℓ₀ (fun _ ↦ n)
    (rateHistoryKernel rates ℓ₀ hap₀ hT hcontinuous) (rateHistoryDualPropagator rates (fun _ ↦ n) T)
    (integral_momentPolynomial_rateHistoryKernel hT hcontinuous ℓ₀ hap₀ (fun _ ↦ n)) p
    (withinBudget_of_totalDegree_le ℓ₀ p hp) x0

/-! ## The diploid law at budget eight -/

/-- **The expected diploid numerator along a history** is, for any two gamete-pair observables, the
budget-eight coefficient vector of the deme's numerator polynomial dotted with the propagated
budget-eight moments. -/
theorem integral_genotypeNumerator_historyEventKernel
    (ℓ₀ : Locus) (hap₀ : FullHaplotype Locus Allele)
    (events : List ((NeutralRates Deme Locus Allele × ℝ≥0) ⊕ PulseMatrix Deme))
    (x0 : FrequencyState Deme Locus Allele)
    (deme : Deme) (inbreeding : Deme → ℝ) (hF0 : ∀ other, 0 ≤ inbreeding other)
    (hF1 : ∀ other, inbreeding other ≤ 1)
    (φ ψ : FullHaplotype Locus Allele × FullHaplotype Locus Allele → ℝ) :
    ∫ y, correlationNumerator (stateGenotypeLaw y deme inbreeding hF0 hF1) φ ψ
        ∂(historyEventKernel ℓ₀ hap₀ events x0)
      = budgetCoefficients ℓ₀ (fun _ ↦ 8) (diploidNumeratorPolynomial deme inbreeding φ ψ)
        ⬝ᵥ (historyEventPropagator (fun _ ↦ 8) events *ᵥ budgetMomentFeature (fun _ ↦ 8) x0) :=
  integral_historyEventKernel_of_totalDegree_le ℓ₀ hap₀ events x0 _
    (totalDegree_diploidNumeratorPolynomial_le deme inbreeding φ ψ) _
    (polynomialFunction_diploidNumeratorPolynomial deme inbreeding hF0 hF1 φ ψ)

/-- **The expected diploid denominator along a history** at budget eight. -/
theorem integral_genotypeDenominator_historyEventKernel
    (ℓ₀ : Locus) (hap₀ : FullHaplotype Locus Allele)
    (events : List ((NeutralRates Deme Locus Allele × ℝ≥0) ⊕ PulseMatrix Deme))
    (x0 : FrequencyState Deme Locus Allele)
    (deme : Deme) (inbreeding : Deme → ℝ) (hF0 : ∀ other, 0 ≤ inbreeding other)
    (hF1 : ∀ other, inbreeding other ≤ 1)
    (φ ψ : FullHaplotype Locus Allele × FullHaplotype Locus Allele → ℝ) :
    ∫ y, correlationDenominator (stateGenotypeLaw y deme inbreeding hF0 hF1) φ ψ
        ∂(historyEventKernel ℓ₀ hap₀ events x0)
      = budgetCoefficients ℓ₀ (fun _ ↦ 8) (diploidDenominatorPolynomial deme inbreeding φ ψ)
        ⬝ᵥ (historyEventPropagator (fun _ ↦ 8) events *ᵥ budgetMomentFeature (fun _ ↦ 8) x0) :=
  integral_historyEventKernel_of_totalDegree_le ℓ₀ hap₀ events x0 _
    (totalDegree_diploidDenominatorPolynomial_le deme inbreeding φ ψ) _
    (polynomialFunction_diploidDenominatorPolynomial deme inbreeding hF0 hF1 φ ψ)

/-- **The expected diploid numerator along a rate history** at budget eight. -/
theorem integral_genotypeNumerator_rateHistoryKernel {rates : ℝ → NeutralRates Deme Locus Allele}
    {T : ℝ} (hT : 0 ≤ T)
    (hcontinuous : ∀ capacity : Locus → ℕ,
      ContinuousOn (fun t ↦ dualGenerator (rates t) capacity) (Set.Icc 0 T))
    (ℓ₀ : Locus) (hap₀ : FullHaplotype Locus Allele) (x0 : FrequencyState Deme Locus Allele)
    (deme : Deme) (inbreeding : Deme → ℝ) (hF0 : ∀ other, 0 ≤ inbreeding other)
    (hF1 : ∀ other, inbreeding other ≤ 1)
    (φ ψ : FullHaplotype Locus Allele × FullHaplotype Locus Allele → ℝ) :
    ∫ y, correlationNumerator (stateGenotypeLaw y deme inbreeding hF0 hF1) φ ψ
        ∂(rateHistoryKernel rates ℓ₀ hap₀ hT hcontinuous x0)
      = budgetCoefficients ℓ₀ (fun _ ↦ 8) (diploidNumeratorPolynomial deme inbreeding φ ψ)
        ⬝ᵥ (rateHistoryDualPropagator rates (fun _ ↦ 8) T
          *ᵥ budgetMomentFeature (fun _ ↦ 8) x0) :=
  integral_rateHistoryKernel_of_totalDegree_le hT hcontinuous ℓ₀ hap₀ x0 _
    (totalDegree_diploidNumeratorPolynomial_le deme inbreeding φ ψ) _
    (polynomialFunction_diploidNumeratorPolynomial deme inbreeding hF0 hF1 φ ψ)

/-- **The expected diploid denominator along a rate history** at budget eight. -/
theorem integral_genotypeDenominator_rateHistoryKernel
    {rates : ℝ → NeutralRates Deme Locus Allele} {T : ℝ} (hT : 0 ≤ T)
    (hcontinuous : ∀ capacity : Locus → ℕ,
      ContinuousOn (fun t ↦ dualGenerator (rates t) capacity) (Set.Icc 0 T))
    (ℓ₀ : Locus) (hap₀ : FullHaplotype Locus Allele) (x0 : FrequencyState Deme Locus Allele)
    (deme : Deme) (inbreeding : Deme → ℝ) (hF0 : ∀ other, 0 ≤ inbreeding other)
    (hF1 : ∀ other, inbreeding other ≤ 1)
    (φ ψ : FullHaplotype Locus Allele × FullHaplotype Locus Allele → ℝ) :
    ∫ y, correlationDenominator (stateGenotypeLaw y deme inbreeding hF0 hF1) φ ψ
        ∂(rateHistoryKernel rates ℓ₀ hap₀ hT hcontinuous x0)
      = budgetCoefficients ℓ₀ (fun _ ↦ 8) (diploidDenominatorPolynomial deme inbreeding φ ψ)
        ⬝ᵥ (rateHistoryDualPropagator rates (fun _ ↦ 8) T
          *ᵥ budgetMomentFeature (fun _ ↦ 8) x0) :=
  integral_rateHistoryKernel_of_totalDegree_le hT hcontinuous ℓ₀ hap₀ x0 _
    (totalDegree_diploidDenominatorPolynomial_le deme inbreeding φ ψ) _
    (polynomialFunction_diploidDenominatorPolynomial deme inbreeding hF0 hF1 φ ψ)

/-- **The rational diploid portability function** of a budget-eight moment vector, for any two
gamete-pair observables and any inbreeding coefficients. -/
def diploidMomentPortability (ℓ₀ : Locus) (source target : Deme) (inbreeding : Deme → ℝ)
    (φ ψ : FullHaplotype Locus Allele × FullHaplotype Locus Allele → ℝ)
    (v : BudgetConfiguration Deme Locus Allele (fun _ ↦ 8) → ℝ) : ℝ :=
  ((budgetCoefficients ℓ₀ (fun _ ↦ 8) (diploidNumeratorPolynomial target inbreeding φ ψ) ⬝ᵥ v)
      * (budgetCoefficients ℓ₀ (fun _ ↦ 8) (diploidDenominatorPolynomial source inbreeding φ ψ)
        ⬝ᵥ v))
    / ((budgetCoefficients ℓ₀ (fun _ ↦ 8) (diploidDenominatorPolynomial target inbreeding φ ψ)
        ⬝ᵥ v)
      * (budgetCoefficients ℓ₀ (fun _ ↦ 8) (diploidNumeratorPolynomial source inbreeding φ ψ)
        ⬝ᵥ v))

/-- **The diploid portability law for every genotype observable along a history of epochs, splits
and pulses.**  Diploid expected portability is the rational function `diploidMomentPortability` of
the chronological propagator applied to the budget-eight moments of `x₀`. -/
theorem expectedDiploidPortability_historyEventKernel_budgetEight
    (ℓ₀ : Locus) (hap₀ : FullHaplotype Locus Allele)
    (events : List ((NeutralRates Deme Locus Allele × ℝ≥0) ⊕ PulseMatrix Deme))
    (x0 : FrequencyState Deme Locus Allele) (source target : Deme) (inbreeding : Deme → ℝ)
    (hF0 : ∀ other, 0 ≤ inbreeding other) (hF1 : ∀ other, inbreeding other ≤ 1)
    (φ ψ : FullHaplotype Locus Allele × FullHaplotype Locus Allele → ℝ) :
    expectedDiploidPortability (historyEventKernel ℓ₀ hap₀ events) x0 source target inbreeding
        hF0 hF1 φ ψ
      = diploidMomentPortability ℓ₀ source target inbreeding φ ψ
          (historyEventPropagator (fun _ ↦ 8) events *ᵥ budgetMomentFeature (fun _ ↦ 8) x0) := by
  rw [expectedDiploidPortability, integral_genotypeNumerator_historyEventKernel,
    integral_genotypeNumerator_historyEventKernel, integral_genotypeDenominator_historyEventKernel,
    integral_genotypeDenominator_historyEventKernel]
  rfl

/-- **The diploid portability law for every genotype observable along a rate history.** -/
theorem expectedDiploidPortability_rateHistoryKernel_budgetEight
    {rates : ℝ → NeutralRates Deme Locus Allele} {T : ℝ} (hT : 0 ≤ T)
    (hcontinuous : ∀ capacity : Locus → ℕ,
      ContinuousOn (fun t ↦ dualGenerator (rates t) capacity) (Set.Icc 0 T))
    (ℓ₀ : Locus) (hap₀ : FullHaplotype Locus Allele) (x0 : FrequencyState Deme Locus Allele)
    (source target : Deme) (inbreeding : Deme → ℝ)
    (hF0 : ∀ other, 0 ≤ inbreeding other) (hF1 : ∀ other, inbreeding other ≤ 1)
    (φ ψ : FullHaplotype Locus Allele × FullHaplotype Locus Allele → ℝ) :
    expectedDiploidPortability (rateHistoryKernel rates ℓ₀ hap₀ hT hcontinuous) x0 source target
        inbreeding hF0 hF1 φ ψ
      = diploidMomentPortability ℓ₀ source target inbreeding φ ψ
          (rateHistoryDualPropagator rates (fun _ ↦ 8) T
            *ᵥ budgetMomentFeature (fun _ ↦ 8) x0) := by
  rw [expectedDiploidPortability, integral_genotypeNumerator_rateHistoryKernel,
    integral_genotypeNumerator_rateHistoryKernel, integral_genotypeDenominator_rateHistoryKernel,
    integral_genotypeDenominator_rateHistoryKernel]
  rfl

/-- **Diploid portability of any genotype observable sees the history only through finitely many
moments.**  Two histories, from two initial states, whose propagated budget-eight moments agree
have equal diploid expected portability for every pair of gamete-pair observables. -/
theorem expectedDiploidPortability_eq_of_budgetEight_moments_eq (ℓ₀ : Locus)
    (hap₀ : FullHaplotype Locus Allele)
    {first second : List ((NeutralRates Deme Locus Allele × ℝ≥0) ⊕ PulseMatrix Deme)}
    {x₁ x₂ : FrequencyState Deme Locus Allele}
    (hmoments : historyEventPropagator (fun _ ↦ 8) first *ᵥ budgetMomentFeature (fun _ ↦ 8) x₁
      = historyEventPropagator (fun _ ↦ 8) second *ᵥ budgetMomentFeature (fun _ ↦ 8) x₂)
    (source target : Deme) (inbreeding : Deme → ℝ) (hF0 : ∀ other, 0 ≤ inbreeding other)
    (hF1 : ∀ other, inbreeding other ≤ 1)
    (φ ψ : FullHaplotype Locus Allele × FullHaplotype Locus Allele → ℝ) :
    expectedDiploidPortability (historyEventKernel ℓ₀ hap₀ first) x₁ source target inbreeding
        hF0 hF1 φ ψ
      = expectedDiploidPortability (historyEventKernel ℓ₀ hap₀ second) x₂ source target
          inbreeding hF0 hF1 φ ψ := by
  rw [expectedDiploidPortability_historyEventKernel_budgetEight,
    expectedDiploidPortability_historyEventKernel_budgetEight, hmoments]

/-- **The two budgets agree on additive observables.**  For additive score and outcome, the
budget-eight diploid function of the budget-eight moments of a history equals the haploid
budget-four function of the budget-four moments of the same history, whatever the inbreeding
coefficients. -/
theorem diploidMomentPortability_diploidSum_historyEventKernel
    (ℓ₀ : Locus) (hap₀ : FullHaplotype Locus Allele)
    (events : List ((NeutralRates Deme Locus Allele × ℝ≥0) ⊕ PulseMatrix Deme))
    (x0 : FrequencyState Deme Locus Allele) (source target : Deme) (inbreeding : Deme → ℝ)
    (hF0 : ∀ other, 0 ≤ inbreeding other) (hF1 : ∀ other, inbreeding other ≤ 1)
    (score outcome : FullHaplotype Locus Allele → ℝ) :
    diploidMomentPortability ℓ₀ source target inbreeding (diploidSum score) (diploidSum outcome)
        (historyEventPropagator (fun _ ↦ 8) events *ᵥ budgetMomentFeature (fun _ ↦ 8) x0)
      = momentPortability ℓ₀ source target score outcome
          (historyEventPropagator (fun _ ↦ 4) events *ᵥ budgetMomentFeature (fun _ ↦ 4) x0) := by
  rw [← expectedDiploidPortability_historyEventKernel_budgetEight ℓ₀ hap₀ events x0 source target
    inbreeding hF0 hF1, expectedDiploidPortability_historyEventKernel]

end History

end

end Descent.Portability.EndToEndDiploidHistoryLaw
