/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.PortabilityMomentLadder

assert_below Descent.Decision Descent.Program

/-!
# The end-to-end law of temporal portability

The end-to-end laws of this corpus compare two demes at the end of a history.  This module
compares one deme with itself through time.  A score is calibrated on the present state `x₀` of a
deme, and the same deme is observed after a neutral history run from `x₀`: a list of epochs,
splits and admixture pulses (`NeutralPulseHistoryKernel.historyEventKernel`), a rate path with
continuous dual generator (`NeutralRateHistoryKernel.rateHistoryKernel`), or any Markov kernel
with dual moments, NOTE1 (20).

The metrics.  For a score `S` and an outcome `Y` in a deme, temporal portability divides a
ratio-of-expectations query of NOTE2 §6.2 after the history by the same metric at `x₀`.  For the
covariance it is `E C_SY / C_SY(x₀)` (`temporalCovariancePortability`).  For calibration it is
the slope of expectations `E C_SY / E V_S` over `C_SY(x₀) / V_S(x₀)`
(`temporalCalibrationPortability`).  For accuracy it is `(E N / E D) / (N(x₀) / D(x₀))`, in cross
form, for the squared-correlation numerator `N` and denominator `D`
(`temporalAccuracyPortability`).

The present state through its own moments.  A frequency polynomial of total degree at most `n`,
evaluated at `x₀`, is its coefficient vector dotted with the budget-`n` configuration moments
`H_n(x₀)` (`polynomialFunction_eq_dotProduct_budgetMomentFeature`).  So are the present
covariance, variance, calibration slope and correlation accumulators
(`presentCovariance_eq_dotProduct`, `presentVariance_eq_dotProduct`,
`presentCalibrationSlope_eq_momentCalibrationSlope`, `presentCorrelationNumerator_eq_dotProduct`,
`presentCorrelationDenominator_eq_dotProduct`).  The present state is the empty history
(`integral_covariance_historyEventKernel_nil`, `integral_variance_historyEventKernel_nil`,
`expectedCalibrationSlope_historyEventKernel_nil`), so temporal calibration portability is the
slope of expectations under a kernel over the slope of expectations under the empty history
(`temporalCalibrationPortability_eq_div_nil`).

The law.  Under a Markov kernel with budget-`n` dual moments along `M`, every temporal portability
is a rational function whose numerator reads the propagated moments `M · H_n(x₀)` and whose
denominator reads the initial moments `H_n(x₀)`.  Covariance and calibration need budget 2
(`temporalCovariancePortability_eq_dotProduct`,
`temporalCalibrationPortability_eq_momentCalibrationSlope`) and accuracy budget 4
(`temporalAccuracyPortability_eq_dotProduct`).  Along a history of epochs, splits and pulses `M`
is the chronological propagator (`temporalCovariancePortability_historyEventKernel`,
`temporalCalibrationPortability_historyEventKernel`,
`temporalAccuracyPortability_historyEventKernel`).  Along a rate history it is the propagator of
the rate path (`temporalCovariancePortability_rateHistoryKernel`,
`temporalCalibrationPortability_rateHistoryKernel`,
`temporalAccuracyPortability_rateHistoryKernel`).

Consequences.  The expected covariance after a history is one propagated budget-2 dot product, so
temporal covariance and calibration portability see the history only through one matrix.  Two
histories whose propagated budget-2 moments from `x₀` agree give equal temporal portability from
`x₀` (`temporalPortability_eq_of_momentsAgreeAt_two`).  Two histories with equal budget-2
propagators give it from every present state (`temporalPortability_eq_of_propagator_eq`).
Accuracy needs agreement at budget 4 (`temporalAccuracyPortability_eq_of_momentsAgreeAt_four`).
A kernel whose dual moments are the identity leaves every temporal portability at one wherever
the present metric is nonzero (`temporalCovariancePortability_eq_one_of_hasDualMoments_one`,
`temporalCalibrationPortability_eq_one_of_hasDualMoments_one`,
`temporalAccuracyPortability_eq_one_of_hasDualMoments_one`).  An epoch of zero duration is such a
kernel (`hasDualMoments_historyEventKernel_zeroEpoch`), so temporal portability at `T = 0` is one
(`temporalPortability_zeroEpoch`).

Significance.  The decay of a score in its own population is the same finite computation as its
transfer between populations: one propagator applied to the present moments, then one rational
function whose denominator is the present value of the metric.  The elapsed time enters only
through the propagator.

Scope.  The metrics after the history are ratio-of-expectations queries; the expectation of the
per-population ratio is not stated.  The direction is forward: a score fitted at `x₀` and applied
after the history.  The action of the budget-2 dual generator on the covariance coefficients is
not computed, so no closed form in the length of a neutral epoch is stated.  One chromosome is
sampled per individual.

## Empirical status

None.  The bodies here are polynomial identities at a state and integrals of polynomials against
Markov kernels whose moments are matrix computations of supplied rates, so no measurement can
bear on them.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.EndToEndTemporalPortability

open MeasureTheory ProbabilityTheory MvPolynomial Descent.Coalescent PartialHaplotypeCarrier
  PartialHaplotypeDualGenerator PartialHaplotypeDualSemigroup NeutralFellerGenerator
  NeutralPolynomialSemigroup PartialHaplotypeMicroscopicApproximation PartialHaplotypePulseKernel
  NeutralPulseHistoryKernel NeutralRateHistoryRealization NeutralRateHistoryKernel
  ReplicaMetricInstances EndToEndPortabilityLaw EndToEndCalibrationLaw EndToEndDiscriminationLaw
  PortabilityMomentLadder
open scoped Matrix NNReal

noncomputable section

variable {Deme Locus : Type*} {Allele : Locus → Type*}
variable [Fintype Deme] [DecidableEq Deme] [Fintype Locus] [DecidableEq Locus]
  [∀ ℓ, Fintype (Allele ℓ)] [∀ ℓ, DecidableEq (Allele ℓ)]

attribute [local instance] isMarkovKernel_historyEventKernel isMarkovKernel_rateHistoryKernel

/-! ## Temporal portability -/

/-- **Temporal covariance portability**: the expected score–outcome covariance of a deme under a
kernel started at the present state `x₀`, over the covariance of the deme at `x₀`. -/
def temporalCovariancePortability
    (κ : Kernel (FrequencyState Deme Locus Allele) (FrequencyState Deme Locus Allele))
    (x0 : FrequencyState Deme Locus Allele) (deme : Deme)
    (score outcome : FullHaplotype Locus Allele → ℝ) : ℝ :=
  (∫ y, (stateLaw y deme).covariance score outcome ∂(κ x0))
    / (stateLaw x0 deme).covariance score outcome

/-- **Temporal calibration portability**: the calibration slope of expectations of a deme under a
kernel started at `x₀`, over the calibration slope `C_SY / V_S` of the deme at `x₀`. -/
def temporalCalibrationPortability
    (κ : Kernel (FrequencyState Deme Locus Allele) (FrequencyState Deme Locus Allele))
    (x0 : FrequencyState Deme Locus Allele) (deme : Deme)
    (score outcome : FullHaplotype Locus Allele → ℝ) : ℝ :=
  expectedCalibrationSlope κ x0 deme score outcome
    / ((stateLaw x0 deme).covariance score outcome / (stateLaw x0 deme).variance score)

/-- **Temporal accuracy portability**: the squared correlation of expectations `E N / E D` of a
deme under a kernel started at `x₀`, over the squared correlation `N / D` of the deme at `x₀`, in
cross form. -/
def temporalAccuracyPortability
    (κ : Kernel (FrequencyState Deme Locus Allele) (FrequencyState Deme Locus Allele))
    (x0 : FrequencyState Deme Locus Allele) (deme : Deme)
    (score outcome : FullHaplotype Locus Allele → ℝ) : ℝ :=
  ((∫ y, correlationNumerator (stateLaw y deme) score outcome ∂(κ x0))
      * correlationDenominator (stateLaw x0 deme) score outcome)
    / ((∫ y, correlationDenominator (stateLaw y deme) score outcome ∂(κ x0))
      * correlationNumerator (stateLaw x0 deme) score outcome)

/-! ## The present state through its own moments -/

/-- **A polynomial at the present state through the initial moments.**  A frequency polynomial of
total degree at most `n`, evaluated at `x₀`, is its budget-`n` coefficient vector dotted with the
budget-`n` configuration moments of `x₀`.

Assumes: the polynomial has total degree at most `n`. -/
theorem polynomialFunction_eq_dotProduct_budgetMomentFeature (ℓ₀ : Locus) {n : ℕ}
    (p : FrequencyPolynomial Deme Locus Allele) (hp : p.totalDegree ≤ n)
    (x0 : FrequencyState Deme Locus Allele) :
    polynomialFunction p x0
      = budgetCoefficients ℓ₀ (fun _ ↦ n) p ⬝ᵥ budgetMomentFeature (fun _ ↦ n) x0 :=
  NeutralPolynomialSemigroup.eval_eq_dotProduct ℓ₀ (fun _ ↦ n) p
    (withinBudget_of_totalDegree_le ℓ₀ p hp) x0

/-- **The present covariance through the initial moments**, at every budget `n ≥ 2`. -/
theorem presentCovariance_eq_dotProduct (ℓ₀ : Locus) {n : ℕ} (hn : 2 ≤ n)
    (x0 : FrequencyState Deme Locus Allele) (deme : Deme)
    (first second : FullHaplotype Locus Allele → ℝ) :
    (stateLaw x0 deme).covariance first second
      = budgetCoefficients ℓ₀ (fun _ ↦ n) (demeCovariancePolynomial deme first second)
        ⬝ᵥ budgetMomentFeature (fun _ ↦ n) x0 := by
  rw [← polynomialFunction_demeCovariancePolynomial deme first second x0]
  exact polynomialFunction_eq_dotProduct_budgetMomentFeature ℓ₀ _
    ((totalDegree_demeCovariancePolynomial_le deme first second).trans hn) x0

/-- **The present variance through the initial moments**, at every budget `n ≥ 2`. -/
theorem presentVariance_eq_dotProduct (ℓ₀ : Locus) {n : ℕ} (hn : 2 ≤ n)
    (x0 : FrequencyState Deme Locus Allele) (deme : Deme)
    (value : FullHaplotype Locus Allele → ℝ) :
    (stateLaw x0 deme).variance value
      = budgetCoefficients ℓ₀ (fun _ ↦ n) (demeCovariancePolynomial deme value value)
        ⬝ᵥ budgetMomentFeature (fun _ ↦ n) x0 :=
  presentCovariance_eq_dotProduct ℓ₀ hn x0 deme value value

/-- **The present calibration slope through the initial moments.**  At every budget `n ≥ 2`,
`C_SY(x₀) / V_S(x₀)` is the rational calibration slope of the budget-`n` moments of `x₀`. -/
theorem presentCalibrationSlope_eq_momentCalibrationSlope (ℓ₀ : Locus) {n : ℕ} (hn : 2 ≤ n)
    (x0 : FrequencyState Deme Locus Allele) (deme : Deme)
    (score outcome : FullHaplotype Locus Allele → ℝ) :
    (stateLaw x0 deme).covariance score outcome / (stateLaw x0 deme).variance score
      = momentCalibrationSlope ℓ₀ n deme score outcome (budgetMomentFeature (fun _ ↦ n) x0) := by
  rw [momentCalibrationSlope, presentCovariance_eq_dotProduct ℓ₀ hn x0 deme score outcome,
    presentVariance_eq_dotProduct ℓ₀ hn x0 deme score]

/-- **The present squared-correlation numerator through the budget-4 initial moments.** -/
theorem presentCorrelationNumerator_eq_dotProduct (ℓ₀ : Locus)
    (x0 : FrequencyState Deme Locus Allele) (deme : Deme)
    (score outcome : FullHaplotype Locus Allele → ℝ) :
    correlationNumerator (stateLaw x0 deme) score outcome
      = budgetCoefficients ℓ₀ (fun _ ↦ 4) (numeratorPolynomial deme score outcome)
        ⬝ᵥ budgetMomentFeature (fun _ ↦ 4) x0 := by
  rw [← polynomialFunction_numeratorPolynomial deme score outcome x0]
  exact polynomialFunction_eq_dotProduct_budgetMomentFeature ℓ₀ _
    (totalDegree_numeratorPolynomial_le deme score outcome) x0

/-- **The present squared-correlation denominator through the budget-4 initial moments.** -/
theorem presentCorrelationDenominator_eq_dotProduct (ℓ₀ : Locus)
    (x0 : FrequencyState Deme Locus Allele) (deme : Deme)
    (score outcome : FullHaplotype Locus Allele → ℝ) :
    correlationDenominator (stateLaw x0 deme) score outcome
      = budgetCoefficients ℓ₀ (fun _ ↦ 4) (denominatorPolynomial deme score outcome)
        ⬝ᵥ budgetMomentFeature (fun _ ↦ 4) x0 := by
  rw [← polynomialFunction_denominatorPolynomial deme score outcome x0]
  exact polynomialFunction_eq_dotProduct_budgetMomentFeature ℓ₀ _
    (totalDegree_denominatorPolynomial_le deme score outcome) x0

/-- **The present state is the empty history.**  The expected covariance of a deme under the
kernel of the empty history started at `x₀` is the covariance of the deme at `x₀`. -/
theorem integral_covariance_historyEventKernel_nil (ℓ₀ : Locus)
    (hap₀ : FullHaplotype Locus Allele) (x0 : FrequencyState Deme Locus Allele) (deme : Deme)
    (first second : FullHaplotype Locus Allele → ℝ) :
    ∫ y, (stateLaw y deme).covariance first second ∂(historyEventKernel ℓ₀ hap₀ [] x0)
      = (stateLaw x0 deme).covariance first second := by
  rw [integral_covariance_historyEventKernel ℓ₀ hap₀ [] (n := 2) le_rfl x0 deme first second,
    presentCovariance_eq_dotProduct ℓ₀ (n := 2) le_rfl x0 deme first second]
  simp only [historyEventPropagator, Matrix.one_mulVec]

/-- The expected variance of a deme under the empty history is the variance at `x₀`. -/
theorem integral_variance_historyEventKernel_nil (ℓ₀ : Locus)
    (hap₀ : FullHaplotype Locus Allele) (x0 : FrequencyState Deme Locus Allele) (deme : Deme)
    (value : FullHaplotype Locus Allele → ℝ) :
    ∫ y, (stateLaw y deme).variance value ∂(historyEventKernel ℓ₀ hap₀ [] x0)
      = (stateLaw x0 deme).variance value :=
  integral_covariance_historyEventKernel_nil ℓ₀ hap₀ x0 deme value value

/-- **The calibration slope of expectations under the empty history** is the slope
`C_SY(x₀) / V_S(x₀)` of the deme at the present state. -/
theorem expectedCalibrationSlope_historyEventKernel_nil (ℓ₀ : Locus)
    (hap₀ : FullHaplotype Locus Allele) (x0 : FrequencyState Deme Locus Allele) (deme : Deme)
    (score outcome : FullHaplotype Locus Allele → ℝ) :
    expectedCalibrationSlope (historyEventKernel ℓ₀ hap₀ []) x0 deme score outcome
      = (stateLaw x0 deme).covariance score outcome / (stateLaw x0 deme).variance score := by
  rw [expectedCalibrationSlope,
    integral_covariance_historyEventKernel_nil ℓ₀ hap₀ x0 deme score outcome,
    integral_variance_historyEventKernel_nil ℓ₀ hap₀ x0 deme score]

/-- **Temporal calibration portability compares a kernel with the empty history.**  It is the
calibration slope of expectations under the kernel over the calibration slope of expectations
under the empty history, both started at `x₀`. -/
theorem temporalCalibrationPortability_eq_div_nil (ℓ₀ : Locus)
    (hap₀ : FullHaplotype Locus Allele)
    (κ : Kernel (FrequencyState Deme Locus Allele) (FrequencyState Deme Locus Allele))
    (x0 : FrequencyState Deme Locus Allele) (deme : Deme)
    (score outcome : FullHaplotype Locus Allele → ℝ) :
    temporalCalibrationPortability κ x0 deme score outcome
      = expectedCalibrationSlope κ x0 deme score outcome
        / expectedCalibrationSlope (historyEventKernel ℓ₀ hap₀ []) x0 deme score outcome := by
  rw [temporalCalibrationPortability,
    expectedCalibrationSlope_historyEventKernel_nil ℓ₀ hap₀ x0 deme score outcome]

/-! ## The law under any process law with dual moments -/

/-- **Temporal covariance portability through the moments.**  Under a Markov kernel with
budget-`n` dual moments along `M`, `n ≥ 2`, the temporal covariance portability is the covariance
coefficient vector dotted with `M · H_n(x₀)`, over the same vector dotted with `H_n(x₀)`.

Assumes: `HasDualMoments κ n M`, the expected budget-`n` moments are `M` applied to the moments of
the initial state. -/
theorem temporalCovariancePortability_eq_dotProduct (ℓ₀ : Locus) {n : ℕ}
    {κ : Kernel (FrequencyState Deme Locus Allele) (FrequencyState Deme Locus Allele)}
    [IsMarkovKernel κ] {M : BudgetMatrix Deme Locus Allele n} (hmoment : HasDualMoments κ n M)
    (hn : 2 ≤ n) (x0 : FrequencyState Deme Locus Allele) (deme : Deme)
    (score outcome : FullHaplotype Locus Allele → ℝ) :
    temporalCovariancePortability κ x0 deme score outcome
      = (budgetCoefficients ℓ₀ (fun _ ↦ n) (demeCovariancePolynomial deme score outcome)
          ⬝ᵥ (M *ᵥ budgetMomentFeature (fun _ ↦ n) x0))
        / (budgetCoefficients ℓ₀ (fun _ ↦ n) (demeCovariancePolynomial deme score outcome)
          ⬝ᵥ budgetMomentFeature (fun _ ↦ n) x0) := by
  rw [temporalCovariancePortability,
    EndToEndCalibrationLaw.integral_covariance_eq_dotProduct ℓ₀ κ M hmoment hn x0 deme score
      outcome,
    presentCovariance_eq_dotProduct ℓ₀ hn x0 deme score outcome]

/-- **Temporal calibration portability through the moments.**  Under a Markov kernel with
budget-`n` dual moments along `M`, `n ≥ 2`, the temporal calibration portability is the rational
calibration slope of `M · H_n(x₀)` over the rational calibration slope of `H_n(x₀)`.

Assumes: `HasDualMoments κ n M`, the expected budget-`n` moments are `M` applied to the moments of
the initial state. -/
theorem temporalCalibrationPortability_eq_momentCalibrationSlope (ℓ₀ : Locus) {n : ℕ}
    {κ : Kernel (FrequencyState Deme Locus Allele) (FrequencyState Deme Locus Allele)}
    [IsMarkovKernel κ] {M : BudgetMatrix Deme Locus Allele n} (hmoment : HasDualMoments κ n M)
    (hn : 2 ≤ n) (x0 : FrequencyState Deme Locus Allele) (deme : Deme)
    (score outcome : FullHaplotype Locus Allele → ℝ) :
    temporalCalibrationPortability κ x0 deme score outcome
      = momentCalibrationSlope ℓ₀ n deme score outcome (M *ᵥ budgetMomentFeature (fun _ ↦ n) x0)
        / momentCalibrationSlope ℓ₀ n deme score outcome (budgetMomentFeature (fun _ ↦ n) x0) := by
  rw [temporalCalibrationPortability,
    expectedCalibrationSlope_eq_momentCalibrationSlope ℓ₀ κ M hmoment hn x0 deme score outcome,
    presentCalibrationSlope_eq_momentCalibrationSlope ℓ₀ hn x0 deme score outcome]

/-- **Temporal accuracy portability through the moments.**  Under a Markov kernel with budget-4
dual moments along `M`, the temporal accuracy portability is a rational function whose numerator
and denominator coefficient vectors meet `M · H₄(x₀)` after the history and `H₄(x₀)` at the
present state.

Assumes: `HasDualMoments κ 4 M`, the expected budget-4 moments are `M` applied to the moments of
the initial state. -/
theorem temporalAccuracyPortability_eq_dotProduct (ℓ₀ : Locus)
    {κ : Kernel (FrequencyState Deme Locus Allele) (FrequencyState Deme Locus Allele)}
    [IsMarkovKernel κ] {M : BudgetMatrix Deme Locus Allele 4} (hmoment : HasDualMoments κ 4 M)
    (x0 : FrequencyState Deme Locus Allele) (deme : Deme)
    (score outcome : FullHaplotype Locus Allele → ℝ) :
    temporalAccuracyPortability κ x0 deme score outcome
      = ((budgetCoefficients ℓ₀ (fun _ ↦ 4) (numeratorPolynomial deme score outcome)
            ⬝ᵥ (M *ᵥ budgetMomentFeature (fun _ ↦ 4) x0))
          * (budgetCoefficients ℓ₀ (fun _ ↦ 4) (denominatorPolynomial deme score outcome)
            ⬝ᵥ budgetMomentFeature (fun _ ↦ 4) x0))
        / ((budgetCoefficients ℓ₀ (fun _ ↦ 4) (denominatorPolynomial deme score outcome)
            ⬝ᵥ (M *ᵥ budgetMomentFeature (fun _ ↦ 4) x0))
          * (budgetCoefficients ℓ₀ (fun _ ↦ 4) (numeratorPolynomial deme score outcome)
            ⬝ᵥ budgetMomentFeature (fun _ ↦ 4) x0)) := by
  rw [temporalAccuracyPortability,
    EndToEndCalibrationLaw.integral_eq_dotProduct_of_totalDegree_le ℓ₀ κ M hmoment _
      (totalDegree_numeratorPolynomial_le deme score outcome) _
      (polynomialFunction_numeratorPolynomial deme score outcome) x0,
    EndToEndCalibrationLaw.integral_eq_dotProduct_of_totalDegree_le ℓ₀ κ M hmoment _
      (totalDegree_denominatorPolynomial_le deme score outcome) _
      (polynomialFunction_denominatorPolynomial deme score outcome) x0,
    presentCorrelationNumerator_eq_dotProduct ℓ₀ x0 deme score outcome,
    presentCorrelationDenominator_eq_dotProduct ℓ₀ x0 deme score outcome]

/-! ## The law along a history of epochs, splits and pulses -/

/-- **The end-to-end temporal covariance law along a history.**  For every budget `n ≥ 2`, the
temporal covariance portability is the covariance coefficient vector dotted with the chronological
propagator applied to `H_n(x₀)`, over the same vector dotted with `H_n(x₀)`. -/
theorem temporalCovariancePortability_historyEventKernel (ℓ₀ : Locus)
    (hap₀ : FullHaplotype Locus Allele)
    (events : List ((NeutralRates Deme Locus Allele × ℝ≥0) ⊕ PulseMatrix Deme)) {n : ℕ}
    (hn : 2 ≤ n) (x0 : FrequencyState Deme Locus Allele) (deme : Deme)
    (score outcome : FullHaplotype Locus Allele → ℝ) :
    temporalCovariancePortability (historyEventKernel ℓ₀ hap₀ events) x0 deme score outcome
      = (budgetCoefficients ℓ₀ (fun _ ↦ n) (demeCovariancePolynomial deme score outcome)
          ⬝ᵥ (historyEventPropagator (fun _ ↦ n) events *ᵥ budgetMomentFeature (fun _ ↦ n) x0))
        / (budgetCoefficients ℓ₀ (fun _ ↦ n) (demeCovariancePolynomial deme score outcome)
          ⬝ᵥ budgetMomentFeature (fun _ ↦ n) x0) :=
  temporalCovariancePortability_eq_dotProduct ℓ₀
    (hasDualMoments_historyEventKernel ℓ₀ hap₀ events n) hn x0 deme score outcome

/-- **The end-to-end temporal calibration law along a history.**  For every budget `n ≥ 2`, the
temporal calibration portability is the rational calibration slope of the chronological propagator
applied to `H_n(x₀)`, over the rational calibration slope of `H_n(x₀)`. -/
theorem temporalCalibrationPortability_historyEventKernel (ℓ₀ : Locus)
    (hap₀ : FullHaplotype Locus Allele)
    (events : List ((NeutralRates Deme Locus Allele × ℝ≥0) ⊕ PulseMatrix Deme)) {n : ℕ}
    (hn : 2 ≤ n) (x0 : FrequencyState Deme Locus Allele) (deme : Deme)
    (score outcome : FullHaplotype Locus Allele → ℝ) :
    temporalCalibrationPortability (historyEventKernel ℓ₀ hap₀ events) x0 deme score outcome
      = momentCalibrationSlope ℓ₀ n deme score outcome
          (historyEventPropagator (fun _ ↦ n) events *ᵥ budgetMomentFeature (fun _ ↦ n) x0)
        / momentCalibrationSlope ℓ₀ n deme score outcome (budgetMomentFeature (fun _ ↦ n) x0) :=
  temporalCalibrationPortability_eq_momentCalibrationSlope ℓ₀
    (hasDualMoments_historyEventKernel ℓ₀ hap₀ events n) hn x0 deme score outcome

/-- **The end-to-end temporal accuracy law along a history.**  The temporal accuracy portability
is a rational function of the chronological propagator applied to `H₄(x₀)` and of `H₄(x₀)`. -/
theorem temporalAccuracyPortability_historyEventKernel (ℓ₀ : Locus)
    (hap₀ : FullHaplotype Locus Allele)
    (events : List ((NeutralRates Deme Locus Allele × ℝ≥0) ⊕ PulseMatrix Deme))
    (x0 : FrequencyState Deme Locus Allele) (deme : Deme)
    (score outcome : FullHaplotype Locus Allele → ℝ) :
    temporalAccuracyPortability (historyEventKernel ℓ₀ hap₀ events) x0 deme score outcome
      = ((budgetCoefficients ℓ₀ (fun _ ↦ 4) (numeratorPolynomial deme score outcome)
            ⬝ᵥ (historyEventPropagator (fun _ ↦ 4) events *ᵥ budgetMomentFeature (fun _ ↦ 4) x0))
          * (budgetCoefficients ℓ₀ (fun _ ↦ 4) (denominatorPolynomial deme score outcome)
            ⬝ᵥ budgetMomentFeature (fun _ ↦ 4) x0))
        / ((budgetCoefficients ℓ₀ (fun _ ↦ 4) (denominatorPolynomial deme score outcome)
            ⬝ᵥ (historyEventPropagator (fun _ ↦ 4) events *ᵥ budgetMomentFeature (fun _ ↦ 4) x0))
          * (budgetCoefficients ℓ₀ (fun _ ↦ 4) (numeratorPolynomial deme score outcome)
            ⬝ᵥ budgetMomentFeature (fun _ ↦ 4) x0)) :=
  temporalAccuracyPortability_eq_dotProduct ℓ₀
    (hasDualMoments_historyEventKernel ℓ₀ hap₀ events 4) x0 deme score outcome

/-! ## The law along a time-varying rate history -/

/-- **The end-to-end temporal covariance law along a rate history**, at every budget `n ≥ 2`.

Assumes: the dual generator path is continuous on `[0, T]`. -/
theorem temporalCovariancePortability_rateHistoryKernel
    {rates : ℝ → NeutralRates Deme Locus Allele} {T : ℝ} (hT : 0 ≤ T)
    (hcontinuous : ∀ capacity : Locus → ℕ,
      ContinuousOn (fun t ↦ dualGenerator (rates t) capacity) (Set.Icc 0 T))
    (ℓ₀ : Locus) (hap₀ : FullHaplotype Locus Allele) {n : ℕ} (hn : 2 ≤ n)
    (x0 : FrequencyState Deme Locus Allele) (deme : Deme)
    (score outcome : FullHaplotype Locus Allele → ℝ) :
    temporalCovariancePortability (rateHistoryKernel rates ℓ₀ hap₀ hT hcontinuous) x0 deme score
        outcome
      = (budgetCoefficients ℓ₀ (fun _ ↦ n) (demeCovariancePolynomial deme score outcome)
          ⬝ᵥ (rateHistoryDualPropagator rates (fun _ ↦ n) T
            *ᵥ budgetMomentFeature (fun _ ↦ n) x0))
        / (budgetCoefficients ℓ₀ (fun _ ↦ n) (demeCovariancePolynomial deme score outcome)
          ⬝ᵥ budgetMomentFeature (fun _ ↦ n) x0) :=
  temporalCovariancePortability_eq_dotProduct ℓ₀
    (hasDualMoments_rateHistoryKernel hT hcontinuous ℓ₀ hap₀ n) hn x0 deme score outcome

/-- **The end-to-end temporal calibration law along a rate history**, at every budget `n ≥ 2`.

Assumes: the dual generator path is continuous on `[0, T]`. -/
theorem temporalCalibrationPortability_rateHistoryKernel
    {rates : ℝ → NeutralRates Deme Locus Allele} {T : ℝ} (hT : 0 ≤ T)
    (hcontinuous : ∀ capacity : Locus → ℕ,
      ContinuousOn (fun t ↦ dualGenerator (rates t) capacity) (Set.Icc 0 T))
    (ℓ₀ : Locus) (hap₀ : FullHaplotype Locus Allele) {n : ℕ} (hn : 2 ≤ n)
    (x0 : FrequencyState Deme Locus Allele) (deme : Deme)
    (score outcome : FullHaplotype Locus Allele → ℝ) :
    temporalCalibrationPortability (rateHistoryKernel rates ℓ₀ hap₀ hT hcontinuous) x0 deme score
        outcome
      = momentCalibrationSlope ℓ₀ n deme score outcome
          (rateHistoryDualPropagator rates (fun _ ↦ n) T *ᵥ budgetMomentFeature (fun _ ↦ n) x0)
        / momentCalibrationSlope ℓ₀ n deme score outcome (budgetMomentFeature (fun _ ↦ n) x0) :=
  temporalCalibrationPortability_eq_momentCalibrationSlope ℓ₀
    (hasDualMoments_rateHistoryKernel hT hcontinuous ℓ₀ hap₀ n) hn x0 deme score outcome

/-- **The end-to-end temporal accuracy law along a rate history.**

Assumes: the dual generator path is continuous on `[0, T]`. -/
theorem temporalAccuracyPortability_rateHistoryKernel
    {rates : ℝ → NeutralRates Deme Locus Allele} {T : ℝ} (hT : 0 ≤ T)
    (hcontinuous : ∀ capacity : Locus → ℕ,
      ContinuousOn (fun t ↦ dualGenerator (rates t) capacity) (Set.Icc 0 T))
    (ℓ₀ : Locus) (hap₀ : FullHaplotype Locus Allele) (x0 : FrequencyState Deme Locus Allele)
    (deme : Deme) (score outcome : FullHaplotype Locus Allele → ℝ) :
    temporalAccuracyPortability (rateHistoryKernel rates ℓ₀ hap₀ hT hcontinuous) x0 deme score
        outcome
      = ((budgetCoefficients ℓ₀ (fun _ ↦ 4) (numeratorPolynomial deme score outcome)
            ⬝ᵥ (rateHistoryDualPropagator rates (fun _ ↦ 4) T
              *ᵥ budgetMomentFeature (fun _ ↦ 4) x0))
          * (budgetCoefficients ℓ₀ (fun _ ↦ 4) (denominatorPolynomial deme score outcome)
            ⬝ᵥ budgetMomentFeature (fun _ ↦ 4) x0))
        / ((budgetCoefficients ℓ₀ (fun _ ↦ 4) (denominatorPolynomial deme score outcome)
            ⬝ᵥ (rateHistoryDualPropagator rates (fun _ ↦ 4) T
              *ᵥ budgetMomentFeature (fun _ ↦ 4) x0))
          * (budgetCoefficients ℓ₀ (fun _ ↦ 4) (numeratorPolynomial deme score outcome)
            ⬝ᵥ budgetMomentFeature (fun _ ↦ 4) x0)) :=
  temporalAccuracyPortability_eq_dotProduct ℓ₀
    (hasDualMoments_rateHistoryKernel hT hcontinuous ℓ₀ hap₀ 4) x0 deme score outcome

/-! ## Temporal portability sees the history through one matrix -/

/-- **Equal propagated budget-2 moments, equal temporal portability.**  Two histories that carry
the budget-2 configuration moments of the present state `x₀` to one vector give every deme, score
and outcome the same temporal covariance and calibration portability from `x₀`.

Assumes: `MomentsAgreeAt 2 first second x0 x0`. -/
theorem temporalPortability_eq_of_momentsAgreeAt_two (ℓ₀ : Locus)
    (hap₀ : FullHaplotype Locus Allele)
    {first second : List ((NeutralRates Deme Locus Allele × ℝ≥0) ⊕ PulseMatrix Deme)}
    {x0 : FrequencyState Deme Locus Allele} (hmoments : MomentsAgreeAt 2 first second x0 x0)
    (deme : Deme) (score outcome : FullHaplotype Locus Allele → ℝ) :
    temporalCovariancePortability (historyEventKernel ℓ₀ hap₀ first) x0 deme score outcome
        = temporalCovariancePortability (historyEventKernel ℓ₀ hap₀ second) x0 deme score outcome
      ∧ temporalCalibrationPortability (historyEventKernel ℓ₀ hap₀ first) x0 deme score outcome
        = temporalCalibrationPortability (historyEventKernel ℓ₀ hap₀ second) x0 deme score
          outcome := by
  rw [MomentsAgreeAt] at hmoments
  rw [temporalCovariancePortability_historyEventKernel ℓ₀ hap₀ first (n := 2) le_rfl,
    temporalCovariancePortability_historyEventKernel ℓ₀ hap₀ second (n := 2) le_rfl,
    temporalCalibrationPortability_historyEventKernel ℓ₀ hap₀ first (n := 2) le_rfl,
    temporalCalibrationPortability_historyEventKernel ℓ₀ hap₀ second (n := 2) le_rfl, hmoments]
  exact ⟨rfl, rfl⟩

/-- **Temporal portability depends on the history only through one matrix.**  Two histories with
equal budget-2 propagators give every present state, deme, score and outcome the same temporal
covariance and calibration portability.

Assumes: the budget-2 propagators of the two histories are equal. -/
theorem temporalPortability_eq_of_propagator_eq (ℓ₀ : Locus) (hap₀ : FullHaplotype Locus Allele)
    {first second : List ((NeutralRates Deme Locus Allele × ℝ≥0) ⊕ PulseMatrix Deme)}
    (hpropagator : historyEventPropagator (fun _ ↦ 2) first
      = historyEventPropagator (fun _ ↦ 2) second)
    (x0 : FrequencyState Deme Locus Allele) (deme : Deme)
    (score outcome : FullHaplotype Locus Allele → ℝ) :
    temporalCovariancePortability (historyEventKernel ℓ₀ hap₀ first) x0 deme score outcome
        = temporalCovariancePortability (historyEventKernel ℓ₀ hap₀ second) x0 deme score outcome
      ∧ temporalCalibrationPortability (historyEventKernel ℓ₀ hap₀ first) x0 deme score outcome
        = temporalCalibrationPortability (historyEventKernel ℓ₀ hap₀ second) x0 deme score
          outcome :=
  temporalPortability_eq_of_momentsAgreeAt_two ℓ₀ hap₀
    (by rw [MomentsAgreeAt, hpropagator]) deme score outcome

/-- **Accuracy climbs one rung.**  Two histories that carry the budget-4 configuration moments of
the present state `x₀` to one vector give every deme, score and outcome the same temporal accuracy
portability from `x₀`.

Assumes: `MomentsAgreeAt 4 first second x0 x0`. -/
theorem temporalAccuracyPortability_eq_of_momentsAgreeAt_four (ℓ₀ : Locus)
    (hap₀ : FullHaplotype Locus Allele)
    {first second : List ((NeutralRates Deme Locus Allele × ℝ≥0) ⊕ PulseMatrix Deme)}
    {x0 : FrequencyState Deme Locus Allele} (hmoments : MomentsAgreeAt 4 first second x0 x0)
    (deme : Deme) (score outcome : FullHaplotype Locus Allele → ℝ) :
    temporalAccuracyPortability (historyEventKernel ℓ₀ hap₀ first) x0 deme score outcome
      = temporalAccuracyPortability (historyEventKernel ℓ₀ hap₀ second) x0 deme score outcome := by
  rw [MomentsAgreeAt] at hmoments
  rw [temporalAccuracyPortability_historyEventKernel ℓ₀ hap₀ first,
    temporalAccuracyPortability_historyEventKernel ℓ₀ hap₀ second, hmoments]

/-! ## Temporal portability at `T = 0` -/

/-- **Identity dual moments keep the covariance portable to itself.**

Assumes: `HasDualMoments κ n 1`, the kernel leaves the expected budget-`n` moments at those of the
initial state; the covariance at `x₀` is nonzero. -/
theorem temporalCovariancePortability_eq_one_of_hasDualMoments_one (ℓ₀ : Locus) {n : ℕ}
    {κ : Kernel (FrequencyState Deme Locus Allele) (FrequencyState Deme Locus Allele)}
    [IsMarkovKernel κ] (hmoment : HasDualMoments κ n 1) (hn : 2 ≤ n)
    {x0 : FrequencyState Deme Locus Allele} {deme : Deme}
    {score outcome : FullHaplotype Locus Allele → ℝ}
    (hcovariance : (stateLaw x0 deme).covariance score outcome ≠ 0) :
    temporalCovariancePortability κ x0 deme score outcome = 1 := by
  rw [temporalCovariancePortability_eq_dotProduct ℓ₀ hmoment hn, Matrix.one_mulVec,
    ← presentCovariance_eq_dotProduct ℓ₀ hn x0 deme score outcome]
  exact div_self hcovariance

/-- **Identity dual moments keep the calibration slope portable to itself.**

Assumes: `HasDualMoments κ n 1`, the kernel leaves the expected budget-`n` moments at those of the
initial state; the covariance and the score variance at `x₀` are nonzero. -/
theorem temporalCalibrationPortability_eq_one_of_hasDualMoments_one (ℓ₀ : Locus) {n : ℕ}
    {κ : Kernel (FrequencyState Deme Locus Allele) (FrequencyState Deme Locus Allele)}
    [IsMarkovKernel κ] (hmoment : HasDualMoments κ n 1) (hn : 2 ≤ n)
    {x0 : FrequencyState Deme Locus Allele} {deme : Deme}
    {score outcome : FullHaplotype Locus Allele → ℝ}
    (hcovariance : (stateLaw x0 deme).covariance score outcome ≠ 0)
    (hvariance : (stateLaw x0 deme).variance score ≠ 0) :
    temporalCalibrationPortability κ x0 deme score outcome = 1 := by
  rw [temporalCalibrationPortability_eq_momentCalibrationSlope ℓ₀ hmoment hn, Matrix.one_mulVec,
    ← presentCalibrationSlope_eq_momentCalibrationSlope ℓ₀ hn x0 deme score outcome]
  exact div_self (div_ne_zero hcovariance hvariance)

/-- **Identity dual moments keep the squared correlation portable to itself.**

Assumes: `HasDualMoments κ 4 1`, the kernel leaves the expected budget-4 moments at those of the
initial state; the correlation numerator and denominator at `x₀` are nonzero. -/
theorem temporalAccuracyPortability_eq_one_of_hasDualMoments_one (ℓ₀ : Locus)
    {κ : Kernel (FrequencyState Deme Locus Allele) (FrequencyState Deme Locus Allele)}
    [IsMarkovKernel κ] (hmoment : HasDualMoments κ 4 1)
    {x0 : FrequencyState Deme Locus Allele} {deme : Deme}
    {score outcome : FullHaplotype Locus Allele → ℝ}
    (hnumerator : correlationNumerator (stateLaw x0 deme) score outcome ≠ 0)
    (hdenominator : correlationDenominator (stateLaw x0 deme) score outcome ≠ 0) :
    temporalAccuracyPortability κ x0 deme score outcome = 1 := by
  rw [temporalAccuracyPortability_eq_dotProduct ℓ₀ hmoment, Matrix.one_mulVec,
    ← presentCorrelationNumerator_eq_dotProduct ℓ₀ x0 deme score outcome,
    ← presentCorrelationDenominator_eq_dotProduct ℓ₀ x0 deme score outcome,
    mul_comm (correlationNumerator (stateLaw x0 deme) score outcome)]
  exact div_self (mul_ne_zero hdenominator hnumerator)

/-- **An epoch of zero duration has the identity as its dual moments**, at every budget: its
propagator is the matrix exponential of the dual generator at time zero. -/
theorem hasDualMoments_historyEventKernel_zeroEpoch (ℓ₀ : Locus)
    (hap₀ : FullHaplotype Locus Allele) (rates : NeutralRates Deme Locus Allele) (n : ℕ) :
    HasDualMoments (historyEventKernel ℓ₀ hap₀ [Sum.inl (rates, 0)]) n 1 := by
  have h := hasDualMoments_historyEventKernel ℓ₀ hap₀ [Sum.inl (rates, 0)] n
  simp only [historyEventPropagator, eventPropagator, NNReal.coe_zero, matrixExponential_zero,
    one_mul] at h
  exact h

/-- **Temporal portability at `T = 0` is one.**  After an epoch of zero duration, the temporal
covariance and calibration portability of a deme from its present state are one.

Assumes: the covariance and the score variance at `x₀` are nonzero. -/
theorem temporalPortability_zeroEpoch (ℓ₀ : Locus) (hap₀ : FullHaplotype Locus Allele)
    (rates : NeutralRates Deme Locus Allele) {x0 : FrequencyState Deme Locus Allele} {deme : Deme}
    {score outcome : FullHaplotype Locus Allele → ℝ}
    (hcovariance : (stateLaw x0 deme).covariance score outcome ≠ 0)
    (hvariance : (stateLaw x0 deme).variance score ≠ 0) :
    temporalCovariancePortability (historyEventKernel ℓ₀ hap₀ [Sum.inl (rates, 0)]) x0 deme score
        outcome = 1
      ∧ temporalCalibrationPortability (historyEventKernel ℓ₀ hap₀ [Sum.inl (rates, 0)]) x0 deme
        score outcome = 1 :=
  ⟨temporalCovariancePortability_eq_one_of_hasDualMoments_one ℓ₀
      (hasDualMoments_historyEventKernel_zeroEpoch ℓ₀ hap₀ rates 2) le_rfl hcovariance,
    temporalCalibrationPortability_eq_one_of_hasDualMoments_one ℓ₀
      (hasDualMoments_historyEventKernel_zeroEpoch ℓ₀ hap₀ rates 2) le_rfl hcovariance hvariance⟩

end

end Descent.Portability.EndToEndTemporalPortability
