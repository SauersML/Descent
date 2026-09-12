/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.EndToEndSensitivityLaw
import Descent.Portability.EndToEndCalibrationLaw
import Descent.Portability.EndToEndDiscriminationLaw

assert_below Descent.Decision Descent.Program

/-!
# The exact sensitivity of accuracy, calibration and AUC portability to demography

`EndToEndSensitivityLaw` differentiates `c · U(θ) v` for a parametrized history of epochs, splits
and pulses: the derivative is the stagewise sum `historySensitivity` of forward law, event
derivative and backward value, with the Duhamel integral as the derivative of each epoch.  This
module carries that derivative to the end-to-end metrics.

Expectations.  Under the history kernel every expected metric numerator and denominator of
`EndToEndPortabilityLaw`, `EndToEndCalibrationLaw` and `EndToEndDiscriminationLaw` is a
coefficient vector dotted with the propagated moments, so its derivative in the parameter is the
same coefficient vector paired with the propagated derivative
(`hasDerivAt_of_eq_dotProduct`, `hasDerivAt_integral_polynomial_historyEventKernel`).  This gives
the exact derivatives of `E N` and `E D` of the squared correlation at budget 4
(`hasDerivAt_integral_correlationNumerator_historyEventKernel`,
`hasDerivAt_integral_correlationDenominator_historyEventKernel`), of the expected covariance and
score variance at every budget `n ≥ 2` (`hasDerivAt_integral_covariance_historyEventKernel`,
`hasDerivAt_integral_variance_historyEventKernel`), and of the expected AUC numerator and
denominator at budget 2 (`hasDerivAt_integral_aucNumerator_historyEventKernel`,
`hasDerivAt_integral_aucDenominator_historyEventKernel`).

Portability.  Each portability of expectations is a cross ratio `a b / (c d)` of four such
expectations, so its derivative is the explicit rational expression `crossRatioDerivative` of the
four values and the four sensitivities, wherever `c d ≠ 0` (`hasDerivAt_crossRatio`).  This is
the derivative of the expected squared-correlation portability
(`hasDerivAt_expectedPortability_historyEventKernel`), of the calibration slope and calibration
portability (`hasDerivAt_expectedCalibrationSlope_historyEventKernel`,
`hasDerivAt_expectedCalibrationPortability_historyEventKernel`) and of the AUC portability
(`hasDerivAt_expectedAUCPortability_historyEventKernel`).

The sign criterion.  The derivative is negative exactly when
`(a' b + a b') (c d) < a b (c' d + c d')` (`crossRatioDerivative_neg_iff`), a form bilinear in each
pair of a value and its sensitivity.  With positive expectations it is the portability times the
difference of relative sensitivities (`crossRatioDerivative_eq_mul`).  For the squared correlation
the portability `(N_t / D_t) / (N_s / D_s)` therefore decreases in the parameter exactly when the
relative sensitivity of the target accuracy, `N_t'/N_t - D_t'/D_t`, is below that of the source,
`N_s'/N_s - D_s'/D_s` (`crossRatioDerivative_neg_iff_of_pos`).

Scope.  The metrics are the ratio-of-expectations queries of NOTE2 §6.2 carried by the corpus end
to end laws; the expected squared correlation `E[N/D]` and the expected AUC, which are series, are
not differentiated.  The parameter enters through the event propagators under the hypotheses of
`EndToEndSensitivityLaw`.

## Empirical status

None.  The bodies here are derivatives of finite pairings of supplied coefficient vectors with
propagated moments and of rational functions of them, so no measurement can bear on them.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.EndToEndSensitivityMetrics

open MeasureTheory ProbabilityTheory MvPolynomial Descent.Coalescent PartialHaplotypeCarrier
  PartialHaplotypeDualGenerator PartialHaplotypeDualSemigroup NeutralFellerGenerator
  NeutralPolynomialSemigroup PartialHaplotypeMicroscopicApproximation PartialHaplotypePulseKernel
  NeutralPulseHistoryKernel ReplicaMetricInstances EndToEndPortabilityLaw EndToEndCalibrationLaw
  EndToEndDiscriminationLaw EndToEndSensitivityLaw
open scoped Matrix NNReal

noncomputable section

/-! ## Cross ratios -/

section CrossRatio

/-- **The derivative of a cross ratio** `a b / (c d)`, from the values and derivatives of its four
factors. -/
def crossRatioDerivative (a b c d a' b' c' d' : ℝ) : ℝ :=
  ((a' * b + a * b') * (c * d) - a * b * (c' * d + c * d')) / (c * d) ^ 2

/-- The quotient rule for a cross ratio. -/
theorem hasDerivAt_crossRatio {a b c d : ℝ → ℝ} {a' b' c' d' x : ℝ} (ha : HasDerivAt a a' x)
    (hb : HasDerivAt b b' x) (hc : HasDerivAt c c' x) (hd : HasDerivAt d d' x)
    (hcd : c x * d x ≠ 0) :
    HasDerivAt (fun θ ↦ a θ * b θ / (c θ * d θ))
      (crossRatioDerivative (a x) (b x) (c x) (d x) a' b' c' d') x :=
  (ha.fun_mul hb).fun_div (hc.fun_mul hd) hcd

/-- **The sign criterion.**  A cross ratio decreases to first order exactly when
`(a' b + a b') (c d) < a b (c' d + c d')`. -/
theorem crossRatioDerivative_neg_iff {a b c d : ℝ} (a' b' c' d' : ℝ) (hcd : c * d ≠ 0) :
    crossRatioDerivative a b c d a' b' c' d' < 0
      ↔ (a' * b + a * b') * (c * d) < a * b * (c' * d + c * d') := by
  have hsquare : 0 < (c * d) ^ 2 := lt_of_le_of_ne (sq_nonneg _) (pow_ne_zero 2 hcd).symm
  rw [crossRatioDerivative, div_lt_iff₀ hsquare, zero_mul, sub_neg]

/-- **The relative form.**  With nonzero factors the derivative of a cross ratio is the cross
ratio times the sum of the relative derivatives of the numerator factors minus those of the
denominator factors. -/
theorem crossRatioDerivative_eq_mul {a b c d : ℝ} (a' b' c' d' : ℝ) (ha : a ≠ 0) (hb : b ≠ 0)
    (hc : c ≠ 0) (hd : d ≠ 0) :
    crossRatioDerivative a b c d a' b' c' d'
      = a * b / (c * d) * (a' / a + b' / b - c' / c - d' / d) := by
  rw [crossRatioDerivative]
  field_simp
  ring

/-- **The sign criterion in relative sensitivities.**  For positive factors, the cross ratio
`(a / c) / (d / b)` decreases to first order exactly when the relative derivative of `a / c` is
below that of `d / b`. -/
theorem crossRatioDerivative_neg_iff_of_pos {a b c d : ℝ} (a' b' c' d' : ℝ) (ha : 0 < a)
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) :
    crossRatioDerivative a b c d a' b' c' d' < 0 ↔ a' / a - c' / c < d' / d - b' / b := by
  have hprefactor : 0 < a * b / (c * d) := by positivity
  rw [crossRatioDerivative_eq_mul a' b' c' d' ha.ne' hb.ne' hc.ne' hd.ne']
  constructor
  · intro hneg
    have hsum : a' / a + b' / b - c' / c - d' / d < 0 := by
      by_contra hnot
      exact absurd hneg (not_lt.mpr (mul_nonneg hprefactor.le (not_lt.mp hnot)))
    linarith
  · intro hlt
    exact mul_neg_of_pos_of_neg hprefactor (by linarith)

end CrossRatio

variable {Deme Locus : Type*} {Allele : Locus → Type*}
variable [Fintype Deme] [DecidableEq Deme] [Fintype Locus] [DecidableEq Locus]
  [∀ ℓ, Fintype (Allele ℓ)] [∀ ℓ, DecidableEq (Allele ℓ)]

/-! ## Propagated expectations -/

/-- **A propagated pairing has the stagewise sensitivity as derivative.**  A function equal at
every parameter to `c · U(θ) v`, with `U(θ)` the propagator of a parametrized history whose event
propagators have derivatives `derivative event` at `θ₀`, has derivative `historySensitivity` at
`θ₀`. -/
theorem hasDerivAt_of_eq_dotProduct {capacity : Locus → ℕ} {θ₀ : ℝ}
    (history : List (ℝ → ((NeutralRates Deme Locus Allele × ℝ≥0) ⊕ PulseMatrix Deme)))
    (derivative : (ℝ → ((NeutralRates Deme Locus Allele × ℝ≥0) ⊕ PulseMatrix Deme)) →
      Matrix (BudgetConfiguration Deme Locus Allele capacity)
        (BudgetConfiguration Deme Locus Allele capacity) ℝ)
    (hderivative : ∀ event ∈ history, ∀ ξ η,
      HasDerivAt (fun θ ↦ eventPropagator capacity (event θ) ξ η) (derivative event ξ η) θ₀)
    {F : ℝ → ℝ} (c v : BudgetConfiguration Deme Locus Allele capacity → ℝ)
    (hF : ∀ θ, F θ = c ⬝ᵥ
      (historyEventPropagator capacity (history.map fun event ↦ event θ) *ᵥ v)) :
    HasDerivAt F (historySensitivity capacity θ₀ history derivative c v) θ₀ := by
  rw [show F = _ from funext hF]
  exact hasDerivAt_dotProduct_historyEventPropagator capacity history derivative hderivative c v

/-- **The derivative of an expected frequency polynomial along a parametrized history.**  For a
polynomial whose monomials lie in the budget, the expected polynomial under the history kernel
has derivative the stagewise sensitivity of its coefficient vector against the initial moments. -/
theorem hasDerivAt_integral_polynomial_historyEventKernel (ℓ₀ : Locus)
    (hap₀ : FullHaplotype Locus Allele) {capacity : Locus → ℕ} {θ₀ : ℝ}
    (history : List (ℝ → ((NeutralRates Deme Locus Allele × ℝ≥0) ⊕ PulseMatrix Deme)))
    (derivative : (ℝ → ((NeutralRates Deme Locus Allele × ℝ≥0) ⊕ PulseMatrix Deme)) →
      Matrix (BudgetConfiguration Deme Locus Allele capacity)
        (BudgetConfiguration Deme Locus Allele capacity) ℝ)
    (hderivative : ∀ event ∈ history, ∀ ξ η,
      HasDerivAt (fun θ ↦ eventPropagator capacity (event θ) ξ η) (derivative event ξ η) θ₀)
    (p : FrequencyPolynomial Deme Locus Allele)
    (hp : ∀ β ∈ p.support, WithinBudget capacity (monomialConfiguration ℓ₀ β))
    (x0 : FrequencyState Deme Locus Allele) :
    HasDerivAt (fun θ ↦ ∫ y, polynomialFunction p y
        ∂(historyEventKernel ℓ₀ hap₀ (history.map fun event ↦ event θ) x0))
      (historySensitivity capacity θ₀ history derivative (budgetCoefficients ℓ₀ capacity p)
        (budgetMomentFeature capacity x0)) θ₀ :=
  hasDerivAt_of_eq_dotProduct history derivative hderivative _ _ fun θ ↦ by
    haveI := isMarkovKernel_historyEventKernel ℓ₀ hap₀ (history.map fun event ↦ event θ)
    exact integral_polynomial_eq_dotProduct ℓ₀ capacity _ _
      (integral_momentPolynomial_historyEventKernel ℓ₀ hap₀ capacity _) p hp x0

/-- **The sensitivity of the expected squared-correlation numerator** `E N` of a deme. -/
theorem hasDerivAt_integral_correlationNumerator_historyEventKernel (ℓ₀ : Locus)
    (hap₀ : FullHaplotype Locus Allele) {θ₀ : ℝ}
    (history : List (ℝ → ((NeutralRates Deme Locus Allele × ℝ≥0) ⊕ PulseMatrix Deme)))
    (derivative : (ℝ → ((NeutralRates Deme Locus Allele × ℝ≥0) ⊕ PulseMatrix Deme)) →
      BudgetMatrix Deme Locus Allele 4)
    (hderivative : ∀ event ∈ history, ∀ ξ η, HasDerivAt
      (fun θ ↦ eventPropagator (fun _ ↦ 4) (event θ) ξ η) (derivative event ξ η) θ₀)
    (x0 : FrequencyState Deme Locus Allele) (deme : Deme)
    (score outcome : FullHaplotype Locus Allele → ℝ) :
    HasDerivAt (fun θ ↦ ∫ y, correlationNumerator (stateLaw y deme) score outcome
        ∂(historyEventKernel ℓ₀ hap₀ (history.map fun event ↦ event θ) x0))
      (historySensitivity (fun _ ↦ 4) θ₀ history derivative
        (budgetCoefficients ℓ₀ (fun _ ↦ 4) (numeratorPolynomial deme score outcome))
        (budgetMomentFeature (fun _ ↦ 4) x0)) θ₀ :=
  hasDerivAt_of_eq_dotProduct history derivative hderivative _ _ fun _ ↦
    integral_correlationNumerator_historyEventKernel ℓ₀ hap₀ _ x0 deme score outcome

/-- **The sensitivity of the expected squared-correlation denominator** `E D` of a deme. -/
theorem hasDerivAt_integral_correlationDenominator_historyEventKernel (ℓ₀ : Locus)
    (hap₀ : FullHaplotype Locus Allele) {θ₀ : ℝ}
    (history : List (ℝ → ((NeutralRates Deme Locus Allele × ℝ≥0) ⊕ PulseMatrix Deme)))
    (derivative : (ℝ → ((NeutralRates Deme Locus Allele × ℝ≥0) ⊕ PulseMatrix Deme)) →
      BudgetMatrix Deme Locus Allele 4)
    (hderivative : ∀ event ∈ history, ∀ ξ η, HasDerivAt
      (fun θ ↦ eventPropagator (fun _ ↦ 4) (event θ) ξ η) (derivative event ξ η) θ₀)
    (x0 : FrequencyState Deme Locus Allele) (deme : Deme)
    (score outcome : FullHaplotype Locus Allele → ℝ) :
    HasDerivAt (fun θ ↦ ∫ y, correlationDenominator (stateLaw y deme) score outcome
        ∂(historyEventKernel ℓ₀ hap₀ (history.map fun event ↦ event θ) x0))
      (historySensitivity (fun _ ↦ 4) θ₀ history derivative
        (budgetCoefficients ℓ₀ (fun _ ↦ 4) (denominatorPolynomial deme score outcome))
        (budgetMomentFeature (fun _ ↦ 4) x0)) θ₀ :=
  hasDerivAt_of_eq_dotProduct history derivative hderivative _ _ fun _ ↦
    integral_correlationDenominator_historyEventKernel ℓ₀ hap₀ _ x0 deme score outcome

/-- **The sensitivity of an expected deme covariance**, at every budget `n ≥ 2`. -/
theorem hasDerivAt_integral_covariance_historyEventKernel (ℓ₀ : Locus)
    (hap₀ : FullHaplotype Locus Allele) {n : ℕ} (hn : 2 ≤ n) {θ₀ : ℝ}
    (history : List (ℝ → ((NeutralRates Deme Locus Allele × ℝ≥0) ⊕ PulseMatrix Deme)))
    (derivative : (ℝ → ((NeutralRates Deme Locus Allele × ℝ≥0) ⊕ PulseMatrix Deme)) →
      BudgetMatrix Deme Locus Allele n)
    (hderivative : ∀ event ∈ history, ∀ ξ η, HasDerivAt
      (fun θ ↦ eventPropagator (fun _ ↦ n) (event θ) ξ η) (derivative event ξ η) θ₀)
    (x0 : FrequencyState Deme Locus Allele) (deme : Deme)
    (first second : FullHaplotype Locus Allele → ℝ) :
    HasDerivAt (fun θ ↦ ∫ y, (stateLaw y deme).covariance first second
        ∂(historyEventKernel ℓ₀ hap₀ (history.map fun event ↦ event θ) x0))
      (historySensitivity (fun _ ↦ n) θ₀ history derivative
        (budgetCoefficients ℓ₀ (fun _ ↦ n) (demeCovariancePolynomial deme first second))
        (budgetMomentFeature (fun _ ↦ n) x0)) θ₀ :=
  hasDerivAt_of_eq_dotProduct history derivative hderivative _ _ fun _ ↦
    integral_covariance_historyEventKernel ℓ₀ hap₀ _ hn x0 deme first second

/-- **The sensitivity of an expected deme variance**, at every budget `n ≥ 2`. -/
theorem hasDerivAt_integral_variance_historyEventKernel (ℓ₀ : Locus)
    (hap₀ : FullHaplotype Locus Allele) {n : ℕ} (hn : 2 ≤ n) {θ₀ : ℝ}
    (history : List (ℝ → ((NeutralRates Deme Locus Allele × ℝ≥0) ⊕ PulseMatrix Deme)))
    (derivative : (ℝ → ((NeutralRates Deme Locus Allele × ℝ≥0) ⊕ PulseMatrix Deme)) →
      BudgetMatrix Deme Locus Allele n)
    (hderivative : ∀ event ∈ history, ∀ ξ η, HasDerivAt
      (fun θ ↦ eventPropagator (fun _ ↦ n) (event θ) ξ η) (derivative event ξ η) θ₀)
    (x0 : FrequencyState Deme Locus Allele) (deme : Deme)
    (value : FullHaplotype Locus Allele → ℝ) :
    HasDerivAt (fun θ ↦ ∫ y, (stateLaw y deme).variance value
        ∂(historyEventKernel ℓ₀ hap₀ (history.map fun event ↦ event θ) x0))
      (historySensitivity (fun _ ↦ n) θ₀ history derivative
        (budgetCoefficients ℓ₀ (fun _ ↦ n) (demeCovariancePolynomial deme value value))
        (budgetMomentFeature (fun _ ↦ n) x0)) θ₀ :=
  hasDerivAt_of_eq_dotProduct history derivative hderivative _ _ fun _ ↦
    integral_variance_historyEventKernel ℓ₀ hap₀ _ hn x0 deme value

/-- **The sensitivity of the expected AUC numerator** of a deme, at budget 2. -/
theorem hasDerivAt_integral_aucNumerator_historyEventKernel (ℓ₀ : Locus)
    (hap₀ : FullHaplotype Locus Allele) {θ₀ : ℝ}
    (history : List (ℝ → ((NeutralRates Deme Locus Allele × ℝ≥0) ⊕ PulseMatrix Deme)))
    (derivative : (ℝ → ((NeutralRates Deme Locus Allele × ℝ≥0) ⊕ PulseMatrix Deme)) →
      BudgetMatrix Deme Locus Allele 2)
    (hderivative : ∀ event ∈ history, ∀ ξ η, HasDerivAt
      (fun θ ↦ eventPropagator (fun _ ↦ 2) (event θ) ξ η) (derivative event ξ η) θ₀)
    (x0 : FrequencyState Deme Locus Allele) (deme : Deme)
    (score : FullHaplotype Locus Allele → ℝ) (outcome : FullHaplotype Locus Allele → Bool) :
    HasDerivAt (fun θ ↦ ∫ y, aucNumerator (stateLaw y deme) score outcome
        ∂(historyEventKernel ℓ₀ hap₀ (history.map fun event ↦ event θ) x0))
      (historySensitivity (fun _ ↦ 2) θ₀ history derivative
        (budgetCoefficients ℓ₀ (fun _ ↦ 2)
          (demePolynomial deme (aucNumeratorPolynomial score outcome)))
        (budgetMomentFeature (fun _ ↦ 2) x0)) θ₀ :=
  hasDerivAt_of_eq_dotProduct history derivative hderivative _ _ fun _ ↦
    integral_aucNumerator_historyEventKernel ℓ₀ hap₀ _ x0 deme score outcome

/-- **The sensitivity of the expected AUC denominator** of a deme, at budget 2. -/
theorem hasDerivAt_integral_aucDenominator_historyEventKernel (ℓ₀ : Locus)
    (hap₀ : FullHaplotype Locus Allele) {θ₀ : ℝ}
    (history : List (ℝ → ((NeutralRates Deme Locus Allele × ℝ≥0) ⊕ PulseMatrix Deme)))
    (derivative : (ℝ → ((NeutralRates Deme Locus Allele × ℝ≥0) ⊕ PulseMatrix Deme)) →
      BudgetMatrix Deme Locus Allele 2)
    (hderivative : ∀ event ∈ history, ∀ ξ η, HasDerivAt
      (fun θ ↦ eventPropagator (fun _ ↦ 2) (event θ) ξ η) (derivative event ξ η) θ₀)
    (x0 : FrequencyState Deme Locus Allele) (deme : Deme)
    (outcome : FullHaplotype Locus Allele → Bool) :
    HasDerivAt (fun θ ↦ ∫ y, aucDenominator (stateLaw y deme) outcome
        ∂(historyEventKernel ℓ₀ hap₀ (history.map fun event ↦ event θ) x0))
      (historySensitivity (fun _ ↦ 2) θ₀ history derivative
        (budgetCoefficients ℓ₀ (fun _ ↦ 2)
          (demePolynomial deme (aucDenominatorPolynomial outcome)))
        (budgetMomentFeature (fun _ ↦ 2) x0)) θ₀ :=
  hasDerivAt_of_eq_dotProduct history derivative hderivative _ _ fun _ ↦
    integral_aucDenominator_historyEventKernel ℓ₀ hap₀ _ x0 deme outcome

/-! ## Portability -/

/-- **The exact sensitivity law of expected portability.**  Along a parametrized history, the
portability of expected accuracies `E N_t E D_s / (E D_t E N_s)` has as derivative the cross-ratio
derivative of the four expectations and their four stagewise sensitivities, wherever
`E D_t E N_s ≠ 0`. -/
theorem hasDerivAt_expectedPortability_historyEventKernel (ℓ₀ : Locus)
    (hap₀ : FullHaplotype Locus Allele) {θ₀ : ℝ}
    (history : List (ℝ → ((NeutralRates Deme Locus Allele × ℝ≥0) ⊕ PulseMatrix Deme)))
    (derivative : (ℝ → ((NeutralRates Deme Locus Allele × ℝ≥0) ⊕ PulseMatrix Deme)) →
      BudgetMatrix Deme Locus Allele 4)
    (hderivative : ∀ event ∈ history, ∀ ξ η, HasDerivAt
      (fun θ ↦ eventPropagator (fun _ ↦ 4) (event θ) ξ η) (derivative event ξ η) θ₀)
    (x0 : FrequencyState Deme Locus Allele) (source target : Deme)
    (score outcome : FullHaplotype Locus Allele → ℝ)
    (hdenominator : (∫ y, correlationDenominator (stateLaw y target) score outcome
          ∂(historyEventKernel ℓ₀ hap₀ (history.map fun event ↦ event θ₀) x0))
        * (∫ y, correlationNumerator (stateLaw y source) score outcome
          ∂(historyEventKernel ℓ₀ hap₀ (history.map fun event ↦ event θ₀) x0)) ≠ 0) :
    HasDerivAt (fun θ ↦ expectedPortability
        (historyEventKernel ℓ₀ hap₀ (history.map fun event ↦ event θ)) x0 source target score
        outcome)
      (crossRatioDerivative
        (∫ y, correlationNumerator (stateLaw y target) score outcome
          ∂(historyEventKernel ℓ₀ hap₀ (history.map fun event ↦ event θ₀) x0))
        (∫ y, correlationDenominator (stateLaw y source) score outcome
          ∂(historyEventKernel ℓ₀ hap₀ (history.map fun event ↦ event θ₀) x0))
        (∫ y, correlationDenominator (stateLaw y target) score outcome
          ∂(historyEventKernel ℓ₀ hap₀ (history.map fun event ↦ event θ₀) x0))
        (∫ y, correlationNumerator (stateLaw y source) score outcome
          ∂(historyEventKernel ℓ₀ hap₀ (history.map fun event ↦ event θ₀) x0))
        (historySensitivity (fun _ ↦ 4) θ₀ history derivative
          (budgetCoefficients ℓ₀ (fun _ ↦ 4) (numeratorPolynomial target score outcome))
          (budgetMomentFeature (fun _ ↦ 4) x0))
        (historySensitivity (fun _ ↦ 4) θ₀ history derivative
          (budgetCoefficients ℓ₀ (fun _ ↦ 4) (denominatorPolynomial source score outcome))
          (budgetMomentFeature (fun _ ↦ 4) x0))
        (historySensitivity (fun _ ↦ 4) θ₀ history derivative
          (budgetCoefficients ℓ₀ (fun _ ↦ 4) (denominatorPolynomial target score outcome))
          (budgetMomentFeature (fun _ ↦ 4) x0))
        (historySensitivity (fun _ ↦ 4) θ₀ history derivative
          (budgetCoefficients ℓ₀ (fun _ ↦ 4) (numeratorPolynomial source score outcome))
          (budgetMomentFeature (fun _ ↦ 4) x0))) θ₀ :=
  hasDerivAt_crossRatio
    (hasDerivAt_integral_correlationNumerator_historyEventKernel ℓ₀ hap₀ history derivative
      hderivative x0 target score outcome)
    (hasDerivAt_integral_correlationDenominator_historyEventKernel ℓ₀ hap₀ history derivative
      hderivative x0 source score outcome)
    (hasDerivAt_integral_correlationDenominator_historyEventKernel ℓ₀ hap₀ history derivative
      hderivative x0 target score outcome)
    (hasDerivAt_integral_correlationNumerator_historyEventKernel ℓ₀ hap₀ history derivative
      hderivative x0 source score outcome)
    hdenominator

/-- **The sensitivity of the calibration slope of expectations** `E C_SY / E V_S`, at every
budget `n ≥ 2`, wherever the expected score variance is nonzero. -/
theorem hasDerivAt_expectedCalibrationSlope_historyEventKernel (ℓ₀ : Locus)
    (hap₀ : FullHaplotype Locus Allele) {n : ℕ} (hn : 2 ≤ n) {θ₀ : ℝ}
    (history : List (ℝ → ((NeutralRates Deme Locus Allele × ℝ≥0) ⊕ PulseMatrix Deme)))
    (derivative : (ℝ → ((NeutralRates Deme Locus Allele × ℝ≥0) ⊕ PulseMatrix Deme)) →
      BudgetMatrix Deme Locus Allele n)
    (hderivative : ∀ event ∈ history, ∀ ξ η, HasDerivAt
      (fun θ ↦ eventPropagator (fun _ ↦ n) (event θ) ξ η) (derivative event ξ η) θ₀)
    (x0 : FrequencyState Deme Locus Allele) (deme : Deme)
    (score outcome : FullHaplotype Locus Allele → ℝ)
    (hvariance : ∫ y, (stateLaw y deme).variance score
      ∂(historyEventKernel ℓ₀ hap₀ (history.map fun event ↦ event θ₀) x0) ≠ 0) :
    HasDerivAt (fun θ ↦ expectedCalibrationSlope
        (historyEventKernel ℓ₀ hap₀ (history.map fun event ↦ event θ)) x0 deme score outcome)
      ((historySensitivity (fun _ ↦ n) θ₀ history derivative
            (budgetCoefficients ℓ₀ (fun _ ↦ n) (demeCovariancePolynomial deme score outcome))
            (budgetMomentFeature (fun _ ↦ n) x0)
          * (∫ y, (stateLaw y deme).variance score
            ∂(historyEventKernel ℓ₀ hap₀ (history.map fun event ↦ event θ₀) x0))
        - (∫ y, (stateLaw y deme).covariance score outcome
            ∂(historyEventKernel ℓ₀ hap₀ (history.map fun event ↦ event θ₀) x0))
          * historySensitivity (fun _ ↦ n) θ₀ history derivative
            (budgetCoefficients ℓ₀ (fun _ ↦ n) (demeCovariancePolynomial deme score score))
            (budgetMomentFeature (fun _ ↦ n) x0))
        / (∫ y, (stateLaw y deme).variance score
            ∂(historyEventKernel ℓ₀ hap₀ (history.map fun event ↦ event θ₀) x0)) ^ 2) θ₀ :=
  (hasDerivAt_integral_covariance_historyEventKernel ℓ₀ hap₀ hn history derivative hderivative
    x0 deme score outcome).fun_div
    (hasDerivAt_integral_variance_historyEventKernel ℓ₀ hap₀ hn history derivative hderivative
      x0 deme score) hvariance

/-- **The sensitivity of calibration portability** `E C_t E V_s / (E V_t E C_s)`, at every budget
`n ≥ 2`, wherever `E V_t E C_s ≠ 0`. -/
theorem hasDerivAt_expectedCalibrationPortability_historyEventKernel (ℓ₀ : Locus)
    (hap₀ : FullHaplotype Locus Allele) {n : ℕ} (hn : 2 ≤ n) {θ₀ : ℝ}
    (history : List (ℝ → ((NeutralRates Deme Locus Allele × ℝ≥0) ⊕ PulseMatrix Deme)))
    (derivative : (ℝ → ((NeutralRates Deme Locus Allele × ℝ≥0) ⊕ PulseMatrix Deme)) →
      BudgetMatrix Deme Locus Allele n)
    (hderivative : ∀ event ∈ history, ∀ ξ η, HasDerivAt
      (fun θ ↦ eventPropagator (fun _ ↦ n) (event θ) ξ η) (derivative event ξ η) θ₀)
    (x0 : FrequencyState Deme Locus Allele) (source target : Deme)
    (score outcome : FullHaplotype Locus Allele → ℝ)
    (hdenominator : (∫ y, (stateLaw y target).variance score
          ∂(historyEventKernel ℓ₀ hap₀ (history.map fun event ↦ event θ₀) x0))
        * (∫ y, (stateLaw y source).covariance score outcome
          ∂(historyEventKernel ℓ₀ hap₀ (history.map fun event ↦ event θ₀) x0)) ≠ 0) :
    HasDerivAt (fun θ ↦ expectedCalibrationPortability
        (historyEventKernel ℓ₀ hap₀ (history.map fun event ↦ event θ)) x0 source target score
        outcome)
      (crossRatioDerivative
        (∫ y, (stateLaw y target).covariance score outcome
          ∂(historyEventKernel ℓ₀ hap₀ (history.map fun event ↦ event θ₀) x0))
        (∫ y, (stateLaw y source).variance score
          ∂(historyEventKernel ℓ₀ hap₀ (history.map fun event ↦ event θ₀) x0))
        (∫ y, (stateLaw y target).variance score
          ∂(historyEventKernel ℓ₀ hap₀ (history.map fun event ↦ event θ₀) x0))
        (∫ y, (stateLaw y source).covariance score outcome
          ∂(historyEventKernel ℓ₀ hap₀ (history.map fun event ↦ event θ₀) x0))
        (historySensitivity (fun _ ↦ n) θ₀ history derivative
          (budgetCoefficients ℓ₀ (fun _ ↦ n) (demeCovariancePolynomial target score outcome))
          (budgetMomentFeature (fun _ ↦ n) x0))
        (historySensitivity (fun _ ↦ n) θ₀ history derivative
          (budgetCoefficients ℓ₀ (fun _ ↦ n) (demeCovariancePolynomial source score score))
          (budgetMomentFeature (fun _ ↦ n) x0))
        (historySensitivity (fun _ ↦ n) θ₀ history derivative
          (budgetCoefficients ℓ₀ (fun _ ↦ n) (demeCovariancePolynomial target score score))
          (budgetMomentFeature (fun _ ↦ n) x0))
        (historySensitivity (fun _ ↦ n) θ₀ history derivative
          (budgetCoefficients ℓ₀ (fun _ ↦ n) (demeCovariancePolynomial source score outcome))
          (budgetMomentFeature (fun _ ↦ n) x0))) θ₀ :=
  (hasDerivAt_crossRatio
    (hasDerivAt_integral_covariance_historyEventKernel ℓ₀ hap₀ hn history derivative hderivative
      x0 target score outcome)
    (hasDerivAt_integral_variance_historyEventKernel ℓ₀ hap₀ hn history derivative hderivative
      x0 source score)
    (hasDerivAt_integral_variance_historyEventKernel ℓ₀ hap₀ hn history derivative hderivative
      x0 target score)
    (hasDerivAt_integral_covariance_historyEventKernel ℓ₀ hap₀ hn history derivative hderivative
      x0 source score outcome)
    hdenominator).congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun _ ↦
      expectedCalibrationPortability_eq_cross _ x0 source target score outcome)

/-- **The sensitivity of AUC portability** `E N_t E D_s / (E D_t E N_s)` of the AUC components,
wherever `E D_t E N_s ≠ 0`. -/
theorem hasDerivAt_expectedAUCPortability_historyEventKernel (ℓ₀ : Locus)
    (hap₀ : FullHaplotype Locus Allele) {θ₀ : ℝ}
    (history : List (ℝ → ((NeutralRates Deme Locus Allele × ℝ≥0) ⊕ PulseMatrix Deme)))
    (derivative : (ℝ → ((NeutralRates Deme Locus Allele × ℝ≥0) ⊕ PulseMatrix Deme)) →
      BudgetMatrix Deme Locus Allele 2)
    (hderivative : ∀ event ∈ history, ∀ ξ η, HasDerivAt
      (fun θ ↦ eventPropagator (fun _ ↦ 2) (event θ) ξ η) (derivative event ξ η) θ₀)
    (x0 : FrequencyState Deme Locus Allele) (source target : Deme)
    (score : FullHaplotype Locus Allele → ℝ) (outcome : FullHaplotype Locus Allele → Bool)
    (hdenominator : (∫ y, aucDenominator (stateLaw y target) outcome
          ∂(historyEventKernel ℓ₀ hap₀ (history.map fun event ↦ event θ₀) x0))
        * (∫ y, aucNumerator (stateLaw y source) score outcome
          ∂(historyEventKernel ℓ₀ hap₀ (history.map fun event ↦ event θ₀) x0)) ≠ 0) :
    HasDerivAt (fun θ ↦ expectedAUCPortability
        (historyEventKernel ℓ₀ hap₀ (history.map fun event ↦ event θ)) x0 source target score
        outcome)
      (crossRatioDerivative
        (∫ y, aucNumerator (stateLaw y target) score outcome
          ∂(historyEventKernel ℓ₀ hap₀ (history.map fun event ↦ event θ₀) x0))
        (∫ y, aucDenominator (stateLaw y source) outcome
          ∂(historyEventKernel ℓ₀ hap₀ (history.map fun event ↦ event θ₀) x0))
        (∫ y, aucDenominator (stateLaw y target) outcome
          ∂(historyEventKernel ℓ₀ hap₀ (history.map fun event ↦ event θ₀) x0))
        (∫ y, aucNumerator (stateLaw y source) score outcome
          ∂(historyEventKernel ℓ₀ hap₀ (history.map fun event ↦ event θ₀) x0))
        (historySensitivity (fun _ ↦ 2) θ₀ history derivative
          (budgetCoefficients ℓ₀ (fun _ ↦ 2)
            (demePolynomial target (aucNumeratorPolynomial score outcome)))
          (budgetMomentFeature (fun _ ↦ 2) x0))
        (historySensitivity (fun _ ↦ 2) θ₀ history derivative
          (budgetCoefficients ℓ₀ (fun _ ↦ 2)
            (demePolynomial source (aucDenominatorPolynomial outcome)))
          (budgetMomentFeature (fun _ ↦ 2) x0))
        (historySensitivity (fun _ ↦ 2) θ₀ history derivative
          (budgetCoefficients ℓ₀ (fun _ ↦ 2)
            (demePolynomial target (aucDenominatorPolynomial outcome)))
          (budgetMomentFeature (fun _ ↦ 2) x0))
        (historySensitivity (fun _ ↦ 2) θ₀ history derivative
          (budgetCoefficients ℓ₀ (fun _ ↦ 2)
            (demePolynomial source (aucNumeratorPolynomial score outcome)))
          (budgetMomentFeature (fun _ ↦ 2) x0))) θ₀ :=
  hasDerivAt_crossRatio
    (hasDerivAt_integral_aucNumerator_historyEventKernel ℓ₀ hap₀ history derivative hderivative
      x0 target score outcome)
    (hasDerivAt_integral_aucDenominator_historyEventKernel ℓ₀ hap₀ history derivative hderivative
      x0 source outcome)
    (hasDerivAt_integral_aucDenominator_historyEventKernel ℓ₀ hap₀ history derivative hderivative
      x0 target outcome)
    (hasDerivAt_integral_aucNumerator_historyEventKernel ℓ₀ hap₀ history derivative hderivative
      x0 source score outcome)
    hdenominator

end

end Descent.Portability.EndToEndSensitivityMetrics
