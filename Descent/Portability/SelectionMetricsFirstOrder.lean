/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.SelectionHistoryFirstOrder
import Descent.Portability.EndToEndCalibrationLaw
import Descent.Portability.EndToEndDiscriminationLaw

assert_below Descent.Decision Descent.Program

/-!
# First-order selection for calibration and AUC portability along a history

`SelectionHistoryFirstOrder` gives the first-order selection correction of the moments along a
history of epochs, splits and pulses, and carries it to the squared-correlation portability of
`EndToEndPortabilityLaw`. This module carries it to the other ratio-of-expectations metrics: the
calibration slope, intercept and portability of `EndToEndCalibrationLaw`, at budgets two and
three, and the AUC portability of `EndToEndDiscriminationLaw`, at budget two.

The selected metrics. Under an expectation functional over per-deme haplotype laws, the covariance
and variance of a deme, its intercept accumulator and its AUC numerator and denominator are
coefficient vectors dotted with the expected moments (`expectation_covariance_eq_dotProduct`,
`expectation_variance_eq_dotProduct`, `expectation_interceptNumerator_eq_dotProduct`,
`expectation_aucNumerator_eq_dotProduct`, `expectation_aucDenominator_eq_dotProduct`), through the
deme copy of a population polynomial (`expectation_demePolynomial_eq_dotProduct`). So the
calibration slope, intercept and portability and the AUC portability of a selected history
(`selectedCalibrationSlope`, `selectedCalibrationIntercept`, `selectedCalibrationPortability`,
`selectedAUCPortability`) are the rational functions of the two end-to-end laws at the selected
moments (`selectedCalibrationSlope_eq_momentCalibrationSlope`,
`selectedCalibrationIntercept_eq_momentCalibrationIntercept`,
`selectedCalibrationPortability_eq_momentCalibrationPortability`,
`selectedAUCPortability_eq_momentAUCPortability`).

Ratios to first order. A cross ratio of dot products with moments in the unit box is its value at
the neutral moments plus `σ` times the cross-ratio derivative in the first-order direction, up to
`SelectionHistoryFirstOrder.crossRatioRemainder` (`abs_crossRatio_dotProduct_sub_firstOrder_le`). A
quotient `a / c` is the cross ratio `a c / (c c)`, whose derivative is the quotient rule
(`crossRatioDerivative_self`), so the same bound covers slopes and intercepts
(`abs_quotient_dotProduct_sub_firstOrder_le`). The moments of a selected history supply the unit
box and the three errors in one statement (`selectedHistory_firstOrder_bounds`).

The metric laws. For the fitness table `σ s`, with `s` in `[0, 1]`, where the denominators are at
least `δ > 0`, each metric of the selected history is its neutral value plus `σ` times its
first-order correction, up to an explicit remainder of order `σ² T²`: the calibration slope
(`abs_selectedCalibrationSlope_sub_firstOrder_le`), the calibration intercept
(`abs_selectedCalibrationIntercept_sub_firstOrder_le`), calibration portability
(`abs_selectedCalibrationPortability_sub_firstOrder_le`) and AUC portability
(`abs_selectedAUCPortability_sub_firstOrder_le`). Each correction is the right derivative of the
metric in `σ` at zero (`hasDerivWithinAt_selectedCalibrationSlope_firstOrder`,
`hasDerivWithinAt_selectedCalibrationIntercept_firstOrder`,
`hasDerivWithinAt_selectedCalibrationPortability_firstOrder`,
`hasDerivWithinAt_selectedAUCPortability_firstOrder`).

Sign criteria. With positive neutral values, selection raises the calibration slope to first order
exactly when the relative first-order change of the covariance exceeds that of the score variance
(`quotientDerivative_pos_iff_of_pos`, `calibrationSlopeFirstOrder_pos_iff`), and raises calibration
or AUC portability exactly when the relative first-order change of the target metric exceeds that
of the source metric (`calibrationPortabilityFirstOrder_pos_iff`,
`aucPortabilityFirstOrder_pos_iff`).

Significance. Together with `SelectionHistoryFirstOrder`, every ratio-of-expectations metric of the
corpus end-to-end laws, for accuracy, calibration and discrimination, has an explicit first-order
selection law along any demographic history, with its derivative in the selection strength and its
sign.

Scope. The forward moment equation with selection is a hypothesis on the families, at the budget
and at the budget with one more copy at the selected locus; the selected diffusion is not
constructed. Selection is haploid at one locus, with one fitness table scaled from a table in
`[0, 1]`. The remainders carry the coefficient masses of the metric polynomials and need lower
bounds `δ` on the denominators under the selected families and at the neutral moments. The expected
AUC and the expected squared correlation, which are series, are not expanded.

## Empirical status

None. The bodies here are norm inequalities for dot products with propagated moments and rational
functions of supplied values, so no measurement can bear on them.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.SelectionMetricsFirstOrder

open MvPolynomial Descent.Coalescent Descent.Foundations PartialHaplotypeCarrier
  PartialHaplotypeDualGenerator PartialHaplotypeDualSemigroup SubstochasticGeneratorSemigroup
  PartialHaplotypePulseKernel NeutralPulseHistoryKernel ReplicaMetricInstances
  EndToEndPortabilityLaw SelectionHistoryMoments EndToEndSelectionLaw SelectionMomentExpansion
  EndToEndSensitivityMetrics EndToEndCalibrationLaw EndToEndDiscriminationLaw
  SelectionHistoryFirstOrder
open scoped Matrix NNReal

noncomputable section

/-! ## Quotients and cross ratios of dot products to first order -/

/-- **The quotient rule** for `a / c`, from the values and derivatives of numerator and
denominator. -/
def quotientDerivative (a c a' c' : ℝ) : ℝ :=
  (a' * c - a * c') / c ^ 2

/-- The cross-ratio derivative at `(a, c, c, c)` in the direction `(a', c', c', c')` is the
quotient derivative of `a / c`. -/
theorem crossRatioDerivative_self {a c : ℝ} (a' c' : ℝ) (hc : c ≠ 0) :
    crossRatioDerivative a c c c a' c' c' c' = quotientDerivative a c a' c' := by
  rw [crossRatioDerivative, quotientDerivative,
    div_eq_div_iff (pow_ne_zero 2 (mul_ne_zero hc hc)) (pow_ne_zero 2 hc)]
  ring

/-- **The sign criterion for a quotient.** For positive `a` and `c`, the quotient `a / c` increases
to first order exactly when the relative change of `c` is below that of `a`. -/
theorem quotientDerivative_pos_iff_of_pos {a c : ℝ} (a' c' : ℝ) (ha : 0 < a) (hc : 0 < c) :
    0 < quotientDerivative a c a' c' ↔ c' / c < a' / a := by
  rw [quotientDerivative, div_pos_iff_of_pos_right (pow_pos hc 2), sub_pos,
    div_lt_div_iff₀ hc ha, mul_comm c' a]

/-- **A cross ratio of dot products to first order.** For moment vectors with `‖V‖, ‖m₀‖ ≤ 1`,
`‖V - m₀‖ ≤ e₀`, `‖σ • m₁‖ ≤ e₁` and `‖V - m₀ - σ • m₁‖ ≤ e₂`, and denominators `c ⬝ᵥ V`, `d ⬝ᵥ V`,
`c ⬝ᵥ m₀`, `d ⬝ᵥ m₀` at least `δ > 0`, the cross ratio `(a ⬝ᵥ V)(b ⬝ᵥ V) / ((c ⬝ᵥ V)(d ⬝ᵥ V))`
is its value at `m₀` plus `σ` times the cross-ratio derivative in the direction `m₁`, up to
`crossRatioRemainder ‖a‖₁ ‖b‖₁ ‖c‖₁ ‖d‖₁ e₀ e₁ e₂ δ`. -/
theorem abs_crossRatio_dotProduct_sub_firstOrder_le {ι : Type*} [Fintype ι] (a b c d : ι → ℝ)
    {V m₀ m₁ : ι → ℝ} {σ e₀ e₁ e₂ δ : ℝ} (hδ : 0 < δ) (hV : ‖V‖ ≤ 1) (hm₀ : ‖m₀‖ ≤ 1)
    (h₀ : ‖V - m₀‖ ≤ e₀) (h₁ : ‖σ • m₁‖ ≤ e₁) (h₂ : ‖V - m₀ - σ • m₁‖ ≤ e₂)
    (hc : δ ≤ c ⬝ᵥ V) (hd : δ ≤ d ⬝ᵥ V) (hc₀ : δ ≤ c ⬝ᵥ m₀) (hd₀ : δ ≤ d ⬝ᵥ m₀) :
    |(a ⬝ᵥ V) * (b ⬝ᵥ V) / ((c ⬝ᵥ V) * (d ⬝ᵥ V))
        - (a ⬝ᵥ m₀) * (b ⬝ᵥ m₀) / ((c ⬝ᵥ m₀) * (d ⬝ᵥ m₀))
        - σ * crossRatioDerivative (a ⬝ᵥ m₀) (b ⬝ᵥ m₀) (c ⬝ᵥ m₀) (d ⬝ᵥ m₀) (a ⬝ᵥ m₁) (b ⬝ᵥ m₁)
          (c ⬝ᵥ m₁) (d ⬝ᵥ m₁)|
      ≤ crossRatioRemainder (∑ i, |a i|) (∑ i, |b i|) (∑ i, |c i|) (∑ i, |d i|) e₀ e₁ e₂ δ := by
  obtain ⟨-, hA₀, -, hA₁, hρA⟩ := dotProduct_firstOrder_bounds a hV hm₀ h₀ h₁ h₂
  obtain ⟨hB, hB₀, hΔB, hB₁, hρB⟩ := dotProduct_firstOrder_bounds b hV hm₀ h₀ h₁ h₂
  obtain ⟨-, hC₀, hΔC, hC₁, hρC⟩ := dotProduct_firstOrder_bounds c hV hm₀ h₀ h₁ h₂
  obtain ⟨hDκ, hD₀, hΔD, hD₁, hρD⟩ := dotProduct_firstOrder_bounds d hV hm₀ h₀ h₁ h₂
  exact abs_crossRatio_sub_firstOrder_le hδ hc hd hc₀ hd₀ hB hDκ hA₀ hB₀ hC₀ hD₀ hΔB hΔC hΔD
    hA₁ hB₁ hC₁ hD₁ hρA hρB hρC hρD

/-- **A quotient of dot products to first order.** Under the hypotheses of
`abs_crossRatio_dotProduct_sub_firstOrder_le`, where `c ⬝ᵥ V` and `c ⬝ᵥ m₀` are at least `δ > 0`,
the quotient `(a ⬝ᵥ V) / (c ⬝ᵥ V)` is its value at `m₀` plus `σ` times the quotient derivative in
the direction `m₁`, up to `crossRatioRemainder ‖a‖₁ ‖c‖₁ ‖c‖₁ ‖c‖₁ e₀ e₁ e₂ δ`. -/
theorem abs_quotient_dotProduct_sub_firstOrder_le {ι : Type*} [Fintype ι] (a c : ι → ℝ)
    {V m₀ m₁ : ι → ℝ} {σ e₀ e₁ e₂ δ : ℝ} (hδ : 0 < δ) (hV : ‖V‖ ≤ 1) (hm₀ : ‖m₀‖ ≤ 1)
    (h₀ : ‖V - m₀‖ ≤ e₀) (h₁ : ‖σ • m₁‖ ≤ e₁) (h₂ : ‖V - m₀ - σ • m₁‖ ≤ e₂)
    (hc : δ ≤ c ⬝ᵥ V) (hc₀ : δ ≤ c ⬝ᵥ m₀) :
    |(a ⬝ᵥ V) / (c ⬝ᵥ V) - (a ⬝ᵥ m₀) / (c ⬝ᵥ m₀)
        - σ * quotientDerivative (a ⬝ᵥ m₀) (c ⬝ᵥ m₀) (a ⬝ᵥ m₁) (c ⬝ᵥ m₁)|
      ≤ crossRatioRemainder (∑ i, |a i|) (∑ i, |c i|) (∑ i, |c i|) (∑ i, |c i|) e₀ e₁ e₂ δ := by
  have hcross := abs_crossRatio_dotProduct_sub_firstOrder_le a c c c hδ hV hm₀ h₀ h₁ h₂ hc hc
    hc₀ hc₀
  rw [mul_div_mul_right _ _ (hδ.trans_le hc).ne', mul_div_mul_right _ _ (hδ.trans_le hc₀).ne',
    crossRatioDerivative_self _ _ (hδ.trans_le hc₀).ne'] at hcross
  exact hcross

variable {Deme Locus : Type*} {Allele : Locus → Type*}
variable [Fintype Deme] [DecidableEq Deme] [Fintype Locus] [DecidableEq Locus]
  [∀ ℓ, Fintype (Allele ℓ)] [∀ ℓ, DecidableEq (Allele ℓ)]

/-! ## Population polynomials under an expectation functional -/

/-- At the frequency point of per-deme laws, the deme copy of a population polynomial evaluates at
that deme's law. -/
theorem eval_lawPoint_demePolynomial (law : Deme → FiniteReportLaw (FullHaplotype Locus Allele))
    (deme : Deme) (p : MvPolynomial (FullHaplotype Locus Allele) ℝ) :
    eval (lawPoint law) (demePolynomial deme p) = eval (law deme).mass p :=
  eval_rename _ _ _

/-- **A population polynomial under an expectation functional.** A polynomial of total degree at
most `n` in the haplotype frequencies of one deme has expectation equal to the budget coefficients
of its deme copy dotted with the expected budget-`n` moments. -/
theorem expectation_demePolynomial_eq_dotProduct (ℓ₀ : Locus) {n : ℕ}
    (expectation : ExpFunctional (Deme → FiniteReportLaw (FullHaplotype Locus Allele)))
    (deme : Deme) (p : MvPolynomial (FullHaplotype Locus Allele) ℝ) (hp : p.totalDegree ≤ n) :
    (expectation fun law ↦ eval (law deme).mass p)
      = budgetCoefficients ℓ₀ (fun _ ↦ n) (demePolynomial deme p)
        ⬝ᵥ fun η ↦ expectation fun law ↦ configurationMoment law η.1 := by
  have h := expectation_polynomial_eq_dotProduct ℓ₀ (fun _ ↦ n) (demePolynomial deme p)
    (withinBudget_of_totalDegree_le ℓ₀ _ ((totalDegree_rename_le _ _).trans hp)) expectation
  simpa only [eval_lawPoint_demePolynomial] using h

/-- The expected covariance of two observables in a deme through the expected budget-`n` moments,
`n ≥ 2`. -/
theorem expectation_covariance_eq_dotProduct (ℓ₀ : Locus) {n : ℕ} (hn : 2 ≤ n)
    (expectation : ExpFunctional (Deme → FiniteReportLaw (FullHaplotype Locus Allele)))
    (deme : Deme) (first second : FullHaplotype Locus Allele → ℝ) :
    (expectation fun law ↦ (law deme).covariance first second)
      = budgetCoefficients ℓ₀ (fun _ ↦ n) (demeCovariancePolynomial deme first second)
        ⬝ᵥ fun η ↦ expectation fun law ↦ configurationMoment law η.1 := by
  simpa only [eval_covariancePolynomial] using expectation_demePolynomial_eq_dotProduct ℓ₀
    expectation deme (covariancePolynomial first second)
    ((totalDegree_covariancePolynomial_le first second).trans hn)

/-- The expected variance of an observable in a deme through the expected budget-`n` moments,
`n ≥ 2`. -/
theorem expectation_variance_eq_dotProduct (ℓ₀ : Locus) {n : ℕ} (hn : 2 ≤ n)
    (expectation : ExpFunctional (Deme → FiniteReportLaw (FullHaplotype Locus Allele)))
    (deme : Deme) (value : FullHaplotype Locus Allele → ℝ) :
    (expectation fun law ↦ (law deme).variance value)
      = budgetCoefficients ℓ₀ (fun _ ↦ n) (demeCovariancePolynomial deme value value)
        ⬝ᵥ fun η ↦ expectation fun law ↦ configurationMoment law η.1 :=
  expectation_covariance_eq_dotProduct ℓ₀ hn expectation deme value value

/-- The expected intercept accumulator `E[μ_Y V_S - C_SY μ_S]` of a deme through the expected
budget-`n` moments, `n ≥ 3`. -/
theorem expectation_interceptNumerator_eq_dotProduct (ℓ₀ : Locus) {n : ℕ} (hn : 3 ≤ n)
    (expectation : ExpFunctional (Deme → FiniteReportLaw (FullHaplotype Locus Allele)))
    (deme : Deme) (score outcome : FullHaplotype Locus Allele → ℝ) :
    (expectation fun law ↦ (law deme).expectation outcome * (law deme).variance score
        - (law deme).covariance score outcome * (law deme).expectation score)
      = budgetCoefficients ℓ₀ (fun _ ↦ n) (interceptNumeratorPolynomial deme score outcome)
        ⬝ᵥ fun η ↦ expectation fun law ↦ configurationMoment law η.1 := by
  have h := expectation_polynomial_eq_dotProduct ℓ₀ (fun _ ↦ n)
    (interceptNumeratorPolynomial deme score outcome)
    (withinBudget_of_totalDegree_le ℓ₀ _
      ((totalDegree_interceptNumeratorPolynomial_le deme score outcome).trans hn)) expectation
  have hpoint : ∀ law : Deme → FiniteReportLaw (FullHaplotype Locus Allele),
      eval (lawPoint law) (interceptNumeratorPolynomial deme score outcome)
        = (law deme).expectation outcome * (law deme).variance score
          - (law deme).covariance score outcome * (law deme).expectation score := by
    intro law
    simp only [interceptNumeratorPolynomial, demeMeanPolynomial, demeCovariancePolynomial,
      map_sub, map_mul, eval_lawPoint_demePolynomial, eval_expectationPolynomial,
      eval_covariancePolynomial, FiniteReportLaw.variance]
  simpa only [hpoint] using h

/-- The expected AUC numerator of a deme through the expected budget-2 moments. -/
theorem expectation_aucNumerator_eq_dotProduct (ℓ₀ : Locus)
    (expectation : ExpFunctional (Deme → FiniteReportLaw (FullHaplotype Locus Allele)))
    (deme : Deme) (score : FullHaplotype Locus Allele → ℝ)
    (outcome : FullHaplotype Locus Allele → Bool) :
    (expectation fun law ↦ aucNumerator (law deme) score outcome)
      = budgetCoefficients ℓ₀ (fun _ ↦ 2)
          (demePolynomial deme (aucNumeratorPolynomial score outcome))
        ⬝ᵥ fun η ↦ expectation fun law ↦ configurationMoment law η.1 := by
  simpa only [eval_aucNumeratorPolynomial] using expectation_demePolynomial_eq_dotProduct ℓ₀
    expectation deme _ (totalDegree_aucNumeratorPolynomial_le score outcome)

/-- The expected AUC denominator of a deme through the expected budget-2 moments. -/
theorem expectation_aucDenominator_eq_dotProduct (ℓ₀ : Locus)
    (expectation : ExpFunctional (Deme → FiniteReportLaw (FullHaplotype Locus Allele)))
    (deme : Deme) (outcome : FullHaplotype Locus Allele → Bool) :
    (expectation fun law ↦ aucDenominator (law deme) outcome)
      = budgetCoefficients ℓ₀ (fun _ ↦ 2) (demePolynomial deme (aucDenominatorPolynomial outcome))
        ⬝ᵥ fun η ↦ expectation fun law ↦ configurationMoment law η.1 := by
  simpa only [eval_aucDenominatorPolynomial] using expectation_demePolynomial_eq_dotProduct ℓ₀
    expectation deme _ (totalDegree_aucDenominatorPolynomial_le outcome)

/-! ## Calibration and AUC of a selected history -/

/-- **The calibration slope of a selected history**: the expected score–outcome covariance of a
deme over its expected score variance, under the family at event `k`. -/
def selectedCalibrationSlope
    (family : ℕ → ℝ → ExpFunctional (Deme → FiniteReportLaw (FullHaplotype Locus Allele)))
    (k : ℕ) (deme : Deme) (score outcome : FullHaplotype Locus Allele → ℝ) : ℝ :=
  (family k 0 fun law ↦ (law deme).covariance score outcome)
    / family k 0 fun law ↦ (law deme).variance score

/-- **The calibration intercept of a selected history**: the expected intercept accumulator
`E[μ_Y V_S - C_SY μ_S]` of a deme over its expected score variance. -/
def selectedCalibrationIntercept
    (family : ℕ → ℝ → ExpFunctional (Deme → FiniteReportLaw (FullHaplotype Locus Allele)))
    (k : ℕ) (deme : Deme) (score outcome : FullHaplotype Locus Allele → ℝ) : ℝ :=
  (family k 0 fun law ↦ (law deme).expectation outcome * (law deme).variance score
      - (law deme).covariance score outcome * (law deme).expectation score)
    / family k 0 fun law ↦ (law deme).variance score

/-- **The calibration portability of a selected history**: the target calibration slope over the
source one. -/
def selectedCalibrationPortability
    (family : ℕ → ℝ → ExpFunctional (Deme → FiniteReportLaw (FullHaplotype Locus Allele)))
    (k : ℕ) (source target : Deme) (score outcome : FullHaplotype Locus Allele → ℝ) : ℝ :=
  selectedCalibrationSlope family k target score outcome
    / selectedCalibrationSlope family k source score outcome

/-- **The AUC portability of a selected history**: `(E N_t · E D_s) / (E D_t · E N_s)` of expected
AUC numerators and denominators under the family at event `k`. -/
def selectedAUCPortability
    (family : ℕ → ℝ → ExpFunctional (Deme → FiniteReportLaw (FullHaplotype Locus Allele)))
    (k : ℕ) (source target : Deme) (score : FullHaplotype Locus Allele → ℝ)
    (outcome : FullHaplotype Locus Allele → Bool) : ℝ :=
  ((family k 0 fun law ↦ aucNumerator (law target) score outcome)
      * family k 0 fun law ↦ aucDenominator (law source) outcome)
    / ((family k 0 fun law ↦ aucDenominator (law target) outcome)
      * family k 0 fun law ↦ aucNumerator (law source) score outcome)

/-- **The selected calibration slope is the rational slope of the selected moments**, at every
budget `n ≥ 2`. -/
theorem selectedCalibrationSlope_eq_momentCalibrationSlope (ℓ₀ : Locus) {n : ℕ} (hn : 2 ≤ n)
    (family : ℕ → ℝ → ExpFunctional (Deme → FiniteReportLaw (FullHaplotype Locus Allele)))
    (k : ℕ) (deme : Deme) (score outcome : FullHaplotype Locus Allele → ℝ) :
    selectedCalibrationSlope family k deme score outcome
      = momentCalibrationSlope ℓ₀ n deme score outcome
          (expectedMomentVector (fun _ ↦ n) (family k) 0) := by
  rw [selectedCalibrationSlope, expectation_covariance_eq_dotProduct ℓ₀ hn,
    expectation_variance_eq_dotProduct ℓ₀ hn]
  rfl

/-- **The selected calibration intercept is the rational intercept of the selected moments**, at
every budget `n ≥ 3`. -/
theorem selectedCalibrationIntercept_eq_momentCalibrationIntercept (ℓ₀ : Locus) {n : ℕ}
    (hn : 3 ≤ n)
    (family : ℕ → ℝ → ExpFunctional (Deme → FiniteReportLaw (FullHaplotype Locus Allele)))
    (k : ℕ) (deme : Deme) (score outcome : FullHaplotype Locus Allele → ℝ) :
    selectedCalibrationIntercept family k deme score outcome
      = momentCalibrationIntercept ℓ₀ n deme score outcome
          (expectedMomentVector (fun _ ↦ n) (family k) 0) := by
  rw [selectedCalibrationIntercept, expectation_interceptNumerator_eq_dotProduct ℓ₀ hn,
    expectation_variance_eq_dotProduct ℓ₀ (by omega : 2 ≤ n)]
  rfl

/-- **The selected calibration portability is the rational calibration portability of the
selected moments**, at every budget `n ≥ 2`. -/
theorem selectedCalibrationPortability_eq_momentCalibrationPortability (ℓ₀ : Locus) {n : ℕ}
    (hn : 2 ≤ n)
    (family : ℕ → ℝ → ExpFunctional (Deme → FiniteReportLaw (FullHaplotype Locus Allele)))
    (k : ℕ) (source target : Deme) (score outcome : FullHaplotype Locus Allele → ℝ) :
    selectedCalibrationPortability family k source target score outcome
      = momentCalibrationPortability ℓ₀ n source target score outcome
          (expectedMomentVector (fun _ ↦ n) (family k) 0) := by
  rw [selectedCalibrationPortability, momentCalibrationPortability,
    selectedCalibrationSlope_eq_momentCalibrationSlope ℓ₀ hn,
    selectedCalibrationSlope_eq_momentCalibrationSlope ℓ₀ hn]

/-- **The selected AUC portability is the rational AUC portability of the selected budget-2
moments.** -/
theorem selectedAUCPortability_eq_momentAUCPortability (ℓ₀ : Locus)
    (family : ℕ → ℝ → ExpFunctional (Deme → FiniteReportLaw (FullHaplotype Locus Allele)))
    (k : ℕ) (source target : Deme) (score : FullHaplotype Locus Allele → ℝ)
    (outcome : FullHaplotype Locus Allele → Bool) :
    selectedAUCPortability family k source target score outcome
      = momentAUCPortability ℓ₀ source target score outcome
          (expectedMomentVector (fun _ ↦ 2) (family k) 0) := by
  rw [selectedAUCPortability, expectation_aucNumerator_eq_dotProduct ℓ₀,
    expectation_aucNumerator_eq_dotProduct ℓ₀, expectation_aucDenominator_eq_dotProduct ℓ₀,
    expectation_aucDenominator_eq_dotProduct ℓ₀]
  rfl

/-! ## The moments of a selected history to first order -/

/-- The neutral moments at the end of a history: the chronological propagator applied to the
initial moments of the family. -/
def neutralEndMoments (capacity : Locus → ℕ)
    (family : ℕ → ℝ → ExpFunctional (Deme → FiniteReportLaw (FullHaplotype Locus Allele)))
    (events : List ((NeutralRates Deme Locus Allele × ℝ≥0) ⊕ PulseMatrix Deme)) :
    BudgetConfiguration Deme Locus Allele capacity → ℝ :=
  historyEventPropagator capacity events *ᵥ expectedMomentVector capacity (family 0) 0

/-- The first-order direction at the end of a history: the first-order correction of the history
at the initial moments of the budget with one more copy at the selected locus. -/
def firstOrderEndMoments (model : SelectionModel Deme Locus Allele) (capacity : Locus → ℕ)
    (family : ℕ → ℝ → ExpFunctional (Deme → FiniteReportLaw (FullHaplotype Locus Allele)))
    (events : List ((NeutralRates Deme Locus Allele × ℝ≥0) ⊕ PulseMatrix Deme)) :
    BudgetConfiguration Deme Locus Allele capacity → ℝ :=
  historyCorrection model capacity events
    (expectedMomentVector (bumpCapacity model capacity) (family 0) 0)

/-- The coefficient mass `‖c‖₁` of a frequency polynomial over the budget-`n` configurations. -/
def budgetMass (ℓ₀ : Locus) (n : ℕ) (p : FrequencyPolynomial Deme Locus Allele) : ℝ :=
  ∑ i, |budgetCoefficients ℓ₀ (fun _ ↦ n) p i|

/-- At budget four the budget mass is `SelectionHistoryFirstOrder.coefficientMass`. -/
theorem budgetMass_four (ℓ₀ : Locus) (p : FrequencyPolynomial Deme Locus Allele) :
    budgetMass ℓ₀ 4 p = coefficientMass ℓ₀ p :=
  rfl

/-- The total size of the uniform budget `n` is `n` copies per locus. -/
theorem sum_const_capacity (n : ℕ) :
    ((∑ ℓ : Locus, (fun _ : Locus ↦ n) ℓ : ℕ) : ℝ) = n * Fintype.card Locus := by
  simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul, Nat.cast_mul]
  ring

/-- **The moments of a selected history to first order, in the form the metric laws read.** For
the fitness table `σ s`, with `s` in `[0, 1]` and masses at most `S`, the selected and the neutral
end moments lie in the unit box, differ by at most `B T σ`, the first-order direction costs at most
`2 B S T σ`, and the remainder is at most `B S (B + 1) T² σ²`, with `B = Σ_ℓ n_ℓ` and `T` the total
epoch duration.

Assumes: `SelectedOnHistory (scaledModel σ model) capacity family events 0` and
`SelectedOnHistory (scaledModel σ model) (bumpCapacity model capacity) family events 0`. -/
theorem selectedHistory_firstOrder_bounds (model : SelectionModel Deme Locus Allele) {σ S : ℝ}
    (hσ : 0 ≤ σ) (hS0 : 0 ≤ S) (hfit : ∀ i b, 0 ≤ model.fitness i b ∧ model.fitness i b ≤ 1)
    (hS : ∀ i, ∑ b, |model.fitness i b| ≤ S) (capacity : Locus → ℕ)
    (family : ℕ → ℝ → ExpFunctional (Deme → FiniteReportLaw (FullHaplotype Locus Allele)))
    (events : List ((NeutralRates Deme Locus Allele × ℝ≥0) ⊕ PulseMatrix Deme))
    (hhistory : SelectedOnHistory (scaledModel σ model) capacity family events 0)
    (hhistory' : SelectedOnHistory (scaledModel σ model) (bumpCapacity model capacity) family
      events 0) :
    ‖expectedMomentVector capacity (family events.length) 0‖ ≤ 1
      ∧ ‖neutralEndMoments capacity family events‖ ≤ 1
      ∧ ‖expectedMomentVector capacity (family events.length) 0
          - neutralEndMoments capacity family events‖
        ≤ (∑ ℓ, capacity ℓ : ℕ) * epochDuration events * σ
      ∧ ‖σ • firstOrderEndMoments model capacity family events‖
        ≤ 2 * (∑ ℓ, capacity ℓ : ℕ) * S * epochDuration events * σ
      ∧ ‖expectedMomentVector capacity (family events.length) 0
          - neutralEndMoments capacity family events
          - σ • firstOrderEndMoments model capacity family events‖
        ≤ (∑ ℓ, capacity ℓ : ℕ) * S * ((∑ ℓ, capacity ℓ : ℕ) + 1) * epochDuration events ^ 2
          * σ ^ 2 := by
  have hfit' : ∀ i b, 0 ≤ (scaledModel σ model).fitness i b
      ∧ (scaledModel σ model).fitness i b ≤ σ := fun i b ↦
    ⟨mul_nonneg hσ (hfit i b).1, mul_le_of_le_one_right hσ (hfit i b).2⟩
  refine ⟨norm_expectedMomentVector_le_one capacity (family events.length) 0,
    (norm_mulVec_le_of_substochastic (historyEventPropagator_substochastic capacity events)
      (expectedMomentVector capacity (family 0) 0)).trans
        (norm_expectedMomentVector_le_one capacity (family 0) 0), ?_, ?_, ?_⟩
  · have h := norm_selectedHistory_sub_propagator_le (scaledModel σ model) hσ hfit' capacity
      family events 0 hhistory
    rw [zero_add] at h
    exact h.trans_eq (by ring)
  · rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hσ]
    exact (mul_comm σ _).trans_le (mul_le_mul_of_nonneg_right
      ((norm_historyCorrection_le model hS0 hS capacity events
        (expectedMomentVector (bumpCapacity model capacity) (family 0) 0)).trans
          (mul_le_of_le_one_right (mul_nonneg (by positivity) (epochDuration_nonneg events))
            (norm_expectedMomentVector_le_one (bumpCapacity model capacity) (family 0) 0))) hσ)
  · exact (norm_scaledHistory_sub_firstOrder_le model hσ hS0 hfit hS capacity family events
      hhistory hhistory').trans_eq (by ring)

end

end Descent.Portability.SelectionMetricsFirstOrder
