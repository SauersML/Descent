/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.EndToEndSensitivityMetrics
import Descent.Portability.EndToEndGWASTrainingLaw

assert_below Descent.Decision Descent.Program

/-!
# The exact sensitivity of accuracy and portability to effects and environment

`EndToEndSensitivityLaw` and `EndToEndSensitivityMetrics` differentiate the end-to-end metrics in
a demographic parameter.  The score and the outcome enter the same metrics polynomially, so their
exact partial derivatives are polynomial or rational.  This module writes them out.

Effects.  For a linear score `S_w = Σ_j w_j X_j`, `EndToEndGWASTrainingLaw` writes the correlation
numerator `16 C(S_w, Y)²` and denominator `16 V(S_w) V(Y)` of any population law as quadratic
forms `wᵀ M w` with the matrices `numeratorMatrix` `16 c cᵀ` and `denominatorMatrix`
`16 C(X, X) V_Y` (`correlationNumerator_linearScore`, `correlationDenominator_linearScore`).  Along
a line of weights `w + ε h` a quadratic form has derivative `Σ_{ij} M_ij (h_i w_j + w_i h_j)`
(`hasDerivAt_quadraticForm_line`), so the numerator and denominator have exact directional
derivatives in the effects (`hasDerivAt_correlationNumerator_linearScore`,
`hasDerivAt_correlationDenominator_linearScore`), and the portability `N_t D_s / (D_t N_s)` of a
linear score between a source and a target law has as derivative the cross-ratio derivative of
those four forms (`hasDerivAt_portability_linearScore`).

Environment.  Environmental noise of variance `σ²` independent of the haplotype adds `σ²` to the
outcome variance and leaves the covariance unchanged, so the squared correlation is
`N / (D + 16 σ² V_S)`.  Its derivative in `σ²` is `-16 N V_S / (D + 16 σ² V_S)²`
(`hasDerivAt_accuracy_environmentVariance`), negative whenever the score carries signal
(`accuracy_environmentVariance_derivative_neg`).  In the target of a portability ratio the same
noise enters one denominator factor, and portability decreases in the target environment variance
whenever the other accumulators are positive (`hasDerivAt_portability_environmentVariance`,
`portability_environmentVariance_derivative_neg`).

Scope.  The effects are a direction of weights for a fixed genotype coding, and the laws are
supplied population laws; composing them with the history kernels is the business of the modules
above.  The environment is noise of one variance per law, additive and independent of the
haplotype; gene–environment interaction is not covered here.

## Empirical status

None.  The bodies here are derivatives of quadratic forms and rational functions of supplied
population accumulators, so no measurement can bear on them.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.EndToEndSensitivityArchitecture

open ReplicaMetricInstances TrainingNoiseAccuracy EndToEndGWASTrainingLaw
  EndToEndSensitivityMetrics

noncomputable section

/-! ## Effects -/

section Effects

variable {J : Type*} [Fintype J]

/-- **A quadratic form along a line of weights**: `ε ↦ (w + ε h)ᵀ M (w + ε h)` has derivative
`Σ_{ij} M_ij (h_i (w + ε₀ h)_j + (w + ε₀ h)_i h_j)` at `ε₀`. -/
theorem hasDerivAt_quadraticForm_line (M : J → J → ℝ) (w h : J → ℝ) (ε₀ : ℝ) :
    HasDerivAt (fun ε ↦ ∑ i, ∑ j, M i j * ((w i + ε * h i) * (w j + ε * h j)))
      (∑ i, ∑ j, M i j * (h i * (w j + ε₀ * h j) + (w i + ε₀ * h i) * h j)) ε₀ := by
  have hline : ∀ k, HasDerivAt (fun ε ↦ w k + ε * h k) (h k) ε₀ := fun k ↦ by
    simpa only [one_mul] using ((hasDerivAt_id' (x := ε₀)).mul_const (h k)).const_add (w k)
  exact HasDerivAt.fun_sum fun i _ ↦ HasDerivAt.fun_sum fun j _ ↦
    ((hline i).fun_mul (hline j)).const_mul (M i j)

variable {Ω : Type*} [Fintype Ω]

/-- **The effect sensitivity of the correlation numerator** of a linear score along the weight
line `w + ε h`. -/
theorem hasDerivAt_correlationNumerator_linearScore (law : FiniteReportLaw Ω)
    (genotype : Ω → J → ℝ) (outcome : Ω → ℝ) (w h : J → ℝ) (ε₀ : ℝ) :
    HasDerivAt
      (fun ε ↦ correlationNumerator law (linearScore genotype fun k ↦ w k + ε * h k) outcome)
      (∑ i, ∑ j, numeratorMatrix law genotype outcome i j
        * (h i * (w j + ε₀ * h j) + (w i + ε₀ * h i) * h j)) ε₀ := by
  simp only [correlationNumerator_linearScore]
  exact hasDerivAt_quadraticForm_line _ w h ε₀

/-- **The effect sensitivity of the correlation denominator** of a linear score along the weight
line `w + ε h`. -/
theorem hasDerivAt_correlationDenominator_linearScore (law : FiniteReportLaw Ω)
    (genotype : Ω → J → ℝ) (outcome : Ω → ℝ) (w h : J → ℝ) (ε₀ : ℝ) :
    HasDerivAt
      (fun ε ↦ correlationDenominator law (linearScore genotype fun k ↦ w k + ε * h k) outcome)
      (∑ i, ∑ j, denominatorMatrix law genotype outcome i j
        * (h i * (w j + ε₀ * h j) + (w i + ε₀ * h i) * h j)) ε₀ := by
  simp only [correlationDenominator_linearScore]
  exact hasDerivAt_quadraticForm_line _ w h ε₀

/-- **The effect sensitivity of portability.**  For a linear score in a source and a target law,
the portability `N_t D_s / (D_t N_s)` along the weight line `w + ε h` has as derivative the
cross-ratio derivative of the four quadratic forms and their directional derivatives, wherever
`D_t N_s ≠ 0`. -/
theorem hasDerivAt_portability_linearScore (source target : FiniteReportLaw Ω)
    (genotype : Ω → J → ℝ) (outcome : Ω → ℝ) (w h : J → ℝ) (ε₀ : ℝ)
    (hdenominator :
      correlationDenominator target (linearScore genotype fun k ↦ w k + ε₀ * h k) outcome
        * correlationNumerator source (linearScore genotype fun k ↦ w k + ε₀ * h k) outcome
        ≠ 0) :
    HasDerivAt (fun ε ↦
        correlationNumerator target (linearScore genotype fun k ↦ w k + ε * h k) outcome
          * correlationDenominator source (linearScore genotype fun k ↦ w k + ε * h k) outcome
        / (correlationDenominator target (linearScore genotype fun k ↦ w k + ε * h k) outcome
          * correlationNumerator source (linearScore genotype fun k ↦ w k + ε * h k) outcome))
      (crossRatioDerivative
        (correlationNumerator target (linearScore genotype fun k ↦ w k + ε₀ * h k) outcome)
        (correlationDenominator source (linearScore genotype fun k ↦ w k + ε₀ * h k) outcome)
        (correlationDenominator target (linearScore genotype fun k ↦ w k + ε₀ * h k) outcome)
        (correlationNumerator source (linearScore genotype fun k ↦ w k + ε₀ * h k) outcome)
        (∑ i, ∑ j, numeratorMatrix target genotype outcome i j
          * (h i * (w j + ε₀ * h j) + (w i + ε₀ * h i) * h j))
        (∑ i, ∑ j, denominatorMatrix source genotype outcome i j
          * (h i * (w j + ε₀ * h j) + (w i + ε₀ * h i) * h j))
        (∑ i, ∑ j, denominatorMatrix target genotype outcome i j
          * (h i * (w j + ε₀ * h j) + (w i + ε₀ * h i) * h j))
        (∑ i, ∑ j, numeratorMatrix source genotype outcome i j
          * (h i * (w j + ε₀ * h j) + (w i + ε₀ * h i) * h j))) ε₀ :=
  hasDerivAt_crossRatio
    (hasDerivAt_correlationNumerator_linearScore target genotype outcome w h ε₀)
    (hasDerivAt_correlationDenominator_linearScore source genotype outcome w h ε₀)
    (hasDerivAt_correlationDenominator_linearScore target genotype outcome w h ε₀)
    (hasDerivAt_correlationNumerator_linearScore source genotype outcome w h ε₀)
    hdenominator

end Effects

/-! ## Environment -/

section Environment

variable {State : Type*} [Fintype State]

/-- **The environment sensitivity of accuracy.**  With environmental noise of variance `σ²` the
squared correlation is `N / (D + 16 σ² V_S)`, whose derivative in `σ²` is
`-16 N V_S / (D + 16 σ² V_S)²`. -/
theorem hasDerivAt_accuracy_environmentVariance (law : FiniteReportLaw State)
    (score outcome : State → ℝ) (variance₀ : ℝ)
    (hne : correlationDenominator law score outcome + 16 * variance₀ * law.variance score ≠ 0) :
    HasDerivAt (fun environment ↦ correlationNumerator law score outcome
        / (correlationDenominator law score outcome + 16 * environment * law.variance score))
      (-(16 * correlationNumerator law score outcome * law.variance score)
        / (correlationDenominator law score outcome + 16 * variance₀ * law.variance score) ^ 2)
      variance₀ := by
  have hdenominator : HasDerivAt (fun environment ↦
      correlationDenominator law score outcome + 16 * environment * law.variance score)
      (16 * law.variance score) variance₀ := by
    simpa only [mul_one] using
      (((hasDerivAt_id' (x := variance₀)).const_mul 16).mul_const (law.variance score)).const_add
        (correlationDenominator law score outcome)
  refine ((hasDerivAt_const variance₀ (correlationNumerator law score outcome)).fun_div
    hdenominator hne).congr_deriv ?_
  simp only [zero_mul, zero_sub]
  ring

/-- **More environmental noise lowers accuracy** whenever the score carries signal: the derivative
of `N / (D + 16 σ² V_S)` in `σ²` is negative when `N > 0` and `V_S > 0`. -/
theorem accuracy_environmentVariance_derivative_neg (law : FiniteReportLaw State)
    (score outcome : State → ℝ) (variance₀ : ℝ)
    (hnumerator : 0 < correlationNumerator law score outcome)
    (hvariance : 0 < law.variance score)
    (hne : correlationDenominator law score outcome + 16 * variance₀ * law.variance score ≠ 0) :
    -(16 * correlationNumerator law score outcome * law.variance score)
        / (correlationDenominator law score outcome + 16 * variance₀ * law.variance score) ^ 2
      < 0 :=
  div_neg_of_neg_of_pos
    (neg_lt_zero.mpr (mul_pos (mul_pos (by norm_num) hnumerator) hvariance))
    (lt_of_le_of_ne (sq_nonneg _) (pow_ne_zero 2 hne).symm)

/-- **The target environment sensitivity of portability.**  With environmental noise of variance
`σ²` in the target, the portability `N_t D_s / ((D_t + 16 σ² V_{S,t}) N_s)` has as derivative the
cross-ratio derivative with only the target denominator factor moving, at rate `16 V_{S,t}`. -/
theorem hasDerivAt_portability_environmentVariance (source target : FiniteReportLaw State)
    (score outcome : State → ℝ) (variance₀ : ℝ)
    (hne : (correlationDenominator target score outcome
        + 16 * variance₀ * target.variance score) * correlationNumerator source score outcome
        ≠ 0) :
    HasDerivAt (fun environment ↦
        correlationNumerator target score outcome * correlationDenominator source score outcome
          / ((correlationDenominator target score outcome
            + 16 * environment * target.variance score)
            * correlationNumerator source score outcome))
      (crossRatioDerivative (correlationNumerator target score outcome)
        (correlationDenominator source score outcome)
        (correlationDenominator target score outcome + 16 * variance₀ * target.variance score)
        (correlationNumerator source score outcome) 0 0 (16 * target.variance score) 0)
      variance₀ := by
  have hdenominator : HasDerivAt (fun environment ↦
      correlationDenominator target score outcome + 16 * environment * target.variance score)
      (16 * target.variance score) variance₀ := by
    simpa only [mul_one] using
      (((hasDerivAt_id' (x := variance₀)).const_mul 16).mul_const
        (target.variance score)).const_add (correlationDenominator target score outcome)
  exact hasDerivAt_crossRatio
    (hasDerivAt_const variance₀ (correlationNumerator target score outcome))
    (hasDerivAt_const variance₀ (correlationDenominator source score outcome)) hdenominator
    (hasDerivAt_const variance₀ (correlationNumerator source score outcome)) hne

/-- **Portability decreases in the target environment variance** whenever the target numerator,
the source accumulators and the target score variance are positive. -/
theorem portability_environmentVariance_derivative_neg (source target : FiniteReportLaw State)
    (score outcome : State → ℝ) (variance₀ : ℝ)
    (htarget : 0 < correlationNumerator target score outcome)
    (hsourceDenominator : 0 < correlationDenominator source score outcome)
    (hsourceNumerator : 0 < correlationNumerator source score outcome)
    (hvariance : 0 < target.variance score)
    (hne : (correlationDenominator target score outcome
        + 16 * variance₀ * target.variance score) * correlationNumerator source score outcome
        ≠ 0) :
    crossRatioDerivative (correlationNumerator target score outcome)
        (correlationDenominator source score outcome)
        (correlationDenominator target score outcome + 16 * variance₀ * target.variance score)
        (correlationNumerator source score outcome) 0 0 (16 * target.variance score) 0
      < 0 := by
  rw [crossRatioDerivative_neg_iff 0 0 (16 * target.variance score) 0 hne]
  simp only [zero_mul, mul_zero, zero_add, add_zero]
  exact mul_pos (mul_pos htarget hsourceDenominator)
    (mul_pos (mul_pos (by norm_num) hvariance) hsourceNumerator)

end Environment

end

end Descent.Portability.EndToEndSensitivityArchitecture
