/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.EndToEndPortabilityLipschitz
import Descent.Portability.PortabilityMetricCompilation

assert_below Descent.Decision Descent.Program

/-!
# Portability is Lipschitz in the rate history: the composed bound

F8 Corollary B in its final form.  `EndToEndPortabilityLaw` writes the expected portability of a
score under a rate history as the rational function `momentPortability` of the propagated
budget-4 moments `U(T) · H₄(x₀)`.  The analysis of that rational function is
`PortabilityMetricCompilation.abs_crossRatio_sub_le`: on the realization body of the budget-4
feature, where the target denominator and the source numerator are at least `δ`, it is Lipschitz
in the sup norm of the moment vector with constant `4 B³ ‖a‖₁ ‖b‖₁ ‖c‖₁ ‖d‖₁ / δ⁴`.  The moment
side supplies the rest: the propagated vectors of two rate histories lie in that body
(`NeutralRateHistoryRealization.rateHistoryDualPropagator_mulVec_mem_realizationBody`), every
feature coordinate is at most the feature bound `B` (`abs_budgetMomentFeature_le`), the two vectors
differ by at most the propagator distance times `B` (`norm_propagated_sub_le`), and the propagator
distance is at most `(∫₀ᵀ ‖Q₁ - Q₂‖) e^{∫₀ᵀ ‖Q₁‖} e^{∫₀ᵀ ‖Q₂‖}`
(`EndToEndPortabilityLipschitz.norm_rateHistoryDualPropagator_sub_le`).

Composed, the portability of the moment law moves by at most an explicit constant times the
`L¹([0, T])` distance of the dual generator paths (`abs_momentPortability_rateHistory_sub_le`),
and so does the expected portability under the neutral Markov kernels of the two rate histories
(`abs_expectedPortability_rateHistory_sub_le`).

Scope.  The rate histories have dual generators continuous on the horizon.  The bound is local: it
needs the lower bound `δ` on the target denominator and the source numerator under both histories.

## Empirical status

None.  The bodies here compose norm inequalities for matrix products with a Lipschitz bound for a
rational function, so no measurement can bear on them.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.EndToEndPortabilityRateLipschitz

open MeasureTheory ProbabilityTheory MvPolynomial Descent.Coalescent PartialHaplotypeCarrier
  PartialHaplotypeDualGenerator PartialHaplotypeDualSemigroup NeutralFellerGenerator
  NeutralPolynomialSemigroup PartialHaplotypeMicroscopicApproximation
  NeutralMicroscopicEulerLimit NeutralRateHistoryRealization NeutralRateHistoryKernel
  ReplicaMetricInstances EndToEndPortabilityLaw EndToEndPortabilityLipschitz
open scoped Matrix NNReal Matrix.Norms.Operator

noncomputable section

variable {Deme Locus : Type*} {Allele : Locus → Type*}
variable [Fintype Deme] [DecidableEq Deme] [Fintype Locus] [DecidableEq Locus]
  [∀ ℓ, Fintype (Allele ℓ)] [∀ ℓ, DecidableEq (Allele ℓ)]

/-- Every coordinate of the budget-moment feature is at most the feature bound. -/
theorem abs_budgetMomentFeature_le (rates : NeutralRates Deme Locus Allele)
    (capacity : Locus → ℕ) (x : FrequencyState Deme Locus Allele)
    (ξ : BudgetConfiguration Deme Locus Allele capacity) :
    |budgetMomentFeature capacity x ξ| ≤ featureBound rates capacity := by
  rw [← Real.norm_eq_abs]
  exact (norm_le_pi_norm _ ξ).trans (norm_budgetMomentFeature_le rates capacity x)

/-- The feature bound is nonnegative. -/
theorem featureBound_nonneg (rates : NeutralRates Deme Locus Allele) (capacity : Locus → ℕ) :
    0 ≤ featureBound rates capacity :=
  Finset.sum_nonneg fun ξ _ ↦ (momentBound_spec rates capacity ξ).1

/-- Two propagators applied to the moments of one state differ by at most the propagator distance
times the feature bound. -/
theorem norm_propagated_sub_le (rates : NeutralRates Deme Locus Allele) (capacity : Locus → ℕ)
    (P Q : Matrix (BudgetConfiguration Deme Locus Allele capacity)
      (BudgetConfiguration Deme Locus Allele capacity) ℝ)
    (x : FrequencyState Deme Locus Allele) :
    ‖P *ᵥ budgetMomentFeature capacity x - Q *ᵥ budgetMomentFeature capacity x‖
      ≤ ‖P - Q‖ * featureBound rates capacity := by
  rw [← Matrix.sub_mulVec]
  exact (Matrix.linfty_opNorm_mulVec _ _).trans
    (mul_le_mul_of_nonneg_left (norm_budgetMomentFeature_le rates capacity x) (norm_nonneg _))

/-- **F8 Corollary B for the moment law.**  For two rate histories with continuous dual
generators, where the target denominator and the source numerator of the propagated moments are at
least `δ` under both, the rational portability function of the propagated budget-4 moments moves
by at most `4 B³ ‖a‖₁ ‖b‖₁ ‖c‖₁ ‖d‖₁ / δ⁴` times `B` times the propagator bound. -/
theorem abs_momentPortability_rateHistory_sub_le
    {first second : ℝ → NeutralRates Deme Locus Allele} {T : ℝ} (hT : 0 ≤ T)
    (hfirst : ∀ capacity : Locus → ℕ,
      ContinuousOn (fun t ↦ dualGenerator (first t) capacity) (Set.Icc 0 T))
    (hsecond : ∀ capacity : Locus → ℕ,
      ContinuousOn (fun t ↦ dualGenerator (second t) capacity) (Set.Icc 0 T))
    (ℓ₀ : Locus) (x0 : FrequencyState Deme Locus Allele) (source target : Deme)
    (score outcome : FullHaplotype Locus Allele → ℝ) {δ : ℝ} (hδ : 0 < δ)
    (htarget₁ : δ ≤ budgetCoefficients ℓ₀ (fun _ ↦ 4) (denominatorPolynomial target score outcome)
      ⬝ᵥ (rateHistoryDualPropagator first (fun _ ↦ 4) T *ᵥ budgetMomentFeature (fun _ ↦ 4) x0))
    (hsource₁ : δ ≤ budgetCoefficients ℓ₀ (fun _ ↦ 4) (numeratorPolynomial source score outcome)
      ⬝ᵥ (rateHistoryDualPropagator first (fun _ ↦ 4) T *ᵥ budgetMomentFeature (fun _ ↦ 4) x0))
    (htarget₂ : δ ≤ budgetCoefficients ℓ₀ (fun _ ↦ 4) (denominatorPolynomial target score outcome)
      ⬝ᵥ (rateHistoryDualPropagator second (fun _ ↦ 4) T *ᵥ budgetMomentFeature (fun _ ↦ 4) x0))
    (hsource₂ : δ ≤ budgetCoefficients ℓ₀ (fun _ ↦ 4) (numeratorPolynomial source score outcome)
      ⬝ᵥ (rateHistoryDualPropagator second (fun _ ↦ 4) T *ᵥ budgetMomentFeature (fun _ ↦ 4) x0)) :
    |momentPortability ℓ₀ source target score outcome
        (rateHistoryDualPropagator first (fun _ ↦ 4) T *ᵥ budgetMomentFeature (fun _ ↦ 4) x0)
      - momentPortability ℓ₀ source target score outcome
        (rateHistoryDualPropagator second (fun _ ↦ 4) T *ᵥ budgetMomentFeature (fun _ ↦ 4) x0)|
      ≤ 4 * featureBound (first 0) (fun _ ↦ 4) ^ 3
          * (∑ i, |budgetCoefficients ℓ₀ (fun _ ↦ 4) (numeratorPolynomial target score outcome) i|)
          * (∑ i, |budgetCoefficients ℓ₀ (fun _ ↦ 4)
              (denominatorPolynomial source score outcome) i|)
          * (∑ i, |budgetCoefficients ℓ₀ (fun _ ↦ 4)
              (denominatorPolynomial target score outcome) i|)
          * (∑ i, |budgetCoefficients ℓ₀ (fun _ ↦ 4) (numeratorPolynomial source score outcome) i|)
          / δ ^ 4
        * ((∫ s in (0 : ℝ)..T, ‖dualGeneratorPath first (fun _ ↦ 4) T s
              - dualGeneratorPath second (fun _ ↦ 4) T s‖)
            * Real.exp (∫ s in (0 : ℝ)..T, ‖dualGeneratorPath first (fun _ ↦ 4) T s‖)
            * Real.exp (∫ s in (0 : ℝ)..T, ‖dualGeneratorPath second (fun _ ↦ 4) T s‖)
          * featureBound (first 0) (fun _ ↦ 4)) := by
  have hB0 := featureBound_nonneg (first 0) (fun _ ↦ 4)
  have hcross := PortabilityMetricCompilation.abs_crossRatio_sub_le
    (budgetMomentFeature (Deme := Deme) (Locus := Locus) (Allele := Allele) (fun _ ↦ 4)) hδ
    (abs_budgetMomentFeature_le (first 0) (fun _ ↦ 4))
    (budgetCoefficients ℓ₀ (fun _ ↦ 4) (numeratorPolynomial target score outcome))
    (budgetCoefficients ℓ₀ (fun _ ↦ 4) (denominatorPolynomial source score outcome))
    (budgetCoefficients ℓ₀ (fun _ ↦ 4) (denominatorPolynomial target score outcome))
    (budgetCoefficients ℓ₀ (fun _ ↦ 4) (numeratorPolynomial source score outcome))
    (rateHistoryDualPropagator_mulVec_mem_realizationBody hT (hfirst _) x0)
    (rateHistoryDualPropagator_mulVec_mem_realizationBody hT (hsecond _) x0)
    htarget₁ hsource₁ htarget₂ hsource₂
  have hvector := (norm_propagated_sub_le (first 0) (fun _ ↦ 4)
    (rateHistoryDualPropagator first (fun _ ↦ 4) T)
    (rateHistoryDualPropagator second (fun _ ↦ 4) T) x0).trans
    (mul_le_mul_of_nonneg_right
      (norm_rateHistoryDualPropagator_sub_le hT (hfirst (fun _ ↦ 4)) (hsecond (fun _ ↦ 4))) hB0)
  have hconstant : 0 ≤ 4 * featureBound (first 0) (fun _ ↦ 4) ^ 3
      * (∑ i, |budgetCoefficients ℓ₀ (fun _ ↦ 4) (numeratorPolynomial target score outcome) i|)
      * (∑ i, |budgetCoefficients ℓ₀ (fun _ ↦ 4) (denominatorPolynomial source score outcome) i|)
      * (∑ i, |budgetCoefficients ℓ₀ (fun _ ↦ 4) (denominatorPolynomial target score outcome) i|)
      * (∑ i, |budgetCoefficients ℓ₀ (fun _ ↦ 4) (numeratorPolynomial source score outcome) i|)
      / δ ^ 4 := by
    refine div_nonneg ?_ (by positivity)
    refine mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num)
      (pow_nonneg hB0 3)) ?_) ?_) ?_) ?_ <;>
    exact Finset.sum_nonneg fun i _ ↦ abs_nonneg _
  exact hcross.trans (mul_le_mul_of_nonneg_left hvector hconstant)

/-- **F8 Corollary B under the process law.**  For two rate histories with continuous dual
generators, where the expected target denominator and source numerator are at least `δ` under
both neutral Markov kernels, the expected portability moves by at most the composed constant times
the `L¹([0, T])` distance of the dual generator paths. -/
theorem abs_expectedPortability_rateHistory_sub_le
    {first second : ℝ → NeutralRates Deme Locus Allele} {T : ℝ} (hT : 0 ≤ T)
    (hfirst : ∀ capacity : Locus → ℕ,
      ContinuousOn (fun t ↦ dualGenerator (first t) capacity) (Set.Icc 0 T))
    (hsecond : ∀ capacity : Locus → ℕ,
      ContinuousOn (fun t ↦ dualGenerator (second t) capacity) (Set.Icc 0 T))
    (ℓ₀ : Locus) (hap₀ : FullHaplotype Locus Allele) (x0 : FrequencyState Deme Locus Allele)
    (source target : Deme) (score outcome : FullHaplotype Locus Allele → ℝ) {δ : ℝ} (hδ : 0 < δ)
    (htarget₁ : δ ≤ ∫ y, correlationDenominator (stateLaw y target) score outcome
      ∂(rateHistoryKernel first ℓ₀ hap₀ hT hfirst x0))
    (hsource₁ : δ ≤ ∫ y, correlationNumerator (stateLaw y source) score outcome
      ∂(rateHistoryKernel first ℓ₀ hap₀ hT hfirst x0))
    (htarget₂ : δ ≤ ∫ y, correlationDenominator (stateLaw y target) score outcome
      ∂(rateHistoryKernel second ℓ₀ hap₀ hT hsecond x0))
    (hsource₂ : δ ≤ ∫ y, correlationNumerator (stateLaw y source) score outcome
      ∂(rateHistoryKernel second ℓ₀ hap₀ hT hsecond x0)) :
    |expectedPortability (rateHistoryKernel first ℓ₀ hap₀ hT hfirst) x0 source target score outcome
      - expectedPortability (rateHistoryKernel second ℓ₀ hap₀ hT hsecond) x0 source target score
          outcome|
      ≤ 4 * featureBound (first 0) (fun _ ↦ 4) ^ 3
          * (∑ i, |budgetCoefficients ℓ₀ (fun _ ↦ 4) (numeratorPolynomial target score outcome) i|)
          * (∑ i, |budgetCoefficients ℓ₀ (fun _ ↦ 4)
              (denominatorPolynomial source score outcome) i|)
          * (∑ i, |budgetCoefficients ℓ₀ (fun _ ↦ 4)
              (denominatorPolynomial target score outcome) i|)
          * (∑ i, |budgetCoefficients ℓ₀ (fun _ ↦ 4) (numeratorPolynomial source score outcome) i|)
          / δ ^ 4
        * ((∫ s in (0 : ℝ)..T, ‖dualGeneratorPath first (fun _ ↦ 4) T s
              - dualGeneratorPath second (fun _ ↦ 4) T s‖)
            * Real.exp (∫ s in (0 : ℝ)..T, ‖dualGeneratorPath first (fun _ ↦ 4) T s‖)
            * Real.exp (∫ s in (0 : ℝ)..T, ‖dualGeneratorPath second (fun _ ↦ 4) T s‖)
          * featureBound (first 0) (fun _ ↦ 4)) := by
  rw [integral_correlationDenominator_rateHistoryKernel] at htarget₁ htarget₂
  rw [integral_correlationNumerator_rateHistoryKernel] at hsource₁ hsource₂
  rw [expectedPortability_rateHistoryKernel, expectedPortability_rateHistoryKernel]
  exact abs_momentPortability_rateHistory_sub_le hT hfirst hsecond ℓ₀ x0 source target score
    outcome hδ htarget₁ hsource₁ htarget₂ hsource₂

end

end Descent.Portability.EndToEndPortabilityRateLipschitz
