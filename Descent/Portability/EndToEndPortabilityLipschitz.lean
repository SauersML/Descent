/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.EndToEndPortabilityLaw
import Descent.Portability.CaratheodoryFundamentalMatrix

assert_below Descent.Decision Descent.Program

/-!
# Portability is Lipschitz in the demographic rate history

`EndToEndPortabilityLaw` writes the expected squared-correlation numerators and denominators of a
score under a neutral rate history as coefficient vectors dotted with `U(T) H₄(x₀)`, and its
portability as a rational function of those.  This module proves that all of them depend
Lipschitz-continuously on the rate history, measured by the `L¹([0, T])` distance of the dual
generator paths.

The propagator.  The propagator of a rate history with continuous dual generator is the
Carathéodory fundamental matrix of its generator path (`rateHistoryDualPropagator_eq_caratheodory`),
so the variation-of-constants bound of `CaratheodoryFundamentalMatrix` applies: two rate histories
have propagators within `(∫₀ᵀ ‖Q₁ - Q₂‖) e^{∫₀ᵀ ‖Q₁‖} e^{∫₀ᵀ ‖Q₂‖}`
(`norm_rateHistoryDualPropagator_sub_le`).

The expectations.  A coefficient vector dotted with the propagated moments moves by at most its
coefficient mass times the propagator distance times the feature bound, so the expected
numerators and denominators are Lipschitz in the generator path
(`abs_integral_correlationNumerator_sub_le`, `abs_integral_correlationDenominator_sub_le`).  For
a score and an outcome in the unit interval they lie in `[0, 1]`
(`integral_correlationNumerator_nonneg`, `integral_correlationNumerator_le_denominator`,
`integral_correlationDenominator_le_one`).

The portability.  A product of numbers in the unit interval moves by at most the sum of the moves
of its factors (`abs_mul_sub_mul_le`), and a quotient with denominators at least `δ` moves by at
most the moves of numerator and denominator over `δ²` (`abs_div_sub_div_le`).  So wherever the
expected target denominator and source numerator stay at least `δ` under both histories, the
expected portability moves by at most the sum of the moves of the four expectations over `δ⁴`
(`abs_expectedPortability_sub_le`), and the four moves are the Lipschitz bounds above.

Scope.  The rate histories have dual generators continuous on the horizon, so that the neutral
Markov kernel of `NeutralRateHistoryKernel` exists; the propagator bound itself holds for
integrable generator paths.  The portability bound is local: it needs the lower bound `δ`.

## Empirical status

None.  The bodies here are norm inequalities for matrix products, integrals of bounded
polynomials and elementary inequalities for quotients, so no measurement can bear on them.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.EndToEndPortabilityLipschitz

open MeasureTheory ProbabilityTheory MvPolynomial Descent.Coalescent PartialHaplotypeCarrier
  PartialHaplotypeDualGenerator PartialHaplotypeDualSemigroup NeutralFellerGenerator
  NeutralPolynomialSemigroup PartialHaplotypeMicroscopicApproximation
  NeutralRateHistoryRealization NeutralRateHistoryKernel ReplicaMetricInstances
  EndToEndPortabilityLaw CaratheodoryFundamentalMatrix LinearFundamentalMatrix
open scoped Matrix NNReal Matrix.Norms.Operator

noncomputable section

/-! ## Elementary bounds -/

/-- A product moves by at most the sum of the moves of its factors when the moved factors are
bounded by one. -/
theorem abs_mul_sub_mul_le {a b c d : ℝ} (hb : |b| ≤ 1) (hc : |c| ≤ 1) :
    |a * b - c * d| ≤ |a - c| + |b - d| := by
  have hsplit : a * b - c * d = (a - c) * b + c * (b - d) := by ring
  rw [hsplit]
  refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
  · rw [abs_mul]
    exact mul_le_of_le_one_right (abs_nonneg _) hb
  · rw [abs_mul]
    exact mul_le_of_le_one_left (abs_nonneg _) hc

/-- A quotient moves by at most the moves of numerator and denominator over `δ²`, when both
denominators are at least `δ`, one of them is at most one, and one numerator is bounded by
one. -/
theorem abs_div_sub_div_le {a b c d δ : ℝ} (hδ : 0 < δ) (hb : δ ≤ b) (hd : δ ≤ d) (hd1 : d ≤ 1)
    (hc : |c| ≤ 1) : |a / b - c / d| ≤ (|a - c| + |b - d|) / δ ^ 2 := by
  have hb0 : 0 < b := hδ.trans_le hb
  have hd0 : 0 < d := hδ.trans_le hd
  rw [div_sub_div _ _ hb0.ne' hd0.ne', abs_div, abs_of_pos (mul_pos hb0 hd0)]
  have hnumerator : |a * d - b * c| ≤ |a - c| + |b - d| := by
    have hsplit : a * d - b * c = (a - c) * d + c * (d - b) := by ring
    rw [hsplit]
    refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [abs_mul, abs_of_pos hd0]
      exact mul_le_of_le_one_right (abs_nonneg _) hd1
    · rw [abs_mul, abs_sub_comm d b]
      exact mul_le_of_le_one_left (abs_nonneg _) hc
  have hdenominator : δ ^ 2 ≤ b * d := by nlinarith
  exact (div_le_div_of_nonneg_right hnumerator (mul_pos hb0 hd0).le).trans
    (div_le_div_of_nonneg_left (add_nonneg (abs_nonneg _) (abs_nonneg _)) (by positivity)
      hdenominator)

variable {Deme Locus : Type*} {Allele : Locus → Type*}
variable [Fintype Deme] [DecidableEq Deme] [Fintype Locus] [DecidableEq Locus]
  [∀ ℓ, Fintype (Allele ℓ)] [∀ ℓ, DecidableEq (Allele ℓ)]

/-! ## The propagator -/

/-- The propagator of a rate history with continuous dual generator is the Carathéodory fundamental
matrix of its dual generator path at the horizon. -/
theorem rateHistoryDualPropagator_eq_caratheodory {rates : ℝ → NeutralRates Deme Locus Allele}
    {capacity : Locus → ℕ} {T : ℝ} (hT : 0 ≤ T)
    (hcontinuous : ContinuousOn (fun t ↦ dualGenerator (rates t) capacity) (Set.Icc 0 T)) :
    rateHistoryDualPropagator rates capacity T
      = caratheodoryFundamentalMatrix (dualGeneratorPath rates capacity T) hT
          ((continuous_dualGeneratorPath hT hcontinuous).intervalIntegrable 0 T) T :=
  (caratheodoryFundamentalMatrix_eq_fundamentalMatrix (continuous_dualGeneratorPath hT hcontinuous)
    hT T ⟨hT, le_rfl⟩).symm

/-- **The propagator is Lipschitz in the rate path.**  Two rate histories with continuous dual
generators have propagators within `(∫₀ᵀ ‖Q₁ - Q₂‖) e^{∫₀ᵀ ‖Q₁‖} e^{∫₀ᵀ ‖Q₂‖}`. -/
theorem norm_rateHistoryDualPropagator_sub_le {first second : ℝ → NeutralRates Deme Locus Allele}
    {capacity : Locus → ℕ} {T : ℝ} (hT : 0 ≤ T)
    (hfirst : ContinuousOn (fun t ↦ dualGenerator (first t) capacity) (Set.Icc 0 T))
    (hsecond : ContinuousOn (fun t ↦ dualGenerator (second t) capacity) (Set.Icc 0 T)) :
    ‖rateHistoryDualPropagator first capacity T - rateHistoryDualPropagator second capacity T‖
      ≤ (∫ s in (0 : ℝ)..T,
          ‖dualGeneratorPath first capacity T s - dualGeneratorPath second capacity T s‖)
        * Real.exp (∫ s in (0 : ℝ)..T, ‖dualGeneratorPath first capacity T s‖)
        * Real.exp (∫ s in (0 : ℝ)..T, ‖dualGeneratorPath second capacity T s‖) := by
  rw [rateHistoryDualPropagator_eq_caratheodory hT hfirst,
    rateHistoryDualPropagator_eq_caratheodory hT hsecond]
  exact norm_caratheodoryFundamentalMatrix_sub_le hT _ _ T ⟨hT, le_rfl⟩

/-! ## The expectations -/

/-- **Expected numerators are Lipschitz in the rate path.** -/
theorem abs_integral_correlationNumerator_sub_le {first second : ℝ → NeutralRates Deme Locus Allele}
    {T : ℝ} (hT : 0 ≤ T)
    (hfirst : ∀ capacity : Locus → ℕ,
      ContinuousOn (fun t ↦ dualGenerator (first t) capacity) (Set.Icc 0 T))
    (hsecond : ∀ capacity : Locus → ℕ,
      ContinuousOn (fun t ↦ dualGenerator (second t) capacity) (Set.Icc 0 T))
    (ℓ₀ : Locus) (hap₀ : FullHaplotype Locus Allele) (x0 : FrequencyState Deme Locus Allele)
    (deme : Deme) (score outcome : FullHaplotype Locus Allele → ℝ) :
    |(∫ y, correlationNumerator (stateLaw y deme) score outcome
        ∂(rateHistoryKernel first ℓ₀ hap₀ hT hfirst x0))
      - ∫ y, correlationNumerator (stateLaw y deme) score outcome
        ∂(rateHistoryKernel second ℓ₀ hap₀ hT hsecond x0)|
      ≤ (∑ η, |budgetCoefficients ℓ₀ (fun _ ↦ 4) (numeratorPolynomial deme score outcome) η|)
        * ((∫ s in (0 : ℝ)..T, ‖dualGeneratorPath first (fun _ ↦ 4) T s
              - dualGeneratorPath second (fun _ ↦ 4) T s‖)
            * Real.exp (∫ s in (0 : ℝ)..T, ‖dualGeneratorPath first (fun _ ↦ 4) T s‖)
            * Real.exp (∫ s in (0 : ℝ)..T, ‖dualGeneratorPath second (fun _ ↦ 4) T s‖)
          * featureBound (first 0) (fun _ ↦ 4)) := by
  rw [integral_correlationNumerator_rateHistoryKernel,
    integral_correlationNumerator_rateHistoryKernel]
  refine (abs_dotProduct_mulVec_sub_le (first 0) (fun _ ↦ 4) _ _ _ x0).trans ?_
  refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right
    (norm_rateHistoryDualPropagator_sub_le hT (hfirst _) (hsecond _)) ?_)
    (Finset.sum_nonneg fun η _ ↦ abs_nonneg _)
  exact Finset.sum_nonneg fun ξ _ ↦ (momentBound_spec (first 0) _ ξ).1

/-- **Expected denominators are Lipschitz in the rate path.** -/
theorem abs_integral_correlationDenominator_sub_le
    {first second : ℝ → NeutralRates Deme Locus Allele} {T : ℝ} (hT : 0 ≤ T)
    (hfirst : ∀ capacity : Locus → ℕ,
      ContinuousOn (fun t ↦ dualGenerator (first t) capacity) (Set.Icc 0 T))
    (hsecond : ∀ capacity : Locus → ℕ,
      ContinuousOn (fun t ↦ dualGenerator (second t) capacity) (Set.Icc 0 T))
    (ℓ₀ : Locus) (hap₀ : FullHaplotype Locus Allele) (x0 : FrequencyState Deme Locus Allele)
    (deme : Deme) (score outcome : FullHaplotype Locus Allele → ℝ) :
    |(∫ y, correlationDenominator (stateLaw y deme) score outcome
        ∂(rateHistoryKernel first ℓ₀ hap₀ hT hfirst x0))
      - ∫ y, correlationDenominator (stateLaw y deme) score outcome
        ∂(rateHistoryKernel second ℓ₀ hap₀ hT hsecond x0)|
      ≤ (∑ η, |budgetCoefficients ℓ₀ (fun _ ↦ 4) (denominatorPolynomial deme score outcome) η|)
        * ((∫ s in (0 : ℝ)..T, ‖dualGeneratorPath first (fun _ ↦ 4) T s
              - dualGeneratorPath second (fun _ ↦ 4) T s‖)
            * Real.exp (∫ s in (0 : ℝ)..T, ‖dualGeneratorPath first (fun _ ↦ 4) T s‖)
            * Real.exp (∫ s in (0 : ℝ)..T, ‖dualGeneratorPath second (fun _ ↦ 4) T s‖)
          * featureBound (first 0) (fun _ ↦ 4)) := by
  rw [integral_correlationDenominator_rateHistoryKernel,
    integral_correlationDenominator_rateHistoryKernel]
  refine (abs_dotProduct_mulVec_sub_le (first 0) (fun _ ↦ 4) _ _ _ x0).trans ?_
  refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right
    (norm_rateHistoryDualPropagator_sub_le hT (hfirst _) (hsecond _)) ?_)
    (Finset.sum_nonneg fun η _ ↦ abs_nonneg _)
  exact Finset.sum_nonneg fun ξ _ ↦ (momentBound_spec (first 0) _ ξ).1

/-- The correlation numerator is integrable under every Markov kernel. -/
theorem integrable_correlationNumerator
    (κ : Kernel (FrequencyState Deme Locus Allele) (FrequencyState Deme Locus Allele))
    [IsMarkovKernel κ] (x0 : FrequencyState Deme Locus Allele) (deme : Deme)
    (score outcome : FullHaplotype Locus Allele → ℝ) :
    Integrable (fun y ↦ correlationNumerator (stateLaw y deme) score outcome) (κ x0) := by
  have hfunction : (fun y : FrequencyState Deme Locus Allele ↦
        correlationNumerator (stateLaw y deme) score outcome)
      = ⇑(polynomialFunction (numeratorPolynomial deme score outcome)) :=
    funext fun y ↦ (polynomialFunction_numeratorPolynomial deme score outcome y).symm
  rw [hfunction]
  exact (BoundedContinuousFunction.mkOfCompact
    (polynomialFunction (numeratorPolynomial deme score outcome))).integrable _

/-- The correlation denominator is integrable under every Markov kernel. -/
theorem integrable_correlationDenominator
    (κ : Kernel (FrequencyState Deme Locus Allele) (FrequencyState Deme Locus Allele))
    [IsMarkovKernel κ] (x0 : FrequencyState Deme Locus Allele) (deme : Deme)
    (score outcome : FullHaplotype Locus Allele → ℝ) :
    Integrable (fun y ↦ correlationDenominator (stateLaw y deme) score outcome) (κ x0) := by
  have hfunction : (fun y : FrequencyState Deme Locus Allele ↦
        correlationDenominator (stateLaw y deme) score outcome)
      = ⇑(polynomialFunction (denominatorPolynomial deme score outcome)) :=
    funext fun y ↦ (polynomialFunction_denominatorPolynomial deme score outcome y).symm
  rw [hfunction]
  exact (BoundedContinuousFunction.mkOfCompact
    (polynomialFunction (denominatorPolynomial deme score outcome))).integrable _

/-- The expected correlation numerator is nonnegative. -/
theorem integral_correlationNumerator_nonneg
    (κ : Kernel (FrequencyState Deme Locus Allele) (FrequencyState Deme Locus Allele))
    [IsMarkovKernel κ] (x0 : FrequencyState Deme Locus Allele) (deme : Deme)
    (score outcome : FullHaplotype Locus Allele → ℝ) :
    0 ≤ ∫ y, correlationNumerator (stateLaw y deme) score outcome ∂(κ x0) :=
  integral_nonneg fun y ↦ correlationNumerator_nonneg _ score outcome

/-- The expected correlation numerator is at most the expected correlation denominator. -/
theorem integral_correlationNumerator_le_denominator
    (κ : Kernel (FrequencyState Deme Locus Allele) (FrequencyState Deme Locus Allele))
    [IsMarkovKernel κ] (x0 : FrequencyState Deme Locus Allele) (deme : Deme)
    (score outcome : FullHaplotype Locus Allele → ℝ) :
    ∫ y, correlationNumerator (stateLaw y deme) score outcome ∂(κ x0)
      ≤ ∫ y, correlationDenominator (stateLaw y deme) score outcome ∂(κ x0) :=
  integral_mono (integrable_correlationNumerator κ x0 deme score outcome)
    (integrable_correlationDenominator κ x0 deme score outcome)
    fun y ↦ correlationNumerator_le_denominator _ score outcome

/-- For a score and an outcome in the unit interval the expected correlation denominator is at
most one. -/
theorem integral_correlationDenominator_le_one
    (κ : Kernel (FrequencyState Deme Locus Allele) (FrequencyState Deme Locus Allele))
    [IsMarkovKernel κ] (x0 : FrequencyState Deme Locus Allele) (deme : Deme)
    (score outcome : FullHaplotype Locus Allele → ℝ)
    (hscore0 : ∀ hap, 0 ≤ score hap) (hscore1 : ∀ hap, score hap ≤ 1)
    (houtcome0 : ∀ hap, 0 ≤ outcome hap) (houtcome1 : ∀ hap, outcome hap ≤ 1) :
    ∫ y, correlationDenominator (stateLaw y deme) score outcome ∂(κ x0) ≤ 1 := by
  have hbound : ∫ y, correlationDenominator (stateLaw y deme) score outcome ∂(κ x0)
      ≤ ∫ _y, (1 : ℝ) ∂(κ x0) :=
    integral_mono (integrable_correlationDenominator κ x0 deme score outcome) (integrable_const 1)
      fun y ↦ correlationDenominator_le_one _ score outcome hscore0 hscore1 houtcome0 houtcome1
  rwa [integral_const, measureReal_univ_eq_one, one_smul] at hbound

/-! ## The portability -/

/-- **Portability is locally Lipschitz in the expectations.**  If the expected target denominator
and source numerator are at least `δ` under both kernels, and the score and outcome lie in the
unit interval, the expected portabilities differ by at most the sum of the moves of the four
expectations over `δ⁴`. -/
theorem abs_expectedPortability_sub_le
    (κ₁ κ₂ : Kernel (FrequencyState Deme Locus Allele) (FrequencyState Deme Locus Allele))
    [IsMarkovKernel κ₁] [IsMarkovKernel κ₂] (x₁ x₂ : FrequencyState Deme Locus Allele)
    (source target : Deme) (score outcome : FullHaplotype Locus Allele → ℝ)
    (hscore0 : ∀ hap, 0 ≤ score hap) (hscore1 : ∀ hap, score hap ≤ 1)
    (houtcome0 : ∀ hap, 0 ≤ outcome hap) (houtcome1 : ∀ hap, outcome hap ≤ 1) {δ : ℝ}
    (hδ : 0 < δ)
    (htarget₁ : δ ≤ ∫ y, correlationDenominator (stateLaw y target) score outcome ∂(κ₁ x₁))
    (hsource₁ : δ ≤ ∫ y, correlationNumerator (stateLaw y source) score outcome ∂(κ₁ x₁))
    (htarget₂ : δ ≤ ∫ y, correlationDenominator (stateLaw y target) score outcome ∂(κ₂ x₂))
    (hsource₂ : δ ≤ ∫ y, correlationNumerator (stateLaw y source) score outcome ∂(κ₂ x₂)) :
    |expectedPortability κ₁ x₁ source target score outcome
        - expectedPortability κ₂ x₂ source target score outcome|
      ≤ (|(∫ y, correlationNumerator (stateLaw y target) score outcome ∂(κ₁ x₁))
            - ∫ y, correlationNumerator (stateLaw y target) score outcome ∂(κ₂ x₂)|
          + |(∫ y, correlationDenominator (stateLaw y source) score outcome ∂(κ₁ x₁))
            - ∫ y, correlationDenominator (stateLaw y source) score outcome ∂(κ₂ x₂)|
          + (|(∫ y, correlationDenominator (stateLaw y target) score outcome ∂(κ₁ x₁))
            - ∫ y, correlationDenominator (stateLaw y target) score outcome ∂(κ₂ x₂)|
          + |(∫ y, correlationNumerator (stateLaw y source) score outcome ∂(κ₁ x₁))
            - ∫ y, correlationNumerator (stateLaw y source) score outcome ∂(κ₂ x₂)|))
        / (δ ^ 2) ^ 2 := by
  have hunit : ∀ (κ : Kernel (FrequencyState Deme Locus Allele) (FrequencyState Deme Locus Allele))
      [IsMarkovKernel κ] (x : FrequencyState Deme Locus Allele) (deme : Deme),
      0 ≤ ∫ y, correlationNumerator (stateLaw y deme) score outcome ∂(κ x)
        ∧ ∫ y, correlationNumerator (stateLaw y deme) score outcome ∂(κ x) ≤ 1
        ∧ 0 ≤ ∫ y, correlationDenominator (stateLaw y deme) score outcome ∂(κ x)
        ∧ ∫ y, correlationDenominator (stateLaw y deme) score outcome ∂(κ x) ≤ 1 := by
    intro κ _ x deme
    have hnonneg := integral_correlationNumerator_nonneg κ x deme score outcome
    have hle := integral_correlationNumerator_le_denominator κ x deme score outcome
    have hone :=
      integral_correlationDenominator_le_one κ x deme score outcome hscore0 hscore1 houtcome0
        houtcome1
    exact ⟨hnonneg, hle.trans hone, hnonneg.trans hle, hone⟩
  obtain ⟨hNt₁0, hNt₁1, hDt₁0, hDt₁1⟩ := hunit κ₁ x₁ target
  obtain ⟨hNs₁0, hNs₁1, hDs₁0, hDs₁1⟩ := hunit κ₁ x₁ source
  obtain ⟨hNt₂0, hNt₂1, hDt₂0, hDt₂1⟩ := hunit κ₂ x₂ target
  obtain ⟨hNs₂0, hNs₂1, hDs₂0, hDs₂1⟩ := hunit κ₂ x₂ source
  have hnumeratorMove := abs_mul_sub_mul_le
    (a := ∫ y, correlationNumerator (stateLaw y target) score outcome ∂(κ₁ x₁))
    (d := ∫ y, correlationDenominator (stateLaw y source) score outcome ∂(κ₂ x₂))
    (abs_le.mpr ⟨by linarith, hDs₁1⟩) (abs_le.mpr ⟨by linarith, hNt₂1⟩)
  have hdenominatorMove := abs_mul_sub_mul_le
    (a := ∫ y, correlationDenominator (stateLaw y target) score outcome ∂(κ₁ x₁))
    (d := ∫ y, correlationNumerator (stateLaw y source) score outcome ∂(κ₂ x₂))
    (abs_le.mpr ⟨by linarith, hNs₁1⟩) (abs_le.mpr ⟨by linarith, hDt₂1⟩)
  have hδ2 : 0 < δ ^ 2 := by positivity
  have hproduct₁ : δ ^ 2 ≤ (∫ y, correlationDenominator (stateLaw y target) score outcome ∂(κ₁ x₁))
      * ∫ y, correlationNumerator (stateLaw y source) score outcome ∂(κ₁ x₁) := by
    rw [sq]
    exact mul_le_mul htarget₁ hsource₁ hδ.le (by linarith)
  have hproduct₂ : δ ^ 2 ≤ (∫ y, correlationDenominator (stateLaw y target) score outcome ∂(κ₂ x₂))
      * ∫ y, correlationNumerator (stateLaw y source) score outcome ∂(κ₂ x₂) := by
    rw [sq]
    exact mul_le_mul htarget₂ hsource₂ hδ.le (by linarith)
  have hproductOne : (∫ y, correlationDenominator (stateLaw y target) score outcome ∂(κ₂ x₂))
      * ∫ y, correlationNumerator (stateLaw y source) score outcome ∂(κ₂ x₂) ≤ 1 :=
    mul_le_one₀ hDt₂1 hNs₂0 hNs₂1
  have hnumeratorOne : |(∫ y, correlationNumerator (stateLaw y target) score outcome ∂(κ₂ x₂))
      * ∫ y, correlationDenominator (stateLaw y source) score outcome ∂(κ₂ x₂)| ≤ 1 := by
    rw [abs_of_nonneg (mul_nonneg hNt₂0 hDs₂0)]
    exact mul_le_one₀ hNt₂1 hDs₂0 hDs₂1
  refine (abs_div_sub_div_le hδ2 hproduct₁ hproduct₂ hproductOne hnumeratorOne).trans ?_
  exact div_le_div_of_nonneg_right (add_le_add hnumeratorMove hdenominatorMove) (by positivity)

end

end Descent.Portability.EndToEndPortabilityLipschitz
