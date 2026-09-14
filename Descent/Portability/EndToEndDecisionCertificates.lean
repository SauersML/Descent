/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.EndToEndDecisionLaw

assert_below Descent.Decision Descent.Program

/-!
# Truncation certificates for the expected recall and precision series

`EndToEndDecisionLaw` writes the expected per-population recall `E[TP / (TP + FN)]` and precision
`E[TP / (TP + FP)]` of a threshold rule as series of the expectations of `TP (1 - (TP + c))ᵏ`, for
a cell `c` of the confusion report (`EndToEndDecisionLaw.expectedPositiveQuotient_eq_tsum`).  This
module certifies every truncation of those series by one division-free budget-`K` quantity.

The pointwise tail.  For `0 ≤ num ≤ den ≤ 1`, the quotient minus its first `K` expansion terms is
`(num / den) (1 - den)ᴷ` (`quotient_sub_partialSum_eq`), which lies between zero and `(1 - den)ᴷ`
(`quotient_truncation_bounds`).  Under every probability measure the integrated tail is the
integral of `(num / den) (1 - den)ᴷ`, nonnegative and at most the integral of `(1 - den)ᴷ`
(`integral_quotient_truncation`).  That certificate tends to the probability that `den` vanishes
(`tendsto_integral_pow_complement`), and so to zero where `den > 0` almost surely
(`tendsto_integral_pow_complement_zero`).

The decision metrics.  The certificate of the positive quotient of a cell `c` is the frequency
polynomial `(1 - (TP + c))ᴷ` of total degree at most `K` (`certificatePolynomial`,
`eval_certificatePolynomial`, `totalDegree_certificatePolynomial_le`).  Under every Markov kernel
`0 ≤ E[TP / (TP + c)] - Σ_{k < K} E[TP (1 - (TP + c))ᵏ] ≤ E[(1 - (TP + c))ᴷ]`
(`expectedPositiveQuotient_truncation`).  For the expected recall the denominator `TP + FN` is the
case probability of the deme, for the expected precision `TP + FP` is the called fraction
(`integral_recallRate_precision_truncation`).  Through the propagated moments the partial sum is a
finite sum of budget-`(k + 1)` dot products and the certificate is one budget-`K` dot product
(`expectedPositiveQuotient_truncation_dotProduct`,
`expectedPositiveQuotient_truncation_historyEventKernel`,
`expectedPositiveQuotient_truncation_rateHistoryKernel`).  The expected certificate tends to the
probability that the denominator vanishes (`tendsto_certificate`), and to zero where the
denominator is positive almost surely (`tendsto_certificate_zero_of_ae_pos`), in particular for
the recall of a deme whose case probability is positive almost surely
(`tendsto_recallCertificate_zero_of_ae_pos`).

Significance.  An expected per-population sensitivity or predictive value needs the whole moment
family, but every finite computation of it carries its own error bar, computed from the same
propagated moments and never dividing.

Scope.  The certificate bounds the tail by the expected complement power; no rate in `K` is
claimed, and the certificate tends to zero only where the denominator is positive almost surely.

## Empirical status

None.  The bodies here are a pointwise geometric identity, elementary inequalities, dominated
convergence and integrals of polynomials against Markov kernels whose moments are matrix
computations of supplied rates, so no measurement can bear on them.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.EndToEndDecisionCertificates

open MeasureTheory ProbabilityTheory MvPolynomial Descent.Coalescent PartialHaplotypeCarrier
  PartialHaplotypeDualGenerator PartialHaplotypeDualSemigroup NeutralFellerGenerator
  NeutralPolynomialSemigroup PartialHaplotypeMicroscopicApproximation PartialHaplotypePulseKernel
  NeutralPulseHistoryKernel NeutralRateHistoryRealization NeutralRateHistoryKernel
  ReplicaMetricInstances EndToEndPortabilityLaw EndToEndDiscriminationLaw EndToEndBrierLaw
  EndToEndDecisionLaw
open scoped Matrix NNReal Topology

noncomputable section

/-! ## The tail of a bounded quotient -/

/-- **The pointwise tail of the positive ratio expansion.**  When `0 ≤ num ≤ den`, the quotient
`num / den`, read by Lean as zero where `den` vanishes, minus the first `K` expansion terms
`num (1 - den)ᵏ` is `(num / den) (1 - den)ᴷ`. -/
theorem quotient_sub_partialSum_eq (num den : ℝ) (hnum : 0 ≤ num) (hle : num ≤ den) (K : ℕ) :
    num / den - ∑ k ∈ Finset.range K, num * (1 - den) ^ k = num / den * (1 - den) ^ K := by
  have hcancel : num / den * den = num := by
    rcases eq_or_lt_of_le (hnum.trans hle) with hzero | hpos
    · rw [← hzero, div_zero, zero_mul]
      exact le_antisymm hnum (hle.trans_eq hzero.symm)
    · exact div_mul_cancel₀ num hpos.ne'
  induction K with
  | zero => simp
  | succ K ih =>
    rw [Finset.sum_range_succ, ← sub_sub, ih]
    linear_combination (1 - den) ^ K * hcancel

/-- **The pointwise certificate.**  When `0 ≤ num ≤ den ≤ 1`, the tail `(num / den) (1 - den)ᴷ`
lies between zero and `(1 - den)ᴷ`. -/
theorem quotient_truncation_bounds (num den : ℝ) (hnum : 0 ≤ num) (hle : num ≤ den)
    (hden : den ≤ 1) (K : ℕ) :
    0 ≤ num / den * (1 - den) ^ K ∧ num / den * (1 - den) ^ K ≤ (1 - den) ^ K := by
  have hquotient : 0 ≤ num / den ∧ num / den ≤ 1 :=
    ⟨div_nonneg hnum (hnum.trans hle), div_le_one_of_le₀ hle (hnum.trans hle)⟩
  have hpower : 0 ≤ (1 - den) ^ K := pow_nonneg (sub_nonneg.mpr hden) K
  exact ⟨mul_nonneg hquotient.1 hpower, mul_le_of_le_one_left hpower hquotient.2⟩

/-- **Truncation certificate for a bounded quotient under a probability measure.**  When
`0 ≤ num ≤ den ≤ 1`, the integral of `num / den` minus the first `K` integrals of the expansion
terms is the integral of `(num / den) (1 - den)ᴷ`, which is nonnegative and at most the integral of
`(1 - den)ᴷ`. -/
theorem integral_quotient_truncation {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (num den : Ω → ℝ) (hnumMeasurable : Measurable num)
    (hdenMeasurable : Measurable den) (hnum : ∀ point, 0 ≤ num point)
    (hle : ∀ point, num point ≤ den point) (hden : ∀ point, den point ≤ 1) (K : ℕ) :
    (∫ point, num point / den point ∂μ)
        - ∑ k ∈ Finset.range K, ∫ point, num point * (1 - den point) ^ k ∂μ
      = ∫ point, num point / den point * (1 - den point) ^ K ∂μ
    ∧ 0 ≤ ∫ point, num point / den point * (1 - den point) ^ K ∂μ
    ∧ ∫ point, num point / den point * (1 - den point) ^ K ∂μ
      ≤ ∫ point, (1 - den point) ^ K ∂μ := by
  have hdenNonneg : ∀ point, 0 ≤ den point := fun point ↦ (hnum point).trans (hle point)
  have hcomplement : ∀ (point : Ω) (k : ℕ), 0 ≤ (1 - den point) ^ k ∧ (1 - den point) ^ k ≤ 1 :=
    fun point k ↦ ⟨pow_nonneg (sub_nonneg.mpr (hden point)) k,
      pow_le_one₀ (sub_nonneg.mpr (hden point)) (by linarith [hdenNonneg point])⟩
  have hquotient : Integrable (fun point ↦ num point / den point) μ :=
    ReplicaMeasureCertificate.integrable_of_unit_bounds μ _ (hnumMeasurable.div hdenMeasurable)
      (fun point ↦ div_nonneg (hnum point) (hdenNonneg point))
      (fun point ↦ div_le_one_of_le₀ (hle point) (hdenNonneg point))
  have hterm : ∀ k ∈ Finset.range K,
      Integrable (fun point ↦ num point * (1 - den point) ^ k) μ :=
    fun k _ ↦ ReplicaMeasureCertificate.integrable_of_unit_bounds μ _
      (hnumMeasurable.mul ((measurable_const.sub hdenMeasurable).pow_const k))
      (fun point ↦ mul_nonneg (hnum point) (hcomplement point k).1)
      (fun point ↦ mul_le_one₀ ((hle point).trans (hden point)) (hcomplement point k).1
        (hcomplement point k).2)
  have hpower : Integrable (fun point ↦ (1 - den point) ^ K) μ :=
    ReplicaMeasureCertificate.integrable_of_unit_bounds μ _
      ((measurable_const.sub hdenMeasurable).pow_const K)
      (fun point ↦ (hcomplement point K).1) (fun point ↦ (hcomplement point K).2)
  have hbounds := fun point ↦
    quotient_truncation_bounds (num point) (den point) (hnum point) (hle point) (hden point) K
  refine ⟨?_, integral_nonneg fun point ↦ (hbounds point).1,
    integral_mono_of_nonneg (ae_of_all _ fun point ↦ (hbounds point).1) hpower
      (ae_of_all _ fun point ↦ (hbounds point).2)⟩
  rw [← integral_finset_sum (Finset.range K) hterm,
    ← integral_sub hquotient (integrable_finset_sum (Finset.range K) hterm)]
  exact integral_congr_ae (ae_of_all _ fun point ↦
    quotient_sub_partialSum_eq (num point) (den point) (hnum point) (hle point) K)

/-- **The certificate tends to the probability that the denominator vanishes.**  When
`0 ≤ den ≤ 1`, the integral of `(1 - den)ᴷ` tends, as `K` grows, to the integral of the indicator
of `den = 0`, by dominated convergence against the constant one. -/
theorem tendsto_integral_pow_complement {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (den : Ω → ℝ) (hdenMeasurable : Measurable den)
    (hden0 : ∀ point, 0 ≤ den point) (hden1 : ∀ point, den point ≤ 1) :
    Filter.Tendsto (fun K : ℕ ↦ ∫ point, (1 - den point) ^ K ∂μ) Filter.atTop
      (𝓝 (∫ point, (if den point = 0 then (1 : ℝ) else 0) ∂μ)) := by
  refine tendsto_integral_of_dominated_convergence (fun _ ↦ (1 : ℝ))
    (fun K ↦ ((measurable_const.sub hdenMeasurable).pow_const K).aestronglyMeasurable)
    (integrable_const 1) (fun K ↦ ae_of_all _ fun point ↦ ?_) (ae_of_all _ fun point ↦ ?_)
  · rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (sub_nonneg.mpr (hden1 point)) K)]
    exact pow_le_one₀ (sub_nonneg.mpr (hden1 point)) (by linarith [hden0 point])
  · rcases eq_or_lt_of_le (hden0 point) with hzero | hpos
    · rw [if_pos hzero.symm, ← hzero, sub_zero]
      simp only [one_pow]
      exact tendsto_const_nhds
    · rw [if_neg hpos.ne']
      exact tendsto_pow_atTop_nhds_zero_of_lt_one (sub_nonneg.mpr (hden1 point)) (by linarith)

/-- **Where the denominator is positive almost surely the certificate tends to zero.**  When
`0 ≤ den ≤ 1` and `den > 0` almost surely, the integral of `(1 - den)ᴷ` tends to zero, so the
truncated expansion is exact in the limit with a vanishing error bar. -/
theorem tendsto_integral_pow_complement_zero {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (den : Ω → ℝ) (hdenMeasurable : Measurable den)
    (hden0 : ∀ point, 0 ≤ den point) (hden1 : ∀ point, den point ≤ 1)
    (hpos : ∀ᵐ point ∂μ, 0 < den point) :
    Filter.Tendsto (fun K : ℕ ↦ ∫ point, (1 - den point) ^ K ∂μ) Filter.atTop (𝓝 0) := by
  have hlimit := tendsto_integral_pow_complement μ den hdenMeasurable hden0 hden1
  have hzero : ∫ point, (if den point = 0 then (1 : ℝ) else 0) ∂μ = 0 :=
    integral_eq_zero_of_ae (hpos.mono fun point hp ↦ if_neg hp.ne')
  rwa [hzero] at hlimit

/-! ## The certificate polynomial -/

section CertificatePolynomial

variable {State : Type*} [Fintype State] {Score : Type*} [Fintype Score]

/-- The truncation certificate `(1 - (TP + c))ᴷ` of the positive quotient of a cell `c` of the
confusion report, as a polynomial in the population probability vector. -/
def certificatePolynomial (report : State → Score × Bool) (called : Score → Bool)
    (other : Bool × Bool) (K : ℕ) : MvPolynomial State ℝ :=
  (1 - (cellPolynomial (confusionReport report called) (true, true)
    + cellPolynomial (confusionReport report called) other)) ^ K

/-- The certificate polynomial evaluates to `(1 - (TP + c))ᴷ` of the confusion report law. -/
theorem eval_certificatePolynomial (law : FiniteReportLaw State)
    (report : State → Score × Bool) (called : Score → Bool) (other : Bool × Bool) (K : ℕ) :
    eval law.mass (certificatePolynomial report called other K)
      = (1 - ((law.pushforward (confusionReport report called)).mass (true, true)
        + (law.pushforward (confusionReport report called)).mass other)) ^ K := by
  simp only [certificatePolynomial, map_pow, map_sub, map_one, map_add, eval_cellPolynomial]

/-- The certificate polynomial has total degree at most `K`. -/
theorem totalDegree_certificatePolynomial_le (report : State → Score × Bool)
    (called : Score → Bool) (other : Bool × Bool) (K : ℕ) :
    (certificatePolynomial report called other K).totalDegree ≤ K := by
  have hcells := (totalDegree_add (cellPolynomial (confusionReport report called) (true, true))
    (cellPolynomial (confusionReport report called) other)).trans
      (max_le (totalDegree_cellPolynomial_le _ _) (totalDegree_cellPolynomial_le _ _))
  have hcomplement := (totalDegree_sub 1
    (cellPolynomial (confusionReport report called) (true, true)
      + cellPolynomial (confusionReport report called) other)).trans
      (max_le (by rw [totalDegree_one]; exact Nat.zero_le 1) hcells)
  exact ((totalDegree_pow _ K).trans (Nat.mul_le_mul_left K hcomplement)).trans (by omega)

end CertificatePolynomial

variable {Deme Locus : Type*} {Allele : Locus → Type*}
variable [Fintype Deme] [DecidableEq Deme] [Fintype Locus] [DecidableEq Locus]
  [∀ ℓ, Fintype (Allele ℓ)] [∀ ℓ, DecidableEq (Allele ℓ)]
variable {Score : Type*} [Fintype Score]

attribute [local instance] isMarkovKernel_historyEventKernel isMarkovKernel_rateHistoryKernel

/-! ## Certificates for the expected positive quotients -/

/-- **Truncation certificate for the expected positive quotients.**  Under every Markov kernel, for
every cell `c` other than the true positives, the expected positive quotient `E[TP / (TP + c)]`
minus the first `K` terms of its series lies between zero and the expected certificate
`E[(1 - (TP + c))ᴷ]`. -/
theorem expectedPositiveQuotient_truncation
    (κ : Kernel (FrequencyState Deme Locus Allele) (FrequencyState Deme Locus Allele))
    [IsMarkovKernel κ] (x0 : FrequencyState Deme Locus Allele) (deme : Deme)
    (report : FullHaplotype Locus Allele → Score × Bool) (called : Score → Bool)
    (other : Bool × Bool) (hother : (true, true) ≠ other) (K : ℕ) :
    0 ≤ expectedPositiveQuotient κ x0 deme report called other
        - ∑ k ∈ Finset.range K,
          ∫ y, eval (stateLaw y deme).mass (positiveTermPolynomial report called other k) ∂(κ x0)
      ∧ expectedPositiveQuotient κ x0 deme report called other
          - ∑ k ∈ Finset.range K,
            ∫ y, eval (stateLaw y deme).mass (positiveTermPolynomial report called other k)
              ∂(κ x0)
        ≤ ∫ y, eval (stateLaw y deme).mass (certificatePolynomial report called other K)
          ∂(κ x0) := by
  have htruncation := integral_quotient_truncation (κ x0) _ _
    (continuous_pushforwardMass deme (confusionReport report called) (true, true)).measurable
    ((continuous_pushforwardMass deme (confusionReport report called) (true, true)).add
      (continuous_pushforwardMass deme (confusionReport report called) other)).measurable
    (fun _ ↦ FiniteReportLaw.mass_nonneg _ _)
    (fun _ ↦ le_add_of_nonneg_right (FiniteReportLaw.mass_nonneg _ _))
    (fun _ ↦ cellMass_add_le_one _ hother) K
  simp only [expectedPositiveQuotient, eval_positiveTermPolynomial, eval_certificatePolynomial]
  rw [htruncation.1]
  exact htruncation.2

/-- **Truncation certificates for the expected recall and precision.**  Under every Markov kernel
the expected per-population recall minus the first `K` terms of its series lies between zero and
`E[(1 - (TP + FN))ᴷ]`, the expected complement power of the case probability.  The expected
precision minus the first `K` terms of its series lies between zero and `E[(1 - (TP + FP))ᴷ]`,
the expected complement power of the called fraction. -/
theorem integral_recallRate_precision_truncation
    (κ : Kernel (FrequencyState Deme Locus Allele) (FrequencyState Deme Locus Allele))
    [IsMarkovKernel κ] (x0 : FrequencyState Deme Locus Allele) (deme : Deme)
    (report : FullHaplotype Locus Allele → Score × Bool) (called : Score → Bool) (K : ℕ) :
    (0 ≤ (∫ y, (ruleConfusion ((stateLaw y deme).pushforward report) called).recallRate ∂(κ x0))
        - ∑ k ∈ Finset.range K, ∫ y, eval (stateLaw y deme).mass
          (positiveTermPolynomial report called (false, true) k) ∂(κ x0)
      ∧ (∫ y, (ruleConfusion ((stateLaw y deme).pushforward report) called).recallRate ∂(κ x0))
          - ∑ k ∈ Finset.range K, ∫ y, eval (stateLaw y deme).mass
            (positiveTermPolynomial report called (false, true) k) ∂(κ x0)
        ≤ ∫ y, eval (stateLaw y deme).mass (certificatePolynomial report called (false, true) K)
          ∂(κ x0))
    ∧ (0 ≤ (∫ y, (ruleConfusion ((stateLaw y deme).pushforward report) called).precision ∂(κ x0))
        - ∑ k ∈ Finset.range K, ∫ y, eval (stateLaw y deme).mass
          (positiveTermPolynomial report called (true, false) k) ∂(κ x0)
      ∧ (∫ y, (ruleConfusion ((stateLaw y deme).pushforward report) called).precision ∂(κ x0))
          - ∑ k ∈ Finset.range K, ∫ y, eval (stateLaw y deme).mass
            (positiveTermPolynomial report called (true, false) k) ∂(κ x0)
        ≤ ∫ y, eval (stateLaw y deme).mass (certificatePolynomial report called (true, false) K)
          ∂(κ x0)) := by
  obtain ⟨hrecall, hprecision⟩ := integral_recallRate_precision κ x0 deme report called
  rw [hrecall, hprecision]
  exact ⟨expectedPositiveQuotient_truncation κ x0 deme report called _ (by decide) K,
    expectedPositiveQuotient_truncation κ x0 deme report called _ (by decide) K⟩

/-- **The certificates through the propagated moments.**  Under a Markov kernel with dual moments
at every budget, the partial sum of the expected positive quotient of a cell `c` is a finite sum of
budget-`(k + 1)` dot products, and its truncation certificate is one budget-`K` dot product.

Assumes: `∀ n, HasDualMoments κ n (M n)`. -/
theorem expectedPositiveQuotient_truncation_dotProduct (ℓ₀ : Locus)
    (κ : Kernel (FrequencyState Deme Locus Allele) (FrequencyState Deme Locus Allele))
    [IsMarkovKernel κ] (M : ∀ n : ℕ, BudgetMatrix Deme Locus Allele n)
    (hmoment : ∀ n : ℕ, HasDualMoments κ n (M n)) (x0 : FrequencyState Deme Locus Allele)
    (deme : Deme) (report : FullHaplotype Locus Allele → Score × Bool) (called : Score → Bool)
    (other : Bool × Bool) (hother : (true, true) ≠ other) (K : ℕ) :
    0 ≤ expectedPositiveQuotient κ x0 deme report called other
        - ∑ k ∈ Finset.range K, budgetCoefficients ℓ₀ (fun _ ↦ k + 1)
            (demePolynomial deme (positiveTermPolynomial report called other k))
          ⬝ᵥ (M (k + 1) *ᵥ budgetMomentFeature (fun _ ↦ k + 1) x0)
      ∧ expectedPositiveQuotient κ x0 deme report called other
          - ∑ k ∈ Finset.range K, budgetCoefficients ℓ₀ (fun _ ↦ k + 1)
              (demePolynomial deme (positiveTermPolynomial report called other k))
            ⬝ᵥ (M (k + 1) *ᵥ budgetMomentFeature (fun _ ↦ k + 1) x0)
        ≤ budgetCoefficients ℓ₀ (fun _ ↦ K)
            (demePolynomial deme (certificatePolynomial report called other K))
          ⬝ᵥ (M K *ᵥ budgetMomentFeature (fun _ ↦ K) x0) := by
  have hterms : ∑ k ∈ Finset.range K, budgetCoefficients ℓ₀ (fun _ ↦ k + 1)
        (demePolynomial deme (positiveTermPolynomial report called other k))
      ⬝ᵥ (M (k + 1) *ᵥ budgetMomentFeature (fun _ ↦ k + 1) x0)
      = ∑ k ∈ Finset.range K,
        ∫ y, eval (stateLaw y deme).mass (positiveTermPolynomial report called other k) ∂(κ x0) :=
    Finset.sum_congr rfl fun k _ ↦ (integral_eval_stateLaw_eq_dotProduct ℓ₀ (k + 1) κ
      (M (k + 1)) (hmoment (k + 1)) deme _
      (totalDegree_positiveTermPolynomial_le report called other k) x0).symm
  rw [hterms, ← integral_eval_stateLaw_eq_dotProduct ℓ₀ K κ (M K) (hmoment K) deme _
    (totalDegree_certificatePolynomial_le report called other K) x0]
  exact expectedPositiveQuotient_truncation κ x0 deme report called other hother K

/-- **The certificates along a history of epochs, splits and pulses.** -/
theorem expectedPositiveQuotient_truncation_historyEventKernel (ℓ₀ : Locus)
    (hap₀ : FullHaplotype Locus Allele)
    (events : List ((NeutralRates Deme Locus Allele × ℝ≥0) ⊕ PulseMatrix Deme))
    (x0 : FrequencyState Deme Locus Allele) (deme : Deme)
    (report : FullHaplotype Locus Allele → Score × Bool) (called : Score → Bool)
    (other : Bool × Bool) (hother : (true, true) ≠ other) (K : ℕ) :
    0 ≤ expectedPositiveQuotient (historyEventKernel ℓ₀ hap₀ events) x0 deme report called other
        - ∑ k ∈ Finset.range K, budgetCoefficients ℓ₀ (fun _ ↦ k + 1)
            (demePolynomial deme (positiveTermPolynomial report called other k))
          ⬝ᵥ (historyEventPropagator (fun _ ↦ k + 1) events
            *ᵥ budgetMomentFeature (fun _ ↦ k + 1) x0)
      ∧ expectedPositiveQuotient (historyEventKernel ℓ₀ hap₀ events) x0 deme report called other
          - ∑ k ∈ Finset.range K, budgetCoefficients ℓ₀ (fun _ ↦ k + 1)
              (demePolynomial deme (positiveTermPolynomial report called other k))
            ⬝ᵥ (historyEventPropagator (fun _ ↦ k + 1) events
              *ᵥ budgetMomentFeature (fun _ ↦ k + 1) x0)
        ≤ budgetCoefficients ℓ₀ (fun _ ↦ K)
            (demePolynomial deme (certificatePolynomial report called other K))
          ⬝ᵥ (historyEventPropagator (fun _ ↦ K) events *ᵥ budgetMomentFeature (fun _ ↦ K) x0) :=
  expectedPositiveQuotient_truncation_dotProduct ℓ₀ (historyEventKernel ℓ₀ hap₀ events)
    (fun n ↦ historyEventPropagator (fun _ ↦ n) events)
    (hasDualMoments_historyEventKernel ℓ₀ hap₀ events) x0 deme report called other hother K

/-- **The certificates along a time-varying rate history.** -/
theorem expectedPositiveQuotient_truncation_rateHistoryKernel
    {rates : ℝ → NeutralRates Deme Locus Allele} {T : ℝ} (hT : 0 ≤ T)
    (hcontinuous : ∀ capacity : Locus → ℕ,
      ContinuousOn (fun t ↦ dualGenerator (rates t) capacity) (Set.Icc 0 T))
    (ℓ₀ : Locus) (hap₀ : FullHaplotype Locus Allele) (x0 : FrequencyState Deme Locus Allele)
    (deme : Deme) (report : FullHaplotype Locus Allele → Score × Bool) (called : Score → Bool)
    (other : Bool × Bool) (hother : (true, true) ≠ other) (K : ℕ) :
    0 ≤ expectedPositiveQuotient (rateHistoryKernel rates ℓ₀ hap₀ hT hcontinuous) x0 deme report
          called other
        - ∑ k ∈ Finset.range K, budgetCoefficients ℓ₀ (fun _ ↦ k + 1)
            (demePolynomial deme (positiveTermPolynomial report called other k))
          ⬝ᵥ (rateHistoryDualPropagator rates (fun _ ↦ k + 1) T
            *ᵥ budgetMomentFeature (fun _ ↦ k + 1) x0)
      ∧ expectedPositiveQuotient (rateHistoryKernel rates ℓ₀ hap₀ hT hcontinuous) x0 deme report
            called other
          - ∑ k ∈ Finset.range K, budgetCoefficients ℓ₀ (fun _ ↦ k + 1)
              (demePolynomial deme (positiveTermPolynomial report called other k))
            ⬝ᵥ (rateHistoryDualPropagator rates (fun _ ↦ k + 1) T
              *ᵥ budgetMomentFeature (fun _ ↦ k + 1) x0)
        ≤ budgetCoefficients ℓ₀ (fun _ ↦ K)
            (demePolynomial deme (certificatePolynomial report called other K))
          ⬝ᵥ (rateHistoryDualPropagator rates (fun _ ↦ K) T
            *ᵥ budgetMomentFeature (fun _ ↦ K) x0) :=
  expectedPositiveQuotient_truncation_dotProduct ℓ₀
    (rateHistoryKernel rates ℓ₀ hap₀ hT hcontinuous)
    (fun n ↦ rateHistoryDualPropagator rates (fun _ ↦ n) T)
    (hasDualMoments_rateHistoryKernel hT hcontinuous ℓ₀ hap₀) x0 deme report called other hother K

/-- **The expected certificate tends to the probability of an empty denominator.**  Under every
Markov kernel, for every cell `c` other than the true positives, the expected certificate
`E[(1 - (TP + c))ᴷ]` tends to the probability that `TP + c` vanishes. -/
theorem tendsto_certificate
    (κ : Kernel (FrequencyState Deme Locus Allele) (FrequencyState Deme Locus Allele))
    [IsMarkovKernel κ] (x0 : FrequencyState Deme Locus Allele) (deme : Deme)
    (report : FullHaplotype Locus Allele → Score × Bool) (called : Score → Bool)
    (other : Bool × Bool) (hother : (true, true) ≠ other) :
    Filter.Tendsto (fun K : ℕ ↦
        ∫ y, eval (stateLaw y deme).mass (certificatePolynomial report called other K) ∂(κ x0))
      Filter.atTop
      (𝓝 (∫ y, (if ((stateLaw y deme).pushforward (confusionReport report called)).mass (true, true)
          + ((stateLaw y deme).pushforward (confusionReport report called)).mass other = 0
        then (1 : ℝ) else 0) ∂(κ x0))) := by
  have hlimit := tendsto_integral_pow_complement (κ x0) _
    ((continuous_pushforwardMass deme (confusionReport report called) (true, true)).add
      (continuous_pushforwardMass deme (confusionReport report called) other)).measurable
    (fun _ ↦ add_nonneg (FiniteReportLaw.mass_nonneg _ _) (FiniteReportLaw.mass_nonneg _ _))
    (fun _ ↦ cellMass_add_le_one _ hother)
  simp only [eval_certificatePolynomial]
  exact hlimit

/-- **Where the denominator is positive almost surely the expected certificate tends to zero.**
For every cell `c` other than the true positives, if `TP + c > 0` almost surely under the kernel,
the expected certificate `E[(1 - (TP + c))ᴷ]` tends to zero. -/
theorem tendsto_certificate_zero_of_ae_pos
    (κ : Kernel (FrequencyState Deme Locus Allele) (FrequencyState Deme Locus Allele))
    [IsMarkovKernel κ] (x0 : FrequencyState Deme Locus Allele) (deme : Deme)
    (report : FullHaplotype Locus Allele → Score × Bool) (called : Score → Bool)
    (other : Bool × Bool) (hother : (true, true) ≠ other)
    (hpos : ∀ᵐ y ∂(κ x0),
      0 < ((stateLaw y deme).pushforward (confusionReport report called)).mass (true, true)
        + ((stateLaw y deme).pushforward (confusionReport report called)).mass other) :
    Filter.Tendsto (fun K : ℕ ↦
        ∫ y, eval (stateLaw y deme).mass (certificatePolynomial report called other K) ∂(κ x0))
      Filter.atTop (𝓝 0) := by
  have hlimit := tendsto_integral_pow_complement_zero (κ x0) _
    ((continuous_pushforwardMass deme (confusionReport report called) (true, true)).add
      (continuous_pushforwardMass deme (confusionReport report called) other)).measurable
    (fun _ ↦ add_nonneg (FiniteReportLaw.mass_nonneg _ _) (FiniteReportLaw.mass_nonneg _ _))
    (fun _ ↦ cellMass_add_le_one _ hother) hpos
  simp only [eval_certificatePolynomial]
  exact hlimit

/-- **The recall certificate vanishes where cases are present almost surely.**  If the case
probability of a deme is positive almost surely under the kernel, the expected recall certificate
`E[(1 - p)ᴷ]` of every rule tends to zero, so the truncated recall series is exact in the limit
with a vanishing error bar. -/
theorem tendsto_recallCertificate_zero_of_ae_pos
    (κ : Kernel (FrequencyState Deme Locus Allele) (FrequencyState Deme Locus Allele))
    [IsMarkovKernel κ] (x0 : FrequencyState Deme Locus Allele) (deme : Deme)
    (report : FullHaplotype Locus Allele → Score × Bool) (called : Score → Bool)
    (hpos : ∀ᵐ y ∂(κ x0), 0 < ((stateLaw y deme).pushforward report).binaryCaseMass Prod.snd) :
    Filter.Tendsto (fun K : ℕ ↦ ∫ y, eval (stateLaw y deme).mass
        (certificatePolynomial report called (false, true) K) ∂(κ x0))
      Filter.atTop (𝓝 0) := by
  have hcase : ∀ y : FrequencyState Deme Locus Allele,
      ((stateLaw y deme).pushforward report).binaryCaseMass Prod.snd
        = ((stateLaw y deme).pushforward (confusionReport report called)).mass (true, true)
          + ((stateLaw y deme).pushforward (confusionReport report called)).mass (false, true) :=
    fun y ↦ by
      rw [← prevalence_ruleConfusion _ called]
      simp only [Foundations.ConfusionMatrix.prevalence, ruleConfusion, calledMass_pushforward,
        clearedMass_pushforward]
  exact tendsto_certificate_zero_of_ae_pos κ x0 deme report called (false, true) (by decide)
    (hpos.mono fun y hy ↦ hcase y ▸ hy)

end

end Descent.Portability.EndToEndDecisionCertificates
