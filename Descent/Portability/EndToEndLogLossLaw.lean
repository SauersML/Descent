/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.EndToEndBrierLaw

assert_below Descent.Decision Descent.Program

/-!
# The end-to-end law of log loss, entropy and mutual information

`EndToEndBrierLaw` carries the repaired Brier loss of a finite score alphabet through every kernel
with dual moments.  This module carries the logarithmic metrics of a binary outcome: the repaired
log loss, which is the conditional entropy of the outcome given the score, the outcome entropy and
the mutual information.

The entropy series.  `η(x) = -x log x` is Mathlib's `Real.negMulLog`, with `η(0) = 0`.  On the unit
interval it is the sum over `k` of `x (1 - x)ᵏ⁺¹ / (k + 1)` (`negMulLog_hasSum`): the corpus series
of `-log` (`LogLossSeriesCertificate.neg_log_hasSum`) multiplied by `x`.  Multiplying the corpus
enclosure of `-log` by `x` also cancels its division by the forecast.  After `K` terms the tail lies
between `0` and `(1 - x)ᴷ⁺¹ / (K + 1)` (`negMulLog_truncation_mem`), and so below `1 / (K + 1)`
uniformly (`negMulLog_sub_partialSum_le_uniform`).  The entropy `Σ_r η(m_r)` of a finite report law
(`reportEntropy`) is the series of the order-`k` terms `Σ_r m_r (1 - m_r)ᵏ⁺¹`, divided by `k + 1`
(`reportEntropyTerm`, `hasSum_reportEntropy`).  Truncating after `K` terms leaves an error between
`0` and `|Report| / (K + 1)` (`reportEntropy_sub_truncation_mem`).  Pushing a law forward twice
gives the entropy of the composite pushforward (`reportEntropy_pushforward_pushforward`).

Scope.  Score groups form a finite alphabet and outcomes are binary; one chromosome is sampled per
individual.

## Empirical status

None.  The bodies here are a pointwise power series for the logarithm, its truncation error, and
finite sums of masses, so no measurement can bear on them.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.EndToEndLogLossLaw

open MeasureTheory ProbabilityTheory MvPolynomial Descent.Coalescent PartialHaplotypeCarrier
  PartialHaplotypeDualGenerator PartialHaplotypeDualSemigroup NeutralFellerGenerator
  NeutralPolynomialSemigroup PartialHaplotypeMicroscopicApproximation PartialHaplotypePulseKernel
  NeutralPulseHistoryKernel NeutralRateHistoryRealization NeutralRateHistoryKernel
  ReplicaMetricInstances EndToEndPortabilityLaw EndToEndDiscriminationLaw EndToEndBrierLaw
open Filter
open scoped Matrix NNReal ENNReal Topology

noncomputable section

/-! ## The entropy series -/

/-- **The entropy function as a series.**  On the unit interval `η(x) = -x log x` is the sum of
`x (1 - x)ᵏ⁺¹ / (k + 1)`.  For positive `x` this is the series of `-log x` multiplied by `x`; at
`x = 0` every term and `η(0)` vanish. -/
theorem negMulLog_hasSum (x : ℝ) (hzero : 0 ≤ x) (hone : x ≤ 1) :
    HasSum (fun order : ℕ ↦ x * (1 - x) ^ (order + 1) / ((order : ℝ) + 1))
      (Real.negMulLog x) := by
  rcases hzero.eq_or_lt with hx | hpos
  · subst hx
    simp only [zero_mul, zero_div, Real.negMulLog_zero]
    exact hasSum_zero
  · have hseries := (LogLossSeriesCertificate.neg_log_hasSum x hpos hone).mul_left x
    have hvalue : x * -Real.log x = Real.negMulLog x := by
      show x * -Real.log x = -x * Real.log x
      ring
    have hterms : (fun order : ℕ ↦ x * (1 - x) ^ (order + 1) / ((order : ℝ) + 1))
        = fun order : ℕ ↦ x * ((1 - x) ^ (order + 1) / ((order : ℝ) + 1)) :=
      funext fun order ↦ mul_div_assoc _ _ _
    rw [hterms, ← hvalue]
    exact hseries

/-- **The entropy tail without division.**  On the unit interval the partial sums of the entropy
series approach `η(x)` from below, and the gap after `terms` terms is at most
`(1 - x)ᵗᵉʳᵐˢ⁺¹ / (terms + 1)`.  Multiplying the corpus enclosure of `-log x` by `x` cancels the
division by `x` in its tail bound. -/
theorem negMulLog_truncation_mem (x : ℝ) (hzero : 0 ≤ x) (hone : x ≤ 1) (terms : ℕ) :
    0 ≤ Real.negMulLog x
        - ∑ order ∈ Finset.range terms, x * (1 - x) ^ (order + 1) / ((order : ℝ) + 1)
    ∧ Real.negMulLog x
        - ∑ order ∈ Finset.range terms, x * (1 - x) ^ (order + 1) / ((order : ℝ) + 1)
      ≤ (1 - x) ^ (terms + 1) / ((terms : ℝ) + 1) := by
  rcases hzero.eq_or_lt with hx | hpos
  · subst hx
    simp only [zero_mul, zero_div, Finset.sum_const_zero, Real.negMulLog_zero, sub_zero, one_pow,
      le_refl, true_and]
    positivity
  · have hscaled : x * (-Real.log x
        - ∑ order ∈ Finset.range terms, (1 - x) ^ (order + 1) / ((order : ℝ) + 1))
        = Real.negMulLog x
          - ∑ order ∈ Finset.range terms, x * (1 - x) ^ (order + 1) / ((order : ℝ) + 1) := by
      rw [mul_sub, Finset.mul_sum]
      congr 1
      · show x * -Real.log x = -x * Real.log x
        ring
      · exact Finset.sum_congr rfl fun order _ ↦ (mul_div_assoc _ _ _).symm
    have hcancel : x * ((1 - x) ^ (terms + 1) / (((terms : ℝ) + 1) * x))
        = (1 - x) ^ (terms + 1) / ((terms : ℝ) + 1) := by
      rw [← div_div, mul_div_cancel₀ _ hpos.ne']
    have hlower :=
      sub_nonneg.mpr (LogLossSeriesCertificate.partial_sum_le_neg_log x hpos hone terms)
    have hupper := LogLossSeriesCertificate.neg_log_tail_bound x hpos hone terms
    rw [← hscaled, ← hcancel]
    exact ⟨mul_nonneg hzero hlower, mul_le_mul_of_nonneg_left hupper hzero⟩

/-- The entropy tail after `terms` terms is at most `1 / (terms + 1)`, uniformly on the unit
interval. -/
theorem negMulLog_sub_partialSum_le_uniform (x : ℝ) (hzero : 0 ≤ x) (hone : x ≤ 1)
    (terms : ℕ) :
    Real.negMulLog x
        - ∑ order ∈ Finset.range terms, x * (1 - x) ^ (order + 1) / ((order : ℝ) + 1)
      ≤ 1 / ((terms : ℝ) + 1) :=
  (negMulLog_truncation_mem x hzero hone terms).2.trans
    (div_le_div_of_nonneg_right (pow_le_one₀ (by linarith) (by linarith)) (by positivity))

/-! ## The entropy of a finite report law -/

section ReportEntropy

variable {Report : Type*} [Fintype Report]

/-- The mass of one report is at most one. -/
theorem reportMass_le_one (law : FiniteReportLaw Report) (report : Report) :
    law.mass report ≤ 1 := by
  have hsingle := Finset.single_le_sum (f := law.mass) (fun other _ ↦ law.mass_nonneg other)
    (Finset.mem_univ report)
  rwa [law.mass_sum] at hsingle

/-- **Shannon entropy of a finite report law**, `Σ_r η(m_r)`. -/
def reportEntropy (law : FiniteReportLaw Report) : ℝ :=
  ∑ report, Real.negMulLog (law.mass report)

/-- The order-`k` entropy term `Σ_r m_r (1 - m_r)ᵏ⁺¹` of a finite report law. -/
def reportEntropyTerm (law : FiniteReportLaw Report) (order : ℕ) : ℝ :=
  ∑ report, law.mass report * (1 - law.mass report) ^ (order + 1)

/-- Every entropy term is nonnegative. -/
theorem reportEntropyTerm_nonneg (law : FiniteReportLaw Report) (order : ℕ) :
    0 ≤ reportEntropyTerm law order :=
  Finset.sum_nonneg fun report _ ↦ mul_nonneg (law.mass_nonneg report)
    (pow_nonneg (sub_nonneg.mpr (reportMass_le_one law report)) _)

/-- **The entropy of a report law as a series** of its order-`k` terms divided by `k + 1`. -/
theorem hasSum_reportEntropy (law : FiniteReportLaw Report) :
    HasSum (fun order : ℕ ↦ reportEntropyTerm law order / ((order : ℝ) + 1))
      (reportEntropy law) := by
  have hcells := hasSum_sum (s := Finset.univ) fun report (_ : report ∈ Finset.univ) ↦
    negMulLog_hasSum (law.mass report) (law.mass_nonneg report) (reportMass_le_one law report)
  simpa only [reportEntropyTerm, reportEntropy, Finset.sum_div] using hcells

/-- **The entropy truncation certificate.**  After `terms` terms the entropy series of a report
law leaves an error between `0` and `|Report| / (terms + 1)`, with no division by any mass. -/
theorem reportEntropy_sub_truncation_mem (law : FiniteReportLaw Report) (terms : ℕ) :
    0 ≤ reportEntropy law
        - ∑ order ∈ Finset.range terms, reportEntropyTerm law order / ((order : ℝ) + 1)
    ∧ reportEntropy law
        - ∑ order ∈ Finset.range terms, reportEntropyTerm law order / ((order : ℝ) + 1)
      ≤ (Fintype.card Report : ℝ) / ((terms : ℝ) + 1) := by
  have hswap : reportEntropy law
      - ∑ order ∈ Finset.range terms, reportEntropyTerm law order / ((order : ℝ) + 1)
      = ∑ report, (Real.negMulLog (law.mass report) - ∑ order ∈ Finset.range terms,
          law.mass report * (1 - law.mass report) ^ (order + 1) / ((order : ℝ) + 1)) := by
    rw [reportEntropy, Finset.sum_sub_distrib]
    congr 1
    simp only [reportEntropyTerm, Finset.sum_div]
    exact Finset.sum_comm
  rw [hswap]
  refine ⟨Finset.sum_nonneg fun report _ ↦ (negMulLog_truncation_mem (law.mass report)
    (law.mass_nonneg report) (reportMass_le_one law report) terms).1, ?_⟩
  calc ∑ report, (Real.negMulLog (law.mass report) - ∑ order ∈ Finset.range terms,
          law.mass report * (1 - law.mass report) ^ (order + 1) / ((order : ℝ) + 1))
      ≤ ∑ _report : Report, 1 / ((terms : ℝ) + 1) :=
        Finset.sum_le_sum fun report _ ↦ negMulLog_sub_partialSum_le_uniform (law.mass report)
          (law.mass_nonneg report) (reportMass_le_one law report) terms
    _ = (Fintype.card Report : ℝ) / ((terms : ℝ) + 1) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one_div]

/-- **Entropy of an iterated pushforward.**  Pushing a report law forward twice has the entropy of
the single pushforward along the composite report map. -/
theorem reportEntropy_pushforward_pushforward {State Report' : Type*} [Fintype State]
    [Fintype Report'] [DecidableEq Report] [DecidableEq Report'] (law : FiniteReportLaw State)
    (first : State → Report) (second : Report → Report') :
    reportEntropy ((law.pushforward first).pushforward second)
      = reportEntropy (law.pushforward fun state ↦ second (first state)) := by
  unfold reportEntropy
  refine Finset.sum_congr rfl fun selected _ ↦ ?_
  rw [pushforwardMass_eq_expectation, FiniteReportLaw.expectation_pushforward,
    ← pushforwardMass_eq_expectation]

end ReportEntropy

end

end Descent.Portability.EndToEndLogLossLaw
