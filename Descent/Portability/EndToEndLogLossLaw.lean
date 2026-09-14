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

The repaired log loss.  For a score-outcome law with case mass `a_s`, control mass `b_s` and group
mass `q_s = a_s + b_s`, the conditional entropy is `H(Y | S) = Σ_s [η(a_s) + η(b_s) - η(q_s)]`
(`conditionalEntropy`), the joint entropy minus the score entropy
(`pushforward_fst_mass`, `conditionalEntropy_eq_reportEntropy_sub`).  It is the log loss of the
forecast repaired to each group's realized rate (`repairedGroupForecast`,
`repairedGroupForecast_mem`, `repairedGroupLoss_eq`, `expectation_neg_log_repairedGroupForecast`),
hence nonnegative (`conditionalEntropy_nonneg`) and equal to the corpus extended log loss read at
that forecast (`expectedLogLoss_eq_ofReal_of_pos`, `expectedLogLoss_repairedGroupForecast`).  For a
binary score it is the corpus `UniformPenetranceArchitecture.repairedLogLoss`
(`repairedGroupForecast_eq_repairedForecast`, `conditionalEntropy_eq_repairedLogLoss`).  The mutual
information is `I(S; Y) = H(Y) - H(Y | S)` (`mutualInformation`).

Fixed forecasts.  The log loss of fixed group forecasts `v_s` (`groupForecast`, `forecastLogLoss`)
is linear in the report law.  For `v_s ∈ (0, 1)` it is the finite corpus extended log loss
(`expectedLogLoss_groupForecast`) and at least the conditional entropy, by Gibbs' inequality
(`cellLoss_ge`, `conditionalEntropy_le_forecastLogLoss`).  A forecast `v_s = 0` against a group of
positive case mass, or `v_s = 1` against a group of positive control mass, gives infinite loss
(`expectedLogLoss_groupForecast_eq_top`).

Through a kernel.  The order-`k` entropy term is a population polynomial of total degree at most
`k + 2` (`entropyTermPolynomial`, `eval_entropyTermPolynomial`,
`totalDegree_entropyTermPolynomial_le`, `conditionalEntropyTermPolynomial`,
`mutualInformationTermPolynomial`, `totalDegree_conditionalEntropyTermPolynomial_le`,
`totalDegree_mutualInformationTermPolynomial_le`).  Under every Markov kernel the truncation after
`K` terms falls short of the expected entropy of a report law by between `0` and
`|Report| / (K + 1)` (`expectedEntropy`, `continuous_reportEntropy`,
`continuous_reportEntropyTerm`, `expectedEntropy_sub_truncation_mem`).  The terms are
nonnegative, so this squeezes the partial sums and the expected entropy is the series of expected
terms (`hasSum_expectedEntropy`).  The expected chain rule carries the series to the expected
conditional entropy and mutual information (`expectedConditionalEntropy`,
`expectedMutualInformation`, `continuous_conditionalEntropy`, `expectedConditionalEntropy_eq_sub`,
`expectedMutualInformation_eq_sub`, `integral_eval_conditionalEntropyTermPolynomial`,
`integral_eval_mutualInformationTermPolynomial`, `hasSum_expectedConditionalEntropy`,
`hasSum_expectedMutualInformation`).  The truncation error lies between `-|Score| / (K + 1)` and
`2 |Score| / (K + 1)` for the conditional entropy (`expectedConditionalEntropy_sub_truncation_mem`),
and between `-2 |Score| / (K + 1)` and `(|Score| + 2) / (K + 1)` for the mutual information
(`expectedMutualInformation_sub_truncation_mem`).  Through the propagated moments each quantity is
a series of budget-`(k + 2)` dot products divided by `k + 1`
(`tsum_integral_eval_eq_tsum_dotProduct`, `expectedEntropy_eq_tsum_dotProduct`,
`expectedConditionalEntropy_eq_tsum_dotProduct`,
`expectedMutualInformation_eq_tsum_dotProduct`), along a history of epochs, splits and pulses and
along a rate history (`expectedEntropy_historyEventKernel`, `expectedEntropy_rateHistoryKernel`,
`expectedConditionalEntropy_and_mutualInformation_historyEventKernel`,
`expectedConditionalEntropy_and_mutualInformation_rateHistoryKernel`).  Two histories whose
propagated moments agree at every budget `k + 2` have equal expected entropies
(`expectedEntropy_eq_of_moments_eq`,
`expectedConditionalEntropy_and_mutualInformation_eq_of_moments_eq`).  The expected log loss of
fixed forecasts is exact at budget one (`expectedForecastLogLoss`, `continuous_forecastLogLoss`,
`expectedForecastLogLoss_eq_dotProduct`) and bounds the expected conditional entropy from above
(`expectedConditionalEntropy_le_expectedForecastLogLoss`).

Pseudo-`R²`.  McFadden's pseudo-`R²`, `E I(S; Y) / E H(Y)` in ratio-of-expectations form
(`expectedPseudoRSquared`), and its target-over-source portability (`pseudoRSquaredPortability`)
are ratios of these series (`pseudoRSquaredPortability_eq_tsum_dotProduct`).  Equal propagated
moments give equal portability (`pseudoRSquaredPortability_eq_of_moments_eq`).

Significance.  The logarithmic metrics of a clinical risk score (the repaired log loss, the
information the score carries about the outcome, and pseudo-`R²` portability) run from the
demographic process law through convergent series of finite matrix computations.  Every truncation
has an explicit division-free error bound, so no floor on the forecasts is needed.

Scope.  Score groups form a finite alphabet and outcomes are binary; one chromosome is sampled per
individual.  The expected metrics average the population metrics over the process law, and
pseudo-`R²` is taken in ratio-of-expectations form.  Whether finitely many propagated moments
determine the expected entropies is not settled here: no pair of histories that agree at a finite
budget and differ in expected entropy is constructed.

## Empirical status

None.  The bodies here are a pointwise power series for the logarithm, its division-free truncation
error, elementary inequalities of the logarithm, and integrals of polynomials against Markov kernels
whose moments are matrix computations of supplied rates, so no measurement can bear on them.
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

/-! ## Conditional entropy and the repaired log loss -/

section ScoreOutcome

variable {Score : Type*} [Fintype Score]

/-- **Conditional entropy of the outcome given the score**,
`H(Y | S) = Σ_s [η(a_s) + η(b_s) - η(q_s)]` for the case mass `a_s`, the control mass `b_s` and the
group mass `q_s = a_s + b_s`. -/
def conditionalEntropy (law : FiniteReportLaw (Score × Bool)) : ℝ :=
  ∑ group, (Real.negMulLog (law.mass (group, true)) + Real.negMulLog (law.mass (group, false))
    - Real.negMulLog (scoreGroupMass law group))

/-- **Mutual information of score and outcome**, `I(S; Y) = H(Y) - H(Y | S)`, where `H(Y)` is the
entropy of the outcome marginal. -/
def mutualInformation (law : FiniteReportLaw (Score × Bool)) : ℝ :=
  reportEntropy (law.pushforward Prod.snd) - conditionalEntropy law

/-- The score marginal of a score-outcome law puts the group mass `q_s` on each score group. -/
theorem pushforward_fst_mass [DecidableEq Score] (law : FiniteReportLaw (Score × Bool))
    (group : Score) : (law.pushforward Prod.fst).mass group = scoreGroupMass law group := by
  rw [pushforwardMass_eq_expectation, FiniteReportLaw.expectation, Fintype.sum_prod_type,
    Finset.sum_eq_single group]
  · simp [Fintype.sum_bool, scoreGroupMass, add_comm]
  · intro other _ hother
    simp [hother]
  · intro hnot
    exact absurd (Finset.mem_univ group) hnot

/-- **Chain rule.**  The conditional entropy is the joint entropy of score and outcome minus the
entropy of the score marginal. -/
theorem conditionalEntropy_eq_reportEntropy_sub [DecidableEq Score]
    (law : FiniteReportLaw (Score × Bool)) :
    conditionalEntropy law = reportEntropy law - reportEntropy (law.pushforward Prod.fst) := by
  simp only [conditionalEntropy, reportEntropy, pushforward_fst_mass, Fintype.sum_prod_type,
    Fintype.sum_bool, Finset.sum_sub_distrib, Finset.sum_add_distrib]

/-- **The repaired forecast** of a finite score alphabet: each score group forecasts its own
realized case rate `a_s / q_s` for a case and its complement for a control. -/
def repairedGroupForecast (law : FiniteReportLaw (Score × Bool)) : Score × Bool → ℝ
  | (group, true) => law.mass (group, true) / scoreGroupMass law group
  | (group, false) => 1 - law.mass (group, true) / scoreGroupMass law group

/-- Every repaired forecast lies in the unit interval. -/
theorem repairedGroupForecast_mem (law : FiniteReportLaw (Score × Bool)) (cell : Score × Bool) :
    0 ≤ repairedGroupForecast law cell ∧ repairedGroupForecast law cell ≤ 1 := by
  have hrate : ∀ group : Score, 0 ≤ law.mass (group, true) / scoreGroupMass law group
      ∧ law.mass (group, true) / scoreGroupMass law group ≤ 1 := fun group ↦
    ⟨div_nonneg (law.mass_nonneg (group, true)) (scoreGroupMass_nonneg law group),
      div_le_one_of_le₀ (caseMass_le_scoreGroupMass law group) (scoreGroupMass_nonneg law group)⟩
  rcases cell with ⟨group, _ | _⟩
  · show 0 ≤ 1 - law.mass (group, true) / scoreGroupMass law group
      ∧ 1 - law.mass (group, true) / scoreGroupMass law group ≤ 1
    exact ⟨sub_nonneg.mpr (hrate group).2, sub_le_self _ (hrate group).1⟩
  · exact hrate group

/-- **One score group's repaired log loss is its entropy contribution.**  For masses `a, b ≥ 0`
with group mass `q = b + a`, `a (-log (a / q)) + b (-log (1 - a / q)) = η(a) + η(b) - η(q)`.  The
proof splits `η(x) = η(q · (x / q))` by `Real.negMulLog_mul`. -/
theorem repairedGroupLoss_eq (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    a * -Real.log (a / (b + a)) + b * -Real.log (1 - a / (b + a))
      = Real.negMulLog a + Real.negMulLog b - Real.negMulLog (b + a) := by
  rcases (add_nonneg hb ha).eq_or_lt with hq | hq
  · have hazero : a = 0 := by linarith
    have hbzero : b = 0 := by linarith
    subst hazero hbzero
    simp
  · have hsplit : ∀ x : ℝ, x * -Real.log (x / (b + a))
        = Real.negMulLog x - x / (b + a) * Real.negMulLog (b + a) := fun x ↦ by
      have hmul := Real.negMulLog_mul (b + a) (x / (b + a))
      rw [mul_div_cancel₀ x hq.ne'] at hmul
      calc x * -Real.log (x / (b + a))
          = -((b + a) * (x / (b + a))) * Real.log (x / (b + a)) := by
            rw [mul_div_cancel₀ x hq.ne']
            ring
        _ = (b + a) * Real.negMulLog (x / (b + a)) := by
            show _ = (b + a) * (-(x / (b + a)) * Real.log (x / (b + a)))
            ring
        _ = Real.negMulLog x - x / (b + a) * Real.negMulLog (b + a) := by
            rw [hmul]
            ring
    have hcomplement : 1 - a / (b + a) = b / (b + a) := by
      rw [eq_div_iff hq.ne', sub_mul, one_mul, div_mul_cancel₀ a hq.ne']
      ring
    have hunit : a / (b + a) + b / (b + a) = 1 := by
      rw [← add_div, add_comm, div_self hq.ne']
    rw [hcomplement, hsplit a, hsplit b]
    linear_combination (-Real.negMulLog (b + a)) * hunit

/-- **The repaired log loss is the conditional entropy.**  The expected negative logarithm of the
repaired forecast of the realized outcome is `Σ_s [η(a_s) + η(b_s) - η(q_s)]`. -/
theorem expectation_neg_log_repairedGroupForecast (law : FiniteReportLaw (Score × Bool)) :
    law.expectation (fun cell ↦ -Real.log (repairedGroupForecast law cell))
      = conditionalEntropy law := by
  rw [FiniteReportLaw.expectation, Fintype.sum_prod_type, conditionalEntropy]
  refine Finset.sum_congr rfl fun group _ ↦ ?_
  rw [Fintype.sum_bool]
  exact repairedGroupLoss_eq _ _ (law.mass_nonneg (group, true)) (law.mass_nonneg (group, false))

/-- The conditional entropy is nonnegative. -/
theorem conditionalEntropy_nonneg (law : FiniteReportLaw (Score × Bool)) :
    0 ≤ conditionalEntropy law := by
  rw [← expectation_neg_log_repairedGroupForecast, FiniteReportLaw.expectation]
  exact Finset.sum_nonneg fun cell _ ↦ mul_nonneg (law.mass_nonneg cell)
    (neg_nonneg.mpr (Real.log_nonpos (repairedGroupForecast_mem law cell).1
      (repairedGroupForecast_mem law cell).2))

/-- **The extended log loss is finite when every realized cell is forecast.**  If every outcome of
positive mass gets a positive forecast and every forecast is at most one, the extended-valued
expected log loss is the real expectation of `-log` of the forecast.  Outcomes of mass zero are
reforecast to one, which changes neither side, and the corpus finite branch
`LogLossSeriesCertificate.expectedLogLoss_eq_ofReal` applies. -/
theorem expectedLogLoss_eq_ofReal_of_pos {Outcome : Type*} [Fintype Outcome]
    (law : FiniteReportLaw Outcome) (forecast : Outcome → ℝ)
    (hpos : ∀ outcome, 0 < law.mass outcome → 0 < forecast outcome)
    (hle : ∀ outcome, forecast outcome ≤ 1) :
    LogLossSeriesCertificate.expectedLogLoss law forecast
      = ENNReal.ofReal (law.expectation fun outcome ↦ -Real.log (forecast outcome)) := by
  set supported : Outcome → ℝ :=
    fun outcome ↦ if 0 < law.mass outcome then forecast outcome else 1 with hsupported
  have hzero : ∀ outcome, ¬ 0 < law.mass outcome → law.mass outcome = 0 := fun outcome hnot ↦
    le_antisymm (not_lt.mp hnot) (law.mass_nonneg outcome)
  have hloss : LogLossSeriesCertificate.expectedLogLoss law forecast
      = LogLossSeriesCertificate.expectedLogLoss law supported := by
    unfold LogLossSeriesCertificate.expectedLogLoss
    refine Finset.sum_congr rfl fun outcome _ ↦ ?_
    by_cases hmass : 0 < law.mass outcome
    · simp only [hsupported, if_pos hmass]
    · simp only [hzero outcome hmass, ENNReal.ofReal_zero, zero_mul]
  have hreal : law.expectation (fun outcome ↦ -Real.log (forecast outcome))
      = law.expectation (fun outcome ↦ -Real.log (supported outcome)) := by
    unfold FiniteReportLaw.expectation
    refine Finset.sum_congr rfl fun outcome _ ↦ ?_
    by_cases hmass : 0 < law.mass outcome
    · simp only [hsupported, if_pos hmass]
    · simp only [hzero outcome hmass, zero_mul]
  rw [hloss, hreal]
  refine LogLossSeriesCertificate.expectedLogLoss_eq_ofReal law supported (fun outcome ↦ ?_)
    (fun outcome ↦ ?_)
  · by_cases hmass : 0 < law.mass outcome
    · simp only [hsupported, if_pos hmass]
      exact hpos outcome hmass
    · simp only [hsupported, if_neg hmass]
      exact one_pos
  · by_cases hmass : 0 < law.mass outcome
    · simp only [hsupported, if_pos hmass]
      exact hle outcome
    · simp only [hsupported, if_neg hmass]
      exact le_refl 1

/-- **The extended repaired log loss is the conditional entropy**: the corpus extended log loss
`LogLossSeriesCertificate.expectedLogLoss` read at the repaired forecast is finite and equals
`H(Y | S)`. -/
theorem expectedLogLoss_repairedGroupForecast (law : FiniteReportLaw (Score × Bool)) :
    LogLossSeriesCertificate.expectedLogLoss law (repairedGroupForecast law)
      = ENNReal.ofReal (conditionalEntropy law) := by
  rw [← expectation_neg_log_repairedGroupForecast]
  refine expectedLogLoss_eq_ofReal_of_pos law _ (fun cell hmass ↦ ?_)
    (fun cell ↦ (repairedGroupForecast_mem law cell).2)
  rcases cell with ⟨group, _ | _⟩
  · show 0 < 1 - law.mass (group, true) / scoreGroupMass law group
    have hgroup : 0 < scoreGroupMass law group :=
      lt_of_lt_of_le hmass (le_add_of_nonneg_right (law.mass_nonneg (group, true)))
    rw [sub_pos, div_lt_one hgroup]
    simp only [scoreGroupMass]
    linarith
  · show 0 < law.mass (group, true) / scoreGroupMass law group
    exact div_pos hmass (lt_of_lt_of_le hmass (caseMass_le_scoreGroupMass law group))

/-- For a binary score the repaired forecast is the corpus
`UniformPenetranceArchitecture.repairedForecast`. -/
theorem repairedGroupForecast_eq_repairedForecast (law : FiniteReportLaw (Bool × Bool)) :
    repairedGroupForecast law = UniformPenetranceArchitecture.repairedForecast law := by
  funext cell
  rcases cell with ⟨group, _ | _⟩ <;> rfl

/-- **For a binary score the conditional entropy is the corpus repaired log loss**
`UniformPenetranceArchitecture.repairedLogLoss`, `Σ_s q_s h(a_s / q_s)` with `h` the binary
entropy.  Both are the extended log loss of the repaired forecast. -/
theorem conditionalEntropy_eq_repairedLogLoss (law : FiniteReportLaw (Bool × Bool)) :
    conditionalEntropy law = UniformPenetranceArchitecture.repairedLogLoss law := by
  have hextended := expectedLogLoss_repairedGroupForecast law
  rw [repairedGroupForecast_eq_repairedForecast,
    UniformPenetranceArchitecture.expectedLogLoss_repairedForecast] at hextended
  refine ((ENNReal.ofReal_eq_ofReal_iff ?_ (conditionalEntropy_nonneg law)).mp hextended).symm
  unfold UniformPenetranceArchitecture.repairedLogLoss
  exact Finset.sum_nonneg fun group _ ↦ mul_nonneg (scoreGroupMass_nonneg law group)
    (Real.binEntropy_nonneg (div_nonneg (law.mass_nonneg _) (scoreGroupMass_nonneg law group))
      (div_le_one_of_le₀ (caseMass_le_scoreGroupMass law group) (scoreGroupMass_nonneg law group)))

/-! ## Fixed forecasts and the Gibbs inequality -/

/-- The forecast of the realized outcome by fixed group forecasts `v_s`: `v_s` for a case and
`1 - v_s` for a control. -/
def groupForecast (value : Score → ℝ) : Score × Bool → ℝ
  | (group, true) => value group
  | (group, false) => 1 - value group

/-- **Log loss of fixed group forecasts**, `Σ_s [a_s (-log v_s) + b_s (-log (1 - v_s))]`, a linear
functional of the report law. -/
def forecastLogLoss (law : FiniteReportLaw (Score × Bool)) (value : Score → ℝ) : ℝ :=
  law.expectation fun cell ↦ -Real.log (groupForecast value cell)

/-- **Fixed forecasts strictly inside the unit interval have finite log loss**: the corpus
extended log loss read at the group forecasts is `forecastLogLoss`. -/
theorem expectedLogLoss_groupForecast (law : FiniteReportLaw (Score × Bool)) (value : Score → ℝ)
    (hpos : ∀ group, 0 < value group) (hlt : ∀ group, value group < 1) :
    LogLossSeriesCertificate.expectedLogLoss law (groupForecast value)
      = ENNReal.ofReal (forecastLogLoss law value) := by
  refine LogLossSeriesCertificate.expectedLogLoss_eq_ofReal law _ (fun cell ↦ ?_)
    (fun cell ↦ ?_)
  · rcases cell with ⟨group, _ | _⟩
    · show 0 < 1 - value group
      linarith [hlt group]
    · exact hpos group
  · rcases cell with ⟨group, _ | _⟩
    · show 1 - value group ≤ 1
      linarith [hpos group]
    · exact (hlt group).le

/-- **A certain forecast against a realized outcome gives infinite log loss.**  A group forecast
`v_s = 0` on a group of positive case mass, or `v_s = 1` on a group of positive control mass, rules
out a realized cell, and the corpus infinite branch
`LogLossSeriesCertificate.expectedLogLoss_eq_top` applies.  Positive group mass alone is not
enough: `v_s = 0` on a group of controls only is finite. -/
theorem expectedLogLoss_groupForecast_eq_top (law : FiniteReportLaw (Score × Bool))
    (value : Score → ℝ) (group : Score)
    (hcertain : (value group = 0 ∧ 0 < law.mass (group, true))
      ∨ (value group = 1 ∧ 0 < law.mass (group, false))) :
    LogLossSeriesCertificate.expectedLogLoss law (groupForecast value) = ⊤ := by
  rcases hcertain with ⟨hvalue, hmass⟩ | ⟨hvalue, hmass⟩
  · refine LogLossSeriesCertificate.expectedLogLoss_eq_top law _ (group, true) hmass ?_
    show ¬ 0 < value group
    rw [hvalue]
    exact lt_irrefl 0
  · refine LogLossSeriesCertificate.expectedLogLoss_eq_top law _ (group, false) hmass ?_
    show ¬ 0 < 1 - value group
    rw [hvalue, sub_self]
    exact lt_irrefl 0

/-- **Gibbs inequality for one cell.**  For a mass `x ≥ 0`, a group mass `q > 0` and a forecast
`w > 0`, `x (-log (x / q)) + x - q w ≤ x (-log w)`, from `log t ≤ t - 1` at `t = q w / x`. -/
theorem cellLoss_ge (x q w : ℝ) (hx : 0 ≤ x) (hq : 0 < q) (hw : 0 < w) :
    x * -Real.log (x / q) + x - q * w ≤ x * -Real.log w := by
  rcases hx.eq_or_lt with hzero | hpos
  · subst hzero
    simp only [zero_mul, zero_add, zero_sub, neg_nonpos]
    exact (mul_pos hq hw).le
  · have hkey := mul_le_mul_of_nonneg_left
      (Real.log_le_sub_one_of_pos (div_pos (mul_pos hq hw) hpos)) hpos.le
    have hright : x * (q * w / x - 1) = q * w - x := by
      rw [mul_sub, mul_one, mul_div_cancel₀ _ hpos.ne']
    have hlog : Real.log (q * w / x) = Real.log q + Real.log w - Real.log x := by
      rw [Real.log_div (mul_pos hq hw).ne' hpos.ne', Real.log_mul hq.ne' hw.ne']
    rw [hright, hlog] at hkey
    rw [Real.log_div hpos.ne' hq.ne']
    linarith

/-- **Gibbs inequality.**  The log loss of fixed group forecasts strictly inside the unit interval
is at least the conditional entropy, the log loss of the repaired forecast. -/
theorem conditionalEntropy_le_forecastLogLoss (law : FiniteReportLaw (Score × Bool))
    (value : Score → ℝ) (hpos : ∀ group, 0 < value group) (hlt : ∀ group, value group < 1) :
    conditionalEntropy law ≤ forecastLogLoss law value := by
  rw [← expectation_neg_log_repairedGroupForecast, forecastLogLoss]
  simp only [FiniteReportLaw.expectation, Fintype.sum_prod_type]
  refine Finset.sum_le_sum fun group _ ↦ ?_
  rw [Fintype.sum_bool, Fintype.sum_bool]
  show law.mass (group, true) * -Real.log (law.mass (group, true) / scoreGroupMass law group)
      + law.mass (group, false)
        * -Real.log (1 - law.mass (group, true) / scoreGroupMass law group)
    ≤ law.mass (group, true) * -Real.log (value group)
      + law.mass (group, false) * -Real.log (1 - value group)
  have hq : scoreGroupMass law group = law.mass (group, false) + law.mass (group, true) := rfl
  have hcaseMass := law.mass_nonneg (group, true)
  have hcontrolMass := law.mass_nonneg (group, false)
  rcases (scoreGroupMass_nonneg law group).eq_or_lt with hzero | hgroup
  · have hcase : law.mass (group, true) = 0 := by linarith
    have hcontrol : law.mass (group, false) = 0 := by linarith
    rw [hcase, hcontrol]
    simp
  · have hcomplement : 1 - law.mass (group, true) / scoreGroupMass law group
        = law.mass (group, false) / scoreGroupMass law group := by
      rw [eq_div_iff hgroup.ne', sub_mul, one_mul, div_mul_cancel₀ _ hgroup.ne', hq]
      ring
    rw [hcomplement]
    have hcase := cellLoss_ge (law.mass (group, true)) (scoreGroupMass law group) (value group)
      hcaseMass hgroup (hpos group)
    have hcontrol := cellLoss_ge (law.mass (group, false)) (scoreGroupMass law group)
      (1 - value group) hcontrolMass hgroup (by linarith [hlt group])
    linarith

end ScoreOutcome

/-! ## Entropy terms as population polynomials -/

section PopulationPolynomials

variable {State : Type*} [Fintype State] {Report : Type*} [Fintype Report] [DecidableEq Report]

/-- The order-`k` entropy term polynomial `Σ_r c_r (1 - c_r)ᵏ⁺¹` of a report map, with `c_r` the
linear cell polynomial of report `r`. -/
def entropyTermPolynomial (report : State → Report) (order : ℕ) : MvPolynomial State ℝ :=
  ∑ selected, cellPolynomial report selected * (1 - cellPolynomial report selected) ^ (order + 1)

/-- The entropy term polynomial evaluates to the entropy term of the pushforward law. -/
theorem eval_entropyTermPolynomial (law : FiniteReportLaw State) (report : State → Report)
    (order : ℕ) :
    eval law.mass (entropyTermPolynomial report order)
      = reportEntropyTerm (law.pushforward report) order := by
  simp only [entropyTermPolynomial, reportEntropyTerm, map_sum, map_mul, map_pow, map_sub,
    map_one, eval_cellPolynomial]

/-- The order-`k` entropy term polynomial has total degree at most `k + 2`: a linear cell
polynomial against `k + 1` powers of its complement. -/
theorem totalDegree_entropyTermPolynomial_le (report : State → Report) (order : ℕ) :
    (entropyTermPolynomial report order).totalDegree ≤ order + 2 := by
  refine (totalDegree_finset_sum _ _).trans (Finset.sup_le fun selected _ ↦ ?_)
  exact (totalDegree_expansionTerm_le _ _ 1 1 (order + 1) (totalDegree_cellPolynomial_le _ _)
    (totalDegree_cellPolynomial_le _ _)).trans (by omega)

end PopulationPolynomials

variable {Deme Locus : Type*} {Allele : Locus → Type*}
variable [Fintype Deme] [DecidableEq Deme] [Fintype Locus] [DecidableEq Locus]
  [∀ ℓ, Fintype (Allele ℓ)] [∀ ℓ, DecidableEq (Allele ℓ)]

/-! ## The entropy of a report law through a kernel -/

section KernelEntropy

variable {Report : Type*} [Fintype Report] [DecidableEq Report]

/-- **Expected entropy** of the report law of a deme, averaged under a kernel started at `x₀`. -/
def expectedEntropy
    (κ : Kernel (FrequencyState Deme Locus Allele) (FrequencyState Deme Locus Allele))
    (x0 : FrequencyState Deme Locus Allele) (deme : Deme)
    (report : FullHaplotype Locus Allele → Report) : ℝ :=
  ∫ y, reportEntropy ((stateLaw y deme).pushforward report) ∂(κ x0)

/-- The entropy of the report law of a deme is a continuous observable of the frequency state. -/
theorem continuous_reportEntropy (deme : Deme) (report : FullHaplotype Locus Allele → Report) :
    Continuous fun y : FrequencyState Deme Locus Allele ↦
      reportEntropy ((stateLaw y deme).pushforward report) := by
  unfold reportEntropy
  exact continuous_finset_sum _ fun selected _ ↦
    Real.continuous_negMulLog.comp (continuous_pushforwardMass deme report selected)

/-- An entropy term of the report law of a deme is a continuous observable of the frequency
state. -/
theorem continuous_reportEntropyTerm (deme : Deme) (report : FullHaplotype Locus Allele → Report)
    (order : ℕ) :
    Continuous fun y : FrequencyState Deme Locus Allele ↦
      reportEntropyTerm ((stateLaw y deme).pushforward report) order := by
  simpa only [eval_entropyTermPolynomial] using
    continuous_eval_stateLaw deme (entropyTermPolynomial report order)

/-- **The entropy truncation certificate under a kernel.**  Truncating the series after `terms`
terms gives the expected entropy of a deme's report law from below, within
`|Report| / (terms + 1)`. -/
theorem expectedEntropy_sub_truncation_mem
    (κ : Kernel (FrequencyState Deme Locus Allele) (FrequencyState Deme Locus Allele))
    [IsMarkovKernel κ] (x0 : FrequencyState Deme Locus Allele) (deme : Deme)
    (report : FullHaplotype Locus Allele → Report) (terms : ℕ) :
    0 ≤ expectedEntropy κ x0 deme report - ∑ order ∈ Finset.range terms,
        (∫ y, reportEntropyTerm ((stateLaw y deme).pushforward report) order ∂(κ x0))
          / ((order : ℝ) + 1)
    ∧ expectedEntropy κ x0 deme report - ∑ order ∈ Finset.range terms,
        (∫ y, reportEntropyTerm ((stateLaw y deme).pushforward report) order ∂(κ x0))
          / ((order : ℝ) + 1)
      ≤ (Fintype.card Report : ℝ) / ((terms : ℝ) + 1) := by
  have hentropy := integrable_continuousObservable κ x0 (continuous_reportEntropy deme report)
  have hterm : ∀ order : ℕ, Integrable (fun y ↦
      reportEntropyTerm ((stateLaw y deme).pushforward report) order / ((order : ℝ) + 1))
      (κ x0) := fun order ↦
    integrable_continuousObservable κ x0
      ((continuous_reportEntropyTerm deme report order).div_const _)
  have hgap : Integrable (fun y ↦ reportEntropy ((stateLaw y deme).pushforward report)
      - ∑ order ∈ Finset.range terms,
        reportEntropyTerm ((stateLaw y deme).pushforward report) order / ((order : ℝ) + 1))
      (κ x0) :=
    hentropy.sub (integrable_finset_sum _ fun order _ ↦ hterm order)
  have hinside : expectedEntropy κ x0 deme report - ∑ order ∈ Finset.range terms,
        (∫ y, reportEntropyTerm ((stateLaw y deme).pushforward report) order ∂(κ x0))
          / ((order : ℝ) + 1)
      = ∫ y, (reportEntropy ((stateLaw y deme).pushforward report)
        - ∑ order ∈ Finset.range terms,
          reportEntropyTerm ((stateLaw y deme).pushforward report) order / ((order : ℝ) + 1))
        ∂(κ x0) := by
    rw [expectedEntropy, integral_sub hentropy (integrable_finset_sum _ fun order _ ↦ hterm order),
      integral_finset_sum _ fun order _ ↦ hterm order]
    simp only [integral_div]
  rw [hinside]
  refine ⟨integral_nonneg fun y ↦
    (reportEntropy_sub_truncation_mem ((stateLaw y deme).pushforward report) terms).1, ?_⟩
  calc ∫ y, (reportEntropy ((stateLaw y deme).pushforward report)
        - ∑ order ∈ Finset.range terms,
          reportEntropyTerm ((stateLaw y deme).pushforward report) order / ((order : ℝ) + 1))
        ∂(κ x0)
      ≤ ∫ _y, (Fintype.card Report : ℝ) / ((terms : ℝ) + 1) ∂(κ x0) :=
        integral_mono hgap (integrable_const _) fun y ↦
          (reportEntropy_sub_truncation_mem ((stateLaw y deme).pushforward report) terms).2
    _ = (Fintype.card Report : ℝ) / ((terms : ℝ) + 1) := by
        rw [integral_const, measureReal_univ_eq_one, one_smul]

/-- **The expected entropy as a series.**  Under every Markov kernel the expected entropy of the
report law of a deme is the series of the expected entropy terms divided by `k + 1`.  The terms
are nonnegative and the truncation certificate squeezes the partial sums, so no interchange of
integral and series is needed beyond finite sums. -/
theorem hasSum_expectedEntropy
    (κ : Kernel (FrequencyState Deme Locus Allele) (FrequencyState Deme Locus Allele))
    [IsMarkovKernel κ] (x0 : FrequencyState Deme Locus Allele) (deme : Deme)
    (report : FullHaplotype Locus Allele → Report) :
    HasSum (fun order : ℕ ↦
        (∫ y, reportEntropyTerm ((stateLaw y deme).pushforward report) order ∂(κ x0))
          / ((order : ℝ) + 1))
      (expectedEntropy κ x0 deme report) := by
  have hnonneg : ∀ order : ℕ, 0 ≤
      (∫ y, reportEntropyTerm ((stateLaw y deme).pushforward report) order ∂(κ x0))
        / ((order : ℝ) + 1) := fun order ↦
    div_nonneg (integral_nonneg fun y ↦ reportEntropyTerm_nonneg _ order) (by positivity)
  rw [hasSum_iff_tendsto_nat_of_nonneg hnonneg]
  have hconst : Tendsto (fun _ : ℕ ↦ expectedEntropy κ x0 deme report) atTop
      (𝓝 (expectedEntropy κ x0 deme report)) := tendsto_const_nhds
  have hscaled : Tendsto (fun terms : ℕ ↦ (Fintype.card Report : ℝ) * (1 / ((terms : ℝ) + 1)))
      atTop (𝓝 ((Fintype.card Report : ℝ) * 0)) :=
    tendsto_one_div_add_atTop_nhds_zero_nat.const_mul _
  have hlower := hconst.sub hscaled
  simp only [mul_one_div, mul_zero, sub_zero] at hlower
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le hlower hconst (fun terms ↦ ?_) (fun terms ↦ ?_)
  · have hupper := (expectedEntropy_sub_truncation_mem κ x0 deme report terms).2
    have hgoal : expectedEntropy κ x0 deme report - (Fintype.card Report : ℝ) / ((terms : ℝ) + 1)
        ≤ ∑ order ∈ Finset.range terms,
          (∫ y, reportEntropyTerm ((stateLaw y deme).pushforward report) order ∂(κ x0))
            / ((order : ℝ) + 1) := by
      linarith
    exact hgoal
  · have hbelow := (expectedEntropy_sub_truncation_mem κ x0 deme report terms).1
    have hgoal : ∑ order ∈ Finset.range terms,
          (∫ y, reportEntropyTerm ((stateLaw y deme).pushforward report) order ∂(κ x0))
            / ((order : ℝ) + 1)
        ≤ expectedEntropy κ x0 deme report := by
      linarith
    exact hgoal

/-- **The expected entropy through the propagated moments.**  The expected entropy of the report
law of a deme is the series over `k` of the coefficient vectors of the order-`k` entropy term
polynomial dotted with the budget-`(k + 2)` propagated moments, divided by `k + 1`.

Assumes: `∀ n, HasDualMoments κ n (M n)`. -/
theorem expectedEntropy_eq_tsum_dotProduct (ℓ₀ : Locus)
    (κ : Kernel (FrequencyState Deme Locus Allele) (FrequencyState Deme Locus Allele))
    [IsMarkovKernel κ] (M : ∀ n : ℕ, BudgetMatrix Deme Locus Allele n)
    (hmoment : ∀ n : ℕ, HasDualMoments κ n (M n)) (x0 : FrequencyState Deme Locus Allele)
    (deme : Deme) (report : FullHaplotype Locus Allele → Report) :
    expectedEntropy κ x0 deme report
      = ∑' order : ℕ, (budgetCoefficients ℓ₀ (fun _ ↦ order + 2)
          (demePolynomial deme (entropyTermPolynomial report order))
        ⬝ᵥ (M (order + 2) *ᵥ budgetMomentFeature (fun _ ↦ order + 2) x0)) / ((order : ℝ) + 1) := by
  rw [← (hasSum_expectedEntropy κ x0 deme report).tsum_eq]
  refine tsum_congr fun order ↦ ?_
  rw [← integral_eval_stateLaw_eq_dotProduct ℓ₀ (order + 2) κ (M (order + 2))
    (hmoment (order + 2)) deme _ (totalDegree_entropyTermPolynomial_le report order) x0]
  simp only [eval_entropyTermPolynomial]

/-- **The expected entropy along a history of epochs, splits and pulses.** -/
theorem expectedEntropy_historyEventKernel (ℓ₀ : Locus) (hap₀ : FullHaplotype Locus Allele)
    (events : List ((NeutralRates Deme Locus Allele × ℝ≥0) ⊕ PulseMatrix Deme))
    (x0 : FrequencyState Deme Locus Allele) (deme : Deme)
    (report : FullHaplotype Locus Allele → Report) :
    expectedEntropy (historyEventKernel ℓ₀ hap₀ events) x0 deme report
      = ∑' order : ℕ, (budgetCoefficients ℓ₀ (fun _ ↦ order + 2)
          (demePolynomial deme (entropyTermPolynomial report order))
        ⬝ᵥ (historyEventPropagator (fun _ ↦ order + 2) events
          *ᵥ budgetMomentFeature (fun _ ↦ order + 2) x0)) / ((order : ℝ) + 1) := by
  haveI := isMarkovKernel_historyEventKernel ℓ₀ hap₀ events
  exact expectedEntropy_eq_tsum_dotProduct ℓ₀ (historyEventKernel ℓ₀ hap₀ events)
    (fun n ↦ historyEventPropagator (fun _ ↦ n) events)
    (hasDualMoments_historyEventKernel ℓ₀ hap₀ events) x0 deme report

/-- **The expected entropy along a time-varying rate history.** -/
theorem expectedEntropy_rateHistoryKernel {rates : ℝ → NeutralRates Deme Locus Allele} {T : ℝ}
    (hT : 0 ≤ T) (hcontinuous : ∀ capacity : Locus → ℕ,
      ContinuousOn (fun t ↦ dualGenerator (rates t) capacity) (Set.Icc 0 T))
    (ℓ₀ : Locus) (hap₀ : FullHaplotype Locus Allele) (x0 : FrequencyState Deme Locus Allele)
    (deme : Deme) (report : FullHaplotype Locus Allele → Report) :
    expectedEntropy (rateHistoryKernel rates ℓ₀ hap₀ hT hcontinuous) x0 deme report
      = ∑' order : ℕ, (budgetCoefficients ℓ₀ (fun _ ↦ order + 2)
          (demePolynomial deme (entropyTermPolynomial report order))
        ⬝ᵥ (rateHistoryDualPropagator rates (fun _ ↦ order + 2) T
          *ᵥ budgetMomentFeature (fun _ ↦ order + 2) x0)) / ((order : ℝ) + 1) := by
  haveI := isMarkovKernel_rateHistoryKernel hT hcontinuous ℓ₀ hap₀
  exact expectedEntropy_eq_tsum_dotProduct ℓ₀ (rateHistoryKernel rates ℓ₀ hap₀ hT hcontinuous)
    (fun n ↦ rateHistoryDualPropagator rates (fun _ ↦ n) T)
    (hasDualMoments_rateHistoryKernel hT hcontinuous ℓ₀ hap₀) x0 deme report

/-- **The expected entropy sees a history only through its propagated moments.**  Two histories,
from two initial states, whose propagated moments agree at every budget `k + 2` have equal
expected entropy for every report map. -/
theorem expectedEntropy_eq_of_moments_eq (ℓ₀ : Locus) (hap₀ : FullHaplotype Locus Allele)
    {first second : List ((NeutralRates Deme Locus Allele × ℝ≥0) ⊕ PulseMatrix Deme)}
    {x₁ x₂ : FrequencyState Deme Locus Allele}
    (hmoments : ∀ order : ℕ,
      historyEventPropagator (fun _ ↦ order + 2) first
          *ᵥ budgetMomentFeature (fun _ ↦ order + 2) x₁
        = historyEventPropagator (fun _ ↦ order + 2) second
          *ᵥ budgetMomentFeature (fun _ ↦ order + 2) x₂)
    (deme : Deme) (report : FullHaplotype Locus Allele → Report) :
    expectedEntropy (historyEventKernel ℓ₀ hap₀ first) x₁ deme report
      = expectedEntropy (historyEventKernel ℓ₀ hap₀ second) x₂ deme report := by
  rw [expectedEntropy_historyEventKernel, expectedEntropy_historyEventKernel]
  exact tsum_congr fun order ↦ by rw [hmoments order]

/-- **Expected population polynomials as dot products, order by order.**  A series of expected
population polynomials of total degree at most `k + 2`, each divided by `k + 1`, is the series of
their coefficient vectors dotted with the budget-`(k + 2)` propagated moments.

Assumes: `∀ n, HasDualMoments κ n (M n)`. -/
theorem tsum_integral_eval_eq_tsum_dotProduct (ℓ₀ : Locus)
    (κ : Kernel (FrequencyState Deme Locus Allele) (FrequencyState Deme Locus Allele))
    [IsMarkovKernel κ] (M : ∀ n : ℕ, BudgetMatrix Deme Locus Allele n)
    (hmoment : ∀ n : ℕ, HasDualMoments κ n (M n)) (x0 : FrequencyState Deme Locus Allele)
    (deme : Deme) (P : ℕ → MvPolynomial (FullHaplotype Locus Allele) ℝ)
    (hP : ∀ order : ℕ, (P order).totalDegree ≤ order + 2) :
    ∑' order : ℕ, (∫ y, eval (stateLaw y deme).mass (P order) ∂(κ x0)) / ((order : ℝ) + 1)
      = ∑' order : ℕ, (budgetCoefficients ℓ₀ (fun _ ↦ order + 2) (demePolynomial deme (P order))
        ⬝ᵥ (M (order + 2) *ᵥ budgetMomentFeature (fun _ ↦ order + 2) x0)) / ((order : ℝ) + 1) :=
  tsum_congr fun order ↦ by
    rw [integral_eval_stateLaw_eq_dotProduct ℓ₀ (order + 2) κ (M (order + 2))
      (hmoment (order + 2)) deme (P order) (hP order) x0]

end KernelEntropy

/-! ## Conditional entropy and mutual information through a kernel -/

section ScorePolynomials

variable {State : Type*} [Fintype State] {Score : Type*} [Fintype Score] [DecidableEq Score]

/-- The order-`k` conditional entropy term polynomial: the joint entropy term polynomial of the
report map minus that of its score map. -/
def conditionalEntropyTermPolynomial (report : State → Score × Bool) (order : ℕ) :
    MvPolynomial State ℝ :=
  entropyTermPolynomial report order - entropyTermPolynomial (fun state ↦ (report state).1) order

/-- The order-`k` mutual information term polynomial: the outcome entropy term polynomial minus the
conditional entropy term polynomial. -/
def mutualInformationTermPolynomial (report : State → Score × Bool) (order : ℕ) :
    MvPolynomial State ℝ :=
  entropyTermPolynomial (fun state ↦ (report state).2) order
    - conditionalEntropyTermPolynomial report order

/-- The conditional entropy term polynomial has total degree at most `k + 2`. -/
theorem totalDegree_conditionalEntropyTermPolynomial_le (report : State → Score × Bool)
    (order : ℕ) : (conditionalEntropyTermPolynomial report order).totalDegree ≤ order + 2 :=
  (totalDegree_sub _ _).trans
    (max_le (totalDegree_entropyTermPolynomial_le _ _) (totalDegree_entropyTermPolynomial_le _ _))

/-- The mutual information term polynomial has total degree at most `k + 2`. -/
theorem totalDegree_mutualInformationTermPolynomial_le (report : State → Score × Bool)
    (order : ℕ) : (mutualInformationTermPolynomial report order).totalDegree ≤ order + 2 :=
  (totalDegree_sub _ _).trans (max_le (totalDegree_entropyTermPolynomial_le _ _)
    (totalDegree_conditionalEntropyTermPolynomial_le _ _))

end ScorePolynomials

section KernelScoreOutcome

variable {Score : Type*} [Fintype Score] [DecidableEq Score]

/-- **Expected conditional entropy** of the report law of a deme, averaged under a kernel started
at `x₀`: the expected repaired log loss. -/
def expectedConditionalEntropy
    (κ : Kernel (FrequencyState Deme Locus Allele) (FrequencyState Deme Locus Allele))
    (x0 : FrequencyState Deme Locus Allele) (deme : Deme)
    (report : FullHaplotype Locus Allele → Score × Bool) : ℝ :=
  ∫ y, conditionalEntropy ((stateLaw y deme).pushforward report) ∂(κ x0)

/-- **Expected mutual information** of score and outcome in the report law of a deme, averaged
under a kernel started at `x₀`. -/
def expectedMutualInformation
    (κ : Kernel (FrequencyState Deme Locus Allele) (FrequencyState Deme Locus Allele))
    (x0 : FrequencyState Deme Locus Allele) (deme : Deme)
    (report : FullHaplotype Locus Allele → Score × Bool) : ℝ :=
  ∫ y, mutualInformation ((stateLaw y deme).pushforward report) ∂(κ x0)

/-- The conditional entropy of the report law of a deme is a continuous observable of the
frequency state. -/
theorem continuous_conditionalEntropy (deme : Deme)
    (report : FullHaplotype Locus Allele → Score × Bool) :
    Continuous fun y : FrequencyState Deme Locus Allele ↦
      conditionalEntropy ((stateLaw y deme).pushforward report) := by
  unfold conditionalEntropy
  exact continuous_finset_sum _ fun group _ ↦
    ((Real.continuous_negMulLog.comp (continuous_pushforwardMass deme report (group, true))).add
      (Real.continuous_negMulLog.comp (continuous_pushforwardMass deme report (group, false)))).sub
      (Real.continuous_negMulLog.comp ((continuous_pushforwardMass deme report (group, false)).add
        (continuous_pushforwardMass deme report (group, true))))

/-- **The expected chain rule.**  The expected conditional entropy is the expected joint entropy
minus the expected entropy of the score. -/
theorem expectedConditionalEntropy_eq_sub
    (κ : Kernel (FrequencyState Deme Locus Allele) (FrequencyState Deme Locus Allele))
    [IsMarkovKernel κ] (x0 : FrequencyState Deme Locus Allele) (deme : Deme)
    (report : FullHaplotype Locus Allele → Score × Bool) :
    expectedConditionalEntropy κ x0 deme report
      = expectedEntropy κ x0 deme report - expectedEntropy κ x0 deme fun hap ↦ (report hap).1 := by
  have hpoint : ∀ y : FrequencyState Deme Locus Allele,
      conditionalEntropy ((stateLaw y deme).pushforward report)
        = reportEntropy ((stateLaw y deme).pushforward report)
          - reportEntropy ((stateLaw y deme).pushforward fun hap ↦ (report hap).1) := fun y ↦ by
    rw [conditionalEntropy_eq_reportEntropy_sub, reportEntropy_pushforward_pushforward]
  simp only [expectedConditionalEntropy, expectedEntropy, hpoint]
  exact integral_sub (integrable_continuousObservable κ x0 (continuous_reportEntropy deme report))
    (integrable_continuousObservable κ x0 (continuous_reportEntropy deme _))

/-- The expected mutual information is the expected outcome entropy minus the expected conditional
entropy. -/
theorem expectedMutualInformation_eq_sub
    (κ : Kernel (FrequencyState Deme Locus Allele) (FrequencyState Deme Locus Allele))
    [IsMarkovKernel κ] (x0 : FrequencyState Deme Locus Allele) (deme : Deme)
    (report : FullHaplotype Locus Allele → Score × Bool) :
    expectedMutualInformation κ x0 deme report
      = expectedEntropy κ x0 deme (fun hap ↦ (report hap).2)
        - expectedConditionalEntropy κ x0 deme report := by
  have hpoint : ∀ y : FrequencyState Deme Locus Allele,
      mutualInformation ((stateLaw y deme).pushforward report)
        = reportEntropy ((stateLaw y deme).pushforward fun hap ↦ (report hap).2)
          - conditionalEntropy ((stateLaw y deme).pushforward report) := fun y ↦ by
    rw [mutualInformation, reportEntropy_pushforward_pushforward]
  simp only [expectedMutualInformation, expectedConditionalEntropy, expectedEntropy, hpoint]
  exact integral_sub (integrable_continuousObservable κ x0 (continuous_reportEntropy deme _))
    (integrable_continuousObservable κ x0 (continuous_conditionalEntropy deme report))

/-- The expected conditional entropy term polynomial of order `k`, divided by `k + 1`, is the
difference of the expected joint and score entropy terms. -/
theorem integral_eval_conditionalEntropyTermPolynomial
    (κ : Kernel (FrequencyState Deme Locus Allele) (FrequencyState Deme Locus Allele))
    [IsMarkovKernel κ] (x0 : FrequencyState Deme Locus Allele) (deme : Deme)
    (report : FullHaplotype Locus Allele → Score × Bool) (order : ℕ) :
    (∫ y, eval (stateLaw y deme).mass (conditionalEntropyTermPolynomial report order) ∂(κ x0))
        / ((order : ℝ) + 1)
      = (∫ y, reportEntropyTerm ((stateLaw y deme).pushforward report) order ∂(κ x0))
          / ((order : ℝ) + 1)
        - (∫ y, reportEntropyTerm ((stateLaw y deme).pushforward fun hap ↦ (report hap).1)
            order ∂(κ x0)) / ((order : ℝ) + 1) := by
  rw [← sub_div]
  congr 1
  simp only [conditionalEntropyTermPolynomial, map_sub, eval_entropyTermPolynomial]
  exact integral_sub
    (integrable_continuousObservable κ x0 (continuous_reportEntropyTerm deme report order))
    (integrable_continuousObservable κ x0 (continuous_reportEntropyTerm deme _ order))

/-- The expected mutual information term polynomial of order `k`, divided by `k + 1`, is the
expected outcome entropy term minus the expected conditional entropy term. -/
theorem integral_eval_mutualInformationTermPolynomial
    (κ : Kernel (FrequencyState Deme Locus Allele) (FrequencyState Deme Locus Allele))
    [IsMarkovKernel κ] (x0 : FrequencyState Deme Locus Allele) (deme : Deme)
    (report : FullHaplotype Locus Allele → Score × Bool) (order : ℕ) :
    (∫ y, eval (stateLaw y deme).mass (mutualInformationTermPolynomial report order) ∂(κ x0))
        / ((order : ℝ) + 1)
      = (∫ y, reportEntropyTerm ((stateLaw y deme).pushforward fun hap ↦ (report hap).2)
            order ∂(κ x0)) / ((order : ℝ) + 1)
        - (∫ y, eval (stateLaw y deme).mass (conditionalEntropyTermPolynomial report order)
            ∂(κ x0)) / ((order : ℝ) + 1) := by
  rw [← sub_div]
  congr 1
  simp only [mutualInformationTermPolynomial, map_sub, eval_entropyTermPolynomial]
  exact integral_sub
    (integrable_continuousObservable κ x0 (continuous_reportEntropyTerm deme _ order))
    (integrable_continuousObservable κ x0 (continuous_eval_stateLaw deme _))

/-- **The expected conditional entropy as a series** of expected budget-`(k + 2)` polynomials
divided by `k + 1`. -/
theorem hasSum_expectedConditionalEntropy
    (κ : Kernel (FrequencyState Deme Locus Allele) (FrequencyState Deme Locus Allele))
    [IsMarkovKernel κ] (x0 : FrequencyState Deme Locus Allele) (deme : Deme)
    (report : FullHaplotype Locus Allele → Score × Bool) :
    HasSum (fun order : ℕ ↦
        (∫ y, eval (stateLaw y deme).mass (conditionalEntropyTermPolynomial report order) ∂(κ x0))
          / ((order : ℝ) + 1))
      (expectedConditionalEntropy κ x0 deme report) := by
  rw [expectedConditionalEntropy_eq_sub]
  simp only [integral_eval_conditionalEntropyTermPolynomial]
  exact (hasSum_expectedEntropy κ x0 deme report).sub (hasSum_expectedEntropy κ x0 deme _)

/-- **The expected mutual information as a series** of expected budget-`(k + 2)` polynomials
divided by `k + 1`. -/
theorem hasSum_expectedMutualInformation
    (κ : Kernel (FrequencyState Deme Locus Allele) (FrequencyState Deme Locus Allele))
    [IsMarkovKernel κ] (x0 : FrequencyState Deme Locus Allele) (deme : Deme)
    (report : FullHaplotype Locus Allele → Score × Bool) :
    HasSum (fun order : ℕ ↦
        (∫ y, eval (stateLaw y deme).mass (mutualInformationTermPolynomial report order) ∂(κ x0))
          / ((order : ℝ) + 1))
      (expectedMutualInformation κ x0 deme report) := by
  rw [expectedMutualInformation_eq_sub]
  simp only [integral_eval_mutualInformationTermPolynomial]
  exact (hasSum_expectedEntropy κ x0 deme _).sub
    (hasSum_expectedConditionalEntropy κ x0 deme report)

/-- **The expected conditional entropy through the propagated moments.**

Assumes: `∀ n, HasDualMoments κ n (M n)`. -/
theorem expectedConditionalEntropy_eq_tsum_dotProduct (ℓ₀ : Locus)
    (κ : Kernel (FrequencyState Deme Locus Allele) (FrequencyState Deme Locus Allele))
    [IsMarkovKernel κ] (M : ∀ n : ℕ, BudgetMatrix Deme Locus Allele n)
    (hmoment : ∀ n : ℕ, HasDualMoments κ n (M n)) (x0 : FrequencyState Deme Locus Allele)
    (deme : Deme) (report : FullHaplotype Locus Allele → Score × Bool) :
    expectedConditionalEntropy κ x0 deme report
      = ∑' order : ℕ, (budgetCoefficients ℓ₀ (fun _ ↦ order + 2)
          (demePolynomial deme (conditionalEntropyTermPolynomial report order))
        ⬝ᵥ (M (order + 2) *ᵥ budgetMomentFeature (fun _ ↦ order + 2) x0)) / ((order : ℝ) + 1) := by
  rw [← (hasSum_expectedConditionalEntropy κ x0 deme report).tsum_eq]
  exact tsum_integral_eval_eq_tsum_dotProduct ℓ₀ κ M hmoment x0 deme _
    (totalDegree_conditionalEntropyTermPolynomial_le report)

/-- **The expected mutual information through the propagated moments.**

Assumes: `∀ n, HasDualMoments κ n (M n)`. -/
theorem expectedMutualInformation_eq_tsum_dotProduct (ℓ₀ : Locus)
    (κ : Kernel (FrequencyState Deme Locus Allele) (FrequencyState Deme Locus Allele))
    [IsMarkovKernel κ] (M : ∀ n : ℕ, BudgetMatrix Deme Locus Allele n)
    (hmoment : ∀ n : ℕ, HasDualMoments κ n (M n)) (x0 : FrequencyState Deme Locus Allele)
    (deme : Deme) (report : FullHaplotype Locus Allele → Score × Bool) :
    expectedMutualInformation κ x0 deme report
      = ∑' order : ℕ, (budgetCoefficients ℓ₀ (fun _ ↦ order + 2)
          (demePolynomial deme (mutualInformationTermPolynomial report order))
        ⬝ᵥ (M (order + 2) *ᵥ budgetMomentFeature (fun _ ↦ order + 2) x0)) / ((order : ℝ) + 1) := by
  rw [← (hasSum_expectedMutualInformation κ x0 deme report).tsum_eq]
  exact tsum_integral_eval_eq_tsum_dotProduct ℓ₀ κ M hmoment x0 deme _
    (totalDegree_mutualInformationTermPolynomial_le report)

/-- **Conditional entropy and mutual information along a history of epochs, splits and
pulses.** -/
theorem expectedConditionalEntropy_and_mutualInformation_historyEventKernel (ℓ₀ : Locus)
    (hap₀ : FullHaplotype Locus Allele)
    (events : List ((NeutralRates Deme Locus Allele × ℝ≥0) ⊕ PulseMatrix Deme))
    (x0 : FrequencyState Deme Locus Allele) (deme : Deme)
    (report : FullHaplotype Locus Allele → Score × Bool) :
    expectedConditionalEntropy (historyEventKernel ℓ₀ hap₀ events) x0 deme report
      = ∑' order : ℕ, (budgetCoefficients ℓ₀ (fun _ ↦ order + 2)
          (demePolynomial deme (conditionalEntropyTermPolynomial report order))
        ⬝ᵥ (historyEventPropagator (fun _ ↦ order + 2) events
          *ᵥ budgetMomentFeature (fun _ ↦ order + 2) x0)) / ((order : ℝ) + 1)
    ∧ expectedMutualInformation (historyEventKernel ℓ₀ hap₀ events) x0 deme report
      = ∑' order : ℕ, (budgetCoefficients ℓ₀ (fun _ ↦ order + 2)
          (demePolynomial deme (mutualInformationTermPolynomial report order))
        ⬝ᵥ (historyEventPropagator (fun _ ↦ order + 2) events
          *ᵥ budgetMomentFeature (fun _ ↦ order + 2) x0)) / ((order : ℝ) + 1) := by
  haveI := isMarkovKernel_historyEventKernel ℓ₀ hap₀ events
  exact ⟨expectedConditionalEntropy_eq_tsum_dotProduct ℓ₀ (historyEventKernel ℓ₀ hap₀ events)
      (fun n ↦ historyEventPropagator (fun _ ↦ n) events)
      (hasDualMoments_historyEventKernel ℓ₀ hap₀ events) x0 deme report,
    expectedMutualInformation_eq_tsum_dotProduct ℓ₀ (historyEventKernel ℓ₀ hap₀ events)
      (fun n ↦ historyEventPropagator (fun _ ↦ n) events)
      (hasDualMoments_historyEventKernel ℓ₀ hap₀ events) x0 deme report⟩

/-- **Conditional entropy and mutual information along a time-varying rate history.** -/
theorem expectedConditionalEntropy_and_mutualInformation_rateHistoryKernel
    {rates : ℝ → NeutralRates Deme Locus Allele} {T : ℝ} (hT : 0 ≤ T)
    (hcontinuous : ∀ capacity : Locus → ℕ,
      ContinuousOn (fun t ↦ dualGenerator (rates t) capacity) (Set.Icc 0 T))
    (ℓ₀ : Locus) (hap₀ : FullHaplotype Locus Allele) (x0 : FrequencyState Deme Locus Allele)
    (deme : Deme) (report : FullHaplotype Locus Allele → Score × Bool) :
    expectedConditionalEntropy (rateHistoryKernel rates ℓ₀ hap₀ hT hcontinuous) x0 deme report
      = ∑' order : ℕ, (budgetCoefficients ℓ₀ (fun _ ↦ order + 2)
          (demePolynomial deme (conditionalEntropyTermPolynomial report order))
        ⬝ᵥ (rateHistoryDualPropagator rates (fun _ ↦ order + 2) T
          *ᵥ budgetMomentFeature (fun _ ↦ order + 2) x0)) / ((order : ℝ) + 1)
    ∧ expectedMutualInformation (rateHistoryKernel rates ℓ₀ hap₀ hT hcontinuous) x0 deme report
      = ∑' order : ℕ, (budgetCoefficients ℓ₀ (fun _ ↦ order + 2)
          (demePolynomial deme (mutualInformationTermPolynomial report order))
        ⬝ᵥ (rateHistoryDualPropagator rates (fun _ ↦ order + 2) T
          *ᵥ budgetMomentFeature (fun _ ↦ order + 2) x0)) / ((order : ℝ) + 1) := by
  haveI := isMarkovKernel_rateHistoryKernel hT hcontinuous ℓ₀ hap₀
  exact ⟨expectedConditionalEntropy_eq_tsum_dotProduct ℓ₀
      (rateHistoryKernel rates ℓ₀ hap₀ hT hcontinuous)
      (fun n ↦ rateHistoryDualPropagator rates (fun _ ↦ n) T)
      (hasDualMoments_rateHistoryKernel hT hcontinuous ℓ₀ hap₀) x0 deme report,
    expectedMutualInformation_eq_tsum_dotProduct ℓ₀
      (rateHistoryKernel rates ℓ₀ hap₀ hT hcontinuous)
      (fun n ↦ rateHistoryDualPropagator rates (fun _ ↦ n) T)
      (hasDualMoments_rateHistoryKernel hT hcontinuous ℓ₀ hap₀) x0 deme report⟩

/-- **Conditional entropy and mutual information see a history only through its propagated
moments.**  Two histories, from two initial states, whose propagated moments agree at every
budget `k + 2` have equal expected conditional entropy and equal expected mutual information. -/
theorem expectedConditionalEntropy_and_mutualInformation_eq_of_moments_eq (ℓ₀ : Locus)
    (hap₀ : FullHaplotype Locus Allele)
    {first second : List ((NeutralRates Deme Locus Allele × ℝ≥0) ⊕ PulseMatrix Deme)}
    {x₁ x₂ : FrequencyState Deme Locus Allele}
    (hmoments : ∀ order : ℕ,
      historyEventPropagator (fun _ ↦ order + 2) first
          *ᵥ budgetMomentFeature (fun _ ↦ order + 2) x₁
        = historyEventPropagator (fun _ ↦ order + 2) second
          *ᵥ budgetMomentFeature (fun _ ↦ order + 2) x₂)
    (deme : Deme) (report : FullHaplotype Locus Allele → Score × Bool) :
    expectedConditionalEntropy (historyEventKernel ℓ₀ hap₀ first) x₁ deme report
      = expectedConditionalEntropy (historyEventKernel ℓ₀ hap₀ second) x₂ deme report
    ∧ expectedMutualInformation (historyEventKernel ℓ₀ hap₀ first) x₁ deme report
      = expectedMutualInformation (historyEventKernel ℓ₀ hap₀ second) x₂ deme report := by
  haveI := isMarkovKernel_historyEventKernel ℓ₀ hap₀ first
  haveI := isMarkovKernel_historyEventKernel ℓ₀ hap₀ second
  have hconditional : expectedConditionalEntropy (historyEventKernel ℓ₀ hap₀ first) x₁ deme report
      = expectedConditionalEntropy (historyEventKernel ℓ₀ hap₀ second) x₂ deme report := by
    rw [expectedConditionalEntropy_eq_sub, expectedConditionalEntropy_eq_sub,
      expectedEntropy_eq_of_moments_eq ℓ₀ hap₀ hmoments deme report,
      expectedEntropy_eq_of_moments_eq ℓ₀ hap₀ hmoments deme fun hap ↦ (report hap).1]
  refine ⟨hconditional, ?_⟩
  rw [expectedMutualInformation_eq_sub, expectedMutualInformation_eq_sub, hconditional,
    expectedEntropy_eq_of_moments_eq ℓ₀ hap₀ hmoments deme fun hap ↦ (report hap).2]

/-- **The conditional entropy truncation certificate.**  Truncating the conditional entropy series
after `terms` terms gives the expected conditional entropy within `-|Score| / (terms + 1)` below
and `2 |Score| / (terms + 1)` above: the joint entropy tail over the `2 |Score|` cells lies in
`[0, 2 |Score| / (terms + 1)]` and the score entropy tail in `[0, |Score| / (terms + 1)]`. -/
theorem expectedConditionalEntropy_sub_truncation_mem
    (κ : Kernel (FrequencyState Deme Locus Allele) (FrequencyState Deme Locus Allele))
    [IsMarkovKernel κ] (x0 : FrequencyState Deme Locus Allele) (deme : Deme)
    (report : FullHaplotype Locus Allele → Score × Bool) (terms : ℕ) :
    -((Fintype.card Score : ℝ) / ((terms : ℝ) + 1))
        ≤ expectedConditionalEntropy κ x0 deme report - ∑ order ∈ Finset.range terms,
          (∫ y, eval (stateLaw y deme).mass (conditionalEntropyTermPolynomial report order)
            ∂(κ x0)) / ((order : ℝ) + 1)
    ∧ expectedConditionalEntropy κ x0 deme report - ∑ order ∈ Finset.range terms,
          (∫ y, eval (stateLaw y deme).mass (conditionalEntropyTermPolynomial report order)
            ∂(κ x0)) / ((order : ℝ) + 1)
        ≤ 2 * (Fintype.card Score : ℝ) / ((terms : ℝ) + 1) := by
  have hjoint := expectedEntropy_sub_truncation_mem κ x0 deme report terms
  have hscore := expectedEntropy_sub_truncation_mem κ x0 deme (fun hap ↦ (report hap).1) terms
  have hcard : (Fintype.card (Score × Bool) : ℝ) = 2 * (Fintype.card Score : ℝ) := by
    simp only [Fintype.card_prod, Fintype.card_bool, Nat.cast_mul, Nat.cast_ofNat]
    ring
  rw [hcard] at hjoint
  rw [expectedConditionalEntropy_eq_sub]
  simp only [integral_eval_conditionalEntropyTermPolynomial, Finset.sum_sub_distrib]
  constructor <;> linarith [hjoint.1, hjoint.2, hscore.1, hscore.2]

/-- **The mutual information truncation certificate.**  Truncating the mutual information series
after `terms` terms gives the expected mutual information within `-2 |Score| / (terms + 1)` below
and `(|Score| + 2) / (terms + 1)` above. -/
theorem expectedMutualInformation_sub_truncation_mem
    (κ : Kernel (FrequencyState Deme Locus Allele) (FrequencyState Deme Locus Allele))
    [IsMarkovKernel κ] (x0 : FrequencyState Deme Locus Allele) (deme : Deme)
    (report : FullHaplotype Locus Allele → Score × Bool) (terms : ℕ) :
    -(2 * (Fintype.card Score : ℝ) / ((terms : ℝ) + 1))
        ≤ expectedMutualInformation κ x0 deme report - ∑ order ∈ Finset.range terms,
          (∫ y, eval (stateLaw y deme).mass (mutualInformationTermPolynomial report order)
            ∂(κ x0)) / ((order : ℝ) + 1)
    ∧ expectedMutualInformation κ x0 deme report - ∑ order ∈ Finset.range terms,
          (∫ y, eval (stateLaw y deme).mass (mutualInformationTermPolynomial report order)
            ∂(κ x0)) / ((order : ℝ) + 1)
        ≤ ((Fintype.card Score : ℝ) + 2) / ((terms : ℝ) + 1) := by
  have houtcome := expectedEntropy_sub_truncation_mem κ x0 deme (fun hap ↦ (report hap).2) terms
  have hconditional := expectedConditionalEntropy_sub_truncation_mem κ x0 deme report terms
  have hbool : (Fintype.card Bool : ℝ) = 2 := by simp
  rw [hbool] at houtcome
  have hsplit : ((Fintype.card Score : ℝ) + 2) / ((terms : ℝ) + 1)
      = (Fintype.card Score : ℝ) / ((terms : ℝ) + 1) + 2 / ((terms : ℝ) + 1) := add_div _ _ _
  rw [expectedMutualInformation_eq_sub]
  simp only [integral_eval_mutualInformationTermPolynomial, Finset.sum_sub_distrib]
  constructor <;> linarith [houtcome.1, houtcome.2, hconditional.1, hconditional.2]

/-! ## Fixed forecasts through a kernel -/

/-- **Expected log loss of fixed group forecasts** for the report law of a deme, averaged under a
kernel started at `x₀`. -/
def expectedForecastLogLoss
    (κ : Kernel (FrequencyState Deme Locus Allele) (FrequencyState Deme Locus Allele))
    (x0 : FrequencyState Deme Locus Allele) (deme : Deme)
    (report : FullHaplotype Locus Allele → Score × Bool) (value : Score → ℝ) : ℝ :=
  ∫ y, forecastLogLoss ((stateLaw y deme).pushforward report) value ∂(κ x0)

/-- The log loss of fixed group forecasts is a continuous observable of the frequency state. -/
theorem continuous_forecastLogLoss (deme : Deme)
    (report : FullHaplotype Locus Allele → Score × Bool) (value : Score → ℝ) :
    Continuous fun y : FrequencyState Deme Locus Allele ↦
      forecastLogLoss ((stateLaw y deme).pushforward report) value := by
  simpa only [forecastLogLoss, FiniteReportLaw.expectation_pushforward,
    eval_expectationPolynomial] using continuous_eval_stateLaw deme
      (expectationPolynomial fun hap ↦ -Real.log (groupForecast value (report hap)))

/-- **Fixed forecasts are exact at budget one.**  The expected log loss of fixed group forecasts is
the coefficient vector of a linear population polynomial dotted with the budget-1 propagated
moments.

Assumes: `HasDualMoments κ 1 M`. -/
theorem expectedForecastLogLoss_eq_dotProduct (ℓ₀ : Locus)
    (κ : Kernel (FrequencyState Deme Locus Allele) (FrequencyState Deme Locus Allele))
    [IsMarkovKernel κ] (M : BudgetMatrix Deme Locus Allele 1) (hmoment : HasDualMoments κ 1 M)
    (x0 : FrequencyState Deme Locus Allele) (deme : Deme)
    (report : FullHaplotype Locus Allele → Score × Bool) (value : Score → ℝ) :
    expectedForecastLogLoss κ x0 deme report value
      = budgetCoefficients ℓ₀ (fun _ ↦ 1) (demePolynomial deme
          (expectationPolynomial fun hap ↦ -Real.log (groupForecast value (report hap))))
        ⬝ᵥ (M *ᵥ budgetMomentFeature (fun _ ↦ 1) x0) := by
  rw [← integral_eval_stateLaw_eq_dotProduct ℓ₀ 1 κ M hmoment deme _
    (totalDegree_expectationPolynomial_le _) x0]
  simp only [expectedForecastLogLoss, forecastLogLoss, FiniteReportLaw.expectation_pushforward,
    eval_expectationPolynomial]

/-- **The expected Gibbs inequality.**  Under every Markov kernel the expected log loss of fixed
group forecasts strictly inside the unit interval is at least the expected conditional entropy, so
the budget-1 computation bounds the expected repaired log loss from above. -/
theorem expectedConditionalEntropy_le_expectedForecastLogLoss
    (κ : Kernel (FrequencyState Deme Locus Allele) (FrequencyState Deme Locus Allele))
    [IsMarkovKernel κ] (x0 : FrequencyState Deme Locus Allele) (deme : Deme)
    (report : FullHaplotype Locus Allele → Score × Bool) (value : Score → ℝ)
    (hpos : ∀ group, 0 < value group) (hlt : ∀ group, value group < 1) :
    expectedConditionalEntropy κ x0 deme report
      ≤ expectedForecastLogLoss κ x0 deme report value := by
  unfold expectedConditionalEntropy expectedForecastLogLoss
  exact integral_mono
    (integrable_continuousObservable κ x0 (continuous_conditionalEntropy deme report))
    (integrable_continuousObservable κ x0 (continuous_forecastLogLoss deme report value))
    fun y ↦ conditionalEntropy_le_forecastLogLoss _ value hpos hlt

/-! ## McFadden's pseudo-`R²` and its portability -/

/-- **McFadden's pseudo-`R²` in ratio-of-expectations form**, `E I(S; Y) / E H(Y)` for the report
law of a deme under a kernel started at `x₀`. -/
def expectedPseudoRSquared
    (κ : Kernel (FrequencyState Deme Locus Allele) (FrequencyState Deme Locus Allele))
    (x0 : FrequencyState Deme Locus Allele) (deme : Deme)
    (report : FullHaplotype Locus Allele → Score × Bool) : ℝ :=
  expectedMutualInformation κ x0 deme report / expectedEntropy κ x0 deme fun hap ↦ (report hap).2

/-- **Pseudo-`R²` portability**: the target-over-source ratio of pseudo-`R²` in
ratio-of-expectations form. -/
def pseudoRSquaredPortability
    (κ : Kernel (FrequencyState Deme Locus Allele) (FrequencyState Deme Locus Allele))
    (x0 : FrequencyState Deme Locus Allele) (source target : Deme)
    (report : FullHaplotype Locus Allele → Score × Bool) : ℝ :=
  expectedPseudoRSquared κ x0 target report / expectedPseudoRSquared κ x0 source report

/-- **Pseudo-`R²` portability as a ratio of series of dot products.**  Mutual information and
outcome entropy of source and target are each a series over `k` of budget-`(k + 2)` dot products
divided by `k + 1`, and pseudo-`R²` portability is the ratio of their ratios.

Assumes: `∀ n, HasDualMoments κ n (M n)`. -/
theorem pseudoRSquaredPortability_eq_tsum_dotProduct (ℓ₀ : Locus)
    (κ : Kernel (FrequencyState Deme Locus Allele) (FrequencyState Deme Locus Allele))
    [IsMarkovKernel κ] (M : ∀ n : ℕ, BudgetMatrix Deme Locus Allele n)
    (hmoment : ∀ n : ℕ, HasDualMoments κ n (M n)) (x0 : FrequencyState Deme Locus Allele)
    (source target : Deme) (report : FullHaplotype Locus Allele → Score × Bool) :
    pseudoRSquaredPortability κ x0 source target report
      = ((∑' order : ℕ, (budgetCoefficients ℓ₀ (fun _ ↦ order + 2)
              (demePolynomial target (mutualInformationTermPolynomial report order))
            ⬝ᵥ (M (order + 2) *ᵥ budgetMomentFeature (fun _ ↦ order + 2) x0)) / ((order : ℝ) + 1))
          / ∑' order : ℕ, (budgetCoefficients ℓ₀ (fun _ ↦ order + 2)
              (demePolynomial target (entropyTermPolynomial (fun hap ↦ (report hap).2) order))
            ⬝ᵥ (M (order + 2) *ᵥ budgetMomentFeature (fun _ ↦ order + 2) x0)) / ((order : ℝ) + 1))
        / ((∑' order : ℕ, (budgetCoefficients ℓ₀ (fun _ ↦ order + 2)
              (demePolynomial source (mutualInformationTermPolynomial report order))
            ⬝ᵥ (M (order + 2) *ᵥ budgetMomentFeature (fun _ ↦ order + 2) x0)) / ((order : ℝ) + 1))
          / ∑' order : ℕ, (budgetCoefficients ℓ₀ (fun _ ↦ order + 2)
              (demePolynomial source (entropyTermPolynomial (fun hap ↦ (report hap).2) order))
            ⬝ᵥ (M (order + 2) *ᵥ budgetMomentFeature (fun _ ↦ order + 2) x0))
            / ((order : ℝ) + 1)) := by
  rw [pseudoRSquaredPortability, expectedPseudoRSquared, expectedPseudoRSquared,
    expectedMutualInformation_eq_tsum_dotProduct ℓ₀ κ M hmoment x0 target,
    expectedMutualInformation_eq_tsum_dotProduct ℓ₀ κ M hmoment x0 source,
    expectedEntropy_eq_tsum_dotProduct ℓ₀ κ M hmoment x0 target,
    expectedEntropy_eq_tsum_dotProduct ℓ₀ κ M hmoment x0 source]

/-- **Pseudo-`R²` portability sees a history only through its propagated moments.**  Two
histories, from two initial states, whose propagated moments agree at every budget `k + 2` have
equal pseudo-`R²` portability for every report map, source and target. -/
theorem pseudoRSquaredPortability_eq_of_moments_eq (ℓ₀ : Locus)
    (hap₀ : FullHaplotype Locus Allele)
    {first second : List ((NeutralRates Deme Locus Allele × ℝ≥0) ⊕ PulseMatrix Deme)}
    {x₁ x₂ : FrequencyState Deme Locus Allele}
    (hmoments : ∀ order : ℕ,
      historyEventPropagator (fun _ ↦ order + 2) first
          *ᵥ budgetMomentFeature (fun _ ↦ order + 2) x₁
        = historyEventPropagator (fun _ ↦ order + 2) second
          *ᵥ budgetMomentFeature (fun _ ↦ order + 2) x₂)
    (source target : Deme) (report : FullHaplotype Locus Allele → Score × Bool) :
    pseudoRSquaredPortability (historyEventKernel ℓ₀ hap₀ first) x₁ source target report
      = pseudoRSquaredPortability (historyEventKernel ℓ₀ hap₀ second) x₂ source target report := by
  simp only [pseudoRSquaredPortability, expectedPseudoRSquared,
    (expectedConditionalEntropy_and_mutualInformation_eq_of_moments_eq ℓ₀ hap₀ hmoments source
      report).2,
    (expectedConditionalEntropy_and_mutualInformation_eq_of_moments_eq ℓ₀ hap₀ hmoments target
      report).2,
    expectedEntropy_eq_of_moments_eq ℓ₀ hap₀ hmoments source,
    expectedEntropy_eq_of_moments_eq ℓ₀ hap₀ hmoments target]

end KernelScoreOutcome

end

end Descent.Portability.EndToEndLogLossLaw
