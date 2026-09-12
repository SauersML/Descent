/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.EndToEndDiscriminationLaw
import Descent.Portability.ReplicaMeasureCertificate

assert_below Descent.Decision Descent.Program

/-!
# The end-to-end law of the repaired Brier loss and the calibration error

`EndToEndDiscriminationLaw` carries the AUC of a score through a neutral demographic history, and
`EndToEndCalibrationLaw` carries the regression calibration slope and intercept.  This module
carries the two binary-outcome metrics of a finite score alphabet, the population repaired Brier
loss of NOTE 2 (23) and the calibration error of NOTE 2 (22), through every kernel with dual
moments (`EndToEndDiscriminationLaw.HasDualMoments`), in particular the history kernels.

The input.  A report map `hap ↦ (s, b)` sends a haplotype to a score group `s` and a binary
outcome `b`, and the deme's haplotype law pushes forward to the report law
`(stateLaw y deme).pushforward report` (`FiniteReportLaw.pushforward`).  Its cell masses are
linear in the haplotype frequencies: the mass of a report is the probability of its fibre
(`pushforwardMass_eq_expectation`), the value of the linear `cellPolynomial`
(`eval_cellPolynomial`, `totalDegree_cellPolynomial_le`), and a continuous observable of the state
(`continuous_pushforwardMass`).

Repaired Brier loss.  `ReplicaMetricInstances.conditionalRepairedBrier` is `p - Σ_s a_s² / q_s`
with `0 ≤ a_s² ≤ q_s ≤ 1`, for the case probability `p`, the case mass `a_s` and the mass `q_s` of
score group `s`.  Under every Markov kernel the expected repaired Brier loss
(`expectedRepairedBrier`) is the expected case probability minus, for every score group, the
series of expectations of `a_s² (1 - q_s)ᵏ` (`expectedRepairedBrier_eq_tsum`).  That term is the
polynomial `brierTermPolynomial` of total degree at most `k + 2` (`eval_brierTermPolynomial`,
`totalDegree_brierTermPolynomial_le`): `q_s` is linear, so the budgets grow by one per term,
against two per term for AUC and four for the squared correlation.  Through the propagated moments
the expected repaired Brier loss is a budget-1 dot product minus a finite sum of series of
budget-`(k + 2)` dot products (`expectedRepairedBrier_eq_dotProduct`,
`expectedRepairedBrier_historyEventKernel`, `expectedRepairedBrier_rateHistoryKernel`).  The Brier
loss of any fixed recalibration of the score groups is linear in the report law, so it bounds the
expected repaired loss from above by one budget-1 dot product
(`expectedRepairedBrier_le_integral_recalibration`, `expectedRepairedBrier_le_dotProduct`,
`expectedRepairedBrier_historyEventKernel_le`).

Calibration error.  `ReplicaMetricInstances.calibrationError` is `Σ_s |a_s - v_s q_s|` for score
values `v_s`, a sum of absolute values of the linear residuals `residualPolynomial`
(`eval_residualPolynomial`, `totalDegree_residualPolynomial_le`).  An absolute value is not a
polynomial, so no finite-budget identity is claimed.  Two finite-budget bounds hold.  The
calibration error of the expected residuals is a lower bound, a budget-1 computation
(`sum_abs_integral_calibrationResidual_le`).  The root mean square of each residual gives an upper
bound, a budget-2 computation (`meanAbs_le_sqrt_meanSquare`,
`expectedCalibrationError_le_sum_sqrt`).  Through the propagated moments both bounds are explicit
(`expectedCalibrationError_bounds_dotProduct`,
`expectedCalibrationError_bounds_historyEventKernel`,
`expectedCalibrationError_bounds_rateHistoryKernel`).

Significance.  Calibration of a clinical risk score, measured by Brier loss or by calibration
error, runs from the demographic process law through finite matrix computations: an exact series
for the repaired Brier loss, and a sandwich between a budget-1 and a budget-2 computation for the
calibration error.

Scope.  Score groups form a finite alphabet and outcomes are binary; one chromosome is sampled per
individual.  Whether the expected calibration error is determined by finitely many propagated
moments is not settled here: no pair of histories with equal moments and different expected
calibration error is constructed.  Truncation certificates for the Brier series are not restated.

## Empirical status

None.  The bodies here are polynomial identities, a pointwise geometric series, an elementary
mean-square inequality, and integrals of polynomials against Markov kernels whose moments are
matrix computations of supplied rates, so no measurement can bear on them.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.EndToEndBrierLaw

open MeasureTheory ProbabilityTheory MvPolynomial Descent.Coalescent PartialHaplotypeCarrier
  PartialHaplotypeDualGenerator PartialHaplotypeDualSemigroup NeutralFellerGenerator
  NeutralPolynomialSemigroup PartialHaplotypeMicroscopicApproximation PartialHaplotypePulseKernel
  NeutralPulseHistoryKernel NeutralRateHistoryRealization NeutralRateHistoryKernel
  ReplicaMetricInstances PositiveRatioExpansion EndToEndPortabilityLaw EndToEndDiscriminationLaw
open scoped Matrix NNReal

noncomputable section

/-! ## Report cells as population polynomials -/

section PopulationPolynomials

variable {State : Type*} [Fintype State]

/-- The mass that a pushforward law puts on one report is the probability of its fibre. -/
theorem pushforwardMass_eq_expectation {Report : Type*} [Fintype Report] [DecidableEq Report]
    (law : FiniteReportLaw State) (report : State → Report) (selected : Report) :
    (law.pushforward report).mass selected
      = law.expectation fun state ↦ if report state = selected then 1 else 0 := by
  have hpoint : (law.pushforward report).mass selected
      = (law.pushforward report).expectation fun other ↦ if other = selected then 1 else 0 := by
    simp [FiniteReportLaw.expectation]
  rw [hpoint, FiniteReportLaw.expectation_pushforward]

/-- The cell polynomial of a report: the linear polynomial whose value at a law is the mass that
its pushforward puts on the report. -/
def cellPolynomial {Report : Type*} [DecidableEq Report] (report : State → Report)
    (selected : Report) : MvPolynomial State ℝ :=
  expectationPolynomial fun state ↦ if report state = selected then 1 else 0

/-- A cell polynomial evaluates to the pushforward mass of its report. -/
theorem eval_cellPolynomial {Report : Type*} [Fintype Report] [DecidableEq Report]
    (law : FiniteReportLaw State) (report : State → Report) (selected : Report) :
    eval law.mass (cellPolynomial report selected) = (law.pushforward report).mass selected := by
  rw [cellPolynomial, eval_expectationPolynomial, pushforwardMass_eq_expectation]

/-- A cell polynomial has total degree at most one. -/
theorem totalDegree_cellPolynomial_le {Report : Type*} [DecidableEq Report]
    (report : State → Report) (selected : Report) :
    (cellPolynomial report selected).totalDegree ≤ 1 :=
  totalDegree_expectationPolynomial_le _

variable {Score : Type*} [Fintype Score] [DecidableEq Score]

/-- The score-group polynomial `q_s`, the sum of the two cell polynomials of a score group, has
total degree at most one. -/
theorem totalDegree_groupCells_le (report : State → Score × Bool) (group : Score) :
    (cellPolynomial report (group, false) + cellPolynomial report (group, true)).totalDegree
      ≤ 1 :=
  (totalDegree_add _ _).trans
    (max_le (totalDegree_cellPolynomial_le _ _) (totalDegree_cellPolynomial_le _ _))

/-- The `k`-th term `a_s² (1 - q_s)ᵏ` of NOTE 2 (15) for the repaired Brier loss of one score
group, as a polynomial in the population probability vector. -/
def brierTermPolynomial (report : State → Score × Bool) (group : Score) (k : ℕ) :
    MvPolynomial State ℝ :=
  cellPolynomial report (group, true) ^ 2
    * (1 - (cellPolynomial report (group, false) + cellPolynomial report (group, true))) ^ k

/-- The Brier term polynomial evaluates to `a_s² (1 - q_s)ᵏ` of the report law. -/
theorem eval_brierTermPolynomial (law : FiniteReportLaw State) (report : State → Score × Bool)
    (group : Score) (k : ℕ) :
    eval law.mass (brierTermPolynomial report group k)
      = (law.pushforward report).mass (group, true) ^ 2
        * (1 - scoreGroupMass (law.pushforward report) group) ^ k := by
  simp only [brierTermPolynomial, map_mul, map_pow, map_sub, map_one, map_add,
    eval_cellPolynomial, scoreGroupMass]

/-- The Brier term polynomial has total degree at most `k + 2`. -/
theorem totalDegree_brierTermPolynomial_le (report : State → Score × Bool) (group : Score)
    (k : ℕ) : (brierTermPolynomial report group k).totalDegree ≤ k + 2 := by
  have hsquare : (cellPolynomial report (group, true) ^ 2).totalDegree ≤ 2 * 1 :=
    (totalDegree_pow _ 2).trans (Nat.mul_le_mul_left 2 (totalDegree_cellPolynomial_le _ _))
  exact (totalDegree_expansionTerm_le _ _ (2 * 1) 1 k hsquare
    (totalDegree_groupCells_le report group)).trans (by omega)

/-- The calibration residual `a_s - v_s q_s` of NOTE 2 (22) of one score group, as a linear
polynomial in the population probability vector. -/
def residualPolynomial (report : State → Score × Bool) (value : Score → ℝ) (group : Score) :
    MvPolynomial State ℝ :=
  cellPolynomial report (group, true)
    - C (value group) * (cellPolynomial report (group, false) + cellPolynomial report (group, true))

/-- The residual polynomial evaluates to the corpus calibration residual of the report law. -/
theorem eval_residualPolynomial (law : FiniteReportLaw State) (report : State → Score × Bool)
    (value : Score → ℝ) (group : Score) :
    eval law.mass (residualPolynomial report value group)
      = calibrationResidual (law.pushforward report) value group := by
  simp only [residualPolynomial, map_sub, map_mul, map_add, eval_C, eval_cellPolynomial,
    calibrationResidual, scoreGroupMass]

/-- The residual polynomial has total degree at most one. -/
theorem totalDegree_residualPolynomial_le (report : State → Score × Bool) (value : Score → ℝ)
    (group : Score) : (residualPolynomial report value group).totalDegree ≤ 1 := by
  have hscaled : (C (value group) * (cellPolynomial report (group, false)
      + cellPolynomial report (group, true))).totalDegree ≤ 1 := by
    refine (totalDegree_mul _ _).trans ?_
    rw [totalDegree_C, zero_add]
    exact totalDegree_groupCells_le report group
  exact (totalDegree_sub _ _).trans (max_le (totalDegree_cellPolynomial_le _ _) hscaled)

/-- The square of the residual polynomial has total degree at most two. -/
theorem totalDegree_residualPolynomial_sq_le (report : State → Score × Bool)
    (value : Score → ℝ) (group : Score) :
    (residualPolynomial report value group ^ 2).totalDegree ≤ 2 := by
  have hsquare := (totalDegree_pow (residualPolynomial report value group) 2).trans
    (Nat.mul_le_mul_left 2 (totalDegree_residualPolynomial_le report value group))
  omega

end PopulationPolynomials

/-- **Mean absolute value against root mean square.**  On a probability measure the mean absolute
value of a square-integrable observable is at most the square root of its mean square. -/
theorem meanAbs_le_sqrt_meanSquare {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] {f : Ω → ℝ} (hf : Integrable f μ)
    (hsquare : Integrable (fun point ↦ f point ^ 2) μ) :
    ∫ point, |f point| ∂μ ≤ Real.sqrt (∫ point, f point ^ 2 ∂μ) := by
  have hmean : 0 ≤ ∫ point, |f point| ∂μ := integral_nonneg fun point ↦ abs_nonneg _
  have hpoint : ∀ point, 2 * (∫ other, |f other| ∂μ) * |f point|
      ≤ f point ^ 2 + (∫ other, |f other| ∂μ) ^ 2 := fun point ↦ by
    nlinarith [sq_nonneg (|f point| - ∫ other, |f other| ∂μ), sq_abs (f point)]
  have hintegrated : ∫ point, 2 * (∫ other, |f other| ∂μ) * |f point| ∂μ
      ≤ ∫ point, (f point ^ 2 + (∫ other, |f other| ∂μ) ^ 2) ∂μ :=
    integral_mono (hf.abs.const_mul _) (hsquare.add (integrable_const _)) hpoint
  rw [integral_const_mul, integral_add hsquare (integrable_const _), integral_const,
    measureReal_univ_eq_one, one_smul] at hintegrated
  have hsquareMean : (∫ point, |f point| ∂μ) ^ 2 ≤ ∫ point, f point ^ 2 ∂μ := by nlinarith
  calc ∫ point, |f point| ∂μ = |∫ point, |f point| ∂μ| := (abs_of_nonneg hmean).symm
    _ ≤ Real.sqrt (∫ point, f point ^ 2 ∂μ) := Real.abs_le_sqrt hsquareMean

variable {Deme Locus : Type*} {Allele : Locus → Type*}
variable [Fintype Deme] [DecidableEq Deme] [Fintype Locus] [DecidableEq Locus]
  [∀ ℓ, Fintype (Allele ℓ)] [∀ ℓ, DecidableEq (Allele ℓ)]
variable {Score : Type*} [Fintype Score] [DecidableEq Score]

/-! ## Report laws of a frequency state -/

/-- A continuous observable of the frequency state is integrable under every Markov kernel. -/
theorem integrable_continuousObservable
    (κ : Kernel (FrequencyState Deme Locus Allele) (FrequencyState Deme Locus Allele))
    [IsMarkovKernel κ] (x0 : FrequencyState Deme Locus Allele)
    {observable : FrequencyState Deme Locus Allele → ℝ} (hcontinuous : Continuous observable) :
    Integrable observable (κ x0) :=
  (BoundedContinuousFunction.mkOfCompact ⟨observable, hcontinuous⟩).integrable _

/-- The mass that the report law of a deme puts on one report is a continuous observable of the
frequency state. -/
theorem continuous_pushforwardMass {Report : Type*} [Fintype Report] [DecidableEq Report]
    (deme : Deme) (report : FullHaplotype Locus Allele → Report) (selected : Report) :
    Continuous fun y : FrequencyState Deme Locus Allele ↦
      ((stateLaw y deme).pushforward report).mass selected := by
  simpa only [eval_cellPolynomial] using
    continuous_eval_stateLaw deme (cellPolynomial report selected)

/-- The squared case mass `a_s²` of a score group is a measurable observable of the state. -/
theorem measurable_squaredCaseMass (deme : Deme)
    (report : FullHaplotype Locus Allele → Score × Bool) (group : Score) :
    Measurable fun y : FrequencyState Deme Locus Allele ↦
      ((stateLaw y deme).pushforward report).mass (group, true) ^ 2 :=
  ((continuous_pushforwardMass deme report (group, true)).pow 2).measurable

/-- The mass `q_s` of a score group is a measurable observable of the state. -/
theorem measurable_scoreGroupMass (deme : Deme)
    (report : FullHaplotype Locus Allele → Score × Bool) (group : Score) :
    Measurable fun y : FrequencyState Deme Locus Allele ↦
      scoreGroupMass ((stateLaw y deme).pushforward report) group :=
  ((continuous_pushforwardMass deme report (group, false)).add
    (continuous_pushforwardMass deme report (group, true))).measurable

/-! ## The repaired Brier loss -/

/-- **Expected repaired Brier loss**: the population-optimal score-conditional Brier loss of the
report law of a deme, averaged under a kernel started at `x₀`. -/
def expectedRepairedBrier
    (κ : Kernel (FrequencyState Deme Locus Allele) (FrequencyState Deme Locus Allele))
    (x0 : FrequencyState Deme Locus Allele) (deme : Deme)
    (report : FullHaplotype Locus Allele → Score × Bool) : ℝ :=
  ∫ y, conditionalRepairedBrier ((stateLaw y deme).pushforward report) ∂(κ x0)

/-- The repaired Brier loss of the report law of a deme, with the ratio `a_s² / q_s` of every score
group read as a function of the frequency state. -/
theorem conditionalRepairedBrier_pushforward_stateLaw (deme : Deme)
    (report : FullHaplotype Locus Allele → Score × Bool) (y : FrequencyState Deme Locus Allele) :
    conditionalRepairedBrier ((stateLaw y deme).pushforward report)
      = ((stateLaw y deme).pushforward report).expectation
          (fun r ↦ ChronologyReportLaw.alleleValue r.2)
        - ∑ group, ratioOnDefined
            (fun z : FrequencyState Deme Locus Allele ↦
              ((stateLaw z deme).pushforward report).mass (group, true) ^ 2)
            (fun z ↦ scoreGroupMass ((stateLaw z deme).pushforward report) group) y :=
  rfl

/-- The case probability of the report law of a deme is integrable under every Markov kernel. -/
theorem integrable_caseProbability
    (κ : Kernel (FrequencyState Deme Locus Allele) (FrequencyState Deme Locus Allele))
    [IsMarkovKernel κ] (x0 : FrequencyState Deme Locus Allele) (deme : Deme)
    (report : FullHaplotype Locus Allele → Score × Bool) :
    Integrable (fun y ↦ ((stateLaw y deme).pushforward report).expectation
      (fun r ↦ ChronologyReportLaw.alleleValue r.2)) (κ x0) := by
  have hcontinuous : Continuous fun y : FrequencyState Deme Locus Allele ↦
      ((stateLaw y deme).pushforward report).expectation
        (fun r ↦ ChronologyReportLaw.alleleValue r.2) := by
    simpa only [FiniteReportLaw.expectation_pushforward, eval_expectationPolynomial] using
      continuous_eval_stateLaw deme
        (expectationPolynomial fun hap ↦ ChronologyReportLaw.alleleValue (report hap).2)
  exact integrable_continuousObservable κ x0 hcontinuous

/-- The ratio `a_s² / q_s` of one score group, read as zero on an empty group, is integrable under
every Markov kernel. -/
theorem integrable_brierRatio
    (κ : Kernel (FrequencyState Deme Locus Allele) (FrequencyState Deme Locus Allele))
    [IsMarkovKernel κ] (x0 : FrequencyState Deme Locus Allele) (deme : Deme)
    (report : FullHaplotype Locus Allele → Score × Bool) (group : Score) :
    Integrable (ratioOnDefined
      (fun y : FrequencyState Deme Locus Allele ↦
        ((stateLaw y deme).pushforward report).mass (group, true) ^ 2)
      (fun y ↦ scoreGroupMass ((stateLaw y deme).pushforward report) group)) (κ x0) :=
  ReplicaMeasureCertificate.integrable_of_unit_bounds (κ x0) _
    (ReplicaMeasureCertificate.measurable_ratioOnDefined _ _
      (measurable_squaredCaseMass deme report group) (measurable_scoreGroupMass deme report group))
    (ratioOnDefined_nonneg _ _ fun y ↦ (squaredCaseMass_le_scoreGroupMass _ group).1)
    (ratioOnDefined_le_one _ _ fun y ↦ (squaredCaseMass_le_scoreGroupMass _ group).2.1)

/-- **NOTE 2 (15) for the repaired Brier loss under a Markov kernel.**  The expected repaired Brier
loss of a deme is the expected case probability minus, for every score group, the series of
expectations of `a_s² (1 - q_s)ᵏ`. -/
theorem expectedRepairedBrier_eq_tsum
    (κ : Kernel (FrequencyState Deme Locus Allele) (FrequencyState Deme Locus Allele))
    [IsMarkovKernel κ] (x0 : FrequencyState Deme Locus Allele) (deme : Deme)
    (report : FullHaplotype Locus Allele → Score × Bool) :
    expectedRepairedBrier κ x0 deme report
      = (∫ y, ((stateLaw y deme).pushforward report).expectation
          (fun r ↦ ChronologyReportLaw.alleleValue r.2) ∂(κ x0))
        - ∑ group, ∑' k : ℕ, ∫ y, ((stateLaw y deme).pushforward report).mass (group, true) ^ 2
          * (1 - scoreGroupMass ((stateLaw y deme).pushforward report) group) ^ k ∂(κ x0) := by
  simp only [expectedRepairedBrier, conditionalRepairedBrier_pushforward_stateLaw]
  rw [integral_sub (integrable_caseProbability κ x0 deme report)
      (integrable_finset_sum Finset.univ fun group _ ↦
        integrable_brierRatio κ x0 deme report group),
    integral_finset_sum Finset.univ fun group _ ↦ integrable_brierRatio κ x0 deme report group]
  congr 1
  exact Finset.sum_congr rfl fun group _ ↦ integral_ratioOnDefined_eq_tsum (κ x0) _ _
    (measurable_squaredCaseMass deme report group) (measurable_scoreGroupMass deme report group)
    (fun y ↦ (squaredCaseMass_le_scoreGroupMass _ group).1)
    (fun y ↦ (squaredCaseMass_le_scoreGroupMass _ group).2.1)
    (fun y ↦ (squaredCaseMass_le_scoreGroupMass _ group).2.2)

/-- **The expected repaired Brier loss through the propagated moments.**  It is the coefficient
vector of the case probability dotted with the budget-1 propagated moments, minus, for every score
group, the series over `k` of the coefficient vectors of `a_s² (1 - q_s)ᵏ` dotted with the
budget-`(k + 2)` propagated moments.

Assumes: `∀ n, HasDualMoments κ n (M n)`. -/
theorem expectedRepairedBrier_eq_dotProduct (ℓ₀ : Locus)
    (κ : Kernel (FrequencyState Deme Locus Allele) (FrequencyState Deme Locus Allele))
    [IsMarkovKernel κ] (M : ∀ n : ℕ, BudgetMatrix Deme Locus Allele n)
    (hmoment : ∀ n : ℕ, HasDualMoments κ n (M n)) (x0 : FrequencyState Deme Locus Allele)
    (deme : Deme) (report : FullHaplotype Locus Allele → Score × Bool) :
    expectedRepairedBrier κ x0 deme report
      = budgetCoefficients ℓ₀ (fun _ ↦ 1)
          (demePolynomial deme
            (expectationPolynomial fun hap ↦ ChronologyReportLaw.alleleValue (report hap).2))
        ⬝ᵥ (M 1 *ᵥ budgetMomentFeature (fun _ ↦ 1) x0)
        - ∑ group, ∑' k : ℕ, budgetCoefficients ℓ₀ (fun _ ↦ k + 2)
            (demePolynomial deme (brierTermPolynomial report group k))
          ⬝ᵥ (M (k + 2) *ᵥ budgetMomentFeature (fun _ ↦ k + 2) x0) := by
  rw [expectedRepairedBrier_eq_tsum]
  congr 1
  · simpa only [FiniteReportLaw.expectation_pushforward, eval_expectationPolynomial] using
      integral_eval_stateLaw_eq_dotProduct ℓ₀ 1 κ (M 1) (hmoment 1) deme
        (expectationPolynomial fun hap ↦ ChronologyReportLaw.alleleValue (report hap).2)
        (totalDegree_expectationPolynomial_le _) x0
  · refine Finset.sum_congr rfl fun group _ ↦ tsum_congr fun k ↦ ?_
    simpa only [eval_brierTermPolynomial] using
      integral_eval_stateLaw_eq_dotProduct ℓ₀ (k + 2) κ (M (k + 2)) (hmoment (k + 2)) deme _
        (totalDegree_brierTermPolynomial_le report group k) x0

/-- **The expected repaired Brier loss along a history of epochs, splits and pulses.** -/
theorem expectedRepairedBrier_historyEventKernel (ℓ₀ : Locus) (hap₀ : FullHaplotype Locus Allele)
    (events : List ((NeutralRates Deme Locus Allele × ℝ≥0) ⊕ PulseMatrix Deme))
    (x0 : FrequencyState Deme Locus Allele) (deme : Deme)
    (report : FullHaplotype Locus Allele → Score × Bool) :
    expectedRepairedBrier (historyEventKernel ℓ₀ hap₀ events) x0 deme report
      = budgetCoefficients ℓ₀ (fun _ ↦ 1)
          (demePolynomial deme
            (expectationPolynomial fun hap ↦ ChronologyReportLaw.alleleValue (report hap).2))
        ⬝ᵥ (historyEventPropagator (fun _ ↦ 1) events *ᵥ budgetMomentFeature (fun _ ↦ 1) x0)
        - ∑ group, ∑' k : ℕ, budgetCoefficients ℓ₀ (fun _ ↦ k + 2)
            (demePolynomial deme (brierTermPolynomial report group k))
          ⬝ᵥ (historyEventPropagator (fun _ ↦ k + 2) events
            *ᵥ budgetMomentFeature (fun _ ↦ k + 2) x0) := by
  haveI := isMarkovKernel_historyEventKernel ℓ₀ hap₀ events
  exact expectedRepairedBrier_eq_dotProduct ℓ₀ (historyEventKernel ℓ₀ hap₀ events)
    (fun n ↦ historyEventPropagator (fun _ ↦ n) events)
    (hasDualMoments_historyEventKernel ℓ₀ hap₀ events) x0 deme report

/-- **The expected repaired Brier loss along a time-varying rate history.** -/
theorem expectedRepairedBrier_rateHistoryKernel {rates : ℝ → NeutralRates Deme Locus Allele}
    {T : ℝ} (hT : 0 ≤ T) (hcontinuous : ∀ capacity : Locus → ℕ,
      ContinuousOn (fun t ↦ dualGenerator (rates t) capacity) (Set.Icc 0 T))
    (ℓ₀ : Locus) (hap₀ : FullHaplotype Locus Allele) (x0 : FrequencyState Deme Locus Allele)
    (deme : Deme) (report : FullHaplotype Locus Allele → Score × Bool) :
    expectedRepairedBrier (rateHistoryKernel rates ℓ₀ hap₀ hT hcontinuous) x0 deme report
      = budgetCoefficients ℓ₀ (fun _ ↦ 1)
          (demePolynomial deme
            (expectationPolynomial fun hap ↦ ChronologyReportLaw.alleleValue (report hap).2))
        ⬝ᵥ (rateHistoryDualPropagator rates (fun _ ↦ 1) T *ᵥ budgetMomentFeature (fun _ ↦ 1) x0)
        - ∑ group, ∑' k : ℕ, budgetCoefficients ℓ₀ (fun _ ↦ k + 2)
            (demePolynomial deme (brierTermPolynomial report group k))
          ⬝ᵥ (rateHistoryDualPropagator rates (fun _ ↦ k + 2) T
            *ᵥ budgetMomentFeature (fun _ ↦ k + 2) x0) := by
  haveI := isMarkovKernel_rateHistoryKernel hT hcontinuous ℓ₀ hap₀
  exact expectedRepairedBrier_eq_dotProduct ℓ₀ (rateHistoryKernel rates ℓ₀ hap₀ hT hcontinuous)
    (fun n ↦ rateHistoryDualPropagator rates (fun _ ↦ n) T)
    (hasDualMoments_rateHistoryKernel hT hcontinuous ℓ₀ hap₀) x0 deme report

/-- **A fixed recalibration bounds the expected repaired Brier loss.**  For every recalibration `g`
of the score groups, the expected repaired Brier loss is at most the expected Brier loss of `g`,
the expectation of `(g_s - b)²` under the deme's haplotype law. -/
theorem expectedRepairedBrier_le_integral_recalibration
    (κ : Kernel (FrequencyState Deme Locus Allele) (FrequencyState Deme Locus Allele))
    [IsMarkovKernel κ] (x0 : FrequencyState Deme Locus Allele) (deme : Deme)
    (report : FullHaplotype Locus Allele → Score × Bool) (recalibration : Score → ℝ) :
    expectedRepairedBrier κ x0 deme report
      ≤ ∫ y, (stateLaw y deme).expectation (fun hap ↦
          (recalibration (report hap).1 - ChronologyReportLaw.alleleValue (report hap).2) ^ 2)
        ∂(κ x0) := by
  have hbrier : Integrable
      (fun y ↦ conditionalRepairedBrier ((stateLaw y deme).pushforward report)) (κ x0) := by
    simp only [conditionalRepairedBrier_pushforward_stateLaw]
    exact (integrable_caseProbability κ x0 deme report).sub
      (integrable_finset_sum Finset.univ fun group _ ↦
        integrable_brierRatio κ x0 deme report group)
  have hcontinuous : Continuous fun y : FrequencyState Deme Locus Allele ↦
      (stateLaw y deme).expectation (fun hap ↦
        (recalibration (report hap).1 - ChronologyReportLaw.alleleValue (report hap).2) ^ 2) := by
    simpa only [eval_expectationPolynomial] using continuous_eval_stateLaw deme
      (expectationPolynomial fun hap ↦
        (recalibration (report hap).1 - ChronologyReportLaw.alleleValue (report hap).2) ^ 2)
  refine integral_mono hbrier (integrable_continuousObservable κ x0 hcontinuous) fun y ↦ ?_
  have hpoint := conditionalRepairedBrier_le_meanSquaredError
    ((stateLaw y deme).pushforward report) recalibration
  rwa [FiniteReportLaw.meanSquaredError, FiniteReportLaw.expectation_pushforward] at hpoint

/-- **A budget-1 upper bound on the expected repaired Brier loss.**  For every recalibration `g`
of the score groups, the expected repaired Brier loss is at most the coefficient vector of the
Brier loss of `g` dotted with the budget-1 propagated moments.

Assumes: `HasDualMoments κ 1 M`. -/
theorem expectedRepairedBrier_le_dotProduct (ℓ₀ : Locus)
    (κ : Kernel (FrequencyState Deme Locus Allele) (FrequencyState Deme Locus Allele))
    [IsMarkovKernel κ] (M : BudgetMatrix Deme Locus Allele 1) (hmoment : HasDualMoments κ 1 M)
    (x0 : FrequencyState Deme Locus Allele) (deme : Deme)
    (report : FullHaplotype Locus Allele → Score × Bool) (recalibration : Score → ℝ) :
    expectedRepairedBrier κ x0 deme report
      ≤ budgetCoefficients ℓ₀ (fun _ ↦ 1)
          (demePolynomial deme (expectationPolynomial fun hap ↦
            (recalibration (report hap).1 - ChronologyReportLaw.alleleValue (report hap).2) ^ 2))
        ⬝ᵥ (M *ᵥ budgetMomentFeature (fun _ ↦ 1) x0) := by
  have hlinear := integral_eval_stateLaw_eq_dotProduct ℓ₀ 1 κ M hmoment deme
    (expectationPolynomial fun hap ↦
      (recalibration (report hap).1 - ChronologyReportLaw.alleleValue (report hap).2) ^ 2)
    (totalDegree_expectationPolynomial_le _) x0
  simp only [eval_expectationPolynomial] at hlinear
  exact (expectedRepairedBrier_le_integral_recalibration κ x0 deme report recalibration).trans_eq
    hlinear

/-- **A budget-1 upper bound along a history of epochs, splits and pulses.** -/
theorem expectedRepairedBrier_historyEventKernel_le (ℓ₀ : Locus)
    (hap₀ : FullHaplotype Locus Allele)
    (events : List ((NeutralRates Deme Locus Allele × ℝ≥0) ⊕ PulseMatrix Deme))
    (x0 : FrequencyState Deme Locus Allele) (deme : Deme)
    (report : FullHaplotype Locus Allele → Score × Bool) (recalibration : Score → ℝ) :
    expectedRepairedBrier (historyEventKernel ℓ₀ hap₀ events) x0 deme report
      ≤ budgetCoefficients ℓ₀ (fun _ ↦ 1)
          (demePolynomial deme (expectationPolynomial fun hap ↦
            (recalibration (report hap).1 - ChronologyReportLaw.alleleValue (report hap).2) ^ 2))
        ⬝ᵥ (historyEventPropagator (fun _ ↦ 1) events *ᵥ budgetMomentFeature (fun _ ↦ 1) x0) := by
  haveI := isMarkovKernel_historyEventKernel ℓ₀ hap₀ events
  exact expectedRepairedBrier_le_dotProduct ℓ₀ (historyEventKernel ℓ₀ hap₀ events) _
    (hasDualMoments_historyEventKernel ℓ₀ hap₀ events 1) x0 deme report recalibration

/-! ## The calibration error -/

/-- **Expected calibration error**: the calibration error `Σ_s |a_s - v_s q_s|` of the report law
of a deme, averaged under a kernel started at `x₀`. -/
def expectedCalibrationError
    (κ : Kernel (FrequencyState Deme Locus Allele) (FrequencyState Deme Locus Allele))
    (x0 : FrequencyState Deme Locus Allele) (deme : Deme)
    (report : FullHaplotype Locus Allele → Score × Bool) (value : Score → ℝ) : ℝ :=
  ∫ y, calibrationError ((stateLaw y deme).pushforward report) value ∂(κ x0)

/-- The calibration residual of a score group is a continuous observable of the frequency
state. -/
theorem continuous_calibrationResidual (deme : Deme)
    (report : FullHaplotype Locus Allele → Score × Bool) (value : Score → ℝ) (group : Score) :
    Continuous fun y : FrequencyState Deme Locus Allele ↦
      calibrationResidual ((stateLaw y deme).pushforward report) value group := by
  simpa only [eval_residualPolynomial] using
    continuous_eval_stateLaw deme (residualPolynomial report value group)

/-- The expected calibration error is the sum over score groups of the expected absolute
residuals. -/
theorem expectedCalibrationError_eq_sum
    (κ : Kernel (FrequencyState Deme Locus Allele) (FrequencyState Deme Locus Allele))
    [IsMarkovKernel κ] (x0 : FrequencyState Deme Locus Allele) (deme : Deme)
    (report : FullHaplotype Locus Allele → Score × Bool) (value : Score → ℝ) :
    expectedCalibrationError κ x0 deme report value
      = ∑ group, ∫ y, |calibrationResidual ((stateLaw y deme).pushforward report) value group|
          ∂(κ x0) := by
  simp only [expectedCalibrationError, calibrationError]
  exact integral_finset_sum Finset.univ fun group _ ↦
    (integrable_continuousObservable κ x0
      (continuous_calibrationResidual deme report value group)).abs

/-- **The calibration error of the expected residuals is a lower bound.**  The expected
calibration error is at least the calibration error formed from the expected residuals, by the
triangle inequality for integrals. -/
theorem sum_abs_integral_calibrationResidual_le
    (κ : Kernel (FrequencyState Deme Locus Allele) (FrequencyState Deme Locus Allele))
    [IsMarkovKernel κ] (x0 : FrequencyState Deme Locus Allele) (deme : Deme)
    (report : FullHaplotype Locus Allele → Score × Bool) (value : Score → ℝ) :
    ∑ group, |∫ y, calibrationResidual ((stateLaw y deme).pushforward report) value group
        ∂(κ x0)|
      ≤ expectedCalibrationError κ x0 deme report value := by
  rw [expectedCalibrationError_eq_sum]
  exact Finset.sum_le_sum fun group _ ↦ abs_integral_le_integral_abs

/-- **The root mean square of the residuals is an upper bound.**  The expected calibration error
is at most the sum over score groups of the square roots of the expected squared residuals. -/
theorem expectedCalibrationError_le_sum_sqrt
    (κ : Kernel (FrequencyState Deme Locus Allele) (FrequencyState Deme Locus Allele))
    [IsMarkovKernel κ] (x0 : FrequencyState Deme Locus Allele) (deme : Deme)
    (report : FullHaplotype Locus Allele → Score × Bool) (value : Score → ℝ) :
    expectedCalibrationError κ x0 deme report value
      ≤ ∑ group, Real.sqrt (∫ y, calibrationResidual ((stateLaw y deme).pushforward report) value
          group ^ 2 ∂(κ x0)) := by
  rw [expectedCalibrationError_eq_sum]
  exact Finset.sum_le_sum fun group _ ↦ meanAbs_le_sqrt_meanSquare (κ x0)
    (integrable_continuousObservable κ x0
      (continuous_calibrationResidual deme report value group))
    (integrable_continuousObservable κ x0
      ((continuous_calibrationResidual deme report value group).pow 2))

/-- **The calibration-error sandwich through the propagated moments.**  The expected calibration
error lies between the calibration error of the residual coefficient vectors dotted with the
budget-1 propagated moments and the sum of the square roots of the squared-residual coefficient
vectors dotted with the budget-2 propagated moments.

Assumes: `∀ n, HasDualMoments κ n (M n)`. -/
theorem expectedCalibrationError_bounds_dotProduct (ℓ₀ : Locus)
    (κ : Kernel (FrequencyState Deme Locus Allele) (FrequencyState Deme Locus Allele))
    [IsMarkovKernel κ] (M : ∀ n : ℕ, BudgetMatrix Deme Locus Allele n)
    (hmoment : ∀ n : ℕ, HasDualMoments κ n (M n)) (x0 : FrequencyState Deme Locus Allele)
    (deme : Deme) (report : FullHaplotype Locus Allele → Score × Bool) (value : Score → ℝ) :
    ∑ group, |budgetCoefficients ℓ₀ (fun _ ↦ 1)
          (demePolynomial deme (residualPolynomial report value group))
        ⬝ᵥ (M 1 *ᵥ budgetMomentFeature (fun _ ↦ 1) x0)|
      ≤ expectedCalibrationError κ x0 deme report value
    ∧ expectedCalibrationError κ x0 deme report value
      ≤ ∑ group, Real.sqrt (budgetCoefficients ℓ₀ (fun _ ↦ 2)
          (demePolynomial deme (residualPolynomial report value group ^ 2))
        ⬝ᵥ (M 2 *ᵥ budgetMomentFeature (fun _ ↦ 2) x0)) := by
  have hlinear : ∀ group, ∫ y, calibrationResidual ((stateLaw y deme).pushforward report) value
      group ∂(κ x0)
      = budgetCoefficients ℓ₀ (fun _ ↦ 1)
          (demePolynomial deme (residualPolynomial report value group))
        ⬝ᵥ (M 1 *ᵥ budgetMomentFeature (fun _ ↦ 1) x0) := fun group ↦ by
    simpa only [eval_residualPolynomial] using integral_eval_stateLaw_eq_dotProduct ℓ₀ 1 κ (M 1)
      (hmoment 1) deme _ (totalDegree_residualPolynomial_le report value group) x0
  have hquadratic : ∀ group, ∫ y, calibrationResidual ((stateLaw y deme).pushforward report)
      value group ^ 2 ∂(κ x0)
      = budgetCoefficients ℓ₀ (fun _ ↦ 2)
          (demePolynomial deme (residualPolynomial report value group ^ 2))
        ⬝ᵥ (M 2 *ᵥ budgetMomentFeature (fun _ ↦ 2) x0) := fun group ↦ by
    simpa only [map_pow, eval_residualPolynomial] using integral_eval_stateLaw_eq_dotProduct ℓ₀ 2
      κ (M 2) (hmoment 2) deme _ (totalDegree_residualPolynomial_sq_le report value group) x0
  refine ⟨?_, ?_⟩
  · simpa only [hlinear] using sum_abs_integral_calibrationResidual_le κ x0 deme report value
  · simpa only [hquadratic] using expectedCalibrationError_le_sum_sqrt κ x0 deme report value

/-- **The calibration-error sandwich along a history of epochs, splits and pulses.** -/
theorem expectedCalibrationError_bounds_historyEventKernel (ℓ₀ : Locus)
    (hap₀ : FullHaplotype Locus Allele)
    (events : List ((NeutralRates Deme Locus Allele × ℝ≥0) ⊕ PulseMatrix Deme))
    (x0 : FrequencyState Deme Locus Allele) (deme : Deme)
    (report : FullHaplotype Locus Allele → Score × Bool) (value : Score → ℝ) :
    ∑ group, |budgetCoefficients ℓ₀ (fun _ ↦ 1)
          (demePolynomial deme (residualPolynomial report value group))
        ⬝ᵥ (historyEventPropagator (fun _ ↦ 1) events *ᵥ budgetMomentFeature (fun _ ↦ 1) x0)|
      ≤ expectedCalibrationError (historyEventKernel ℓ₀ hap₀ events) x0 deme report value
    ∧ expectedCalibrationError (historyEventKernel ℓ₀ hap₀ events) x0 deme report value
      ≤ ∑ group, Real.sqrt (budgetCoefficients ℓ₀ (fun _ ↦ 2)
          (demePolynomial deme (residualPolynomial report value group ^ 2))
        ⬝ᵥ (historyEventPropagator (fun _ ↦ 2) events *ᵥ budgetMomentFeature (fun _ ↦ 2) x0)) := by
  haveI := isMarkovKernel_historyEventKernel ℓ₀ hap₀ events
  exact expectedCalibrationError_bounds_dotProduct ℓ₀ (historyEventKernel ℓ₀ hap₀ events)
    (fun n ↦ historyEventPropagator (fun _ ↦ n) events)
    (hasDualMoments_historyEventKernel ℓ₀ hap₀ events) x0 deme report value

/-- **The calibration-error sandwich along a time-varying rate history.** -/
theorem expectedCalibrationError_bounds_rateHistoryKernel
    {rates : ℝ → NeutralRates Deme Locus Allele} {T : ℝ} (hT : 0 ≤ T)
    (hcontinuous : ∀ capacity : Locus → ℕ,
      ContinuousOn (fun t ↦ dualGenerator (rates t) capacity) (Set.Icc 0 T))
    (ℓ₀ : Locus) (hap₀ : FullHaplotype Locus Allele) (x0 : FrequencyState Deme Locus Allele)
    (deme : Deme) (report : FullHaplotype Locus Allele → Score × Bool) (value : Score → ℝ) :
    ∑ group, |budgetCoefficients ℓ₀ (fun _ ↦ 1)
          (demePolynomial deme (residualPolynomial report value group))
        ⬝ᵥ (rateHistoryDualPropagator rates (fun _ ↦ 1) T *ᵥ budgetMomentFeature (fun _ ↦ 1) x0)|
      ≤ expectedCalibrationError (rateHistoryKernel rates ℓ₀ hap₀ hT hcontinuous) x0 deme report
        value
    ∧ expectedCalibrationError (rateHistoryKernel rates ℓ₀ hap₀ hT hcontinuous) x0 deme report
        value
      ≤ ∑ group, Real.sqrt (budgetCoefficients ℓ₀ (fun _ ↦ 2)
          (demePolynomial deme (residualPolynomial report value group ^ 2))
        ⬝ᵥ (rateHistoryDualPropagator rates (fun _ ↦ 2) T
          *ᵥ budgetMomentFeature (fun _ ↦ 2) x0)) := by
  haveI := isMarkovKernel_rateHistoryKernel hT hcontinuous ℓ₀ hap₀
  exact expectedCalibrationError_bounds_dotProduct ℓ₀
    (rateHistoryKernel rates ℓ₀ hap₀ hT hcontinuous)
    (fun n ↦ rateHistoryDualPropagator rates (fun _ ↦ n) T)
    (hasDualMoments_rateHistoryKernel hT hcontinuous ℓ₀ hap₀) x0 deme report value

end

end Descent.Portability.EndToEndBrierLaw
