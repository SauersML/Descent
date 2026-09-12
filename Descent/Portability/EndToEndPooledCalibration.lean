/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.EndToEndCalibrationLaw
import Descent.Portability.PortabilityMasterTheorem

assert_below Descent.Decision Descent.Program

/-!
# The deployed calibration of a demographic history

`EndToEndCalibrationLaw` carries a demographic history to the calibration of expectations.  This
module joins the history to `PortabilityMasterTheorem`, whose docstring leaves the derivation of
its inputs from a demography to another layer, and separates the calibration queries a history
supports.

The pooled law.  Under a Markov kernel started at `x₀`, the expected haplotype frequencies of a
deme form a finite law (`pooledLaw`): the law of one haplotype drawn from the deme of a random
population at the end of the history.  Its expectations are the expected deme expectations
(`expectation_pooledLaw`), and its frequencies are coefficient vectors dotted with the propagated
budget-1 moments (`pooledLaw_mass_historyEventKernel`).  Two histories that agree on those moments
have one pooled law (`pooledLaw_eq_of_moments_eq`), so every metric of it agrees.

Pooled against within-population moments.  The pooled covariance is the expected
within-population covariance plus the covariance, across populations, of the deme means
(`covariance_pooledLaw`, `variance_pooledLaw`), and that between-population term is a budget-2
moment (`integral_mul_expectation_historyEventKernel`).  So the pooled calibration slope and the
slope of expectations `E C_SY / E V_S` differ exactly by the drift of the deme means.

The master theorem under a history.  A deployment recipe `P` of `PortabilityMasterTheorem` read in
the deme of one population (`replicatePopulation`) has master moments equal to the corpus metrics
of the deme law (`scoreVariance_replicatePopulation`, `predictiveCovariance_replicatePopulation`,
`outcomeVariance_replicatePopulation`, `calibrationSlope_replicatePopulation`).  Each deployed
calibration metric, weighted by the population's score variance and divided by the expected
weight, is a rational function of propagated moments of a stated budget:
* the calibration slope is the slope of expectations `E C_SY / E V_S`, budget 2
  (`expectedDeploymentSlope_eq`, `expectedDeploymentSlope_historyEventKernel`);
* the calibration intercept is `E[μ_Y V_S - C_SY μ_S] / E V_S`, budget 3
  (`expectedDeploymentIntercept_eq`, `expectedDeploymentIntercept_historyEventKernel`);
* the minimum recalibrated error `Var(Y) (1 - R²)` is `(E D - E N) / (16 E V_S)`, with `N`, `D`
  the correlation accumulators of NOTE2 (21), budget 4 (`expectedMinimumRecalibratedMse_eq`,
  `expectedMinimumRecalibratedMse_historyEventKernel`).

The deployed mean squared error needs no weights: it is linear in the law, so its expectation is
the pooled deployed error, a budget-1 moment (`integral_deployedMse_eq_pooled`,
`integral_deployedMse_historyEventKernel`).

The best fixed recalibration.  The same recipe read in the pooled law is a genuine master-theorem
population (`pooledPopulation`), so every theorem of the master theorem applies to it.  One affine
correction applied to every population has expected error equal to its pooled error
(`integral_expMse_replicatePopulation`).  So no fixed correction does better than the pooled
`Var(Y) (1 - R²)` (`integral_recalibratedMse_ge`), and the pooled calibration line attains it
(`integral_bestAffineMse_eq`).  The pooled deployment sees the history only through budget-1
moments (`pooledPopulation_eq_of_moments_eq`).

Lipschitz dependence on the rate path.  The pooled second moments are a linear readout of budget-1
moments (`momentsOf_pooledLaw_rateHistoryKernel`), and every feature reads into the unit cube
(`readout_budgetMomentFeature`).  Composing
`PortabilityMetricCompilation.abs_compiledSlope_readout_sub_le` with the propagator bound makes the
pooled calibration slope Lipschitz in the `L¹([0, T])` distance of the dual generator paths
(`abs_compiledSlope_pooledLaw_rateHistory_sub_le`).

The queries of NOTE2 §6.2.  The deployment slope, intercept and minimum recalibrated error are
ratios of expectations: the expectation of each population's accumulator over the expectation of
its score variance.  The expected deployed error is the expectation of the metric, and because the
metric is linear the two queries coincide there.  The pooled metrics are a third query, the
metrics of the expected law: the calibration a deployer fits once across the populations of a
history.

Scope.  One chromosome is sampled per individual, and the deployment recipe is a function of the
haplotype.  The expectation of the per-population slope, the expectation-of-a-ratio query of
NOTE2 §6.2, is not a rational function of finitely many moments and is not stated.  The Lipschitz
bound covers rate histories with continuous dual generators, scores and outcomes in the unit
interval, and pooled score variance at least `ε` under both histories.

## Empirical status

None.  The bodies here are integrals of polynomials against Markov kernels, finite sums and the
master theorem's identities, so no measurement can bear on them.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.EndToEndPooledCalibration

open MeasureTheory ProbabilityTheory MvPolynomial Descent.Coalescent PartialHaplotypeCarrier
  PartialHaplotypeDualGenerator PartialHaplotypeDualSemigroup NeutralFellerGenerator
  NeutralPolynomialSemigroup PartialHaplotypeMicroscopicApproximation PartialHaplotypePulseKernel
  NeutralPulseHistoryKernel NeutralRateHistoryRealization NeutralRateHistoryKernel
  ReplicaMetricInstances PortabilityMetricCompilation EndToEndPortabilityLaw
  EndToEndPortabilityLipschitz EndToEndPortabilityRateLipschitz EndToEndCalibrationLaw
open scoped Matrix NNReal Matrix.Norms.Operator

noncomputable section

variable {Deme Locus : Type*} {Allele : Locus → Type*}
variable [Fintype Deme] [DecidableEq Deme] [Fintype Locus] [DecidableEq Locus]
  [∀ ℓ, Fintype (Allele ℓ)] [∀ ℓ, DecidableEq (Allele ℓ)]

attribute [local instance] isMarkovKernel_historyEventKernel isMarkovKernel_rateHistoryKernel

/-! ## The pooled haplotype law -/

/-- The frequency of one haplotype in one deme is continuous in the state. -/
theorem continuous_stateLaw_mass (deme : Deme) (hap : FullHaplotype Locus Allele) :
    Continuous fun y : FrequencyState Deme Locus Allele ↦ (stateLaw y deme).mass hap := by
  have hcoordinate : Continuous fun y : FrequencyState Deme Locus Allele ↦ y.1 (deme, hap) :=
    continuous_pi_iff.mp continuous_subtype_val (deme, hap)
  exact hcoordinate

/-- The mean of a haplotype observable in one deme is continuous in the state. -/
theorem continuous_expectation_stateLaw (deme : Deme) (value : FullHaplotype Locus Allele → ℝ) :
    Continuous fun y : FrequencyState Deme Locus Allele ↦ (stateLaw y deme).expectation value :=
  (polynomialFunction (demeMeanPolynomial deme value)).continuous.congr
    (polynomialFunction_demeMeanPolynomial deme value)

/-- A continuous observable of the state is integrable under every Markov kernel. -/
theorem integrable_of_continuous
    (κ : Kernel (FrequencyState Deme Locus Allele) (FrequencyState Deme Locus Allele))
    [IsMarkovKernel κ] (x0 : FrequencyState Deme Locus Allele)
    {g : FrequencyState Deme Locus Allele → ℝ} (hg : Continuous g) : Integrable g (κ x0) :=
  (BoundedContinuousFunction.mkOfCompact ⟨g, hg⟩).integrable _

/-- The frequency of one haplotype in one deme is integrable under every Markov kernel. -/
theorem integrable_stateLaw_mass
    (κ : Kernel (FrequencyState Deme Locus Allele) (FrequencyState Deme Locus Allele))
    [IsMarkovKernel κ] (x0 : FrequencyState Deme Locus Allele) (deme : Deme)
    (hap : FullHaplotype Locus Allele) :
    Integrable (fun y ↦ (stateLaw y deme).mass hap) (κ x0) :=
  integrable_of_continuous κ x0 (continuous_stateLaw_mass deme hap)

/-- The expected haplotype frequencies of a deme sum to one. -/
theorem sum_integral_stateLaw_mass
    (κ : Kernel (FrequencyState Deme Locus Allele) (FrequencyState Deme Locus Allele))
    [IsMarkovKernel κ] (x0 : FrequencyState Deme Locus Allele) (deme : Deme) :
    ∑ hap, ∫ y, (stateLaw y deme).mass hap ∂(κ x0) = 1 := by
  rw [← integral_finset_sum Finset.univ fun hap _ ↦ integrable_stateLaw_mass κ x0 deme hap]
  simp only [FiniteReportLaw.mass_sum, integral_const, measureReal_univ_eq_one, smul_eq_mul,
    mul_one]

/-- **The pooled haplotype law** of a deme under a Markov kernel started at `x₀`: the expected
haplotype frequencies, the law of one haplotype drawn from the deme of a random population at the
end of the history. -/
def pooledLaw (κ : Kernel (FrequencyState Deme Locus Allele) (FrequencyState Deme Locus Allele))
    [IsMarkovKernel κ] (x0 : FrequencyState Deme Locus Allele) (deme : Deme) :
    FiniteReportLaw (FullHaplotype Locus Allele) where
  mass hap := ∫ y, (stateLaw y deme).mass hap ∂(κ x0)
  mass_nonneg hap := integral_nonneg fun y ↦ (stateLaw y deme).mass_nonneg hap
  mass_sum := sum_integral_stateLaw_mass κ x0 deme

/-- **The pooled law averages the deme laws.**  Every expectation under the pooled law is the
expected expectation under the deme's haplotype law. -/
theorem expectation_pooledLaw
    (κ : Kernel (FrequencyState Deme Locus Allele) (FrequencyState Deme Locus Allele))
    [IsMarkovKernel κ] (x0 : FrequencyState Deme Locus Allele) (deme : Deme)
    (value : FullHaplotype Locus Allele → ℝ) :
    (pooledLaw κ x0 deme).expectation value
      = ∫ y, (stateLaw y deme).expectation value ∂(κ x0) := by
  show ∑ hap, (∫ y, (stateLaw y deme).mass hap ∂(κ x0)) * value hap
    = ∫ y, ∑ hap, (stateLaw y deme).mass hap * value hap ∂(κ x0)
  rw [integral_finset_sum Finset.univ fun hap _ ↦
    (integrable_stateLaw_mass κ x0 deme hap).mul_const (value hap)]
  exact Finset.sum_congr rfl fun hap _ ↦ (integral_mul_const (value hap) _).symm

/-! ## The pooled law through the moments -/

/-- The frequency of one haplotype in one deme, as a frequency polynomial. -/
theorem polynomialFunction_demePolynomial_X (deme : Deme) (hap : FullHaplotype Locus Allele)
    (y : FrequencyState Deme Locus Allele) :
    polynomialFunction (demePolynomial deme (X hap)) y = (stateLaw y deme).mass hap := by
  rw [polynomialFunction_apply, eval_demePolynomial, eval_X]

/-- The haplotype frequency polynomial has total degree at most one. -/
theorem totalDegree_demePolynomial_X_le (deme : Deme) (hap : FullHaplotype Locus Allele) :
    (demePolynomial deme (X hap : MvPolynomial (FullHaplotype Locus Allele) ℝ)).totalDegree
      ≤ 1 :=
  (totalDegree_rename_le _ _).trans_eq (totalDegree_X hap)

/-- **The pooled law along a history.**  For every budget `n ≥ 1`, each pooled haplotype frequency
of a deme is a coefficient vector dotted with the chronological propagator applied to the
budget-`n` moments of the initial state. -/
theorem pooledLaw_mass_historyEventKernel (ℓ₀ : Locus) (hap₀ : FullHaplotype Locus Allele)
    (events : List ((NeutralRates Deme Locus Allele × ℝ≥0) ⊕ PulseMatrix Deme)) {n : ℕ}
    (hn : 1 ≤ n) (x0 : FrequencyState Deme Locus Allele) (deme : Deme)
    (hap : FullHaplotype Locus Allele) :
    (pooledLaw (historyEventKernel ℓ₀ hap₀ events) x0 deme).mass hap
      = budgetCoefficients ℓ₀ (fun _ ↦ n) (demePolynomial deme (X hap))
        ⬝ᵥ (historyEventPropagator (fun _ ↦ n) events *ᵥ budgetMomentFeature (fun _ ↦ n) x0) :=
  integral_eq_dotProduct_of_totalDegree_le ℓ₀ (historyEventKernel ℓ₀ hap₀ events) _
    (integral_momentPolynomial_historyEventKernel ℓ₀ hap₀ (fun _ ↦ n) events) _
    ((totalDegree_demePolynomial_X_le deme hap).trans hn) _
    (polynomialFunction_demePolynomial_X deme hap) x0

/-- **The pooled law sees the history only through budget-1 moments.**  Two histories, from two
initial states, whose propagated budget-1 moments agree have the same pooled law in every deme, so
every metric of the pooled law agrees. -/
theorem pooledLaw_eq_of_moments_eq (ℓ₀ : Locus) (hap₀ : FullHaplotype Locus Allele)
    {first second : List ((NeutralRates Deme Locus Allele × ℝ≥0) ⊕ PulseMatrix Deme)}
    {x₁ x₂ : FrequencyState Deme Locus Allele}
    (hmoments : historyEventPropagator (fun _ ↦ 1) first *ᵥ budgetMomentFeature (fun _ ↦ 1) x₁
      = historyEventPropagator (fun _ ↦ 1) second *ᵥ budgetMomentFeature (fun _ ↦ 1) x₂)
    (deme : Deme) :
    pooledLaw (historyEventKernel ℓ₀ hap₀ first) x₁ deme
      = pooledLaw (historyEventKernel ℓ₀ hap₀ second) x₂ deme := by
  ext hap
  rw [pooledLaw_mass_historyEventKernel ℓ₀ hap₀ first le_rfl x₁ deme hap,
    pooledLaw_mass_historyEventKernel ℓ₀ hap₀ second le_rfl x₂ deme hap, hmoments]

/-! ## Pooled against within-population calibration moments -/

/-- **The law of total covariance along a history.**  The pooled covariance of two observables is
the expected within-population covariance plus the covariance, across populations, of the deme
means. -/
theorem covariance_pooledLaw
    (κ : Kernel (FrequencyState Deme Locus Allele) (FrequencyState Deme Locus Allele))
    [IsMarkovKernel κ] (x0 : FrequencyState Deme Locus Allele) (deme : Deme)
    (first second : FullHaplotype Locus Allele → ℝ) :
    (pooledLaw κ x0 deme).covariance first second
      = (∫ y, (stateLaw y deme).covariance first second ∂(κ x0))
        + ((∫ y, (stateLaw y deme).expectation first * (stateLaw y deme).expectation second
            ∂(κ x0))
          - (∫ y, (stateLaw y deme).expectation first ∂(κ x0))
            * ∫ y, (stateLaw y deme).expectation second ∂(κ x0)) := by
  have hwithin : (∫ y, (stateLaw y deme).covariance first second ∂(κ x0))
      = (∫ y, (stateLaw y deme).expectation (fun hap ↦ first hap * second hap) ∂(κ x0))
        - ∫ y, (stateLaw y deme).expectation first * (stateLaw y deme).expectation second
          ∂(κ x0) := by
    simp only [FiniteReportLaw.covariance_eq_rawMoments]
    exact integral_sub (integrable_of_continuous κ x0 (continuous_expectation_stateLaw deme _))
      (integrable_of_continuous κ x0 ((continuous_expectation_stateLaw deme first).mul
        (continuous_expectation_stateLaw deme second)))
  rw [FiniteReportLaw.covariance_eq_rawMoments, expectation_pooledLaw, expectation_pooledLaw,
    expectation_pooledLaw, hwithin]
  ring

/-- **The law of total variance along a history.**  The pooled variance of an observable is the
expected within-population variance plus the variance, across populations, of the deme mean. -/
theorem variance_pooledLaw
    (κ : Kernel (FrequencyState Deme Locus Allele) (FrequencyState Deme Locus Allele))
    [IsMarkovKernel κ] (x0 : FrequencyState Deme Locus Allele) (deme : Deme)
    (value : FullHaplotype Locus Allele → ℝ) :
    (pooledLaw κ x0 deme).variance value
      = (∫ y, (stateLaw y deme).variance value ∂(κ x0))
        + ((∫ y, (stateLaw y deme).expectation value * (stateLaw y deme).expectation value
            ∂(κ x0))
          - (∫ y, (stateLaw y deme).expectation value ∂(κ x0))
            * ∫ y, (stateLaw y deme).expectation value ∂(κ x0)) :=
  covariance_pooledLaw κ x0 deme value value

/-- The product of two deme means, as a frequency polynomial. -/
theorem polynomialFunction_meanProduct (deme : Deme)
    (first second : FullHaplotype Locus Allele → ℝ) (y : FrequencyState Deme Locus Allele) :
    polynomialFunction (demeMeanPolynomial deme first * demeMeanPolynomial deme second) y
      = (stateLaw y deme).expectation first * (stateLaw y deme).expectation second := by
  rw [polynomialFunction_apply, map_mul, ← polynomialFunction_apply, ← polynomialFunction_apply,
    polynomialFunction_demeMeanPolynomial, polynomialFunction_demeMeanPolynomial]

/-- The product of two mean polynomials has total degree at most two. -/
theorem totalDegree_meanProduct_le (deme : Deme) (first second : FullHaplotype Locus Allele → ℝ) :
    (demeMeanPolynomial deme first * demeMeanPolynomial deme second).totalDegree ≤ 2 := by
  have hfirst := totalDegree_demeMeanPolynomial_le deme first
  have hsecond := totalDegree_demeMeanPolynomial_le deme second
  exact (totalDegree_mul _ _).trans (by omega)

/-- **The between-population term along a history** is a budget-2 moment: for every budget
`n ≥ 2`, the expected product of two deme means is a coefficient vector dotted with the
chronological propagator applied to the budget-`n` moments of the initial state. -/
theorem integral_mul_expectation_historyEventKernel (ℓ₀ : Locus)
    (hap₀ : FullHaplotype Locus Allele)
    (events : List ((NeutralRates Deme Locus Allele × ℝ≥0) ⊕ PulseMatrix Deme)) {n : ℕ}
    (hn : 2 ≤ n) (x0 : FrequencyState Deme Locus Allele) (deme : Deme)
    (first second : FullHaplotype Locus Allele → ℝ) :
    ∫ y, (stateLaw y deme).expectation first * (stateLaw y deme).expectation second
        ∂(historyEventKernel ℓ₀ hap₀ events x0)
      = budgetCoefficients ℓ₀ (fun _ ↦ n)
          (demeMeanPolynomial deme first * demeMeanPolynomial deme second)
        ⬝ᵥ (historyEventPropagator (fun _ ↦ n) events *ᵥ budgetMomentFeature (fun _ ↦ n) x0) :=
  integral_eq_dotProduct_of_totalDegree_le ℓ₀ (historyEventKernel ℓ₀ hap₀ events) _
    (integral_momentPolynomial_historyEventKernel ℓ₀ hap₀ (fun _ ↦ n) events) _
    ((totalDegree_meanProduct_le deme first second).trans hn) _
    (polynomialFunction_meanProduct deme first second) x0

/-! ## The pooled calibration slope is Lipschitz in the rate history -/

/-- The five observables whose expectations are the second-moment coordinates
`(E S, E Y, E S², E S Y, E Y²)`. -/
def secondMomentObservables {Ω : Type*} (score outcome : Ω → ℝ) : Fin 5 → Ω → ℝ :=
  ![score, outcome, fun ω ↦ score ω ^ 2, fun ω ↦ score ω * outcome ω, fun ω ↦ outcome ω ^ 2]

/-- The second-moment coordinates of a finite law are the expectations of the five second-moment
observables. -/
theorem momentsOf_apply {Ω : Type*} [Fintype Ω] (p : FiniteReportLaw Ω) (score outcome : Ω → ℝ)
    (c : Fin 5) :
    momentsOf p score outcome c = p.expectation (secondMomentObservables score outcome c) := by
  fin_cases c <;> rfl

/-- The coefficient matrix reading the pooled second-moment coordinates off budget-1 moments. -/
def pooledReadout (ℓ₀ : Locus) (deme : Deme) (score outcome : FullHaplotype Locus Allele → ℝ) :
    Fin 5 → BudgetConfiguration Deme Locus Allele (fun _ ↦ 1) → ℝ :=
  fun c ↦ budgetCoefficients ℓ₀ (fun _ ↦ 1)
    (demeMeanPolynomial deme (secondMomentObservables score outcome c))

/-- **The pooled second moments along a rate history are a readout of budget-1 moments.** -/
theorem momentsOf_pooledLaw_rateHistoryKernel {rates : ℝ → NeutralRates Deme Locus Allele}
    {T : ℝ} (hT : 0 ≤ T)
    (hcontinuous : ∀ capacity : Locus → ℕ,
      ContinuousOn (fun t ↦ dualGenerator (rates t) capacity) (Set.Icc 0 T))
    (ℓ₀ : Locus) (hap₀ : FullHaplotype Locus Allele) (x0 : FrequencyState Deme Locus Allele)
    (deme : Deme) (score outcome : FullHaplotype Locus Allele → ℝ) :
    momentsOf (pooledLaw (rateHistoryKernel rates ℓ₀ hap₀ hT hcontinuous) x0 deme) score outcome
      = readout (pooledReadout ℓ₀ deme score outcome)
          (rateHistoryDualPropagator rates (fun _ ↦ 1) T
            *ᵥ budgetMomentFeature (fun _ ↦ 1) x0) := by
  funext c
  rw [momentsOf_apply, expectation_pooledLaw,
    integral_expectation_rateHistoryKernel hT hcontinuous ℓ₀ hap₀ le_rfl x0 deme]
  rfl

/-- Every configuration-moment feature reads into the pooled coordinates of the state's own deme
law. -/
theorem readout_budgetMomentFeature (ℓ₀ : Locus) (deme : Deme)
    (score outcome : FullHaplotype Locus Allele → ℝ) (x : FrequencyState Deme Locus Allele)
    (c : Fin 5) :
    readout (pooledReadout ℓ₀ deme score outcome) (budgetMomentFeature (fun _ ↦ 1) x) c
      = (stateLaw x deme).expectation (secondMomentObservables score outcome c) := by
  rw [← polynomialFunction_demeMeanPolynomial, polynomialFunction_apply,
    eval_eq_dotProduct ℓ₀ (fun _ ↦ 1) _
      (withinBudget_of_totalDegree_le ℓ₀ _ (totalDegree_demeMeanPolynomial_le deme _)) x]
  rfl

/-- The expectation of the constant observable one is one. -/
theorem expectation_one_observable {Ω : Type*} [Fintype Ω] (p : FiniteReportLaw Ω) :
    p.expectation (fun _ ↦ (1 : ℝ)) = 1 := by
  simp only [FiniteReportLaw.expectation, mul_one, p.mass_sum]

/-- The expectation of an observable in the unit interval lies in the unit interval. -/
theorem expectation_mem_unitInterval {Ω : Type*} [Fintype Ω] (p : FiniteReportLaw Ω)
    (value : Ω → ℝ) (hvalue : ∀ ω, 0 ≤ value ω ∧ value ω ≤ 1) :
    0 ≤ p.expectation value ∧ p.expectation value ≤ 1 :=
  ⟨Finset.sum_nonneg fun ω _ ↦ mul_nonneg (p.mass_nonneg ω) (hvalue ω).1,
    (BellmanReportBounds.expectation_mono p value _ fun ω ↦ (hvalue ω).2).trans_eq
      (expectation_one_observable p)⟩

/-- The five second-moment observables of a score and an outcome in the unit interval lie in the
unit interval. -/
theorem secondMomentObservables_mem_unitInterval {Ω : Type*} (score outcome : Ω → ℝ)
    (hscore : ∀ ω, 0 ≤ score ω ∧ score ω ≤ 1) (houtcome : ∀ ω, 0 ≤ outcome ω ∧ outcome ω ≤ 1)
    (c : Fin 5) (ω : Ω) :
    0 ≤ secondMomentObservables score outcome c ω
      ∧ secondMomentObservables score outcome c ω ≤ 1 := by
  obtain ⟨hs0, hs1⟩ := hscore ω
  obtain ⟨ho0, ho1⟩ := houtcome ω
  fin_cases c
  · exact ⟨hs0, hs1⟩
  · exact ⟨ho0, ho1⟩
  · exact ⟨sq_nonneg _, pow_le_one₀ hs0 hs1⟩
  · exact ⟨mul_nonneg hs0 ho0, mul_le_one₀ hs1 ho0 ho1⟩
  · exact ⟨sq_nonneg _, pow_le_one₀ ho0 ho1⟩

/-- The `ℓ¹` distance of two vectors is at most the number of coordinates times their sup
distance. -/
theorem sum_abs_sub_le_card_mul_norm {ι : Type*} [Fintype ι] (v w : ι → ℝ) :
    ∑ i, |v i - w i| ≤ Fintype.card ι * ‖v - w‖ := by
  have hsum := Finset.sum_le_card_nsmul Finset.univ (fun i ↦ |v i - w i|) ‖v - w‖ fun i _ ↦ by
    have hcoordinate := norm_le_pi_norm (v - w) i
    rwa [Real.norm_eq_abs, Pi.sub_apply] at hcoordinate
  rwa [Finset.card_univ, nsmul_eq_mul] at hsum

/-- The propagated moments of two rate histories differ by at most the propagator bound times the
feature bound. -/
theorem norm_rateHistoryPropagated_sub_le {first second : ℝ → NeutralRates Deme Locus Allele}
    {T : ℝ} (hT : 0 ≤ T)
    (hfirst : ∀ capacity : Locus → ℕ,
      ContinuousOn (fun t ↦ dualGenerator (first t) capacity) (Set.Icc 0 T))
    (hsecond : ∀ capacity : Locus → ℕ,
      ContinuousOn (fun t ↦ dualGenerator (second t) capacity) (Set.Icc 0 T))
    (capacity : Locus → ℕ) (x0 : FrequencyState Deme Locus Allele) :
    ‖rateHistoryDualPropagator first capacity T *ᵥ budgetMomentFeature capacity x0
        - rateHistoryDualPropagator second capacity T *ᵥ budgetMomentFeature capacity x0‖
      ≤ (∫ s in (0 : ℝ)..T, ‖dualGeneratorPath first capacity T s
            - dualGeneratorPath second capacity T s‖)
          * Real.exp (∫ s in (0 : ℝ)..T, ‖dualGeneratorPath first capacity T s‖)
          * Real.exp (∫ s in (0 : ℝ)..T, ‖dualGeneratorPath second capacity T s‖)
        * featureBound (first 0) capacity :=
  (norm_propagated_sub_le (first 0) capacity _ _ x0).trans
    (mul_le_mul_of_nonneg_right
      (norm_rateHistoryDualPropagator_sub_le hT (hfirst capacity) (hsecond capacity))
      (featureBound_nonneg (first 0) capacity))

/-- **The pooled calibration slope is Lipschitz in the rate path.**  For two rate histories with
continuous dual generators, a score and an outcome in the unit interval, and pooled score variance
at least `ε > 0` under both, the compiled calibration slope of the pooled law moves by at most
`3/ε² · 5a` times the number of budget-1 configurations times the propagator bound times the
feature bound, where `a` is the coefficient mass of the pooled readout. -/
theorem abs_compiledSlope_pooledLaw_rateHistory_sub_le
    {first second : ℝ → NeutralRates Deme Locus Allele} {T : ℝ} (hT : 0 ≤ T)
    (hfirst : ∀ capacity : Locus → ℕ,
      ContinuousOn (fun t ↦ dualGenerator (first t) capacity) (Set.Icc 0 T))
    (hsecond : ∀ capacity : Locus → ℕ,
      ContinuousOn (fun t ↦ dualGenerator (second t) capacity) (Set.Icc 0 T))
    (ℓ₀ : Locus) (hap₀ : FullHaplotype Locus Allele) (x0 : FrequencyState Deme Locus Allele)
    (deme : Deme) (score outcome : FullHaplotype Locus Allele → ℝ)
    (hscore : ∀ hap, 0 ≤ score hap ∧ score hap ≤ 1)
    (houtcome : ∀ hap, 0 ≤ outcome hap ∧ outcome hap ≤ 1) {ε : ℝ} (hε : 0 < ε)
    (hvariance₁ : ε ≤ scoreVariance
      (momentsOf (pooledLaw (rateHistoryKernel first ℓ₀ hap₀ hT hfirst) x0 deme) score outcome))
    (hvariance₂ : ε ≤ scoreVariance
      (momentsOf (pooledLaw (rateHistoryKernel second ℓ₀ hap₀ hT hsecond) x0 deme) score
        outcome)) :
    |compiledSlope
        (momentsOf (pooledLaw (rateHistoryKernel first ℓ₀ hap₀ hT hfirst) x0 deme) score outcome)
      - compiledSlope
        (momentsOf (pooledLaw (rateHistoryKernel second ℓ₀ hap₀ hT hsecond) x0 deme) score
          outcome)|
      ≤ 3 / ε ^ 2 * (5 * (∑ c, ∑ i, |pooledReadout ℓ₀ deme score outcome c i|)
        * (Fintype.card (BudgetConfiguration Deme Locus Allele (fun _ ↦ 1))
          * ((∫ s in (0 : ℝ)..T, ‖dualGeneratorPath first (fun _ ↦ 1) T s
                - dualGeneratorPath second (fun _ ↦ 1) T s‖)
              * Real.exp (∫ s in (0 : ℝ)..T, ‖dualGeneratorPath first (fun _ ↦ 1) T s‖)
              * Real.exp (∫ s in (0 : ℝ)..T, ‖dualGeneratorPath second (fun _ ↦ 1) T s‖)
            * featureBound (first 0) (fun _ ↦ 1)))) := by
  have hfeature : ∀ (x : FrequencyState Deme Locus Allele) (c : Fin 5),
      0 ≤ readout (pooledReadout ℓ₀ deme score outcome) (budgetMomentFeature (fun _ ↦ 1) x) c
        ∧ readout (pooledReadout ℓ₀ deme score outcome) (budgetMomentFeature (fun _ ↦ 1) x) c
          ≤ 1 := by
    intro x c
    rw [readout_budgetMomentFeature]
    exact expectation_mem_unitInterval _ _ fun hap ↦
      secondMomentObservables_mem_unitInterval score outcome hscore houtcome c hap
  have hcoefficient : ∀ c i, |pooledReadout ℓ₀ deme score outcome c i|
      ≤ ∑ d, ∑ j, |pooledReadout ℓ₀ deme score outcome d j| := fun c i ↦
    (Finset.single_le_sum (fun j _ ↦ abs_nonneg (pooledReadout ℓ₀ deme score outcome c j))
      (Finset.mem_univ i)).trans
      (Finset.single_le_sum (fun d _ ↦ Finset.sum_nonneg fun j _ ↦
        abs_nonneg (pooledReadout ℓ₀ deme score outcome d j)) (Finset.mem_univ c))
  rw [momentsOf_pooledLaw_rateHistoryKernel hT hfirst ℓ₀ hap₀ x0 deme score
    outcome] at hvariance₁ ⊢
  rw [momentsOf_pooledLaw_rateHistoryKernel hT hsecond ℓ₀ hap₀ x0 deme score
    outcome] at hvariance₂ ⊢
  refine le_trans (abs_compiledSlope_readout_sub_le
    (budgetMomentFeature (Deme := Deme) (Locus := Locus) (Allele := Allele) (fun _ ↦ 1))
    (pooledReadout ℓ₀ deme score outcome) hε hcoefficient hfeature
    (rateHistoryDualPropagator_mulVec_mem_realizationBody hT (hfirst _) x0)
    (rateHistoryDualPropagator_mulVec_mem_realizationBody hT (hsecond _) x0)
    hvariance₁ hvariance₂) ?_
  refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ ?_) (by positivity)
  · exact (sum_abs_sub_le_card_mul_norm _ _).trans
      (mul_le_mul_of_nonneg_left (norm_rateHistoryPropagated_sub_le hT hfirst hsecond _ x0)
        (Nat.cast_nonneg _))
  · exact mul_nonneg (by norm_num) (Finset.sum_nonneg fun d _ ↦
      Finset.sum_nonneg fun j _ ↦ abs_nonneg _)

/-! ## Deployment metrics of one population -/

/-- The expectation functional of a finite law: the master theorem's `weightedExp` of its
masses. -/
def lawExpectation {Ω : Type*} [Fintype Ω] (p : FiniteReportLaw Ω) :
    Foundations.ExpFunctional Ω :=
  weightedExp p.mass p.mass_nonneg p.mass_sum

/-- The score variance times the corpus residual variance `V_Y (1 - C² / (V_S V_Y))` is
`(D - N) / 16`, with `N` and `D` the correlation accumulators of NOTE2 (21). -/
theorem variance_mul_residual {Ω : Type*} [Fintype Ω] (law : FiniteReportLaw Ω)
    (score outcome : Ω → ℝ) :
    law.variance score * (law.variance outcome
        * (1 - law.covariance score outcome ^ 2 / (law.variance score * law.variance outcome)))
      = (correlationDenominator law score outcome - correlationNumerator law score outcome)
        / 16 := by
  unfold correlationDenominator correlationNumerator
  by_cases hproduct : law.variance score * law.variance outcome = 0
  · have hcauchy := law.covariance_sq_le_variance_mul score outcome
    rw [hproduct] at hcauchy
    have hsquare : law.covariance score outcome ^ 2 = 0 := le_antisymm hcauchy (sq_nonneg _)
    rw [hsquare, zero_div, sub_zero, mul_one, hproduct]
    norm_num
  · have hcancel : law.variance score * law.variance outcome
        * (law.covariance score outcome ^ 2 / (law.variance score * law.variance outcome))
        = law.covariance score outcome ^ 2 := mul_div_cancel₀ _ hproduct
    linear_combination -hcancel

section Master

variable {J L : Type*} [Fintype J] [DecidableEq J] [Fintype L] [DecidableEq L]

/-- **A deployment recipe read in one population**: the recipe's scored codings, causal codings,
effects and residual, with the haplotype law of the deme at state `y` as its expectation.  The
recipe's own expectation is not used. -/
def replicatePopulation (P : DeploymentPopulation (FullHaplotype Locus Allele) J L)
    (y : FrequencyState Deme Locus Allele) (deme : Deme) :
    DeploymentPopulation (FullHaplotype Locus Allele) J L :=
  { P with E := lawExpectation (stateLaw y deme) }

/-- **A deployment recipe read in the pooled law** of a deme under a Markov kernel.  The
recipe's own expectation is not used. -/
def pooledPopulation (P : DeploymentPopulation (FullHaplotype Locus Allele) J L)
    (κ : Kernel (FrequencyState Deme Locus Allele) (FrequencyState Deme Locus Allele))
    [IsMarkovKernel κ] (x0 : FrequencyState Deme Locus Allele) (deme : Deme) :
    DeploymentPopulation (FullHaplotype Locus Allele) J L :=
  { P with E := lawExpectation (pooledLaw κ x0 deme) }

/-- The master score variance of a recipe read in one population is the corpus score variance of
the deme law. -/
theorem scoreVariance_replicatePopulation
    (P : DeploymentPopulation (FullHaplotype Locus Allele) J L)
    (y : FrequencyState Deme Locus Allele) (deme : Deme) (w : J → ℝ) :
    (replicatePopulation P y deme).scoreVariance w = (stateLaw y deme).variance (P.score w) := by
  unfold DeploymentPopulation.scoreVariance
  rw [Foundations.variance_eq_covariance_self]
  rfl

/-- The master predictive covariance of a recipe read in one population is the corpus covariance
of the deployed score and phenotype under the deme law. -/
theorem predictiveCovariance_replicatePopulation
    (P : DeploymentPopulation (FullHaplotype Locus Allele) J L)
    (y : FrequencyState Deme Locus Allele) (deme : Deme) (w : J → ℝ) :
    (replicatePopulation P y deme).predictiveCovariance w
      = (stateLaw y deme).covariance (P.score w) P.phenotype :=
  rfl

/-- The master outcome variance of a recipe read in one population is the corpus variance of the
phenotype under the deme law. -/
theorem outcomeVariance_replicatePopulation
    (P : DeploymentPopulation (FullHaplotype Locus Allele) J L)
    (y : FrequencyState Deme Locus Allele) (deme : Deme) :
    (replicatePopulation P y deme).outcomeVariance = (stateLaw y deme).variance P.phenotype := by
  unfold DeploymentPopulation.outcomeVariance
  rw [Foundations.variance_eq_covariance_self]
  rfl

/-- The master calibration slope of a recipe read in one population is the corpus calibration
slope of the deme law, read as zero where it is undefined. -/
theorem calibrationSlope_replicatePopulation
    (P : DeploymentPopulation (FullHaplotype Locus Allele) J L)
    (y : FrequencyState Deme Locus Allele) (deme : Deme) (w : J → ℝ) :
    (replicatePopulation P y deme).calibrationSlope w
      = ((stateLaw y deme).calibrationSlope (P.score w) P.phenotype).getD 0 := by
  rw [DeploymentPopulation.calibrationSlope, predictiveCovariance_replicatePopulation,
    scoreVariance_replicatePopulation]
  unfold FiniteReportLaw.calibrationSlope
  split_ifs with hpositive
  · rfl
  · exact div_eq_zero_iff.mpr
      (Or.inr (le_antisymm (not_lt.mp hpositive) ((stateLaw y deme).variance_nonneg _)))

/-- In one population, the master score variance times the master calibration slope is the
corpus covariance of the deployed score and phenotype. -/
theorem scoreVariance_mul_calibrationSlope_replicatePopulation
    (P : DeploymentPopulation (FullHaplotype Locus Allele) J L)
    (y : FrequencyState Deme Locus Allele) (deme : Deme) (w : J → ℝ) :
    (replicatePopulation P y deme).scoreVariance w
        * (replicatePopulation P y deme).calibrationSlope w
      = (stateLaw y deme).covariance (P.score w) P.phenotype := by
  rw [calibrationSlope_replicatePopulation, scoreVariance_replicatePopulation]
  exact variance_mul_getD_calibrationSlope (stateLaw y deme) (P.score w) P.phenotype

/-- In one population, the master score variance times the master calibration intercept is the
intercept accumulator `μ_Y V_S - C_SY μ_S`. -/
theorem scoreVariance_mul_calibrationIntercept_replicatePopulation
    (P : DeploymentPopulation (FullHaplotype Locus Allele) J L)
    (y : FrequencyState Deme Locus Allele) (deme : Deme) (w : J → ℝ) :
    (replicatePopulation P y deme).scoreVariance w
        * (replicatePopulation P y deme).calibrationIntercept w
      = (stateLaw y deme).expectation P.phenotype * (stateLaw y deme).variance (P.score w)
        - (stateLaw y deme).covariance (P.score w) P.phenotype
          * (stateLaw y deme).expectation (P.score w) := by
  rw [DeploymentPopulation.calibrationIntercept, calibrationSlope_replicatePopulation,
    scoreVariance_replicatePopulation]
  exact variance_mul_intercept (stateLaw y deme) (P.score w) P.phenotype

/-- In one population, the master score variance times the minimum recalibrated error
`Var(Y) (1 - R²)` is `(D - N) / 16`. -/
theorem scoreVariance_mul_minimumRecalibratedMse_replicatePopulation
    (P : DeploymentPopulation (FullHaplotype Locus Allele) J L)
    (y : FrequencyState Deme Locus Allele) (deme : Deme) (w : J → ℝ) :
    (replicatePopulation P y deme).scoreVariance w
        * ((replicatePopulation P y deme).outcomeVariance
          * (1 - (replicatePopulation P y deme).r2 w))
      = (correlationDenominator (stateLaw y deme) (P.score w) P.phenotype
          - correlationNumerator (stateLaw y deme) (P.score w) P.phenotype) / 16 := by
  rw [DeploymentPopulation.r2, predictiveCovariance_replicatePopulation,
    scoreVariance_replicatePopulation, outcomeVariance_replicatePopulation]
  exact variance_mul_residual (stateLaw y deme) (P.score w) P.phenotype

/-! ## The deployed calibration of a history -/

/-- **The deployed calibration slope in ratio-of-expectations form**: the master calibration slope
of each population weighted by its score variance, over the expected weight.  NOTE2 §6.2 query: a
ratio of expectations. -/
def expectedDeploymentSlope (P : DeploymentPopulation (FullHaplotype Locus Allele) J L)
    (κ : Kernel (FrequencyState Deme Locus Allele) (FrequencyState Deme Locus Allele))
    (x0 : FrequencyState Deme Locus Allele) (deme : Deme) (w : J → ℝ) : ℝ :=
  (∫ y, (replicatePopulation P y deme).scoreVariance w
      * (replicatePopulation P y deme).calibrationSlope w ∂(κ x0))
    / ∫ y, (replicatePopulation P y deme).scoreVariance w ∂(κ x0)

/-- **The deployed calibration intercept in ratio-of-expectations form**: the master calibration
intercept of each population weighted by its score variance, over the expected weight.  NOTE2
§6.2 query: a ratio of expectations. -/
def expectedDeploymentIntercept (P : DeploymentPopulation (FullHaplotype Locus Allele) J L)
    (κ : Kernel (FrequencyState Deme Locus Allele) (FrequencyState Deme Locus Allele))
    (x0 : FrequencyState Deme Locus Allele) (deme : Deme) (w : J → ℝ) : ℝ :=
  (∫ y, (replicatePopulation P y deme).scoreVariance w
      * (replicatePopulation P y deme).calibrationIntercept w ∂(κ x0))
    / ∫ y, (replicatePopulation P y deme).scoreVariance w ∂(κ x0)

/-- **The minimum recalibrated error in ratio-of-expectations form**: the master error
`Var(Y) (1 - R²)` of the best affine correction of each population, weighted by its score
variance, over the expected weight.  NOTE2 §6.2 query: a ratio of expectations. -/
def expectedMinimumRecalibratedMse (P : DeploymentPopulation (FullHaplotype Locus Allele) J L)
    (κ : Kernel (FrequencyState Deme Locus Allele) (FrequencyState Deme Locus Allele))
    (x0 : FrequencyState Deme Locus Allele) (deme : Deme) (w : J → ℝ) : ℝ :=
  (∫ y, (replicatePopulation P y deme).scoreVariance w
      * ((replicatePopulation P y deme).outcomeVariance
        * (1 - (replicatePopulation P y deme).r2 w)) ∂(κ x0))
    / ∫ y, (replicatePopulation P y deme).scoreVariance w ∂(κ x0)

/-- **The deployed slope is the calibration slope of expectations** of the deployed score and
phenotype, `E C_SY / E V_S`. -/
theorem expectedDeploymentSlope_eq (P : DeploymentPopulation (FullHaplotype Locus Allele) J L)
    (κ : Kernel (FrequencyState Deme Locus Allele) (FrequencyState Deme Locus Allele))
    (x0 : FrequencyState Deme Locus Allele) (deme : Deme) (w : J → ℝ) :
    expectedDeploymentSlope P κ x0 deme w
      = expectedCalibrationSlope κ x0 deme (P.score w) P.phenotype := by
  simp only [expectedDeploymentSlope, expectedCalibrationSlope,
    scoreVariance_mul_calibrationSlope_replicatePopulation]
  simp only [scoreVariance_replicatePopulation]

/-- **The deployed intercept is the calibration intercept of expectations** of the deployed score
and phenotype, `E[μ_Y V_S - C_SY μ_S] / E V_S`. -/
theorem expectedDeploymentIntercept_eq
    (P : DeploymentPopulation (FullHaplotype Locus Allele) J L)
    (κ : Kernel (FrequencyState Deme Locus Allele) (FrequencyState Deme Locus Allele))
    (x0 : FrequencyState Deme Locus Allele) (deme : Deme) (w : J → ℝ) :
    expectedDeploymentIntercept P κ x0 deme w
      = expectedCalibrationIntercept κ x0 deme (P.score w) P.phenotype := by
  simp only [expectedDeploymentIntercept, expectedCalibrationIntercept,
    scoreVariance_mul_calibrationIntercept_replicatePopulation]
  simp only [scoreVariance_replicatePopulation]

/-- **The minimum recalibrated error in ratio-of-expectations form** is `(E D - E N) / (16 E V_S)`,
with `N` and `D` the correlation accumulators of NOTE2 (21) of the deployed score and phenotype. -/
theorem expectedMinimumRecalibratedMse_eq
    (P : DeploymentPopulation (FullHaplotype Locus Allele) J L)
    (κ : Kernel (FrequencyState Deme Locus Allele) (FrequencyState Deme Locus Allele))
    [IsMarkovKernel κ] (x0 : FrequencyState Deme Locus Allele) (deme : Deme) (w : J → ℝ) :
    expectedMinimumRecalibratedMse P κ x0 deme w
      = ((∫ y, correlationDenominator (stateLaw y deme) (P.score w) P.phenotype ∂(κ x0))
          - ∫ y, correlationNumerator (stateLaw y deme) (P.score w) P.phenotype ∂(κ x0))
        / (16 * ∫ y, (stateLaw y deme).variance (P.score w) ∂(κ x0)) := by
  simp only [expectedMinimumRecalibratedMse,
    scoreVariance_mul_minimumRecalibratedMse_replicatePopulation]
  simp only [scoreVariance_replicatePopulation]
  rw [integral_div, integral_sub
    (integrable_correlationDenominator κ x0 deme (P.score w) P.phenotype)
    (integrable_correlationNumerator κ x0 deme (P.score w) P.phenotype), div_div]

/-- **The deployed slope along a history** is a rational function of budget-2 moments. -/
theorem expectedDeploymentSlope_historyEventKernel
    (P : DeploymentPopulation (FullHaplotype Locus Allele) J L) (ℓ₀ : Locus)
    (hap₀ : FullHaplotype Locus Allele)
    (events : List ((NeutralRates Deme Locus Allele × ℝ≥0) ⊕ PulseMatrix Deme))
    (x0 : FrequencyState Deme Locus Allele) (deme : Deme) (w : J → ℝ) :
    expectedDeploymentSlope P (historyEventKernel ℓ₀ hap₀ events) x0 deme w
      = momentCalibrationSlope ℓ₀ 2 deme (P.score w) P.phenotype
          (historyEventPropagator (fun _ ↦ 2) events *ᵥ budgetMomentFeature (fun _ ↦ 2) x0) := by
  rw [expectedDeploymentSlope_eq,
    expectedCalibrationSlope_historyEventKernel ℓ₀ hap₀ events le_rfl x0 deme]

/-- **The deployed intercept along a history** is a rational function of budget-3 moments. -/
theorem expectedDeploymentIntercept_historyEventKernel
    (P : DeploymentPopulation (FullHaplotype Locus Allele) J L) (ℓ₀ : Locus)
    (hap₀ : FullHaplotype Locus Allele)
    (events : List ((NeutralRates Deme Locus Allele × ℝ≥0) ⊕ PulseMatrix Deme))
    (x0 : FrequencyState Deme Locus Allele) (deme : Deme) (w : J → ℝ) :
    expectedDeploymentIntercept P (historyEventKernel ℓ₀ hap₀ events) x0 deme w
      = momentCalibrationIntercept ℓ₀ 3 deme (P.score w) P.phenotype
          (historyEventPropagator (fun _ ↦ 3) events *ᵥ budgetMomentFeature (fun _ ↦ 3) x0) := by
  rw [expectedDeploymentIntercept_eq,
    expectedCalibrationIntercept_historyEventKernel ℓ₀ hap₀ events le_rfl x0 deme]

/-- **The minimum recalibrated error along a history** is a rational function of budget-4 moments:
the coefficient vectors of `D`, `N` and `V_S` dotted with the chronological propagator applied to
the budget-4 moments of the initial state. -/
theorem expectedMinimumRecalibratedMse_historyEventKernel
    (P : DeploymentPopulation (FullHaplotype Locus Allele) J L) (ℓ₀ : Locus)
    (hap₀ : FullHaplotype Locus Allele)
    (events : List ((NeutralRates Deme Locus Allele × ℝ≥0) ⊕ PulseMatrix Deme))
    (x0 : FrequencyState Deme Locus Allele) (deme : Deme) (w : J → ℝ) :
    expectedMinimumRecalibratedMse P (historyEventKernel ℓ₀ hap₀ events) x0 deme w
      = (budgetCoefficients ℓ₀ (fun _ ↦ 4) (denominatorPolynomial deme (P.score w) P.phenotype)
            ⬝ᵥ (historyEventPropagator (fun _ ↦ 4) events *ᵥ budgetMomentFeature (fun _ ↦ 4) x0)
          - budgetCoefficients ℓ₀ (fun _ ↦ 4) (numeratorPolynomial deme (P.score w) P.phenotype)
            ⬝ᵥ (historyEventPropagator (fun _ ↦ 4) events *ᵥ budgetMomentFeature (fun _ ↦ 4) x0))
        / (16 * (budgetCoefficients ℓ₀ (fun _ ↦ 4)
            (demeCovariancePolynomial deme (P.score w) (P.score w))
          ⬝ᵥ (historyEventPropagator (fun _ ↦ 4) events
            *ᵥ budgetMomentFeature (fun _ ↦ 4) x0))) := by
  rw [expectedMinimumRecalibratedMse_eq, integral_correlationDenominator_historyEventKernel,
    integral_correlationNumerator_historyEventKernel,
    integral_variance_historyEventKernel ℓ₀ hap₀ events (by norm_num : 2 ≤ 4)]

/-! ## The best fixed recalibration of a history -/

/-- **One prediction across a history.**  The expected mean squared error of one prediction of the
phenotype, applied in every population of a kernel, is its error in the pooled law. -/
theorem integral_expMse_replicatePopulation
    (P : DeploymentPopulation (FullHaplotype Locus Allele) J L)
    (κ : Kernel (FrequencyState Deme Locus Allele) (FrequencyState Deme Locus Allele))
    [IsMarkovKernel κ] (x0 : FrequencyState Deme Locus Allele) (deme : Deme)
    (prediction : FullHaplotype Locus Allele → ℝ) :
    ∫ y, Foundations.expMse (replicatePopulation P y deme).E P.phenotype prediction ∂(κ x0)
      = Foundations.expMse (pooledPopulation P κ x0 deme).E P.phenotype prediction := by
  show ∫ y, (stateLaw y deme).expectation (fun hap ↦ (P.phenotype hap - prediction hap) ^ 2)
      ∂(κ x0)
    = (pooledLaw κ x0 deme).expectation (fun hap ↦ (P.phenotype hap - prediction hap) ^ 2)
  exact (expectation_pooledLaw κ x0 deme _).symm

/-- **The expected deployed error is the pooled deployed error.**  The master deployed error is
linear in the law, so its expectation over the populations of a kernel is its value in the pooled
law.  NOTE2 §6.2: the expectation of the metric and the ratio of expectations coincide here. -/
theorem integral_deployedMse_eq_pooled
    (P : DeploymentPopulation (FullHaplotype Locus Allele) J L)
    (κ : Kernel (FrequencyState Deme Locus Allele) (FrequencyState Deme Locus Allele))
    [IsMarkovKernel κ] (x0 : FrequencyState Deme Locus Allele) (deme : Deme) (w : J → ℝ) :
    ∫ y, (replicatePopulation P y deme).deployedMse w ∂(κ x0)
      = (pooledPopulation P κ x0 deme).deployedMse w :=
  integral_expMse_replicatePopulation P κ x0 deme (P.score w)

/-- **The expected deployed error along a history** is a budget-1 moment. -/
theorem integral_deployedMse_historyEventKernel
    (P : DeploymentPopulation (FullHaplotype Locus Allele) J L) (ℓ₀ : Locus)
    (hap₀ : FullHaplotype Locus Allele)
    (events : List ((NeutralRates Deme Locus Allele × ℝ≥0) ⊕ PulseMatrix Deme))
    (x0 : FrequencyState Deme Locus Allele) (deme : Deme) (w : J → ℝ) :
    ∫ y, (replicatePopulation P y deme).deployedMse w ∂(historyEventKernel ℓ₀ hap₀ events x0)
      = budgetCoefficients ℓ₀ (fun _ ↦ 1)
          (demeMeanPolynomial deme fun hap ↦ (P.phenotype hap - P.score w hap) ^ 2)
        ⬝ᵥ (historyEventPropagator (fun _ ↦ 1) events *ᵥ budgetMomentFeature (fun _ ↦ 1) x0) :=
  integral_expectation_historyEventKernel ℓ₀ hap₀ events le_rfl x0 deme
    fun hap ↦ (P.phenotype hap - P.score w hap) ^ 2

/-- **The best fixed recalibration of a history.**  No affine correction `a + b·S` applied in every
population of a kernel has expected mean squared error below the pooled outcome variance times
one minus the pooled `R²`. -/
theorem integral_recalibratedMse_ge
    (P : DeploymentPopulation (FullHaplotype Locus Allele) J L)
    (κ : Kernel (FrequencyState Deme Locus Allele) (FrequencyState Deme Locus Allele))
    [IsMarkovKernel κ] (x0 : FrequencyState Deme Locus Allele) (deme : Deme) (w : J → ℝ)
    (hvariance : 0 < (pooledPopulation P κ x0 deme).scoreVariance w) (a b : ℝ) :
    (pooledPopulation P κ x0 deme).outcomeVariance * (1 - (pooledPopulation P κ x0 deme).r2 w)
      ≤ ∫ y, Foundations.expMse (replicatePopulation P y deme).E P.phenotype
          ((pooledPopulation P κ x0 deme).recalibratedScore w a b) ∂(κ x0) := by
  rw [integral_expMse_replicatePopulation,
    ← DeploymentPopulation.bestAffine_mse_eq (pooledPopulation P κ x0 deme) w hvariance.ne']
  exact DeploymentPopulation.bestAffine_mse_le (pooledPopulation P κ x0 deme) w hvariance a b

/-- **The pooled calibration line attains the bound**: applied in every population it has
expected mean squared error the pooled `Var(Y) (1 - R²)`. -/
theorem integral_bestAffineMse_eq
    (P : DeploymentPopulation (FullHaplotype Locus Allele) J L)
    (κ : Kernel (FrequencyState Deme Locus Allele) (FrequencyState Deme Locus Allele))
    [IsMarkovKernel κ] (x0 : FrequencyState Deme Locus Allele) (deme : Deme) (w : J → ℝ)
    (hvariance : (pooledPopulation P κ x0 deme).scoreVariance w ≠ 0) :
    ∫ y, Foundations.expMse (replicatePopulation P y deme).E P.phenotype
        ((pooledPopulation P κ x0 deme).bestAffineScore w) ∂(κ x0)
      = (pooledPopulation P κ x0 deme).outcomeVariance
        * (1 - (pooledPopulation P κ x0 deme).r2 w) := by
  rw [integral_expMse_replicatePopulation]
  exact DeploymentPopulation.bestAffine_mse_eq (pooledPopulation P κ x0 deme) w hvariance

/-- **The pooled deployment sees the history only through budget-1 moments.**  Two histories whose
propagated budget-1 moments agree give one pooled population, so every metric of the master
theorem agrees on them: slope, intercept, `R²`, deployed error and recalibrated error. -/
theorem pooledPopulation_eq_of_moments_eq
    (P : DeploymentPopulation (FullHaplotype Locus Allele) J L) (ℓ₀ : Locus)
    (hap₀ : FullHaplotype Locus Allele)
    {first second : List ((NeutralRates Deme Locus Allele × ℝ≥0) ⊕ PulseMatrix Deme)}
    {x₁ x₂ : FrequencyState Deme Locus Allele}
    (hmoments : historyEventPropagator (fun _ ↦ 1) first *ᵥ budgetMomentFeature (fun _ ↦ 1) x₁
      = historyEventPropagator (fun _ ↦ 1) second *ᵥ budgetMomentFeature (fun _ ↦ 1) x₂)
    (deme : Deme) :
    pooledPopulation P (historyEventKernel ℓ₀ hap₀ first) x₁ deme
      = pooledPopulation P (historyEventKernel ℓ₀ hap₀ second) x₂ deme := by
  unfold pooledPopulation
  rw [pooledLaw_eq_of_moments_eq ℓ₀ hap₀ hmoments deme]

end Master

end

end Descent.Portability.EndToEndPooledCalibration
