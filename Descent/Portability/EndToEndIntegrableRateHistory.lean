/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.Normed.Operator.BanachSteinhaus
import Descent.Portability.NeutralIntegrableRateRealization
import Descent.Portability.PortabilityMomentLadderSeries

assert_below Descent.Decision Descent.Program

/-!
# The Markov kernel of an integrable rate history, and its moment ladder

`NeutralRateHistoryKernel.rateHistoryKernel` is the neutral process law of a rate history whose
dual generator is continuous on the horizon, and `PortabilityMomentLadder` reads the metrics of
portability off the propagated moments of a process law.  `NeutralIntegrableRateRealization`
realizes the moments of a rate history with merely integrable rates, NOTE1 §4.2a, one initial
state at a time, with no process law.  This module constructs that process law and carries the
ladder to it.

The propagator.  At every budget the integral equation `U(t) = 1 + ∫₀ᵗ Q(s) U(s) ds` along the
dual generator of the history has one continuous solution, and `integrableRateDualPropagator` is
its value at the horizon (`integrableRateDualPropagator_eq`).  The rate histories with continuous
coordinates within `1 / (k + 1)` of the history in `L¹([0, T])` (`approximatingRates`,
`approximatingRates_spec`) have dual propagators converging to it at every budget
(`tendsto_rateHistoryDualPropagator_approximatingRates`).

The kernel.  Each approximating history has a continuous dual generator, so it has a kernel whose
operator on continuous observables (`approximatingOperator`) is a positive, constant-preserving
contraction (`norm_approximatingOperator_apply_le`).  On a polynomial observable that operator is
a fixed linear readout of the propagator at the support budget (`momentReadout`,
`approximatingOperator_polynomial`), so the operators converge there.  Contractions that converge
on a dense set converge everywhere (`cauchySeq_of_dense`, `cauchySeq_approximatingOperator`), and
by Banach–Steinhaus the limit is a continuous linear operator (`integrableRateHistoryOperator`),
positive and constant-preserving (`integrableRateHistoryOperator_nonneg`,
`integrableRateHistoryOperator_one`).  Its Riesz kernel is a Markov kernel
(`integrableRateHistoryKernel`, `isMarkovKernel_integrableRateHistoryKernel`,
`integral_integrableRateHistoryKernel`) whose expected configuration moments are the propagator
applied to the initial moments, NOTE1 (20)
(`integral_momentPolynomial_integrableRateHistoryKernel`,
`hasDualMoments_integrableRateHistoryKernel`).

The ladder.  An event history of epochs, splits and pulses and an integrable rate history whose
propagated budget-4 moments agree give every score one portability report
(`portabilityReport_historyEvent_eq_integrableRateHistory`).  Equal propagated moments at every
budget give one expected squared correlation and one expected AUC in every deme
(`expectedMetrics_historyEvent_eq_integrableRateHistory`).

Scope.  The hypothesis is interval integrability of the rate coordinates on `[0, T]`, NOTE1's
hypothesis of measurable rates with integrable norm.  The kernel is built from one choice of
approximating histories.  Its moments do not depend on that choice, but the independence of the
kernel itself, and its agreement with `rateHistoryKernel` for continuous rates, are not stated
here.  A locus `ℓ₀` and a haplotype `hap₀` are explicit arguments, as in
`NeutralRateHistoryKernel`.

## Empirical status

None.  The bodies here are limits of positive operators on continuous observables and integrals
against Markov kernels whose moments solve a matrix integral equation of supplied rates, so no
measurement can bear on them.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.EndToEndIntegrableRateHistory

open MeasureTheory ProbabilityTheory MvPolynomial Filter Topology Descent.Coalescent
  PartialHaplotypeCarrier PartialHaplotypeDualGenerator PartialHaplotypeDualSemigroup
  NeutralFellerGenerator NeutralPolynomialSemigroup NeutralPolynomialPositivity
  PartialHaplotypeMicroscopicApproximation PolynomialFellerExtension FellerMarkovKernel
  NeutralMicroscopicEulerLimit NeutralMicroscopicFloorLimit NeutralHistoryKernel
  LinearFundamentalMatrix NeutralRateHistoryRealization NeutralRateHistoryKernel
  NeutralRateLipschitz NeutralIntegrableRateRealization PartialHaplotypePulseKernel
  NeutralPulseHistoryKernel ReplicaMetricInstances EndToEndPortabilityLaw
  EndToEndCorrelationSeries EndToEndDiscriminationLaw PortabilityMomentLadder
  PortabilityMomentLadderSeries
open IntegrableRateRealization (eq_of_integral_eq
  exists_integral_solution_of_continuous_approximation)
open scoped Matrix NNReal Matrix.Norms.Operator

noncomputable section

/-! ## Contractions converging on a dense set -/

/-- **Contractions that converge on a dense set converge everywhere.**  If every operator of a
sequence contracts norms, and its values at every vector of a dense set form Cauchy sequences, then
its values at every vector form a Cauchy sequence.

Assumes: every operator contracts norms, and the values are Cauchy on a dense set. -/
theorem cauchySeq_of_dense {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (S : ℕ → E →L[ℝ] F)
    (hcontract : ∀ k g, ‖S k g‖ ≤ ‖g‖) {D : Set E} (hD : Dense D)
    (hcauchy : ∀ f ∈ D, CauchySeq fun k ↦ S k f) (g : E) : CauchySeq fun k ↦ S k g := by
  refine Metric.cauchySeq_iff.mpr fun ε hε ↦ ?_
  obtain ⟨f, hgf, hf⟩ := Metric.dense_iff.mp hD g (ε / 3) (div_pos hε zero_lt_three)
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp (hcauchy f hf) (ε / 3) (div_pos hε zero_lt_three)
  have hnear : ∀ k, dist (S k g) (S k f) < ε / 3 := fun k ↦ by
    rw [dist_eq_norm, ← map_sub]
    refine (hcontract k (g - f)).trans_lt ?_
    rw [← dist_eq_norm, dist_comm]
    exact hgf
  refine ⟨N, fun m hm n hn ↦ ?_⟩
  calc dist (S m g) (S n g)
      ≤ dist (S m g) (S m f) + dist (S m f) (S n f) + dist (S n f) (S n g) :=
        dist_triangle4 _ _ _ _
    _ < ε / 3 + ε / 3 + ε / 3 := by
        rw [dist_comm (S n f)]
        exact add_lt_add (add_lt_add (hnear m) (hN m hm n hn)) (hnear n)
    _ = ε := by ring

variable {Deme Locus : Type*} {Allele : Locus → Type*}
variable [Fintype Deme] [DecidableEq Deme] [Fintype Locus] [DecidableEq Locus]
  [∀ ℓ, Fintype (Allele ℓ)] [∀ ℓ, DecidableEq (Allele ℓ)]

/-! ## The propagator of an integrable rate history -/

/-- **The dual propagator of an integrable rate history** at a budget: the value at the horizon of
a continuous solution of `U(t) = 1 + ∫₀ᵗ Q(s) U(s) ds` along its dual generator. -/
def integrableRateDualPropagator (rates : ℝ → NeutralRates Deme Locus Allele)
    (capacity : Locus → ℕ) {T : ℝ} (hT : 0 ≤ T)
    (hintegrable : IntervalIntegrable (fun t ↦ neutralRateCoordinates (rates t)) volume 0 T) :
    Matrix (BudgetConfiguration Deme Locus Allele capacity)
      (BudgetConfiguration Deme Locus Allele capacity) ℝ :=
  (exists_neutralIntegrablePropagator rates capacity hT hintegrable).choose T

/-- **The propagator is the solution of the integral equation.**  Every continuous solution of
`U(t) = 1 + ∫₀ᵗ Q(s) U(s) ds` along the dual generator of an integrable rate history takes the
value `integrableRateDualPropagator` at the horizon.

Assumes: the rate coordinates are interval integrable on `[0, T]`, and `propagator` is a
continuous solution of the integral equation. -/
theorem integrableRateDualPropagator_eq {rates : ℝ → NeutralRates Deme Locus Allele} {T : ℝ}
    (hT : 0 ≤ T)
    (hintegrable : IntervalIntegrable (fun t ↦ neutralRateCoordinates (rates t)) volume 0 T)
    (capacity : Locus → ℕ)
    {propagator : ℝ → Matrix (BudgetConfiguration Deme Locus Allele capacity)
      (BudgetConfiguration Deme Locus Allele capacity) ℝ}
    (hcontinuous : Continuous propagator)
    (hequation : ∀ t ∈ Set.Icc 0 T,
      propagator t = 1 + ∫ s in (0 : ℝ)..t, dualGenerator (rates s) capacity * propagator s) :
    integrableRateDualPropagator rates capacity hT hintegrable = propagator T :=
  eq_of_integral_eq hT (intervalIntegrable_dualGenerator capacity hintegrable)
    (exists_neutralIntegrablePropagator rates capacity hT hintegrable).choose_spec.1 hcontinuous
    (exists_neutralIntegrablePropagator rates capacity hT hintegrable).choose_spec.2.1 hequation
    T ⟨hT, le_rfl⟩

/-- The continuous rate histories approximating an integrable one: at step `k`, a rate history
with continuous coordinates within `1 / (k + 1)` of it in `L¹([0, T])`. -/
def approximatingRates (rates : ℝ → NeutralRates Deme Locus Allele) {T : ℝ} (hT : 0 ≤ T)
    (hintegrable : IntervalIntegrable (fun t ↦ neutralRateCoordinates (rates t)) volume 0 T)
    (k : ℕ) : ℝ → NeutralRates Deme Locus Allele :=
  (exists_continuous_neutralRates_near hT hintegrable
    (by positivity : (0 : ℝ) < 1 / ((k : ℝ) + 1))).choose

/-- The approximating rate histories have continuous coordinates, and lie within `1 / (k + 1)` of
the history in `L¹([0, T])`.

Assumes: the rate coordinates are interval integrable on `[0, T]`. -/
theorem approximatingRates_spec {rates : ℝ → NeutralRates Deme Locus Allele} {T : ℝ}
    (hT : 0 ≤ T)
    (hintegrable : IntervalIntegrable (fun t ↦ neutralRateCoordinates (rates t)) volume 0 T)
    (k : ℕ) :
    Continuous (fun t ↦ neutralRateCoordinates (approximatingRates rates hT hintegrable k t)) ∧
      ∫ t in (0 : ℝ)..T, ‖neutralRateCoordinates (approximatingRates rates hT hintegrable k t)
        - neutralRateCoordinates (rates t)‖ ≤ 1 / ((k : ℝ) + 1) :=
  (exists_continuous_neutralRates_near hT hintegrable
    (by positivity : (0 : ℝ) < 1 / ((k : ℝ) + 1))).choose_spec

/-- Every approximating rate history has a dual generator continuous on the horizon at every
budget.

Assumes: the rate coordinates are interval integrable on `[0, T]`. -/
theorem continuousOn_dualGenerator_approximatingRates
    {rates : ℝ → NeutralRates Deme Locus Allele} {T : ℝ} (hT : 0 ≤ T)
    (hintegrable : IntervalIntegrable (fun t ↦ neutralRateCoordinates (rates t)) volume 0 T)
    (k : ℕ) (capacity : Locus → ℕ) :
    ContinuousOn (fun t ↦ dualGenerator (approximatingRates rates hT hintegrable k t) capacity)
      (Set.Icc 0 T) :=
  continuousOn_dualGenerator_of_continuous (approximatingRates_spec hT hintegrable k).1 capacity T

/-- **The approximating propagators converge to the propagator.**  At every budget the dual
propagators of the approximating rate histories converge to the propagator of the integrable rate
history.

Assumes: the rate coordinates are interval integrable on `[0, T]`. -/
theorem tendsto_rateHistoryDualPropagator_approximatingRates
    {rates : ℝ → NeutralRates Deme Locus Allele} {T : ℝ} (hT : 0 ≤ T)
    (hintegrable : IntervalIntegrable (fun t ↦ neutralRateCoordinates (rates t)) volume 0 T)
    (capacity : Locus → ℕ) :
    Tendsto (fun k ↦ rateHistoryDualPropagator (approximatingRates rates hT hintegrable k)
        capacity T) atTop (𝓝 (integrableRateDualPropagator rates capacity hT hintegrable)) := by
  obtain ⟨K, hK, hlipschitz⟩ :=
    exists_dualGenerator_lipschitz (Deme := Deme) (Allele := Allele) capacity
  have hgenerator := intervalIntegrable_dualGenerator capacity hintegrable
  have hpath : ∀ k : ℕ,
      Continuous (dualGeneratorPath (approximatingRates rates hT hintegrable k) capacity T) :=
    fun k ↦ continuous_dualGeneratorPath hT
      (continuousOn_dualGenerator_approximatingRates hT hintegrable k capacity)
  have hclose : ∀ k : ℕ, ∫ s in (0 : ℝ)..T,
      ‖dualGeneratorPath (approximatingRates rates hT hintegrable k) capacity T s
        - dualGenerator (rates s) capacity‖ ≤ K * (1 / ((k : ℝ) + 1)) := fun k ↦ by
    refine le_trans (intervalIntegral.integral_mono_on hT
      (((hpath k).intervalIntegrable 0 T).sub hgenerator).norm
      ((((approximatingRates_spec hT hintegrable k).1.intervalIntegrable 0 T).sub
        hintegrable).norm.const_mul K) fun s hs ↦ ?_) ?_
    · simp only [dualGeneratorPath, clampTime_of_mem hs]
      exact hlipschitz _ _
    · rw [intervalIntegral.integral_const_mul]
      exact mul_le_mul_of_nonneg_left (approximatingRates_spec hT hintegrable k).2 hK
  obtain ⟨solution, hsolution, hequation, hlimit⟩ :=
    exists_integral_solution_of_continuous_approximation hT hgenerator hK
      (fun k ↦ dualGeneratorPath (approximatingRates rates hT hintegrable k) capacity T) hpath
      hclose
  rw [integrableRateDualPropagator_eq hT hintegrable capacity hsolution hequation]
  exact hlimit

/-! ## The operator of an integrable rate history -/

/-- The operator on continuous observables of the kernel of the `k`-th approximating rate
history. -/
def approximatingOperator (rates : ℝ → NeutralRates Deme Locus Allele) (ℓ₀ : Locus)
    (hap₀ : FullHaplotype Locus Allele) {T : ℝ} (hT : 0 ≤ T)
    (hintegrable : IntervalIntegrable (fun t ↦ neutralRateCoordinates (rates t)) volume 0 T)
    (k : ℕ) :
    C(FrequencyState Deme Locus Allele, ℝ) →L[ℝ] C(FrequencyState Deme Locus Allele, ℝ) :=
  rateHistoryOperator (approximatingRates rates hT hintegrable k) ℓ₀ hap₀ hT
    (continuousOn_dualGenerator_approximatingRates hT hintegrable k)

/-- The observable `x ↦ c ⬝ᵥ (P *ᵥ H(x))` read off a matrix `P` of a budget: a fixed combination of
propagated configuration moments, linear in the matrix. -/
def momentReadout (capacity : Locus → ℕ)
    (c : BudgetConfiguration Deme Locus Allele capacity → ℝ) :
    Matrix (BudgetConfiguration Deme Locus Allele capacity)
        (BudgetConfiguration Deme Locus Allele capacity) ℝ
      →ₗ[ℝ] C(FrequencyState Deme Locus Allele, ℝ) where
  toFun P := ⟨fun x ↦ c ⬝ᵥ (P *ᵥ budgetMomentFeature capacity x),
    Continuous.dotProduct continuous_const
      (Continuous.matrix_mulVec continuous_const (continuous_budgetMomentFeature capacity))⟩
  map_add' P Q := ContinuousMap.ext fun x ↦ by simp [Matrix.add_mulVec, dotProduct_add]
  map_smul' a P := ContinuousMap.ext fun x ↦ by simp [Matrix.smul_mulVec, dotProduct_smul]

/-- The readout of a matrix at a state. -/
theorem momentReadout_apply (capacity : Locus → ℕ)
    (c : BudgetConfiguration Deme Locus Allele capacity → ℝ)
    (P : Matrix (BudgetConfiguration Deme Locus Allele capacity)
      (BudgetConfiguration Deme Locus Allele capacity) ℝ)
    (x : FrequencyState Deme Locus Allele) :
    momentReadout capacity c P x = c ⬝ᵥ (P *ᵥ budgetMomentFeature capacity x) :=
  rfl

/-- **An approximating operator on a polynomial observable** is the readout, by the coefficient
vector of the observable at its support budget, of the propagator of the approximating rate
history.

Assumes: the rate coordinates are interval integrable on `[0, T]`. -/
theorem approximatingOperator_polynomial {rates : ℝ → NeutralRates Deme Locus Allele} {T : ℝ}
    (hT : 0 ≤ T)
    (hintegrable : IntervalIntegrable (fun t ↦ neutralRateCoordinates (rates t)) volume 0 T)
    (ℓ₀ : Locus) (hap₀ : FullHaplotype Locus Allele) (k : ℕ)
    (f : PolynomialSubspace Deme Locus Allele) :
    approximatingOperator rates ℓ₀ hap₀ hT hintegrable k
        (f : C(FrequencyState Deme Locus Allele, ℝ))
      = momentReadout (supportBudget ℓ₀ (representative f))
          (budgetCoefficients ℓ₀ (supportBudget ℓ₀ (representative f)) (representative f))
          (rateHistoryDualPropagator (approximatingRates rates hT hintegrable k)
            (supportBudget ℓ₀ (representative f)) T) := by
  haveI := isMarkovKernel_rateHistoryKernel hT
    (continuousOn_dualGenerator_approximatingRates hT hintegrable k) ℓ₀ hap₀
  refine ContinuousMap.ext fun x ↦ ?_
  rw [momentReadout_apply, approximatingOperator, ← integral_rateHistoryKernel,
    ← polynomialFunction_representative f]
  exact integral_polynomial_eq_dotProduct ℓ₀ (supportBudget ℓ₀ (representative f)) _ _
    (integral_momentPolynomial_rateHistoryKernel hT
      (continuousOn_dualGenerator_approximatingRates hT hintegrable k) ℓ₀ hap₀ _)
    (representative f) (withinBudget_supportBudget ℓ₀ (representative f)) x

/-- An approximating operator on a configuration moment is the coordinate of the propagator of
the approximating rate history applied to the initial moments.

Assumes: the rate coordinates are interval integrable on `[0, T]`. -/
theorem approximatingOperator_momentPolynomial {rates : ℝ → NeutralRates Deme Locus Allele}
    {T : ℝ} (hT : 0 ≤ T)
    (hintegrable : IntervalIntegrable (fun t ↦ neutralRateCoordinates (rates t)) volume 0 T)
    (ℓ₀ : Locus) (hap₀ : FullHaplotype Locus Allele) (k : ℕ) (capacity : Locus → ℕ)
    (x : FrequencyState Deme Locus Allele) (ξ : BudgetConfiguration Deme Locus Allele capacity) :
    approximatingOperator rates ℓ₀ hap₀ hT hintegrable k
        (polynomialFunction (momentPolynomial ξ.1)) x
      = (rateHistoryDualPropagator (approximatingRates rates hT hintegrable k) capacity T
          *ᵥ budgetMomentFeature capacity x) ξ :=
  (integral_rateHistoryKernel hT (continuousOn_dualGenerator_approximatingRates hT hintegrable k)
      ℓ₀ hap₀ x _).symm.trans
    (integral_momentPolynomial_rateHistoryKernel hT
      (continuousOn_dualGenerator_approximatingRates hT hintegrable k) ℓ₀ hap₀ capacity x ξ)

/-- The approximating operators contract sup norms.

Assumes: the rate coordinates are interval integrable on `[0, T]`. -/
theorem norm_approximatingOperator_apply_le {rates : ℝ → NeutralRates Deme Locus Allele} {T : ℝ}
    (hT : 0 ≤ T)
    (hintegrable : IntervalIntegrable (fun t ↦ neutralRateCoordinates (rates t)) volume 0 T)
    (ℓ₀ : Locus) (hap₀ : FullHaplotype Locus Allele) (k : ℕ)
    (g : C(FrequencyState Deme Locus Allele, ℝ)) :
    ‖approximatingOperator rates ℓ₀ hap₀ hT hintegrable k g‖ ≤ ‖g‖ := by
  rw [approximatingOperator, rateHistoryOperator_apply]
  exact norm_rateHistoryOperatorValue_le hT
    (continuousOn_dualGenerator_approximatingRates hT hintegrable k) ℓ₀ hap₀ g

/-- **The approximating operators converge on every continuous observable.**  Their values form a
Cauchy sequence in sup norm at every continuous observable.

Assumes: the rate coordinates are interval integrable on `[0, T]`. -/
theorem cauchySeq_approximatingOperator {rates : ℝ → NeutralRates Deme Locus Allele} {T : ℝ}
    (hT : 0 ≤ T)
    (hintegrable : IntervalIntegrable (fun t ↦ neutralRateCoordinates (rates t)) volume 0 T)
    (ℓ₀ : Locus) (hap₀ : FullHaplotype Locus Allele)
    (g : C(FrequencyState Deme Locus Allele, ℝ)) :
    CauchySeq fun k ↦ approximatingOperator rates ℓ₀ hap₀ hT hintegrable k g := by
  refine cauchySeq_of_dense _ (norm_approximatingOperator_apply_le hT hintegrable ℓ₀ hap₀)
    dense_polynomialSubspace (fun f hf ↦ ?_) g
  have hreadout := ((momentReadout (supportBudget ℓ₀ (representative ⟨f, hf⟩))
      (budgetCoefficients ℓ₀ (supportBudget ℓ₀ (representative ⟨f, hf⟩))
        (representative ⟨f, hf⟩))).continuous_of_finiteDimensional.tendsto _).comp
    (tendsto_rateHistoryDualPropagator_approximatingRates hT hintegrable
      (supportBudget ℓ₀ (representative ⟨f, hf⟩)))
  exact (hreadout.congr fun k ↦
    (approximatingOperator_polynomial hT hintegrable ℓ₀ hap₀ k ⟨f, hf⟩).symm).cauchySeq

/-- The approximating operators converge pointwise, as maps on continuous observables, to their
limit values.

Assumes: the rate coordinates are interval integrable on `[0, T]`. -/
theorem tendsto_approximatingOperator {rates : ℝ → NeutralRates Deme Locus Allele} {T : ℝ}
    (hT : 0 ≤ T)
    (hintegrable : IntervalIntegrable (fun t ↦ neutralRateCoordinates (rates t)) volume 0 T)
    (ℓ₀ : Locus) (hap₀ : FullHaplotype Locus Allele) :
    Tendsto (fun k g ↦ approximatingOperator rates ℓ₀ hap₀ hT hintegrable k g) atTop
      (𝓝 fun g ↦ limUnder atTop fun k ↦ approximatingOperator rates ℓ₀ hap₀ hT hintegrable k g) :=
  tendsto_pi_nhds.mpr fun g ↦
    (cauchySeq_approximatingOperator hT hintegrable ℓ₀ hap₀ g).tendsto_limUnder

/-- **The operator of an integrable rate history** on continuous observables: the limit of the
operators of the approximating rate histories, continuous by Banach–Steinhaus. -/
def integrableRateHistoryOperator (rates : ℝ → NeutralRates Deme Locus Allele) (ℓ₀ : Locus)
    (hap₀ : FullHaplotype Locus Allele) {T : ℝ} (hT : 0 ≤ T)
    (hintegrable : IntervalIntegrable (fun t ↦ neutralRateCoordinates (rates t)) volume 0 T) :
    C(FrequencyState Deme Locus Allele, ℝ) →L[ℝ] C(FrequencyState Deme Locus Allele, ℝ) :=
  continuousLinearMapOfTendsto (approximatingOperator rates ℓ₀ hap₀ hT hintegrable)
    (tendsto_approximatingOperator hT hintegrable ℓ₀ hap₀)

/-- The operator of an integrable rate history is the limit value. -/
theorem integrableRateHistoryOperator_apply (rates : ℝ → NeutralRates Deme Locus Allele)
    (ℓ₀ : Locus) (hap₀ : FullHaplotype Locus Allele) {T : ℝ} (hT : 0 ≤ T)
    (hintegrable : IntervalIntegrable (fun t ↦ neutralRateCoordinates (rates t)) volume 0 T)
    (g : C(FrequencyState Deme Locus Allele, ℝ)) :
    integrableRateHistoryOperator rates ℓ₀ hap₀ hT hintegrable g
      = limUnder atTop fun k ↦ approximatingOperator rates ℓ₀ hap₀ hT hintegrable k g :=
  rfl

/-- The approximating operators converge to the operator of the integrable rate history at every
state.

Assumes: the rate coordinates are interval integrable on `[0, T]`. -/
theorem tendsto_approximatingOperator_apply {rates : ℝ → NeutralRates Deme Locus Allele} {T : ℝ}
    (hT : 0 ≤ T)
    (hintegrable : IntervalIntegrable (fun t ↦ neutralRateCoordinates (rates t)) volume 0 T)
    (ℓ₀ : Locus) (hap₀ : FullHaplotype Locus Allele)
    (g : C(FrequencyState Deme Locus Allele, ℝ)) (x : FrequencyState Deme Locus Allele) :
    Tendsto (fun k ↦ approximatingOperator rates ℓ₀ hap₀ hT hintegrable k g x) atTop
      (𝓝 (integrableRateHistoryOperator rates ℓ₀ hap₀ hT hintegrable g x)) := by
  rw [integrableRateHistoryOperator_apply]
  exact ((continuous_eval_const x).tendsto _).comp
    (cauchySeq_approximatingOperator hT hintegrable ℓ₀ hap₀ g).tendsto_limUnder

/-- The operator of an integrable rate history is positive.

Assumes: the rate coordinates are interval integrable on `[0, T]`, and the observable is
nonnegative. -/
theorem integrableRateHistoryOperator_nonneg {rates : ℝ → NeutralRates Deme Locus Allele} {T : ℝ}
    (hT : 0 ≤ T)
    (hintegrable : IntervalIntegrable (fun t ↦ neutralRateCoordinates (rates t)) volume 0 T)
    (ℓ₀ : Locus) (hap₀ : FullHaplotype Locus Allele)
    (g : C(FrequencyState Deme Locus Allele, ℝ)) (hg : 0 ≤ g) :
    0 ≤ integrableRateHistoryOperator rates ℓ₀ hap₀ hT hintegrable g := by
  refine ContinuousMap.le_def.mpr fun x ↦ ?_
  refine ge_of_tendsto' (tendsto_approximatingOperator_apply hT hintegrable ℓ₀ hap₀ g x)
    fun k ↦ ?_
  rw [approximatingOperator]
  exact ContinuousMap.le_def.mp (rateHistoryOperator_nonneg hT _ ℓ₀ hap₀ g hg) x

/-- The operator of an integrable rate history fixes the constant observable.

Assumes: the rate coordinates are interval integrable on `[0, T]`. -/
theorem integrableRateHistoryOperator_one {rates : ℝ → NeutralRates Deme Locus Allele} {T : ℝ}
    (hT : 0 ≤ T)
    (hintegrable : IntervalIntegrable (fun t ↦ neutralRateCoordinates (rates t)) volume 0 T)
    (ℓ₀ : Locus) (hap₀ : FullHaplotype Locus Allele) :
    integrableRateHistoryOperator rates ℓ₀ hap₀ hT hintegrable 1 = 1 := by
  rw [integrableRateHistoryOperator_apply]
  refine Tendsto.limUnder_eq (tendsto_const_nhds.congr fun k ↦ ?_)
  rw [approximatingOperator, rateHistoryOperator_one]

/-! ## The kernel of an integrable rate history -/

/-- **The neutral Markov kernel of an integrable rate history** over `[0, T]`: the Riesz kernel of
the operator of the history. -/
def integrableRateHistoryKernel (rates : ℝ → NeutralRates Deme Locus Allele) (ℓ₀ : Locus)
    (hap₀ : FullHaplotype Locus Allele) {T : ℝ} (hT : 0 ≤ T)
    (hintegrable : IntervalIntegrable (fun t ↦ neutralRateCoordinates (rates t)) volume 0 T) :
    Kernel (FrequencyState Deme Locus Allele) (FrequencyState Deme Locus Allele) :=
  markovKernel (integrableRateHistoryOperator rates ℓ₀ hap₀ hT hintegrable)
    (integrableRateHistoryOperator_nonneg hT hintegrable ℓ₀ hap₀)
    (integrableRateHistoryOperator_one hT hintegrable ℓ₀ hap₀)

/-- The kernel of an integrable rate history is a Markov kernel.

Assumes: the rate coordinates are interval integrable on `[0, T]`. -/
theorem isMarkovKernel_integrableRateHistoryKernel {rates : ℝ → NeutralRates Deme Locus Allele}
    {T : ℝ} (hT : 0 ≤ T)
    (hintegrable : IntervalIntegrable (fun t ↦ neutralRateCoordinates (rates t)) volume 0 T)
    (ℓ₀ : Locus) (hap₀ : FullHaplotype Locus Allele) :
    IsMarkovKernel (integrableRateHistoryKernel rates ℓ₀ hap₀ hT hintegrable) :=
  isMarkovKernel_markovKernel _ _ _

/-- The kernel of an integrable rate history integrates every continuous observable to the
operator of the history.

Assumes: the rate coordinates are interval integrable on `[0, T]`. -/
theorem integral_integrableRateHistoryKernel {rates : ℝ → NeutralRates Deme Locus Allele}
    {T : ℝ} (hT : 0 ≤ T)
    (hintegrable : IntervalIntegrable (fun t ↦ neutralRateCoordinates (rates t)) volume 0 T)
    (ℓ₀ : Locus) (hap₀ : FullHaplotype Locus Allele) (x : FrequencyState Deme Locus Allele)
    (g : C(FrequencyState Deme Locus Allele, ℝ)) :
    ∫ y, g y ∂(integrableRateHistoryKernel rates ℓ₀ hap₀ hT hintegrable x)
      = integrableRateHistoryOperator rates ℓ₀ hap₀ hT hintegrable g x :=
  integral_markovKernel _ _ _ x g

/-- **NOTE1 (20) for an integrable rate history, under the process law.**  For every budget, the
expected configuration moments under the kernel of an integrable rate history are its propagator
applied to the moments of the initial state.

Assumes: the rate coordinates are interval integrable on `[0, T]`. -/
theorem integral_momentPolynomial_integrableRateHistoryKernel
    {rates : ℝ → NeutralRates Deme Locus Allele} {T : ℝ} (hT : 0 ≤ T)
    (hintegrable : IntervalIntegrable (fun t ↦ neutralRateCoordinates (rates t)) volume 0 T)
    (ℓ₀ : Locus) (hap₀ : FullHaplotype Locus Allele) (capacity : Locus → ℕ)
    (x : FrequencyState Deme Locus Allele) (ξ : BudgetConfiguration Deme Locus Allele capacity) :
    ∫ y, polynomialFunction (momentPolynomial ξ.1) y
        ∂(integrableRateHistoryKernel rates ℓ₀ hap₀ hT hintegrable x)
      = (integrableRateDualPropagator rates capacity hT hintegrable
          *ᵥ budgetMomentFeature capacity x) ξ := by
  rw [integral_integrableRateHistoryKernel]
  refine tendsto_nhds_unique (tendsto_approximatingOperator_apply hT hintegrable ℓ₀ hap₀ _ x)
    ((((continuous_apply ξ).tendsto _).comp
      (((EulerInvariantSet.mulVecMap
        (budgetMomentFeature capacity x)).continuous_of_finiteDimensional.tendsto _).comp
        (tendsto_rateHistoryDualPropagator_approximatingRates hT hintegrable capacity))).congr
      fun k ↦ ?_)
  exact (approximatingOperator_momentPolynomial hT hintegrable ℓ₀ hap₀ k capacity x ξ).symm

/-- **The kernel of an integrable rate history has dual moments at every budget**, along its
propagator.

Assumes: the rate coordinates are interval integrable on `[0, T]`. -/
theorem hasDualMoments_integrableRateHistoryKernel {rates : ℝ → NeutralRates Deme Locus Allele}
    {T : ℝ} (hT : 0 ≤ T)
    (hintegrable : IntervalIntegrable (fun t ↦ neutralRateCoordinates (rates t)) volume 0 T)
    (ℓ₀ : Locus) (hap₀ : FullHaplotype Locus Allele) (n : ℕ) :
    HasDualMoments (integrableRateHistoryKernel rates ℓ₀ hap₀ hT hintegrable) n
      (integrableRateDualPropagator rates (fun _ ↦ n) hT hintegrable) :=
  integral_momentPolynomial_integrableRateHistoryKernel hT hintegrable ℓ₀ hap₀ (fun _ ↦ n)

/-! ## The ladder for integrable rate histories -/

attribute [local instance] isMarkovKernel_historyEventKernel
  isMarkovKernel_integrableRateHistoryKernel

/-- **An event history and an integrable rate history with equal propagated moments are
indistinguishable.**  If a history of epochs, splits and pulses from `x₁` and a rate history with
integrable rates from `x₂` have equal propagated budget-4 moments, every score, outcome, binary
endpoint, source and target has the same portability report under both.

Assumes: the rate coordinates are interval integrable on `[0, T]`, and the propagated budget-4
moments agree. -/
theorem portabilityReport_historyEvent_eq_integrableRateHistory (ℓ₀ : Locus)
    (hap₀ : FullHaplotype Locus Allele)
    (events : List ((NeutralRates Deme Locus Allele × ℝ≥0) ⊕ PulseMatrix Deme))
    {rates : ℝ → NeutralRates Deme Locus Allele} {T : ℝ} (hT : 0 ≤ T)
    (hintegrable : IntervalIntegrable (fun t ↦ neutralRateCoordinates (rates t)) volume 0 T)
    {x₁ x₂ : FrequencyState Deme Locus Allele}
    (hmoments : historyEventPropagator (fun _ ↦ 4) events *ᵥ budgetMomentFeature (fun _ ↦ 4) x₁
      = integrableRateDualPropagator rates (fun _ ↦ 4) hT hintegrable
          *ᵥ budgetMomentFeature (fun _ ↦ 4) x₂)
    (source target : Deme) (score outcome : FullHaplotype Locus Allele → ℝ)
    (case : FullHaplotype Locus Allele → Bool) :
    portabilityReport (historyEventKernel ℓ₀ hap₀ events) x₁ source target score outcome case
      = portabilityReport (integrableRateHistoryKernel rates ℓ₀ hap₀ hT hintegrable) x₂ source
          target score outcome case :=
  portabilityReport_eq_of_polynomialsAgreeAt_four
    (polynomialsAgreeAt_of_hasDualMoments ℓ₀ (hasDualMoments_historyEventKernel ℓ₀ hap₀ events 4)
      (hasDualMoments_integrableRateHistoryKernel hT hintegrable ℓ₀ hap₀ 4) hmoments)
    source target score outcome case

/-- **An event history and an integrable rate history with equal moment sequences give equal
expected metrics.**  If a history of epochs, splits and pulses from `x₁` and a rate history with
integrable rates from `x₂` have equal propagated moments at every budget, every score and outcome
in the unit interval, and every binary endpoint, have the same expected squared correlation and
expected AUC in every deme under both.

Assumes: the rate coordinates are interval integrable on `[0, T]`, the propagated moments agree at
every budget, and the score and outcome take values in the unit interval. -/
theorem expectedMetrics_historyEvent_eq_integrableRateHistory (ℓ₀ : Locus)
    (hap₀ : FullHaplotype Locus Allele)
    (events : List ((NeutralRates Deme Locus Allele × ℝ≥0) ⊕ PulseMatrix Deme))
    {rates : ℝ → NeutralRates Deme Locus Allele} {T : ℝ} (hT : 0 ≤ T)
    (hintegrable : IntervalIntegrable (fun t ↦ neutralRateCoordinates (rates t)) volume 0 T)
    {x₁ x₂ : FrequencyState Deme Locus Allele}
    (hmoments : ∀ n : ℕ,
      historyEventPropagator (fun _ ↦ n) events *ᵥ budgetMomentFeature (fun _ ↦ n) x₁
        = integrableRateDualPropagator rates (fun _ ↦ n) hT hintegrable
            *ᵥ budgetMomentFeature (fun _ ↦ n) x₂)
    (deme : Deme) (score outcome : FullHaplotype Locus Allele → ℝ)
    (hscore0 : ∀ hap, 0 ≤ score hap) (hscore1 : ∀ hap, score hap ≤ 1)
    (houtcome0 : ∀ hap, 0 ≤ outcome hap) (houtcome1 : ∀ hap, outcome hap ≤ 1)
    (case : FullHaplotype Locus Allele → Bool) :
    expectedSquaredCorrelation (historyEventKernel ℓ₀ hap₀ events) x₁ deme score outcome
        = expectedSquaredCorrelation (integrableRateHistoryKernel rates ℓ₀ hap₀ hT hintegrable) x₂
            deme score outcome
      ∧ expectedAUC (historyEventKernel ℓ₀ hap₀ events) x₁ deme score case
        = expectedAUC (integrableRateHistoryKernel rates ℓ₀ hap₀ hT hintegrable) x₂ deme score
            case :=
  expectedMetrics_eq_of_polynomialsAgreeAt_all
    (fun n ↦ polynomialsAgreeAt_of_hasDualMoments ℓ₀
      (hasDualMoments_historyEventKernel ℓ₀ hap₀ events n)
      (hasDualMoments_integrableRateHistoryKernel hT hintegrable ℓ₀ hap₀ n) (hmoments n))
    deme score outcome case hscore0 hscore1 houtcome0 houtcome1

end

end Descent.Portability.EndToEndIntegrableRateHistory
