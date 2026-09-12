/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.NeutralKernelPanelLikelihood
import Descent.Portability.PartialHaplotypePulseKernel

assert_below Descent.Decision Descent.Program

/-!
# Neutral Markov kernels along a history with splits and admixture pulses

NOTE1 §4.2: splits and admixture pulses have finite substitution kernels because they only
reassign lineage parents.  `PartialHaplotypePulseKernel` proves the substitution on moment
vectors.  This module composes pulses with neutral epochs into one process law.

A pulse acts on a frequency state deterministically, `x'_i[h] = Σ_j A_ij x_j[h]`
(`pulsedState`), and the per-deme laws of the pulsed state are the pulsed laws
(`stateLaw_pulsedState`).  The map is continuous (`continuous_pulsedState`), so it defines a
Markov kernel (`pulseStateKernel`), whose expected configuration moments are the substitution
kernel applied to the initial moments (`integral_momentPolynomial_pulseStateKernel`).

Expected configuration moments compose under kernel composition by matrix product
(`integral_momentPolynomial_comp`).  An event of a history is an epoch of neutral dynamics with a
duration, or a pulse; each has a Markov kernel and a moment matrix (`eventKernel`,
`eventPropagator`, `integral_momentPolynomial_eventKernel`).  The history kernel runs the events in
chronological order (`historyEventKernel`, `isMarkovKernel_historyEventKernel`).  For every budget
its expected configuration moments are the chronological product of the epoch dual propagators
and pulse substitution kernels applied to the initial moments
(`integral_momentPolynomial_historyEventKernel`).  That chronological moment matrix is
substochastic (`historyEventPropagator_substochastic`), and the expected compiled report of an
independently sampled panel at the end of the history is the sum over genotypes of the readout
times the seed coordinate of that matrix applied to the initial moments
(`integral_panelReport_historyEventKernel`).

## Empirical status

None.  The bodies here are integrals of polynomials against compositions of Markov kernels,
products of supplied mixture weights, and matrix exponentials of supplied rates, so no measurement
can bear on them.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.NeutralPulseHistoryKernel

open MeasureTheory ProbabilityTheory MvPolynomial Descent.Coalescent PartialHaplotypeCarrier
  PartialHaplotypeDualGenerator PartialHaplotypeDualSemigroup NeutralFellerGenerator
  NeutralPolynomialSemigroup PartialHaplotypeMicroscopicApproximation PartialHaplotypePulseKernel
  NeutralMicroscopicEulerLimit NeutralKernelPanelLikelihood SubstochasticGeneratorSemigroup
  PartialHaplotypePanelLikelihood
open scoped Matrix NNReal

noncomputable section

variable {Deme Locus : Type*} {Allele : Locus → Type*}
variable [Fintype Deme] [DecidableEq Deme] [Fintype Locus] [DecidableEq Locus]
  [∀ ℓ, Fintype (Allele ℓ)] [∀ ℓ, DecidableEq (Allele ℓ)]

/-! ## A pulse on frequency states -/

/-- The frequency state after a pulse: deme `i` holds the mixture `Σ_j A i j · x_j`. -/
def pulsedState (pulse : PulseMatrix Deme) (x : FrequencyState Deme Locus Allele) :
    FrequencyState Deme Locus Allele :=
  ⟨fun c ↦ ∑ j, pulse.weight c.1 j * x.1 (j, c.2), by
    refine And.intro (fun c ↦ ?_) (fun i ↦ ?_)
    · exact Finset.sum_nonneg fun j _ ↦ mul_nonneg (pulse.weight_nonneg c.1 j) (x.2.1 (j, c.2))
    · show ∑ hap, ∑ j, pulse.weight i j * x.1 (j, hap) = 1
      rw [Finset.sum_comm]
      simp only [← Finset.mul_sum, x.2.2, mul_one]
      exact pulse.row_sum i⟩

/-- The per-deme laws of a pulsed state are the pulsed laws. -/
theorem stateLaw_pulsedState (pulse : PulseMatrix Deme) (x : FrequencyState Deme Locus Allele) :
    stateLaw (pulsedState pulse x) = pulsedLaw pulse (stateLaw x) :=
  rfl

/-- A pulse acts continuously on frequency states. -/
theorem continuous_pulsedState (pulse : PulseMatrix Deme) :
    Continuous (pulsedState (Locus := Locus) (Allele := Allele) pulse) :=
  (continuous_pi fun c ↦ continuous_finset_sum _ fun j _ ↦
    continuous_const.mul ((continuous_apply (j, c.2)).comp continuous_subtype_val)).subtype_mk
    fun x ↦ (pulsedState pulse x).2

/-- The Markov kernel of a pulse: the deterministic move to the pulsed state. -/
def pulseStateKernel (pulse : PulseMatrix Deme) :
    Kernel (FrequencyState Deme Locus Allele) (FrequencyState Deme Locus Allele) :=
  Kernel.deterministic (pulsedState pulse) (continuous_pulsedState pulse).measurable

/-- **A pulse on configuration moments, under the process law.**  The expected configuration
moments after a pulse are its substitution kernel applied to the moments of the initial state. -/
theorem integral_momentPolynomial_pulseStateKernel (pulse : PulseMatrix Deme)
    (capacity : Locus → ℕ) (x : FrequencyState Deme Locus Allele)
    (ξ : BudgetConfiguration Deme Locus Allele capacity) :
    ∫ y, polynomialFunction (momentPolynomial ξ.1) y ∂(pulseStateKernel pulse x)
      = (pulseKernel pulse capacity *ᵥ budgetMomentFeature capacity x) ξ := by
  rw [pulseStateKernel, Kernel.deterministic_apply, integral_dirac' _ _
    (polynomialFunction (momentPolynomial ξ.1)).continuous.stronglyMeasurable]
  have hx : budgetMomentFeature capacity x = fun η ↦ configurationMoment (stateLaw x) η.1 :=
    funext fun η ↦ eval_momentPolynomial (stateLaw x) η.1
  rw [hx, pulseKernel_mulVec_configurationMoment, ← stateLaw_pulsedState]
  exact eval_momentPolynomial (stateLaw (pulsedState pulse x)) ξ.1

/-! ## Composition along a history -/

/-- **Expected configuration moments compose by matrix product.**  If the expected configuration
moments under `κ` are `M` applied to the initial moments and under `η` are `N` applied to them,
then under `η ∘ₖ κ` (first `κ`, then `η`) they are `N M` applied to the initial moments. -/
theorem integral_momentPolynomial_comp (capacity : Locus → ℕ)
    (κ η : Kernel (FrequencyState Deme Locus Allele) (FrequencyState Deme Locus Allele))
    [IsMarkovKernel κ] [IsMarkovKernel η]
    (M N : Matrix (BudgetConfiguration Deme Locus Allele capacity)
      (BudgetConfiguration Deme Locus Allele capacity) ℝ)
    (hκ : ∀ (x : FrequencyState Deme Locus Allele)
      (ξ : BudgetConfiguration Deme Locus Allele capacity),
      ∫ y, polynomialFunction (momentPolynomial ξ.1) y ∂(κ x)
        = (M *ᵥ budgetMomentFeature capacity x) ξ)
    (hη : ∀ (x : FrequencyState Deme Locus Allele)
      (ξ : BudgetConfiguration Deme Locus Allele capacity),
      ∫ y, polynomialFunction (momentPolynomial ξ.1) y ∂(η x)
        = (N *ᵥ budgetMomentFeature capacity x) ξ)
    (x : FrequencyState Deme Locus Allele) (ξ : BudgetConfiguration Deme Locus Allele capacity) :
    ∫ y, polynomialFunction (momentPolynomial ξ.1) y ∂((η ∘ₖ κ) x)
      = ((N * M) *ᵥ budgetMomentFeature capacity x) ξ := by
  have hint : ∀ ζ : BudgetConfiguration Deme Locus Allele capacity,
      Integrable (fun y ↦ polynomialFunction (momentPolynomial ζ.1) y) (κ x) := fun ζ ↦
    (BoundedContinuousFunction.mkOfCompact
      (polynomialFunction (momentPolynomial ζ.1))).integrable _
  have hcomp : Integrable (fun y ↦ polynomialFunction (momentPolynomial ξ.1) y) ((η ∘ₖ κ) x) :=
    (BoundedContinuousFunction.mkOfCompact
      (polynomialFunction (momentPolynomial ξ.1))).integrable _
  rw [Kernel.integral_comp hcomp]
  calc ∫ y, ∫ z, polynomialFunction (momentPolynomial ξ.1) z ∂(η y) ∂(κ x)
      = ∫ y, ∑ ζ, N ξ ζ * polynomialFunction (momentPolynomial ζ.1) y ∂(κ x) := by
        congr 1
        funext y
        rw [hη y ξ]
        simp only [Matrix.mulVec, dotProduct]
        rfl
    _ = ∑ ζ, N ξ ζ * ∫ y, polynomialFunction (momentPolynomial ζ.1) y ∂(κ x) := by
        rw [integral_finset_sum Finset.univ fun ζ _ ↦ (hint ζ).const_mul (N ξ ζ)]
        simp only [integral_const_mul]
    _ = _ := by
        simp only [hκ, ← Matrix.mulVec_mulVec]
        simp only [Matrix.mulVec, dotProduct]

/-- The Markov kernel of one event of a history: the neutral Markov kernel of an epoch, or the
kernel of a pulse. -/
def eventKernel (ℓ₀ : Locus) (hap₀ : FullHaplotype Locus Allele) :
    (NeutralRates Deme Locus Allele × ℝ≥0) ⊕ PulseMatrix Deme →
      Kernel (FrequencyState Deme Locus Allele) (FrequencyState Deme Locus Allele)
  | Sum.inl epoch => neutralMarkovKernel epoch.1 ℓ₀ hap₀ epoch.2
  | Sum.inr pulse => pulseStateKernel pulse

/-- The moment matrix of one event: the dual propagator of an epoch, or the substitution kernel
of a pulse. -/
def eventPropagator (capacity : Locus → ℕ) :
    (NeutralRates Deme Locus Allele × ℝ≥0) ⊕ PulseMatrix Deme →
      Matrix (BudgetConfiguration Deme Locus Allele capacity)
        (BudgetConfiguration Deme Locus Allele capacity) ℝ
  | Sum.inl epoch => matrixExponential (dualGenerator epoch.1 capacity) epoch.2
  | Sum.inr pulse => pulseKernel pulse capacity

/-- The kernel of an event is a Markov kernel. -/
theorem isMarkovKernel_eventKernel (ℓ₀ : Locus) (hap₀ : FullHaplotype Locus Allele) :
    ∀ event : (NeutralRates Deme Locus Allele × ℝ≥0) ⊕ PulseMatrix Deme,
      IsMarkovKernel (eventKernel ℓ₀ hap₀ event)
  | Sum.inl epoch => isMarkovKernel_neutralMarkovKernel epoch.1 ℓ₀ hap₀ epoch.2
  | Sum.inr pulse => by
    rw [eventKernel, pulseStateKernel]
    infer_instance

/-- The expected configuration moments after an event are its moment matrix applied to the
moments of the initial state. -/
theorem integral_momentPolynomial_eventKernel (ℓ₀ : Locus) (hap₀ : FullHaplotype Locus Allele)
    (capacity : Locus → ℕ) :
    ∀ (event : (NeutralRates Deme Locus Allele × ℝ≥0) ⊕ PulseMatrix Deme)
      (x : FrequencyState Deme Locus Allele) (ξ : BudgetConfiguration Deme Locus Allele capacity),
      ∫ y, polynomialFunction (momentPolynomial ξ.1) y ∂(eventKernel ℓ₀ hap₀ event x)
        = (eventPropagator capacity event *ᵥ budgetMomentFeature capacity x) ξ
  | Sum.inl epoch, x, ξ =>
      integral_momentPolynomial_neutralMarkovKernel epoch.1 ℓ₀ hap₀ capacity epoch.2 x ξ
  | Sum.inr pulse, x, ξ => integral_momentPolynomial_pulseStateKernel pulse capacity x ξ

/-- **The history kernel with pulses.**  The kernels of the events of a history, run in
chronological order: first the head event, then the rest of the history. -/
def historyEventKernel (ℓ₀ : Locus) (hap₀ : FullHaplotype Locus Allele) :
    List ((NeutralRates Deme Locus Allele × ℝ≥0) ⊕ PulseMatrix Deme) →
      Kernel (FrequencyState Deme Locus Allele) (FrequencyState Deme Locus Allele)
  | [] => Kernel.id
  | event :: rest => historyEventKernel ℓ₀ hap₀ rest ∘ₖ eventKernel ℓ₀ hap₀ event

/-- The chronological product of the moment matrices of the events of a history. -/
def historyEventPropagator (capacity : Locus → ℕ) :
    List ((NeutralRates Deme Locus Allele × ℝ≥0) ⊕ PulseMatrix Deme) →
      Matrix (BudgetConfiguration Deme Locus Allele capacity)
        (BudgetConfiguration Deme Locus Allele capacity) ℝ
  | [] => 1
  | event :: rest => historyEventPropagator capacity rest * eventPropagator capacity event

/-- The history kernel with pulses is a Markov kernel. -/
theorem isMarkovKernel_historyEventKernel (ℓ₀ : Locus) (hap₀ : FullHaplotype Locus Allele) :
    ∀ events : List ((NeutralRates Deme Locus Allele × ℝ≥0) ⊕ PulseMatrix Deme),
      IsMarkovKernel (historyEventKernel ℓ₀ hap₀ events)
  | [] => by
    rw [historyEventKernel]
    infer_instance
  | event :: rest => by
    haveI := isMarkovKernel_historyEventKernel ℓ₀ hap₀ rest
    haveI := isMarkovKernel_eventKernel ℓ₀ hap₀ event
    rw [historyEventKernel]
    infer_instance

/-- **NOTE1 §4.2, a history with splits and pulses under the process law.**  For every budget,
the expected configuration moments under the history kernel are the chronological product of the
epoch dual propagators and pulse substitution kernels applied to the moments of the initial
state. -/
theorem integral_momentPolynomial_historyEventKernel (ℓ₀ : Locus)
    (hap₀ : FullHaplotype Locus Allele) (capacity : Locus → ℕ) :
    ∀ (events : List ((NeutralRates Deme Locus Allele × ℝ≥0) ⊕ PulseMatrix Deme))
      (x : FrequencyState Deme Locus Allele) (ξ : BudgetConfiguration Deme Locus Allele capacity),
      ∫ y, polynomialFunction (momentPolynomial ξ.1) y ∂(historyEventKernel ℓ₀ hap₀ events x)
        = (historyEventPropagator capacity events *ᵥ budgetMomentFeature capacity x) ξ
  | [], x, ξ => by
    rw [historyEventKernel, Kernel.id_apply, integral_dirac' _ _
      (polynomialFunction (momentPolynomial ξ.1)).continuous.stronglyMeasurable]
    simp only [historyEventPropagator, Matrix.one_mulVec]
    rfl
  | event :: rest, x, ξ => by
    haveI := isMarkovKernel_historyEventKernel ℓ₀ hap₀ rest
    haveI := isMarkovKernel_eventKernel ℓ₀ hap₀ event
    rw [historyEventKernel, historyEventPropagator]
    exact integral_momentPolynomial_comp capacity _ _ _ _
      (integral_momentPolynomial_eventKernel ℓ₀ hap₀ capacity event)
      (integral_momentPolynomial_historyEventKernel ℓ₀ hap₀ capacity rest) x ξ

/-- The moment matrix of an event is substochastic. -/
theorem eventPropagator_substochastic (capacity : Locus → ℕ) :
    ∀ event : (NeutralRates Deme Locus Allele × ℝ≥0) ⊕ PulseMatrix Deme,
      SubstochasticMatrix (eventPropagator capacity event)
  | Sum.inl epoch => dualPropagator_substochastic epoch.1 capacity epoch.2 (NNReal.coe_nonneg _)
  | Sum.inr pulse => pulseKernel_substochastic (Allele := Allele) pulse capacity

/-- The chronological moment matrix of a history with splits and pulses is substochastic. -/
theorem historyEventPropagator_substochastic (capacity : Locus → ℕ) :
    ∀ events : List ((NeutralRates Deme Locus Allele × ℝ≥0) ⊕ PulseMatrix Deme),
      SubstochasticMatrix (historyEventPropagator capacity events)
  | [] => substochastic_one
  | event :: rest => substochastic_mul (historyEventPropagator_substochastic capacity rest)
      (eventPropagator_substochastic capacity event)

variable {Sample Report : Type*} [Fintype Sample] [DecidableEq Sample] [Fintype Report]

/-- **NOTE1 (20) with (22) along a history with splits and pulses, under the process law.**  The
expected compiled report of an independently sampled panel at the end of a history of epochs and
pulses, started at a frequency state, is the sum over panel genotypes of the conditional readout
times the seed coordinate of the chronological moment matrix applied to the initial moments. -/
theorem integral_panelReport_historyEventKernel (ℓ₀ : Locus)
    (hap₀ : FullHaplotype Locus Allele) (deme : Sample → Deme)
    (report : (Sample → FullHaplotype Locus Allele) → FiniteReportLaw Report)
    (metric : Report → ℝ)
    (events : List ((NeutralRates Deme Locus Allele × ℝ≥0) ⊕ PulseMatrix Deme))
    (x0 : FrequencyState Deme Locus Allele) :
    ∫ y, ((FiniteGeneticTransition.piLaw fun draw ↦ stateLaw y (deme draw)).bind
        report).expectation metric ∂(historyEventKernel ℓ₀ hap₀ events x0)
      = ∑ genotype : Sample → FullHaplotype Locus Allele,
          (report genotype).expectation metric *
            (historyEventPropagator (fun _ ↦ Fintype.card Sample) events
              *ᵥ budgetMomentFeature (fun _ ↦ Fintype.card Sample) x0)
              (seedState deme genotype ℓ₀) := by
  haveI := isMarkovKernel_historyEventKernel ℓ₀ hap₀ events
  have hint : ∀ genotype : Sample → FullHaplotype Locus Allele,
      Integrable (fun y ↦ (report genotype).expectation metric
        * polynomialFunction (momentPolynomial (seedState deme genotype ℓ₀).1) y)
        (historyEventKernel ℓ₀ hap₀ events x0) := fun genotype ↦
    Integrable.const_mul ((BoundedContinuousFunction.mkOfCompact
      (polynomialFunction (momentPolynomial (seedState deme genotype ℓ₀).1))).integrable _) _
  calc ∫ y, ((FiniteGeneticTransition.piLaw fun draw ↦ stateLaw y (deme draw)).bind
          report).expectation metric ∂(historyEventKernel ℓ₀ hap₀ events x0)
      = ∫ y, ∑ genotype : Sample → FullHaplotype Locus Allele,
          (report genotype).expectation metric
            * polynomialFunction (momentPolynomial (seedState deme genotype ℓ₀).1) y
          ∂(historyEventKernel ℓ₀ hap₀ events x0) := by
        congr 1
        funext y
        exact panelReport_eq_sum_seedMoment deme report metric ℓ₀ y
    _ = ∑ genotype : Sample → FullHaplotype Locus Allele,
          ∫ y, (report genotype).expectation metric
            * polynomialFunction (momentPolynomial (seedState deme genotype ℓ₀).1) y
          ∂(historyEventKernel ℓ₀ hap₀ events x0) :=
        integral_finset_sum Finset.univ fun genotype _ ↦ hint genotype
    _ = _ := by
        refine Finset.sum_congr rfl fun genotype _ ↦ ?_
        rw [integral_const_mul, integral_momentPolynomial_historyEventKernel]

end

end Descent.Portability.NeutralPulseHistoryKernel
