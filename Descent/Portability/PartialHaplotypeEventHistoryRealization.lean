/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.PartialHaplotypeHistoryRealization
import Descent.Portability.PartialHaplotypePulseKernel

assert_below Descent.Decision Descent.Program

/-!
# NOTE1 (20) along a history of epochs, splits and admixture pulses, realized

NOTE1 §4.2 composes a demographic history in chronological moment order, and its last paragraph
gives splits and admixture pulses finite substitution kernels on the partial-haplotype carrier
(`PartialHaplotypePulseKernel.pulseKernel`).  `PartialHaplotypeHistoryRealization` realizes the
dual moments along a history of constant-rate epochs.  This module adds the splits and pulses.

A history is a chronological list of events (`HaplotypeHistoryEvent`): a constant-rate epoch of
the neutral model, or a pulse.  The split of a daughter deme from a parent deme is the pulse
`PulseMatrix.split` (`HaplotypeHistoryEvent.demeSplit`).  Its kernel sends every configuration,
with probability one, to the configuration whose daughter carriers are moved to the parent, so it
acts on configuration moments by relabelling (`pulseKernel_split_mulVec`).  The chronological
propagator multiplies the epoch exponentials and the pulse kernels, latest event leftmost
(`eventPropagator`); on a history of epochs alone it is
`PartialHaplotypeDualSemigroup.historyPropagator` (`eventPropagator_ofEpoch`).

Realizability.  A pulse keeps the realization body of the budget-moment feature invariant by
transforming the witness: every support point of a finitely supported law is replaced by its
pulsed state (`pulsedState`), whose budget moments are the pulse kernel applied to those of the
point (`budgetMomentFeature_pulsedState`), so the transformed law has the kernel's moments
(`pulseKernel_mulVec_mem_realizationBody`).  An epoch keeps the body by NOTE1 Theorem 1, so every
event does (`eventMatrix_mulVec_mem_realizationBody`), the chronological product does
(`eventPropagator_mulVec_mem_realizationBody`), and a finitely supported law has the history's
moments at its end (`exists_eventHistoryLaw`).

The forward equation.  A pulse is instantaneous, so an expectation family along the history is
indexed by a segment, the number of pulses passed, and a time (`ForwardOnEventHistory`): on every
epoch the current segment obeys the forward moment equation of that epoch, and at every pulse the
next segment starts with the expected moments of the pulsed laws.  Under that equation the
expected moments at the end of the history are the chronological propagator applied to the
initial moments (`expectedMomentVector_eventHistory`).  The moment vectors along the history
(`eventMoments`) are realizable, so Dirac mixtures at realized laws form an expectation family
with exactly those moments (`eventRealizedExpectation`), which obeys the forward equation with no
hypothesis (`forwardOnEventHistory_eventRealizedExpectation`).  At the end of the history its
expected moments are the chronological product of the epoch propagators and the pulse kernels
applied to the initial moments (`expectedMomentVector_eventHistory_realized`).

Scope.  A split acts on a fixed set of demes: the daughter deme is a label before the split, and
the split replaces its ancestry by the parent's.  As in `PartialHaplotypeHistoryRealization`, the
realized family matches the history on the budget-respecting moments of one fixed budget; it is
not shown to be the marginal law of one process across budgets.

## Empirical status

None.  The bodies here are convex geometry, matrix algebra and calculus of matrix exponentials:
invariance of a convex hull under matrix exponentials and substitution kernels, finite mixtures
read off it, and derivatives of exponential orbits, so no measurement can bear on them.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.PartialHaplotypeEventHistoryRealization

open PartialHaplotypeCarrier PartialHaplotypeDualGenerator PartialHaplotypeDualSemigroup
open PartialHaplotypeMicroscopicApproximation PartialHaplotypeHistoryRealization
open PartialHaplotypePulseKernel NeutralFellerGenerator
open FiniteMixtureKernel RealizationBody KernelRealizationPreservation
open SubstochasticGeneratorSemigroup Descent.Coalescent Descent.Foundations MvPolynomial

/-- An event of a demographic history: a constant-rate epoch of the neutral model with its
duration, or an admixture pulse with its parent-deme weights. -/
inductive HaplotypeHistoryEvent (Deme Locus : Type*) (Allele : Locus → Type*) [Fintype Deme] where
  /-- A constant-rate epoch: the neutral rates and the duration. -/
  | epoch (rates : NeutralRates Deme Locus Allele) (time : ℝ)
  /-- An admixture pulse. -/
  | pulse (weights : PulseMatrix Deme)

variable {Deme Locus : Type*} {Allele : Locus → Type*}

namespace HaplotypeHistoryEvent

variable [Fintype Deme]

/-- The time an event takes: an epoch's duration, and zero for a pulse. -/
def duration : HaplotypeHistoryEvent Deme Locus Allele → ℝ
  | HaplotypeHistoryEvent.epoch _ time => time
  | HaplotypeHistoryEvent.pulse _ => 0

/-- A constant-rate epoch of `PartialHaplotypeDualSemigroup`, read as an event. -/
def ofEpoch (step : NeutralRates Deme Locus Allele × ℝ) : HaplotypeHistoryEvent Deme Locus Allele :=
  HaplotypeHistoryEvent.epoch step.1 step.2

/-- The split of a daughter deme from a parent deme, as an event: the pulse whose daughter row is
the point mass at the parent. -/
def demeSplit [DecidableEq Deme] (daughter parent : Deme) :
    HaplotypeHistoryEvent Deme Locus Allele :=
  HaplotypeHistoryEvent.pulse (PulseMatrix.split daughter parent)

end HaplotypeHistoryEvent

variable [Fintype Deme] [DecidableEq Deme] [Fintype Locus] [DecidableEq Locus]
  [∀ ℓ, Fintype (Allele ℓ)] [∀ ℓ, DecidableEq (Allele ℓ)]

noncomputable section

/-! ## A split relabels the daughter's carriers -/

/-- The deme from which a lineage sampled in deme `i` descends across the split of `daughter`
from `parent`. -/
def splitParent (daughter parent i : Deme) : Deme :=
  if i = daughter then parent else i

/-- The weights of the split pulse are the point masses at `splitParent`. -/
theorem split_weight (daughter parent i j : Deme) :
    (PulseMatrix.split daughter parent).weight i j
      = if j = splitParent daughter parent i then 1 else 0 := by
  show (if i = daughter then (if j = parent then (1 : ℝ) else 0) else (if i = j then 1 else 0))
      = if j = (if i = daughter then parent else i) then 1 else 0
  by_cases hi : i = daughter
  · rw [if_pos hi, if_pos hi]
  · rw [if_neg hi, if_neg hi]
    by_cases hj : j = i
    · rw [if_pos hj.symm, if_pos hj]
    · rw [if_neg (Ne.symm hj), if_neg hj]

/-- **A split relabels.**  The kernel of the split of `daughter` from `parent` sends a
configuration, with probability one, to the configuration whose daughter carriers are moved to the
parent, so on a table of values it is the relabelling. -/
theorem pulseKernel_split_mulVec (daughter parent : Deme) (capacity : Locus → ℕ)
    (value : Multiset (PartialType Deme Locus Allele) → ℝ)
    (ξ : BudgetConfiguration Deme Locus Allele capacity) :
    (pulseKernel (PulseMatrix.split daughter parent) capacity).mulVec (fun η ↦ value η.1) ξ
      = value (ξ.1.map fun τ ↦ migrate τ (splitParent daughter parent τ.deme)) := by
  rw [pulseKernel_mulVec,
    Finset.sum_eq_single fun k ↦ splitParent daughter parent (ξ.1.toList.get k).deme]
  · have hweight : choiceWeight (PulseMatrix.split daughter parent) ξ.1.toList
        (fun k ↦ splitParent daughter parent (ξ.1.toList.get k).deme) = 1 :=
      Finset.prod_eq_one fun k _ ↦ by
        rw [split_weight]
        exact if_pos rfl
    have hrelabel : relabelCarriers ξ.1.toList
        (fun k ↦ splitParent daughter parent (ξ.1.toList.get k).deme)
          = ξ.1.map fun τ ↦ migrate τ (splitParent daughter parent τ.deme) := by
      calc relabelCarriers ξ.1.toList
            (fun k ↦ splitParent daughter parent (ξ.1.toList.get k).deme)
          = (Finset.univ.val.map ξ.1.toList.get).map
              fun τ ↦ migrate τ (splitParent daughter parent τ.deme) := by
            rw [Multiset.map_map]
            rfl
        _ = ξ.1.map fun τ ↦ migrate τ (splitParent daughter parent τ.deme) := by
            rw [← carriers_eq_map_get, Multiset.coe_toList]
    rw [hweight, one_mul, hrelabel]
  · intro choice _ hne
    obtain ⟨k, hk⟩ := Function.ne_iff.mp hne
    have hzero : choiceWeight (PulseMatrix.split daughter parent) ξ.1.toList choice = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ k) (by
        rw [split_weight]
        exact if_neg hk)
    rw [hzero, zero_mul]
  · intro hnot
    exact absurd (Finset.mem_univ _) hnot

/-! ## A pulse transforms the witness -/

/-- The population state after a pulse: the haplotype frequencies of deme `i` are the
pulse-weighted average of the frequencies of the parent demes. -/
def pulsedState (weights : PulseMatrix Deme) (x : FrequencyState Deme Locus Allele) :
    FrequencyState Deme Locus Allele :=
  ⟨fun coordinate ↦ ∑ j, weights.weight coordinate.1 j * x.1 (j, coordinate.2),
    fun coordinate ↦ Finset.sum_nonneg fun j _ ↦
      mul_nonneg (weights.weight_nonneg coordinate.1 j) (x.2.1 (j, coordinate.2)),
    fun i ↦ by
      show ∑ hap, ∑ j, weights.weight i j * x.1 (j, hap) = 1
      rw [Finset.sum_comm]
      simp only [← Finset.mul_sum, x.2.2, mul_one]
      exact weights.row_sum i⟩

/-- The per-deme haplotype laws of the pulsed state are the pulsed laws. -/
theorem stateLaw_pulsedState (weights : PulseMatrix Deme) (x : FrequencyState Deme Locus Allele) :
    stateLaw (pulsedState weights x) = pulsedLaw weights (stateLaw x) :=
  rfl

/-- The budget moments of the pulsed state are the pulse kernel applied to the budget moments of
the state. -/
theorem budgetMomentFeature_pulsedState (weights : PulseMatrix Deme) (capacity : Locus → ℕ)
    (x : FrequencyState Deme Locus Allele) :
    budgetMomentFeature capacity (pulsedState weights x)
      = (pulseKernel weights capacity).mulVec (budgetMomentFeature capacity x) := by
  have hfeature : ∀ y : FrequencyState Deme Locus Allele,
      budgetMomentFeature capacity y = fun η ↦ configurationMoment (stateLaw y) η.1 :=
    fun y ↦ funext fun η ↦ eval_momentPolynomial (stateLaw y) η.1
  funext ξ
  rw [hfeature x, pulseKernel_mulVec_configurationMoment, ← stateLaw_pulsedState, hfeature]

/-- **A pulse keeps moment vectors realizable.**  Replacing every support point of a finitely
supported law by its pulsed state gives a law whose budget moments are the pulse kernel applied to
the law's. -/
theorem pulseKernel_mulVec_mem_realizationBody (weights : PulseMatrix Deme)
    (capacity : Locus → ℕ) (v : BudgetConfiguration Deme Locus Allele capacity → ℝ)
    (hv : v ∈ realizationBody (budgetMomentFeature (Deme := Deme) (Locus := Locus)
      (Allele := Allele) capacity)) :
    (pulseKernel weights capacity).mulVec v ∈
      realizationBody (budgetMomentFeature (Deme := Deme) (Locus := Locus) (Allele := Allele)
        capacity) := by
  obtain ⟨Ω, hΩ, p, point, hp, hsum, rfl⟩ := (mem_realizationBody_iff _ v).mp hv
  refine (mem_realizationBody_iff _ _).mpr
    ⟨Ω, hΩ, p, fun ω ↦ pulsedState weights (point ω), hp, hsum, ?_⟩
  funext ξ
  simp only [featureVector_apply, budgetMomentFeature_pulsedState, Matrix.mulVec, dotProduct,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ ↦ Finset.sum_congr rfl fun _ _ ↦ by ring

/-! ## Histories of events -/

/-- The moment matrix of one event: an epoch's dual propagator, or a pulse's substitution
kernel. -/
def eventMatrix (capacity : Locus → ℕ) :
    HaplotypeHistoryEvent Deme Locus Allele →
      Matrix (BudgetConfiguration Deme Locus Allele capacity)
        (BudgetConfiguration Deme Locus Allele capacity) ℝ
  | HaplotypeHistoryEvent.epoch rates time => matrixExponential (dualGenerator rates capacity) time
  | HaplotypeHistoryEvent.pulse weights => pulseKernel weights capacity

/-- The chronological propagator of a history of events: the product of the event matrices, the
latest event leftmost. -/
def eventPropagator (capacity : Locus → ℕ) :
    List (HaplotypeHistoryEvent Deme Locus Allele) →
      Matrix (BudgetConfiguration Deme Locus Allele capacity)
        (BudgetConfiguration Deme Locus Allele capacity) ℝ
  | [] => 1
  | event :: rest => eventPropagator capacity rest * eventMatrix capacity event

/-- The number of pulses of a history of events. -/
def eventPulseCount : List (HaplotypeHistoryEvent Deme Locus Allele) → ℕ
  | [] => 0
  | HaplotypeHistoryEvent.epoch _ _ :: rest => eventPulseCount rest
  | HaplotypeHistoryEvent.pulse _ :: rest => 1 + eventPulseCount rest

/-- The total duration of a history of events. -/
def eventHistoryDuration : List (HaplotypeHistoryEvent Deme Locus Allele) → ℝ
  | [] => 0
  | event :: rest => event.duration + eventHistoryDuration rest

/-- On a history of epochs alone, the event propagator is the chronological propagator of
`PartialHaplotypeDualSemigroup`. -/
theorem eventPropagator_ofEpoch (capacity : Locus → ℕ) :
    ∀ epochs : List (NeutralRates Deme Locus Allele × ℝ),
      eventPropagator capacity (epochs.map HaplotypeHistoryEvent.ofEpoch)
        = historyPropagator capacity epochs
  | [] => rfl
  | epoch :: rest =>
    congrArg (· * matrixExponential (dualGenerator epoch.1 capacity) epoch.2)
      (eventPropagator_ofEpoch capacity rest)

/-- Every event with a nonnegative duration keeps moment vectors realizable. -/
theorem eventMatrix_mulVec_mem_realizationBody (capacity : Locus → ℕ)
    (event : HaplotypeHistoryEvent Deme Locus Allele) (hevent : 0 ≤ event.duration)
    (v : BudgetConfiguration Deme Locus Allele capacity → ℝ)
    (hv : v ∈ realizationBody (budgetMomentFeature (Deme := Deme) (Locus := Locus)
      (Allele := Allele) capacity)) :
    (eventMatrix capacity event).mulVec v ∈
      realizationBody (budgetMomentFeature (Deme := Deme) (Locus := Locus) (Allele := Allele)
        capacity) := by
  cases event with
  | epoch rates time =>
    exact exp_mulVec_mem_realizationBody _ _ (neutralMicroscopicApproximation rates capacity)
      (isClosed_realizationBody _ (continuous_budgetMomentFeature capacity)) time hevent v hv
  | pulse weights => exact pulseKernel_mulVec_mem_realizationBody weights capacity v hv

/-- **Every history of events keeps moment vectors realizable.**  The chronological product of the
epoch dual propagators and the pulse kernels, with nonnegative durations, maps the realization
body of the budget-moment feature into itself. -/
theorem eventPropagator_mulVec_mem_realizationBody (capacity : Locus → ℕ) :
    ∀ events : List (HaplotypeHistoryEvent Deme Locus Allele),
      (∀ event ∈ events, 0 ≤ event.duration) →
      ∀ v : BudgetConfiguration Deme Locus Allele capacity → ℝ,
        v ∈ realizationBody (budgetMomentFeature (Deme := Deme) (Locus := Locus)
          (Allele := Allele) capacity) →
        (eventPropagator capacity events).mulVec v ∈
          realizationBody (budgetMomentFeature (Deme := Deme) (Locus := Locus)
            (Allele := Allele) capacity)
  | [], _, v, hv => by simpa [eventPropagator] using hv
  | event :: rest, hdurations, v, hv => by
    rw [eventPropagator, ← Matrix.mulVec_mulVec]
    exact eventPropagator_mulVec_mem_realizationBody capacity rest
      (fun other hother ↦ hdurations other (List.mem_cons.mpr (Or.inr hother))) _
      (eventMatrix_mulVec_mem_realizationBody capacity event
        (hdurations event (List.mem_cons.mpr (Or.inl rfl))) v hv)

/-- **NOTE1 (20) along a history of epochs, splits and pulses, realized at its end.**  For every
chronological history of events with nonnegative durations and every initial population state,
some finitely supported law on population states has, at every budget-respecting configuration,
the expected moment given by the chronological propagator applied to the initial moments. -/
theorem exists_eventHistoryLaw (capacity : Locus → ℕ)
    (events : List (HaplotypeHistoryEvent Deme Locus Allele))
    (hdurations : ∀ event ∈ events, 0 ≤ event.duration) (x0 : FrequencyState Deme Locus Allele) :
    ∃ p : Fin (Fintype.card (BudgetConfiguration Deme Locus Allele capacity) + 1) → ℝ,
      ∃ point : Fin (Fintype.card (BudgetConfiguration Deme Locus Allele capacity) + 1)
          → FrequencyState Deme Locus Allele,
        (∀ k, 0 ≤ p k) ∧ ∑ k, p k = 1
          ∧ featureVector p point (budgetMomentFeature capacity)
            = (eventPropagator capacity events).mulVec (budgetMomentFeature capacity x0) :=
  exists_law_of_mem_realizationBody _ _
    (eventPropagator_mulVec_mem_realizationBody capacity events hdurations _
      (mem_realizationBody_of_range _ x0))

/-! ## The forward equation along a history of events -/

/-- The forward moment equation along a history of events, for an expectation family indexed by a
segment, the number of pulses passed, and a time.  On every epoch, from where the previous event
ended, the current segment obeys the forward moment equation of that epoch (`ForwardOnHistory` of
the one epoch); at every pulse the next segment starts with the expected moments of the pulsed
laws of the segment before.

Assumes: the expectation family is the moment table of a process run through the events in
chronological order, a new segment starting at every pulse. -/
def ForwardOnEventHistory (capacity : Locus → ℕ)
    (expectationAt :
      ℕ → ℝ → ExpFunctional (Deme → FiniteReportLaw (FullHaplotype Locus Allele))) :
    List (HaplotypeHistoryEvent Deme Locus Allele) → ℕ → ℝ → Prop
  | [], _, _ => True
  | HaplotypeHistoryEvent.epoch rates time :: rest, segment, start =>
      ForwardOnHistory capacity (expectationAt segment) [(rates, time)] start
        ∧ ForwardOnEventHistory capacity expectationAt rest segment (start + time)
  | HaplotypeHistoryEvent.pulse weights :: rest, segment, start =>
      (∀ ξ : BudgetConfiguration Deme Locus Allele capacity,
        (expectationAt (segment + 1) start fun law ↦ configurationMoment law ξ.1)
          = expectationAt segment start fun law ↦ configurationMoment (pulsedLaw weights law) ξ.1)
        ∧ ForwardOnEventHistory capacity expectationAt rest (segment + 1) start

/-- The empty history carries no forward obligation, so `ForwardOnEventHistory` is inhabited. -/
theorem forwardOnEventHistory_nil (capacity : Locus → ℕ)
    (expectationAt :
      ℕ → ℝ → ExpFunctional (Deme → FiniteReportLaw (FullHaplotype Locus Allele)))
    (segment : ℕ) (start : ℝ) : ForwardOnEventHistory capacity expectationAt [] segment start :=
  trivial

/-- **Chronological composition of NOTE1 (20) with pulses.**  Along a history of events with
nonnegative durations that obeys the forward moment equation, the expected moment vector of the
last segment at the end of the history is the chronological propagator applied to the expected
moment vector of the first segment at the start. -/
theorem expectedMomentVector_eventHistory (capacity : Locus → ℕ)
    (expectationAt :
      ℕ → ℝ → ExpFunctional (Deme → FiniteReportLaw (FullHaplotype Locus Allele))) :
    ∀ (events : List (HaplotypeHistoryEvent Deme Locus Allele)) (segment : ℕ) (start : ℝ),
      (∀ event ∈ events, 0 ≤ event.duration) →
      ForwardOnEventHistory capacity expectationAt events segment start →
      expectedMomentVector capacity (expectationAt (segment + eventPulseCount events))
          (start + eventHistoryDuration events)
        = (eventPropagator capacity events).mulVec
            (expectedMomentVector capacity (expectationAt segment) start)
  | [], segment, start, _, _ => by
    simp [eventPulseCount, eventHistoryDuration, eventPropagator]
  | HaplotypeHistoryEvent.epoch rates time :: rest, segment, start, hdurations, hforward => by
    have htime : 0 ≤ time := hdurations _ (List.mem_cons.mpr (Or.inl rfl))
    have hfirst := expectedMomentVector_epoch rates capacity (expectationAt segment) start
      (start + time) (by linarith) hforward.1.1.1 hforward.1.1.2
    rw [add_sub_cancel_left] at hfirst
    have hrest := expectedMomentVector_eventHistory capacity expectationAt rest segment
      (start + time) (fun other hother ↦ hdurations other (List.mem_cons.mpr (Or.inr hother)))
      hforward.2
    simp only [eventPulseCount, eventHistoryDuration, HaplotypeHistoryEvent.duration,
      eventPropagator, eventMatrix]
    rw [← add_assoc, hrest, ← Matrix.mulVec_mulVec, hfirst]
  | HaplotypeHistoryEvent.pulse weights :: rest, segment, start, hdurations, hforward => by
    have hjump : expectedMomentVector capacity (expectationAt (segment + 1)) start
        = (pulseKernel weights capacity).mulVec
            (expectedMomentVector capacity (expectationAt segment) start) :=
      funext fun ξ ↦ (hforward.1 ξ).trans
        (pulseKernel_mulVec_expectedMoment weights capacity (expectationAt segment start) ξ)
    have hrest := expectedMomentVector_eventHistory capacity expectationAt rest (segment + 1)
      start (fun other hother ↦ hdurations other (List.mem_cons.mpr (Or.inr hother))) hforward.2
    simp only [eventPulseCount, eventHistoryDuration, HaplotypeHistoryEvent.duration, zero_add,
      eventPropagator, eventMatrix]
    rw [← add_assoc, hrest, ← Matrix.mulVec_mulVec, hjump]

/-! ## One expectation family along the whole history -/

/-- The weights and support points of a finitely supported law on population states whose budget
moments are a given realizable vector. -/
def realizableLaw (capacity : Locus → ℕ) (v : BudgetConfiguration Deme Locus Allele capacity → ℝ)
    (hv : v ∈ realizationBody (budgetMomentFeature (Deme := Deme) (Locus := Locus)
      (Allele := Allele) capacity)) :
    (Fin (Fintype.card (BudgetConfiguration Deme Locus Allele capacity) + 1) → ℝ)
      × (Fin (Fintype.card (BudgetConfiguration Deme Locus Allele capacity) + 1)
        → FrequencyState Deme Locus Allele) :=
  (Classical.choose (exists_law_of_mem_realizationBody _ v hv),
    Classical.choose (Classical.choose_spec (exists_law_of_mem_realizationBody _ v hv)))

/-- The realizable law is a probability law with the given budget moments. -/
theorem realizableLaw_spec (capacity : Locus → ℕ)
    (v : BudgetConfiguration Deme Locus Allele capacity → ℝ)
    (hv : v ∈ realizationBody (budgetMomentFeature (Deme := Deme) (Locus := Locus)
      (Allele := Allele) capacity)) :
    (∀ k, 0 ≤ (realizableLaw capacity v hv).1 k) ∧ ∑ k, (realizableLaw capacity v hv).1 k = 1
      ∧ featureVector (realizableLaw capacity v hv).1 (realizableLaw capacity v hv).2
          (budgetMomentFeature capacity) = v :=
  Classical.choose_spec (Classical.choose_spec (exists_law_of_mem_realizationBody _ v hv))

/-- The Dirac mixture at the realizable law of a realizable vector. -/
def realizableExpectation (capacity : Locus → ℕ)
    (v : BudgetConfiguration Deme Locus Allele capacity → ℝ)
    (hv : v ∈ realizationBody (budgetMomentFeature (Deme := Deme) (Locus := Locus)
      (Allele := Allele) capacity)) :
    ExpFunctional (Deme → FiniteReportLaw (FullHaplotype Locus Allele)) :=
  mixtureExpectation (realizableLaw capacity v hv).1 (realizableLaw_spec capacity v hv).1
    (realizableLaw_spec capacity v hv).2.1 (realizableLaw capacity v hv).2

/-- The Dirac mixture at the realizable law has the given budget moments. -/
theorem expectedMoments_realizableExpectation (capacity : Locus → ℕ)
    (v : BudgetConfiguration Deme Locus Allele capacity → ℝ)
    (hv : v ∈ realizationBody (budgetMomentFeature (Deme := Deme) (Locus := Locus)
      (Allele := Allele) capacity)) :
    (fun ξ : BudgetConfiguration Deme Locus Allele capacity ↦
        realizableExpectation capacity v hv fun law ↦ configurationMoment law ξ.1) = v := by
  funext ξ
  rw [← congrFun (realizableLaw_spec capacity v hv).2.2 ξ, featureVector_apply]
  show ∑ k, (realizableLaw capacity v hv).1 k
      * configurationMoment (stateLaw ((realizableLaw capacity v hv).2 k)) ξ.1 = _
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [← eval_momentPolynomial]
  rfl

/-- **The moment vector along a history of events.**  Times are measured from the start of the
history, and a segment counts the pulses passed.  Inside an epoch it is that epoch's dual
propagator applied to the vector at the epoch's start, with negative times clamped to the start;
from the epoch's end on it is the rest of the history.  At a pulse, segment zero keeps the vector
before the pulse, and every later segment runs the rest of the history from the pulsed vector. -/
def eventMoments (capacity : Locus → ℕ) :
    List (HaplotypeHistoryEvent Deme Locus Allele) →
      (BudgetConfiguration Deme Locus Allele capacity → ℝ) → ℕ → ℝ →
        BudgetConfiguration Deme Locus Allele capacity → ℝ
  | [], v, _, _ => v
  | HaplotypeHistoryEvent.epoch rates time :: rest, v, segment, t =>
      if t < time then (matrixExponential (dualGenerator rates capacity) (max t 0)).mulVec v
      else eventMoments capacity rest
        ((matrixExponential (dualGenerator rates capacity) time).mulVec v) segment (t - time)
  | HaplotypeHistoryEvent.pulse _ :: _, v, 0, _ => v
  | HaplotypeHistoryEvent.pulse weights :: rest, v, segment + 1, t =>
      eventMoments capacity rest ((pulseKernel weights capacity).mulVec v) segment t

/-- On a history of epochs alone, segment zero of the event moment vector is the moment vector of
`PartialHaplotypeHistoryRealization`. -/
theorem eventMoments_ofEpoch (capacity : Locus → ℕ) :
    ∀ (epochs : List (NeutralRates Deme Locus Allele × ℝ))
      (v : BudgetConfiguration Deme Locus Allele capacity → ℝ) (t : ℝ),
      eventMoments capacity (epochs.map HaplotypeHistoryEvent.ofEpoch) v 0 t
        = historyMoments capacity epochs v t
  | [], _, _ => rfl
  | epoch :: rest, v, t => by
    simp only [List.map_cons, HaplotypeHistoryEvent.ofEpoch, eventMoments, historyMoments,
      eventMoments_ofEpoch capacity rest]

/-- At the start of a history with nonnegative durations, segment zero holds the initial
vector. -/
theorem eventMoments_zero (capacity : Locus → ℕ) :
    ∀ events : List (HaplotypeHistoryEvent Deme Locus Allele),
      (∀ event ∈ events, 0 ≤ event.duration) →
      ∀ v : BudgetConfiguration Deme Locus Allele capacity → ℝ,
        eventMoments capacity events v 0 0 = v
  | [], _, _ => rfl
  | HaplotypeHistoryEvent.epoch rates time :: rest, hdurations, v => by
    rcases (hdurations _ (List.mem_cons.mpr (Or.inl rfl)) : (0 : ℝ) ≤ time).lt_or_eq with
      hpositive | hzero
    · simp only [eventMoments, if_pos hpositive, max_self, matrixExponential_zero,
        Matrix.one_mulVec]
    · subst hzero
      simp only [eventMoments, if_neg (lt_irrefl (0 : ℝ)), sub_self, matrixExponential_zero,
        Matrix.one_mulVec]
      exact eventMoments_zero capacity rest
        (fun other hother ↦ hdurations other (List.mem_cons.mpr (Or.inr hother))) v
  | HaplotypeHistoryEvent.pulse _ :: _, _, _ => rfl

/-- Every moment vector along a history of events lies in the realization body of the
budget-moment feature when the initial vector does. -/
theorem eventMoments_mem_realizationBody (capacity : Locus → ℕ) :
    ∀ events : List (HaplotypeHistoryEvent Deme Locus Allele),
      (∀ event ∈ events, 0 ≤ event.duration) →
      ∀ v : BudgetConfiguration Deme Locus Allele capacity → ℝ,
        v ∈ realizationBody (budgetMomentFeature (Deme := Deme) (Locus := Locus)
          (Allele := Allele) capacity) →
        ∀ (segment : ℕ) (t : ℝ), eventMoments capacity events v segment t ∈
          realizationBody (budgetMomentFeature (Deme := Deme) (Locus := Locus)
            (Allele := Allele) capacity)
  | [], _, _, hv, _, _ => hv
  | HaplotypeHistoryEvent.epoch rates time :: rest, hdurations, v, hv, segment, t => by
    have hstep : ∀ s : ℝ, 0 ≤ s →
        (matrixExponential (dualGenerator rates capacity) s).mulVec v ∈
          realizationBody (budgetMomentFeature (Deme := Deme) (Locus := Locus)
            (Allele := Allele) capacity) :=
      fun s hs ↦ eventMatrix_mulVec_mem_realizationBody capacity
        (HaplotypeHistoryEvent.epoch rates s) hs v hv
    simp only [eventMoments]
    split_ifs
    · exact hstep (max t 0) (le_max_right t 0)
    · exact eventMoments_mem_realizationBody capacity rest
        (fun other hother ↦ hdurations other (List.mem_cons.mpr (Or.inr hother))) _
        (hstep time (hdurations _ (List.mem_cons.mpr (Or.inl rfl)))) segment (t - time)
  | HaplotypeHistoryEvent.pulse _ :: _, _, _, hv, 0, _ => by
    simp only [eventMoments]
    exact hv
  | HaplotypeHistoryEvent.pulse weights :: rest, hdurations, v, hv, segment + 1, t => by
    simp only [eventMoments]
    exact eventMoments_mem_realizationBody capacity rest
      (fun other hother ↦ hdurations other (List.mem_cons.mpr (Or.inr hother))) _
      (pulseKernel_mulVec_mem_realizationBody weights capacity v hv) segment t

/-- **The realized expectation family of a history of events.**  At every segment and time it is
the Dirac mixture at a realized law with the history's moments. -/
def eventRealizedExpectation (capacity : Locus → ℕ)
    (events : List (HaplotypeHistoryEvent Deme Locus Allele))
    (hdurations : ∀ event ∈ events, 0 ≤ event.duration) (x0 : FrequencyState Deme Locus Allele)
    (segment : ℕ) (t : ℝ) : ExpFunctional (Deme → FiniteReportLaw (FullHaplotype Locus Allele)) :=
  realizableExpectation capacity
    (eventMoments capacity events (budgetMomentFeature capacity x0) segment t)
    (eventMoments_mem_realizationBody capacity events hdurations _
      (mem_realizationBody_of_range _ x0) segment t)

/-- The realized family has the history's moments at every segment and time. -/
theorem expectedMomentVector_eventRealizedExpectation (capacity : Locus → ℕ)
    (events : List (HaplotypeHistoryEvent Deme Locus Allele))
    (hdurations : ∀ event ∈ events, 0 ≤ event.duration) (x0 : FrequencyState Deme Locus Allele)
    (segment : ℕ) (t : ℝ) :
    expectedMomentVector capacity (eventRealizedExpectation capacity events hdurations x0 segment)
        t
      = eventMoments capacity events (budgetMomentFeature capacity x0) segment t :=
  expectedMoments_realizableExpectation capacity
    (eventMoments capacity events (budgetMomentFeature capacity x0) segment t) _

/-- **The forward equation along a history of events, from the moments.**  Any expectation family
whose segments follow `eventMoments` from `start` on obeys the forward moment equation along the
history: inside an epoch through `PartialHaplotypeHistoryRealization.forwardOnHistory_of_moments`,
and at a pulse through `PartialHaplotypePulseKernel.pulseKernel_mulVec_expectedMoment`. -/
theorem forwardOnEventHistory_of_moments (capacity : Locus → ℕ)
    (expectationAt :
      ℕ → ℝ → ExpFunctional (Deme → FiniteReportLaw (FullHaplotype Locus Allele))) :
    ∀ (events : List (HaplotypeHistoryEvent Deme Locus Allele)) (segment : ℕ) (start : ℝ)
      (v : BudgetConfiguration Deme Locus Allele capacity → ℝ),
      (∀ event ∈ events, 0 ≤ event.duration) →
      (∀ (later : ℕ) (t : ℝ), start ≤ t →
        expectedMomentVector capacity (expectationAt (segment + later)) t
          = eventMoments capacity events v later (t - start)) →
      ForwardOnEventHistory capacity expectationAt events segment start
  | [], _, _, _, _, _ => trivial
  | HaplotypeHistoryEvent.epoch rates time :: rest, segment, start, v, hdurations, hmoments => by
    have htime : 0 ≤ time := hdurations _ (List.mem_cons.mpr (Or.inl rfl))
    have hrest : ∀ other ∈ rest, 0 ≤ other.duration :=
      fun other hother ↦ hdurations other (List.mem_cons.mpr (Or.inr hother))
    rw [ForwardOnEventHistory]
    refine ⟨forwardOnHistory_of_moments capacity (expectationAt segment) [(rates, time)] start v
      (fun epoch hepoch ↦ by
        rw [List.mem_singleton.mp hepoch]
        exact htime) fun t ht ↦ ?_, ?_⟩
    · have hend : t ≤ start + time := by simpa using ht.2
      have h := hmoments 0 t ht.1
      simp only [add_zero] at h
      rw [h]
      by_cases hlt : t - start < time
      · simp only [eventMoments, historyMoments, if_pos hlt]
      · have hsame : t - start = time := le_antisymm (by linarith) (not_lt.mp hlt)
        simp only [eventMoments, historyMoments, if_neg hlt]
        rw [hsame, sub_self, eventMoments_zero capacity rest hrest]
    · refine forwardOnEventHistory_of_moments capacity expectationAt rest segment (start + time)
        ((matrixExponential (dualGenerator rates capacity) time).mulVec v) hrest
        fun later t ht ↦ ?_
      have hlater : ¬t - start < time := not_lt.mpr (by linarith)
      have h := hmoments later t (by linarith)
      simp only [eventMoments, if_neg hlater] at h
      rw [h, sub_sub]
  | HaplotypeHistoryEvent.pulse weights :: rest, segment, start, v, hdurations, hmoments => by
    have hrest : ∀ other ∈ rest, 0 ≤ other.duration :=
      fun other hother ↦ hdurations other (List.mem_cons.mpr (Or.inr hother))
    have hbefore : expectedMomentVector capacity (expectationAt segment) start = v := by
      have h := hmoments 0 start le_rfl
      simp only [add_zero, sub_self, eventMoments] at h
      exact h
    have hafter : expectedMomentVector capacity (expectationAt (segment + 1)) start
        = (pulseKernel weights capacity).mulVec v := by
      have h := hmoments 1 start le_rfl
      simp only [sub_self, eventMoments, eventMoments_zero capacity rest hrest] at h
      exact h
    rw [ForwardOnEventHistory]
    refine ⟨fun ξ ↦ ?_, ?_⟩
    · exact (congrFun hafter ξ).trans
        ((congrArg (fun w ↦ (pulseKernel weights capacity).mulVec w ξ) hbefore).symm.trans
          (pulseKernel_mulVec_expectedMoment weights capacity (expectationAt segment start)
            ξ).symm)
    · refine forwardOnEventHistory_of_moments capacity expectationAt rest (segment + 1) start
        ((pulseKernel weights capacity).mulVec v) hrest fun later t ht ↦ ?_
      have h := hmoments (later + 1) t ht
      simp only [eventMoments] at h
      rw [show segment + 1 + later = segment + (later + 1) by omega]
      exact h

/-- **The realized family obeys the forward equation along the history**, with no hypothesis. -/
theorem forwardOnEventHistory_eventRealizedExpectation (capacity : Locus → ℕ)
    (events : List (HaplotypeHistoryEvent Deme Locus Allele))
    (hdurations : ∀ event ∈ events, 0 ≤ event.duration) (x0 : FrequencyState Deme Locus Allele) :
    ForwardOnEventHistory capacity (eventRealizedExpectation capacity events hdurations x0) events
      0 0 :=
  forwardOnEventHistory_of_moments capacity _ events 0 0 (budgetMomentFeature capacity x0)
    hdurations fun later t _ ↦ by
      rw [zero_add, expectedMomentVector_eventRealizedExpectation, sub_zero]

/-- **NOTE1 (20) along a history of epochs, splits and pulses, with no hypothesis.**  The realized
expectation family of a history of events with nonnegative durations obeys the forward equation
along the history, so by `expectedMomentVector_eventHistory` its expected moments in the last
segment at the end of the history are the chronological product of the epoch dual propagators and
the pulse kernels applied to the initial moments. -/
theorem expectedMomentVector_eventHistory_realized (capacity : Locus → ℕ)
    (events : List (HaplotypeHistoryEvent Deme Locus Allele))
    (hdurations : ∀ event ∈ events, 0 ≤ event.duration) (x0 : FrequencyState Deme Locus Allele) :
    expectedMomentVector capacity
        (eventRealizedExpectation capacity events hdurations x0 (eventPulseCount events))
        (eventHistoryDuration events)
      = (eventPropagator capacity events).mulVec (budgetMomentFeature capacity x0) := by
  have h := expectedMomentVector_eventHistory capacity
    (eventRealizedExpectation capacity events hdurations x0) events 0 0 hdurations
    (forwardOnEventHistory_eventRealizedExpectation capacity events hdurations x0)
  rwa [zero_add, zero_add,
    expectedMomentVector_eventRealizedExpectation capacity events hdurations x0 0 0,
    eventMoments_zero capacity events hdurations] at h

end

end Descent.Portability.PartialHaplotypeEventHistoryRealization
