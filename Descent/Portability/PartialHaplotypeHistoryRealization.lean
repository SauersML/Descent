/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.PartialHaplotypeMicroscopicApproximation

assert_below Descent.Decision Descent.Program

/-!
# NOTE1 (20) along a demographic history, realized

NOTE1 §4.2 says that a changing demographic history composes the epoch generators in
chronological moment order.  `PartialHaplotypeDualSemigroup.historyPropagator` is that product of
epoch dual propagators, latest epoch leftmost, and
`PartialHaplotypeDualSemigroup.expectedMomentVector_history` identifies it with the evolution of
an expectation family that obeys the forward moment equation epoch by epoch (`ForwardOnHistory`).
For one epoch, `PartialHaplotypeMicroscopicApproximation` realizes the dual moments by a finitely
supported law on population states, through NOTE1 Theorem 1 applied to the neutral microscopic
kernel.

This module carries the realization through a whole history.  Every epoch's dual propagator
keeps the realization body of the budget-moment feature invariant
(`KernelRealizationPreservation.exp_mulVec_mem_realizationBody` with that epoch's
`neutralMicroscopicApproximation`), so by induction over the epochs the chronological product
does too (`historyPropagator_mulVec_mem_realizationBody`), and Carathéodory gives a finitely
supported law with the history's moments at its end (`exists_historyLaw`, `historyLaw_spec`).

It then builds one expectation family for the whole history.  `historyMoments` is the moment
vector along the history: inside an epoch, that epoch's dual propagator applied to the vector at
the epoch's start; from the epoch's end on, the rest of the history from the propagated vector.
Every such vector is realizable (`historyMoments_mem_realizationBody`), so
`historyRealizedExpectation` is at every time the Dirac mixture at a realized law, with exactly
those moments (`expectedMomentVector_historyRealizedExpectation`).  Any family whose expected
moments follow `historyMoments` satisfies the forward moment equation on every epoch
(`forwardOnHistory_of_moments`): inside an epoch its moments are the exponential orbit, whose
right derivative is the dual generator of that epoch, and the matrix form of (19) turns that into
the expected neutral generator.  Hence the realized family satisfies `ForwardOnHistory` with no
hypothesis (`forwardOnHistory_historyRealizedExpectation`), and `expectedMomentVector_history`
applies to it: at the end of the history its expected moments are the chronological product of
the epoch dual propagators applied to the initial moments (`expectedMomentVector_history_realized`).

Scope.  The history is a list of constant-rate epochs with nonnegative durations; splits and
admixture pulses are not composed here.  The realized family matches the history on the
budget-respecting moments of one fixed budget; it is not shown to be the marginal law of one
process across budgets.

## Empirical status

None.  The bodies here are convex geometry, matrix algebra and calculus of matrix exponentials:
invariance of a convex hull under products of matrix exponentials, finite mixtures read off it,
and derivatives of exponential orbits, so no measurement can bear on them.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.PartialHaplotypeHistoryRealization

open PartialHaplotypeCarrier PartialHaplotypeDualGenerator PartialHaplotypeDualSemigroup
open PartialHaplotypeMicroscopicApproximation NeutralFellerGenerator
open FiniteMixtureKernel RealizationBody KernelRealizationPreservation
open SubstochasticGeneratorSemigroup Descent.Coalescent Descent.Foundations MvPolynomial

variable {Deme Locus : Type*} {Allele : Locus → Type*}
variable [Fintype Deme] [DecidableEq Deme] [Fintype Locus] [DecidableEq Locus]
  [∀ ℓ, Fintype (Allele ℓ)] [∀ ℓ, DecidableEq (Allele ℓ)]

noncomputable section

/-- **Every history keeps moment vectors realizable.**  The chronological product of the epoch
dual propagators, with nonnegative durations, maps the realization body of the budget-moment
feature into itself. -/
theorem historyPropagator_mulVec_mem_realizationBody (capacity : Locus → ℕ) :
    ∀ epochs : List (NeutralRates Deme Locus Allele × ℝ), (∀ epoch ∈ epochs, 0 ≤ epoch.2) →
      ∀ v : BudgetConfiguration Deme Locus Allele capacity → ℝ,
        v ∈ realizationBody (budgetMomentFeature (Deme := Deme) (Locus := Locus)
          (Allele := Allele) capacity) →
        (historyPropagator capacity epochs).mulVec v ∈
          realizationBody (budgetMomentFeature (Deme := Deme) (Locus := Locus)
            (Allele := Allele) capacity)
  | [], _, v, hv => by simpa [historyPropagator] using hv
  | epoch :: rest, hdurations, v, hv => by
    rw [historyPropagator, ← Matrix.mulVec_mulVec]
    refine historyPropagator_mulVec_mem_realizationBody capacity rest
      (fun other hother ↦ hdurations other (List.mem_cons.mpr (Or.inr hother))) _ ?_
    exact exp_mulVec_mem_realizationBody _ _ (neutralMicroscopicApproximation epoch.1 capacity)
      (isClosed_realizationBody _ (continuous_budgetMomentFeature capacity)) epoch.2
      (hdurations epoch (List.mem_cons.mpr (Or.inl rfl))) v hv

/-- **NOTE1 (20) along a history, realized.**  For every chronological history of constant-rate
epochs with nonnegative durations and every initial population state, some finitely supported
law on population states has, at every budget-respecting configuration, the expected moment
given by the chronological product of the epoch dual propagators applied to the initial moments. -/
theorem exists_historyLaw (capacity : Locus → ℕ)
    (epochs : List (NeutralRates Deme Locus Allele × ℝ))
    (hdurations : ∀ epoch ∈ epochs, 0 ≤ epoch.2) (x0 : FrequencyState Deme Locus Allele) :
    ∃ q : (Fin (Fintype.card (BudgetConfiguration Deme Locus Allele capacity) + 1) → ℝ)
        × (Fin (Fintype.card (BudgetConfiguration Deme Locus Allele capacity) + 1)
          → FrequencyState Deme Locus Allele),
      (∀ k, 0 ≤ q.1 k) ∧ ∑ k, q.1 k = 1
        ∧ featureVector q.1 q.2 (budgetMomentFeature capacity)
          = (historyPropagator capacity epochs).mulVec (budgetMomentFeature capacity x0) := by
  obtain ⟨p, point, hp, hsum, hfeature⟩ := exists_law_of_mem_realizationBody _ _
    (historyPropagator_mulVec_mem_realizationBody capacity epochs hdurations _
      (mem_realizationBody_of_range _ x0))
  exact ⟨(p, point), hp, hsum, hfeature⟩

/-- The realized law at the end of a history: the weights and support points of a finitely
supported law with the history's dual moments. -/
def historyLaw (capacity : Locus → ℕ) (epochs : List (NeutralRates Deme Locus Allele × ℝ))
    (hdurations : ∀ epoch ∈ epochs, 0 ≤ epoch.2) (x0 : FrequencyState Deme Locus Allele) :
    (Fin (Fintype.card (BudgetConfiguration Deme Locus Allele capacity) + 1) → ℝ)
      × (Fin (Fintype.card (BudgetConfiguration Deme Locus Allele capacity) + 1)
        → FrequencyState Deme Locus Allele) :=
  Classical.choose (exists_historyLaw capacity epochs hdurations x0)

/-- The realized law at the end of a history is a probability law whose budget moments are the
chronological product of the epoch dual propagators applied to the initial moments. -/
theorem historyLaw_spec (capacity : Locus → ℕ)
    (epochs : List (NeutralRates Deme Locus Allele × ℝ))
    (hdurations : ∀ epoch ∈ epochs, 0 ≤ epoch.2) (x0 : FrequencyState Deme Locus Allele) :
    (∀ k, 0 ≤ (historyLaw capacity epochs hdurations x0).1 k)
      ∧ ∑ k, (historyLaw capacity epochs hdurations x0).1 k = 1
      ∧ featureVector (historyLaw capacity epochs hdurations x0).1
          (historyLaw capacity epochs hdurations x0).2 (budgetMomentFeature capacity)
        = (historyPropagator capacity epochs).mulVec (budgetMomentFeature capacity x0) :=
  Classical.choose_spec (exists_historyLaw capacity epochs hdurations x0)

/-! ## One expectation family along the whole history -/

/-- **The moment vector along a history.**  Times are measured from the start of the history.
Inside the first epoch it is that epoch's dual propagator applied to the initial vector, with
negative times clamped to the start; from the epoch's end on it is the rest of the history started
from the propagated vector. -/
def historyMoments (capacity : Locus → ℕ) :
    List (NeutralRates Deme Locus Allele × ℝ) →
      (BudgetConfiguration Deme Locus Allele capacity → ℝ) → ℝ →
        BudgetConfiguration Deme Locus Allele capacity → ℝ
  | [], v, _ => v
  | epoch :: rest, v, t =>
      if t < epoch.2 then
        (matrixExponential (dualGenerator epoch.1 capacity) (max t 0)).mulVec v
      else historyMoments capacity rest
        ((matrixExponential (dualGenerator epoch.1 capacity) epoch.2).mulVec v) (t - epoch.2)

/-- At the start of a history with nonnegative durations the moment vector is the initial one. -/
theorem historyMoments_zero (capacity : Locus → ℕ) :
    ∀ epochs : List (NeutralRates Deme Locus Allele × ℝ), (∀ epoch ∈ epochs, 0 ≤ epoch.2) →
      ∀ v : BudgetConfiguration Deme Locus Allele capacity → ℝ,
        historyMoments capacity epochs v 0 = v
  | [], _, _ => rfl
  | epoch :: rest, hdurations, v => by
    simp only [historyMoments]
    split_ifs with hpositive
    · rw [max_self, matrixExponential_zero, Matrix.one_mulVec]
    · have hzero : epoch.2 = 0 :=
        le_antisymm (not_lt.mp hpositive) (hdurations epoch (List.mem_cons.mpr (Or.inl rfl)))
      rw [hzero, sub_zero, matrixExponential_zero, Matrix.one_mulVec]
      exact historyMoments_zero capacity rest
        (fun other hother ↦ hdurations other (List.mem_cons.mpr (Or.inr hother))) v

/-- Every moment vector along a history lies in the realization body of the budget-moment
feature when the initial vector does. -/
theorem historyMoments_mem_realizationBody (capacity : Locus → ℕ) :
    ∀ epochs : List (NeutralRates Deme Locus Allele × ℝ), (∀ epoch ∈ epochs, 0 ≤ epoch.2) →
      ∀ v : BudgetConfiguration Deme Locus Allele capacity → ℝ,
        v ∈ realizationBody (budgetMomentFeature (Deme := Deme) (Locus := Locus)
          (Allele := Allele) capacity) →
        ∀ t : ℝ, historyMoments capacity epochs v t ∈
          realizationBody (budgetMomentFeature (Deme := Deme) (Locus := Locus)
            (Allele := Allele) capacity)
  | [], _, _, hv, _ => hv
  | epoch :: rest, hdurations, v, hv, t => by
    have hclosed := isClosed_realizationBody _ (continuous_budgetMomentFeature (Deme := Deme)
      (Locus := Locus) (Allele := Allele) capacity)
    simp only [historyMoments]
    split_ifs
    · exact exp_mulVec_mem_realizationBody _ _ (neutralMicroscopicApproximation epoch.1 capacity)
        hclosed (max t 0) (le_max_right t 0) v hv
    · exact historyMoments_mem_realizationBody capacity rest
        (fun other hother ↦ hdurations other (List.mem_cons.mpr (Or.inr hother))) _
        (exp_mulVec_mem_realizationBody _ _ (neutralMicroscopicApproximation epoch.1 capacity)
          hclosed epoch.2 (hdurations epoch (List.mem_cons.mpr (Or.inl rfl))) v hv) (t - epoch.2)

/-- A finitely supported law on population states with the moment vector of a history at a
given time. -/
theorem exists_historyMomentLaw (capacity : Locus → ℕ)
    (epochs : List (NeutralRates Deme Locus Allele × ℝ))
    (hdurations : ∀ epoch ∈ epochs, 0 ≤ epoch.2) (x0 : FrequencyState Deme Locus Allele)
    (t : ℝ) :
    ∃ q : (Fin (Fintype.card (BudgetConfiguration Deme Locus Allele capacity) + 1) → ℝ)
        × (Fin (Fintype.card (BudgetConfiguration Deme Locus Allele capacity) + 1)
          → FrequencyState Deme Locus Allele),
      (∀ k, 0 ≤ q.1 k) ∧ ∑ k, q.1 k = 1
        ∧ featureVector q.1 q.2 (budgetMomentFeature capacity)
          = historyMoments capacity epochs (budgetMomentFeature capacity x0) t := by
  obtain ⟨p, point, hp, hsum, hfeature⟩ := exists_law_of_mem_realizationBody _ _
    (historyMoments_mem_realizationBody capacity epochs hdurations _
      (mem_realizationBody_of_range _ x0) t)
  exact ⟨(p, point), hp, hsum, hfeature⟩

/-- The realized law of a history at a given time. -/
def historyMomentLaw (capacity : Locus → ℕ) (epochs : List (NeutralRates Deme Locus Allele × ℝ))
    (hdurations : ∀ epoch ∈ epochs, 0 ≤ epoch.2) (x0 : FrequencyState Deme Locus Allele)
    (t : ℝ) :
    (Fin (Fintype.card (BudgetConfiguration Deme Locus Allele capacity) + 1) → ℝ)
      × (Fin (Fintype.card (BudgetConfiguration Deme Locus Allele capacity) + 1)
        → FrequencyState Deme Locus Allele) :=
  Classical.choose (exists_historyMomentLaw capacity epochs hdurations x0 t)

/-- The realized law of a history at a time is a probability law with the history's moments. -/
theorem historyMomentLaw_spec (capacity : Locus → ℕ)
    (epochs : List (NeutralRates Deme Locus Allele × ℝ))
    (hdurations : ∀ epoch ∈ epochs, 0 ≤ epoch.2) (x0 : FrequencyState Deme Locus Allele)
    (t : ℝ) :
    (∀ k, 0 ≤ (historyMomentLaw capacity epochs hdurations x0 t).1 k)
      ∧ ∑ k, (historyMomentLaw capacity epochs hdurations x0 t).1 k = 1
      ∧ featureVector (historyMomentLaw capacity epochs hdurations x0 t).1
          (historyMomentLaw capacity epochs hdurations x0 t).2 (budgetMomentFeature capacity)
        = historyMoments capacity epochs (budgetMomentFeature capacity x0) t :=
  Classical.choose_spec (exists_historyMomentLaw capacity epochs hdurations x0 t)

/-- **The realized expectation family of a history.**  At every time it is the Dirac mixture at
the realized law with the history's moments. -/
def historyRealizedExpectation (capacity : Locus → ℕ)
    (epochs : List (NeutralRates Deme Locus Allele × ℝ))
    (hdurations : ∀ epoch ∈ epochs, 0 ≤ epoch.2) (x0 : FrequencyState Deme Locus Allele)
    (t : ℝ) : ExpFunctional (Deme → FiniteReportLaw (FullHaplotype Locus Allele)) :=
  mixtureExpectation (historyMomentLaw capacity epochs hdurations x0 t).1
    (historyMomentLaw_spec capacity epochs hdurations x0 t).1
    (historyMomentLaw_spec capacity epochs hdurations x0 t).2.1
    (historyMomentLaw capacity epochs hdurations x0 t).2

/-- The realized family has the history's moments at every time. -/
theorem expectedMomentVector_historyRealizedExpectation (capacity : Locus → ℕ)
    (epochs : List (NeutralRates Deme Locus Allele × ℝ))
    (hdurations : ∀ epoch ∈ epochs, 0 ≤ epoch.2) (x0 : FrequencyState Deme Locus Allele)
    (t : ℝ) :
    expectedMomentVector capacity (historyRealizedExpectation capacity epochs hdurations x0) t
      = historyMoments capacity epochs (budgetMomentFeature capacity x0) t := by
  have hspec := (historyMomentLaw_spec capacity epochs hdurations x0 t).2.2
  funext ξ
  rw [← hspec, featureVector_apply]
  show ∑ k, (historyMomentLaw capacity epochs hdurations x0 t).1 k
      * configurationMoment
          (stateLaw ((historyMomentLaw capacity epochs hdurations x0 t).2 k)) ξ.1 = _
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  show (historyMomentLaw capacity epochs hdurations x0 t).1 k
      * configurationMoment
          (stateLaw ((historyMomentLaw capacity epochs hdurations x0 t).2 k)) ξ.1 = _
  rw [← eval_momentPolynomial]
  rfl

/-- **The forward moment equation along a history, from the moments.**  Any expectation family
whose expected moment vector follows `historyMoments` from `start` on satisfies the forward
moment equation of NOTE1 (20) on every epoch of the history. -/
theorem forwardOnHistory_of_moments (capacity : Locus → ℕ)
    (expectationAt : ℝ → ExpFunctional (Deme → FiniteReportLaw (FullHaplotype Locus Allele))) :
    ∀ (epochs : List (NeutralRates Deme Locus Allele × ℝ)) (start : ℝ)
      (v : BudgetConfiguration Deme Locus Allele capacity → ℝ),
      (∀ epoch ∈ epochs, 0 ≤ epoch.2) →
      (∀ t, start ≤ t → expectedMomentVector capacity expectationAt t =
        historyMoments capacity epochs v (t - start)) →
      ForwardOnHistory capacity expectationAt epochs start
  | [], _, _, _, _ => trivial
  | epoch :: rest, start, v, hdurations, hmoments => by
    have hrest : ∀ other ∈ rest, 0 ≤ other.2 :=
      fun other hother ↦ hdurations other (List.mem_cons.mpr (Or.inr hother))
    have horbit : ∀ s : ℝ, HasDerivAt
        (fun r ↦ (matrixExponential (dualGenerator epoch.1 capacity) (r - start)).mulVec v)
        ((dualGenerator epoch.1 capacity).mulVec
          ((matrixExponential (dualGenerator epoch.1 capacity) (s - start)).mulVec v)) s := by
      intro s
      have h := HasDerivAt.scomp (x := s)
        (StationaryHaplotypeRealization.hasDerivAt_matrixExponential_mulVec
          (dualGenerator epoch.1 capacity) v (s - start))
        ((hasDerivAt_id (x := s)).sub_const start)
      simpa only [one_smul, Function.comp_def, id_eq] using h
    have hinside : ∀ t ∈ Set.Icc start (start + epoch.2),
        expectedMomentVector capacity expectationAt t =
          (matrixExponential (dualGenerator epoch.1 capacity) (t - start)).mulVec v := by
      intro t ht
      rw [hmoments t ht.1]
      simp only [historyMoments]
      split_ifs with hlt
      · rw [max_eq_left (sub_nonneg.mpr ht.1)]
      · have hend : t - start = epoch.2 :=
          le_antisymm (by linarith [ht.2]) (not_lt.mp hlt)
        rw [hend, sub_self, historyMoments_zero capacity rest hrest]
    rw [ForwardOnHistory]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · refine ContinuousOn.congr ?_ hinside
      exact (continuous_iff_continuousAt.mpr fun s ↦ (horbit s).continuousAt).continuousOn
    · intro ξ t ht
      have hmem : t ∈ Set.Icc start (start + epoch.2) := ⟨ht.1, ht.2.le⟩
      rw [expectedGenerator_eq_mulVec epoch.1 capacity expectationAt t ξ, hinside t hmem]
      refine (hasDerivAt_pi.mp (horbit t) ξ).hasDerivWithinAt.congr_of_eventuallyEq ?_ ?_
      · refine Filter.mem_of_superset (Ico_mem_nhdsGE ht.2) fun u hu ↦ ?_
        exact congrFun (hinside u ⟨ht.1.trans hu.1, hu.2.le⟩) ξ
      · exact congrFun (hinside t hmem) ξ
    · refine forwardOnHistory_of_moments capacity expectationAt rest (start + epoch.2)
        ((matrixExponential (dualGenerator epoch.1 capacity) epoch.2).mulVec v) hrest ?_
      intro t ht
      have hstart : start ≤ t := by linarith [ht, hdurations epoch (List.mem_cons.mpr
        (Or.inl rfl))]
      rw [hmoments t hstart]
      simp only [historyMoments]
      rw [if_neg (not_lt.mpr (by linarith)), sub_sub]

/-- **The realized family satisfies the forward moment equation on every epoch**, with no
hypothesis. -/
theorem forwardOnHistory_historyRealizedExpectation (capacity : Locus → ℕ)
    (epochs : List (NeutralRates Deme Locus Allele × ℝ))
    (hdurations : ∀ epoch ∈ epochs, 0 ≤ epoch.2) (x0 : FrequencyState Deme Locus Allele) :
    ForwardOnHistory capacity (historyRealizedExpectation capacity epochs hdurations x0) epochs
      0 :=
  forwardOnHistory_of_moments capacity _ epochs 0 (budgetMomentFeature capacity x0) hdurations
    fun t _ ↦ by rw [expectedMomentVector_historyRealizedExpectation, sub_zero]

/-- **NOTE1 (20) along a history, with no hypothesis.**  The realized expectation family of a
history of constant-rate epochs with nonnegative durations obeys the forward moment equation on
every epoch, so by `expectedMomentVector_history` its expected moments at the end of the history
are the chronological product of the epoch dual propagators applied to the initial moments. -/
theorem expectedMomentVector_history_realized (capacity : Locus → ℕ)
    (epochs : List (NeutralRates Deme Locus Allele × ℝ))
    (hdurations : ∀ epoch ∈ epochs, 0 ≤ epoch.2) (x0 : FrequencyState Deme Locus Allele) :
    expectedMomentVector capacity (historyRealizedExpectation capacity epochs hdurations x0)
        (epochs.map Prod.snd).sum
      = (historyPropagator capacity epochs).mulVec (budgetMomentFeature capacity x0) := by
  have h := expectedMomentVector_history capacity
    (historyRealizedExpectation capacity epochs hdurations x0) epochs 0 hdurations
    (forwardOnHistory_historyRealizedExpectation capacity epochs hdurations x0)
  rwa [zero_add, expectedMomentVector_historyRealizedExpectation capacity epochs hdurations x0 0,
    historyMoments_zero capacity epochs hdurations] at h

end

end Descent.Portability.PartialHaplotypeHistoryRealization
