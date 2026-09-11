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
an expectation family that obeys the forward moment equation epoch by epoch.  For one epoch,
`PartialHaplotypeMicroscopicApproximation` realizes the dual moments by a finitely supported law
on population states, through NOTE1 Theorem 1 applied to the neutral microscopic kernel.

This module carries the realization through a whole history.  Every epoch's dual propagator
keeps the realization body of the budget-moment feature invariant
(`KernelRealizationPreservation.exp_mulVec_mem_realizationBody` with that epoch's
`neutralMicroscopicApproximation`), so by induction over the epochs the chronological product
does too (`historyPropagator_mulVec_mem_realizationBody`).  Carathéodory then gives, for every
initial population state, a finitely supported law on states whose budget-respecting
configuration moments are the chronological product applied to the initial moments
(`exists_historyLaw`, `historyLaw`, `historyLaw_spec`).  These are genuine expectations of
configuration moments, with no forward-moment hypothesis anywhere.

Scope.  The history is a list of constant-rate epochs with nonnegative durations; splits and
admixture pulses are not composed here.  The realized law matches the history on the
budget-respecting moments of one fixed budget.  A single expectation family satisfying the
forward moment equation across all epochs at once (`ForwardOnHistory`) is not assembled here.

## Empirical status

None.  The bodies here are convex geometry and matrix algebra: invariance of a convex hull under
products of matrix exponentials and a finite mixture read off it, so no measurement can bear on
them.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.PartialHaplotypeHistoryRealization

open PartialHaplotypeCarrier PartialHaplotypeDualGenerator PartialHaplotypeDualSemigroup
open PartialHaplotypeMicroscopicApproximation NeutralFellerGenerator
open FiniteMixtureKernel RealizationBody KernelRealizationPreservation

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

end

end Descent.Portability.PartialHaplotypeHistoryRealization
