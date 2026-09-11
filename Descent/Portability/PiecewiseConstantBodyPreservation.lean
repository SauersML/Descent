/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.KernelRealizationPreservation
import Descent.Coalescent.TwoLocusHistory

assert_below Descent.Decision Descent.Program

/-!
# Piecewise-constant histories preserve the corpus realization body

NOTE1 §2.4 reduces a time-varying demographic history to a piecewise-constant one: finitely
many epochs, each with its own constant rate matrix, interleaved with finitely many
instantaneous events.  In the corpus that is exactly a list of
`Descent.Coalescent.LowOrderLDInstruction`, composed by `propagateLowOrderLDInstructions`.
This module proves NOTE1 Theorem 2 on that list for histories whose epochs admit a microscopic
approximation on the stored features, which rules out positive mutation (see the scope paragraph
below): the present state of such a compiled history is haplotype realizable whenever its
initial state is.

The list induction itself is not here.  It is
`Descent.Portability.KernelRealizationPreservation.propagate_mem_realizationBody`, which takes
preservation of the already-composed instruction action as its hypothesis, and everything
below is derived from it.  What this module adds is three things that theorem does not give.

First, a constructor-level interface.  A compiler holds body preservation for the epochs that
occur in its history and body preservation for the instantaneous transforms that occur, not a
single statement about `LowOrderLDInstruction.apply`; reading the instruction by its
constructor turns the one into the other, and costs a case split rather than an induction.

Second, composition over concatenation, stated for an arbitrary invariant set on top of the
corpus chain law `propagateLowOrderLDInstructions_append`.  Two consecutive blocks that each
preserve a set compose to a block that preserves it, which is the sense in which the
piecewise-constant compilation of §2.4 is closed under refining the epoch partition.

Third, the history-level conclusion.  `history_present_mem_realizationBody` takes the
microscopic approximation as a family indexed by the epochs occurring in the history, which is
how a compiler holds it: one approximation per epoch, not one for all generators at once.
Each epoch then preserves the body by `propagator_mulVec_mem_realizationBody_of_approx` and
each instantaneous instruction, assumed to be a physically realized split, by
`split_mulVec_mem_realizationBody_of_mem`, neither of which needs a closedness hypothesis any
more: closedness of the corpus body is now the theorem
`RealizationBody.isClosed_realizationBody_lowOrderLDFeature`.  A history made only of splits
therefore preserves realizability outright, and that is recorded separately.

Scope of the history-level theorem.  Its approximations are for the stored feature map
`lowOrderLDFeature D`.  No such approximation exists for an epoch whose generator is the corpus
rate law's `augmentedLowOrderLDGenerator` at a positive mutation rate: the stored `pi2` mutation
row reads the left heterozygosity `H` where the physical velocity reads the right
heterozygosity `H^R`, which is why NOTE1 (6) enlarges the observable family.  The theorem is
true as stated, but its approximation family can be supplied only when every epoch of the
history is mutation-free, so that is the only case in which it has content.  The general
statement, with positive mutation and no supplied approximation, is over locus-exchangeable
realizations:
`TwoLocusMicroscopicApproximation.history_present_locusExchangeable_realization`, with body
membership in `TwoLocusMicroscopicApproximation.history_present_mem_realizationBody_of_events`.

Not formalized here: the L¹ limit of NOTE1 §2.4, in which general nonnegative integrable rates
are approximated by step functions and the propagator difference is bounded by a constant times
the L¹ difference of generators.  Only the piecewise-constant composition is proved, which is
what the corpus's instruction lists express.

## Empirical status

None.  The bodies here are algebra: a fold of linear maps over a list and membership in a
convex hull, so no measurement can bear on them.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.PiecewiseConstantBodyPreservation

open Descent.Portability.FiniteMixtureKernel
open Descent.Portability.RealizationBody
open Descent.Portability.KernelRealizationPreservation
open Descent.Coalescent

variable {D : ℕ}

/-- The constructor-level reading of the corpus list induction: body preservation for the
epochs occurring in a history and for the instantaneous transforms occurring in it is enough,
and is what a compiler actually holds.  The induction is
`KernelRealizationPreservation.propagate_mem_realizationBody`; this only splits on the
instruction constructor. -/
theorem propagateInstructions_mem_of_epochs_and_transforms
    (instructions : List (LowOrderLDInstruction D))
    (hevolve : ∀ epoch : LowOrderLDEpoch D,
      LowOrderLDInstruction.evolve epoch ∈ instructions →
        ∀ state ∈ realizationBody (lowOrderLDFeature D),
          epoch.propagator.mulVec state ∈ realizationBody (lowOrderLDFeature D))
    (htransform : ∀ transform,
      LowOrderLDInstruction.instantaneous transform ∈ instructions →
        ∀ state ∈ realizationBody (lowOrderLDFeature D),
          transform.mulVec state ∈ realizationBody (lowOrderLDFeature D))
    (initial : AffineLowOrderLDCoordinate D → ℝ)
    (hinitial : initial ∈ realizationBody (lowOrderLDFeature D)) :
    propagateLowOrderLDInstructions instructions initial
      ∈ realizationBody (lowOrderLDFeature D) := by
  refine propagate_mem_realizationBody instructions ?_ initial hinitial
  intro instruction hmem state hstate
  cases instruction with
  | evolve epoch => exact hevolve epoch hmem state hstate
  | instantaneous transform => exact htransform transform hmem state hstate

/-- Two consecutive blocks of instructions that each preserve a set compose to a block that
preserves it; the corpus chain law supplies the operator composition.  This is NOTE1 §2.4's
refinement of the epoch partition, and it holds of any invariant set. -/
theorem propagateInstructions_append_mem
    (invariant : Set (AffineLowOrderLDCoordinate D → ℝ))
    (front rest : List (LowOrderLDInstruction D))
    (hfront : ∀ state ∈ invariant, propagateLowOrderLDInstructions front state ∈ invariant)
    (hrest : ∀ state ∈ invariant, propagateLowOrderLDInstructions rest state ∈ invariant)
    (initial : AffineLowOrderLDCoordinate D → ℝ) (hinitial : initial ∈ invariant) :
    propagateLowOrderLDInstructions (front ++ rest) initial ∈ invariant := by
  rw [propagateLowOrderLDInstructions_append]
  exact hrest _ (hfront _ hinitial)

/-- **NOTE1 Theorem 2, closing sentence, for mutation-free epochs.**  A compiled low-order
history keeps a haplotype-realizable state realizable: every epoch whose generator admits a
microscopic approximation on the stored features preserves the corpus realization body, every
instantaneous instruction that is a physically realized split preserves it, and the composed
history therefore does too.  No closedness hypothesis is needed; the corpus body is closed.
Scope: a stored-feature approximation cannot exist for an epoch with a positive mutation rate,
because the stored `pi2` mutation row reads `H` where the physical velocity reads `H^R`, so
this has content only when every epoch is mutation-free.  The general history statement, with
mutation and no supplied approximation, is
`TwoLocusMicroscopicApproximation.history_present_locusExchangeable_realization`. -/
theorem history_present_mem_realizationBody {B : Type*} [Fintype B]
    (history : LowOrderLDHistory D)
    (approximation : ∀ epoch : LowOrderLDEpoch D,
      LowOrderLDInstruction.evolve epoch ∈ history.instructions →
        MicroscopicApproximation (B := B) (lowOrderLDFeature D) epoch.generator)
    (hsplit : ∀ transform,
      LowOrderLDInstruction.instantaneous transform ∈ history.instructions →
        ∃ parent child : Fin D, transform = lowOrderLDSplitTransform parent child)
    (hinitial : history.initial ∈ realizationBody (lowOrderLDFeature D)) :
    history.present ∈ realizationBody (lowOrderLDFeature D) := by
  unfold LowOrderLDHistory.present
  refine propagateInstructions_mem_of_epochs_and_transforms _ ?_ ?_ _ hinitial
  · intro epoch hmem state hstate
    exact propagator_mulVec_mem_realizationBody_of_approx epoch (approximation epoch hmem)
      state hstate
  · intro transform hmem state hstate
    obtain ⟨parent, child, hform⟩ := hsplit transform hmem
    subst hform
    exact split_mulVec_mem_realizationBody_of_mem hstate parent child

/-- A history built only from physically realized splits preserves the corpus realization body
outright, with no microscopic approximation and no limit.  This shows the hypothesis family of
the previous theorem is satisfiable, vacuously in the epochs. -/
theorem splitInstructions_mem_realizationBody (splits : List (Fin D × Fin D))
    (initial : AffineLowOrderLDCoordinate D → ℝ)
    (hinitial : initial ∈ realizationBody (lowOrderLDFeature D)) :
    propagateLowOrderLDInstructions
        (splits.map fun pair ↦ LowOrderLDInstruction.split pair.1 pair.2) initial
      ∈ realizationBody (lowOrderLDFeature D) := by
  refine propagateInstructions_mem_of_epochs_and_transforms _ ?_ ?_ _ hinitial
  · intro epoch hmem
    exfalso
    obtain ⟨pair, _, hpair⟩ := List.mem_map.mp hmem
    simp [LowOrderLDInstruction.split] at hpair
  · intro transform hmem state hstate
    obtain ⟨pair, _, hpair⟩ := List.mem_map.mp hmem
    simp only [LowOrderLDInstruction.split, LowOrderLDInstruction.instantaneous.injEq] at hpair
    subst hpair
    exact split_mulVec_mem_realizationBody_of_mem hstate pair.1 pair.2

end Descent.Portability.PiecewiseConstantBodyPreservation
