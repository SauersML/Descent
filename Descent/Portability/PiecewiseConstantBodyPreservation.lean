/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.KernelRealizationPreservation
import Descent.Coalescent.TwoLocusHistory

assert_below Descent.Decision Descent.Program

/-!
# Piecewise-constant histories preserve an invariant body

NOTE1 §2.4 reduces a time-varying demographic history to a piecewise-constant one: finitely
many epochs, each with its own constant rate matrix, interleaved with finitely many
instantaneous events.  In the corpus that is exactly a list of
`Descent.Coalescent.LowOrderLDInstruction`, composed by `propagateLowOrderLDInstructions`.
This module proves that such a list preserves any set preserved by each of its epoch
propagators and each of its instantaneous transforms, and then assembles the end-to-end
statement that NOTE1 Theorem 2 closes with: the present state of a compiled history is
haplotype realizable whenever its initial state is.

The list step is separated into two layers.  The first is a generic invariance of a left
fold over an arbitrary set, with no demographic vocabulary in it.  The second reads a
`LowOrderLDInstruction` by its constructor, so the caller supplies exactly what it has: body
preservation for the epochs that actually occur in the history and body preservation for the
instantaneous transforms that actually occur, rather than a single hypothesis about the
already-composed instruction action.  The corpus-body instance of the composed statement is
`Descent.Portability.KernelRealizationPreservation.propagate_mem_realizationBody` and is not
reproved here; what is added is the arbitrary invariant set, the constructor-level interface,
and the history-level conclusion.

The end-to-end theorem takes the microscopic approximation as a family indexed by the epochs
occurring in the history, which is how a compiler holds it: one approximation per epoch, not
one for all generators at once.  Each epoch then preserves the corpus body by
`propagator_mulVec_mem_realizationBody`, and each instantaneous instruction, assumed to be a
physically realized split, preserves it by `split_mulVec_mem_realizationBody`, which needs no
approximation because a split relabels the realizing haplotype law.  A history made only of
splits therefore preserves realizability unconditionally, which is recorded separately so the
hypothesis family of the general theorem is known to be satisfiable.

Composition over concatenation is recorded as well, on top of the corpus chain law
`propagateLowOrderLDInstructions_append`: two consecutive blocks that each preserve a set
compose to a block that preserves it.  This is the sense in which the piecewise-constant
compilation of NOTE1 §2.4 is closed under refining the epoch partition.

Not formalized here: the L¹ limit of NOTE1 §2.4, in which general nonnegative integrable
rates are approximated by step functions and the propagator difference is bounded by a
constant times the L¹ difference of generators.  Only the piecewise-constant composition is
proved, which is what the corpus's instruction lists express.  Also not proved here, and
assumed throughout as in the modules this one builds on, is the closedness of the corpus
realization body.

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

/-- A set closed under every step of a left fold is closed under the whole fold.  This is the
demography-free skeleton of piecewise-constant composition. -/
theorem foldl_mem_of_steps {α β : Type*} (invariant : Set α) (step : α → β → α)
    (items : List β)
    (hstep : ∀ item ∈ items, ∀ state ∈ invariant, step state item ∈ invariant)
    (initial : α) (hinitial : initial ∈ invariant) :
    items.foldl step initial ∈ invariant := by
  induction items generalizing initial with
  | nil => simpa using hinitial
  | cons head tail ih =>
    refine ih (fun item hmem state hstate ↦
      hstep item (List.mem_cons_of_mem head hmem) state hstate) (step initial head) ?_
    exact hstep head (by simp) initial hinitial

variable {D : ℕ}

/-- **NOTE1 §2.4 for an arbitrary invariant set.**  A piecewise-constant history preserves
every set that each of its epoch propagators and each of its instantaneous transforms
preserves.  The hypotheses are read off the instruction constructors, so only the epochs and
transforms actually occurring in the history are constrained. -/
theorem propagateInstructions_mem_of_epochs_and_transforms
    (invariant : Set (AffineLowOrderLDCoordinate D → ℝ))
    (instructions : List (LowOrderLDInstruction D))
    (hevolve : ∀ epoch : LowOrderLDEpoch D,
      LowOrderLDInstruction.evolve epoch ∈ instructions →
        ∀ state ∈ invariant, epoch.propagator.mulVec state ∈ invariant)
    (htransform : ∀ transform,
      LowOrderLDInstruction.instantaneous transform ∈ instructions →
        ∀ state ∈ invariant, transform.mulVec state ∈ invariant)
    (initial : AffineLowOrderLDCoordinate D → ℝ) (hinitial : initial ∈ invariant) :
    propagateLowOrderLDInstructions instructions initial ∈ invariant := by
  refine foldl_mem_of_steps invariant _ instructions ?_ initial hinitial
  intro instruction hmem state hstate
  cases instruction with
  | evolve epoch => exact hevolve epoch hmem state hstate
  | instantaneous transform => exact htransform transform hmem state hstate

/-- Two consecutive blocks of instructions that each preserve a set compose to a block that
preserves it; the corpus chain law supplies the operator composition. -/
theorem propagateInstructions_append_mem
    (invariant : Set (AffineLowOrderLDCoordinate D → ℝ))
    (front rest : List (LowOrderLDInstruction D))
    (hfront : ∀ state ∈ invariant, propagateLowOrderLDInstructions front state ∈ invariant)
    (hrest : ∀ state ∈ invariant, propagateLowOrderLDInstructions rest state ∈ invariant)
    (initial : AffineLowOrderLDCoordinate D → ℝ) (hinitial : initial ∈ invariant) :
    propagateLowOrderLDInstructions (front ++ rest) initial ∈ invariant := by
  rw [propagateLowOrderLDInstructions_append]
  exact hrest _ (hfront _ hinitial)

/-- **NOTE1 Theorem 2, closing sentence.**  A compiled low-order history keeps a
haplotype-realizable state realizable: every epoch whose generator admits a microscopic
approximation preserves the corpus realization body, every instantaneous instruction that is a
physically realized split preserves it, and the composed history therefore does too.
Assumes: the corpus realization body is closed. -/
theorem history_present_mem_realizationBody {B : Type*} [Fintype B]
    (hclosed : IsClosed (realizationBody (lowOrderLDFeature D)))
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
  refine propagateInstructions_mem_of_epochs_and_transforms _ _ ?_ ?_ _ hinitial
  · intro epoch hmem state hstate
    exact propagator_mulVec_mem_realizationBody hclosed epoch (approximation epoch hmem)
      state hstate
  · intro transform hmem state hstate
    obtain ⟨parent, child, hform⟩ := hsplit transform hmem
    subst hform
    exact split_mulVec_mem_realizationBody hclosed hstate parent child

/-- A history built only from physically realized splits preserves the corpus realization body
outright, with no microscopic approximation and no limit.  This shows the hypothesis family of
the previous theorem is satisfiable. -/
theorem splitInstructions_mem_realizationBody
    (hclosed : IsClosed (realizationBody (lowOrderLDFeature D)))
    (splits : List (Fin D × Fin D)) (initial : AffineLowOrderLDCoordinate D → ℝ)
    (hinitial : initial ∈ realizationBody (lowOrderLDFeature D)) :
    propagateLowOrderLDInstructions
        (splits.map fun pair ↦ LowOrderLDInstruction.split pair.1 pair.2) initial
      ∈ realizationBody (lowOrderLDFeature D) := by
  refine propagateInstructions_mem_of_epochs_and_transforms _ _ ?_ ?_ _ hinitial
  · intro epoch hmem
    exfalso
    obtain ⟨pair, _, hpair⟩ := List.mem_map.mp hmem
    simp [LowOrderLDInstruction.split] at hpair
  · intro transform hmem state hstate
    obtain ⟨pair, _, hpair⟩ := List.mem_map.mp hmem
    simp only [LowOrderLDInstruction.split, LowOrderLDInstruction.instantaneous.injEq] at hpair
    subst hpair
    exact split_mulVec_mem_realizationBody hclosed hstate pair.1 pair.2

end Descent.Portability.PiecewiseConstantBodyPreservation
