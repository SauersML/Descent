/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.ExactFiniteHistoryLaw
import Mathlib.LinearAlgebra.Projection

assert_below Descent.Decision Descent.Program

/-!
Exact elimination of a discarded linear state, corresponding to Theorem 16
of the supplied research report. The initial discarded state remains an
explicit forcing term, independently of the memory terms from retained history.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.ExactMemoryLaw

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]

/-- Solve the discarded-state recursion exactly at every finite time. -/
theorem discarded_expansion (coupling : E →ₗ[ℝ] F) (hidden : Module.End ℝ F)
    (retained : ℕ → E) (discarded : ℕ → F)
    (hstep : ∀ time, discarded (time + 1) = coupling (retained time) + hidden (discarded time))
    (time : ℕ) :
    discarded time = (hidden ^ time) (discarded 0) +
      ∑ earlier ∈ Finset.range time,
        (hidden ^ (time - 1 - earlier)) (coupling (retained earlier)) := by
  induction time with
  | zero => simp
  | succ time ih =>
      rw [hstep, ih, map_add, map_sum, Finset.sum_range_succ]
      simp only [Nat.add_sub_cancel_right, Nat.sub_self, pow_zero, Module.End.one_apply]
      have hexp (earlier : ℕ) (hearlier : earlier ∈ Finset.range time) :
          hidden ((hidden ^ (time - 1 - earlier)) (coupling (retained earlier))) =
            (hidden ^ (time - earlier)) (coupling (retained earlier)) := by
        have hj := Finset.mem_range.mp hearlier
        rw [show time - earlier = (time - 1 - earlier) + 1 by omega, pow_succ']
        rfl
      rw [Finset.sum_congr rfl hexp, pow_succ']
      simp only [Module.End.mul_apply]
      abel

/-- The retained dynamics have an exact memory law, including hidden initial data. -/
theorem retained_memory (direct : Module.End ℝ E) (feedback : F →ₗ[ℝ] E)
    (coupling : E →ₗ[ℝ] F) (hidden : Module.End ℝ F)
    (retained : ℕ → E) (discarded : ℕ → F)
    (hretained : ∀ time, retained (time + 1) = direct (retained time) + feedback (discarded time))
    (hdiscarded : ∀ time, discarded (time + 1) =
      coupling (retained time) + hidden (discarded time)) (time : ℕ) :
    retained (time + 1) = direct (retained time) + feedback ((hidden ^ time) (discarded 0)) +
      ∑ earlier ∈ Finset.range time,
        feedback ((hidden ^ (time - 1 - earlier)) (coupling (retained earlier))) := by
  rw [hretained, discarded_expansion coupling hidden retained discarded hdiscarded,
    map_add, map_sum]
  abel

/-- Uniform one-step closure over every discarded initial state holds exactly
when the discarded-to-retained block vanishes. Vanishing feedback memory
products alone do not supply this condition. -/
theorem one_step_closure_iff (direct : Module.End ℝ E) (feedback : F →ₗ[ℝ] E) :
    (∀ retained first second,
      direct retained + feedback first = direct retained + feedback second) ↔ feedback = 0 := by
  constructor
  · intro h
    ext discarded
    have heq := h (0 : E) discarded (0 : F)
    simpa using heq
  · intro h
    simp [h]

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

noncomputable def retainedState (projection evolution : Module.End ℝ V)
    (initial : V) (time : ℕ) : V := projection ((evolution ^ time) initial)

noncomputable def discardedState (projection evolution : Module.End ℝ V)
    (initial : V) (time : ℕ) : V := (1 - projection) ((evolution ^ time) initial)

theorem retained_add_discarded (projection evolution : Module.End ℝ V)
    (initial : V) (time : ℕ) :
    retainedState projection evolution initial time +
        discardedState projection evolution initial time =
      (evolution ^ time) initial := by
  simp [retainedState, discardedState]

private theorem projection_retained (projection evolution : Module.End ℝ V)
    (hidempotent : projection * projection = projection) (initial : V) (time : ℕ) :
    projection (retainedState projection evolution initial time) =
      retainedState projection evolution initial time := by
  exact congrArg (fun operator : Module.End ℝ V ↦ operator ((evolution ^ time) initial)) hidempotent

private theorem projection_discarded (projection evolution : Module.End ℝ V)
    (hidempotent : projection * projection = projection) (initial : V) (time : ℕ) :
    (1 - projection) (discardedState projection evolution initial time) =
      discardedState projection evolution initial time := by
  have hp := congrArg (fun operator : Module.End ℝ V ↦ operator ((evolution ^ time) initial))
    hidempotent
  change projection (projection ((evolution ^ time) initial)) =
    projection ((evolution ^ time) initial) at hp
  simp [discardedState, hp]

theorem projected_block_steps (projection evolution : Module.End ℝ V)
    (hidempotent : projection * projection = projection) (initial : V) (time : ℕ) :
    retainedState projection evolution initial (time + 1) =
      (projection * evolution * projection) (retainedState projection evolution initial time) +
      (projection * evolution * (1 - projection))
        (discardedState projection evolution initial time) ∧
    discardedState projection evolution initial (time + 1) =
      ((1 - projection) * evolution * projection)
        (retainedState projection evolution initial time) +
      ((1 - projection) * evolution * (1 - projection))
        (discardedState projection evolution initial time) := by
  have ha := projection_retained projection evolution hidempotent initial time
  have hb := projection_discarded projection evolution hidempotent initial time
  have hab := retained_add_discarded projection evolution initial time
  constructor
  · simp only [Module.End.mul_apply]
    rw [ha, hb, ← map_add, ← map_add, hab]
    simp [retainedState, pow_succ']
  · simp only [Module.End.mul_apply]
    rw [ha, hb, ← map_add, ← map_add, hab]
    simp [discardedState, pow_succ']

/-- The report's eliminated-state identity for any idempotent projection and
any linear evolution, with all four blocks derived from those operators. -/
theorem projected_memory (projection evolution : Module.End ℝ V)
    (hidempotent : projection * projection = projection) (initial : V) (time : ℕ) :
    retainedState projection evolution initial (time + 1) =
      (projection * evolution * projection) (retainedState projection evolution initial time) +
      (projection * evolution * (1 - projection))
        ((((1 - projection) * evolution * (1 - projection)) ^ time)
          (discardedState projection evolution initial 0)) +
      ∑ earlier ∈ Finset.range time,
        (projection * evolution * (1 - projection))
          ((((1 - projection) * evolution * (1 - projection)) ^ (time - 1 - earlier))
            (((1 - projection) * evolution * projection)
              (retainedState projection evolution initial earlier))) :=
  retained_memory _ _ _ _ _ _
    (fun time ↦ (projected_block_steps projection evolution hidempotent initial time).1)
    (fun time ↦ (projected_block_steps projection evolution hidempotent initial time).2) time

end Descent.Portability.ExactMemoryLaw
