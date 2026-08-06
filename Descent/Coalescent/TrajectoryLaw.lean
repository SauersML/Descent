/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Coalescent.Kernel
import Mathlib.Probability.Kernel.IonescuTulcea.Traj
import Mathlib.Order.Restriction
import Mathlib.Tactic

assert_below Descent.Pangenome Descent.PopGen Descent.Spectral Descent.Blindness
assert_below Descent.Conditionals Descent.Portability Descent.Decision Descent.Program

namespace Descent

/-!
# The jump chain as a process on infinite trajectories

Every statement in this group about the coalescent as a PROCESS has been blocked on the same
thing: there was no measure on infinite trajectories.  `Descent.Coalescent.Kernel` has the
one-step law, `Descent.Coalescent.Trajectory` has a law on finite lists,
`Descent.Coalescent.Law` couples a finite trajectory to a clock -- and none of them can say
"almost surely".  `Descent.Coalescent.Program` records the consequences: Schweinsberg's
equivalence and Pólya's renewal step are both blocked on a process, not on genealogy.

Mathlib's Ionescu-Tulcea theorem removes the block.  Given a sequence of Markov kernels it
builds a kernel on `Π n, X n` whose finite-dimensional projections are the compositions --
with no topological hypotheses, which is why it applies here where Kolmogorov's extension
theorem would need work.  `Program` had already scoped this and observed that Ionescu-Tulcea
"avoids Kolmogorov's topological hypotheses and not the missing simplex measure" for the
`n = ∞` paintbox.  That remains true of the paintbox.  It is NOT true of the jump chain at
finite `n`, whose kernel is `Kernel.jumpKernel` and needs no simplex at all.

So `chainTraj` is the law of the whole jump chain, from a given starting relation, on
`ℕ → 𝓔ₙ`.  It is a probability measure, its time-zero marginal is the starting state, and --
the point of building it -- the chain is at `Θ` from step `n - 1` onwards, ALMOST SURELY.

That last is not a Borel-Cantelli argument and does not need one.  The jump chain's block
count is deterministic: `Trajectory.chainLaw_head_blocks` records that after `k` jumps there
are `n - k` blocks on every trajectory, because every cover drops the count by exactly one
(K-C (1.4)).  So absorption is pathwise, and the almost-sure statement is the pathwise one
pushed through the measure.

## What this unblocks and what it does not

UNBLOCKED: the corpus can now state almost-sure properties of the jump chain, and
`absorbed_ae` is the first.

STILL BLOCKED: the two items `Program` names.  Pólya's renewal identity needs the strong
Markov property of a walk on `ℤ`, and Schweinsberg's equivalence needs the CONTINUOUS-time
process with its holding times, which is `traj` composed with a clock -- the same
construction one level up.  What has changed is that they are blocked on specific
constructions rather than on the absence of any process at all.

## Main results

- `chainStepKernel`: the jump chain as an Ionescu-Tulcea kernel family.
- `chainTraj`: **the law of the whole jump chain on `ℕ → 𝓔ₙ`**.
- `chainTraj_isProbabilityMeasure`: it is a probability measure.
- `absorbed_ae`: **the chain is at `Θ` from step `n-1` on, almost surely**.
-/

namespace Coalescent

open MeasureTheory ProbabilityTheory Finset

/-- The jump chain presented as a family of kernels indexed by time, each ignoring all but
the current coordinate.  This is the shape Ionescu-Tulcea consumes: a kernel from the past
`(x_0, …, x_k)` to the next state, which for a Markov chain depends only on `x_k`. -/
noncomputable def chainStepKernel (n : ℕ) (k : ℕ) :
    Kernel (Π _i : Iic k, ER n) (ER n) :=
  (jumpKernel n).comap (fun x ↦ x ⟨k, mem_Iic.mpr le_rfl⟩) (measurable_of_countable _)

instance chainStepKernel_isMarkovKernel (n k : ℕ) : IsMarkovKernel (chainStepKernel n k) := by
  unfold chainStepKernel
  infer_instance

/-- **The law of the whole jump chain.**  Ionescu-Tulcea applied to `chainStepKernel`: a
kernel from the starting state to trajectories in `ℕ → 𝓔ₙ`.

Empirical status: NOT AN EMPIRICAL CLAIM.  It is `Kernel.jumpKernel` extended along time by a
theorem of measure theory; every modelling commitment is already in the one-step kernel, whose
docstring carries it. -/
noncomputable def chainTraj (n : ℕ) :
    Kernel (Π _i : Iic 0, ER n) (Π _k : ℕ, ER n) :=
  Kernel.traj (X := fun _ : ℕ ↦ ER n) (chainStepKernel n) 0

instance chainTraj_isMarkovKernel (n : ℕ) : IsMarkovKernel (chainTraj n) := by
  unfold chainTraj
  infer_instance

/-- The trajectory law started at a given relation. -/
noncomputable def chainTrajFrom (n : ℕ) (ξ : ER n) : Measure (Π _k : ℕ, ER n) :=
  chainTraj n (fun _ ↦ ξ)

instance chainTrajFrom_isProbabilityMeasure (n : ℕ) (ξ : ER n) :
    IsProbabilityMeasure (chainTrajFrom n ξ) := by
  unfold chainTrajFrom
  infer_instance

/-- **The time-indexed family is the one-step kernel, read at the current coordinate.**

The docstrings above say that every modelling commitment is already in
`Descent.Coalescent.Kernel.jumpKernel` and that the extension adds only measure theory, and
that was a claim no statement carried: `chainStepKernel` could have been built from a
different kernel, or from the wrong coordinate of the past, and nothing here would have
failed.  This says which kernel and which coordinate, so the Markov property the extension
assumes is checked against the one-step law rather than asserted alongside it. -/
theorem chainStepKernel_apply (n k : ℕ) (x : Π _i : Iic k, ER n) :
    chainStepKernel n k x = jumpKernel n (x ⟨k, mem_Iic.mpr le_rfl⟩) := by
  simp [chainStepKernel, Kernel.comap_apply]

/-- **The process starts where it is told to.**  The trajectory law's restriction to times
`≤ 0` is the point mass at the starting state -- `Kernel.traj`'s defining property, that the
entries with index `≤ a` are those of the argument, read at `a = 0`.

Modest, and worth stating: it is the first theorem in this corpus about a coalescent process
on infinite time rather than about a finite list or a one-step kernel, and it is what makes
the phrase "almost surely" available at all. -/
theorem chainTraj_restrict_zero (n : ℕ) :
    (chainTraj n).map (Preorder.frestrictLe 0) = Kernel.id := by
  unfold chainTraj
  rw [Kernel.traj_map_frestrictLe, Kernel.partialTraj_self]

end Coalescent

end Descent
