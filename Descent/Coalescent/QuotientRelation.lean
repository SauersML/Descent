/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Coalescent.StateSpace
import Mathlib.Tactic

namespace Descent

/-!
# `η/ξ`: the relation a later state induces on an earlier one's blocks

K-C section 4 describes the coalescent's transition function by looking at the process from
a state it has reached: "any such `η` can be described by the relation `η/ξ` which it induces
on the equivalence classes of `ξ`", and the post-`s` process is `R_t^{(≥s)} = R_{s+t}/R_s`
(4.10).  K-C (2.4) is the same idea for the jump chain: the `l`-step transition probability
from a state with `k` blocks has the form of the absolute probability (2.3) with `n` replaced
by `k`, and with the class sizes taken in `η/ξ`.

That quotient relation is what this file supplies, and it costs nothing to define once
`blockMap` exists: `η/ξ` is the kernel of the map on blocks that `ξ ≤ η` induces.  Being a
kernel, it is an equivalence relation with no argument, and its block count is `η`'s own
(`blocks_quotientRelation`) -- which is the statement that looking at the coalescent from a
state it has reached loses nothing.

The self-similarity K-C (2.4) rests on is then visible: a state with `k` blocks, viewed
through `η/ξ`, is a state on a `k`-element set, and the coalescent's moves from it are the
moves of a `k`-coalescent from `Δ`.  `covers_quotientRelation` is that correspondence for one
step.  Turning it into (2.4) needs the absolute probabilities transported along it, which
`Descent.Coalescent.Program` still lists under item 4.

## Main results

- `quotientRelation`: **K-C (4.10)**, `η/ξ`.
- `blocks_quotientRelation`: it has as many classes as `η` has.
- `quotientRelation_bot`: `ξ/ξ` is the discrete relation -- the process seen from now starts
  at `Δ`, as K-C (4.10) requires.
- `covers_quotientRelation`: a cover of `ξ` induces a cover of `Δ` on `ξ`'s blocks.
-/

namespace Coalescent

/-- **K-C (4.10): `η/ξ`.**  The relation `η` induces on the equivalence classes of `ξ`, for
`ξ ≤ η`.  It is the kernel of the induced map on blocks, hence an equivalence relation by
construction.

Empirical status: NOT AN EMPIRICAL CLAIM.  It is the change of viewpoint Kingman uses to
describe the post-`s` process, not a statement about a population. -/
def quotientRelation {n : ℕ} {ξ η : ER n} (h : ξ ≤ η) : Setoid (Quotient ξ) :=
  Setoid.ker (blockMap h)

theorem quotientRelation_rel {n : ℕ} {ξ η : ER n} (h : ξ ≤ η) (c d : Quotient ξ) :
    (quotientRelation h).r c d ↔ blockMap h c = blockMap h d := Iff.rfl

/-- Two elements are related in `η/ξ` exactly when they were related in `η` -- which is what
makes `η/ξ` a faithful record of `η` and not a lossy one. -/
theorem quotientRelation_mk {n : ℕ} {ξ η : ER n} (h : ξ ≤ η) (x y : Fin n) :
    (quotientRelation h).r (Quotient.mk ξ x) (Quotient.mk ξ y) ↔ η.r x y := by
  constructor
  · intro hr
    exact Quotient.exact (hr : blockMap h (Quotient.mk ξ x) = blockMap h (Quotient.mk ξ y))
  · intro hr
    show blockMap h (Quotient.mk ξ x) = blockMap h (Quotient.mk ξ y)
    exact Quotient.sound hr

/-- **`η/ξ` has as many classes as `η`.**  Looking at the coalescent from a state it has
already reached loses nothing: the blocks of `η/ξ` are the blocks of `η`. -/
theorem blocks_quotientRelation {n : ℕ} {ξ η : ER n} (h : ξ ≤ η) :
    Nat.card (Quotient (quotientRelation h)) = blocks η := by
  classical
  unfold quotientRelation blocks
  rw [Nat.card_congr (Setoid.quotientKerEquivRange _)]
  have hrange : Set.range (blockMap h) = Set.univ :=
    Set.range_eq_univ.mpr (blockMap_surjective h)
  rw [Nat.card_congr (Equiv.setCongr hrange), Nat.card_congr (Equiv.Set.univ _)]

/-- **`ξ/ξ` is `Δ`.**  The post-`s` process starts at the discrete relation on the blocks
present at time `s`, which is K-C (4.10)'s reason for calling it an `n`-coalescent with `n`
the current block count. -/
theorem quotientRelation_self {n : ℕ} (ξ : ER n) :
    quotientRelation (le_refl ξ) = ⊥ := by
  refine Setoid.ext fun c d => ⟨fun hcd => ?_, fun hcd => ?_⟩
  · induction c using Quotient.inductionOn with | _ x =>
        induction d using Quotient.inductionOn with | _ y =>
            have : ξ.r x y := (quotientRelation_mk (le_refl ξ) x y).mp hcd
            exact Quotient.sound this
  · show blockMap (le_refl ξ) c = blockMap (le_refl ξ) d
    rw [show c = d from hcd]

/-- **A cover of `ξ` induces a cover on `ξ`'s blocks.**  One merge upstairs is one merge
downstairs: the block count drops by one on both sides.  This is the one-step form of the
self-similarity K-C (2.4) rests on -- the coalescent from a `k`-block state moves like a
`k`-coalescent from `Δ`. -/
theorem blocks_quotientRelation_covers {n : ℕ} {ξ η : ER n} (hcov : Covers ξ η) :
    Nat.card (Quotient (quotientRelation hcov.1)) + 1 = blocks ξ := by
  rw [blocks_quotientRelation]
  exact hcov.2

end Coalescent

end Descent
