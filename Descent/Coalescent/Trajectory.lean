/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Coalescent.Kernel
import Descent.Coalescent.Path
import Mathlib.Tactic

namespace Descent

/-!
# The jump chain as a law on trajectories

`Descent.Coalescent.Kernel` gives the jump chain's one-step law; `Descent.Coalescent.Path`
gives a path built from a trajectory supplied by hand.  This file closes the gap between
them: `chainLaw` is a probability mass function whose values are whole TRAJECTORIES --
lists of equivalence relations -- so the jump chain is a random process and not just a
transition rule.

Kingman writes a sample path as

  `Δ = ℛ_n ≺ ℛ_{n-1} ≺ ⋯ ≺ ℛ_2 ≺ ℛ_1 = Θ`,                                     K-C (1.13)

and the theorem here is that every trajectory in the support looks like that:
`chainLaw_support_chain'` says consecutive entries are covers, except where the chain has
already been absorbed, in which case it repeats -- the total-kernel convention recorded in
`Kernel.jumpKernel_absorbing`.  `chainLaw_length` and `chainLaw_getLast` place the
trajectory: it has one entry per jump plus the start, and it starts at `Δ`.

This is the discrete half of the law that `Descent.Coalescent.Program` item 5 asks for.  The
half still missing is the holding times: they are continuous, and putting a measure on
`ℕ → ℝ` with independent exponential coordinates is a construction this corpus does not
have.  With it, `Path.pathState` applied to a `chainLaw` trajectory and an independent hold
sequence would be K-G section 6's temporal coupling outright, and independence would hold by
construction -- which is Theorem 3's direction, not Theorem 1's.

## Main results

- `mem_support_jumpLaw`: the one-step law's support is exactly the covers.
- `chainLaw`: the law of a whole trajectory, newest state first.
- `chainLaw_length`, `chainLaw_getLast`: `k` jumps from `Δ`.
- `chainLaw_support_chain'`: **K-C (1.13)** -- consecutive states are covers, or repeat
  once absorbed.
-/

namespace Coalescent

open scoped Classical

/-- **The one-step law's support is exactly the covers.**  From a state with two or more
blocks the chain moves to one of its covers, and to nothing else -- which is what makes the
trajectories below descending chains. -/
theorem mem_support_jumpLaw {n : ℕ} {ξ η : ER n} (hk : 2 ≤ blocks ξ) :
    η ∈ (jumpLaw ξ).support ↔ Covers ξ η := by
  classical
  rw [jumpLaw, dif_pos hk, PMF.mem_support_map_iff]
  constructor
  · rintro ⟨s, -, rfl⟩
    exact s.2
  · intro h
    refine ⟨⟨η, h⟩, ?_, rfl⟩
    letI := covers_nonempty ξ hk
    simp [jumpStep, PMF.support_uniformOfFintype]

/-- An absorbed state stays put: the total kernel's convention, seen in the support. -/
theorem mem_support_jumpLaw_of_absorbed {n : ℕ} {ξ η : ER n} (hk : blocks ξ < 2) :
    η ∈ (jumpLaw ξ).support ↔ η = ξ := by
  classical
  rw [jumpLaw, dif_neg (by omega), PMF.mem_support_pure_iff]

/-- **The law of a whole trajectory of the jump chain**, newest state at the head.

Empirical status: NOT AN EMPIRICAL CLAIM.  It is `Kernel.jumpLaw` iterated; every step is
the uniform choice among covers that K-C (1.3) forces. -/
noncomputable def chainLaw (n : ℕ) : ℕ → PMF (List (ER n))
  | 0 => PMF.pure [Delta n]
  | k + 1 => (chainLaw n k).bind fun l =>
      match l with
      | [] => PMF.pure []
      | x :: rest => (jumpLaw x).map fun y => y :: x :: rest

/-- A trajectory after `k` jumps has `k + 1` entries. -/
theorem chainLaw_length {n : ℕ} (k : ℕ) {l : List (ER n)} (hl : l ∈ (chainLaw n k).support) :
    l.length = k + 1 := by
  classical
  induction k generalizing l with
  | zero =>
      rw [chainLaw, PMF.mem_support_pure_iff] at hl
      rw [hl]
      rfl
  | succ m ih =>
      rw [chainLaw, PMF.mem_support_bind_iff] at hl
      obtain ⟨l', hl', hmem⟩ := hl
      have hlen := ih hl'
      match l', hlen with
      | x :: rest, hlen =>
          rw [PMF.mem_support_map_iff] at hmem
          obtain ⟨y, -, rfl⟩ := hmem
          simp only [List.length_cons] at hlen ⊢
          omega

/-- Every trajectory starts at `Δ`, which is K-C (1.1). -/
theorem chainLaw_getLast {n : ℕ} (k : ℕ) {l : List (ER n)} (hl : l ∈ (chainLaw n k).support) :
    l.getLast? = some (Delta n) := by
  classical
  induction k generalizing l with
  | zero =>
      rw [chainLaw, PMF.mem_support_pure_iff] at hl
      rw [hl]
      rfl
  | succ m ih =>
      rw [chainLaw, PMF.mem_support_bind_iff] at hl
      obtain ⟨l', hl', hmem⟩ := hl
      have hlast := ih hl'
      have hlen := chainLaw_length m hl'
      match l' with
      | x :: rest =>
          rw [PMF.mem_support_map_iff] at hmem
          obtain ⟨y, -, rfl⟩ := hmem
          rw [List.getLast?_cons_cons]
          exact hlast

/-- **K-C (1.13): every trajectory is a descending chain of covers.**

`Δ = ℛ_n ≺ ℛ_{n-1} ≺ ⋯ ≺ ℛ_1 = Θ`.  The disjunct `y = x` is the absorbing convention of
`Kernel.jumpKernel_absorbing`: Kingman's chain terminates on reaching a state with no
covers, and a total kernel cannot terminate, so it repeats.  Before absorption the two
descriptions agree exactly. -/
theorem chainLaw_support_chain' {n : ℕ} (k : ℕ) {l : List (ER n)}
    (hl : l ∈ (chainLaw n k).support) :
    List.Chain' (fun y x => Covers x y ∨ y = x) l := by
  classical
  induction k generalizing l with
  | zero =>
      rw [chainLaw, PMF.mem_support_pure_iff] at hl
      rw [hl]
      exact List.chain'_singleton _
  | succ m ih =>
      rw [chainLaw, PMF.mem_support_bind_iff] at hl
      obtain ⟨l', hl', hmem⟩ := hl
      have hchain := ih hl'
      have hlen := chainLaw_length m hl'
      match l' with
      | x :: rest =>
          rw [PMF.mem_support_map_iff] at hmem
          obtain ⟨y, hy, rfl⟩ := hmem
          refine List.Chain'.cons ?_ hchain
          rcases lt_or_ge (blocks x) 2 with hb | hb
          · exact Or.inr ((mem_support_jumpLaw_of_absorbed hb).mp hy)
          · exact Or.inl ((mem_support_jumpLaw hb).mp hy)

/-- The head of a trajectory is the current state; every entry after the first jump is a
state the chain can be in. -/
theorem chainLaw_ne_nil {n : ℕ} (k : ℕ) {l : List (ER n)} (hl : l ∈ (chainLaw n k).support) :
    l ≠ [] := by
  intro hnil
  have := chainLaw_length k hl
  rw [hnil] at this
  simp at this

end Coalescent

end Descent
