/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Coalescent.Kernel
import Descent.Coalescent.Path
import Mathlib.Tactic

assert_below Descent.Pangenome Descent.PopGen Descent.Spectral Descent.Blindness
assert_below Descent.Conditionals Descent.Portability Descent.Decision Descent.Program

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

/-- Trajectories are countable, so the discrete σ-algebra is the right one and costs nothing.

This instance is needed, not decorative: `Descent.Coalescent.Law` takes `PMF.toMeasure` of a
law on trajectories, and `toMeasure` requires a measurable structure on its type.  Without it
that file does not even typecheck. -/
scoped instance instMeasurableSpaceListER (n : ℕ) : MeasurableSpace (List (ER n)) := ⊤

instance instMeasurableSingletonClassListER (n : ℕ) :
    MeasurableSingletonClass (List (ER n)) :=
  ⟨fun _ ↦ trivial⟩

/-- **The law of a whole trajectory of the jump chain**, newest state at the head.

Empirical status: NOT AN EMPIRICAL CLAIM.  It is `Kernel.jumpLaw` iterated; every step is
the uniform choice among covers that K-C (1.3) forces. -/
noncomputable def chainLaw (n : ℕ) : ℕ → PMF (List (ER n))
  | 0 => PMF.pure [Delta n]
  | k + 1 => (chainLaw n k).bind fun l ↦
      match l with
      | [] => PMF.pure []
      | x :: rest => (jumpLaw x).map fun y ↦ y :: x :: rest

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

/-- **The successor step of `chainLaw`, destructured once.**  A trajectory after `m + 1`
jumps is a trajectory after `m` -- nonempty, by `chainLaw_length` -- carrying one more state
on the front, drawn from `jumpLaw` of its head.

Both theorems below open the successor case this way, and each wrote the eight lines out:
the same `bind` and `map` support rewrites, the same `match` on a list whose empty case
`chainLaw_length` rules out.  Neither step was doing anything specific to what it went on
to prove, which is what made them one block of text to `duplication` and one argument in
fact. -/
theorem mem_support_chainLaw_succ {n m : ℕ} {l : List (ER n)}
    (hl : l ∈ (chainLaw n (m + 1)).support) :
    ∃ (x y : ER n) (rest : List (ER n)),
      l = y :: x :: rest ∧ (x :: rest) ∈ (chainLaw n m).support
        ∧ y ∈ (jumpLaw x).support := by
  classical
  rw [chainLaw, PMF.mem_support_bind_iff] at hl
  obtain ⟨lPrev, hPrev, hmem⟩ := hl
  have hlen := chainLaw_length m hPrev
  match lPrev with
  | x :: rest =>
      rw [PMF.mem_support_map_iff] at hmem
      obtain ⟨y, hy, rfl⟩ := hmem
      exact ⟨x, y, rest, rfl, hPrev, hy⟩

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
      obtain ⟨x, y, rest, rfl, hPrev, -⟩ := mem_support_chainLaw_succ hl
      rw [List.getLast?_cons_cons]
      exact ih hPrev

/-- **K-C (1.13): every trajectory is a descending chain of covers.**

`Δ = ℛ_n ≺ ℛ_{n-1} ≺ ⋯ ≺ ℛ_1 = Θ`.  The disjunct `y = x` is the absorbing convention of
`Kernel.jumpKernel_absorbing`: Kingman's chain terminates on reaching a state with no
covers, and a total kernel cannot terminate, so it repeats.  Before absorption the two
descriptions agree exactly. -/
theorem chainLaw_support_chain' {n : ℕ} (k : ℕ) {l : List (ER n)}
    (hl : l ∈ (chainLaw n k).support) :
    List.Chain' (fun y x ↦ Covers x y ∨ y = x) l := by
  classical
  induction k generalizing l with
  | zero =>
      rw [chainLaw, PMF.mem_support_pure_iff] at hl
      rw [hl]
      exact List.chain'_singleton _
  | succ m ih =>
      obtain ⟨x, y, rest, rfl, hPrev, hy⟩ := mem_support_chainLaw_succ hl
      refine List.Chain'.cons ?_ (ih hPrev)
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

/-- **The block count is a deterministic function of the number of jumps.**  After `k` jumps
the chain has `n - k` blocks, on every trajectory, because K-C (1.4) makes every transition
drop the count by exactly one.

This is the structural reason K-C Theorem 1's independence is even possible: the death
process cannot learn anything about the jump chain from the block count, since the block
count is not random given the jump count.  Kingman notes it in passing at (1.9) -- "the
transition from `ξ` must be to a state `η` with `|η| = |ξ| - 1`" -- and it is doing real work
there. -/
theorem chainLaw_head_blocks {n : ℕ} :
    ∀ (k : ℕ), k < n → ∀ {l : List (ER n)}, l ∈ (chainLaw n k).support →
      ∀ {x : ER n}, l.head? = some x → blocks x + k = n := by
  intro k
  induction k with
  | zero =>
      intro _ l hl x hx
      rw [chainLaw, PMF.mem_support_pure_iff] at hl
      subst hl
      rw [List.head?_cons, Option.some_inj] at hx
      subst hx
      simpa using blocks_bot n
  | succ m ih =>
      intro hmn l hl x hx
      rw [chainLaw, PMF.mem_support_bind_iff] at hl
      obtain ⟨l', hl', hmem⟩ := hl
      have hlen := chainLaw_length m hl'
      match l' with
      | y :: rest =>
          rw [PMF.mem_support_map_iff] at hmem
          obtain ⟨z, hz, rfl⟩ := hmem
          rw [List.head?_cons, Option.some_inj] at hx
          have hy : blocks y + m = n := ih (by omega) hl' List.head?_cons
          have hy2 : 2 ≤ blocks y := by omega
          have hcov : Covers y z := (mem_support_jumpLaw hy2).mp hz
          have hc2 := hcov.2
          rw [← hx]
          omega

/-- **The law of `ℛ_k`**, the jump chain's state after `k` jumps: the head of the trajectory.

This is the object K-C (2.3) computes.  `Descent.Coalescent.JumpChain.absoluteProb` writes
down Kingman's formula for it; `blockLaw` is the law itself, so the two now have somewhere to
meet. -/
noncomputable def blockLaw (n k : ℕ) : PMF (ER n) :=
  (chainLaw n k).bind fun l ↦
    match l with
    | [] => PMF.pure (Delta n)
    | x :: _ => PMF.pure x

/-- **`ℛ_k` has exactly `n - k` blocks**, with probability one.  The support of the law is
confined to one level of the state space, which is `Trajectory.chainLaw_head_blocks` read as a
statement about the law rather than about trajectories -- and is why the death process and
the jump chain can be independent. -/
theorem blocks_of_mem_support_blockLaw {n : ℕ} {k : ℕ} (hk : k < n) {x : ER n}
    (hx : x ∈ (blockLaw n k).support) : blocks x + k = n := by
  classical
  rw [blockLaw, PMF.mem_support_bind_iff] at hx
  obtain ⟨l, hl, hmem⟩ := hx
  have hlen := chainLaw_length k hl
  match l with
  | y :: rest =>
      rw [PMF.mem_support_pure_iff] at hmem
      subst hmem
      exact chainLaw_head_blocks k hk hl List.head?_cons

/-- **The block count at every position, not just the head.**  Entry `i` of a trajectory
after `k` jumps is the state the chain was in `i` jumps ago, so it has `n - k + i` blocks.

`chainLaw_head_blocks` is the `i = 0` case.  The general statement is what a construction
like `Path.pathState` needs, because it reads the trajectory at whatever level the clock has
reached rather than always at the head. -/
theorem chainLaw_blocks_at {n : ℕ} :
    ∀ (k : ℕ), k < n → ∀ {l : List (ER n)}, l ∈ (chainLaw n k).support →
      ∀ i, i < l.length → blocks (l.getD i (Delta n)) = n - k + i := by
  intro k
  induction k with
  | zero =>
      intro _ l hl i hi
      rw [chainLaw, PMF.mem_support_pure_iff] at hl
      subst hl
      have hi0 : i = 0 := by
        simp only [List.length_cons, List.length_nil] at hi
        omega
      subst hi0
      simpa using blocks_bot n
  | succ m ih =>
      intro hmn l hl i hi
      rw [chainLaw, PMF.mem_support_bind_iff] at hl
      obtain ⟨l', hl', hmem⟩ := hl
      have hlen := chainLaw_length m hl'
      match l' with
      | y :: rest =>
          rw [PMF.mem_support_map_iff] at hmem
          obtain ⟨z, hz, rfl⟩ := hmem
          match i with
          | 0 =>
              have hhead : blocks z + (m + 1) = n :=
                chainLaw_head_blocks (m + 1) hmn
                  (by rw [chainLaw, PMF.mem_support_bind_iff]
                      exact ⟨y :: rest, hl', by rw [PMF.mem_support_map_iff]; exact ⟨z, hz, rfl⟩⟩)
                  List.head?_cons
              simp only [List.getD_cons_zero, Nat.add_zero]
              omega
          | j + 1 =>
              have hj : j < (y :: rest).length := by
                simp only [List.length_cons] at hi ⊢
                omega
              have hrec := ih (by omega) hl' j hj
              simp only [List.getD_cons_succ]
              omega

/-- A trajectory read as the chain function `Path` takes: `chainOfList l k` is the state with `k`
blocks, which on a full trajectory sits at position `k - 1`. -/
noncomputable def chainOfList {n : ℕ} (l : List (ER n)) (k : ℕ) : ER n :=
  l.getD (k - 1) (Delta n)

/-- **A full trajectory really does give the chain `Path` wants.**  On a trajectory of `n - 1`
jumps the state at index `k` has `k` blocks, which is `Path.blocks_pathState`'s hypothesis
`hblocks`.

The other hypothesis `Path` takes -- that consecutive states are covers -- is
`chainLaw_support_chain'` read at positions rather than as a `List.Chain'`, and converting
between those needs list-indexing lemmas this file does not develop.  So the connector is
half-built, and saying which half is better than implying it is whole. -/
theorem blocks_chainOfList {n : ℕ} (hn : 1 ≤ n) {l : List (ER n)}
    (hl : l ∈ (chainLaw n (n - 1)).support) {k : ℕ} (hk1 : 1 ≤ k) (hkn : k ≤ n) :
    blocks (chainOfList l k) = k := by
  have hlen : l.length = n := by
    have := chainLaw_length (n - 1) hl
    omega
  have hpos : blocks (l.getD (k - 1) (Delta n)) = n - (n - 1) + (k - 1) :=
    chainLaw_blocks_at (n - 1) (by omega) hl (k - 1) (by omega)
  unfold chainOfList
  omega

/-- **K-C (1.13) in full: the chain runs from `Δ` to `Θ` in `n - 1` jumps.**

`Δ = ℛ_n ≺ ℛ_{n-1} ≺ ⋯ ≺ ℛ_1 = Θ`.  The trajectory starts at `Δ`
(`chainLaw_getLast`), every step is a cover (`chainLaw_support_chain'`), the block count
after `k` jumps is `n - k` (`chainLaw_head_blocks`), and so after `n - 1` jumps the count is
`1`, which by `StateSpace.blocks_eq_one_iff` is `Θ`.  The transit time of K-C (1.11) is the
time this takes. -/
theorem chainLaw_head_eq_top {n : ℕ} [NeZero n] (hn : 2 ≤ n) {l : List (ER n)}
    (hl : l ∈ (chainLaw n (n - 1)).support) {x : ER n} (hx : l.head? = some x) :
    x = Theta n := by
  have hblocks : blocks x + (n - 1) = n := chainLaw_head_blocks (n - 1) (by omega) hl hx
  have : blocks x = 1 := by omega
  exact (blocks_eq_one_iff x).mp this

end Coalescent

end Descent
