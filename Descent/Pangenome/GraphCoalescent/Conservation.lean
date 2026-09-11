/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Pangenome.GraphCoalescent.HiddenLoads

assert_below Descent.PopGen Descent.Spectral Descent.Blindness Descent.Conditionals
assert_below Descent.Portability Descent.Decision Descent.Program

/-!
# Silent-merger conservation: the hidden excess and the two step counts

The spec is `PANGENOME_HIDDEN_CLOCK.md` §5, Theorem C, its combinatorial parts (C1) and (C5).

The hidden excess `hiddenExcess s ξ = |ξ| - |observed s ξ|` counts the true lineages beyond one
per reported component. It is the total excess `∑_C (L_C - 1)` of the loads of
`Descent.Pangenome.GraphCoalescent.HiddenLoads` (`sum_hiddenLoad_sub_one`). A silent merger lowers
it by one (`hiddenExcess_of_invisible`) and a visible merger leaves it unchanged
(`hiddenExcess_of_visible`). Before any coalescence it is the merger depth `n - w` of
`Descent.Pangenome.GraphCoalescent.MergerDepth` (`hiddenExcess_bot`), and at the root it is zero
(`hiddenExcess_top`).

(C1). Along a chain of covers the excess at the start is the excess at step `k` plus the number
of silent steps (`hiddenExcess_path_eq`), and the report's block count at the start is its block
count at step `k` plus the number of visible steps (`reportBlocks_path_eq`). So along any chain
of covers from the singletons to the root exactly `mergerDepth s = n - w` steps are silent and
exactly `w - 1` are visible (`card_silentSteps_visibleSteps`): the builder's `n - w`
coalescences at time zero reappear as the population's `n - w` silent mergers.

(C5). A finer interface merge gives a finer report of every state
(`observed_le_observed_of_graphKer_le`), so the coarser report is connected whenever the finer
one is (`observed_eq_top_of_graphKer_le`), on every path and at every time
(`connectedTimes_subset`); composing an interface with a further map coarsens its merge
(`graphKer_le_graphKer_comp`).

Scope. The stochastic parts of Theorem C, (C2)-(C4), are not formalized: they need the
continuous-time chain and its expectations.

## Empirical status

None. The bodies here are block counts of equivalence relations on a finite set, so no
measurement can bear on them.
-/

namespace Descent.Pangenome.GraphCoalescent

open Coalescent Finset
open scoped Classical

noncomputable section

/-! ### The hidden excess -/

/-- **The hidden excess** `E(ξ) = |ξ| - |observed s ξ|`: true lineages beyond one per reported
component. -/
def hiddenExcess {n : ℕ} (s : Fin n → Fin n) (ξ : ER n) : ℕ :=
  blocks ξ - blocks (observed s ξ)

/-- The truth has the report's blocks plus the hidden excess. -/
theorem hiddenExcess_add_reportBlocks {n : ℕ} (s : Fin n → Fin n) (ξ : ER n) :
    hiddenExcess s ξ + blocks (observed s ξ) = blocks ξ := by
  have h := blocks_antitone (le_observed s ξ)
  unfold hiddenExcess
  omega

/-- **The excess is the loads' total excess**: `E(ξ) = ∑_C (L_C - 1)`. -/
theorem sum_hiddenLoad_sub_one {n : ℕ} (s : Fin n → Fin n) (ξ : ER n) :
    ∑ C, (hiddenLoad s ξ C - 1) = hiddenExcess s ξ := by
  have hsplit : ∑ C, ((hiddenLoad s ξ C - 1) + 1) = ∑ C, hiddenLoad s ξ C :=
    sum_congr rfl fun C _ ↦ Nat.sub_add_cancel (hiddenLoad_pos s ξ C)
  rw [sum_add_distrib, sum_const, card_univ, smul_eq_mul, mul_one, sum_hiddenLoad,
    ← Nat.card_eq_fintype_card] at hsplit
  have h := hiddenExcess_add_reportBlocks s ξ
  have hcard : Nat.card (Quotient (observed s ξ)) = blocks (observed s ξ) := rfl
  omega

/-- **A silent merger spends one unit of hidden excess.** -/
theorem hiddenExcess_of_invisible {n : ℕ} (s : Fin n → Fin n) {ξ η : ER n} (h : Covers ξ η)
    (hobs : observed s η = observed s ξ) : hiddenExcess s η + 1 = hiddenExcess s ξ := by
  have h1 := hiddenExcess_add_reportBlocks s ξ
  have h2 := hiddenExcess_add_reportBlocks s η
  have h3 := h.2
  rw [hobs] at h2
  omega

/-- **A visible merger conserves the hidden excess.** -/
theorem hiddenExcess_of_visible {n : ℕ} (s : Fin n → Fin n) {ξ η : ER n} (h : Covers ξ η)
    (hobs : Covers (observed s ξ) (observed s η)) : hiddenExcess s η = hiddenExcess s ξ := by
  have h1 := hiddenExcess_add_reportBlocks s ξ
  have h2 := hiddenExcess_add_reportBlocks s η
  have h3 := h.2
  have h4 := hobs.2
  omega

/-- **Before any coalescence the excess is the merger depth** `n - w`: the builder's coalescences
are exactly the hidden excess the population still has to spend. -/
theorem hiddenExcess_bot {n : ℕ} (s : Fin n → Fin n) : hiddenExcess s ⊥ = mergerDepth s := by
  rw [hiddenExcess, observed_bot, blocks_bot, blocks_graphKer]
  rfl

/-- At the root nothing is hidden. -/
theorem hiddenExcess_top {n : ℕ} (s : Fin n → Fin n) : hiddenExcess s ⊤ = 0 := by
  rw [hiddenExcess, top_unique (le_observed s ⊤)]
  exact Nat.sub_self _

/-! ### Counting silent and visible steps -/

/-- The steps of a chain of states at which the report does not move: the silent mergers. -/
def silentSteps {n : ℕ} (s : Fin n → Fin n) (path : ℕ → ER n) (k : ℕ) : Finset ℕ :=
  (range k).filter fun i ↦ observed s (path (i + 1)) = observed s (path i)

/-- The steps of a chain of states at which the report moves: the visible mergers. -/
def visibleSteps {n : ℕ} (s : Fin n → Fin n) (path : ℕ → ER n) (k : ℕ) : Finset ℕ :=
  (range k).filter fun i ↦ observed s (path (i + 1)) ≠ observed s (path i)

/-- Along a chain of covers the excess at the start is the excess at step `k` plus the number of
silent steps before `k`. -/
theorem hiddenExcess_path_eq {n : ℕ} (s : Fin n → Fin n) (path : ℕ → ER n) :
    ∀ k, (∀ i < k, Covers (path i) (path (i + 1))) →
      hiddenExcess s (path 0) = hiddenExcess s (path k) + (silentSteps s path k).card := by
  intro k
  induction k with
  | zero => intro _; simp [silentSteps]
  | succ k ih =>
    intro hcov
    have hprev := ih fun i hi ↦ hcov i (Nat.lt_succ_of_lt hi)
    have hstep := hcov k (Nat.lt_succ_self k)
    rw [hprev]
    unfold silentSteps
    rw [range_add_one, filter_insert]
    split_ifs with hsilent
    · rw [card_insert_of_notMem (by simp)]
      have := hiddenExcess_of_invisible s hstep hsilent
      omega
    · rcases observed_eq_or_covers s hstep with hobs | hobs
      · exact absurd hobs hsilent
      · have := hiddenExcess_of_visible s hstep hobs
        omega

/-- Along a chain of covers the report's block count at the start is its block count at step
`k` plus the number of visible steps before `k`. -/
theorem reportBlocks_path_eq {n : ℕ} (s : Fin n → Fin n) (path : ℕ → ER n) :
    ∀ k, (∀ i < k, Covers (path i) (path (i + 1))) →
      blocks (observed s (path 0)) =
        blocks (observed s (path k)) + (visibleSteps s path k).card := by
  intro k
  induction k with
  | zero => intro _; simp [visibleSteps]
  | succ k ih =>
    intro hcov
    have hprev := ih fun i hi ↦ hcov i (Nat.lt_succ_of_lt hi)
    have hstep := hcov k (Nat.lt_succ_self k)
    rw [hprev]
    unfold visibleSteps
    rw [range_add_one, filter_insert]
    split_ifs with hvisible
    · rw [card_insert_of_notMem (by simp)]
      rcases observed_eq_or_covers s hstep with hobs | hobs
      · exact absurd hobs hvisible
      · have := hobs.2
        omega
    · rw [not_not.mp hvisible]

/-- **Spec (C1).** Along any chain of covers from the singletons to the root, exactly
`mergerDepth s = n - w` steps are silent mergers and exactly `w - 1` are visible. -/
theorem card_silentSteps_visibleSteps {n : ℕ} (hn : 0 < n) (s : Fin n → Fin n)
    (path : ℕ → ER n) (k : ℕ) (hstart : path 0 = ⊥) (hend : path k = ⊤)
    (hcov : ∀ i < k, Covers (path i) (path (i + 1))) :
    (silentSteps s path k).card = mergerDepth s ∧
      (visibleSteps s path k).card = Linkage.width s - 1 := by
  haveI : NeZero n := ⟨hn.ne'⟩
  have hE := hiddenExcess_path_eq s path k hcov
  have hr := reportBlocks_path_eq s path k hcov
  rw [hstart, hend, hiddenExcess_bot, hiddenExcess_top] at hE
  rw [hstart, hend, observed_bot, blocks_graphKer, top_unique (le_observed s ⊤), blocks_top] at hr
  exact ⟨by omega, by omega⟩

/-! ### Refining the interface refines the report -/

/-- Composing an interface with a further map coarsens its merge. -/
theorem graphKer_le_graphKer_comp {n : ℕ} (s φ : Fin n → Fin n) :
    graphKer s ≤ graphKer (φ ∘ s) := by
  intro x y hxy
  rw [graphKer_rel_iff] at hxy ⊢
  exact congrArg φ hxy

/-- **Spec (C5).** A finer interface merge gives a finer report of every state. -/
theorem observed_le_observed_of_graphKer_le {n : ℕ} {s s' : Fin n → Fin n}
    (h : graphKer s ≤ graphKer s') (ξ : ER n) : observed s ξ ≤ observed s' ξ :=
  sup_le_sup_left h ξ

/-- **Spec (C5), connection.** Whenever the finer report is connected, so is the coarser one. -/
theorem observed_eq_top_of_graphKer_le {n : ℕ} {s s' : Fin n → Fin n}
    (h : graphKer s ≤ graphKer s') {ξ : ER n} (htop : observed s ξ = ⊤) :
    observed s' ξ = ⊤ :=
  top_unique (htop ▸ observed_le_observed_of_graphKer_le h ξ)

/-- **Spec (C5), pathwise.** On every path of states, the times at which the finer report is
connected are times at which the coarser report is connected, so the coarser interface's first
connection time is at most the finer one's. -/
theorem connectedTimes_subset {n : ℕ} {Time : Type*} {s s' : Fin n → Fin n}
    (h : graphKer s ≤ graphKer s') (path : Time → ER n) :
    {t | observed s (path t) = ⊤} ⊆ {t | observed s' (path t) = ⊤} :=
  fun _ ht ↦ observed_eq_top_of_graphKer_le h ht

end

end Descent.Pangenome.GraphCoalescent
