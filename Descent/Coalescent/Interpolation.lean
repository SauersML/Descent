/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Coalescent.StateSpace

assert_below Descent.Pangenome Descent.PopGen Descent.Spectral Descent.Blindness
assert_below Descent.Conditionals Descent.Portability Descent.Decision Descent.Program

namespace Descent

/-!
# Between two comparable states there is a path, and every path has the same length

K-C (1.4) gives the coalescent's transitions as covers: `ξ ≺ η` when `ξ ⊂ η` and
`|ξ| = |η| + 1`.  `Descent.Coalescent.StateSpace` proves that covers are exactly the
merges of two classes, and `Descent.Coalescent.Lumping` counts them.  Neither answers the
question this file answers, which is what a coarsening that is NOT a cover costs:

**If `ξ ≤ η`, the coalescent can get from `ξ` to `η`, every way of doing so takes exactly
`|ξ| - |η|` coalescences, and there is no shorter route.**

Both halves are needed and neither is formal bookkeeping.

*Every path has that length* is the easy half and follows from covers dropping the block
count by exactly one, so a path's length is determined by its endpoints and not by which
pairs it chose.  It is what makes "the number of coalescences between two states" a
well-defined quantity at all.

*A path exists* is the half with content.  It needs `exists_cover_le_of_lt`: a state
strictly below `η` admits a cover still below `η`.  That is not automatic in a lattice —
it says the interval `[ξ, η]` in `𝓔ₙ` has no gaps — and the proof is that a pair `η`
relates and `ξ` does not gives a merge of two `ξ`-classes, which `merge_le_of_le_of_rel`
shows stays under `η` because a merge identifies the named pair and nothing else.

## Why the corpus needs it

`Descent.Pangenome.GraphCoalescent.MergerDepth` uses it to say what a pangenome graph does
when it merges a panel: the graph's construction is a coarsening, so it IS a number of
coalescences, and that number is `n - w`.  Without the theorem below "how many coalescences
did the graph perform" would not be a question with an answer.

## Main results

- `blocks_antitone`: a coarsening cannot gain blocks.
- `merge_le_of_le_of_rel`: a merge of two `ξ`-classes stays below any `ζ ≥ ξ` that already
  relates the pair.  The generalisation to arbitrary `ξ` of the `⊥` case that
  `Descent.Pangenome.GraphCoalescent.Visibility` needed.
- `exists_cover_le_of_lt`: **the interval has no gaps.**
- `CoalescencePath`: `k` coalescences carrying `ξ` to `η`.
- `blocks_of_coalescencePath`: a path of length `k` drops exactly `k` blocks.
- `coalescencePath_length_unique`: so the length is a function of the endpoints.
- `exists_coalescencePath`: **and one of that length exists.**
-/

namespace Coalescent

/-! ### A coarsening cannot gain blocks -/

/-- **A coarsening cannot gain blocks.**  `blockMap` is onto, so the coarser relation has no
more classes than the finer one.  K-C's block count is antitone in the state order, which is
why the coalescent is a death process rather than merely a monotone one. -/
theorem blocks_antitone {n : ℕ} {ξ η : ER n} (h : ξ ≤ η) : blocks η ≤ blocks ξ := by
  letI : Fintype (Quotient ξ) := Fintype.ofFinite _
  letI : Fintype (Quotient η) := Fintype.ofFinite _
  have hsurj := Fintype.card_le_of_surjective _ (blockMap_surjective h)
  simpa [blocks, Nat.card_eq_fintype_card] using hsurj

/-! ### A merge stays under anything that already relates its pair

`Descent.Coalescent.StateSpace.mergeMap_eq_iff` says a merge identifies the two named
classes and nothing else.  So a relation that contains `ξ` and relates one representative of
each named class contains the whole merge: there is nothing else in it to contain. -/

/-- **A merge of two `ξ`-classes stays below any coarsening that already relates them.**

The three cases are the three disjuncts of `mergeMap_eq_iff`, and each is a walk in `ζ`:
either the pair was already `ξ`-related, or it is the named pair in one order or the
other. -/
theorem merge_le_of_le_of_rel {n : ℕ} {ξ ζ : ER n} (hξ : ξ ≤ ζ) {A B : Quotient ξ}
    (hAB : A ≠ B) {x y : Fin n} (hx : Quotient.mk ξ x = A) (hy : Quotient.mk ξ y = B)
    (hrel : ζ.r x y) : merge ξ A B ≤ ζ := by
  intro u v huv
  have huv' : mergeMap ξ A B (Quotient.mk ξ u) = mergeMap ξ A B (Quotient.mk ξ v) := huv
  rcases (mergeMap_eq_iff ξ hAB (Quotient.mk ξ u) (Quotient.mk ξ v)).mp huv' with
    h | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact hξ (Quotient.exact h)
  · have hu : ζ.r u x := hξ (Quotient.exact (h1.trans hx.symm))
    have hv : ζ.r y v := hξ (Quotient.exact (hy.trans h2.symm))
    exact ζ.iseqv.trans hu (ζ.iseqv.trans hrel hv)
  · have hu : ζ.r u y := hξ (Quotient.exact (h1.trans hy.symm))
    have hv : ζ.r x v := hξ (Quotient.exact (hx.trans h2.symm))
    exact ζ.iseqv.trans hu (ζ.iseqv.trans (ζ.iseqv.symm hrel) hv)

/-- **The interval `[ξ, η]` in `𝓔ₙ` has no gaps.**  A state strictly below `η` admits a
cover that is still below `η`, so the coalescent can always take one step towards a target
coarsening without overshooting it.

This is what makes a coarsening a NUMBER OF COALESCENCES rather than merely a comparison.  A
pair that `η` relates and `ξ` does not names two `ξ`-classes; merging them is a cover, and
`merge_le_of_le_of_rel` is why it does not pass `η`. -/
theorem exists_cover_le_of_lt {n : ℕ} {ξ η : ER n} (hle : ξ ≤ η) (hne : ξ ≠ η) :
    ∃ ζ, Covers ξ ζ ∧ ζ ≤ η := by
  obtain ⟨x, y, hη, hξ⟩ : ∃ x y : Fin n, η.r x y ∧ ¬ ξ.r x y := by
    by_contra hcon
    push_neg at hcon
    exact hne (Setoid.ext fun x y ↦ ⟨fun h ↦ hle h, fun h ↦ hcon x y h⟩)
  have hAB : Quotient.mk ξ x ≠ Quotient.mk ξ y := fun h ↦ hξ (Quotient.exact h)
  exact ⟨merge ξ (Quotient.mk ξ x) (Quotient.mk ξ y), merge_covers ξ hAB,
    merge_le_of_le_of_rel hle hAB rfl rfl hη⟩

/-! ### Paths of coalescences -/

/-- `k` coalescences carrying `ξ` to `η`: a chain of `k` covers.  K-C's transitions, iterated.

Empirical status: NOT AN EMPIRICAL CLAIM.  It counts steps in the transition graph of
`𝓔ₙ`; how long those steps TAKE is `Descent.Coalescent.HoldingTime`, and nothing here is a
statement about time. -/
def CoalescencePath {n : ℕ} (k : ℕ) (ξ η : ER n) : Prop :=
  match k with
  | 0 => ξ = η
  | k + 1 => ∃ ζ, Covers ξ ζ ∧ CoalescencePath k ζ η

/-- A path of `k` coalescences drops exactly `k` blocks, because each cover drops one. -/
theorem blocks_of_coalescencePath {n : ℕ} : ∀ (k : ℕ) {ξ η : ER n},
    CoalescencePath k ξ η → blocks η + k = blocks ξ := by
  intro k
  induction k with
  | zero =>
    intro ξ η h
    have hxy : ξ = η := h
    subst hxy
    simp
  | succ k ih =>
    intro ξ η h
    obtain ⟨ζ, hcov, hpath⟩ := h
    have h1 := ih hpath
    have h2 := hcov.2
    omega

/-- A path only coarsens. -/
theorem le_of_coalescencePath {n : ℕ} : ∀ (k : ℕ) {ξ η : ER n},
    CoalescencePath k ξ η → ξ ≤ η := by
  intro k
  induction k with
  | zero =>
    intro ξ η h
    exact le_of_eq h
  | succ k ih =>
    intro ξ η h
    obtain ⟨ζ, hcov, hpath⟩ := h
    exact le_trans hcov.1 (ih hpath)

/-- **The number of coalescences between two states is a function of the states.**  Two
paths with the same endpoints have the same length, whichever pairs they chose to merge and
in whichever order. -/
theorem coalescencePath_length_unique {n : ℕ} {k k' : ℕ} {ξ η : ER n}
    (h : CoalescencePath k ξ η) (h' : CoalescencePath k' ξ η) : k = k' := by
  have hk := blocks_of_coalescencePath k h
  have hk' := blocks_of_coalescencePath k' h'
  omega

/-- **And a path of that length exists.**  Every coarsening is realised by a sequence of
coalescences, so `|ξ| - |η|` is not merely a lower bound on the work: it is the work.

The induction is on the block difference, and `exists_cover_le_of_lt` supplies each step. -/
theorem exists_coalescencePath {n : ℕ} : ∀ (d : ℕ) {ξ η : ER n}, ξ ≤ η →
    blocks ξ - blocks η = d → CoalescencePath d ξ η := by
  intro d
  induction d with
  | zero =>
    intro ξ η hle hd
    have h1 : blocks η ≤ blocks ξ := blocks_antitone hle
    have h2 : blocks ξ = blocks η := by omega
    exact eq_of_le_of_blocks_eq hle h2
  | succ d ih =>
    intro ξ η hle hd
    have hne : ξ ≠ η := by
      intro h
      subst h
      omega
    obtain ⟨ζ, hcov, hζ⟩ := exists_cover_le_of_lt hle hne
    refine ⟨ζ, hcov, ih hζ ?_⟩
    have h2 := hcov.2
    have h1 : blocks η ≤ blocks ζ := blocks_antitone hζ
    omega

/-- The headline in the form it is used: a coarsening is exactly `|ξ| - |η|` coalescences. -/
theorem exists_coalescencePath_sub {n : ℕ} {ξ η : ER n} (hle : ξ ≤ η) :
    CoalescencePath (blocks ξ - blocks η) ξ η :=
  exists_coalescencePath _ hle rfl

end Coalescent

end Descent
