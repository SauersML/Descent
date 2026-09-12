/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Pangenome.AncestralLocality.ClosureReachability
import Descent.Pangenome.AncestralLocality.LocalityTransition

assert_below Descent.PopGen Descent.Spectral Descent.Blindness Descent.Conditionals
assert_below Descent.Portability Descent.Decision Descent.Program

/-!
# The hereditary closure on a random checking graph

`Descent.Pangenome.AncestralLocality.ClosureReachability` proves the note's Theorem 4: for a
query `A` of at least two features and nonnegative rates `r`, the hereditary closure of `π_A` is
`π_{Reach_G(A)}`, with `Reach_G(A) = directedReach r A`. `Descent.Pangenome.AncestralLocality.
LocalityTransition` bounds the size of `reach (edgeGraph E) A` in `G(m, α/m)`. This file joins the
two, so that Theorem 5 is a statement about the hereditary closure itself.

**The two reaches agree.** A checking graph with both orientations of every edge is carried by
rates that are positive exactly on the present edges. For such rates `directedReach r A` is
`reach (edgeGraph E) A` (`directedReach_eq_reach`). The degree-normalized rates of §6.1 are such
rates for every `β > 0` (`degreeRate_nonneg`, `degreeRate_pos_iff`), so their reach is
`reach (edgeGraph E) A` (`directedReach_degreeRate`).

**Theorem 4 on `G(m, α/m)`.** With the degree-normalized rates on the present edges of `E`, for
`|A| ≥ 2` every refinement of `P_{π_A}` from the `m`-th on is `P_{π_{reach (edgeGraph E) A}}`
(`iterate_refinementStep_degreeRate`). **(6.1) for the closure.** For `0 ≤ α < 1` the support
of that closure has expected size at most `|A|/(1 - α)` for every genome size
(`graphExpect_card_directedReach_le`).

Scope. Only the degree-normalized rates are joined explicitly; any rates positive exactly on the
present edges give the same reach by `directedReach_eq_reach`. The hereditary closure is read, as
in `ClosureReachability`, as the stable value of the refinement iteration (3.2), not through
Theorem 1's universal property. The supercritical limit law (6.2) is proved for `reach` in the
sibling modules and transfers through `directedReach_degreeRate`; it is not restated here.

## Empirical status

None. The bodies identify two finite reachability closures and restate an expectation bound
through that identity. Nothing is measured.
-/

namespace Descent.Pangenome.AncestralLocality

open Finset
open scoped Classical

noncomputable section

/-- **The reach of Theorem 4 is `reach` in the symmetric graph.** For rates `r` that are positive
exactly on the present edges of `E`, in both orientations, `Reach_G(A)` of the checking graph
carried by `r` is `reach (edgeGraph E) A`. -/
theorem directedReach_eq_reach {m : ℕ} (E : Finset (Sym2 (Fin m))) {r : Fin m → Fin m → ℝ}
    (hr : ∀ i j, 0 < r i j ↔ (edgeGraph E).Adj i j) (A : Finset (Fin m)) :
    directedReach r A = reach (edgeGraph E) A := by
  have hrel : (fun i j ↦ 0 < r i j) = (edgeGraph E).Adj := by
    funext i j
    exact propext (hr i j)
  ext v
  rw [mem_directedReach, mem_reach_iff, hrel]
  simp only [SimpleGraph.reachable_iff_reflTransGen]

/-- The degree-normalized rates are nonnegative for `β ≥ 0`. -/
theorem degreeRate_nonneg {m : ℕ} (G : SimpleGraph (Fin m)) {β : ℝ} (hβ : 0 ≤ β)
    (i j : Fin m) : 0 ≤ degreeRate G β i j := by
  unfold degreeRate
  split_ifs
  · exact div_nonneg hβ (Nat.cast_nonneg _)
  · exact le_rfl

/-- **The degree-normalized rates are positive exactly on the edges** when `β > 0`. -/
theorem degreeRate_pos_iff {m : ℕ} (G : SimpleGraph (Fin m)) {β : ℝ} (hβ : 0 < β)
    (i j : Fin m) : 0 < degreeRate G β i j ↔ G.Adj i j := by
  constructor
  · intro h
    by_contra hn
    rw [degreeRate_eq_zero G β hn] at h
    exact lt_irrefl 0 h
  · exact degreeRate_pos G hβ

/-- The reach carried by the degree-normalized rates on the present edges of `E` is
`reach (edgeGraph E) A`. -/
theorem directedReach_degreeRate {m : ℕ} (E : Finset (Sym2 (Fin m))) {β : ℝ} (hβ : 0 < β)
    (A : Finset (Fin m)) :
    directedReach (degreeRate (edgeGraph E) β) A = reach (edgeGraph E) A :=
  directedReach_eq_reach E (degreeRate_pos_iff (edgeGraph E) hβ) A

/-- **Theorem 4 on the checking graph of an edge set.** With the degree-normalized rates of §6.1
on the present edges of `E` and a query of at least two features, every hereditary refinement of
`P_{π_A}` from the `m`-th on is `P_{π_{reach (edgeGraph E) A}}`. -/
theorem iterate_refinementStep_degreeRate {m : ℕ} (E : Finset (Sym2 (Fin m))) {β : ℝ}
    (hβ : 0 < β) {A : Finset (Fin m)} (hA : 2 ≤ A.card) {n : ℕ} (hn : m ≤ n) :
    (refinementStep (checkKernel (degreeRate (edgeGraph E) β)))^[n] (agreeOn A) =
      agreeOn (reach (edgeGraph E) A) := by
  rw [iterate_refinementStep_agreeOn_eq_reach (degreeRate_nonneg (edgeGraph E) hβ.le) hA
    (by rwa [Fintype.card_fin]), directedReach_degreeRate E hβ A]

/-- **Theorem 5, (6.1), for the hereditary closure.** In `G(m, α / m)` with `0 ≤ α < 1` and the
degree-normalized rates, the support `Reach_G(A)` of the hereditary closure of `π_A` has expected
size at most `|A| / (1 - α)`, for every genome size `m`. -/
theorem graphExpect_card_directedReach_le {m : ℕ} {α β : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1)
    (hβ : 0 < β) (A : Finset (Fin m)) :
    graphExpect m (α / m)
        (fun E ↦ ((directedReach (degreeRate (edgeGraph E) β) A).card : ℝ)) ≤
      A.card / (1 - α) := by
  simp only [directedReach_degreeRate _ hβ]
  exact graphExpect_card_reach_le hα0 hα1 A

end

end Descent.Pangenome.AncestralLocality
