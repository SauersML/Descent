/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Pangenome.AncestralLocality.SupercriticalGiantLaw
import Descent.Pangenome.AncestralLocality.SupercriticalUnconditional

assert_below Descent.PopGen Descent.Spectral Descent.Blindness Descent.Conditionals
assert_below Descent.Portability Descent.Decision Descent.Program

/-!
# The locality transition of Theorem 5 without the Erdős–Rényi hypothesis

The note's Theorem 5 states the supercritical limit law (6.2) for `G(m, α/m)` with `α > 1`. The
reach fraction `|C_m(A)|/m` of `k` roots tends to `s = giantFraction α` with probability
`1 - (1 - s)^k` and to `0` with probability `(1 - s)^k`. The note's proof cites the Erdős–Rényi
giant component theorem without proving it. The corpus carried that theorem as the hypothesis
`GiantComponentLaw α` of `Descent.Pangenome.AncestralLocality.SupercriticalReach`, and at every
rate above `1` as `SupercriticalGiantComponentLaw` of
`Descent.Pangenome.AncestralLocality.SupercriticalUnconditional`. This file removes it.

**The giant component theorem.** `giantComponentLaw_of_one_lt` of
`Descent.Pangenome.AncestralLocality.SupercriticalGiantLaw` proves the law at every `α > 1` from
the exploration lower bound, the uniform upper bound, sprinkling and the concentration of the
number of features in large components. So `SupercriticalGiantComponentLaw` holds
(`supercriticalGiantComponentLaw`). With the subcritical half `giantComponentLaw_of_lt_one`, the
law holds at every rate `α ≥ 0` except the critical `α = 1` (`giantComponentLaw_of_ne_one`).
`giantComponentLaw_two` is the witness at `α = 2`.

**(6.2) without hypotheses.** Take `α > 1` and queries of eventually `k` features. The chance that
the roots all miss the giant component tends to `(1 - s)^k`
(`tendsto_graphProb_disjoint_bigSet_of_one_lt`). The reach fraction is at most `ε` with
probability tending to `(1 - s)^k` for `0 < ε < s` (`tendsto_graphProb_reach_small_of_one_lt`).
It is within `ε` of `s` with probability tending to `1 - (1 - s)^k` for `0 < 2ε < s`
(`tendsto_graphProb_reach_giant_of_one_lt`). For queries of at most `k` features and every rate
`α ≥ 0` other than `1`, the reach fraction is within `ε` of `0` or of `s` with probability tending
to one (`tendsto_graphProb_reach_near_zero_or_giant_of_ne_one`).

Scope. The critical rate `α = 1` is not studied. The reach is `reach`, not the hereditary closure
itself (the note's Theorem 4). The limits come without rates, and the note's `k ≥ 2` is not
needed.

## Empirical status

None. The bodies are probabilities under `G(m, α/m)`, the giant fraction and their limits in `m`.
The graph law is supplied, and nothing is measured.
-/

namespace Descent.Pangenome.AncestralLocality

open Finset Filter Topology
open scoped Classical

noncomputable section

/-! ### The giant component theorem -/

/-- **The Erdős–Rényi giant component theorem at every rate above `1`**, the hypothesis of
`Descent.Pangenome.AncestralLocality.SupercriticalUnconditional`. -/
theorem supercriticalGiantComponentLaw : SupercriticalGiantComponentLaw :=
  fun _ hα ↦ giantComponentLaw_of_one_lt hα

/-- **The giant component law off the critical rate.** For every `α ≥ 0` with `α ≠ 1`, the
giant-component event of `G(m, α/m)` at every positive scale has probability tending to one. -/
theorem giantComponentLaw_of_ne_one {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≠ 1) :
    GiantComponentLaw α := by
  rcases lt_or_gt_of_ne hα1 with h | h
  · exact giantComponentLaw_of_lt_one hα0 h
  · exact giantComponentLaw_of_one_lt h

/-- **Witness**: the giant component law at the supercritical rate `α = 2`. -/
theorem giantComponentLaw_two : GiantComponentLaw 2 :=
  giantComponentLaw_of_one_lt (by norm_num)

/-! ### The limit law (6.2) -/

/-- **(6.2), the weight of the small branch.** For `α > 1` and queries of eventually `k`
features, the probability that the roots all miss the giant component tends to `(1 - s)^k`. -/
theorem tendsto_graphProb_disjoint_bigSet_of_one_lt {α : ℝ} (hα : 1 < α) {k : ℕ}
    (A : ∀ m : ℕ, Finset (Fin m)) (hA : ∀ᶠ m in atTop, (A m).card = k) :
    Tendsto (fun m : ℕ ↦ graphProb m (α / m) fun E ↦
      Disjoint (A m) (bigSet (edgeGraph E) (giantFraction α * m / 2))) atTop
        (𝓝 ((1 - giantFraction α) ^ k)) :=
  tendsto_graphProb_disjoint_bigSet (giantComponentLaw_of_one_lt hα) hα A hA

/-- **Theorem 5, supercritical, (6.2): the small branch.** For `α > 1`, queries of eventually `k`
features and `0 < ε < s`, `P(|C_m(A)|/m ≤ ε) → (1 - s)^k`. -/
theorem tendsto_graphProb_reach_small_of_one_lt {α : ℝ} (hα : 1 < α) {k : ℕ}
    (A : ∀ m : ℕ, Finset (Fin m)) (hA : ∀ᶠ m in atTop, (A m).card = k) {ε : ℝ} (hε : 0 < ε)
    (hεs : ε < giantFraction α) :
    Tendsto (fun m : ℕ ↦ graphProb m (α / m) fun E ↦
      ((reach (edgeGraph E) (A m)).card : ℝ) / m ≤ ε) atTop
        (𝓝 ((1 - giantFraction α) ^ k)) :=
  tendsto_graphProb_reach_small_of_supercritical supercriticalGiantComponentLaw hα A hA hε hεs

/-- **Theorem 5, supercritical, (6.2): the giant branch.** For `α > 1`, queries of eventually `k`
features and `0 < 2ε < s`, `P(||C_m(A)|/m - s| ≤ ε) → 1 - (1 - s)^k`. -/
theorem tendsto_graphProb_reach_giant_of_one_lt {α : ℝ} (hα : 1 < α) {k : ℕ}
    (A : ∀ m : ℕ, Finset (Fin m)) (hA : ∀ᶠ m in atTop, (A m).card = k) {ε : ℝ} (hε : 0 < ε)
    (hεs : 2 * ε < giantFraction α) :
    Tendsto (fun m : ℕ ↦ graphProb m (α / m) fun E ↦
      |((reach (edgeGraph E) (A m)).card : ℝ) / m - giantFraction α| ≤ ε) atTop
        (𝓝 (1 - (1 - giantFraction α) ^ k)) :=
  tendsto_graphProb_reach_giant_of_supercritical supercriticalGiantComponentLaw hα A hA hε hεs

/-- **Theorem 5: the support of the limit law off the critical rate.** For `α ≥ 0` with `α ≠ 1`
and queries of at most `k` features, the reach fraction is within `ε` of `0` or of
`giantFraction α` with probability tending to one. -/
theorem tendsto_graphProb_reach_near_zero_or_giant_of_ne_one {α : ℝ} (hα0 : 0 ≤ α)
    (hα1 : α ≠ 1) {k : ℕ} (A : ∀ m : ℕ, Finset (Fin m)) (hA : ∀ m, (A m).card ≤ k) {ε : ℝ}
    (hε : 0 < ε) :
    Tendsto (fun m : ℕ ↦ graphProb m (α / m) fun E ↦
      ((reach (edgeGraph E) (A m)).card : ℝ) / m ≤ ε ∨
        |((reach (edgeGraph E) (A m)).card : ℝ) / m - giantFraction α| ≤ ε) atTop (𝓝 1) :=
  tendsto_graphProb_reach_near_zero_or_giant (giantComponentLaw_of_ne_one hα0 hα1) hα0 A hA hε

end

end Descent.Pangenome.AncestralLocality
