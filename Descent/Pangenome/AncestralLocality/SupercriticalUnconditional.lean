/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Pangenome.AncestralLocality.SupercriticalBranches
import Descent.Pangenome.AncestralLocality.SupercriticalGiantLaw

assert_below Descent.PopGen Descent.Spectral Descent.Blindness Descent.Conditionals
assert_below Descent.Portability Descent.Decision Descent.Program

/-!
# The supercritical transition without hypotheses

`Descent.Pangenome.AncestralLocality.SupercriticalGiantLaw` proves the Erdős–Rényi giant component
theorem `GiantComponentLaw α` for every `α > 1` (`giantComponentLaw_of_one_lt`). This file records
two consequences.

## Continuity of the giant fraction

`SupercriticalConcentration.exists_lt_giantFraction_of_lt` gives the giant fraction from the left.
Here it is continuous above `1` (`continuousAt_giantFraction`). The survival map `s ↦ 1 - e^{-α s}`
lies above the diagonal exactly below the giant fraction, and below it above
(`lt_survivalMap_of_lt_giantFraction`, `survivalMap_lt_of_giantFraction_lt`, with the converses
`SupercriticalConcentration.lt_giantFraction_of_lt_survivalMap` and
`giantFraction_lt_of_survivalMap_lt`). The survival map is continuous in `α`, so at a point `a`
below `giantFraction α` it stays above the diagonal for rates near `α`. So `a` stays below their
giant fraction, and similarly from above.

## The limit law (6.2) for every `α > 1`

`SupercriticalBranches` proves the weights of (6.2) assuming `GiantComponentLaw α`. With
`giantComponentLaw_of_one_lt` they hold outright. For queries of eventually `k` features, the reach
fraction is small with probability tending to `(1 - s)^k`
(`tendsto_graphProb_reach_small_of_one_lt`), and within `ε` of `s` with probability tending to
`1 - (1 - s)^k` (`tendsto_graphProb_reach_giant_of_one_lt`).

Scope. The continuity is pointwise above `1`; the behaviour at `α = 1` is not studied.

## Empirical status

None. The bodies are the survival equation and its root, and probabilities under `G(m, α/m)` with
their limits in `m`. The graph law is supplied, and nothing is measured.
-/

set_option autoImplicit false

namespace Descent.Pangenome.AncestralLocality

open Finset Filter Topology
open scoped Classical

noncomputable section

/-! ### Continuity of the giant fraction -/

/-- Below the giant fraction the survival map lies above the diagonal. -/
theorem lt_survivalMap_of_lt_giantFraction {α s : ℝ} (hα : 1 < α) (hs : 0 < s)
    (hsg : s < giantFraction α) : s < survivalMap α s :=
  lt_survivalMap_of_lt (by linarith) hs hsg (survivalMap_giantFraction α).ge

/-- Above the giant fraction the survival map lies below the diagonal. -/
theorem survivalMap_lt_of_giantFraction_lt {α s : ℝ} (hα : 1 < α)
    (hgs : giantFraction α < s) : survivalMap α s < s := by
  have hg0 := (giantFraction_mem_Ioo hα).1
  by_contra h
  push_neg at h
  have hlt := lt_survivalMap_of_lt (by linarith) hg0 hgs h
  rw [survivalMap_giantFraction] at hlt
  exact lt_irrefl _ hlt

/-- A positive point where the survival map lies below the diagonal is above the giant
fraction. -/
theorem giantFraction_lt_of_survivalMap_lt {α s : ℝ} (hα : 1 < α) (hs0 : 0 < s)
    (hs : survivalMap α s < s) : giantFraction α < s := by
  by_contra h
  push_neg at h
  rcases h.lt_or_eq with hlt | heq
  · exact lt_asymm hs (lt_survivalMap_of_lt_giantFraction hα hs0 hlt)
  · rw [heq, survivalMap_giantFraction] at hs
    exact lt_irrefl _ hs

/-- **The giant fraction is continuous above `1`.** -/
theorem continuousAt_giantFraction {α : ℝ} (hα : 1 < α) : ContinuousAt giantFraction α := by
  have hcont : ∀ s : ℝ, Continuous fun β : ℝ ↦ survivalMap β s := fun s ↦ by
    unfold survivalMap
    fun_prop
  have hev : ∀ᶠ β in 𝓝 α, 1 < β := lt_mem_nhds hα
  obtain ⟨hg0, -⟩ := giantFraction_mem_Ioo hα
  refine tendsto_order.2 ⟨fun a ha ↦ ?_, fun b hb ↦ ?_⟩
  · by_cases ha0 : a ≤ 0
    · filter_upwards [hev] with β hβ
      exact ha0.trans_lt (giantFraction_mem_Ioo hβ).1
    · push_neg at ha0
      have h1 : a < survivalMap α a := lt_survivalMap_of_lt_giantFraction hα ha0 ha
      filter_upwards [hev, (tendsto_order.1 ((hcont a).tendsto α)).1 a h1] with β hβ h
      exact lt_giantFraction_of_lt_survivalMap hβ h
  · by_cases hb1 : 1 ≤ b
    · filter_upwards [hev] with β hβ
      exact (giantFraction_mem_Ioo hβ).2.trans_le hb1
    · have hb0 : 0 < b := hg0.trans hb
      have h1 : survivalMap α b < b := survivalMap_lt_of_giantFraction_lt hα hb
      filter_upwards [hev, (tendsto_order.1 ((hcont b).tendsto α)).2 b h1] with β hβ h
      exact giantFraction_lt_of_survivalMap_lt hβ hb0 h

/-! ### The limit law (6.2) for every `α > 1` -/

/-- **(6.2), the small branch, for every `α > 1`.** For queries of eventually `k` features and
`0 < ε < s`, the reach fraction is at most `ε` with probability tending to `(1 - s)^k`. -/
theorem tendsto_graphProb_reach_small_of_one_lt {α : ℝ} (hα : 1 < α) {k : ℕ}
    (A : ∀ m : ℕ, Finset (Fin m)) (hA : ∀ᶠ m in atTop, (A m).card = k) {ε : ℝ} (hε : 0 < ε)
    (hεs : ε < giantFraction α) :
    Tendsto (fun m : ℕ ↦ graphProb m (α / m) fun E ↦
      ((reach (edgeGraph E) (A m)).card : ℝ) / m ≤ ε) atTop
        (𝓝 ((1 - giantFraction α) ^ k)) :=
  tendsto_graphProb_reach_small (giantComponentLaw_of_one_lt hα) hα A hA hε hεs

/-- **(6.2), the giant branch, for every `α > 1`.** For queries of eventually `k` features and
`0 < 2ε < s`, the reach fraction is within `ε` of `s` with probability tending to
`1 - (1 - s)^k`. -/
theorem tendsto_graphProb_reach_giant_of_one_lt {α : ℝ} (hα : 1 < α) {k : ℕ}
    (A : ∀ m : ℕ, Finset (Fin m)) (hA : ∀ᶠ m in atTop, (A m).card = k) {ε : ℝ} (hε : 0 < ε)
    (hεs : 2 * ε < giantFraction α) :
    Tendsto (fun m : ℕ ↦ graphProb m (α / m) fun E ↦
      |((reach (edgeGraph E) (A m)).card : ℝ) / m - giantFraction α| ≤ ε) atTop
        (𝓝 (1 - (1 - giantFraction α) ^ k)) :=
  tendsto_graphProb_reach_giant (giantComponentLaw_of_one_lt hα) hα A hA hε hεs

end

end Descent.Pangenome.AncestralLocality
