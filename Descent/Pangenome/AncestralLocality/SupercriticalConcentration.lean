/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Pangenome.AncestralLocality.SupercriticalSecondMoment
import Descent.Pangenome.AncestralLocality.SupercriticalUpperBound

assert_below Descent.PopGen Descent.Spectral Descent.Blindness Descent.Conditionals
assert_below Descent.Portability Descent.Decision Descent.Program

/-!
# Concentration of the number of features in large components

For `α > 1` and `s = giantFraction α`, this file proves that the number of features of
`G(m, α/m)` in components of at least `⌈κ m⌉` features is at least `(s - δ) m` with probability
tending to one, for every `δ > 0` and every small enough `κ > 0`
(`exists_eventually_graphProb_largeCount_le`). No giant component theorem is assumed.

**The route.** Let `Y = largeCount E ⌈κ m⌉` and choose a slack `η₁`, with `s' = s - η₁`. The
exploration lower bound of `Descent.Pangenome.AncestralLocality.SupercriticalLowerBound`, with
`q = 1 - s'` and a threshold linear in `m`, gives `E[Y] ≥ s' m`. The uniform upper bound of
`Descent.Pangenome.AncestralLocality.SupercriticalUpperBound` gives `E[Y] ≤ (s + η₁) m`. The second
moment of `Descent.Pangenome.AncestralLocality.SupercriticalSecondMoment` expands
(`graphExpect_sub_sq`, through `graphExpect_const_mul`) to
`E[(Y - s' m)²] ≤ (1 - s') m (E[Y] - s' m) + m K ≤ 2 η₁ m² + m (κ m + 1)`. Chebyshev's inequality
bounds the chance of `Y ≤ (s - δ) m` by `4 (3 η₁ + 1/m)/δ²`, which the choice of `η₁` and `m` makes
at most `η`.

**Left-continuity of the giant fraction.** If `0 < s' < s(α)`, the survival map lies strictly above
the diagonal at `s'`, so it still does for every `α' < α` close enough to `α`, and then
`s' < s(α')` (`lt_giantFraction_of_lt_survivalMap`, `exists_lt_giantFraction_of_lt`). The sprinkling
argument runs at a slightly smaller `α'` and needs this.

Scope. The conclusion is the concentration of the number of features in components of linear size
from below; the matching statement from above, the merging of the large components and the
assembly into `GiantComponentLaw α` are in sibling modules.

## Empirical status

None. The bodies are probabilities and expectations under `G(m, α/m)`, the giant fraction and limits
in `m`. The graph law is supplied, and nothing is measured.
-/

namespace Descent.Pangenome.AncestralLocality

open Finset Filter Topology
open scoped Classical

noncomputable section

/-! ### Moments -/

/-- Expectation under `G(m, p)` commutes with a constant factor on the left. -/
theorem graphExpect_const_mul {m : ℕ} (p k : ℝ) (f : Finset (Sym2 (Fin m)) → ℝ) :
    graphExpect m p (fun E ↦ k * f E) = k * graphExpect m p f := by
  simp only [graphExpect, mul_sum]
  exact sum_congr rfl fun E _ ↦ by ring

/-- **The second moment about a constant.** -/
theorem graphExpect_sub_sq {m : ℕ} (p : ℝ) (X : Finset (Sym2 (Fin m)) → ℝ) (c : ℝ) :
    graphExpect m p (fun E ↦ (X E - c) ^ 2) =
      graphExpect m p (fun E ↦ X E ^ 2) - 2 * c * graphExpect m p X + c ^ 2 := by
  have h : (fun E ↦ (X E - c) ^ 2) = fun E ↦ (X E ^ 2 + -(2 * c) * X E) + c ^ 2 := by
    funext E
    ring
  rw [h, graphExpect_add, graphExpect_add, graphExpect_const_mul, graphExpect_const]
  ring

/-! ### The giant fraction from the left -/

/-- **Above the diagonal means below the giant fraction.** For `α > 1`, a positive `s'` at which
the survival map lies strictly above the diagonal is below the giant fraction. -/
theorem lt_giantFraction_of_lt_survivalMap {α s' : ℝ} (hα : 1 < α)
    (h : s' < survivalMap α s') : s' < giantFraction α := by
  obtain ⟨hs0, -⟩ := giantFraction_mem_Ioo hα
  by_contra hle
  push_neg at hle
  rcases hle.lt_or_eq with hlt | heq
  · have hself := lt_survivalMap_of_lt (by linarith) hs0 hlt h.le
    rw [survivalMap_giantFraction] at hself
    exact lt_irrefl _ hself
  · rw [← heq, survivalMap_giantFraction] at h
    exact lt_irrefl _ h

/-- **Left-continuity of the giant fraction.** For `α > 1` and `0 < s' < s(α)` there is `α'` with
`1 < α' < α` and `s' < s(α')`. -/
theorem exists_lt_giantFraction_of_lt {α s' : ℝ} (hα : 1 < α) (hs'0 : 0 < s')
    (hs' : s' < giantFraction α) : ∃ α' : ℝ, 1 < α' ∧ α' < α ∧ s' < giantFraction α' := by
  have hα0 : 0 < α := by linarith
  have hs'1 : s' < 1 := hs'.trans (giantFraction_mem_Ioo hα).2
  have hlt : Real.exp (-(α * s')) < 1 - s' := by
    have h := lt_survivalMap_of_lt hα0 hs'0 hs' (survivalMap_giantFraction α).ge
    unfold survivalMap at h
    linarith
  have hlog : -(α * s') < Real.log (1 - s') := (Real.lt_log_iff_exp_lt (by linarith)).mpr hlt
  obtain ⟨β, hβ⟩ : ∃ β : ℝ, β = -Real.log (1 - s') / s' := ⟨_, rfl⟩
  have hβα : β < α := by
    rw [hβ, div_lt_iff₀ hs'0]
    linarith
  refine ⟨max ((1 + α) / 2) ((β + α) / 2), lt_max_of_lt_left (by linarith),
    max_lt (by linarith) (by linarith),
    lt_giantFraction_of_lt_survivalMap (lt_max_of_lt_left (by linarith)) ?_⟩
  have hβ' : β < max ((1 + α) / 2) ((β + α) / 2) := lt_max_of_lt_right (by linarith)
  have hβs : β * s' = -Real.log (1 - s') := by
    rw [hβ, div_mul_cancel₀ _ hs'0.ne']
  have h1 : -(max ((1 + α) / 2) ((β + α) / 2) * s') < Real.log (1 - s') := by
    have hmul := mul_lt_mul_of_pos_right hβ' hs'0
    linarith
  have h2 := (Real.lt_log_iff_exp_lt (by linarith : (0 : ℝ) < 1 - s')).mp h1
  unfold survivalMap
  linarith

/-! ### Concentration -/

/-- **Concentration from below.** For `α > 1`, `δ > 0` and `η > 0` there is `κ > 0` such that,
eventually, fewer than `(s - δ) m` features of `G(m, α/m)` lie in components of at least `⌈κ m⌉`
features with probability at most `η`, with `s = giantFraction α`. -/
theorem exists_eventually_graphProb_largeCount_le {α δ η : ℝ} (hα : 1 < α) (hδ : 0 < δ)
    (hη : 0 < η) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ᶠ m : ℕ in atTop,
      graphProb m (α / m) (fun E ↦ largeCount E ⌈κ * m⌉₊ ≤ (giantFraction α - δ) * m) ≤ η := by
  have hα0 : 0 < α := by linarith
  obtain ⟨hs0, hs1⟩ := giantFraction_mem_Ioo hα
  obtain ⟨η₁, hη₁0, hη₁δ, hη₁s, hη₁η⟩ : ∃ η₁ : ℝ, 0 < η₁ ∧ η₁ ≤ δ / 2 ∧
      η₁ < giantFraction α ∧ 24 * η₁ ≤ η * δ ^ 2 := by
    refine ⟨min (min (δ / 2) (giantFraction α / 2)) (η * δ ^ 2 / 24), ?_, ?_, ?_, ?_⟩
    · exact lt_min (lt_min (by linarith) (by linarith)) (by positivity)
    · exact (min_le_left _ _).trans (min_le_left _ _)
    · exact lt_of_le_of_lt ((min_le_left _ _).trans (min_le_right _ _)) (by linarith)
    · have hmin := min_le_right (min (δ / 2) (giantFraction α / 2)) (η * δ ^ 2 / 24)
      linarith
  obtain ⟨κ₀, hκ₀, hbound⟩ := exists_one_sub_pow_le hα (s' := giantFraction α - η₁)
    (by linarith) (by linarith)
  obtain ⟨κ, hκ0, hκκ₀, hκη₁⟩ : ∃ κ : ℝ, 0 < κ ∧ 4 * κ ≤ κ₀ ∧ κ ≤ η₁ :=
    ⟨min (κ₀ / 4) η₁, lt_min (by linarith) hη₁0,
      by have hmin := min_le_left (κ₀ / 4) η₁; linarith, min_le_right _ _⟩
  refine ⟨κ, hκ0, ?_⟩
  filter_upwards [eventually_forall_graphProb_card_reach_singleton_ge_le hα hκ0 hη₁0,
    tendsto_natCast_atTop_atTop.eventually_ge_atTop α,
    tendsto_natCast_atTop_atTop.eventually_ge_atTop (4 / κ₀),
    tendsto_natCast_atTop_atTop.eventually_ge_atTop (8 / (η * δ ^ 2)),
    eventually_gt_atTop 0] with m hup hmα hmκ hmη hm0
  have hm : (0 : ℝ) < m := Nat.cast_pos.mpr hm0
  have hp0 : 0 ≤ α / m := div_nonneg hα0.le hm.le
  have hp1 : α / m ≤ 1 := (div_le_one hm).mpr hmα
  obtain ⟨K, hK⟩ : ∃ K : ℕ, K = ⌈κ * m⌉₊ := ⟨_, rfl⟩
  rw [← hK]
  have hKle : (K : ℝ) < κ * m + 1 := by
    rw [hK]
    exact Nat.ceil_lt_add_one (by positivity)
  have hκm : 4 ≤ κ₀ * m := by
    rw [div_le_iff₀ hκ₀] at hmκ
    linarith
  have h4κ : 4 * κ * m ≤ κ₀ * m := mul_le_mul_of_nonneg_right hκκ₀ hm.le
  have hK1 : (K : ℝ) ≤ κ₀ * m := by linarith
  have hK2 : ((2 * K : ℕ) : ℝ) ≤ κ₀ * m := by
    push_cast
    linarith
  have hq1 := hbound m K hmα hK1
  have hq2 := hbound m (2 * K) hmα hK2
  have hlow : ∀ v : Fin m, giantFraction α - η₁ ≤
      graphProb m (α / m) (fun E ↦ K ≤ (reach (edgeGraph E) {v}).card) := by
    intro v
    have hlt := graphProb_card_reach_lt_le hp0 hp1 (q := 1 - (giantFraction α - η₁))
      (by linarith) (by linarith) hq1 v
    have hadd := graphProb_add_not m (α / m) (fun E ↦ K ≤ (reach (edgeGraph E) {v}).card)
    have hc := graphProb_congr (m := m) (α / m)
      (P := fun E ↦ ¬K ≤ (reach (edgeGraph E) {v}).card)
      (Q := fun E ↦ (reach (edgeGraph E) {v}).card < K) fun _ ↦ not_le
    linarith
  have hhigh : ∀ v : Fin m,
      graphProb m (α / m) (fun E ↦ K ≤ (reach (edgeGraph E) {v}).card) ≤ giantFraction α + η₁ := by
    intro v
    refine (graphProb_mono hp0 hp1 fun E h ↦ ?_).trans (hup {v} (card_singleton v).le)
    have hceil : κ * m ≤ (K : ℝ) := by
      rw [hK]
      exact Nat.le_ceil _
    exact hceil.trans (by exact_mod_cast h)
  have hy := graphExpect_largeCount (m := m) (α / m) K
  have hylow : (giantFraction α - η₁) * m ≤ graphExpect m (α / m) (fun E ↦ largeCount E K) := by
    rw [hy]
    calc (giantFraction α - η₁) * m = ∑ _v : Fin m, (giantFraction α - η₁) := by
          rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, mul_comm]
      _ ≤ ∑ v : Fin m, graphProb m (α / m) (fun E ↦ K ≤ (reach (edgeGraph E) {v}).card) :=
          sum_le_sum fun v _ ↦ hlow v
  have hyup : graphExpect m (α / m) (fun E ↦ largeCount E K) ≤ (giantFraction α + η₁) * m := by
    rw [hy]
    calc ∑ v : Fin m, graphProb m (α / m) (fun E ↦ K ≤ (reach (edgeGraph E) {v}).card)
        ≤ ∑ _v : Fin m, (giantFraction α + η₁) := sum_le_sum fun v _ ↦ hhigh v
      _ = (giantFraction α + η₁) * m := by
          rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, mul_comm]
  have hsq := graphExpect_largeCount_sq_le hp0 hp1 (q := 1 - (giantFraction α - η₁))
    (by linarith) (by linarith) hq2
  have hexp := graphExpect_sub_sq (m := m) (α / m) (fun E ↦ largeCount E K)
    ((giantFraction α - η₁) * m)
  beta_reduce at hexp
  have hA : (1 - (giantFraction α - η₁)) * m *
      (graphExpect m (α / m) (fun E ↦ largeCount E K) - (giantFraction α - η₁) * m) ≤
        2 * η₁ * m ^ 2 := by
    have h1 : graphExpect m (α / m) (fun E ↦ largeCount E K) - (giantFraction α - η₁) * m ≤
        2 * η₁ * m := by linarith
    have h2 : 0 ≤ (1 - (giantFraction α - η₁)) * m := mul_nonneg (by linarith) hm.le
    have h3 := mul_le_mul_of_nonneg_left h1 h2
    have h4 : 0 ≤ η₁ * m ^ 2 * (giantFraction α - η₁) :=
      mul_nonneg (mul_nonneg hη₁0.le (sq_nonneg _)) (by linarith)
    linarith
  have hB : (giantFraction α - η₁) * m * K ≤ m * (κ * m + 1) := by
    have h3 : 0 ≤ m * (K : ℝ) := mul_nonneg hm.le (Nat.cast_nonneg K)
    calc (giantFraction α - η₁) * m * K = (giantFraction α - η₁) * (m * K) := by ring
      _ ≤ m * K := mul_le_of_le_one_left h3 (by linarith)
      _ ≤ m * (κ * m + 1) := mul_le_mul_of_nonneg_left hKle.le hm.le
  have hvar : graphExpect m (α / m) (fun E ↦ (largeCount E K - (giantFraction α - η₁) * m) ^ 2) ≤
      2 * η₁ * m ^ 2 + m * (κ * m + 1) := by
    rw [hexp]
    linarith
  have hδη : 0 < (δ - η₁) * m := mul_pos (by linarith) hm
  have hcheb := graphProb_le_sub_le hp0 hp1 (fun E ↦ largeCount E K)
    ((giantFraction α - η₁) * m) ((δ - η₁) * m) hδη
  have hmono : graphProb m (α / m) (fun E ↦ largeCount E K ≤ (giantFraction α - δ) * m) ≤
      graphProb m (α / m)
        (fun E ↦ largeCount E K ≤ (giantFraction α - η₁) * m - (δ - η₁) * m) :=
    graphProb_mono hp0 hp1 fun _ h ↦ by linarith
  refine hmono.trans (hcheb.trans ?_)
  rw [div_le_iff₀ (by positivity)]
  have hden : (δ / 2 * m) ^ 2 ≤ ((δ - η₁) * m) ^ 2 :=
    pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_right (by linarith) hm.le) 2
  have hmη' : 8 ≤ η * δ ^ 2 * m := by
    rw [div_le_iff₀ (by positivity)] at hmη
    linarith
  have hmbig : 8 * m ≤ η * δ ^ 2 * m ^ 2 := by nlinarith
  have hk : κ * m ^ 2 ≤ η₁ * m ^ 2 := mul_le_mul_of_nonneg_right hκη₁ (by positivity)
  have hη₁' : 24 * η₁ * m ^ 2 ≤ η * δ ^ 2 * m ^ 2 :=
    mul_le_mul_of_nonneg_right hη₁η (by positivity)
  have hden' := mul_le_mul_of_nonneg_left hden hη.le
  linarith

end

end Descent.Pangenome.AncestralLocality
