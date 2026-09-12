/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Pangenome.AncestralLocality.SupercriticalConcentration
import Descent.Pangenome.AncestralLocality.SupercriticalSprinkling

assert_below Descent.PopGen Descent.Spectral Descent.Blindness Descent.Conditionals
assert_below Descent.Portability Descent.Decision Descent.Program

/-!
# The giant component theorem for `G(m, α/m)` with `α > 1`

`Descent.Pangenome.AncestralLocality.SupercriticalReach` carries the Erdős–Rényi giant component
theorem as the hypothesis `GiantComponentLaw α` and proves it for `0 ≤ α < 1`. This file proves it
for every `α > 1` (`giantComponentLaw_of_one_lt`). So the limit law (6.2) of the note holds without
that hypothesis on both sides of the transition.

**A component of `c m` features, for `c < s`.** At a slightly smaller rate `α'` with `c < s(α')`
(`exists_lt_giantFraction_of_lt`), at least `c m` features lie in components larger than
`m^{2/3}` with probability tending to one (`tendsto_graphProb_bigSet_ge`). That follows from the
concentration of `Descent.Pangenome.AncestralLocality.SupercriticalConcentration` at the threshold
`⌈κ m⌉`, since `m^{2/3} < κ m` eventually (`eventually_rpow_two_thirds_lt`). Sprinkling at rate
`α - α'` joins those components (`tendsto_graphProb_exists_card_reach_ge` of
`Descent.Pangenome.AncestralLocality.SupercriticalSprinkling`), which gives
`tendsto_graphProb_exists_card_reach_ge_of_lt`.

**Few features outside it.** The uniform upper bound of
`Descent.Pangenome.AncestralLocality.SupercriticalUpperBound` gives
`E#{w : ε'' m ≤ |C(w)|} ≤ (s + ε₁) m`. On the event that a component has `(s - ε₁) m` features,
that count is at least `(s - ε₁) m` (`card_large_ge_of_mem`). Markov's inequality on the excess
then bounds the chance that it exceeds `(s + ε) m` by `2 ε₁/(ε + ε₁)` plus a multiple of the
chance of the complement (`tendsto_graphProb_card_large_le`).

**The event.** If some component has at least `(s - ε₁) m` features and at most `(s + ε') m`
features lie in components of at least `ε'' m` features, then `GiantEvent s ε` holds when
`ε' + ε₁ ≤ ε`,
`ε'' ≤ ε` and `ε'' ≤ s - ε₁` (`giantEvent_of_exists_of_card_le`). A second component of at least
`ε'' m` features would have to fit into `(ε' + ε₁) m` features. Both events hold with probability
tending to one, and `graphProb_add_sub_one_le_and` combines them.

Scope. The theorem is the law of large numbers for the largest component in the form of
`GiantEvent`. Fluctuations, rates of convergence and the size of the second-largest component are
not studied.

## Empirical status

None. The bodies are probabilities of events about finite edge sets under `G(m, α/m)` and their
limits in `m`. The graph law is supplied, and nothing is measured.
-/

namespace Descent.Pangenome.AncestralLocality

open Finset Filter Topology
open scoped Classical

noncomputable section

/-! ### Events -/

/-- **Two likely events are jointly likely**: `P(A) + P(B) - 1 ≤ P(A ∧ B)`. -/
theorem graphProb_add_sub_one_le_and {m : ℕ} {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    {P Q : Finset (Sym2 (Fin m)) → Prop} [DecidablePred P] [DecidablePred Q] :
    graphProb m p P + graphProb m p Q - 1 ≤ graphProb m p (fun E ↦ P E ∧ Q E) := by
  rw [← graphExpect_const (m := m) p (1 : ℝ), graphProb, graphProb, graphProb, ← graphExpect_add,
    ← graphExpect_sub]
  refine graphExpect_mono hp0 hp1 fun E ↦ ?_
  beta_reduce
  by_cases hP : P E <;> by_cases hQ : Q E <;> norm_num [hP, hQ]

/-- A component that meets the large features lies among them. -/
theorem card_large_ge_of_mem {m : ℕ} {G : SimpleGraph (Fin m)} {t : ℝ} {v : Fin m}
    (hv : t ≤ ((reach G {v}).card : ℝ)) :
    ((reach G {v}).card : ℝ) ≤ ((univ.filter fun w ↦ t ≤ ((reach G {w}).card : ℝ)).card : ℝ) := by
  exact_mod_cast card_le_card fun w hw ↦
    mem_filter.mpr ⟨mem_univ w, by rwa [reach_singleton_eq_of_mem hw]⟩

/-- **The giant-component event from two counts.** If some component has at least `(s - ε₁) m`
features and at most `(s + ε') m` features lie in components of at least `ε'' m` features, with
`ε' + ε₁ ≤ ε`, `ε'' ≤ ε` and `ε'' ≤ s - ε₁`, the giant-component event at scale `ε` holds. -/
theorem giantEvent_of_exists_of_card_le {m : ℕ} {G : SimpleGraph (Fin m)} {s ε ε₁ ε' ε'' : ℝ}
    (hm : 0 < m) (hε₁0 : 0 ≤ ε₁) (hε' : ε' + ε₁ ≤ ε) (hε'0 : 0 ≤ ε') (hε'' : ε'' ≤ ε)
    (hε''s : ε'' ≤ s - ε₁) (hv : ∃ v, (s - ε₁) * m ≤ ((reach G {v}).card : ℝ))
    (hW : ((univ.filter fun w ↦ ε'' * m ≤ ((reach G {w}).card : ℝ)).card : ℝ) ≤ (s + ε') * m) :
    GiantEvent s ε G := by
  obtain ⟨v, hv⟩ := hv
  have hm' : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  have hL : ε'' * m ≤ (s - ε₁) * m := mul_le_mul_of_nonneg_right hε''s hm'.le
  have hsub : ∀ u, ε'' * m ≤ ((reach G {u}).card : ℝ) →
      reach G {u} ⊆ univ.filter fun w ↦ ε'' * m ≤ ((reach G {w}).card : ℝ) :=
    fun u hu w hw ↦ mem_filter.mpr ⟨mem_univ w, by rwa [reach_singleton_eq_of_mem hw]⟩
  have hCv : ((reach G {v}).card : ℝ) ≤ (s + ε') * m := by
    have h := card_large_ge_of_mem (G := G) (hL.trans hv)
    linarith
  refine ⟨v, abs_le.mpr ⟨?_, ?_⟩, fun w hw ↦ ?_⟩
  · rw [le_sub_iff_add_le, le_div_iff₀ hm']
    have h := mul_le_mul_of_nonneg_right (by linarith : -ε + s ≤ s - ε₁) hm'.le
    linarith
  · rw [sub_le_iff_le_add, div_le_iff₀ hm']
    have h := mul_le_mul_of_nonneg_right (by linarith : s + ε' ≤ ε + s) hm'.le
    linarith
  · by_cases hlarge : ε'' * m ≤ ((reach G {w}).card : ℝ)
    · have hne : reach G {v} ≠ reach G {w} := fun h ↦ hw (by
        rw [h]
        exact subset_reach G {w} (mem_singleton_self w))
      have hunion : ((reach G {v} ∪ reach G {w}).card : ℝ) ≤
          ((univ.filter fun w ↦ ε'' * m ≤ ((reach G {w}).card : ℝ)).card : ℝ) := by
        exact_mod_cast card_le_card (union_subset (hsub v (hL.trans hv)) (hsub w hlarge))
      rw [card_union_of_disjoint (disjoint_reach_singleton hne), Nat.cast_add] at hunion
      have h := mul_le_mul_of_nonneg_right hε' hm'.le
      linarith
    · push_neg at hlarge
      have h := mul_le_mul_of_nonneg_right hε'' hm'.le
      linarith

/-! ### A component of `c m` features -/

/-- Eventually `m^{2/3} < κ m`. -/
theorem eventually_rpow_two_thirds_lt {κ : ℝ} (hκ : 0 < κ) :
    ∀ᶠ m : ℕ in atTop, (m : ℝ) ^ ((2 : ℝ) / 3) < κ * m := by
  have h := (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 3)).comp
    tendsto_natCast_atTop_atTop
  filter_upwards [(tendsto_order.1 h).2 κ hκ, eventually_gt_atTop 0] with m hm hm0
  have hm' : (0 : ℝ) < m := Nat.cast_pos.mpr hm0
  have hsplit : (m : ℝ) ^ ((2 : ℝ) / 3) = m * (m : ℝ) ^ (-(1 / 3 : ℝ)) := by
    rw [show ((2 : ℝ) / 3) = 1 + -(1 / 3 : ℝ) by norm_num, Real.rpow_add hm', Real.rpow_one]
  rw [hsplit, mul_comm κ]
  exact mul_lt_mul_of_pos_left hm hm'

/-- **The sprinkling hypothesis holds.** For `α > 1` and `c < s(α)`, with probability tending to
one at least `c m` features of `G(m, α/m)` lie in components larger than `m^{2/3}`. -/
theorem tendsto_graphProb_bigSet_ge {α c : ℝ} (hα : 1 < α) (hc : c < giantFraction α) :
    Tendsto (fun m : ℕ ↦ graphProb m (α / m) fun E ↦
      c * m ≤ ((bigSet (edgeGraph E) ((m : ℝ) ^ ((2 : ℝ) / 3))).card : ℝ)) atTop (𝓝 1) := by
  have hα0 : 0 < α := by linarith
  refine tendsto_order.2 ⟨fun a ha ↦ ?_, fun a ha ↦ ?_⟩
  · obtain ⟨κ, hκ0, hev⟩ := exists_eventually_graphProb_largeCount_le hα
      (δ := giantFraction α - c) (η := (1 - a) / 2) (by linarith) (by linarith)
    filter_upwards [hev, eventually_rpow_two_thirds_lt hκ0,
      tendsto_natCast_atTop_atTop.eventually_ge_atTop α, eventually_gt_atTop 0]
      with m h1 h2 h3 h4
    have hm : (0 : ℝ) < m := Nat.cast_pos.mpr h4
    have hp0 : 0 ≤ α / m := div_nonneg hα0.le hm.le
    have hp1 : α / m ≤ 1 := (div_le_one hm).mpr h3
    have hmono : graphProb m (α / m) (fun E ↦
        ¬c * m ≤ ((bigSet (edgeGraph E) ((m : ℝ) ^ ((2 : ℝ) / 3))).card : ℝ)) ≤
          graphProb m (α / m) (fun E ↦
            largeCount E ⌈κ * m⌉₊ ≤ (giantFraction α - (giantFraction α - c)) * m) := by
      refine graphProb_mono hp0 hp1 fun E h ↦ ?_
      push_neg at h
      have hsub : (univ.filter fun v ↦ ⌈κ * m⌉₊ ≤ (reach (edgeGraph E) {v}).card) ⊆
          bigSet (edgeGraph E) ((m : ℝ) ^ ((2 : ℝ) / 3)) := by
        intro v hv
        rw [mem_bigSet_iff]
        have hv' := (mem_filter.mp hv).2
        calc (m : ℝ) ^ ((2 : ℝ) / 3) < κ * m := h2
          _ ≤ (⌈κ * m⌉₊ : ℝ) := Nat.le_ceil _
          _ ≤ ((reach (edgeGraph E) {v}).card : ℝ) := by exact_mod_cast hv'
      have hcard : largeCount E ⌈κ * m⌉₊ ≤
          ((bigSet (edgeGraph E) ((m : ℝ) ^ ((2 : ℝ) / 3))).card : ℝ) := by
        rw [largeCount]
        exact_mod_cast card_le_card hsub
      linarith
    have hadd := graphProb_add_not m (α / m) (fun E ↦
      c * m ≤ ((bigSet (edgeGraph E) ((m : ℝ) ^ ((2 : ℝ) / 3))).card : ℝ))
    linarith
  · filter_upwards [tendsto_natCast_atTop_atTop.eventually_ge_atTop α, eventually_gt_atTop 0]
      with m h3 h4
    have hm : (0 : ℝ) < m := Nat.cast_pos.mpr h4
    exact (graphProb_le_one (div_nonneg hα0.le hm.le) ((div_le_one hm).mpr h3) _).trans_lt ha

/-- **A component of `c m` features exists.** For `α > 1` and `c < s(α)`, with probability tending
to one some component of `G(m, α/m)` has at least `c m` features. -/
theorem tendsto_graphProb_exists_card_reach_ge_of_lt {α c : ℝ} (hα : 1 < α)
    (hc : c < giantFraction α) :
    Tendsto (fun m : ℕ ↦ graphProb m (α / m) fun E ↦
      ∃ v, c * m ≤ ((reach (edgeGraph E) {v}).card : ℝ)) atTop (𝓝 1) := by
  obtain ⟨hs0, -⟩ := giantFraction_mem_Ioo hα
  obtain ⟨s', hs'0, hcs', hs's⟩ : ∃ s' : ℝ, 0 < s' ∧ c < s' ∧ s' < giantFraction α :=
    ⟨max ((c + giantFraction α) / 2) (giantFraction α / 2), lt_max_of_lt_right (by linarith),
      lt_max_of_lt_left (by linarith), max_lt (by linarith) (by linarith)⟩
  obtain ⟨α', hα'1, hα'α, hs'α'⟩ := exists_lt_giantFraction_of_lt hα hs'0 hs's
  have hlarge := tendsto_graphProb_bigSet_ge hα'1 (hcs'.trans hs'α')
  exact tendsto_graphProb_exists_card_reach_ge (by linarith : 0 < α - α') (by linarith)
    (by rwa [sub_sub_cancel])

/-! ### Few features outside it -/

/-- **Few features lie in large components.** For `α > 1`, `ε > 0` and `0 < ε'' < s(α)`, with
probability tending to one at most `(s + ε) m` features of `G(m, α/m)` lie in components of at
least `ε'' m` features. -/
theorem tendsto_graphProb_card_large_le {α ε ε'' : ℝ} (hα : 1 < α) (hε : 0 < ε)
    (hε''0 : 0 < ε'') (hε''s : ε'' < giantFraction α) :
    Tendsto (fun m : ℕ ↦ graphProb m (α / m) fun E ↦
      ((univ.filter fun w ↦ ε'' * m ≤ ((reach (edgeGraph E) {w}).card : ℝ)).card : ℝ) ≤
        (giantFraction α + ε) * m) atTop (𝓝 1) := by
  have hα0 : 0 < α := by linarith
  obtain ⟨hs0, hs1⟩ := giantFraction_mem_Ioo hα
  refine tendsto_order.2 ⟨fun a ha ↦ ?_, fun a ha ↦ ?_⟩
  · have h1a : 0 < 1 - a := by linarith
    obtain ⟨ε₁, hε₁0, hε₁s, hε₁a⟩ : ∃ ε₁ : ℝ, 0 < ε₁ ∧ ε₁ ≤ giantFraction α - ε'' ∧
        8 * ε₁ ≤ (1 - a) * ε := by
      refine ⟨min (giantFraction α - ε'') ((1 - a) * ε / 8),
        lt_min (by linarith) (by positivity), min_le_left _ _, ?_⟩
      have hmin := min_le_right (giantFraction α - ε'') ((1 - a) * ε / 8)
      linarith
    have hd : 0 < ε + ε₁ := by linarith
    have hC : 0 < giantFraction α / (ε + ε₁) + 1 := by positivity
    have hη : 0 < (1 - a) / (4 * (giantFraction α / (ε + ε₁) + 1)) := by positivity
    have hA := tendsto_graphProb_exists_card_reach_ge_of_lt hα
      (c := giantFraction α - ε₁) (by linarith)
    filter_upwards [(tendsto_order.1 hA).1
        (1 - (1 - a) / (4 * (giantFraction α / (ε + ε₁) + 1))) (by linarith),
      eventually_forall_graphProb_card_reach_singleton_ge_le hα hε''0 hε₁0,
      tendsto_natCast_atTop_atTop.eventually_ge_atTop α, eventually_gt_atTop 0]
      with m hPA hup h3 h4
    have hm : (0 : ℝ) < m := Nat.cast_pos.mpr h4
    have hp0 : 0 ≤ α / m := div_nonneg hα0.le hm.le
    have hp1 : α / m ≤ 1 := (div_le_one hm).mpr h3
    have hdm : 0 < (ε + ε₁) * m := mul_pos hd hm
    have hEW : graphExpect m (α / m) (fun E ↦
        ((univ.filter fun w ↦ ε'' * m ≤ ((reach (edgeGraph E) {w}).card : ℝ)).card : ℝ)) ≤
          (giantFraction α + ε₁) * m := by
      simp only [natCast_card_filter]
      rw [graphExpect_sum]
      calc ∑ w : Fin m, graphExpect m (α / m) (fun E ↦
            if ε'' * m ≤ ((reach (edgeGraph E) {w}).card : ℝ) then (1 : ℝ) else 0)
          ≤ ∑ _w : Fin m, (giantFraction α + ε₁) :=
            sum_le_sum fun w _ ↦ hup {w} (card_singleton w).le
        _ = (giantFraction α + ε₁) * m := by
            rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, mul_comm]
    have hsd : giantFraction α / (ε + ε₁) * ((ε + ε₁) * m) = giantFraction α * m := by
      rw [show giantFraction α / (ε + ε₁) * ((ε + ε₁) * m) =
        giantFraction α / (ε + ε₁) * (ε + ε₁) * m by ring, div_mul_cancel₀ _ hd.ne']
    have hpt : ∀ E : Finset (Sym2 (Fin m)),
        (if ¬((univ.filter fun w ↦ ε'' * m ≤ ((reach (edgeGraph E) {w}).card : ℝ)).card : ℝ) ≤
          (giantFraction α + ε) * m then (1 : ℝ) else 0) ≤
        (((univ.filter fun w ↦ ε'' * m ≤ ((reach (edgeGraph E) {w}).card : ℝ)).card : ℝ) -
            (giantFraction α - ε₁) * m) / ((ε + ε₁) * m) +
          (giantFraction α / (ε + ε₁) + 1) *
            (if ¬∃ v, (giantFraction α - ε₁) * m ≤ ((reach (edgeGraph E) {v}).card : ℝ)
              then (1 : ℝ) else 0) := by
      intro E
      have hW0 : (0 : ℝ) ≤
          ((univ.filter fun w ↦ ε'' * m ≤ ((reach (edgeGraph E) {w}).card : ℝ)).card : ℝ) :=
        Nat.cast_nonneg _
      by_cases hAE : ∃ v, (giantFraction α - ε₁) * m ≤ ((reach (edgeGraph E) {v}).card : ℝ)
      · obtain ⟨v, hv⟩ := hAE
        have hvε : ε'' * m ≤ ((reach (edgeGraph E) {v}).card : ℝ) :=
          (mul_le_mul_of_nonneg_right (by linarith) hm.le).trans hv
        have hWL := hv.trans (card_large_ge_of_mem hvε)
        rw [if_neg (not_not.mpr ⟨v, hv⟩), mul_zero, add_zero]
        split_ifs with hbig
        · rw [le_div_iff₀ hdm, one_mul]
          push_neg at hbig
          linarith
        · exact div_nonneg (by linarith) hdm.le
      · rw [if_pos hAE, mul_one]
        have h1 : -(giantFraction α / (ε + ε₁)) ≤
            (((univ.filter fun w ↦ ε'' * m ≤ ((reach (edgeGraph E) {w}).card : ℝ)).card : ℝ) -
              (giantFraction α - ε₁) * m) / ((ε + ε₁) * m) := by
          rw [le_div_iff₀ hdm, neg_mul, hsd]
          have h2 := mul_nonneg hε₁0.le hm.le
          linarith
        split_ifs <;> linarith
    have hbound := graphExpect_mono hp0 hp1 hpt
    rw [graphExpect_add, graphExpect_div_const, graphExpect_sub, graphExpect_const,
      graphExpect_const_mul] at hbound
    have haddA := graphProb_add_not m (α / m)
      (fun E ↦ ∃ v, (giantFraction α - ε₁) * m ≤ ((reach (edgeGraph E) {v}).card : ℝ))
    have hnotA : graphProb m (α / m)
        (fun E ↦ ¬∃ v, (giantFraction α - ε₁) * m ≤ ((reach (edgeGraph E) {v}).card : ℝ)) ≤
          (1 - a) / (4 * (giantFraction α / (ε + ε₁) + 1)) := by linarith
    have hCnot : (giantFraction α / (ε + ε₁) + 1) * graphProb m (α / m)
        (fun E ↦ ¬∃ v, (giantFraction α - ε₁) * m ≤ ((reach (edgeGraph E) {v}).card : ℝ)) ≤
          (1 - a) / 4 := by
      calc (giantFraction α / (ε + ε₁) + 1) * graphProb m (α / m)
          (fun E ↦ ¬∃ v, (giantFraction α - ε₁) * m ≤ ((reach (edgeGraph E) {v}).card : ℝ))
          ≤ (giantFraction α / (ε + ε₁) + 1) *
              ((1 - a) / (4 * (giantFraction α / (ε + ε₁) + 1))) :=
            mul_le_mul_of_nonneg_left hnotA hC.le
        _ = (1 - a) / 4 := by
            rw [mul_div_assoc', mul_comm (giantFraction α / (ε + ε₁) + 1),
              mul_div_mul_right _ _ hC.ne']
    have hexcess : (graphExpect m (α / m) (fun E ↦
        ((univ.filter fun w ↦ ε'' * m ≤ ((reach (edgeGraph E) {w}).card : ℝ)).card : ℝ)) -
          (giantFraction α - ε₁) * m) / ((ε + ε₁) * m) ≤ (1 - a) / 4 := by
      rw [div_le_iff₀ hdm]
      have h1 := mul_le_mul_of_nonneg_right hε₁a hm.le
      have h2 := mul_nonneg (mul_nonneg h1a.le hε₁0.le) hm.le
      nlinarith
    have haddW := graphProb_add_not m (α / m) (fun E ↦
      ((univ.filter fun w ↦ ε'' * m ≤ ((reach (edgeGraph E) {w}).card : ℝ)).card : ℝ) ≤
        (giantFraction α + ε) * m)
    have hnotW : graphProb m (α / m) (fun E ↦
        ¬((univ.filter fun w ↦ ε'' * m ≤ ((reach (edgeGraph E) {w}).card : ℝ)).card : ℝ) ≤
          (giantFraction α + ε) * m) ≤ (1 - a) / 2 := by
      have hle : graphProb m (α / m) (fun E ↦
          ¬((univ.filter fun w ↦ ε'' * m ≤ ((reach (edgeGraph E) {w}).card : ℝ)).card : ℝ) ≤
            (giantFraction α + ε) * m) ≤
          (graphExpect m (α / m) (fun E ↦
            ((univ.filter fun w ↦ ε'' * m ≤ ((reach (edgeGraph E) {w}).card : ℝ)).card : ℝ)) -
              (giantFraction α - ε₁) * m) / ((ε + ε₁) * m) +
            (giantFraction α / (ε + ε₁) + 1) * graphProb m (α / m)
              (fun E ↦ ¬∃ v, (giantFraction α - ε₁) * m ≤
                ((reach (edgeGraph E) {v}).card : ℝ)) := hbound
      linarith
    linarith
  · filter_upwards [tendsto_natCast_atTop_atTop.eventually_ge_atTop α, eventually_gt_atTop 0]
      with m h3 h4
    have hm : (0 : ℝ) < m := Nat.cast_pos.mpr h4
    exact (graphProb_le_one (div_nonneg hα0.le hm.le) ((div_le_one hm).mpr h3) _).trans_lt ha

/-! ### The theorem -/

/-- **The Erdős–Rényi giant component theorem for `α > 1`.** For every `α > 1` and every `ε > 0`
the giant-component event has probability tending to one in `G(m, α/m)`. -/
theorem giantComponentLaw_of_one_lt {α : ℝ} (hα : 1 < α) : GiantComponentLaw α := by
  refine ⟨fun ε hε ↦ ?_⟩
  have hα0 : 0 < α := by linarith
  obtain ⟨hs0, hs1⟩ := giantFraction_mem_Ioo hα
  obtain ⟨ε₁, hε₁0, hε₁ε, hε₁s⟩ : ∃ ε₁ : ℝ, 0 < ε₁ ∧ ε₁ ≤ ε / 2 ∧ ε₁ ≤ giantFraction α / 2 :=
    ⟨min (ε / 2) (giantFraction α / 2), lt_min (by linarith) (by linarith), min_le_left _ _,
      min_le_right _ _⟩
  have hA := tendsto_graphProb_exists_card_reach_ge_of_lt hα
    (c := giantFraction α - ε₁) (by linarith)
  have hW := tendsto_graphProb_card_large_le hα (ε := ε / 2) (by linarith) hε₁0 (by linarith)
  refine tendsto_order.2 ⟨fun a ha ↦ ?_, fun a ha ↦ ?_⟩
  · filter_upwards [(tendsto_order.1 hA).1 ((1 + a) / 2) (by linarith),
      (tendsto_order.1 hW).1 ((1 + a) / 2) (by linarith),
      tendsto_natCast_atTop_atTop.eventually_ge_atTop α, eventually_gt_atTop 0]
      with m h1 h2 h3 h4
    have hm : (0 : ℝ) < m := Nat.cast_pos.mpr h4
    have hp0 : 0 ≤ α / m := div_nonneg hα0.le hm.le
    have hp1 : α / m ≤ 1 := (div_le_one hm).mpr h3
    have hand := graphProb_add_sub_one_le_and (m := m) hp0 hp1
      (P := fun E ↦ ∃ v, (giantFraction α - ε₁) * m ≤ ((reach (edgeGraph E) {v}).card : ℝ))
      (Q := fun E ↦
        ((univ.filter fun w ↦ ε₁ * m ≤ ((reach (edgeGraph E) {w}).card : ℝ)).card : ℝ) ≤
          (giantFraction α + ε / 2) * m)
    have hmono := graphProb_mono (m := m) hp0 hp1
      (P := fun E ↦ (∃ v, (giantFraction α - ε₁) * m ≤ ((reach (edgeGraph E) {v}).card : ℝ)) ∧
        ((univ.filter fun w ↦ ε₁ * m ≤ ((reach (edgeGraph E) {w}).card : ℝ)).card : ℝ) ≤
          (giantFraction α + ε / 2) * m)
      (Q := fun E ↦ GiantEvent (giantFraction α) ε (edgeGraph E))
      fun _ h ↦ giantEvent_of_exists_of_card_le h4 hε₁0.le (by linarith) (by linarith)
        (by linarith) (by linarith) h.1 h.2
    linarith
  · filter_upwards [tendsto_natCast_atTop_atTop.eventually_ge_atTop α, eventually_gt_atTop 0]
      with m h3 h4
    have hm : (0 : ℝ) < m := Nat.cast_pos.mpr h4
    exact (graphProb_le_one (div_nonneg hα0.le hm.le) ((div_le_one hm).mpr h3) _).trans_lt ha

end

end Descent.Pangenome.AncestralLocality
