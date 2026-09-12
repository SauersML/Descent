/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Pangenome.AncestralLocality.SupercriticalSecondMoment
import Descent.Pangenome.AncestralLocality.SupercriticalSprinkling
import Descent.Pangenome.AncestralLocality.SupercriticalUpperBound

assert_below Descent.PopGen Descent.Spectral Descent.Blindness Descent.Conditionals
assert_below Descent.Portability Descent.Decision Descent.Program

/-!
# The giant component theorem for `G(m, α/m)`, from the concentration of large features

`Descent.Pangenome.AncestralLocality.SupercriticalReach` carries the Erdős–Rényi giant component
theorem as the hypothesis `GiantComponentLaw α`. This file derives it for `α > 1` from one named
hypothesis, `LargeCountConcentration`: at every rate above `1`, with probability tending to one at
least `(giantFraction α - ε) m` features lie in components of more than `m^{2/3}` features. The
count is `SupercriticalSecondMoment.largeCount`, whose second moment that file bounds.

## Continuity of the giant fraction

Below the giant fraction the survival map `s ↦ 1 - e^{-α s}` lies above the diagonal, and above it
below (`lt_survivalMap_of_lt_giantFraction`, `survivalMap_lt_of_giantFraction_lt`, and their
converses). Since the survival map is continuous in `α`, so is the giant fraction above `1`
(`continuousAt_giantFraction`).

## The lower half

At a rate `α - δ` just below `α` the giant fraction is within `ε₁/2` of `s = giantFraction α`, and
`largeCount E (⌊m^{2/3}⌋₊ + 1)` is the number of features of `bigSet (edgeGraph E) (m^{2/3})`
(`largeCount_floor_add_one`). So concentration at `α - δ` and the sprinkling lemma
`SupercriticalSprinkling.tendsto_graphProb_exists_card_reach_ge` give, with probability tending to
one, a component of at least `(s - ε₁) m` features in `G(m, α/m)`
(`tendsto_graphProb_exists_card_reach_ge_giantFraction`).

## The upper half

By the uniform one-root bound of `SupercriticalUpperBound`, the expected number of features in
components of more than `ε m` features is eventually at most `(s + η) m`
(`eventually_graphExpect_card_bigSet_le`). That number is at least `(s - ε₁) m` on the lower event
and exceeds `(s + θ) m` on the overshoot event, so its mean bounds the overshoot probability; letting
`ε₁` and `η` shrink, the overshoot has probability tending to zero (`tendsto_graphProb_card_bigSet_gt`).

## The giant event

On the lower event and without overshoot, the component `C` of at least `(s - ε/4) m` features is
inside the large set, so `|C| ≤ (s + ε/4) m`; any other component of more than `ε m` features would
be disjoint from `C` and overflow the large set. So the giant-component event at scale `ε` holds
(`giantComponentLaw_of_lower`), and `GiantComponentLaw α` follows from concentration
(`giantComponentLaw_of_largeCountConcentration`).

Scope. `LargeCountConcentration` is a hypothesis here, to be proved from the second-moment bound of
`SupercriticalSecondMoment`. It is assumed at every rate above `1`, because the sprinkling runs its
first round at `α - δ`.

## Empirical status

None. The bodies are probabilities and expectations under `G(m, α/m)`, the survival equation, and
limits in `m` and `α`. The graph law is supplied, and nothing is measured.
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

/-- A point where the survival map lies above the diagonal is below the giant fraction. -/
theorem lt_giantFraction_of_lt_survivalMap {α s : ℝ} (hα : 1 < α)
    (hs : s < survivalMap α s) : s < giantFraction α := by
  by_contra h
  push_neg at h
  rcases h.lt_or_eq with hlt | heq
  · exact lt_asymm hs (survivalMap_lt_of_giantFraction_lt hα hlt)
  · rw [← heq, survivalMap_giantFraction] at hs
    exact lt_irrefl _ hs

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

/-- **The giant fraction is continuous in `α` above `1`.** -/
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

/-! ### Large features and the giant event -/

/-- The giant-component event is monotone in its scale. -/
theorem GiantEvent.mono {m : ℕ} {s ε₁ ε₂ : ℝ} {G : SimpleGraph (Fin m)} (h : GiantEvent s ε₁ G)
    (h₁₂ : ε₁ ≤ ε₂) : GiantEvent s ε₂ G := by
  obtain ⟨v, hv, hsmall⟩ := h
  exact ⟨v, hv.trans h₁₂, fun w hw ↦ (hsmall w hw).trans
    (mul_le_mul_of_nonneg_right h₁₂ (Nat.cast_nonneg m))⟩

/-- The number of features in components of more than `t` features, as a sum of indicators. -/
theorem card_bigSet_eq_sum {m : ℕ} (G : SimpleGraph (Fin m)) (t : ℝ) :
    ((bigSet G t).card : ℝ) = ∑ v, if t < ((reach G {v}).card : ℝ) then (1 : ℝ) else 0 := by
  rw [bigSet, natCast_card_filter]

/-- A constant factor comes out of an expectation under `G(m, p)`. -/
theorem graphExpect_const_mul {m : ℕ} (p c : ℝ) (f : Finset (Sym2 (Fin m)) → ℝ) :
    graphExpect m p (fun E ↦ c * f E) = c * graphExpect m p f := by
  simp only [graphExpect_eq_subsetExpect, subsetExpect_const_mul]

/-- **The expected number of features in components of more than `ε m` features** is eventually
at most `(s + η) m`, by the uniform one-root upper bound. -/
theorem eventually_graphExpect_card_bigSet_le {α : ℝ} (hα : 1 < α) {ε : ℝ} (hε : 0 < ε)
    {η : ℝ} (hη : 0 < η) :
    ∀ᶠ m : ℕ in atTop,
      graphExpect m (α / m) (fun E ↦ ((bigSet (edgeGraph E) (ε * m)).card : ℝ))
        ≤ (giantFraction α + η) * m := by
  filter_upwards [eventually_forall_graphProb_card_reach_singleton_ge_le hα hε hη,
    tendsto_natCast_atTop_atTop.eventually_ge_atTop α] with m hm hαm
  have hm0 : (0 : ℝ) < m := by linarith
  have hp0 : 0 ≤ α / m := div_nonneg (by linarith) hm0.le
  have hp1 : α / m ≤ 1 := (div_le_one hm0).mpr hαm
  calc graphExpect m (α / m) (fun E ↦ ((bigSet (edgeGraph E) (ε * m)).card : ℝ))
      = ∑ v, graphProb m (α / m) (fun E ↦ ε * m < ((reach (edgeGraph E) {v}).card : ℝ)) := by
        simp only [card_bigSet_eq_sum]
        rw [graphExpect_sum]
        rfl
    _ ≤ ∑ _v : Fin m, (giantFraction α + η) := by
        refine sum_le_sum fun v _ ↦ ?_
        refine (graphProb_mono (P := fun E ↦ ε * m < ((reach (edgeGraph E) {v}).card : ℝ))
          (Q := fun E ↦ ε * m ≤ ((reach (edgeGraph E) {v}).card : ℝ)) hp0 hp1
          fun E h ↦ h.le).trans ?_
        exact hm {v} (card_singleton v).le
    _ = (giantFraction α + η) * m := by
        rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, mul_comm]

/-- **The count of large features does not overshoot.** If for every `ε₁ > 0` some component has
at least `(s - ε₁) m` features with probability tending to one, then for `0 < ε < s` and `θ > 0`
the number of features in components of more than `ε m` features exceeds `(s + θ) m` with
probability tending to zero. -/
theorem tendsto_graphProb_card_bigSet_gt {α : ℝ} (hα : 1 < α) {ε θ : ℝ} (hε : 0 < ε)
    (hθ : 0 < θ) (hεs : ε < giantFraction α)
    (hlow : ∀ ε₁ : ℝ, 0 < ε₁ → Tendsto (fun m : ℕ ↦ graphProb m (α / m) fun E ↦
      ∃ v, (giantFraction α - ε₁) * m ≤ ((reach (edgeGraph E) {v}).card : ℝ)) atTop (𝓝 1)) :
    Tendsto (fun m : ℕ ↦ graphProb m (α / m) fun E ↦
      (giantFraction α + θ) * m < ((bigSet (edgeGraph E) (ε * m)).card : ℝ)) atTop (𝓝 0) := by
  have hs1 := (giantFraction_mem_Ioo hα).2
  refine tendsto_order.2 ⟨fun a ha ↦ ?_, fun τ hτ ↦ ?_⟩
  · filter_upwards [tendsto_natCast_atTop_atTop.eventually_ge_atTop α] with m hαm
    have hm0 : (0 : ℝ) < m := by linarith
    exact ha.trans_le (graphProb_nonneg (div_nonneg (by linarith) hm0.le)
      ((div_le_one hm0).mpr hαm) _)
  · obtain ⟨ε₁, hε₁0, hε₁τ, hε₁s⟩ : ∃ ε₁ : ℝ,
        0 < ε₁ ∧ ε₁ ≤ τ * θ / 4 ∧ ε₁ ≤ (giantFraction α - ε) / 2 :=
      ⟨min (τ * θ / 4) ((giantFraction α - ε) / 2), lt_min (by positivity) (by linarith),
        min_le_left _ _, min_le_right _ _⟩
    have hτθ : 0 < τ * θ := mul_pos hτ hθ
    have hA := (tendsto_order.1 (hlow ε₁ hε₁0)).1 (1 - τ * θ / 4) (by linarith)
    have hE := eventually_graphExpect_card_bigSet_le hα hε (η := τ * θ / 4) (by positivity)
    filter_upwards [hA, hE, tendsto_natCast_atTop_atTop.eventually_ge_atTop α]
      with m hPA hEX hαm
    have hm0 : (0 : ℝ) < m := by linarith
    have hp0 : 0 ≤ α / m := div_nonneg (by linarith) hm0.le
    have hp1 : α / m ≤ 1 := (div_le_one hm0).mpr hαm
    -- the count is at least `(s - ε₁) m` on the lower event and `(s + θ) m` on the overshoot
    have hpt : ∀ E : Finset (Sym2 (Fin m)),
        (giantFraction α - ε₁) * m * (if ∃ v, (giantFraction α - ε₁) * m
            ≤ ((reach (edgeGraph E) {v}).card : ℝ) then (1 : ℝ) else 0)
          + (θ + ε₁) * m * (if (giantFraction α + θ) * m
            < ((bigSet (edgeGraph E) (ε * m)).card : ℝ) then (1 : ℝ) else 0)
          ≤ ((bigSet (edgeGraph E) (ε * m)).card : ℝ) := by
      intro E
      have hX0 : (0 : ℝ) ≤ ((bigSet (edgeGraph E) (ε * m)).card : ℝ) := Nat.cast_nonneg _
      by_cases hA' : ∃ v, (giantFraction α - ε₁) * m ≤ ((reach (edgeGraph E) {v}).card : ℝ)
      · rw [if_pos hA']
        obtain ⟨v, hv⟩ := hA'
        have hbig : ε * m < ((reach (edgeGraph E) {v}).card : ℝ) :=
          lt_of_lt_of_le (mul_lt_mul_of_pos_right (by linarith) hm0) hv
        have hsub : reach (edgeGraph E) {v} ⊆ bigSet (edgeGraph E) (ε * m) := fun w hw ↦ by
          rw [mem_bigSet_iff, reach_singleton_eq_of_mem hw]
          exact hbig
        have hXA : (giantFraction α - ε₁) * m ≤ ((bigSet (edgeGraph E) (ε * m)).card : ℝ) :=
          hv.trans (Nat.cast_le.mpr (card_le_card hsub))
        split_ifs with hB
        · linarith
        · linarith
      · rw [if_neg hA', mul_zero, zero_add]
        split_ifs with hB
        · nlinarith [mul_le_mul_of_nonneg_right (show ε₁ ≤ giantFraction α by linarith) hm0.le]
        · linarith
    have hlin : (giantFraction α - ε₁) * m * graphProb m (α / m) (fun E ↦
          ∃ v, (giantFraction α - ε₁) * m ≤ ((reach (edgeGraph E) {v}).card : ℝ))
        + (θ + ε₁) * m * graphProb m (α / m) (fun E ↦
          (giantFraction α + θ) * m < ((bigSet (edgeGraph E) (ε * m)).card : ℝ))
        ≤ graphExpect m (α / m) (fun E ↦ ((bigSet (edgeGraph E) (ε * m)).card : ℝ)) := by
      have h := graphExpect_mono hp0 hp1 hpt
      rw [graphExpect_add, graphExpect_const_mul, graphExpect_const_mul] at h
      exact h
    have hPA' : 1 - τ * θ / 4 < graphProb m (α / m) (fun E ↦
        ∃ v, (giantFraction α - ε₁) * m ≤ ((reach (edgeGraph E) {v}).card : ℝ)) := hPA
    have hPB0 := graphProb_nonneg hp0 hp1 (fun E ↦
      (giantFraction α + θ) * m < ((bigSet (edgeGraph E) (ε * m)).card : ℝ))
    -- divide by `m`
    have h2 : (giantFraction α - ε₁) * graphProb m (α / m) (fun E ↦
          ∃ v, (giantFraction α - ε₁) * m ≤ ((reach (edgeGraph E) {v}).card : ℝ))
        + (θ + ε₁) * graphProb m (α / m) (fun E ↦
          (giantFraction α + θ) * m < ((bigSet (edgeGraph E) (ε * m)).card : ℝ))
        ≤ giantFraction α + τ * θ / 4 := by
      have h3 : (m : ℝ) * ((giantFraction α - ε₁) * graphProb m (α / m) (fun E ↦
            ∃ v, (giantFraction α - ε₁) * m ≤ ((reach (edgeGraph E) {v}).card : ℝ))
          + (θ + ε₁) * graphProb m (α / m) (fun E ↦
            (giantFraction α + θ) * m < ((bigSet (edgeGraph E) (ε * m)).card : ℝ)))
          ≤ (m : ℝ) * (giantFraction α + τ * θ / 4) := by
        linarith [hlin.trans hEX]
      exact le_of_mul_le_mul_left h3 hm0
    have h4 : (giantFraction α - ε₁) * (1 - τ * θ / 4) ≤ (giantFraction α - ε₁) *
        graphProb m (α / m) (fun E ↦
          ∃ v, (giantFraction α - ε₁) * m ≤ ((reach (edgeGraph E) {v}).card : ℝ)) :=
      mul_le_mul_of_nonneg_left hPA'.le (by linarith)
    have h5 : θ * graphProb m (α / m) (fun E ↦
          (giantFraction α + θ) * m < ((bigSet (edgeGraph E) (ε * m)).card : ℝ))
        ≤ (θ + ε₁) * graphProb m (α / m) (fun E ↦
          (giantFraction α + θ) * m < ((bigSet (edgeGraph E) (ε * m)).card : ℝ)) :=
      mul_le_mul_of_nonneg_right (by linarith) hPB0
    have h6 : (giantFraction α - ε₁) * (τ * θ / 4) ≤ τ * θ / 4 :=
      mul_le_of_le_one_left (by positivity) (by linarith)
    have h7 : θ * graphProb m (α / m) (fun E ↦
          (giantFraction α + θ) * m < ((bigSet (edgeGraph E) (ε * m)).card : ℝ))
        < θ * τ := by
      linarith
    exact lt_of_mul_lt_mul_left h7 hθ.le

/-- **The giant component theorem, given its lower half.** For `α > 1`, if for every `ε₁ > 0` some
component of `G(m, α/m)` has at least `(giantFraction α - ε₁) m` features with probability tending
to one, then `GiantComponentLaw α` holds. -/
theorem giantComponentLaw_of_lower {α : ℝ} (hα : 1 < α)
    (hlow : ∀ ε₁ : ℝ, 0 < ε₁ → Tendsto (fun m : ℕ ↦ graphProb m (α / m) fun E ↦
      ∃ v, (giantFraction α - ε₁) * m ≤ ((reach (edgeGraph E) {v}).card : ℝ)) atTop (𝓝 1)) :
    GiantComponentLaw α := by
  refine ⟨fun ε hε ↦ ?_⟩
  obtain ⟨hs0, -⟩ := giantFraction_mem_Ioo hα
  obtain ⟨ε', hε'0, hε'ε, hε's⟩ : ∃ ε' : ℝ, 0 < ε' ∧ ε' ≤ ε ∧ ε' ≤ giantFraction α / 2 :=
    ⟨min ε (giantFraction α / 2), lt_min hε (by linarith), min_le_left _ _, min_le_right _ _⟩
  have hL := hlow (ε' / 4) (by linarith)
  have hU := tendsto_graphProb_card_bigSet_gt hα hε'0 (by linarith : (0 : ℝ) < ε' / 4)
    (by linarith) hlow
  -- the lower event without overshoot is a giant event
  have hgood : ∀ m : ℕ, 0 < m → ∀ E : Finset (Sym2 (Fin m)),
      (∃ v, (giantFraction α - ε' / 4) * m ≤ ((reach (edgeGraph E) {v}).card : ℝ)) →
      ¬(giantFraction α + ε' / 4) * m < ((bigSet (edgeGraph E) (ε' * m)).card : ℝ) →
      GiantEvent (giantFraction α) ε (edgeGraph E) := by
    intro m hm E hA hB
    obtain ⟨v, hv⟩ := hA
    push_neg at hB
    have hm0 : (0 : ℝ) < m := Nat.cast_pos.mpr hm
    have hbig : ε' * m < ((reach (edgeGraph E) {v}).card : ℝ) :=
      lt_of_lt_of_le (mul_lt_mul_of_pos_right (by linarith) hm0) hv
    have hsub : reach (edgeGraph E) {v} ⊆ bigSet (edgeGraph E) (ε' * m) := fun w hw ↦ by
      rw [mem_bigSet_iff, reach_singleton_eq_of_mem hw]
      exact hbig
    have hC : ((reach (edgeGraph E) {v}).card : ℝ) ≤ (giantFraction α + ε' / 4) * m :=
      (Nat.cast_le.mpr (card_le_card hsub)).trans hB
    refine GiantEvent.mono (ε₁ := ε') ⟨v, ?_, fun w hw ↦ ?_⟩ hε'ε
    · rw [abs_le]
      constructor
      · rw [le_sub_iff_add_le, le_div_iff₀ hm0]
        nlinarith
      · rw [sub_le_iff_le_add, div_le_iff₀ hm0]
        nlinarith
    · by_contra hw'
      push_neg at hw'
      have hsubw : reach (edgeGraph E) {w} ⊆ bigSet (edgeGraph E) (ε' * m) := fun x hx ↦ by
        rw [mem_bigSet_iff, reach_singleton_eq_of_mem hx]
        exact hw'
      have hne : reach (edgeGraph E) {w} ≠ reach (edgeGraph E) {v} := fun heq ↦
        hw (heq ▸ subset_reach _ _ (mem_singleton_self w))
      have hcard : ((reach (edgeGraph E) {w}).card : ℝ) + ((reach (edgeGraph E) {v}).card : ℝ)
          ≤ ((bigSet (edgeGraph E) (ε' * m)).card : ℝ) := by
        rw [← Nat.cast_add, ← card_union_of_disjoint (disjoint_reach_singleton hne)]
        exact Nat.cast_le.mpr (card_le_card (union_subset hsubw hsub))
      nlinarith [mul_pos hε'0 hm0]
  have hbadL : Tendsto (fun m : ℕ ↦ graphProb m (α / m) fun E ↦
      ¬∃ v, (giantFraction α - ε' / 4) * m ≤ ((reach (edgeGraph E) {v}).card : ℝ)) atTop
      (𝓝 0) := by
    have h := hL.const_sub 1
    rw [sub_self] at h
    refine h.congr fun m ↦ ?_
    linarith [graphProb_add_not m (α / m) fun E ↦
      ∃ v, (giantFraction α - ε' / 4) * m ≤ ((reach (edgeGraph E) {v}).card : ℝ)]
  have hsum := hbadL.add hU
  rw [add_zero] at hsum
  have hbad : Tendsto (fun m : ℕ ↦ graphProb m (α / m) fun E ↦
      ¬GiantEvent (giantFraction α) ε (edgeGraph E)) atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsum ?_ ?_
    · filter_upwards [tendsto_natCast_atTop_atTop.eventually_ge_atTop α] with m hαm
      have hm0 : (0 : ℝ) < m := by linarith
      exact graphProb_nonneg (div_nonneg (by linarith) hm0.le) ((div_le_one hm0).mpr hαm) _
    · filter_upwards [tendsto_natCast_atTop_atTop.eventually_ge_atTop α] with m hαm
      have hm0 : (0 : ℝ) < m := by linarith
      have hm : 0 < m := by exact_mod_cast hm0
      have hp0 : 0 ≤ α / m := div_nonneg (by linarith) hm0.le
      have hp1 : α / m ≤ 1 := (div_le_one hm0).mpr hαm
      rw [graphProb, graphProb, graphProb, ← graphExpect_add]
      refine graphExpect_mono hp0 hp1 fun E ↦ ?_
      by_cases hA : ∃ v, (giantFraction α - ε' / 4) * m ≤ ((reach (edgeGraph E) {v}).card : ℝ)
      · by_cases hB : (giantFraction α + ε' / 4) * m
            < ((bigSet (edgeGraph E) (ε' * m)).card : ℝ)
        · rw [if_pos hB]
          split_ifs <;> norm_num
        · rw [if_neg (not_not.mpr (hgood m hm E hA hB))]
          split_ifs <;> norm_num
      · rw [if_pos hA]
        split_ifs <;> norm_num
  have h := hbad.const_sub 1
  rw [sub_zero] at h
  refine h.congr fun m ↦ ?_
  linarith [graphProb_add_not m (α / m) fun E ↦ GiantEvent (giantFraction α) ε (edgeGraph E)]

/-! ### The lower half from concentration -/

/-- **The named hypothesis: the number of large features concentrates.** For every `ε > 0`, with
probability tending to one at least `(giantFraction α - ε) m` features of `G(m, α/m)` lie in
components of more than `m^{2/3}` features. -/
def LargeCountConcentration (α : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → Tendsto (fun m : ℕ ↦ graphProb m (α / m) fun E ↦
    (giantFraction α - ε) * m ≤ largeCount E (⌊(m : ℝ) ^ ((2 : ℝ) / 3)⌋₊ + 1)) atTop (𝓝 1)

/-- At the threshold `⌊x⌋₊ + 1` the count of large features is the size of `bigSet` at `x`. -/
theorem largeCount_floor_add_one {m : ℕ} (E : Finset (Sym2 (Fin m))) {x : ℝ} (hx : 0 ≤ x) :
    largeCount E (⌊x⌋₊ + 1) = ((bigSet (edgeGraph E) x).card : ℝ) := by
  have h : (univ.filter fun v : Fin m ↦ ⌊x⌋₊ + 1 ≤ (reach (edgeGraph E) {v}).card)
      = bigSet (edgeGraph E) x := by
    ext v
    rw [mem_filter, mem_bigSet_iff, Nat.add_one_le_iff, Nat.floor_lt hx]
    simp
  rw [largeCount, h]

/-- **The lower half of the giant component theorem, from concentration.** If the numbers of large
features concentrate at every rate above `1`, then for `α > 1` and `ε₁ > 0`, with probability
tending to one some component of `G(m, α/m)` has at least `(giantFraction α - ε₁) m` features. -/
theorem tendsto_graphProb_exists_card_reach_ge_giantFraction {α : ℝ} (hα : 1 < α)
    (hconc : ∀ β : ℝ, 1 < β → LargeCountConcentration β) {ε₁ : ℝ} (hε₁ : 0 < ε₁) :
    Tendsto (fun m : ℕ ↦ graphProb m (α / m) fun E ↦
      ∃ v, (giantFraction α - ε₁) * m ≤ ((reach (edgeGraph E) {v}).card : ℝ)) atTop (𝓝 1) := by
  obtain ⟨δ₀, hδ₀, hδ₀g⟩ :=
    Metric.continuousAt_iff.mp (continuousAt_giantFraction hα) (ε₁ / 2) (by linarith)
  obtain ⟨δ, hδ0, hδδ₀, hδα1⟩ : ∃ δ : ℝ, 0 < δ ∧ δ < δ₀ ∧ δ < α - 1 :=
    ⟨min (δ₀ / 2) ((α - 1) / 2), lt_min (by linarith) (by linarith),
      (min_le_left _ _).trans_lt (by linarith), (min_le_right _ _).trans_lt (by linarith)⟩
  have hβ : 1 < α - δ := by linarith
  have hgβ : giantFraction α - ε₁ / 2 < giantFraction (α - δ) := by
    have hd : dist (α - δ) α < δ₀ := by
      rw [Real.dist_eq, show α - δ - α = -δ by ring, abs_neg, abs_of_pos hδ0]
      exact hδδ₀
    have h := hδ₀g hd
    rw [Real.dist_eq] at h
    linarith [neg_abs_le (giantFraction (α - δ) - giantFraction α)]
  have hlarge := hconc (α - δ) hβ (ε₁ / 2) (by linarith)
  refine tendsto_graphProb_exists_card_reach_ge hδ0 (by linarith) ?_
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlarge tendsto_const_nhds ?_ ?_
  · filter_upwards [tendsto_natCast_atTop_atTop.eventually_ge_atTop α] with m hαm
    have hm0 : (0 : ℝ) < m := by linarith
    have hp0 : 0 ≤ (α - δ) / m := div_nonneg (by linarith) hm0.le
    have hp1 : (α - δ) / m ≤ 1 := (div_le_one hm0).mpr (by linarith)
    refine graphProb_mono hp0 hp1 fun E hE ↦ ?_
    rw [← largeCount_floor_add_one E (Real.rpow_nonneg hm0.le _)]
    exact le_trans (mul_le_mul_of_nonneg_right (by linarith) hm0.le) hE
  · filter_upwards [tendsto_natCast_atTop_atTop.eventually_ge_atTop α] with m hαm
    have hm0 : (0 : ℝ) < m := by linarith
    exact graphProb_le_one (div_nonneg (by linarith) hm0.le) ((div_le_one hm0).mpr (by linarith))
      _

/-- **The Erdős–Rényi giant component theorem for `G(m, α/m)` with `α > 1`, from concentration.**
If the numbers of large features concentrate at every rate above `1`, then `GiantComponentLaw α`
holds. -/
theorem giantComponentLaw_of_largeCountConcentration {α : ℝ} (hα : 1 < α)
    (hconc : ∀ β : ℝ, 1 < β → LargeCountConcentration β) : GiantComponentLaw α :=
  giantComponentLaw_of_lower hα fun _ hε₁ ↦
    tendsto_graphProb_exists_card_reach_ge_giantFraction hα hconc hε₁

end

end Descent.Pangenome.AncestralLocality
