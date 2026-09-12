/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Pangenome.AncestralLocality.RootExchangeability

assert_below Descent.PopGen Descent.Spectral Descent.Blindness Descent.Conditionals
assert_below Descent.Portability Descent.Decision Descent.Program

/-!
# The supercritical locality transition (6.2), conditional on the giant component theorem

The note's (6.2): for `α > 1` and `k` fixed roots, `|C_m(A)|/m ⇒ s` with probability
`1 - (1 - s)^k` and `⇒ 0` with probability `(1 - s)^k`, where `s = giantFraction α`. This file
proves both branch limits from `GiantComponentLaw α`, the Erdős–Rényi theorem carried as a
hypothesis, through the exchangeability identity of
`Descent.Pangenome.AncestralLocality.RootExchangeability`.

**The weight.** Let the large set be the features whose component has more than `s m / 2`
features (`bigSet`). On the giant-component event at a scale `δ < s / 2` the large set is the
giant component (`bigSet_eq_reach_of_giantEvent`). So `C(m - |large|, k)/C(m, k)` is within `η` of
`(1 - s)^k` on that event (`abs_choose_div_choose_sub_pow_le`), and it lies between `0` and `1`
off it. Its expectation therefore tends to `(1 - s)^k` (`tendsto_graphExpect_choose_div_choose`),
and by the averaging identity so does the probability that `k` roots all miss the giant component
(`tendsto_graphProb_disjoint_bigSet`).

**The branches.** Two events that agree on the giant-component event have probabilities whose
difference tends to zero (`tendsto_graphProb_sub_of_eq_on_giantEvent`). On that event at a small
scale, `|C_m(A)|/m ≤ ε` holds exactly when the roots miss the giant component, and
`||C_m(A)|/m - s| ≤ ε` holds exactly when they touch it. Hence `P(|C_m(A)|/m ≤ ε) → (1 - s)^k`
for `0 < ε < s` (`tendsto_graphProb_reach_small`), and `P(||C_m(A)|/m - s| ≤ ε) → 1 - (1 - s)^k`
for `0 < 2ε < s` (`tendsto_graphProb_reach_giant`). Together these are the convergence in
distribution of `|C_m(A)|/m` to the two-point law of (6.2).

Scope. Every limit here assumes `GiantComponentLaw α`, the Erdős–Rényi giant component theorem,
which is not formalized for `α > 1`. The roots are any queries of eventually exactly `k`
features; the note's `k ≥ 2` is not needed. The reach is `reach`, not the hereditary closure
itself (the note's Theorem 4), and the Wright–Fisher statements of the note's last line are not
restated.

## Empirical status

None. The bodies are probabilities under `G(m, α/m)` and their limits in `m`. Nothing is
measured.
-/

namespace Descent.Pangenome.AncestralLocality

open Finset Filter Topology
open scoped Classical

noncomputable section

/-! ### Expectation -/

/-- Expectation of a constant under `G(m, p)`. -/
theorem graphExpect_const {m : ℕ} (p c : ℝ) : graphExpect m p (fun _ ↦ c) = c := by
  have h := graphExpect_const_one m p
  simp only [graphExpect, mul_one] at h
  simp only [graphExpect, ← sum_mul, h, one_mul]

/-- Expectation under `G(m, p)` commutes with differences. -/
theorem graphExpect_sub {m : ℕ} (p : ℝ) (f g : Finset (Sym2 (Fin m)) → ℝ) :
    graphExpect m p (fun E ↦ f E - g E) = graphExpect m p f - graphExpect m p g := by
  simp only [graphExpect, mul_sub, sum_sub_distrib]

/-- `|E f| ≤ E |f|` under `G(m, p)` when `p` is a probability. -/
theorem abs_graphExpect_le {m : ℕ} {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (f : Finset (Sym2 (Fin m)) → ℝ) :
    |graphExpect m p f| ≤ graphExpect m p (fun E ↦ |f E|) := by
  refine (abs_sum_le_sum_abs _ _).trans (le_of_eq (sum_congr rfl fun E _ ↦ ?_))
  rw [abs_mul, abs_of_nonneg (edgeWeight_nonneg hp0 hp1 E)]

/-! ### The large set on the giant-component event -/

/-- **On the giant-component event the large set is the giant component**, for the threshold
`s m / 2` and a scale `δ < s / 2`. -/
theorem bigSet_eq_reach_of_giantEvent {m : ℕ} {G : SimpleGraph (Fin m)} {s δ : ℝ}
    (hδ : δ < s / 2) {v : Fin m} (hv : |((reach G {v}).card : ℝ) / m - s| ≤ δ)
    (hsmall : ∀ w, w ∉ reach G {v} → ((reach G {w}).card : ℝ) ≤ δ * m) :
    bigSet G (s * m / 2) = reach G {v} := by
  have hm : (0 : ℝ) < m := Nat.cast_pos.mpr v.pos
  have hkey : δ * m < s * m / 2 := by
    nlinarith [mul_pos (by linarith : (0 : ℝ) < s / 2 - δ) hm]
  have hbig : s * m / 2 < ((reach G {v}).card : ℝ) := by
    have h2 : s - δ ≤ ((reach G {v}).card : ℝ) / m := by linarith [(abs_le.mp hv).1]
    rw [le_div_iff₀ hm] at h2
    nlinarith
  ext w
  rw [mem_bigSet_iff]
  constructor
  · intro hw
    by_contra hnot
    linarith [hsmall w hnot]
  · intro hw
    rw [reach_singleton_eq_of_mem hw]
    exact hbig

/-! ### The weight `(1 - s)^k` -/

/-- **The averaged chance that `k` draws miss the large set tends to `(1 - s)^k`**:
`E[C(m - |large|, k)/C(m, k)] → (1 - s)^k`.
Assumes: `GiantComponentLaw α`. -/
theorem tendsto_graphExpect_choose_div_choose {α : ℝ} (hG : GiantComponentLaw α) (hα : 1 < α)
    (k : ℕ) :
    Tendsto (fun m : ℕ ↦ graphExpect m (α / m) fun E ↦
      ((m - (bigSet (edgeGraph E) (giantFraction α * m / 2)).card).choose k : ℝ) / m.choose k)
      atTop (𝓝 ((1 - giantFraction α) ^ k)) := by
  obtain ⟨hs0, hs1⟩ := giantFraction_mem_Ioo hα
  have hα0 : 0 ≤ α := by linarith
  rw [Metric.tendsto_atTop]
  intro η hη
  have hcont : ContinuousAt (fun t : ℝ ↦ t ^ k) (1 - giantFraction α) :=
    (continuous_pow k).continuousAt
  obtain ⟨δ₀, hδ₀, hmod₀⟩ := Metric.continuousAt_iff.mp hcont (η / 3) (by linarith)
  obtain ⟨δ, hδ0, hδ₀', hδc, hδs⟩ : ∃ δ : ℝ, 0 < δ ∧ δ ≤ δ₀ / 3 ∧
      δ ≤ (1 - giantFraction α) / 2 ∧ δ ≤ giantFraction α / 4 :=
    ⟨min (δ₀ / 3) (min ((1 - giantFraction α) / 2) (giantFraction α / 4)),
      lt_min (by linarith) (lt_min (by linarith) (by linarith)), min_le_left _ _,
      (min_le_right _ _).trans (min_le_left _ _), (min_le_right _ _).trans (min_le_right _ _)⟩
  have hmod : ∀ t : ℝ, |t - (1 - giantFraction α)| ≤ 2 * δ →
      |t ^ k - (1 - giantFraction α) ^ k| ≤ η / 3 := by
    intro t ht
    have h := hmod₀ (x := t) (by rw [Real.dist_eq]; linarith)
    rw [Real.dist_eq] at h
    exact h.le
  have hgood := (tendsto_order.1 (hG.tendsto_giantEvent δ hδ0)).1 (1 - η / 3) (by linarith)
  have hkm := (tendsto_order.1 (tendsto_const_div_atTop_nhds_zero_nat (k : ℝ))).2 δ hδ0
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hgood.and (hkm.and ((eventually_ge_atTop k).and
    ((eventually_gt_atTop 0).and (tendsto_natCast_atTop_atTop.eventually_ge_atTop α)))))
  refine ⟨N, fun m hm ↦ ?_⟩
  obtain ⟨hgm, hkmm, hkm', hm0, hmα⟩ := hN m hm
  have hm' : (0 : ℝ) < m := Nat.cast_pos.mpr hm0
  have hp0 : 0 ≤ α / m := div_nonneg hα0 hm'.le
  have hp1 : α / m ≤ 1 := (div_le_one hm').mpr hmα
  have hpt : ∀ E : Finset (Sym2 (Fin m)),
      |((m - (bigSet (edgeGraph E) (giantFraction α * m / 2)).card).choose k : ℝ) /
          m.choose k - (1 - giantFraction α) ^ k| ≤
        η / 3 + (if ¬GiantEvent (giantFraction α) δ (edgeGraph E) then 1 else 0) := by
    intro E
    by_cases hE : GiantEvent (giantFraction α) δ (edgeGraph E)
    · rw [if_neg (not_not.mpr hE), add_zero]
      obtain ⟨v, hv, hsmall⟩ := hE
      rw [bigSet_eq_reach_of_giantEvent (by linarith) hv hsmall]
      refine abs_choose_div_choose_sub_pow_le ((card_le_univ _).trans_eq (Fintype.card_fin m))
        hkm' hm0 (by linarith) hmod ?_ hkmm.le
      rw [show 1 - ((reach (edgeGraph E) {v}).card : ℝ) / m - (1 - giantFraction α) =
        -(((reach (edgeGraph E) {v}).card : ℝ) / m - giantFraction α) by ring, abs_neg]
      exact hv
    · rw [if_pos hE]
      have hq0 : 0 ≤ ((m - (bigSet (edgeGraph E) (giantFraction α * m / 2)).card).choose k : ℝ) /
          m.choose k := by positivity
      have hq1 : ((m - (bigSet (edgeGraph E) (giantFraction α * m / 2)).card).choose k : ℝ) /
          m.choose k ≤ 1 :=
        div_le_one_of_le₀ (by exact_mod_cast Nat.choose_le_choose k (Nat.sub_le _ _))
          (Nat.cast_nonneg _)
      have hc0 : 0 ≤ (1 - giantFraction α) ^ k := pow_nonneg (by linarith) k
      have hc1 : (1 - giantFraction α) ^ k ≤ 1 := pow_le_one₀ (by linarith) (by linarith)
      rw [abs_le]
      constructor <;> linarith
  have hnot : graphProb m (α / m) (fun E ↦ ¬GiantEvent (giantFraction α) δ (edgeGraph E)) =
      graphExpect m (α / m)
        (fun E ↦ if ¬GiantEvent (giantFraction α) δ (edgeGraph E) then 1 else 0) := rfl
  have hcompl :=
    graphProb_add_not m (α / m) (fun E ↦ GiantEvent (giantFraction α) δ (edgeGraph E))
  rw [Real.dist_eq]
  calc _ = |graphExpect m (α / m) (fun E ↦
          ((m - (bigSet (edgeGraph E) (giantFraction α * m / 2)).card).choose k : ℝ) /
            m.choose k - (1 - giantFraction α) ^ k)| := by
        rw [graphExpect_sub, graphExpect_const]
    _ ≤ _ := abs_graphExpect_le hp0 hp1 _
    _ ≤ graphExpect m (α / m) (fun E ↦
          η / 3 + (if ¬GiantEvent (giantFraction α) δ (edgeGraph E) then 1 else 0)) :=
        graphExpect_mono hp0 hp1 hpt
    _ = η / 3 +
          graphProb m (α / m) (fun E ↦ ¬GiantEvent (giantFraction α) δ (edgeGraph E)) := by
        rw [graphExpect_add, graphExpect_const, hnot]
    _ < η := by linarith

/-- **(6.2), the weight of the small branch**: the probability that `k` roots all miss the giant
component tends to `(1 - s)^k`.
Assumes: `GiantComponentLaw α`. -/
theorem tendsto_graphProb_disjoint_bigSet {α : ℝ} (hG : GiantComponentLaw α) (hα : 1 < α)
    {k : ℕ} (A : ∀ m : ℕ, Finset (Fin m)) (hA : ∀ᶠ m in atTop, (A m).card = k) :
    Tendsto (fun m : ℕ ↦ graphProb m (α / m) fun E ↦
      Disjoint (A m) (bigSet (edgeGraph E) (giantFraction α * m / 2))) atTop
        (𝓝 ((1 - giantFraction α) ^ k)) := by
  refine (tendsto_graphExpect_choose_div_choose hG hα k).congr' ?_
  filter_upwards [hA, eventually_ge_atTop k] with m hAm hkm
  have hC : (0 : ℝ) < m.choose k := by exact_mod_cast Nat.choose_pos hkm
  rw [graphExpect_div_const, ← choose_mul_graphProb_disjoint_bigSet (α / m) _ hAm,
    mul_div_cancel_left₀ _ hC.ne']

/-! ### The branches -/

/-- **Events that agree on the giant-component event** have probabilities whose difference tends
to zero.
Assumes: `GiantComponentLaw α`. -/
theorem tendsto_graphProb_sub_of_eq_on_giantEvent {α δ : ℝ} (hG : GiantComponentLaw α)
    (hα0 : 0 ≤ α) (hδ : 0 < δ) (P Q : ∀ m : ℕ, Finset (Sym2 (Fin m)) → Prop)
    [∀ m, DecidablePred (P m)] [∀ m, DecidablePred (Q m)]
    (hPQ : ∀ᶠ m in atTop, ∀ E : Finset (Sym2 (Fin m)),
      GiantEvent (giantFraction α) δ (edgeGraph E) → (P m E ↔ Q m E)) :
    Tendsto (fun m : ℕ ↦ graphProb m (α / m) (P m) - graphProb m (α / m) (Q m)) atTop
      (𝓝 0) := by
  have hbad : Tendsto (fun m : ℕ ↦
      1 - graphProb m (α / m) fun E ↦ GiantEvent (giantFraction α) δ (edgeGraph E))
      atTop (𝓝 0) := by
    have h := (hG.tendsto_giantEvent δ hδ).const_sub 1
    rwa [sub_self] at h
  have hneg := hbad.neg
  rw [neg_zero] at hneg
  have key : ∀ᶠ m in atTop, |graphProb m (α / m) (P m) - graphProb m (α / m) (Q m)| ≤
      1 - graphProb m (α / m) fun E ↦ GiantEvent (giantFraction α) δ (edgeGraph E) := by
    filter_upwards [hPQ, eventually_gt_atTop 0,
      tendsto_natCast_atTop_atTop.eventually_ge_atTop α] with m hm hm0 hmα
    have hm' : (0 : ℝ) < m := Nat.cast_pos.mpr hm0
    have hp0 : 0 ≤ α / m := div_nonneg hα0 hm'.le
    have hp1 : α / m ≤ 1 := (div_le_one hm').mpr hmα
    have hpt : ∀ E, |(if P m E then (1 : ℝ) else 0) - (if Q m E then 1 else 0)| ≤
        (if ¬GiantEvent (giantFraction α) δ (edgeGraph E) then 1 else 0) := by
      intro E
      by_cases hE : GiantEvent (giantFraction α) δ (edgeGraph E)
      · rw [if_neg (not_not.mpr hE)]
        by_cases hQ : Q m E
        · rw [if_pos ((hm E hE).mpr hQ), if_pos hQ, sub_self, abs_zero]
        · rw [if_neg (mt (hm E hE).mp hQ), if_neg hQ, sub_self, abs_zero]
      · rw [if_pos hE]
        split_ifs <;> norm_num
    have hnot : graphProb m (α / m) (fun E ↦ ¬GiantEvent (giantFraction α) δ (edgeGraph E)) =
        graphExpect m (α / m)
          (fun E ↦ if ¬GiantEvent (giantFraction α) δ (edgeGraph E) then 1 else 0) := rfl
    have hcompl :=
      graphProb_add_not m (α / m) (fun E ↦ GiantEvent (giantFraction α) δ (edgeGraph E))
    have hdiff : graphProb m (α / m) (P m) - graphProb m (α / m) (Q m) =
        graphExpect m (α / m)
          (fun E ↦ (if P m E then (1 : ℝ) else 0) - (if Q m E then 1 else 0)) := by
      rw [graphExpect_sub]
      rfl
    rw [hdiff]
    calc _ ≤ _ := abs_graphExpect_le hp0 hp1 _
      _ ≤ _ := graphExpect_mono hp0 hp1 hpt
      _ = 1 - graphProb m (α / m) fun E ↦ GiantEvent (giantFraction α) δ (edgeGraph E) := by
        rw [← hnot]
        linarith
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' hneg hbad
    (key.mono fun _ h ↦ (abs_le.mp h).1) (key.mono fun _ h ↦ (abs_le.mp h).2)

/-- **Theorem 5, supercritical, (6.2): the small branch.** For `α > 1` and queries `A m` of
eventually exactly `k` features, `P(|C_m(A)|/m ≤ ε) → (1 - s)^k` for every `0 < ε < s`.
Assumes: `GiantComponentLaw α`. -/
theorem tendsto_graphProb_reach_small {α : ℝ} (hG : GiantComponentLaw α) (hα : 1 < α) {k : ℕ}
    (A : ∀ m : ℕ, Finset (Fin m)) (hA : ∀ᶠ m in atTop, (A m).card = k) {ε : ℝ} (hε : 0 < ε)
    (hεs : ε < giantFraction α) :
    Tendsto (fun m : ℕ ↦ graphProb m (α / m) fun E ↦
      ((reach (edgeGraph E) (A m)).card : ℝ) / m ≤ ε) atTop
        (𝓝 ((1 - giantFraction α) ^ k)) := by
  have hα0 : 0 ≤ α := by linarith
  have hk1 : (0 : ℝ) < k + 1 := by positivity
  obtain ⟨e, he0, heε, hes⟩ : ∃ e : ℝ, 0 < e ∧ e ≤ ε ∧ e ≤ (giantFraction α - ε) / 2 :=
    ⟨min ε ((giantFraction α - ε) / 2), lt_min hε (by linarith), min_le_left _ _,
      min_le_right _ _⟩
  obtain ⟨δ, hδ0, hkδ⟩ : ∃ δ : ℝ, 0 < δ ∧ ((k : ℝ) + 1) * δ = e :=
    ⟨e / (k + 1), div_pos he0 hk1, by rw [mul_div_assoc', mul_div_cancel_left₀ e hk1.ne']⟩
  have hkδ0 : 0 ≤ (k : ℝ) * δ := mul_nonneg (Nat.cast_nonneg k) hδ0.le
  have hδs : δ < giantFraction α / 2 := by linarith
  have hPQ : ∀ᶠ m in atTop, ∀ E : Finset (Sym2 (Fin m)),
      GiantEvent (giantFraction α) δ (edgeGraph E) →
        (((reach (edgeGraph E) (A m)).card : ℝ) / m ≤ ε ↔
          Disjoint (A m) (bigSet (edgeGraph E) (giantFraction α * m / 2))) := by
    filter_upwards [hA] with m hAm E hE
    obtain ⟨v, hv, hsmall⟩ := hE
    have hm' : (0 : ℝ) < m := Nat.cast_pos.mpr v.pos
    rw [bigSet_eq_reach_of_giantEvent hδs hv hsmall]
    constructor
    · intro hsm
      by_contra hnd
      obtain ⟨a, haA, haB⟩ := not_disjoint_iff.mp hnd
      have h := abs_card_reach_div_sub_le_of_mem (A m) hv hsmall haA haB
      rw [hAm, hkδ] at h
      linarith [(abs_le.mp h).1]
    · intro hd
      have h := card_reach_le_of_forall_not_mem (A m) hsmall fun a ha ↦ disjoint_left.mp hd ha
      rw [hAm] at h
      have h4 : (k : ℝ) * δ ≤ ε := by linarith
      rw [div_le_iff₀ hm']
      nlinarith [mul_le_mul_of_nonneg_right h4 hm'.le]
  have h := (tendsto_graphProb_sub_of_eq_on_giantEvent hG hα0 hδ0 _ _ hPQ).add
    (tendsto_graphProb_disjoint_bigSet hG hα A hA)
  rw [zero_add] at h
  exact h.congr fun _ ↦ sub_add_cancel _ _

/-- **Theorem 5, supercritical, (6.2): the giant branch.** For `α > 1` and queries `A m` of
eventually exactly `k` features, `P(||C_m(A)|/m - s| ≤ ε) → 1 - (1 - s)^k` for every
`0 < ε < s / 2`.
Assumes: `GiantComponentLaw α`. -/
theorem tendsto_graphProb_reach_giant {α : ℝ} (hG : GiantComponentLaw α) (hα : 1 < α) {k : ℕ}
    (A : ∀ m : ℕ, Finset (Fin m)) (hA : ∀ᶠ m in atTop, (A m).card = k) {ε : ℝ} (hε : 0 < ε)
    (hεs : 2 * ε < giantFraction α) :
    Tendsto (fun m : ℕ ↦ graphProb m (α / m) fun E ↦
      |((reach (edgeGraph E) (A m)).card : ℝ) / m - giantFraction α| ≤ ε) atTop
        (𝓝 (1 - (1 - giantFraction α) ^ k)) := by
  have hα0 : 0 ≤ α := by linarith
  have hk1 : (0 : ℝ) < k + 1 := by positivity
  obtain ⟨δ, hδ0, hkδ⟩ : ∃ δ : ℝ, 0 < δ ∧ ((k : ℝ) + 1) * δ = ε :=
    ⟨ε / (k + 1), div_pos hε hk1, by rw [mul_div_assoc', mul_div_cancel_left₀ ε hk1.ne']⟩
  have hkδ0 : 0 ≤ (k : ℝ) * δ := mul_nonneg (Nat.cast_nonneg k) hδ0.le
  have hδs : δ < giantFraction α / 2 := by linarith
  have hPQ : ∀ᶠ m in atTop, ∀ E : Finset (Sym2 (Fin m)),
      GiantEvent (giantFraction α) δ (edgeGraph E) →
        (|((reach (edgeGraph E) (A m)).card : ℝ) / m - giantFraction α| ≤ ε ↔
          ¬Disjoint (A m) (bigSet (edgeGraph E) (giantFraction α * m / 2))) := by
    filter_upwards [hA] with m hAm E hE
    obtain ⟨v, hv, hsmall⟩ := hE
    have hm' : (0 : ℝ) < m := Nat.cast_pos.mpr v.pos
    rw [bigSet_eq_reach_of_giantEvent hδs hv hsmall]
    constructor
    · intro hgiant hd
      have h := card_reach_le_of_forall_not_mem (A m) hsmall fun a ha ↦ disjoint_left.mp hd ha
      rw [hAm] at h
      have h4 : (k : ℝ) * δ ≤ ε := by linarith
      have h5 : ((reach (edgeGraph E) (A m)).card : ℝ) / m ≤ ε := by
        rw [div_le_iff₀ hm']
        nlinarith [mul_le_mul_of_nonneg_right h4 hm'.le]
      linarith [(abs_le.mp hgiant).1]
    · intro hnd
      obtain ⟨a, haA, haB⟩ := not_disjoint_iff.mp hnd
      have h := abs_card_reach_div_sub_le_of_mem (A m) hv hsmall haA haB
      rwa [hAm, hkδ] at h
  have hmiss := (tendsto_graphProb_disjoint_bigSet hG hα A hA).const_sub 1
  have hhit : Tendsto (fun m : ℕ ↦ graphProb m (α / m) fun E ↦
      ¬Disjoint (A m) (bigSet (edgeGraph E) (giantFraction α * m / 2))) atTop
        (𝓝 (1 - (1 - giantFraction α) ^ k)) :=
    hmiss.congr fun m ↦ by
      linarith [graphProb_add_not m (α / m)
        (fun E ↦ Disjoint (A m) (bigSet (edgeGraph E) (giantFraction α * m / 2)))]
  have h := (tendsto_graphProb_sub_of_eq_on_giantEvent hG hα0 hδ0 _ _ hPQ).add hhit
  rw [zero_add] at h
  exact h.congr fun _ ↦ sub_add_cancel _ _

end

end Descent.Pangenome.AncestralLocality
