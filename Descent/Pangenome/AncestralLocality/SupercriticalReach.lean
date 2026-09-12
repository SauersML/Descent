/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Pangenome.AncestralLocality.LocalityTransition
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Order.Filter.AtTopBot.Archimedean

assert_below Descent.PopGen Descent.Spectral Descent.Blindness Descent.Conditionals
assert_below Descent.Portability Descent.Decision Descent.Program

/-!
# The supercritical locality transition, conditional on the giant component theorem

`Descent.Pangenome.AncestralLocality.LocalityTransition` bounds the expected reach of a query in
`G(m, α/m)` for `α < 1` and constructs the giant fraction `giantFraction α`, the root of
`s = 1 - e^{-α s}` for `α > 1`. This file proves what the note's (6.2) needs from the random graph
beyond that constant, with the one classical input it rests on carried as a hypothesis.

**The classical input.** `GiantComponentLaw α` is the Erdős–Rényi giant component theorem for
`G(m, α/m)`, in a form that chooses no largest component. For every `ε > 0` the probability of
`GiantEvent (giantFraction α) ε` tends to one. The event says that some component `C(v)` has
`|C(v)|/m` within `ε` of `s`, and that every feature outside `C(v)` lies in a component of at
most `ε m` features. Probabilities are `graphProb`, the expectation of an indicator.

**The subcritical half is proved.** For `0 ≤ α < 1` the law holds with `s = 0`
(`giantComponentLaw_of_lt_one`), derived from (6.1). If every component has at most `ε m`
features the event holds (`giantEvent_zero_of_forall_card_le`). If some component is larger, the
component sizes summed over features exceed `(ε m)^2` (`sq_card_reach_le_sum`, via
`reach_singleton_eq_of_mem`), and that sum has expectation at most `m/(1 - α)` by (6.1). So the
event fails with probability at most `1/((1 - α) ε^2 m)` (`graphProb_not_giantEvent_zero_le`).
`giantComponentLaw_half` is the witness at `α = 1/2`.

**The support of the limit law (6.2).** On `GiantEvent s ε` the reach of a query `A` is either at
most `|A| ε m` or within `(|A| + 1) ε` of `s m` (`giantEvent_card_reach_dichotomy`). A query that
touches the giant component contains it and adds at most `ε m` features per root
(`abs_card_reach_div_sub_le_of_mem`); a query that misses it is a union of `|A|` small components
(`card_reach_le_of_forall_not_mem`). Assuming the law, for queries of at most `k`
features the reach fraction `|C_m(A)|/m` is, with probability tending to one, within `ε` of `0`
or of `giantFraction α` (`tendsto_graphProb_reach_near_zero_or_giant`).

Scope. The Erdős–Rényi theorem for `α > 1` is not formalized: `GiantComponentLaw α` is a
hypothesis, proved here only for `0 ≤ α < 1`. The weights of the limit law, `1 - (1 - s)^k` on the
giant branch and `(1 - s)^k` on the small one, need the exchangeability of the `k` roots under
vertex permutations and are not proved. What is proved is that the limit law has no mass away
from `0` and `s`. The reach is `reach`, not the hereditary closure itself (the note's Theorem 4).

## Empirical status

None. The bodies are probabilities of events about finite edge sets under `G(m, α/m)` and their
limits in `m`. The graph law is supplied, and nothing is measured.
-/

namespace Descent.Pangenome.AncestralLocality

open Finset Filter Topology
open scoped Classical

noncomputable section

/-! ### Probabilities under `G(m, p)` -/

/-- **The probability under `G(m, p)`** of an event about the edge set. -/
def graphProb (m : ℕ) (p : ℝ) (P : Finset (Sym2 (Fin m)) → Prop) [DecidablePred P] : ℝ :=
  graphExpect m p fun E ↦ if P E then 1 else 0

/-- Expectation under `G(m, p)` is additive. -/
theorem graphExpect_add {m : ℕ} (p : ℝ) (f g : Finset (Sym2 (Fin m)) → ℝ) :
    graphExpect m p (fun E ↦ f E + g E) = graphExpect m p f + graphExpect m p g := by
  simp only [graphExpect, mul_add, sum_add_distrib]

/-- Expectation under `G(m, p)` commutes with division by a constant. -/
theorem graphExpect_div_const {m : ℕ} (p : ℝ) (f : Finset (Sym2 (Fin m)) → ℝ) (c : ℝ) :
    graphExpect m p (fun E ↦ f E / c) = graphExpect m p f / c := by
  simp only [graphExpect, div_eq_mul_inv, sum_mul, mul_assoc]

/-- The probabilities of an event and of its negation add up to one. -/
theorem graphProb_add_not (m : ℕ) (p : ℝ) (P : Finset (Sym2 (Fin m)) → Prop)
    [DecidablePred P] : graphProb m p P + graphProb m p (fun E ↦ ¬P E) = 1 := by
  rw [← graphExpect_const_one m p, graphProb, graphProb, ← graphExpect_add]
  refine sum_congr rfl fun E _ ↦ ?_
  by_cases hE : P E <;> simp [hE]

/-- A probability under `G(m, p)` is at most one. -/
theorem graphProb_le_one {m : ℕ} {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (P : Finset (Sym2 (Fin m)) → Prop) [DecidablePred P] : graphProb m p P ≤ 1 := by
  rw [← graphExpect_const_one m p, graphProb]
  exact graphExpect_mono hp0 hp1 fun E ↦ by split_ifs <;> norm_num

/-- Probability under `G(m, p)` is monotone in the event. -/
theorem graphProb_mono {m : ℕ} {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    {P Q : Finset (Sym2 (Fin m)) → Prop} [DecidablePred P] [DecidablePred Q]
    (h : ∀ E, P E → Q E) : graphProb m p P ≤ graphProb m p Q :=
  graphExpect_mono hp0 hp1 fun E ↦ by
    by_cases hP : P E
    · rw [if_pos hP, if_pos (h E hP)]
    · rw [if_neg hP]
      split_ifs <;> norm_num

/-! ### Components -/

/-- The reach is monotone in the query. -/
theorem reach_mono {m : ℕ} (G : SimpleGraph (Fin m)) {A B : Finset (Fin m)} (h : A ⊆ B) :
    reach G A ⊆ reach G B := by
  intro v hv
  obtain ⟨a, ha, hav⟩ := (mem_reach_iff G A v).mp hv
  exact (mem_reach_iff G B v).mpr ⟨a, h ha, hav⟩

/-- Features of one component have that component as their reach. -/
theorem reach_singleton_eq_of_mem {m : ℕ} {G : SimpleGraph (Fin m)} {u w : Fin m}
    (hu : u ∈ reach G {w}) : reach G {u} = reach G {w} := by
  have hwu : G.Reachable w u := by simpa [mem_reach_iff] using hu
  ext v
  simp only [mem_reach_iff, mem_singleton, exists_eq_left]
  exact ⟨fun h ↦ hwu.trans h, fun h ↦ hwu.symm.trans h⟩

/-- **The component sizes summed over features dominate the square of any one component.** -/
theorem sq_card_reach_le_sum {m : ℕ} (G : SimpleGraph (Fin m)) (w : Fin m) :
    ((reach G {w}).card : ℝ) ^ 2 ≤ ∑ u, ((reach G {u}).card : ℝ) := by
  have hconst : ∑ u ∈ reach G {w}, ((reach G {u}).card : ℝ) =
      ∑ _u ∈ reach G {w}, ((reach G {w}).card : ℝ) :=
    sum_congr rfl fun u hu ↦ by rw [reach_singleton_eq_of_mem hu]
  calc ((reach G {w}).card : ℝ) ^ 2 = ∑ u ∈ reach G {w}, ((reach G {u}).card : ℝ) := by
        rw [hconst, sum_const, nsmul_eq_mul, sq]
    _ ≤ ∑ u, ((reach G {u}).card : ℝ) :=
        sum_le_sum_of_subset_of_nonneg (subset_univ _) fun _ _ _ ↦ Nat.cast_nonneg _

/-! ### The giant-component event and the classical law -/

/-- **The giant-component event at scale `ε`**: some component `C(v)` has `|C(v)|/m` within `ε`
of `s`, and every feature outside `C(v)` lies in a component of at most `ε m` features. -/
def GiantEvent {m : ℕ} (s ε : ℝ) (G : SimpleGraph (Fin m)) : Prop :=
  ∃ v : Fin m, |((reach G {v}).card : ℝ) / m - s| ≤ ε ∧
    ∀ w, w ∉ reach G {v} → ((reach G {w}).card : ℝ) ≤ ε * m

/-- **The Erdős–Rényi giant component theorem for `G(m, α / m)`**, carried as a hypothesis: for
every `ε > 0` the giant-component event at scale `ε`, with `s = giantFraction α`, has probability
tending to one as `m → ∞`. For `α > 1` this is the classical theorem of Erdős and Rényi (1960),
which is not proved in this corpus. For `0 ≤ α < 1` it is `giantComponentLaw_of_lt_one`. -/
structure GiantComponentLaw (α : ℝ) : Prop where
  /-- The giant-component event has probability tending to one. -/
  tendsto_giantEvent : ∀ ε : ℝ, 0 < ε →
    Tendsto (fun m : ℕ ↦ graphProb m (α / m) fun E ↦
      GiantEvent (giantFraction α) ε (edgeGraph E)) atTop (𝓝 1)

/-- If every component has at most `ε m` features, the giant-component event with `s = 0`
holds. -/
theorem giantEvent_zero_of_forall_card_le {m : ℕ} {G : SimpleGraph (Fin m)} {ε : ℝ}
    (hm : 0 < m) (h : ∀ w, ((reach G {w}).card : ℝ) ≤ ε * m) : GiantEvent 0 ε G := by
  have hm' : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  refine ⟨⟨0, hm⟩, ?_, fun w _ ↦ h w⟩
  rw [sub_zero, abs_of_nonneg (div_nonneg (Nat.cast_nonneg _) hm'.le), div_le_iff₀ hm']
  exact h _

/-- The indicator that the event with `s = 0` fails is at most the component sizes summed over
features, divided by `(ε m)^2`. -/
theorem indicator_not_giantEvent_zero_le {m : ℕ} (hm : 0 < m) {ε : ℝ} (hε : 0 < ε)
    (G : SimpleGraph (Fin m)) :
    (if ¬GiantEvent 0 ε G then (1 : ℝ) else 0) ≤
      (∑ u, ((reach G {u}).card : ℝ)) / (ε * m) ^ 2 := by
  have hm' : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  have hc : 0 < (ε * m) ^ 2 := pow_pos (mul_pos hε hm') 2
  by_cases hG : GiantEvent 0 ε G
  · rw [if_neg (not_not.mpr hG)]
    exact div_nonneg (sum_nonneg fun _ _ ↦ Nat.cast_nonneg _) hc.le
  · rw [if_pos hG]
    have hw : ∃ w, ε * m < ((reach G {w}).card : ℝ) := by
      by_contra hall
      push_neg at hall
      exact hG (giantEvent_zero_of_forall_card_le hm hall)
    obtain ⟨w, hw⟩ := hw
    rw [one_le_div hc]
    exact (pow_le_pow_left₀ (mul_pos hε hm').le hw.le 2).trans (sq_card_reach_le_sum G w)

/-- **The subcritical giant-component bound.** For `0 ≤ α < 1` and `m ≥ 1` the event with
`s = 0` fails with probability at most `1 / ((1 - α) ε^2 m)`. -/
theorem graphProb_not_giantEvent_zero_le {α ε : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1) (hε : 0 < ε)
    {m : ℕ} (hm : 0 < m) :
    graphProb m (α / m) (fun E ↦ ¬GiantEvent 0 ε (edgeGraph E)) ≤
      1 / ((1 - α) * ε ^ 2) / m := by
  obtain ⟨hp0, hp1⟩ := div_natCast_nonneg_and_le_one hα0 hα1.le m
  have hm' : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  have hm'' : (m : ℝ) ≠ 0 := hm'.ne'
  have hc : 0 < (ε * m) ^ 2 := pow_pos (mul_pos hε hm') 2
  have h1α : (1 - α) ≠ 0 := (sub_pos.mpr hα1).ne'
  have hε' : ε ≠ 0 := hε.ne'
  calc graphProb m (α / m) (fun E ↦ ¬GiantEvent 0 ε (edgeGraph E))
      ≤ graphExpect m (α / m)
          (fun E ↦ (∑ u, ((reach (edgeGraph E) {u}).card : ℝ)) / (ε * m) ^ 2) :=
        graphExpect_mono hp0 hp1 fun E ↦ indicator_not_giantEvent_zero_le hm hε (edgeGraph E)
    _ = (∑ u : Fin m, graphExpect m (α / m)
          (fun E ↦ ((reach (edgeGraph E) {u}).card : ℝ))) / (ε * m) ^ 2 := by
        rw [graphExpect_div_const, graphExpect_sum]
    _ ≤ (∑ _u : Fin m, 1 / (1 - α)) / (ε * m) ^ 2 :=
        div_le_div_of_nonneg_right
          (sum_le_sum fun u _ ↦ graphExpect_card_reach_singleton_le hα0 hα1 u) hc.le
    _ = 1 / ((1 - α) * ε ^ 2) / m := by
        rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
        field_simp

/-- **The subcritical half of the giant component law**, derived from (6.1): for `0 ≤ α < 1`,
with probability tending to one every component of `G(m, α / m)` has at most `ε m` features. -/
theorem giantComponentLaw_of_lt_one {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1) :
    GiantComponentLaw α := by
  refine ⟨fun ε hε ↦ ?_⟩
  rw [giantFraction_eq_zero hα1.le]
  have hlow : Tendsto (fun m : ℕ ↦ 1 - 1 / ((1 - α) * ε ^ 2) / m) atTop (𝓝 1) := by
    have h := (tendsto_const_div_atTop_nhds_zero_nat (1 / ((1 - α) * ε ^ 2))).const_sub 1
    rwa [sub_zero] at h
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds ?_ ?_
  · filter_upwards [eventually_gt_atTop 0] with m hm
    have h1 := graphProb_not_giantEvent_zero_le hα0 hα1 hε hm
    have h2 := graphProb_add_not m (α / m) (fun E ↦ GiantEvent 0 ε (edgeGraph E))
    linarith
  · filter_upwards with m
    obtain ⟨hp0, hp1⟩ := div_natCast_nonneg_and_le_one hα0 hα1.le m
    exact graphProb_le_one hp0 hp1 _

/-- **Witness**: the giant component law at `α = 1/2`, a subcritical density at which the graph
has edges, rather than the empty graph at `α = 0`. -/
theorem giantComponentLaw_half : GiantComponentLaw (1 / 2) :=
  giantComponentLaw_of_lt_one (by norm_num) (by norm_num)

/-! ### The support of the limit law (6.2) -/

/-- **A query that misses the giant component is small.** If every feature outside `C(v)` lies in
a component of at most `ε m` features and no root of `A` lies in `C(v)`, then
`|Reach(A)| ≤ |A| ε m`. -/
theorem card_reach_le_of_forall_not_mem {m : ℕ} {G : SimpleGraph (Fin m)} {ε : ℝ} {v : Fin m}
    (A : Finset (Fin m)) (hsmall : ∀ w, w ∉ reach G {v} → ((reach G {w}).card : ℝ) ≤ ε * m)
    (hmiss : ∀ a ∈ A, a ∉ reach G {v}) : ((reach G A).card : ℝ) ≤ A.card * (ε * m) :=
  calc ((reach G A).card : ℝ) ≤ ∑ a ∈ A, ((reach G {a}).card : ℝ) := by
        exact_mod_cast card_reach_le_sum G A
    _ ≤ ∑ _a ∈ A, ε * m := sum_le_sum fun a ha ↦ hsmall a (hmiss a ha)
    _ = A.card * (ε * m) := by rw [sum_const, nsmul_eq_mul]

/-- **A query that touches the giant component is giant.** If `|C(v)|/m` is within `ε` of `s`,
every feature outside `C(v)` lies in a component of at most `ε m` features, and some root of `A`
lies in `C(v)`, then `|Reach(A)|/m` is within `(|A| + 1) ε` of `s`. -/
theorem abs_card_reach_div_sub_le_of_mem {m : ℕ} {G : SimpleGraph (Fin m)} {s ε : ℝ}
    {v : Fin m} (A : Finset (Fin m)) (hv : |((reach G {v}).card : ℝ) / m - s| ≤ ε)
    (hsmall : ∀ w, w ∉ reach G {v} → ((reach G {w}).card : ℝ) ≤ ε * m) {a : Fin m}
    (haA : a ∈ A) (haB : a ∈ reach G {v}) :
    |((reach G A).card : ℝ) / m - s| ≤ (A.card + 1) * ε := by
  have hm : (0 : ℝ) < m := Nat.cast_pos.mpr v.pos
  have hε : 0 ≤ ε := (abs_nonneg _).trans hv
  have hlow : reach G {v} ⊆ reach G A := by
    rw [← reach_singleton_eq_of_mem haB]
    exact reach_mono G (singleton_subset_iff.mpr haA)
  have hup : reach G A ⊆
      reach G {v} ∪ (A.filter fun b ↦ b ∉ reach G {v}).biUnion fun b ↦ reach G {b} := by
    intro w hw
    obtain ⟨b, hbA, hbw⟩ := (mem_reach_iff G A w).mp hw
    have hwb : w ∈ reach G {b} :=
      (mem_reach_iff G {b} w).mpr ⟨b, mem_singleton_self b, hbw⟩
    by_cases hb : b ∈ reach G {v}
    · exact mem_union_left _ (reach_singleton_eq_of_mem hb ▸ hwb)
    · exact mem_union_right _ (mem_biUnion.mpr ⟨b, mem_filter.mpr ⟨hbA, hb⟩, hwb⟩)
  have hsum : (∑ b ∈ A.filter fun b ↦ b ∉ reach G {v}, ((reach G {b}).card : ℝ)) ≤
      A.card * (ε * m) := by
    calc _ ≤ ∑ _b ∈ A.filter fun b ↦ b ∉ reach G {v}, ε * m :=
          sum_le_sum fun b hb ↦ hsmall b (mem_filter.mp hb).2
      _ = (A.filter fun b ↦ b ∉ reach G {v}).card * (ε * m) := by
          rw [sum_const, nsmul_eq_mul]
      _ ≤ A.card * (ε * m) :=
          mul_le_mul_of_nonneg_right (by exact_mod_cast card_filter_le _ _)
            (mul_nonneg hε hm.le)
  have hcard : ((reach G A).card : ℝ) ≤ (reach G {v}).card +
      ∑ b ∈ A.filter fun b ↦ b ∉ reach G {v}, ((reach G {b}).card : ℝ) := by
    have h1 := (card_le_card hup).trans (card_union_le _ _)
    have h2 := card_biUnion_le (s := A.filter fun b ↦ b ∉ reach G {v})
      (t := fun b ↦ reach G {b})
    exact_mod_cast h1.trans (Nat.add_le_add_left h2 _)
  have hcard_low : ((reach G {v}).card : ℝ) ≤ (reach G A).card := by
    exact_mod_cast card_le_card hlow
  obtain ⟨hB1, hB2⟩ := abs_le.mp hv
  have hdiv_low : ((reach G {v}).card : ℝ) / m ≤ (reach G A).card / m :=
    div_le_div_of_nonneg_right hcard_low hm.le
  have hdiv_up : ((reach G A).card : ℝ) / m ≤ (reach G {v}).card / m + A.card * ε := by
    rw [div_le_iff₀ hm, add_mul, div_mul_cancel₀ _ hm.ne']
    linarith
  have hkε : 0 ≤ (A.card : ℝ) * ε := mul_nonneg (Nat.cast_nonneg _) hε
  rw [abs_le]
  constructor <;> linarith

/-- **The deterministic core of (6.2).** On the giant-component event at scale `ε` the reach of a
query `A` is either at most `|A| ε m` or within `(|A| + 1) ε` of `s m`. -/
theorem giantEvent_card_reach_dichotomy {m : ℕ} {G : SimpleGraph (Fin m)} {s ε : ℝ}
    (A : Finset (Fin m)) (h : GiantEvent s ε G) :
    ((reach G A).card : ℝ) ≤ A.card * (ε * m) ∨
      |((reach G A).card : ℝ) / m - s| ≤ (A.card + 1) * ε := by
  obtain ⟨v, hv, hsmall⟩ := h
  by_cases hhit : ∃ a ∈ A, a ∈ reach G {v}
  · obtain ⟨a, haA, haB⟩ := hhit
    exact Or.inr (abs_card_reach_div_sub_le_of_mem A hv hsmall haA haB)
  · push_neg at hhit
    exact Or.inl (card_reach_le_of_forall_not_mem A hsmall hhit)

/-- **Theorem 5, supercritical: the support of the limit law (6.2).**
Assumes: `GiantComponentLaw α`.
For queries `A m` of at most `k` features, the probability that the reach fraction `|C_m(A)|/m`
is within `ε` of `0` or of `giantFraction α` tends to one. -/
theorem tendsto_graphProb_reach_near_zero_or_giant {α : ℝ} (hG : GiantComponentLaw α)
    (hα0 : 0 ≤ α) {k : ℕ} (A : ∀ m : ℕ, Finset (Fin m)) (hA : ∀ m, (A m).card ≤ k) {ε : ℝ}
    (hε : 0 < ε) :
    Tendsto (fun m : ℕ ↦ graphProb m (α / m) fun E ↦
      ((reach (edgeGraph E) (A m)).card : ℝ) / m ≤ ε ∨
        |((reach (edgeGraph E) (A m)).card : ℝ) / m - giantFraction α| ≤ ε) atTop (𝓝 1) := by
  have hk : (0 : ℝ) < k + 1 := by positivity
  obtain ⟨δ, hδ0, hkδ⟩ : ∃ δ : ℝ, 0 < δ ∧ ((k : ℝ) + 1) * δ = ε :=
    ⟨ε / (k + 1), div_pos hε hk, by rw [mul_div_assoc', mul_div_cancel_left₀ ε hk.ne']⟩
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (hG.tendsto_giantEvent δ hδ0) tendsto_const_nhds ?_ ?_
  · filter_upwards [eventually_gt_atTop 0,
      tendsto_natCast_atTop_atTop.eventually_ge_atTop α] with m hm0 hmα
    have hm : (0 : ℝ) < m := Nat.cast_pos.mpr hm0
    have hp1 : α / m ≤ 1 := (div_le_one hm).mpr hmα
    refine graphProb_mono (div_nonneg hα0 hm.le) hp1 fun E hE ↦ ?_
    have hAk : ((A m).card : ℝ) ≤ k := by exact_mod_cast hA m
    have hδm : 0 ≤ δ * m := mul_nonneg hδ0.le hm.le
    rcases giantEvent_card_reach_dichotomy (A m) hE with h | h
    · left
      rw [div_le_iff₀ hm]
      have h2 : ((A m).card : ℝ) * (δ * m) ≤ k * (δ * m) := mul_le_mul_of_nonneg_right hAk hδm
      have h3 : (k : ℝ) * (δ * m) + δ * m = ε * m := by
        rw [← hkδ]
        ring
      linarith
    · right
      have h2 : ((A m).card + 1 : ℝ) * δ ≤ (k + 1) * δ :=
        mul_le_mul_of_nonneg_right (by linarith) hδ0.le
      linarith
  · filter_upwards [eventually_gt_atTop 0,
      tendsto_natCast_atTop_atTop.eventually_ge_atTop α] with m hm0 hmα
    have hm : (0 : ℝ) < m := Nat.cast_pos.mpr hm0
    exact graphProb_le_one (div_nonneg hα0 hm.le) ((div_le_one hm).mpr hmα) _

end

end Descent.Pangenome.AncestralLocality
