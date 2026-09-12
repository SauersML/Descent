/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Pangenome.AncestralLocality.SupercriticalLowerBound

assert_below Descent.PopGen Descent.Spectral Descent.Blindness Descent.Conditionals
assert_below Descent.Portability Descent.Decision Descent.Program

/-!
# The second moment of the number of features in large components

`Descent.Pangenome.AncestralLocality.SupercriticalLowerBound` shows that in `G(m, α/m)` with
`α > 1` every feature lies in a component of at least `K` features with probability at least
`s - η`. This file bounds the second moment of the number `largeCount E K` of such features. So
that number concentrates, which the sprinkling argument of
`Descent.Pangenome.AncestralLocality.SupercriticalSprinkling` needs as its hypothesis.

**Components read the pairs touching them.** If two edge sets agree on every pair with a feature
in `S`, and the component of `u` in one of them is `S`, so is its component in the other
(`reach_singleton_eq_of_agree`). A quantity that reads only the pairs touching `S` is independent
of one that reads only the pairs avoiding `S` (`graphExpect_mul_of_local`, through
`touchingEdges`). Summing over the candidate components `S` recovers any quantity of the component
(`graphExpect_comp_reach_singleton`).

**A small component leaves room for a large one.** Let the component `S` of `u` have fewer than
`K` features and miss `w`. The exploration from `S ∪ {w}`, active at `w`, reads only pairs
avoiding `S` (`exploreDies_outside_congr`). If it does not die before `|S| + K` features are
discovered, `w` is in a component of at least `K` features (`le_card_reach_of_not_exploreDies`).
While fewer than `2K` features are discovered its supermartingale bound applies. So the chance that
`u` is small, `w` lies outside its component and `w` is large is at least `1 - q` times the chance
of the first two (`graphProb_small_not_mem_large_ge`), when `(1 - p (1 - q))^(m - 2K) ≤ q`.

**The second moment.** Summing over pairs, with at most `K` features `w` inside a small component
of `u` (`sum_graphProb_large_pair_le`), gives
`E[Y²] ≤ m y - (1 - q) (m (m - y) - m K)` for `Y = largeCount E K` and `y = E[Y]`
(`graphExpect_largeCount_sq_le`). With `q = 1 - s + η`, `y ≈ s m` and `K = κ m`, the variance of
`Y` is at most of order `(η + κ) m²`. Chebyshev's inequality (`graphProb_le_sub_le`) turns that into
concentration.

Scope. What is proved is the finite second-moment inequality and Chebyshev's inequality. The limit
in `m`, and its use with the upper bound of
`Descent.Pangenome.AncestralLocality.SupercriticalUpperBound` and the sprinkling lemma, are not done
here.

## Empirical status

None. The bodies are finite sums over random edge sets, counts of components and explored features.
The graph law is supplied, and nothing is measured.
-/

namespace Descent.Pangenome.AncestralLocality

open Finset Filter Topology
open scoped Classical

noncomputable section

/-! ### Events of the graph law -/

/-- Equivalent events have equal probabilities. -/
theorem graphProb_congr {m : ℕ} (p : ℝ) {P Q : Finset (Sym2 (Fin m)) → Prop} [DecidablePred P]
    [DecidablePred Q] (h : ∀ E, P E ↔ Q E) : graphProb m p P = graphProb m p Q := by
  rw [graphProb, graphProb]
  exact sum_congr rfl fun E _ ↦ by simp only [h E]

/-- Two disjoint events implying a third have probabilities adding up to at most its probability. -/
theorem graphProb_add_le_of_disjoint {m : ℕ} {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    {P Q R : Finset (Sym2 (Fin m)) → Prop} [DecidablePred P] [DecidablePred Q]
    [DecidablePred R] (hPQ : ∀ E, P E → ¬Q E) (hPR : ∀ E, P E → R E) (hQR : ∀ E, Q E → R E) :
    graphProb m p P + graphProb m p Q ≤ graphProb m p R := by
  rw [graphProb, graphProb, ← graphExpect_add, graphProb]
  refine graphExpect_mono hp0 hp1 fun E ↦ ?_
  by_cases hP : P E
  · simp only [if_pos hP, if_neg (hPQ E hP), if_pos (hPR E hP), add_zero, le_refl]
  · by_cases hQ : Q E
    · simp only [if_neg hP, if_pos hQ, if_pos (hQR E hQ), zero_add, le_refl]
    · simp only [if_neg hP, if_neg hQ, add_zero]
      split_ifs <;> norm_num

/-- An event splits into two disjoint parts. -/
theorem graphProb_eq_add_of_disjoint {m : ℕ} (p : ℝ) {P Q R : Finset (Sym2 (Fin m)) → Prop}
    [DecidablePred P] [DecidablePred Q] [DecidablePred R] (hR : ∀ E, R E ↔ P E ∨ Q E)
    (hPQ : ∀ E, P E → ¬Q E) :
    graphProb m p R = graphProb m p P + graphProb m p Q := by
  rw [graphProb, graphProb, graphProb, ← graphExpect_add]
  refine sum_congr rfl fun E _ ↦ ?_
  by_cases hP : P E
  · simp only [if_pos hP, if_neg (hPQ E hP), if_pos ((hR E).mpr (Or.inl hP)), add_zero]
  · by_cases hQ : Q E
    · simp only [if_neg hP, if_pos hQ, if_pos ((hR E).mpr (Or.inr hQ)), zero_add]
    · have hnR : ¬R E := fun h ↦ ((hR E).mp h).elim hP hQ
      simp only [if_neg hP, if_neg hQ, if_neg hnR, add_zero]

/-- **Chebyshev's inequality under `G(m, p)`.** -/
theorem graphProb_le_sub_le {m : ℕ} {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (X : Finset (Sym2 (Fin m)) → ℝ) (c t : ℝ) (ht : 0 < t) :
    graphProb m p (fun E ↦ X E ≤ c - t) ≤ graphExpect m p (fun E ↦ (X E - c) ^ 2) / t ^ 2 := by
  rw [← graphExpect_div_const, graphProb]
  refine graphExpect_mono hp0 hp1 fun E ↦ ?_
  show (if X E ≤ c - t then (1 : ℝ) else 0) ≤ (X E - c) ^ 2 / t ^ 2
  split_ifs with h
  · rw [le_div_iff₀ (by positivity), one_mul]
    nlinarith [mul_nonneg (sub_nonneg.mpr h) (by linarith : (0 : ℝ) ≤ c - X E + t)]
  · positivity

/-! ### Components read the pairs touching them -/

/-- Membership in the component of one feature is reachability. -/
theorem mem_reach_singleton_iff {m : ℕ} (G : SimpleGraph (Fin m)) (u v : Fin m) :
    v ∈ reach G {u} ↔ Relation.ReflTransGen G.Adj u v := by
  rw [mem_reach_iff, ← SimpleGraph.reachable_iff_reflTransGen]
  simp

/-- **The component of `u` reads only the pairs touching it.** If `E` and `E'` agree on every pair
with a feature in `S` and the component of `u` in `E` is `S`, its component in `E'` is `S`. -/
theorem reach_singleton_eq_of_agree {m : ℕ} {E E' : Finset (Sym2 (Fin m))}
    {S : Finset (Fin m)} {u : Fin m}
    (h : ∀ x y, (x ∈ S ∨ y ∈ S) → (s(x, y) ∈ E ↔ s(x, y) ∈ E'))
    (hS : reach (edgeGraph E) {u} = S) : reach (edgeGraph E') {u} = S := by
  have hu : u ∈ S := by
    rw [← hS]
    exact (mem_reach_singleton_iff _ u u).mpr Relation.ReflTransGen.refl
  ext v
  rw [mem_reach_singleton_iff]
  constructor
  · intro hv
    induction hv with
    | refl => exact hu
    | @tail b c _ hbc ih =>
      obtain ⟨hbcE', -⟩ := (edgeGraph_adj_iff E' b c).mp hbc
      have hb : b ∈ reach (edgeGraph E) {u} := by
        rw [hS]
        exact ih
      have hc := reach_singleton_closed E u b hb c ((h b c (Or.inl ih)).mpr hbcE')
      rwa [hS] at hc
  · intro hv
    have hv' : Relation.ReflTransGen (edgeGraph E).Adj u v := by
      rw [← mem_reach_singleton_iff, hS]
      exact hv
    clear hv
    induction hv' with
    | refl => exact Relation.ReflTransGen.refl
    | @tail b c hab hbc ih =>
      have hb : b ∈ S := by
        rw [← hS]
        exact (mem_reach_singleton_iff _ u b).mpr hab
      obtain ⟨hbcE, hne⟩ := (edgeGraph_adj_iff E b c).mp hbc
      exact ih.tail ((edgeGraph_adj_iff E' b c).mpr ⟨(h b c (Or.inl hb)).mp hbcE, hne⟩)

/-- **The potential edges touching a set of features.** -/
def touchingEdges {m : ℕ} (S : Finset (Fin m)) : Finset (Sym2 (Fin m)) :=
  (potentialEdges m).filter fun e ↦ ∃ x ∈ S, x ∈ e

/-- A pair touches `S` when it is a potential edge with a feature in `S`. -/
theorem mk_mem_touchingEdges_iff {m : ℕ} {S : Finset (Fin m)} {x y : Fin m} :
    s(x, y) ∈ touchingEdges S ↔ s(x, y) ∈ potentialEdges m ∧ (x ∈ S ∨ y ∈ S) := by
  simp only [touchingEdges, mem_filter, Sym2.mem_iff]
  constructor
  · rintro ⟨hp, z, hz, hzxy⟩
    rcases hzxy with rfl | rfl
    · exact ⟨hp, Or.inl hz⟩
    · exact ⟨hp, Or.inr hz⟩
  · rintro ⟨hp, hx | hy⟩
    · exact ⟨hp, x, hx, Or.inl rfl⟩
    · exact ⟨hp, y, hy, Or.inr rfl⟩

/-- **Quantities of the pairs touching `S` and of the pairs avoiding `S` are independent.** -/
theorem graphExpect_mul_of_local {m : ℕ} (p : ℝ) (S : Finset (Fin m))
    {f g : Finset (Sym2 (Fin m)) → ℝ}
    (hf : ∀ E E', (∀ x y, (x ∈ S ∨ y ∈ S) → (s(x, y) ∈ E ↔ s(x, y) ∈ E')) → f E = f E')
    (hg : ∀ E E', (∀ x y, x ∉ S → y ∉ S → (s(x, y) ∈ E ↔ s(x, y) ∈ E')) → g E = g E') :
    graphExpect m p (fun E ↦ f E * g E) = graphExpect m p f * graphExpect m p g := by
  have hT : touchingEdges S ⊆ potentialEdges m := filter_subset _ _
  have hf' : ∀ E₁ ⊆ touchingEdges S, ∀ E₂ ⊆ potentialEdges m \ touchingEdges S,
      f (E₁ ∪ E₂) = f E₁ := by
    intro E₁ _ E₂ hE₂
    refine hf _ _ fun x y hxy ↦ ?_
    rw [mem_union]
    refine ⟨fun h ↦ h.resolve_right fun h2 ↦ ?_, Or.inl⟩
    obtain ⟨hpot, hnot⟩ := mem_sdiff.mp (hE₂ h2)
    exact hnot (mk_mem_touchingEdges_iff.mpr ⟨hpot, hxy⟩)
  have hg' : ∀ E₁ ⊆ touchingEdges S, ∀ E₂ ⊆ potentialEdges m \ touchingEdges S,
      g (E₁ ∪ E₂) = g E₂ := by
    intro E₁ hE₁ E₂ _
    refine hg _ _ fun x y hx hy ↦ ?_
    rw [mem_union]
    refine ⟨fun h ↦ h.resolve_left fun h1 ↦ ?_, Or.inr⟩
    rcases (mk_mem_touchingEdges_iff.mp (hE₁ h1)).2 with h' | h'
    · exact hx h'
    · exact hy h'
  have hgT : graphExpect m p g = subsetExpect (potentialEdges m \ touchingEdges S) p g := by
    rw [graphExpect_eq_subsetExpect]
    refine subsetExpect_eq_of_local p sdiff_subset fun E₂ hE₂ E₁ hE₁ ↦ ?_
    have hE₁T : E₁ ⊆ touchingEdges S := fun e he ↦ by
      have h := hE₁ he
      rw [mem_sdiff, mem_sdiff] at h
      tauto
    rw [union_comm]
    exact hg' E₁ hE₁T E₂ hE₂
  rw [graphExpect_eq_subsetExpect, subsetExpect_split p hT, hgT, graphExpect_eq_subsetExpect,
    subsetExpect_eq_of_local p hT hf', ← subsetExpect_mul_const]
  refine sum_congr rfl fun E₁ hE₁ ↦ ?_
  congr 1
  rw [mul_comm (f E₁), ← subsetExpect_mul_const]
  refine sum_congr rfl fun E₂ hE₂ ↦ ?_
  rw [hf' E₁ (mem_powerset.mp hE₁) E₂ (mem_powerset.mp hE₂),
    hg' E₁ (mem_powerset.mp hE₁) E₂ (mem_powerset.mp hE₂), mul_comm (f E₁)]

/-- **Summing over the candidate components.** A quantity of the component of `u` is the sum, over
the candidate sets `S`, of the quantity at `S` on the event that the component is `S`. -/
theorem graphExpect_comp_reach_singleton {m : ℕ} (p : ℝ) (u : Fin m)
    (h : Finset (Fin m) → Finset (Sym2 (Fin m)) → ℝ) :
    graphExpect m p (fun E ↦ h (reach (edgeGraph E) {u}) E) =
      ∑ S : Finset (Fin m), graphExpect m p
        (fun E ↦ (if reach (edgeGraph E) {u} = S then (1 : ℝ) else 0) * h S E) := by
  rw [← graphExpect_sum]
  congr 1
  funext E
  simp only [ite_mul, one_mul, zero_mul]
  rw [sum_ite_eq, if_pos (mem_univ _)]

/-! ### A small component leaves room for a large one -/

/-- **The exploration from outside a set reads only the pairs avoiding it.** -/
theorem exploreDies_outside_congr {m K : ℕ} {E E' : Finset (Sym2 (Fin m))}
    {S : Finset (Fin m)} {w : Fin m} (hw : w ∉ S)
    (h : ∀ x y, x ∉ S → y ∉ S → (s(x, y) ∈ E ↔ s(x, y) ∈ E')) (t : ℕ) :
    exploreDies E K t (S ∪ {w}) {w} ↔ exploreDies E' K t (S ∪ {w}) {w} := by
  have hX : ∀ x, x ∉ (S ∪ {w}) \ {w} → x ∉ S := fun x hx hxS ↦
    hx (mem_sdiff.mpr ⟨mem_union_left _ hxS, fun h' ↦ hw (mem_singleton.mp h' ▸ hxS)⟩)
  exact exploreDies_congr t (fun _ hx ↦ mem_union_right _ hx)
    fun x y hx hy ↦ h x y (hX x hx) (hX y hy)

/-- **Survival from outside a component makes a large component.** If the exploration from the
component of `u` together with `w`, active at `w`, does not die before `|C(u)| + K` features are
discovered, the component of `w` has at least `K` features. -/
theorem le_card_reach_of_not_exploreDies {m K : ℕ} {E : Finset (Sym2 (Fin m))} {u w : Fin m}
    (h : ¬exploreDies E ((reach (edgeGraph E) {u}).card + K) m
      (reach (edgeGraph E) {u} ∪ {w}) {w}) :
    K ≤ (reach (edgeGraph E) {w}).card := by
  by_contra hK
  push_neg at hK
  refine h (exploreDies_of_closed (C := reach (edgeGraph E) {u} ∪ reach (edgeGraph E) {w})
    ?_ ?_ m (fun _ hx ↦ mem_union_right _ hx)
    (union_subset_union Subset.rfl
      (singleton_subset_iff.mpr (subset_reach (edgeGraph E) {w} (mem_singleton_self w)))) ?_)
  · intro x hx y hxy
    rcases mem_union.mp hx with hx | hx
    · exact mem_union_left _ (reach_singleton_closed E u x hx y hxy)
    · exact mem_union_right _ (reach_singleton_closed E w x hx y hxy)
  · calc (reach (edgeGraph E) {u} ∪ reach (edgeGraph E) {w}).card
        ≤ (reach (edgeGraph E) {u}).card + (reach (edgeGraph E) {w}).card := card_union_le _ _
      _ < (reach (edgeGraph E) {u}).card + K := by omega
  · calc (univ \ ((reach (edgeGraph E) {u} ∪ {w}) \ {w})).card
        ≤ (univ : Finset (Fin m)).card := card_le_card sdiff_subset
      _ = m := by rw [card_univ, Fintype.card_fin]

/-- **A small component leaves room for a large one.** If `(1 - p (1 - q))^(m - 2K) ≤ q`, then
for any two features `u` and `w`, the chance that `u` is in a component of fewer than `K`
features, `w` lies outside it, and `w` is in a component of at least `K` features is at least
`1 - q` times the chance of the first two. -/
theorem graphProb_small_not_mem_large_ge {m K : ℕ} {p q : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hq : (1 - p * (1 - q)) ^ (m - 2 * K) ≤ q) (u w : Fin m) :
    (1 - q) * graphProb m p (fun E ↦ (reach (edgeGraph E) {u}).card < K ∧
        w ∉ reach (edgeGraph E) {u}) ≤
      graphProb m p (fun E ↦ (reach (edgeGraph E) {u}).card < K ∧
        w ∉ reach (edgeGraph E) {u} ∧ K ≤ (reach (edgeGraph E) {w}).card) := by
  have hbase0 : 0 ≤ 1 - p * (1 - q) := by nlinarith
  have hbase1 : 1 - p * (1 - q) ≤ 1 := by nlinarith
  have hstep : ∀ S : Finset (Fin m),
      (1 - q) * graphExpect m p (fun E ↦ (if reach (edgeGraph E) {u} = S then (1 : ℝ) else 0) *
          (if S.card < K ∧ w ∉ S then (1 : ℝ) else 0)) ≤
        graphExpect m p (fun E ↦ (if reach (edgeGraph E) {u} = S then (1 : ℝ) else 0) *
          (if S.card < K ∧ w ∉ S ∧ ¬exploreDies E (S.card + K) m (S ∪ {w}) {w}
            then (1 : ℝ) else 0)) := by
    intro S
    by_cases hc : S.card < K ∧ w ∉ S
    · have hindep := graphExpect_mul_of_local p S
        (f := fun E ↦ if reach (edgeGraph E) {u} = S then (1 : ℝ) else 0)
        (g := fun E ↦ if S.card < K ∧ w ∉ S ∧ ¬exploreDies E (S.card + K) m (S ∪ {w}) {w}
          then (1 : ℝ) else 0)
        (fun E E' hEE' ↦ by
          have hiff : reach (edgeGraph E) {u} = S ↔ reach (edgeGraph E') {u} = S :=
            ⟨reach_singleton_eq_of_agree hEE',
              reach_singleton_eq_of_agree fun x y hxy ↦ (hEE' x y hxy).symm⟩
          simp only [hiff])
        (fun E E' hEE' ↦ by simp only [exploreDies_outside_congr hc.2 hEE' m])
      beta_reduce at hindep
      rw [hindep]
      have hqS : (1 - p * (1 - q)) ^ (m - (S.card + K)) ≤ q :=
        (pow_le_pow_of_le_one hbase0 hbase1 (by omega)).trans hq
      have hdie := graphProb_exploreDies_le (K := S.card + K) hp0 hp1 hq0 hq1 hqS m
        (D := S ∪ {w}) (A := {w}) (fun _ hx ↦ mem_union_right _ hx)
      rw [card_singleton, pow_one] at hdie
      have hadd := graphProb_add_not m p
        (fun E ↦ exploreDies E (S.card + K) m (S ∪ {w}) {w})
      have hsurv : graphExpect m p (fun E ↦ if S.card < K ∧ w ∉ S ∧
          ¬exploreDies E (S.card + K) m (S ∪ {w}) {w} then (1 : ℝ) else 0) =
            graphProb m p (fun E ↦ ¬exploreDies E (S.card + K) m (S ∪ {w}) {w}) := by
        rw [graphProb]
        exact sum_congr rfl fun E _ ↦ by simp only [hc, true_and]
      have hconst : graphExpect m p (fun E ↦ (if reach (edgeGraph E) {u} = S then (1 : ℝ) else 0) *
          (if S.card < K ∧ w ∉ S then (1 : ℝ) else 0)) =
            graphExpect m p (fun E ↦ if reach (edgeGraph E) {u} = S then (1 : ℝ) else 0) := by
        simp only [if_pos hc, mul_one]
      rw [hconst, hsurv]
      have hnn : 0 ≤ graphExpect m p (fun E ↦ if reach (edgeGraph E) {u} = S then (1 : ℝ) else 0) :=
        graphProb_nonneg hp0 hp1 (fun E ↦ reach (edgeGraph E) {u} = S)
      calc (1 - q) * graphExpect m p (fun E ↦ if reach (edgeGraph E) {u} = S then (1 : ℝ) else 0)
          = graphExpect m p (fun E ↦ if reach (edgeGraph E) {u} = S then (1 : ℝ) else 0) *
              (1 - q) := mul_comm _ _
        _ ≤ graphExpect m p (fun E ↦ if reach (edgeGraph E) {u} = S then (1 : ℝ) else 0) *
              graphProb m p (fun E ↦ ¬exploreDies E (S.card + K) m (S ∪ {w}) {w}) :=
            mul_le_mul_of_nonneg_left (by linarith) hnn
    · have h1 : (fun E ↦ (if reach (edgeGraph E) {u} = S then (1 : ℝ) else 0) *
          (if S.card < K ∧ w ∉ S then (1 : ℝ) else 0)) = fun _ ↦ 0 := by
        funext E
        simp only [if_neg hc, mul_zero]
      have h2 : (fun E ↦ (if reach (edgeGraph E) {u} = S then (1 : ℝ) else 0) *
          (if S.card < K ∧ w ∉ S ∧ ¬exploreDies E (S.card + K) m (S ∪ {w}) {w}
            then (1 : ℝ) else 0)) = fun _ ↦ 0 := by
        funext E
        rw [if_neg fun h ↦ hc ⟨h.1, h.2.1⟩, mul_zero]
      rw [h1, h2, graphExpect_const, mul_zero]
  have hL := graphExpect_comp_reach_singleton p u
    (fun S _ ↦ if S.card < K ∧ w ∉ S then (1 : ℝ) else 0)
  have hR := graphExpect_comp_reach_singleton p u
    (fun S E ↦ if S.card < K ∧ w ∉ S ∧ ¬exploreDies E (S.card + K) m (S ∪ {w}) {w}
      then (1 : ℝ) else 0)
  beta_reduce at hL hR
  calc (1 - q) * graphProb m p (fun E ↦ (reach (edgeGraph E) {u}).card < K ∧
          w ∉ reach (edgeGraph E) {u})
      = (1 - q) * graphExpect m p (fun E ↦ if (reach (edgeGraph E) {u}).card < K ∧
          w ∉ reach (edgeGraph E) {u} then (1 : ℝ) else 0) := by
        rw [graphProb]
        congr 1
        exact sum_congr rfl fun E _ ↦ by simp only []
    _ = ∑ S : Finset (Fin m), (1 - q) * graphExpect m p
          (fun E ↦ (if reach (edgeGraph E) {u} = S then (1 : ℝ) else 0) *
            (if S.card < K ∧ w ∉ S then (1 : ℝ) else 0)) := by
        rw [hL, mul_sum]
    _ ≤ ∑ S : Finset (Fin m), graphExpect m p
          (fun E ↦ (if reach (edgeGraph E) {u} = S then (1 : ℝ) else 0) *
            (if S.card < K ∧ w ∉ S ∧ ¬exploreDies E (S.card + K) m (S ∪ {w}) {w}
              then (1 : ℝ) else 0)) :=
        sum_le_sum fun S _ ↦ hstep S
    _ = graphExpect m p (fun E ↦ if (reach (edgeGraph E) {u}).card < K ∧
          w ∉ reach (edgeGraph E) {u} ∧ ¬exploreDies E ((reach (edgeGraph E) {u}).card + K) m
            (reach (edgeGraph E) {u} ∪ {w}) {w} then (1 : ℝ) else 0) := hR.symm
    _ ≤ graphProb m p (fun E ↦ (reach (edgeGraph E) {u}).card < K ∧
          w ∉ reach (edgeGraph E) {u} ∧ K ≤ (reach (edgeGraph E) {w}).card) := by
        rw [graphProb]
        refine graphExpect_mono hp0 hp1 fun E ↦ ?_
        by_cases h : (reach (edgeGraph E) {u}).card < K ∧ w ∉ reach (edgeGraph E) {u} ∧
            ¬exploreDies E ((reach (edgeGraph E) {u}).card + K) m
              (reach (edgeGraph E) {u} ∪ {w}) {w}
        · have hK := le_card_reach_of_not_exploreDies h.2.2
          simp only [if_pos h, if_pos (show (reach (edgeGraph E) {u}).card < K ∧
            w ∉ reach (edgeGraph E) {u} ∧ K ≤ (reach (edgeGraph E) {w}).card from
              ⟨h.1, h.2.1, hK⟩), le_refl]
        · simp only [if_neg h]
          split_ifs <;> norm_num

/-! ### The second moment -/

/-- **The number of features in components of at least `K` features.** -/
def largeCount {m : ℕ} (E : Finset (Sym2 (Fin m))) (K : ℕ) : ℝ :=
  ((univ.filter fun v ↦ K ≤ (reach (edgeGraph E) {v}).card).card : ℝ)

/-- The number of large features is a sum of indicators. -/
theorem largeCount_eq_sum {m : ℕ} (E : Finset (Sym2 (Fin m))) (K : ℕ) :
    largeCount E K = ∑ v, if K ≤ (reach (edgeGraph E) {v}).card then (1 : ℝ) else 0 := by
  rw [largeCount, natCast_card_filter]

/-- The expected number of large features is the sum of the chances that each feature is large. -/
theorem graphExpect_largeCount {m : ℕ} (p : ℝ) (K : ℕ) :
    graphExpect m p (fun E ↦ largeCount E K) =
      ∑ v, graphProb m p (fun E ↦ K ≤ (reach (edgeGraph E) {v}).card) := by
  simp only [largeCount_eq_sum]
  rw [graphExpect_sum]
  exact sum_congr rfl fun v _ ↦ by rw [graphProb]

/-- **The large pairs from one feature.** If `(1 - p (1 - q))^(m - 2K) ≤ q`, the chances that `u`
and `w` are both in components of at least `K` features, summed over `w`, are at most the expected
number of large features minus `(1 - q) (m P(|C(u)| < K) - K)`. -/
theorem sum_graphProb_large_pair_le {m K : ℕ} {p q : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hq : (1 - p * (1 - q)) ^ (m - 2 * K) ≤ q) (u : Fin m) :
    ∑ w, graphProb m p (fun E ↦ K ≤ (reach (edgeGraph E) {u}).card ∧
        K ≤ (reach (edgeGraph E) {w}).card) ≤
      graphExpect m p (fun E ↦ largeCount E K) -
        (1 - q) * (m * graphProb m p (fun E ↦ (reach (edgeGraph E) {u}).card < K) - K) := by
  have h1 : ∀ w, graphProb m p (fun E ↦ K ≤ (reach (edgeGraph E) {u}).card ∧
        K ≤ (reach (edgeGraph E) {w}).card) +
      (1 - q) * graphProb m p (fun E ↦ (reach (edgeGraph E) {u}).card < K ∧
        w ∉ reach (edgeGraph E) {u}) ≤
      graphProb m p (fun E ↦ K ≤ (reach (edgeGraph E) {w}).card) := by
    intro w
    have hdisj := graphProb_add_le_of_disjoint hp0 hp1
      (P := fun E ↦ K ≤ (reach (edgeGraph E) {u}).card ∧ K ≤ (reach (edgeGraph E) {w}).card)
      (Q := fun E ↦ (reach (edgeGraph E) {u}).card < K ∧ w ∉ reach (edgeGraph E) {u} ∧
        K ≤ (reach (edgeGraph E) {w}).card)
      (R := fun E ↦ K ≤ (reach (edgeGraph E) {w}).card)
      (fun _ hP hQ ↦ absurd hQ.1 (not_lt.mpr hP.1)) (fun _ hP ↦ hP.2) (fun _ hQ ↦ hQ.2.2)
    have hsmall := graphProb_small_not_mem_large_ge hp0 hp1 hq0 hq1 hq u w
    linarith
  have h2 : ∀ w, graphProb m p (fun E ↦ (reach (edgeGraph E) {u}).card < K ∧
        w ∉ reach (edgeGraph E) {u}) =
      graphProb m p (fun E ↦ (reach (edgeGraph E) {u}).card < K) -
        graphProb m p (fun E ↦ (reach (edgeGraph E) {u}).card < K ∧
          w ∈ reach (edgeGraph E) {u}) := by
    intro w
    have h := graphProb_eq_add_of_disjoint p
      (R := fun E ↦ (reach (edgeGraph E) {u}).card < K)
      (P := fun E ↦ (reach (edgeGraph E) {u}).card < K ∧ w ∉ reach (edgeGraph E) {u})
      (Q := fun E ↦ (reach (edgeGraph E) {u}).card < K ∧ w ∈ reach (edgeGraph E) {u})
      (fun _ ↦ by tauto) (fun _ hP hQ ↦ hP.2 hQ.2)
    linarith
  have h3 : ∑ w, graphProb m p (fun E ↦ (reach (edgeGraph E) {u}).card < K ∧
      w ∈ reach (edgeGraph E) {u}) ≤ K := by
    rw [← graphExpect_const (m := m) p (K : ℝ)]
    simp only [graphProb]
    rw [← graphExpect_sum]
    refine graphExpect_mono hp0 hp1 fun E ↦ ?_
    by_cases hs : (reach (edgeGraph E) {u}).card < K
    · simp only [hs, true_and]
      rw [Fintype.sum_ite_mem, sum_const, nsmul_eq_mul, mul_one]
      exact_mod_cast hs.le
    · simp only [hs, false_and, if_false, sum_const_zero]
      exact Nat.cast_nonneg K
  have hsum := sum_le_sum fun w (_ : w ∈ (univ : Finset (Fin m))) ↦ h1 w
  rw [sum_add_distrib, ← mul_sum, ← graphExpect_largeCount] at hsum
  have hsplit : ∑ w, graphProb m p (fun E ↦ (reach (edgeGraph E) {u}).card < K ∧
      w ∉ reach (edgeGraph E) {u}) =
        m * graphProb m p (fun E ↦ (reach (edgeGraph E) {u}).card < K) -
          ∑ w, graphProb m p (fun E ↦ (reach (edgeGraph E) {u}).card < K ∧
            w ∈ reach (edgeGraph E) {u}) := by
    rw [sum_congr rfl fun w _ ↦ h2 w, sum_sub_distrib, sum_const, card_univ, Fintype.card_fin,
      nsmul_eq_mul]
  rw [hsplit] at hsum
  have hq' : 0 ≤ 1 - q := by linarith
  have h4 := mul_le_mul_of_nonneg_left h3 hq'
  linarith

/-- **The second moment of the number of large features.** If `(1 - p (1 - q))^(m - 2K) ≤ q` and
`y` is the expected number of features in components of at least `K` features, the expected square
of that number is at most `m y - (1 - q) (m (m - y) - m K)`. -/
theorem graphExpect_largeCount_sq_le {m K : ℕ} {p q : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hq : (1 - p * (1 - q)) ^ (m - 2 * K) ≤ q) :
    graphExpect m p (fun E ↦ largeCount E K ^ 2) ≤
      m * graphExpect m p (fun E ↦ largeCount E K) -
        (1 - q) * (m * (m - graphExpect m p (fun E ↦ largeCount E K)) - m * K) := by
  have hpt : ∀ E : Finset (Sym2 (Fin m)), largeCount E K ^ 2 = ∑ u, ∑ w,
      if K ≤ (reach (edgeGraph E) {u}).card ∧ K ≤ (reach (edgeGraph E) {w}).card
        then (1 : ℝ) else 0 := by
    intro E
    rw [largeCount_eq_sum, sq, sum_mul_sum]
    simp only [ite_zero_mul_ite_zero, mul_one]
  have hsq : graphExpect m p (fun E ↦ largeCount E K ^ 2) =
      ∑ u, ∑ w, graphProb m p (fun E ↦ K ≤ (reach (edgeGraph E) {u}).card ∧
        K ≤ (reach (edgeGraph E) {w}).card) := by
    simp only [hpt]
    rw [graphExpect_sum]
    refine sum_congr rfl fun u _ ↦ ?_
    rw [graphExpect_sum]
    exact sum_congr rfl fun w _ ↦ by rw [graphProb]
  have hcompl : ∀ u : Fin m, graphProb m p (fun E ↦ (reach (edgeGraph E) {u}).card < K) =
      1 - graphProb m p (fun E ↦ K ≤ (reach (edgeGraph E) {u}).card) := by
    intro u
    have h := graphProb_add_not m p (fun E ↦ K ≤ (reach (edgeGraph E) {u}).card)
    have hc : graphProb m p (fun E ↦ ¬K ≤ (reach (edgeGraph E) {u}).card) =
        graphProb m p (fun E ↦ (reach (edgeGraph E) {u}).card < K) :=
      graphProb_congr p fun _ ↦ not_le
    linarith
  have hsmall : ∑ u : Fin m, graphProb m p (fun E ↦ (reach (edgeGraph E) {u}).card < K) =
      m - graphExpect m p (fun E ↦ largeCount E K) := by
    rw [graphExpect_largeCount, sum_congr rfl fun u _ ↦ hcompl u, sum_sub_distrib, sum_const,
      card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  rw [hsq]
  calc ∑ u, ∑ w, graphProb m p (fun E ↦ K ≤ (reach (edgeGraph E) {u}).card ∧
          K ≤ (reach (edgeGraph E) {w}).card)
      ≤ ∑ u : Fin m, (graphExpect m p (fun E ↦ largeCount E K) -
          (1 - q) * (m * graphProb m p (fun E ↦ (reach (edgeGraph E) {u}).card < K) - K)) :=
        sum_le_sum fun u _ ↦ sum_graphProb_large_pair_le hp0 hp1 hq0 hq1 hq u
    _ = m * graphExpect m p (fun E ↦ largeCount E K) -
          (1 - q) * (m * ∑ u : Fin m, graphProb m p
            (fun E ↦ (reach (edgeGraph E) {u}).card < K) - m * K) := by
        simp only [sum_sub_distrib, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul,
          ← mul_sum]
        ring
    _ = m * graphExpect m p (fun E ↦ largeCount E K) -
          (1 - q) * (m * (m - graphExpect m p (fun E ↦ largeCount E K)) - m * K) := by
        rw [hsmall]

end

end Descent.Pangenome.AncestralLocality
