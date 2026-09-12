/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Pangenome.AncestralLocality.BreadthFirstDomination
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

assert_below Descent.PopGen Descent.Spectral Descent.Blindness Descent.Conditionals
assert_below Descent.Portability Descent.Decision Descent.Program

/-!
# Sprinkling: the large components of `G(m, α/m)` merge

`Descent.Pangenome.AncestralLocality.SupercriticalReach` carries the Erdős–Rényi giant component
theorem for `α > 1` as the hypothesis `GiantComponentLaw α`. Its lower half has two parts: many
features lie in large components (the exploration lower bound), and the large components are one.
This file proves the second part by sprinkling.

## The sprinkle

`subsetExpect_union`: when `1 - p = (1 - p₁)(1 - p₂)`, a random subset at rate `p` is the union of
independent random subsets at rates `p₁` and `p₂`. The proof is by induction on the ground set
through `BreadthFirstDomination.subsetExpect_insert`. For graphs (`graphExpect_union`), `G(m, α/m)`
is `G(m, (α - δ)/m)` together with an independent sprinkle at rate `p₂ = δ/(m - α + δ) ≥ δ/m`.

## Two large components are joined

For disjoint feature sets `A` and `B` the sprinkle contains no pair between them with probability
`(1 - p)^{|A| |B|}` (`graphProb_disjoint_pairsBetween`). `largeVertices E κ` collects the features
in components of more than `κ` features, and two distinct components are disjoint
(`disjoint_reach_singleton`). A pair between two components joins them in the union graph
(`reachable_union_of_not_disjoint`). So the sprinkle fails to join all large components with
probability at most `m² e^{-p κ²}`, by a union bound over pairs of large features
(`graphProb_not_joined_le`). On the complement one component holds every large feature, so under
`G(m, p)` no component has `c` features with probability at most the probability under `G(m, p₁)`
that fewer than `c` features are large, plus `m² e^{-p₂ κ²}` (`graphProb_card_reach_lt_le`).

## The limit

With `κ = m^{2/3}` and `p₂ ≥ δ/m` the sprinkling term is at most `m² e^{-δ m^{1/3}} → 0`
(`tendsto_sq_mul_exp_neg_rpow`). So if `G(m, (α - δ)/m)` has at least `c m` features in components
larger than `m^{2/3}` with probability tending to one, then `G(m, α/m)` has a component of at least
`c m` features with probability tending to one (`tendsto_graphProb_exists_card_reach_ge`).

Scope. The hypothesis is the exploration lower bound, which is not proved here. The conclusion is
the existence of one component of at least `c m` features; with `c = s - ε` it is the lower half of
the size condition in `GiantEvent`. The upper half, the smallness of the other components, and the
assembly into `GiantComponentLaw α` are not done here.

## Empirical status

None. The bodies are finite sums over random edge sets, counts of components, and limits in `m`.
The graph law is supplied, and nothing is measured.
-/

set_option autoImplicit false

namespace Descent.Pangenome.AncestralLocality

open Finset Filter Topology
open scoped Classical

noncomputable section

/-! ### The sprinkle -/

/-- A constant factor comes out of the expectation over a random subset. -/
theorem subsetExpect_const_mul {α : Type*} (T : Finset α) (p c : ℝ) (f : Finset α → ℝ) :
    subsetExpect T p (fun E ↦ c * f E) = c * subsetExpect T p f := by
  simp only [subsetExpect, mul_sum]
  exact sum_congr rfl fun E _ ↦ by ring

/-- **Two independent random subsets make one.** If `1 - p = (1 - p₁)(1 - p₂)`, the union of
independent random subsets of `T` at rates `p₁` and `p₂` is a random subset of `T` at rate `p`. -/
theorem subsetExpect_union {α : Type*} [DecidableEq α] (T : Finset α) {p p₁ p₂ : ℝ}
    (hp : 1 - p = (1 - p₁) * (1 - p₂)) (f : Finset α → ℝ) :
    subsetExpect T p f
      = subsetExpect T p₁ fun E₁ ↦ subsetExpect T p₂ fun E₂ ↦ f (E₁ ∪ E₂) := by
  induction T using Finset.induction_on generalizing f with
  | empty => simp [subsetExpect]
  | @insert a T ha ih =>
    conv_lhs => rw [subsetExpect_insert ha]
    rw [ih, ih]
    simp only [subsetExpect_insert ha, union_insert, insert_union, insert_idem, subsetExpect_add,
      subsetExpect_const_mul]
    linear_combination ((subsetExpect T p₁ fun E₁ ↦ subsetExpect T p₂ fun E₂ ↦ f (E₁ ∪ E₂))
      - subsetExpect T p₁ fun E₁ ↦ subsetExpect T p₂ fun E₂ ↦ f (insert a (E₁ ∪ E₂))) * hp

/-- **`G(m, p)` is `G(m, p₁)` with an independent sprinkle at rate `p₂`**, when
`1 - p = (1 - p₁)(1 - p₂)`. -/
theorem graphExpect_union {m : ℕ} {p p₁ p₂ : ℝ} (hp : 1 - p = (1 - p₁) * (1 - p₂))
    (f : Finset (Sym2 (Fin m)) → ℝ) :
    graphExpect m p f = graphExpect m p₁ fun E₁ ↦ graphExpect m p₂ fun E₂ ↦ f (E₁ ∪ E₂) := by
  simp only [graphExpect_eq_subsetExpect]
  exact subsetExpect_union _ hp f

/-! ### No sprinkled pair between two sets -/

/-- The unordered pairs with one feature in `A` and the other in `B`. -/
def pairsBetween {m : ℕ} (A B : Finset (Fin m)) : Finset (Sym2 (Fin m)) :=
  (A ×ˢ B).image fun x ↦ s(x.1, x.2)

/-- Between disjoint sets there are `|A| |B|` pairs. -/
theorem card_pairsBetween {m : ℕ} {A B : Finset (Fin m)} (hAB : Disjoint A B) :
    (pairsBetween A B).card = A.card * B.card := by
  have hinj : Set.InjOn (fun x : Fin m × Fin m ↦ s(x.1, x.2)) (A ×ˢ B : Finset _) := by
    intro x hx y hy hxy
    simp only [mem_coe, mem_product] at hx hy
    rcases Sym2.eq_iff.mp hxy with ⟨h1, h2⟩ | ⟨h1, -⟩
    · exact Prod.ext h1 h2
    · exact (disjoint_left.mp hAB hx.1) (h1 ▸ hy.2)
  rw [pairsBetween, card_image_of_injOn hinj, card_product]

/-- Pairs between disjoint sets are potential edges. -/
theorem pairsBetween_subset_potentialEdges {m : ℕ} {A B : Finset (Fin m)} (hAB : Disjoint A B) :
    pairsBetween A B ⊆ potentialEdges m := by
  intro e he
  obtain ⟨⟨a, b⟩, hab, rfl⟩ := mem_image.mp he
  obtain ⟨ha, hb⟩ := mem_product.mp hab
  simp only [mem_potentialEdges_iff, Sym2.mk_isDiag_iff]
  exact fun h ↦ disjoint_left.mp hAB ha (h ▸ hb)

/-- **No pair between two disjoint sets**, with probability `(1 - p)^{|A| |B|}` under `G(m, p)`. -/
theorem graphProb_disjoint_pairsBetween {m : ℕ} (p : ℝ) {A B : Finset (Fin m)}
    (hAB : Disjoint A B) :
    graphProb m p (fun E ↦ Disjoint (pairsBetween A B) E) = (1 - p) ^ (A.card * B.card) := by
  have hS := pairsBetween_subset_potentialEdges hAB
  have hlocal : ∀ E₁ ⊆ pairsBetween A B, ∀ E₂ ⊆ potentialEdges m \ pairsBetween A B,
      (if Disjoint (pairsBetween A B) (E₁ ∪ E₂) then (1 : ℝ) else 0)
        = if E₁ = ∅ then 1 else 0 := by
    intro E₁ hE₁ E₂ hE₂
    have hE₂S : Disjoint (pairsBetween A B) E₂ := disjoint_sdiff.mono_right hE₂
    have hiff : Disjoint (pairsBetween A B) (E₁ ∪ E₂) ↔ E₁ = ∅ := by
      rw [disjoint_union_right]
      constructor
      · rintro ⟨h1, -⟩
        exact eq_empty_of_forall_notMem fun e he ↦ disjoint_left.mp h1 (hE₁ he) he
      · rintro rfl
        exact ⟨disjoint_empty_right _, hE₂S⟩
    by_cases h : E₁ = ∅
    · rw [if_pos (hiff.mpr h), if_pos h]
    · rw [if_neg fun h' ↦ h (hiff.mp h'), if_neg h]
  have hzero : ∀ E ∈ (pairsBetween A B).powerset, E ≠ ∅ →
      p ^ E.card * (1 - p) ^ ((pairsBetween A B).card - E.card)
        * (if E = ∅ then (1 : ℝ) else 0) = 0 := fun E _ hE ↦ by rw [if_neg hE, mul_zero]
  calc graphProb m p (fun E ↦ Disjoint (pairsBetween A B) E)
      = subsetExpect (pairsBetween A B) p (fun E ↦ if E = ∅ then 1 else 0) := by
        rw [graphProb, graphExpect_eq_subsetExpect]
        exact subsetExpect_eq_of_local p hS hlocal
    _ = (1 - p) ^ (A.card * B.card) := by
        rw [subsetExpect, sum_eq_single_of_mem _ (empty_mem_powerset _) hzero, if_pos rfl,
          card_empty, pow_zero, one_mul, mul_one, Nat.sub_zero, card_pairsBetween hAB]

/-! ### The large components merge -/

/-- **The features in components of more than `κ` features.** -/
def largeVertices {m : ℕ} (E : Finset (Sym2 (Fin m))) (κ : ℝ) : Finset (Fin m) :=
  univ.filter fun v ↦ κ < ((reach (edgeGraph E) {v}).card : ℝ)

/-- Two distinct components are disjoint. -/
theorem disjoint_reach_singleton {m : ℕ} {G : SimpleGraph (Fin m)} {u w : Fin m}
    (h : reach G {u} ≠ reach G {w}) : Disjoint (reach G {u}) (reach G {w}) := by
  rw [disjoint_left]
  intro x hxu hxw
  exact h ((reach_singleton_eq_of_mem hxu).symm.trans (reach_singleton_eq_of_mem hxw))

/-- The graph of an edge set is a subgraph of the graph of a larger one. -/
theorem edgeGraph_le_union {m : ℕ} (E₁ E₂ : Finset (Sym2 (Fin m))) :
    edgeGraph E₁ ≤ edgeGraph (E₁ ∪ E₂) :=
  SimpleGraph.fromEdgeSet_mono fun e he ↦ mem_coe.mpr (mem_union_left _ (mem_coe.mp he))

/-- **A sprinkled pair joins two components**: if `E₂` has a pair between the components of `u`
and `w` in `E₁`, then `u` reaches `w` in the union graph. -/
theorem reachable_union_of_not_disjoint {m : ℕ} {E₁ E₂ : Finset (Sym2 (Fin m))} {u w : Fin m}
    (hne : reach (edgeGraph E₁) {u} ≠ reach (edgeGraph E₁) {w})
    (hjoin : ¬Disjoint (pairsBetween (reach (edgeGraph E₁) {u}) (reach (edgeGraph E₁) {w})) E₂) :
    (edgeGraph (E₁ ∪ E₂)).Reachable u w := by
  have hle := edgeGraph_le_union E₁ E₂
  obtain ⟨e, he₁, he₂⟩ := not_disjoint_iff.mp hjoin
  obtain ⟨⟨a, b⟩, hab, rfl⟩ := mem_image.mp he₁
  obtain ⟨ha, hb⟩ := mem_product.mp hab
  have hua : (edgeGraph E₁).Reachable u a := by simpa [mem_reach_iff] using ha
  have hwb : (edgeGraph E₁).Reachable w b := by simpa [mem_reach_iff] using hb
  have hab' : a ≠ b := fun h ↦ disjoint_left.mp (disjoint_reach_singleton hne) ha (h ▸ hb)
  have hadj : (edgeGraph (E₁ ∪ E₂)).Adj a b :=
    (edgeGraph_adj_iff _ a b).mpr ⟨mem_union_right _ he₂, hab'⟩
  exact ((hua.mono hle).trans hadj.reachable).trans (hwb.mono hle).symm

/-- **The sprinkle joins all large components**, except with probability at most
`m² e^{-p κ²}`: two distinct large components miss the sprinkle with probability
`(1 - p)^{|C| |C'|} ≤ e^{-p κ²}`, and there are at most `m²` pairs of large features. -/
theorem graphProb_not_joined_le {m : ℕ} {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (E₁ : Finset (Sym2 (Fin m))) {κ : ℝ} (hκ : 0 ≤ κ) :
    graphProb m p (fun E₂ ↦ ¬∀ u ∈ largeVertices E₁ κ, ∀ w ∈ largeVertices E₁ κ,
        (edgeGraph (E₁ ∪ E₂)).Reachable u w)
      ≤ (m : ℝ) ^ 2 * Real.exp (-(p * κ ^ 2)) := by
  -- a failure is a pair of distinct large components with no sprinkled pair between them
  have hpoint : ∀ E₂ : Finset (Sym2 (Fin m)),
      (if ¬∀ u ∈ largeVertices E₁ κ, ∀ w ∈ largeVertices E₁ κ,
          (edgeGraph (E₁ ∪ E₂)).Reachable u w then (1 : ℝ) else 0)
        ≤ ∑ u ∈ largeVertices E₁ κ, ∑ w ∈ largeVertices E₁ κ,
          (if reach (edgeGraph E₁) {u} ≠ reach (edgeGraph E₁) {w} ∧
              Disjoint (pairsBetween (reach (edgeGraph E₁) {u}) (reach (edgeGraph E₁) {w})) E₂
            then 1 else 0) := by
    intro E₂
    have hnn : ∀ u w : Fin m, (0 : ℝ) ≤
        (if reach (edgeGraph E₁) {u} ≠ reach (edgeGraph E₁) {w} ∧
            Disjoint (pairsBetween (reach (edgeGraph E₁) {u}) (reach (edgeGraph E₁) {w})) E₂
          then 1 else 0) := fun u w ↦ by split_ifs <;> norm_num
    by_cases hJ : ∀ u ∈ largeVertices E₁ κ, ∀ w ∈ largeVertices E₁ κ,
        (edgeGraph (E₁ ∪ E₂)).Reachable u w
    · rw [if_neg (not_not.mpr hJ)]
      exact sum_nonneg fun u _ ↦ sum_nonneg fun w _ ↦ hnn u w
    · rw [if_pos hJ]
      push_neg at hJ
      obtain ⟨u, hu, w, hw, huw⟩ := hJ
      have hne : reach (edgeGraph E₁) {u} ≠ reach (edgeGraph E₁) {w} := by
        intro heq
        have hwmem : w ∈ reach (edgeGraph E₁) {u} := by
          rw [heq]
          exact subset_reach _ _ (mem_singleton_self w)
        have hreach : (edgeGraph E₁).Reachable u w := by simpa [mem_reach_iff] using hwmem
        exact huw (hreach.mono (edgeGraph_le_union E₁ E₂))
      have hdisj : Disjoint (pairsBetween (reach (edgeGraph E₁) {u})
          (reach (edgeGraph E₁) {w})) E₂ := by
        by_contra hjoin
        exact huw (reachable_union_of_not_disjoint hne hjoin)
      calc (1 : ℝ)
          = if reach (edgeGraph E₁) {u} ≠ reach (edgeGraph E₁) {w} ∧
              Disjoint (pairsBetween (reach (edgeGraph E₁) {u}) (reach (edgeGraph E₁) {w})) E₂
            then 1 else 0 := (if_pos ⟨hne, hdisj⟩).symm
        _ ≤ ∑ w' ∈ largeVertices E₁ κ,
            (if reach (edgeGraph E₁) {u} ≠ reach (edgeGraph E₁) {w'} ∧
              Disjoint (pairsBetween (reach (edgeGraph E₁) {u}) (reach (edgeGraph E₁) {w'})) E₂
            then 1 else 0) := single_le_sum (fun w' _ ↦ hnn u w') hw
        _ ≤ _ := single_le_sum (fun u' _ ↦ sum_nonneg fun w' _ ↦ hnn u' w') hu
  -- one pair of large features
  have hterm : ∀ u ∈ largeVertices E₁ κ, ∀ w ∈ largeVertices E₁ κ,
      graphExpect m p (fun E₂ ↦ if reach (edgeGraph E₁) {u} ≠ reach (edgeGraph E₁) {w} ∧
          Disjoint (pairsBetween (reach (edgeGraph E₁) {u}) (reach (edgeGraph E₁) {w})) E₂
        then (1 : ℝ) else 0)
        ≤ Real.exp (-(p * κ ^ 2)) := by
    intro u hu w hw
    by_cases hne : reach (edgeGraph E₁) {u} = reach (edgeGraph E₁) {w}
    · calc _ ≤ graphExpect m p (fun _ ↦ (0 : ℝ)) :=
            graphExpect_mono hp0 hp1 fun E₂ ↦ by simp [hne]
        _ = 0 := graphExpect_const p 0
        _ ≤ Real.exp (-(p * κ ^ 2)) := (Real.exp_pos _).le
    · have hcu : κ < ((reach (edgeGraph E₁) {u}).card : ℝ) := (mem_filter.mp hu).2
      have hcw : κ < ((reach (edgeGraph E₁) {w}).card : ℝ) := (mem_filter.mp hw).2
      have hsq : κ ^ 2
          ≤ (((reach (edgeGraph E₁) {u}).card * (reach (edgeGraph E₁) {w}).card : ℕ) : ℝ) := by
        push_cast
        nlinarith [mul_le_mul hcu.le hcw.le hκ (hκ.trans hcu.le)]
      have hbound : (1 - p) ^ ((reach (edgeGraph E₁) {u}).card * (reach (edgeGraph E₁) {w}).card)
          ≤ Real.exp (-(p * κ ^ 2)) := by
        calc (1 - p) ^ ((reach (edgeGraph E₁) {u}).card * (reach (edgeGraph E₁) {w}).card)
            ≤ Real.exp (-p)
                ^ ((reach (edgeGraph E₁) {u}).card * (reach (edgeGraph E₁) {w}).card) :=
              pow_le_pow_left₀ (sub_nonneg.mpr hp1) (by linarith [Real.add_one_le_exp (-p)]) _
          _ = Real.exp ((((reach (edgeGraph E₁) {u}).card
                * (reach (edgeGraph E₁) {w}).card : ℕ) : ℝ) * -p) :=
              (Real.exp_nat_mul _ _).symm
          _ ≤ Real.exp (-(p * κ ^ 2)) :=
              Real.exp_le_exp.mpr (by nlinarith [mul_le_mul_of_nonneg_left hsq hp0])
      calc _ ≤ graphProb m p (fun E₂ ↦ Disjoint (pairsBetween (reach (edgeGraph E₁) {u})
              (reach (edgeGraph E₁) {w})) E₂) :=
            graphExpect_mono hp0 hp1 fun E₂ ↦ by
              split_ifs with h₁ h₂ <;> first | norm_num | exact absurd h₁.2 h₂
        _ = (1 - p) ^ ((reach (edgeGraph E₁) {u}).card * (reach (edgeGraph E₁) {w}).card) :=
            graphProb_disjoint_pairsBetween p (disjoint_reach_singleton hne)
        _ ≤ Real.exp (-(p * κ ^ 2)) := hbound
  calc graphProb m p (fun E₂ ↦ ¬∀ u ∈ largeVertices E₁ κ, ∀ w ∈ largeVertices E₁ κ,
        (edgeGraph (E₁ ∪ E₂)).Reachable u w)
      ≤ graphExpect m p (fun E₂ ↦ ∑ u ∈ largeVertices E₁ κ, ∑ w ∈ largeVertices E₁ κ,
          (if reach (edgeGraph E₁) {u} ≠ reach (edgeGraph E₁) {w} ∧
              Disjoint (pairsBetween (reach (edgeGraph E₁) {u}) (reach (edgeGraph E₁) {w})) E₂
            then (1 : ℝ) else 0)) := graphExpect_mono hp0 hp1 hpoint
    _ = ∑ u ∈ largeVertices E₁ κ, ∑ w ∈ largeVertices E₁ κ,
          graphExpect m p (fun E₂ ↦ if reach (edgeGraph E₁) {u} ≠ reach (edgeGraph E₁) {w} ∧
              Disjoint (pairsBetween (reach (edgeGraph E₁) {u}) (reach (edgeGraph E₁) {w})) E₂
            then (1 : ℝ) else 0) := by
        rw [graphExpect_sum]
        exact sum_congr rfl fun u _ ↦ graphExpect_sum _ _ _
    _ ≤ ∑ _u ∈ largeVertices E₁ κ, ∑ _w ∈ largeVertices E₁ κ, Real.exp (-(p * κ ^ 2)) :=
        sum_le_sum fun u hu ↦ sum_le_sum fun w hw ↦ hterm u hu w hw
    _ = ((largeVertices E₁ κ).card : ℝ) ^ 2 * Real.exp (-(p * κ ^ 2)) := by
        rw [sum_const, sum_const, nsmul_eq_mul, nsmul_eq_mul]
        ring
    _ ≤ (m : ℝ) ^ 2 * Real.exp (-(p * κ ^ 2)) := by
        have hL : ((largeVertices E₁ κ).card : ℝ) ≤ m := by
          exact_mod_cast (card_le_univ _).trans_eq (Fintype.card_fin m)
        exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (Nat.cast_nonneg _) hL 2)
          (Real.exp_pos _).le

/-- **The sprinkling bound.** When `1 - p = (1 - p₁)(1 - p₂)`, the probability under `G(m, p)` that
no component has `c` features is at most the probability under `G(m, p₁)` that fewer than `c`
features lie in components larger than `κ`, plus `m² e^{-p₂ κ²}`. -/
theorem graphProb_card_reach_lt_le {m : ℕ} (hm : 0 < m) {p p₁ p₂ : ℝ}
    (hp : 1 - p = (1 - p₁) * (1 - p₂)) (hp₁0 : 0 ≤ p₁) (hp₁1 : p₁ ≤ 1) (hp₂0 : 0 ≤ p₂)
    (hp₂1 : p₂ ≤ 1) {κ c : ℝ} (hκ : 0 ≤ κ) :
    graphProb m p (fun E ↦ ¬∃ v, c ≤ ((reach (edgeGraph E) {v}).card : ℝ))
      ≤ graphProb m p₁ (fun E₁ ↦ ¬c ≤ ((largeVertices E₁ κ).card : ℝ))
        + (m : ℝ) ^ 2 * Real.exp (-(p₂ * κ ^ 2)) := by
  have hexp0 : 0 ≤ (m : ℝ) ^ 2 * Real.exp (-(p₂ * κ ^ 2)) := by positivity
  -- given the first round, the sprinkle fails only by not joining the large components
  have hinner : ∀ E₁ : Finset (Sym2 (Fin m)),
      graphExpect m p₂ (fun E₂ ↦
          if ¬∃ v, c ≤ ((reach (edgeGraph (E₁ ∪ E₂)) {v}).card : ℝ) then (1 : ℝ) else 0)
        ≤ (if ¬c ≤ ((largeVertices E₁ κ).card : ℝ) then 1 else 0)
          + (m : ℝ) ^ 2 * Real.exp (-(p₂ * κ ^ 2)) := by
    intro E₁
    by_cases hgood : c ≤ ((largeVertices E₁ κ).card : ℝ)
    · rw [if_neg (not_not.mpr hgood), zero_add]
      refine le_trans (graphExpect_mono hp₂0 hp₂1 fun E₂ ↦ ?_)
        (graphProb_not_joined_le hp₂0 hp₂1 E₁ hκ)
      by_cases hJ : ∀ u ∈ largeVertices E₁ κ, ∀ w ∈ largeVertices E₁ κ,
          (edgeGraph (E₁ ∪ E₂)).Reachable u w
      · have hQ : ∃ v, c ≤ ((reach (edgeGraph (E₁ ∪ E₂)) {v}).card : ℝ) := by
          by_cases hne : (largeVertices E₁ κ).Nonempty
          · obtain ⟨v, hv⟩ := hne
            refine ⟨v, hgood.trans (Nat.cast_le.mpr (card_le_card fun u hu ↦ ?_))⟩
            exact (mem_reach_iff _ _ _).mpr ⟨v, mem_singleton_self v, hJ v hv u hu⟩
          · rw [not_nonempty_iff_eq_empty] at hne
            rw [hne, card_empty, Nat.cast_zero] at hgood
            exact ⟨⟨0, hm⟩, hgood.trans (Nat.cast_nonneg _)⟩
        rw [if_neg (not_not.mpr hQ)]
        split_ifs <;> norm_num
      · rw [if_pos hJ]
        split_ifs <;> norm_num
    · rw [if_pos hgood]
      exact (graphProb_le_one hp₂0 hp₂1
        (fun E₂ ↦ ¬∃ v, c ≤ ((reach (edgeGraph (E₁ ∪ E₂)) {v}).card : ℝ))).trans
        (le_add_of_nonneg_right hexp0)
  have hconst : graphExpect m p₁ (fun _ ↦ (m : ℝ) ^ 2 * Real.exp (-(p₂ * κ ^ 2)))
      = (m : ℝ) ^ 2 * Real.exp (-(p₂ * κ ^ 2)) := graphExpect_const p₁ _
  show graphExpect m p
      (fun E ↦ if ¬∃ v, c ≤ ((reach (edgeGraph E) {v}).card : ℝ) then (1 : ℝ) else 0) ≤ _
  rw [graphExpect_union hp]
  calc graphExpect m p₁ (fun E₁ ↦ graphExpect m p₂ fun E₂ ↦
        if ¬∃ v, c ≤ ((reach (edgeGraph (E₁ ∪ E₂)) {v}).card : ℝ) then (1 : ℝ) else 0)
      ≤ graphExpect m p₁ (fun E₁ ↦ (if ¬c ≤ ((largeVertices E₁ κ).card : ℝ) then (1 : ℝ) else 0)
          + (m : ℝ) ^ 2 * Real.exp (-(p₂ * κ ^ 2))) := graphExpect_mono hp₁0 hp₁1 hinner
    _ = graphProb m p₁ (fun E₁ ↦ ¬c ≤ ((largeVertices E₁ κ).card : ℝ))
          + (m : ℝ) ^ 2 * Real.exp (-(p₂ * κ ^ 2)) := by
        rw [graphExpect_add, hconst]
        rfl

/-! ### The limit -/

/-- `m² e^{-δ m^{1/3}} → 0`. -/
theorem tendsto_sq_mul_exp_neg_rpow {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun m : ℕ ↦ (m : ℝ) ^ 2 * Real.exp (-(δ * (m : ℝ) ^ ((1 : ℝ) / 3)))) atTop
      (𝓝 0) := by
  have hx : Tendsto (fun m : ℕ ↦ δ * (m : ℝ) ^ ((1 : ℝ) / 3)) atTop atTop :=
    ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 3)).comp
      tendsto_natCast_atTop_atTop).const_mul_atTop hδ
  have h := ((Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 6).comp hx).const_mul (δ ^ 6)⁻¹
  rw [mul_zero] at h
  refine h.congr fun m ↦ ?_
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hpow : ((m : ℝ) ^ ((1 : ℝ) / 3)) ^ 6 = (m : ℝ) ^ 2 := by
    rw [← Real.rpow_natCast ((m : ℝ) ^ ((1 : ℝ) / 3)) 6, ← Real.rpow_mul hm,
      show (1 : ℝ) / 3 * ((6 : ℕ) : ℝ) = 2 by norm_num, Real.rpow_two]
  have hδ6 : δ ^ 6 ≠ 0 := pow_ne_zero _ hδ.ne'
  simp only [Function.comp_apply]
  rw [mul_pow, hpow, ← mul_assoc, ← mul_assoc, inv_mul_cancel₀ hδ6, one_mul]

/-- **The large components of `G(m, (α - δ)/m)` merge under sprinkling.** If `G(m, (α - δ)/m)`
has at least `c m` features in components larger than `m^{2/3}` with probability tending to one,
then `G(m, α/m)` has a component of at least `c m` features with probability tending to one. -/
theorem tendsto_graphProb_exists_card_reach_ge {α δ c : ℝ} (hδ : 0 < δ) (hδα : δ ≤ α)
    (hlarge : Tendsto (fun m : ℕ ↦ graphProb m ((α - δ) / m) fun E ↦
      c * m ≤ ((largeVertices E ((m : ℝ) ^ ((2 : ℝ) / 3))).card : ℝ)) atTop (𝓝 1)) :
    Tendsto (fun m : ℕ ↦ graphProb m (α / m) fun E ↦
      ∃ v, c * m ≤ ((reach (edgeGraph E) {v}).card : ℝ)) atTop (𝓝 1) := by
  have hbad₁ : Tendsto (fun m : ℕ ↦ graphProb m ((α - δ) / m) fun E ↦
      ¬c * m ≤ ((largeVertices E ((m : ℝ) ^ ((2 : ℝ) / 3))).card : ℝ)) atTop (𝓝 0) := by
    have h := hlarge.const_sub 1
    rw [sub_self] at h
    refine h.congr fun m ↦ ?_
    linarith [graphProb_add_not m ((α - δ) / m) fun E ↦
      c * m ≤ ((largeVertices E ((m : ℝ) ^ ((2 : ℝ) / 3))).card : ℝ)]
  have hsum := hbad₁.add (tendsto_sq_mul_exp_neg_rpow hδ)
  rw [add_zero] at hsum
  have hbad : Tendsto (fun m : ℕ ↦ graphProb m (α / m) fun E ↦
      ¬∃ v, c * m ≤ ((reach (edgeGraph E) {v}).card : ℝ)) atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsum ?_ ?_
    · filter_upwards [eventually_gt_atTop ⌈α⌉₊] with m hm
      have hmα : α < m := (Nat.le_ceil α).trans_lt (by exact_mod_cast hm)
      have hmpos : (0 : ℝ) < m := by linarith
      exact graphProb_nonneg (div_nonneg (by linarith) hmpos.le)
        ((div_le_one hmpos).mpr hmα.le) _
    · filter_upwards [eventually_gt_atTop ⌈α⌉₊] with m hm
      have hmα : α < m := (Nat.le_ceil α).trans_lt (by exact_mod_cast hm)
      have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
      have hmpos : (0 : ℝ) < m := by linarith
      have hmpos' : 0 < m := by exact_mod_cast hmpos
      have hden : 0 < (m : ℝ) - α + δ := by linarith
      have hm' : (m : ℝ) ≠ 0 := hmpos.ne'
      have hden' : (m : ℝ) - α + δ ≠ 0 := hden.ne'
      have hp : 1 - α / m = (1 - (α - δ) / m) * (1 - δ / (m - α + δ)) := by
        field_simp <;> ring
      have hp₁0 : 0 ≤ (α - δ) / m := div_nonneg (by linarith) hm0
      have hp₁1 : (α - δ) / m ≤ 1 := (div_le_one hmpos).mpr (by linarith)
      have hp₂0 : 0 ≤ δ / (m - α + δ) := div_nonneg hδ.le hden.le
      have hp₂1 : δ / (m - α + δ) ≤ 1 := (div_le_one hden).mpr (by linarith)
      have hκ : (0 : ℝ) ≤ (m : ℝ) ^ ((2 : ℝ) / 3) := Real.rpow_nonneg hm0 _
      have hκsq : ((m : ℝ) ^ ((2 : ℝ) / 3)) ^ 2 = m * (m : ℝ) ^ ((1 : ℝ) / 3) := by
        rw [← Real.rpow_natCast ((m : ℝ) ^ ((2 : ℝ) / 3)) 2, ← Real.rpow_mul hm0,
          show (2 : ℝ) / 3 * ((2 : ℕ) : ℝ) = 1 + 1 / 3 by norm_num, Real.rpow_add hmpos,
          Real.rpow_one]
      have hp₂m : δ ≤ δ / (m - α + δ) * m := by
        rw [div_mul_eq_mul_div, le_div_iff₀ hden]
        nlinarith [mul_le_mul_of_nonneg_left (show (m : ℝ) - α + δ ≤ m by linarith) hδ.le]
      have hexp : Real.exp (-(δ / (m - α + δ) * ((m : ℝ) ^ ((2 : ℝ) / 3)) ^ 2))
          ≤ Real.exp (-(δ * (m : ℝ) ^ ((1 : ℝ) / 3))) := by
        refine Real.exp_le_exp.mpr (neg_le_neg ?_)
        rw [hκsq, ← mul_assoc]
        exact mul_le_mul_of_nonneg_right hp₂m (Real.rpow_nonneg hm0 _)
      refine (graphProb_card_reach_lt_le hmpos' hp hp₁0 hp₁1 hp₂0 hp₂1 hκ).trans ?_
      exact add_le_add_left (mul_le_mul_of_nonneg_left hexp (by positivity)) _
  have h := hbad.const_sub 1
  rw [sub_zero] at h
  refine h.congr fun m ↦ ?_
  linarith [graphProb_add_not m (α / m) fun E ↦
    ∃ v, c * m ≤ ((reach (edgeGraph E) {v}).card : ℝ)]

end

end Descent.Pangenome.AncestralLocality
