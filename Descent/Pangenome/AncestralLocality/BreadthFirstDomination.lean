/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Pangenome.AncestralLocality.SupercriticalBranches

assert_below Descent.PopGen Descent.Spectral Descent.Blindness Descent.Conditionals
assert_below Descent.Portability Descent.Decision Descent.Program

/-!
# Breadth-first search in `G(m, p)` is dominated by a Galton–Watson process

This is the finite half of the supercritical upper bound in the note's (6.2). The reach of `k`
roots is large only if breadth-first search from them survives many generations or its first
generations are already large. Survival to generation `g` is at most as likely as survival of a
Galton–Watson process with `Binomial(m, p)` offspring started from `k` individuals.

**Random subsets.** `subsetExpect T p` is the expectation over a random subset of `T` that keeps
each element independently with probability `p`. `G(m, p)` is the case `T = potentialEdges m`
(`graphExpect_eq_subsetExpect`). Adding one element to the ground set splits off one coin
(`subsetExpect_insert`). Hence a random subset of `T` is a random subset of `S ⊆ T` together with
an independent random subset of `T \ S` (`subsetExpect_split`), and a quantity that sees only the
part inside `S` has the expectation of that part (`subsetExpect_eq_of_local`). The number of kept
elements has generating function `(p q + 1 - p)^|T|` (`subsetExpect_pow_card`) and mean `p |T|`
(`subsetExpect_card`).

**Breadth-first layers.** From a root set `R` inside the features `U`, the next layer is the set of
features of `U \ R` joined to `R` (`nextLayer`), and `layer E R U g` is the `g`-th layer
(`layer_succ`). One step reads only the edges between `R` and `U \ R` (`crossEdges`,
`nextLayer_congr`), and the later layers read only the edges inside `U \ R` (`layer_congr`).
Conditioning on the explored edges therefore separates the step from the rest
(`graphExpect_nextLayer`). A layer has at most as many features as explored edges
(`card_nextLayer_le`), and there are at most `m |R|` explored edges (`card_crossEdges_le`).

**The domination.** Let `q_g = gwExtinct m p g` be the probability that a Galton–Watson process with
`Binomial(m, p)` offspring is extinct by generation `g`: `q_0 = 0` and `q_{g+1}` is the offspring
generating function at `q_g`. Then `q_g^|R| ≤ P(layer g from R is empty)`
(`gwExtinct_pow_le_graphProb_layer_eq_empty`). The proof is by induction on `g`. Given the explored
edges `E₁`, the induction hypothesis bounds the rest by `q_g^|nextLayer E₁|`, which is at least
`q_g^|E₁|`; that has expectation `(1 - p (1 - q_g))^|crossEdges|`, at least `q_{g+1}^|R|`. The
layers have mean size at most `|R| (p m)^g` (`graphExpect_card_layer_le`). If layer `g` is empty,
the reach of `R` is the union of the first `g` layers (`reach_subset_biUnion_layer`, through
`mem_layers_of_adj`). So for every `g` and `K > 0`,
`P(|Reach(A)| ≥ K) ≤ 1 - q_g^|A| + |A| Σ_{t<g} (p m)^t / K` (`graphProb_card_reach_ge_le`).

Scope. The comparison is with survival of the Galton–Watson process generation by generation,
through its extinction probabilities `q_g`. No law of its total progeny is constructed, so the
total-progeny form `P(|Reach(i)| ≥ K) ≤ P(Z ≥ K)` is not stated; the survival-plus-Markov bound
above is what the limit in `m` uses, and that limit is taken in a sibling module.

## Empirical status

None. The bodies are finite sums over random subsets and counts of breadth-first layers. The graph
law is supplied, and nothing is measured.
-/

namespace Descent.Pangenome.AncestralLocality

open Finset
open scoped Classical

noncomputable section

/-! ### Random subsets -/

/-- **The expectation over a random subset of `T`**, each element kept independently with
probability `p`. -/
def subsetExpect {α : Type*} (T : Finset α) (p : ℝ) (f : Finset α → ℝ) : ℝ :=
  ∑ E ∈ T.powerset, p ^ E.card * (1 - p) ^ (T.card - E.card) * f E

/-- `G(m, p)` is the random subset of the potential edges. -/
theorem graphExpect_eq_subsetExpect {m : ℕ} (p : ℝ) (f : Finset (Sym2 (Fin m)) → ℝ) :
    graphExpect m p f = subsetExpect (potentialEdges m) p f := by
  simp only [graphExpect, subsetExpect, edgeWeight, card_potentialEdges]

/-- The expectation of a constant over a random subset is that constant. -/
theorem subsetExpect_const {α : Type*} (T : Finset α) (p c : ℝ) :
    subsetExpect T p (fun _ ↦ c) = c := by
  have h := sum_pow_mul_eq_add_pow p (1 - p) T
  rw [show p + (1 - p) = 1 by ring, one_pow] at h
  simp only [subsetExpect, ← sum_mul, h, one_mul]

/-- Expectation over a random subset is monotone when `p` is a probability. -/
theorem subsetExpect_mono {α : Type*} (T : Finset α) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    {f g : Finset α → ℝ} (h : ∀ E ⊆ T, f E ≤ g E) : subsetExpect T p f ≤ subsetExpect T p g :=
  sum_le_sum fun E hE ↦ mul_le_mul_of_nonneg_left (h E (mem_powerset.mp hE))
    (mul_nonneg (pow_nonneg hp0 _) (pow_nonneg (sub_nonneg.mpr hp1) _))

/-- Expectation over a random subset is additive. -/
theorem subsetExpect_add {α : Type*} (T : Finset α) (p : ℝ) (f g : Finset α → ℝ) :
    subsetExpect T p (fun E ↦ f E + g E) = subsetExpect T p f + subsetExpect T p g := by
  simp only [subsetExpect, mul_add, sum_add_distrib]

/-- Expectation over a random subset commutes with a constant factor. -/
theorem subsetExpect_mul_const {α : Type*} (T : Finset α) (p : ℝ) (f : Finset α → ℝ) (c : ℝ) :
    subsetExpect T p (fun E ↦ f E * c) = subsetExpect T p f * c := by
  simp only [subsetExpect, sum_mul, mul_assoc]

/-- **Adding one element to the ground set**: that element is kept with probability `p`. -/
theorem subsetExpect_insert {α : Type*} [DecidableEq α] {T : Finset α} {a : α} (ha : a ∉ T)
    (p : ℝ) (f : Finset α → ℝ) :
    subsetExpect (insert a T) p f =
      p * subsetExpect T p (fun E ↦ f (insert a E)) + (1 - p) * subsetExpect T p f := by
  have h1 : ∑ E ∈ T.powerset, p ^ (insert a E).card *
      (1 - p) ^ ((insert a T).card - (insert a E).card) * f (insert a E) =
        p * subsetExpect T p (fun E ↦ f (insert a E)) := by
    rw [subsetExpect, mul_sum]
    refine sum_congr rfl fun E hE ↦ ?_
    have hEa : a ∉ E := fun h ↦ ha (mem_powerset.mp hE h)
    have hle : E.card ≤ T.card := card_le_card (mem_powerset.mp hE)
    rw [card_insert_of_notMem hEa, card_insert_of_notMem ha,
      show T.card + 1 - (E.card + 1) = T.card - E.card by omega]
    ring
  have h2 : ∑ E ∈ T.powerset, p ^ E.card * (1 - p) ^ ((insert a T).card - E.card) * f E =
      (1 - p) * subsetExpect T p f := by
    rw [subsetExpect, mul_sum]
    refine sum_congr rfl fun E hE ↦ ?_
    have hle : E.card ≤ T.card := card_le_card (mem_powerset.mp hE)
    rw [card_insert_of_notMem ha, show T.card + 1 - E.card = T.card - E.card + 1 by omega]
    ring
  have hinj : Set.InjOn (insert a) (T.powerset : Set (Finset α)) := fun E₁ h₁ E₂ h₂ heq ↦ by
    have ha₁ : a ∉ E₁ := fun h ↦ ha (mem_powerset.mp h₁ h)
    have ha₂ : a ∉ E₂ := fun h ↦ ha (mem_powerset.mp h₂ h)
    rw [← erase_insert ha₁, ← erase_insert ha₂, heq]
  have hdisj : Disjoint T.powerset (T.powerset.image (insert a)) := by
    rw [disjoint_left]
    intro E hE hE'
    obtain ⟨E', -, rfl⟩ := mem_image.mp hE'
    exact ha (mem_powerset.mp hE (mem_insert_self a E'))
  conv_lhs => rw [subsetExpect, powerset_insert, sum_union hdisj, sum_image hinj]
  rw [h1, h2, add_comm]

/-- **Conditioning on part of the ground set.** For `S ⊆ T`, a random subset of `T` is a random
subset of `S` together with an independent random subset of `T \ S`. -/
theorem subsetExpect_split {α : Type*} [DecidableEq α] (p : ℝ) {S T : Finset α} (hST : S ⊆ T)
    (f : Finset α → ℝ) :
    subsetExpect T p f =
      subsetExpect S p (fun E₁ ↦ subsetExpect (T \ S) p (fun E₂ ↦ f (E₁ ∪ E₂))) := by
  induction S using Finset.induction_on generalizing T f with
  | empty => simp [subsetExpect]
  | @insert a S ha ih =>
    have haT : a ∈ T := hST (mem_insert_self a S)
    have hS : S ⊆ T.erase a := fun x hx ↦
      mem_erase.mpr ⟨fun h ↦ ha (h ▸ hx), hST (mem_insert_of_mem hx)⟩
    have hdiff : T \ insert a S = T.erase a \ S := by
      ext x
      simp only [mem_sdiff, mem_insert, mem_erase]
      tauto
    conv_lhs => rw [← insert_erase haT, subsetExpect_insert (notMem_erase a T)]
    rw [ih hS, ih hS, subsetExpect_insert ha, hdiff]
    simp only [insert_union]

/-- **A quantity of part of the random subset** has the expectation of that part. -/
theorem subsetExpect_eq_of_local {α : Type*} [DecidableEq α] (p : ℝ) {S T : Finset α}
    (hST : S ⊆ T) {f g : Finset α → ℝ} (h : ∀ E₁ ⊆ S, ∀ E₂ ⊆ T \ S, f (E₁ ∪ E₂) = g E₁) :
    subsetExpect T p f = subsetExpect S p g := by
  rw [subsetExpect_split p hST]
  refine sum_congr rfl fun E₁ hE₁ ↦ ?_
  have hconst : subsetExpect (T \ S) p (fun E₂ ↦ f (E₁ ∪ E₂)) = g E₁ := by
    rw [← subsetExpect_const (T \ S) p (g E₁)]
    exact sum_congr rfl fun E₂ hE₂ ↦ by
      simp only [h E₁ (mem_powerset.mp hE₁) E₂ (mem_powerset.mp hE₂)]
  simp only [hconst]

/-- **The generating function of the number of kept elements**: `E[q^|E|] = (p q + 1 - p)^|T|`. -/
theorem subsetExpect_pow_card {α : Type*} (T : Finset α) (p q : ℝ) :
    subsetExpect T p (fun E ↦ q ^ E.card) = (p * q + (1 - p)) ^ T.card := by
  simp only [subsetExpect]
  rw [← sum_pow_mul_eq_add_pow]
  exact sum_congr rfl fun E _ ↦ by ring

/-- **The mean number of kept elements**: `E|E| = p |T|`. -/
theorem subsetExpect_card {α : Type*} [DecidableEq α] (T : Finset α) (p : ℝ) :
    subsetExpect T p (fun E ↦ (E.card : ℝ)) = p * T.card := by
  induction T using Finset.induction_on with
  | empty => simp [subsetExpect]
  | @insert a T ha ih =>
    have h2 : subsetExpect T p (fun E ↦ ((insert a E).card : ℝ)) =
        subsetExpect T p (fun E ↦ (E.card : ℝ)) + 1 := by
      rw [← subsetExpect_const T p (1 : ℝ), ← subsetExpect_add]
      refine sum_congr rfl fun E hE ↦ ?_
      have haE : a ∉ E := fun h ↦ ha (mem_powerset.mp hE h)
      simp only [card_insert_of_notMem haE, Nat.cast_add, Nat.cast_one]
    rw [subsetExpect_insert ha, h2, ih, card_insert_of_notMem ha]
    push_cast
    ring

/-- A probability under `G(m, p)` is nonnegative. -/
theorem graphProb_nonneg {m : ℕ} {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (P : Finset (Sym2 (Fin m)) → Prop) [DecidablePred P] : 0 ≤ graphProb m p P := by
  rw [← graphExpect_const (m := m) p (0 : ℝ), graphProb]
  exact graphExpect_mono hp0 hp1 fun E ↦ by split_ifs <;> norm_num

/-! ### Breadth-first layers -/

/-- **The next breadth-first layer**: the features of `U \ R` joined in `E` to a feature of `R`. -/
def nextLayer {m : ℕ} (E : Finset (Sym2 (Fin m))) (R U : Finset (Fin m)) : Finset (Fin m) :=
  (U \ R).filter fun u ↦ ∃ r ∈ R, s(r, u) ∈ E

/-- Membership in the next layer. -/
theorem mem_nextLayer_iff {m : ℕ} (E : Finset (Sym2 (Fin m))) (R U : Finset (Fin m))
    (u : Fin m) : u ∈ nextLayer E R U ↔ u ∈ U \ R ∧ ∃ r ∈ R, s(r, u) ∈ E := by
  rw [nextLayer, mem_filter]

/-- The next layer lies among the unexplored features. -/
theorem nextLayer_subset {m : ℕ} (E : Finset (Sym2 (Fin m))) (R U : Finset (Fin m)) :
    nextLayer E R U ⊆ U \ R :=
  filter_subset _ _

/-- An empty layer has an empty successor. -/
theorem nextLayer_empty {m : ℕ} (E : Finset (Sym2 (Fin m))) (U : Finset (Fin m)) :
    nextLayer E ∅ U = ∅ := by
  ext u
  simp [nextLayer]

/-- One breadth-first step on the pair (current layer, unexplored features). -/
def layerStep {m : ℕ} (E : Finset (Sym2 (Fin m))) (x : Finset (Fin m) × Finset (Fin m)) :
    Finset (Fin m) × Finset (Fin m) :=
  (nextLayer E x.1 x.2, x.2 \ x.1)

/-- **The `g`-th breadth-first layer** from `R` inside `U`. -/
def layer {m : ℕ} (E : Finset (Sym2 (Fin m))) (R U : Finset (Fin m)) (g : ℕ) : Finset (Fin m) :=
  ((layerStep E)^[g] (R, U)).1

/-- The features not yet excluded after `g` breadth-first steps. -/
def unexplored {m : ℕ} (E : Finset (Sym2 (Fin m))) (R U : Finset (Fin m)) (g : ℕ) :
    Finset (Fin m) :=
  ((layerStep E)^[g] (R, U)).2

/-- The zeroth layer is the root set. -/
theorem layer_zero {m : ℕ} (E : Finset (Sym2 (Fin m))) (R U : Finset (Fin m)) :
    layer E R U 0 = R :=
  rfl

/-- **The first step, then `g` more**: layer `g + 1` from `R` in `U` is layer `g` from the next
layer in `U \ R`. -/
theorem layer_succ {m : ℕ} (E : Finset (Sym2 (Fin m))) (R U : Finset (Fin m)) (g : ℕ) :
    layer E R U (g + 1) = layer E (nextLayer E R U) (U \ R) g :=
  rfl

/-- **`g` steps, then one more**: layer `g + 1` is the next layer of layer `g`. -/
theorem layer_succ' {m : ℕ} (E : Finset (Sym2 (Fin m))) (R U : Finset (Fin m)) (g : ℕ) :
    layer E R U (g + 1) = nextLayer E (layer E R U g) (unexplored E R U g) := by
  simp only [layer, unexplored, Function.iterate_succ_apply', layerStep]

/-- Each step excludes the current layer. -/
theorem unexplored_succ {m : ℕ} (E : Finset (Sym2 (Fin m))) (R U : Finset (Fin m)) (g : ℕ) :
    unexplored E R U (g + 1) = unexplored E R U g \ layer E R U g := by
  simp only [layer, unexplored, Function.iterate_succ_apply', layerStep]

/-- A feature already excluded lies in an earlier layer. -/
theorem exists_lt_mem_layer_of_not_mem_unexplored {m : ℕ} (E : Finset (Sym2 (Fin m)))
    (R : Finset (Fin m)) {g : ℕ} {w : Fin m} (hw : w ∉ unexplored E R univ g) :
    ∃ t < g, w ∈ layer E R univ t := by
  induction g with
  | zero => exact absurd (mem_univ w) hw
  | succ g ih =>
    rw [unexplored_succ, mem_sdiff, not_and_or, not_not] at hw
    rcases hw with hw | hw
    · obtain ⟨t, ht, hwt⟩ := ih hw
      exact ⟨t, Nat.lt_succ_of_lt ht, hwt⟩
    · exact ⟨g, Nat.lt_succ_self g, hw⟩

/-- Once a layer is empty, every later layer is empty. -/
theorem layer_eq_empty_of_le {m : ℕ} (E : Finset (Sym2 (Fin m))) (R U : Finset (Fin m))
    {g t : ℕ} (hg : layer E R U g = ∅) (hgt : g ≤ t) : layer E R U t = ∅ := by
  induction t, hgt using Nat.le_induction with
  | base => exact hg
  | succ t _ ih => rw [layer_succ', ih, nextLayer_empty]

/-- **A neighbour of a layer lies in the next layer or in an earlier one.** -/
theorem mem_layers_of_adj {m : ℕ} (E : Finset (Sym2 (Fin m))) (R : Finset (Fin m)) {t : ℕ}
    {w w' : Fin m} (hw : w ∈ layer E R univ t) (hadj : (edgeGraph E).Adj w w') :
    w' ∈ layer E R univ (t + 1) ∨ ∃ s ≤ t, w' ∈ layer E R univ s := by
  by_cases hrest : w' ∈ unexplored E R univ t
  · by_cases hlay : w' ∈ layer E R univ t
    · exact Or.inr ⟨t, le_rfl, hlay⟩
    · left
      rw [layer_succ', mem_nextLayer_iff]
      exact ⟨mem_sdiff.mpr ⟨hrest, hlay⟩, w, hw, ((edgeGraph_adj_iff E w w').mp hadj).1⟩
  · obtain ⟨s, hs, hws⟩ := exists_lt_mem_layer_of_not_mem_unexplored E R hrest
    exact Or.inr ⟨s, hs.le, hws⟩

/-- **If breadth-first search from `R` is empty at step `g`, the reach of `R` is the union of the
first `g` layers.** -/
theorem reach_subset_biUnion_layer {m : ℕ} (E : Finset (Sym2 (Fin m))) (R : Finset (Fin m))
    {g : ℕ} (hg : layer E R univ g = ∅) :
    reach (edgeGraph E) R ⊆ (range g).biUnion fun t ↦ layer E R univ t := by
  have hclosed : ∀ w w', w ∈ (range g).biUnion (fun t ↦ layer E R univ t) →
      (edgeGraph E).Adj w w' → w' ∈ (range g).biUnion (fun t ↦ layer E R univ t) := by
    intro w w' hw hadj
    obtain ⟨t, ht, hwt⟩ := mem_biUnion.mp hw
    rw [mem_range] at ht
    rcases mem_layers_of_adj E R hwt hadj with h | ⟨s, hs, hws⟩
    · rcases Nat.lt_or_ge (t + 1) g with htg | htg
      · exact mem_biUnion.mpr ⟨t + 1, mem_range.mpr htg, h⟩
      · rw [layer_eq_empty_of_le E R univ hg htg] at h
        exact absurd h (by simp)
    · exact mem_biUnion.mpr ⟨s, mem_range.mpr (lt_of_le_of_lt hs ht), hws⟩
  intro w hw
  obtain ⟨a, ha, hreach⟩ := (mem_reach_iff _ _ w).mp hw
  clear hw
  have ha' : a ∈ (range g).biUnion (fun t ↦ layer E R univ t) := by
    rcases Nat.eq_zero_or_pos g with rfl | hg0
    · rw [layer_zero] at hg
      rw [hg] at ha
      exact absurd ha (by simp)
    · exact mem_biUnion.mpr ⟨0, mem_range.mpr hg0, ha⟩
  rw [SimpleGraph.reachable_iff_reflTransGen] at hreach
  induction hreach with
  | refl => exact ha'
  | tail _ hbc ih => exact hclosed _ _ ih hbc

/-- **The edges explored in one breadth-first step**: the pairs between `R` and `U \ R`. -/
def crossEdges {m : ℕ} (R U : Finset (Fin m)) : Finset (Sym2 (Fin m)) :=
  (R ×ˢ (U \ R)).image fun x ↦ s(x.1, x.2)

/-- A pair from `R` to `U \ R` is explored. -/
theorem mk_mem_crossEdges {m : ℕ} {R U : Finset (Fin m)} {r u : Fin m} (hr : r ∈ R)
    (hu : u ∈ U \ R) : s(r, u) ∈ crossEdges R U :=
  mem_image.mpr ⟨(r, u), mem_product.mpr ⟨hr, hu⟩, rfl⟩

/-- A pair with both features outside `R` is not explored. -/
theorem mk_not_mem_crossEdges {m : ℕ} {R U : Finset (Fin m)} {a b : Fin m} (ha : a ∉ R)
    (hb : b ∉ R) : s(a, b) ∉ crossEdges R U := by
  intro h
  obtain ⟨⟨r, u⟩, hru, heq⟩ := mem_image.mp h
  obtain ⟨hr, -⟩ := mem_product.mp hru
  rcases Sym2.eq_iff.mp heq with ⟨hra, -⟩ | ⟨hrb, -⟩
  · exact ha (hra ▸ hr)
  · exact hb (hrb ▸ hr)

/-- The explored pairs are potential edges. -/
theorem crossEdges_subset_potentialEdges {m : ℕ} (R U : Finset (Fin m)) :
    crossEdges R U ⊆ potentialEdges m := by
  intro e he
  obtain ⟨⟨r, u⟩, hru, rfl⟩ := mem_image.mp he
  obtain ⟨hr, hu⟩ := mem_product.mp hru
  simp only [mem_potentialEdges_iff, Sym2.mk_isDiag_iff]
  exact fun h ↦ (mem_sdiff.mp hu).2 (h ▸ hr)

/-- **There are at most `m |R|` explored pairs.** -/
theorem card_crossEdges_le {m : ℕ} (R U : Finset (Fin m)) :
    (crossEdges R U).card ≤ m * R.card := by
  have h1 : (crossEdges R U).card ≤ R.card * (U \ R).card :=
    card_image_le.trans (card_product _ _).le
  have h2 : (U \ R).card ≤ m := (card_le_univ _).trans_eq (Fintype.card_fin m)
  exact h1.trans (by rw [mul_comm]; exact Nat.mul_le_mul h2 le_rfl)

/-- **A layer has at most as many features as there are edges**: distinct features of the next layer
are reached through distinct edges. -/
theorem card_nextLayer_le {m : ℕ} (E : Finset (Sym2 (Fin m))) (R U : Finset (Fin m)) :
    (nextLayer E R U).card ≤ E.card := by
  let f : Fin m → Sym2 (Fin m) := fun u ↦
    if h : ∃ r ∈ R, s(r, u) ∈ E then s(h.choose, u) else s(u, u)
  refine card_le_card_of_injOn f (fun u hu ↦ ?_) (fun u hu u' hu' huu' ↦ ?_)
  · obtain ⟨-, h⟩ := (mem_nextLayer_iff E R U u).mp hu
    simp only [f, dif_pos h]
    exact h.choose_spec.2
  · obtain ⟨-, h⟩ := (mem_nextLayer_iff E R U u).mp hu
    obtain ⟨hu1', h'⟩ := (mem_nextLayer_iff E R U u').mp hu'
    simp only [f, dif_pos h, dif_pos h'] at huu'
    rcases Sym2.eq_iff.mp huu' with ⟨-, h2⟩ | ⟨h1, -⟩
    · exact h2
    · exact absurd (h1 ▸ h.choose_spec.1) (mem_sdiff.mp hu1').2

/-- One step reads only the explored pairs. -/
theorem nextLayer_congr {m : ℕ} {E E' : Finset (Sym2 (Fin m))} {R U : Finset (Fin m)}
    (h : ∀ r ∈ R, ∀ u ∈ U \ R, (s(r, u) ∈ E ↔ s(r, u) ∈ E')) :
    nextLayer E R U = nextLayer E' R U := by
  ext u
  rw [mem_nextLayer_iff, mem_nextLayer_iff]
  constructor
  · rintro ⟨hu, r, hr, hru⟩
    exact ⟨hu, r, hr, (h r hr u hu).mp hru⟩
  · rintro ⟨hu, r, hr, hru⟩
    exact ⟨hu, r, hr, (h r hr u hu).mpr hru⟩

/-- **The layers from `R` inside `U` read only the edges inside `U`.** -/
theorem layer_congr {m : ℕ} {E E' : Finset (Sym2 (Fin m))} (g : ℕ) :
    ∀ {R U : Finset (Fin m)}, R ⊆ U → (∀ a ∈ U, ∀ b ∈ U, (s(a, b) ∈ E ↔ s(a, b) ∈ E')) →
      layer E R U g = layer E' R U g := by
  induction g with
  | zero => intro R U _ _; rfl
  | succ g ih =>
    intro R U hRU h
    rw [layer_succ, layer_succ, nextLayer_congr fun r hr u hu ↦ h r (hRU hr) u (mem_sdiff.mp hu).1]
    exact ih (nextLayer_subset _ _ _) fun a ha b hb ↦ h a (mem_sdiff.mp ha).1 b (mem_sdiff.mp hb).1

/-- **One breadth-first step, conditioned on the explored edges.** For a quantity
`F S E` that sees `E` only through the edges inside `U \ R` whenever `S ⊆ U \ R`, the expectation
of `F (nextLayer E R U) E` averages, over the explored edges `E₁`, the expectation of `F S` at the
layer `S` that `E₁` produces. -/
theorem graphExpect_nextLayer {m : ℕ} (p : ℝ) {R U : Finset (Fin m)}
    (F : Finset (Fin m) → Finset (Sym2 (Fin m)) → ℝ)
    (hF : ∀ S ⊆ U \ R, ∀ E E',
      (∀ a ∈ U \ R, ∀ b ∈ U \ R, (s(a, b) ∈ E ↔ s(a, b) ∈ E')) → F S E = F S E') :
    graphExpect m p (fun E ↦ F (nextLayer E R U) E) =
      subsetExpect (crossEdges R U) p (fun E₁ ↦ graphExpect m p (F (nextLayer E₁ R U))) := by
  have hT := crossEdges_subset_potentialEdges R U
  rw [graphExpect_eq_subsetExpect, subsetExpect_split p hT]
  refine sum_congr rfl fun E₁ hE₁ ↦ ?_
  have hE₁T : E₁ ⊆ crossEdges R U := mem_powerset.mp hE₁
  have hS := nextLayer_subset E₁ R U
  have hlocal : graphExpect m p (F (nextLayer E₁ R U)) =
      subsetExpect (potentialEdges m \ crossEdges R U) p (F (nextLayer E₁ R U)) := by
    rw [graphExpect_eq_subsetExpect]
    refine subsetExpect_eq_of_local p sdiff_subset fun E₂ _ E₃ hE₃ ↦
      hF _ hS _ _ fun a ha b hb ↦ ?_
    have hE₃T : E₃ ⊆ crossEdges R U := fun e he ↦ by
      have h3 := hE₃ he
      rw [mem_sdiff, mem_sdiff] at h3
      tauto
    have hab := mk_not_mem_crossEdges (U := U) (mem_sdiff.mp ha).2 (mem_sdiff.mp hb).2
    rw [mem_union]
    exact ⟨fun h ↦ h.resolve_right fun h3 ↦ hab (hE₃T h3), Or.inl⟩
  have hinner : subsetExpect (potentialEdges m \ crossEdges R U) p
      (fun E₂ ↦ F (nextLayer (E₁ ∪ E₂) R U) (E₁ ∪ E₂)) =
        subsetExpect (potentialEdges m \ crossEdges R U) p (F (nextLayer E₁ R U)) := by
    refine sum_congr rfl fun E₂ hE₂ ↦ ?_
    have hE₂T : ∀ e ∈ E₂, e ∉ crossEdges R U := fun e he ↦
      (mem_sdiff.mp (mem_powerset.mp hE₂ he)).2
    have hnext : nextLayer (E₁ ∪ E₂) R U = nextLayer E₁ R U :=
      nextLayer_congr fun r hr u hu ↦ by
        rw [mem_union]
        exact ⟨fun h ↦ h.resolve_right fun h2 ↦ hE₂T _ h2 (mk_mem_crossEdges hr hu), Or.inl⟩
    have hF' : F (nextLayer E₁ R U) (E₁ ∪ E₂) = F (nextLayer E₁ R U) E₂ :=
      hF _ hS _ _ fun a ha b hb ↦ by
        have hab := mk_not_mem_crossEdges (U := U) (mem_sdiff.mp ha).2 (mem_sdiff.mp hb).2
        rw [mem_union]
        exact ⟨fun h ↦ h.resolve_left fun h1 ↦ hab (hE₁T h1), Or.inr⟩
    simp only [hnext, hF']
  simp only [hinner, hlocal]

/-! ### The Galton–Watson domination -/

/-- **Galton–Watson extinction by generation `g`**, for `Binomial(m, p)` offspring: `q₀ = 0` and
`q_{g+1} = (1 - p (1 - q_g))^m`, the offspring generating function at `q_g`. -/
def gwExtinct (m : ℕ) (p : ℝ) : ℕ → ℝ
  | 0 => 0
  | g + 1 => (1 - p * (1 - gwExtinct m p g)) ^ m

/-- No process is extinct at generation zero. -/
theorem gwExtinct_zero (m : ℕ) (p : ℝ) : gwExtinct m p 0 = 0 :=
  rfl

/-- The extinction recursion. -/
theorem gwExtinct_succ (m : ℕ) (p : ℝ) (g : ℕ) :
    gwExtinct m p (g + 1) = (1 - p * (1 - gwExtinct m p g)) ^ m :=
  rfl

/-- The extinction probabilities lie in `[0, 1]`. -/
theorem gwExtinct_mem_Icc {m : ℕ} {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (g : ℕ) :
    0 ≤ gwExtinct m p g ∧ gwExtinct m p g ≤ 1 := by
  induction g with
  | zero => simp [gwExtinct_zero]
  | succ g ih =>
    obtain ⟨h0, h1⟩ := ih
    have hb0 : 0 ≤ 1 - p * (1 - gwExtinct m p g) := by nlinarith
    have hb1 : 1 - p * (1 - gwExtinct m p g) ≤ 1 := by nlinarith
    rw [gwExtinct_succ]
    exact ⟨pow_nonneg hb0 m, pow_le_one₀ hb0 hb1⟩

/-- **Breadth-first search is dominated by the Galton–Watson process.** From a root set `R` inside
`U`, layer `g` is empty with probability at least `q_g^|R|`, the chance that a Galton–Watson
process with `Binomial(m, p)` offspring started from `|R|` individuals is extinct by generation
`g`. -/
theorem gwExtinct_pow_le_graphProb_layer_eq_empty {m : ℕ} {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (g : ℕ) : ∀ {R U : Finset (Fin m)}, R ⊆ U →
      gwExtinct m p g ^ R.card ≤ graphProb m p (fun E ↦ layer E R U g = ∅) := by
  induction g with
  | zero =>
    intro R U _
    by_cases hR : R = ∅
    · subst hR
      simp [graphProb, layer_zero, graphExpect_const_one]
    · rw [gwExtinct_zero, zero_pow (card_ne_zero.mpr (nonempty_iff_ne_empty.mpr hR))]
      exact graphProb_nonneg hp0 hp1 _
  | succ g ih =>
    intro R U hRU
    obtain ⟨hq0, hq1⟩ := gwExtinct_mem_Icc (m := m) hp0 hp1 g
    have hb0 : 0 ≤ 1 - p * (1 - gwExtinct m p g) := by nlinarith
    have hb1 : 1 - p * (1 - gwExtinct m p g) ≤ 1 := by nlinarith
    have hstep : graphProb m p (fun E ↦ layer E R U (g + 1) = ∅) =
        subsetExpect (crossEdges R U) p (fun E₁ ↦
          graphProb m p (fun E ↦ layer E (nextLayer E₁ R U) (U \ R) g = ∅)) :=
      graphExpect_nextLayer p (fun S E ↦ if layer E S (U \ R) g = ∅ then 1 else 0)
        fun S hS E E' h ↦ by simp only [layer_congr g hS h]
    rw [hstep, gwExtinct_succ, ← pow_mul]
    calc (1 - p * (1 - gwExtinct m p g)) ^ (m * R.card)
        ≤ (1 - p * (1 - gwExtinct m p g)) ^ (crossEdges R U).card :=
          pow_le_pow_of_le_one hb0 hb1 (card_crossEdges_le R U)
      _ = subsetExpect (crossEdges R U) p (fun E₁ ↦ gwExtinct m p g ^ E₁.card) := by
          rw [subsetExpect_pow_card]
          congr 1
          ring
      _ ≤ subsetExpect (crossEdges R U) p
            (fun E₁ ↦ gwExtinct m p g ^ (nextLayer E₁ R U).card) :=
          subsetExpect_mono _ hp0 hp1 fun E₁ _ ↦
            pow_le_pow_of_le_one hq0 hq1 (card_nextLayer_le E₁ R U)
      _ ≤ subsetExpect (crossEdges R U) p (fun E₁ ↦
            graphProb m p (fun E ↦ layer E (nextLayer E₁ R U) (U \ R) g = ∅)) :=
          subsetExpect_mono _ hp0 hp1 fun E₁ _ ↦ ih (nextLayer_subset E₁ R U)

/-- **The layers have mean size at most `|R| (p m)^g`.** -/
theorem graphExpect_card_layer_le {m : ℕ} {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (g : ℕ) :
    ∀ {R U : Finset (Fin m)}, R ⊆ U →
      graphExpect m p (fun E ↦ ((layer E R U g).card : ℝ)) ≤ R.card * (p * m) ^ g := by
  induction g with
  | zero =>
    intro R U _
    simp only [layer_zero, graphExpect_const, pow_zero, mul_one, le_refl]
  | succ g ih =>
    intro R U hRU
    have hstep : graphExpect m p (fun E ↦ ((layer E R U (g + 1)).card : ℝ)) =
        subsetExpect (crossEdges R U) p (fun E₁ ↦
          graphExpect m p (fun E ↦ ((layer E (nextLayer E₁ R U) (U \ R) g).card : ℝ))) :=
      graphExpect_nextLayer p (fun S E ↦ ((layer E S (U \ R) g).card : ℝ))
        fun S hS E E' h ↦ by simp only [layer_congr g hS h]
    have hpm : 0 ≤ (p * m) ^ g := pow_nonneg (mul_nonneg hp0 (Nat.cast_nonneg m)) g
    rw [hstep]
    calc _ ≤ subsetExpect (crossEdges R U) p
          (fun E₁ ↦ ((nextLayer E₁ R U).card : ℝ) * (p * m) ^ g) :=
          subsetExpect_mono _ hp0 hp1 fun E₁ _ ↦ ih (nextLayer_subset E₁ R U)
      _ ≤ subsetExpect (crossEdges R U) p (fun E₁ ↦ (E₁.card : ℝ) * (p * m) ^ g) :=
          subsetExpect_mono _ hp0 hp1 fun E₁ _ ↦
            mul_le_mul_of_nonneg_right (by exact_mod_cast card_nextLayer_le E₁ R U) hpm
      _ = p * (crossEdges R U).card * (p * m) ^ g := by
          rw [subsetExpect_mul_const, subsetExpect_card]
      _ ≤ p * (m * R.card) * (p * m) ^ g := by
          refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ?_ hp0) hpm
          exact_mod_cast card_crossEdges_le R U
      _ = R.card * (p * m) ^ (g + 1) := by ring

/-- **The finite domination inequality.** For every generation `g` and `K > 0`,
`P(|Reach(A)| ≥ K) ≤ 1 - q_g^|A| + |A| Σ_{t<g} (p m)^t / K`: either breadth-first search survives
to generation `g`, or the reach is the union of the first `g` layers, whose total mean size is at
most `|A| Σ_{t<g} (p m)^t`. -/
theorem graphProb_card_reach_ge_le {m : ℕ} {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (A : Finset (Fin m)) (g : ℕ) {K : ℝ} (hK : 0 < K) :
    graphProb m p (fun E ↦ K ≤ ((reach (edgeGraph E) A).card : ℝ)) ≤
      1 - gwExtinct m p g ^ A.card + A.card * (∑ t ∈ range g, (p * m) ^ t) / K := by
  have hpt : ∀ E : Finset (Sym2 (Fin m)),
      (if K ≤ ((reach (edgeGraph E) A).card : ℝ) then (1 : ℝ) else 0) ≤
        (if ¬layer E A univ g = ∅ then 1 else 0) +
          (∑ t ∈ range g, ((layer E A univ t).card : ℝ)) / K := by
    intro E
    have hsum0 : 0 ≤ (∑ t ∈ range g, ((layer E A univ t).card : ℝ)) / K :=
      div_nonneg (sum_nonneg fun _ _ ↦ Nat.cast_nonneg _) hK.le
    by_cases hL : layer E A univ g = ∅
    · rw [if_neg (not_not.mpr hL), zero_add]
      split_ifs with hKr
      · rw [le_div_iff₀ hK, one_mul]
        have hreach : ((reach (edgeGraph E) A).card : ℝ) ≤
            ∑ t ∈ range g, ((layer E A univ t).card : ℝ) := by
          exact_mod_cast (card_le_card (reach_subset_biUnion_layer E A hL)).trans
            card_biUnion_le
        linarith
      · exact hsum0
    · rw [if_pos hL]
      split_ifs <;> linarith
  have h1 := graphProb_add_not m p (fun E ↦ layer E A univ g = ∅)
  have h2 := gwExtinct_pow_le_graphProb_layer_eq_empty hp0 hp1 g (subset_univ A)
  have h3 : ∑ t ∈ range g, graphExpect m p (fun E ↦ ((layer E A univ t).card : ℝ)) ≤
      A.card * ∑ t ∈ range g, (p * m) ^ t := by
    rw [mul_sum]
    exact sum_le_sum fun t _ ↦ graphExpect_card_layer_le hp0 hp1 t (subset_univ A)
  have h4 := div_le_div_of_nonneg_right h3 hK.le
  have hnot : graphProb m p (fun E ↦ ¬layer E A univ g = ∅) =
      graphExpect m p (fun E ↦ if ¬layer E A univ g = ∅ then 1 else 0) := rfl
  calc graphProb m p (fun E ↦ K ≤ ((reach (edgeGraph E) A).card : ℝ))
      ≤ graphExpect m p (fun E ↦ (if ¬layer E A univ g = ∅ then 1 else 0) +
          (∑ t ∈ range g, ((layer E A univ t).card : ℝ)) / K) :=
        graphExpect_mono hp0 hp1 hpt
    _ = graphProb m p (fun E ↦ ¬layer E A univ g = ∅) +
          (∑ t ∈ range g, graphExpect m p (fun E ↦ ((layer E A univ t).card : ℝ))) / K := by
        rw [graphExpect_add, graphExpect_div_const, graphExpect_sum, hnot]
    _ ≤ 1 - gwExtinct m p g ^ A.card + A.card * (∑ t ∈ range g, (p * m) ^ t) / K := by
        linarith

end

end Descent.Pangenome.AncestralLocality
