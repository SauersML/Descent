/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.GeomSum
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Fintype.CardEmbedding
import Mathlib.Data.Real.Archimedean
import Mathlib.Topology.Order.IntermediateValue
import Descent.Layer

assert_below Descent.PopGen Descent.Spectral Descent.Blindness Descent.Conditionals
assert_below Descent.Portability Descent.Decision Descent.Program

/-!
# The locality transition: how large a query's hereditary closure is on a random graph

The note "Ancestral locality" (spec `ANCESTRAL_LOCALITY.md`) shows that on a checking graph `G`
the hereditary closure of the coordinate observation `π_A` on `|A| ≥ 2` features is the
observation on `Reach_G(A)` (its Theorem 4). This file asks how large `Reach_G(A)` is when the
graph is random, `G_m ~ G(m, α/m)` on `m` features with both orientations of every edge, and
proves the finite half of the note's Theorem 5 and its §6.1.

**The model.** `G(m, p)` is a finite law on edge sets. The potential edges are the `C(m, 2)`
unordered pairs of distinct features (`potentialEdges`, `card_potentialEdges`); an edge set `E`
has weight `p^|E| (1 - p)^(C(m,2) - |E|)` (`edgeWeight`), and `graphExpect` is the expectation.
The weights factor as independent coin flips (`edgeWeight_eq_prod`), a fixed set `S` of potential
edges is present with probability `p^|S|` (`graphExpect_indicator_subset`), and the weights add
up to one (`graphExpect_const_one`). The graph `edgeGraph E` is symmetric, so `reach` in it is
`Reach_G(A)` of the directed checking graph with both orientations of each edge. Reachability
does not see the rates, so every choice of positive rates on the present edges has the same
closure.

**Subcritical, (6.1).** For `0 ≤ α < 1` the expected reach satisfies `E|Reach(A)| ≤ |A|/(1 - α)`
for every genome size (`graphExpect_card_reach_le`). The route is the note's. A simple path of
length `ℓ` from a root `r` is an embedding of `Fin ℓ` into the other features (`pathVertex`),
and it has `ℓ` distinct edges (`pathEdges`, `card_pathEdges`). Every feature reachable from `r`
ends a present simple path of length below `m` (`reach_singleton_subset_biUnion`), so `|Reach(r)|`
is at most the number of present simple paths (`card_reach_singleton_le_sum`). There are
`(m - 1)_ℓ` of length `ℓ`, each present with probability `p^ℓ` (`graphExpect_card_presentPaths`),
and `(m - 1)_ℓ (α/m)^ℓ ≤ α^ℓ` (`descFactorial_mul_div_pow_le`). The geometric series gives
`1/(1 - α)` per root (`graphExpect_card_reach_singleton_le`), and the union bound
`|Reach(A)| ≤ Σ_{a ∈ A} |Reach(a)|` (`card_reach_le_sum`) gives (6.1).

**Rates, §6.1.** The rates `r_ij = β / deg(i)` on present edges (`degreeRate`) are positive on
edges (`degreeRate_pos`) and vanish off them (`degreeRate_eq_zero`). Their row sums are `β` or
`0` (`sum_degreeRate`), so `sup_i Σ_j r_ij ≤ β` for every graph and genome size
(`sum_degreeRate_le`, `iSup_sum_degreeRate_le`).

**Supercritical, the constant of (6.2).** For `α > 1` the survival equation `s = 1 - e^{-α s}`
(`survivalMap`) has exactly one root in `(0, 1)` (`existsUnique_survival_root`). That root is
`giantFraction α` (`giantFraction_mem_Ioo`, `survivalMap_giantFraction`, `eq_giantFraction`). It
exists by the intermediate value theorem (`exists_survivalMap_eq_self`) and is unique among all
positive roots by strict convexity of `exp` (`lt_survivalMap_of_lt`,
`survivalMap_root_unique`). For `α ≤ 1` there is no positive root (`survivalMap_lt_self`), which
is where the threshold sits.

Scope. The limit law (6.2) itself is narrower here than in the note: `|C_m(A)|/m ⇒ s` with
probability `1 - (1 - s)^k` and `⇒ 0` with probability `(1 - s)^k` rests on the Erdős–Rényi
giant component theorem, which is not in Mathlib and is not formalized in this file; only its
constant `s` is. The identification of `Reach_G(A)` with the hereditary closure (Theorem 4) is
not imported, so every result is stated about `reach`, the reachability closure of `A` in the
symmetric graph. The note's remark that the single-feature Wright–Fisher chains and Kingman
limits are unchanged is not restated.

## Empirical status

None. The bodies here are finite sums over edge sets, counts of simple paths, and the real fixed
point of `s ↦ 1 - e^{-α s}`. The graph law and the rates are supplied, and no measurement can
bear on them. The note does not claim that real pangenomes lie on either side of `α = 1`.
-/

namespace Descent.Pangenome.AncestralLocality

open Finset Real
open scoped Classical

noncomputable section

/-! ### The law of `G(m, p)` -/

/-- The potential edges on `m` features: the unordered pairs of distinct features. -/
def potentialEdges (m : ℕ) : Finset (Sym2 (Fin m)) :=
  univ.filter fun e ↦ ¬e.IsDiag

/-- A potential edge is an unordered pair that is not a loop. -/
theorem mem_potentialEdges_iff {m : ℕ} (e : Sym2 (Fin m)) :
    e ∈ potentialEdges m ↔ ¬e.IsDiag := by
  simp [potentialEdges]

/-- There are `C(m, 2)` potential edges. -/
theorem card_potentialEdges (m : ℕ) : (potentialEdges m).card = m.choose 2 := by
  have h := Sym2.card_subtype_not_diag (α := Fin m)
  rw [Fintype.card_subtype, Fintype.card_fin] at h
  rw [potentialEdges]
  convert h using 2

/-- **The weight of an edge set under `G(m, p)`**: `p^|E| (1 - p)^(C(m, 2) - |E|)`. -/
def edgeWeight (m : ℕ) (p : ℝ) (E : Finset (Sym2 (Fin m))) : ℝ :=
  p ^ E.card * (1 - p) ^ (m.choose 2 - E.card)

/-- **The expectation under `G(m, p)`** of a function of the edge set. -/
def graphExpect (m : ℕ) (p : ℝ) (f : Finset (Sym2 (Fin m)) → ℝ) : ℝ :=
  ∑ E ∈ (potentialEdges m).powerset, edgeWeight m p E * f E

/-- The weight of an edge set is a product of independent coin flips over the potential edges:
`p` for each present edge and `1 - p` for each absent one. -/
theorem edgeWeight_eq_prod {m : ℕ} (p : ℝ) {E : Finset (Sym2 (Fin m))}
    (hE : E ⊆ potentialEdges m) :
    edgeWeight m p E = (∏ _e ∈ E, p) * ∏ _e ∈ potentialEdges m \ E, (1 - p) := by
  rw [edgeWeight, prod_const, prod_const, card_sdiff_of_subset hE, card_potentialEdges]

/-- **A fixed set of potential edges is present with probability `p^|S|`.** -/
theorem graphExpect_indicator_subset {m : ℕ} (p : ℝ) {S : Finset (Sym2 (Fin m))}
    (hS : S ⊆ potentialEdges m) :
    graphExpect m p (fun E ↦ if S ⊆ E then 1 else 0) = p ^ S.card := by
  have hterm : ∀ E ∈ (potentialEdges m).powerset,
      edgeWeight m p E * (if S ⊆ E then 1 else 0) =
        (∏ _e ∈ E, p) * ∏ e ∈ potentialEdges m \ E, (if e ∈ S then 0 else 1 - p) := by
    intro E hE
    rw [edgeWeight_eq_prod p (mem_powerset.mp hE)]
    by_cases h : S ⊆ E
    · rw [if_pos h, mul_one]
      congr 1
      refine prod_congr rfl fun e he ↦ ?_
      rw [if_neg fun heS ↦ (mem_sdiff.mp he).2 (h heS)]
    · rw [if_neg h, mul_zero]
      obtain ⟨e, heS, heE⟩ := not_subset.mp h
      rw [prod_eq_zero (mem_sdiff.mpr ⟨hS heS, heE⟩) (if_pos heS), mul_zero]
  calc graphExpect m p (fun E ↦ if S ⊆ E then 1 else 0)
      = ∑ E ∈ (potentialEdges m).powerset,
          (∏ _e ∈ E, p) * ∏ e ∈ potentialEdges m \ E, (if e ∈ S then 0 else 1 - p) :=
        sum_congr rfl hterm
    _ = ∏ e ∈ potentialEdges m, (p + if e ∈ S then 0 else 1 - p) := (prod_add _ _ _).symm
    _ = ∏ e ∈ potentialEdges m, (if e ∈ S then p else 1) :=
        prod_congr rfl fun e _ ↦ by split_ifs <;> ring
    _ = p ^ S.card := by rw [prod_ite_mem, inter_eq_right.mpr hS, prod_const]

/-- The weights of `G(m, p)` add up to one. -/
theorem graphExpect_const_one (m : ℕ) (p : ℝ) : graphExpect m p (fun _ ↦ 1) = 1 := by
  simpa using graphExpect_indicator_subset p (empty_subset (potentialEdges m))

/-- The weights of `G(m, p)` are nonnegative when `p` is a probability. -/
theorem edgeWeight_nonneg {m : ℕ} {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (E : Finset (Sym2 (Fin m))) : 0 ≤ edgeWeight m p E :=
  mul_nonneg (pow_nonneg hp0 _) (pow_nonneg (sub_nonneg.mpr hp1) _)

/-- Expectation under `G(m, p)` is monotone. -/
theorem graphExpect_mono {m : ℕ} {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    {f g : Finset (Sym2 (Fin m)) → ℝ} (hfg : ∀ E, f E ≤ g E) :
    graphExpect m p f ≤ graphExpect m p g :=
  sum_le_sum fun E _ ↦ mul_le_mul_of_nonneg_left (hfg E) (edgeWeight_nonneg hp0 hp1 E)

/-- Expectation under `G(m, p)` commutes with finite sums. -/
theorem graphExpect_sum {m : ℕ} (p : ℝ) {ι : Type*} (s : Finset ι)
    (f : ι → Finset (Sym2 (Fin m)) → ℝ) :
    graphExpect m p (fun E ↦ ∑ i ∈ s, f i E) = ∑ i ∈ s, graphExpect m p (f i) := by
  simp only [graphExpect, mul_sum]
  exact sum_comm

/-- `α / m` is a probability when `0 ≤ α ≤ 1`. -/
theorem div_natCast_nonneg_and_le_one {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (m : ℕ) :
    0 ≤ α / m ∧ α / m ≤ 1 := by
  refine ⟨div_nonneg hα0 (Nat.cast_nonneg m), ?_⟩
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp
  · exact (div_le_self hα0 (Nat.one_le_cast.mpr hm)).trans hα1

/-! ### Reachability and simple paths -/

/-- **The checking graph of an edge set**: features `u ≠ v` are adjacent when `{u, v} ∈ E`. The
adjacency is symmetric: both orientations of every edge are present. -/
def edgeGraph {m : ℕ} (E : Finset (Sym2 (Fin m))) : SimpleGraph (Fin m) :=
  SimpleGraph.fromEdgeSet (E : Set (Sym2 (Fin m)))

/-- Adjacency in the checking graph of `E`. -/
theorem edgeGraph_adj_iff {m : ℕ} (E : Finset (Sym2 (Fin m))) (u v : Fin m) :
    (edgeGraph E).Adj u v ↔ s(u, v) ∈ E ∧ u ≠ v := by
  rw [edgeGraph, SimpleGraph.fromEdgeSet_adj, mem_coe]

/-- **`Reach_G(A)`**: the features joined to a member of `A` by a path of `G`, `A` included. -/
def reach {m : ℕ} (G : SimpleGraph (Fin m)) (A : Finset (Fin m)) : Finset (Fin m) :=
  univ.filter fun v ↦ ∃ a ∈ A, G.Reachable a v

/-- Membership in the reach. -/
theorem mem_reach_iff {m : ℕ} (G : SimpleGraph (Fin m)) (A : Finset (Fin m)) (v : Fin m) :
    v ∈ reach G A ↔ ∃ a ∈ A, G.Reachable a v := by
  simp [reach]

/-- A query lies inside its reach. -/
theorem subset_reach {m : ℕ} (G : SimpleGraph (Fin m)) (A : Finset (Fin m)) :
    A ⊆ reach G A :=
  fun a ha ↦ (mem_reach_iff G A a).mpr ⟨a, ha, SimpleGraph.Reachable.refl a⟩

/-- The reach of a query is the union of the reaches of its members. -/
theorem reach_eq_biUnion {m : ℕ} (G : SimpleGraph (Fin m)) (A : Finset (Fin m)) :
    reach G A = A.biUnion fun a ↦ reach G {a} := by
  ext v
  simp [reach]

/-- **The union bound**: `|Reach(A)| ≤ Σ_{a ∈ A} |Reach(a)|`. -/
theorem card_reach_le_sum {m : ℕ} (G : SimpleGraph (Fin m)) (A : Finset (Fin m)) :
    (reach G A).card ≤ ∑ a ∈ A, (reach G {a}).card := by
  rw [reach_eq_biUnion]
  exact card_biUnion_le

/-- The vertex sequence `r = v₀, v₁, …, v_ℓ` of the simple path from `r` whose later vertices
are `f 0, …, f (ℓ - 1)`. -/
def pathVertex {m ℓ : ℕ} (r : Fin m) (f : Fin ℓ ↪ {v : Fin m // v ≠ r}) :
    Fin (ℓ + 1) → Fin m :=
  Fin.cons r fun t ↦ (f t : Fin m)

/-- The vertices of a simple path are distinct. -/
theorem pathVertex_injective {m ℓ : ℕ} (r : Fin m) (f : Fin ℓ ↪ {v : Fin m // v ≠ r}) :
    Function.Injective (pathVertex r f) := by
  refine Fin.cons_injective_iff.mpr ⟨?_, Subtype.val_injective.comp f.injective⟩
  rintro ⟨t, ht⟩
  exact (f t).2 ht

/-- **The edges `{v_t, v_{t+1}}` of a simple path.** -/
def pathEdges {m ℓ : ℕ} (r : Fin m) (f : Fin ℓ ↪ {v : Fin m // v ≠ r}) :
    Finset (Sym2 (Fin m)) :=
  univ.image fun t : Fin ℓ ↦ s(pathVertex r f t.castSucc, pathVertex r f t.succ)

/-- **A simple path of length `ℓ` has `ℓ` distinct edges.** -/
theorem card_pathEdges {m ℓ : ℕ} (r : Fin m) (f : Fin ℓ ↪ {v : Fin m // v ≠ r}) :
    (pathEdges r f).card = ℓ := by
  have hinj : Function.Injective fun t : Fin ℓ ↦
      s(pathVertex r f t.castSucc, pathVertex r f t.succ) := by
    intro t u htu
    have hv := pathVertex_injective r f
    rcases Sym2.eq_iff.mp htu with ⟨h1, -⟩ | ⟨h1, h2⟩
    · exact Fin.castSucc_injective ℓ (hv h1)
    · have e1 := congrArg Fin.val (hv h1)
      have e2 := congrArg Fin.val (hv h2)
      simp only [Fin.coe_castSucc, Fin.val_succ] at e1 e2
      omega
  rw [pathEdges, card_image_of_injective _ hinj, card_univ, Fintype.card_fin]

/-- A path edge joins two distinct features, so it is a potential edge. -/
theorem pathEdges_subset {m ℓ : ℕ} (r : Fin m) (f : Fin ℓ ↪ {v : Fin m // v ≠ r}) :
    pathEdges r f ⊆ potentialEdges m := by
  intro e he
  obtain ⟨t, -, rfl⟩ := mem_image.mp he
  simp only [mem_potentialEdges_iff, Sym2.mk_isDiag_iff]
  exact (pathVertex_injective r f).ne (Fin.castSucc_lt_succ t).ne

/-- The endpoint `v_ℓ` of a simple path. -/
def pathEnd {m ℓ : ℕ} (r : Fin m) (f : Fin ℓ ↪ {v : Fin m // v ≠ r}) : Fin m :=
  pathVertex r f (Fin.last ℓ)

/-- **The simple paths of length `ℓ` from `r` all of whose edges are present in `E`.** -/
def presentPaths {m : ℕ} (E : Finset (Sym2 (Fin m))) (r : Fin m) (ℓ : ℕ) :
    Finset (Fin ℓ ↪ {v : Fin m // v ≠ r}) :=
  univ.filter fun f ↦ pathEdges r f ⊆ E

/-- **Every feature reachable from `r` ends a present simple path** of length below `m`. -/
theorem reach_singleton_subset_biUnion {m : ℕ} (E : Finset (Sym2 (Fin m))) (r : Fin m) :
    reach (edgeGraph E) {r} ⊆
      (range m).biUnion fun ℓ ↦ (presentPaths E r ℓ).image (pathEnd r) := by
  intro v hv
  obtain ⟨a, ha, hreach⟩ := (mem_reach_iff _ _ v).mp hv
  rw [mem_singleton] at ha
  rw [ha] at hreach
  obtain ⟨p, hp⟩ := hreach.exists_isPath
  have hlen : p.length < m := by simpa using hp.length_lt
  have hmem : ∀ i, i ≤ p.length → i ∈ {i | i ≤ p.length} := fun i hi ↦ hi
  have hne : ∀ t : Fin p.length, p.getVert (t + 1) ≠ r := by
    intro t h
    have ht := t.2
    have h0 := hp.getVert_injOn (hmem (t + 1) ht) (hmem 0 (Nat.zero_le _))
      (h.trans p.getVert_zero.symm)
    omega
  let f : Fin p.length ↪ {w : Fin m // w ≠ r} :=
    ⟨fun t ↦ ⟨p.getVert (t + 1), hne t⟩, fun t u htu ↦ by
      have ht := t.2
      have hu := u.2
      have h := hp.getVert_injOn (hmem (t + 1) ht) (hmem (u + 1) hu)
        (congrArg Subtype.val htu)
      exact Fin.ext (by omega)⟩
  have hvert : ∀ j : Fin (p.length + 1), pathVertex r f j = p.getVert j := by
    intro j
    induction j using Fin.cases with
    | zero => simp [pathVertex]
    | succ t => simp [pathVertex, f]
  refine mem_biUnion.mpr ⟨p.length, mem_range.mpr hlen, mem_image.mpr ⟨f, ?_, ?_⟩⟩
  · refine mem_filter.mpr ⟨mem_univ _, fun e he ↦ ?_⟩
    obtain ⟨t, -, rfl⟩ := mem_image.mp he
    have hadj := p.adj_getVert_succ t.2
    simp only [hvert, Fin.coe_castSucc, Fin.val_succ]
    exact ((edgeGraph_adj_iff E _ _).mp hadj).1
  · rw [pathEnd, hvert, Fin.val_last, p.getVert_length]

/-- **The reach of a root is at most the number of present simple paths from it.** -/
theorem card_reach_singleton_le_sum {m : ℕ} (E : Finset (Sym2 (Fin m))) (r : Fin m) :
    ((reach (edgeGraph E) {r}).card : ℝ) ≤ ∑ ℓ ∈ range m, ((presentPaths E r ℓ).card : ℝ) := by
  have h := (card_le_card (reach_singleton_subset_biUnion E r)).trans card_biUnion_le
  have h2 : ∑ ℓ ∈ range m, ((presentPaths E r ℓ).image (pathEnd r)).card ≤
      ∑ ℓ ∈ range m, (presentPaths E r ℓ).card :=
    sum_le_sum fun ℓ _ ↦ card_image_le
  exact_mod_cast h.trans h2

/-- A root has `m - 1` other features. -/
theorem card_subtype_ne {m : ℕ} (r : Fin m) : Fintype.card {v : Fin m // v ≠ r} = m - 1 := by
  rw [Fintype.card_subtype_compl, Fintype.card_fin, Fintype.card_subtype_eq]

/-- **There are `(m - 1)_ℓ` simple paths of length `ℓ` from a root, and each is present with
probability `p^ℓ`**, so the expected number of present ones is `(m - 1)_ℓ p^ℓ`. -/
theorem graphExpect_card_presentPaths (m : ℕ) (p : ℝ) (r : Fin m) (ℓ : ℕ) :
    graphExpect m p (fun E ↦ ((presentPaths E r ℓ).card : ℝ)) =
      ((m - 1).descFactorial ℓ : ℝ) * p ^ ℓ := by
  have hcard : ∀ E : Finset (Sym2 (Fin m)), ((presentPaths E r ℓ).card : ℝ) =
      ∑ f : Fin ℓ ↪ {v : Fin m // v ≠ r}, if pathEdges r f ⊆ E then 1 else 0 :=
    fun E ↦ natCast_card_filter _ _
  simp only [hcard]
  rw [graphExpect_sum]
  simp only [graphExpect_indicator_subset p (pathEdges_subset r _), card_pathEdges]
  rw [sum_const, card_univ, Fintype.card_embedding_eq, Fintype.card_fin, card_subtype_ne,
    nsmul_eq_mul]

/-- `(m - 1)_ℓ (α / m)^ℓ ≤ α^ℓ` for `α ≥ 0`. -/
theorem descFactorial_mul_div_pow_le {α : ℝ} (hα : 0 ≤ α) (m ℓ : ℕ) :
    ((m - 1).descFactorial ℓ : ℝ) * (α / m) ^ ℓ ≤ α ^ ℓ := by
  have hp : 0 ≤ α / m := div_nonneg hα (Nat.cast_nonneg m)
  have h1 : ((m - 1).descFactorial ℓ : ℝ) ≤ (m : ℝ) ^ ℓ := by
    exact_mod_cast (Nat.descFactorial_le_pow (m - 1) ℓ).trans
      (Nat.pow_le_pow_left (Nat.sub_le m 1) ℓ)
  have h2 : (m : ℝ) * (α / m) ≤ α := by
    rcases eq_or_ne (m : ℝ) 0 with h | h
    · rw [h, zero_mul]
      exact hα
    · exact le_of_eq (by rw [mul_div_assoc', mul_div_cancel_left₀ α h])
  calc ((m - 1).descFactorial ℓ : ℝ) * (α / m) ^ ℓ ≤ (m : ℝ) ^ ℓ * (α / m) ^ ℓ :=
        mul_le_mul_of_nonneg_right h1 (pow_nonneg hp ℓ)
    _ = ((m : ℝ) * (α / m)) ^ ℓ := (mul_pow _ _ _).symm
    _ ≤ α ^ ℓ := pow_le_pow_left₀ (mul_nonneg (Nat.cast_nonneg m) hp) h2 ℓ

/-- **The expected reach of one root is at most `1 / (1 - α)`** in `G(m, α / m)` with
`0 ≤ α < 1`, whatever the genome size `m`. -/
theorem graphExpect_card_reach_singleton_le {m : ℕ} {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1)
    (r : Fin m) :
    graphExpect m (α / m) (fun E ↦ ((reach (edgeGraph E) {r}).card : ℝ)) ≤ 1 / (1 - α) := by
  obtain ⟨hp0, hp1⟩ := div_natCast_nonneg_and_le_one hα0 hα1.le m
  calc graphExpect m (α / m) (fun E ↦ ((reach (edgeGraph E) {r}).card : ℝ))
      ≤ graphExpect m (α / m) (fun E ↦ ∑ ℓ ∈ range m, ((presentPaths E r ℓ).card : ℝ)) :=
        graphExpect_mono hp0 hp1 fun E ↦ card_reach_singleton_le_sum E r
    _ = ∑ ℓ ∈ range m, ((m - 1).descFactorial ℓ : ℝ) * (α / m) ^ ℓ := by
        rw [graphExpect_sum]
        exact sum_congr rfl fun ℓ _ ↦ graphExpect_card_presentPaths m (α / m) r ℓ
    _ ≤ ∑ ℓ ∈ range m, α ^ ℓ := sum_le_sum fun ℓ _ ↦ descFactorial_mul_div_pow_le hα0 m ℓ
    _ ≤ α ^ 0 / (1 - α) := by
        rw [range_eq_Ico]
        exact geom_sum_Ico_le_of_lt_one hα0 hα1
    _ = 1 / (1 - α) := by rw [pow_zero]

/-- **Theorem 5, subcritical, (6.1).** In `G(m, α / m)` with `0 ≤ α < 1` the expected size of
`Reach(A)` is at most `|A| / (1 - α)`, for every genome size `m`. -/
theorem graphExpect_card_reach_le {m : ℕ} {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1)
    (A : Finset (Fin m)) :
    graphExpect m (α / m) (fun E ↦ ((reach (edgeGraph E) A).card : ℝ)) ≤ A.card / (1 - α) := by
  obtain ⟨hp0, hp1⟩ := div_natCast_nonneg_and_le_one hα0 hα1.le m
  calc graphExpect m (α / m) (fun E ↦ ((reach (edgeGraph E) A).card : ℝ))
      ≤ graphExpect m (α / m) (fun E ↦ ∑ a ∈ A, ((reach (edgeGraph E) {a}).card : ℝ)) :=
        graphExpect_mono hp0 hp1 fun E ↦ by exact_mod_cast card_reach_le_sum (edgeGraph E) A
    _ = ∑ a ∈ A, graphExpect m (α / m) (fun E ↦ ((reach (edgeGraph E) {a}).card : ℝ)) :=
        graphExpect_sum _ _ _
    _ ≤ ∑ _a ∈ A, 1 / (1 - α) :=
        sum_le_sum fun a _ ↦ graphExpect_card_reach_singleton_le hα0 hα1 a
    _ = A.card / (1 - α) := by rw [sum_const, nsmul_eq_mul, mul_one_div]

/-! ### Degree-normalized rates (§6.1) -/

/-- **The rates of §6.1**: `r_ij = β / deg(i)` on the edges of `G`, and `0` off them. -/
def degreeRate {m : ℕ} (G : SimpleGraph (Fin m)) (β : ℝ) (i j : Fin m) : ℝ :=
  if G.Adj i j then β / G.degree i else 0

/-- The degree-normalized rates are positive on the edges of `G`. -/
theorem degreeRate_pos {m : ℕ} (G : SimpleGraph (Fin m)) {β : ℝ} (hβ : 0 < β) {i j : Fin m}
    (h : G.Adj i j) : 0 < degreeRate G β i j := by
  have hdeg : 0 < G.degree i := by
    rw [SimpleGraph.degree_pos_iff_exists_adj]
    exact ⟨j, h⟩
  rw [degreeRate, if_pos h]
  exact div_pos hβ (Nat.cast_pos.mpr hdeg)

/-- The degree-normalized rates vanish off the edges of `G`. -/
theorem degreeRate_eq_zero {m : ℕ} (G : SimpleGraph (Fin m)) (β : ℝ) {i j : Fin m}
    (h : ¬G.Adj i j) : degreeRate G β i j = 0 := by
  rw [degreeRate, if_neg h]

/-- **The row sums of the degree-normalized rates**: `β` at a feature with an edge, `0` at an
isolated one. -/
theorem sum_degreeRate {m : ℕ} (G : SimpleGraph (Fin m)) (β : ℝ) (i : Fin m) :
    ∑ j, degreeRate G β i j = if G.degree i = 0 then 0 else β := by
  have hrate : ∀ j, degreeRate G β i j =
      if j ∈ G.neighborFinset i then β / G.degree i else 0 := by
    intro j
    by_cases h : G.Adj i j
    · rw [degreeRate, if_pos h, if_pos (by simpa using h)]
    · rw [degreeRate, if_neg h, if_neg (by simpa using h)]
  simp only [hrate]
  rw [sum_ite_mem, univ_inter, sum_const, SimpleGraph.card_neighborFinset_eq_degree,
    nsmul_eq_mul]
  split_ifs with h
  · rw [h, Nat.cast_zero, zero_mul]
  · have hdeg : (G.degree i : ℝ) ≠ 0 := by exact_mod_cast h
    rw [mul_div_assoc', mul_div_cancel_left₀ β hdeg]

/-- Every row sum of the degree-normalized rates is at most `β`. -/
theorem sum_degreeRate_le {m : ℕ} (G : SimpleGraph (Fin m)) {β : ℝ} (hβ : 0 ≤ β) (i : Fin m) :
    ∑ j, degreeRate G β i j ≤ β := by
  rw [sum_degreeRate]
  split_ifs
  · exact hβ
  · exact le_rfl

/-- **§6.1: `sup_i Σ_j r_ij ≤ β`** for the degree-normalized rates, for every graph and every
genome size. -/
theorem iSup_sum_degreeRate_le {m : ℕ} (G : SimpleGraph (Fin m)) {β : ℝ} (hβ : 0 ≤ β) :
    ⨆ i, ∑ j, degreeRate G β i j ≤ β :=
  Real.iSup_le (sum_degreeRate_le G hβ) hβ

/-! ### The survival equation `s = 1 - e^{-α s}` -/

/-- **The survival map** `s ↦ 1 - e^{-α s}`; its positive fixed point is the survival
probability of a Poisson(`α`) branching process and the giant fraction of `G(m, α / m)`. -/
def survivalMap (α s : ℝ) : ℝ :=
  1 - exp (-(α * s))

/-- **Strict convexity of `exp` below a super-solution.** If `0 < s < t` and
`t ≤ 1 - e^{-α t}`, then `s < 1 - e^{-α s}`. -/
theorem lt_survivalMap_of_lt {α s t : ℝ} (hα : 0 < α) (hs : 0 < s) (hst : s < t)
    (ht : t ≤ survivalMap α t) : s < survivalMap α s := by
  have ht0 : 0 < t := hs.trans hst
  have ha0 : 0 < s / t := div_pos hs ht0
  have ha1 : 0 < 1 - s / t := by
    rw [sub_pos, div_lt_one ht0]
    exact hst
  have hconv := strictConvexOn_exp.2 (Set.mem_univ (-(α * t))) (Set.mem_univ 0)
    (neg_ne_zero.mpr (mul_pos hα ht0).ne') ha0 ha1 (by ring)
  have hkey : s / t * -(α * t) + (1 - s / t) * 0 = -(α * s) := by
    rw [mul_zero, add_zero, mul_neg, neg_inj]
    calc s / t * (α * t) = α * (s / t * t) := by ring
      _ = α * s := by rw [div_mul_cancel₀ s ht0.ne']
  simp only [smul_eq_mul] at hconv
  rw [hkey, Real.exp_zero, mul_one] at hconv
  have hexp : exp (-(α * t)) ≤ 1 - t := by
    unfold survivalMap at ht
    linarith
  have h2 : s / t * exp (-(α * t)) ≤ s / t * (1 - t) := mul_le_mul_of_nonneg_left hexp ha0.le
  have h3 : s / t * (1 - t) = s / t - s := by
    rw [mul_sub, mul_one, div_mul_cancel₀ s ht0.ne']
  unfold survivalMap
  linarith

/-- **For `α ≤ 1` the survival equation has no positive root**: `1 - e^{-α s} < s` for `s > 0`. -/
theorem survivalMap_lt_self {α s : ℝ} (hα : α ≤ 1) (hs : 0 < s) : survivalMap α s < s := by
  have h1 : exp (-s) ≤ exp (-(α * s)) := Real.exp_le_exp.mpr (by nlinarith)
  have h2 := Real.add_one_lt_exp (neg_ne_zero.mpr hs.ne')
  unfold survivalMap
  linarith

/-- **For `α > 1` the survival equation has a root in `(0, 1)`**, by the intermediate value
theorem between `s = (α - 1) / (2 α)`, where the map lies above the diagonal, and `s = 1`. -/
theorem exists_survivalMap_eq_self {α : ℝ} (hα : 1 < α) :
    ∃ s ∈ Set.Ioo (0 : ℝ) 1, survivalMap α s = s := by
  have hα0 : 0 < α := by linarith
  set ε := (α - 1) / (2 * α) with hε
  have hε0 : 0 < ε := div_pos (by linarith) (by linarith)
  have hε1 : ε < 1 := by
    rw [hε, div_lt_one (by linarith)]
    linarith
  have hαε : α * ε = (α - 1) / 2 := by
    rw [hε, mul_div_assoc', mul_comm 2 α, mul_div_mul_left _ _ hα0.ne']
  have hexp : exp (-(α * ε)) ≤ 2 / (α + 1) := by
    rw [Real.exp_neg, inv_eq_one_div, div_le_div_iff₀ (Real.exp_pos _) (by linarith)]
    linarith [Real.add_one_le_exp (α * ε)]
  have hsum : 2 / (α + 1) + ε < 1 := by
    have h1 : (0 : ℝ) < α + 1 := by linarith
    have h2 : (0 : ℝ) < 2 * α := by linarith
    rw [hε, div_add_div _ _ h1.ne' h2.ne', div_lt_one (mul_pos h1 h2)]
    nlinarith [mul_pos (sub_pos.mpr hα) (sub_pos.mpr hα)]
  have hfε : 0 < survivalMap α ε - ε := by
    unfold survivalMap
    linarith
  have hf1 : survivalMap α 1 - 1 < 0 := by
    unfold survivalMap
    linarith [Real.exp_pos (-(α * 1))]
  have hcont : ContinuousOn (fun s ↦ survivalMap α s - s) (Set.Icc ε 1) := by
    unfold survivalMap
    fun_prop
  obtain ⟨s, hs, hs0⟩ := intermediate_value_Ioo' hε1.le hcont ⟨hf1, hfε⟩
  exact ⟨s, ⟨hε0.trans hs.1, hs.2⟩, sub_eq_zero.mp hs0⟩

/-- **The giant fraction `s(α)`**: the root in `(0, 1)` of `s = 1 - e^{-α s}` when `α > 1`, and
`0` when `α ≤ 1`. -/
def giantFraction (α : ℝ) : ℝ :=
  if h : 1 < α then (exists_survivalMap_eq_self h).choose else 0

/-- For `α > 1` the giant fraction lies in `(0, 1)`. -/
theorem giantFraction_mem_Ioo {α : ℝ} (h : 1 < α) : giantFraction α ∈ Set.Ioo 0 1 := by
  rw [giantFraction, dif_pos h]
  exact (exists_survivalMap_eq_self h).choose_spec.1

/-- The giant fraction solves the survival equation. -/
theorem survivalMap_giantFraction (α : ℝ) :
    survivalMap α (giantFraction α) = giantFraction α := by
  by_cases h : 1 < α
  · rw [giantFraction, dif_pos h]
    exact (exists_survivalMap_eq_self h).choose_spec.2
  · rw [giantFraction, dif_neg h]
    simp [survivalMap]

/-- For `α ≤ 1` the giant fraction is `0`. -/
theorem giantFraction_eq_zero {α : ℝ} (h : α ≤ 1) : giantFraction α = 0 := by
  rw [giantFraction, dif_neg (not_lt.mpr h)]

/-- **The positive root of the survival equation is unique.** -/
theorem survivalMap_root_unique {α s t : ℝ} (hα : 0 < α) (hs : 0 < s) (ht : 0 < t)
    (hs' : survivalMap α s = s) (ht' : survivalMap α t = t) : s = t := by
  rcases lt_trichotomy s t with h | h | h
  · exact absurd hs' (lt_survivalMap_of_lt hα hs h ht'.ge).ne'
  · exact h
  · exact absurd ht' (lt_survivalMap_of_lt hα ht h hs'.ge).ne'

/-- For `α > 1` every positive root of the survival equation is the giant fraction. -/
theorem eq_giantFraction {α s : ℝ} (hα : 1 < α) (hs : 0 < s) (hs' : survivalMap α s = s) :
    s = giantFraction α :=
  survivalMap_root_unique (by linarith) hs (giantFraction_mem_Ioo hα).1 hs'
    (survivalMap_giantFraction α)

/-- **Theorem 5, the constant of (6.2).** For `α > 1` there is exactly one `s ∈ (0, 1)` with
`s = 1 - e^{-α s}`. -/
theorem existsUnique_survival_root {α : ℝ} (hα : 1 < α) :
    ∃! s : ℝ, s ∈ Set.Ioo 0 1 ∧ s = 1 - exp (-(α * s)) :=
  ⟨giantFraction α, ⟨giantFraction_mem_Ioo hα, (survivalMap_giantFraction α).symm⟩,
    fun _ hs ↦ eq_giantFraction hα hs.1.1 hs.2.symm⟩

end

end Descent.Pangenome.AncestralLocality
