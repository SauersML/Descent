/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Pangenome.AncestralLocality.SupercriticalReach

assert_below Descent.PopGen Descent.Spectral Descent.Blindness Descent.Conditionals
assert_below Descent.Portability Descent.Decision Descent.Program

/-!
# Exchangeable roots: the weights of the supercritical limit law

The note's (6.2) gives the giant branch probability `1 - (1 - s)^k` for `k` fixed roots. The
reason is exchangeability. `G(m, p)` does not see the names of the features, so the chance that
`k` roots all miss the large components depends on the roots only through `k`. Averaging over all
`k`-subsets turns that chance into a count of subsets of the complement. This file proves the
identity exactly, at every genome size, together with the bounds on the resulting ratio of
binomial coefficients that the limit in `m` needs.

**Relabeling.** A permutation `σ` of the features relabels an edge set (`mapEdges`). Relabeling
keeps potential edges potential (`mapEdges_subset`) and the number of edges fixed
(`card_mapEdges`), so it preserves the law of `G(m, p)` (`graphExpect_comp_mapEdges`). It is an
isomorphism of checking graphs (`edgeGraphIso`), so it carries reaches to reaches
(`reach_mapEdges`) and the features in components of more than `t` features (`bigSet`) to the
same set for the relabeled graph (`bigSet_mapEdges`).

**Exchangeability.** Any two queries of one size are related by a relabeling
(`exists_perm_image_eq`), so the probability that a query misses the large components depends
only on its size (`graphProb_disjoint_bigSet_eq`). The `k`-subsets that miss a set `S` number
`C(m - |S|, k)` (`sum_powersetCard_indicator_disjoint`). Summing over all `k`-subsets therefore
gives `C(m, k) P(A misses the large components) = E[C(m - |large|, k)]`
(`choose_mul_graphProb_disjoint_bigSet`).

**The ratio.** `C(n, k)/C(m, k) = n_(k)/m_(k)` (`choose_div_choose_eq`) lies between
`((n + 1 - k)/m)^k` and `(n/m)^k` for `n ≤ m` (`pow_le_choose_div_choose`,
`choose_div_choose_le`, through `descFactorial_mul_pow_le`). So `C(m - x, k)/C(m, k)` is within `η`
of `c^k` once `1 - x/m` is within `δ` of `c` and `k/m ≤ δ`, where `2δ` is a modulus of continuity
of `t ↦ t^k` at `c` (`abs_choose_div_choose_sub_pow_le`).

Scope. Nothing here is asymptotic, and nothing rests on the Erdős–Rényi theorem; the limit in `m`
is taken in a sibling module. The large components are those above a threshold `t`, not a chosen
largest component, so no tie is broken and relabeling needs no choice.

## Empirical status

None. The bodies are sums over edge sets, counts of subsets and ratios of binomial coefficients.
Nothing is measured.
-/

namespace Descent.Pangenome.AncestralLocality

open Finset
open scoped Classical

noncomputable section

/-! ### Relabeling the features -/

/-- **Relabeling an edge set** by a permutation `σ` of the features. -/
def mapEdges {m : ℕ} (σ : Equiv.Perm (Fin m)) (E : Finset (Sym2 (Fin m))) :
    Finset (Sym2 (Fin m)) :=
  E.image (Sym2.map σ)

/-- Relabeling by `σ⁻¹` undoes relabeling by `σ`. -/
theorem mapEdges_symm_mapEdges {m : ℕ} (σ : Equiv.Perm (Fin m)) (E : Finset (Sym2 (Fin m))) :
    mapEdges σ.symm (mapEdges σ E) = E := by
  have h : (Sym2.map σ.symm ∘ Sym2.map σ) = id := by
    funext e
    rw [Function.comp_apply, Sym2.map_map, Equiv.symm_comp_self, Sym2.map_id]
  rw [mapEdges, mapEdges, image_image, h, image_id]

/-- Relabeling by `σ` undoes relabeling by `σ⁻¹`. -/
theorem mapEdges_mapEdges_symm {m : ℕ} (σ : Equiv.Perm (Fin m)) (E : Finset (Sym2 (Fin m))) :
    mapEdges σ (mapEdges σ.symm E) = E := by
  have h : (Sym2.map σ ∘ Sym2.map σ.symm) = id := by
    funext e
    rw [Function.comp_apply, Sym2.map_map, Equiv.self_comp_symm, Sym2.map_id]
  rw [mapEdges, mapEdges, image_image, h, image_id]

/-- Relabeling keeps potential edges potential. -/
theorem mapEdges_subset {m : ℕ} (σ : Equiv.Perm (Fin m)) {E : Finset (Sym2 (Fin m))}
    (hE : E ⊆ potentialEdges m) : mapEdges σ E ⊆ potentialEdges m := by
  intro e he
  obtain ⟨e', he', rfl⟩ := mem_image.mp he
  rw [mem_potentialEdges_iff, Sym2.isDiag_map σ.injective]
  exact (mem_potentialEdges_iff e').mp (hE he')

/-- Relabeling keeps the number of edges. -/
theorem card_mapEdges {m : ℕ} (σ : Equiv.Perm (Fin m)) (E : Finset (Sym2 (Fin m))) :
    (mapEdges σ E).card = E.card :=
  card_image_of_injective _ (Sym2.map.injective σ.injective)

/-- **The law of `G(m, p)` does not see the names of the features.** -/
theorem graphExpect_comp_mapEdges {m : ℕ} (p : ℝ) (σ : Equiv.Perm (Fin m))
    (f : Finset (Sym2 (Fin m)) → ℝ) :
    graphExpect m p (fun E ↦ f (mapEdges σ E)) = graphExpect m p f := by
  refine sum_nbij' (mapEdges σ) (mapEdges σ.symm) (fun E hE ↦ ?_) (fun E hE ↦ ?_)
    (fun E _ ↦ mapEdges_symm_mapEdges σ E) (fun E _ ↦ mapEdges_mapEdges_symm σ E)
    (fun E _ ↦ ?_)
  · exact mem_powerset.mpr (mapEdges_subset σ (mem_powerset.mp hE))
  · exact mem_powerset.mpr (mapEdges_subset σ.symm (mem_powerset.mp hE))
  · rw [edgeWeight, edgeWeight, card_mapEdges]

/-- **Relabeling is an isomorphism of checking graphs.** -/
def edgeGraphIso {m : ℕ} (σ : Equiv.Perm (Fin m)) (E : Finset (Sym2 (Fin m))) :
    edgeGraph E ≃g edgeGraph (mapEdges σ E) where
  toEquiv := σ
  map_rel_iff' := by
    intro u v
    rw [edgeGraph_adj_iff, edgeGraph_adj_iff, mapEdges, ← Sym2.map_pair_eq σ u v,
      (Sym2.map.injective σ.injective).mem_finset_image, σ.injective.ne_iff]

/-- **Relabeling carries reaches to reaches.** -/
theorem reach_mapEdges {m : ℕ} (σ : Equiv.Perm (Fin m)) (E : Finset (Sym2 (Fin m)))
    (A : Finset (Fin m)) :
    reach (edgeGraph (mapEdges σ E)) (A.image σ) = (reach (edgeGraph E) A).image σ := by
  ext v
  obtain ⟨u, rfl⟩ := σ.surjective v
  rw [σ.injective.mem_finset_image, mem_reach_iff, mem_reach_iff]
  constructor
  · rintro ⟨b, hb, hbu⟩
    obtain ⟨a, ha, rfl⟩ := mem_image.mp hb
    exact ⟨a, ha, (SimpleGraph.Iso.reachable_iff (φ := edgeGraphIso σ E)).mp hbu⟩
  · rintro ⟨a, ha, hau⟩
    exact ⟨σ a, mem_image_of_mem σ ha,
      (SimpleGraph.Iso.reachable_iff (φ := edgeGraphIso σ E)).mpr hau⟩

/-- **The features in large components**: those whose component has more than `t` features. -/
def bigSet {m : ℕ} (G : SimpleGraph (Fin m)) (t : ℝ) : Finset (Fin m) :=
  univ.filter fun v ↦ t < ((reach G {v}).card : ℝ)

/-- Membership in the large set. -/
theorem mem_bigSet_iff {m : ℕ} (G : SimpleGraph (Fin m)) (t : ℝ) (v : Fin m) :
    v ∈ bigSet G t ↔ t < ((reach G {v}).card : ℝ) := by
  simp [bigSet]

/-- **Relabeling carries the large set to the large set.** -/
theorem bigSet_mapEdges {m : ℕ} (σ : Equiv.Perm (Fin m)) (E : Finset (Sym2 (Fin m))) (t : ℝ) :
    bigSet (edgeGraph (mapEdges σ E)) t = (bigSet (edgeGraph E) t).image σ := by
  ext v
  obtain ⟨u, rfl⟩ := σ.surjective v
  have hcard : (reach (edgeGraph (mapEdges σ E)) {σ u}).card =
      (reach (edgeGraph E) {u}).card := by
    rw [← image_singleton σ u, reach_mapEdges, card_image_of_injective _ σ.injective]
  rw [σ.injective.mem_finset_image, mem_bigSet_iff, mem_bigSet_iff, hcard]

/-! ### Exchangeability -/

/-- **Any two queries of one size are related by a relabeling.** -/
theorem exists_perm_image_eq {m : ℕ} {A B : Finset (Fin m)} (h : A.card = B.card) :
    ∃ σ : Equiv.Perm (Fin m), A.image σ = B := by
  have hcard : Fintype.card {x // x ∈ A} = Fintype.card {x // x ∈ B} := by
    simp only [Fintype.card_coe, h]
  refine ⟨(Fintype.equivOfCardEq hcard).extendSubtype, eq_of_subset_of_card_le ?_ ?_⟩
  · intro y hy
    obtain ⟨x, hx, rfl⟩ := mem_image.mp hy
    rw [Equiv.extendSubtype_apply_of_mem _ x hx]
    exact (Fintype.equivOfCardEq hcard ⟨x, hx⟩).2
  · rw [card_image_of_injective _ (Equiv.injective _), h]

/-- **Exchangeability of the roots**: the probability that a query misses the large components
depends on the query only through its size. -/
theorem graphProb_disjoint_bigSet_eq {m : ℕ} (p t : ℝ) {A B : Finset (Fin m)}
    (h : A.card = B.card) :
    graphProb m p (fun E ↦ Disjoint A (bigSet (edgeGraph E) t)) =
      graphProb m p (fun E ↦ Disjoint B (bigSet (edgeGraph E) t)) := by
  obtain ⟨σ, rfl⟩ := exists_perm_image_eq h
  symm
  rw [graphProb, graphProb, ← graphExpect_comp_mapEdges p σ]
  refine sum_congr rfl fun E _ ↦ ?_
  have hiff : Disjoint (A.image σ) (bigSet (edgeGraph (mapEdges σ E)) t) ↔
      Disjoint A (bigSet (edgeGraph E) t) := by
    rw [bigSet_mapEdges, disjoint_image σ.injective]
  by_cases hA : Disjoint A (bigSet (edgeGraph E) t)
  · rw [if_pos (hiff.mpr hA), if_pos hA]
  · rw [if_neg (mt hiff.mp hA), if_neg hA]

/-- **The `k`-subsets of the features that miss a set `S`** number `C(m - |S|, k)`. -/
theorem sum_powersetCard_indicator_disjoint {m : ℕ} (k : ℕ) (S : Finset (Fin m)) :
    ∑ B ∈ powersetCard k (univ : Finset (Fin m)), (if Disjoint B S then (1 : ℝ) else 0) =
      ((m - S.card).choose k : ℝ) := by
  rw [← natCast_card_filter]
  congr 1
  have hfilter : (powersetCard k (univ : Finset (Fin m))).filter (fun B ↦ Disjoint B S) =
      powersetCard k Sᶜ := by
    ext B
    simp only [mem_filter, mem_powersetCard, subset_univ, true_and,
      subset_compl_iff_disjoint_right]
    exact and_comm
  rw [hfilter, card_powersetCard, card_compl, Fintype.card_fin]

/-- **Averaging over the queries of size `k`.** For a query `A` of `k` features,
`C(m, k) P(A misses the large components) = E[C(m - |large|, k)]`. -/
theorem choose_mul_graphProb_disjoint_bigSet {m k : ℕ} (p t : ℝ) {A : Finset (Fin m)}
    (hA : A.card = k) :
    (m.choose k : ℝ) * graphProb m p (fun E ↦ Disjoint A (bigSet (edgeGraph E) t)) =
      graphExpect m p (fun E ↦ ((m - (bigSet (edgeGraph E) t).card).choose k : ℝ)) := by
  have hconst : ∀ B ∈ powersetCard k (univ : Finset (Fin m)),
      graphProb m p (fun E ↦ Disjoint B (bigSet (edgeGraph E) t)) =
        graphProb m p (fun E ↦ Disjoint A (bigSet (edgeGraph E) t)) :=
    fun B hB ↦ graphProb_disjoint_bigSet_eq p t ((mem_powersetCard.mp hB).2.trans hA.symm)
  have hsum : ∑ B ∈ powersetCard k (univ : Finset (Fin m)),
      graphProb m p (fun E ↦ Disjoint B (bigSet (edgeGraph E) t)) =
        (m.choose k : ℝ) * graphProb m p (fun E ↦ Disjoint A (bigSet (edgeGraph E) t)) := by
    rw [sum_congr rfl hconst, sum_const, card_powersetCard, card_univ, Fintype.card_fin,
      nsmul_eq_mul]
  rw [← hsum]
  simp only [graphProb]
  rw [← graphExpect_sum]
  refine sum_congr rfl fun E _ ↦ ?_
  rw [sum_powersetCard_indicator_disjoint]

/-! ### Ratios of binomial coefficients -/

/-- `C(n, k)/C(m, k) = n_(k)/m_(k)`. -/
theorem choose_div_choose_eq (n m k : ℕ) :
    (n.choose k : ℝ) / m.choose k = (n.descFactorial k : ℝ) / m.descFactorial k := by
  rw [Nat.descFactorial_eq_factorial_mul_choose, Nat.descFactorial_eq_factorial_mul_choose,
    Nat.cast_mul, Nat.cast_mul, mul_div_mul_left _ _ (by positivity : (k.factorial : ℝ) ≠ 0)]

/-- **Each falling factor is at most the ratio**: `n_(k) m^k ≤ n^k m_(k)` for `n ≤ m`. -/
theorem descFactorial_mul_pow_le {n m : ℕ} (h : n ≤ m) (k : ℕ) :
    n.descFactorial k * m ^ k ≤ n ^ k * m.descFactorial k := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hfac : (n - k) * m ≤ n * (m - k) := by
      rw [tsub_mul, mul_tsub]
      refine tsub_le_tsub_left ?_ _
      rw [mul_comm n k]
      exact Nat.mul_le_mul le_rfl h
    rw [Nat.descFactorial_succ, Nat.descFactorial_succ, pow_succ, pow_succ]
    calc (n - k) * n.descFactorial k * (m ^ k * m)
        = n.descFactorial k * m ^ k * ((n - k) * m) := by ring
      _ ≤ n ^ k * m.descFactorial k * (n * (m - k)) := Nat.mul_le_mul ih hfac
      _ = n ^ k * n * ((m - k) * m.descFactorial k) := by ring

/-- The descending factorial `m_(k)` is positive for `k ≤ m`. -/
theorem descFactorial_cast_pos {m k : ℕ} (hk : k ≤ m) : (0 : ℝ) < m.descFactorial k := by
  rw [Nat.descFactorial_eq_factorial_mul_choose, Nat.cast_mul]
  exact mul_pos (by positivity) (by exact_mod_cast Nat.choose_pos hk)

/-- **Drawing `k` of `m` features without replacement, all from a set of `n`**, is at most as
likely as drawing them with replacement: `C(n, k)/C(m, k) ≤ (n/m)^k` for `n ≤ m`, `k ≤ m`. -/
theorem choose_div_choose_le {n m k : ℕ} (h : n ≤ m) (hk : k ≤ m) :
    (n.choose k : ℝ) / m.choose k ≤ ((n : ℝ) / m) ^ k := by
  rcases Nat.eq_zero_or_pos m with rfl | hm0
  · obtain rfl : k = 0 := Nat.le_zero.mp hk
    simp
  have hm : (0 : ℝ) < m := Nat.cast_pos.mpr hm0
  rw [choose_div_choose_eq, div_pow, div_le_div_iff₀ (descFactorial_cast_pos hk) (pow_pos hm k)]
  exact_mod_cast descFactorial_mul_pow_le h k

/-- The lower bound `((n + 1 - k)/m)^k ≤ C(n, k)/C(m, k)` for `k ≤ m`. -/
theorem pow_le_choose_div_choose (n : ℕ) {m k : ℕ} (hk : k ≤ m) :
    (((n + 1 - k : ℕ) : ℝ) / m) ^ k ≤ (n.choose k : ℝ) / m.choose k := by
  rcases Nat.eq_zero_or_pos m with rfl | hm0
  · obtain rfl : k = 0 := Nat.le_zero.mp hk
    simp
  have hm : (0 : ℝ) < m := Nat.cast_pos.mpr hm0
  rw [choose_div_choose_eq, div_pow, div_le_div_iff₀ (pow_pos hm k) (descFactorial_cast_pos hk)]
  exact_mod_cast Nat.mul_le_mul (Nat.pow_sub_le_descFactorial n k)
    (Nat.descFactorial_le_pow m k)

/-- **The ratio is near `c^k`.** Suppose `|t - c| ≤ 2δ` forces `|t^k - c^k| ≤ η`, and
`2δ ≤ c`. If `1 - x/m` is within `δ` of `c` and `k/m ≤ δ`, then `C(m - x, k)/C(m, k)` is within
`η` of `c^k`. -/
theorem abs_choose_div_choose_sub_pow_le {m x k : ℕ} {c δ η : ℝ} (hx : x ≤ m) (hk : k ≤ m)
    (hm : 0 < m) (hc : 2 * δ ≤ c) (hmod : ∀ t : ℝ, |t - c| ≤ 2 * δ → |t ^ k - c ^ k| ≤ η)
    (hxm : |1 - (x : ℝ) / m - c| ≤ δ) (hkm : (k : ℝ) / m ≤ δ) :
    |((m - x).choose k : ℝ) / m.choose k - c ^ k| ≤ η := by
  have hm' : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  have hδ : 0 ≤ δ := (abs_nonneg _).trans hxm
  have hk0 : 0 ≤ (k : ℝ) / m := div_nonneg (Nat.cast_nonneg k) hm'.le
  have hn : ((m - x : ℕ) : ℝ) / m = 1 - (x : ℝ) / m := by
    rw [Nat.cast_sub hx, sub_div, div_self hm'.ne']
  obtain ⟨hx1, hx2⟩ := abs_le.mp hxm
  have hup : ((m - x).choose k : ℝ) / m.choose k ≤ (1 - (x : ℝ) / m) ^ k := by
    rw [← hn]
    exact choose_div_choose_le (Nat.sub_le m x) hk
  have hupmod := abs_le.mp (hmod (1 - (x : ℝ) / m) (by rw [abs_le]; constructor <;> linarith))
  have htl : (1 - (x : ℝ) / m - (k : ℝ) / m) * m = ((m - x : ℕ) : ℝ) - k := by
    rw [Nat.cast_sub hx, sub_mul, sub_mul, one_mul, div_mul_cancel₀ _ hm'.ne',
      div_mul_cancel₀ _ hm'.ne']
  have htl0 : 0 ≤ 1 - (x : ℝ) / m - (k : ℝ) / m := by linarith
  have htl_le : 1 - (x : ℝ) / m - (k : ℝ) / m ≤ ((m - x + 1 - k : ℕ) : ℝ) / m := by
    rw [le_div_iff₀ hm', htl]
    have h1 : m - x ≤ (m - x + 1 - k) + k := by omega
    have h2 : ((m - x : ℕ) : ℝ) ≤ ((m - x + 1 - k : ℕ) : ℝ) + k := by exact_mod_cast h1
    linarith
  have hlow : (1 - (x : ℝ) / m - (k : ℝ) / m) ^ k ≤ ((m - x).choose k : ℝ) / m.choose k :=
    (pow_le_pow_left₀ htl0 htl_le k).trans (pow_le_choose_div_choose (m - x) hk)
  have hlowmod := abs_le.mp (hmod (1 - (x : ℝ) / m - (k : ℝ) / m)
    (by rw [abs_le]; constructor <;> linarith))
  rw [abs_le]
  constructor <;> linarith [hupmod.1, hupmod.2, hlowmod.1, hlowmod.2]

end

end Descent.Pangenome.AncestralLocality
