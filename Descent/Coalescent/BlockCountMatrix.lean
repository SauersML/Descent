/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Coalescent.WrightFisher
import Mathlib.Tactic

assert_below Descent.Pangenome Descent.PopGen Descent.Spectral Descent.Blindness
assert_below Descent.Conditionals Descent.Portability Descent.Decision Descent.Program

namespace Descent

/-!
# Two collisions, and the `O(N⁻²)` row of the block-count matrix

`Descent.Coalescent.SemigroupLimit.tendsto_pow_of_expansion` now takes K-G (2.11)'s
hypothesis directly -- `P_N = 1 + N⁻¹Q + O(N⁻²)` -- so the many-state instantiation needs one
thing: the block-count transition matrix's rows, to that order.

Two of the three parts are already counted.  `WrightFisher.noCoalescenceProb` is the diagonal
entry exactly, and `WrightFisher.coalescenceProb_le` with `.le_coalescenceProb` put it within
`(d_k/N)²/2` of `1 - d_k/N`.  What was missing is the tail: the chance that a generation
drops TWO or more lineages, which must be `O(N⁻²)` for the expansion to hold.

The classical route is the occupancy distribution -- Stirling numbers of the second kind
times a falling factorial -- and this corpus has no Stirling numbers.  It does not need them.
A generation that drops two lineages has two DISTINCT colliding pairs, and the chance of any
one prescribed pair of pairs colliding is at most `N⁻²`, so a union bound over the
`C(C(k,2),2)` pairs of pairs finishes it.

`exists_two_collisions` is the combinatorial step, and it is shorter than the occupancy
formula it replaces.  Suppose every collision were the same pair `{a,b}`.  Then `f` restricted
to everything but `b` is injective -- a collision avoiding `b` would be a second pair -- so the
image has at least `k - 1` elements.  Contrapositive: an image of size `k - 2` or less forces
two distinct colliding pairs.

## Main results

- `injOn_erase_of_unique_collision`: if every collision is the pair `{a,b}`, then `f` is
  injective off `b`.
- `card_image_ge_of_unique_collision`: hence the image has at least `k - 1` elements.
- `exists_two_collisions`: **an image of size `≤ k - 2` gives two distinct colliding pairs**,
  which is what a union bound needs.

- `card_filter_le_of_determined`: **two determined coordinates leave `N^{k-2}` maps**.
- `card_two_collisions_le'`: hence a prescribed pair of pairs has at most `N^{k-2}` witnesses,
  disjoint or overlapping.
- `card_two_drop_le`, `twoDropProb_le`: **the tail of the row is `k⁴/N²`**, counted.

## What the union bound is

`exists_two_collisions` puts the event "this generation dropped two or more lineages" inside
the union, over the at most `k⁴` quadruples, of "both pairs collided".  `card_two_collisions_le`
bounds each of those by `N^{k-2}`, i.e. by `N^{-2}` in probability.  So the tail is `O(N⁻²)`
with a constant depending only on `k`, which is what K-G (2.11) asks of the row -- the
diagonal being `WrightFisher.noCoalescenceProb`, already within `(d_k/N)²/2` of `1 - d_k/N`.
-/

namespace Coalescent

open Finset

/-- If every collision of `f` is the single pair `{a,b}`, then `f` is injective on everything
but `b`: a collision among the rest would be a second pair. -/
theorem injOn_erase_of_unique_collision {k N : ℕ} (f : Fin k → Fin N) {a b : Fin k}
    (hab : a ≠ b)
    (huniq : ∀ x y : Fin k, x ≠ y → f x = f y → (x = a ∧ y = b) ∨ (x = b ∧ y = a)) :
    Set.InjOn f ((univ.erase b : Finset (Fin k)) : Set (Fin k)) := by
  intro x hx y hy hxy
  by_contra hne
  rcases huniq x y hne hxy with ⟨hxa, hyb⟩ | ⟨hxb, hya⟩
  · have : y ∈ univ.erase b := by simpa using hy
    exact (Finset.mem_erase.mp this).1 hyb
  · have : x ∈ univ.erase b := by simpa using hx
    exact (Finset.mem_erase.mp this).1 hxb

/-- **A single collision costs a single lineage.**  With every collision the same pair, the
image has at least `k - 1` elements. -/
theorem card_image_ge_of_unique_collision {k N : ℕ} (f : Fin k → Fin N) {a b : Fin k}
    (hab : a ≠ b)
    (huniq : ∀ x y : Fin k, x ≠ y → f x = f y → (x = a ∧ y = b) ∨ (x = b ∧ y = a)) :
    k - 1 ≤ (univ.image f).card := by
  have hinj := injOn_erase_of_unique_collision f hab huniq
  have hcard : ((univ.erase b).image f).card = (univ.erase b).card :=
    Finset.card_image_of_injOn hinj
  have hsub : (univ.erase b).image f ⊆ univ.image f :=
    Finset.image_subset_image (Finset.erase_subset _ _)
  have hle : ((univ.erase b).image f).card ≤ (univ.image f).card :=
    Finset.card_le_card hsub
  have herase : (univ.erase b : Finset (Fin k)).card = k - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ b), Finset.card_univ, Fintype.card_fin]
  rw [hcard, herase] at hle
  exact hle

/-- **Two dropped lineages mean two distinct collisions.**  The contrapositive of
`card_image_ge_of_unique_collision`, and the combinatorial content the `O(N⁻²)` tail bound
needs: the event "this generation lost two or more lineages" is contained in the union, over
pairs of distinct pairs, of "both collided", and each of those has probability at most `N⁻²`.

This replaces the occupancy distribution -- Stirling numbers times a falling factorial --
which the corpus does not have and, for the expansion K-G (2.11) asks for, does not need. -/
theorem exists_two_collisions {k N : ℕ} (f : Fin k → Fin N)
    (h : (univ.image f).card + 2 ≤ k) :
    ∃ a b c d : Fin k, a ≠ b ∧ c ≠ d ∧ f a = f b ∧ f c = f d ∧
      ¬ ((a = c ∧ b = d) ∨ (a = d ∧ b = c)) := by
  classical
  by_contra hcon
  push_neg at hcon
  -- `f` is not injective, so some collision exists
  have hnotinj : ¬ Function.Injective f := by
    intro hinj
    have : (univ.image f).card = k := by
      rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]
    omega
  obtain ⟨a, b, hfab, hab⟩ := Function.not_injective_iff.mp hnotinj
  -- every collision is that pair, by the contradiction hypothesis
  have huniq : ∀ x y : Fin k, x ≠ y → f x = f y → (x = a ∧ y = b) ∨ (x = b ∧ y = a) := by
    intro x y hxy hfxy
    rcases hcon a b x y hab hxy hfab hfxy with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨h1.symm, h2.symm⟩
    · exact Or.inr ⟨h2.symm, h1.symm⟩
  have hge := card_image_ge_of_unique_collision f hab huniq
  omega

/-! ### Two determined coordinates -/

/-- **A map with two determined coordinates is a map on `k - 2` coordinates.**  If a property
forces `f y = f u` and `f z = f v` with `u, v` outside `{y, z}`, then `f` is determined by its
values off `{y, z}`, so there are at most `N^{k-2}` such maps. -/
theorem card_filter_le_of_determined {k N : ℕ} {y z u v : Fin k} (hyz : y ≠ z)
    (huy : u ≠ y) (huz : u ≠ z) (hvy : v ≠ y) (hvz : v ≠ z)
    (p : (Fin k → Fin N) → Prop) [DecidablePred p]
    (hdet : ∀ f, p f → f y = f u ∧ f z = f v) :
    (univ.filter p).card ≤ N ^ (k - 2) := by
  classical
  have hcard : Fintype.card {x : Fin k // x ≠ y ∧ x ≠ z} = k - 2 := by
    rw [Fintype.card_subtype]
    have hfil : (univ.filter fun x : Fin k ↦ x ≠ y ∧ x ≠ z)
        = ({y, z} : Finset (Fin k))ᶜ := by
      ext x
      simp [not_or]
    rw [hfil, Finset.card_compl, Fintype.card_fin,
      Finset.card_insert_of_notMem (by simpa using hyz), Finset.card_singleton]
  have hinj : Set.InjOn (fun f : Fin k → Fin N ↦ fun x : {x : Fin k // x ≠ y ∧ x ≠ z} ↦ f x)
      ((univ.filter p : Finset (Fin k → Fin N)) : Set (Fin k → Fin N)) := by
    intro f hf g hg hfg
    have hpf : p f := (Finset.mem_filter.mp (Finset.mem_coe.mp hf)).2
    have hpg : p g := (Finset.mem_filter.mp (Finset.mem_coe.mp hg)).2
    have hagree : ∀ x : Fin k, x ≠ y → x ≠ z → f x = g x := by
      intro x hxy hxz
      exact congrFun hfg ⟨x, hxy, hxz⟩
    funext x
    by_cases hxy : x = y
    · subst hxy
      rw [(hdet f hpf).1, (hdet g hpg).1, hagree u huy huz]
    · by_cases hxz : x = z
      · subst hxz
        rw [(hdet f hpf).2, (hdet g hpg).2, hagree v hvy hvz]
      · exact hagree x hxy hxz
  have hle := Finset.card_le_card_of_injOn _ (fun _ _ ↦ Finset.mem_univ _) hinj
  refine le_trans hle ?_
  rw [Finset.card_univ, Fintype.card_fun, hcard, Fintype.card_fin]

/-- **A prescribed pair of pairs has at most `N^{k-2}` witnesses**, whether the pairs are
disjoint or share a lineage.  Disjoint: `b` and `d` are determined by `a` and `c`.  Sharing:
the two outer lineages are determined by the shared one. -/
theorem card_two_collisions_le {k N : ℕ} {a b c d : Fin k} (hab : a ≠ b) (hcd : c ≠ d)
    (hbd : b ≠ d) (hab' : a ≠ d) (hcb : c ≠ b) :
    (univ.filter fun f : Fin k → Fin N ↦ f a = f b ∧ f c = f d).card ≤ N ^ (k - 2) := by
  classical
  refine card_filter_le_of_determined (y := b) (z := d) (u := a) (v := c) hbd
    hab hab' hcb hcd _ ?_
  intro f hf
  exact ⟨hf.1.symm, hf.2.symm⟩

/-- **Every prescribed pair of distinct pairs has at most `N^{k-2}` witnesses.**  Five
configurations -- disjoint, or sharing any one of the four positions -- and in each the two
constraints determine two coordinates from two others.  Which two depends on the overlap,
which is the only reason this needs a case split at all. -/
theorem card_two_collisions_le' {k N : ℕ} {a b c d : Fin k} (hab : a ≠ b) (hcd : c ≠ d)
    (hne : ¬((a = c ∧ b = d) ∨ (a = d ∧ b = c))) :
    (univ.filter fun f : Fin k → Fin N ↦ f a = f b ∧ f c = f d).card ≤ N ^ (k - 2) := by
  classical
  by_cases hbd : b = d
  · subst hbd
    have hac : a ≠ c := fun h ↦ hne (Or.inl ⟨h, rfl⟩)
    refine card_filter_le_of_determined (y := a) (z := c) (u := b) (v := b) hac
      (Ne.symm hab) (Ne.symm hcd) (Ne.symm hab) (Ne.symm hcd) _ ?_
    intro f hf
    exact ⟨hf.1, hf.2⟩
  · by_cases had : a = d
    · subst had
      have hbc : b ≠ c := fun h ↦ hne (Or.inr ⟨rfl, h⟩)
      refine card_filter_le_of_determined (y := b) (z := c) (u := a) (v := a) hbc
        hab (Ne.symm hcd) hab (Ne.symm hcd) _ ?_
      intro f hf
      exact ⟨hf.1.symm, hf.2⟩
    · by_cases hbc : b = c
      · subst hbc
        refine card_filter_le_of_determined (y := a) (z := d) (u := b) (v := b) had
          (Ne.symm hab) hcd (Ne.symm hab) hcd _ ?_
        intro f hf
        exact ⟨hf.1, hf.2.symm⟩
      · exact card_two_collisions_le hab hcd hbd had (Ne.symm hbc)

/-! ### The union bound, and the tail of the row -/

/-- The quadruples a union bound must range over: two pairs, each a genuine pair, and
distinct as unordered pairs. -/
noncomputable def collisionQuadruples (k : ℕ) : Finset (Fin k × Fin k × Fin k × Fin k) :=
  Finset.univ.filter fun q ↦ q.1 ≠ q.2.1 ∧ q.2.2.1 ≠ q.2.2.2 ∧
    ¬((q.1 = q.2.2.1 ∧ q.2.1 = q.2.2.2) ∨ (q.1 = q.2.2.2 ∧ q.2.1 = q.2.2.1))

/-- **The tail of the block-count row is `O(N⁻²)`.**  The maps that drop two or more lineages
number at most `k⁴ N^{k-2}`, so their share of the `N^k` maps is at most `k⁴/N²`.

`exists_two_collisions` puts each such map inside one of the `≤ k⁴` two-collision events, and
`card_two_collisions_le'` bounds each event by `N^{k-2}`.  That is the last ingredient of
K-G (2.11) for the block-count chain: the diagonal is `WrightFisher.noCoalescenceProb`, within
`(d_k/N)²/2` of `1 - d_k/N`; the subdiagonal is what is left; and everything below it is
this. -/
theorem card_two_drop_le {k N : ℕ} :
    (Finset.univ.filter fun f : Fin k → Fin N ↦ (Finset.univ.image f).card + 2 ≤ k).card
      ≤ k ^ 4 * N ^ (k - 2) := by
  classical
  set inner : (Fin k × Fin k × Fin k × Fin k) → Finset (Fin k → Fin N) := fun q ↦
    Finset.univ.filter fun f ↦ f q.1 = f q.2.1 ∧ f q.2.2.1 = f q.2.2.2 with hinner
  have hsub : (Finset.univ.filter fun f : Fin k → Fin N ↦ (Finset.univ.image f).card + 2 ≤ k)
      ⊆ (collisionQuadruples k).biUnion inner := by
    intro f hf
    have hcard : (Finset.univ.image f).card + 2 ≤ k := (Finset.mem_filter.mp hf).2
    obtain ⟨a, b, c, d, hab, hcd, h1, h2, hne⟩ := exists_two_collisions f hcard
    refine Finset.mem_biUnion.mpr ⟨(a, b, c, d), ?_, ?_⟩
    · simp only [collisionQuadruples, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨hab, hcd, hne⟩
    · simp only [hinner, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨h1, h2⟩
  calc (Finset.univ.filter fun f : Fin k → Fin N ↦ (Finset.univ.image f).card + 2 ≤ k).card
      ≤ ((collisionQuadruples k).biUnion inner).card := Finset.card_le_card hsub
    _ ≤ ∑ q ∈ collisionQuadruples k, (inner q).card := Finset.card_biUnion_le
    _ ≤ ∑ _q ∈ collisionQuadruples k, N ^ (k - 2) := by
        refine Finset.sum_le_sum fun q hq ↦ ?_
        have hq' := (Finset.mem_filter.mp hq).2
        exact card_two_collisions_le' hq'.1 hq'.2.1 hq'.2.2
    _ = (collisionQuadruples k).card * N ^ (k - 2) := by
        rw [Finset.sum_const, smul_eq_mul]
    _ ≤ k ^ 4 * N ^ (k - 2) := by
        refine Nat.mul_le_mul_right _ ?_
        have hle : (collisionQuadruples k).card
            ≤ (Finset.univ : Finset (Fin k × Fin k × Fin k × Fin k)).card :=
          Finset.card_le_card (Finset.filter_subset _ _)
        simpa [Finset.card_univ, pow_succ, Nat.mul_assoc] using hle

/-- **The same as a probability: `O(N⁻²)` with a constant in `k` alone.**  Dividing by the
`N^k` parent maps, the chance a generation drops two or more of `k` lineages is at most
`k⁴/N²`.

This is the `O(N⁻²)` of K-G (2.9)-(2.11) for everything below the subdiagonal, and it is
counted rather than asserted -- as `WrightFisher.coalescenceProb_le` counts the diagonal. -/
theorem twoDropProb_le {k N : ℕ} (hN : 0 < N) (hk : 2 ≤ k) :
    ((Finset.univ.filter fun f : Fin k → Fin N ↦
        (Finset.univ.image f).card + 2 ≤ k).card : ℝ) / (N : ℝ) ^ k
      ≤ (k : ℝ) ^ 4 / (N : ℝ) ^ 2 := by
  have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hcard := card_two_drop_le (k := k) (N := N)
  have hcardR : ((Finset.univ.filter fun f : Fin k → Fin N ↦
      (Finset.univ.image f).card + 2 ≤ k).card : ℝ) ≤ (k : ℝ) ^ 4 * (N : ℝ) ^ (k - 2) := by
    exact_mod_cast hcard
  have hpow : (N : ℝ) ^ (k - 2) * (N : ℝ) ^ 2 = (N : ℝ) ^ k := by
    rw [← pow_add]
    congr 1
    omega
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  calc ((Finset.univ.filter fun f : Fin k → Fin N ↦
        (Finset.univ.image f).card + 2 ≤ k).card : ℝ) * (N : ℝ) ^ 2
      ≤ ((k : ℝ) ^ 4 * (N : ℝ) ^ (k - 2)) * (N : ℝ) ^ 2 := by
        exact mul_le_mul_of_nonneg_right hcardR (by positivity)
    _ = (k : ℝ) ^ 4 * ((N : ℝ) ^ (k - 2) * (N : ℝ) ^ 2) := by ring
    _ = (k : ℝ) ^ 4 * (N : ℝ) ^ k := by rw [hpow]

/-! ### The entries themselves -/

/-- The one-generation block-count transition probability: from `k` lineages to `j`, counted
as the share of parent maps whose image has exactly `j` elements.

Empirical status: DERIVED.  It is a count over `WrightFisher.parentAssignment`'s sample space
divided by its size, which is that event's probability under the uniform law -- the same
reading `WrightFisher.noCoalescenceProb_eq_card_ratio` makes of the diagonal. -/
noncomputable def blockTransition (N k j : ℕ) : ℝ :=
  ((Finset.univ.filter fun f : Fin k → Fin N ↦ (Finset.univ.image f).card = j).card : ℝ)
    / (N : ℝ) ^ k

/-- **The rows are probability distributions.**  Every parent map has an image of some size
between `0` and `k`, so the fibres of "image size" partition the sample space. -/
theorem sum_blockTransition {N k : ℕ} (hN : 0 < N) :
    ∑ j ∈ Finset.range (k + 1), blockTransition N k j = 1 := by
  classical
  have hNR : (0 : ℝ) < (N : ℝ) ^ k := by
    have : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
    positivity
  have hmaps : ∀ f : Fin k → Fin N, (Finset.univ.image f).card ∈ Finset.range (k + 1) := by
    intro f
    refine Finset.mem_range.mpr ?_
    have := Finset.card_image_le (s := (Finset.univ : Finset (Fin k))) (f := f)
    simp only [Finset.card_univ, Fintype.card_fin] at this
    omega
  have hpart : (Finset.univ : Finset (Fin k → Fin N)).card
      = ∑ j ∈ Finset.range (k + 1),
          (Finset.univ.filter fun f : Fin k → Fin N ↦ (Finset.univ.image f).card = j).card :=
    Finset.card_eq_sum_card_fiberwise fun f _ ↦ hmaps f
  have htotal : ((Finset.univ : Finset (Fin k → Fin N)).card : ℝ) = (N : ℝ) ^ k := by
    rw [Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]
    push_cast
    ring
  unfold blockTransition
  rw [← Finset.sum_div, ← Nat.cast_sum, ← hpart, htotal, div_self (ne_of_gt hNR)]

/-- **The diagonal entry is the counted no-coalescence probability.**  An image of size `k`
is an injective parent map, which is what `WrightFisher.noCoalescenceProb` counts -- so the
matrix's diagonal is the quantity `coalescenceProb_le` already places within `(d_k/N)²/2` of
`1 - d_k/N`. -/
theorem blockTransition_diag {N k : ℕ} (hN : 0 < N) :
    blockTransition N k k = noCoalescenceProb N k := by
  classical
  have hNR : (0 : ℝ) < (N : ℝ) ^ k := by
    have : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
    positivity
  have hfil : (Finset.univ.filter fun f : Fin k → Fin N ↦ (Finset.univ.image f).card = k)
      = Finset.univ.filter fun f : Fin k → Fin N ↦ Function.Injective f := by
    ext f
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro h
      have hinj : Set.InjOn f (Finset.univ : Finset (Fin k)) := by
        refine Finset.injOn_of_card_image_eq ?_
        rw [h, Finset.card_univ, Fintype.card_fin]
      intro x y hxy
      exact hinj (Finset.mem_coe.mpr (Finset.mem_univ x))
        (Finset.mem_coe.mpr (Finset.mem_univ y)) hxy
    · intro h
      rw [Finset.card_image_of_injective _ h, Finset.card_univ, Fintype.card_fin]
  have hcard : (Finset.univ.filter fun f : Fin k → Fin N ↦ Function.Injective f).card
      = N.descFactorial k := by
    have h := card_injective_parentMaps N k
    rw [← h, Fintype.card_subtype]
  unfold blockTransition noCoalescenceProb
  rw [hfil, hcard]

end Coalescent

end Descent
