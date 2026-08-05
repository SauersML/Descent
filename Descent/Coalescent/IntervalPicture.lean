/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Coalescent.Paintbox
import Mathlib.Tactic

namespace Descent

/-!
# Another picture of the jump chain: cuts in an interval

Kingman (1982), *The coalescent* (**K-C**), section 5, gives a second model of the jump
chain, and says why: "the essential conceptual and analytical difficulties of the coalescent
reside in the jump chain".  Take `U₁, U₂, …` and `V₁, V₂, …` independent uniform on `(0,1)`
and let

  `R_k = {(i, j) ; i = j or no V_l (l ≤ k-1) lies between U_i and U_j}`.          K-C §5

Then `|R_k| = k`, the `R_k` are nested (K-C (5.1)), and `R_k` has the paintbox law `𝒫_k`.
Removing the partitions one at a time, in descending order of `k`, lets two colours mix --
which is the merge.

Everything except the law is deterministic, and that is what is formalised here.  The
relation is the kernel of the map "which cell of the cut interval does this point fall in",
so it is an equivalence relation by construction rather than by an argument about
betweenness.  The two structural claims K-C makes -- the betweenness characterisation, and
nesting under adding a cut -- are then theorems about that map.

The randomness is not formalised: that `R_k` has law `𝒫_k` requires the uniform order
statistics of K-C's cited `[5, Section 2.8]`, and that is a claim about distributions, not
about cuts.  What is here is the combinatorial skeleton the probability sits on, and the
block count `|R_k| = k`, which K-C states as clear and which does need a hypothesis:
every cell must actually contain a ball.  With infinitely many i.i.d. uniform `U_i` that
holds almost surely, and with finitely many balls it can fail, so `blocks_intervalRel`
carries the hypothesis explicitly.

## Main results

- `cellIndex`: which cell of the cut interval a point falls in.
- `intervalRel`: K-C's `R_k`, as a kernel.
- `intervalRel_iff_no_cut_between`: it IS the betweenness relation K-C defines.
- `intervalRel_mono`: adding a cut refines -- K-C (5.1), `R_{k+1} ⊆ R_k`.
- `blocks_intervalRel`: `|R_k| = k`, given that every cell contains a ball.
-/

namespace Coalescent

open Finset

/-- How many cuts lie below a point: the index of the cell it falls in. -/
noncomputable def cellIndex (V : Finset ℝ) (u : ℝ) : ℕ := (V.filter (fun v => v < u)).card

theorem cellIndex_mono (V : Finset ℝ) {u w : ℝ} (h : u ≤ w) :
    cellIndex V u ≤ cellIndex V w := by
  classical
  refine Finset.card_le_card ?_
  intro v hv
  rw [mem_filter] at hv ⊢
  exact ⟨hv.1, lt_of_lt_of_le hv.2 h⟩

/-- The cuts strictly below `w` and not below `u` are exactly the cuts in `[u, w)`. -/
theorem filter_sdiff_filter (V : Finset ℝ) {u w : ℝ} :
    (V.filter (fun v => v < w)) \ (V.filter (fun v => v < u))
      = V.filter (fun v => u ≤ v ∧ v < w) := by
  classical
  ext v
  simp only [mem_sdiff, mem_filter, not_and, not_lt]
  constructor
  · rintro ⟨⟨hv, hvw⟩, hnot⟩
    exact ⟨hv, hnot hv, hvw⟩
  · rintro ⟨hv, huv, hvw⟩
    exact ⟨⟨hv, hvw⟩, fun _ => huv⟩

/-- Two points fall in the same cell exactly when no cut separates them. -/
theorem cellIndex_eq_iff (V : Finset ℝ) {u w : ℝ} (h : u ≤ w) :
    cellIndex V u = cellIndex V w ↔ ∀ v ∈ V, ¬ (u ≤ v ∧ v < w) := by
  classical
  have hsub : (V.filter (fun v => v < u)) ⊆ (V.filter (fun v => v < w)) := by
    intro v hv
    rw [mem_filter] at hv ⊢
    exact ⟨hv.1, lt_of_lt_of_le hv.2 h⟩
  have hcard : (V.filter (fun v => u ≤ v ∧ v < w)).card
      = cellIndex V w - cellIndex V u := by
    rw [← filter_sdiff_filter V, Finset.card_sdiff, Finset.inter_eq_left.mpr hsub]
    rfl
  constructor
  · intro heq v hv hbet
    have hzero : (V.filter (fun v => u ≤ v ∧ v < w)).card = 0 := by
      rw [hcard, heq]
      omega
    have hmem : v ∈ V.filter (fun v => u ≤ v ∧ v < w) := mem_filter.mpr ⟨hv, hbet⟩
    rw [Finset.card_eq_zero] at hzero
    simp [hzero] at hmem
  · intro hno
    have hempty : V.filter (fun v => u ≤ v ∧ v < w) = ∅ := by
      refine Finset.filter_false_of_mem ?_
      intro v hv
      exact hno v hv
    have hz : cellIndex V w - cellIndex V u = 0 := by
      rw [← hcard, hempty, Finset.card_empty]
    have := cellIndex_mono V h
    omega

/-- **K-C section 5: the relation `R_k`.**  Balls `i` and `j` are related when they fall in
the same cell of the interval cut at the points of `V`.  Building it as a kernel makes it an
equivalence relation by construction; `intervalRel_iff_no_cut_between` shows it is the
betweenness relation Kingman writes down.

Empirical status: NOT AN EMPIRICAL CLAIM.  A construction of equivalence relations from
points and cuts. -/
noncomputable def intervalRel {n : ℕ} (V : Finset ℝ) (U : Fin n → ℝ) : ER n :=
  Setoid.ker fun i => cellIndex V (U i)

/-- **The kernel is Kingman's betweenness relation.**  For balls in the given order, `i` and
`j` are related exactly when no cut lies between them. -/
theorem intervalRel_iff_no_cut_between {n : ℕ} (V : Finset ℝ) (U : Fin n → ℝ) {i j : Fin n}
    (h : U i ≤ U j) :
    (intervalRel V U).r i j ↔ ∀ v ∈ V, ¬ (U i ≤ v ∧ v < U j) :=
  cellIndex_eq_iff V h

/-- **K-C (5.1): adding a cut refines.**  `R_{k+1} ⊆ R_k`: the sequence of relations grows
coarser as the cuts are removed one by one, which is exactly the jump chain running
backwards. -/
theorem intervalRel_mono {n : ℕ} {V W : Finset ℝ} (hVW : V ⊆ W) (U : Fin n → ℝ) :
    intervalRel W U ≤ intervalRel V U := by
  classical
  intro i j hij
  rcases le_total (U i) (U j) with h | h
  · refine (cellIndex_eq_iff V h).mpr ?_
    have hW := (cellIndex_eq_iff W h).mp hij
    exact fun v hv => hW v (hVW hv)
  · have hji : (intervalRel W U).r j i := (intervalRel W U).iseqv.symm hij
    have hW := (cellIndex_eq_iff W h).mp hji
    have hV : cellIndex V (U j) = cellIndex V (U i) :=
      (cellIndex_eq_iff V h).mpr fun v hv => hW v (hVW hv)
    exact hV.symm

/-- **`|R_k| = k`.**  The blocks are the cells, so there are `|V| + 1` of them -- provided
every cell contains a ball.  K-C gets that from having infinitely many i.i.d. uniform balls,
where it holds almost surely; the hypothesis is stated here rather than assumed away,
because with finitely many balls it can fail. -/
theorem blocks_intervalRel {n : ℕ} (V : Finset ℝ) (U : Fin n → ℝ)
    (hsurj : ∀ c ≤ V.card, ∃ i : Fin n, cellIndex V (U i) = c)
    (hle : ∀ i : Fin n, cellIndex V (U i) ≤ V.card) :
    blocks (intervalRel V U) = V.card + 1 := by
  classical
  have hrange : Set.range (fun i : Fin n => cellIndex V (U i)) = {c | c ≤ V.card} := by
    ext c
    constructor
    · rintro ⟨i, rfl⟩
      exact hle i
    · intro hc
      obtain ⟨i, hi⟩ := hsurj c hc
      exact ⟨i, hi⟩
  unfold blocks intervalRel
  rw [Nat.card_congr (Setoid.quotientKerEquivRange _),
    Nat.card_congr (Equiv.setCongr hrange)]
  have hfin : {c : ℕ | c ≤ V.card} = ↑(Finset.range (V.card + 1)) := by
    ext c
    simp [Nat.lt_succ_iff]
  rw [Nat.card_congr (Equiv.setCongr hfin)]
  simp

end Coalescent

end Descent
