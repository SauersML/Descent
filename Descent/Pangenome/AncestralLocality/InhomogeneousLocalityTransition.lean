/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Pangenome.AncestralLocality.BreadthFirstDomination
import Descent.Pangenome.AncestralLocality.RandomClosure
import Mathlib.Algebra.Order.Chebyshev

assert_below Descent.PopGen Descent.Spectral Descent.Blindness Descent.Conditionals
assert_below Descent.Portability Descent.Decision Descent.Program

/-!
# The locality transition on inhomogeneous random checking graphs

Theorem 5 of the note puts the locality transition of hereditary closure at `α = 1` for the
homogeneous graph `G(m, α/m)`. Real checking graphs have hubs: a few features check many others.
This file proves the subcritical half of the transition for every random checking graph whose edges
are independent with probabilities dominated by a rank-one kernel. The threshold is the size-biased
mean weight `ν = Σ w_i² / Σ w_i`, not the mean degree.

**The model.** The features `Fin m` carry weights `w_i ≥ 0` with total `S = Σ w_i > 0`. Each
potential edge `e` is present independently with probability `q e ∈ [0, 1]` (`productExpect`, the
expectation over independent coins with probabilities `q`). The hypothesis is rank-one domination,
`q s(i, j) ≤ w_i w_j / S` (`rankOneKernel`). It covers the Chung–Lu graph
`q s(i, j) = min(1, w_i w_j / S)` (`chungLuProb`, `chungLuProb_le_rankOneKernel`), the Norros–Reittu
graph, and `G(m, α/m)` itself, the constant weight `w ≡ α` (`rankOneKernel_const`,
`graphExpect_eq_productExpect`). The weights bound the expected degrees, `E deg(i) ≤ w_i`
(`productExpect_card_adj_le`).

**The criterion.** `ν = rankOneRatio w = Σ w_i² / Σ w_i` is the mean weight at the end of a
uniformly chosen edge end, the size-biased mean weight. It is the branching number of the
rank-one graph, the analogue of `E[D(D - 1)] / E[D]` for a configuration model, and for `w ≡ α` it
is `α` (`rankOneRatio_const`). By Cauchy–Schwarz it is at least the mean weight `S / m`
(`mean_le_rankOneRatio`), so hubs raise the threshold quantity above the mean degree.

**The bound, (6.1) inhomogeneous.** For every root set `A` and every genome size,
`E|Reach(A)| ≤ |A| + (Σ_{r ∈ A} w_r) Σ_{k < m-1} ν^k` (`productExpect_card_reach_le`). No
hypothesis on `ν` is needed for this finite form. When `ν < 1` it gives
`E|Reach(A)| ≤ |A| + (Σ_{r ∈ A} w_r) / (1 - ν)`, independent of `m`
(`productExpect_card_reach_le_of_lt_one`, and `chungLu_card_reach_le_of_lt_one` for Chung–Lu).
Averaged over a uniformly chosen root, `Σ_r E|Reach(r)| ≤ m + S Σ_k ν^k`, the form
`1 + E[W] Σ_k ν^k` (`sum_productExpect_card_reach_singleton_le`). The support of the hereditary
closure of `π_A` with the degree-normalized rates obeys the same bound
(`productExpect_card_directedReach_le`). For `w ≡ α` the bound reads `|A| (1 + α Σ_k α^k)`
(`graphExpect_card_reach_le_constantWeight`), which is `|A| / (1 - α)` when `α < 1`: Theorem 5's
(6.1).

**The route** is `LocalityTransition`'s simple-path count. A present simple path of length `ℓ` from
`r` has probability the product of its edge probabilities (`productExpect_card_presentPaths`,
`prod_pathEdges_eq`), at most the rank-one weight of its step sequence. Summing over injective step
sequences is at most summing over all step sequences, whose total is the walk weight `W_ℓ(r)`
(`productExpect_card_presentPaths_le`, `sum_walkProduct_eq_walkWeight`, `walkProduct_cons`). For
`ℓ ≥ 1` that weight is `w_r ν^{ℓ-1}` (`walkWeight_succ`). Every feature reachable from `r` ends a
present simple path of length below `m`.

**Significance.** Hereditary closure of a query stays genome-size independent whenever the
size-biased weight is below one. The quantity that matters is not the mean number of checks per
feature but its size-biased version, which is at least as large: a checking graph with mean degree
below one but heavy-tailed weights can have `ν > 1`, and the homogeneous criterion would miss it.

Scope. Only the subcritical side is proved here; the supercritical upper half for `ν > 1` is not in
this file. The configuration model is not treated, since its edges are not independent; its
criterion `E[D(D - 1)] / E[D]` enters only as the analogue of `ν`. The rank-one hypothesis bounds
each edge probability separately, so kernels not dominated by a rank-one kernel, such as blocks
with a high within-block rate, are not covered. The reach is `reach` of the symmetric graph; the
hereditary closure enters through `directedReach_degreeRate`.

## Empirical status

None. The bodies are finite sums over edge sets and step sequences. The weights and edge
probabilities are supplied, and nothing is measured.
-/

namespace Descent.Pangenome.AncestralLocality

open Finset
open scoped Classical

noncomputable section

/-! ### Independent coins with unequal probabilities -/

/-- **The expectation over independent coins on `T`**, the element `e` kept with probability
`q e`. -/
def productExpect {α : Type*} [DecidableEq α] (T : Finset α) (q : α → ℝ)
    (f : Finset α → ℝ) : ℝ :=
  ∑ E ∈ T.powerset, (∏ e ∈ E, q e) * (∏ e ∈ T \ E, (1 - q e)) * f E

/-- **Equal probabilities give the random subset.** -/
theorem productExpect_const {α : Type*} [DecidableEq α] (T : Finset α) (p : ℝ)
    (f : Finset α → ℝ) : productExpect T (fun _ ↦ p) f = subsetExpect T p f := by
  simp only [productExpect, subsetExpect]
  refine sum_congr rfl fun E hE ↦ ?_
  rw [prod_const, prod_const, card_sdiff_of_subset (mem_powerset.mp hE)]

/-- **A fixed set of coins all land with probability `∏_{e ∈ S} q e`.** -/
theorem productExpect_indicator_subset {α : Type*} [DecidableEq α] {T S : Finset α}
    (q : α → ℝ) (hS : S ⊆ T) :
    productExpect T q (fun E ↦ if S ⊆ E then 1 else 0) = ∏ e ∈ S, q e := by
  have hterm : ∀ E ∈ T.powerset, (∏ e ∈ E, q e) * (∏ e ∈ T \ E, (1 - q e)) *
      (if S ⊆ E then 1 else 0) =
        (∏ e ∈ E, q e) * ∏ e ∈ T \ E, (if e ∈ S then 0 else 1 - q e) := by
    intro E _
    by_cases h : S ⊆ E
    · rw [if_pos h, mul_one]
      congr 1
      refine prod_congr rfl fun e he ↦ ?_
      rw [if_neg fun heS ↦ (mem_sdiff.mp he).2 (h heS)]
    · rw [if_neg h, mul_zero]
      obtain ⟨e, heS, heE⟩ := not_subset.mp h
      have hzero : ∏ e ∈ T \ E, (if e ∈ S then (0 : ℝ) else 1 - q e) = 0 :=
        Finset.prod_eq_zero (mem_sdiff.mpr ⟨hS heS, heE⟩) (if_pos heS)
      rw [hzero, mul_zero]
  calc productExpect T q (fun E ↦ if S ⊆ E then 1 else 0)
      = ∑ E ∈ T.powerset, (∏ e ∈ E, q e) * ∏ e ∈ T \ E, (if e ∈ S then 0 else 1 - q e) :=
        sum_congr rfl hterm
    _ = ∏ e ∈ T, (q e + if e ∈ S then 0 else 1 - q e) := (prod_add _ _ _).symm
    _ = ∏ e ∈ T, (if e ∈ S then q e else 1) :=
        prod_congr rfl fun e _ ↦ by split_ifs <;> ring
    _ = ∏ e ∈ S, q e := by rw [prod_ite_mem, inter_eq_right.mpr hS]

/-- The coins on `T` land somehow: the weights add up to one. -/
theorem productExpect_const_one {α : Type*} [DecidableEq α] (T : Finset α) (q : α → ℝ) :
    productExpect T q (fun _ ↦ 1) = 1 := by
  simpa using productExpect_indicator_subset q (empty_subset T)

/-- Expectation over independent coins is monotone when every probability lies in `[0, 1]`. -/
theorem productExpect_mono {α : Type*} [DecidableEq α] {T : Finset α} {q : α → ℝ}
    (hq0 : ∀ e ∈ T, 0 ≤ q e) (hq1 : ∀ e ∈ T, q e ≤ 1) {f g : Finset α → ℝ}
    (h : ∀ E ⊆ T, f E ≤ g E) : productExpect T q f ≤ productExpect T q g := by
  refine sum_le_sum fun E hE ↦ mul_le_mul_of_nonneg_left (h E (mem_powerset.mp hE)) ?_
  exact mul_nonneg (prod_nonneg fun e he ↦ hq0 e (mem_powerset.mp hE he))
    (prod_nonneg fun e he ↦ sub_nonneg.mpr (hq1 e (mem_sdiff.mp he).1))

/-- Expectation over independent coins commutes with finite sums. -/
theorem productExpect_sum {α ι : Type*} [DecidableEq α] (T : Finset α) (q : α → ℝ)
    (s : Finset ι) (f : ι → Finset α → ℝ) :
    productExpect T q (fun E ↦ ∑ i ∈ s, f i E) = ∑ i ∈ s, productExpect T q (f i) := by
  simp only [productExpect, mul_sum]
  exact sum_comm

/-- **`G(m, p)` is the inhomogeneous graph with every edge probability `p`.** -/
theorem graphExpect_eq_productExpect (m : ℕ) (p : ℝ) (f : Finset (Sym2 (Fin m)) → ℝ) :
    graphExpect m p f = productExpect (potentialEdges m) (fun _ ↦ p) f := by
  rw [productExpect_const, graphExpect_eq_subsetExpect]

/-! ### Rank-one weights -/

/-- **The rank-one kernel** `κ(i, j) = w_i w_j / S`, `S = Σ w_k`. -/
def rankOneKernel {m : ℕ} (w : Fin m → ℝ) (i j : Fin m) : ℝ :=
  w i * w j / ∑ k, w k

/-- **The size-biased mean weight** `ν = Σ w_i² / Σ w_i`, the branching number of a rank-one
checking graph. -/
def rankOneRatio {m : ℕ} (w : Fin m → ℝ) : ℝ :=
  (∑ i, w i ^ 2) / ∑ i, w i

/-- The rank-one kernel is nonnegative for nonnegative weights. -/
theorem rankOneKernel_nonneg {m : ℕ} {w : Fin m → ℝ} (hw : ∀ i, 0 ≤ w i) (i j : Fin m) :
    0 ≤ rankOneKernel w i j :=
  div_nonneg (mul_nonneg (hw i) (hw j)) (sum_nonneg fun k _ ↦ hw k)

/-- **Constant weight `α` is `G(m, α/m)`**: the kernel is `α / m`. -/
theorem rankOneKernel_const {m : ℕ} (hm : 0 < m) {α : ℝ} (hα : α ≠ 0) (i j : Fin m) :
    rankOneKernel (fun _ : Fin m ↦ α) i j = α / m := by
  have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  simp only [rankOneKernel, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [div_eq_div_iff (mul_ne_zero hm' hα) hm']
  ring

/-- **Constant weight `α` has branching number `α`.** -/
theorem rankOneRatio_const {m : ℕ} (hm : 0 < m) {α : ℝ} (hα : α ≠ 0) :
    rankOneRatio (fun _ : Fin m ↦ α) = α := by
  have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  simp only [rankOneRatio, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [div_eq_iff (mul_ne_zero hm' hα)]
  ring

/-- **The branching number is at least the mean weight**: `S / m ≤ ν`, by Cauchy–Schwarz. -/
theorem mean_le_rankOneRatio {m : ℕ} {w : Fin m → ℝ} (hS : 0 < ∑ i, w i) :
    (∑ i, w i) / m ≤ rankOneRatio w := by
  have hm : (0 : ℝ) < m := by
    rcases Nat.eq_zero_or_pos m with rfl | h
    · simp at hS
    · exact_mod_cast h
  have h := sq_sum_le_card_mul_sum_sq (s := (univ : Finset (Fin m))) (f := w)
  rw [card_univ, Fintype.card_fin] at h
  rw [rankOneRatio, div_le_div_iff₀ hm hS]
  nlinarith [h]

/-- **The Chung–Lu edge probability** `min(1, w_i w_j / S)`. -/
def chungLuProb {m : ℕ} (w : Fin m → ℝ) : Sym2 (Fin m) → ℝ :=
  Sym2.lift ⟨fun i j ↦ min 1 (rankOneKernel w i j), fun i j ↦ by
    show min 1 (rankOneKernel w i j) = min 1 (rankOneKernel w j i)
    rw [rankOneKernel, rankOneKernel, mul_comm (w i)]⟩

/-- The Chung–Lu probability of the pair `{i, j}`. -/
theorem chungLuProb_mk {m : ℕ} (w : Fin m → ℝ) (i j : Fin m) :
    chungLuProb w s(i, j) = min 1 (rankOneKernel w i j) :=
  rfl

/-- Chung–Lu probabilities are nonnegative for nonnegative weights. -/
theorem chungLuProb_nonneg {m : ℕ} {w : Fin m → ℝ} (hw : ∀ i, 0 ≤ w i) (e : Sym2 (Fin m)) :
    0 ≤ chungLuProb w e :=
  Sym2.ind (fun i j ↦ le_min zero_le_one (rankOneKernel_nonneg hw i j)) e

/-- Chung–Lu probabilities are at most one. -/
theorem chungLuProb_le_one {m : ℕ} (w : Fin m → ℝ) (e : Sym2 (Fin m)) : chungLuProb w e ≤ 1 :=
  Sym2.ind (fun i j ↦ min_le_left 1 (rankOneKernel w i j)) e

/-- **Chung–Lu is dominated by its rank-one kernel.** -/
theorem chungLuProb_le_rankOneKernel {m : ℕ} (w : Fin m → ℝ) (i j : Fin m) :
    chungLuProb w s(i, j) ≤ rankOneKernel w i j :=
  min_le_right 1 (rankOneKernel w i j)

/-- **The weights bound the expected degrees**: under rank-one domination the expected number of
neighbours of `i` is at most `w_i`. -/
theorem productExpect_card_adj_le {m : ℕ} {q : Sym2 (Fin m) → ℝ} {w : Fin m → ℝ}
    (hw : ∀ i, 0 ≤ w i) (hS : 0 < ∑ k, w k)
    (hq : ∀ i j, i ≠ j → q s(i, j) ≤ rankOneKernel w i j) (i : Fin m) :
    productExpect (potentialEdges m) q
        (fun E ↦ ((univ.filter fun j ↦ (edgeGraph E).Adj i j).card : ℝ)) ≤ w i := by
  have hcount : ∀ E : Finset (Sym2 (Fin m)),
      ((univ.filter fun j ↦ (edgeGraph E).Adj i j).card : ℝ) =
        ∑ j ∈ univ.erase i, if ({s(i, j)} : Finset (Sym2 (Fin m))) ⊆ E then 1 else 0 := by
    intro E
    have hfilter : (univ.filter fun j ↦ (edgeGraph E).Adj i j) =
        (univ.erase i).filter fun j ↦ ({s(i, j)} : Finset (Sym2 (Fin m))) ⊆ E := by
      ext j
      simp only [mem_filter, mem_univ, true_and, and_true, mem_erase, edgeGraph_adj_iff,
        singleton_subset_iff]
      exact ⟨fun ⟨h1, h2⟩ ↦ ⟨h2.symm, h1⟩, fun ⟨h1, h2⟩ ↦ ⟨h2, h1.symm⟩⟩
    rw [hfilter, natCast_card_filter]
  simp only [hcount]
  rw [productExpect_sum]
  calc ∑ j ∈ univ.erase i, productExpect (potentialEdges m) q
        (fun E ↦ if ({s(i, j)} : Finset (Sym2 (Fin m))) ⊆ E then 1 else 0)
      = ∑ j ∈ univ.erase i, q s(i, j) := by
        refine sum_congr rfl fun j hj ↦ ?_
        have hij : s(i, j) ∈ potentialEdges m := by
          rw [mem_potentialEdges_iff, Sym2.mk_isDiag_iff]
          exact (mem_erase.mp hj).1.symm
        rw [productExpect_indicator_subset q (singleton_subset_iff.mpr hij), prod_singleton]
    _ ≤ ∑ j ∈ univ.erase i, rankOneKernel w i j :=
        sum_le_sum fun j hj ↦ hq i j (mem_erase.mp hj).1.symm
    _ ≤ ∑ j, rankOneKernel w i j :=
        sum_le_sum_of_subset_of_nonneg (erase_subset _ _) fun j _ _ ↦ rankOneKernel_nonneg hw i j
    _ = (w i / ∑ k, w k) * ∑ j, w j := by
        rw [mul_sum]
        exact sum_congr rfl fun j _ ↦ by rw [rankOneKernel]; ring
    _ = w i := div_mul_cancel₀ (w i) hS.ne'

/-! ### Step sequences and their weights -/

/-- The vertex sequence `r, u 0, …, u (ℓ - 1)` of a step sequence from `r`. -/
def walkVertex {m ℓ : ℕ} (r : Fin m) (u : Fin ℓ → Fin m) : Fin (ℓ + 1) → Fin m :=
  Fin.cons r u

/-- **The rank-one weight of a step sequence**: the product of the kernel over its steps. -/
def walkProduct {m ℓ : ℕ} (w : Fin m → ℝ) (r : Fin m) (u : Fin ℓ → Fin m) : ℝ :=
  ∏ t : Fin ℓ, rankOneKernel w (walkVertex r u t.castSucc) (walkVertex r u t.succ)

/-- **The walk weight** `W_ℓ(r)`, defined by one step: `W_0 = 1` and
`W_{ℓ+1}(r) = Σ_u κ(r, u) W_ℓ(u)`. -/
def walkWeight {m : ℕ} (w : Fin m → ℝ) : ℕ → Fin m → ℝ
  | 0, _ => 1
  | ℓ + 1, r => ∑ u, rankOneKernel w r u * walkWeight w ℓ u

/-- **A step sequence splits at its first step.** -/
theorem walkProduct_cons {m ℓ : ℕ} (w : Fin m → ℝ) (r a : Fin m) (u : Fin ℓ → Fin m) :
    walkProduct w r (Fin.cons a u : Fin (ℓ + 1) → Fin m) =
      rankOneKernel w r a * walkProduct w a u := by
  simp only [walkProduct, walkVertex, Fin.prod_univ_succ, Fin.castSucc_zero, Fin.cons_zero,
    Fin.cons_succ, Fin.castSucc_succ]

/-- **The step sequences from `r` carry the walk weight**: `Σ_u Π_t κ(u_t, u_{t+1}) = W_ℓ(r)`. -/
theorem sum_walkProduct_eq_walkWeight {m : ℕ} (w : Fin m → ℝ) (ℓ : ℕ) :
    ∀ r : Fin m, ∑ u : Fin ℓ → Fin m, walkProduct w r u = walkWeight w ℓ r := by
  induction ℓ with
  | zero =>
    intro r
    simp [walkProduct, walkWeight]
  | succ ℓ ih =>
    intro r
    rw [← (Fin.consEquiv fun _ : Fin (ℓ + 1) ↦ Fin m).sum_comp, Fintype.sum_prod_type]
    show ∑ a, ∑ u, walkProduct w r (Fin.cons a u : Fin (ℓ + 1) → Fin m) =
      ∑ a, rankOneKernel w r a * walkWeight w ℓ a
    refine sum_congr rfl fun a _ ↦ ?_
    rw [← ih a, mul_sum]
    exact sum_congr rfl fun u _ ↦ walkProduct_cons w r a u

/-- **The walk weight of a rank-one kernel**: `W_{ℓ+1}(r) = w_r ν^ℓ`. -/
theorem walkWeight_succ {m : ℕ} {w : Fin m → ℝ} (hS : ∑ i, w i ≠ 0) (ℓ : ℕ) :
    ∀ r : Fin m, walkWeight w (ℓ + 1) r = w r * rankOneRatio w ^ ℓ := by
  induction ℓ with
  | zero =>
    intro r
    show ∑ u, rankOneKernel w r u * walkWeight w 0 u = w r * rankOneRatio w ^ 0
    simp only [walkWeight, mul_one, pow_zero]
    calc ∑ u, rankOneKernel w r u = (w r / ∑ i, w i) * ∑ u, w u := by
          rw [mul_sum]
          exact sum_congr rfl fun u _ ↦ by rw [rankOneKernel]; ring
      _ = w r := div_mul_cancel₀ (w r) hS
  | succ ℓ ih =>
    intro r
    show ∑ u, rankOneKernel w r u * walkWeight w (ℓ + 1) u = w r * rankOneRatio w ^ (ℓ + 1)
    simp only [ih]
    calc ∑ u, rankOneKernel w r u * (w u * rankOneRatio w ^ ℓ)
        = (w r * rankOneRatio w ^ ℓ / ∑ i, w i) * ∑ u, w u ^ 2 := by
          rw [mul_sum]
          exact sum_congr rfl fun u _ ↦ by rw [rankOneKernel]; ring
      _ = w r * rankOneRatio w ^ (ℓ + 1) := by
          rw [pow_succ, rankOneRatio]
          ring

/-! ### Present simple paths -/

/-- The step map of a simple path is injective: distinct steps are distinct edges. -/
theorem pathStep_injective {m ℓ : ℕ} (r : Fin m) (f : Fin ℓ ↪ {v : Fin m // v ≠ r}) :
    Function.Injective fun t : Fin ℓ ↦ s(pathVertex r f t.castSucc, pathVertex r f t.succ) := by
  intro t u htu
  have hv := pathVertex_injective r f
  rcases Sym2.eq_iff.mp htu with ⟨h1, -⟩ | ⟨h1, h2⟩
  · exact Fin.castSucc_injective ℓ (hv h1)
  · have e1 := congrArg Fin.val (hv h1)
    have e2 := congrArg Fin.val (hv h2)
    simp only [Fin.coe_castSucc, Fin.val_succ] at e1 e2
    omega

/-- **The edge product of a simple path is the product over its steps.** -/
theorem prod_pathEdges_eq {m ℓ : ℕ} (q : Sym2 (Fin m) → ℝ) (r : Fin m)
    (f : Fin ℓ ↪ {v : Fin m // v ≠ r}) :
    ∏ e ∈ pathEdges r f, q e =
      ∏ t : Fin ℓ, q s(pathVertex r f t.castSucc, pathVertex r f t.succ) := by
  rw [pathEdges, prod_image fun t _ u _ htu ↦ pathStep_injective r f htu]

/-- **The expected number of present simple paths** of length `ℓ` from `r` is the sum, over the
simple paths, of the products of their edge probabilities. -/
theorem productExpect_card_presentPaths {m : ℕ} (q : Sym2 (Fin m) → ℝ) (r : Fin m) (ℓ : ℕ) :
    productExpect (potentialEdges m) q (fun E ↦ ((presentPaths E r ℓ).card : ℝ)) =
      ∑ f : Fin ℓ ↪ {v : Fin m // v ≠ r},
        ∏ t : Fin ℓ, q s(pathVertex r f t.castSucc, pathVertex r f t.succ) := by
  have hcard : ∀ E : Finset (Sym2 (Fin m)), ((presentPaths E r ℓ).card : ℝ) =
      ∑ f : Fin ℓ ↪ {v : Fin m // v ≠ r}, if pathEdges r f ⊆ E then 1 else 0 :=
    fun E ↦ natCast_card_filter _ _
  simp only [hcard]
  rw [productExpect_sum]
  exact sum_congr rfl fun f _ ↦ by
    rw [productExpect_indicator_subset q (pathEdges_subset r f), prod_pathEdges_eq]

/-- **Rank-one domination of the present simple paths**: the expected number of present simple
paths of length `ℓ` from `r` is at most the walk weight `W_ℓ(r)`. -/
theorem productExpect_card_presentPaths_le {m : ℕ} {q : Sym2 (Fin m) → ℝ} {w : Fin m → ℝ}
    (hq0 : ∀ e, 0 ≤ q e) (hw : ∀ i, 0 ≤ w i)
    (hq : ∀ i j, i ≠ j → q s(i, j) ≤ rankOneKernel w i j) (r : Fin m) (ℓ : ℕ) :
    productExpect (potentialEdges m) q (fun E ↦ ((presentPaths E r ℓ).card : ℝ)) ≤
      walkWeight w ℓ r := by
  rw [productExpect_card_presentPaths, ← sum_walkProduct_eq_walkWeight]
  have hinj : Function.Injective fun f : Fin ℓ ↪ {v : Fin m // v ≠ r} ↦
      fun t ↦ (f t : Fin m) :=
    fun f g hfg ↦ Function.Embedding.ext fun t ↦ Subtype.ext (congrFun hfg t)
  have himage : ∑ f : Fin ℓ ↪ {v : Fin m // v ≠ r}, walkProduct w r (fun t ↦ (f t : Fin m)) =
      ∑ u ∈ univ.image (fun f : Fin ℓ ↪ {v : Fin m // v ≠ r} ↦ fun t ↦ (f t : Fin m)),
        walkProduct w r u :=
    (sum_image fun f _ g _ hfg ↦ hinj hfg).symm
  calc ∑ f : Fin ℓ ↪ {v : Fin m // v ≠ r},
        ∏ t : Fin ℓ, q s(pathVertex r f t.castSucc, pathVertex r f t.succ)
      ≤ ∑ f : Fin ℓ ↪ {v : Fin m // v ≠ r}, walkProduct w r (fun t ↦ (f t : Fin m)) :=
        sum_le_sum fun f _ ↦ prod_le_prod (fun t _ ↦ hq0 _) fun t _ ↦
          hq _ _ ((pathVertex_injective r f).ne (Fin.castSucc_lt_succ t).ne)
    _ ≤ ∑ u : Fin ℓ → Fin m, walkProduct w r u := by
        rw [himage]
        exact sum_le_sum_of_subset_of_nonneg (subset_univ _) fun u _ _ ↦
          prod_nonneg fun t _ ↦ rankOneKernel_nonneg hw _ _

/-! ### The subcritical bound -/

/-- **The reach of one root in a rank-one checking graph**:
`E|Reach(r)| ≤ 1 + w_r Σ_{k < m-1} ν^k`. -/
theorem productExpect_card_reach_singleton_le {m : ℕ} {q : Sym2 (Fin m) → ℝ} {w : Fin m → ℝ}
    (hq0 : ∀ e, 0 ≤ q e) (hq1 : ∀ e, q e ≤ 1) (hw : ∀ i, 0 ≤ w i) (hS : 0 < ∑ i, w i)
    (hq : ∀ i j, i ≠ j → q s(i, j) ≤ rankOneKernel w i j) (r : Fin m) :
    productExpect (potentialEdges m) q (fun E ↦ ((reach (edgeGraph E) {r}).card : ℝ)) ≤
      1 + w r * ∑ k ∈ range (m - 1), rankOneRatio w ^ k := by
  calc productExpect (potentialEdges m) q (fun E ↦ ((reach (edgeGraph E) {r}).card : ℝ))
      ≤ productExpect (potentialEdges m) q
          (fun E ↦ ∑ ℓ ∈ range m, ((presentPaths E r ℓ).card : ℝ)) :=
        productExpect_mono (fun e _ ↦ hq0 e) (fun e _ ↦ hq1 e) fun E _ ↦
          card_reach_singleton_le_sum E r
    _ = ∑ ℓ ∈ range m, productExpect (potentialEdges m) q
          (fun E ↦ ((presentPaths E r ℓ).card : ℝ)) :=
        productExpect_sum _ _ _ _
    _ ≤ ∑ ℓ ∈ range m, walkWeight w ℓ r :=
        sum_le_sum fun ℓ _ ↦ productExpect_card_presentPaths_le hq0 hw hq r ℓ
    _ = 1 + w r * ∑ k ∈ range (m - 1), rankOneRatio w ^ k := by
        obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, (Nat.succ_pred_eq_of_pos r.pos).symm⟩
        rw [sum_range_succ', Nat.add_sub_cancel]
        simp only [walkWeight_succ hS.ne']
        rw [show walkWeight w 0 r = 1 from rfl, mul_sum, add_comm]

/-- **(6.1), inhomogeneous, in finite form.** In a rank-one checking graph,
`E|Reach(A)| ≤ |A| + (Σ_{r ∈ A} w_r) Σ_{k < m-1} ν^k` for every root set `A`. -/
theorem productExpect_card_reach_le {m : ℕ} {q : Sym2 (Fin m) → ℝ} {w : Fin m → ℝ}
    (hq0 : ∀ e, 0 ≤ q e) (hq1 : ∀ e, q e ≤ 1) (hw : ∀ i, 0 ≤ w i) (hS : 0 < ∑ i, w i)
    (hq : ∀ i j, i ≠ j → q s(i, j) ≤ rankOneKernel w i j) (A : Finset (Fin m)) :
    productExpect (potentialEdges m) q (fun E ↦ ((reach (edgeGraph E) A).card : ℝ)) ≤
      A.card + (∑ r ∈ A, w r) * ∑ k ∈ range (m - 1), rankOneRatio w ^ k := by
  calc productExpect (potentialEdges m) q (fun E ↦ ((reach (edgeGraph E) A).card : ℝ))
      ≤ productExpect (potentialEdges m) q
          (fun E ↦ ∑ r ∈ A, ((reach (edgeGraph E) {r}).card : ℝ)) :=
        productExpect_mono (fun e _ ↦ hq0 e) (fun e _ ↦ hq1 e) fun E _ ↦ by
          exact_mod_cast card_reach_le_sum (edgeGraph E) A
    _ = ∑ r ∈ A, productExpect (potentialEdges m) q
          (fun E ↦ ((reach (edgeGraph E) {r}).card : ℝ)) :=
        productExpect_sum _ _ _ _
    _ ≤ ∑ r ∈ A, (1 + w r * ∑ k ∈ range (m - 1), rankOneRatio w ^ k) :=
        sum_le_sum fun r _ ↦ productExpect_card_reach_singleton_le hq0 hq1 hw hS hq r
    _ = A.card + (∑ r ∈ A, w r) * ∑ k ∈ range (m - 1), rankOneRatio w ^ k := by
        rw [sum_add_distrib, sum_const, nsmul_eq_mul, mul_one, sum_mul]

/-- **(6.1), inhomogeneous.** In a rank-one checking graph with `ν < 1`,
`E|Reach(A)| ≤ |A| + (Σ_{r ∈ A} w_r) / (1 - ν)`, independent of the genome size. -/
theorem productExpect_card_reach_le_of_lt_one {m : ℕ} {q : Sym2 (Fin m) → ℝ} {w : Fin m → ℝ}
    (hq0 : ∀ e, 0 ≤ q e) (hq1 : ∀ e, q e ≤ 1) (hw : ∀ i, 0 ≤ w i) (hS : 0 < ∑ i, w i)
    (hq : ∀ i j, i ≠ j → q s(i, j) ≤ rankOneKernel w i j) (hν : rankOneRatio w < 1)
    (A : Finset (Fin m)) :
    productExpect (potentialEdges m) q (fun E ↦ ((reach (edgeGraph E) A).card : ℝ)) ≤
      A.card + (∑ r ∈ A, w r) / (1 - rankOneRatio w) := by
  have hν0 : 0 ≤ rankOneRatio w := div_nonneg (sum_nonneg fun i _ ↦ sq_nonneg (w i)) hS.le
  have hgeom : ∑ k ∈ range (m - 1), rankOneRatio w ^ k ≤ 1 / (1 - rankOneRatio w) := by
    have h := geom_sum_Ico_le_of_lt_one hν0 hν (m := 0) (n := m - 1)
    rwa [← range_eq_Ico, pow_zero] at h
  have hwA : 0 ≤ ∑ r ∈ A, w r := sum_nonneg fun r _ ↦ hw r
  calc productExpect (potentialEdges m) q (fun E ↦ ((reach (edgeGraph E) A).card : ℝ))
      ≤ A.card + (∑ r ∈ A, w r) * ∑ k ∈ range (m - 1), rankOneRatio w ^ k :=
        productExpect_card_reach_le hq0 hq1 hw hS hq A
    _ ≤ A.card + (∑ r ∈ A, w r) * (1 / (1 - rankOneRatio w)) :=
        add_le_add_left (mul_le_mul_of_nonneg_left hgeom hwA) _
    _ = A.card + (∑ r ∈ A, w r) / (1 - rankOneRatio w) := by rw [mul_one_div]

/-- **Averaged over the roots**: `Σ_r E|Reach(r)| ≤ m + S Σ_{k < m-1} ν^k`, so a uniformly chosen
root has `E|Reach| ≤ 1 + E[W] Σ_k ν^k`. -/
theorem sum_productExpect_card_reach_singleton_le {m : ℕ} {q : Sym2 (Fin m) → ℝ}
    {w : Fin m → ℝ} (hq0 : ∀ e, 0 ≤ q e) (hq1 : ∀ e, q e ≤ 1) (hw : ∀ i, 0 ≤ w i)
    (hS : 0 < ∑ i, w i) (hq : ∀ i j, i ≠ j → q s(i, j) ≤ rankOneKernel w i j) :
    ∑ r : Fin m, productExpect (potentialEdges m) q
        (fun E ↦ ((reach (edgeGraph E) {r}).card : ℝ)) ≤
      m + (∑ i, w i) * ∑ k ∈ range (m - 1), rankOneRatio w ^ k := by
  calc ∑ r : Fin m, productExpect (potentialEdges m) q
        (fun E ↦ ((reach (edgeGraph E) {r}).card : ℝ))
      ≤ ∑ r : Fin m, (1 + w r * ∑ k ∈ range (m - 1), rankOneRatio w ^ k) :=
        sum_le_sum fun r _ ↦ productExpect_card_reach_singleton_le hq0 hq1 hw hS hq r
    _ = m + (∑ i, w i) * ∑ k ∈ range (m - 1), rankOneRatio w ^ k := by
        rw [sum_add_distrib, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one,
          sum_mul]

/-- **The hereditary closure obeys the same bound.** With the degree-normalized rates of §6.1 on
the present edges, the support of the hereditary closure of `π_A` in a rank-one checking graph has
`E|Reach_G(A)| ≤ |A| + (Σ_{r ∈ A} w_r) Σ_{k < m-1} ν^k`. -/
theorem productExpect_card_directedReach_le {m : ℕ} {q : Sym2 (Fin m) → ℝ} {w : Fin m → ℝ}
    (hq0 : ∀ e, 0 ≤ q e) (hq1 : ∀ e, q e ≤ 1) (hw : ∀ i, 0 ≤ w i) (hS : 0 < ∑ i, w i)
    (hq : ∀ i j, i ≠ j → q s(i, j) ≤ rankOneKernel w i j) {β : ℝ} (hβ : 0 < β)
    (A : Finset (Fin m)) :
    productExpect (potentialEdges m) q
        (fun E ↦ ((directedReach (degreeRate (edgeGraph E) β) A).card : ℝ)) ≤
      A.card + (∑ r ∈ A, w r) * ∑ k ∈ range (m - 1), rankOneRatio w ^ k := by
  simp only [directedReach_degreeRate _ hβ]
  exact productExpect_card_reach_le hq0 hq1 hw hS hq A

/-- **The Chung–Lu graph with `ν < 1` is local**:
`E|Reach(A)| ≤ |A| + (Σ_{r ∈ A} w_r) / (1 - ν)`. -/
theorem chungLu_card_reach_le_of_lt_one {m : ℕ} {w : Fin m → ℝ} (hw : ∀ i, 0 ≤ w i)
    (hS : 0 < ∑ i, w i) (hν : rankOneRatio w < 1) (A : Finset (Fin m)) :
    productExpect (potentialEdges m) (chungLuProb w)
        (fun E ↦ ((reach (edgeGraph E) A).card : ℝ)) ≤
      A.card + (∑ r ∈ A, w r) / (1 - rankOneRatio w) :=
  productExpect_card_reach_le_of_lt_one (chungLuProb_nonneg hw) (chungLuProb_le_one w) hw hS
    (fun i j _ ↦ chungLuProb_le_rankOneKernel w i j) hν A

/-- **Theorem 5's (6.1) is the constant-weight case**: in `G(m, α/m)`, the constant weight `α` gives
`E|Reach(A)| ≤ |A| + |A| α Σ_{k < m-1} α^k`. -/
theorem graphExpect_card_reach_le_constantWeight {m : ℕ} {α : ℝ} (hm : 0 < m) (hα0 : 0 < α)
    (hαm : α ≤ m) (A : Finset (Fin m)) :
    graphExpect m (α / m) (fun E ↦ ((reach (edgeGraph E) A).card : ℝ)) ≤
      A.card + A.card * α * ∑ k ∈ range (m - 1), α ^ k := by
  have hm' : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  have hS : 0 < ∑ _i : Fin m, α := by
    rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
    exact mul_pos hm' hα0
  have h := productExpect_card_reach_le (q := fun _ ↦ α / m) (w := fun _ ↦ α)
    (fun _ ↦ div_nonneg hα0.le hm'.le) (fun _ ↦ (div_le_one hm').mpr hαm) (fun _ ↦ hα0.le) hS
    (fun i j _ ↦ (rankOneKernel_const hm hα0.ne' i j).ge) A
  rw [rankOneRatio_const hm hα0.ne', sum_const, nsmul_eq_mul] at h
  rw [graphExpect_eq_productExpect]
  exact h

end

end Descent.Pangenome.AncestralLocality
