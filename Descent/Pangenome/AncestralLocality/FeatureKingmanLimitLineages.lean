/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Pangenome.AncestralLocality.FeatureKingmanLimit

assert_below Descent.PopGen Descent.Spectral Descent.Blindness Descent.Conditionals
assert_below Descent.Portability Descent.Decision Descent.Program

/-!
# The single-feature Kingman limit for many lineages

The spec is `ANCESTRAL_LOCALITY.md` §4.1. `FeatureKingmanLimit` traces two lineages at one feature
`k` through the finite-population chain (4.5); this file traces `n` of them for one generation
and reads off the rates of the block-counting chain.

**Sources of `n` lineages.** The sources at `k` of `n` distinct offspring of one generation are
independent and uniform on the `N` parents, whatever the checking graph and the parental genomes:
`sum_prod_mul_comp_injective` is the `n`-coordinate marginal of a product law, and
`sum_prod_annotatedLaw_sources` sums out the genomes. So the block count after one generation, the
number of distinct sources, has the law `blockTransition N n` (`sum_prod_annotatedLaw_blockCount`,
`sum_prod_annotatedLaw_blockTransition`).

**Merging within a generation.** No two lineages merge with probability `∏_{i<n} (1 - i/N)`
(`blockTransition_self`). With the product bounds `1 - Σ x_i ≤ ∏ (1 - x_i) ≤ 1 - Σ x_i + (Σ x_i)²/2`
(`one_sub_sum_le_prod_range`, `prod_range_le_one_sub_add_sq`) and `Σ_{i<n} i = C(n,2)`
(`sum_range_cast_eq_choose_two`), some pair merges with probability `C(n,2)/N + O(1/N²)`, with the
explicit error `(C(n,2)/N)²/2` (`abs_blockMergeProb_sub_le`). The block count falls by two or more
with probability at most `(C(n,2)/N)²/2` (`blockMultiMergeProb_le`), through the mean image size
`N (1 - (1 - 1/N)^n)` (`sum_uniformSources_card_image`) and `(1 - x)^n ≤ 1 - nx + C(n,2) x²`
(`one_sub_pow_le_choose_two`).

**Kingman's rates.** On the time scale of `N` generations the block-counting chain has Kingman's
rates in the limit: `N · P(some merger) → C(n,2)` (`tendsto_mul_blockMergeProb`),
`N · P(n → n - 1) → C(n,2)` (`tendsto_mul_blockTransition_pred`), and `N · P(n → b) → 0` for
`b ≤ n - 2` (`tendsto_mul_blockTransition_of_add_two_le`).

Scope. The transition law is for one generation from `n` lineages at distinct offspring; the
multi-generation block-counting chain, its Markov property across generations and the convergence
of its paths to Kingman's coalescent are not constructed. The limit statements concern the
generator, the one-step probabilities scaled by `N`.

## Empirical status

None. The bodies here are finite sums of products of indicators and real limits; no measurement
can bear on them.
-/

namespace Descent.Pangenome.AncestralLocality

open Finset Filter
open scoped Topology

noncomputable section

/-! ### Product bounds -/

/-- **The Weierstrass product inequality**: `1 - Σ_{i<n} x_i ≤ ∏_{i<n} (1 - x_i)` for
`0 ≤ x_i ≤ 1`. -/
theorem one_sub_sum_le_prod_range (x : ℕ → ℝ) (n : ℕ) (h0 : ∀ i < n, 0 ≤ x i)
    (h1 : ∀ i < n, x i ≤ 1) : 1 - ∑ i ∈ range n, x i ≤ ∏ i ∈ range n, (1 - x i) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have ih' := ih (fun i hi ↦ h0 i (by omega)) (fun i hi ↦ h1 i (by omega))
    have hS : 0 ≤ ∑ i ∈ range n, x i :=
      sum_nonneg fun i hi ↦ h0 i (by have := mem_range.mp hi; omega)
    have hx0 : 0 ≤ x n := h0 n (by omega)
    have hx1 : 0 ≤ 1 - x n := by linarith [h1 n (by omega)]
    rw [sum_range_succ, prod_range_succ]
    nlinarith [mul_le_mul_of_nonneg_right ih' hx1, mul_nonneg hS hx0]

/-- **The second Bonferroni product bound**: `∏_{i<n} (1 - x_i) ≤ 1 - Σ x_i + (Σ x_i)²/2` for
`0 ≤ x_i ≤ 1`. -/
theorem prod_range_le_one_sub_add_sq (x : ℕ → ℝ) (n : ℕ) (h0 : ∀ i < n, 0 ≤ x i)
    (h1 : ∀ i < n, x i ≤ 1) :
    ∏ i ∈ range n, (1 - x i) ≤ 1 - ∑ i ∈ range n, x i + (∑ i ∈ range n, x i) ^ 2 / 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    have ih' := ih (fun i hi ↦ h0 i (by omega)) (fun i hi ↦ h1 i (by omega))
    have hx0 : 0 ≤ x n := h0 n (by omega)
    have hx1 : 0 ≤ 1 - x n := by linarith [h1 n (by omega)]
    rw [sum_range_succ, prod_range_succ]
    nlinarith [mul_le_mul_of_nonneg_right ih' hx1, sq_nonneg (x n),
      mul_nonneg (sq_nonneg (∑ i ∈ range n, x i)) hx0]

/-- `Σ_{i<n} i = C(n,2)`. -/
theorem sum_range_cast_eq_choose_two (n : ℕ) : ∑ i ∈ range n, (i : ℝ) = n.choose 2 := by
  induction n with
  | zero => simp [Nat.cast_choose_two]
  | succ n ih =>
    rw [sum_range_succ, ih, Nat.cast_choose_two, Nat.cast_choose_two]
    push_cast
    ring

/-- **The binomial Bonferroni bound**: `(1 - x)^n ≤ 1 - n x + C(n,2) x²` for `0 ≤ x ≤ 1`. -/
theorem one_sub_pow_le_choose_two (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (n : ℕ) :
    (1 - x) ^ n ≤ 1 - n * x + n.choose 2 * x ^ 2 := by
  induction n with
  | zero => simp [Nat.cast_choose_two]
  | succ n ih =>
    have hx : 0 ≤ 1 - x := by linarith
    have hC : (0 : ℝ) ≤ n.choose 2 := Nat.cast_nonneg _
    have hc : ((n + 1).choose 2 : ℝ) = n.choose 2 + n := by
      rw [Nat.cast_choose_two, Nat.cast_choose_two]
      push_cast
      ring
    rw [pow_succ, hc]
    push_cast
    nlinarith [mul_le_mul_of_nonneg_right ih hx, mul_nonneg hC (pow_nonneg hx0 3)]

/-! ### Marginals on several coordinates -/

/-- **The marginal of a product law on distinct coordinates.** Under `∏_i w_i(x_i)`, with every
`w_i` of total mass one, the coordinates `c_0, …, c_{n-1}` have the product law `⊗_j w_{c_j}`. -/
theorem sum_prod_mul_comp_injective {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    [DecidableEq κ] (w : ι → κ → ℝ) (hw : ∀ i, ∑ t, w i t = 1) {n : ℕ} {c : Fin n → ι}
    (hc : Function.Injective c) (g : (Fin n → κ) → ℝ) :
    ∑ x : ι → κ, (∏ i, w i (x i)) * g (fun j ↦ x (c j)) =
      ∑ y : Fin n → κ, (∏ j, w (c j) (y j)) * g y := by
  have hind : ∀ (x : ι → κ) (y : Fin n → κ), (if (fun j ↦ x (c j)) = y then (1 : ℝ) else 0) =
      ∏ i, ∏ j ∈ univ.filter (fun j ↦ c j = i), (if x i = y j then (1 : ℝ) else 0) := by
    intro x y
    calc (if (fun j ↦ x (c j)) = y then (1 : ℝ) else 0)
        = ∏ j, (if x (c j) = y j then (1 : ℝ) else 0) := by
          rw [Fintype.prod_boole]
          exact if_congr funext_iff rfl rfl
      _ = ∏ i, ∏ j ∈ univ.filter (fun j ↦ c j = i), (if x (c j) = y j then (1 : ℝ) else 0) :=
          (prod_fiberwise_of_maps_to (fun j _ ↦ mem_univ (c j)) _).symm
      _ = ∏ i, ∏ j ∈ univ.filter (fun j ↦ c j = i), (if x i = y j then (1 : ℝ) else 0) :=
          prod_congr rfl fun i _ ↦ prod_congr rfl fun j hj ↦ by rw [(mem_filter.mp hj).2]
  have hfib : ∀ (y : Fin n → κ) (i : ι),
      ∑ t, w i t * ∏ j ∈ univ.filter (fun j ↦ c j = i), (if t = y j then (1 : ℝ) else 0) =
        ∏ j ∈ univ.filter (fun j ↦ c j = i), w (c j) (y j) := by
    intro y i
    by_cases hi : ∃ j, c j = i
    · obtain ⟨j₀, hj₀⟩ := hi
      have hsingle : univ.filter (fun j ↦ c j = i) = {j₀} := by
        ext j
        simp only [mem_filter, mem_univ, true_and, mem_singleton]
        exact ⟨fun hj ↦ hc (hj.trans hj₀.symm), fun hj ↦ by rw [hj]; exact hj₀⟩
      rw [hsingle, prod_singleton, hj₀]
      simp only [prod_singleton, mul_boole, sum_ite_eq', mem_univ, ↓reduceIte]
    · have hempty : univ.filter (fun j ↦ c j = i) = ∅ :=
        filter_eq_empty_iff.mpr fun j _ hj ↦ hi ⟨j, hj⟩
      rw [hempty, prod_empty]
      simp only [prod_empty, mul_one, hw i]
  have key : ∀ y : Fin n → κ, ∑ x : ι → κ, (∏ i, w i (x i)) *
      (if (fun j ↦ x (c j)) = y then (1 : ℝ) else 0) = ∏ j, w (c j) (y j) := by
    intro y
    calc ∑ x : ι → κ, (∏ i, w i (x i)) * (if (fun j ↦ x (c j)) = y then (1 : ℝ) else 0)
        = ∑ x : ι → κ, ∏ i, (w i (x i) *
            ∏ j ∈ univ.filter (fun j ↦ c j = i), (if x i = y j then (1 : ℝ) else 0)) := by
          refine sum_congr rfl fun x _ ↦ ?_
          rw [hind x y, prod_mul_distrib]
      _ = ∏ i, ∑ t, w i t *
            ∏ j ∈ univ.filter (fun j ↦ c j = i), (if t = y j then (1 : ℝ) else 0) :=
          (Fintype.prod_sum fun i t ↦ w i t *
            ∏ j ∈ univ.filter (fun j ↦ c j = i), (if t = y j then (1 : ℝ) else 0)).symm
      _ = ∏ i, ∏ j ∈ univ.filter (fun j ↦ c j = i), w (c j) (y j) :=
          prod_congr rfl fun i _ ↦ hfib y i
      _ = ∏ j, w (c j) (y j) := prod_fiberwise_of_maps_to (fun j _ ↦ mem_univ (c j)) _
  calc ∑ x : ι → κ, (∏ i, w i (x i)) * g (fun j ↦ x (c j))
      = ∑ x : ι → κ, ∑ y : Fin n → κ, g y *
          ((∏ i, w i (x i)) * (if (fun j ↦ x (c j)) = y then (1 : ℝ) else 0)) := by
        refine sum_congr rfl fun x _ ↦ ?_
        simp only [mul_boole, mul_ite, mul_zero, sum_ite_eq, mem_univ, ↓reduceIte]
        ring
    _ = ∑ y : Fin n → κ, g y * ∑ x : ι → κ,
          (∏ i, w i (x i)) * (if (fun j ↦ x (c j)) = y then (1 : ℝ) else 0) := by
        rw [sum_comm]
        simp only [mul_sum]
    _ = ∑ y : Fin n → κ, (∏ j, w (c j) (y j)) * g y := by
        simp only [key]
        exact sum_congr rfl fun y _ ↦ mul_comm _ _

/-! ### Uniform sources -/

/-- The uniform law on source vectors has total mass one. -/
theorem sum_uniformSources_const {N : ℕ} (hN : N ≠ 0) (n : ℕ) :
    ∑ _s : Fin n → Fin N, (N : ℝ)⁻¹ ^ n = 1 := by
  have hN' : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN
  calc ∑ _s : Fin n → Fin N, (N : ℝ)⁻¹ ^ n
      = ∑ _s : Fin n → Fin N, ∏ _j : Fin n, (N : ℝ)⁻¹ := by
        simp only [prod_const, card_univ, Fintype.card_fin]
    _ = ∏ _j : Fin n, ∑ _t : Fin N, (N : ℝ)⁻¹ :=
        (Fintype.prod_sum fun (_ : Fin n) (_ : Fin N) ↦ (N : ℝ)⁻¹).symm
    _ = 1 := by
        simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, mul_inv_cancel₀ hN',
          prod_const_one]

/-- The image of a source vector has `n` elements exactly when no two lineages share a source. -/
theorem card_image_univ_eq_iff_injective {N n : ℕ} (s : Fin n → Fin N) :
    #(univ.image s) = n ↔ Function.Injective s := by
  constructor
  · intro h a b hab
    exact (card_image_iff.mp (by rwa [card_univ, Fintype.card_fin])) (mem_univ a) (mem_univ b) hab
  · intro h
    rw [card_image_of_injective _ h, card_univ, Fintype.card_fin]

/-- **No merger**: `n ≤ N` uniform sources are distinct with probability `∏_{i<n} (1 - i/N)`. -/
theorem sum_uniformSources_injective {N : ℕ} (hN : N ≠ 0) :
    ∀ n : ℕ, n ≤ N → ∑ s : Fin n → Fin N, (N : ℝ)⁻¹ ^ n *
      (if Function.Injective s then 1 else 0) = ∏ i ∈ range n, (1 - (i : ℝ) / N)
  | 0, _ => by
    rw [Fintype.sum_unique, if_pos (Function.injective_of_subsingleton _)]
    simp
  | n + 1, hn => by
    have hN' : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN
    have ih := sum_uniformSources_injective hN n (by omega)
    have hstep : ∀ s' : Fin n → Fin N, ∑ t : Fin N, (N : ℝ)⁻¹ ^ (n + 1) *
        (if Function.Injective (Fin.cons t s' : Fin (n + 1) → Fin N) then 1 else 0) =
        (N : ℝ)⁻¹ ^ n * (if Function.Injective s' then 1 else 0) * (1 - (n : ℝ) / N) := by
      intro s'
      by_cases hs' : Function.Injective s'
      · have hrange : ∀ t : Fin N,
            (if Function.Injective (Fin.cons t s' : Fin (n + 1) → Fin N) then (1 : ℝ) else 0) =
              1 - (if t ∈ univ.image s' then 1 else 0) := by
          intro t
          by_cases ht : t ∈ univ.image s'
          · have hnot : ¬ Function.Injective (Fin.cons t s' : Fin (n + 1) → Fin N) := by
              rw [Fin.cons_injective_iff]
              obtain ⟨a, -, ha⟩ := mem_image.mp ht
              exact fun h ↦ h.1 ⟨a, ha⟩
            rw [if_neg hnot, if_pos ht]
            ring
          · have hyes : Function.Injective (Fin.cons t s' : Fin (n + 1) → Fin N) := by
              rw [Fin.cons_injective_iff]
              exact ⟨fun ⟨a, ha⟩ ↦ ht (mem_image.mpr ⟨a, mem_univ a, ha⟩), hs'⟩
            rw [if_pos hyes, if_neg ht]
            ring
        have hcard : #(univ.image s') = n := by
          rw [card_image_of_injective _ hs', card_univ, Fintype.card_fin]
        have e : (1 : ℝ) - n / N = (N : ℝ)⁻¹ * (N - n) := by field_simp
        calc ∑ t : Fin N, (N : ℝ)⁻¹ ^ (n + 1) *
              (if Function.Injective (Fin.cons t s' : Fin (n + 1) → Fin N) then 1 else 0)
            = (N : ℝ)⁻¹ ^ (n + 1) * ((N : ℝ) - #(univ.image s')) := by
              rw [← mul_sum]
              congr 1
              simp only [hrange, sum_sub_distrib, sum_const, card_univ, Fintype.card_fin,
                nsmul_eq_mul, mul_one, sum_boole, filter_mem_eq_inter, univ_inter]
          _ = (N : ℝ)⁻¹ ^ n * (if Function.Injective s' then 1 else 0) * (1 - (n : ℝ) / N) := by
              rw [if_pos hs', hcard, e, pow_succ]
              ring
      · have hnot : ∀ t : Fin N, ¬ Function.Injective (Fin.cons t s' : Fin (n + 1) → Fin N) :=
          fun t h ↦ hs' (Fin.cons_injective_iff.mp h).2
        simp [hnot, hs']
    calc ∑ s : Fin (n + 1) → Fin N, (N : ℝ)⁻¹ ^ (n + 1) * (if Function.Injective s then 1 else 0)
        = ∑ p : Fin N × (Fin n → Fin N), (N : ℝ)⁻¹ ^ (n + 1) *
            (if Function.Injective (Fin.cons p.1 p.2 : Fin (n + 1) → Fin N) then 1 else 0) :=
          ((Fin.consEquiv fun _ ↦ Fin N).sum_comp
            fun s ↦ (N : ℝ)⁻¹ ^ (n + 1) * (if Function.Injective s then 1 else 0)).symm
      _ = ∑ s' : Fin n → Fin N, (N : ℝ)⁻¹ ^ n * (if Function.Injective s' then 1 else 0) *
            (1 - (n : ℝ) / N) := by
          rw [Fintype.sum_prod_type, sum_comm]
          exact sum_congr rfl fun s' _ ↦ hstep s'
      _ = ∏ i ∈ range (n + 1), (1 - (i : ℝ) / N) := by
          rw [← sum_mul, ih, prod_range_succ]

/-- **The mean number of distinct sources**: `n` uniform sources hit `N (1 - (1 - 1/N)^n)`
parents on average. -/
theorem sum_uniformSources_card_image {N : ℕ} (hN : N ≠ 0) (n : ℕ) :
    ∑ s : Fin n → Fin N, (N : ℝ)⁻¹ ^ n * #(univ.image s) = N * (1 - (1 - (N : ℝ)⁻¹) ^ n) := by
  have hN' : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN
  have hmiss : ∀ p : Fin N, ∑ s : Fin n → Fin N, (N : ℝ)⁻¹ ^ n *
      (if p ∈ univ.image s then 0 else 1) = (1 - (N : ℝ)⁻¹) ^ n := by
    intro p
    have hprod : ∀ s : Fin n → Fin N, (N : ℝ)⁻¹ ^ n * (if p ∈ univ.image s then 0 else 1) =
        ∏ j, ((N : ℝ)⁻¹ * (if s j = p then 0 else 1)) := by
      intro s
      rw [prod_mul_distrib, prod_const, card_univ, Fintype.card_fin]
      congr 1
      by_cases h : p ∈ univ.image s
      · obtain ⟨j, -, hj⟩ := mem_image.mp h
        rw [if_pos h]
        exact (prod_eq_zero (f := fun j ↦ if s j = p then (0 : ℝ) else 1) (mem_univ j)
          (if_pos hj)).symm
      · rw [if_neg h]
        exact (prod_eq_one (f := fun j ↦ if s j = p then (0 : ℝ) else 1) fun j _ ↦
          if_neg fun hj ↦ h (mem_image.mpr ⟨j, mem_univ j, hj⟩)).symm
    have hone : ∑ t : Fin N, (N : ℝ)⁻¹ * (if t = p then 0 else 1) = 1 - (N : ℝ)⁻¹ := by
      have e : ∀ t : Fin N, (N : ℝ)⁻¹ * (if t = p then 0 else 1) =
          (N : ℝ)⁻¹ - (N : ℝ)⁻¹ * (if t = p then 1 else 0) := by
        intro t
        split_ifs <;> ring
      simp only [e, sum_sub_distrib, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul,
        ← mul_sum, sum_ite_eq', mem_univ, ↓reduceIte, mul_one, mul_inv_cancel₀ hN']
    calc ∑ s : Fin n → Fin N, (N : ℝ)⁻¹ ^ n * (if p ∈ univ.image s then 0 else 1)
        = ∑ s : Fin n → Fin N, ∏ j, ((N : ℝ)⁻¹ * (if s j = p then 0 else 1)) :=
          sum_congr rfl fun s _ ↦ hprod s
      _ = ∏ _j : Fin n, ∑ t : Fin N, (N : ℝ)⁻¹ * (if t = p then 0 else 1) :=
          (Fintype.prod_sum fun (_ : Fin n) (t : Fin N) ↦
            (N : ℝ)⁻¹ * (if t = p then 0 else 1)).symm
      _ = (1 - (N : ℝ)⁻¹) ^ n := by
          rw [prod_congr rfl fun j _ ↦ hone, prod_const, card_univ, Fintype.card_fin]
  have hcard : ∀ s : Fin n → Fin N, (#(univ.image s) : ℝ) =
      ∑ p : Fin N, (1 - (if p ∈ univ.image s then 0 else 1)) := by
    intro s
    have e : ∀ p : Fin N, (1 : ℝ) - (if p ∈ univ.image s then 0 else 1) =
        if p ∈ univ.image s then 1 else 0 := by
      intro p
      split_ifs <;> ring
    simp only [e]
    rw [sum_boole, filter_mem_eq_inter, univ_inter]
  calc ∑ s : Fin n → Fin N, (N : ℝ)⁻¹ ^ n * #(univ.image s)
      = ∑ p : Fin N, ∑ s : Fin n → Fin N,
          ((N : ℝ)⁻¹ ^ n - (N : ℝ)⁻¹ ^ n * (if p ∈ univ.image s then 0 else 1)) := by
        rw [sum_comm]
        refine sum_congr rfl fun s _ ↦ ?_
        rw [hcard s, mul_sum]
        exact sum_congr rfl fun p _ ↦ by ring
    _ = ∑ _p : Fin N, (1 - (1 - (N : ℝ)⁻¹) ^ n) := by
        refine sum_congr rfl fun p _ ↦ ?_
        rw [sum_sub_distrib, sum_uniformSources_const hN n, hmiss p]
    _ = N * (1 - (1 - (N : ℝ)⁻¹) ^ n) := by
        rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- Losing at least one block, plus losing at least two, is at most the number of blocks lost. -/
theorem uniformSources_indicator_add_le {N n : ℕ} (s : Fin n → Fin N) :
    (if #(univ.image s) < n then (1 : ℝ) else 0) + (if #(univ.image s) + 2 ≤ n then 1 else 0) ≤
      n - #(univ.image s) := by
  have h : #(univ.image s) ≤ n := card_image_le.trans (by rw [card_univ, Fintype.card_fin])
  have hc : (#(univ.image s) : ℝ) ≤ n := by exact_mod_cast h
  by_cases h1 : #(univ.image s) < n
  · by_cases h2 : #(univ.image s) + 2 ≤ n
    · rw [if_pos h1, if_pos h2]
      have : (#(univ.image s) : ℝ) + 2 ≤ n := by exact_mod_cast h2
      linarith
    · rw [if_pos h1, if_neg h2]
      have : (#(univ.image s) : ℝ) + 1 ≤ n := by exact_mod_cast h1
      linarith
  · rw [if_neg h1, if_neg (show ¬ #(univ.image s) + 2 ≤ n by omega)]
    linarith

/-! ### The block-count law of one generation -/

/-- **The one-generation block-count law**: the probability that `n` lineages at distinct
offspring are carried at feature `k` by exactly `b` parents. -/
def blockTransition (N n b : ℕ) : ℝ :=
  ∑ s : Fin n → Fin N, (N : ℝ)⁻¹ ^ n * (if #(univ.image s) = b then 1 else 0)

/-- The probability that some two of `n` lineages merge within a generation. -/
def blockMergeProb (N n : ℕ) : ℝ :=
  ∑ s : Fin n → Fin N, (N : ℝ)⁻¹ ^ n * (if #(univ.image s) < n then 1 else 0)

/-- The probability that the block count falls by at least two within a generation. -/
def blockMultiMergeProb (N n : ℕ) : ℝ :=
  ∑ s : Fin n → Fin N, (N : ℝ)⁻¹ ^ n * (if #(univ.image s) + 2 ≤ n then 1 else 0)

/-- **No merger**: `blockTransition N n n = ∏_{i<n} (1 - i/N)` for `n ≤ N`. -/
theorem blockTransition_self {N : ℕ} (hN : N ≠ 0) {n : ℕ} (hn : n ≤ N) :
    blockTransition N n n = ∏ i ∈ range n, (1 - (i : ℝ) / N) := by
  rw [← sum_uniformSources_injective hN n hn]
  refine sum_congr rfl fun s _ ↦ ?_
  congr 1
  exact if_congr (card_image_univ_eq_iff_injective s) rfl rfl

/-- Some pair merges with probability `1 - ∏_{i<n} (1 - i/N)`. -/
theorem blockMergeProb_eq {N : ℕ} (hN : N ≠ 0) {n : ℕ} (hn : n ≤ N) :
    blockMergeProb N n = 1 - ∏ i ∈ range n, (1 - (i : ℝ) / N) := by
  rw [← blockTransition_self hN hn, ← sum_uniformSources_const hN n, blockMergeProb,
    blockTransition, ← sum_sub_distrib]
  refine sum_congr rfl fun s _ ↦ ?_
  have hle : #(univ.image s) ≤ n := card_image_le.trans (by rw [card_univ, Fintype.card_fin])
  by_cases h : #(univ.image s) = n
  · rw [if_neg (show ¬ #(univ.image s) < n by omega), if_pos h]
    ring
  · rw [if_pos (show #(univ.image s) < n by omega), if_neg h]
    ring

/-- **Merging within a generation**: `C(n,2)/N - (C(n,2)/N)²/2 ≤ P(some merger) ≤ C(n,2)/N`. -/
theorem blockMergeProb_bounds {N : ℕ} (hN : N ≠ 0) {n : ℕ} (hn : n ≤ N) :
    (n.choose 2 : ℝ) / N - ((n.choose 2 : ℝ) / N) ^ 2 / 2 ≤ blockMergeProb N n ∧
      blockMergeProb N n ≤ (n.choose 2 : ℝ) / N := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero hN
  have hsum : ∑ i ∈ range n, (i : ℝ) / N = (n.choose 2 : ℝ) / N := by
    rw [← sum_div, sum_range_cast_eq_choose_two]
  have h0 : ∀ i < n, (0 : ℝ) ≤ (i : ℝ) / N := fun i _ ↦ by positivity
  have h1 : ∀ i < n, (i : ℝ) / N ≤ 1 := fun i hi ↦
    div_le_one_of_le₀ (by exact_mod_cast (show i ≤ N by omega)) hNpos.le
  have hL := one_sub_sum_le_prod_range (fun i ↦ (i : ℝ) / N) n h0 h1
  have hU := prod_range_le_one_sub_add_sq (fun i ↦ (i : ℝ) / N) n h0 h1
  simp only [hsum] at hL hU
  rw [blockMergeProb_eq hN hn]
  constructor <;> linarith

/-- **Some pair merges with probability `C(n,2)/N + O(1/N²)`**, with error at most
`(C(n,2)/N)²/2`. -/
theorem abs_blockMergeProb_sub_le {N : ℕ} (hN : N ≠ 0) {n : ℕ} (hn : n ≤ N) :
    |blockMergeProb N n - (n.choose 2 : ℝ) / N| ≤ ((n.choose 2 : ℝ) / N) ^ 2 / 2 := by
  obtain ⟨hL, hU⟩ := blockMergeProb_bounds hN hn
  rw [abs_le]
  constructor <;> nlinarith [sq_nonneg ((n.choose 2 : ℝ) / N)]

/-- **Multiple mergers are of second order**: the block count falls by two or more with
probability at most `(C(n,2)/N)²/2`. -/
theorem blockMultiMergeProb_le {N : ℕ} (hN : N ≠ 0) {n : ℕ} (hn : n ≤ N) :
    blockMultiMergeProb N n ≤ ((n.choose 2 : ℝ) / N) ^ 2 / 2 := by
  have hN' : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN
  have hpos : (0 : ℝ) ≤ (N : ℝ)⁻¹ ^ n := by positivity
  have hsumle : blockMergeProb N n + blockMultiMergeProb N n ≤
      ∑ s : Fin n → Fin N, (N : ℝ)⁻¹ ^ n * ((n : ℝ) - #(univ.image s)) := by
    rw [blockMergeProb, blockMultiMergeProb, ← sum_add_distrib]
    exact sum_le_sum fun s _ ↦ by
      rw [← mul_add]
      exact mul_le_mul_of_nonneg_left (uniformSources_indicator_add_le s) hpos
  have hE : ∑ s : Fin n → Fin N, (N : ℝ)⁻¹ ^ n * ((n : ℝ) - #(univ.image s)) =
      n - N * (1 - (1 - (N : ℝ)⁻¹) ^ n) := by
    simp only [mul_sub, sum_sub_distrib, ← sum_mul, sum_uniformSources_const hN n, one_mul,
      sum_uniformSources_card_image hN n]
  have hpow := one_sub_pow_le_choose_two (N : ℝ)⁻¹ (by positivity)
    (inv_le_one_of_one_le₀ (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hN)) n
  have h1 : (N : ℝ) * (N : ℝ)⁻¹ = 1 := mul_inv_cancel₀ hN'
  have hNpow : (N : ℝ) * (1 - (N : ℝ)⁻¹) ^ n ≤ N - n + n.choose 2 * (N : ℝ)⁻¹ := by
    have hm := mul_le_mul_of_nonneg_left hpow (Nat.cast_nonneg N)
    have h1n : (n : ℝ) * ((N : ℝ) * (N : ℝ)⁻¹) = n := by rw [h1, mul_one]
    have h1c : (n.choose 2 : ℝ) * (N : ℝ)⁻¹ * ((N : ℝ) * (N : ℝ)⁻¹) =
        n.choose 2 * (N : ℝ)⁻¹ := by
      rw [h1, mul_one]
    nlinarith [hm, h1n, h1c, h1]
  obtain ⟨hL, -⟩ := blockMergeProb_bounds hN hn
  rw [hE] at hsumle
  have hdiv : (n.choose 2 : ℝ) / N = n.choose 2 * (N : ℝ)⁻¹ := div_eq_mul_inv _ _
  rw [hdiv] at hL ⊢
  nlinarith [hsumle, hNpow, hL]

/-- The block count falls by exactly one when some pair merges and no second merger happens. -/
theorem blockTransition_pred {N n : ℕ} (hn : 1 ≤ n) :
    blockTransition N n (n - 1) = blockMergeProb N n - blockMultiMergeProb N n := by
  rw [blockTransition, blockMergeProb, blockMultiMergeProb, ← sum_sub_distrib]
  refine sum_congr rfl fun s _ ↦ ?_
  have hle : #(univ.image s) ≤ n := card_image_le.trans (by rw [card_univ, Fintype.card_fin])
  by_cases h1 : #(univ.image s) = n - 1
  · rw [if_pos h1, if_pos (show #(univ.image s) < n by omega),
      if_neg (show ¬ #(univ.image s) + 2 ≤ n by omega)]
    ring
  · by_cases h2 : #(univ.image s) + 2 ≤ n
    · rw [if_neg h1, if_pos (show #(univ.image s) < n by omega), if_pos h2]
      ring
    · rw [if_neg h1, if_neg (show ¬ #(univ.image s) < n by omega), if_neg h2]
      ring

/-! ### Kingman's rates -/

/-- **The total rate out of `n` blocks is `C(n,2)`**: `N · P(some merger) → C(n,2)`. -/
theorem tendsto_mul_blockMergeProb (n : ℕ) :
    Tendsto (fun N : ℕ ↦ (N : ℝ) * blockMergeProb N n) atTop (𝓝 (n.choose 2 : ℝ)) := by
  have hlow : Tendsto (fun N : ℕ ↦ (n.choose 2 : ℝ) - ((n.choose 2 : ℝ) ^ 2 / 2) / N) atTop
      (𝓝 (n.choose 2 : ℝ)) := by
    have h := (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (n.choose 2 : ℝ)) atTop
      (𝓝 (n.choose 2 : ℝ))).sub (tendsto_const_div_atTop_nhds_zero_nat ((n.choose 2 : ℝ) ^ 2 / 2))
    rw [sub_zero] at h
    exact h
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds ?_ ?_
  · filter_upwards [eventually_ge_atTop (max n 1)] with N hN
    have hN0 : N ≠ 0 := by omega
    have hNpos : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero hN0
    have h1 : (N : ℝ) * (N : ℝ)⁻¹ = 1 := mul_inv_cancel₀ hNpos.ne'
    obtain ⟨hL, -⟩ := blockMergeProb_bounds hN0 (show n ≤ N by omega)
    calc (n.choose 2 : ℝ) - ((n.choose 2 : ℝ) ^ 2 / 2) / N
        = N * ((n.choose 2 : ℝ) / N - ((n.choose 2 : ℝ) / N) ^ 2 / 2) := by
          linear_combination ((n.choose 2 : ℝ) ^ 2 * (N : ℝ)⁻¹ / 2 - n.choose 2) * h1
      _ ≤ N * blockMergeProb N n := mul_le_mul_of_nonneg_left hL hNpos.le
  · filter_upwards [eventually_ge_atTop (max n 1)] with N hN
    have hN0 : N ≠ 0 := by omega
    have hNpos : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero hN0
    have h1 : (N : ℝ) * (N : ℝ)⁻¹ = 1 := mul_inv_cancel₀ hNpos.ne'
    obtain ⟨-, hU⟩ := blockMergeProb_bounds hN0 (show n ≤ N by omega)
    calc (N : ℝ) * blockMergeProb N n ≤ N * ((n.choose 2 : ℝ) / N) :=
          mul_le_mul_of_nonneg_left hU hNpos.le
      _ = n.choose 2 := by linear_combination (n.choose 2 : ℝ) * h1

/-- **No multiple mergers in the limit**: `N · P(the block count falls by two or more) → 0`. -/
theorem tendsto_mul_blockMultiMergeProb (n : ℕ) :
    Tendsto (fun N : ℕ ↦ (N : ℝ) * blockMultiMergeProb N n) atTop (𝓝 0) := by
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (tendsto_const_div_atTop_nhds_zero_nat ((n.choose 2 : ℝ) ^ 2 / 2)) ?_ ?_
  · filter_upwards with N
    exact mul_nonneg (Nat.cast_nonneg N) (sum_nonneg fun s _ ↦
      mul_nonneg (by positivity) (by split_ifs <;> norm_num))
  · filter_upwards [eventually_ge_atTop (max n 1)] with N hN
    have hN0 : N ≠ 0 := by omega
    have hNpos : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero hN0
    have h1 : (N : ℝ) * (N : ℝ)⁻¹ = 1 := mul_inv_cancel₀ hNpos.ne'
    calc (N : ℝ) * blockMultiMergeProb N n ≤ N * (((n.choose 2 : ℝ) / N) ^ 2 / 2) :=
          mul_le_mul_of_nonneg_left (blockMultiMergeProb_le hN0 (by omega)) hNpos.le
      _ = ((n.choose 2 : ℝ) ^ 2 / 2) / N := by
          linear_combination ((n.choose 2 : ℝ) ^ 2 * (N : ℝ)⁻¹ / 2) * h1

/-- **Kingman's rate from `n` to `n - 1` blocks**: `N · P(n → n - 1) → C(n,2)`. -/
theorem tendsto_mul_blockTransition_pred {n : ℕ} (hn : 1 ≤ n) :
    Tendsto (fun N : ℕ ↦ (N : ℝ) * blockTransition N n (n - 1)) atTop
      (𝓝 (n.choose 2 : ℝ)) := by
  have h := (tendsto_mul_blockMergeProb n).sub (tendsto_mul_blockMultiMergeProb n)
  rw [sub_zero] at h
  refine h.congr fun N ↦ ?_
  rw [blockTransition_pred hn, mul_sub]

/-- **No other transitions in the limit**: `N · P(n → b) → 0` for `b ≤ n - 2`. -/
theorem tendsto_mul_blockTransition_of_add_two_le {n b : ℕ} (hb : b + 2 ≤ n) :
    Tendsto (fun N : ℕ ↦ (N : ℝ) * blockTransition N n b) atTop (𝓝 0) := by
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (tendsto_mul_blockMultiMergeProb n) ?_ ?_
  · filter_upwards with N
    exact mul_nonneg (Nat.cast_nonneg N) (sum_nonneg fun s _ ↦
      mul_nonneg (by positivity) (by split_ifs <;> norm_num))
  · filter_upwards with N
    refine mul_le_mul_of_nonneg_left (sum_le_sum fun s _ ↦
      mul_le_mul_of_nonneg_left ?_ (by positivity)) (Nat.cast_nonneg N)
    by_cases h1 : #(univ.image s) = b
    · have e1 : (if #(univ.image s) = b then (1 : ℝ) else 0) = 1 := if_pos h1
      have e2 : (if #(univ.image s) + 2 ≤ n then (1 : ℝ) else 0) = 1 := if_pos (by omega)
      simp only [e1, e2, le_refl]
    · rw [if_neg h1]
      split_ifs <;> norm_num

/-! ### The annotated generation -/

section Annotated

variable {V : Type*} [DecidableEq V] [Fintype V]

/-- **The sources of `n` lineages are uniform**: summing out the genomes of `n` annotated
offspring leaves the uniform law on their source vectors. -/
theorem sum_prod_annotatedLaw_sources (G : CheckingGraph V) {N : ℕ} (hN : N ≠ 0) (k : V)
    (pop : Fin N → V → Bool) {n : ℕ} (h : (Fin n → Fin N) → ℝ) :
    ∑ y : Fin n → Fin N × (V → Bool), (∏ j, annotatedLaw G N k pop (y j)) *
        h (fun j ↦ (y j).1) =
      ∑ s : Fin n → Fin N, (N : ℝ)⁻¹ ^ n * h s := by
  have key : ∀ s : Fin n → Fin N, ∑ y : Fin n → Fin N × (V → Bool),
      (∏ j, annotatedLaw G N k pop (y j)) * (if (fun j ↦ (y j).1) = s then (1 : ℝ) else 0) =
        (N : ℝ)⁻¹ ^ n := by
    intro s
    calc ∑ y : Fin n → Fin N × (V → Bool),
          (∏ j, annotatedLaw G N k pop (y j)) * (if (fun j ↦ (y j).1) = s then (1 : ℝ) else 0)
        = ∑ y : Fin n → Fin N × (V → Bool),
            ∏ j, (annotatedLaw G N k pop (y j) * (if (y j).1 = s j then (1 : ℝ) else 0)) := by
          refine sum_congr rfl fun y _ ↦ ?_
          rw [prod_mul_distrib, Fintype.prod_boole]
          congr 1
          exact if_congr funext_iff rfl rfl
      _ = ∏ j, ∑ q : Fin N × (V → Bool),
            annotatedLaw G N k pop q * (if q.1 = s j then (1 : ℝ) else 0) :=
          (Fintype.prod_sum fun j q ↦
            annotatedLaw G N k pop q * (if q.1 = s j then (1 : ℝ) else 0)).symm
      _ = ∏ _j : Fin n, (N : ℝ)⁻¹ := by
          refine prod_congr rfl fun j _ ↦ ?_
          calc ∑ q : Fin N × (V → Bool),
                annotatedLaw G N k pop q * (if q.1 = s j then (1 : ℝ) else 0)
              = ∑ t : Fin N, (∑ z : V → Bool, annotatedLaw G N k pop (t, z)) *
                  (if t = s j then (1 : ℝ) else 0) := by
                rw [Fintype.sum_prod_type]
                exact sum_congr rfl fun t _ ↦ (sum_mul _ _ _).symm
            _ = (N : ℝ)⁻¹ := by
                simp only [sum_annotatedLaw_snd G hN k pop, mul_boole, sum_ite_eq', mem_univ,
                  ↓reduceIte]
      _ = (N : ℝ)⁻¹ ^ n := by rw [prod_const, card_univ, Fintype.card_fin]
  calc ∑ y : Fin n → Fin N × (V → Bool), (∏ j, annotatedLaw G N k pop (y j)) *
        h (fun j ↦ (y j).1)
      = ∑ y : Fin n → Fin N × (V → Bool), ∑ s : Fin n → Fin N, h s *
          ((∏ j, annotatedLaw G N k pop (y j)) *
            (if (fun j ↦ (y j).1) = s then (1 : ℝ) else 0)) := by
        refine sum_congr rfl fun y _ ↦ ?_
        simp only [mul_boole, mul_ite, mul_zero, sum_ite_eq, mem_univ, ↓reduceIte]
        ring
    _ = ∑ s : Fin n → Fin N, h s * ∑ y : Fin n → Fin N × (V → Bool),
          (∏ j, annotatedLaw G N k pop (y j)) *
            (if (fun j ↦ (y j).1) = s then (1 : ℝ) else 0) := by
        rw [sum_comm]
        simp only [mul_sum]
    _ = ∑ s : Fin n → Fin N, (N : ℝ)⁻¹ ^ n * h s := by
        simp only [key]
        exact sum_congr rfl fun s _ ↦ mul_comm _ _

/-- **The block count of an annotated generation**: for `n` distinct offspring `c`, any function
of the number of their distinct sources has the mean it has under uniform source vectors. -/
theorem sum_prod_annotatedLaw_blockCount (G : CheckingGraph V) {N : ℕ} (hN : N ≠ 0) (k : V)
    (pop : Fin N → V → Bool) {n : ℕ} {c : Fin n → Fin N} (hc : Function.Injective c)
    (F : ℕ → ℝ) :
    ∑ x : Fin N → Fin N × (V → Bool), (∏ i, annotatedLaw G N k pop (x i)) *
        F #(univ.image fun j ↦ (x (c j)).1) =
      ∑ s : Fin n → Fin N, (N : ℝ)⁻¹ ^ n * F #(univ.image s) := by
  rw [sum_prod_mul_comp_injective (fun _ q ↦ annotatedLaw G N k pop q)
    (fun _ ↦ sum_annotatedLaw G hN k pop) hc (fun y ↦ F #(univ.image fun j ↦ (y j).1))]
  exact sum_prod_annotatedLaw_sources G hN k pop fun s ↦ F #(univ.image s)

/-- The block-count law of an annotated generation is `blockTransition`. -/
theorem sum_prod_annotatedLaw_blockTransition (G : CheckingGraph V) {N : ℕ} (hN : N ≠ 0)
    (k : V) (pop : Fin N → V → Bool) {n : ℕ} {c : Fin n → Fin N} (hc : Function.Injective c)
    (b : ℕ) :
    ∑ x : Fin N → Fin N × (V → Bool), (∏ i, annotatedLaw G N k pop (x i)) *
        (if #(univ.image fun j ↦ (x (c j)).1) = b then 1 else 0) =
      blockTransition N n b :=
  sum_prod_annotatedLaw_blockCount G hN k pop hc fun m ↦ if m = b then 1 else 0

/-- The merger probability of an annotated generation is `blockMergeProb`. -/
theorem sum_prod_annotatedLaw_blockMergeProb (G : CheckingGraph V) {N : ℕ} (hN : N ≠ 0)
    (k : V) (pop : Fin N → V → Bool) {n : ℕ} {c : Fin n → Fin N} (hc : Function.Injective c) :
    ∑ x : Fin N → Fin N × (V → Bool), (∏ i, annotatedLaw G N k pop (x i)) *
        (if #(univ.image fun j ↦ (x (c j)).1) < n then 1 else 0) =
      blockMergeProb N n :=
  sum_prod_annotatedLaw_blockCount G hN k pop hc fun m ↦ if m < n then 1 else 0

end Annotated

end

end Descent.Pangenome.AncestralLocality
