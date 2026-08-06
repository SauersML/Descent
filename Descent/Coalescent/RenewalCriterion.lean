/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Coalescent.PolyaCriterion
import Mathlib.Tactic
import Descent.Layer

assert_below Descent.Pangenome Descent.PopGen Descent.Spectral Descent.Conditionals Descent.Portability Descent.Decision Descent.Program

-- LAYER DEBT. This file cannot yet assert it is below `Descent.Blindness`:
--   Blindness: reaches 1 module(s) -- `Descent.Blindness.MultipleMergerBlindness`
-- The repair is to move what it reaches for DOWN, not to move this file up.

namespace Descent

/-!
# The renewal criterion: divergence forces certain return

`Descent.Coalescent.PolyaCriterion` proves the counting half of Pólya's theorem in one
dimension: the simple walk's return probabilities are `C(2n,n)/4ⁿ`, and
`not_summable_returnProb` shows they sum to infinity.  What that file then CITED rather than
proved is the step from divergence to recurrence.  This file proves that step.

Write `uₙ` for the chance of being at the origin at time `n` and `f_k` for the chance that the
FIRST return happens at time `k`.  Decomposing a visit according to when the first return
occurred relates them:

  `uₙ = Σ_{k=1}^{n} f_k · u_{n-k}`,   `u₀ = 1`.

That identity is the one genuinely probabilistic input, and it enters as a hypothesis.
Everything after it is a bounded-partial-sums argument with no probability in it at all:

  `Σ_{n=1}^{N} uₙ = Σ_{k=1}^{N} f_k · Σ_{m=0}^{N-k} u_m ≤ q · U_N`,   `q = Σ f_k`,

so `U_N ≤ u₀ + q·U_N`, and if `q < 1` then `U_N ≤ u₀(1-q)⁻¹` for every `N`.  Bounded partial
sums of non-negative terms is summability.  Contrapositively: **if the return probabilities
are not summable then `q = 1`**, and the walk returns almost surely.

## What this closes and what it does not

`polya_certain_return` is Pólya's theorem in one dimension with the renewal identity as an
explicit named hypothesis rather than an appeal to a citation.  The identity itself is a
statement about the walk's probability space -- that `{T = k}` depends only on the first `k`
increments while `{S_n - S_k = 0}` depends only on the rest, so the two are independent.  For
an i.i.d. increment sequence that is disjointness of coordinate blocks rather than the strong
Markov property, but it still needs the walk built on a product measure, which is the work
`Descent.Coalescent.TrajectoryLaw` records.

The reduction is worth having on its own.  It converts "cite Pólya" into "supply one
identity", and the identity is a fact about a random walk rather than about genealogy -- so
the genealogical side of the corpus no longer has an open citation in it.  It also shows the
divergence is doing ALL the work: no property of the simple walk is used below beyond
`u₀ = 1` and non-negativity, so the same argument decides recurrence for any walk whose
return probabilities are known.

## Main results

- `sum_shift_le`: a shifted partial sum is at most the full one.
- `sum_le_of_renewal`: the partial sums satisfy `U_N ≤ u₀ + q·U_N`.
- `summable_of_renewal`: **a sub-critical first-return mass forces summability**.
- `tsum_eq_one_of_not_summable`: hence divergence forces `q = 1`.
- `polya_certain_return`: **the one-dimensional walk returns almost surely**, since
  `PolyaCriterion.not_summable_returnProb` supplies the divergence.
-/

namespace Coalescent

open Finset

/-! ### The partial-sum estimate -/

/-- The shifted sum `Σ_{n ∈ Icc k N} u (n - k)` is at most the full partial sum, because
`n ↦ n - k` is injective on `Icc k N` and lands in `range (N + 1)`. -/
theorem sum_shift_le {u : ℕ → ℝ} (hunn : ∀ n, 0 ≤ u n) (k N : ℕ) :
    ∑ n ∈ Finset.Icc k N, u (n - k) ≤ ∑ m ∈ Finset.range (N + 1), u m := by
  classical
  have hinj : ∀ x ∈ Finset.Icc k N, ∀ y ∈ Finset.Icc k N, x - k = y - k → x = y := by
    intro x hx y hy h
    have hx' := Finset.mem_Icc.mp hx
    have hy' := Finset.mem_Icc.mp hy
    omega
  rw [← Finset.sum_image hinj]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun i _ _ ↦ hunn i)
  intro m hm
  obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hm
  have hn' := Finset.mem_Icc.mp hn
  exact Finset.mem_range.mpr (by omega)

/-- **The renewal identity bounds the partial sums by themselves.**  Summing the identity over
`1 ≤ n ≤ N` and exchanging the order of summation puts every `f_k` in front of a shifted
partial sum, which `sum_shift_le` replaces by the full one. -/
theorem sum_le_of_renewal {u f : ℕ → ℝ} {q : ℝ} (hunn : ∀ n, 0 ≤ u n) (hfnn : ∀ n, 0 ≤ f n)
    (hren : ∀ n, 1 ≤ n → u n = ∑ k ∈ Finset.Icc 1 n, f k * u (n - k))
    (hq : ∀ N : ℕ, ∑ k ∈ Finset.Icc 1 N, f k ≤ q) (N : ℕ) :
    ∑ n ∈ Finset.range (N + 1), u n ≤ u 0 + q * ∑ m ∈ Finset.range (N + 1), u m := by
  classical
  set U : ℝ := ∑ m ∈ Finset.range (N + 1), u m with hU
  have hU0 : 0 ≤ U := Finset.sum_nonneg fun i _ ↦ hunn i
  -- peel the `n = 0` term
  have hpeel : ∑ n ∈ Finset.range (N + 1), u n = u 0 + ∑ n ∈ Finset.Icc 1 N, u n := by
    have hIcc : ∑ n ∈ Finset.Icc 1 N, u n = ∑ i ∈ Finset.range N, u (1 + i) := by
      rw [← Nat.Ico_succ_right, Finset.sum_Ico_eq_sum_range]
      simp
    rw [hIcc, Finset.sum_range_succ', add_comm]
    congr 1
    exact Finset.sum_congr rfl fun i _ ↦ by rw [Nat.add_comm]
  -- rewrite each term by the renewal identity and exchange the order of summation
  have hren' : ∑ n ∈ Finset.Icc 1 N, u n
      = ∑ n ∈ Finset.Icc 1 N, ∑ k ∈ Finset.Icc 1 n, f k * u (n - k) :=
    Finset.sum_congr rfl fun n hn ↦ hren n (Finset.mem_Icc.mp hn).1
  have hswap : ∑ n ∈ Finset.Icc 1 N, ∑ k ∈ Finset.Icc 1 n, f k * u (n - k)
      = ∑ k ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc k N, f k * u (n - k) := by
    refine Finset.sum_comm' ?_
    intro n k
    simp only [Finset.mem_Icc]
    omega
  have hinner : ∀ k ∈ Finset.Icc 1 N,
      ∑ n ∈ Finset.Icc k N, f k * u (n - k) ≤ f k * U := by
    intro k _
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (sum_shift_le hunn k N) (hfnn k)
  calc ∑ n ∈ Finset.range (N + 1), u n
      = u 0 + ∑ n ∈ Finset.Icc 1 N, ∑ k ∈ Finset.Icc 1 n, f k * u (n - k) := by
        rw [hpeel, hren']
    _ = u 0 + ∑ k ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc k N, f k * u (n - k) := by rw [hswap]
    _ ≤ u 0 + ∑ k ∈ Finset.Icc 1 N, f k * U :=
        add_le_add_left (Finset.sum_le_sum hinner) _
    _ = u 0 + (∑ k ∈ Finset.Icc 1 N, f k) * U := by rw [Finset.sum_mul]
    _ ≤ u 0 + q * U :=
        add_le_add_left (mul_le_mul_of_nonneg_right (hq N) hU0) _

/-! ### Sub-critical mass forces summability -/

/-- **If the first-return mass is below one, the return probabilities are summable.**  The
partial sums satisfy `U_N ≤ u₀ + q·U_N`, hence `U_N ≤ u₀/(1-q)` uniformly, and bounded partial
sums of non-negative terms is summability.

This is the whole content of the renewal criterion: a walk that has a positive chance of never
returning is visited finitely often on average. -/
theorem summable_of_renewal {u f : ℕ → ℝ} {q : ℝ} (hunn : ∀ n, 0 ≤ u n) (hfnn : ∀ n, 0 ≤ f n)
    (hren : ∀ n, 1 ≤ n → u n = ∑ k ∈ Finset.Icc 1 n, f k * u (n - k))
    (hq : ∀ N : ℕ, ∑ k ∈ Finset.Icc 1 N, f k ≤ q) (hq1 : q < 1) : Summable u := by
  refine summable_of_sum_range_le (c := u 0 / (1 - q)) hunn fun n ↦ ?_
  have hq0 : 0 < 1 - q := by linarith
  have hu00 : 0 ≤ u 0 := hunn 0
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h
    simp only [Finset.range_zero, Finset.sum_empty]
    positivity
  · obtain ⟨N, rfl⟩ : ∃ N, n = N + 1 := ⟨n - 1, by omega⟩
    have hb := sum_le_of_renewal hunn hfnn hren hq N
    rw [le_div_iff₀ hq0]
    nlinarith [Finset.sum_nonneg (fun i (_ : i ∈ Finset.range (N + 1)) ↦ hunn i)]

/-- **Divergence forces the first-return mass to be exactly one.**  Contrapositive of
`summable_of_renewal`, with the mass known a priori to be at most one because it is a
probability. -/
theorem tsum_eq_one_of_not_summable {u f : ℕ → ℝ} (hunn : ∀ n, 0 ≤ u n) (hfnn : ∀ n, 0 ≤ f n)
    (hf0 : f 0 = 0) (hf : Summable f) (hf1 : ∑' k, f k ≤ 1)
    (hren : ∀ n, 1 ≤ n → u n = ∑ k ∈ Finset.Icc 1 n, f k * u (n - k))
    (hns : ¬ Summable u) : ∑' k, f k = 1 := by
  by_contra hne
  have hlt : ∑' k, f k < 1 := lt_of_le_of_ne hf1 hne
  refine hns (summable_of_renewal (q := ∑' k, f k) hunn hfnn hren (fun N ↦ ?_) hlt)
  exact sum_le_tsum _ (fun i _ ↦ hfnn i) hf

/-! ### Pólya in one dimension -/

/-- **The one-dimensional simple walk returns to the origin almost surely.**

`PolyaCriterion.not_summable_returnProb` supplies the divergence -- from the count
`C(2n,n)/4ⁿ` and the harmonic series, with no probability in it -- and the renewal identity
converts divergence into certainty.  The conclusion `Σ f_k = 1` says the first-return time is
finite with probability one.

For the genealogy this is the last step of the chain
`SpatialCoalescent.meet_iff_difference_walk_zero` starts: two lineages in a one-dimensional
habitat are at the same site exactly when their difference walk is at zero, that walk is a
simple walk, and it hits zero almost surely.  So in one dimension coalescence is certain, and
the corpus no longer takes that on citation.

    Empirical status: NOT AN EMPIRICAL CLAIM -- a theorem about a random walk.  Whether a
    population's lineages move like one is the empirical question, and the spatial modules
    carry it.  What is assumed here is the renewal identity, which holds for any walk with
    independent identically distributed steps. -/
theorem polya_certain_return {f : ℕ → ℝ} (hfnn : ∀ n, 0 ≤ f n) (hf0 : f 0 = 0)
    (hf : Summable f) (hf1 : ∑' k, f k ≤ 1)
    (hren : ∀ n, 1 ≤ n → returnProb n = ∑ k ∈ Finset.Icc 1 n, f k * returnProb (n - k)) :
    ∑' k, f k = 1 :=
  tsum_eq_one_of_not_summable returnProb_nonneg hfnn hf0 hf hf1 hren not_summable_returnProb

/-- **The walk is at the origin at time zero**, which is the initial condition the renewal
identity is written against. -/
@[simp] theorem returnProb_zero : returnProb 0 = 1 := by
  unfold returnProb
  norm_num

end Coalescent

end Descent
