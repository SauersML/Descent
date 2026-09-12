/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Pangenome.GraphCoalescent.ReportedConnectionClock
import Descent.Pangenome.GraphCoalescent.VisibleIntensityClock

assert_below Descent.PopGen Descent.Spectral Descent.Blindness Descent.Conditionals
assert_below Descent.Portability Descent.Decision Descent.Program

/-!
# The first-step mean connection time is the path expectation

`VisibleIntensityClock.meanConnectionTime s ξ` is defined as the solution of the backward
equation `V(ξ) = (1 + ∑_{ξ ⋖ η} V(η)) / d_K` on unconnected reports, with `V = 0` on connected
ones, and that module records that the identification of the solution with the path expectation
it solves for is not formalized.  `ReportedConnectionClock` has a path law, the jump-chain
trajectory paired with an independent Kingman clock.  This file proves the identification at the
entrance state `⊥`:

  `E τ_q = meanConnectionTime s ⊥`.        (`connectionTime_mean_eq_meanConnectionTime`)

Both sides equal `∑_{k=2}^{n} (1 - F_k)/d_k`: the holding time at level `k` counts exactly when
the report is not yet connected there.  The first-step value unrolls along the head law of the
jump chain one level at a time (`sum_blockLaw_meanConnectionTime`), because the backward
equation's average over covers is the jump kernel (`meanConnectionTime_eq_sum_jumpLaw`).  The path
expectation comes from (D8) through `p_b = F_b - F_{b+1}` and an exchange of sums
(`mean_eq_sum_survival`).

Scope.  The identification is at `ξ = ⊥`, the note's entrance state; the path law of
`ReportedConnectionClock` starts there.  The discounted values `connectionValue s t` with `t > 0`
are not identified with transforms here.

## Empirical status

None.  Every declaration is an identity between a finite recursion along the covering order and
the expectations of `ReportedConnectionClock`, all built from K-C (1.3) and (1.7).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Pangenome.GraphCoalescent

open Finset Coalescent MeasureTheory
open scoped Classical ENNReal

/-! ### The path expectation in survival form -/

/-- `∑_{b<k} p_b = 1 - F_k`: the report is unconnected at level `k` exactly when it connects only
after the chain drops below `k` blocks. -/
theorem sum_Ico_stoppingProb {n : ℕ} (hn : 1 ≤ n) (s : Fin n → Fin n) :
    ∀ k, 1 ≤ k → k ≤ n → ∑ b ∈ Ico 1 k, stoppingProb s b = 1 - connectedProb s k := by
  intro k hk
  induction k, hk using Nat.le_induction with
  | base =>
    intro _
    rw [Ico_self, sum_empty, connectedProb_one s hn, sub_self]
  | succ k hk ih =>
    intro hkn
    rw [sum_Ico_succ_top hk, ih (by omega), stoppingProb_eq s hk (by omega)]
    ring

/-- **(D8) in survival form**: `2 ∑_b p_b / b - 2/n = ∑_{k=2}^{n} (1 - F_k)/d_k`. -/
theorem mean_eq_sum_survival {n : ℕ} (hn : 2 ≤ n) (s : Fin n → Fin n) :
    2 * ∑ b ∈ Icc 1 n, stoppingProb s b / b - 2 / n
      = ∑ k ∈ Ioc 1 n, (1 - connectedProb s k) / deathRate k := by
  have hform : 2 * ∑ b ∈ Icc 1 n, stoppingProb s b / b - 2 / n
      = ∑ b ∈ Icc 1 n, ∑ k ∈ Ioc b n, stoppingProb s b * (1 / deathRate k) := by
    have hterm : ∀ b ∈ Icc 1 n, ∑ k ∈ Ioc b n, stoppingProb s b * (1 / deathRate k)
        = 2 * (stoppingProb s b / b) - 2 / n * stoppingProb s b := by
      intro b hb
      rw [← mul_sum, sum_Ioc_one_div_deathRate (mem_Icc.mp hb).1 (mem_Icc.mp hb).2]
      ring
    rw [sum_congr rfl hterm, sum_sub_distrib, ← mul_sum, ← mul_sum, sum_stoppingProb hn s,
      mul_one]
  rw [hform, sum_comm' (t' := Ioc 1 n) (s' := fun k ↦ Ico 1 k)]
  · refine sum_congr rfl fun k hk ↦ ?_
    have hk1 : 1 ≤ k := by
      have h1 := (mem_Ioc.mp hk).1
      omega
    rw [← sum_mul, sum_Ico_stoppingProb (by omega) s k hk1 (mem_Ioc.mp hk).2]
    ring
  · intro b k
    simp only [mem_Icc, mem_Ioc, mem_Ico]
    omega

/-- **The path expectation of the connection time in survival form.** -/
theorem connectionTime_mean_survival {n : ℕ} (hn : 2 ≤ n) (s : Fin n → Fin n) :
    ∫⁻ p, ENNReal.ofReal (connectionTime s p) ∂(trajectoryClockLaw n)
      = ENNReal.ofReal (∑ k ∈ Ioc 1 n, (1 - connectedProb s k) / deathRate k) := by
  rw [connectionTime_mean hn s, mean_eq_sum_survival hn s]

/-! ### The first-step value, level by level -/

/-- A report has at most one block exactly when it is connected. -/
theorem blocks_observed_le_one_iff {n : ℕ} (hn : 0 < n) (s : Fin n → Fin n) (ξ : ER n) :
    blocks (observed s ξ) ≤ 1 ↔ observed s ξ = ⊤ := by
  haveI : NeZero n := ⟨hn.ne'⟩
  constructor
  · intro h
    exact (blocks_eq_one_iff _).mp (le_antisymm h (blocks_pos _))
  · intro h
    rw [h, blocks_top]

/-- **The backward equation's average over covers is the jump kernel.** -/
theorem meanConnectionTime_eq_sum_jumpLaw {n : ℕ} (hn : 0 < n) (s : Fin n → Fin n) {ξ : ER n}
    (hk : 2 ≤ blocks ξ) :
    meanConnectionTime s ξ
      = (if observed s ξ = ⊤ then 0 else 1 / deathRate (blocks ξ))
        + ∑ η : ER n, (jumpLaw ξ η).toReal * meanConnectionTime s η := by
  have hsum : ∑ η : ER n, (jumpLaw ξ η).toReal * meanConnectionTime s η
      = (∑ η : {η : ER n // Covers ξ η}, meanConnectionTime s η.1) / deathRate (blocks ξ) := by
    simp only [jumpLaw_toReal hk, ite_mul, zero_mul]
    rw [← sum_filter, sum_div]
    refine sum_bij' (fun η h ↦ ⟨η, (mem_filter.mp h).2⟩) (fun η _ ↦ η.1)
      (fun _ _ ↦ mem_univ _) (fun η _ ↦ mem_filter.mpr ⟨mem_univ _, η.2⟩) (fun _ _ ↦ rfl)
      (fun _ _ ↦ rfl) fun η _ ↦ ?_
    ring
  rw [hsum, meanConnectionTime_eq s ξ]
  by_cases hc : observed s ξ = ⊤
  · have hzero : ∀ η : {η : ER n // Covers ξ η}, meanConnectionTime s η.1 = 0 := by
      intro η
      have htop : observed s η.1 = ⊤ := top_unique (hc.symm.le.trans (observed_mono s η.2.1))
      rw [meanConnectionTime_eq, if_pos ((blocks_observed_le_one_iff hn s _).mpr htop)]
    rw [if_pos ((blocks_observed_le_one_iff hn s ξ).mpr hc), if_pos hc,
      sum_congr rfl fun η _ ↦ hzero η, sum_const_zero, zero_div, add_zero]
  · rw [if_neg fun h ↦ hc ((blocks_observed_le_one_iff hn s ξ).mp h), if_neg hc, add_div]

/-- The head law in real form: the jump kernel applied to the previous level. -/
theorem blockLaw_succ_toReal {n : ℕ} (j : ℕ) (η : ER n) :
    (blockLaw n (j + 1) η).toReal
      = ∑ ξ : ER n, (blockLaw n j ξ).toReal * (jumpLaw ξ η).toReal := by
  rw [blockLaw_succ, PMF.bind_apply, tsum_fintype, ENNReal.toReal_sum
    fun ξ _ ↦ ENNReal.mul_ne_top (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)]
  exact sum_congr rfl fun ξ _ ↦ ENNReal.toReal_mul

/-- **One level of the first-step value.**  Averaged over the head law after `j` jumps, the
backward equation gives the level's contribution `(1 - F_{n-j})/d_{n-j}` plus the average after
`j + 1` jumps. -/
theorem sum_blockLaw_meanConnectionTime_succ {n j : ℕ} (s : Fin n → Fin n) (hj : j + 1 < n) :
    ∑ ξ : ER n, (blockLaw n j ξ).toReal * meanConnectionTime s ξ
      = (1 - connectedProb s (n - j)) / deathRate (n - j)
        + ∑ η : ER n, (blockLaw n (j + 1) η).toReal * meanConnectionTime s η := by
  have hn : 0 < n := by omega
  have hlevel : ∀ ξ : ER n, (blockLaw n j ξ).toReal * meanConnectionTime s ξ
      = (blockLaw n j ξ).toReal * (if observed s ξ = ⊤ then 0 else 1 / deathRate (n - j))
        + ∑ η : ER n,
          (blockLaw n j ξ).toReal * (jumpLaw ξ η).toReal * meanConnectionTime s η := by
    intro ξ
    by_cases hb : blocks ξ = n - j
    · rw [meanConnectionTime_eq_sum_jumpLaw hn s (by omega : 2 ≤ blocks ξ), hb, mul_add,
        mul_sum]
      simp only [mul_assoc]
    · have hzero : (blockLaw n j ξ).toReal = 0 := by
        rw [blockLaw_toReal j (by omega) ξ, if_neg hb]
      simp only [hzero, zero_mul, sum_const_zero, add_zero]
  have hmass : ∑ ξ : ER n, (blockLaw n j ξ).toReal = 1 := by
    have htsum := PMF.tsum_coe (blockLaw n j)
    rw [tsum_fintype] at htsum
    rw [← ENNReal.toReal_sum fun ξ _ ↦ PMF.apply_ne_top _ _, htsum, ENNReal.toReal_one]
  have hunconnected : (1 : ℝ) - connectedProb s (n - j)
      = ∑ ξ : ER n, (if observed s ξ = ⊤ then 0 else (blockLaw n j ξ).toReal) := by
    rw [connectedProb, show n - (n - j) = j by omega, sum_filter, ← hmass, ← sum_sub_distrib]
    refine sum_congr rfl fun ξ _ ↦ ?_
    by_cases hc : observed s ξ = ⊤ <;> simp [hc]
  have hfirst : ∑ ξ : ER n, (blockLaw n j ξ).toReal
        * (if observed s ξ = ⊤ then 0 else 1 / deathRate (n - j))
      = (1 - connectedProb s (n - j)) / deathRate (n - j) := by
    rw [hunconnected, sum_div]
    refine sum_congr rfl fun ξ _ ↦ ?_
    by_cases hc : observed s ξ = ⊤ <;> simp [hc] <;> ring
  rw [sum_congr rfl fun ξ _ ↦ hlevel ξ, sum_add_distrib, hfirst, sum_comm]
  congr 1
  refine sum_congr rfl fun η _ ↦ ?_
  rw [blockLaw_succ_toReal, sum_mul]

/-- **The first-step value at `k` blocks, unrolled**: averaged over the head law at level `k`, it
is `∑_{i=2}^{k} (1 - F_i)/d_i`. -/
theorem sum_blockLaw_meanConnectionTime {n : ℕ} (s : Fin n → Fin n) :
    ∀ k, 1 ≤ k → k ≤ n → ∑ ξ : ER n, (blockLaw n (n - k) ξ).toReal * meanConnectionTime s ξ
      = ∑ i ∈ Ioc 1 k, (1 - connectedProb s i) / deathRate i := by
  intro k hk
  induction k, hk using Nat.le_induction with
  | base =>
    intro hn
    rw [Ioc_self, sum_empty]
    refine sum_eq_zero fun ξ _ ↦ ?_
    by_cases hb : blocks ξ = 1
    · have htop : observed s ξ = ⊤ := by
        haveI : NeZero n := ⟨by omega⟩
        rw [(blocks_eq_one_iff ξ).mp hb]
        exact top_sup_eq _
      rw [meanConnectionTime_eq, if_pos ((blocks_observed_le_one_iff (by omega) s ξ).mpr htop),
        mul_zero]
    · rw [blockLaw_toReal (n - 1) (by omega) ξ,
        if_neg (show ¬ blocks ξ = n - (n - 1) by omega), zero_mul]
  | succ k hk ih =>
    intro hkn
    rw [sum_blockLaw_meanConnectionTime_succ s (show n - (k + 1) + 1 < n by omega),
      show n - (n - (k + 1)) = k + 1 by omega, show n - (k + 1) + 1 = n - k by omega,
      ih (by omega), sum_Ioc_succ_top (by omega : 1 ≤ k)]
    ring

/-- The first-step mean connection time from `⊥`, unrolled. -/
theorem meanConnectionTime_bot_eq_sum {n : ℕ} (hn : 2 ≤ n) (s : Fin n → Fin n) :
    meanConnectionTime s ⊥ = ∑ k ∈ Ioc 1 n, (1 - connectedProb s k) / deathRate k := by
  have h := sum_blockLaw_meanConnectionTime s n (by omega) le_rfl
  have hlaw : blockLaw n (n - n) = PMF.pure (Delta n) := by
    rw [Nat.sub_self, blockLaw_eq_map, chainLaw, PMF.pure_map]
    rfl
  rw [hlaw, sum_eq_single (Delta n)
    (fun ξ _ hξ ↦ by rw [PMF.pure_apply, if_neg hξ, ENNReal.toReal_zero, zero_mul])
    (fun hmem ↦ absurd (mem_univ _) hmem), PMF.pure_apply, if_pos rfl, ENNReal.toReal_one,
    one_mul] at h
  exact h

/-- **The first-step mean connection time is the path expectation.**  The solution of
`VisibleIntensityClock`'s backward equation at `⊥` is the expectation of the connection time
under the path law of `ReportedConnectionClock`. -/
theorem connectionTime_mean_eq_meanConnectionTime {n : ℕ} (hn : 2 ≤ n) (s : Fin n → Fin n) :
    ∫⁻ p, ENNReal.ofReal (connectionTime s p) ∂(trajectoryClockLaw n)
      = ENNReal.ofReal (meanConnectionTime s ⊥) := by
  rw [connectionTime_mean_survival hn s, meanConnectionTime_bot_eq_sum hn s]

end Descent.Pangenome.GraphCoalescent
