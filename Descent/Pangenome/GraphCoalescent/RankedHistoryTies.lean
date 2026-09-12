/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Pangenome.GraphCoalescent.FirstConnectionLaw
import Descent.Pangenome.GraphCoalescent.LeadingCoefficient
import Descent.Pangenome.GraphCoalescent.ReportedConnectionFirstStep

assert_below Descent.PopGen Descent.Spectral Descent.Blindness Descent.Conditionals
assert_below Descent.Portability Descent.Decision Descent.Program

/-!
# Ranked merger histories under the jump chain: (D4), (D5) and (E1) by counting

The pangenome note proves (D4) by counting ranked merger sequences and reads the top coefficient
of the connectivity cumulant through the same law.  In the corpus `RankedHistoryLaw` proves (D4)
by Kingman's backward recursion, `FirstConnectionLaw` proves (D5) from it, and
`LeadingCoefficient` proves (E1) from the Möbius sum.  This file supplies the counting route and
ties it to all three.

- `rankedHistoryCount m η` is the number of ranked merger histories
  `Δ = ξ₀ ≺ ξ₁ ≺ ⋯ ≺ ξ_m = η` of `m` mergers from the singletons to `η`, counted by their last
  merger; such a history ends at `n - m` blocks (`rankedHistoryCount_eq_zero_of_blocks_ne`).
- `two_pow_mul_rankedHistoryCount`: **the count**.  A state `η` with `n - m` blocks is reached by
  `m! ∏_{B∈η} |B|! / 2^m` ranked histories, through the weighted cover count
  `RankedHistoryLaw.two_mul_sum_rankWeight_covers`.
- `blockLaw_toReal_eq_rankedHistoryCount`: **(D4) as a sum over ranked merger sequences**.  Every
  history of `m` mergers has probability `∏_{j<m} 1/C(n - j, 2)` under the jump chain, so after
  `m < n` jumps the chain is at `η` with probability `#histories(Δ → η) ∏_{j<m} 1/d_{n-j}`.
- `reportConnectedProbability_eq_sum_rankedHistoryCount`: **(D5) as a sum over ranked merger
  sequences**.  `F_k` of `FirstConnectionLaw` is the mass of the histories of `n - k` mergers whose
  final report is connected.
- `reportConnectedProbability_eq_jumpCoeff_mul_leadingCoefficient`: **(E1) through the history
  law**.  At the lowest level where the report can be connected, `k = n - w + 1`, the probability
  that it is connected is `a_{n,k} · 2 (∏_i c_i) (2n - w)! / (2n - 2w + 2)!`.
- `sum_rankedHistoryCount_mul_prod_eq_leadingCoefficient`: the same top coefficient as the
  probability mass of the ranked histories of `w - 1` mergers that connect the report.

## Empirical status

None.  The bodies are counts of chains of finite equivalence relations and finite sums of the
jump chain's law, so no measurement can bear on them.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Pangenome.GraphCoalescent.RankedHistoryTies

open Coalescent Finset
open scoped Classical

noncomputable section

/-! ## Counting ranked merger histories -/

/-- The number of ranked merger histories of `m` mergers from the singletons `Δ` to `η`: the
chains of covers `Δ = ξ₀ ≺ ξ₁ ≺ ⋯ ≺ ξ_m = η`, counted by their last merger. -/
def rankedHistoryCount {n : ℕ} : ℕ → ER n → ℕ
  | 0, η => if η = Delta n then 1 else 0
  | m + 1, η => ∑ ξ : ER n, if Covers ξ η then rankedHistoryCount m ξ else 0

/-- A ranked history of `m` mergers ends at `n - m` blocks. -/
theorem rankedHistoryCount_eq_zero_of_blocks_ne {n : ℕ} :
    ∀ m, m < n → ∀ η : ER n, blocks η + m ≠ n → rankedHistoryCount m η = 0 := by
  intro m
  induction m with
  | zero =>
    intro _ η hη
    have hne : η ≠ Delta n := by
      rintro rfl
      exact hη (by rw [blocks_bot, add_zero])
    simp [rankedHistoryCount, hne]
  | succ m ih =>
    intro hm η hη
    rw [rankedHistoryCount]
    refine sum_eq_zero fun ξ _ ↦ ?_
    split_ifs with hcov
    · exact ih (by omega) ξ (by have := hcov.2; omega)
    · rfl

/-- **The count of ranked merger histories.**  A state `η` with `n - m` blocks is reached by
`m! ∏_{B∈η} |B|! / 2^m` ranked histories of `m` mergers from the singletons. -/
theorem two_pow_mul_rankedHistoryCount {n : ℕ} :
    ∀ m, m < n → ∀ η : ER n, blocks η + m = n →
      2 ^ m * rankedHistoryCount m η = m.factorial * rankWeight η := by
  intro m
  induction m with
  | zero =>
    intro _ η hη
    have heq : Delta n = η := eq_of_le_of_blocks_eq bot_le (by rw [blocks_bot]; omega)
    subst heq
    rw [rankedHistoryCount, if_pos rfl, rankWeight_bot]
  | succ m ih =>
    intro hm η hη
    have hterm : ∀ ξ : ER n,
        2 * (2 ^ m * (if Covers ξ η then rankedHistoryCount m ξ else 0))
          = m.factorial * (2 * (if Covers ξ η then rankWeight ξ else 0)) := by
      intro ξ
      split_ifs with hcov
      · rw [ih (by omega) ξ (by have := hcov.2; omega)]
        ring
      · simp
    calc 2 ^ (m + 1) * rankedHistoryCount (m + 1) η
        = ∑ ξ : ER n, 2 * (2 ^ m * (if Covers ξ η then rankedHistoryCount m ξ else 0)) := by
          rw [rankedHistoryCount, ← mul_sum, ← mul_sum, pow_succ]
          ring
      _ = ∑ ξ : ER n, m.factorial * (2 * (if Covers ξ η then rankWeight ξ else 0)) :=
          sum_congr rfl fun ξ _ ↦ hterm ξ
      _ = m.factorial * (2 * ∑ ξ ∈ univ.filter (fun ξ ↦ Covers ξ η), rankWeight ξ) := by
          rw [sum_filter, ← mul_sum, ← mul_sum]
      _ = m.factorial * ((n - blocks η) * rankWeight η) := by
          rw [two_mul_sum_rankWeight_covers]
      _ = (m + 1).factorial * rankWeight η := by
          rw [show n - blocks η = m + 1 by omega, Nat.factorial_succ]
          ring

/-! ## (D4) and (D5) as sums over ranked merger sequences -/

/-- **(D4) as a sum over ranked merger sequences.**  Every ranked history of `m` mergers has
probability `∏_{j<m} 1/C(n - j, 2)` under the jump chain, so after `m < n` jumps from `Δ` the
chain is at `η` with probability `#histories(Δ → η) ∏_{j<m} 1/d_{n-j}`. -/
theorem blockLaw_toReal_eq_rankedHistoryCount {n : ℕ} :
    ∀ m, m < n → ∀ η : ER n,
      (blockLaw n m η).toReal
        = rankedHistoryCount m η * ∏ j ∈ range m, 1 / deathRate (n - j) := by
  intro m
  induction m with
  | zero =>
    intro _ η
    have hlaw : blockLaw n 0 = PMF.pure (Delta n) := by
      rw [blockLaw_eq_map, chainLaw, PMF.pure_map]
      rfl
    rw [hlaw, PMF.pure_apply, rankedHistoryCount, prod_range_zero, mul_one]
    split_ifs <;> simp
  | succ m ih =>
    intro hm η
    rw [blockLaw_succ_toReal, rankedHistoryCount, Nat.cast_sum, sum_mul, prod_range_succ]
    refine sum_congr rfl fun ξ _ ↦ ?_
    rw [ih (by omega) ξ]
    by_cases hξ : blocks ξ + m = n
    · rw [jumpLaw_toReal (by omega) η]
      split_ifs
      · rw [show blocks ξ = n - m by omega]
        push_cast
        ring
      · simp
    · rw [rankedHistoryCount_eq_zero_of_blocks_ne m (by omega) ξ hξ]
      simp

/-- **(D5) as a sum over ranked merger sequences.**  The report of the jump chain's `k`-block
state is connected with the probability mass of the ranked histories of `n - k` mergers whose
final report is connected. -/
theorem reportConnectedProbability_eq_sum_rankedHistoryCount {n : ℕ} (s : Fin n → Fin n) {k : ℕ}
    (hk : 1 ≤ k) (hkn : k ≤ n) :
    reportConnectedProbability s k
      = (∑ η ∈ univ.filter (fun η : ER n ↦ observed s η = ⊤),
          (rankedHistoryCount (n - k) η : ℝ)) * ∏ j ∈ range (n - k), 1 / deathRate (n - j) := by
  rw [reportConnectedProbability, sum_mul, sum_filter]
  refine sum_congr rfl fun η _ ↦ ?_
  rw [blockLaw_toReal_eq_rankedHistoryCount (n - k) (by omega) η]
  split_ifs <;> simp

/-! ## (E1) through the history law -/

/-- **(E1) through the history law.**  For an interface of width `w ≥ 2`, the report of the jump
chain's state on first reaching `n - w + 1` blocks is connected with probability
`a_{n,n-w+1}` times the top coefficient `2 (∏_i c_i) (2n - w)! / (2n - 2w + 2)!`. -/
theorem reportConnectedProbability_eq_jumpCoeff_mul_leadingCoefficient {n : ℕ}
    (s : Fin n → Fin n) (hw : 2 ≤ Linkage.width s) :
    reportConnectedProbability s (n - Linkage.width s + 1)
      = jumpCoeff n (n - Linkage.width s + 1)
          * (leadingCoefficient (Finpartition.ofSetoid (graphKer s)).parts (fun t ↦ #t) : ℝ) := by
  have hwn : Linkage.width s ≤ n := by
    simpa [blocks_graphKer] using blocks_graphKer_le s
  have hparts : #(Finpartition.ofSetoid (graphKer s)).parts = Linkage.width s := by
    simp only [card_parts_ofSetoid, blocks_graphKer]
  have htop := coeff_connectivityCumulant_top (Finpartition.ofSetoid (graphKer s))
    (by rw [hparts]; exact hw)
  rw [card_univ, Fintype.card_fin, hparts] at htop
  rw [reportConnectedProbability_eq_connectedByLevel s (by omega) (by omega),
    ConnectivityClockTable.connectedByLevel, ← htop, Rat.cast_intCast]

/-- **The top coefficient as a weighted count of ranked histories.**  The ranked histories of
`w - 1` mergers from the singletons that connect the report, weighted by their probability under
the jump chain, have total mass `a_{n,n-w+1}` times the top coefficient of the cumulant. -/
theorem sum_rankedHistoryCount_mul_prod_eq_leadingCoefficient {n : ℕ} (s : Fin n → Fin n)
    (hw : 2 ≤ Linkage.width s) :
    (∑ η ∈ univ.filter (fun η : ER n ↦ observed s η = ⊤),
        (rankedHistoryCount (Linkage.width s - 1) η : ℝ))
        * ∏ j ∈ range (Linkage.width s - 1), 1 / deathRate (n - j)
      = jumpCoeff n (n - Linkage.width s + 1)
          * (leadingCoefficient (Finpartition.ofSetoid (graphKer s)).parts (fun t ↦ #t) : ℝ) := by
  have hwn : Linkage.width s ≤ n := by
    simpa [blocks_graphKer] using blocks_graphKer_le s
  rw [← reportConnectedProbability_eq_jumpCoeff_mul_leadingCoefficient s hw,
    reportConnectedProbability_eq_sum_rankedHistoryCount s (by omega) (by omega),
    show n - (n - Linkage.width s + 1) = Linkage.width s - 1 by omega]

end

end Descent.Pangenome.GraphCoalescent.RankedHistoryTies
