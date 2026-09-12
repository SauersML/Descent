/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Pangenome.GraphCoalescent.ConnectionClockHittingTime
import Descent.Pangenome.GraphCoalescent.ConnectivityCumulantCorpus

assert_below Descent.PopGen Descent.Spectral Descent.Blindness Descent.Conditionals
assert_below Descent.Portability Descent.Decision Descent.Program

/-!
# (C4) as a stochastic order: the report waits out the top `w - 1` Kingman phases

(C4) of the hidden-lineage clock note bounds the reported connection time from below by the
Kingman phases between `n` and `n - w + 1` lineages,

  `Σ_{k=n-w+2}^{n} Exp(d_k) ≤_st τ_q`,

and hence `2/(n - w + 1) - 2/n ≤ E τ_q`.  The mean bound is proved in `VisibleIntensityClock` and
`ConnectionClockPathLaw`.  This file proves the stochastic order on the path law of
`ReportedConnectionClock`, the product of a jump-chain trajectory and an independent Kingman
clock whose coordinates are independent holding times `H_k ~ Exp(d_k)`.

The reason is the block count.  A report `q ⊔ π` can be connected only when `π` has at most
`n - w + 1` blocks (`blocks_add_width_le_of_observed_eq_top`, through the partition-lattice bound
of `ConnectivityCumulantDegree`).  So the stopping level `B` of a trajectory, the number of true
lineages right after the report first connects, is at most `n - w + 1`
(`stoppingLevel_add_width_le`).  The connection time is the sum of the holding times at the
levels `B + 1, …, n`, so it contains the phases `n - w + 2, …, n` on every path
(`sum_top_levels_le_connectionTime`) and almost surely under the path law
(`ae_sum_top_levels_le_connectionTime`).  Every survival probability of the top phases is then at
most that of the connection time (`kingmanClock_sum_top_levels_lt_le`).

Scope.  The stochastic order is stated for the connection time of the trajectory clock, which is
almost surely the first time the report of the coalescent path reaches `⊤`
(`ConnectionClockHittingTime`).  The comparison is pathwise on one probability space, so no
quantile coupling is involved.

## Empirical status

None.  The bodies compare finite sums of clock coordinates on a fixed product measure, so no
measurement can bear on them.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Pangenome.GraphCoalescent.ConnectionClockLowerBound

open Coalescent Finset MeasureTheory
open scoped Classical

/-- **A connected report needs few true blocks.**  If the report of an interface of width `w`
on `n ≥ 1` individuals is connected at a state `π`, then `π` has at most `n - w + 1` blocks. -/
theorem blocks_add_width_le_of_observed_eq_top {n : ℕ} (hn : 0 < n) (s : Fin n → Fin n)
    {π : ER n} (h : observed s π = ⊤) : blocks π + Linkage.width s ≤ n + 1 := by
  have hs : (univ : Finset (Fin n)).Nonempty := ⟨⟨0, hn⟩, mem_univ _⟩
  have hbound := card_parts_add_card_parts_le_of_connected (Finpartition.ofSetoid (graphKer s))
    (Finpartition.ofSetoid π) hs ((observed_eq_top_iff_reportConnected s π).mp h)
  simp only [card_parts_ofSetoid, blocks_graphKer, card_univ, Fintype.card_fin] at hbound
  omega

/-- **The stopping level is at most `n - w + 1`.**  The report of a trajectory's `B`-block state
is connected, so `B + w ≤ n + 1`. -/
theorem stoppingLevel_add_width_le {n : ℕ} (hn : 2 ≤ n) (s : Fin n → Fin n)
    {l : List (ER n)} (hl : l ∈ (chainLaw n (n - 1)).support) :
    stoppingLevel s l + Linkage.width s ≤ n + 1 := by
  have hmem := mem_Icc.mp (stoppingLevel_mem_Icc hn s hl)
  have hconn : observed s (chainOfList l (stoppingLevel s l)) = ⊤ := by
    rcases lt_or_eq_of_le hmem.2 with hlt | heq
    · exact ((stoppingLevel_eq_iff (s := s) hl hmem.1 hlt).mp rfl).1
    · rw [heq]
      exact (stoppingLevel_eq_self_iff (by omega)).mp heq
  have hbound := blocks_add_width_le_of_observed_eq_top (by omega) s hconn
  rwa [blocks_chainOfList (by omega) hl hmem.1 hmem.2] at hbound

/-- **On every path the connection time contains the top `w - 1` phases**: with nonnegative
holding times, `Σ_{k=n-w+2}^{n} H_k ≤ τ_q`, the clock coordinates `n - w, …, n - 2` being the
levels `n - w + 2, …, n`. -/
theorem sum_top_levels_le_connectionTime {n : ℕ} (hn : 2 ≤ n) (s : Fin n → Fin n)
    {p : List (ER n) × (ℕ → ℝ)} (hl : p.1 ∈ (chainLaw n (n - 1)).support)
    (hclock : ∀ j, 0 ≤ p.2 j) :
    ∑ j ∈ Ico (n - Linkage.width s) (n - 1), p.2 j ≤ connectionTime s p := by
  have hle := stoppingLevel_add_width_le hn s hl
  have hmem := mem_Icc.mp (stoppingLevel_mem_Icc hn s hl)
  rw [connectionTime]
  exact sum_le_sum_of_subset_of_nonneg (Ico_subset_Ico (by omega) le_rfl) fun j _ _ ↦ hclock j

/-- The top `w - 1` phases are at most the connection time, almost surely under the path law. -/
theorem ae_sum_top_levels_le_connectionTime {n : ℕ} (hn : 2 ≤ n) (s : Fin n → Fin n) :
    ∀ᵐ p ∂(trajectoryClockLaw n),
      ∑ j ∈ Ico (n - Linkage.width s) (n - 1), p.2 j ≤ connectionTime s p :=
  ae_mem_support_nonneg.mono fun _ hp ↦ sum_top_levels_le_connectionTime hn s hp.1 hp.2

/-- **(C4), the stochastic order**: `Σ_{k=n-w+2}^{n} Exp(d_k) ≤_st τ_q`.  For every threshold
`c`, the probability that the independent Kingman phases `n - w + 2, …, n` last longer than `c`
is at most the probability that the report is still unconnected at `c`. -/
theorem kingmanClock_sum_top_levels_lt_le {n : ℕ} (hn : 2 ≤ n) (s : Fin n → Fin n) (c : ℝ) :
    kingmanClock {ω : ℕ → ℝ | c < ∑ j ∈ Ico (n - Linkage.width s) (n - 1), ω j}
      ≤ trajectoryClockLaw n {p | c < connectionTime s p} := by
  have hmarginal :
      kingmanClock {ω : ℕ → ℝ | c < ∑ j ∈ Ico (n - Linkage.width s) (n - 1), ω j}
        = trajectoryClockLaw n
            (Set.univ ×ˢ {ω : ℕ → ℝ | c < ∑ j ∈ Ico (n - Linkage.width s) (n - 1), ω j}) := by
    rw [trajectoryClockLaw_prod, measure_univ, one_mul]
  rw [hmarginal]
  refine measure_mono_ae ?_
  filter_upwards [ae_sum_top_levels_le_connectionTime hn s] with p hp hpc
  exact lt_of_lt_of_le (Set.mem_prod.mp hpc).2 hp

end Descent.Pangenome.GraphCoalescent.ConnectionClockLowerBound
