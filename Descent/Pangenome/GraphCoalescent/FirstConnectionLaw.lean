/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Pangenome.GraphCoalescent.RankedHistoryLaw
import Descent.Pangenome.GraphCoalescent.ConnectivityCumulantCorpus
import Descent.Pangenome.GraphCoalescent.ConnectivityClockTable

assert_below Descent.PopGen Descent.Spectral Descent.Blindness Descent.Conditionals
assert_below Descent.Portability Descent.Decision Descent.Program

/-!
# The first-connection law of a pangenome report: (D5) and (D6)

Theorem D of the pangenome hidden-clock note turns the connectivity cumulant into the law of
the moment the report connects. Let `Π^(k)` be the state of Kingman's embedded jump chain on
first reaching `k` blocks, and `F_k` the probability that its report `observed s Π^(k)` is
connected. (D5) says `F_k = a_{n,k} [z^k] C_q(z)`, and (D6) says that the number `B` of true
lineages right after the report first connects has law `Pr(B = b) = F_b − F_{b+1}`, with
`F_1 = 1` and `F_n = 0` when the interface has width at least two.

`ConnectivityClockTable` transcribes both right-hand sides as formulas,
`ConnectivityClockTable.connectedByLevel` and `ConnectivityClockTable.firstConnectionLaw`, and
evaluates them at the tabulated fiber sizes. This module proves that they are the law of the
jump chain. `reportConnectedProbability s k` is `F_k` as a probability: the sum over coalescent
states of the corpus law `Coalescent.blockLaw n (n − k)` against the indicator of a connected
report. `reportConnectedProbability_eq_connectedByLevel` is (D5). It combines the ranked history
law `RankedHistoryLaw.blockLaw_toReal`, which gives the jump chain's law on the `k`-block level
as `a_{n,k} ∏_B |B|!`, with (D3) in the corpus vocabulary,
`ConnectivityCumulantCorpus.connectivityCumulant_graphKer_eq_sum_observed`, read at the
coefficient of `z^k`. The boundary values are `reportConnectedProbability_one` and
`reportConnectedProbability_self`, and `reportConnectedProbability_eq_zero_of_degree_lt` shows
that `F_k` vanishes above the cumulant's degree `n + 1 − w`, so the report first connects at
some `b ≤ n − w + 1`.

`firstConnectionProbability s b` is the probability that the report is not connected at the
`(b + 1)`-block level and is connected at the `b`-block level, computed from the joint law of
two consecutive states of the chain: the law at `b + 1` blocks followed by one jump
`Coalescent.jumpLaw`. `firstConnectionProbability_eq_sub` is (D6). A jump never undoes a
coalescence (`le_of_mem_support_jumpLaw`) and the report is monotone (`observed_mono`), so a
connected report stays connected along every jump; that turns the indicator of first
connection into the difference of two level indicators, and `RankedHistoryLaw.blockLaw_succ`
turns the two resulting sums into `F_b` and `F_{b+1}`.
`firstConnectionProbability_eq_firstConnectionLaw` states (D6) against the table's formula.

Not formalised here: the holding times and the transforms (D7)–(D9) built on this law.

## Empirical status

None. The bodies here are finite sums of the jump chain's law against report indicators, so
no measurement on any pangenome can bear on them.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Pangenome.GraphCoalescent

open Finset Coalescent
open scoped Classical

noncomputable section

/-- `F_k` as a probability: the probability that the report of the jump chain's state on first
reaching `k` blocks is connected. -/
def reportConnectedProbability {n : ℕ} (s : Fin n → Fin n) (k : ℕ) : ℝ :=
  ∑ π : ER n, (blockLaw n (n - k) π).toReal * if observed s π = ⊤ then 1 else 0

/-- **(D5).** For `1 ≤ k ≤ n`, the report of the jump chain's state at the `k`-block level is
connected with probability `a_{n,k} [z^k] C_q(z)`, where `C_q` is the connectivity cumulant of
the interface kernel `q = graphKer s`: the table's formula is the law. -/
theorem reportConnectedProbability_eq_connectedByLevel {n : ℕ} (s : Fin n → Fin n) {k : ℕ}
    (hk : 1 ≤ k) (hkn : k ≤ n) :
    reportConnectedProbability s k = ConnectivityClockTable.connectedByLevel
      (connectivityCumulant (Finpartition.ofSetoid (graphKer s))) n k := by
  have hlaw : ∀ π : ER n, (blockLaw n (n - k) π).toReal =
      if blocks π = k then jumpCoeff n k * (blockWeight (Finpartition.ofSetoid π) : ℝ)
      else 0 := by
    intro π
    rw [blockLaw_toReal (n - k) (by omega) π, show n - (n - k) = k by omega,
      rankWeight_eq_blockWeight]
  have hcoeff : ((connectivityCumulant (Finpartition.ofSetoid (graphKer s))).coeff k : ℝ) =
      ∑ π ∈ univ.filter (fun π : ER n ↦ observed s π = ⊤),
        if blocks π = k then (blockWeight (Finpartition.ofSetoid π) : ℝ) else 0 := by
    rw [connectivityCumulant_graphKer_eq_sum_observed s (by omega),
      Polynomial.finset_sum_coeff, Int.cast_sum]
    refine sum_congr (by ext π; simp) fun π _ ↦ ?_
    rw [Polynomial.coeff_C_mul_X_pow]
    split_ifs with hleft hright hright
    · simp
    · exact absurd hleft.symm hright
    · exact absurd hright.symm hleft
    · simp
  unfold reportConnectedProbability
  rw [ConnectivityClockTable.connectedByLevel, hcoeff, Finset.mul_sum, sum_filter]
  refine sum_congr (by ext π; simp) fun π _ ↦ ?_
  rw [hlaw π]
  split_ifs <;> simp

/-- At the one-block level the chain is at the top state, and the report is connected with
probability one: `F_1 = 1`. -/
theorem reportConnectedProbability_one {n : ℕ} [NeZero n] (s : Fin n → Fin n) :
    reportConnectedProbability s 1 = 1 := by
  have hmass : ∑ π : ER n, (blockLaw n (n - 1) π).toReal = 1 := by
    rw [← ENNReal.toReal_sum fun π _ ↦ PMF.apply_ne_top _ _, ← tsum_fintype, PMF.tsum_coe,
      ENNReal.toReal_one]
  rw [← hmass]
  unfold reportConnectedProbability
  refine sum_congr rfl fun π _ ↦ ?_
  by_cases hmem : π ∈ (blockLaw n (n - 1)).support
  · have hblocks := blocks_of_mem_support_blockLaw (by have := NeZero.pos n; omega) hmem
    have htop : π = ⊤ := (blocks_eq_one_iff π).mp (by omega)
    have hreport : observed s π = ⊤ := by
      rw [htop]
      exact eq_top_iff.mpr (le_observed s ⊤)
    rw [if_pos hreport, mul_one]
  · rw [(PMF.apply_eq_zero_iff _ _).mpr hmem, ENNReal.toReal_zero, zero_mul]

/-- At the `n`-block level the chain has not moved, and its report is the interface kernel,
which is not connected when the interface has width at least two: `F_n = 0`. -/
theorem reportConnectedProbability_self {n : ℕ} (s : Fin n → Fin n)
    (hwidth : 2 ≤ Linkage.width s) : reportConnectedProbability s n = 0 := by
  have hlaw : blockLaw n 0 = PMF.pure (Delta n) := by
    rw [blockLaw_eq_map, chainLaw, PMF.pure_map]
    rfl
  have hreport : observed s (Delta n) ≠ ⊤ := by
    intro htop
    have hn : NeZero n := ⟨by
      have hle := blocks_graphKer_le s
      rw [blocks_graphKer] at hle
      omega⟩
    have hkernel : graphKer s = ⊤ := by
      rw [← observed_bot s]
      exact htop
    have hwidthOne : Linkage.width s = 1 := by
      rw [← blocks_graphKer, hkernel]
      exact blocks_top n
    omega
  unfold reportConnectedProbability
  rw [Nat.sub_self, hlaw]
  refine sum_eq_zero fun π _ ↦ ?_
  by_cases hπ : π = Delta n
  · rw [hπ, if_neg hreport, mul_zero]
  · rw [PMF.pure_apply, if_neg hπ, ENNReal.toReal_zero, zero_mul]

/-- Above the degree of the cumulant the report is never connected: for `n + 1 − w < k ≤ n`,
`F_k = 0`, so the report first connects at some `b ≤ n − w + 1`. -/
theorem reportConnectedProbability_eq_zero_of_degree_lt {n : ℕ} (s : Fin n → Fin n) {k : ℕ}
    (hk : n + 1 - Linkage.width s < k) (hkn : k ≤ n) :
    reportConnectedProbability s k = 0 := by
  have hpos : 1 ≤ k := by omega
  rw [reportConnectedProbability_eq_connectedByLevel s hpos hkn,
    ConnectivityClockTable.connectedByLevel,
    Polynomial.coeff_eq_zero_of_natDegree_lt
      (lt_of_le_of_lt (natDegree_connectivityCumulant_graphKer_le s (by omega)) hk),
    Int.cast_zero, mul_zero]

/-- A jump of the chain never undoes a coalescence: every state it can reach dominates the
current one. -/
theorem le_of_mem_support_jumpLaw {n : ℕ} {ξ η : ER n} (h : η ∈ (jumpLaw ξ).support) :
    ξ ≤ η := by
  by_cases hk : 2 ≤ blocks ξ
  · exact ((mem_support_jumpLaw hk).mp h).1
  · rw [(mem_support_jumpLaw_of_absorbed (by omega)).mp h]

/-- The probability that the report first becomes connected when the jump chain passes from
`b + 1` blocks to `b` blocks: not connected at the `(b + 1)`-block level, connected after one
more jump. -/
def firstConnectionProbability {n : ℕ} (s : Fin n → Fin n) (b : ℕ) : ℝ :=
  ∑ ξ : ER n, ∑ η : ER n, (blockLaw n (n - (b + 1)) ξ).toReal * (jumpLaw ξ η).toReal *
    if observed s ξ ≠ ⊤ ∧ observed s η = ⊤ then 1 else 0

/-- **(D6).** The report first connects at the `b`-block level with probability
`F_b − F_{b+1}`. -/
theorem firstConnectionProbability_eq_sub {n : ℕ} (s : Fin n → Fin n) {b : ℕ} (hb : 1 ≤ b)
    (hbn : b + 1 ≤ n) :
    firstConnectionProbability s b =
      reportConnectedProbability s b - reportConnectedProbability s (b + 1) := by
  have hstep : ∀ η : ER n, (blockLaw n (n - b) η).toReal =
      ∑ ξ : ER n, (blockLaw n (n - (b + 1)) ξ).toReal * (jumpLaw ξ η).toReal := by
    intro η
    rw [show n - b = n - (b + 1) + 1 by omega, blockLaw_succ, PMF.bind_apply, tsum_fintype,
      ENNReal.toReal_sum fun ξ _ ↦ ENNReal.mul_ne_top (PMF.apply_ne_top _ _)
        (PMF.apply_ne_top _ _)]
    exact sum_congr rfl fun ξ _ ↦ ENNReal.toReal_mul
  have hjumpMass : ∀ ξ : ER n, ∑ η : ER n, (jumpLaw ξ η).toReal = 1 := by
    intro ξ
    rw [← ENNReal.toReal_sum fun η _ ↦ PMF.apply_ne_top _ _, ← tsum_fintype, PMF.tsum_coe,
      ENNReal.toReal_one]
  have hterm : ∀ ξ η : ER n,
      (blockLaw n (n - (b + 1)) ξ).toReal * (jumpLaw ξ η).toReal *
          (if observed s ξ ≠ ⊤ ∧ observed s η = ⊤ then 1 else 0) =
        (blockLaw n (n - (b + 1)) ξ).toReal * (jumpLaw ξ η).toReal *
            (if observed s η = ⊤ then 1 else 0) -
          (blockLaw n (n - (b + 1)) ξ).toReal * (jumpLaw ξ η).toReal *
            (if observed s ξ = ⊤ then 1 else 0) := by
    intro ξ η
    by_cases hjump : (jumpLaw ξ η).toReal = 0
    · rw [hjump]
      ring
    · have hle : ξ ≤ η := le_of_mem_support_jumpLaw
        ((PMF.mem_support_iff _ _).mpr fun hzero ↦ hjump (by rw [hzero, ENNReal.toReal_zero]))
      by_cases hsource : observed s ξ = ⊤
      · have htarget : observed s η = ⊤ :=
          eq_top_iff.mpr (by rw [← hsource]; exact observed_mono s hle)
        rw [if_neg fun hboth ↦ hboth.1 hsource, if_pos htarget, if_pos hsource]
        ring
      · by_cases htarget : observed s η = ⊤
        · rw [if_pos ⟨hsource, htarget⟩, if_pos htarget, if_neg hsource]
          ring
        · rw [if_neg fun hboth ↦ htarget hboth.2, if_neg htarget, if_neg hsource]
          ring
  have hfirst : ∑ ξ : ER n, ∑ η : ER n, (blockLaw n (n - (b + 1)) ξ).toReal *
      (jumpLaw ξ η).toReal * (if observed s η = ⊤ then 1 else 0) =
        reportConnectedProbability s b := by
    unfold reportConnectedProbability
    rw [sum_comm]
    refine sum_congr rfl fun η _ ↦ ?_
    rw [← sum_mul, ← hstep η]
  have hsecond : ∑ ξ : ER n, ∑ η : ER n, (blockLaw n (n - (b + 1)) ξ).toReal *
      (jumpLaw ξ η).toReal * (if observed s ξ = ⊤ then 1 else 0) =
        reportConnectedProbability s (b + 1) := by
    unfold reportConnectedProbability
    refine sum_congr rfl fun ξ _ ↦ ?_
    rw [← sum_mul, ← Finset.mul_sum, hjumpMass ξ, mul_one]
  unfold firstConnectionProbability
  rw [sum_congr rfl fun ξ _ ↦ sum_congr rfl fun η _ ↦ hterm ξ η]
  simp only [sum_sub_distrib]
  rw [hfirst, hsecond]

/-- **(D6) against the table's formula.** For `1 ≤ b < n`, the probability that the report first
connects at the `b`-block level is the transcribed law
`p_b = a_{n,b} [z^b] C_q − a_{n,b+1} [z^(b+1)] C_q`. -/
theorem firstConnectionProbability_eq_firstConnectionLaw {n : ℕ} (s : Fin n → Fin n) {b : ℕ}
    (hb : 1 ≤ b) (hbn : b + 1 ≤ n) :
    firstConnectionProbability s b = ConnectivityClockTable.firstConnectionLaw
      (connectivityCumulant (Finpartition.ofSetoid (graphKer s))) n b := by
  rw [firstConnectionProbability_eq_sub s hb hbn,
    reportConnectedProbability_eq_connectedByLevel s hb (by omega),
    reportConnectedProbability_eq_connectedByLevel s (by omega) hbn,
    ConnectivityClockTable.firstConnectionLaw]

end

end Descent.Pangenome.GraphCoalescent
