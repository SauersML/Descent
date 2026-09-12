/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Coalescent.HoldingSecondMoment
import Descent.Coalescent.TransitTransform
import Descent.Pangenome.GraphCoalescent.Observation
import Descent.Pangenome.GraphCoalescent.RankedHistoryLaw

assert_below Descent.PopGen Descent.Spectral Descent.Blindness Descent.Conditionals
assert_below Descent.Portability Descent.Decision Descent.Program

/-!
# The reported connection clock: stopping level, transform and moments

A graph built at interface `s` reports `observed s Π_t = Π_t ⊔ graphKer s` of the panel's
Kingman coalescent `Π_t`, started at `⊥`.  The reported connection time `τ_q` is the first
time the report is `⊤`.  This file proves equations (D5)-(D9) of §6 of the pangenome
hidden-clock note: the law of the number `B` of true lineages right after the report first
connects, and the Laplace transform, mean and second moment of `τ_q`.

## The model, and what represents the continuous-time path

The continuous-time path is represented through its two independent factors, K-G section 6's
construction: a jump-chain trajectory of `n - 1` jumps from `Δ`
(`Descent.Coalescent.Trajectory.chainLaw`) and a clock with one independent exponential holding
time per level (`Descent.Coalescent.EntranceLaw.holdProduct` at Kingman's ladder).
`trajectoryClockLaw n` is their product measure, so the independence is arranged, as in
`Descent.Coalescent.Law`.  On a trajectory the report is connected at levels `1, …, B` and not
above (`stoppingLevel_eq_iff`), and `connectionTime` is the sum of the holding times at levels
`B + 1, …, n` (`connectionTime_of_stoppingLevel`).  That this sum is the first hitting time of
`⊤` by the report of the path `R_t = ℛ_{D(n,t)}` of `Descent.Coalescent.Path` is the pathwise
reading of the definition and is not proved here.

## Main results

- `connectionCount`, `connectedProb`, `connectedProb_eq`: **(D5)**, `F_k = a_{n,k} [z^k] C_c(z)`,
  with `[z^k] C_c(z)` counted as the weight `∏_B |B|!` of the connected `k`-block partitions.
  `connectedProb_one` and `connectedProb_self` are `F_1 = 1` and `F_n = 0` for width `≥ 2`.
- `stoppingLevel`, `stoppingLaw`, `stoppingProb`, `stoppingProb_eq`: **(D6)**,
  `p_b = Pr(B = b) = F_b - F_{b+1}`, with `stoppingProb_self` at `b = n`.
- `trajectoryClockLaw`, `connectionTime`, `lintegral_trajectoryClockLaw`: the path law, and the
  mixture over `B` it produces.
- `connectionTime_laplace`: **(D7)**, `E e^{-θ τ_q} = ∑_b p_b ∏_{k=b+1}^{n} d_k/(d_k + θ)`.
- `connectionTime_mean`: **(D8)**, `E τ_q = 2 ∑_b p_b / b - 2/n`.
- `connectionTime_secondMoment`: **(D9)**,
  `E τ_q² = ∑_b p_b [(2/b - 2/n)² + ∑_{k=b+1}^{n} d_k⁻²]`.

## What is narrower than the note

The expectations are lower Lebesgue integrals of `ENNReal.ofReal` of the time, which is the
expectation of a nonnegative random variable; the clock is almost surely nonnegative
(`ae_nonneg_kingmanClock`).  The spectral remark after (D9) and the exact example means are not
in this file.

## Empirical status

None.  Every declaration is a statement about the jump-chain law, the exponential clock and
their product measure, all built from K-C (1.3) and (1.7); whether a real genealogy is
Kingman's is the modelling premise of those modules.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Pangenome.GraphCoalescent

open Finset Coalescent MeasureTheory ProbabilityTheory
open scoped Classical Nat ENNReal

/-! ### The connection probabilities `F_k` -/

/-- **`[z^k] C_c(z)`, counted over `𝓔ₙ`**: the Kingman weights `∏_B |B|!` of the `k`-block
partitions whose report at interface `s` is connected, the right side of (D3) at `z^k`. -/
noncomputable def connectionCount {n : ℕ} (s : Fin n → Fin n) (k : ℕ) : ℕ :=
  ∑ π ∈ univ.filter (fun π : ER n ↦ blocks π = k ∧ observed s π = ⊤),
    blockWeight (Finpartition.ofSetoid π)

/-- **`F_k`**: the probability that the report is connected when the jump chain first has `k`
blocks. -/
noncomputable def connectedProb {n : ℕ} (s : Fin n → Fin n) (k : ℕ) : ℝ :=
  ∑ π ∈ univ.filter (fun π : ER n ↦ observed s π = ⊤), (blockLaw n (n - k) π).toReal

theorem connectedProb_nonneg {n : ℕ} (s : Fin n → Fin n) (k : ℕ) : 0 ≤ connectedProb s k :=
  sum_nonneg fun _ _ ↦ ENNReal.toReal_nonneg

/-- **(D5)**: `F_k = a_{n,k} [z^k] C_c(z)`. -/
theorem connectedProb_eq {n k : ℕ} (s : Fin n → Fin n) (hk : 1 ≤ k) (hkn : k ≤ n) :
    connectedProb s k = jumpCoeff n k * (connectionCount s k : ℝ) := by
  unfold connectedProb connectionCount
  rw [Nat.cast_sum, mul_sum, sum_filter, sum_filter]
  refine sum_congr rfl fun π _ ↦ ?_
  rw [blockLaw_toReal (n - k) (by omega) π, show n - (n - k) = k by omega,
    rankWeight_eq_blockWeight]
  by_cases h1 : observed s π = ⊤ <;> by_cases h2 : blocks π = k <;> simp [h1, h2]

/-- `F_1 = 1`: with one block the report is connected. -/
theorem connectedProb_one {n : ℕ} (s : Fin n → Fin n) (hn : 1 ≤ n) : connectedProb s 1 = 1 := by
  haveI : NeZero n := ⟨by omega⟩
  have hfilter : univ.filter (fun π : ER n ↦ blocks π = 1 ∧ observed s π = ⊤)
      = univ.filter (fun π : ER n ↦ blocks π = 1) := by
    refine filter_congr fun π _ ↦ ⟨fun h ↦ h.1, fun h ↦ ⟨h, ?_⟩⟩
    rw [(blocks_eq_one_iff π).mp h]
    exact top_sup_eq _
  rw [connectedProb_eq s le_rfl hn, connectionCount, hfilter,
    sum_blockWeight_ofSetoid_eq_lahNumber le_rfl hn]
  exact jumpCoeff_mul_lahNumber le_rfl hn

/-- `F_n = 0` when the interface has at least two occupied states: before any merger the report
is the interface's own partition, which is not `⊤`. -/
theorem connectedProb_self {n : ℕ} {s : Fin n → Fin n} (hw : 2 ≤ Linkage.width s) :
    connectedProb s n = 0 := by
  have hwn : Linkage.width s ≤ n := by
    have h := blocks_graphKer_le s
    rwa [blocks_graphKer] at h
  haveI : NeZero n := ⟨by omega⟩
  have hfilter : univ.filter (fun π : ER n ↦ blocks π = n ∧ observed s π = ⊤) = ∅ := by
    refine filter_eq_empty_iff.mpr fun π _ h ↦ ?_
    have hbot : π = ⊥ := (eq_of_le_of_blocks_eq bot_le (by rw [blocks_bot, h.1])).symm
    have htop := h.2
    rw [hbot, observed_bot] at htop
    have hb := blocks_graphKer s
    rw [htop, blocks_top] at hb
    omega
  rw [connectedProb_eq s (by omega) le_rfl, connectionCount, hfilter, sum_empty, Nat.cast_zero,
    mul_zero]

/-! ### The stopping level `B` -/

/-- Along a trajectory, each entry is coarser than the next. -/
theorem chainLaw_getD_succ_le {n : ℕ} :
    ∀ m {l : List (ER n)}, l ∈ (chainLaw n m).support →
      ∀ i, l.getD (i + 1) (Delta n) ≤ l.getD i (Delta n) := by
  intro m
  induction m with
  | zero =>
    intro l hl i
    rw [chainLaw, PMF.mem_support_pure_iff] at hl
    subst hl
    exact bot_le
  | succ m ih =>
    intro l hl i
    obtain ⟨x, y, rest, rfl, hprev, hy⟩ := mem_support_chainLaw_succ hl
    cases i with
    | zero =>
      show x ≤ y
      rcases lt_or_ge (blocks x) 2 with hb | hb
      · exact le_of_eq ((mem_support_jumpLaw_of_absorbed hb).mp hy).symm
      · exact ((mem_support_jumpLaw hb).mp hy).1
    | succ i => exact ih hprev i

theorem chainLaw_getD_antitone {n m : ℕ} {l : List (ER n)} (hl : l ∈ (chainLaw n m).support)
    {i j : ℕ} (hij : i ≤ j) : l.getD j (Delta n) ≤ l.getD i (Delta n) := by
  induction j, hij using Nat.le_induction with
  | base => exact le_rfl
  | succ j _ ih => exact le_trans (chainLaw_getD_succ_le m hl j) ih

/-- A report connected at a level stays connected at every lower level. -/
theorem observed_chainOfList_mono {n m : ℕ} {s : Fin n → Fin n} {l : List (ER n)}
    (hl : l ∈ (chainLaw n m).support) {i j : ℕ} (hij : i ≤ j)
    (hj : observed s (chainOfList l j) = ⊤) : observed s (chainOfList l i) = ⊤ :=
  top_unique (hj.symm.le.trans (observed_mono s (chainLaw_getD_antitone hl (by omega))))

/-- On a full trajectory the one-block level is `Θ`, whose report is connected. -/
theorem observed_chainOfList_one {n : ℕ} (hn : 2 ≤ n) (s : Fin n → Fin n) {l : List (ER n)}
    (hl : l ∈ (chainLaw n (n - 1)).support) : observed s (chainOfList l 1) = ⊤ := by
  haveI : NeZero n := ⟨by omega⟩
  obtain ⟨x, rest, rfl⟩ := List.exists_cons_of_ne_nil (chainLaw_ne_nil (n - 1) hl)
  have hx : x = Theta n := chainLaw_head_eq_top hn hl rfl
  show observed s x = ⊤
  rw [hx]
  exact top_sup_eq _

/-- **The stopping level `B`**: the largest level `k ≤ n` at which the report of the
trajectory's `k`-block state is connected. -/
noncomputable def stoppingLevel {n : ℕ} (s : Fin n → Fin n) (l : List (ER n)) : ℕ :=
  Nat.findGreatest (fun k ↦ observed s (chainOfList l k) = ⊤) n

/-- **`B = b` is "connected at `b`, not at `b + 1`".**  The connected levels of a trajectory are
`1, …, B`, so `B` is the number of true lineages right after the report first connects. -/
theorem stoppingLevel_eq_iff {n : ℕ} {s : Fin n → Fin n} {l : List (ER n)}
    (hl : l ∈ (chainLaw n (n - 1)).support) {b : ℕ} (hb : 1 ≤ b) (hbn : b < n) :
    stoppingLevel s l = b ↔
      observed s (chainOfList l b) = ⊤ ∧ observed s (chainOfList l (b + 1)) ≠ ⊤ := by
  rw [stoppingLevel, Nat.findGreatest_eq_iff]
  constructor
  · rintro ⟨-, hP, hgt⟩
    exact ⟨hP (by omega), hgt (show b < b + 1 by omega) (show b + 1 ≤ n by omega)⟩
  · rintro ⟨hP, hP1⟩
    exact ⟨by omega, fun _ ↦ hP, fun m hm _ hPm ↦ hP1 (observed_chainOfList_mono hl hm hPm)⟩

theorem stoppingLevel_eq_self_iff {n : ℕ} (hn : 1 ≤ n) {s : Fin n → Fin n} {l : List (ER n)} :
    stoppingLevel s l = n ↔ observed s (chainOfList l n) = ⊤ := by
  rw [stoppingLevel, Nat.findGreatest_eq_iff]
  exact ⟨fun h ↦ h.2.1 (by omega),
    fun h ↦ ⟨le_rfl, fun _ ↦ h, fun m hm hmn ↦ absurd hmn (by omega)⟩⟩

theorem stoppingLevel_mem_Icc {n : ℕ} (hn : 2 ≤ n) (s : Fin n → Fin n) {l : List (ER n)}
    (hl : l ∈ (chainLaw n (n - 1)).support) : stoppingLevel s l ∈ Icc 1 n :=
  mem_Icc.mpr ⟨Nat.le_findGreatest (by omega) (observed_chainOfList_one hn s hl),
    Nat.findGreatest_le n⟩

/-- The law of the stopping level `B`. -/
noncomputable def stoppingLaw {n : ℕ} (s : Fin n → Fin n) : PMF ℕ :=
  (chainLaw n (n - 1)).map (stoppingLevel s)

/-- **`p_b = Pr(B = b)`.** -/
noncomputable def stoppingProb {n : ℕ} (s : Fin n → Fin n) (b : ℕ) : ℝ :=
  (stoppingLaw s b).toReal

/-- `F_k` is the probability, under the trajectory law, that the report is connected at
level `k`. -/
theorem ofReal_connectedProb {n k : ℕ} (s : Fin n → Fin n) (hk : 1 ≤ k) (hkn : k ≤ n) :
    ENNReal.ofReal (connectedProb s k)
      = (chainLaw n (n - 1)).toOuterMeasure {l | observed s (chainOfList l k) = ⊤} := by
  have hpre : {l : List (ER n) | observed s (chainOfList l k) = ⊤}
      = (fun l ↦ l.getD (k - 1) (Delta n)) ⁻¹'
        ↑(univ.filter fun π : ER n ↦ observed s π = ⊤) := by
    ext l
    simp [chainOfList]
  rw [hpre, ← PMF.toOuterMeasure_map_apply, chainLaw_map_getD (n - 1) (k - 1) (by omega),
    PMF.toOuterMeasure_apply_finset, show n - 1 - (k - 1) = n - k by omega, connectedProb,
    ENNReal.ofReal_sum_of_nonneg fun π _ ↦ ENNReal.toReal_nonneg]
  exact sum_congr rfl fun π _ ↦ ENNReal.ofReal_toReal (PMF.apply_ne_top _ _)

theorem stoppingLaw_apply {n : ℕ} (s : Fin n → Fin n) (b : ℕ) :
    stoppingLaw s b = (chainLaw n (n - 1)).toOuterMeasure {l | stoppingLevel s l = b} := by
  rw [← PMF.toOuterMeasure_apply_singleton, stoppingLaw, PMF.toOuterMeasure_map_apply]
  rfl

/-- The stopping level lies in `1, …, n`. -/
theorem stoppingLaw_eq_zero {n : ℕ} (hn : 2 ≤ n) (s : Fin n → Fin n) {b : ℕ}
    (hb : b ∉ Icc 1 n) : stoppingLaw s b = 0 := by
  rw [PMF.apply_eq_zero_iff, stoppingLaw, PMF.support_map]
  rintro ⟨l, hl, rfl⟩
  exact hb (stoppingLevel_mem_Icc hn s hl)

theorem sum_stoppingProb {n : ℕ} (hn : 2 ≤ n) (s : Fin n → Fin n) :
    ∑ b ∈ Icc 1 n, stoppingProb s b = 1 := by
  have htsum := PMF.tsum_coe (stoppingLaw s)
  rw [tsum_eq_sum fun b hb ↦ stoppingLaw_eq_zero hn s hb] at htsum
  unfold stoppingProb
  rw [← ENNReal.toReal_sum fun b _ ↦ PMF.apply_ne_top _ _, htsum, ENNReal.toReal_one]

/-- The event decomposition behind (D6): connected at `b` is `B = b` or connected at `b + 1`. -/
theorem stoppingLaw_add_ofReal {n b : ℕ} (s : Fin n → Fin n) (hb : 1 ≤ b) (hbn : b < n) :
    stoppingLaw s b + ENNReal.ofReal (connectedProb s (b + 1))
      = ENNReal.ofReal (connectedProb s b) := by
  rw [stoppingLaw_apply, ofReal_connectedProb s (by omega) (by omega),
    ofReal_connectedProb s hb hbn.le, PMF.toOuterMeasure_apply, PMF.toOuterMeasure_apply,
    PMF.toOuterMeasure_apply, ← ENNReal.tsum_add]
  refine tsum_congr fun l ↦ ?_
  by_cases hl : l ∈ (chainLaw n (n - 1)).support
  · by_cases hc : observed s (chainOfList l (b + 1)) = ⊤
    · have hc' := observed_chainOfList_mono hl (Nat.le_succ b) hc
      have hne : stoppingLevel s l ≠ b := fun h ↦ ((stoppingLevel_eq_iff hl hb hbn).mp h).2 hc
      simp only [Set.indicator_apply, Set.mem_setOf_eq, hne, hc, hc', if_true, if_false,
        zero_add]
    · by_cases hc' : observed s (chainOfList l b) = ⊤
      · have heq : stoppingLevel s l = b := (stoppingLevel_eq_iff hl hb hbn).mpr ⟨hc', hc⟩
        simp only [Set.indicator_apply, Set.mem_setOf_eq, heq, hc, hc', if_true, if_false,
          add_zero]
      · have hne : stoppingLevel s l ≠ b := fun h ↦
          hc' ((stoppingLevel_eq_iff hl hb hbn).mp h).1
        simp only [Set.indicator_apply, Set.mem_setOf_eq, hne, hc, hc', if_false, add_zero]
  · have hzero : chainLaw n (n - 1) l = 0 := (PMF.apply_eq_zero_iff _ _).mpr hl
    simp only [Set.indicator_apply, hzero, ite_self, add_zero]

/-- **(D6)**: `p_b = F_b - F_{b+1}`. -/
theorem stoppingProb_eq {n b : ℕ} (s : Fin n → Fin n) (hb : 1 ≤ b) (hbn : b < n) :
    stoppingProb s b = connectedProb s b - connectedProb s (b + 1) := by
  have h := congrArg ENNReal.toReal (stoppingLaw_add_ofReal s hb hbn)
  rw [ENNReal.toReal_add (PMF.apply_ne_top _ _) ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal (connectedProb_nonneg s _),
    ENNReal.toReal_ofReal (connectedProb_nonneg s _)] at h
  unfold stoppingProb
  linarith

/-- (D6) at the top level: `p_n = F_n`. -/
theorem stoppingProb_self {n : ℕ} (hn : 1 ≤ n) (s : Fin n → Fin n) :
    stoppingProb s n = connectedProb s n := by
  have h : stoppingLaw s n = ENNReal.ofReal (connectedProb s n) := by
    rw [stoppingLaw_apply, ofReal_connectedProb s hn le_rfl]
    congr 1
    ext l
    exact stoppingLevel_eq_self_iff hn
  rw [stoppingProb, h, ENNReal.toReal_ofReal (connectedProb_nonneg s n)]

/-! ### The clock and the path law -/

/-- **Kingman's clock**: one independent holding time per level, coordinate `j` being the time
spent with `j + 2` blocks, of rate `d_{j+2}` (K-C (1.7)). -/
noncomputable def kingmanClock : Measure (ℕ → ℝ) :=
  holdProduct deathRate fun k ↦ deathRate_add_two_pos k

instance kingmanClock_isProbabilityMeasure : IsProbabilityMeasure kingmanClock := by
  haveI : ∀ k : ℕ, IsProbabilityMeasure (holdMeasure (deathRate (k + 2))) := fun k ↦
    holdMeasure_isProbabilityMeasure (deathRate_add_two_pos k)
  unfold kingmanClock holdProduct
  infer_instance

/-- **The path law**: a jump-chain trajectory of `n - 1` jumps from `Δ`, with an independent
Kingman clock. -/
noncomputable def trajectoryClockLaw (n : ℕ) : Measure (List (ER n) × (ℕ → ℝ)) :=
  (chainLaw n (n - 1)).toMeasure.prod kingmanClock

/-- The trajectory and the clock are independent, by construction. -/
theorem trajectoryClockLaw_prod {n : ℕ} (A : Set (List (ER n))) (B : Set (ℕ → ℝ)) :
    trajectoryClockLaw n (A ×ˢ B) = (chainLaw n (n - 1)).toMeasure A * kingmanClock B :=
  Measure.prod_prod A B

/-- **The reported connection time**: the holding times at levels `B + 1, …, n`, which are the
clock coordinates `B - 1, …, n - 2`. -/
noncomputable def connectionTime {n : ℕ} (s : Fin n → Fin n) (p : List (ER n) × (ℕ → ℝ)) : ℝ :=
  ∑ j ∈ Ico (stoppingLevel s p.1 - 1) (n - 1), p.2 j

theorem ico_succ_eq_ioc (b n : ℕ) : Ico (b + 1) (n + 1) = Ioc b n := by
  ext x
  simp only [mem_Ico, mem_Ioc]
  omega

/-- Clock coordinates `b - 1, …, n - 2` are levels `b + 1, …, n`. -/
theorem sum_Ico_pred {M : Type*} [AddCommMonoid M] (f : ℕ → M) {b n : ℕ} (hb : 1 ≤ b)
    (hn : 1 ≤ n) : ∑ j ∈ Ico (b - 1) (n - 1), f (j + 2) = ∑ k ∈ Ioc b n, f k := by
  rw [sum_Ico_add', show b - 1 + 2 = b + 1 by omega, show n - 1 + 2 = n + 1 by omega,
    ico_succ_eq_ioc]

theorem prod_Ico_pred {M : Type*} [CommMonoid M] (f : ℕ → M) {b n : ℕ} (hb : 1 ≤ b)
    (hn : 1 ≤ n) : ∏ j ∈ Ico (b - 1) (n - 1), f (j + 2) = ∏ k ∈ Ioc b n, f k := by
  rw [prod_Ico_add', show b - 1 + 2 = b + 1 by omega, show n - 1 + 2 = n + 1 by omega,
    ico_succ_eq_ioc]

/-- **Conditional on the stopping level, the connection time is a sum of holding times.**  On a
path with `B = b`, `τ_q = ∑_{k=b+1}^{n} H_k`, `H_k` being clock coordinate `k - 2`. -/
theorem connectionTime_of_stoppingLevel {n b : ℕ} (s : Fin n → Fin n) (hb : 1 ≤ b)
    (hbn : b ≤ n) {p : List (ER n) × (ℕ → ℝ)} (hp : stoppingLevel s p.1 = b) :
    connectionTime s p = ∑ k ∈ Ioc b n, p.2 (k - 2) := by
  rw [connectionTime, hp, ← sum_Ico_pred (fun k ↦ p.2 (k - 2)) hb (by omega)]
  simp only [Nat.add_sub_cancel]

/-- **The path law mixes the clock over the stopping level.**  A functional of the path that
sees the trajectory only through `B` integrates to `∑_b p_b E[F b]`. -/
theorem lintegral_trajectoryClockLaw {n : ℕ} (hn : 2 ≤ n) (s : Fin n → Fin n)
    (F : ℕ → (ℕ → ℝ) → ℝ≥0∞) (hF : ∀ b, Measurable (F b)) :
    ∫⁻ p, F (stoppingLevel s p.1) p.2 ∂(trajectoryClockLaw n)
      = ∑ b ∈ Icc 1 n, stoppingLaw s b * ∫⁻ ω, F b ω ∂kingmanClock := by
  have hswap : Measurable fun q : (ℕ → ℝ) × List (ER n) ↦ F (stoppingLevel s q.2) q.1 :=
    measurable_from_prod_countable_left fun l ↦ hF (stoppingLevel s l)
  have hmeas : Measurable fun p : List (ER n) × (ℕ → ℝ) ↦ F (stoppingLevel s p.1) p.2 :=
    hswap.comp measurable_swap
  have hH : Measurable fun b : ℕ ↦ ∫⁻ ω, F b ω ∂kingmanClock := measurable_of_countable _
  have hB : Measurable (stoppingLevel s) := measurable_of_countable _
  have htm : (chainLaw n (n - 1)).toMeasure.map (stoppingLevel s)
      = (stoppingLaw s).toMeasure := by
    ext S hS
    rw [Measure.map_apply hB hS, stoppingLaw, PMF.toMeasure_map_apply (hf := hB) (hs := hS)]
  have hmix : ∫⁻ l, ∫⁻ ω, F (stoppingLevel s l) ω ∂kingmanClock ∂(chainLaw n (n - 1)).toMeasure
      = ∫⁻ b, ∫⁻ ω, F b ω ∂kingmanClock ∂(stoppingLaw s).toMeasure := by
    rw [← htm, lintegral_map hH hB]
  have hoff : ∀ b ∉ Icc 1 n,
      (∫⁻ ω, F b ω ∂kingmanClock) * (stoppingLaw s).toMeasure {b} = 0 := by
    intro b hb
    rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton b),
      stoppingLaw_eq_zero hn s hb, mul_zero]
  rw [trajectoryClockLaw, lintegral_prod _ hmeas.aemeasurable]
  dsimp only
  rw [hmix, lintegral_countable', tsum_eq_sum hoff]
  refine sum_congr rfl fun b _ ↦ ?_
  rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton b), mul_comm]

/-! ### The clock over a block of levels -/

theorem kingmanClock_eval (j : ℕ) :
    MeasurePreserving (fun ω : ℕ → ℝ ↦ ω j) kingmanClock (holdMeasure (deathRate (j + 2))) := by
  haveI : ∀ k : ℕ, IsProbabilityMeasure (holdMeasure (deathRate (k + 2))) := fun k ↦
    holdMeasure_isProbabilityMeasure (deathRate_add_two_pos k)
  unfold kingmanClock holdProduct
  exact measurePreserving_eval_infinitePi (fun k : ℕ ↦ holdMeasure (deathRate (k + 2))) j

theorem lintegral_coord_kingmanClock (j : ℕ) :
    ∫⁻ ω, ENNReal.ofReal (ω j) ∂kingmanClock = ENNReal.ofReal (1 / deathRate (j + 2)) :=
  ((kingmanClock_eval j).lintegral_comp ENNReal.measurable_ofReal).trans
    (lintegral_id_holdMeasure (deathRate_add_two_pos j))

/-- **The transform of a block of holding times is the product of the per-level factors.** -/
theorem lintegral_exp_neg_sum_kingmanClock {θ : ℝ} (hθ : 0 ≤ θ) (T : Finset ℕ) :
    ∫⁻ ω, ENNReal.ofReal (Real.exp (-(θ * ∑ j ∈ T, ω j))) ∂kingmanClock
      = ∏ j ∈ T, ENNReal.ofReal (deathRate (j + 2) / (deathRate (j + 2) + θ)) := by
  have hprod : (fun ω : ℕ → ℝ ↦ ENNReal.ofReal (Real.exp (-(θ * ∑ j ∈ T, ω j))))
      = fun ω ↦ ∏ j ∈ T, ENNReal.ofReal (Real.exp (-(θ * ω j))) := by
    funext ω
    rw [mul_sum, ← sum_neg_distrib, Real.exp_sum,
      ENNReal.ofReal_prod_of_nonneg fun j _ ↦ (Real.exp_pos _).le]
  have hind : iIndepFun (fun (k : ℕ) (ω : ℕ → ℝ) ↦ ENNReal.ofReal (Real.exp (-(θ * ω k))))
      kingmanClock := indep_holdCoords (fun k ↦ deathRate_add_two_pos k) θ
  rw [hprod, lintegral_prod_eq_prod_lintegral_of_indepFun T _ hind
    fun j ↦ ((measurable_const.mul (measurable_pi_apply j)).neg.exp).ennreal_ofReal]
  refine prod_congr rfl fun j _ ↦ ?_
  have hcomp := (kingmanClock_eval j).lintegral_comp
    (f := fun t : ℝ ↦ ENNReal.ofReal (Real.exp (-(θ * t))))
    ((measurable_const.mul measurable_id).neg.exp).ennreal_ofReal
  exact hcomp.trans (lintegral_exp_neg_holdMeasure (deathRate_add_two_pos j) hθ)

/-- A holding time is positive: its density vanishes on the negative half-line. -/
theorem holdMeasure_Iio_zero (d : ℝ) : holdMeasure d (Set.Iio 0) = 0 := by
  rw [holdMeasure, withDensity_apply _ measurableSet_Iio]
  refine (setLIntegral_congr_fun measurableSet_Iio fun t ht ↦ ?_).trans lintegral_zero
  simp [holdDensity, not_lt.mpr (Set.mem_Iio.mp ht).le]

theorem ae_nonneg_kingmanClock : ∀ᵐ ω ∂kingmanClock, ∀ j, 0 ≤ ω j := by
  rw [ae_all_iff]
  intro j
  rw [ae_iff]
  have h := (kingmanClock_eval j).measure_preimage
    (measurableSet_Iio (a := (0 : ℝ))).nullMeasurableSet
  rw [holdMeasure_Iio_zero] at h
  have hset : {ω : ℕ → ℝ | ¬ 0 ≤ ω j} = (fun ω : ℕ → ℝ ↦ ω j) ⁻¹' Set.Iio 0 := by
    ext ω
    simp
  rw [hset]
  exact h

/-- **The mean of a block of holding times.** -/
theorem lintegral_sum_kingmanClock (T : Finset ℕ) :
    ∫⁻ ω, ENNReal.ofReal (∑ j ∈ T, ω j) ∂kingmanClock
      = ENNReal.ofReal (∑ j ∈ T, 1 / deathRate (j + 2)) := by
  have hae : (fun ω : ℕ → ℝ ↦ ENNReal.ofReal (∑ j ∈ T, ω j))
      =ᵐ[kingmanClock] fun ω ↦ ∑ j ∈ T, ENNReal.ofReal (ω j) := by
    filter_upwards [ae_nonneg_kingmanClock] with ω hω
    exact ENNReal.ofReal_sum_of_nonneg fun j _ ↦ hω j
  rw [lintegral_congr_ae hae,
    lintegral_finset_sum _ fun j _ ↦ (measurable_pi_apply j).ennreal_ofReal,
    ENNReal.ofReal_sum_of_nonneg fun j _ ↦ (one_div_pos.mpr (deathRate_add_two_pos j)).le]
  exact sum_congr rfl fun j _ ↦ lintegral_coord_kingmanClock j

/-- **The second moment of a holding time**, `2/d²`, as a lower integral. -/
theorem lintegral_sq_holdMeasure {d : ℝ} (hd : 0 < d) :
    ∫⁻ t, ENNReal.ofReal t * ENNReal.ofReal t ∂(holdMeasure d) = ENNReal.ofReal (2 / d ^ 2) := by
  have hdne : d ≠ 0 := hd.ne'
  have hmeas : Measurable (holdDensity d) := by
    unfold holdDensity
    refine Measurable.ite measurableSet_Ioi ?_ measurable_const
    exact (measurable_const.mul ((measurable_const.mul measurable_id).neg.exp)).ennreal_ofReal
  have hsq : Measurable fun t : ℝ ↦ ENNReal.ofReal t * ENNReal.ofReal t :=
    measurable_id.ennreal_ofReal.mul measurable_id.ennreal_ofReal
  have hint : IntegrableOn (fun t : ℝ ↦ t ^ 2 * (d * Real.exp (-(d * t)))) (Set.Ioi 0) := by
    have hg : IntegrableOn (fun x : ℝ ↦ Real.exp (-x) * x ^ ((3 : ℝ) - 1)) (Set.Ioi 0) :=
      Real.GammaIntegral_convergent (by norm_num)
    have hscale : IntegrableOn
        (fun x : ℝ ↦ Real.exp (-(d * x)) * (d * x) ^ ((3 : ℝ) - 1)) (Set.Ioi 0) := by
      refine (integrableOn_Ioi_comp_mul_left_iff
        (fun x : ℝ ↦ Real.exp (-x) * x ^ ((3 : ℝ) - 1)) 0 hd).mpr ?_
      simpa using hg
    have hscale' : IntegrableOn
        (fun x : ℝ ↦ d⁻¹ * (Real.exp (-(d * x)) * (d * x) ^ ((3 : ℝ) - 1))) (Set.Ioi 0) :=
      hscale.const_mul d⁻¹
    refine hscale'.congr_fun (fun t _ ↦ ?_) measurableSet_Ioi
    have hinv : d⁻¹ * d = 1 := inv_mul_cancel₀ hdne
    show d⁻¹ * (Real.exp (-(d * t)) * (d * t) ^ ((3 : ℝ) - 1))
      = t ^ 2 * (d * Real.exp (-(d * t)))
    rw [show (3 : ℝ) - 1 = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    linear_combination (Real.exp (-(d * t)) * t ^ 2 * d) * hinv
  have hnonneg : ∀ᵐ t ∂(volume.restrict (Set.Ioi (0 : ℝ))),
      0 ≤ t ^ 2 * (d * Real.exp (-(d * t))) := by
    filter_upwards with t
    positivity
  have hind : ∀ t : ℝ, holdDensity d t * (ENNReal.ofReal t * ENNReal.ofReal t)
      = (Set.Ioi (0 : ℝ)).indicator
          (fun t ↦ ENNReal.ofReal (t ^ 2 * (d * Real.exp (-(d * t))))) t := by
    intro t
    unfold holdDensity
    by_cases ht : 0 < t
    · rw [if_pos ht, Set.indicator_of_mem (Set.mem_Ioi.mpr ht), ← ENNReal.ofReal_mul ht.le,
        ← ENNReal.ofReal_mul (show (0 : ℝ) ≤ d * Real.exp (-(d * t)) by positivity)]
      congr 1
      ring
    · rw [if_neg ht, Set.indicator_of_notMem (by simpa using le_of_not_gt ht), zero_mul]
  calc ∫⁻ t, ENNReal.ofReal t * ENNReal.ofReal t ∂(holdMeasure d)
      = ∫⁻ t, holdDensity d t * (ENNReal.ofReal t * ENNReal.ofReal t) := by
        rw [holdMeasure, lintegral_withDensity_eq_lintegral_mul _ hmeas hsq]
        rfl
    _ = ∫⁻ t in Set.Ioi (0 : ℝ), ENNReal.ofReal (t ^ 2 * (d * Real.exp (-(d * t)))) := by
        simp only [hind]
        rw [lintegral_indicator measurableSet_Ioi]
    _ = ENNReal.ofReal (∫ t in Set.Ioi (0 : ℝ), t ^ 2 * (d * Real.exp (-(d * t)))) := by
        rw [← ofReal_integral_eq_lintegral_ofReal hint hnonneg]
    _ = ENNReal.ofReal (2 / d ^ 2) := by
        rw [integral_sq_mul_holdDensity hd]

/-- Distinct levels of the clock are independent, so their product integrates to the product of
the means. -/
theorem lintegral_mul_coords_kingmanClock {i j : ℕ} (hij : i ≠ j) :
    ∫⁻ ω, ENNReal.ofReal (ω i) * ENNReal.ofReal (ω j) ∂kingmanClock
      = ENNReal.ofReal (1 / deathRate (i + 2)) * ENNReal.ofReal (1 / deathRate (j + 2)) := by
  haveI : ∀ k : ℕ, IsProbabilityMeasure (holdMeasure (deathRate (k + 2))) := fun k ↦
    holdMeasure_isProbabilityMeasure (deathRate_add_two_pos k)
  have hind : iIndepFun (fun (k : ℕ) (ω : ℕ → ℝ) ↦ ENNReal.ofReal (ω k)) kingmanClock :=
    iIndepFun_infinitePi (X := fun _ (t : ℝ) ↦ ENNReal.ofReal t)
      fun _ ↦ measurable_id.ennreal_ofReal
  have h := lintegral_mul_eq_lintegral_mul_lintegral_of_indepFun
    (measurable_pi_apply i).ennreal_ofReal (measurable_pi_apply j).ennreal_ofReal
    (hind.indepFun hij)
  rw [← lintegral_coord_kingmanClock i, ← lintegral_coord_kingmanClock j, ← h]
  rfl

/-- The algebra of the second moment: a double sum with a diagonal correction. -/
theorem sum_sum_ofReal_add_ite {T : Finset ℕ} {a : ℕ → ℝ} (ha : ∀ j, 0 ≤ a j) :
    ∑ i ∈ T, ∑ j ∈ T,
        (ENNReal.ofReal (a i * a j) + if i = j then ENNReal.ofReal (a i ^ 2) else 0)
      = ENNReal.ofReal ((∑ j ∈ T, a j) ^ 2 + ∑ j ∈ T, a j ^ 2) := by
  have hdiag : ∀ i ∈ T,
      ∑ j ∈ T, (if i = j then ENNReal.ofReal (a i ^ 2) else 0) = ENNReal.ofReal (a i ^ 2) := by
    intro i hi
    rw [sum_ite_eq, if_pos hi]
  rw [ENNReal.ofReal_add (sq_nonneg _) (sum_nonneg fun j _ ↦ sq_nonneg (a j)), sq, sum_mul_sum,
    ENNReal.ofReal_sum_of_nonneg fun i _ ↦ sum_nonneg fun j _ ↦ mul_nonneg (ha i) (ha j),
    ENNReal.ofReal_sum_of_nonneg fun j _ ↦ sq_nonneg (a j), ← sum_add_distrib]
  refine sum_congr rfl fun i hi ↦ ?_
  rw [sum_add_distrib, hdiag i hi,
    ENNReal.ofReal_sum_of_nonneg fun j _ ↦ mul_nonneg (ha i) (ha j)]

/-- **The second moment of a block of holding times**: `(∑ d⁻¹)² + ∑ d⁻²`. -/
theorem lintegral_sq_sum_kingmanClock (T : Finset ℕ) :
    ∫⁻ ω, ENNReal.ofReal ((∑ j ∈ T, ω j) ^ 2) ∂kingmanClock
      = ENNReal.ofReal ((∑ j ∈ T, 1 / deathRate (j + 2)) ^ 2
          + ∑ j ∈ T, (1 / deathRate (j + 2)) ^ 2) := by
  have ha : ∀ j, 0 ≤ 1 / deathRate (j + 2) := fun j ↦
    (one_div_pos.mpr (deathRate_add_two_pos j)).le
  have hae : (fun ω : ℕ → ℝ ↦ ENNReal.ofReal ((∑ j ∈ T, ω j) ^ 2))
      =ᵐ[kingmanClock] fun ω ↦ ∑ i ∈ T, ∑ j ∈ T, ENNReal.ofReal (ω i) * ENNReal.ofReal (ω j) := by
    filter_upwards [ae_nonneg_kingmanClock] with ω hω
    rw [ENNReal.ofReal_pow (sum_nonneg fun j _ ↦ hω j),
      ENNReal.ofReal_sum_of_nonneg fun j _ ↦ hω j, sq, sum_mul_sum]
  have hmeas : ∀ i j : ℕ,
      Measurable fun ω : ℕ → ℝ ↦ ENNReal.ofReal (ω i) * ENNReal.ofReal (ω j) :=
    fun i j ↦ (measurable_pi_apply i).ennreal_ofReal.mul (measurable_pi_apply j).ennreal_ofReal
  have hpair : ∀ i j, ∫⁻ ω, ENNReal.ofReal (ω i) * ENNReal.ofReal (ω j) ∂kingmanClock
      = ENNReal.ofReal (1 / deathRate (i + 2) * (1 / deathRate (j + 2)))
        + if i = j then ENNReal.ofReal ((1 / deathRate (i + 2)) ^ 2) else 0 := by
    intro i j
    by_cases hij : i = j
    · subst hij
      have hcomp := (kingmanClock_eval i).lintegral_comp
        (f := fun t : ℝ ↦ ENNReal.ofReal t * ENNReal.ofReal t)
        (ENNReal.measurable_ofReal.mul ENNReal.measurable_ofReal)
      rw [if_pos rfl, ← ENNReal.ofReal_add (mul_nonneg (ha i) (ha i)) (sq_nonneg _)]
      refine hcomp.trans ((lintegral_sq_holdMeasure (deathRate_add_two_pos i)).trans ?_)
      congr 1
      ring
    · rw [if_neg hij, add_zero, lintegral_mul_coords_kingmanClock hij,
        ← ENNReal.ofReal_mul (ha i)]
  have hrow : ∀ i ∈ T,
      ∫⁻ ω, ∑ j ∈ T, ENNReal.ofReal (ω i) * ENNReal.ofReal (ω j) ∂kingmanClock
        = ∑ j ∈ T, (ENNReal.ofReal (1 / deathRate (i + 2) * (1 / deathRate (j + 2)))
          + if i = j then ENNReal.ofReal ((1 / deathRate (i + 2)) ^ 2) else 0) := by
    intro i _
    rw [lintegral_finset_sum _ fun j _ ↦ hmeas i j]
    exact sum_congr rfl fun j _ ↦ hpair i j
  rw [lintegral_congr_ae hae,
    lintegral_finset_sum _ fun i _ ↦ Finset.measurable_sum T fun j _ ↦ hmeas i j,
    sum_congr rfl hrow]
  exact sum_sum_ofReal_add_ite ha

/-! ### (D7), (D8), (D9) -/

/-- `∑_{k=b+1}^{n} d_k⁻¹ = 2/b - 2/n`. -/
theorem sum_Ioc_one_div_deathRate {b n : ℕ} (hb : 1 ≤ b) (hbn : b ≤ n) :
    ∑ k ∈ Ioc b n, 1 / deathRate k = 2 / (b : ℝ) - 2 / n := by
  have h1 : ∑ k ∈ Ioc b n, 1 / deathRate k = meanTransitTime n - meanTransitTime b := by
    rw [← sum_Ico_pred (fun k ↦ 1 / deathRate k) hb (by omega), sum_Ico_eq_sub _ (by omega)]
    rfl
  rw [h1, meanTransitTime_eq_two_sub (by omega), meanTransitTime_eq_two_sub hb]
  ring

/-- **(D7)**: `E e^{-θ τ_q} = ∑_b p_b ∏_{k=b+1}^{n} d_k/(d_k + θ)`. -/
theorem connectionTime_laplace {n : ℕ} (hn : 2 ≤ n) (s : Fin n → Fin n) {θ : ℝ} (hθ : 0 ≤ θ) :
    ∫⁻ p, ENNReal.ofReal (Real.exp (-(θ * connectionTime s p))) ∂(trajectoryClockLaw n)
      = ENNReal.ofReal (∑ b ∈ Icc 1 n,
          stoppingProb s b * ∏ k ∈ Ioc b n, deathRate k / (deathRate k + θ)) := by
  have hmix := lintegral_trajectoryClockLaw hn s
    (fun b ω ↦ ENNReal.ofReal (Real.exp (-(θ * ∑ j ∈ Ico (b - 1) (n - 1), ω j))))
    fun b ↦ ((measurable_const.mul
      (Finset.measurable_sum _ fun j _ ↦ measurable_pi_apply j)).neg.exp).ennreal_ofReal
  have hterm : ∀ b ∈ Icc 1 n,
      0 ≤ stoppingProb s b * ∏ k ∈ Ioc b n, deathRate k / (deathRate k + θ) := by
    intro b hb
    refine mul_nonneg ENNReal.toReal_nonneg (prod_nonneg fun k hk ↦ ?_)
    have hd := deathRate_pos (show 2 ≤ k by
      have h1 := (mem_Icc.mp hb).1
      have h2 := (mem_Ioc.mp hk).1
      omega)
    exact div_nonneg hd.le (add_nonneg hd.le hθ)
  refine hmix.trans ?_
  rw [ENNReal.ofReal_sum_of_nonneg hterm]
  refine sum_congr rfl fun b hb ↦ ?_
  have hb1 : 1 ≤ b := (mem_Icc.mp hb).1
  rw [lintegral_exp_neg_sum_kingmanClock hθ, stoppingProb,
    ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal (PMF.apply_ne_top _ _),
    ← prod_Ico_pred (fun k ↦ deathRate k / (deathRate k + θ)) hb1 (by omega),
    ENNReal.ofReal_prod_of_nonneg fun j _ ↦
      div_nonneg (deathRate_add_two_pos j).le (add_nonneg (deathRate_add_two_pos j).le hθ)]

/-- **(D8)**: `E τ_q = 2 ∑_b p_b / b - 2/n`. -/
theorem connectionTime_mean {n : ℕ} (hn : 2 ≤ n) (s : Fin n → Fin n) :
    ∫⁻ p, ENNReal.ofReal (connectionTime s p) ∂(trajectoryClockLaw n)
      = ENNReal.ofReal (2 * ∑ b ∈ Icc 1 n, stoppingProb s b / b - 2 / n) := by
  have hmix := lintegral_trajectoryClockLaw hn s
    (fun b ω ↦ ENNReal.ofReal (∑ j ∈ Ico (b - 1) (n - 1), ω j))
    fun b ↦ (Finset.measurable_sum _ fun j _ ↦ measurable_pi_apply j).ennreal_ofReal
  have hform : 2 * ∑ b ∈ Icc 1 n, stoppingProb s b / b - 2 / n
      = ∑ b ∈ Icc 1 n,
          stoppingProb s b * ∑ j ∈ Ico (b - 1) (n - 1), 1 / deathRate (j + 2) := by
    have hterm : ∀ b ∈ Icc 1 n,
        stoppingProb s b * ∑ j ∈ Ico (b - 1) (n - 1), 1 / deathRate (j + 2)
          = 2 * (stoppingProb s b / b) - 2 / n * stoppingProb s b := by
      intro b hb
      have hb1 := (mem_Icc.mp hb).1
      rw [sum_Ico_pred (fun k ↦ 1 / deathRate k) hb1 (by omega),
        sum_Ioc_one_div_deathRate hb1 (mem_Icc.mp hb).2]
      ring
    rw [sum_congr rfl hterm, sum_sub_distrib, ← mul_sum, ← mul_sum, sum_stoppingProb hn s,
      mul_one]
  have hterm : ∀ b ∈ Icc 1 n,
      0 ≤ stoppingProb s b * ∑ j ∈ Ico (b - 1) (n - 1), 1 / deathRate (j + 2) := fun b _ ↦
    mul_nonneg ENNReal.toReal_nonneg
      (sum_nonneg fun j _ ↦ (one_div_pos.mpr (deathRate_add_two_pos j)).le)
  rw [hform]
  refine hmix.trans ?_
  rw [ENNReal.ofReal_sum_of_nonneg hterm]
  refine sum_congr rfl fun b _ ↦ ?_
  rw [lintegral_sum_kingmanClock, stoppingProb, ENNReal.ofReal_mul ENNReal.toReal_nonneg,
    ENNReal.ofReal_toReal (PMF.apply_ne_top _ _)]

/-- **(D9)**: `E τ_q² = ∑_b p_b [(2/b - 2/n)² + ∑_{k=b+1}^{n} d_k⁻²]`. -/
theorem connectionTime_secondMoment {n : ℕ} (hn : 2 ≤ n) (s : Fin n → Fin n) :
    ∫⁻ p, ENNReal.ofReal (connectionTime s p ^ 2) ∂(trajectoryClockLaw n)
      = ENNReal.ofReal (∑ b ∈ Icc 1 n, stoppingProb s b *
          ((2 / (b : ℝ) - 2 / n) ^ 2 + ∑ k ∈ Ioc b n, (1 / deathRate k) ^ 2)) := by
  have hmix := lintegral_trajectoryClockLaw hn s
    (fun b ω ↦ ENNReal.ofReal ((∑ j ∈ Ico (b - 1) (n - 1), ω j) ^ 2))
    fun b ↦ ((Finset.measurable_sum _ fun j _ ↦ measurable_pi_apply j).pow_const 2).ennreal_ofReal
  have hterm : ∀ b ∈ Icc 1 n, 0 ≤ stoppingProb s b *
      ((2 / (b : ℝ) - 2 / n) ^ 2 + ∑ k ∈ Ioc b n, (1 / deathRate k) ^ 2) := fun b _ ↦
    mul_nonneg ENNReal.toReal_nonneg
      (add_nonneg (sq_nonneg _) (sum_nonneg fun k _ ↦ sq_nonneg _))
  refine hmix.trans ?_
  rw [ENNReal.ofReal_sum_of_nonneg hterm]
  refine sum_congr rfl fun b hb ↦ ?_
  have hb1 : 1 ≤ b := (mem_Icc.mp hb).1
  rw [lintegral_sq_sum_kingmanClock, stoppingProb, ENNReal.ofReal_mul ENNReal.toReal_nonneg,
    ENNReal.ofReal_toReal (PMF.apply_ne_top _ _),
    sum_Ico_pred (fun k ↦ 1 / deathRate k) hb1 (by omega),
    sum_Ico_pred (fun k ↦ (1 / deathRate k) ^ 2) hb1 (by omega),
    sum_Ioc_one_div_deathRate hb1 (mem_Icc.mp hb).2]

end Descent.Pangenome.GraphCoalescent
