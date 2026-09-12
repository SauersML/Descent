/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Pangenome.GraphCoalescent.ConnectionClockHittingTime

assert_below Descent.PopGen Descent.Spectral Descent.Blindness Descent.Conditionals
assert_below Descent.Portability Descent.Decision Descent.Program

/-!
# (C3) as a path identity on the trajectory-and-clock law

Theorem C of the pangenome hidden-clock note states Dynkin's formula at the connection time,

  `2 - 2/w - E τ_q = E ∫_0^{τ_q} (λ_vis(X_t)/C(r_t, 2) - 1) dt`,                        (C3)

with `X_t` the coalescent path, `r_t` the width of its report and `λ_vis` the visible intensity.
`VisibleIntensityClock` proves it for the solution of the backward equation, and this file proves
it for the path.

## The path integral is a finite sum

`ReportedConnectionClock` represents the path by a jump-chain trajectory and an independent
Kingman clock, `Descent.Coalescent.Path` reads the path off them, and `ConnectionClockHittingTime`
identifies the connection time with the first time the report of the path is connected.  On one
trajectory the path is constant between consecutive descents: it holds the state with `k` blocks
for the holding time at level `k` (`integral_pathState_descentTime`).  So the path integral of the
correction rate up to the connection time is a finite sum over the levels above the stopping
level `B`: holding time times the correction rate at the state the chain visits
(`integral_clockCorrectionRate_pathState`).

## Taking expectations

The clock is independent of the chain and the holding time at level `k` has mean `1/C(k, 2)`, so
the expectation of that sum is `∑_k E[λ_vis/C(r, 2) - 1 at level k, before connection]/C(k, 2)`.
The level `k` is unconnected exactly when `B < k` (`stoppingLevel_lt_iff`), and the state at level
`k` has the head law of the jump chain.  The first-step value of the backward equation unrolls
along the same head law (`sum_blockLaw_connectionValue`, generalizing
`ReportedConnectionFirstStep.sum_blockLaw_meanConnectionTime` from the unit rate to any running
rate), so both sides are one finite sum (`lintegral_integral_clockCorrectionRate`).  With
`VisibleIntensityClock.meanTransitTime_sub_meanConnectionTime` and
`ReportedConnectionFirstStep.connectionTime_mean_eq_meanConnectionTime` this is (C3) on the path
(`clockDynkin_path`), and at the first hitting time of the connected report
(`clockDynkin_reportHittingTime`).

## Scope

The continuous-time path is the one `ReportedConnectionClock` constructs from the jump chain and
the clock; its identification with a Markov process on càdlàg paths is not formalized.  The
expectations are lower Lebesgue integrals of `ENNReal.ofReal` of nonnegative quantities, read
back as real numbers.

## Empirical status

None.  Every declaration is an identity about one trajectory and one clock, a finite recursion
along the covering order, or an expectation under the product law built from K-C (1.3) and (1.7).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Pangenome.GraphCoalescent

open Finset Coalescent MeasureTheory
open scoped Classical ENNReal

noncomputable section

/-! ### The path integral on one trajectory -/

/-- **The integral of a function of the path over a descent.**  Before the path first has `n - d`
blocks it holds the state with `k` blocks for time `hold k` at each level `k = n - d + 1, …, n`,
so the integral of `g` along the path is the sum over those levels of the holding time times `g`
at the state of that level. -/
theorem integral_pathState_descentTime {n : ℕ} (chain : ℕ → ER n) {hold : ℕ → ℝ}
    (hpos : ∀ j, 0 ≤ hold j) (g : ER n → ℝ) :
    ∀ d, d + 1 ≤ n →
      IntegrableOn (fun t ↦ g (pathState n chain hold t))
          (Set.Ico 0 (descentTime n hold (n - d)))
        ∧ ∫ t in Set.Ico 0 (descentTime n hold (n - d)), g (pathState n chain hold t)
          = ∑ k ∈ Ioc (n - d) n, hold k * g (chain k) := by
  intro d
  induction d with
  | zero =>
    intro _
    simp
  | succ d ih =>
    intro hd
    obtain ⟨hint, heq⟩ := ih (by omega)
    have hsplit : descentTime n hold (n - (d + 1)) = descentTime n hold (n - d) + hold (n - d) := by
      rw [descentTime, descentTime, show n - (d + 1) + 1 = n - d by omega,
        sum_eq_sum_Ico_succ_bot (show n - d < n + 1 by omega)]
      ring
    have hT0 : 0 ≤ descentTime n hold (n - d) := descentTime_nonneg n hpos (n - d)
    have hTle : descentTime n hold (n - d) ≤ descentTime n hold (n - (d + 1)) := by
      rw [hsplit]
      linarith [hpos (n - d)]
    have hconst : Set.EqOn (fun t ↦ g (pathState n chain hold t)) (fun _ ↦ g (chain (n - d)))
        (Set.Ico (descentTime n hold (n - d)) (descentTime n hold (n - (d + 1)))) := by
      intro t ht
      show g (chain (blockCountAt n hold t)) = g (chain (n - d))
      rw [blockCountAt_eq n hpos (by omega : 1 ≤ n - d) (by omega : n - d ≤ n) ht.1
        fun j _ hjb ↦ lt_of_lt_of_le ht.2 (descentTime_antitone n hpos (by omega))]
    have hpiece : IntegrableOn (fun t ↦ g (pathState n chain hold t))
        (Set.Ico (descentTime n hold (n - d)) (descentTime n hold (n - (d + 1)))) :=
      (integrableOn_const measure_Ico_lt_top.ne).congr_fun hconst.symm measurableSet_Ico
    have hunion : Set.Ico 0 (descentTime n hold (n - (d + 1)))
        = Set.Ico 0 (descentTime n hold (n - d))
          ∪ Set.Ico (descentTime n hold (n - d)) (descentTime n hold (n - (d + 1))) :=
      (Set.Ico_union_Ico_eq_Ico hT0 hTle).symm
    have hinsert : Ioc (n - (d + 1)) n = insert (n - d) (Ioc (n - d) n) := by
      ext k
      simp only [mem_Ioc, mem_insert]
      omega
    refine ⟨by rw [hunion]; exact hint.union hpiece, ?_⟩
    rw [hunion, setIntegral_union Set.Ico_disjoint_Ico_same measurableSet_Ico hint hpiece, heq,
      setIntegral_congr_fun measurableSet_Ico hconst, setIntegral_const, Real.volume_real_Ico,
      max_eq_left (sub_nonneg.mpr hTle), smul_eq_mul, hsplit, hinsert,
      sum_insert (by simp)]
    ring

/-- The connection time is nonnegative on a nonnegative clock. -/
theorem connectionTime_nonneg {n : ℕ} (s : Fin n → Fin n) {p : List (ER n) × (ℕ → ℝ)}
    (hpos : ∀ j, 0 ≤ p.2 j) : 0 ≤ connectionTime s p :=
  sum_nonneg fun j _ ↦ hpos j

/-- **The path integral of the correction rate up to the connection time is a finite sum over the
unconnected levels**: the holding time at each level above the stopping level times the correction
rate at the state of that level. -/
theorem integral_clockCorrectionRate_pathState {n : ℕ} (hn : 2 ≤ n) (s : Fin n → Fin n)
    {p : List (ER n) × (ℕ → ℝ)} (hl : p.1 ∈ (chainLaw n (n - 1)).support)
    (hpos : ∀ j, 0 ≤ p.2 j) :
    ∫ t in (0)..(connectionTime s p),
        clockCorrectionRate s (pathState n (chainOfList p.1) (clockHold p.2) t)
      = ∑ k ∈ Ioc (stoppingLevel s p.1) n,
          p.2 (k - 2) * clockCorrectionRate s (chainOfList p.1 k) := by
  have hB := mem_Icc.mp (stoppingLevel_mem_Icc hn s hl)
  have hhold : ∀ j, 0 ≤ clockHold p.2 j := fun j ↦ hpos (j - 2)
  obtain ⟨-, hint⟩ := integral_pathState_descentTime (chainOfList p.1) hhold
    (clockCorrectionRate s) (n - stoppingLevel s p.1) (by omega)
  rw [show n - (n - stoppingLevel s p.1) = stoppingLevel s p.1 by omega,
    descentTime_clockHold_eq_connectionTime hn s hl] at hint
  rw [intervalIntegral.integral_of_le (connectionTime_nonneg s hpos), integral_Ioc_eq_integral_Ioo,
    ← integral_Ico_eq_integral_Ioo, hint]
  rfl

/-! ### Unconnected levels -/

/-- **A level lies above the stopping level exactly when the report is not connected there.** -/
theorem stoppingLevel_lt_iff {n : ℕ} (hn : 2 ≤ n) (s : Fin n → Fin n) {l : List (ER n)}
    (hl : l ∈ (chainLaw n (n - 1)).support) {k : ℕ} (hk : k ≤ n) :
    stoppingLevel s l < k ↔ observed s (chainOfList l k) ≠ ⊤ := by
  constructor
  · intro hlt htop
    exact absurd (Nat.le_findGreatest hk htop) (not_le.mpr hlt)
  · intro hne
    by_contra hle
    push_neg at hle
    exact hne (observed_chainOfList_mono hl hle (observed_chainOfList_stoppingLevel hn s hl))

/-- A running rate cut off at connected reports. -/
def unconnectedRate {n : ℕ} (s : Fin n → Fin n) (g : ER n → ℝ) (ξ : ER n) : ℝ :=
  if observed s ξ = ⊤ then 0 else g ξ

/-- The correction rate cut off at connected reports is nonnegative. -/
theorem unconnectedRate_clockCorrectionRate_nonneg {n : ℕ} (hn : 0 < n) (s : Fin n → Fin n)
    (ξ : ER n) : 0 ≤ unconnectedRate s (clockCorrectionRate s) ξ := by
  unfold unconnectedRate
  by_cases hc : observed s ξ = ⊤
  · rw [if_pos hc]
  · rw [if_neg hc]
    exact clockCorrectionRate_nonneg s
      (not_le.mp fun h ↦ hc ((blocks_observed_le_one_iff hn s ξ).mp h))

/-! ### The first-step value with a running rate, unrolled -/

/-- The backward equation at zero discount and zero terminal value. -/
theorem connectionValue_zero_eq {n : ℕ} (s : Fin n → Fin n) (g : ER n → ℝ) (ξ : ER n) :
    connectionValue s 0 0 g ξ =
      if blocks (observed s ξ) ≤ 1 then 0
      else (g ξ + ∑ η : {η : ER n // Covers ξ η}, connectionValue s 0 0 g η.1)
        / deathRate (blocks ξ) := by
  have h := connectionValue_eq s 0 0 g ξ
  simp only [Pi.zero_apply, add_zero] at h
  exact h

/-- **The backward equation's average over covers is the jump kernel**, for any running rate. -/
theorem connectionValue_eq_sum_jumpLaw {n : ℕ} (hn : 0 < n) (s : Fin n → Fin n)
    (g : ER n → ℝ) {ξ : ER n} (hk : 2 ≤ blocks ξ) :
    connectionValue s 0 0 g ξ
      = (if observed s ξ = ⊤ then 0 else g ξ / deathRate (blocks ξ))
        + ∑ η : ER n, (jumpLaw ξ η).toReal * connectionValue s 0 0 g η := by
  have hsum : ∑ η : ER n, (jumpLaw ξ η).toReal * connectionValue s 0 0 g η
      = (∑ η : {η : ER n // Covers ξ η}, connectionValue s 0 0 g η.1) / deathRate (blocks ξ) := by
    simp only [jumpLaw_toReal hk, ite_mul, zero_mul]
    rw [← sum_filter, sum_div]
    refine sum_bij' (fun η h ↦ ⟨η, (mem_filter.mp h).2⟩) (fun η _ ↦ η.1)
      (fun _ _ ↦ mem_univ _) (fun η _ ↦ mem_filter.mpr ⟨mem_univ _, η.2⟩) (fun _ _ ↦ rfl)
      (fun _ _ ↦ rfl) fun η _ ↦ ?_
    ring
  rw [hsum, connectionValue_zero_eq s g ξ]
  by_cases hc : observed s ξ = ⊤
  · have hzero : ∀ η : {η : ER n // Covers ξ η}, connectionValue s 0 0 g η.1 = 0 := by
      intro η
      have htop : observed s η.1 = ⊤ := top_unique (hc.symm.le.trans (observed_mono s η.2.1))
      rw [connectionValue_zero_eq, if_pos ((blocks_observed_le_one_iff hn s _).mpr htop)]
    rw [if_pos ((blocks_observed_le_one_iff hn s ξ).mpr hc), if_pos hc,
      sum_congr rfl fun η _ ↦ hzero η, sum_const_zero, zero_div, add_zero]
  · rw [if_neg fun h ↦ hc ((blocks_observed_le_one_iff hn s ξ).mp h), if_neg hc, add_div]

/-- **One level of the first-step value with a running rate.**  Averaged over the head law after
`j` jumps, the backward equation gives the level's running rate over `d_{n-j}` plus the average
after `j + 1` jumps. -/
theorem sum_blockLaw_connectionValue_succ {n j : ℕ} (s : Fin n → Fin n) (g : ER n → ℝ)
    (hj : j + 1 < n) :
    ∑ ξ : ER n, (blockLaw n j ξ).toReal * connectionValue s 0 0 g ξ
      = (∑ ξ : ER n, (blockLaw n j ξ).toReal * unconnectedRate s g ξ) / deathRate (n - j)
        + ∑ η : ER n, (blockLaw n (j + 1) η).toReal * connectionValue s 0 0 g η := by
  have hn : 0 < n := by omega
  have hlevel : ∀ ξ : ER n, (blockLaw n j ξ).toReal * connectionValue s 0 0 g ξ
      = (blockLaw n j ξ).toReal * (if observed s ξ = ⊤ then 0 else g ξ / deathRate (n - j))
        + ∑ η : ER n,
          (blockLaw n j ξ).toReal * (jumpLaw ξ η).toReal * connectionValue s 0 0 g η := by
    intro ξ
    by_cases hb : blocks ξ = n - j
    · rw [connectionValue_eq_sum_jumpLaw hn s g (by omega : 2 ≤ blocks ξ), hb, mul_add,
        mul_sum]
      simp only [mul_assoc]
    · have hzero : (blockLaw n j ξ).toReal = 0 := by
        rw [blockLaw_toReal j (by omega) ξ, if_neg hb]
      simp only [hzero, zero_mul, sum_const_zero, add_zero]
  have hfirst : ∑ ξ : ER n, (blockLaw n j ξ).toReal
        * (if observed s ξ = ⊤ then 0 else g ξ / deathRate (n - j))
      = (∑ ξ : ER n, (blockLaw n j ξ).toReal * unconnectedRate s g ξ) / deathRate (n - j) := by
    rw [sum_div]
    refine sum_congr rfl fun ξ _ ↦ ?_
    unfold unconnectedRate
    by_cases hc : observed s ξ = ⊤
    · simp only [if_pos hc, mul_zero, zero_div]
    · simp only [if_neg hc]
      ring
  rw [sum_congr rfl fun ξ _ ↦ hlevel ξ, sum_add_distrib, hfirst, sum_comm]
  congr 1
  refine sum_congr rfl fun η _ ↦ ?_
  rw [blockLaw_succ_toReal, sum_mul]

/-- **The first-step value at `k` blocks with a running rate, unrolled.** -/
theorem sum_blockLaw_connectionValue {n : ℕ} (s : Fin n → Fin n) (g : ER n → ℝ) :
    ∀ k, 1 ≤ k → k ≤ n →
      ∑ ξ : ER n, (blockLaw n (n - k) ξ).toReal * connectionValue s 0 0 g ξ
        = ∑ i ∈ Ioc 1 k,
          (∑ ξ : ER n, (blockLaw n (n - i) ξ).toReal * unconnectedRate s g ξ) / deathRate i := by
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
      rw [connectionValue_zero_eq,
        if_pos ((blocks_observed_le_one_iff (by omega) s ξ).mpr htop), mul_zero]
    · rw [blockLaw_toReal (n - 1) (by omega) ξ,
        if_neg (show ¬ blocks ξ = n - (n - 1) by omega), zero_mul]
  | succ k hk ih =>
    intro hkn
    rw [sum_blockLaw_connectionValue_succ s g (show n - (k + 1) + 1 < n by omega),
      show n - (n - (k + 1)) = k + 1 by omega, show n - (k + 1) + 1 = n - k by omega,
      ih (by omega), sum_Ioc_succ_top (by omega : 1 ≤ k)]
    ring

/-- The first-step value from `⊥` with a running rate, unrolled. -/
theorem connectionValue_bot_eq_sum {n : ℕ} (hn : 2 ≤ n) (s : Fin n → Fin n) (g : ER n → ℝ) :
    connectionValue s 0 0 g ⊥
      = ∑ k ∈ Ioc 1 n,
          (∑ ξ : ER n, (blockLaw n (n - k) ξ).toReal * unconnectedRate s g ξ) / deathRate k := by
  have h := sum_blockLaw_connectionValue s g n (by omega) le_rfl
  have hlaw : blockLaw n (n - n) = PMF.pure (Delta n) := by
    rw [Nat.sub_self, blockLaw_eq_map, chainLaw, PMF.pure_map]
    rfl
  rw [hlaw, sum_eq_single (Delta n)
    (fun ξ _ hξ ↦ by rw [PMF.pure_apply, if_neg hξ, ENNReal.toReal_zero, zero_mul])
    (fun hmem ↦ absurd (mem_univ _) hmem), PMF.pure_apply, if_pos rfl, ENNReal.toReal_one,
    one_mul] at h
  exact h

/-! ### The expectation of the path integral -/

/-- **The expected path integral of the correction rate is the first-step value.**  Under the path
law, the expectation of `∫_0^{τ_q} (λ_vis(X_t)/C(r_t, 2) - 1) dt` is the solution at `⊥` of the
backward equation with that running rate. -/
theorem lintegral_integral_clockCorrectionRate {n : ℕ} (hn : 2 ≤ n) (s : Fin n → Fin n) :
    ∫⁻ p, ENNReal.ofReal (∫ t in (0)..(connectionTime s p),
        clockCorrectionRate s (pathState n (chainOfList p.1) (clockHold p.2) t))
        ∂(trajectoryClockLaw n)
      = ENNReal.ofReal (connectionValue s 0 0 (clockCorrectionRate s) ⊥) := by
  haveI := measurableSingletonClass_ER n
  have hh0 : ∀ ξ : ER n, 0 ≤ unconnectedRate s (clockCorrectionRate s) ξ :=
    unconnectedRate_clockCorrectionRate_nonneg (by omega) s
  have hae : (fun p : List (ER n) × (ℕ → ℝ) ↦ ENNReal.ofReal (∫ t in (0)..(connectionTime s p),
        clockCorrectionRate s (pathState n (chainOfList p.1) (clockHold p.2) t)))
      =ᵐ[trajectoryClockLaw n] fun p ↦ ∑ k ∈ Ioc 1 n,
        ENNReal.ofReal (unconnectedRate s (clockCorrectionRate s) (chainOfList p.1 k))
          * ENNReal.ofReal (p.2 (k - 2)) := by
    filter_upwards [ae_mem_support_nonneg] with p hp
    rw [integral_clockCorrectionRate_pathState hn s hp.1 hp.2]
    have hB := mem_Icc.mp (stoppingLevel_mem_Icc hn s hp.1)
    have hfilter : Ioc (stoppingLevel s p.1) n = (Ioc 1 n).filter (stoppingLevel s p.1 < ·) := by
      ext k
      simp only [mem_Ioc, mem_filter]
      omega
    have hsum : ∑ k ∈ Ioc (stoppingLevel s p.1) n,
          p.2 (k - 2) * clockCorrectionRate s (chainOfList p.1 k)
        = ∑ k ∈ Ioc 1 n,
          unconnectedRate s (clockCorrectionRate s) (chainOfList p.1 k) * p.2 (k - 2) := by
      rw [hfilter, sum_filter]
      refine sum_congr rfl fun k hk ↦ ?_
      have hkn := (mem_Ioc.mp hk).2
      unfold unconnectedRate
      by_cases hlt : stoppingLevel s p.1 < k
      · rw [if_pos hlt, if_neg ((stoppingLevel_lt_iff hn s hp.1 hkn).mp hlt)]
        ring
      · rw [if_neg hlt,
          if_pos (not_not.mp (mt (stoppingLevel_lt_iff hn s hp.1 hkn).mpr hlt)), zero_mul]
    rw [hsum, ENNReal.ofReal_sum_of_nonneg fun k _ ↦ mul_nonneg (hh0 _) (hp.2 _)]
    exact sum_congr rfl fun k _ ↦ ENNReal.ofReal_mul (hh0 _)
  have hmeas : ∀ k ∈ Ioc 1 n, Measurable fun p : List (ER n) × (ℕ → ℝ) ↦
      ENNReal.ofReal (unconnectedRate s (clockCorrectionRate s) (chainOfList p.1 k))
        * ENNReal.ofReal (p.2 (k - 2)) := by
    intro k _
    have hf : Measurable fun l : List (ER n) ↦
        ENNReal.ofReal (unconnectedRate s (clockCorrectionRate s) (chainOfList l k)) :=
      measurable_of_countable _
    have hg : Measurable fun ω : ℕ → ℝ ↦ ENNReal.ofReal (ω (k - 2)) :=
      ENNReal.measurable_ofReal.comp (measurable_pi_apply (k - 2))
    exact (hf.comp measurable_fst).mul (hg.comp measurable_snd)
  have hlevel : ∀ k ∈ Ioc 1 n, ∫⁻ p, ENNReal.ofReal
        (unconnectedRate s (clockCorrectionRate s) (chainOfList p.1 k))
          * ENNReal.ofReal (p.2 (k - 2)) ∂(trajectoryClockLaw n)
      = ENNReal.ofReal ((∑ ξ : ER n, (blockLaw n (n - k) ξ).toReal
          * unconnectedRate s (clockCorrectionRate s) ξ) / deathRate k) := by
    intro k hk
    have hk2 : 2 ≤ k := by
      have h1 := (mem_Ioc.mp hk).1
      omega
    have hkn : k ≤ n := (mem_Ioc.mp hk).2
    rw [trajectoryClockLaw, lintegral_prod_mul
      (f := fun l : List (ER n) ↦
        ENNReal.ofReal (unconnectedRate s (clockCorrectionRate s) (chainOfList l k)))
      (g := fun ω : ℕ → ℝ ↦ ENNReal.ofReal (ω (k - 2)))
      (measurable_of_countable _).aemeasurable
      (ENNReal.measurable_ofReal.comp (measurable_pi_apply (k - 2))).aemeasurable,
      lintegral_coord_kingmanClock, show k - 2 + 2 = k by omega]
    have hgetD := chainLaw_map_getD (n := n) (n - 1) (k - 1) (by omega)
    rw [show n - 1 - (k - 1) = n - k by omega] at hgetD
    have hmap : (chainLaw n (n - 1)).toMeasure.map (fun l ↦ l.getD (k - 1) (Delta n))
        = (blockLaw n (n - k)).toMeasure := by
      ext S hS
      rw [Measure.map_apply (measurable_of_countable _) hS, ← hgetD,
        PMF.toMeasure_map_apply (hf := measurable_of_countable _) (hs := hS)]
    have hchain : ∫⁻ l, ENNReal.ofReal
          (unconnectedRate s (clockCorrectionRate s) (chainOfList l k))
          ∂(chainLaw n (n - 1)).toMeasure
        = ENNReal.ofReal (∑ ξ : ER n, (blockLaw n (n - k) ξ).toReal
          * unconnectedRate s (clockCorrectionRate s) ξ) := by
      change ∫⁻ l, ENNReal.ofReal
          (unconnectedRate s (clockCorrectionRate s) (l.getD (k - 1) (Delta n)))
          ∂(chainLaw n (n - 1)).toMeasure = _
      rw [← lintegral_map
        (f := fun ξ : ER n ↦ ENNReal.ofReal (unconnectedRate s (clockCorrectionRate s) ξ))
        (g := fun l : List (ER n) ↦ l.getD (k - 1) (Delta n))
        (measurable_of_countable _) (measurable_of_countable _), hmap, lintegral_fintype,
        ENNReal.ofReal_sum_of_nonneg fun ξ _ ↦ mul_nonneg ENNReal.toReal_nonneg (hh0 ξ)]
      refine sum_congr rfl fun ξ _ ↦ ?_
      rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton ξ),
        ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal (PMF.apply_ne_top _ _),
        mul_comm]
    rw [hchain, ← ENNReal.ofReal_mul
      (sum_nonneg fun ξ _ ↦ mul_nonneg ENNReal.toReal_nonneg (hh0 ξ)), ← div_eq_mul_one_div]
  have hd : ∀ k ∈ Ioc 1 n, 0 < deathRate k := fun k hk ↦
    deathRate_pos (by have h1 := (mem_Ioc.mp hk).1; omega)
  rw [lintegral_congr_ae hae, lintegral_finset_sum _ hmeas, sum_congr rfl hlevel,
    connectionValue_bot_eq_sum hn s,
    ENNReal.ofReal_sum_of_nonneg fun k hk ↦ div_nonneg
      (sum_nonneg fun ξ _ ↦ mul_nonneg ENNReal.toReal_nonneg (hh0 ξ)) (hd k hk).le]

/-! ### (C3) on the path -/

/-- **(C3) as a path identity.**  Under the trajectory-and-clock law, the Kingman clock at the
interface width minus the expected connection time is the expected path integral of the correction
rate up to the connection time:
`2 - 2/w - E τ_q = E ∫_0^{τ_q} (λ_vis(X_t)/C(r_t, 2) - 1) dt`. -/
theorem clockDynkin_path {n : ℕ} (hn : 2 ≤ n) (s : Fin n → Fin n) :
    2 - 2 / (Linkage.width s : ℝ)
        - (∫⁻ p, ENNReal.ofReal (connectionTime s p) ∂(trajectoryClockLaw n)).toReal
      = (∫⁻ p, ENNReal.ofReal (∫ t in (0)..(connectionTime s p),
          clockCorrectionRate s (pathState n (chainOfList p.1) (clockHold p.2) t))
          ∂(trajectoryClockLaw n)).toReal := by
  haveI : NeZero n := ⟨by omega⟩
  have hw : 1 ≤ Linkage.width s := by
    rw [← blocks_graphKer]
    exact blocks_pos _
  have hmean : 0 ≤ meanConnectionTime s ⊥ :=
    connectionValue_nonneg s le_rfl (fun _ _ ↦ le_rfl) (fun _ _ ↦ zero_le_one) ⊥
  have hvalue : 0 ≤ connectionValue s 0 0 (clockCorrectionRate s) ⊥ :=
    connectionValue_nonneg s le_rfl (fun _ _ ↦ le_rfl)
      (fun _ hζ ↦ clockCorrectionRate_nonneg s hζ) ⊥
  rw [connectionTime_mean_eq_meanConnectionTime hn s, lintegral_integral_clockCorrectionRate hn s,
    ENNReal.toReal_ofReal hmean, ENNReal.toReal_ofReal hvalue,
    ← meanTransitTime_sub_meanConnectionTime s ⊥, observed_bot, blocks_graphKer,
    meanTransitTime_eq_two_sub hw]

/-- **(C3) at the first hitting time of the connected report.**  The same identity with `τ_q` the
first time the report of the coalescent path is connected. -/
theorem clockDynkin_reportHittingTime {n : ℕ} (hn : 2 ≤ n) (s : Fin n → Fin n) :
    2 - 2 / (Linkage.width s : ℝ)
        - (∫⁻ p, ENNReal.ofReal (reportHittingTime s p.1 (clockHold p.2))
          ∂(trajectoryClockLaw n)).toReal
      = (∫⁻ p, ENNReal.ofReal (∫ t in (0)..(reportHittingTime s p.1 (clockHold p.2)),
          clockCorrectionRate s (pathState n (chainOfList p.1) (clockHold p.2) t))
          ∂(trajectoryClockLaw n)).toReal := by
  have htime : (fun p : List (ER n) × (ℕ → ℝ) ↦
        ENNReal.ofReal (reportHittingTime s p.1 (clockHold p.2)))
      =ᵐ[trajectoryClockLaw n] fun p ↦ ENNReal.ofReal (connectionTime s p) :=
    (ae_reportHittingTime_eq_connectionTime hn s).mono fun p hp ↦ by simp only [hp]
  have hpath : (fun p : List (ER n) × (ℕ → ℝ) ↦
        ENNReal.ofReal (∫ t in (0)..(reportHittingTime s p.1 (clockHold p.2)),
          clockCorrectionRate s (pathState n (chainOfList p.1) (clockHold p.2) t)))
      =ᵐ[trajectoryClockLaw n] fun p ↦ ENNReal.ofReal (∫ t in (0)..(connectionTime s p),
          clockCorrectionRate s (pathState n (chainOfList p.1) (clockHold p.2) t)) :=
    (ae_reportHittingTime_eq_connectionTime hn s).mono fun p hp ↦ by simp only [hp]
  rw [lintegral_congr_ae htime, lintegral_congr_ae hpath]
  exact clockDynkin_path hn s

end

end Descent.Pangenome.GraphCoalescent
