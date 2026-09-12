/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Pangenome.GraphCoalescent.ConnectionClockPathLaw
import Descent.Pangenome.GraphCoalescent.ReportedConnectionFirstStep

assert_below Descent.PopGen Descent.Spectral Descent.Blindness Descent.Conditionals
assert_below Descent.Portability Descent.Decision Descent.Program

/-!
# The reported connection time is the first hitting time of `⊤` by the report of the path

`Descent.Pangenome.GraphCoalescent.ReportedConnectionClock` defines `connectionTime s p`, on a pair
`p` of a jump-chain trajectory and a Kingman clock, as the sum of the holding times at the levels
above the stopping level `B`, and records that this sum is not proved to be the first time the
report of the coalescent path `R_t = ℛ_{D(n,t)}` of `Descent.Coalescent.Path` reaches `⊤`. This file
proves it.

## What is proved

* `reportHittingTime s l hold` is the first time `t ≥ 0` at which the report `observed s R_t` of
  the path `Path.pathState n (chainOfList l) hold` is `⊤`.
* `isLeast_reportHittingSet`: on every full trajectory of the jump chain and every nonnegative
  sequence of holding times, the connected times are exactly `[descentTime n hold B, ∞)`. The
  report is connected at the levels `1, …, B` and at no level above, and the path is at a level at
  most `B` exactly once the descent to `B` has elapsed. So the first hitting time is the time to
  descend to the stopping level (`reportHittingTime_eq`).
* With the clock coordinates as holding times (`clockHold`), the hitting time is `connectionTime`
  on every trajectory (`reportHittingTime_clockHold`) and almost surely under `trajectoryClockLaw`
  (`ae_reportHittingTime_eq_connectionTime`). So the hitting time and the connection time have one
  law (`map_reportHittingTime_eq_map_connectionTime`), and its mean is the first-step mean
  connection time of `VisibleIntensityClock` (`lintegral_reportHittingTime`).

## Empirical status

None. The bodies here are identities about one trajectory of the jump chain and one sequence of
holding times, and a null-set argument under the product law built from the corpus jump law and
holding law; no measurement can bear on them.
-/

set_option autoImplicit false

namespace Descent.Pangenome.GraphCoalescent

open Coalescent Finset MeasureTheory
open scoped Classical NNReal ENNReal

noncomputable section

/-! ### The first hitting time on one trajectory -/

/-- The times at which the report of the coalescent path is connected. -/
def reportHittingSet {n : ℕ} (s : Fin n → Fin n) (l : List (ER n)) (hold : ℕ → ℝ) : Set ℝ :=
  {t : ℝ | 0 ≤ t ∧ observed s (pathState n (chainOfList l) hold t) = ⊤}

/-- **The first time the report of the coalescent path is connected.** -/
def reportHittingTime {n : ℕ} (s : Fin n → Fin n) (l : List (ER n)) (hold : ℕ → ℝ) : ℝ :=
  sInf (reportHittingSet s l hold)

/-- On a full trajectory the report is connected at the stopping level. -/
theorem observed_chainOfList_stoppingLevel {n : ℕ} (hn : 2 ≤ n) (s : Fin n → Fin n)
    {l : List (ER n)} (hl : l ∈ (chainLaw n (n - 1)).support) :
    observed s (chainOfList l (stoppingLevel s l)) = ⊤ :=
  Nat.findGreatest_spec (P := fun k ↦ observed s (chainOfList l k) = ⊤) (by omega : 1 ≤ n)
    (observed_chainOfList_one hn s hl)

/-- **The connected times of the path are `[descentTime n hold B, ∞)`.** The descent to the
stopping level `B` is connected, and every earlier time sees the path at a level above `B`, where
the report is not connected. -/
theorem isLeast_reportHittingSet {n : ℕ} (hn : 2 ≤ n) (s : Fin n → Fin n) {l : List (ER n)}
    (hl : l ∈ (chainLaw n (n - 1)).support) {hold : ℕ → ℝ} (hpos : ∀ j, 0 ≤ hold j) :
    IsLeast (reportHittingSet s l hold) (descentTime n hold (stoppingLevel s l)) := by
  have hB := stoppingLevel_mem_Icc hn s hl
  rw [mem_Icc] at hB
  constructor
  · refine ⟨descentTime_nonneg n hpos _, ?_⟩
    unfold pathState
    exact observed_chainOfList_mono hl
      (blockCountAt_le_of_descentTime_le n hpos hB.1 hB.2 le_rfl)
      (observed_chainOfList_stoppingLevel hn s hl)
  · rintro t ⟨ht0, htop⟩
    by_contra hlt
    have hk := lt_blockCountAt_of_lt_descentTime n hpos hB.1 hB.2 (not_le.mp hlt)
    have hkn := blockCountAt_le n (hold := hold) ht0 (by omega : 1 ≤ n)
    exact Nat.findGreatest_is_greatest (P := fun k ↦ observed s (chainOfList l k) = ⊤) hk hkn
      htop

/-- **The first hitting time of `⊤` by the report is the time to descend to the stopping
level.** -/
theorem reportHittingTime_eq {n : ℕ} (hn : 2 ≤ n) (s : Fin n → Fin n) {l : List (ER n)}
    (hl : l ∈ (chainLaw n (n - 1)).support) {hold : ℕ → ℝ} (hpos : ∀ j, 0 ≤ hold j) :
    reportHittingTime s l hold = descentTime n hold (stoppingLevel s l) :=
  (isLeast_reportHittingSet hn s hl hpos).csInf_eq

/-! ### The clock as holding times -/

/-- The clock coordinates read as holding times indexed by level: level `k` holds `ω (k - 2)`. -/
def clockHold (ω : ℕ → ℝ) (k : ℕ) : ℝ :=
  ω (k - 2)

/-- The descent to the stopping level, timed by the clock, is the reported connection time. -/
theorem descentTime_clockHold_eq_connectionTime {n : ℕ} (hn : 2 ≤ n) (s : Fin n → Fin n)
    {p : List (ER n) × (ℕ → ℝ)} (hl : p.1 ∈ (chainLaw n (n - 1)).support) :
    descentTime n (clockHold p.2) (stoppingLevel s p.1) = connectionTime s p := by
  have hB := stoppingLevel_mem_Icc hn s hl
  rw [mem_Icc] at hB
  rw [connectionTime_of_stoppingLevel s hB.1 hB.2 rfl, descentTime, ico_succ_eq_ioc]
  rfl

/-- **The reported connection time is the first hitting time of `⊤` by the report of the path**,
on every full trajectory and every nonnegative clock. -/
theorem reportHittingTime_clockHold {n : ℕ} (hn : 2 ≤ n) (s : Fin n → Fin n)
    {p : List (ER n) × (ℕ → ℝ)} (hl : p.1 ∈ (chainLaw n (n - 1)).support)
    (hpos : ∀ j, 0 ≤ p.2 j) :
    reportHittingTime s p.1 (clockHold p.2) = connectionTime s p := by
  rw [reportHittingTime_eq hn s hl (hold := clockHold p.2) fun j ↦ hpos (j - 2),
    descentTime_clockHold_eq_connectionTime hn s hl]

/-- Under the path law the trajectory is a full trajectory and the clock is nonnegative, almost
surely. -/
theorem ae_mem_support_nonneg {n : ℕ} :
    ∀ᵐ p ∂(trajectoryClockLaw n), p.1 ∈ (chainLaw n (n - 1)).support ∧ ∀ j, 0 ≤ p.2 j := by
  have h1 : (chainLaw n (n - 1)).toMeasure (chainLaw n (n - 1)).supportᶜ = 0 :=
    ((chainLaw n (n - 1)).toMeasure_apply_eq_zero_iff MeasurableSpace.measurableSet_top).mpr
      disjoint_compl_right
  have h2 : kingmanClock {ω : ℕ → ℝ | ¬ ∀ j, 0 ≤ ω j} = 0 := ae_iff.mp ae_nonneg_kingmanClock
  rw [ae_iff]
  refine measure_mono_null (t := (chainLaw n (n - 1)).supportᶜ ×ˢ Set.univ
    ∪ Set.univ ×ˢ {ω : ℕ → ℝ | ¬ ∀ j, 0 ≤ ω j}) ?_ ?_
  · intro p hp
    simp only [Set.mem_setOf_eq, not_and_or] at hp
    rcases hp with h | h
    · exact Or.inl ⟨h, Set.mem_univ _⟩
    · exact Or.inr ⟨Set.mem_univ _, h⟩
  · refine measure_union_null ?_ ?_
    · rw [trajectoryClockLaw_prod, h1, zero_mul]
    · rw [trajectoryClockLaw_prod, h2, mul_zero]

/-- **Almost surely, the reported connection time is the first hitting time of `⊤`.** -/
theorem ae_reportHittingTime_eq_connectionTime {n : ℕ} (hn : 2 ≤ n) (s : Fin n → Fin n) :
    ∀ᵐ p ∂(trajectoryClockLaw n),
      reportHittingTime s p.1 (clockHold p.2) = connectionTime s p := by
  filter_upwards [ae_mem_support_nonneg] with p hp
  exact reportHittingTime_clockHold hn s hp.1 hp.2

/-- **The hitting time and the reported connection time have one law.** -/
theorem map_reportHittingTime_eq_map_connectionTime {n : ℕ} (hn : 2 ≤ n) (s : Fin n → Fin n) :
    (trajectoryClockLaw n).map (fun p ↦ Real.toNNReal (reportHittingTime s p.1 (clockHold p.2)))
      = (trajectoryClockLaw n).map (fun p ↦ Real.toNNReal (connectionTime s p)) :=
  Measure.map_congr ((ae_reportHittingTime_eq_connectionTime hn s).mono fun p hp ↦ by
    simp only [hp])

/-- **The mean first hitting time is the first-step mean connection time**, through
`ReportedConnectionFirstStep.connectionTime_mean_eq_meanConnectionTime`, and hence the mean of
`ConnectionClockPathLaw.connectionTimeLaw` at `⊥`. -/
theorem lintegral_reportHittingTime {n : ℕ} (hn : 2 ≤ n) (s : Fin n → Fin n) :
    ∫⁻ p, ENNReal.ofReal (reportHittingTime s p.1 (clockHold p.2)) ∂(trajectoryClockLaw n)
      = ∫⁻ x, (x : ℝ≥0∞) ∂(connectionTimeLaw s ⊥) := by
  have hae : (fun p : List (ER n) × (ℕ → ℝ) ↦
        ENNReal.ofReal (reportHittingTime s p.1 (clockHold p.2)))
      =ᵐ[trajectoryClockLaw n] fun p ↦ ENNReal.ofReal (connectionTime s p) :=
    (ae_reportHittingTime_eq_connectionTime hn s).mono fun p hp ↦ by simp only [hp]
  rw [lintegral_congr_ae hae, connectionTime_mean_eq_meanConnectionTime hn s,
    lintegral_coe_connectionTimeLaw]

end

end Descent.Pangenome.GraphCoalescent
