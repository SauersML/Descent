/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Coalescent.StructuredPresentDay
import Descent.Pangenome.GraphCoalescent.ReportedConnectionClock
import Descent.Pangenome.GraphCoalescent.ConnectionClockStochasticOrder
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Probability.ProductMeasure

assert_below Descent.PopGen Descent.Spectral Descent.Blindness Descent.Conditionals
assert_below Descent.Portability Descent.Decision Descent.Program

/-!
# The finite continuous-time jump process: its path law and matrix-exponential marginals

The pangenome hidden-clock note runs its chains in continuous time, and the corpus had them only
through their semigroups (`TwoComponentSurvival`, `HiddenLoadFiltering`, `UniformizationIdentity`)
or, for Kingman's coalescent alone, through a jump chain with an independent clock
(`ReportedConnectionClock.trajectoryClockLaw`). This module constructs the continuous-time chain
on a finite state space as a process, from its jump chain and exponential holding times, and
proves that its one-dimensional marginals are the rows of the matrix exponential.

**The data.** A finite state space `S`, a holding rate `rate x > 0` and a jump law `kernel x` for
every state. The chain holds at `x` for an exponential time of rate `rate x` and then jumps to a
state drawn from `kernel x`. Its generator is
`holdJumpGenerator rate kernel x y = rate x (kernel x y - [x = y])`. A generator `Q` with
nonnegative off-diagonal rates and zero row sums is `holdJumpGenerator` of the jump chain with rates
`Q x y / q x` and holding rate `q x = -Q x x` (`holdJumpGenerator_canonical`); an absorbing state,
`q x = 0`, holds at rate one and jumps to itself, so Kingman-type chains are included.

**The path space.** At every step `k` and for every state `x` an independent draw from
`kernel x ⊗ Exp(rate x)` is made (`stepMeasure`, `pathMeasure` on `ℕ → S → S × ℝ`). From `x` the
chain reads the draw of its current state at each step: `jumpState ω x k` is the state after `k`
jumps, and `jumpHoldSeq ω x k` is that state with its holding time. The jump states form the jump
chain and, given them, the holding times are independent exponentials of their rates
(`pathMeasure_jumpHold_cylinder`).

**The state at time `t`.** On a sequence of states and holding times, `stateAt path t` is the
state of the sojourn containing `t`: it is `(path k).1` on `[T_k, T_{k+1})` with `T_k` the time
the first `k` sojourns have ended (`stateAt_eq_of_mem_Ico`), and `none` if infinitely many
sojourns end by time `t`. It is computed by following at most `m` sojourns (`fuelState`), and
the first step decomposes it: either the first holding time exceeds `t`, or the chain jumps at
an independent exponential time and restarts (`fuelProb_succ`, through the splitting of the
infinite product `map_consSeq_infinitePi`).

**The marginals.** For `t ≥ 0`, `P_x(X_t = y) = e^{tG}(x, y)` (`pathMeasure_stateAt_eq`,
`stateProb_eq`). The probabilities of the fuel-limited states are the Picard iterates of the
first-jump equation, which the matrix exponential satisfies (`exp_smul_apply_eq_firstJump`,
`ofReal_exp_smul_apply_eq_firstJump`), so they stay below it (`fuelProb_le_exp`). The chance that
`m` sojourns end by time `t` is at most `(1 - e^{-Rt})^m` for `R` the total rate
(`fuelProb_none_le`), so the marginals sum to one, and since the rows of `e^{tG}` sum to one
(`sum_exp_smul_holdJumpGenerator`) the two agree. The chain does not explode
(`pathMeasure_stateAt_none`). The marginals solve the forward and backward equations
(`hasDerivAt_stateProb_forward`, `hasDerivAt_stateProb_backward`) and Chapman-Kolmogorov
(`stateProb_add`).

Scope. The Markov property at fixed times is proved only for the one-dimensional marginals, as
Chapman-Kolmogorov for `P_x(X_t = y)`; the finite-dimensional laws at several times and the
identification of the path law with a measure on càdlàg paths are not formalized. The forward and
backward equations are stated at `t > 0`.

## Empirical status

None. The bodies here are an infinite product of exponential and finite laws, a first-step
recursion for events of that product, and a finite matrix exponential, so no measurement can bear
on them.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Pangenome.GraphCoalescent.FiniteJumpProcess

open MeasureTheory Filter Topology
open scoped Classical ENNReal Matrix.Norms.Operator

noncomputable section

/-! ### The state at time `t` of a sequence of sojourns -/

section Paths

variable {S : Type*}

/-- **The state at time `t` after at most `m` sojourns** of a sequence of states and holding
times, sojourn `k` holding `(path k).1` for the time `(path k).2`. It is `none` when the first `m`
sojourns end by time `t`. -/
def fuelState : ℕ → (ℕ → S × ℝ) → ℝ → Option S
  | 0, _, _ => none
  | m + 1, path, t =>
    if t < (path 0).2 then some (path 0).1
    else fuelState m (fun k ↦ path (k + 1)) (t - (path 0).2)

theorem fuelState_succ (m : ℕ) (path : ℕ → S × ℝ) (t : ℝ) :
    fuelState (m + 1) path t = if t < (path 0).2 then some (path 0).1
      else fuelState m (fun k ↦ path (k + 1)) (t - (path 0).2) := rfl

/-- A state found by following `m` sojourns is found by following one more. -/
theorem fuelState_succ_of_eq_some {m : ℕ} {path : ℕ → S × ℝ} {t : ℝ} {y : S}
    (h : fuelState m path t = some y) : fuelState (m + 1) path t = some y := by
  induction m generalizing path t with
  | zero => simp [fuelState] at h
  | succ m ih =>
    rw [fuelState_succ] at h ⊢
    split_ifs at h ⊢
    · exact h
    · exact ih h

theorem fuelState_eq_some_of_le {m m' : ℕ} (hm : m ≤ m') {path : ℕ → S × ℝ} {t : ℝ} {y : S}
    (h : fuelState m path t = some y) : fuelState m' path t = some y := by
  induction m', hm using Nat.le_induction with
  | base => exact h
  | succ m' _ ih => exact fuelState_succ_of_eq_some ih

/-- **The state at time `t`** of a sequence of states and holding times: the state of the sojourn
containing `t`, or `none` when infinitely many sojourns end by time `t`. -/
def stateAt (path : ℕ → S × ℝ) (t : ℝ) : Option S :=
  if h : ∃ m, (fuelState m path t).isSome then fuelState (Nat.find h) path t else none

theorem stateAt_eq_some_iff {path : ℕ → S × ℝ} {t : ℝ} {y : S} :
    stateAt path t = some y ↔ ∃ m, fuelState m path t = some y := by
  unfold stateAt
  split_ifs with h
  · refine ⟨fun hy ↦ ⟨Nat.find h, hy⟩, ?_⟩
    rintro ⟨m, hm⟩
    obtain ⟨y', hy'⟩ := Option.isSome_iff_exists.mp (Nat.find_spec h)
    have hmin : Nat.find h ≤ m := Nat.find_min' h (by simp [hm])
    have h2 := fuelState_eq_some_of_le hmin hy'
    rw [hm] at h2
    rw [hy']
    exact h2.symm
  · refine ⟨fun hy ↦ by simp at hy, ?_⟩
    rintro ⟨m, hm⟩
    exact (h ⟨m, by simp [hm]⟩).elim

theorem stateAt_eq_none_iff {path : ℕ → S × ℝ} {t : ℝ} :
    stateAt path t = none ↔ ∀ m, fuelState m path t = none := by
  constructor
  · intro h m
    cases hm : fuelState m path t with
    | none => rfl
    | some y =>
      have hy := stateAt_eq_some_iff.mpr ⟨m, hm⟩
      rw [h] at hy
      simp at hy
  · intro h
    cases hs : stateAt path t with
    | none => rfl
    | some y =>
      obtain ⟨m, hm⟩ := stateAt_eq_some_iff.mp hs
      rw [h m] at hm
      simp at hm

/-- The time at which the first `k` sojourns of a sequence have ended. -/
def jumpTime (path : ℕ → S × ℝ) (k : ℕ) : ℝ := ∑ j ∈ Finset.range k, (path j).2

theorem jumpTime_succ_shift (path : ℕ → S × ℝ) (k : ℕ) :
    jumpTime path (k + 1) = (path 0).2 + jumpTime (fun j ↦ path (j + 1)) k := by
  rw [jumpTime, jumpTime, Finset.sum_range_succ', add_comm]

theorem fuelState_of_jumpTime_le :
    ∀ (k : ℕ) (path : ℕ → S × ℝ) (t : ℝ), (∀ j ≤ k, jumpTime path j ≤ t) →
      t < jumpTime path (k + 1) → fuelState (k + 1) path t = some (path k).1
  | 0, path, t, _, hlt => by
    have h0 : t < (path 0).2 := by simpa [jumpTime] using hlt
    rw [fuelState_succ, if_pos h0]
  | k + 1, path, t, hle, hlt => by
    have h1 : (path 0).2 ≤ t := by simpa [jumpTime] using hle 1 (by omega)
    rw [fuelState_succ, if_neg (not_lt.mpr h1)]
    refine fuelState_of_jumpTime_le k (fun j ↦ path (j + 1)) (t - (path 0).2)
      (fun j hj ↦ ?_) ?_
    · have hj' := hle (j + 1) (by omega)
      rw [jumpTime_succ_shift] at hj'
      linarith
    · rw [jumpTime_succ_shift] at hlt
      linarith

/-- **The state at time `t` is defined piecewise**: with nonnegative holding times it is the state
of sojourn `k` on `[T_k, T_{k+1})`, `T_k` being the time the first `k` sojourns have ended. -/
theorem stateAt_eq_of_mem_Ico {path : ℕ → S × ℝ} (hpos : ∀ j, 0 ≤ (path j).2) {t : ℝ} {k : ℕ}
    (ht : t ∈ Set.Ico (jumpTime path k) (jumpTime path (k + 1))) :
    stateAt path t = some (path k).1 := by
  refine stateAt_eq_some_iff.mpr
    ⟨k + 1, fuelState_of_jumpTime_le k path t (fun j hj ↦ ?_) ht.2⟩
  exact le_trans (Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset.mpr hj)
    fun i _ _ ↦ hpos i) ht.1

end Paths

/-! ### Splitting an infinite product at its first coordinate -/

/-- Prepend one term to a sequence. -/
def consSeq {X : Type*} (a : X) (ω : ℕ → X) : ℕ → X
  | 0 => a
  | k + 1 => ω k

theorem measurable_consSeq {X : Type*} [MeasurableSpace X] :
    Measurable fun p : X × (ℕ → X) ↦ consSeq p.1 p.2 := by
  refine measurable_pi_iff.mpr fun k ↦ ?_
  cases k with
  | zero => exact measurable_fst
  | succ k => exact (measurable_pi_apply k).comp measurable_snd

/-- **An infinite product splits off its first coordinate**: prepending an independent draw of
`P` to a sequence drawn from `P^ℕ` gives a sequence drawn from `P^ℕ`. -/
theorem map_consSeq_infinitePi {X : Type*} [MeasurableSpace X] (P : Measure X)
    [IsProbabilityMeasure P] :
    (P.prod (Measure.infinitePi fun _ : ℕ ↦ P)).map (fun p ↦ consSeq p.1 p.2)
      = Measure.infinitePi fun _ : ℕ ↦ P := by
  refine Measure.eq_infinitePi _ fun s t ht ↦ ?_
  have hinj : Set.InjOn (fun i : ℕ ↦ i + 1) ((fun i : ℕ ↦ i + 1) ⁻¹' ↑s) :=
    fun _ _ _ _ h ↦ Nat.succ_injective h
  have hpre : (fun p : X × (ℕ → X) ↦ consSeq p.1 p.2) ⁻¹' Set.pi (↑s) t
      = {a | 0 ∈ s → a ∈ t 0} ×ˢ Set.pi ↑(s.preimage (fun i : ℕ ↦ i + 1) hinj)
          (fun i ↦ t (i + 1)) := by
    ext ⟨a, ω⟩
    simp only [Set.mem_preimage, Set.mem_pi, Finset.mem_coe, Set.mem_prod, Set.mem_setOf_eq,
      Finset.mem_preimage]
    constructor
    · intro h
      exact ⟨fun h0 ↦ h 0 h0, fun i hi ↦ h (i + 1) hi⟩
    · rintro ⟨h0, h1⟩ k hk
      cases k with
      | zero => exact h0 hk
      | succ k => exact h1 k hk
  have hone : ∀ k ∈ s, k ∉ Set.range (fun i : ℕ ↦ i + 1) →
      (fun k ↦ if k = 0 then (1 : ℝ≥0∞) else P (t k)) k = 1 := by
    intro k _ hk
    have hk0 : k = 0 := by
      by_contra hne
      exact hk ⟨k - 1, show k - 1 + 1 = k by omega⟩
    simp [hk0]
  have hpreimage := Finset.prod_preimage (fun i : ℕ ↦ i + 1) s hinj
    (fun k ↦ if k = 0 then (1 : ℝ≥0∞) else P (t k)) hone
  simp only [Nat.add_one_ne_zero, ↓reduceIte] at hpreimage
  rw [Measure.map_apply measurable_consSeq (MeasurableSet.pi s.countable_toSet ht), hpre,
    Measure.prod_prod,
    Measure.infinitePi_pi _ fun i hi ↦ ht (i + 1) (Finset.mem_preimage.mp hi), hpreimage]
  by_cases h0 : 0 ∈ s
  · have hset : {a : X | 0 ∈ s → a ∈ t 0} = t 0 := by
      ext a
      simp [h0]
    have hg : ∏ k ∈ s, (if k = 0 then (1 : ℝ≥0∞) else P (t k)) = ∏ k ∈ s.erase 0, P (t k) := by
      rw [← Finset.prod_erase s (f := fun k ↦ if k = 0 then (1 : ℝ≥0∞) else P (t k)) (a := 0)
        (if_pos rfl)]
      exact Finset.prod_congr rfl fun k hk ↦ if_neg (Finset.ne_of_mem_erase hk)
    rw [hset, hg, Finset.mul_prod_erase s (fun i ↦ P (t i)) h0]
  · have hset : {a : X | 0 ∈ s → a ∈ t 0} = Set.univ := by
      ext a
      simp [h0]
    rw [hset, measure_univ, one_mul]
    exact Finset.prod_congr rfl fun k hk ↦ if_neg fun hk0 ↦ h0 (hk0 ▸ hk)

/-- **The first-step decomposition of an event of an infinite product.** -/
theorem infinitePi_eq_lintegral_consSeq {X : Type*} [MeasurableSpace X] (P : Measure X)
    [IsProbabilityMeasure P] {E : Set (ℕ → X)} (hE : MeasurableSet E) :
    Measure.infinitePi (fun _ : ℕ ↦ P) E
      = ∫⁻ a, Measure.infinitePi (fun _ : ℕ ↦ P) {ω | consSeq a ω ∈ E} ∂P := by
  have h1 : (P.prod (Measure.infinitePi fun _ : ℕ ↦ P)).map (fun p ↦ consSeq p.1 p.2) E
      = Measure.infinitePi (fun _ : ℕ ↦ P) E := by
    rw [map_consSeq_infinitePi P]
  rw [Measure.map_apply measurable_consSeq hE, Measure.prod_apply (measurable_consSeq hE)] at h1
  exact h1.symm

end

end Descent.Pangenome.GraphCoalescent.FiniteJumpProcess
