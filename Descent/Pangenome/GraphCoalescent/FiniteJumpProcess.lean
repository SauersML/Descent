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

theorem consSeq_succ_shift {X : Type*} (a : X) (ω : ℕ → X) (k : ℕ) :
    consSeq a ω (k + 1) = consSeq (ω 0) (fun j ↦ ω (j + 1)) k := by
  cases k <;> rfl

/-! ### The path measure of the jump process -/

section Law

variable {S : Type*} [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S]

/-- **The randomness of one step**: for every state `x`, an independent target drawn from
`kernel x` and an independent holding time of rate `rate x`. -/
def stepMeasure (rate : S → ℝ) (kernel : S → PMF S) : Measure (S → S × ℝ) :=
  Measure.pi fun x ↦ (kernel x).toMeasure.prod (Coalescent.holdMeasure (rate x))

theorem stepMeasure_isProbabilityMeasure {rate : S → ℝ} (hrate : ∀ x, 0 < rate x)
    (kernel : S → PMF S) : IsProbabilityMeasure (stepMeasure rate kernel) := by
  haveI : ∀ x, IsProbabilityMeasure (Coalescent.holdMeasure (rate x)) := fun x ↦
    Coalescent.holdMeasure_isProbabilityMeasure (hrate x)
  unfold stepMeasure
  infer_instance

/-- The draw made for the state `x` at one step is a target from `kernel x` with an independent
holding time of rate `rate x`. -/
theorem stepMeasure_map_eval {rate : S → ℝ} (hrate : ∀ x, 0 < rate x) (kernel : S → PMF S)
    (x : S) :
    (stepMeasure rate kernel).map (fun a : S → S × ℝ ↦ a x)
      = (kernel x).toMeasure.prod (Coalescent.holdMeasure (rate x)) := by
  haveI : ∀ y, IsProbabilityMeasure (Coalescent.holdMeasure (rate y)) := fun y ↦
    Coalescent.holdMeasure_isProbabilityMeasure (hrate y)
  exact (measurePreserving_eval
    (fun y ↦ (kernel y).toMeasure.prod (Coalescent.holdMeasure (rate y))) x).map_eq

theorem sum_kernel (kernel : S → PMF S) (x : S) : ∑ z, kernel x z = 1 := by
  rw [← tsum_fintype]
  exact PMF.tsum_coe (kernel x)

/-- Integrating a function of the draw made for `x` sums over the target and integrates over the
holding time. -/
theorem lintegral_stepMeasure_eval {rate : S → ℝ} (hrate : ∀ x, 0 < rate x)
    (kernel : S → PMF S) (x : S) {F : S × ℝ → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ a, F (a x) ∂stepMeasure rate kernel
      = ∑ z, kernel x z * ∫⁻ h, F (z, h) ∂Coalescent.holdMeasure (rate x) := by
  haveI := Coalescent.holdMeasure_isProbabilityMeasure (hrate x)
  rw [← lintegral_map hF (measurable_pi_apply x), stepMeasure_map_eval hrate kernel x,
    lintegral_prod _ hF.aemeasurable, lintegral_fintype (μ := (kernel x).toMeasure)]
  refine Finset.sum_congr rfl fun z _ ↦ ?_
  rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton z), mul_comm]

/-- **The path measure**: an independent step at every time `k`. -/
def pathMeasure (rate : S → ℝ) (hrate : ∀ x, 0 < rate x) (kernel : S → PMF S) :
    Measure (ℕ → S → S × ℝ) :=
  haveI := stepMeasure_isProbabilityMeasure hrate kernel
  Measure.infinitePi fun _ : ℕ ↦ stepMeasure rate kernel

theorem pathMeasure_isProbabilityMeasure {rate : S → ℝ} (hrate : ∀ x, 0 < rate x)
    (kernel : S → PMF S) : IsProbabilityMeasure (pathMeasure rate hrate kernel) := by
  haveI := stepMeasure_isProbabilityMeasure hrate kernel
  unfold pathMeasure
  infer_instance

/-- **The state after `k` jumps from `x`**: each jump reads the target drawn at that step for the
current state. -/
def jumpState : (ℕ → S → S × ℝ) → S → ℕ → S
  | _, x, 0 => x
  | ω, x, k + 1 => jumpState (fun j ↦ ω (j + 1)) (ω 0 x).1 k

/-- **The sequence of sojourns from `x`**: the state after `k` jumps with its holding time. -/
def jumpHoldSeq (ω : ℕ → S → S × ℝ) (x : S) (k : ℕ) : S × ℝ :=
  (jumpState ω x k, (ω k (jumpState ω x k)).2)

/-- After the first step the sojourns from `x` are the sojourns of the remaining steps from the
first target, so following `m + 1` sojourns is the first-step recursion. -/
theorem fuelState_jumpHoldSeq_consSeq (m : ℕ) (a : S → S × ℝ) (ω : ℕ → S → S × ℝ) (x : S)
    (t : ℝ) :
    fuelState (m + 1) (jumpHoldSeq (consSeq a ω) x) t
      = if t < (a x).2 then some x
        else fuelState m (jumpHoldSeq ω (a x).1) (t - (a x).2) := rfl

theorem measurable_jumpState (x : S) (k : ℕ) :
    Measurable fun ω : ℕ → S → S × ℝ ↦ jumpState ω x k := by
  induction k generalizing x with
  | zero => exact measurable_const
  | succ k ih =>
    have hjoint : Measurable fun p : S × (ℕ → S → S × ℝ) ↦ jumpState p.2 p.1 k :=
      measurable_from_prod_countable_right fun z ↦ ih z
    have hpair : Measurable fun ω : ℕ → S → S × ℝ ↦ ((ω 0 x).1, fun j ↦ ω (j + 1)) := by
      fun_prop
    have h := hjoint.comp hpair
    exact h

theorem measurable_jumpHoldSeq (x : S) :
    Measurable fun ω : ℕ → S → S × ℝ ↦ jumpHoldSeq ω x := by
  refine measurable_pi_lambda _ fun k ↦ ?_
  have hhold : Measurable fun p : S × (ℕ → S → S × ℝ) ↦ (p.2 k p.1).2 :=
    measurable_from_prod_countable_right fun z ↦ by
      show Measurable fun ω : ℕ → S → S × ℝ ↦ (ω k z).2
      fun_prop
  have hpair : Measurable fun ω : ℕ → S → S × ℝ ↦ (jumpState ω x k, ω) :=
    (measurable_jumpState x k).prodMk measurable_id
  have h := (measurable_jumpState x k).prodMk (hhold.comp hpair)
  exact h

theorem measurableSet_fuelState (m : ℕ) (o : Option S) :
    MeasurableSet {p : (ℕ → S × ℝ) × ℝ | fuelState m p.1 p.2 = o} := by
  induction m generalizing o with
  | zero =>
    have hset : {p : (ℕ → S × ℝ) × ℝ | fuelState 0 p.1 p.2 = o} = {_p | none = o} := rfl
    rw [hset]
    exact MeasurableSet.const _
  | succ m ih =>
    have hlt : MeasurableSet {p : (ℕ → S × ℝ) × ℝ | p.2 < (p.1 0).2} :=
      measurableSet_lt (by fun_prop) (by fun_prop)
    have hstate : MeasurableSet {p : (ℕ → S × ℝ) × ℝ | some (p.1 0).1 = o} := by
      have hm : Measurable fun p : (ℕ → S × ℝ) × ℝ ↦ (p.1 0).1 := by fun_prop
      exact hm (Set.toFinite {x : S | some x = o}).measurableSet
    have hshift : Measurable fun p : (ℕ → S × ℝ) × ℝ ↦
        ((fun k ↦ p.1 (k + 1)), p.2 - (p.1 0).2) := by fun_prop
    have hset : {p : (ℕ → S × ℝ) × ℝ | fuelState (m + 1) p.1 p.2 = o}
        = ({p | p.2 < (p.1 0).2} ∩ {p | some (p.1 0).1 = o})
          ∪ ({p | p.2 < (p.1 0).2}ᶜ ∩ (fun p : (ℕ → S × ℝ) × ℝ ↦
            ((fun k ↦ p.1 (k + 1)), p.2 - (p.1 0).2)) ⁻¹' {q | fuelState m q.1 q.2 = o}) := by
      ext p
      by_cases h : p.2 < (p.1 0).2 <;> simp [fuelState_succ, h]
    rw [hset]
    exact (hlt.inter hstate).union (hlt.compl.inter (hshift (ih o)))

theorem measurableSet_fuelEvent (m : ℕ) (x : S) (t : ℝ) (o : Option S) :
    MeasurableSet {ω : ℕ → S → S × ℝ | fuelState m (jumpHoldSeq ω x) t = o} := by
  have hm : Measurable fun ω : ℕ → S → S × ℝ ↦ (jumpHoldSeq ω x, t) :=
    (measurable_jumpHoldSeq x).prodMk measurable_const
  exact hm (measurableSet_fuelState m o)

/-- **The probability that the chain from `x`, following at most `m` sojourns, is at `o` at time
`t`.** -/
def fuelProb (rate : S → ℝ) (hrate : ∀ x, 0 < rate x) (kernel : S → PMF S) (m : ℕ) (x : S)
    (t : ℝ) (o : Option S) : ℝ≥0∞ :=
  pathMeasure rate hrate kernel {ω | fuelState m (jumpHoldSeq ω x) t = o}

theorem measurable_fuelProb_sub (rate : S → ℝ) (hrate : ∀ x, 0 < rate x) (kernel : S → PMF S)
    (m : ℕ) (z : S) (t : ℝ) (o : Option S) :
    Measurable fun h : ℝ ↦ fuelProb rate hrate kernel m z (t - h) o := by
  haveI := pathMeasure_isProbabilityMeasure hrate kernel
  have h1 := (measurable_jumpHoldSeq (S := S) z).comp (measurable_snd (α := ℝ))
  have h2 : Measurable fun q : ℝ × (ℕ → S → S × ℝ) ↦ t - q.1 := by fun_prop
  have hm := h1.prodMk h2
  exact measurable_measure_prodMk_left (ν := pathMeasure rate hrate kernel)
    (hm (measurableSet_fuelState m o))

/-- The value of the first-step decomposition at a jump to `p.1` after the holding time `p.2`. -/
def firstStepValue (rate : S → ℝ) (hrate : ∀ x, 0 < rate x) (kernel : S → PMF S) (m : ℕ)
    (x : S) (t : ℝ) (o : Option S) (p : S × ℝ) : ℝ≥0∞ :=
  if t < p.2 then (if some x = o then 1 else 0) else fuelProb rate hrate kernel m p.1 (t - p.2) o

theorem measurable_firstStepValue (rate : S → ℝ) (hrate : ∀ x, 0 < rate x)
    (kernel : S → PMF S) (m : ℕ) (x : S) (t : ℝ) (o : Option S) :
    Measurable (firstStepValue rate hrate kernel m x t o) := by
  refine measurable_from_prod_countable_right fun z ↦ ?_
  show Measurable fun h : ℝ ↦
    if t < h then (if some x = o then (1 : ℝ≥0∞) else 0)
    else fuelProb rate hrate kernel m z (t - h) o
  exact Measurable.ite measurableSet_Ioi measurable_const
    (measurable_fuelProb_sub rate hrate kernel m z t o)

theorem pathMeasure_consSeq_fuelEvent (rate : S → ℝ) (hrate : ∀ x, 0 < rate x)
    (kernel : S → PMF S) (m : ℕ) (x : S) (t : ℝ) (o : Option S) (a : S → S × ℝ) :
    pathMeasure rate hrate kernel
        {ω | consSeq a ω ∈ {ω' : ℕ → S → S × ℝ | fuelState (m + 1) (jumpHoldSeq ω' x) t = o}}
      = firstStepValue rate hrate kernel m x t o (a x) := by
  haveI := pathMeasure_isProbabilityMeasure hrate kernel
  simp only [Set.mem_setOf_eq, fuelState_jumpHoldSeq_consSeq, firstStepValue]
  by_cases ha : t < (a x).2
  · by_cases hx : some x = o
    · simp [ha, hx]
    · simp [ha, hx]
  · simp only [ha, ↓reduceIte] <;> rfl

/-- **The first-step decomposition.** Following `m + 1` sojourns from `x`, the chain is at `o` at
time `t` either because the first holding time exceeds `t` and `o = some x`, or because it jumps
to `z` at a time `h ≤ t` and, following `m` sojourns from `z`, is at `o` at time `t - h`. -/
theorem fuelProb_succ (rate : S → ℝ) (hrate : ∀ x, 0 < rate x) (kernel : S → PMF S) (m : ℕ)
    (x : S) (t : ℝ) (o : Option S) :
    fuelProb rate hrate kernel (m + 1) x t o
      = (if some x = o then Coalescent.holdMeasure (rate x) (Set.Ioi t) else 0)
        + ∑ z, kernel x z * ∫⁻ h in Set.Iic t, fuelProb rate hrate kernel m z (t - h) o
            ∂Coalescent.holdMeasure (rate x) := by
  haveI := stepMeasure_isProbabilityMeasure hrate kernel
  have hsplit : fuelProb rate hrate kernel (m + 1) x t o
      = ∫⁻ a, firstStepValue rate hrate kernel m x t o (a x) ∂stepMeasure rate kernel := by
    rw [fuelProb, pathMeasure,
      infinitePi_eq_lintegral_consSeq _ (measurableSet_fuelEvent (m + 1) x t o)]
    exact lintegral_congr fun a ↦ pathMeasure_consSeq_fuelEvent rate hrate kernel m x t o a
  have hvalue : ∀ z, ∫⁻ h, firstStepValue rate hrate kernel m x t o (z, h)
        ∂Coalescent.holdMeasure (rate x)
      = (if some x = o then Coalescent.holdMeasure (rate x) (Set.Ioi t) else 0)
        + ∫⁻ h in Set.Iic t, fuelProb rate hrate kernel m z (t - h) o
            ∂Coalescent.holdMeasure (rate x) := by
    intro z
    have hIoi : ∫⁻ h in Set.Ioi t, firstStepValue rate hrate kernel m x t o (z, h)
          ∂Coalescent.holdMeasure (rate x)
        = ∫⁻ _ in Set.Ioi t, (if some x = o then (1 : ℝ≥0∞) else 0)
          ∂Coalescent.holdMeasure (rate x) :=
      setLIntegral_congr_fun measurableSet_Ioi fun h hh ↦ if_pos hh
    have hIic : ∫⁻ h in Set.Iic t, firstStepValue rate hrate kernel m x t o (z, h)
          ∂Coalescent.holdMeasure (rate x)
        = ∫⁻ h in Set.Iic t, fuelProb rate hrate kernel m z (t - h) o
          ∂Coalescent.holdMeasure (rate x) :=
      setLIntegral_congr_fun measurableSet_Iic fun h hh ↦ if_neg (not_lt.mpr hh)
    rw [← lintegral_add_compl _ (measurableSet_Ioi (a := t)), Set.compl_Ioi, hIoi, hIic,
      setLIntegral_const]
    split_ifs <;> simp
  rw [hsplit, lintegral_stepMeasure_eval hrate kernel x
    (measurable_firstStepValue rate hrate kernel m x t o)]
  simp only [hvalue, mul_add, Finset.sum_add_distrib]
  rw [← Finset.sum_mul, sum_kernel, one_mul]

/-- **The path measure is the jump chain with independent exponential holding times.** From `x`,
the probability that the first `m` jumps go to `states 0, …, states (m - 1)` and the holding times
before them lie in `sets 0, …, sets (m - 1)` is `∏_k kernel(s_k, states k) Exp(rate s_k)(sets k)`,
with `s_0 = x` and `s_{k+1} = states k`. -/
theorem pathMeasure_jumpHold_cylinder (rate : S → ℝ) (hrate : ∀ x, 0 < rate x)
    (kernel : S → PMF S) (m : ℕ) :
    ∀ (x : S) (states : ℕ → S) (sets : ℕ → Set ℝ), (∀ k, MeasurableSet (sets k)) →
      pathMeasure rate hrate kernel {ω | ∀ k < m, jumpState ω x (k + 1) = states k ∧
          (jumpHoldSeq ω x k).2 ∈ sets k}
        = ∏ k ∈ Finset.range m, kernel (consSeq x states k) (states k)
            * Coalescent.holdMeasure (rate (consSeq x states k)) (sets k) := by
  haveI := pathMeasure_isProbabilityMeasure hrate kernel
  haveI := stepMeasure_isProbabilityMeasure hrate kernel
  induction m with
  | zero =>
    intro x states sets _
    have hset : {ω : ℕ → S → S × ℝ | ∀ k < 0, jumpState ω x (k + 1) = states k ∧
        (jumpHoldSeq ω x k).2 ∈ sets k} = Set.univ := by
      ext ω
      simp
    rw [hset, measure_univ, Finset.range_zero, Finset.prod_empty]
  | succ m ih =>
    intro x states sets hsets
    have hE : MeasurableSet {ω : ℕ → S → S × ℝ | ∀ k < m + 1,
        jumpState ω x (k + 1) = states k ∧ (jumpHoldSeq ω x k).2 ∈ sets k} := by
      simp only [Set.setOf_forall, Set.setOf_and]
      refine MeasurableSet.iInter fun k ↦ MeasurableSet.iInter fun _ ↦ ?_
      have hjump := measurable_jumpState (S := S) x (k + 1)
      have hhold := measurable_snd.comp ((measurable_pi_apply k).comp (measurable_jumpHoldSeq x))
      exact (hjump (measurableSet_singleton (states k))).inter (hhold (hsets k))
    have hA : MeasurableSet {b : S → S × ℝ | (b x).1 = states 0 ∧ (b x).2 ∈ sets 0} := by
      have hm : Measurable fun b : S → S × ℝ ↦ b x := measurable_pi_apply x
      exact hm ((measurableSet_singleton (states 0)).prod (hsets 0))
    have hstep : stepMeasure rate kernel {b : S → S × ℝ | (b x).1 = states 0 ∧ (b x).2 ∈ sets 0}
        = kernel x (states 0) * Coalescent.holdMeasure (rate x) (sets 0) := by
      have hset : {b : S → S × ℝ | (b x).1 = states 0 ∧ (b x).2 ∈ sets 0}
          = (fun b : S → S × ℝ ↦ b x) ⁻¹' ({states 0} ×ˢ sets 0) := by
        ext b
        simp [Set.mem_prod]
      rw [hset, ← Measure.map_apply (measurable_pi_apply x)
          ((measurableSet_singleton (states 0)).prod (hsets 0)),
        stepMeasure_map_eval hrate kernel x, Measure.prod_prod,
        PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)]
    have hpoint : ∀ a : S → S × ℝ, pathMeasure rate hrate kernel {ω' | consSeq a ω' ∈
          {ω : ℕ → S → S × ℝ | ∀ k < m + 1, jumpState ω x (k + 1) = states k ∧
            (jumpHoldSeq ω x k).2 ∈ sets k}}
        = {b : S → S × ℝ | (b x).1 = states 0 ∧ (b x).2 ∈ sets 0}.indicator
            (fun _ ↦ pathMeasure rate hrate kernel {ω | ∀ k < m,
              jumpState ω (states 0) (k + 1) = states (k + 1) ∧
                (jumpHoldSeq ω (states 0) k).2 ∈ sets (k + 1)}) a := by
      intro a
      by_cases ha : (a x).1 = states 0 ∧ (a x).2 ∈ sets 0
      · rw [Set.indicator_of_mem ha]
        obtain ⟨ha1, ha2⟩ := ha
        congr 1
        ext ω'
        simp only [Set.mem_setOf_eq]
        rw [← ha1]
        constructor
        · intro h k hk
          exact h (k + 1) (by omega)
        · intro h k hk
          cases k with
          | zero => exact ⟨ha1, ha2⟩
          | succ k => exact h k (by omega)
      · rw [Set.indicator_of_notMem ha]
        have hempty : {ω' : ℕ → S → S × ℝ | consSeq a ω' ∈
            {ω : ℕ → S → S × ℝ | ∀ k < m + 1, jumpState ω x (k + 1) = states k ∧
              (jumpHoldSeq ω x k).2 ∈ sets k}} = ∅ := by
          ext ω'
          simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
          intro h
          exact ha (h 0 (by omega))
        rw [hempty, measure_empty]
    have hsplit : pathMeasure rate hrate kernel {ω | ∀ k < m + 1, jumpState ω x (k + 1) = states k ∧
          (jumpHoldSeq ω x k).2 ∈ sets k}
        = ∫⁻ a, pathMeasure rate hrate kernel {ω' | consSeq a ω' ∈
          {ω : ℕ → S → S × ℝ | ∀ k < m + 1, jumpState ω x (k + 1) = states k ∧
            (jumpHoldSeq ω x k).2 ∈ sets k}} ∂stepMeasure rate kernel := by
      rw [pathMeasure, infinitePi_eq_lintegral_consSeq _ hE]
    rw [hsplit, lintegral_congr hpoint, lintegral_indicator_const hA, hstep,
      ih (states 0) (fun k ↦ states (k + 1)) (fun k ↦ sets (k + 1)) (fun k ↦ hsets (k + 1)),
      Finset.prod_range_succ']
    refine congrArg₂ (· * ·) (Finset.prod_congr rfl fun k _ ↦ ?_) rfl
    rw [consSeq_succ_shift]

end Law

end

end Descent.Pangenome.GraphCoalescent.FiniteJumpProcess
