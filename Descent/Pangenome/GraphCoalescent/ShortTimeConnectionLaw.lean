/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Coalescent.Kernel
import Descent.Pangenome.GraphCoalescent.VisibleIntensityClock
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.SpecificLimits.Normed

assert_below Descent.PopGen Descent.Spectral Descent.Blindness Descent.Conditionals
assert_below Descent.Portability Descent.Decision Descent.Program

/-!
# Theorem E, (E2): the short-time law of the connection time

The hidden-clock note (§7, Theorem E) gives the law of the reported connection time `τ_q` near
`t = 0` for a panel of `w ≥ 2` fibers:

  (E2)  `Pr(τ_q ≤ t) = (∏_i c_i) (2n - w)! / (2^{w-2} (2n - 2w + 2)!) t^{w-1} + O(t^w)`.

Its route is analytic and then combinatorial. A report of width `w` needs `w - 1` visible
mergers to connect, so the probability of connecting by time `t` is `H_w(c) t^{w-1}/(w-1)!` plus
`O(t^w)`, where `H_w(c)` sums the rate products of the minimal connecting histories; the
recursion for `H_w(c)` then gives the constant. This module proves the analytic half, for every
finite chain and then for Kingman's coalescent seen through an interface.

## A finite chain

For a matrix `Q` on a finite state space, `exp_smul_apply` writes the entries of `e^{tQ}` as the
series `Σ_k t^k (Q^k)_{xa} / k!`, and `abs_pow_apply_le` bounds `(Q^k)_{xa}` by `S^k` with `S` the
sum of the absolute entries of `Q`. A power series with coefficients bounded by `C S^k` converges
(`summable_series`); when its coefficients vanish below order `m`, less its `m`-th term it is its
tail (`tsum_sub_leading_eq`), which is at most a constant times `|t|^{m+1}` for `|t| ≤ 1`
(`norm_tsum_tail_le`). So the series is its `m`-th term plus `O(t^{m+1})`
(`tsum_sub_leading_isBigO`), and `exp_smul_apply_sub_isBigO` expands an entry of `e^{tQ}` from its
first nonzero power.

A level function lowered by at most one along every nonzero rate forces the vanishing: `Q^k`
cannot join two states whose levels differ by more than `k` (`pow_apply_eq_zero_of_level`). At
exactly that distance `Q^k` agrees with the power of `descentMatrix Q level`, which keeps only
the rates that lower the level by one (`pow_apply_eq_descentMatrix_pow_apply`): the sum over the
minimal histories of their rate products. `targetProbability_sub_isBigO` is the resulting law. If
a state sits `m` levels above a target at the floor level, the target's weight in `e^{tQ}` is the
minimal-history sum times `t^m/m!`, plus `O(t^{m+1})`.

## Kingman's coalescent through an interface

`kingmanMatrix n` is Kingman's generator on the coalescent states of `n` individuals, rate one on
every cover, and applied to a function it is `kingmanGenerator` of `VisibleIntensityClock`
(`kingmanMatrix_mulVec`). The report width `blocks (observed s ξ)` is a level: a cover keeps the
report or merges two of its components (`kingmanMatrix_step`, from `observed_eq_or_covers`). The
descent matrix of Kingman's generator is the indicator of the covers that merge two report
components (`descentMatrix_kingmanMatrix_apply`), so the minimal histories are the chains of
`w - 1` visible covers from the singletons, and `minimalHistoryCount s` counts those that end
connected. `reportConnectedProbability_sub_isBigO` is (E2) with that count as the constant:

  `reportConnectedProbability s t = minimalHistoryCount s t^{w-1}/(w-1)! + O(t^w)`,

with `w = width s`.

## What is narrower than the note

`reportConnectedProbability s t` is the weight of the connected reports in the first row of
`e^{tQ}`, started at the singletons. The note's `Pr(τ_q ≤ t)` is that weight because the connected
reports are closed under covers, but the continuous-time chain as a stochastic process is not
constructed in the corpus, and the identification is not formalized.

The constant is `minimalHistoryCount s`, the note's `H_w(c)` counted over labeled histories. Not
formalized here: the lumping of those histories into the recursion
`H_w(c) = Σ_{i<j} c_i c_j H_{w-1}(c_i + c_j - 1, c_others)` and the closed form
`H_w(c) = (∏_i c_i) g_w(n)`, whose algebra is the subject of `LeadingCoefficient`.

## Empirical status

None. The bodies here are a matrix exponential of a finite matrix, a power series bound and
counts of chains of covers of equivalence relations on a finite set, so no measurement can bear
on them.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Pangenome.GraphCoalescent.ShortTimeConnectionLaw

open Coalescent Asymptotics Topology
open scoped Nat

noncomputable section

/-! ### The entries of a matrix exponential -/

/-- Every entry of a power of a matrix is bounded by that power of the sum of the absolute values
of its entries. -/
theorem abs_pow_apply_le {State : Type*} [Fintype State] [DecidableEq State]
    (Q : Matrix State State ℝ) (k : ℕ) (x a : State) :
    |(Q ^ k) x a| ≤ (∑ y, ∑ z, |Q y z|) ^ k := by
  induction k generalizing x with
  | zero =>
    rw [pow_zero, pow_zero, Matrix.one_apply]
    split_ifs <;> simp
  | succ k ih =>
    have hnonneg : 0 ≤ ∑ y, ∑ z, |Q y z| :=
      Finset.sum_nonneg fun y _ ↦ Finset.sum_nonneg fun z _ ↦ abs_nonneg (Q y z)
    have hrow : ∑ y, |Q x y| ≤ ∑ y, ∑ z, |Q y z| :=
      Finset.single_le_sum (fun y _ ↦ Finset.sum_nonneg fun z _ ↦ abs_nonneg (Q y z))
        (Finset.mem_univ x)
    rw [pow_succ', Matrix.mul_apply, pow_succ']
    calc |∑ y, Q x y * (Q ^ k) y a| ≤ ∑ y, |Q x y * (Q ^ k) y a| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ y, |Q x y| * (∑ y, ∑ z, |Q y z|) ^ k := by
          refine Finset.sum_le_sum fun y _ ↦ ?_
          rw [abs_mul]
          exact mul_le_mul_of_nonneg_left (ih y) (abs_nonneg _)
      _ = (∑ y, |Q x y|) * (∑ y, ∑ z, |Q y z|) ^ k := by rw [Finset.sum_mul]
      _ ≤ (∑ y, ∑ z, |Q y z|) * (∑ y, ∑ z, |Q y z|) ^ k :=
          mul_le_mul_of_nonneg_right hrow (pow_nonneg hnonneg k)

/-- The exponential series of a matrix converges entry by entry. -/
theorem summable_pow_apply {State : Type*} [Fintype State] [DecidableEq State]
    (Q : Matrix State State ℝ) (t : ℝ) (x a : State) :
    Summable fun k : ℕ ↦ t ^ k / k ! * (Q ^ k) x a := by
  refine Summable.of_norm_bounded (Real.summable_pow_div_factorial (|t| * ∑ y, ∑ z, |Q y z|))
    fun k ↦ ?_
  rw [Real.norm_eq_abs, abs_mul, abs_div, abs_pow, Nat.abs_cast, mul_pow]
  calc |t| ^ k / k ! * |(Q ^ k) x a| ≤ |t| ^ k / k ! * (∑ y, ∑ z, |Q y z|) ^ k :=
        mul_le_mul_of_nonneg_left (abs_pow_apply_le Q k x a) (by positivity)
    _ = |t| ^ k * (∑ y, ∑ z, |Q y z|) ^ k / k ! := by ring

/-- **The entries of `e^{tQ}`**: `(e^{tQ})_{xa} = Σ_k t^k (Q^k)_{xa} / k!`. -/
theorem exp_smul_apply {State : Type*} [Fintype State] [DecidableEq State]
    (Q : Matrix State State ℝ) (t : ℝ) (x a : State) :
    NormedSpace.exp ℝ (t • Q) x a = ∑' k : ℕ, t ^ k / k ! * (Q ^ k) x a := by
  have hentry : ∀ y b, HasSum (fun k : ℕ ↦ ((k !⁻¹ : ℝ) • (t • Q) ^ k) y b)
      (∑' k : ℕ, t ^ k / k ! * (Q ^ k) y b) := by
    intro y b
    convert (summable_pow_apply Q t y b).hasSum using 1
    funext k
    show ((k !⁻¹ : ℝ) • (t • Q) ^ k) y b = t ^ k / k ! * (Q ^ k) y b
    rw [smul_pow, Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul, smul_eq_mul]
    ring
  have hmatrix : HasSum (fun k : ℕ ↦ (k !⁻¹ : ℝ) • (t • Q) ^ k)
      (Matrix.of fun y b ↦ ∑' k : ℕ, t ^ k / k ! * (Q ^ k) y b) :=
    Pi.hasSum.mpr fun y ↦ Pi.hasSum.mpr fun b ↦ hentry y b
  have hexp : NormedSpace.exp ℝ (t • Q) = ∑' k : ℕ, (k !⁻¹ : ℝ) • (t • Q) ^ k := by
    rw [NormedSpace.exp_eq_tsum]
  rw [hexp, hmatrix.tsum_eq, Matrix.of_apply]

/-! ### A power series from its first term -/

/-- A power series with coefficients bounded by `C S^k` converges at every `t`. -/
theorem summable_series (c : ℕ → ℝ) {C S : ℝ} (hbound : ∀ k, |c k| ≤ C * S ^ k) (t : ℝ) :
    Summable fun k : ℕ ↦ t ^ k / k ! * c k := by
  refine Summable.of_norm_bounded
    ((Real.summable_pow_div_factorial (|t| * S)).mul_left C) fun k ↦ ?_
  rw [Real.norm_eq_abs, abs_mul, abs_div, abs_pow, Nat.abs_cast]
  calc |t| ^ k / k ! * |c k| ≤ |t| ^ k / k ! * (C * S ^ k) :=
        mul_le_mul_of_nonneg_left (hbound k) (by positivity)
    _ = C * ((|t| * S) ^ k / k !) := by ring

/-- **The series less its first term is its tail**, when the coefficients below order `m`
vanish. -/
theorem tsum_sub_leading_eq (c : ℕ → ℝ) {C S : ℝ} (hbound : ∀ k, |c k| ≤ C * S ^ k) {m : ℕ}
    (hvanish : ∀ k < m, c k = 0) (t : ℝ) :
    (∑' k : ℕ, t ^ k / k ! * c k) - t ^ m / m ! * c m =
      ∑' i : ℕ, t ^ (i + (m + 1)) / (i + (m + 1))! * c (i + (m + 1)) := by
  have hzero : ∑ i ∈ Finset.range m, t ^ i / i ! * c i = 0 :=
    Finset.sum_eq_zero fun i hi ↦ by rw [hvanish i (Finset.mem_range.mp hi), mul_zero]
  have hsplit := (summable_series c hbound t).sum_add_tsum_nat_add (m + 1)
  rw [Finset.sum_range_succ, hzero, zero_add] at hsplit
  rw [← hsplit]
  ring

/-- **The tail is of the next order.** For `|t| ≤ 1` the tail of the series past order `m` is at
most `C |t|^{m+1} Σ_i S^{i+m+1}/(i+m+1)!`. -/
theorem norm_tsum_tail_le (c : ℕ → ℝ) {C S : ℝ} (hbound : ∀ k, |c k| ≤ C * S ^ k) (m : ℕ)
    {t : ℝ} (ht : |t| ≤ 1) :
    ‖∑' i : ℕ, t ^ (i + (m + 1)) / (i + (m + 1))! * c (i + (m + 1))‖ ≤
      C * |t| ^ (m + 1) * ∑' i : ℕ, S ^ (i + (m + 1)) / (i + (m + 1))! := by
  have htail : Summable fun i : ℕ ↦ S ^ (i + (m + 1)) / (i + (m + 1))! :=
    (summable_nat_add_iff (f := fun k : ℕ ↦ S ^ k / k !) (m + 1)).mpr
      (Real.summable_pow_div_factorial S)
  have hnorm : ∀ i : ℕ, ‖t ^ (i + (m + 1)) / (i + (m + 1))! * c (i + (m + 1))‖ ≤
      C * |t| ^ (m + 1) * (S ^ (i + (m + 1)) / (i + (m + 1))!) := by
    intro i
    rw [Real.norm_eq_abs, abs_mul, abs_div, abs_pow, Nat.abs_cast]
    have hpow : |t| ^ (i + (m + 1)) ≤ |t| ^ (m + 1) :=
      pow_le_pow_of_le_one (abs_nonneg t) ht (by omega)
    calc |t| ^ (i + (m + 1)) / (i + (m + 1))! * |c (i + (m + 1))|
        ≤ |t| ^ (m + 1) / (i + (m + 1))! * (C * S ^ (i + (m + 1))) :=
          mul_le_mul (div_le_div_of_nonneg_right hpow (by positivity)) (hbound _)
            (abs_nonneg _) (by positivity)
      _ = C * |t| ^ (m + 1) * (S ^ (i + (m + 1)) / (i + (m + 1))!) := by ring
  exact tsum_of_norm_bounded (htail.hasSum.mul_left (C * |t| ^ (m + 1))) hnorm

/-- **A power series is its first term plus the next order.** If the coefficients are bounded by
`C S^k` and vanish below order `m`, then `Σ_k t^k c_k / k! = t^m c_m / m! + O(t^{m+1})` at `0`. -/
theorem tsum_sub_leading_isBigO (c : ℕ → ℝ) {C S : ℝ} (hbound : ∀ k, |c k| ≤ C * S ^ k) {m : ℕ}
    (hvanish : ∀ k < m, c k = 0) :
    (fun t : ℝ ↦ (∑' k : ℕ, t ^ k / k ! * c k) - t ^ m / m ! * c m) =O[𝓝 0]
      fun t : ℝ ↦ t ^ (m + 1) := by
  refine IsBigO.of_bound (C * ∑' i : ℕ, S ^ (i + (m + 1)) / (i + (m + 1))!) ?_
  filter_upwards [Metric.ball_mem_nhds (0 : ℝ) one_pos] with t ht
  rw [Metric.mem_ball, Real.dist_eq, sub_zero] at ht
  have htail := norm_tsum_tail_le c hbound m ht.le
  rw [← tsum_sub_leading_eq c hbound hvanish t] at htail
  rw [norm_pow, Real.norm_eq_abs t]
  exact htail.trans_eq (by ring)

/-- **An entry of `e^{tQ}` from its first nonzero power.** If `(Q^k)_{xa} = 0` below order `m`,
then `(e^{tQ})_{xa} = t^m (Q^m)_{xa} / m! + O(t^{m+1})` at `0`. -/
theorem exp_smul_apply_sub_isBigO {State : Type*} [Fintype State] [DecidableEq State]
    (Q : Matrix State State ℝ) (x a : State) {m : ℕ} (hvanish : ∀ k < m, (Q ^ k) x a = 0) :
    (fun t : ℝ ↦ NormedSpace.exp ℝ (t • Q) x a - t ^ m / m ! * (Q ^ m) x a) =O[𝓝 0]
      fun t : ℝ ↦ t ^ (m + 1) := by
  have hfun : (fun t : ℝ ↦ NormedSpace.exp ℝ (t • Q) x a - t ^ m / m ! * (Q ^ m) x a) =
      fun t : ℝ ↦ (∑' k : ℕ, t ^ k / k ! * (Q ^ k) x a) - t ^ m / m ! * (Q ^ m) x a :=
    funext fun t ↦ by rw [exp_smul_apply]
  rw [hfun]
  exact tsum_sub_leading_isBigO (fun k ↦ (Q ^ k) x a) (C := 1) (S := ∑ y, ∑ z, |Q y z|)
    (fun k ↦ by rw [one_mul]; exact abs_pow_apply_le Q k x a) hvanish

/-! ### Levels and minimal histories -/

/-- **Rates join nearby levels only.** If every nonzero rate lowers the level by at most one, then
`Q^k` cannot join a state to one more than `k` levels below it. -/
theorem pow_apply_eq_zero_of_level {State : Type*} [Fintype State] [DecidableEq State]
    (Q : Matrix State State ℝ) (level : State → ℕ)
    (hstep : ∀ y z, Q y z ≠ 0 → level y ≤ level z + 1) (k : ℕ) (x a : State)
    (hk : k + level a < level x) : (Q ^ k) x a = 0 := by
  induction k generalizing x with
  | zero =>
    have hxa : x ≠ a := fun hxa ↦ by
      subst hxa
      omega
    rw [pow_zero, Matrix.one_apply, if_neg hxa]
  | succ k ih =>
    rw [pow_succ', Matrix.mul_apply]
    refine Finset.sum_eq_zero fun y _ ↦ ?_
    by_cases hxy : Q x y = 0
    · rw [hxy, zero_mul]
    · rw [ih y (by have := hstep x y hxy; omega), mul_zero]

/-- **The descent matrix**: the rates of `Q` that lower the level by exactly one. Its powers sum
the rate products of the histories that lose one level at every step. -/
def descentMatrix {State : Type*} (Q : Matrix State State ℝ) (level : State → ℕ) :
    Matrix State State ℝ :=
  Matrix.of fun y z ↦ if level z + 1 = level y then Q y z else 0

/-- The entries of the descent matrix. -/
theorem descentMatrix_apply {State : Type*} (Q : Matrix State State ℝ) (level : State → ℕ)
    (y z : State) :
    descentMatrix Q level y z = if level z + 1 = level y then Q y z else 0 :=
  rfl

/-- **At the minimal distance only the minimal histories count.** If every nonzero rate lowers the
level by at most one and `a` lies `k` levels below `x`, then `(Q^k)_{xa}` is the sum over the
histories that lose one level at every step. -/
theorem pow_apply_eq_descentMatrix_pow_apply {State : Type*} [Fintype State] [DecidableEq State]
    (Q : Matrix State State ℝ) (level : State → ℕ)
    (hstep : ∀ y z, Q y z ≠ 0 → level y ≤ level z + 1) (k : ℕ) (x a : State)
    (hk : k + level a = level x) : (Q ^ k) x a = (descentMatrix Q level ^ k) x a := by
  induction k generalizing x with
  | zero => rw [pow_zero, pow_zero]
  | succ k ih =>
    rw [pow_succ', pow_succ', Matrix.mul_apply, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun y _ ↦ ?_
    by_cases hlevel : level y + 1 = level x
    · rw [descentMatrix_apply, if_pos hlevel, ih y (by omega)]
    · rw [descentMatrix_apply, if_neg hlevel, zero_mul]
      by_cases hxy : Q x y = 0
      · rw [hxy, zero_mul]
      · rw [pow_apply_eq_zero_of_level Q level hstep k y a (by have := hstep x y hxy; omega),
          mul_zero]

/-- **The weight of a target at time `t`**: `Σ_{a ∈ target} (e^{tQ})_{xa}`. For a generator whose
target is closed under its rates, this is the probability of having reached the target by
time `t`. -/
def targetProbability {State : Type*} [Fintype State] [DecidableEq State]
    (Q : Matrix State State ℝ) (x : State) (target : Finset State) (t : ℝ) : ℝ :=
  ∑ a ∈ target, NormedSpace.exp ℝ (t • Q) x a

/-- **The short-time law of a level-lowering chain.** If every nonzero rate lowers the level by at
most one, the start `x` sits `m` levels above `floor` and every target state lies at or below
`floor`, then the weight of the target at time `t` is the minimal-history sum into the target
states at the floor, times `t^m/m!`, plus `O(t^{m+1})`. -/
theorem targetProbability_sub_isBigO {State : Type*} [Fintype State] [DecidableEq State]
    (Q : Matrix State State ℝ) (level : State → ℕ)
    (hstep : ∀ y z, Q y z ≠ 0 → level y ≤ level z + 1) (x : State) (target : Finset State)
    {m floor : ℕ} (hx : level x = m + floor) (htarget : ∀ a ∈ target, level a ≤ floor) :
    (fun t : ℝ ↦ targetProbability Q x target t - t ^ m / m ! *
        ∑ a ∈ target.filter (fun a ↦ level a = floor), (descentMatrix Q level ^ m) x a)
      =O[𝓝 0] fun t : ℝ ↦ t ^ (m + 1) := by
  have hleading : ∑ a ∈ target, (Q ^ m) x a =
      ∑ a ∈ target.filter (fun a ↦ level a = floor), (descentMatrix Q level ^ m) x a := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun a ha ↦ ?_
    by_cases hfloor : level a = floor
    · rw [if_pos hfloor, pow_apply_eq_descentMatrix_pow_apply Q level hstep m x a (by omega)]
    · rw [if_neg hfloor,
        pow_apply_eq_zero_of_level Q level hstep m x a (by have := htarget a ha; omega)]
  have hentry : ∀ a ∈ target, (fun t : ℝ ↦
      NormedSpace.exp ℝ (t • Q) x a - t ^ m / m ! * (Q ^ m) x a) =O[𝓝 0]
        fun t : ℝ ↦ t ^ (m + 1) :=
    fun a ha ↦ exp_smul_apply_sub_isBigO Q x a fun k hk ↦
      pow_apply_eq_zero_of_level Q level hstep k x a (by have := htarget a ha; omega)
  have hfun : (fun t : ℝ ↦ targetProbability Q x target t - t ^ m / m ! *
        ∑ a ∈ target.filter (fun a ↦ level a = floor), (descentMatrix Q level ^ m) x a) =
      fun t : ℝ ↦ ∑ a ∈ target, (NormedSpace.exp ℝ (t • Q) x a - t ^ m / m ! * (Q ^ m) x a) := by
    funext t
    rw [targetProbability, Finset.sum_sub_distrib, ← Finset.mul_sum, hleading]
  rw [hfun]
  exact IsBigO.sum hentry

/-! ### Kingman's coalescent through an interface -/

section Kingman

open scoped Classical

/-- **Kingman's generator as a matrix** on the coalescent states of `n` individuals: rate one on
every cover, and minus the number of covers on the diagonal. -/
def kingmanMatrix (n : ℕ) : Matrix (ER n) (ER n) ℝ :=
  Matrix.of fun ξ η ↦
    if Covers ξ η then 1 else if ξ = η then -(Nat.card {ζ : ER n // Covers ξ ζ} : ℝ) else 0

/-- **The matrix is the corpus generator.** Applied to a function of the coalescent state,
`kingmanMatrix n` is `kingmanGenerator` of `VisibleIntensityClock`. -/
theorem kingmanMatrix_mulVec {n : ℕ} (F : ER n → ℝ) (ξ : ER n) :
    (kingmanMatrix n).mulVec F ξ = kingmanGenerator F ξ := by
  have hself : ¬Covers ξ ξ := fun hcovers ↦ by
    have hblocks := hcovers.2
    omega
  have hmem : ξ ∈ Finset.univ.filter (fun η ↦ ¬Covers ξ η) :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, hself⟩
  have hcovers : ∑ η : {η : ER n // Covers ξ η}, F η.1 =
      ∑ η ∈ Finset.univ.filter (fun η ↦ Covers ξ η), F η :=
    (Finset.sum_subtype (Finset.univ.filter fun η ↦ Covers ξ η) (fun η ↦ by simp) F).symm
  rw [kingmanGenerator, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    hcovers, ← Nat.card_eq_fintype_card]
  simp only [Matrix.mulVec, dotProduct, kingmanMatrix, Matrix.of_apply, ite_mul, one_mul,
    zero_mul, neg_mul]
  rw [Finset.sum_ite, Finset.sum_ite_eq, if_pos hmem]
  exact (sub_eq_add_neg _ _).symm

/-- **A cover lowers the report width by at most one**: it keeps the report or merges two of its
components. -/
theorem kingmanMatrix_step {n : ℕ} (s : Fin n → Fin n) (ξ η : ER n)
    (hrate : kingmanMatrix n ξ η ≠ 0) :
    blocks (observed s ξ) ≤ blocks (observed s η) + 1 := by
  by_cases hcovers : Covers ξ η
  · rcases observed_eq_or_covers s hcovers with hequal | hreport
    · rw [hequal]
      exact Nat.le_succ _
    · exact hreport.2.ge
  · by_cases hsame : ξ = η
    · rw [hsame]
      exact Nat.le_succ _
    · refine (hrate ?_).elim
      rw [kingmanMatrix, Matrix.of_apply, if_neg hcovers, if_neg hsame]

/-- **The minimal steps are the visible covers.** The descent matrix of Kingman's generator for
the report width is the indicator of the covers that merge two report components. -/
theorem descentMatrix_kingmanMatrix_apply {n : ℕ} (s : Fin n → Fin n) (ξ η : ER n) :
    descentMatrix (kingmanMatrix n) (fun ζ ↦ blocks (observed s ζ)) ξ η =
      if Covers ξ η ∧ blocks (observed s η) + 1 = blocks (observed s ξ) then 1 else 0 := by
  rw [descentMatrix_apply, kingmanMatrix, Matrix.of_apply]
  by_cases hlevel : blocks (observed s η) + 1 = blocks (observed s ξ)
  · by_cases hcovers : Covers ξ η
    · rw [if_pos hlevel, if_pos hcovers, if_pos (And.intro hcovers hlevel)]
    · have hsame : ξ ≠ η := fun hsame ↦ by
        rw [hsame] at hlevel
        omega
      have hnot : ¬(Covers ξ η ∧ blocks (observed s η) + 1 = blocks (observed s ξ)) :=
        fun hboth ↦ hcovers hboth.1
      rw [if_pos hlevel, if_neg hcovers, if_neg hsame, if_neg hnot]
  · have hnot : ¬(Covers ξ η ∧ blocks (observed s η) + 1 = blocks (observed s ξ)) :=
      fun hboth ↦ hlevel hboth.2
    rw [if_neg hlevel, if_neg hnot]

/-- The coalescent states whose report is connected: at most one report component. -/
def connectedStates {n : ℕ} (s : Fin n → Fin n) : Finset (ER n) :=
  Finset.univ.filter fun η ↦ blocks (observed s η) ≤ 1

/-- A coalescent state is connected when its report has at most one component. -/
theorem mem_connectedStates {n : ℕ} (s : Fin n → Fin n) (η : ER n) :
    η ∈ connectedStates s ↔ blocks (observed s η) ≤ 1 := by
  rw [connectedStates, Finset.mem_filter]
  exact and_iff_right (Finset.mem_univ η)

/-- **The probability that the report is connected at time `t`**, started at the singletons: the
weight of the connected reports in the first row of `e^{tQ}` for Kingman's generator `Q`. -/
def reportConnectedProbability {n : ℕ} (s : Fin n → Fin n) (t : ℝ) : ℝ :=
  targetProbability (kingmanMatrix n) ⊥ (connectedStates s) t

/-- **The minimal connecting histories**: the chains of `w - 1` visible covers from the singletons
to a connected report, `w` the width of the interface. -/
def minimalHistoryCount {n : ℕ} (s : Fin n → Fin n) : ℝ :=
  ∑ η ∈ (connectedStates s).filter (fun η ↦ blocks (observed s η) = 1),
    (descentMatrix (kingmanMatrix n) (fun ζ ↦ blocks (observed s ζ)) ^ (Linkage.width s - 1)) ⊥ η

/-- **Theorem E, (E2), analytic part.** Started at the singletons, the probability that the
report of an interface of width `w` is connected at time `t` is the number of minimal connecting
histories times `t^{w-1}/(w-1)!`, plus `O(t^w)` as `t → 0`. -/
theorem reportConnectedProbability_sub_isBigO {n : ℕ} (s : Fin n → Fin n)
    (hwidth : 1 ≤ Linkage.width s) :
    (fun t : ℝ ↦ reportConnectedProbability s t -
        t ^ (Linkage.width s - 1) / (Linkage.width s - 1)! * minimalHistoryCount s) =O[𝓝 0]
      fun t : ℝ ↦ t ^ Linkage.width s := by
  have hlevel : blocks (observed s ⊥) = Linkage.width s - 1 + 1 := by
    rw [observed_bot, blocks_graphKer, Nat.sub_add_cancel hwidth]
  have h := targetProbability_sub_isBigO (kingmanMatrix n) (fun ζ ↦ blocks (observed s ζ))
    (kingmanMatrix_step s) ⊥ (connectedStates s) hlevel
    fun η hη ↦ (mem_connectedStates s η).mp hη
  rw [Nat.sub_add_cancel hwidth] at h
  exact h

end Kingman

end

end Descent.Pangenome.GraphCoalescent.ShortTimeConnectionLaw
