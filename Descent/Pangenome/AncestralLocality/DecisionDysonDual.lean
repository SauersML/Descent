/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Pangenome.AncestralLocality.DecisionDualMoments
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Module

assert_below Descent.PopGen Descent.Spectral Descent.Blindness Descent.Conditionals
assert_below Descent.Portability Descent.Decision Descent.Program

/-!
# The Dyson series of the ancestral decision circuit

Theorem 6 of the research note "Ancestral locality" reads the forward population on a finite
state space `H` backwards: an observation `f : (Fin n → H) → ℝ` of `n` sampled genomes coalesces
at rate `c` per pair and branches at rate `r_e` per argument and event, and the sampling duality
(7.5) is `E_p[H_f(P_t)] = E_f[H_{f_t}(p)]`. Branching raises the arity, so no finite-dimensional
exponential carries the backward circuit. This module constructs its Dyson series instead, one
number of branchings at a time, with explicit sup-norm majorants.

The killed coalescence semigroup. On observations of arity `m` the arity-preserving part of the
backward generator is the coalescence gain `P` of `DecisionDualMoments` minus the exit rate
`λ_m = c d_m + m R` (`dualExitRate`), and `killedSemigroup c r m t = e^{-λ_m t} e^{tP}`. It obeys
the semigroup law (`killedSemigroup_zero`, `killedSemigroup_add`), moves an observation along
`P - λ_m` (`hasDerivAt_killedSemigroup_apply`), and kills at the branching rate,
`‖e^{-λ_m t} e^{tP} f‖ ≤ e^{-m R t} ‖f‖` for `t ≥ 0` (`norm_killedSemigroup_apply_le`), because
`e^{tP}` grows by at most `e^{c d_m t}` (`norm_gainSemigroup_le`).

The Dyson components. `dysonTerm c r T f k t`, an observation of arity `n + k`, is the part of the
backward circuit started at `f` that has branched `k` times by time `t`: the killed semigroup at
`k = 0`, and `∫_0^t e^{(t-s)(P - λ)} G u_k(s) ds` after a branching, with the branching gain `G`
(`branchingGain`). The components are continuous (`continuous_dysonTerm`) and solve the lower
triangular system `u_0' = (P - λ_n) u_0`, `u_{k+1}' = (P - λ_{n+k+1}) u_{k+1} + G u_k`
(`hasDerivAt_dysonTerm_zero`, `hasDerivAt_dysonTerm_succ`) from `u_0(0) = f` and
`u_{k+1}(0) = 0` (`dysonTerm_zero_zero`, `dysonTerm_succ_zero`). Read through a sampling
observable, the right-hand side is the backward generator of `SamplingDuality`
(`samplingObservable_generator`).

The Yule weights. `yuleWeight n R k t` solves the equations of a pure birth process from `n`
lineages at rate `R` per lineage after `k` births, through the same recursion:
`y_0 = e^{-nRt}` and `y_{k+1}(t) = ∫_0^t e^{-(n+k+1)R(t-s)} (n+k) R y_k(s) ds`. They are nonnegative
(`yuleWeight_nonneg`), solve the birth equations (`hasDerivAt_yuleWeight`), and are the majorants
of the components, `‖u_k(t)‖ ≤ y_k(t) ‖f‖` (`norm_dysonTerm_le`). Since births occur at a rate
linear in the arity, their cubic moment is bounded:
`∑_{k ≤ K} (n+k+1)(n+k+2)(n+k+3) y_k(t) ≤ (n+1)(n+2)(n+3) e^{3Rt}` for `t ≥ 0`
(`sum_yuleMoment_mul_le`), so the components are summable against every weight of degree at most
three, uniformly on bounded times.

Scope. The components are constructed and bounded one at a time. The identity
`E_p[H_f(P_t)] = ∑_k H_{u_k(t)}(p)` of (7.5), and the forward population it refers to, are not in
this module, and the components are not shown to be positive.

## Empirical status

None. The bodies here are linear differential equations on finite-dimensional spaces of
observations, their integrals and scalar comparisons, so no measurement can bear on them.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Pangenome.AncestralLocality.DecisionDysonDual

open Finset Filter Topology

noncomputable section

/-! ## Primitives -/

/-- **The fundamental theorem of calculus** from time zero, for a continuous integrand. -/
theorem hasDerivAt_integral_from_zero {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [CompleteSpace F] {g : ℝ → F} (hg : Continuous g) (t : ℝ) :
    HasDerivAt (fun u ↦ ∫ s in (0 : ℝ)..u, g s) (g t) t :=
  intervalIntegral.integral_hasDerivAt_right (hg.intervalIntegrable _ _)
    hg.aestronglyMeasurable.stronglyMeasurableAtFilter hg.continuousAt

/-- The integral from time zero of a continuous integrand is continuous in its endpoint. -/
theorem continuous_integral_from_zero {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [CompleteSpace F] {g : ℝ → F} (hg : Continuous g) :
    Continuous fun u ↦ ∫ s in (0 : ℝ)..u, g s :=
  continuous_iff_continuousAt.mpr fun t ↦ (hasDerivAt_integral_from_zero hg t).continuousAt

/-- **The derivative of an exponential decay**, `d/dt e^{-at} = -a e^{-at}`. -/
theorem hasDerivAt_exp_neg_mul (a t : ℝ) :
    HasDerivAt (fun u ↦ Real.exp (-(a * u))) (-a * Real.exp (-(a * t))) t := by
  have h := ((hasDerivAt_id' (x := t)).const_mul a).neg.exp
  convert h using 1
  simp only [Pi.neg_apply, mul_one]
  ring

/-! ## Yule weights -/

section Yule

/-- **The Yule weights** `y_0(t) = e^{-nRt}` and
`y_{k+1}(t) = ∫_0^t e^{-(n+k+1)R(t-s)} (n+k) R y_k(s) ds`: the equations of a pure birth process
from `n` lineages at rate `R` per lineage, after `k` births. -/
def yuleWeight (n : ℕ) (R : ℝ) : ℕ → ℝ → ℝ
  | 0, t => Real.exp (-((n : ℝ) * R * t))
  | k + 1, t => ∫ s in (0 : ℝ)..t,
      Real.exp (-(((n : ℝ) + k + 1) * R * (t - s))) * (((n : ℝ) + k) * R * yuleWeight n R k s)

variable {n : ℕ} {R : ℝ}

/-- The Yule weight without births. -/
theorem yuleWeight_zero (t : ℝ) : yuleWeight n R 0 t = Real.exp (-((n : ℝ) * R * t)) :=
  rfl

/-- The Yule weight after a birth. -/
theorem yuleWeight_succ (k : ℕ) (t : ℝ) :
    yuleWeight n R (k + 1) t = ∫ s in (0 : ℝ)..t,
      Real.exp (-(((n : ℝ) + k + 1) * R * (t - s))) * (((n : ℝ) + k) * R * yuleWeight n R k s) :=
  rfl

/-- At time zero the weight of no birth is one. -/
theorem yuleWeight_zero_zero : yuleWeight n R 0 0 = 1 := by
  rw [yuleWeight_zero, mul_zero, neg_zero, Real.exp_zero]

/-- At time zero every weight after a birth vanishes. -/
theorem yuleWeight_succ_zero (k : ℕ) : yuleWeight n R (k + 1) 0 = 0 :=
  intervalIntegral.integral_same

/-- **The factored form** of a Yule weight after a birth. -/
theorem yuleWeight_succ_eq_mul (k : ℕ) (t : ℝ) :
    yuleWeight n R (k + 1) t = Real.exp (-(((n : ℝ) + k + 1) * R * t)) *
      ∫ s in (0 : ℝ)..t,
        Real.exp (((n : ℝ) + k + 1) * R * s) * (((n : ℝ) + k) * R * yuleWeight n R k s) := by
  rw [yuleWeight_succ, ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr fun s _ ↦ ?_
  show Real.exp (-(((n : ℝ) + k + 1) * R * (t - s))) * _ =
    Real.exp (-(((n : ℝ) + k + 1) * R * t)) * _
  have hsplit : Real.exp (-(((n : ℝ) + k + 1) * R * (t - s))) =
      Real.exp (-(((n : ℝ) + k + 1) * R * t)) * Real.exp (((n : ℝ) + k + 1) * R * s) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hsplit, mul_assoc]

/-- The Yule weights are continuous in time. -/
theorem continuous_yuleWeight (n : ℕ) (R : ℝ) (k : ℕ) : Continuous (yuleWeight n R k) := by
  induction k with
  | zero =>
    show Continuous fun t ↦ Real.exp (-((n : ℝ) * R * t))
    fun_prop
  | succ k ih =>
    have hint : Continuous fun s ↦
        Real.exp (((n : ℝ) + k + 1) * R * s) * (((n : ℝ) + k) * R * yuleWeight n R k s) := by
      fun_prop
    rw [funext (yuleWeight_succ_eq_mul (n := n) (R := R) k)]
    exact (by fun_prop : Continuous fun t : ℝ ↦ Real.exp (-(((n : ℝ) + k + 1) * R * t))).mul
      (continuous_integral_from_zero hint)

/-- **The birth equation without births**, `y_0' = -nR y_0`. -/
theorem hasDerivAt_yuleWeight_zero (t : ℝ) :
    HasDerivAt (yuleWeight n R 0) (-((n : ℝ) * R) * yuleWeight n R 0 t) t :=
  hasDerivAt_exp_neg_mul ((n : ℝ) * R) t

/-- **The birth equation after a birth**, `y_{k+1}' = -(n+k+1)R y_{k+1} + (n+k)R y_k`. -/
theorem hasDerivAt_yuleWeight_succ (k : ℕ) (t : ℝ) :
    HasDerivAt (yuleWeight n R (k + 1))
      (-(((n : ℝ) + k + 1) * R) * yuleWeight n R (k + 1) t +
        ((n : ℝ) + k) * R * yuleWeight n R k t) t := by
  have hint : Continuous fun s ↦
      Real.exp (((n : ℝ) + k + 1) * R * s) * (((n : ℝ) + k) * R * yuleWeight n R k s) := by
    have := continuous_yuleWeight n R k
    fun_prop
  have hprod := (hasDerivAt_exp_neg_mul (((n : ℝ) + k + 1) * R) t).mul
    (hasDerivAt_integral_from_zero hint t)
  have hone : Real.exp (-(((n : ℝ) + k + 1) * R * t)) *
      Real.exp (((n : ℝ) + k + 1) * R * t) = 1 := by
    rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  have hfun := hprod.congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun u ↦ yuleWeight_succ_eq_mul (n := n) (R := R) k u)
  refine hfun.congr_deriv ?_
  rw [yuleWeight_succ_eq_mul]
  linear_combination (((n : ℝ) + k) * R * yuleWeight n R k t) * hone

/-- The derivative of a Yule weight, case by case. -/
def yuleDeriv (n : ℕ) (R : ℝ) : ℕ → ℝ → ℝ
  | 0, t => -((n : ℝ) * R) * yuleWeight n R 0 t
  | k + 1, t => -(((n : ℝ) + k + 1) * R) * yuleWeight n R (k + 1) t +
      ((n : ℝ) + k) * R * yuleWeight n R k t

/-- **The birth equations.** Every Yule weight has derivative `yuleDeriv`. -/
theorem hasDerivAt_yuleWeight (k : ℕ) (t : ℝ) :
    HasDerivAt (yuleWeight n R k) (yuleDeriv n R k t) t := by
  cases k with
  | zero => exact hasDerivAt_yuleWeight_zero t
  | succ k => exact hasDerivAt_yuleWeight_succ k t

/-- The Yule weights are nonnegative at nonnegative times. -/
theorem yuleWeight_nonneg (hR : 0 ≤ R) (k : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ yuleWeight n R k t := by
  induction k generalizing t with
  | zero => exact (Real.exp_pos _).le
  | succ k ih =>
    rw [yuleWeight_succ]
    refine intervalIntegral.integral_nonneg ht fun s hs ↦ ?_
    have hnk : (0 : ℝ) ≤ (n : ℝ) + k := by positivity
    exact mul_nonneg (Real.exp_pos _).le (mul_nonneg (mul_nonneg hnk hR) (ih hs.1))

/-- The cubic weight `(n + k + 1)(n + k + 2)(n + k + 3)` of the moment bound. -/
def yuleMoment (n k : ℕ) : ℝ :=
  ((n : ℝ) + k + 1) * ((n : ℝ) + k + 2) * ((n : ℝ) + k + 3)

/-- The cubic weight is at least one. -/
theorem one_le_yuleMoment (n k : ℕ) : 1 ≤ yuleMoment n k := by
  have h0 : (0 : ℝ) ≤ (n : ℝ) + k := by positivity
  unfold yuleMoment
  nlinarith [mul_nonneg h0 h0, mul_nonneg (mul_nonneg h0 h0) h0]

/-- The cubic weight dominates the cube of the arity. -/
theorem pow_three_le_yuleMoment (n k : ℕ) : ((n : ℝ) + k) ^ 3 ≤ yuleMoment n k := by
  have h0 : (0 : ℝ) ≤ (n : ℝ) + k := by positivity
  unfold yuleMoment
  nlinarith [mul_nonneg h0 h0]

/-- **The cubic weight grows by at most three times itself per birth, at the birth rate**:
`(n + k) (w_{k+1} - w_k) ≤ 3 w_k`. -/
theorem mul_sub_yuleMoment_le (n k : ℕ) :
    ((n : ℝ) + k) * (yuleMoment n (k + 1) - yuleMoment n k) ≤ 3 * yuleMoment n k := by
  have h0 : (0 : ℝ) ≤ (n : ℝ) + k := by positivity
  unfold yuleMoment
  push_cast
  nlinarith [mul_nonneg h0 h0]

/-- **The derivative of the partial cubic moment**, with the loss of the last weight:
`∑_{k ≤ K} w_k y_k' + (n + K) R w_K y_K ≤ 3R ∑_{k < K} w_k y_k`. -/
theorem sum_yuleMoment_mul_yuleDeriv_le (hR : 0 ≤ R) {t : ℝ} (ht : 0 ≤ t) (K : ℕ) :
    ∑ k ∈ range (K + 1), yuleMoment n k * yuleDeriv n R k t +
        ((n : ℝ) + K) * R * (yuleMoment n K * yuleWeight n R K t) ≤
      3 * R * ∑ k ∈ range K, yuleMoment n k * yuleWeight n R k t := by
  induction K with
  | zero =>
    rw [sum_range_one, sum_range_zero, mul_zero]
    have hder : yuleDeriv n R 0 t = -((n : ℝ) * R) * yuleWeight n R 0 t := rfl
    rw [hder, Nat.cast_zero, add_zero]
    nlinarith
  | succ K ih =>
    rw [sum_range_succ, sum_range_succ (fun k ↦ yuleMoment n k * yuleWeight n R k t)]
    have hder : yuleDeriv n R (K + 1) t =
        -(((n : ℝ) + K + 1) * R) * yuleWeight n R (K + 1) t +
          ((n : ℝ) + K) * R * yuleWeight n R K t := rfl
    rw [hder]
    have hstep := mul_le_mul_of_nonneg_right (mul_sub_yuleMoment_le n K)
      (mul_nonneg hR (yuleWeight_nonneg (n := n) hR K ht))
    push_cast
    nlinarith [ih, hstep]

/-- **The cubic moment of the Yule weights**: for `t ≥ 0`,
`∑_{k ≤ K} (n+k+1)(n+k+2)(n+k+3) y_k(t) ≤ (n+1)(n+2)(n+3) e^{3Rt}`. The partial moment times
`e^{-3Rt}` does not increase. -/
theorem sum_yuleMoment_mul_le (hR : 0 ≤ R) (K : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    ∑ k ∈ range (K + 1), yuleMoment n k * yuleWeight n R k t ≤
      yuleMoment n 0 * Real.exp (3 * R * t) := by
  have hS : ∀ u, HasDerivAt (fun u ↦ ∑ k ∈ range (K + 1), yuleMoment n k * yuleWeight n R k u)
      (∑ k ∈ range (K + 1), yuleMoment n k * yuleDeriv n R k u) u :=
    fun u ↦ HasDerivAt.fun_sum fun k _ ↦ (hasDerivAt_yuleWeight k u).const_mul (yuleMoment n k)
  have hP : ∀ u, HasDerivAt
      (fun u ↦ Real.exp (-(3 * R * u)) *
        ∑ k ∈ range (K + 1), yuleMoment n k * yuleWeight n R k u)
      (-(3 * R) * Real.exp (-(3 * R * u)) *
          ∑ k ∈ range (K + 1), yuleMoment n k * yuleWeight n R k u +
        Real.exp (-(3 * R * u)) * ∑ k ∈ range (K + 1), yuleMoment n k * yuleDeriv n R k u) u :=
    fun u ↦ (hasDerivAt_exp_neg_mul (3 * R) u).mul (hS u)
  have hanti : AntitoneOn
      (fun u ↦ Real.exp (-(3 * R * u)) *
        ∑ k ∈ range (K + 1), yuleMoment n k * yuleWeight n R k u) (Set.Ici 0) := by
    refine antitoneOn_of_deriv_nonpos (convex_Ici 0)
      (fun u _ ↦ (hP u).continuousAt.continuousWithinAt)
      (fun u _ ↦ (hP u).differentiableAt.differentiableWithinAt) fun u hu ↦ ?_
    rw [interior_Ici] at hu
    rw [(hP u).deriv]
    have hu0 : 0 ≤ u := le_of_lt hu
    have hbound := sum_yuleMoment_mul_yuleDeriv_le (n := n) hR hu0 K
    have hlastw := mul_nonneg (zero_le_one.trans (one_le_yuleMoment n K))
      (yuleWeight_nonneg (n := n) hR K hu0)
    have htail : 0 ≤ ((n : ℝ) + K) * R * (yuleMoment n K * yuleWeight n R K u) :=
      mul_nonneg (mul_nonneg (by positivity) hR) hlastw
    have hlast : ∑ k ∈ range K, yuleMoment n k * yuleWeight n R k u ≤
        ∑ k ∈ range (K + 1), yuleMoment n k * yuleWeight n R k u := by
      rw [sum_range_succ]
      linarith
    have h3R : (0 : ℝ) ≤ 3 * R := mul_nonneg (by norm_num) hR
    have hderiv_le : ∑ k ∈ range (K + 1), yuleMoment n k * yuleDeriv n R k u ≤
        3 * R * ∑ k ∈ range (K + 1), yuleMoment n k * yuleWeight n R k u := by
      linarith [mul_le_mul_of_nonneg_left hlast h3R]
    have hexp := (Real.exp_pos (-(3 * R * u))).le
    nlinarith [mul_le_mul_of_nonneg_left hderiv_le hexp]
  have hle := hanti (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr ht) ht
  have hzero : ∑ k ∈ range (K + 1), yuleMoment n k * yuleWeight n R k 0 = yuleMoment n 0 := by
    rw [sum_range_succ']
    simp only [yuleWeight_succ_zero, mul_zero, sum_const_zero, zero_add, yuleWeight_zero_zero,
      mul_one]
  simp only [mul_zero, neg_zero, Real.exp_zero, one_mul, hzero] at hle
  have hsplit : ∑ k ∈ range (K + 1), yuleMoment n k * yuleWeight n R k t =
      Real.exp (3 * R * t) * (Real.exp (-(3 * R * t)) *
        ∑ k ∈ range (K + 1), yuleMoment n k * yuleWeight n R k t) := by
    rw [← mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, one_mul]
  rw [hsplit, mul_comm (yuleMoment n 0)]
  exact mul_le_mul_of_nonneg_left hle (Real.exp_pos _).le

/-- **One cubic moment term** is bounded by the whole moment. -/
theorem yuleMoment_mul_yuleWeight_le (hR : 0 ≤ R) (k : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    yuleMoment n k * yuleWeight n R k t ≤ yuleMoment n 0 * Real.exp (3 * R * t) := by
  refine le_trans ?_ (sum_yuleMoment_mul_le (n := n) hR k ht)
  rw [sum_range_succ]
  have hrest : 0 ≤ ∑ j ∈ range k, yuleMoment n j * yuleWeight n R j t :=
    sum_nonneg fun j _ ↦ mul_nonneg (zero_le_one.trans (one_le_yuleMoment n j))
      (yuleWeight_nonneg (n := n) hR j ht)
  linarith

end Yule

/-! ## The killed coalescence semigroup -/

section Dyson

variable {H : Type*} [Fintype H] {E : Type*} [Fintype E]

/-- **The semigroup law of the gain semigroup**, `e^{(s+t)P} = e^{sP} e^{tP}`. -/
theorem gainSemigroup_add {m : ℕ} (c s t : ℝ) :
    gainSemigroup (H := H) (n := m) c (s + t) = gainSemigroup c s * gainSemigroup c t := by
  have hcomm : Commute
      (s • LinearMap.toContinuousLinearMap (coalescenceGain (H := H) (n := m) c))
      (t • LinearMap.toContinuousLinearMap (coalescenceGain (H := H) (n := m) c)) := by
    show s • _ * t • _ = t • _ * s • _
    rw [smul_mul_smul_comm, smul_mul_smul_comm, mul_comm s t]
  rw [gainSemigroup, gainSemigroup, gainSemigroup, add_smul, NormedSpace.exp_add_of_commute hcomm]

/-- The gain semigroup is continuous in time in the operator norm. -/
theorem continuous_gainSemigroup {m : ℕ} (c : ℝ) :
    Continuous fun t : ℝ ↦ gainSemigroup (H := H) (n := m) c t :=
  continuous_iff_continuousAt.mpr fun t ↦
    (hasDerivAt_exp_smul_const' (LinearMap.toContinuousLinearMap
      (coalescenceGain (H := H) (n := m) c)) t).continuousAt

/-- **The killed coalescence semigroup** `e^{t(P - λ_m)} = e^{-λ_m t} e^{tP}` on observations of
arity `m`, with the exit rate `λ_m = c d_m + m R`. -/
def killedSemigroup (c : ℝ) (r : E → ℝ) (m : ℕ) (t : ℝ) :
    ((Fin m → H) → ℝ) →L[ℝ] ((Fin m → H) → ℝ) :=
  Real.exp (-(dualExitRate c r m * t)) • gainSemigroup c t

/-- At time zero the killed semigroup is the identity. -/
theorem killedSemigroup_zero (c : ℝ) (r : E → ℝ) (m : ℕ) :
    killedSemigroup (H := H) c r m 0 = 1 := by
  rw [killedSemigroup, mul_zero, neg_zero, Real.exp_zero, one_smul, gainSemigroup_zero]

/-- **The semigroup law of the killed semigroup**, at all real times. -/
theorem killedSemigroup_add (c : ℝ) (r : E → ℝ) (m : ℕ) (s t : ℝ) :
    killedSemigroup (H := H) c r m (s + t) =
      killedSemigroup c r m s * killedSemigroup c r m t := by
  ext g : 1
  simp only [killedSemigroup, ContinuousLinearMap.smul_apply, ContinuousLinearMap.mul_apply,
    map_smul, smul_smul, gainSemigroup_add]
  congr 1
  rw [← Real.exp_add]
  congr 1
  ring

/-- The killed semigroup is continuous in time in the operator norm. -/
theorem continuous_killedSemigroup (c : ℝ) (r : E → ℝ) (m : ℕ) :
    Continuous fun t : ℝ ↦ killedSemigroup (H := H) c r m t :=
  (Real.continuous_exp.comp (continuous_const.mul continuous_id).neg).smul
    (continuous_gainSemigroup c)

/-- **The derivative of the killed semigroup** in the operator norm. -/
theorem hasDerivAt_killedSemigroup (c : ℝ) (r : E → ℝ) (m : ℕ) (t : ℝ) :
    HasDerivAt (fun u ↦ killedSemigroup (H := H) c r m u)
      (Real.exp (-(dualExitRate c r m * t)) •
          (LinearMap.toContinuousLinearMap (coalescenceGain (H := H) (n := m) c) *
            gainSemigroup c t) +
        (-dualExitRate c r m * Real.exp (-(dualExitRate c r m * t))) • gainSemigroup c t) t :=
  (hasDerivAt_exp_neg_mul (dualExitRate c r m) t).smul
    (hasDerivAt_exp_smul_const' (LinearMap.toContinuousLinearMap
      (coalescenceGain (H := H) (n := m) c)) t)

/-- **The killed semigroup moves an observation along `P - λ_m`.** -/
theorem hasDerivAt_killedSemigroup_apply (c : ℝ) (r : E → ℝ) {m : ℕ} (t : ℝ)
    (f : (Fin m → H) → ℝ) :
    HasDerivAt (fun u ↦ killedSemigroup c r m u f)
      (coalescenceGain c (killedSemigroup c r m t f) -
        dualExitRate c r m • killedSemigroup c r m t f) t := by
  have h := (hasDerivAt_exp_neg_mul (dualExitRate c r m) t).smul
    (hasDerivAt_gainSemigroup_apply c t f)
  convert h using 1
  rw [killedSemigroup, ContinuousLinearMap.smul_apply, map_smul, smul_smul, neg_mul, neg_smul,
    sub_eq_add_neg]

/-- **The killed semigroup kills at the branching rate**: for `t ≥ 0`,
`‖e^{-λ_m t} e^{tP} f‖ ≤ e^{-m R t} ‖f‖`. -/
theorem norm_killedSemigroup_apply_le {c : ℝ} (hc : 0 ≤ c) (r : E → ℝ) {m : ℕ} {t : ℝ}
    (ht : 0 ≤ t) (f : (Fin m → H) → ℝ) :
    ‖killedSemigroup c r m t f‖ ≤ Real.exp (-((m : ℝ) * (∑ e, r e) * t)) * ‖f‖ := by
  rw [killedSemigroup, ContinuousLinearMap.smul_apply, norm_smul, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _)]
  calc Real.exp (-(dualExitRate c r m * t)) * ‖gainSemigroup c t f‖
      ≤ Real.exp (-(dualExitRate c r m * t)) *
          (‖f‖ * Real.exp ((c * ∑ b : Fin m, ((Iio b).card : ℝ)) * t)) :=
        mul_le_mul_of_nonneg_left (norm_gainSemigroup_le hc ht f) (Real.exp_pos _).le
    _ = Real.exp (-((m : ℝ) * (∑ e, r e) * t)) * ‖f‖ := by
        rw [dualExitRate, mul_left_comm, ← Real.exp_add, mul_comm]
        congr 2
        ring

/-! ## The Dyson components -/

/-- The integrand of a branching: the observation `u s` branched, and brought back to time zero
by the killed semigroup. -/
theorem continuous_branchIntegrand (c : ℝ) (r : E → ℝ) (T : E → H → H → H) {m : ℕ}
    {u : ℝ → (Fin m → H) → ℝ} (hu : Continuous u) :
    Continuous fun s ↦ killedSemigroup c r (m + 1) (-s) (branchingGain r T (u s)) :=
  ((continuous_killedSemigroup c r (m + 1)).comp continuous_neg).clm_apply
    ((LinearMap.continuous_of_finiteDimensional (branchingGain r T)).comp hu)

/-- **The Dyson components of the backward circuit** started at `f`:
`u_0(t) = e^{t(P - λ_n)} f` and `u_{k+1}(t) = ∫_0^t e^{(t-s)(P - λ_{n+k+1})} G u_k(s) ds`, an
observation of arity `n + k`. -/
def dysonTerm (c : ℝ) (r : E → ℝ) (T : E → H → H → H) {n : ℕ} (f : (Fin n → H) → ℝ) :
    (k : ℕ) → ℝ → ((Fin (n + k) → H) → ℝ)
  | 0, t => killedSemigroup c r n t f
  | k + 1, t => ∫ s in (0 : ℝ)..t,
      killedSemigroup c r (n + k + 1) (t - s) (branchingGain r T (dysonTerm c r T f k s))

variable (c : ℝ) (r : E → ℝ) (T : E → H → H → H) {n : ℕ} (f : (Fin n → H) → ℝ)

/-- The component without branchings. -/
theorem dysonTerm_zero (t : ℝ) : dysonTerm c r T f 0 t = killedSemigroup c r n t f :=
  rfl

/-- The component after a branching. -/
theorem dysonTerm_succ (k : ℕ) (t : ℝ) :
    dysonTerm c r T f (k + 1) t = ∫ s in (0 : ℝ)..t,
      killedSemigroup c r (n + k + 1) (t - s) (branchingGain r T (dysonTerm c r T f k s)) :=
  rfl

/-- At time zero the component without branchings is the observation. -/
theorem dysonTerm_zero_zero : dysonTerm c r T f 0 0 = f := by
  rw [dysonTerm_zero, killedSemigroup_zero, ContinuousLinearMap.one_apply]

/-- At time zero every component after a branching vanishes. -/
theorem dysonTerm_succ_zero (k : ℕ) : dysonTerm c r T f (k + 1) 0 = 0 :=
  intervalIntegral.integral_same

/-- **The factored form of a component after a branching**, given that the previous component
is continuous. -/
theorem dysonTerm_succ_eq_mul (k : ℕ) (hk : Continuous (dysonTerm c r T f k)) (t : ℝ) :
    dysonTerm c r T f (k + 1) t = killedSemigroup c r (n + k + 1) t
      (∫ s in (0 : ℝ)..t,
        killedSemigroup c r (n + k + 1) (-s) (branchingGain r T (dysonTerm c r T f k s))) := by
  rw [dysonTerm_succ, ← ContinuousLinearMap.intervalIntegral_comp_comm
    (killedSemigroup c r (n + k + 1) t)
    ((continuous_branchIntegrand c r T hk).intervalIntegrable 0 t)]
  refine intervalIntegral.integral_congr fun s _ ↦ ?_
  show killedSemigroup c r (n + k + 1) (t - s) _ =
    killedSemigroup c r (n + k + 1) t (killedSemigroup c r (n + k + 1) (-s) _)
  rw [← ContinuousLinearMap.mul_apply, ← killedSemigroup_add, sub_eq_add_neg]

/-- The Dyson components are continuous in time. -/
theorem continuous_dysonTerm (k : ℕ) : Continuous (dysonTerm c r T f k) := by
  induction k with
  | zero => exact (continuous_killedSemigroup c r n).clm_apply continuous_const
  | succ k ih =>
    rw [funext (dysonTerm_succ_eq_mul c r T f k ih)]
    exact (continuous_killedSemigroup c r (n + k + 1)).clm_apply
      (continuous_integral_from_zero (continuous_branchIntegrand c r T ih))

/-- **The component without branchings solves `u_0' = (P - λ_n) u_0`.** -/
theorem hasDerivAt_dysonTerm_zero (t : ℝ) :
    HasDerivAt (dysonTerm c r T f 0)
      (coalescenceGain c (dysonTerm c r T f 0 t) - dualExitRate c r n • dysonTerm c r T f 0 t)
      t :=
  hasDerivAt_killedSemigroup_apply c r t f

/-- **A component after a branching solves `u_{k+1}' = (P - λ_{n+k+1}) u_{k+1} + G u_k`.** -/
theorem hasDerivAt_dysonTerm_succ (k : ℕ) (t : ℝ) :
    HasDerivAt (dysonTerm c r T f (k + 1))
      (coalescenceGain c (dysonTerm c r T f (k + 1) t) -
          dualExitRate c r (n + k + 1) • dysonTerm c r T f (k + 1) t +
        (branchingGain r T (dysonTerm c r T f k t) : (Fin (n + (k + 1)) → H) → ℝ)) t := by
  have hk := continuous_dysonTerm c r T f k
  have h := HasDerivAt.clm_apply (hasDerivAt_killedSemigroup c r (n + k + 1) t)
    (hasDerivAt_integral_from_zero (continuous_branchIntegrand c r T hk) t)
  have hfun := h.congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun u ↦ dysonTerm_succ_eq_mul c r T f k hk u)
  refine hfun.congr_deriv ?_
  rw [dysonTerm_succ_eq_mul c r T f k hk t,
    ← ContinuousLinearMap.mul_apply (killedSemigroup c r (n + k + 1) t), ← killedSemigroup_add,
    add_neg_cancel, killedSemigroup_zero, ContinuousLinearMap.one_apply]
  simp only [killedSemigroup, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.mul_apply, LinearMap.coe_toContinuousLinearMap', map_smul]
  module

/-- **The Yule weights majorize the Dyson components**: for `c ≥ 0`, nonnegative rates and
`t ≥ 0`, `‖u_k(t)‖ ≤ y_k(t) ‖f‖` with `R = ∑_e r_e`. -/
theorem norm_dysonTerm_le {c : ℝ} (hc : 0 ≤ c) {r : E → ℝ} (hr : ∀ e, 0 ≤ r e)
    (T : E → H → H → H) {n : ℕ} (f : (Fin n → H) → ℝ) (k : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    ‖dysonTerm c r T f k t‖ ≤ yuleWeight n (∑ e, r e) k t * ‖f‖ := by
  induction k generalizing t with
  | zero => exact norm_killedSemigroup_apply_le hc r ht f
  | succ k ih =>
    have hR : 0 ≤ ∑ e, r e := sum_nonneg fun e _ ↦ hr e
    have hy := continuous_yuleWeight n (∑ e, r e) k
    have hbound : Continuous fun s ↦
        Real.exp (-(((n : ℝ) + k + 1) * (∑ e, r e) * (t - s))) *
          (((n : ℝ) + k) * (∑ e, r e) * yuleWeight n (∑ e, r e) k s) * ‖f‖ := by
      fun_prop
    rw [dysonTerm_succ, yuleWeight_succ, ← intervalIntegral.integral_mul_const]
    refine intervalIntegral.norm_integral_le_of_norm_le ht
      (Filter.Eventually.of_forall fun s hs ↦ ?_) (hbound.intervalIntegrable 0 t)
    have hkill := norm_killedSemigroup_apply_le hc r (sub_nonneg.mpr hs.2)
      (branchingGain r T (dysonTerm c r T f k s))
    have hbranch := norm_branchingGain_le hr T (dysonTerm c r T f k s)
    have hprev := ih hs.1.le
    have hrate : (0 : ℝ) ≤ ((n + k : ℕ) : ℝ) * ∑ e, r e := mul_nonneg (Nat.cast_nonneg _) hR
    calc ‖killedSemigroup c r (n + k + 1) (t - s) (branchingGain r T (dysonTerm c r T f k s))‖
        ≤ Real.exp (-(((n + k + 1 : ℕ) : ℝ) * (∑ e, r e) * (t - s))) *
            (((n + k : ℕ) : ℝ) * (∑ e, r e) * (yuleWeight n (∑ e, r e) k s * ‖f‖)) :=
          hkill.trans (mul_le_mul_of_nonneg_left
            (hbranch.trans (mul_le_mul_of_nonneg_left hprev hrate)) (Real.exp_pos _).le)
      _ = Real.exp (-(((n : ℝ) + k + 1) * (∑ e, r e) * (t - s))) *
            (((n : ℝ) + k) * (∑ e, r e) * yuleWeight n (∑ e, r e) k s) * ‖f‖ := by
          push_cast
          ring

/-- **The backward generator through a sampling observable.** The right-hand side of the Dyson
system, `(P - λ_m) g + G g`, read at `p` is the backward generator applied to `g`. -/
theorem samplingObservable_generator [DecidableEq H] {m : ℕ} (g : (Fin m → H) → ℝ)
    (p : H → ℝ) :
    samplingObservable (coalescenceGain c g - dualExitRate c r m • g) p +
        samplingObservable (branchingGain r T g) p = backwardGenerator c r T g p := by
  rw [backwardGenerator_eq_jump]
  simp only [← samplingFunctional_apply, coalescenceGain, branchingGain, LinearMap.coe_mk,
    AddHom.coe_mk, map_sub, map_smul, map_sum, smul_eq_mul]
  ring

end Dyson

end

end Descent.Pangenome.AncestralLocality.DecisionDysonDual
