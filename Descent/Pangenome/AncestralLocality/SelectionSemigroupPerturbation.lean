/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Pangenome.AncestralLocality.DecisionWindowSemigroup

assert_below Descent.PopGen Descent.Spectral Descent.Blindness Descent.Conditionals
assert_below Descent.Portability Descent.Decision Descent.Program

/-!
# Weak selection moves the window semigroup by at most `2 n R t`

`DecisionWindowSemigroup` constructs the forward semigroup `T^r` of one finite window: resampling
at rate `c ≥ 0` and events `e` with deterministic rules `T e` at rates `r_e ≥ 0`. Selection enters
the window as such events. This module bounds how far the events move the semigroup from the
neutral semigroup of the same window, `T^0`, where every event has rate zero
(`neutralWindowSemigroup`).

The bound. For an observation `f` of `n` genomes, with `R = ∑_e r_e`,
`‖T^r_t H_f - T^0_t H_f‖ ≤ 2 (1 - e^{-nRt}) ‖f‖ ≤ 2 n R t ‖f‖` at every time `t ≥ 0`
(`norm_decisionWindowSemigroup_sub_neutral_le`). The constant `2n` is uniform in the time, in the
genome types and in the coalescence rate. For event rates at most `σ` the bound reads
`t σ (2 n |E|) ‖f‖` (`norm_decisionWindowSemigroup_sub_neutral_le_card`), and for a total
selective rate at most `σ` it reads `t σ (2n) ‖f‖`
(`norm_decisionWindowSemigroup_sub_neutral_le_of_sum_le`). The number of events enters only
through `R`: an event duplicated `m` times acts as one event at `m` times the rate.

The dual route. Both semigroups are dual series on sampling functions
(`decisionWindowSemigroup_samplingFunction`). At rate zero nothing branches
(`branchingGain_zero_rates`, `dysonTerm_zero_rates_succ`), so the neutral series is its unbranched
component alone (`dualSeries_zero_rates`). The selective series differs from it in two places.
Its unbranched component is the neutral one killed at the branching rate,
`e^{t(P - λ^r_n)} f = e^{-nRt} e^{t(P - λ^0_n)} f` (`killedSemigroup_eq_smul_zero_rates`), so the
two differ by at most `(1 - e^{-nRt}) ‖f‖` (`norm_killedSemigroup_sub_zero_rates_le`). Its
branched components are bounded by the Yule weights of at least one birth. The Yule weights lose
mass only through the last weight, `1 - ∑_{k ≤ K} y_k(t) = ∫_0^t (n + K) R y_K(s) ds`
(`sum_yuleDeriv`, `one_sub_sum_yuleWeight`), so they have mass at most one
(`sum_yuleWeight_le_one`), and the weights of at least one birth total at most `1 - e^{-nRt}`
(`sum_yuleWeight_succ_le`). The zeroth moment of the Yule weights gives a constant independent of
the time; the cubic moment of `DecisionDysonDual` would carry `e^{3Rt}`. Summing the two parts
bounds every partial dual series (`norm_partialDual_sub_zero_rates_le`), and the limit bounds the
dual series (`norm_dualSeries_sub_zero_rates_le`).

Significance. Every expectation of a sampling observable, and so every polynomial in the window
frequencies, that the neutral semigroup computes survives weak selection to first order, with the
explicit error bar `2 n R t ‖f‖`.

Scope. One finite window, deterministic decision rules and constant rates. A selection kernel
enters through a decomposition into decision events, which is not constructed here.

## Empirical status

None. The bodies here are bounds on Dyson components, integrals of Yule weights and elementary
exponential inequalities, so no measurement can bear on them.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Pangenome.AncestralLocality.SelectionSemigroupPerturbation

open Finset Filter Topology InfiniteGenomeLimit DecisionDysonDual DecisionWindowJumps
  DecisionWindowSemigroup
open scoped NNReal

noncomputable section

/-! ## The mass of the Yule weights -/

section Yule

variable {n : ℕ} {R : ℝ}

/-- **The birth equations telescope**: the derivatives of the first `K + 1` Yule weights sum to
the loss of the last, `∑_{k ≤ K} y_k' = -(n + K) R y_K`. -/
theorem sum_yuleDeriv (n : ℕ) (R : ℝ) (K : ℕ) (t : ℝ) :
    ∑ k ∈ range (K + 1), yuleDeriv n R k t = -(((n : ℝ) + K) * R) * yuleWeight n R K t := by
  induction K with
  | zero =>
    have hder : yuleDeriv n R 0 t = -((n : ℝ) * R) * yuleWeight n R 0 t := rfl
    simp only [sum_range_one, hder, Nat.cast_zero, add_zero]
  | succ K ih =>
    have hder : yuleDeriv n R (K + 1) t =
        -(((n : ℝ) + K + 1) * R) * yuleWeight n R (K + 1) t +
          ((n : ℝ) + K) * R * yuleWeight n R K t := rfl
    rw [sum_range_succ, ih, hder]
    push_cast
    ring

/-- At time zero the Yule weights have total mass one. -/
theorem sum_yuleWeight_zero (K : ℕ) : ∑ k ∈ range (K + 1), yuleWeight n R k 0 = 1 := by
  rw [sum_range_succ']
  simp only [yuleWeight_succ_zero, sum_const_zero, zero_add, yuleWeight_zero_zero]

/-- **The mass lost by the first `K + 1` Yule weights is the flux through the last**:
`1 - ∑_{k ≤ K} y_k(t) = ∫_0^t (n + K) R y_K(s) ds`. -/
theorem one_sub_sum_yuleWeight (K : ℕ) (t : ℝ) :
    1 - ∑ k ∈ range (K + 1), yuleWeight n R k t =
      ∫ s in (0 : ℝ)..t, ((n : ℝ) + K) * R * yuleWeight n R K s := by
  have hderiv : ∀ u ∈ Set.uIcc (0 : ℝ) t,
      HasDerivAt (fun u ↦ 1 - ∑ k ∈ range (K + 1), yuleWeight n R k u)
        (((n : ℝ) + K) * R * yuleWeight n R K u) u := fun u _ ↦ by
    have hsum : HasDerivAt (fun u ↦ ∑ k ∈ range (K + 1), yuleWeight n R k u)
        (∑ k ∈ range (K + 1), yuleDeriv n R k u) u :=
      HasDerivAt.fun_sum fun k _ ↦ hasDerivAt_yuleWeight k u
    rw [sum_yuleDeriv] at hsum
    convert hsum.const_sub 1 using 1
    ring
  have hint : IntervalIntegrable (fun u ↦ ((n : ℝ) + K) * R * yuleWeight n R K u)
      MeasureTheory.volume 0 t :=
    (continuous_const.mul (continuous_yuleWeight n R K)).intervalIntegrable 0 t
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint, sum_yuleWeight_zero]
  ring

/-- **The Yule weights have mass at most one**: `∑_{k ≤ K} y_k(t) ≤ 1` for `R ≥ 0` and
`t ≥ 0`. -/
theorem sum_yuleWeight_le_one (hR : 0 ≤ R) (K : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    ∑ k ∈ range (K + 1), yuleWeight n R k t ≤ 1 := by
  have hflux : 0 ≤ ∫ s in (0 : ℝ)..t, ((n : ℝ) + K) * R * yuleWeight n R K s :=
    intervalIntegral.integral_nonneg ht fun s hs ↦
      mul_nonneg (mul_nonneg (by positivity) hR) (yuleWeight_nonneg hR K hs.1)
  linarith [one_sub_sum_yuleWeight (n := n) (R := R) K t]

/-- **At least one birth has weight at most `1 - e^{-nRt}`**: for `R ≥ 0` and `t ≥ 0`,
`∑_{k < K} y_{k+1}(t) ≤ 1 - e^{-nRt}`. -/
theorem sum_yuleWeight_succ_le (hR : 0 ≤ R) (K : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    ∑ k ∈ range K, yuleWeight n R (k + 1) t ≤ 1 - Real.exp (-((n : ℝ) * R * t)) := by
  have h := sum_yuleWeight_le_one (n := n) hR K ht
  rw [sum_range_succ', yuleWeight_zero] at h
  linarith

end Yule

/-! ## The neutral dual series -/

section Window

variable {H : Type*} [Fintype H] [DecidableEq H] {E : Type*} [Fintype E]

/-- **Branching at rate zero does nothing.** -/
theorem branchingGain_zero_rates (T : E → H → H → H) {m : ℕ} (g : (Fin m → H) → ℝ) :
    branchingGain (0 : E → ℝ) T g = 0 := by
  show ∑ e, (0 : E → ℝ) e • ∑ a, decisionBranch (T e) a g = 0
  simp only [Pi.zero_apply, zero_smul, sum_const_zero]

/-- **Without selection no component branches**: at rate zero every Dyson component after a
branching vanishes. -/
theorem dysonTerm_zero_rates_succ (c : ℝ) (T : E → H → H → H) {n : ℕ} (f : (Fin n → H) → ℝ)
    (k : ℕ) (t : ℝ) : dysonTerm c (0 : E → ℝ) T f (k + 1) t = 0 := by
  rw [dysonTerm_succ]
  refine (intervalIntegral.integral_congr fun s _ ↦ ?_).trans intervalIntegral.integral_zero
  rw [branchingGain_zero_rates, map_zero]

/-- **The neutral dual series is its unbranched component**: at rate zero,
`∑_k H_{u_k(t)} = H_{u_0(t)}`. -/
theorem dualSeries_zero_rates (c : ℝ) (T : E → H → H → H) {n : ℕ} (f : (Fin n → H) → ℝ)
    (t : ℝ) :
    dualSeries c (0 : E → ℝ) T f t = samplingFunction (dysonTerm c (0 : E → ℝ) T f 0 t) := by
  have hzero : ∀ k ≠ 0, samplingFunction (dysonTerm c (0 : E → ℝ) T f k t) = 0 := by
    intro k hk
    cases k with
    | zero => exact absurd rfl hk
    | succ k => rw [dysonTerm_zero_rates_succ, samplingFunction_zero]
  rw [dualSeries, tsum_eq_single 0 hzero]

/-! ## The unbranched components -/

/-- **Selection kills the unbranched component at the branching rate**:
`e^{t(P - λ^r_m)} g = e^{-mRt} e^{t(P - λ^0_m)} g`. -/
theorem killedSemigroup_eq_smul_zero_rates (c : ℝ) (r : E → ℝ) (m : ℕ) (t : ℝ)
    (g : (Fin m → H) → ℝ) :
    killedSemigroup c r m t g =
      Real.exp (-((m : ℝ) * (∑ e, r e) * t)) • killedSemigroup c (0 : E → ℝ) m t g := by
  have hexp : Real.exp (-(dualExitRate c r m * t)) = Real.exp (-((m : ℝ) * (∑ e, r e) * t)) *
      Real.exp (-(dualExitRate c (0 : E → ℝ) m * t)) := by
    rw [← Real.exp_add]
    congr 1
    simp only [dualExitRate, Pi.zero_apply, sum_const_zero, mul_zero, add_zero]
    ring
  simp only [killedSemigroup, ContinuousLinearMap.smul_apply, smul_smul, hexp]

/-- The neutral unbranched component contracts: `‖e^{t(P - λ^0_m)} g‖ ≤ ‖g‖` for `t ≥ 0`. -/
theorem norm_killedSemigroup_zero_rates_le {c : ℝ} (hc : 0 ≤ c) {m : ℕ} {t : ℝ} (ht : 0 ≤ t)
    (g : (Fin m → H) → ℝ) : ‖killedSemigroup c (0 : E → ℝ) m t g‖ ≤ ‖g‖ := by
  have h := norm_killedSemigroup_apply_le hc (0 : E → ℝ) ht g
  simpa only [Pi.zero_apply, sum_const_zero, mul_zero, zero_mul, neg_zero, Real.exp_zero,
    one_mul] using h

/-- **The unbranched components with and without selection** differ by at most
`(1 - e^{-mRt}) ‖g‖` for `t ≥ 0`. -/
theorem norm_killedSemigroup_sub_zero_rates_le {c : ℝ} (hc : 0 ≤ c) {r : E → ℝ}
    (hr : ∀ e, 0 ≤ r e) {m : ℕ} {t : ℝ} (ht : 0 ≤ t) (g : (Fin m → H) → ℝ) :
    ‖killedSemigroup c r m t g - killedSemigroup c (0 : E → ℝ) m t g‖ ≤
      (1 - Real.exp (-((m : ℝ) * (∑ e, r e) * t))) * ‖g‖ := by
  have hR : 0 ≤ ∑ e, r e := sum_nonneg fun e _ ↦ hr e
  have hexp : Real.exp (-((m : ℝ) * (∑ e, r e) * t)) ≤ 1 :=
    Real.exp_le_one_iff.mpr (neg_nonpos.mpr (mul_nonneg (mul_nonneg (Nat.cast_nonneg m) hR) ht))
  have hsplit : killedSemigroup c r m t g - killedSemigroup c (0 : E → ℝ) m t g =
      (Real.exp (-((m : ℝ) * (∑ e, r e) * t)) - 1) • killedSemigroup c (0 : E → ℝ) m t g := by
    rw [killedSemigroup_eq_smul_zero_rates c r m t g, sub_smul, one_smul]
  rw [hsplit, norm_smul, Real.norm_eq_abs, abs_of_nonpos (sub_nonpos.mpr hexp), neg_sub]
  exact mul_le_mul_of_nonneg_left (norm_killedSemigroup_zero_rates_le hc ht g)
    (sub_nonneg.mpr hexp)

/-! ## The dual series with and without selection -/

/-- **A partial dual series with selection against the neutral dual series**: for `t ≥ 0`,
`‖W_K(t) - H_{u^0_0(t)}‖ ≤ 2 (1 - e^{-nRt}) ‖f‖`. The unbranched components contribute
`1 - e^{-nRt}`, and the branched components the Yule weights of at least one birth. -/
theorem norm_partialDual_sub_zero_rates_le {c : ℝ} (hc : 0 ≤ c) {r : E → ℝ}
    (hr : ∀ e, 0 ≤ r e) (T : E → H → H → H) {n : ℕ} (f : (Fin n → H) → ℝ) (K : ℕ) {t : ℝ}
    (ht : 0 ≤ t) :
    ‖partialDual c r T f K t - samplingFunction (dysonTerm c (0 : E → ℝ) T f 0 t)‖ ≤
      2 * (1 - Real.exp (-((n : ℝ) * (∑ e, r e) * t))) * ‖f‖ := by
  have hR : 0 ≤ ∑ e, r e := sum_nonneg fun e _ ↦ hr e
  have hsub : samplingFunction (dysonTerm c r T f 0 t - dysonTerm c (0 : E → ℝ) T f 0 t) =
      samplingFunction (dysonTerm c r T f 0 t) -
        samplingFunction (dysonTerm c (0 : E → ℝ) T f 0 t) :=
    map_sub (samplingCLM (n + 0)) (dysonTerm c r T f 0 t) (dysonTerm c (0 : E → ℝ) T f 0 t)
  have hsplit : partialDual c r T f K t - samplingFunction (dysonTerm c (0 : E → ℝ) T f 0 t) =
      ∑ k ∈ range K, samplingFunction (dysonTerm c r T f (k + 1) t) +
        samplingFunction (dysonTerm c r T f 0 t - dysonTerm c (0 : E → ℝ) T f 0 t) := by
    rw [hsub, partialDual, sum_range_succ']
    abel
  have htail : ‖∑ k ∈ range K, samplingFunction (dysonTerm c r T f (k + 1) t)‖ ≤
      (1 - Real.exp (-((n : ℝ) * (∑ e, r e) * t))) * ‖f‖ := by
    refine (norm_sum_le _ _).trans ?_
    calc ∑ k ∈ range K, ‖samplingFunction (dysonTerm c r T f (k + 1) t)‖
        ≤ ∑ k ∈ range K, yuleWeight n (∑ e, r e) (k + 1) t * ‖f‖ :=
          sum_le_sum fun k _ ↦ norm_samplingFunction_dysonTerm_le hc hr T f (k + 1) ht
      _ = (∑ k ∈ range K, yuleWeight n (∑ e, r e) (k + 1) t) * ‖f‖ := by rw [sum_mul]
      _ ≤ (1 - Real.exp (-((n : ℝ) * (∑ e, r e) * t))) * ‖f‖ :=
          mul_le_mul_of_nonneg_right (sum_yuleWeight_succ_le hR K ht) (norm_nonneg f)
  have hhead : ‖samplingFunction (dysonTerm c r T f 0 t - dysonTerm c (0 : E → ℝ) T f 0 t)‖ ≤
      (1 - Real.exp (-((n : ℝ) * (∑ e, r e) * t))) * ‖f‖ :=
    (norm_samplingFunction_le _).trans (norm_killedSemigroup_sub_zero_rates_le hc hr ht f)
  rw [hsplit]
  calc _ ≤ _ := norm_add_le _ _
    _ ≤ (1 - Real.exp (-((n : ℝ) * (∑ e, r e) * t))) * ‖f‖ +
          (1 - Real.exp (-((n : ℝ) * (∑ e, r e) * t))) * ‖f‖ := add_le_add htail hhead
    _ = 2 * (1 - Real.exp (-((n : ℝ) * (∑ e, r e) * t))) * ‖f‖ := by ring

/-- **The dual series with selection against the neutral dual series**: for `t ≥ 0`,
`‖∑_k H_{u^r_k(t)} - ∑_k H_{u^0_k(t)}‖ ≤ 2 (1 - e^{-nRt}) ‖f‖`. -/
theorem norm_dualSeries_sub_zero_rates_le {c : ℝ} (hc : 0 ≤ c) {r : E → ℝ}
    (hr : ∀ e, 0 ≤ r e) (T : E → H → H → H) {n : ℕ} (f : (Fin n → H) → ℝ) {t : ℝ}
    (ht : 0 ≤ t) :
    ‖dualSeries c r T f t - dualSeries c (0 : E → ℝ) T f t‖ ≤
      2 * (1 - Real.exp (-((n : ℝ) * (∑ e, r e) * t))) * ‖f‖ := by
  rw [dualSeries_zero_rates]
  have hlim : Tendsto (fun K : ℕ ↦
      ‖partialDual c r T f K t - samplingFunction (dysonTerm c (0 : E → ℝ) T f 0 t)‖) atTop
      (𝓝 ‖dualSeries c r T f t - samplingFunction (dysonTerm c (0 : E → ℝ) T f 0 t)‖) :=
    ((tendsto_partialDual hc hr T f ht).sub tendsto_const_nhds).norm
  exact le_of_tendsto' hlim fun K ↦ norm_partialDual_sub_zero_rates_le hc hr T f K ht

/-! ## The semigroups -/

/-- **The neutral window semigroup**: the forward semigroup of the same window with every event at
rate zero, resampling alone. -/
def neutralWindowSemigroup {c : ℝ} (hc : 0 ≤ c) (T : E → H → H → H) :
    FellerSemigroup (SimplexLaw H) :=
  decisionWindowSemigroup hc (r := (0 : E → ℝ)) (fun _ ↦ le_rfl) T

/-- **On a sampling function the neutral semigroup is the killed coalescence semigroup**,
`T^0_t H_f = H_{e^{t(P - λ^0_n)} f}`. -/
theorem neutralWindowSemigroup_samplingFunction {c : ℝ} (hc : 0 ≤ c) (T : E → H → H → H)
    (t : ℝ≥0) {n : ℕ} (f : (Fin n → H) → ℝ) :
    (neutralWindowSemigroup hc T).operator t (samplingFunction f) =
      samplingFunction (killedSemigroup c (0 : E → ℝ) n t f) := by
  rw [neutralWindowSemigroup, decisionWindowSemigroup_samplingFunction, dualSeries_zero_rates,
    dysonTerm_zero]

/-- **Weak selection moves the window semigroup by at most `2 n R t`.** For resampling at rate
`c ≥ 0`, events at rates `r_e ≥ 0` with total `R = ∑_e r_e`, and an observation `f` of `n`
genomes, `‖T^r_t H_f - T^0_t H_f‖ ≤ 2 n R t ‖f‖` at every time `t ≥ 0`. -/
theorem norm_decisionWindowSemigroup_sub_neutral_le {c : ℝ} (hc : 0 ≤ c) {r : E → ℝ}
    (hr : ∀ e, 0 ≤ r e) (T : E → H → H → H) (t : ℝ≥0) {n : ℕ} (f : (Fin n → H) → ℝ) :
    ‖(decisionWindowSemigroup hc hr T).operator t (samplingFunction f) -
        (neutralWindowSemigroup hc T).operator t (samplingFunction f)‖ ≤
      2 * n * (∑ e, r e) * (t : ℝ) * ‖f‖ := by
  rw [decisionWindowSemigroup_samplingFunction, neutralWindowSemigroup,
    decisionWindowSemigroup_samplingFunction]
  refine (norm_dualSeries_sub_zero_rates_le hc hr T f (NNReal.coe_nonneg t)).trans ?_
  calc 2 * (1 - Real.exp (-((n : ℝ) * (∑ e, r e) * t))) * ‖f‖
      ≤ 2 * ((n : ℝ) * (∑ e, r e) * t) * ‖f‖ := by
        refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ?_ (by norm_num))
          (norm_nonneg f)
        linarith [Real.add_one_le_exp (-((n : ℝ) * (∑ e, r e) * t))]
    _ = 2 * n * (∑ e, r e) * (t : ℝ) * ‖f‖ := by ring

/-- **The error bar for a total selective rate at most `σ`**:
`‖T^r_t H_f - T^0_t H_f‖ ≤ t σ (2n) ‖f‖` when `∑_e r_e ≤ σ`. -/
theorem norm_decisionWindowSemigroup_sub_neutral_le_of_sum_le {c σ : ℝ} (hc : 0 ≤ c)
    {r : E → ℝ} (hr : ∀ e, 0 ≤ r e) (hRσ : ∑ e, r e ≤ σ) (T : E → H → H → H) (t : ℝ≥0) {n : ℕ}
    (f : (Fin n → H) → ℝ) :
    ‖(decisionWindowSemigroup hc hr T).operator t (samplingFunction f) -
        (neutralWindowSemigroup hc T).operator t (samplingFunction f)‖ ≤
      (t : ℝ) * σ * (2 * n) * ‖f‖ := by
  refine (norm_decisionWindowSemigroup_sub_neutral_le hc hr T t f).trans ?_
  have hX : 0 ≤ 2 * (n : ℝ) * t * ‖f‖ := by positivity
  calc 2 * (n : ℝ) * (∑ e, r e) * t * ‖f‖ = (2 * n * t * ‖f‖) * ∑ e, r e := by ring
    _ ≤ (2 * n * t * ‖f‖) * σ := mul_le_mul_of_nonneg_left hRσ hX
    _ = (t : ℝ) * σ * (2 * n) * ‖f‖ := by ring

/-- **The error bar for event rates at most `σ`**:
`‖T^r_t H_f - T^0_t H_f‖ ≤ t σ (2 n |E|) ‖f‖` when `0 ≤ r_e ≤ σ` for every event. -/
theorem norm_decisionWindowSemigroup_sub_neutral_le_card {c σ : ℝ} (hc : 0 ≤ c) {r : E → ℝ}
    (hr : ∀ e, 0 ≤ r e) (hrσ : ∀ e, r e ≤ σ) (T : E → H → H → H) (t : ℝ≥0) {n : ℕ}
    (f : (Fin n → H) → ℝ) :
    ‖(decisionWindowSemigroup hc hr T).operator t (samplingFunction f) -
        (neutralWindowSemigroup hc T).operator t (samplingFunction f)‖ ≤
      (t : ℝ) * σ * (2 * n * Fintype.card E) * ‖f‖ := by
  have hRσ : ∑ e, r e ≤ Fintype.card E * σ :=
    calc ∑ e, r e ≤ ∑ _e : E, σ := sum_le_sum fun e _ ↦ hrσ e
      _ = Fintype.card E * σ := by rw [sum_const, card_univ, nsmul_eq_mul]
  refine (norm_decisionWindowSemigroup_sub_neutral_le_of_sum_le hc hr hRσ T t f).trans_eq ?_
  ring

end Window

end

end Descent.Pangenome.AncestralLocality.SelectionSemigroupPerturbation
