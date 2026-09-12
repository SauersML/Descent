/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Pangenome.AncestralLocality.DecisionWindowJumps
import Descent.Pangenome.AncestralLocality.DecisionDysonDual

assert_below Descent.PopGen Descent.Spectral Descent.Blindness Descent.Conditionals
assert_below Descent.Portability Descent.Decision Descent.Program

/-!
# The forward semigroup of a finite window with decisions

Theorem 9 of the research note "Ancestral locality" takes the finite-genome semigroups as given.
This module constructs the semigroup of one finite window: for genome types `H`, resampling at
rate `c ≥ 0` and events `e` with rules `T e` at rates `r_e ≥ 0`, a Feller semigroup on the laws of
`H` whose generator on sampling observables is the forward generator (7.1) of `SamplingDuality`.

The dual series. For an observation `f` of `n` genomes, `dualSeries c r T f t` is the continuous
function `∑_k H_{u_k(t)}` over the Dyson components `u_k` of `DecisionDysonDual`. It converges
because `‖u_k(t)‖ ≤ y_k(t) ‖f‖` and the Yule weights have a bounded cubic moment
(`summable_dualTerm`).

The approximation. The jump approximations of `DecisionWindowJumps` at step `ε` agree with the
dual series on sampling functions up to `t · 4 (c + R) ε (n+1)(n+2)(n+3) e^{3RT} ‖f‖` for
`0 ≤ t ≤ T`, with `R = ∑_e r_e` (`norm_jumpOperator_sub_dualSeries_le`). The proof differentiates
`s ↦ e^{s(J - λ)} W_K(t - s)` for the partial sums `W_K` of the series
(`norm_jumpOperator_sub_partialDual_le`): the generator estimate of `DecisionWindowJumps` controls
every component through the cubic moment, the last branching is controlled by the Yule weights,
and the jump semigroup contracts.

The semigroup. At the steps `ε_m = 1/(m+1)` the approximations satisfy the uniform approximation
bound of `InfiniteGenomeLimit` on the polynomials in the frequencies
(`decisionLightConeApproximation`), so their limit is a Feller semigroup
(`decisionWindowSemigroup`): positive, fixing the constants, contracting, with the semigroup law
and strong continuity. On a sampling function it is the dual series,
`T_t H_f = ∑_k H_{u_k(t)}` (`decisionWindowSemigroup_samplingFunction`), the sampling duality
(7.5) in Dyson form. Its generator on sampling functions is the forward generator (7.1): uniformly
on the simplex, `(T_t H_f - H_f)/t → L H_f` as `t ↓ 0` (`tendsto_decisionWindowSemigroup_slope`,
with `backwardFunction_apply` identifying the limit with `forwardGenerator`).

Scope. One finite window, a finite set of events and constant rates. The window semigroups are not
glued across windows here, and the limit is identified with the dual series on sampling functions,
which determine it.

## Empirical status

None. The bodies here are limits of bounded operators on continuous functions of a simplex and
bounds on Dyson components, so no measurement can bear on them.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Pangenome.AncestralLocality.DecisionWindowSemigroup

open Finset Filter Topology InfiniteGenomeLimit JumpFellerSemigroup DecisionJumpExpansion
  DecisionDysonDual DecisionWindowJumps
open scoped NNReal

noncomputable section

variable {H : Type*} [Fintype H] [DecidableEq H] {E : Type*} [Fintype E]

/-- The bounded operators on the continuous observables of the simplex form a normed ring. -/
local instance instNormedRingWindowOperator :
    NormedRing (C(SimplexLaw H, ℝ) →L[ℝ] C(SimplexLaw H, ℝ)) :=
  ContinuousLinearMap.toNormedRing

/-- The bounded operators on the continuous observables of the simplex form a normed algebra. -/
local instance instNormedAlgebraWindowOperator :
    NormedAlgebra ℝ (C(SimplexLaw H, ℝ) →L[ℝ] C(SimplexLaw H, ℝ)) :=
  ContinuousLinearMap.toNormedAlgebra

/-- The bounded operators on the continuous observables of the simplex form a topological ring. -/
local instance instIsTopologicalRingWindowOperator :
    IsTopologicalRing (C(SimplexLaw H, ℝ) →L[ℝ] C(SimplexLaw H, ℝ)) :=
  NonUnitalSeminormedRing.toIsTopologicalRing

/-! ## Time derivatives -/

/-- **The derivative of a jump operator with the generator on the right**,
`d/dt e^{t(J - λ)} = e^{t(J - λ)} (J - λ)`. -/
theorem hasDerivAt_jumpOperator_right (J : C(SimplexLaw H, ℝ) →L[ℝ] C(SimplexLaw H, ℝ))
    (rate t : ℝ) :
    HasDerivAt (jumpOperator J rate) (jumpOperator J rate t * (J - rate • 1)) t := by
  unfold jumpOperator
  exact hasDerivAt_exp_smul_const (J - rate • 1) t

/-- The derivative of a Dyson component, case by case. -/
def dysonDeriv (c : ℝ) (r : E → ℝ) (T : E → H → H → H) {n : ℕ} (f : (Fin n → H) → ℝ) :
    (k : ℕ) → ℝ → ((Fin (n + k) → H) → ℝ)
  | 0, t => coalescenceGain c (dysonTerm c r T f 0 t) - dualExitRate c r n • dysonTerm c r T f 0 t
  | k + 1, t => coalescenceGain c (dysonTerm c r T f (k + 1) t) -
      dualExitRate c r (n + (k + 1)) • dysonTerm c r T f (k + 1) t +
        @id ((Fin (n + (k + 1)) → H) → ℝ) (branchingGain r T (dysonTerm c r T f k t))

/-- **The Dyson components solve their equations**, case by case. -/
theorem hasDerivAt_dysonTerm (c : ℝ) (r : E → ℝ) (T : E → H → H → H) {n : ℕ}
    (f : (Fin n → H) → ℝ) (k : ℕ) (t : ℝ) :
    HasDerivAt (dysonTerm c r T f k) (dysonDeriv c r T f k t) t := by
  cases k with
  | zero => exact hasDerivAt_dysonTerm_zero c r T f t
  | succ k => exact hasDerivAt_dysonTerm_succ c r T f k t

/-- A sampling function of the zero observation vanishes. -/
theorem samplingFunction_zero {m : ℕ} : samplingFunction (0 : (Fin m → H) → ℝ) = 0 :=
  ContinuousMap.ext fun p ↦ by simp [samplingFunction_apply, samplingObservable]

/-- **The sampled derivatives telescope**: the derivatives of the first `K + 1` components read at
`p` are the backward generator applied to those components, minus the branching of the last. -/
theorem sum_samplingObservable_dysonDeriv (c : ℝ) (r : E → ℝ) (T : E → H → H → H) {n : ℕ}
    (f : (Fin n → H) → ℝ) (K : ℕ) (u : ℝ) (p : H → ℝ) :
    ∑ k ∈ range (K + 1), samplingObservable (dysonDeriv c r T f k u) p =
      ∑ k ∈ range (K + 1), backwardGenerator c r T (dysonTerm c r T f k u) p -
        samplingObservable (branchingGain r T (dysonTerm c r T f K u)) p := by
  induction K with
  | zero =>
    rw [sum_range_one, sum_range_one,
      ← samplingObservable_generator c r T (dysonTerm c r T f 0 u) p]
    have h0 : dysonDeriv c r T f 0 u = coalescenceGain c (dysonTerm c r T f 0 u) -
        dualExitRate c r n • dysonTerm c r T f 0 u := rfl
    rw [h0]
    ring
  | succ K ih =>
    rw [sum_range_succ, ih, sum_range_succ _ (K + 1)]
    have hd : samplingObservable (dysonDeriv c r T f (K + 1) u) p =
        samplingObservable (coalescenceGain c (dysonTerm c r T f (K + 1) u) -
          dualExitRate c r (n + (K + 1)) • dysonTerm c r T f (K + 1) u) p +
        samplingObservable (branchingGain r T (dysonTerm c r T f K u)) p :=
      samplingObservable_add _ _ p
    rw [hd, ← samplingObservable_generator c r T (dysonTerm c r T f (K + 1) u) p]
    ring

/-! ## The dual series -/

/-- **The partial dual series** `W_K(t) = ∑_{k ≤ K} H_{u_k(t)}`. -/
def partialDual (c : ℝ) (r : E → ℝ) (T : E → H → H → H) {n : ℕ} (f : (Fin n → H) → ℝ) (K : ℕ)
    (t : ℝ) : C(SimplexLaw H, ℝ) :=
  ∑ k ∈ range (K + 1), samplingFunction (dysonTerm c r T f k t)

/-- The derivative of the partial dual series. -/
def partialDualDeriv (c : ℝ) (r : E → ℝ) (T : E → H → H → H) {n : ℕ} (f : (Fin n → H) → ℝ)
    (K : ℕ) (t : ℝ) : C(SimplexLaw H, ℝ) :=
  ∑ k ∈ range (K + 1), samplingFunction (dysonDeriv c r T f k t)

/-- **The partial dual series moves along its derivative.** -/
theorem hasDerivAt_partialDual (c : ℝ) (r : E → ℝ) (T : E → H → H → H) {n : ℕ}
    (f : (Fin n → H) → ℝ) (K : ℕ) (t : ℝ) :
    HasDerivAt (partialDual c r T f K) (partialDualDeriv c r T f K t) t :=
  HasDerivAt.fun_sum fun k _ ↦ by
    have h := (samplingCLM (H := H) (n + k)).hasFDerivAt.comp_hasDerivAt t
      (hasDerivAt_dysonTerm c r T f k t)
    exact h

/-- At time zero the partial dual series is the sampling function of the observation. -/
theorem partialDual_zero (c : ℝ) (r : E → ℝ) (T : E → H → H → H) {n : ℕ}
    (f : (Fin n → H) → ℝ) (K : ℕ) : partialDual c r T f K 0 = samplingFunction f := by
  rw [partialDual, sum_range_succ']
  simp only [dysonTerm_succ_zero, samplingFunction_zero, sum_const_zero, zero_add]
  rw [dysonTerm_zero_zero]

/-- **A component is bounded by its Yule weight**, as a function on the simplex. -/
theorem norm_samplingFunction_dysonTerm_le {c : ℝ} (hc : 0 ≤ c) {r : E → ℝ} (hr : ∀ e, 0 ≤ r e)
    (T : E → H → H → H) {n : ℕ} (f : (Fin n → H) → ℝ) (k : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    ‖samplingFunction (dysonTerm c r T f k t)‖ ≤ yuleWeight n (∑ e, r e) k t * ‖f‖ :=
  (norm_samplingFunction_le _).trans (norm_dysonTerm_le hc hr T f k ht)

/-- **The dual series converges** at every nonnegative time. -/
theorem summable_dualTerm {c : ℝ} (hc : 0 ≤ c) {r : E → ℝ} (hr : ∀ e, 0 ≤ r e)
    (T : E → H → H → H) {n : ℕ} (f : (Fin n → H) → ℝ) {t : ℝ} (ht : 0 ≤ t) :
    Summable fun k ↦ samplingFunction (dysonTerm c r T f k t) := by
  have hR : 0 ≤ ∑ e, r e := sum_nonneg fun e _ ↦ hr e
  refine Summable.of_norm (summable_of_sum_range_le
    (c := yuleMoment n 0 * Real.exp (3 * (∑ e, r e) * t) * ‖f‖) (fun k ↦ norm_nonneg _)
      fun K ↦ ?_)
  calc ∑ k ∈ range K, ‖samplingFunction (dysonTerm c r T f k t)‖
      ≤ ∑ k ∈ range (K + 1), ‖samplingFunction (dysonTerm c r T f k t)‖ :=
        sum_le_sum_of_subset_of_nonneg (range_mono (Nat.le_succ K))
          fun _ _ _ ↦ norm_nonneg _
    _ ≤ ∑ k ∈ range (K + 1), yuleMoment n k * yuleWeight n (∑ e, r e) k t * ‖f‖ :=
        sum_le_sum fun k _ ↦ (norm_samplingFunction_dysonTerm_le hc hr T f k ht).trans
          (mul_le_mul_of_nonneg_right (le_mul_of_one_le_left (yuleWeight_nonneg (n := n) hR k ht)
            (one_le_yuleMoment n k)) (norm_nonneg f))
    _ = (∑ k ∈ range (K + 1), yuleMoment n k * yuleWeight n (∑ e, r e) k t) * ‖f‖ := by
        rw [sum_mul]
    _ ≤ yuleMoment n 0 * Real.exp (3 * (∑ e, r e) * t) * ‖f‖ :=
        mul_le_mul_of_nonneg_right (sum_yuleMoment_mul_le (n := n) hR K ht) (norm_nonneg f)

/-- **The dual series** `∑_k H_{u_k(t)}` of an observation. -/
def dualSeries (c : ℝ) (r : E → ℝ) (T : E → H → H → H) {n : ℕ} (f : (Fin n → H) → ℝ) (t : ℝ) :
    C(SimplexLaw H, ℝ) :=
  ∑' k, samplingFunction (dysonTerm c r T f k t)

/-- The partial sums converge to the dual series. -/
theorem tendsto_partialDual {c : ℝ} (hc : 0 ≤ c) {r : E → ℝ} (hr : ∀ e, 0 ≤ r e)
    (T : E → H → H → H) {n : ℕ} (f : (Fin n → H) → ℝ) {t : ℝ} (ht : 0 ≤ t) :
    Tendsto (fun K ↦ partialDual c r T f K t) atTop (𝓝 (dualSeries c r T f t)) :=
  ((summable_dualTerm hc hr T f ht).hasSum.tendsto_sum_nat).comp (tendsto_add_atTop_nat 1)

/-! ## The jump approximations against the dual series -/

/-- **The jump approximation against a partial dual series.** For `0 < ε ≤ 1`, `0 ≤ t ≤ T₀` and
`R = ∑_e r_e`, `‖e^{t(J - λ)} H_f - W_K(t)‖ ≤ t (4 (c + R) ε + R/(K + 1)) w_0 e^{3RT₀} ‖f‖`. -/
theorem norm_jumpOperator_sub_partialDual_le {c : ℝ} (hc : 0 ≤ c) {r : E → ℝ}
    (hr : ∀ e, 0 ≤ r e) (T : E → H → H → H) {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) {n : ℕ}
    (f : (Fin n → H) → ℝ) (K : ℕ) {t T₀ : ℝ} (ht : 0 ≤ t) (htT : t ≤ T₀) :
    ‖jumpOperator (jumpGenerator c r T hε0.le hε1) (jumpRate c r ε) t (samplingFunction f) -
        partialDual c r T f K t‖ ≤
      (4 * (c + ∑ e, r e) * ε + (∑ e, r e) * (1 / ((K : ℝ) + 1))) *
        (yuleMoment n 0 * Real.exp (3 * (∑ e, r e) * T₀) * ‖f‖) * t := by
  have hR : 0 ≤ ∑ e, r e := sum_nonneg fun e _ ↦ hr e
  set J := jumpGenerator c r T hε0.le hε1 with hJ
  set rate := jumpRate c r ε with hrate
  set C := (4 * (c + ∑ e, r e) * ε + (∑ e, r e) * (1 / ((K : ℝ) + 1))) *
    (yuleMoment n 0 * Real.exp (3 * (∑ e, r e) * T₀) * ‖f‖) with hC
  have hpos : ∀ g : C(SimplexLaw H, ℝ), 0 ≤ g → 0 ≤ J g :=
    fun _ hg ↦ jumpGenerator_nonneg hc hr T hε0.le hε1 hg
  have hone : J 1 = rate • 1 := jumpGenerator_one c r T hε0.le hε1
  have hψ : ∀ s, HasDerivAt (fun s ↦ jumpOperator J rate s (partialDual c r T f K (t - s)))
      (jumpOperator J rate s ((J - rate • 1) (partialDual c r T f K (t - s)) -
        partialDualDeriv c r T f K (t - s))) s := by
    intro s
    have h2 : HasDerivAt (fun s ↦ partialDual c r T f K (t - s))
        (-partialDualDeriv c r T f K (t - s)) s := by
      convert HasDerivAt.scomp (hg := hasDerivAt_partialDual c r T f K (t - s))
        (hh := (hasDerivAt_id' (x := s)).const_sub t) using 1
      simp
    have h3 := HasDerivAt.clm_apply (hasDerivAt_jumpOperator_right J rate s) h2
    convert h3 using 1
    rw [ContinuousLinearMap.mul_apply, ← map_add, sub_eq_add_neg]
  have hbound : ∀ s ∈ Set.Ico (0 : ℝ) t,
      ‖jumpOperator J rate s ((J - rate • 1) (partialDual c r T f K (t - s)) -
        partialDualDeriv c r T f K (t - s))‖ ≤ C := by
    intro s hs
    refine (norm_jumpOperator_apply_le hpos hone hs.1 _).trans ?_
    have hu0 : 0 ≤ t - s := by linarith [hs.2]
    have huT : t - s ≤ T₀ := by linarith [hs.1]
    have hexp : Real.exp (3 * (∑ e, r e) * (t - s)) ≤ Real.exp (3 * (∑ e, r e) * T₀) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left huT (mul_nonneg (by norm_num) hR))
    have hCnn : 0 ≤ C := by
      rw [hC]
      refine mul_nonneg (add_nonneg ?_ (mul_nonneg hR (by positivity)))
        (mul_nonneg (mul_nonneg (zero_le_one.trans (one_le_yuleMoment n 0))
          (Real.exp_pos _).le) (norm_nonneg f))
      exact mul_nonneg (mul_nonneg (by norm_num) (add_nonneg hc hR)) hε0.le
    refine (ContinuousMap.norm_le _ hCnn).mpr fun p ↦ ?_
    have hval : ((J - rate • 1) (partialDual c r T f K (t - s)) -
        partialDualDeriv c r T f K (t - s)) p =
          ∑ k ∈ range (K + 1), ((J - rate • 1) (samplingFunction (dysonTerm c r T f k (t - s))) p -
            backwardGenerator c r T (dysonTerm c r T f k (t - s)) p.1) +
          samplingObservable (branchingGain r T (dysonTerm c r T f K (t - s))) p.1 := by
      simp only [partialDual, partialDualDeriv, map_sum, ContinuousMap.sub_apply,
        ContinuousMap.sum_apply, samplingFunction_apply]
      rw [sum_samplingObservable_dysonDeriv c r T f K (t - s) p.1, sum_sub_distrib]
      ring
    rw [hval, Real.norm_eq_abs]
    have hfirst : |∑ k ∈ range (K + 1), ((J - rate • 1)
        (samplingFunction (dysonTerm c r T f k (t - s))) p -
          backwardGenerator c r T (dysonTerm c r T f k (t - s)) p.1)| ≤
        4 * (c + ∑ e, r e) * ε * (yuleMoment n 0 * Real.exp (3 * (∑ e, r e) * T₀) * ‖f‖) := by
      refine (abs_sum_le_sum_abs _ _).trans ?_
      calc ∑ k ∈ range (K + 1), |(J - rate • 1)
            (samplingFunction (dysonTerm c r T f k (t - s))) p -
              backwardGenerator c r T (dysonTerm c r T f k (t - s)) p.1|
          ≤ ∑ k ∈ range (K + 1), 4 * (c + ∑ e, r e) * ε *
              (yuleMoment n k * yuleWeight n (∑ e, r e) k (t - s) * ‖f‖) := by
            refine sum_le_sum fun k _ ↦ ?_
            refine (abs_jumpGenerator_sub_le hc hr T hε0 hε1
              (dysonTerm c r T f k (t - s)) p).trans ?_
            have hk := norm_dysonTerm_le hc hr T f k hu0
            have hcube : ((n + k : ℕ) : ℝ) ^ 3 ≤ yuleMoment n k := by
              push_cast
              exact pow_three_le_yuleMoment n k
            have hconst : 0 ≤ 4 * (c + ∑ e, r e) * ε :=
              mul_nonneg (mul_nonneg (by norm_num) (add_nonneg hc hR)) hε0.le
            calc 4 * (c + ∑ e, r e) * ε * ((n + k : ℕ) : ℝ) ^ 3 *
                  ‖dysonTerm c r T f k (t - s)‖
                ≤ 4 * (c + ∑ e, r e) * ε * yuleMoment n k *
                    (yuleWeight n (∑ e, r e) k (t - s) * ‖f‖) :=
                  mul_le_mul (mul_le_mul_of_nonneg_left hcube hconst) hk (norm_nonneg _)
                    (mul_nonneg hconst (zero_le_one.trans (one_le_yuleMoment n k)))
              _ = 4 * (c + ∑ e, r e) * ε *
                    (yuleMoment n k * yuleWeight n (∑ e, r e) k (t - s) * ‖f‖) := by ring
        _ = 4 * (c + ∑ e, r e) * ε *
              ((∑ k ∈ range (K + 1), yuleMoment n k * yuleWeight n (∑ e, r e) k (t - s)) *
                ‖f‖) := by
            rw [← mul_sum, sum_mul]
        _ ≤ 4 * (c + ∑ e, r e) * ε *
              (yuleMoment n 0 * Real.exp (3 * (∑ e, r e) * T₀) * ‖f‖) := by
            refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right ?_ (norm_nonneg f))
              (mul_nonneg (mul_nonneg (by norm_num) (add_nonneg hc hR)) hε0.le)
            exact (sum_yuleMoment_mul_le (n := n) hR K hu0).trans (mul_le_mul_of_nonneg_left hexp
              (zero_le_one.trans (one_le_yuleMoment n 0)))
    have hsecond : |samplingObservable (branchingGain r T (dysonTerm c r T f K (t - s))) p.1| ≤
        (∑ e, r e) * (1 / ((K : ℝ) + 1)) *
          (yuleMoment n 0 * Real.exp (3 * (∑ e, r e) * T₀) * ‖f‖) := by
      refine (abs_samplingObservable_le _ p.2).trans ?_
      refine (norm_branchingGain_le hr T _).trans ?_
      have hK := norm_dysonTerm_le hc hr T f K hu0
      have hy := yuleWeight_nonneg (n := n) hR K hu0
      have hmoment := yuleMoment_mul_yuleWeight_le (n := n) hR K hu0
      have harity : ((n + K : ℕ) : ℝ) * ((K : ℝ) + 1) ≤ yuleMoment n K := by
        unfold yuleMoment
        push_cast
        have h0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
        have h1 : (0 : ℝ) ≤ K := Nat.cast_nonneg K
        nlinarith [mul_nonneg h0 h1, mul_nonneg h0 h0, mul_nonneg h1 h1,
          mul_nonneg (mul_nonneg h0 h1) h1, mul_nonneg (mul_nonneg h0 h0) h1,
          mul_nonneg (mul_nonneg h0 h0) h0, mul_nonneg (mul_nonneg h1 h1) h1]
      have hK1 : (0 : ℝ) < (K : ℝ) + 1 := by positivity
      have hy' : ((n + K : ℕ) : ℝ) * yuleWeight n (∑ e, r e) K (t - s) ≤
          (1 / ((K : ℝ) + 1)) * (yuleMoment n 0 * Real.exp (3 * (∑ e, r e) * T₀)) := by
        rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ hK1]
        calc ((n + K : ℕ) : ℝ) * yuleWeight n (∑ e, r e) K (t - s) * ((K : ℝ) + 1)
            = ((n + K : ℕ) : ℝ) * ((K : ℝ) + 1) * yuleWeight n (∑ e, r e) K (t - s) := by ring
          _ ≤ yuleMoment n K * yuleWeight n (∑ e, r e) K (t - s) :=
              mul_le_mul_of_nonneg_right harity hy
          _ ≤ yuleMoment n 0 * Real.exp (3 * (∑ e, r e) * (t - s)) := hmoment
          _ ≤ yuleMoment n 0 * Real.exp (3 * (∑ e, r e) * T₀) :=
              mul_le_mul_of_nonneg_left hexp (zero_le_one.trans (one_le_yuleMoment n 0))
      calc (((n + K : ℕ) : ℝ) * ∑ e, r e) * ‖dysonTerm c r T f K (t - s)‖
          ≤ (((n + K : ℕ) : ℝ) * ∑ e, r e) * (yuleWeight n (∑ e, r e) K (t - s) * ‖f‖) :=
            mul_le_mul_of_nonneg_left hK (mul_nonneg (Nat.cast_nonneg _) hR)
        _ = (∑ e, r e) * (((n + K : ℕ) : ℝ) * yuleWeight n (∑ e, r e) K (t - s)) * ‖f‖ := by
            ring
        _ ≤ (∑ e, r e) * ((1 / ((K : ℝ) + 1)) *
              (yuleMoment n 0 * Real.exp (3 * (∑ e, r e) * T₀))) * ‖f‖ :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hy' hR) (norm_nonneg f)
        _ = (∑ e, r e) * (1 / ((K : ℝ) + 1)) *
              (yuleMoment n 0 * Real.exp (3 * (∑ e, r e) * T₀) * ‖f‖) := by ring
    refine (abs_add_le _ _).trans ?_
    rw [hC, add_mul]
    exact add_le_add hfirst hsecond
  have hmv := norm_image_sub_le_of_norm_deriv_le_segment'
    (fun s _ ↦ (hψ s).hasDerivWithinAt) hbound t (Set.right_mem_Icc.mpr ht)
  simp only [sub_self, partialDual_zero, jumpOperator_zero, ContinuousLinearMap.id_apply,
    sub_zero] at hmv
  exact hmv

/-- **The jump approximation against the dual series**: for `0 < ε ≤ 1` and `0 ≤ t ≤ T₀`,
`‖e^{t(J - λ)} H_f - ∑_k H_{u_k(t)}‖ ≤ 4 (c + R) ε w_0 e^{3RT₀} ‖f‖ t`. -/
theorem norm_jumpOperator_sub_dualSeries_le {c : ℝ} (hc : 0 ≤ c) {r : E → ℝ}
    (hr : ∀ e, 0 ≤ r e) (T : E → H → H → H) {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) {n : ℕ}
    (f : (Fin n → H) → ℝ) {t T₀ : ℝ} (ht : 0 ≤ t) (htT : t ≤ T₀) :
    ‖jumpOperator (jumpGenerator c r T hε0.le hε1) (jumpRate c r ε) t (samplingFunction f) -
        dualSeries c r T f t‖ ≤
      4 * (c + ∑ e, r e) * ε * (yuleMoment n 0 * Real.exp (3 * (∑ e, r e) * T₀) * ‖f‖) * t := by
  have hlim : Tendsto (fun K : ℕ ↦ ‖jumpOperator (jumpGenerator c r T hε0.le hε1)
      (jumpRate c r ε) t (samplingFunction f) - partialDual c r T f K t‖) atTop
      (𝓝 ‖jumpOperator (jumpGenerator c r T hε0.le hε1) (jumpRate c r ε) t
        (samplingFunction f) - dualSeries c r T f t‖) :=
    (tendsto_const_nhds.sub (tendsto_partialDual hc hr T f ht)).norm
  have hK : Tendsto (fun K : ℕ ↦ (4 * (c + ∑ e, r e) * ε + (∑ e, r e) * (1 / ((K : ℝ) + 1))) *
      (yuleMoment n 0 * Real.exp (3 * (∑ e, r e) * T₀) * ‖f‖) * t) atTop
      (𝓝 ((4 * (c + ∑ e, r e) * ε + (∑ e, r e) * 0) *
        (yuleMoment n 0 * Real.exp (3 * (∑ e, r e) * T₀) * ‖f‖) * t)) :=
    (((tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (∑ e, r e)).const_add
      (4 * (c + ∑ e, r e) * ε)).mul_const _).mul_const t
  rw [mul_zero, add_zero] at hK
  exact le_of_tendsto_of_tendsto' hlim hK fun K ↦
    norm_jumpOperator_sub_partialDual_le hc hr T hε0 hε1 f K ht htT

/-! ## The forward semigroup -/

/-- The steps `ε_m = 1/(m + 1)` of the jump approximations. -/
def stepSize (m : ℕ) : ℝ :=
  1 / ((m : ℝ) + 1)

theorem stepSize_pos (m : ℕ) : 0 < stepSize m := by
  unfold stepSize
  positivity

theorem stepSize_le_one (m : ℕ) : stepSize m ≤ 1 := by
  unfold stepSize
  rw [div_le_one (by positivity)]
  linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]

theorem stepSize_antitone {m m' : ℕ} (h : m ≤ m') : stepSize m' ≤ stepSize m := by
  unfold stepSize
  refine one_div_le_one_div_of_le (by positivity) ?_
  exact_mod_cast Nat.succ_le_succ h

/-- **The jump approximations** at the steps `ε_m`. -/
def decisionApproximations {c : ℝ} (hc : 0 ≤ c) {r : E → ℝ} (hr : ∀ e, 0 ≤ r e)
    (T : E → H → H → H) (m : ℕ) : FellerSemigroup (SimplexLaw H) :=
  jumpApproximation hc hr T (stepSize_pos m).le (stepSize_le_one m)

/-- The approximation at step `ε_m` against the dual series. -/
theorem norm_decisionApproximations_sub_le {c : ℝ} (hc : 0 ≤ c) {r : E → ℝ}
    (hr : ∀ e, 0 ≤ r e) (T : E → H → H → H) (m : ℕ) {n : ℕ} (f : (Fin n → H) → ℝ)
    {t T₀ : ℝ≥0} (htT : t ≤ T₀) :
    ‖(decisionApproximations hc hr T m).operator t (samplingFunction f) - dualSeries c r T f t‖ ≤
      4 * (c + ∑ e, r e) * stepSize m *
        (yuleMoment n 0 * Real.exp (3 * (∑ e, r e) * T₀) * ‖f‖) * T₀ := by
  have h := norm_jumpOperator_sub_dualSeries_le hc hr T (stepSize_pos m) (stepSize_le_one m) f
    (NNReal.coe_nonneg t) (NNReal.coe_le_coe.mpr htT)
  refine h.trans (mul_le_mul_of_nonneg_left (NNReal.coe_le_coe.mpr htT) ?_)
  exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (add_nonneg hc
    (sum_nonneg fun e _ ↦ hr e))) (stepSize_pos m).le)
    (mul_nonneg (mul_nonneg (zero_le_one.trans (one_le_yuleMoment n 0)) (Real.exp_pos _).le)
      (norm_nonneg f))

open scoped Classical in
/-- **The uniform approximation bound** of the jump approximations on the polynomials in the
frequencies: later approximations stay within `2 ‖F‖` times an escape term that vanishes with the
step. -/
def decisionLightConeApproximation {c : ℝ} (hc : 0 ≤ c) {r : E → ℝ} (hr : ∀ e, 0 ≤ r e)
    (T : E → H → H → H) :
    LightConeApproximation (decisionApproximations hc hr T) (windowPolynomialAlgebra H) where
  escape F T₀ m :=
    if h : ∃ (n : ℕ) (f : (Fin n → H) → ℝ), samplingFunction f = F then
      8 * (c + ∑ e, r e) * stepSize m * (yuleMoment (Classical.choose h) 0 *
        Real.exp (3 * (∑ e, r e) * T₀) * ‖Classical.choose (Classical.choose_spec h)‖) * T₀ /
          (2 * ‖F‖)
    else 0
  escape_tendsto F hF T₀ := by
    have h := exists_samplingFunction_eq hF
    simp only [dif_pos h]
    have hstep : Tendsto stepSize atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
    have hlim := ((((hstep.const_mul (8 * (c + ∑ e, r e))).mul_const
      (yuleMoment (Classical.choose h) 0 * Real.exp (3 * (∑ e, r e) * T₀) *
        ‖Classical.choose (Classical.choose_spec h)‖)).mul_const (T₀ : ℝ)).div_const
      (2 * ‖F‖))
    simpa using hlim
  norm_sub_le F hF T₀ t htT m m' hmm' := by
    have h := exists_samplingFunction_eq hF
    rw [dif_pos h]
    set n := Classical.choose h with hn
    set f := Classical.choose (Classical.choose_spec h) with hf
    have hfF : samplingFunction f = F := Classical.choose_spec (Classical.choose_spec h)
    by_cases hF0 : ‖F‖ = 0
    · have hzero : F = 0 := norm_eq_zero.mp hF0
      have h0m : (decisionApproximations hc hr T m).operator t F = 0 := by rw [hzero, map_zero]
      have h0m' : (decisionApproximations hc hr T m').operator t F = 0 := by
        rw [hzero, map_zero]
      rw [h0m, h0m', sub_zero, norm_zero, hF0]
      simp
    · have hpos : 0 < 2 * ‖F‖ := mul_pos two_pos ((norm_nonneg F).lt_of_ne (Ne.symm hF0))
      have hm1 : (decisionApproximations hc hr T m).operator t F =
          (decisionApproximations hc hr T m).operator t (samplingFunction f) := by rw [hfF]
      have hm2 : (decisionApproximations hc hr T m').operator t F =
          (decisionApproximations hc hr T m').operator t (samplingFunction f) := by rw [hfF]
      rw [← mul_div_assoc, mul_div_cancel_left₀ _ hpos.ne', hm1, hm2]
      have h1 := norm_decisionApproximations_sub_le hc hr T m f htT
      have h2 := norm_decisionApproximations_sub_le hc hr T m' f htT
      have hstep := stepSize_antitone hmm'
      have hX : 0 ≤ yuleMoment n 0 * Real.exp (3 * (∑ e, r e) * T₀) * ‖f‖ :=
        mul_nonneg (mul_nonneg (zero_le_one.trans (one_le_yuleMoment n 0)) (Real.exp_pos _).le)
          (norm_nonneg f)
      have hcR : 0 ≤ 4 * (c + ∑ e, r e) :=
        mul_nonneg (by norm_num) (add_nonneg hc (sum_nonneg fun e _ ↦ hr e))
      have hmono : 4 * (c + ∑ e, r e) * stepSize m' *
          (yuleMoment n 0 * Real.exp (3 * (∑ e, r e) * T₀) * ‖f‖) * T₀ ≤
            4 * (c + ∑ e, r e) * stepSize m *
              (yuleMoment n 0 * Real.exp (3 * (∑ e, r e) * T₀) * ‖f‖) * T₀ :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hstep hcR) hX) (NNReal.coe_nonneg T₀)
      calc ‖(decisionApproximations hc hr T m).operator t (samplingFunction f) -
            (decisionApproximations hc hr T m').operator t (samplingFunction f)‖
          ≤ ‖(decisionApproximations hc hr T m).operator t (samplingFunction f) -
              dualSeries c r T f t‖ +
            ‖(decisionApproximations hc hr T m').operator t (samplingFunction f) -
              dualSeries c r T f t‖ := by
            rw [norm_sub_rev ((decisionApproximations hc hr T m').operator t
              (samplingFunction f))]
            exact norm_sub_le_norm_sub_add_norm_sub _ _ _
        _ ≤ 8 * (c + ∑ e, r e) * stepSize m *
              (yuleMoment n 0 * Real.exp (3 * (∑ e, r e) * T₀) * ‖f‖) * T₀ := by
            linarith

/-- **The forward semigroup of a finite window with decisions**: the limit of the jump
approximations, a Feller semigroup on the laws of the window. -/
def decisionWindowSemigroup {c : ℝ} (hc : 0 ≤ c) {r : E → ℝ} (hr : ∀ e, 0 ≤ r e)
    (T : E → H → H → H) : FellerSemigroup (SimplexLaw H) :=
  limitSemigroup windowPolynomialAlgebra_separatesPoints (decisionLightConeApproximation hc hr T)

/-- **The sampling duality (7.5) in Dyson form.** On a sampling function the forward semigroup is
the dual series, `T_t H_f = ∑_k H_{u_k(t)}`. -/
theorem decisionWindowSemigroup_samplingFunction {c : ℝ} (hc : 0 ≤ c) {r : E → ℝ}
    (hr : ∀ e, 0 ≤ r e) (T : E → H → H → H) (t : ℝ≥0) {n : ℕ} (f : (Fin n → H) → ℝ) :
    (decisionWindowSemigroup hc hr T).operator t (samplingFunction f) = dualSeries c r T f t := by
  refine tendsto_nhds_unique (tendsto_limitSemigroup windowPolynomialAlgebra_separatesPoints
    (decisionLightConeApproximation hc hr T) t (samplingFunction f)) ?_
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hstep : Tendsto stepSize atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hlim := ((hstep.const_mul (4 * (c + ∑ e, r e))).mul_const
    (yuleMoment n 0 * Real.exp (3 * (∑ e, r e) * t) * ‖f‖)).mul_const (t : ℝ)
  rw [mul_zero, zero_mul, zero_mul] at hlim
  exact squeeze_zero (fun _ ↦ norm_nonneg _)
    (fun m ↦ norm_decisionApproximations_sub_le hc hr T m f le_rfl) hlim

/-! ## The generator on sampling functions -/

/-- **The backward generator as a continuous function**:
`p ↦ H_{(P - λ) f}(p) + H_{G f}(p)`. -/
def backwardFunction (c : ℝ) (r : E → ℝ) (T : E → H → H → H) {n : ℕ} (f : (Fin n → H) → ℝ) :
    C(SimplexLaw H, ℝ) :=
  samplingFunction (coalescenceGain c f - dualExitRate c r n • f) +
    samplingFunction (branchingGain r T f)

/-- **The backward function is the forward generator (7.1)** of the sampling observable, at every
law. -/
theorem backwardFunction_apply (c : ℝ) (r : E → ℝ) (T : E → H → H → H) {n : ℕ}
    (f : (Fin n → H) → ℝ) (p : SimplexLaw H) :
    backwardFunction c r T f p = forwardGenerator c r T (samplingObservable f) p.1 := by
  rw [backwardFunction, ContinuousMap.add_apply, samplingFunction_apply, samplingFunction_apply,
    samplingObservable_generator, forwardGenerator_samplingObservable c r T f p.2.2]

/-- The jump generator on a sampling function is the backward function up to
`4 (c + R) ε n³ ‖f‖`. -/
theorem norm_jumpGenerator_sub_backwardFunction_le {c : ℝ} (hc : 0 ≤ c) {r : E → ℝ}
    (hr : ∀ e, 0 ≤ r e) (T : E → H → H → H) {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) {n : ℕ}
    (f : (Fin n → H) → ℝ) :
    ‖(jumpGenerator c r T hε0.le hε1 - jumpRate c r ε • 1) (samplingFunction f) -
        backwardFunction c r T f‖ ≤ 4 * (c + ∑ e, r e) * ε * (n : ℝ) ^ 3 * ‖f‖ := by
  refine (ContinuousMap.norm_le _ (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg
    (by norm_num) (add_nonneg hc (sum_nonneg fun e _ ↦ hr e))) hε0.le) (by positivity))
      (norm_nonneg f))).mpr fun p ↦ ?_
  rw [ContinuousMap.sub_apply, Real.norm_eq_abs, backwardFunction_apply,
    forwardGenerator_samplingObservable c r T f p.2.2]
  exact abs_jumpGenerator_sub_le hc hr T hε0 hε1 f p

/-- **The generator of the forward semigroup on sampling functions is (7.1).** Uniformly on the
simplex, `(T_t H_f - H_f)/t` tends to the forward generator of `H_f` as `t ↓ 0`. -/
theorem tendsto_decisionWindowSemigroup_slope {c : ℝ} (hc : 0 ≤ c) {r : E → ℝ}
    (hr : ∀ e, 0 ≤ r e) (T : E → H → H → H) {n : ℕ} (f : (Fin n → H) → ℝ) :
    Tendsto (fun t : ℝ ↦ t⁻¹ • ((decisionWindowSemigroup hc hr T).operator t.toNNReal
      (samplingFunction f) - samplingFunction f)) (𝓝[>] 0) (𝓝 (backwardFunction c r T f)) := by
  set R := ∑ e, r e with hRdef
  have hR : 0 ≤ R := sum_nonneg fun e _ ↦ hr e
  set X := yuleMoment n 0 * Real.exp (3 * R * 1) * ‖f‖ with hX
  have hXnn : 0 ≤ X := mul_nonneg (mul_nonneg (zero_le_one.trans (one_le_yuleMoment n 0))
    (Real.exp_pos _).le) (norm_nonneg f)
  refine Metric.tendsto_nhds.mpr fun δ hδ ↦ ?_
  have hstep : Tendsto (fun m : ℕ ↦ 4 * (c + R) * stepSize m * (X + (n : ℝ) ^ 3 * ‖f‖)) atTop
      (𝓝 0) := by
    have hone : Tendsto (fun m : ℕ ↦ 1 / ((m : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have h := (hone.const_mul (4 * (c + R))).mul_const (X + (n : ℝ) ^ 3 * ‖f‖)
    simpa [stepSize] using h
  obtain ⟨m, hm⟩ := (hstep.eventually (gt_mem_nhds (by positivity : 0 < δ / 2))).exists
  set J := jumpGenerator c r T (stepSize_pos m).le (stepSize_le_one m) with hJ
  set rate := jumpRate c r (stepSize m) with hrate
  have hderiv : HasDerivAt (fun u : ℝ ↦ jumpOperator J rate u (samplingFunction f))
      ((J - rate • 1) (samplingFunction f)) 0 := by
    have h := HasDerivAt.clm_apply (hasDerivAt_jumpOperator J rate 0)
      (hasDerivAt_const (x := (0 : ℝ)) (c := samplingFunction f))
    convert h using 1
    rw [ContinuousLinearMap.map_zero, add_zero, ContinuousLinearMap.mul_apply,
      jumpOperator_zero, ContinuousLinearMap.id_apply]
  have hslope := hderiv.tendsto_slope_zero_right
  have hgen := norm_jumpGenerator_sub_backwardFunction_le hc hr T (stepSize_pos m)
    (stepSize_le_one m) f
  filter_upwards [Metric.tendsto_nhds.mp hslope (δ / 2) (by positivity), self_mem_nhdsWithin,
    eventually_nhdsWithin_of_eventually_nhds (eventually_lt_nhds zero_lt_one)]
    with t ht1 ht2 ht3
  have htpos : 0 < t := ht2
  have hcoe : (t.toNNReal : ℝ) = t := Real.coe_toNNReal t htpos.le
  have happrox := norm_jumpOperator_sub_dualSeries_le hc hr T (stepSize_pos m)
    (stepSize_le_one m) f htpos.le ht3.le
  rw [decisionWindowSemigroup_samplingFunction, hcoe]
  simp only [zero_add, jumpOperator_zero, ContinuousLinearMap.id_apply] at ht1
  rw [dist_eq_norm] at ht1 ⊢
  have hdecomp : t⁻¹ • (dualSeries c r T f t - samplingFunction f) - backwardFunction c r T f =
      t⁻¹ • (dualSeries c r T f t - jumpOperator J rate t (samplingFunction f)) +
        (t⁻¹ • (jumpOperator J rate t (samplingFunction f) - samplingFunction f) -
          (J - rate • 1) (samplingFunction f)) +
        ((J - rate • 1) (samplingFunction f) - backwardFunction c r T f) := by
    module
  rw [hdecomp]
  have hfirst : ‖t⁻¹ • (dualSeries c r T f t - jumpOperator J rate t (samplingFunction f))‖ ≤
      4 * (c + R) * stepSize m * X := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr htpos), norm_sub_rev,
      inv_mul_le_iff₀ htpos]
    calc ‖jumpOperator J rate t (samplingFunction f) - dualSeries c r T f t‖
        ≤ 4 * (c + R) * stepSize m * X * t := happrox
      _ = t * (4 * (c + R) * stepSize m * X) := by ring
  have hthird : ‖(J - rate • 1) (samplingFunction f) - backwardFunction c r T f‖ ≤
      4 * (c + R) * stepSize m * ((n : ℝ) ^ 3 * ‖f‖) := by
    calc ‖(J - rate • 1) (samplingFunction f) - backwardFunction c r T f‖
        ≤ 4 * (c + R) * stepSize m * (n : ℝ) ^ 3 * ‖f‖ := hgen
      _ = 4 * (c + R) * stepSize m * ((n : ℝ) ^ 3 * ‖f‖) := by ring
  calc ‖t⁻¹ • (dualSeries c r T f t - jumpOperator J rate t (samplingFunction f)) +
        (t⁻¹ • (jumpOperator J rate t (samplingFunction f) - samplingFunction f) -
          (J - rate • 1) (samplingFunction f)) +
        ((J - rate • 1) (samplingFunction f) - backwardFunction c r T f)‖
      ≤ ‖t⁻¹ • (dualSeries c r T f t - jumpOperator J rate t (samplingFunction f))‖ +
          ‖t⁻¹ • (jumpOperator J rate t (samplingFunction f) - samplingFunction f) -
            (J - rate • 1) (samplingFunction f)‖ +
          ‖(J - rate • 1) (samplingFunction f) - backwardFunction c r T f‖ :=
        norm_add₃_le
    _ < δ := by
        have hsum : 4 * (c + R) * stepSize m * X + 4 * (c + R) * stepSize m * ((n : ℝ) ^ 3 * ‖f‖) =
            4 * (c + R) * stepSize m * (X + (n : ℝ) ^ 3 * ‖f‖) := by ring
        linarith

end

end Descent.Pangenome.AncestralLocality.DecisionWindowSemigroup
