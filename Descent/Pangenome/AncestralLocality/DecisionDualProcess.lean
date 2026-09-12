/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Pangenome.AncestralLocality.CoalescentDualSemigroup
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.UniformSpace.UniformApproximation

assert_below Descent.PopGen Descent.Spectral Descent.Blindness Descent.Conditionals
assert_below Descent.Portability Descent.Decision Descent.Program

/-!
# The backward decision circuit: existence of the dual expectation

Theorem 6 of the research note "Ancestral locality" is the sampling duality (7.5),
`E_p[H_f(P_t)] = E_f[H_{f_t}(p)]`. `Descent.Pangenome.AncestralLocality.SamplingDuality` proves
the generator identity behind it: the forward generator on `H_f` is the backward generator applied
to `f`, a jump generator whose exit rate from `n` arguments is `c d_n + n R` (`dualExitRate_eq`).
This file constructs the right-hand side of (7.5) for decisions at rates `r ≥ 0`, as the limit of
the circuit killed at its `M`-th decision, and proves that it solves the moment equation.

## The circuit between decisions

Coalescence keeps the arity, so between two decisions the circuit is a finite linear flow. The
holding generator `holdingGenerator c r n` is `c ∑_{a<b} C_ab - (c d_n + n R)`: coalescence at
rate `c` per pair (`pairSubstitution`), with the whole exit rate on the diagonal, so that a
decision removes mass. Its exponential `holdingSemigroup c r n t` moves every observation along
the generator (`hasDerivAt_holdingSemigroup_apply`), satisfies `S_{-u} S_t = S_{t-u}`
(`holdingSemigroup_neg_mul`) and contracts at the decision rate, `‖S_t f‖ ≤ e^{-nRt} ‖f‖` for
`c ≥ 0`, `r ≥ 0` and `t ≥ 0` (`norm_holdingSemigroup_apply_le`). A decision acts through
`decisionSubstitution r T n`, `f ↦ ∑_e r_e ∑_a B_{a,e} f`, which raises the arity by one and has
norm at most `n R` (`norm_decisionSubstitution_le`).

## The Dyson terms

`dysonMoment c r T p k n t f` is the expectation of `H_{f_t}(p)` on the runs of the circuit that
take exactly `k` decisions by time `t`: `H_{S_t f}(p)` for `k = 0` (`dysonMoment_zero_apply`),
and for `k + 1` the integral over the time of the first decision of the term of arity `n + 1`,
`d_{k+1}(t, f) = ∫_0^t d_k(u, B S_{t-u} f) du` (`dysonMoment_succ_eq_integral`). It is written
against the indicators of the tuples, so it is linear by construction. Every term is continuous in
time (`continuous_dysonMoment_apply`) and has derivative `d_{k+1}(t, K f) + d_k(t, B f)`
(`hasDerivAt_dysonMoment_zero`, `hasDerivAt_dysonMoment_succ`).

## The number of decisions

`yuleWeight R k n t` is the probability that a Yule process in which each argument branches at
rate `R`, started from `n` arguments, has exactly `k` births by time `t`. Every Dyson term is at
most its Yule weight times the sup norm (`abs_dysonMoment_le`). The weights have mass at most one
(`sum_range_yuleWeight_le_one`), and `(n + M)(1 - ∑_{k<M} w_k) ≤ n e^{Rt}`
(`mul_one_sub_sum_range_yuleWeight_le`): at least `M` decisions by time `t` have probability at
most `n e^{Rt} / (n + M)`. So the weights sum to one (`tsum_yuleWeight_eq_one`), and the circuit,
with its linear birth rate, does not explode.

## The dual expectation and the moment equation

`truncatedDual c r T p M n t f` is the dual expectation of the circuit killed at its `M`-th
decision, and `decisionDual c r T p n t f`, the sum of all Dyson terms, is `E_f[H_{f_t}(p)]`. For
`c ≥ 0`, `r ≥ 0`, a probability vector `p` and `t ≥ 0` the truncated circuits converge to it
(`tendsto_truncatedDual`) within `n e^{Rt} ‖f‖ / (n + M)`
(`abs_decisionDual_sub_truncatedDual_le_exp`), uniformly on `[0, τ]`, so the dual expectation is
continuous in time (`continuousOn_decisionDual`). It is at most `‖f‖` (`abs_decisionDual_le`),
linear (`decisionDual_add`, `decisionDual_smul`), and starts at `H_f(p)`
(`decisionDual_zero_time`).

The truncated circuits obey Dynkin's formula (`hasDerivAt_truncatedDual`), and dominated
convergence carries its integrated form to the limit (`decisionDual_sub_eq_integral`). Read
through the backward generator of `SamplingDuality` (`decisionDual_holdingGenerator_add`), this is
the moment equation of Theorem 6, `D_t f - H_f(p) = ∫_0^t (c ∑_{a<b} (D_s(C_ab f) - D_s f) +
∑_e r_e ∑_a (D_s(B_{a,e} f) - D_s f)) ds` for `t ≥ 0` (`decisionDual_moment_equation`), with its
derivative form for `t > 0` (`hasDerivAt_decisionDual_moment_equation`).

Scope. The state space and the event set are finite, `c ≥ 0`, `r ≥ 0`, and the bounds hold at a
probability vector `p`. No path space is constructed: the circuit is represented by its expansion
over the number of decisions, and the partial sums are the expectations on the event of fewer than
`M` decisions, the circuit killed at its `M`-th decision, not the chain of `SupportChainDynkin`
in which further decisions are suppressed. The Yule weights are defined by the first-birth
recursion and are not identified with a Yule process on a probability space. The moment equation
is proved for the dual expectation only; the duality (7.5) also needs the uniqueness of moment
families that obey it and the forward equation of the population process, neither of which is in
this file.

## Empirical status

None. The bodies here are linear operators, their exponentials, integrals and series over a
supplied state space, rate table, rule family and vector, so no measurement can bear on them.
-/

namespace Descent.Pangenome.AncestralLocality

open Finset Filter Topology MeasureTheory

noncomputable section

variable {H E : Type*}

/-! ### The holding generator, its semigroup and the decision substitution -/

/-- **A substitution of arguments does not raise the sup norm.** -/
theorem norm_substitution_le [Fintype H] {n m : ℕ} (f : (Fin n → H) → ℝ)
    (σ : (Fin m → H) → Fin n → H) : ‖fun w ↦ f (σ w)‖ ≤ ‖f‖ :=
  (pi_norm_le_iff_of_nonneg (norm_nonneg f)).mpr fun w ↦ norm_le_pi_norm f (σ w)

/-- **The coalescence substitutions summed over the pairs**, `f ↦ ∑_{a<b} C_ab f`. -/
def pairSubstitution (n : ℕ) : ((Fin n → H) → ℝ) →ₗ[ℝ] ((Fin n → H) → ℝ) where
  toFun f := ∑ b, ∑ a ∈ Iio b, coalesceArguments a b f
  map_add' f g := by
    have hadd : ∀ a b : Fin n, coalesceArguments a b (f + g) =
        coalesceArguments a b f + coalesceArguments a b g := fun _ _ ↦ rfl
    simp only [hadd, sum_add_distrib]
  map_smul' d f := by
    have hsmul : ∀ a b : Fin n, coalesceArguments a b (d • f) = d • coalesceArguments a b f :=
      fun _ _ ↦ rfl
    simp only [hsmul, smul_sum, RingHom.id_apply]

/-- **Decision branching summed over the events and the arguments**,
`f ↦ ∑_e r_e ∑_a B_{a,e} f`: an observation of arity `n` becomes one of arity `n + 1`. -/
def decisionSubstitution [Fintype E] (r : E → ℝ) (T : E → H → H → H) (n : ℕ) :
    ((Fin n → H) → ℝ) →ₗ[ℝ] ((Fin (n + 1) → H) → ℝ) where
  toFun f := ∑ e, r e • ∑ a, decisionBranch (T e) a f
  map_add' f g := by
    have hadd : ∀ (e : E) (a : Fin n), decisionBranch (T e) a (f + g) =
        decisionBranch (T e) a f + decisionBranch (T e) a g := fun _ _ ↦ rfl
    simp only [hadd, sum_add_distrib, smul_add]
  map_smul' d f := by
    have hsmul : ∀ (e : E) (a : Fin n), decisionBranch (T e) a (d • f) =
        d • decisionBranch (T e) a f := fun _ _ ↦ rfl
    simp only [hsmul, smul_sum, RingHom.id_apply]
    exact sum_congr rfl fun e _ ↦ sum_congr rfl fun a _ ↦ smul_comm (r e) d _

/-- The coalescence substitutions raise the sup norm by at most the number of pairs. -/
theorem norm_pairSubstitution_le [Fintype H] {n : ℕ} (f : (Fin n → H) → ℝ) :
    ‖pairSubstitution n f‖ ≤ (∑ b : Fin n, ((Iio b).card : ℝ)) * ‖f‖ :=
  calc ‖pairSubstitution n f‖ = ‖∑ b, ∑ a ∈ Iio b, coalesceArguments a b f‖ := rfl
    _ ≤ ∑ b, ∑ a ∈ Iio b, ‖coalesceArguments a b f‖ :=
        (norm_sum_le _ _).trans (sum_le_sum fun b _ ↦ norm_sum_le _ _)
    _ ≤ ∑ b : Fin n, ∑ _a ∈ Iio b, ‖f‖ := sum_le_sum fun b _ ↦ sum_le_sum fun a _ ↦
        norm_substitution_le f fun w ↦ Function.update w a (w b)
    _ = (∑ b : Fin n, ((Iio b).card : ℝ)) * ‖f‖ := by
        simp only [sum_const, nsmul_eq_mul, sum_mul]

/-- **A decision has norm at most `n R`** for nonnegative rates. -/
theorem norm_decisionSubstitution_le [Fintype H] [Fintype E] {r : E → ℝ} (hr : ∀ e, 0 ≤ r e)
    (T : E → H → H → H) {n : ℕ} (f : (Fin n → H) → ℝ) :
    ‖decisionSubstitution r T n f‖ ≤ n * (∑ e, r e) * ‖f‖ :=
  calc ‖decisionSubstitution r T n f‖ = ‖∑ e, r e • ∑ a, decisionBranch (T e) a f‖ := rfl
    _ ≤ ∑ e, ‖r e • ∑ a, decisionBranch (T e) a f‖ := norm_sum_le _ _
    _ ≤ ∑ e, r e * (n * ‖f‖) := sum_le_sum fun e _ ↦ by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hr e)]
        refine mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans ?_) (hr e)
        calc ∑ a, ‖decisionBranch (T e) a f‖ ≤ ∑ _a : Fin n, ‖f‖ := sum_le_sum fun a _ ↦
              norm_substitution_le f fun u ↦
                Function.update (Fin.init u) a (T e (u a.castSucc) (u (Fin.last n)))
          _ = n * ‖f‖ := by rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
    _ = n * (∑ e, r e) * ‖f‖ := by
        rw [← sum_mul]
        ring

/-- **The holding generator** on observations of arity `n`: coalescence of every pair at rate `c`,
less the whole exit rate `c d_n + n R`, so that a decision removes mass. -/
def holdingGenerator [Fintype H] [Fintype E] (c : ℝ) (r : E → ℝ) (n : ℕ) :
    ((Fin n → H) → ℝ) →L[ℝ] ((Fin n → H) → ℝ) :=
  c • LinearMap.toContinuousLinearMap (pairSubstitution n) - dualExitRate c r n • 1

/-- The holding generator applied to an observation. -/
theorem holdingGenerator_apply [Fintype H] [Fintype E] (c : ℝ) (r : E → ℝ) {n : ℕ}
    (f : (Fin n → H) → ℝ) :
    holdingGenerator c r n f = c • pairSubstitution n f - dualExitRate c r n • f :=
  rfl

/-- **The holding semigroup** `S_t = e^{t K}` of the holding generator: the circuit between two
decisions, killed at the rate of the decisions. -/
def holdingSemigroup [Fintype H] [Fintype E] (c : ℝ) (r : E → ℝ) (n : ℕ) (t : ℝ) :
    ((Fin n → H) → ℝ) →L[ℝ] ((Fin n → H) → ℝ) :=
  NormedSpace.exp ℝ (t • holdingGenerator c r n)

/-- The holding semigroup starts at the identity. -/
theorem holdingSemigroup_zero [Fintype H] [Fintype E] (c : ℝ) (r : E → ℝ) (n : ℕ) :
    holdingSemigroup (H := H) c r n 0 = 1 := by
  rw [holdingSemigroup, zero_smul, NormedSpace.exp_zero]

/-- **The semigroup law read backwards**, `S_{-u} S_t = S_{t-u}`. -/
theorem holdingSemigroup_neg_mul [Fintype H] [Fintype E] (c : ℝ) (r : E → ℝ) (n : ℕ)
    (u t : ℝ) :
    holdingSemigroup (H := H) c r n (-u) * holdingSemigroup c r n t =
      holdingSemigroup c r n (t - u) := by
  have hcomm : Commute ((-u) • holdingGenerator (H := H) c r n) (t • holdingGenerator c r n) :=
    ((Commute.refl _).smul_left _).smul_right _
  rw [holdingSemigroup, holdingSemigroup, holdingSemigroup,
    ← NormedSpace.exp_add_of_commute hcomm, ← add_smul, neg_add_eq_sub]

/-- `S_{-t}` undoes `S_t`. -/
theorem holdingSemigroup_neg_apply [Fintype H] [Fintype E] (c : ℝ) (r : E → ℝ) (n : ℕ) (t : ℝ)
    (f : (Fin n → H) → ℝ) :
    holdingSemigroup c r n (-t) (holdingSemigroup c r n t f) = f := by
  rw [← ContinuousLinearMap.mul_apply, holdingSemigroup_neg_mul, sub_self, holdingSemigroup_zero,
    ContinuousLinearMap.one_apply]

/-- **The holding semigroup moves an observation along the generator**,
`d/dt S_t f = S_t K f`. -/
theorem hasDerivAt_holdingSemigroup_apply [Fintype H] [Fintype E] (c : ℝ) (r : E → ℝ) (n : ℕ)
    (t : ℝ) (f : (Fin n → H) → ℝ) :
    HasDerivAt (fun s ↦ holdingSemigroup c r n s f)
      (holdingSemigroup c r n t (holdingGenerator c r n f)) t := by
  have h := (hasDerivAt_exp_smul_const (𝕂 := ℝ) (holdingGenerator (H := H) c r n) t).clm_apply
    (hasDerivAt_const (x := t) (c := f))
  rw [ContinuousLinearMap.map_zero, add_zero] at h
  exact h

/-- The holding semigroup is continuous in time on every observation. -/
theorem continuous_holdingSemigroup_apply [Fintype H] [Fintype E] (c : ℝ) (r : E → ℝ) (n : ℕ)
    (f : (Fin n → H) → ℝ) : Continuous fun s ↦ holdingSemigroup c r n s f :=
  continuous_iff_continuousAt.mpr fun t ↦
    (hasDerivAt_holdingSemigroup_apply c r n t f).continuousAt

/-- **The holding semigroup contracts at the rate of the decisions.** For `c ≥ 0`, `r ≥ 0` and
`t ≥ 0`, `‖S_t f‖ ≤ e^{-n R t} ‖f‖`: the coalescence part is a contraction and the diagonal
carries the exit rate. -/
theorem norm_holdingSemigroup_apply_le [Fintype H] [Fintype E] {c : ℝ} {r : E → ℝ} (hc : 0 ≤ c)
    (n : ℕ) {t : ℝ} (ht : 0 ≤ t) (f : (Fin n → H) → ℝ) :
    ‖holdingSemigroup c r n t f‖ ≤ Real.exp (-(n * (∑ e, r e) * t)) * ‖f‖ := by
  have hP : ‖LinearMap.toContinuousLinearMap (pairSubstitution (H := H) n)‖ ≤
      ∑ b : Fin n, ((Iio b).card : ℝ) :=
    ContinuousLinearMap.opNorm_le_bound _ (sum_nonneg fun _ _ ↦ Nat.cast_nonneg _)
      fun g ↦ norm_pairSubstitution_le g
  have hexp : ∀ x : ((Fin n → H) → ℝ) →L[ℝ] ((Fin n → H) → ℝ),
      ‖NormedSpace.exp ℝ x‖ ≤ Real.exp ‖x‖ := by
    intro x
    rw [NormedSpace.exp_eq_tsum, Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum]
    refine (norm_tsum_le_tsum_norm (NormedSpace.norm_expSeries_summable' (𝕂 := ℝ) x)).trans
      (Summable.tsum_le_tsum (fun k ↦ ?_) (NormedSpace.norm_expSeries_summable' (𝕂 := ℝ) x)
        (NormedSpace.expSeries_summable' (𝕂 := ℝ) ‖x‖))
    simp only [norm_smul, smul_eq_mul, Real.norm_eq_abs]
    rw [abs_of_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))]
    refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.mpr (Nat.cast_nonneg _))
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · rw [pow_zero, pow_zero]
      exact ContinuousLinearMap.norm_id_le
    · exact norm_pow_le' x hk
  have hscalar : ∀ s : ℝ,
      NormedSpace.exp ℝ (s • (1 : ((Fin n → H) → ℝ) →L[ℝ] ((Fin n → H) → ℝ))) =
        Real.exp s • (1 : ((Fin n → H) → ℝ) →L[ℝ] ((Fin n → H) → ℝ)) := fun s ↦ by
    rw [← Algebra.algebraMap_eq_smul_one s, ← NormedSpace.algebraMap_exp_comm,
      Algebra.algebraMap_eq_smul_one, ← Real.exp_eq_exp_ℝ]
  have hsplit : t • holdingGenerator (H := H) c r n =
      t • c • LinearMap.toContinuousLinearMap (pairSubstitution (H := H) n) +
        (-(t * dualExitRate c r n)) • 1 := by
    ext g w
    simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.one_apply, holdingGenerator_apply, LinearMap.coe_toContinuousLinearMap',
      Pi.smul_apply, Pi.sub_apply, Pi.add_apply, smul_eq_mul]
    ring
  have hS : holdingSemigroup (H := H) c r n t =
      Real.exp (-(t * dualExitRate c r n)) •
        NormedSpace.exp ℝ (t • c • LinearMap.toContinuousLinearMap (pairSubstitution n)) := by
    rw [holdingSemigroup, hsplit,
      NormedSpace.exp_add_of_commute ((Commute.one_right _).smul_right _), hscalar,
      mul_smul_comm, mul_one]
  have hnorm : ‖t • c • LinearMap.toContinuousLinearMap (pairSubstitution (H := H) n)‖ ≤
      t * (c * ∑ b : Fin n, ((Iio b).card : ℝ)) := by
    rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg ht,
      abs_of_nonneg hc]
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hP hc) ht
  calc ‖holdingSemigroup c r n t f‖ ≤ ‖holdingSemigroup (H := H) c r n t‖ * ‖f‖ :=
        (holdingSemigroup c r n t).le_opNorm f
    _ ≤ Real.exp (-(n * (∑ e, r e) * t)) * ‖f‖ := by
        refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg f)
        rw [hS, norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
        calc Real.exp (-(t * dualExitRate c r n)) * ‖NormedSpace.exp ℝ
              (t • c • LinearMap.toContinuousLinearMap (pairSubstitution (H := H) n))‖
            ≤ Real.exp (-(t * dualExitRate c r n)) *
                Real.exp (t * (c * ∑ b : Fin n, ((Iio b).card : ℝ))) :=
              mul_le_mul_of_nonneg_left ((hexp _).trans (Real.exp_le_exp.mpr hnorm))
                (Real.exp_pos _).le
          _ = Real.exp (-(n * (∑ e, r e) * t)) := by
              rw [← Real.exp_add, dualExitRate]
              congr 1
              ring

/-- **A sampling observable at a probability vector is at most the sup norm.** -/
theorem abs_samplingObservable_le [Fintype H] {n : ℕ} (f : (Fin n → H) → ℝ) {p : H → ℝ}
    (hp0 : ∀ h, 0 ≤ p h) (hp : ∑ h, p h = 1) : |samplingObservable f p| ≤ ‖f‖ := by
  have hmass : ∑ w : Fin n → H, ∏ a, p (w a) = 1 := by
    have h := Finset.prod_univ_sum (fun _ : Fin n ↦ (univ : Finset H)) fun _ h ↦ p h
    rw [Fintype.piFinset_univ] at h
    rw [← h, hp, prod_const_one]
  calc |samplingObservable f p| ≤ ∑ w, |f w * ∏ a, p (w a)| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ w, ‖f‖ * ∏ a, p (w a) := sum_le_sum fun w _ ↦ by
        rw [abs_mul, abs_of_nonneg (prod_nonneg fun a _ ↦ hp0 (w a))]
        refine mul_le_mul_of_nonneg_right ?_ (prod_nonneg fun a _ ↦ hp0 (w a))
        simpa only [Real.norm_eq_abs] using norm_le_pi_norm f w
    _ = ‖f‖ := by rw [← mul_sum, hmass, mul_one]

/-- `S_{-u}` after `S_t` is `S_{t-u}`, on one observation. -/
theorem holdingSemigroup_neg_apply_apply [Fintype H] [Fintype E] (c : ℝ) (r : E → ℝ) (n : ℕ)
    (u t : ℝ) (f : (Fin n → H) → ℝ) :
    holdingSemigroup c r n (-u) (holdingSemigroup c r n t f) =
      holdingSemigroup c r n (t - u) f := by
  rw [← holdingSemigroup_neg_mul]
  rfl

/-! ### The Dyson terms of the backward circuit -/

/-- **The Dyson terms of the backward circuit.** `dysonMoment c r T p k n t f` is the expectation
of `H_{f_t}(p)` over the runs of the circuit started from the observation `f` of arity `n` that
take exactly `k` decisions by time `t`. With no decision it is `H_{S_t f}(p)`. With `k + 1`
decisions the first one falls at a time `t - u`, after which the branched observation of arity
`n + 1` runs for the time `u` with `k` decisions. The integral over `u` is taken against the
indicators of the tuples, so that the term is linear by construction;
`dysonMoment_succ_eq_integral` gives the integral itself. -/
def dysonMoment [Fintype H] [DecidableEq H] [Fintype E] (c : ℝ) (r : E → ℝ)
    (T : E → H → H → H) (p : H → ℝ) : ℕ → (n : ℕ) → ℝ → ((Fin n → H) → ℝ) →ₗ[ℝ] ℝ
  | 0, n, t => (samplingFunctional p).comp (holdingSemigroup c r n t).toLinearMap
  | k + 1, n, t =>
    { toFun := fun f ↦ ∑ w, holdingSemigroup c r n t f w *
        ∫ u in (0 : ℝ)..t, dysonMoment c r T p k (n + 1) u (decisionSubstitution r T n
          (holdingSemigroup c r n (-u) fun j ↦ if w = j then 1 else 0))
      map_add' := fun f g ↦ by simp only [map_add, Pi.add_apply, add_mul, sum_add_distrib]
      map_smul' := fun d f ↦ by
        simp only [map_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, mul_sum, mul_assoc] }

/-- The Dyson term without decisions is the sampling observable of the holding semigroup. -/
theorem dysonMoment_zero_apply [Fintype H] [DecidableEq H] [Fintype E] (c : ℝ) (r : E → ℝ)
    (T : E → H → H → H) (p : H → ℝ) (n : ℕ) (t : ℝ) (f : (Fin n → H) → ℝ) :
    dysonMoment c r T p 0 n t f = samplingObservable (holdingSemigroup c r n t f) p :=
  rfl

/-- **The integrand of a Dyson term** against the indicator of the tuple `w`: one decision on the
indicator run backwards by `u`, followed by the Dyson term of arity `n + 1` at time `u`. -/
def dysonIntegrand [Fintype H] [DecidableEq H] [Fintype E] (c : ℝ) (r : E → ℝ)
    (T : E → H → H → H) (p : H → ℝ) (k n : ℕ) (w : Fin n → H) (u : ℝ) : ℝ :=
  dysonMoment c r T p k (n + 1) u
    (decisionSubstitution r T n (holdingSemigroup c r n (-u) fun j ↦ if w = j then 1 else 0))

/-- A Dyson term with decisions, against the indicators. -/
theorem dysonMoment_succ_apply [Fintype H] [DecidableEq H] [Fintype E] (c : ℝ) (r : E → ℝ)
    (T : E → H → H → H) (p : H → ℝ) (k n : ℕ) (t : ℝ) (f : (Fin n → H) → ℝ) :
    dysonMoment c r T p (k + 1) n t f =
      ∑ w, holdingSemigroup c r n t f w * ∫ u in (0 : ℝ)..t, dysonIntegrand c r T p k n w u :=
  rfl

/-- A Dyson term that is continuous in time on every observation is continuous along every
continuous path of observations, since it is linear. -/
theorem continuous_dysonMoment_comp [Fintype H] [DecidableEq H] [Fintype E] {c : ℝ} {r : E → ℝ}
    {T : E → H → H → H} {p : H → ℝ} {k n : ℕ}
    (hk : ∀ f : (Fin n → H) → ℝ, Continuous fun t ↦ dysonMoment c r T p k n t f)
    {g : ℝ → (Fin n → H) → ℝ} (hg : Continuous g) :
    Continuous fun t ↦ dysonMoment c r T p k n t (g t) := by
  have h : (fun t ↦ dysonMoment c r T p k n t (g t)) =
      fun t ↦ ∑ w, g t w * dysonMoment c r T p k n t fun j ↦ if w = j then 1 else 0 :=
    funext fun t ↦ by
      rw [LinearMap.pi_apply_eq_sum_univ (dysonMoment c r T p k n t) (g t)]
      simp only [smul_eq_mul]
  rw [h]
  exact continuous_finset_sum _ fun w _ ↦ ((continuous_apply w).comp hg).mul (hk _)

/-- The integrand of a Dyson term is continuous once the previous term is. -/
theorem continuous_dysonIntegrand [Fintype H] [DecidableEq H] [Fintype E] (c : ℝ) (r : E → ℝ)
    (T : E → H → H → H) (p : H → ℝ) {k : ℕ}
    (hk : ∀ (n : ℕ) (f : (Fin n → H) → ℝ), Continuous fun t ↦ dysonMoment c r T p k n t f)
    (n : ℕ) (w : Fin n → H) : Continuous (dysonIntegrand c r T p k n w) := by
  have hg : Continuous fun u ↦ decisionSubstitution r T n
      (holdingSemigroup c r n (-u) fun j ↦ if w = j then 1 else 0) :=
    (LinearMap.continuous_of_finiteDimensional (decisionSubstitution r T n)).comp
      ((continuous_holdingSemigroup_apply c r n fun j ↦ if w = j then 1 else 0).comp
        continuous_neg)
  exact continuous_dysonMoment_comp (hk (n + 1)) hg

/-- **Every Dyson term is continuous in time** on every observation. -/
theorem continuous_dysonMoment_apply [Fintype H] [DecidableEq H] [Fintype E] (c : ℝ)
    (r : E → ℝ) (T : E → H → H → H) (p : H → ℝ) (k : ℕ) :
    ∀ (n : ℕ) (f : (Fin n → H) → ℝ), Continuous fun t ↦ dysonMoment c r T p k n t f := by
  induction k with
  | zero =>
    intro n f
    have hS := continuous_holdingSemigroup_apply (H := H) c r n f
    simp only [dysonMoment_zero_apply, samplingObservable]
    exact continuous_finset_sum _ fun w _ ↦ ((continuous_apply w).comp hS).mul continuous_const
  | succ k ih =>
    intro n f
    simp only [dysonMoment_succ_apply]
    refine continuous_finset_sum _ fun w _ ↦
      ((continuous_apply w).comp (continuous_holdingSemigroup_apply c r n f)).mul ?_
    exact intervalIntegral.continuous_primitive
      (fun a b ↦ (continuous_dysonIntegrand c r T p ih n w).intervalIntegrable a b) 0

/-- **The Dyson term without decisions moves along the holding generator**,
`d/dt d_0(t, f) = d_0(t, K f)`. -/
theorem hasDerivAt_dysonMoment_zero [Fintype H] [DecidableEq H] [Fintype E] (c : ℝ) (r : E → ℝ)
    (T : E → H → H → H) (p : H → ℝ) (n : ℕ) (f : (Fin n → H) → ℝ) (t : ℝ) :
    HasDerivAt (fun s ↦ dysonMoment c r T p 0 n s f)
      (dysonMoment c r T p 0 n t (holdingGenerator c r n f)) t := by
  have h := (LinearMap.toContinuousLinearMap (samplingFunctional (n := n) p)).hasFDerivAt
    |>.comp_hasDerivAt t (hasDerivAt_holdingSemigroup_apply c r n t f)
  exact h

/-- **The derivative of a Dyson term with decisions**,
`d/dt d_{k+1}(t, f) = d_{k+1}(t, K f) + d_k(t, B f)`: the holding generator at arity `n`, and
one decision into arity `n + 1` read by the term with one decision less. -/
theorem hasDerivAt_dysonMoment_succ [Fintype H] [DecidableEq H] [Fintype E] (c : ℝ) (r : E → ℝ)
    (T : E → H → H → H) (p : H → ℝ) {k : ℕ}
    (hk : ∀ (n : ℕ) (f : (Fin n → H) → ℝ), Continuous fun t ↦ dysonMoment c r T p k n t f)
    (n : ℕ) (f : (Fin n → H) → ℝ) (t : ℝ) :
    HasDerivAt (fun s ↦ dysonMoment c r T p (k + 1) n s f)
      (dysonMoment c r T p (k + 1) n t (holdingGenerator c r n f) +
        dysonMoment c r T p k (n + 1) t (decisionSubstitution r T n f)) t := by
  have hψ := continuous_dysonIntegrand c r T p hk n
  have hterm : ∀ w ∈ (univ : Finset (Fin n → H)), HasDerivAt
      (fun s ↦ holdingSemigroup c r n s f w * ∫ u in (0 : ℝ)..s, dysonIntegrand c r T p k n w u)
      (holdingSemigroup c r n t (holdingGenerator c r n f) w *
          (∫ u in (0 : ℝ)..t, dysonIntegrand c r T p k n w u) +
        holdingSemigroup c r n t f w * dysonIntegrand c r T p k n w t) t := fun w _ ↦
    ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n → H ↦ ℝ) w).hasFDerivAt
        |>.comp_hasDerivAt t (hasDerivAt_holdingSemigroup_apply c r n t f)).mul
      (intervalIntegral.integral_hasDerivAt_right ((hψ w).intervalIntegrable 0 t)
        ((hψ w).stronglyMeasurableAtFilter _ _) (hψ w).continuousAt)
  have hfun : (fun s ↦ dysonMoment c r T p (k + 1) n s f) = fun s ↦ ∑ w ∈ univ,
      holdingSemigroup c r n s f w * ∫ u in (0 : ℝ)..s, dysonIntegrand c r T p k n w u :=
    funext fun s ↦ dysonMoment_succ_apply c r T p k n s f
  rw [hfun]
  refine (HasDerivAt.fun_sum hterm).congr_deriv ?_
  rw [sum_add_distrib, ← dysonMoment_succ_apply]
  congr 1
  have hlin := LinearMap.pi_apply_eq_sum_univ ((dysonMoment c r T p k (n + 1) t).comp
    ((decisionSubstitution r T n).comp (holdingSemigroup c r n (-t)).toLinearMap))
    (holdingSemigroup c r n t f)
  simp only [LinearMap.comp_apply, ContinuousLinearMap.coe_coe, smul_eq_mul,
    holdingSemigroup_neg_apply] at hlin
  exact hlin.symm

/-- **A Dyson term is the integral over the time of the first decision**,
`d_{k+1}(t, f) = ∫_0^t d_k(u, B S_{t-u} f) du`. -/
theorem dysonMoment_succ_eq_integral [Fintype H] [DecidableEq H] [Fintype E] (c : ℝ)
    (r : E → ℝ) (T : E → H → H → H) (p : H → ℝ) {k : ℕ}
    (hk : ∀ (n : ℕ) (f : (Fin n → H) → ℝ), Continuous fun t ↦ dysonMoment c r T p k n t f)
    (n : ℕ) (t : ℝ) (f : (Fin n → H) → ℝ) :
    dysonMoment c r T p (k + 1) n t f = ∫ u in (0 : ℝ)..t, dysonMoment c r T p k (n + 1) u
      (decisionSubstitution r T n (holdingSemigroup c r n (t - u) f)) := by
  have hψ := continuous_dysonIntegrand c r T p hk n
  have hint : ∀ w ∈ (univ : Finset (Fin n → H)), IntervalIntegrable
      (fun u ↦ holdingSemigroup c r n t f w * dysonIntegrand c r T p k n w u) volume 0 t :=
    fun w _ ↦ (continuous_const.mul (hψ w)).intervalIntegrable 0 t
  rw [dysonMoment_succ_apply]
  simp only [← intervalIntegral.integral_const_mul]
  rw [← intervalIntegral.integral_finset_sum hint]
  refine intervalIntegral.integral_congr fun u _ ↦ ?_
  have hlin := LinearMap.pi_apply_eq_sum_univ ((dysonMoment c r T p k (n + 1) u).comp
    ((decisionSubstitution r T n).comp (holdingSemigroup c r n (-u)).toLinearMap))
    (holdingSemigroup c r n t f)
  simp only [LinearMap.comp_apply, ContinuousLinearMap.coe_coe, smul_eq_mul,
    holdingSemigroup_neg_apply_apply] at hlin
  exact hlin.symm

/-! ### The Yule weights: the number of decisions -/

/-- **The Yule weights.** `yuleWeight R k n t` is the probability that a Yule process in which
each of `n` arguments branches at rate `R` has exactly `k` births by time `t`, written through the
time `t - u` of the first birth, after which `n + 1` arguments run for the time `u`. -/
def yuleWeight (R : ℝ) : ℕ → ℕ → ℝ → ℝ
  | 0, n, t => Real.exp (-(n * R * t))
  | k + 1, n, t => Real.exp (-(n * R * t)) *
      ∫ u in (0 : ℝ)..t, n * R * Real.exp (n * R * u) * yuleWeight R k (n + 1) u

/-- The Yule weight of a run with a birth, through the time of the first birth. -/
theorem yuleWeight_succ (R : ℝ) (k n : ℕ) (t : ℝ) :
    yuleWeight R (k + 1) n t = Real.exp (-(n * R * t)) *
      ∫ u in (0 : ℝ)..t, n * R * Real.exp (n * R * u) * yuleWeight R k (n + 1) u :=
  rfl

/-- The Yule weights are continuous in time. -/
theorem continuous_yuleWeight (R : ℝ) (k : ℕ) : ∀ n, Continuous (yuleWeight R k n) := by
  induction k with
  | zero =>
    intro n
    show Continuous fun t ↦ Real.exp (-(n * R * t))
    fun_prop
  | succ k ih =>
    intro n
    have hint : Continuous fun u ↦ n * R * Real.exp (n * R * u) * yuleWeight R k (n + 1) u :=
      (by fun_prop : Continuous fun u : ℝ ↦ (n : ℝ) * R * Real.exp (n * R * u)).mul (ih (n + 1))
    show Continuous fun t ↦ Real.exp (-(n * R * t)) *
      ∫ u in (0 : ℝ)..t, n * R * Real.exp (n * R * u) * yuleWeight R k (n + 1) u
    exact (by fun_prop : Continuous fun t : ℝ ↦ Real.exp (-(n * R * t))).mul
      (intervalIntegral.continuous_primitive (fun a b ↦ hint.intervalIntegrable a b) 0)

/-- The Yule weights are nonnegative at nonnegative times. -/
theorem yuleWeight_nonneg {R : ℝ} (hR : 0 ≤ R) (k : ℕ) :
    ∀ (n : ℕ) {t : ℝ}, 0 ≤ t → 0 ≤ yuleWeight R k n t := by
  induction k with
  | zero =>
    intro n t _
    exact (Real.exp_pos _).le
  | succ k ih =>
    intro n t ht
    rw [yuleWeight_succ]
    refine mul_nonneg (Real.exp_pos _).le (intervalIntegral.integral_nonneg ht fun u hu ↦ ?_)
    exact mul_nonneg (mul_nonneg (mul_nonneg (Nat.cast_nonneg n) hR) (Real.exp_pos _).le)
      (ih (n + 1) hu.1)

/-- `∫_0^t a e^{a u} du = e^{a t} - 1`. -/
theorem integral_mul_exp_mul (a t : ℝ) :
    ∫ u in (0 : ℝ)..t, a * Real.exp (a * u) = Real.exp (a * t) - 1 := by
  have hderiv : ∀ u ∈ Set.uIcc (0 : ℝ) t,
      HasDerivAt (fun u ↦ Real.exp (a * u)) (a * Real.exp (a * u)) u := fun u _ ↦
    ((hasDerivAt_id' (x := u)).const_mul a).exp.congr_deriv (by ring)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    ((by fun_prop : Continuous fun u : ℝ ↦ a * Real.exp (a * u)).intervalIntegrable 0 t),
    mul_zero, Real.exp_zero]

/-- **The first-birth decomposition of the Yule weights**,
`∑_{k ≤ M} w_k^{(n)}(t) = e^{-nRt} (1 + ∫_0^t n R e^{nRu} ∑_{k<M} w_k^{(n+1)}(u) du)`. -/
theorem sum_range_succ_yuleWeight (R : ℝ) (M n : ℕ) (t : ℝ) :
    ∑ k ∈ range (M + 1), yuleWeight R k n t = Real.exp (-(n * R * t)) *
      (1 + ∫ u in (0 : ℝ)..t,
        n * R * Real.exp (n * R * u) * ∑ k ∈ range M, yuleWeight R k (n + 1) u) := by
  have hint : ∀ k ∈ range M, IntervalIntegrable
      (fun u ↦ n * R * Real.exp (n * R * u) * yuleWeight R k (n + 1) u) volume 0 t :=
    fun k _ ↦ ((by fun_prop : Continuous fun u : ℝ ↦ (n : ℝ) * R * Real.exp (n * R * u)).mul
      (continuous_yuleWeight R k (n + 1))).intervalIntegrable 0 t
  rw [sum_range_succ']
  simp only [mul_sum]
  rw [intervalIntegral.integral_finset_sum hint, mul_add, mul_one, mul_sum, add_comm]
  rfl

/-- **The Yule weights have mass at most one.** -/
theorem sum_range_yuleWeight_le_one {R : ℝ} (hR : 0 ≤ R) (M : ℕ) :
    ∀ (n : ℕ) {t : ℝ}, 0 ≤ t → ∑ k ∈ range M, yuleWeight R k n t ≤ 1 := by
  induction M with
  | zero =>
    intro n t _
    simp
  | succ M ih =>
    intro n t ht
    rw [sum_range_succ_yuleWeight]
    have hrate : 0 ≤ (n : ℝ) * R := mul_nonneg (Nat.cast_nonneg n) hR
    have hcont : Continuous fun u : ℝ ↦ (n : ℝ) * R * Real.exp (n * R * u) := by fun_prop
    have hmono : ∫ u in (0 : ℝ)..t,
        n * R * Real.exp (n * R * u) * ∑ k ∈ range M, yuleWeight R k (n + 1) u ≤
          ∫ u in (0 : ℝ)..t, n * R * Real.exp (n * R * u) := by
      refine intervalIntegral.integral_mono_on ht
        ((hcont.mul (continuous_finset_sum (range M) fun k _ ↦
          continuous_yuleWeight R k (n + 1)))
          |>.intervalIntegrable 0 t) (hcont.intervalIntegrable 0 t) fun u hu ↦ ?_
      exact mul_le_of_le_one_right (mul_nonneg hrate (Real.exp_pos _).le) (ih (n + 1) hu.1)
    rw [integral_mul_exp_mul] at hmono
    calc Real.exp (-(n * R * t)) * (1 + ∫ u in (0 : ℝ)..t,
          n * R * Real.exp (n * R * u) * ∑ k ∈ range M, yuleWeight R k (n + 1) u)
        ≤ Real.exp (-(n * R * t)) * (1 + (Real.exp (n * R * t) - 1)) :=
          mul_le_mul_of_nonneg_left (by linarith) (Real.exp_pos _).le
      _ = 1 := by
          rw [show (1 : ℝ) + (Real.exp (n * R * t) - 1) = Real.exp (n * R * t) by ring,
            ← Real.exp_add, neg_add_cancel, Real.exp_zero]

/-- **The quantitative tail of the number of decisions**:
`(n + M) (1 - ∑_{k<M} w_k^{(n)}(t)) ≤ n e^{Rt}`, so the probability of at least `M` births by
time `t` is at most `n e^{Rt} / (n + M)`. -/
theorem mul_one_sub_sum_range_yuleWeight_le {R : ℝ} (hR : 0 ≤ R) (M : ℕ) :
    ∀ (n : ℕ) {t : ℝ}, 0 ≤ t →
      (n + M) * (1 - ∑ k ∈ range M, yuleWeight R k n t) ≤ n * Real.exp (R * t) := by
  induction M with
  | zero =>
    intro n t ht
    simp only [Nat.cast_zero, add_zero, range_zero, sum_empty, sub_zero, mul_one]
    exact le_mul_of_one_le_right (Nat.cast_nonneg n) (Real.one_le_exp (mul_nonneg hR ht))
  | succ M ih =>
    intro n t ht
    have hrate : 0 ≤ (n : ℝ) * R := mul_nonneg (Nat.cast_nonneg n) hR
    have hcont : Continuous fun u : ℝ ↦ (n : ℝ) * R * Real.exp (n * R * u) := by fun_prop
    have hsum : Continuous fun u ↦ ∑ k ∈ range M, yuleWeight R k (n + 1) u :=
      continuous_finset_sum _ fun k _ ↦ continuous_yuleWeight R k (n + 1)
    set J := ∫ u in (0 : ℝ)..t,
      n * R * Real.exp (n * R * u) * (1 - ∑ k ∈ range M, yuleWeight R k (n + 1) u) with hJdef
    have hone : Real.exp (-(n * R * t)) * Real.exp (n * R * t) = 1 := by
      rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
    have hdeficit : 1 - ∑ k ∈ range (M + 1), yuleWeight R k n t = Real.exp (-(n * R * t)) * J := by
      rw [sum_range_succ_yuleWeight, hJdef]
      simp only [mul_sub, mul_one]
      rw [intervalIntegral.integral_sub (hcont.intervalIntegrable 0 t)
        ((hcont.mul hsum).intervalIntegrable 0 t), integral_mul_exp_mul]
      linear_combination -hone
    have hJ : ((n : ℝ) + ((M + 1 : ℕ) : ℝ)) * J ≤ n * (Real.exp (((n : ℝ) + 1) * R * t) - 1) := by
      rw [hJdef, ← intervalIntegral.integral_const_mul, ← integral_mul_exp_mul,
        ← intervalIntegral.integral_const_mul]
      refine intervalIntegral.integral_mono_on ht
        ((continuous_const.mul (hcont.mul (continuous_const.sub hsum))).intervalIntegrable 0 t)
        ((continuous_const.mul (by fun_prop :
          Continuous fun u : ℝ ↦ ((n : ℝ) + 1) * R * Real.exp (((n : ℝ) + 1) * R * u)))
          |>.intervalIntegrable 0 t) fun u hu ↦ ?_
      have h := ih (n + 1) hu.1
      push_cast at h
      calc ((n : ℝ) + ((M + 1 : ℕ) : ℝ)) * (n * R * Real.exp (n * R * u) *
            (1 - ∑ k ∈ range M, yuleWeight R k (n + 1) u))
          = n * R * Real.exp (n * R * u) *
              (((n : ℝ) + 1 + M) * (1 - ∑ k ∈ range M, yuleWeight R k (n + 1) u)) := by
            push_cast
            ring
        _ ≤ n * R * Real.exp (n * R * u) * (((n : ℝ) + 1) * Real.exp (R * u)) :=
            mul_le_mul_of_nonneg_left h (mul_nonneg hrate (Real.exp_pos _).le)
        _ = n * (((n : ℝ) + 1) * R * Real.exp (((n : ℝ) + 1) * R * u)) := by
            rw [show ((n : ℝ) + 1) * R * u = n * R * u + R * u by ring, Real.exp_add]
            ring
    have h1 : Real.exp (-(n * R * t)) * Real.exp (((n : ℝ) + 1) * R * t) = Real.exp (R * t) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [hdeficit]
    calc ((n : ℝ) + ((M + 1 : ℕ) : ℝ)) * (Real.exp (-(n * R * t)) * J)
        = Real.exp (-(n * R * t)) * (((n : ℝ) + ((M + 1 : ℕ) : ℝ)) * J) := by ring
      _ ≤ Real.exp (-(n * R * t)) * (n * (Real.exp (((n : ℝ) + 1) * R * t) - 1)) :=
          mul_le_mul_of_nonneg_left hJ (Real.exp_pos _).le
      _ = n * (Real.exp (-(n * R * t)) * Real.exp (((n : ℝ) + 1) * R * t)) -
            Real.exp (-(n * R * t)) * n := by ring
      _ = n * Real.exp (R * t) - Real.exp (-(n * R * t)) * n := by rw [h1]
      _ ≤ n * Real.exp (R * t) :=
          sub_le_self _ (mul_nonneg (Real.exp_pos _).le (Nat.cast_nonneg n))

/-- The Yule weights at a nonnegative time are summable. -/
theorem summable_yuleWeight {R : ℝ} (hR : 0 ≤ R) (n : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    Summable fun k ↦ yuleWeight R k n t :=
  summable_of_sum_range_le (fun k ↦ yuleWeight_nonneg hR k n ht) fun M ↦
    sum_range_yuleWeight_le_one hR M n ht

/-- **The circuit does not explode**: the Yule weights sum to one at every time `t ≥ 0`, so the
linear birth rate leaves no mass at infinitely many decisions. -/
theorem tsum_yuleWeight_eq_one {R : ℝ} (hR : 0 ≤ R) (n : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    ∑' k, yuleWeight R k n t = 1 := by
  refine tendsto_nhds_unique (summable_yuleWeight hR n ht).hasSum.tendsto_sum_nat ?_
  have hlow : Tendsto (fun M : ℕ ↦ 1 - n * Real.exp (R * t) / M) atTop (𝓝 1) := by
    simpa only [sub_zero] using
      (tendsto_const_div_atTop_nhds_zero_nat (n * Real.exp (R * t))).const_sub 1
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds ?_
    (Eventually.of_forall fun M ↦ sum_range_yuleWeight_le_one hR M n ht)
  filter_upwards [eventually_gt_atTop 0] with M hM
  have hM' : (0 : ℝ) < M := Nat.cast_pos.mpr hM
  have h := mul_one_sub_sum_range_yuleWeight_le hR M n ht
  have hle := sum_range_yuleWeight_le_one hR M n ht
  rw [sub_le_comm, le_div_iff₀ hM']
  nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) n) (sub_nonneg.mpr hle)]

/-- **A Dyson term is at most its Yule weight.** For `c ≥ 0`, `r ≥ 0`, a probability vector `p`
and `t ≥ 0`, `|d_k(t, f)| ≤ yuleWeight R k n t ‖f‖` with `R = ∑_e r_e`. -/
theorem abs_dysonMoment_le [Fintype H] [DecidableEq H] [Fintype E] {c : ℝ} {r : E → ℝ}
    (hc : 0 ≤ c) (hr : ∀ e, 0 ≤ r e) (T : E → H → H → H) {p : H → ℝ} (hp0 : ∀ h, 0 ≤ p h)
    (hp : ∑ h, p h = 1) (k : ℕ) :
    ∀ (n : ℕ) {t : ℝ}, 0 ≤ t → ∀ f : (Fin n → H) → ℝ,
      |dysonMoment c r T p k n t f| ≤ yuleWeight (∑ e, r e) k n t * ‖f‖ := by
  have hR : 0 ≤ ∑ e, r e := sum_nonneg fun e _ ↦ hr e
  induction k with
  | zero =>
    intro n t ht f
    rw [dysonMoment_zero_apply]
    exact (abs_samplingObservable_le _ hp0 hp).trans (norm_holdingSemigroup_apply_le hc n ht f)
  | succ k ih =>
    intro n t ht f
    rw [dysonMoment_succ_eq_integral c r T p (continuous_dysonMoment_apply c r T p k) n t f,
      yuleWeight_succ]
    have hcont : Continuous fun u : ℝ ↦ (n : ℝ) * (∑ e, r e) *
        Real.exp (n * (∑ e, r e) * u) * yuleWeight (∑ e, r e) k (n + 1) u :=
      (by fun_prop : Continuous fun u : ℝ ↦ (n : ℝ) * (∑ e, r e) *
        Real.exp (n * (∑ e, r e) * u)).mul (continuous_yuleWeight _ k (n + 1))
    calc |∫ u in (0 : ℝ)..t, dysonMoment c r T p k (n + 1) u
          (decisionSubstitution r T n (holdingSemigroup c r n (t - u) f))|
        ≤ ∫ u in (0 : ℝ)..t, (Real.exp (-(n * (∑ e, r e) * t)) * ‖f‖) * ((n : ℝ) *
            (∑ e, r e) * Real.exp (n * (∑ e, r e) * u) * yuleWeight (∑ e, r e) k (n + 1) u) := by
          rw [← Real.norm_eq_abs]
          refine intervalIntegral.norm_integral_le_of_norm_le ht (ae_of_all _ fun u hu ↦ ?_)
            ((continuous_const.mul hcont).intervalIntegrable 0 t)
          rw [Real.norm_eq_abs]
          have hu0 : 0 ≤ u := hu.1.le
          have htu : 0 ≤ t - u := sub_nonneg.mpr hu.2
          calc |dysonMoment c r T p k (n + 1) u
                (decisionSubstitution r T n (holdingSemigroup c r n (t - u) f))|
              ≤ yuleWeight (∑ e, r e) k (n + 1) u *
                  ‖decisionSubstitution r T n (holdingSemigroup c r n (t - u) f)‖ :=
                ih (n + 1) hu0 _
            _ ≤ yuleWeight (∑ e, r e) k (n + 1) u * ((n : ℝ) * (∑ e, r e) *
                  (Real.exp (-(n * (∑ e, r e) * (t - u))) * ‖f‖)) := by
                refine mul_le_mul_of_nonneg_left ?_ (yuleWeight_nonneg hR k (n + 1) hu0)
                exact (norm_decisionSubstitution_le hr T _).trans
                  (mul_le_mul_of_nonneg_left (norm_holdingSemigroup_apply_le hc n htu f)
                    (mul_nonneg (Nat.cast_nonneg n) hR))
            _ = (Real.exp (-(n * (∑ e, r e) * t)) * ‖f‖) * ((n : ℝ) * (∑ e, r e) *
                  Real.exp (n * (∑ e, r e) * u) * yuleWeight (∑ e, r e) k (n + 1) u) := by
                rw [show -((n : ℝ) * (∑ e, r e) * (t - u)) =
                  -(n * (∑ e, r e) * t) + n * (∑ e, r e) * u by ring, Real.exp_add]
                ring
      _ = Real.exp (-(n * (∑ e, r e) * t)) * (∫ u in (0 : ℝ)..t, (n : ℝ) * (∑ e, r e) *
            Real.exp (n * (∑ e, r e) * u) * yuleWeight (∑ e, r e) k (n + 1) u) * ‖f‖ := by
          rw [intervalIntegral.integral_const_mul]
          ring

/-! ### The dual expectation and the truncated circuits -/

/-- **The dual expectation of the circuit killed at its `M`-th decision**: the sum of the Dyson
terms with fewer than `M` decisions. -/
def truncatedDual [Fintype H] [DecidableEq H] [Fintype E] (c : ℝ) (r : E → ℝ)
    (T : E → H → H → H) (p : H → ℝ) (M n : ℕ) (t : ℝ) (f : (Fin n → H) → ℝ) : ℝ :=
  ∑ k ∈ range M, dysonMoment c r T p k n t f

/-- **The dual expectation** `E_f[H_{f_t}(p)]` of the backward decision circuit: the sum of its
Dyson terms over the number of decisions. -/
def decisionDual [Fintype H] [DecidableEq H] [Fintype E] (c : ℝ) (r : E → ℝ)
    (T : E → H → H → H) (p : H → ℝ) (n : ℕ) (t : ℝ) (f : (Fin n → H) → ℝ) : ℝ :=
  ∑' k, dysonMoment c r T p k n t f

/-- The Dyson terms at a nonnegative time are summable. -/
theorem summable_dysonMoment [Fintype H] [DecidableEq H] [Fintype E] {c : ℝ} {r : E → ℝ}
    (hc : 0 ≤ c) (hr : ∀ e, 0 ≤ r e) (T : E → H → H → H) {p : H → ℝ} (hp0 : ∀ h, 0 ≤ p h)
    (hp : ∑ h, p h = 1) (n : ℕ) {t : ℝ} (ht : 0 ≤ t) (f : (Fin n → H) → ℝ) :
    Summable fun k ↦ dysonMoment c r T p k n t f :=
  ((summable_yuleWeight (sum_nonneg fun e _ ↦ hr e) n ht).mul_right ‖f‖).of_norm_bounded
    fun k ↦ (Real.norm_eq_abs _).trans_le (abs_dysonMoment_le hc hr T hp0 hp k n ht f)

/-- The Dyson terms sum to the dual expectation. -/
theorem hasSum_dysonMoment [Fintype H] [DecidableEq H] [Fintype E] {c : ℝ} {r : E → ℝ}
    (hc : 0 ≤ c) (hr : ∀ e, 0 ≤ r e) (T : E → H → H → H) {p : H → ℝ} (hp0 : ∀ h, 0 ≤ p h)
    (hp : ∑ h, p h = 1) (n : ℕ) {t : ℝ} (ht : 0 ≤ t) (f : (Fin n → H) → ℝ) :
    HasSum (fun k ↦ dysonMoment c r T p k n t f) (decisionDual c r T p n t f) :=
  (summable_dysonMoment hc hr T hp0 hp n ht f).hasSum

/-- **The truncated circuits converge to the dual expectation** as `M → ∞`. -/
theorem tendsto_truncatedDual [Fintype H] [DecidableEq H] [Fintype E] {c : ℝ} {r : E → ℝ}
    (hc : 0 ≤ c) (hr : ∀ e, 0 ≤ r e) (T : E → H → H → H) {p : H → ℝ} (hp0 : ∀ h, 0 ≤ p h)
    (hp : ∑ h, p h = 1) (n : ℕ) {t : ℝ} (ht : 0 ≤ t) (f : (Fin n → H) → ℝ) :
    Tendsto (fun M ↦ truncatedDual c r T p M n t f) atTop (𝓝 (decisionDual c r T p n t f)) :=
  (hasSum_dysonMoment hc hr T hp0 hp n ht f).tendsto_sum_nat

/-- A truncated circuit is at most the sup norm. -/
theorem abs_truncatedDual_le [Fintype H] [DecidableEq H] [Fintype E] {c : ℝ} {r : E → ℝ}
    (hc : 0 ≤ c) (hr : ∀ e, 0 ≤ r e) (T : E → H → H → H) {p : H → ℝ} (hp0 : ∀ h, 0 ≤ p h)
    (hp : ∑ h, p h = 1) (M n : ℕ) {t : ℝ} (ht : 0 ≤ t) (f : (Fin n → H) → ℝ) :
    |truncatedDual c r T p M n t f| ≤ ‖f‖ :=
  calc |truncatedDual c r T p M n t f| ≤ ∑ k ∈ range M, |dysonMoment c r T p k n t f| :=
        abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ range M, yuleWeight (∑ e, r e) k n t * ‖f‖ :=
        sum_le_sum fun k _ ↦ abs_dysonMoment_le hc hr T hp0 hp k n ht f
    _ ≤ ‖f‖ := by
        rw [← sum_mul]
        exact mul_le_of_le_one_left (norm_nonneg f)
          (sum_range_yuleWeight_le_one (sum_nonneg fun e _ ↦ hr e) M n ht)

/-- **The dual expectation is at most the sup norm.** -/
theorem abs_decisionDual_le [Fintype H] [DecidableEq H] [Fintype E] {c : ℝ} {r : E → ℝ}
    (hc : 0 ≤ c) (hr : ∀ e, 0 ≤ r e) (T : E → H → H → H) {p : H → ℝ} (hp0 : ∀ h, 0 ≤ p h)
    (hp : ∑ h, p h = 1) (n : ℕ) {t : ℝ} (ht : 0 ≤ t) (f : (Fin n → H) → ℝ) :
    |decisionDual c r T p n t f| ≤ ‖f‖ :=
  le_of_tendsto' ((continuous_abs.tendsto _).comp (tendsto_truncatedDual hc hr T hp0 hp n ht f))
    fun M ↦ abs_truncatedDual_le hc hr T hp0 hp M n ht f

/-- **The truncation error.** The circuit killed at its `M`-th decision is within the mass of the
Yule weights with at least `M` births, times the sup norm. -/
theorem abs_decisionDual_sub_truncatedDual_le [Fintype H] [DecidableEq H] [Fintype E] {c : ℝ}
    {r : E → ℝ} (hc : 0 ≤ c) (hr : ∀ e, 0 ≤ r e) (T : E → H → H → H) {p : H → ℝ}
    (hp0 : ∀ h, 0 ≤ p h) (hp : ∑ h, p h = 1) (M n : ℕ) {t : ℝ} (ht : 0 ≤ t)
    (f : (Fin n → H) → ℝ) :
    |decisionDual c r T p n t f - truncatedDual c r T p M n t f| ≤
      (1 - ∑ k ∈ range M, yuleWeight (∑ e, r e) k n t) * ‖f‖ := by
  have hR : 0 ≤ ∑ e, r e := sum_nonneg fun e _ ↦ hr e
  refine le_of_tendsto ((continuous_abs.tendsto _).comp
    ((tendsto_truncatedDual hc hr T hp0 hp n ht f).sub_const (truncatedDual c r T p M n t f))) ?_
  filter_upwards [eventually_ge_atTop M] with N hN
  show |truncatedDual c r T p N n t f - truncatedDual c r T p M n t f| ≤ _
  simp only [truncatedDual]
  rw [sum_range_sub_sum_range hN]
  calc |∑ k ∈ range N with M ≤ k, dysonMoment c r T p k n t f|
      ≤ ∑ k ∈ range N with M ≤ k, |dysonMoment c r T p k n t f| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ range N with M ≤ k, yuleWeight (∑ e, r e) k n t * ‖f‖ :=
        sum_le_sum fun k _ ↦ abs_dysonMoment_le hc hr T hp0 hp k n ht f
    _ = (∑ k ∈ range N, yuleWeight (∑ e, r e) k n t -
          ∑ k ∈ range M, yuleWeight (∑ e, r e) k n t) * ‖f‖ := by
        rw [sum_range_sub_sum_range hN, sum_mul]
    _ ≤ (1 - ∑ k ∈ range M, yuleWeight (∑ e, r e) k n t) * ‖f‖ :=
        mul_le_mul_of_nonneg_right (sub_le_sub_right (sum_range_yuleWeight_le_one hR N n ht) _)
          (norm_nonneg f)

/-- **The truncation error at rate `1 / M`**: the circuit killed at its `M`-th decision is within
`n e^{Rt} ‖f‖ / (n + M)` of the dual expectation. -/
theorem abs_decisionDual_sub_truncatedDual_le_exp [Fintype H] [DecidableEq H] [Fintype E]
    {c : ℝ} {r : E → ℝ} (hc : 0 ≤ c) (hr : ∀ e, 0 ≤ r e) (T : E → H → H → H) {p : H → ℝ}
    (hp0 : ∀ h, 0 ≤ p h) (hp : ∑ h, p h = 1) (M n : ℕ) {t : ℝ} (ht : 0 ≤ t)
    (f : (Fin n → H) → ℝ) (hM : 0 < n + M) :
    |decisionDual c r T p n t f - truncatedDual c r T p M n t f| ≤
      n * Real.exp ((∑ e, r e) * t) / (n + M) * ‖f‖ := by
  have hpos : (0 : ℝ) < n + M := by exact_mod_cast hM
  refine (abs_decisionDual_sub_truncatedDual_le hc hr T hp0 hp M n ht f).trans
    (mul_le_mul_of_nonneg_right ?_ (norm_nonneg f))
  rw [le_div_iff₀ hpos]
  exact (mul_comm _ _).trans_le
    (mul_one_sub_sum_range_yuleWeight_le (sum_nonneg fun e _ ↦ hr e) M n ht)

/-- A Dyson term with a decision vanishes at time zero. -/
theorem dysonMoment_succ_zero_time [Fintype H] [DecidableEq H] [Fintype E] (c : ℝ) (r : E → ℝ)
    (T : E → H → H → H) (p : H → ℝ) (k n : ℕ) (f : (Fin n → H) → ℝ) :
    dysonMoment c r T p (k + 1) n 0 f = 0 := by
  rw [dysonMoment_succ_apply]
  simp only [intervalIntegral.integral_same, mul_zero, sum_const_zero]

/-- **The dual expectation starts at the sampling observable**, `D_0 f = H_f(p)`. -/
theorem decisionDual_zero_time [Fintype H] [DecidableEq H] [Fintype E] (c : ℝ) (r : E → ℝ)
    (T : E → H → H → H) (p : H → ℝ) (n : ℕ) (f : (Fin n → H) → ℝ) :
    decisionDual c r T p n 0 f = samplingObservable f p := by
  have hzero : ∀ k ≠ 0, dysonMoment c r T p k n 0 f = 0 := by
    intro k hk
    cases k with
    | zero => exact absurd rfl hk
    | succ k => exact dysonMoment_succ_zero_time c r T p k n f
  rw [decisionDual, tsum_eq_single 0 hzero, dysonMoment_zero_apply, holdingSemigroup_zero,
    ContinuousLinearMap.one_apply]

/-- A truncated circuit that keeps the run without decisions starts at the sampling observable. -/
theorem truncatedDual_succ_zero_time [Fintype H] [DecidableEq H] [Fintype E] (c : ℝ)
    (r : E → ℝ) (T : E → H → H → H) (p : H → ℝ) (M n : ℕ) (f : (Fin n → H) → ℝ) :
    truncatedDual c r T p (M + 1) n 0 f = samplingObservable f p := by
  rw [truncatedDual, sum_range_succ',
    sum_eq_zero fun k _ ↦ dysonMoment_succ_zero_time c r T p k n f, zero_add,
    dysonMoment_zero_apply, holdingSemigroup_zero, ContinuousLinearMap.one_apply]

/-- **Dynkin's formula for the truncated circuits**:
`d/dt T_{M+1}(t, f) = T_{M+1}(t, K f) + T_M(t, B f)`. -/
theorem hasDerivAt_truncatedDual [Fintype H] [DecidableEq H] [Fintype E] (c : ℝ) (r : E → ℝ)
    (T : E → H → H → H) (p : H → ℝ) (M n : ℕ) (f : (Fin n → H) → ℝ) (t : ℝ) :
    HasDerivAt (fun s ↦ truncatedDual c r T p (M + 1) n s f)
      (truncatedDual c r T p (M + 1) n t (holdingGenerator c r n f) +
        truncatedDual c r T p M (n + 1) t (decisionSubstitution r T n f)) t := by
  induction M with
  | zero =>
    simp only [truncatedDual, zero_add, sum_range_one, range_zero, sum_empty, add_zero]
    exact hasDerivAt_dysonMoment_zero c r T p n f t
  | succ M ih =>
    have h := ih.add
      (hasDerivAt_dysonMoment_succ c r T p (continuous_dysonMoment_apply c r T p M) n f t)
    simp only [truncatedDual, sum_range_succ] at h ⊢
    refine h.congr_deriv ?_
    ring

/-- The integrated form of Dynkin's formula for the truncated circuits. -/
theorem truncatedDual_sub_eq_integral [Fintype H] [DecidableEq H] [Fintype E] (c : ℝ)
    (r : E → ℝ) (T : E → H → H → H) (p : H → ℝ) (M n : ℕ) (f : (Fin n → H) → ℝ) (t : ℝ) :
    truncatedDual c r T p (M + 1) n t f - samplingObservable f p =
      ∫ s in (0 : ℝ)..t, (truncatedDual c r T p (M + 1) n s (holdingGenerator c r n f) +
        truncatedDual c r T p M (n + 1) s (decisionSubstitution r T n f)) := by
  have hcont : ∀ (N m : ℕ) (g : (Fin m → H) → ℝ),
      Continuous fun s ↦ truncatedDual c r T p N m s g :=
    fun N m g ↦ continuous_finset_sum (range N) fun k _ ↦
      continuous_dysonMoment_apply c r T p k m g
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun s _ ↦ hasDerivAt_truncatedDual c r T p M n f s)
    (((hcont _ _ _).add (hcont _ _ _)).intervalIntegrable 0 t), truncatedDual_succ_zero_time]

/-- **The integrated moment equation with the holding generator.** For `t ≥ 0`,
`D_t f - H_f(p) = ∫_0^t (D_s(K f) + D_s(B f)) ds`, where `D_s(B f)` is the dual expectation at
arity `n + 1`. The truncated circuits obey it by Dynkin's formula, and the limit `M → ∞` passes
under the integral by dominated convergence, with the bound `‖K f‖ + ‖B f‖`. -/
theorem decisionDual_sub_eq_integral [Fintype H] [DecidableEq H] [Fintype E] {c : ℝ} {r : E → ℝ}
    (hc : 0 ≤ c) (hr : ∀ e, 0 ≤ r e) (T : E → H → H → H) {p : H → ℝ} (hp0 : ∀ h, 0 ≤ p h)
    (hp : ∑ h, p h = 1) (n : ℕ) {t : ℝ} (ht : 0 ≤ t) (f : (Fin n → H) → ℝ) :
    decisionDual c r T p n t f - samplingObservable f p =
      ∫ s in (0 : ℝ)..t, (decisionDual c r T p n s (holdingGenerator c r n f) +
        decisionDual c r T p (n + 1) s (decisionSubstitution r T n f)) := by
  have hlhs : Tendsto (fun M ↦ truncatedDual c r T p (M + 1) n t f - samplingObservable f p)
      atTop (𝓝 (decisionDual c r T p n t f - samplingObservable f p)) :=
    ((tendsto_add_atTop_iff_nat 1).mpr (tendsto_truncatedDual hc hr T hp0 hp n ht f)).sub_const _
  have hrhs : Tendsto (fun M ↦ ∫ s in (0 : ℝ)..t,
      (truncatedDual c r T p (M + 1) n s (holdingGenerator c r n f) +
        truncatedDual c r T p M (n + 1) s (decisionSubstitution r T n f))) atTop
      (𝓝 (∫ s in (0 : ℝ)..t, (decisionDual c r T p n s (holdingGenerator c r n f) +
        decisionDual c r T p (n + 1) s (decisionSubstitution r T n f)))) := by
    refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence
      (fun _ ↦ ‖holdingGenerator c r n f‖ + ‖decisionSubstitution r T n f‖) ?_ ?_
      intervalIntegrable_const ?_
    · exact Eventually.of_forall fun M ↦
        ((continuous_finset_sum (range (M + 1)) fun k _ ↦
            continuous_dysonMoment_apply c r T p k n (holdingGenerator c r n f)).add
          (continuous_finset_sum (range M) fun k _ ↦ continuous_dysonMoment_apply c r T p k
            (n + 1) (decisionSubstitution r T n f))).aestronglyMeasurable
    · refine Eventually.of_forall fun M ↦ ae_of_all _ fun s hs ↦ ?_
      rw [Set.uIoc_of_le ht] at hs
      exact (norm_add_le _ _).trans
        (add_le_add (abs_truncatedDual_le hc hr T hp0 hp _ n hs.1.le _)
          (abs_truncatedDual_le hc hr T hp0 hp _ (n + 1) hs.1.le _))
    · refine ae_of_all _ fun s hs ↦ ?_
      rw [Set.uIoc_of_le ht] at hs
      exact ((tendsto_add_atTop_iff_nat 1).mpr
        (tendsto_truncatedDual hc hr T hp0 hp n hs.1.le _)).add
          (tendsto_truncatedDual hc hr T hp0 hp (n + 1) hs.1.le _)
  exact tendsto_nhds_unique hlhs
    (hrhs.congr fun M ↦ (truncatedDual_sub_eq_integral c r T p M n f t).symm)

/-- **The dual expectation is continuous in time** on every interval `[0, τ]`: the truncated
circuits converge to it uniformly there, within `n e^{Rτ} ‖f‖ / M`. -/
theorem continuousOn_decisionDual [Fintype H] [DecidableEq H] [Fintype E] {c : ℝ} {r : E → ℝ}
    (hc : 0 ≤ c) (hr : ∀ e, 0 ≤ r e) (T : E → H → H → H) {p : H → ℝ} (hp0 : ∀ h, 0 ≤ p h)
    (hp : ∑ h, p h = 1) (n : ℕ) (f : (Fin n → H) → ℝ) (τ : ℝ) :
    ContinuousOn (fun t ↦ decisionDual c r T p n t f) (Set.Icc 0 τ) := by
  have hR : 0 ≤ ∑ e, r e := sum_nonneg fun e _ ↦ hr e
  refine TendstoUniformlyOn.continuousOn (p := atTop)
    (F := fun M t ↦ truncatedDual c r T p M n t f) ?_
    (Eventually.of_forall fun M ↦
      (continuous_finset_sum (range M) fun k _ ↦
        continuous_dysonMoment_apply c r T p k n f).continuousOn)
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have hC : Tendsto (fun M : ℕ ↦ n * Real.exp ((∑ e, r e) * τ) * ‖f‖ / M) atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat _
  filter_upwards [hC.eventually (gt_mem_nhds hε), eventually_gt_atTop 0] with M hM hM0
  intro t ht
  rw [Real.dist_eq]
  calc |decisionDual c r T p n t f - truncatedDual c r T p M n t f|
      ≤ n * Real.exp ((∑ e, r e) * t) / (n + M) * ‖f‖ :=
        abs_decisionDual_sub_truncatedDual_le_exp hc hr T hp0 hp M n ht.1 f (by omega)
    _ ≤ n * Real.exp ((∑ e, r e) * τ) * ‖f‖ / M := by
        rw [div_mul_eq_mul_div]
        refine div_le_div₀ (by positivity) ?_ (Nat.cast_pos.mpr hM0)
          (le_add_of_nonneg_left (Nat.cast_nonneg n))
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
          (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left ht.2 hR)) (Nat.cast_nonneg n))
          (norm_nonneg f)
    _ < ε := hM

/-- **The moment equation with the holding generator, as a derivative**: for `t > 0`,
`d/dt D_t f = D_t(K f) + D_t(B f)`. -/
theorem hasDerivAt_decisionDual [Fintype H] [DecidableEq H] [Fintype E] {c : ℝ} {r : E → ℝ}
    (hc : 0 ≤ c) (hr : ∀ e, 0 ≤ r e) (T : E → H → H → H) {p : H → ℝ} (hp0 : ∀ h, 0 ≤ p h)
    (hp : ∑ h, p h = 1) (n : ℕ) (f : (Fin n → H) → ℝ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s ↦ decisionDual c r T p n s f)
      (decisionDual c r T p n t (holdingGenerator c r n f) +
        decisionDual c r T p (n + 1) t (decisionSubstitution r T n f)) t := by
  have hF : ContinuousOn (fun s ↦ decisionDual c r T p n s (holdingGenerator c r n f) +
      decisionDual c r T p (n + 1) s (decisionSubstitution r T n f)) (Set.Icc 0 (t + 1)) :=
    (continuousOn_decisionDual hc hr T hp0 hp n _ (t + 1)).add
      (continuousOn_decisionDual hc hr T hp0 hp (n + 1) _ (t + 1))
  have hint : IntervalIntegrable (fun s ↦ decisionDual c r T p n s (holdingGenerator c r n f) +
      decisionDual c r T p (n + 1) s (decisionSubstitution r T n f)) volume 0 t :=
    (hF.mono (Set.Icc_subset_Icc_right (by linarith))).intervalIntegrable_of_Icc ht.le
  have hmeas := (hF.mono Set.Ioo_subset_Icc_self).stronglyMeasurableAtFilter (μ := volume)
    isOpen_Ioo t ⟨ht, by linarith⟩
  have h := (intervalIntegral.integral_hasDerivAt_right hint hmeas
    (hF.continuousAt (Icc_mem_nhds ht (by linarith)))).const_add (samplingObservable f p)
  refine h.congr_of_eventuallyEq ?_
  filter_upwards [Ioi_mem_nhds ht] with s hs
  rw [← decisionDual_sub_eq_integral hc hr T hp0 hp n (le_of_lt hs) f]
  ring

/-- The dual expectation is additive at nonnegative times. -/
theorem decisionDual_add [Fintype H] [DecidableEq H] [Fintype E] {c : ℝ} {r : E → ℝ}
    (hc : 0 ≤ c) (hr : ∀ e, 0 ≤ r e) (T : E → H → H → H) {p : H → ℝ} (hp0 : ∀ h, 0 ≤ p h)
    (hp : ∑ h, p h = 1) (n : ℕ) {t : ℝ} (ht : 0 ≤ t) (f g : (Fin n → H) → ℝ) :
    decisionDual c r T p n t (f + g) = decisionDual c r T p n t f + decisionDual c r T p n t g :=
  (hasSum_dysonMoment hc hr T hp0 hp n ht (f + g)).unique (by
    simpa only [map_add] using
      (hasSum_dysonMoment hc hr T hp0 hp n ht f).add (hasSum_dysonMoment hc hr T hp0 hp n ht g))

/-- The dual expectation is homogeneous at nonnegative times. -/
theorem decisionDual_smul [Fintype H] [DecidableEq H] [Fintype E] {c : ℝ} {r : E → ℝ}
    (hc : 0 ≤ c) (hr : ∀ e, 0 ≤ r e) (T : E → H → H → H) {p : H → ℝ} (hp0 : ∀ h, 0 ≤ p h)
    (hp : ∑ h, p h = 1) (n : ℕ) {t : ℝ} (ht : 0 ≤ t) (d : ℝ) (f : (Fin n → H) → ℝ) :
    decisionDual c r T p n t (d • f) = d * decisionDual c r T p n t f :=
  (hasSum_dysonMoment hc hr T hp0 hp n ht (d • f)).unique (by
    simpa only [map_smul, smul_eq_mul] using (hasSum_dysonMoment hc hr T hp0 hp n ht f).mul_left d)

/-- **The holding generator and one decision are the backward generator** inside the dual
expectation: `D_t(K f) + D_t(B f) = c ∑_{a<b} (D_t(C_ab f) - D_t f) + ∑_e r_e ∑_a
(D_t(B_{a,e} f) - D_t f)`, for `t ≥ 0`. -/
theorem decisionDual_holdingGenerator_add [Fintype H] [DecidableEq H] [Fintype E] {c : ℝ}
    {r : E → ℝ} (hc : 0 ≤ c) (hr : ∀ e, 0 ≤ r e) (T : E → H → H → H) {p : H → ℝ}
    (hp0 : ∀ h, 0 ≤ p h) (hp : ∑ h, p h = 1) (n : ℕ) {t : ℝ} (ht : 0 ≤ t)
    (f : (Fin n → H) → ℝ) :
    decisionDual c r T p n t (holdingGenerator c r n f) +
        decisionDual c r T p (n + 1) t (decisionSubstitution r T n f) =
      c * ∑ b, ∑ a ∈ Iio b,
          (decisionDual c r T p n t (coalesceArguments a b f) - decisionDual c r T p n t f) +
        ∑ e, r e * ∑ a,
          (decisionDual c r T p (n + 1) t (decisionBranch (T e) a f) -
            decisionDual c r T p n t f) := by
  have hs : ∀ (m : ℕ) (g : (Fin m → H) → ℝ),
      HasSum (fun k ↦ dysonMoment c r T p k m t g) (decisionDual c r T p m t g) :=
    fun m g ↦ hasSum_dysonMoment hc hr T hp0 hp m ht g
  have hK : HasSum (fun k ↦ dysonMoment c r T p k n t (holdingGenerator c r n f))
      (c * ∑ b, ∑ a ∈ Iio b, decisionDual c r T p n t (coalesceArguments a b f) -
        dualExitRate c r n * decisionDual c r T p n t f) := by
    have h := ((hasSum_sum (s := univ) fun b _ ↦ hasSum_sum (s := Iio b) fun a _ ↦
      hs n (coalesceArguments a b f)) |>.mul_left c).sub ((hs n f).mul_left (dualExitRate c r n))
    convert h using 1
    funext k
    simp only [holdingGenerator_apply, pairSubstitution, map_sub, map_smul, map_sum, smul_eq_mul,
      LinearMap.coe_mk, AddHom.coe_mk]
  have hB : HasSum (fun k ↦ dysonMoment c r T p k (n + 1) t (decisionSubstitution r T n f))
      (∑ e, r e * ∑ a, decisionDual c r T p (n + 1) t (decisionBranch (T e) a f)) := by
    have h := hasSum_sum (s := univ) fun e _ ↦
      (hasSum_sum (s := univ) fun a _ ↦ hs (n + 1) (decisionBranch (T e) a f)).mul_left (r e)
    convert h using 1
    funext k
    simp only [decisionSubstitution, map_sum, map_smul, smul_eq_mul, LinearMap.coe_mk,
      AddHom.coe_mk]
  have hcoal : ∀ b : Fin n, ∑ a ∈ Iio b,
      (decisionDual c r T p n t (coalesceArguments a b f) - decisionDual c r T p n t f) =
        ∑ a ∈ Iio b, decisionDual c r T p n t (coalesceArguments a b f) -
          ((Iio b).card : ℝ) * decisionDual c r T p n t f := fun b ↦ by
    rw [sum_sub_distrib, sum_const, nsmul_eq_mul]
  have hdec : ∀ e, r e * ∑ a : Fin n,
      (decisionDual c r T p (n + 1) t (decisionBranch (T e) a f) - decisionDual c r T p n t f) =
        r e * (∑ a, decisionDual c r T p (n + 1) t (decisionBranch (T e) a f) -
          n * decisionDual c r T p n t f) := fun e ↦ by
    rw [sum_sub_distrib, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [(hs n _).unique hK, (hs (n + 1) _).unique hB, dualExitRate,
    sum_congr rfl fun b _ ↦ hcoal b, sum_congr rfl fun e _ ↦ hdec e]
  simp only [mul_sub, sum_sub_distrib, ← sum_mul]
  ring

/-- **Theorem 6, existence: the integrated moment equation of the backward circuit.** For `c ≥ 0`,
`r ≥ 0`, a probability vector `p` and `t ≥ 0`, the dual expectation `D_t f = E_f[H_{f_t}(p)]`
obeys `D_t f - H_f(p) = ∫_0^t (L D_s)(f) ds`, where `L` is the backward generator of
`SamplingDuality`: coalescence of every pair at rate `c` and decision branching of every argument
by every event at its rate, each read by the dual expectation at the new arity. -/
theorem decisionDual_moment_equation [Fintype H] [DecidableEq H] [Fintype E] {c : ℝ}
    {r : E → ℝ} (hc : 0 ≤ c) (hr : ∀ e, 0 ≤ r e) (T : E → H → H → H) {p : H → ℝ}
    (hp0 : ∀ h, 0 ≤ p h) (hp : ∑ h, p h = 1) (n : ℕ) {t : ℝ} (ht : 0 ≤ t)
    (f : (Fin n → H) → ℝ) :
    decisionDual c r T p n t f - samplingObservable f p = ∫ s in (0 : ℝ)..t,
      (c * ∑ b, ∑ a ∈ Iio b,
          (decisionDual c r T p n s (coalesceArguments a b f) - decisionDual c r T p n s f) +
        ∑ e, r e * ∑ a,
          (decisionDual c r T p (n + 1) s (decisionBranch (T e) a f) -
            decisionDual c r T p n s f)) := by
  rw [decisionDual_sub_eq_integral hc hr T hp0 hp n ht f]
  refine intervalIntegral.integral_congr fun s hs ↦ ?_
  rw [Set.uIcc_of_le ht] at hs
  exact decisionDual_holdingGenerator_add hc hr T hp0 hp n hs.1 f

/-- **Theorem 6, existence: the moment equation as a derivative.** For `t > 0`,
`d/dt D_t f = c ∑_{a<b} (D_t(C_ab f) - D_t f) + ∑_e r_e ∑_a (D_t(B_{a,e} f) - D_t f)`. -/
theorem hasDerivAt_decisionDual_moment_equation [Fintype H] [DecidableEq H] [Fintype E] {c : ℝ}
    {r : E → ℝ} (hc : 0 ≤ c) (hr : ∀ e, 0 ≤ r e) (T : E → H → H → H) {p : H → ℝ}
    (hp0 : ∀ h, 0 ≤ p h) (hp : ∑ h, p h = 1) (n : ℕ) (f : (Fin n → H) → ℝ) {t : ℝ}
    (ht : 0 < t) :
    HasDerivAt (fun s ↦ decisionDual c r T p n s f)
      (c * ∑ b, ∑ a ∈ Iio b,
          (decisionDual c r T p n t (coalesceArguments a b f) - decisionDual c r T p n t f) +
        ∑ e, r e * ∑ a,
          (decisionDual c r T p (n + 1) t (decisionBranch (T e) a f) -
            decisionDual c r T p n t f)) t :=
  (hasDerivAt_decisionDual hc hr T hp0 hp n f ht).congr_deriv
    (decisionDual_holdingGenerator_add hc hr T hp0 hp n ht.le f)

end

end Descent.Pangenome.AncestralLocality
