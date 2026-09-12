/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Pangenome.AncestralLocality.CoalescentDualSemigroup
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
  let P : ((Fin n → H) → ℝ) →L[ℝ] ((Fin n → H) → ℝ) :=
    LinearMap.toContinuousLinearMap (pairSubstitution n)
  have hP : ‖P‖ ≤ ∑ b : Fin n, ((Iio b).card : ℝ) :=
    ContinuousLinearMap.opNorm_le_bound _ (sum_nonneg fun _ _ ↦ Nat.cast_nonneg _)
      fun g ↦ norm_pairSubstitution_le g
  have hexp : ∀ x : ((Fin n → H) → ℝ) →L[ℝ] ((Fin n → H) → ℝ),
      ‖NormedSpace.exp ℝ x‖ ≤ Real.exp ‖x‖ := by
    intro x
    rw [NormedSpace.exp_eq_tsum, Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum]
    refine (norm_tsum_le_tsum_norm (NormedSpace.norm_expSeries_summable' x)).trans
      (Summable.tsum_le_tsum (fun k ↦ ?_) (NormedSpace.norm_expSeries_summable' x)
        (NormedSpace.expSeries_summable' ‖x‖))
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
  have hsplit : t • holdingGenerator c r n = t • c • P + (-(t * dualExitRate c r n)) • 1 := by
    rw [holdingGenerator, smul_sub, smul_smul t (dualExitRate c r n), neg_smul,
      ← sub_eq_add_neg]
  have hS : holdingSemigroup c r n t =
      Real.exp (-(t * dualExitRate c r n)) • NormedSpace.exp ℝ (t • c • P) := by
    rw [holdingSemigroup, hsplit,
      NormedSpace.exp_add_of_commute ((Commute.one_right _).smul_right _), hscalar,
      mul_smul_comm, mul_one]
  have hnorm : ‖t • c • P‖ ≤ t * (c * ∑ b : Fin n, ((Iio b).card : ℝ)) := by
    rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg ht,
      abs_of_nonneg hc]
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hP hc) ht
  calc ‖holdingSemigroup c r n t f‖ ≤ ‖holdingSemigroup c r n t‖ * ‖f‖ :=
        (holdingSemigroup c r n t).le_opNorm f
    _ ≤ Real.exp (-(n * (∑ e, r e) * t)) * ‖f‖ := by
        refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg f)
        rw [hS, norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
        calc Real.exp (-(t * dualExitRate c r n)) * ‖NormedSpace.exp ℝ (t • c • P)‖
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

end

end Descent.Pangenome.AncestralLocality
