/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.BanachEulerExponential
import Descent.Coalescent.StructuredPresentDay
import Mathlib.Analysis.Matrix
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.SpecificLimits.Basic

assert_below Descent.Decision Descent.Program

/-!
# Closed sets invariant under a positively approximated generator

This module proves NOTE1 Theorem 1 in its abstract form. The hypothesis is exactly (3) of
NOTE1: a family of maps `S h`, one for each positive step size, each of which carries a
closed set `C` into itself, together with a matrix `A` and a remainder bound `ε` vanishing as
the step size decreases to zero, such that `S h v` agrees with the Euler step
`v + h A v` to within `h · ε h` uniformly on `C`. The conclusion is (4): the semigroup
`Coalescent.matrixExponential A t` carries `C` into itself for every `t ≥ 0`.

Nothing about `S` beyond those two properties is used. In the intended application `S h` is
the map sending a low-order moment vector to the moment vector of the law obtained by pushing
a realizing law through the microscopic probability kernel `K_h` of NOTE1 §2.3, so that
`S h` preserves the realization body because a probability kernel maps probability laws to
probability laws. That `S` is not canonical and involves a choice of realizing law is
irrelevant here: only the two displayed properties enter.

The proof is the telescoping estimate NOTE1 (5) made exact. Fixing `t > 0` and taking the
step size `t / n`, the `n`-fold iterate of `S` started at `v` differs from the Euler product
`(1 + (t/n) A)^n v` by at most `n · (1 + (t/n)‖A‖)^n · (t/n) · ε(t/n)`, which is bounded by
`t · exp(t‖A‖) · ε(t/n)` and therefore tends to zero. The Euler products converge to the
exponential by `Descent.Portability.BanachEulerExponential.euler_tends_exp`, transported
through the continuous linear map `M ↦ M v`. The iterates lie in `C`, so the limit does too.
The matrix norm is the maximum absolute row-sum norm, for which
`Matrix.linfty_opNorm_mulVec` is the operator bound on the supremum norm of vectors.

The bound is proved for a fixed step size and all iteration counts as
`norm_iterate_sub_euler_le`, in the sharpened form `n · b^n · h · ε h` rather than the
geometric sum `(∑_{k<n} b^k) · h · ε h` of NOTE1 (5); the two differ only by the trivial
bound `b^k ≤ b^n`.

What is NOT proved here: the time-varying case of NOTE1 §2.4, and the existence of any
particular `S` (the corpus instances are constructed elsewhere). The result is stated for a
closed `C`; compactness is never used.

## Empirical status

None. The bodies here are algebra and analysis: a telescoping norm estimate, a limit of
Euler products, and the closedness of a set. No measurement bears on them.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.EulerInvariantSet

open scoped Matrix.Norms.Operator

/-- The `n`-fold iterate of the step map at a fixed step size. -/
def iterateStep {ι : Type*} (S : ℝ → (ι → ℝ) → (ι → ℝ)) (h : ℝ) (v : ι → ℝ) : ℕ → ι → ℝ
  | 0 => v
  | n + 1 => S h (iterateStep S h v n)

/-- Every iterate of a step map that preserves a set stays in that set. -/
theorem iterateStep_mem {ι : Type*} (S : ℝ → (ι → ℝ) → (ι → ℝ)) (C : Set (ι → ℝ))
    (hS : ∀ h, 0 < h → ∀ v ∈ C, S h v ∈ C) (h : ℝ) (hh : 0 < h) (v : ι → ℝ) (hv : v ∈ C)
    (n : ℕ) : iterateStep S h v n ∈ C := by
  induction n with
  | zero => exact hv
  | succ n ih => exact hS h hh _ ih

/-- Evaluating a matrix against a fixed vector is linear in the matrix. This is the
vector-valued analogue of the coordinatewise map used in
`Descent.Portability.ContinuousTurnoverSemigroup`. -/
noncomputable def mulVecMap {ι : Type*} [Fintype ι] (v : ι → ℝ) :
    Matrix ι ι ℝ →ₗ[ℝ] (ι → ℝ) where
  toFun M := M.mulVec v
  map_add' M N := by simp [Matrix.add_mulVec]
  map_smul' c M := by simp [Matrix.smul_mulVec]

/-- Evaluation of the linear matrix-to-vector map. -/
@[simp] theorem mulVecMap_apply {ι : Type*} [Fintype ι] (v : ι → ℝ) (M : Matrix ι ι ℝ) :
    mulVecMap v M = M.mulVec v := rfl

/-- One Euler step expands a vector by at most the factor `1 + h ‖A‖` in supremum norm. -/
theorem norm_euler_step_le {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℝ)
    (h : ℝ) (hh : 0 ≤ h) (w : ι → ℝ) :
    ‖(1 + h • A).mulVec w‖ ≤ (1 + h * ‖A‖) * ‖w‖ := by
  have hexpand : (1 + h • A).mulVec w = w + h • A.mulVec w := by
    rw [Matrix.add_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec]
  rw [hexpand]
  calc ‖w + h • A.mulVec w‖ ≤ ‖w‖ + ‖h • A.mulVec w‖ := norm_add_le _ _
    _ = ‖w‖ + h * ‖A.mulVec w‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hh]
    _ ≤ ‖w‖ + h * (‖A‖ * ‖w‖) := by
        have hmul : ‖A.mulVec w‖ ≤ ‖A‖ * ‖w‖ := Matrix.linfty_opNorm_mulVec A w
        exact add_le_add_left (mul_le_mul_of_nonneg_left hmul hh) _
    _ = (1 + h * ‖A‖) * ‖w‖ := by ring

/-- One step of the telescoping estimate NOTE1 (5): the step map applied to a point of `C`
differs from the Euler step applied to any comparison point by the local truncation error
plus the expanded distance between the two points. -/
theorem norm_step_sub_le {ι : Type*} [Fintype ι] [DecidableEq ι] (C : Set (ι → ℝ))
    (A : Matrix ι ι ℝ) (S : ℝ → (ι → ℝ) → (ι → ℝ)) (ε : ℝ → ℝ)
    (hexp : ∀ h, 0 < h → ∀ v ∈ C, ‖S h v - (v + h • A.mulVec v)‖ ≤ h * ε h)
    (h : ℝ) (hh : 0 < h) (x y : ι → ℝ) (hx : x ∈ C) :
    ‖S h x - (1 + h • A).mulVec y‖ ≤ h * ε h + (1 + h * ‖A‖) * ‖x - y‖ := by
  have hdecomp : S h x - (1 + h • A).mulVec y
      = (S h x - (x + h • A.mulVec x)) + (1 + h • A).mulVec (x - y) := by
    simp only [Matrix.add_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec, Matrix.mulVec_sub]
    abel
  rw [hdecomp]
  exact (norm_add_le _ _).trans
    (add_le_add (hexp h hh x hx) (norm_euler_step_le A h hh.le (x - y)))

/-- The telescoping estimate NOTE1 (5) at a fixed step size: after `n` steps the iterate of
the step map differs from the `n`-th Euler product by at most `n · (1 + h‖A‖)^n · h · ε h`. -/
theorem norm_iterate_sub_euler_le {ι : Type*} [Fintype ι] [DecidableEq ι] (C : Set (ι → ℝ))
    (A : Matrix ι ι ℝ) (S : ℝ → (ι → ℝ) → (ι → ℝ))
    (hS : ∀ h, 0 < h → ∀ v ∈ C, S h v ∈ C) (ε : ℝ → ℝ)
    (hexp : ∀ h, 0 < h → ∀ v ∈ C, ‖S h v - (v + h • A.mulVec v)‖ ≤ h * ε h)
    (h : ℝ) (hh : 0 < h) (v : ι → ℝ) (hv : v ∈ C) (n : ℕ) :
    ‖iterateStep S h v n - ((1 + h • A) ^ n).mulVec v‖
      ≤ (n : ℝ) * (1 + h * ‖A‖) ^ n * (h * ε h) := by
  have hb : (1 : ℝ) ≤ 1 + h * ‖A‖ := by
    have := mul_nonneg hh.le (norm_nonneg A)
    linarith
  have hstepnn : 0 ≤ h * ε h :=
    le_trans (norm_nonneg _) (hexp h hh v hv)
  induction n with
  | zero => simp [iterateStep]
  | succ n ih =>
    have hxmem : iterateStep S h v n ∈ C := iterateStep_mem S C hS h hh v hv n
    have hpow : ((1 + h • A) ^ (n + 1)).mulVec v
        = (1 + h • A).mulVec (((1 + h • A) ^ n).mulVec v) := by
      rw [pow_succ']
      exact (Matrix.mulVec_mulVec v (1 + h • A) ((1 + h • A) ^ n)).symm
    have hiter : iterateStep S h v (n + 1) = S h (iterateStep S h v n) := rfl
    rw [hiter, hpow]
    refine (norm_step_sub_le C A S ε hexp h hh _ _ hxmem).trans ?_
    have hone : (1 : ℝ) ≤ (1 + h * ‖A‖) ^ (n + 1) := one_le_pow₀ hb
    calc h * ε h + (1 + h * ‖A‖)
            * ‖iterateStep S h v n - ((1 + h • A) ^ n).mulVec v‖
        ≤ h * ε h + (1 + h * ‖A‖)
            * ((n : ℝ) * (1 + h * ‖A‖) ^ n * (h * ε h)) := by
          exact add_le_add_left
            (mul_le_mul_of_nonneg_left ih (by linarith)) _
      _ = (h * ε h) * (1 + (n : ℝ) * (1 + h * ‖A‖) ^ (n + 1)) := by ring
      _ ≤ (h * ε h) * (((n : ℝ) + 1) * (1 + h * ‖A‖) ^ (n + 1)) := by
          have hgap : 1 + (n : ℝ) * (1 + h * ‖A‖) ^ (n + 1)
              ≤ ((n : ℝ) + 1) * (1 + h * ‖A‖) ^ (n + 1) := by nlinarith
          exact mul_le_mul_of_nonneg_left hgap hstepnn
      _ = ((n + 1 : ℕ) : ℝ) * (1 + h * ‖A‖) ^ (n + 1) * (h * ε h) := by
          push_cast
          ring

/-- **NOTE1 Theorem 1.** If a closed set `C` is preserved by maps `S h` that agree with the
Euler step of `A` to within `h · ε h` uniformly on `C`, with `ε` vanishing as the step size
decreases to zero, then `C` is preserved by the semigroup generated by `A`: for every
`t ≥ 0` and every `v ∈ C`, `exp(tA) v ∈ C`. Assumes: `C` closed, `S` preserving `C`, and the
uniform expansion; no compactness and no convexity are used. -/
theorem exp_mulVec_mem_of_euler_approx {ι : Type*} [Fintype ι] [DecidableEq ι]
    (C : Set (ι → ℝ)) (hC : IsClosed C) (A : Matrix ι ι ℝ)
    (S : ℝ → (ι → ℝ) → (ι → ℝ)) (hS : ∀ h, 0 < h → ∀ v ∈ C, S h v ∈ C)
    (ε : ℝ → ℝ) (hε : Filter.Tendsto ε (nhdsWithin 0 (Set.Ioi 0)) (nhds 0))
    (hexp : ∀ h, 0 < h → ∀ v ∈ C, ‖S h v - (v + h • A.mulVec v)‖ ≤ h * ε h)
    (t : ℝ) (ht : 0 ≤ t) (v : ι → ℝ) (hv : v ∈ C) :
    (Coalescent.matrixExponential A t).mulVec v ∈ C := by
  rw [Coalescent.matrixExponential_eq_normedSpace_exp]
  rcases ht.eq_or_lt with htz | htp
  · rw [← htz, zero_smul, NormedSpace.exp_zero, Matrix.one_mulVec]
    exact hv
  have hpos : ∀ n : ℕ, 0 < n → 0 < t / (n : ℝ) := by
    intro n hn
    exact div_pos htp (by exact_mod_cast hn)
  have hmat : ∀ n : ℕ,
      (1 : Matrix ι ι ℝ) + (t / (n : ℝ)) • A = 1 + (n : ℝ)⁻¹ • (t • A) := by
    intro n
    have hs : (n : ℝ)⁻¹ • (t • A) = (t / (n : ℝ)) • A := by
      rw [smul_smul, div_eq_mul_inv, mul_comm]
    rw [hs]
  have hEuler : Filter.Tendsto
      (fun n : ℕ ↦ ((1 + (t / (n : ℝ)) • A) ^ n).mulVec v) Filter.atTop
      (nhds ((NormedSpace.exp ℝ (t • A)).mulVec v)) := by
    have hcont : Continuous (mulVecMap v) :=
      (mulVecMap v).continuous_of_finiteDimensional
    have hfun : (fun n : ℕ ↦ ((1 + (t / (n : ℝ)) • A) ^ n).mulVec v)
        = fun n : ℕ ↦ (mulVecMap v) ((1 + (n : ℝ)⁻¹ • (t • A)) ^ n) := by
      funext n
      rw [hmat n]
      rfl
    rw [hfun]
    exact (hcont.tendsto _).comp (BanachEulerExponential.euler_tends_exp (t • A))
  have hbound : ∀ n : ℕ, 0 < n →
      ‖iterateStep S (t / (n : ℝ)) v n - ((1 + (t / (n : ℝ)) • A) ^ n).mulVec v‖
        ≤ t * Real.exp (t * ‖A‖) * ε (t / (n : ℝ)) := by
    intro n hn
    have hh : 0 < t / (n : ℝ) := hpos n hn
    have hn0 : ((n : ℝ)) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
    have hmain := norm_iterate_sub_euler_le C A S hS ε hexp (t / (n : ℝ)) hh v hv n
    have hεnn : 0 ≤ ε (t / (n : ℝ)) := by
      have h0 : 0 ≤ (t / (n : ℝ)) * ε (t / (n : ℝ)) :=
        le_trans (norm_nonneg _) (hexp (t / (n : ℝ)) hh v hv)
      nlinarith [h0, hh]
    have hnn : (0 : ℝ) ≤ 1 + (t / (n : ℝ)) * ‖A‖ := by
      have := mul_nonneg hh.le (norm_nonneg A)
      linarith
    have hle : 1 + (t / (n : ℝ)) * ‖A‖ ≤ Real.exp ((t / (n : ℝ)) * ‖A‖) := by
      have hexpge := Real.add_one_le_exp ((t / (n : ℝ)) * ‖A‖)
      linarith
    have hexpb : (1 + (t / (n : ℝ)) * ‖A‖) ^ n ≤ Real.exp (t * ‖A‖) := by
      calc (1 + (t / (n : ℝ)) * ‖A‖) ^ n
          ≤ (Real.exp ((t / (n : ℝ)) * ‖A‖)) ^ n := pow_le_pow_left₀ hnn hle n
        _ = Real.exp ((n : ℝ) * ((t / (n : ℝ)) * ‖A‖)) :=
            (Real.exp_nat_mul ((t / (n : ℝ)) * ‖A‖) n).symm
        _ = Real.exp (t * ‖A‖) := by
            congr 1
            field_simp
    refine hmain.trans ?_
    have hcollapse : (n : ℝ) * (1 + (t / (n : ℝ)) * ‖A‖) ^ n
          * ((t / (n : ℝ)) * ε (t / (n : ℝ)))
        = t * (1 + (t / (n : ℝ)) * ‖A‖) ^ n * ε (t / (n : ℝ)) := by
      field_simp
    rw [hcollapse]
    have hmul : t * (1 + (t / (n : ℝ)) * ‖A‖) ^ n ≤ t * Real.exp (t * ‖A‖) :=
      mul_le_mul_of_nonneg_left hexpb htp.le
    exact mul_le_mul_of_nonneg_right hmul hεnn
  have hεlim : Filter.Tendsto (fun n : ℕ ↦ ε (t / (n : ℝ))) Filter.atTop (nhds 0) := by
    refine hε.comp ?_
    rw [tendsto_nhdsWithin_iff]
    refine ⟨tendsto_const_div_atTop_nhds_zero_nat t, ?_⟩
    filter_upwards [Filter.eventually_gt_atTop 0] with n hn
    simpa using hpos n hn
  have hdiff : Filter.Tendsto
      (fun n : ℕ ↦ iterateStep S (t / (n : ℝ)) v n
        - ((1 + (t / (n : ℝ)) • A) ^ n).mulVec v) Filter.atTop (nhds 0) := by
    refine squeeze_zero_norm'
      (a := fun n : ℕ ↦ t * Real.exp (t * ‖A‖) * ε (t / (n : ℝ))) ?_ ?_
    · filter_upwards [Filter.eventually_gt_atTop 0] with n hn
      exact hbound n hn
    · have hscaled := hεlim.const_mul (t * Real.exp (t * ‖A‖))
      simpa using hscaled
  have hiter : Filter.Tendsto (fun n : ℕ ↦ iterateStep S (t / (n : ℝ)) v n) Filter.atTop
      (nhds ((NormedSpace.exp ℝ (t • A)).mulVec v)) := by
    have hsum := hdiff.add hEuler
    rw [zero_add] at hsum
    exact hsum.congr fun n ↦ by abel
  refine hC.mem_of_tendsto hiter ?_
  filter_upwards [Filter.eventually_gt_atTop 0] with n hn
  exact iterateStep_mem S C hS (t / (n : ℝ)) (hpos n hn) v hv n

end Descent.Portability.EulerInvariantSet
