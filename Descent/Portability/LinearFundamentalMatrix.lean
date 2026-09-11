/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Coalescent.ExpRemainder
import Descent.Coalescent.StructuredPresentDay
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Matrix
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Topology.UniformSpace.HeineCantor

assert_below Descent.Decision Descent.Program

/-!
# The fundamental matrix of a time-varying linear moment system

NOTE1 section 2.4 extends the realizability theorem from piecewise-constant demographic
histories to time-varying rates.  Its first step is the fundamental matrix `U` of the linear
system `U' = A(t) U`, `U(0) = 1`, for a finite-dimensional generator path `A`.  This module
constructs it for every continuous generator path, by Picard iteration in the Banach algebra of
real matrices under the operator norm, and records the facts the realizability argument uses.

`picardIterate A T` is the sequence of Picard iterates: the identity, then the primitive of
`A * U_n` from `0`, with its upper limit clamped into the horizon `[0, T]` so that every iterate
is a continuous function on the whole line and uniformly bounded.
`norm_picardIterate_le` is the factorial bound `‖U_n(t)‖ ≤ (K t)^n / n!` when `‖A‖ ≤ K` on the
horizon, `fundamentalMatrix A T` is the sum of the iterates, and
`fundamentalMatrix_eq_integral` is the integral equation `U(t) = 1 + ∫₀ᵗ A U` on the horizon,
obtained by dominated convergence.  `fundamentalMatrix_hasDerivWithinAt` and
`fundamentalMatrix_zero` are the initial value problem itself, by the fundamental theorem of
calculus, and `norm_fundamentalMatrix_le` bounds the solution by `exp (K T)`.
`norm_exp_matrix_le` bounds a matrix exponential by the exponential of the norm, with no
nonemptiness assumption on the index.

Scope.  The generator path is assumed continuous.  NOTE1 section 2.4 allows measurable rates
with integrable norm, whose fundamental matrix is absolutely continuous and solves the equation
only almost everywhere; that Carathéodory case is not formalized here.  Uniqueness of the
solution is not proved either; the theorems below are about the constructed series.

## Empirical status

None.  The bodies here are calculus in a finite-dimensional Banach algebra: power-series bounds,
interval integrals and derivatives of matrix-valued functions, so no measurement can bear on
them.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.LinearFundamentalMatrix

open MeasureTheory
open scoped Matrix.Norms.Operator

noncomputable section

/-! ## Clamped time and matrix norms -/

/-- Time clamped into the horizon `[0, T]`. -/
def clampTime (T t : ℝ) : ℝ := max 0 (min t T)

/-- A clamped time lies in the horizon. -/
theorem clampTime_mem {T : ℝ} (hT : 0 ≤ T) (t : ℝ) : clampTime T t ∈ Set.Icc 0 T :=
  ⟨le_max_left _ _, max_le hT (min_le_right _ _)⟩

/-- Clamping leaves a time inside the horizon unchanged. -/
theorem clampTime_of_mem {T t : ℝ} (ht : t ∈ Set.Icc 0 T) : clampTime T t = t := by
  rw [clampTime, min_eq_left ht.2, max_eq_right ht.1]

/-- Clamping is continuous. -/
theorem continuous_clampTime (T : ℝ) : Continuous (clampTime T) :=
  continuous_const.max (continuous_id.min continuous_const)

/-- The identity matrix has operator norm at most one, with no nonemptiness assumption on the
index. -/
theorem norm_identityMatrix_le_one {ι : Type*} [Fintype ι] [DecidableEq ι] :
    ‖(1 : Matrix ι ι ℝ)‖ ≤ 1 := by
  rw [← Matrix.diagonal_one, Matrix.linfty_opNorm_diagonal]
  refine (pi_norm_le_iff_of_nonneg zero_le_one).mpr fun _ ↦ ?_
  simp

/-- A matrix exponential is bounded in operator norm by the real exponential of the norm of
its argument. -/
theorem norm_exp_matrix_le {ι : Type*} [Fintype ι] [DecidableEq ι] (X : Matrix ι ι ℝ) :
    ‖NormedSpace.exp ℝ X‖ ≤ Real.exp ‖X‖ := by
  have hsplit : NormedSpace.exp ℝ X = 1 + X + (NormedSpace.exp ℝ X - 1 - X) := by abel
  have hremainder := Descent.norm_exp_sub_one_sub_self_le X
  have hone := norm_identityMatrix_le_one (ι := ι)
  have htriangle : ‖1 + X + (NormedSpace.exp ℝ X - 1 - X)‖ ≤
      ‖(1 : Matrix ι ι ℝ)‖ + ‖X‖ + ‖NormedSpace.exp ℝ X - 1 - X‖ :=
    (norm_add_le _ _).trans (add_le_add_right (norm_add_le _ _) _)
  rw [hsplit]
  linarith

/-! ## Picard iterates -/

/-- The Picard iterates of `U' = A(t) U`, `U(0) = 1`: the identity, then the primitive of
`A * U_n` from `0`, with the upper limit clamped into the horizon `[0, T]`. -/
def picardIterate {ι : Type*} [Fintype ι] [DecidableEq ι] (A : ℝ → Matrix ι ι ℝ) (T : ℝ) :
    ℕ → ℝ → Matrix ι ι ℝ
  | 0 => fun _ ↦ 1
  | n + 1 => fun t ↦ ∫ s in (0 : ℝ)..clampTime T t, A s * picardIterate A T n s

/-- Every Picard iterate of a continuous generator path is continuous on the whole line. -/
theorem continuous_picardIterate {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : ℝ → Matrix ι ι ℝ} (hA : Continuous A) (T : ℝ) :
    ∀ n, Continuous (picardIterate A T n)
  | 0 => continuous_const
  | n + 1 => by
      have hintegrand : Continuous fun s ↦ A s * picardIterate A T n s :=
        hA.mul (continuous_picardIterate hA T n)
      exact (intervalIntegral.continuous_primitive
        (fun a b ↦ hintegrand.intervalIntegrable a b) 0).comp (continuous_clampTime T)

/-- **The Picard iterates obey the factorial bound.**  If `‖A s‖ ≤ K` on the horizon, then the
`n`-th iterate at time `t` has norm at most `(K t)^n / n!`, with `t` clamped into the
horizon. -/
theorem norm_picardIterate_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : ℝ → Matrix ι ι ℝ} (hA : Continuous A) {T K : ℝ} (hT : 0 ≤ T) (hK : 0 ≤ K)
    (hbound : ∀ s ∈ Set.Icc 0 T, ‖A s‖ ≤ K) :
    ∀ n t, ‖picardIterate A T n t‖ ≤ (K * clampTime T t) ^ n / n.factorial
  | 0, t => by
      have hone := norm_identityMatrix_le_one (ι := ι)
      simpa [picardIterate] using hone
  | n + 1, t => by
      have hmem := clampTime_mem hT t
      have hstep : ‖∫ s in (0 : ℝ)..clampTime T t, A s * picardIterate A T n s‖ ≤
          ∫ s in (0 : ℝ)..clampTime T t, K ^ (n + 1) / n.factorial * s ^ n := by
        refine intervalIntegral.norm_integral_le_of_norm_le hmem.1
          (ae_of_all _ fun s hs ↦ ?_) (Continuous.intervalIntegrable (by fun_prop) _ _)
        have hsmem : s ∈ Set.Icc 0 T := ⟨hs.1.le, hs.2.trans hmem.2⟩
        have hprevious := norm_picardIterate_le hA hT hK hbound n s
        rw [clampTime_of_mem hsmem] at hprevious
        calc ‖A s * picardIterate A T n s‖ ≤ ‖A s‖ * ‖picardIterate A T n s‖ :=
              norm_mul_le _ _
          _ ≤ K * ((K * s) ^ n / n.factorial) :=
              mul_le_mul (hbound s hsmem) hprevious (norm_nonneg _) hK
          _ = K ^ (n + 1) / n.factorial * s ^ n := by ring
      have hvalue : ∫ s in (0 : ℝ)..clampTime T t, K ^ (n + 1) / n.factorial * s ^ n =
          (K * clampTime T t) ^ (n + 1) / (n + 1).factorial := by
        rw [intervalIntegral.integral_const_mul, integral_pow, zero_pow (Nat.succ_ne_zero n),
          sub_zero, Nat.factorial_succ]
        push_cast
        ring
      exact hstep.trans_eq hvalue

/-- The iterates are dominated, uniformly in time, by the exponential series at `K T`. -/
theorem norm_picardIterate_le_majorant {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : ℝ → Matrix ι ι ℝ} (hA : Continuous A) {T K : ℝ} (hT : 0 ≤ T) (hK : 0 ≤ K)
    (hbound : ∀ s ∈ Set.Icc 0 T, ‖A s‖ ≤ K) (n : ℕ) (t : ℝ) :
    ‖picardIterate A T n t‖ ≤ (K * T) ^ n / n.factorial := by
  refine (norm_picardIterate_le hA hT hK hbound n t).trans ?_
  have hmem := clampTime_mem hT t
  have hlow : 0 ≤ K * clampTime T t := mul_nonneg hK hmem.1
  have hhigh : K * clampTime T t ≤ K * T := mul_le_mul_of_nonneg_left hmem.2 hK
  have hfactorial : (0 : ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
  exact div_le_div_of_nonneg_right (pow_le_pow_left₀ hlow hhigh n) hfactorial.le

/-! ## The fundamental matrix -/

/-- The fundamental matrix of the generator path at horizon `T`: the sum of the Picard
iterates. -/
def fundamentalMatrix {ι : Type*} [Fintype ι] [DecidableEq ι] (A : ℝ → Matrix ι ι ℝ)
    (T t : ℝ) : Matrix ι ι ℝ :=
  ∑' n, picardIterate A T n t

/-- The Picard series converges absolutely at every time. -/
theorem summable_picardIterate {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : ℝ → Matrix ι ι ℝ} (hA : Continuous A) {T K : ℝ} (hT : 0 ≤ T) (hK : 0 ≤ K)
    (hbound : ∀ s ∈ Set.Icc 0 T, ‖A s‖ ≤ K) (t : ℝ) :
    Summable fun n ↦ picardIterate A T n t :=
  Summable.of_norm (Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _)
    (fun n ↦ norm_picardIterate_le_majorant hA hT hK hbound n t)
    (Real.summable_pow_div_factorial (K * T)))

/-- The fundamental matrix is continuous on the whole line. -/
theorem continuous_fundamentalMatrix {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : ℝ → Matrix ι ι ℝ} (hA : Continuous A) {T K : ℝ} (hT : 0 ≤ T) (hK : 0 ≤ K)
    (hbound : ∀ s ∈ Set.Icc 0 T, ‖A s‖ ≤ K) : Continuous (fundamentalMatrix A T) :=
  continuous_tsum (continuous_picardIterate hA T) (Real.summable_pow_div_factorial (K * T))
    (fun n t ↦ norm_picardIterate_le_majorant hA hT hK hbound n t)

/-- The fundamental matrix starts at the identity. -/
theorem fundamentalMatrix_zero {ι : Type*} [Fintype ι] [DecidableEq ι] (A : ℝ → Matrix ι ι ℝ)
    {T : ℝ} (hT : 0 ≤ T) : fundamentalMatrix A T 0 = 1 := by
  rw [fundamentalMatrix, tsum_eq_single 0]
  · rfl
  · intro n hn
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
    show ∫ s in (0 : ℝ)..clampTime T 0, A s * picardIterate A T m s = 0
    rw [clampTime_of_mem ⟨le_rfl, hT⟩, intervalIntegral.integral_same]

/-- **The integral equation.**  On the horizon the fundamental matrix satisfies
`U(t) = 1 + ∫₀ᵗ A(s) U(s) ds`: summing the Picard recursion and exchanging the sum with the
integral by dominated convergence. -/
theorem fundamentalMatrix_eq_integral {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : ℝ → Matrix ι ι ℝ} (hA : Continuous A) {T K : ℝ} (hT : 0 ≤ T) (hK : 0 ≤ K)
    (hbound : ∀ s ∈ Set.Icc 0 T, ‖A s‖ ≤ K) {t : ℝ} (ht : t ∈ Set.Icc 0 T) :
    fundamentalMatrix A T t = 1 + ∫ s in (0 : ℝ)..t, A s * fundamentalMatrix A T s := by
  have hsummable := summable_picardIterate hA hT hK hbound
  have hlimit : HasSum (fun n ↦ ∫ s in (0 : ℝ)..t, A s * picardIterate A T n s)
      (∫ s in (0 : ℝ)..t, A s * fundamentalMatrix A T s) := by
    refine intervalIntegral.hasSum_integral_of_dominated_convergence
      (fun n _ ↦ K * ((K * T) ^ n / n.factorial))
      (fun n ↦ (hA.mul (continuous_picardIterate hA T n)).aestronglyMeasurable)
      (fun n ↦ ae_of_all _ fun s hs ↦ ?_)
      (ae_of_all _ fun _ _ ↦ (Real.summable_pow_div_factorial (K * T)).mul_left K)
      (continuous_const.intervalIntegrable _ _)
      (ae_of_all _ fun s _ ↦ (hsummable s).hasSum.mul_left (A s))
    have hioc : s ∈ Set.Ioc 0 t := by rwa [Set.uIoc_of_le ht.1] at hs
    have hsmem : s ∈ Set.Icc 0 T := ⟨hioc.1.le, hioc.2.trans ht.2⟩
    exact (norm_mul_le _ _).trans (mul_le_mul (hbound s hsmem)
      (norm_picardIterate_le_majorant hA hT hK hbound n s) (norm_nonneg _) hK)
  have hshift : (fun n ↦ picardIterate A T (n + 1) t) =
      fun n ↦ ∫ s in (0 : ℝ)..t, A s * picardIterate A T n s := by
    funext n
    show (∫ s in (0 : ℝ)..clampTime T t, A s * picardIterate A T n s) =
      ∫ s in (0 : ℝ)..t, A s * picardIterate A T n s
    rw [clampTime_of_mem ht]
  have hvalue : ∑' n, picardIterate A T (n + 1) t =
      ∫ s in (0 : ℝ)..t, A s * fundamentalMatrix A T s := by
    rw [hshift]
    exact hlimit.tsum_eq
  rw [fundamentalMatrix, (hsummable t).tsum_eq_zero_add, hvalue]
  rfl

/-- **The fundamental matrix solves `U' = A(t) U` on the horizon.**  The derivative within
`[0, T]` at every time of the horizon is `A(t) U(t)`, by the fundamental theorem of calculus
applied to the integral equation. -/
theorem fundamentalMatrix_hasDerivWithinAt {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : ℝ → Matrix ι ι ℝ} (hA : Continuous A) {T K : ℝ} (hT : 0 ≤ T) (hK : 0 ≤ K)
    (hbound : ∀ s ∈ Set.Icc 0 T, ‖A s‖ ≤ K) {t : ℝ} (ht : t ∈ Set.Icc 0 T) :
    HasDerivWithinAt (fundamentalMatrix A T) (A t * fundamentalMatrix A T t)
      (Set.Icc 0 T) t := by
  have hcontinuous : Continuous fun s ↦ A s * fundamentalMatrix A T s :=
    hA.mul (continuous_fundamentalMatrix hA hT hK hbound)
  have hprimitive : HasDerivAt (fun u ↦ 1 + ∫ s in (0 : ℝ)..u, A s * fundamentalMatrix A T s)
      (A t * fundamentalMatrix A T t) t :=
    (intervalIntegral.integral_hasDerivAt_right (hcontinuous.intervalIntegrable 0 t)
      (hcontinuous.stronglyMeasurableAtFilter _ _) hcontinuous.continuousAt).const_add 1
  exact hprimitive.hasDerivWithinAt.congr
    (fun s hs ↦ fundamentalMatrix_eq_integral hA hT hK hbound hs)
    (fundamentalMatrix_eq_integral hA hT hK hbound ht)

/-- The fundamental matrix is bounded by `exp (K T)` at every time. -/
theorem norm_fundamentalMatrix_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : ℝ → Matrix ι ι ℝ} (hA : Continuous A) {T K : ℝ} (hT : 0 ≤ T) (hK : 0 ≤ K)
    (hbound : ∀ s ∈ Set.Icc 0 T, ‖A s‖ ≤ K) (t : ℝ) :
    ‖fundamentalMatrix A T t‖ ≤ Real.exp (K * T) := by
  have hmajorant := norm_picardIterate_le_majorant hA hT hK hbound
  have hnorms : Summable fun n ↦ ‖picardIterate A T n t‖ :=
    Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) (fun n ↦ hmajorant n t)
      (Real.summable_pow_div_factorial (K * T))
  have hexp : ∑' n : ℕ, (K * T) ^ n / (n.factorial : ℝ) = Real.exp (K * T) := by
    rw [Real.exp_eq_exp_ℝ]
    exact (NormedSpace.expSeries_div_hasSum_exp (𝕂 := ℝ) (K * T)).tsum_eq
  calc ‖fundamentalMatrix A T t‖ ≤ ∑' n, ‖picardIterate A T n t‖ :=
        norm_tsum_le_tsum_norm hnorms
    _ ≤ ∑' n : ℕ, (K * T) ^ n / (n.factorial : ℝ) :=
        hnorms.tsum_le_tsum (fun n ↦ hmajorant n t) (Real.summable_pow_div_factorial (K * T))
    _ = Real.exp (K * T) := hexp

end

end Descent.Portability.LinearFundamentalMatrix
