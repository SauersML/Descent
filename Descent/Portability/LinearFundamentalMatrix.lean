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

The realizability argument of NOTE1 section 2.4 needs three further facts, proved here for
continuous paths.  `norm_fundamentalMatrix_step_sub_le` compares one exact epoch `e^{h A(t)}`
with the fundamental matrix over `[t, t + h]` by the mean value inequality, and
`norm_fundamentalMatrix_sub_sampledProduct_le` is the discrete Gronwall estimate for the
product of such epochs along a uniform left-endpoint sampling, so `tendsto_sampledProduct`
says those products converge to `U(T)`.  `norm_fundamentalMatrix_sub_le` is the
variation-of-constants bound `‖U_A(T) - U_B(T)‖ ≤ e^{2 K T} ∫₀ᵀ ‖A - B‖`, proved iterate by
iterate (`norm_picardIterate_sub_le`), and `eventually_integral_norm_sample_sub_le` is the
`L¹` convergence of the left-endpoint step approximation `sampleTime`.

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
  have hremainder := Descent.Coalescent.norm_exp_sub_one_sub_self_le X
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
          sub_zero]
        have hsucc : ((n + 1).factorial : ℝ) = ((n : ℝ) + 1) * n.factorial := by
          rw [Nat.factorial_succ]
          push_cast
          ring
        rw [hsucc]
        generalize ((n : ℝ) + 1) = next
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


/-! ## Exact epochs against the fundamental matrix -/

/-- An exact epoch propagator is bounded by the exponential of the duration times the norm of
its generator. -/
theorem norm_matrixExponential_le {ι : Type*} [Fintype ι] [DecidableEq ι] (X : Matrix ι ι ℝ)
    {h : ℝ} (hh : 0 ≤ h) : ‖Coalescent.matrixExponential X h‖ ≤ Real.exp (h * ‖X‖) := by
  rw [Coalescent.matrixExponential_eq_normedSpace_exp]
  refine (norm_exp_matrix_le _).trans ?_
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hh]

/-- **One exact epoch against the fundamental matrix.**  If the generator path stays within `ε`
of its left-endpoint value on an interval `[t, t + h]` of the horizon, then the fundamental
matrix at `t + h` differs from the exact epoch `e^{h A(t)}` applied to `U(t)` by at most
`e^{h K} ε e^{K T} h`.  The comparison path `s ↦ e^{(t + h - s) A(t)} U(s)` has derivative
`e^{(t + h - s) A(t)} (A(s) - A(t)) U(s)`, and the mean value inequality bounds its change. -/
theorem norm_fundamentalMatrix_step_sub_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : ℝ → Matrix ι ι ℝ} (hA : Continuous A) {T K : ℝ} (hT : 0 ≤ T) (hK : 0 ≤ K)
    (hbound : ∀ s ∈ Set.Icc 0 T, ‖A s‖ ≤ K) {t h ε : ℝ} (ht : 0 ≤ t) (hh : 0 ≤ h)
    (hth : t + h ≤ T) (hclose : ∀ s ∈ Set.Icc t (t + h), ‖A s - A t‖ ≤ ε) :
    ‖fundamentalMatrix A T (t + h) -
        Coalescent.matrixExponential (A t) h * fundamentalMatrix A T t‖ ≤
      Real.exp (h * K) * ε * Real.exp (K * T) * h := by
  have hsub : Set.Icc t (t + h) ⊆ Set.Icc 0 T := fun s hs ↦ ⟨ht.trans hs.1, hs.2.trans hth⟩
  have hderiv : ∀ s ∈ Set.Icc t (t + h),
      HasDerivWithinAt (fun r ↦ NormedSpace.exp ℝ ((t + h - r) • A t) * fundamentalMatrix A T r)
        (NormedSpace.exp ℝ ((t + h - s) • A t) * ((A s - A t) * fundamentalMatrix A T s))
        (Set.Icc t (t + h)) s := by
    intro s hs
    have hexp : HasDerivAt (fun r : ℝ ↦ NormedSpace.exp ℝ ((t + h - r) • A t))
        ((-1 : ℝ) • (NormedSpace.exp ℝ ((t + h - s) • A t) * A t)) s :=
      HasDerivAt.scomp (g₁ := fun u : ℝ ↦ NormedSpace.exp ℝ (u • A t))
        (h := fun r : ℝ ↦ t + h - r)
        (hg := hasDerivAt_exp_smul_const (A t) (t + h - s))
        (hh := (hasDerivAt_id s).const_sub (t + h))
    have hU := (fundamentalMatrix_hasDerivWithinAt hA hT hK hbound (hsub hs)).mono hsub
    refine (hexp.hasDerivWithinAt.fun_mul hU).congr_deriv ?_
    simp only [neg_smul, one_smul]
    noncomm_ring
  have hslope : ∀ s ∈ Set.Ico t (t + h),
      ‖NormedSpace.exp ℝ ((t + h - s) • A t) * ((A s - A t) * fundamentalMatrix A T s)‖ ≤
        Real.exp (h * K) * ε * Real.exp (K * T) := by
    intro s hs
    have hsIcc : s ∈ Set.Icc t (t + h) := Set.Ico_subset_Icc_self hs
    have hgap : 0 ≤ t + h - s := by linarith [hs.2]
    have htmem : t ∈ Set.Icc 0 T := ⟨ht, by linarith⟩
    have hexp_le : ‖NormedSpace.exp ℝ ((t + h - s) • A t)‖ ≤ Real.exp (h * K) := by
      refine (norm_exp_matrix_le _).trans (Real.exp_le_exp.mpr ?_)
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hgap]
      exact mul_le_mul (by linarith [hs.1]) (hbound t htmem) (norm_nonneg _) hh
    have hclose_s := hclose s hsIcc
    have hε : 0 ≤ ε := (norm_nonneg _).trans hclose_s
    have hU := norm_fundamentalMatrix_le hA hT hK hbound s
    calc ‖NormedSpace.exp ℝ ((t + h - s) • A t) * ((A s - A t) * fundamentalMatrix A T s)‖
        ≤ ‖NormedSpace.exp ℝ ((t + h - s) • A t)‖ *
            (‖A s - A t‖ * ‖fundamentalMatrix A T s‖) :=
          (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left (norm_mul_le _ _) (norm_nonneg _))
      _ ≤ Real.exp (h * K) * (ε * Real.exp (K * T)) :=
          mul_le_mul hexp_le (mul_le_mul hclose_s hU (norm_nonneg _) hε)
            (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (Real.exp_pos _).le
      _ = Real.exp (h * K) * ε * Real.exp (K * T) := by ring
  have hmvt := norm_image_sub_le_of_norm_deriv_le_segment' hderiv hslope (t + h)
    ⟨by linarith, le_rfl⟩
  simp only [sub_self, zero_smul, NormedSpace.exp_zero, one_mul, add_sub_cancel_left] at hmvt
  rw [Coalescent.matrixExponential_eq_normedSpace_exp]
  exact hmvt

/-! ## Sampled epoch products converge to the fundamental matrix -/

/-- The product of exact epochs along the left-endpoint sampling of the generator path at step
`h`: `e^{h A((k - 1) h)} ⋯ e^{h A(0)}`. -/
def sampledProduct {ι : Type*} [Fintype ι] [DecidableEq ι] (A : ℝ → Matrix ι ι ℝ) (h : ℝ) :
    ℕ → Matrix ι ι ℝ
  | 0 => 1
  | k + 1 => Coalescent.matrixExponential (A ((k : ℝ) * h)) h * sampledProduct A h k

/-- **Discrete Gronwall for the sampled products.**  If the generator path varies by at most
`ε` across every pair of horizon times at most `h` apart, then after `k` epochs with `k h ≤ T`
the sampled product differs from the fundamental matrix at `k h` by at most
`k (h e^{h K} ε e^{K T}) e^{k h K}`. -/
theorem norm_fundamentalMatrix_sub_sampledProduct_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : ℝ → Matrix ι ι ℝ} (hA : Continuous A) {T K : ℝ} (hT : 0 ≤ T) (hK : 0 ≤ K)
    (hbound : ∀ s ∈ Set.Icc 0 T, ‖A s‖ ≤ K) {h ε : ℝ} (hh : 0 ≤ h)
    (hclose : ∀ s ∈ Set.Icc 0 T, ∀ r ∈ Set.Icc 0 T, r ≤ s → s ≤ r + h → ‖A s - A r‖ ≤ ε) :
    ∀ k : ℕ, (k : ℝ) * h ≤ T →
      ‖fundamentalMatrix A T ((k : ℝ) * h) - sampledProduct A h k‖ ≤
        (k : ℝ) * (h * Real.exp (h * K) * ε * Real.exp (K * T)) *
          Real.exp ((k : ℝ) * h * K)
  | 0, _ => by
      simp [sampledProduct, fundamentalMatrix_zero A hT]
  | k + 1, hk => by
      rw [Nat.cast_add_one] at hk ⊢
      have hk0 : 0 ≤ (k : ℝ) * h := mul_nonneg (Nat.cast_nonneg k) hh
      have hkT : (k : ℝ) * h + h ≤ T := by linarith
      have hprevious := norm_fundamentalMatrix_sub_sampledProduct_le hA hT hK hbound hh hclose k
        (by linarith)
      have hlocal := norm_fundamentalMatrix_step_sub_le hA hT hK hbound hk0 hh hkT
        (fun s hs ↦ hclose s ⟨hk0.trans hs.1, hs.2.trans hkT⟩ ((k : ℝ) * h)
          ⟨hk0, by linarith⟩ hs.1 hs.2)
      have hfactor : ‖Coalescent.matrixExponential (A ((k : ℝ) * h)) h‖ ≤ Real.exp (h * K) :=
        (norm_matrixExponential_le _ hh).trans (Real.exp_le_exp.mpr
          (mul_le_mul_of_nonneg_left (hbound _ ⟨hk0, by linarith⟩) hh))
      have hε : 0 ≤ ε := by
        have hself := hclose 0 ⟨le_rfl, hT⟩ 0 ⟨le_rfl, hT⟩ le_rfl (by linarith)
        simpa using hself
      have hL : 0 ≤ h * Real.exp (h * K) * ε * Real.exp (K * T) := by positivity
      have hsplit : fundamentalMatrix A T (((k : ℝ) + 1) * h) - sampledProduct A h (k + 1) =
          (fundamentalMatrix A T ((k : ℝ) * h + h) -
              Coalescent.matrixExponential (A ((k : ℝ) * h)) h *
                fundamentalMatrix A T ((k : ℝ) * h)) +
            Coalescent.matrixExponential (A ((k : ℝ) * h)) h *
              (fundamentalMatrix A T ((k : ℝ) * h) - sampledProduct A h k) := by
        rw [add_mul, one_mul]
        simp only [sampledProduct]
        noncomm_ring
      rw [hsplit]
      have hexp_add : Real.exp (h * K) * Real.exp ((k : ℝ) * h * K) =
          Real.exp (((k : ℝ) + 1) * h * K) := by
        rw [← Real.exp_add]
        congr 1
        ring
      have hone : 1 ≤ Real.exp (((k : ℝ) + 1) * h * K) :=
        Real.one_le_exp (mul_nonneg (mul_nonneg (by positivity) hh) hK)
      calc ‖(fundamentalMatrix A T ((k : ℝ) * h + h) -
              Coalescent.matrixExponential (A ((k : ℝ) * h)) h *
                fundamentalMatrix A T ((k : ℝ) * h)) +
            Coalescent.matrixExponential (A ((k : ℝ) * h)) h *
              (fundamentalMatrix A T ((k : ℝ) * h) - sampledProduct A h k)‖
          ≤ Real.exp (h * K) * ε * Real.exp (K * T) * h +
              Real.exp (h * K) * ((k : ℝ) * (h * Real.exp (h * K) * ε * Real.exp (K * T)) *
                Real.exp ((k : ℝ) * h * K)) :=
            (norm_add_le _ _).trans (add_le_add hlocal ((norm_mul_le _ _).trans
              (mul_le_mul hfactor hprevious (norm_nonneg _) (Real.exp_pos _).le)))
        _ = h * Real.exp (h * K) * ε * Real.exp (K * T) +
              (k : ℝ) * (h * Real.exp (h * K) * ε * Real.exp (K * T)) *
                (Real.exp (h * K) * Real.exp ((k : ℝ) * h * K)) := by ring
        _ ≤ ((k : ℝ) + 1) * (h * Real.exp (h * K) * ε * Real.exp (K * T)) *
              Real.exp (((k : ℝ) + 1) * h * K) := by
            rw [hexp_add]
            nlinarith [mul_le_mul_of_nonneg_left hone hL]

/-- **The sampled epoch products converge to the fundamental matrix.**  Along the uniform
partition of `[0, T]` into `n` intervals, the product of the exact epochs of the left-endpoint
generators converges to `U(T)` as `n → ∞`. -/
theorem tendsto_sampledProduct {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : ℝ → Matrix ι ι ℝ} (hA : Continuous A) {T K : ℝ} (hT : 0 ≤ T) (hK : 0 ≤ K)
    (hbound : ∀ s ∈ Set.Icc 0 T, ‖A s‖ ≤ K) :
    Filter.Tendsto (fun n : ℕ ↦ sampledProduct A (T / n) n) Filter.atTop
      (nhds (fundamentalMatrix A T T)) := by
  have huniform : UniformContinuousOn A (Set.Icc 0 T) :=
    isCompact_Icc.uniformContinuousOn_of_continuous hA.continuousOn
  rw [Metric.uniformContinuousOn_iff] at huniform
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hP : 0 ≤ T * Real.exp (T * K) * Real.exp (K * T) * Real.exp (T * K) :=
    mul_nonneg (mul_nonneg (mul_nonneg hT (Real.exp_pos _).le) (Real.exp_pos _).le)
      (Real.exp_pos _).le
  have hMpos : 0 < T * Real.exp (T * K) * Real.exp (K * T) * Real.exp (T * K) + 1 := by
    linarith
  obtain ⟨δ, hδ, hclose⟩ := huniform (ε / (T * Real.exp (T * K) * Real.exp (K * T) *
    Real.exp (T * K) + 1)) (div_pos hε hMpos)
  obtain ⟨N, hN⟩ := exists_nat_gt (T / δ)
  refine ⟨N + 1, fun n hn ↦ ?_⟩
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hNn : (N : ℝ) < n := by exact_mod_cast (by omega : N < n)
  have hone_n : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
  have hh : 0 ≤ T / n := div_nonneg hT hnpos.le
  have hnh : (n : ℝ) * (T / n) = T := by field_simp
  have hhT : T / n ≤ T := div_le_self hT hone_n
  have hhδ : T / n < δ := by
    have hTN : T < N * δ := (div_lt_iff₀ hδ).mp hN
    have hNδ : (N : ℝ) * δ < n * δ := mul_lt_mul_of_pos_right hNn hδ
    rw [div_lt_iff₀ hnpos]
    linarith
  have hlocal : ∀ s ∈ Set.Icc 0 T, ∀ r ∈ Set.Icc 0 T, r ≤ s → s ≤ r + T / n →
      ‖A s - A r‖ ≤ ε / (T * Real.exp (T * K) * Real.exp (K * T) * Real.exp (T * K) + 1) := by
    intro s hs r hr hrs hsr
    have hdist : dist s r < δ := by
      rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hrs)]
      linarith
    have hA_close := hclose s hs r hr hdist
    rw [dist_eq_norm] at hA_close
    exact hA_close.le
  have herror := norm_fundamentalMatrix_sub_sampledProduct_le hA hT hK hbound hh hlocal n
    hnh.le
  rw [hnh] at herror
  rw [dist_eq_norm, norm_sub_rev]
  refine lt_of_le_of_lt herror ?_
  have hexp_le : Real.exp (T / n * K) ≤ Real.exp (T * K) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hhT hK)
  have hrearrange : (n : ℝ) * (T / n * Real.exp (T / n * K) *
      (ε / (T * Real.exp (T * K) * Real.exp (K * T) * Real.exp (T * K) + 1)) *
        Real.exp (K * T)) * Real.exp (T * K) =
      ((n : ℝ) * (T / n)) * Real.exp (T / n * K) * Real.exp (K * T) * Real.exp (T * K) *
        (ε / (T * Real.exp (T * K) * Real.exp (K * T) * Real.exp (T * K) + 1)) := by
    ring
  rw [hrearrange, hnh]
  have hstep : T * Real.exp (T / n * K) * Real.exp (K * T) * Real.exp (T * K) *
      (ε / (T * Real.exp (T * K) * Real.exp (K * T) * Real.exp (T * K) + 1)) ≤
      T * Real.exp (T * K) * Real.exp (K * T) * Real.exp (T * K) *
        (ε / (T * Real.exp (T * K) * Real.exp (K * T) * Real.exp (T * K) + 1)) :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hexp_le hT) (Real.exp_pos _).le) (Real.exp_pos _).le)
      (div_nonneg hε.le hMpos.le)
  refine lt_of_le_of_lt hstep ?_
  have hfraction : T * Real.exp (T * K) * Real.exp (K * T) * Real.exp (T * K) /
      (T * Real.exp (T * K) * Real.exp (K * T) * Real.exp (T * K) + 1) < 1 :=
    (div_lt_one hMpos).mpr (by linarith)
  calc T * Real.exp (T * K) * Real.exp (K * T) * Real.exp (T * K) *
        (ε / (T * Real.exp (T * K) * Real.exp (K * T) * Real.exp (T * K) + 1))
      = ε * (T * Real.exp (T * K) * Real.exp (K * T) * Real.exp (T * K) /
          (T * Real.exp (T * K) * Real.exp (K * T) * Real.exp (T * K) + 1)) := by ring
    _ < ε * 1 := mul_lt_mul_of_pos_left hfraction hε
    _ = ε := mul_one ε

/-! ## Variation of constants -/

/-- **Iterate differences under two generator paths.**  If both paths are bounded by `K` on the
horizon, the `(n + 1)`-st Picard iterates at time `s` differ by at most
`(∫₀ˢ ‖A - B‖) (2 K s)^n / n!`. -/
theorem norm_picardIterate_sub_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A B : ℝ → Matrix ι ι ℝ} (hA : Continuous A) (hB : Continuous B) {T K : ℝ} (hT : 0 ≤ T)
    (hK : 0 ≤ K) (hboundA : ∀ s ∈ Set.Icc 0 T, ‖A s‖ ≤ K)
    (hboundB : ∀ s ∈ Set.Icc 0 T, ‖B s‖ ≤ K) :
    ∀ n, ∀ s ∈ Set.Icc 0 T,
      ‖picardIterate A T (n + 1) s - picardIterate B T (n + 1) s‖ ≤
        (∫ u in (0 : ℝ)..s, ‖A u - B u‖) * (2 * K * s) ^ n / n.factorial
  | 0, s, hs => by
      have hcontA := continuous_picardIterate hA T 0
      have hcontB := continuous_picardIterate hB T 0
      have hdifference : picardIterate A T 1 s - picardIterate B T 1 s =
          ∫ u in (0 : ℝ)..s, (A u - B u) := by
        show (∫ u in (0 : ℝ)..clampTime T s, A u * picardIterate A T 0 u) -
            (∫ u in (0 : ℝ)..clampTime T s, B u * picardIterate B T 0 u) = _
        rw [clampTime_of_mem hs, ← intervalIntegral.integral_sub
          ((hA.mul hcontA).intervalIntegrable _ _) ((hB.mul hcontB).intervalIntegrable _ _)]
        simp [picardIterate]
      rw [hdifference]
      simpa using intervalIntegral.norm_integral_le_integral_norm hs.1
  | n + 1, s, hs => by
      have hcontA := continuous_picardIterate hA T (n + 1)
      have hcontB := continuous_picardIterate hB T (n + 1)
      have hdifference : picardIterate A T (n + 2) s - picardIterate B T (n + 2) s =
          ∫ u in (0 : ℝ)..s, ((A u - B u) * picardIterate A T (n + 1) u +
            B u * (picardIterate A T (n + 1) u - picardIterate B T (n + 1) u)) := by
        show (∫ u in (0 : ℝ)..clampTime T s, A u * picardIterate A T (n + 1) u) -
            (∫ u in (0 : ℝ)..clampTime T s, B u * picardIterate B T (n + 1) u) = _
        rw [clampTime_of_mem hs, ← intervalIntegral.integral_sub
          ((hA.mul hcontA).intervalIntegrable _ _) ((hB.mul hcontB).intervalIntegrable _ _)]
        congr 1
        funext u
        noncomm_ring
      rw [hdifference]
      have hnormcont : Continuous fun u ↦ ‖A u - B u‖ := (hA.sub hB).norm
      have hEnn : 0 ≤ ∫ u in (0 : ℝ)..s, ‖A u - B u‖ :=
        intervalIntegral.integral_nonneg hs.1 fun _ _ ↦ norm_nonneg _
      have hpointwise : ∀ u ∈ Set.Ioc 0 s,
          ‖(A u - B u) * picardIterate A T (n + 1) u +
              B u * (picardIterate A T (n + 1) u - picardIterate B T (n + 1) u)‖ ≤
            ‖A u - B u‖ * ((K * s) ^ (n + 1) / (n + 1).factorial) +
              K * (∫ v in (0 : ℝ)..s, ‖A v - B v‖) * (2 * K) ^ n / n.factorial * u ^ n := by
        intro u hu
        have humem : u ∈ Set.Icc 0 T := ⟨hu.1.le, hu.2.trans hs.2⟩
        have hfactorial : (0 : ℝ) < (n + 1).factorial := by exact_mod_cast Nat.factorial_pos _
        have hUA : ‖picardIterate A T (n + 1) u‖ ≤ (K * s) ^ (n + 1) / (n + 1).factorial := by
          have hbase := norm_picardIterate_le hA hT hK hboundA (n + 1) u
          rw [clampTime_of_mem humem] at hbase
          exact hbase.trans (div_le_div_of_nonneg_right (pow_le_pow_left₀
            (mul_nonneg hK hu.1.le) (mul_le_mul_of_nonneg_left hu.2 hK) _) hfactorial.le)
        have hmono : (∫ v in (0 : ℝ)..u, ‖A v - B v‖) ≤ ∫ v in (0 : ℝ)..s, ‖A v - B v‖ :=
          intervalIntegral.integral_mono_interval le_rfl hu.1.le hu.2
            (ae_of_all _ fun _ ↦ norm_nonneg _) (hnormcont.intervalIntegrable _ _)
        have hprevious := norm_picardIterate_sub_le hA hB hT hK hboundA hboundB n u humem
        have hpow : 0 ≤ (2 * K * u) ^ n := pow_nonneg (mul_nonneg (by positivity) hu.1.le) n
        have hprevious' : ‖picardIterate A T (n + 1) u - picardIterate B T (n + 1) u‖ ≤
            (∫ v in (0 : ℝ)..s, ‖A v - B v‖) * (2 * K * u) ^ n / n.factorial :=
          hprevious.trans (div_le_div_of_nonneg_right
            (mul_le_mul_of_nonneg_right hmono hpow) (Nat.cast_nonneg _))
        calc ‖(A u - B u) * picardIterate A T (n + 1) u +
              B u * (picardIterate A T (n + 1) u - picardIterate B T (n + 1) u)‖
            ≤ ‖A u - B u‖ * ‖picardIterate A T (n + 1) u‖ +
                ‖B u‖ * ‖picardIterate A T (n + 1) u - picardIterate B T (n + 1) u‖ :=
              (norm_add_le _ _).trans (add_le_add (norm_mul_le _ _) (norm_mul_le _ _))
          _ ≤ ‖A u - B u‖ * ((K * s) ^ (n + 1) / (n + 1).factorial) +
                K * ((∫ v in (0 : ℝ)..s, ‖A v - B v‖) * (2 * K * u) ^ n / n.factorial) :=
              add_le_add (mul_le_mul_of_nonneg_left hUA (norm_nonneg _))
                (mul_le_mul (hboundB u humem) hprevious' (norm_nonneg _) hK)
          _ = ‖A u - B u‖ * ((K * s) ^ (n + 1) / (n + 1).factorial) +
                K * (∫ v in (0 : ℝ)..s, ‖A v - B v‖) * (2 * K) ^ n / n.factorial * u ^ n := by
              ring
      have hintegral : ‖∫ u in (0 : ℝ)..s, ((A u - B u) * picardIterate A T (n + 1) u +
            B u * (picardIterate A T (n + 1) u - picardIterate B T (n + 1) u))‖ ≤
          ∫ u in (0 : ℝ)..s, (‖A u - B u‖ * ((K * s) ^ (n + 1) / (n + 1).factorial) +
            K * (∫ v in (0 : ℝ)..s, ‖A v - B v‖) * (2 * K) ^ n / n.factorial * u ^ n) :=
        intervalIntegral.norm_integral_le_of_norm_le hs.1 (ae_of_all _ hpointwise)
          (Continuous.intervalIntegrable (by fun_prop) _ _)
      have hvalue : ∫ u in (0 : ℝ)..s, (‖A u - B u‖ * ((K * s) ^ (n + 1) / (n + 1).factorial) +
            K * (∫ v in (0 : ℝ)..s, ‖A v - B v‖) * (2 * K) ^ n / n.factorial * u ^ n) =
          (∫ u in (0 : ℝ)..s, ‖A u - B u‖) * ((K * s) ^ (n + 1) / (n + 1).factorial) +
            K * (∫ v in (0 : ℝ)..s, ‖A v - B v‖) * (2 * K) ^ n / n.factorial *
              (s ^ (n + 1) / (n + 1)) := by
        rw [intervalIntegral.integral_add ((hnormcont.mul continuous_const).intervalIntegrable _ _)
          ((continuous_const.mul (continuous_pow n)).intervalIntegrable _ _),
          intervalIntegral.integral_mul_const, intervalIntegral.integral_const_mul, integral_pow,
          zero_pow (Nat.succ_ne_zero n), sub_zero]
      have hfactorial : (0 : ℝ) < (n + 1).factorial := by exact_mod_cast Nat.factorial_pos _
      have hpower : (2 : ℝ) ≤ 2 ^ (n + 1) := by
        calc (2 : ℝ) = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ (n + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
      have hP : 0 ≤ (K * s) ^ (n + 1) := pow_nonneg (mul_nonneg hK hs.1) _
      have hexpand : (∫ u in (0 : ℝ)..s, ‖A u - B u‖) * ((K * s) ^ (n + 1) / (n + 1).factorial) +
            K * (∫ v in (0 : ℝ)..s, ‖A v - B v‖) * (2 * K) ^ n / n.factorial *
              (s ^ (n + 1) / (n + 1)) =
          (∫ u in (0 : ℝ)..s, ‖A u - B u‖) * (K * s) ^ (n + 1) / (n + 1).factorial *
            (1 + 2 ^ (n + 1) / 2) := by
        have hsucc : ((n + 1).factorial : ℝ) = ((n : ℝ) + 1) * n.factorial := by
          rw [Nat.factorial_succ]
          push_cast
          ring
        rw [hsucc]
        generalize ((n : ℝ) + 1) = next
        ring
      have htarget : (∫ u in (0 : ℝ)..s, ‖A u - B u‖) * (2 * K * s) ^ (n + 1) /
            (n + 1).factorial =
          (∫ u in (0 : ℝ)..s, ‖A u - B u‖) * (K * s) ^ (n + 1) / (n + 1).factorial *
            2 ^ (n + 1) := by
        ring
      rw [htarget]
      refine hintegral.trans (hvalue.trans_le ?_)
      rw [hexpand]
      exact mul_le_mul_of_nonneg_left (by linarith)
        (div_nonneg (mul_nonneg hEnn hP) hfactorial.le)

/-- **Variation of constants.**  Two continuous generator paths bounded by `K` on the horizon
have fundamental matrices at `T` differing by at most `e^{2 K T}` times the `L¹` distance of the
paths on `[0, T]`. -/
theorem norm_fundamentalMatrix_sub_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A B : ℝ → Matrix ι ι ℝ} (hA : Continuous A) (hB : Continuous B) {T K : ℝ} (hT : 0 ≤ T)
    (hK : 0 ≤ K) (hboundA : ∀ s ∈ Set.Icc 0 T, ‖A s‖ ≤ K)
    (hboundB : ∀ s ∈ Set.Icc 0 T, ‖B s‖ ≤ K) :
    ‖fundamentalMatrix A T T - fundamentalMatrix B T T‖ ≤
      (∫ u in (0 : ℝ)..T, ‖A u - B u‖) * Real.exp (2 * K * T) := by
  have hsA := summable_picardIterate hA hT hK hboundA T
  have hsB := summable_picardIterate hB hT hK hboundB T
  have hdifference : HasSum (fun n ↦ picardIterate A T n T - picardIterate B T n T)
      (fundamentalMatrix A T T - fundamentalMatrix B T T) := hsA.hasSum.sub hsB.hasSum
  have hzero : picardIterate A T 0 T - picardIterate B T 0 T = 0 := sub_self _
  have hshift : fundamentalMatrix A T T - fundamentalMatrix B T T =
      ∑' n, (picardIterate A T (n + 1) T - picardIterate B T (n + 1) T) := by
    rw [← hdifference.tsum_eq, hdifference.summable.tsum_eq_zero_add, hzero, zero_add]
  have hiterate : ∀ n, ‖picardIterate A T (n + 1) T - picardIterate B T (n + 1) T‖ ≤
      (∫ u in (0 : ℝ)..T, ‖A u - B u‖) * ((2 * K * T) ^ n / n.factorial) := by
    intro n
    have hbase := norm_picardIterate_sub_le hA hB hT hK hboundA hboundB n T ⟨hT, le_rfl⟩
    rwa [mul_div_assoc] at hbase
  have hmajorant : Summable fun n : ℕ ↦
      (∫ u in (0 : ℝ)..T, ‖A u - B u‖) * ((2 * K * T) ^ n / n.factorial) :=
    (Real.summable_pow_div_factorial (2 * K * T)).mul_left _
  have hnorms : Summable fun n ↦
      ‖picardIterate A T (n + 1) T - picardIterate B T (n + 1) T‖ :=
    Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) hiterate hmajorant
  have hexp : ∑' n : ℕ, (2 * K * T) ^ n / (n.factorial : ℝ) = Real.exp (2 * K * T) := by
    rw [Real.exp_eq_exp_ℝ]
    exact (NormedSpace.expSeries_div_hasSum_exp (𝕂 := ℝ) (2 * K * T)).tsum_eq
  rw [hshift]
  calc ‖∑' n, (picardIterate A T (n + 1) T - picardIterate B T (n + 1) T)‖
      ≤ ∑' n, ‖picardIterate A T (n + 1) T - picardIterate B T (n + 1) T‖ :=
        norm_tsum_le_tsum_norm hnorms
    _ ≤ ∑' n : ℕ, (∫ u in (0 : ℝ)..T, ‖A u - B u‖) * ((2 * K * T) ^ n / n.factorial) :=
        hnorms.tsum_le_tsum hiterate hmajorant
    _ = (∫ u in (0 : ℝ)..T, ‖A u - B u‖) * Real.exp (2 * K * T) := by
        rw [tsum_mul_left, hexp]

/-! ## Step approximation -/

/-- The left endpoint of the sampling interval containing `t`, for the uniform partition of the
horizon `[0, T]` into `n` intervals. -/
def sampleTime (T : ℝ) (n : ℕ) (t : ℝ) : ℝ :=
  (Nat.floor (t / (T / n)) : ℝ) * (T / n)

/-- **Left-endpoint step approximation in `L¹`.**  For every `ε > 0`, eventually in `n`, the
generator path sampled at the left endpoints of the uniform partition is within `ε T` of the
path in `L¹([0, T])`. -/
theorem eventually_integral_norm_sample_sub_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : ℝ → Matrix ι ι ℝ} (hA : Continuous A) {T : ℝ} (hT : 0 ≤ T) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in Filter.atTop, ∫ t in (0 : ℝ)..T, ‖A (sampleTime T n t) - A t‖ ≤ ε * T := by
  have huniform : UniformContinuousOn A (Set.Icc 0 T) :=
    isCompact_Icc.uniformContinuousOn_of_continuous hA.continuousOn
  rw [Metric.uniformContinuousOn_iff] at huniform
  obtain ⟨δ, hδ, hclose⟩ := huniform ε hε
  obtain ⟨N, hN⟩ := exists_nat_gt (T / δ)
  refine Filter.eventually_atTop.mpr ⟨N + 1, fun n hn ↦ ?_⟩
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hNn : (N : ℝ) < n := by exact_mod_cast (by omega : N < n)
  have hpointwise : ∀ t ∈ Set.uIoc 0 T, ‖‖A (sampleTime T n t) - A t‖‖ ≤ ε := by
    intro t ht
    rw [Set.uIoc_of_le hT] at ht
    have hTpos : 0 < T := lt_of_lt_of_le ht.1 ht.2
    have hstep : 0 < T / n := div_pos hTpos hnpos
    have hratio : 0 ≤ t / (T / n) := div_nonneg ht.1.le hstep.le
    have hlow : sampleTime T n t ≤ t := by
      have hfloor := Nat.floor_le hratio
      calc sampleTime T n t ≤ t / (T / n) * (T / n) :=
            mul_le_mul_of_nonneg_right hfloor hstep.le
        _ = t := by field_simp
    have hhigh : t < sampleTime T n t + T / n := by
      have hfloor := Nat.lt_floor_add_one (t / (T / n))
      have hmul := mul_lt_mul_of_pos_right hfloor hstep
      have hleft : t / (T / n) * (T / n) = t := by field_simp
      rw [hleft, add_mul, one_mul] at hmul
      exact hmul
    have hsample_mem : sampleTime T n t ∈ Set.Icc 0 T :=
      ⟨mul_nonneg (Nat.cast_nonneg _) hstep.le, hlow.trans ht.2⟩
    have hstep_lt : T / n < δ := by
      have hTN : T < N * δ := (div_lt_iff₀ hδ).mp hN
      have hNδ : (N : ℝ) * δ < n * δ := mul_lt_mul_of_pos_right hNn hδ
      rw [div_lt_iff₀ hnpos]
      linarith
    have hdist : dist (sampleTime T n t) t < δ := by
      rw [Real.dist_eq, abs_of_nonpos (by linarith)]
      linarith
    have hA_close := hclose _ hsample_mem t ⟨ht.1.le, ht.2⟩ hdist
    rw [dist_eq_norm] at hA_close
    rw [norm_norm]
    exact hA_close.le
  have hbound := intervalIntegral.norm_integral_le_of_norm_le_const hpointwise
  rw [sub_zero, abs_of_nonneg hT] at hbound
  exact (Real.le_norm_self _).trans hbound

end

end Descent.Portability.LinearFundamentalMatrix
