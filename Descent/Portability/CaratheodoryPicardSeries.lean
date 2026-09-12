/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.CaratheodoryFundamentalMatrix

assert_below Descent.Decision Descent.Program

/-!
# The Picard series of an integrable generator path

`LinearFundamentalMatrix.fundamentalMatrix A T t` is the Picard series `Σₙ Pₙ(t)`, the sum of the
iterates `picardIterate A T n t = ∫…∫ A(sₙ)⋯A(s₁)`, and it is defined for every generator path.
`LinearFundamentalMatrix` sums it for continuous paths.  This module sums it for paths with
integrable norm and identifies the sum with the Carathéodory fundamental matrix of
`CaratheodoryFundamentalMatrix`, which is how NOTE1 §2.4 constructs the propagator.

The factorial bound in integrated form.  For a continuous path `B` the primitive `a(s) = ∫₀ˢ ‖B‖`
satisfies `∫₀ᶜ ‖B(s)‖ a(s)ⁿ / n! ds = a(c)ⁿ⁺¹ / (n + 1)!` by the fundamental theorem of calculus
(`integral_norm_mul_primitive_pow`), so the iterates obey `‖Pₙ(t)‖ ≤ (∫₀ᵗ ‖B‖)ⁿ / n!` with `t`
clamped into the horizon (`norm_picardIterate_le_integral`).

Integrable paths.  The iterates of a path with integrable norm are continuous
(`continuous_picardIterate_of_intervalIntegrable`).  Continuous paths converging to it in
`L¹([0, T])` exist (`exists_continuous_approximation`), have iterates bounded uniformly in the
approximation (`norm_picardIterate_le_of_integral_norm_sub_le`), and every iterate of the
approximations converges uniformly to the iterate of the path (`tendstoUniformly_picardIterate`).
So the integrated factorial bound holds for the path itself
(`norm_picardIterate_le_integral_of_intervalIntegrable`) and the series converges absolutely
(`summable_picardIterate_of_intervalIntegrable`).  By dominated convergence of the series, the
Picard sums of the approximations converge to the Picard sum of the path; they also converge to
the Carathéodory fundamental matrix
(`CaratheodoryFundamentalMatrix.tendstoUniformlyOn_fundamentalMatrix_of_continuous`).  Hence the
Carathéodory fundamental matrix is the Picard series
(`caratheodoryFundamentalMatrix_eq_fundamentalMatrix_of_intervalIntegrable`,
`hasSum_picardIterate_caratheodoryFundamentalMatrix`).

## Empirical status

None.  The bodies here are integral inequalities, uniform limits and series in a
finite-dimensional Banach algebra, so no measurement can bear on them.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.CaratheodoryPicardSeries

open MeasureTheory Filter Topology
open Descent.Portability.LinearFundamentalMatrix Descent.Portability.IntegrableGeneratorPropagator
  Descent.Portability.CaratheodoryFundamentalMatrix
open scoped Matrix.Norms.Operator

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## The factorial bound in integrated form -/

/-- **The simplex integral.**  For a continuous path `B` the primitive `a(s) = ∫₀ˢ ‖B‖` satisfies
`∫₀ᶜ ‖B(s)‖ a(s)ⁿ / n! ds = a(c)ⁿ⁺¹ / (n + 1)!`. -/
theorem integral_norm_mul_primitive_pow {B : ℝ → Matrix ι ι ℝ} (hB : Continuous B) (n : ℕ)
    (c : ℝ) :
    ∫ s in (0 : ℝ)..c, ‖B s‖ * (∫ r in (0 : ℝ)..s, ‖B r‖) ^ n / n.factorial
      = (∫ r in (0 : ℝ)..c, ‖B r‖) ^ (n + 1) / (n + 1).factorial := by
  have hprimitive : Continuous fun s ↦ ∫ r in (0 : ℝ)..s, ‖B r‖ :=
    intervalIntegral.continuous_primitive (fun a b ↦ hB.norm.intervalIntegrable a b) 0
  have hderiv : ∀ x ∈ Set.uIcc (0 : ℝ) c,
      HasDerivAt (fun s ↦ (∫ r in (0 : ℝ)..s, ‖B r‖) ^ (n + 1) / (n + 1).factorial)
        (‖B x‖ * (∫ r in (0 : ℝ)..x, ‖B r‖) ^ n / n.factorial) x := by
    intro x _
    have hbase : HasDerivAt (fun s ↦ ∫ r in (0 : ℝ)..s, ‖B r‖) ‖B x‖ x :=
      intervalIntegral.integral_hasDerivAt_right (hB.norm.intervalIntegrable 0 x)
        (hB.norm.stronglyMeasurableAtFilter _ _) hB.norm.continuousAt
    refine ((hbase.fun_pow (n + 1)).div_const ((n + 1).factorial : ℝ)).congr_deriv ?_
    have hsucc : ((n + 1).factorial : ℝ) = ((n : ℝ) + 1) * n.factorial := by
      rw [Nat.factorial_succ]
      push_cast
      ring
    have hn1 : ((n : ℝ) + 1) ≠ 0 := by positivity
    have hfac : (n.factorial : ℝ) ≠ 0 := by positivity
    rw [Nat.add_sub_cancel, hsucc, Nat.cast_add_one, div_eq_div_iff (mul_ne_zero hn1 hfac) hfac]
    ring
  have hintegrand : Continuous fun s ↦ ‖B s‖ * (∫ r in (0 : ℝ)..s, ‖B r‖) ^ n / n.factorial :=
    (hB.norm.mul (hprimitive.pow n)).div_const _
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hintegrand.intervalIntegrable _ _),
    intervalIntegral.integral_same, zero_pow (Nat.succ_ne_zero n), zero_div, sub_zero]

/-- **The factorial bound in integrated form.**  For a continuous generator path the Picard
iterates obey `‖Pₙ(t)‖ ≤ (∫₀ᵗ ‖B‖)ⁿ / n!`, with `t` clamped into the horizon. -/
theorem norm_picardIterate_le_integral {B : ℝ → Matrix ι ι ℝ} (hB : Continuous B) {T : ℝ}
    (hT : 0 ≤ T) :
    ∀ n t, ‖picardIterate B T n t‖ ≤ (∫ r in (0 : ℝ)..clampTime T t, ‖B r‖) ^ n / n.factorial
  | 0, t => by
      have hone := norm_identityMatrix_le_one (ι := ι)
      simpa [picardIterate] using hone
  | n + 1, t => by
      have hmem := clampTime_mem hT t
      have hprimitive : Continuous fun s ↦ ∫ r in (0 : ℝ)..s, ‖B r‖ :=
        intervalIntegral.continuous_primitive (fun a b ↦ hB.norm.intervalIntegrable a b) 0
      have hintegrand :
          Continuous fun s ↦ ‖B s‖ * (∫ r in (0 : ℝ)..s, ‖B r‖) ^ n / n.factorial :=
        (hB.norm.mul (hprimitive.pow n)).div_const _
      have hstep : ‖∫ s in (0 : ℝ)..clampTime T t, B s * picardIterate B T n s‖ ≤
          ∫ s in (0 : ℝ)..clampTime T t,
            ‖B s‖ * (∫ r in (0 : ℝ)..s, ‖B r‖) ^ n / n.factorial := by
        refine intervalIntegral.norm_integral_le_of_norm_le hmem.1 (ae_of_all _ fun s hs ↦ ?_)
          (hintegrand.intervalIntegrable _ _)
        have hsmem : s ∈ Set.Icc 0 T := ⟨hs.1.le, hs.2.trans hmem.2⟩
        have hprevious := norm_picardIterate_le_integral hB hT n s
        rw [clampTime_of_mem hsmem] at hprevious
        calc ‖B s * picardIterate B T n s‖ ≤ ‖B s‖ * ‖picardIterate B T n s‖ :=
              norm_mul_le _ _
          _ ≤ ‖B s‖ * ((∫ r in (0 : ℝ)..s, ‖B r‖) ^ n / n.factorial) :=
              mul_le_mul_of_nonneg_left hprevious (norm_nonneg _)
          _ = ‖B s‖ * (∫ r in (0 : ℝ)..s, ‖B r‖) ^ n / n.factorial := by ring
      exact hstep.trans_eq (integral_norm_mul_primitive_pow hB n _)

/-! ## Integrable paths -/

/-- The Picard iterates of a generator path with integrable norm on the horizon are continuous on
the whole line. -/
theorem continuous_picardIterate_of_intervalIntegrable {A : ℝ → Matrix ι ι ℝ} {T : ℝ}
    (hT : 0 ≤ T) (hA : IntervalIntegrable A volume 0 T) :
    ∀ n, Continuous (picardIterate A T n)
  | 0 => continuous_const
  | n + 1 => by
      have hprevious := continuous_picardIterate_of_intervalIntegrable hT hA n
      have hintegrand : IntervalIntegrable (fun s ↦ A s * picardIterate A T n s) volume 0 T :=
        hA.mul_continuousOn hprevious.continuousOn
      have hon : ContinuousOn (fun b ↦ ∫ s in (0 : ℝ)..b, A s * picardIterate A T n s)
          (Set.Icc 0 T) := by
        have h := intervalIntegral.continuousOn_primitive_interval' hintegrand
          (Set.left_mem_uIcc (a := (0 : ℝ)) (b := T))
        rwa [Set.uIcc_of_le hT] at h
      exact hon.comp_continuous (continuous_clampTime T) (clampTime_mem hT)

/-- Every generator path with integrable norm on the horizon is a limit of continuous paths in
`L¹([0, T])`. -/
theorem exists_continuous_approximation {A : ℝ → Matrix ι ι ℝ} {T : ℝ} (hT : 0 ≤ T)
    (hA : IntervalIntegrable A volume 0 T) :
    ∃ B : ℕ → ℝ → Matrix ι ι ℝ, (∀ k, Continuous (B k)) ∧
      Tendsto (fun k ↦ ∫ s in (0 : ℝ)..T, ‖B k s - A s‖) atTop (𝓝 0) := by
  choose B hB hclose using fun k : ℕ ↦ exists_continuous_integral_norm_sub_le hT hA
    (show (0 : ℝ) < 1 / ((k : ℝ) + 1) by positivity)
  refine ⟨B, hB, squeeze_zero (fun k ↦ intervalIntegral.integral_nonneg hT fun _ _ ↦ norm_nonneg _)
    (fun k ↦ ?_) tendsto_one_div_add_atTop_nhds_zero_nat⟩
  calc ∫ s in (0 : ℝ)..T, ‖B k s - A s‖ = ∫ s in (0 : ℝ)..T, ‖A s - B k s‖ :=
        intervalIntegral.integral_congr fun s _ ↦ norm_sub_rev _ _
    _ ≤ 1 / ((k : ℝ) + 1) := hclose k

/-- A path within `δ` of `A` in `L¹([0, T])` has integrated norm at most `∫₀ᵀ ‖A‖ + δ`. -/
theorem integral_norm_le_of_integral_norm_sub_le {A B : ℝ → Matrix ι ι ℝ} {T δ : ℝ} (hT : 0 ≤ T)
    (hA : IntervalIntegrable A volume 0 T) (hB : IntervalIntegrable B volume 0 T)
    (hδ : ∫ s in (0 : ℝ)..T, ‖B s - A s‖ ≤ δ) :
    ∫ s in (0 : ℝ)..T, ‖B s‖ ≤ (∫ s in (0 : ℝ)..T, ‖A s‖) + δ := by
  have hstep : (∫ s in (0 : ℝ)..T, ‖B s‖) ≤ ∫ s in (0 : ℝ)..T, (‖A s‖ + ‖B s - A s‖) :=
    intervalIntegral.integral_mono_on hT hB.norm (hA.norm.add (hB.sub hA).norm) fun s _ ↦
      calc ‖B s‖ = ‖A s + (B s - A s)‖ := by
            congr 1
            abel
        _ ≤ ‖A s‖ + ‖B s - A s‖ := norm_add_le _ _
  rw [intervalIntegral.integral_add hA.norm (hB.sub hA).norm] at hstep
  linarith

/-- The iterates of a continuous path within `δ` of `A` in `L¹([0, T])` are bounded by
`(∫₀ᵀ ‖A‖ + δ)ⁿ / n!`. -/
theorem norm_picardIterate_le_of_integral_norm_sub_le {A B : ℝ → Matrix ι ι ℝ} {T δ : ℝ}
    (hT : 0 ≤ T) (hA : IntervalIntegrable A volume 0 T) (hB : Continuous B)
    (hδ : ∫ s in (0 : ℝ)..T, ‖B s - A s‖ ≤ δ) (n : ℕ) (t : ℝ) :
    ‖picardIterate B T n t‖ ≤ ((∫ s in (0 : ℝ)..T, ‖A s‖) + δ) ^ n / n.factorial := by
  have hmem := clampTime_mem hT t
  refine (norm_picardIterate_le_integral hB hT n t).trans ?_
  refine div_le_div_of_nonneg_right (pow_le_pow_left₀
    (intervalIntegral.integral_nonneg hmem.1 fun _ _ ↦ norm_nonneg _) ?_ n) (by positivity)
  exact (intervalIntegral.integral_mono_interval le_rfl hmem.1 hmem.2
    (ae_of_all _ fun _ ↦ norm_nonneg _) (hB.norm.intervalIntegrable _ _)).trans
    (integral_norm_le_of_integral_norm_sub_le hT hA (hB.intervalIntegrable _ _) hδ)

/-- **The iterates converge under `L¹` approximation.**  If continuous generator paths converge to
a path with integrable norm in `L¹([0, T])`, every Picard iterate of the approximations converges
uniformly on the line to the iterate of the path. -/
theorem tendstoUniformly_picardIterate {A : ℝ → Matrix ι ι ℝ}
    {approximation : ℕ → ℝ → Matrix ι ι ℝ} {T : ℝ} (hT : 0 ≤ T)
    (hA : IntervalIntegrable A volume 0 T) (hcontinuous : ∀ k, Continuous (approximation k))
    (hclose : Tendsto (fun k ↦ ∫ s in (0 : ℝ)..T, ‖approximation k s - A s‖) atTop (𝓝 0)) :
    ∀ n, TendstoUniformly (fun k ↦ picardIterate (approximation k) T n) (picardIterate A T n)
      atTop
  | 0 => by
      rw [Metric.tendstoUniformly_iff]
      intro ε hε
      exact Eventually.of_forall fun k t ↦ by simpa [picardIterate] using hε
  | n + 1 => by
      have hprevious := tendstoUniformly_picardIterate hT hA hcontinuous hclose n
      have hAn := continuous_picardIterate_of_intervalIntegrable hT hA n
      have hmass0 : 0 ≤ ∫ s in (0 : ℝ)..T, ‖A s‖ :=
        intervalIntegral.integral_nonneg hT fun s _ ↦ norm_nonneg _
      have hbound0 : 0 ≤ ((∫ s in (0 : ℝ)..T, ‖A s‖) + 1) ^ n / n.factorial := by positivity
      rw [Metric.tendstoUniformly_iff] at hprevious ⊢
      intro ε hε
      have hη : 0 < ε / (2 * ((∫ s in (0 : ℝ)..T, ‖A s‖) + 1)) := by positivity
      have hη' : 0 < ε / (2 * (((∫ s in (0 : ℝ)..T, ‖A s‖) + 1) ^ n / n.factorial + 1)) := by
        positivity
      filter_upwards [hprevious _ hη, (tendsto_order.1 hclose).2 _ hη',
        (tendsto_order.1 hclose).2 1 one_pos] with k hk hkclose hkone t
      have hkclose' : ∫ s in (0 : ℝ)..T, ‖approximation k s - A s‖
          < ε / (2 * (((∫ s in (0 : ℝ)..T, ‖A s‖) + 1) ^ n / n.factorial + 1)) := hkclose
      have hkone' : ∫ s in (0 : ℝ)..T, ‖approximation k s - A s‖ ≤ 1 := hkone.le
      have hk' : ∀ s, ‖picardIterate (approximation k) T n s - picardIterate A T n s‖
          < ε / (2 * ((∫ s in (0 : ℝ)..T, ‖A s‖) + 1)) := fun s ↦ by
        have h := hk s
        rwa [dist_comm, dist_eq_norm] at h
      have hmem := clampTime_mem hT t
      have hAc : IntervalIntegrable A volume 0 (clampTime T t) :=
        hA.mono_set (Set.uIcc_subset_uIcc_left (Set.mem_uIcc_of_le hmem.1 hmem.2))
      have hBn := continuous_picardIterate (hcontinuous k) T n
      have hBc : IntervalIntegrable (approximation k) volume 0 (clampTime T t) :=
        (hcontinuous k).intervalIntegrable _ _
      have hsplit : picardIterate (approximation k) T (n + 1) t - picardIterate A T (n + 1) t
          = (∫ s in (0 : ℝ)..clampTime T t,
              (approximation k s - A s) * picardIterate (approximation k) T n s)
            + ∫ s in (0 : ℝ)..clampTime T t,
              A s * (picardIterate (approximation k) T n s - picardIterate A T n s) := by
        show (∫ s in (0 : ℝ)..clampTime T t,
              approximation k s * picardIterate (approximation k) T n s)
            - (∫ s in (0 : ℝ)..clampTime T t, A s * picardIterate A T n s) = _
        rw [← intervalIntegral.integral_sub (((hcontinuous k).mul hBn).intervalIntegrable _ _)
            (hAc.mul_continuousOn hAn.continuousOn),
          ← intervalIntegral.integral_add ((hBc.sub hAc).mul_continuousOn hBn.continuousOn)
            (hAc.mul_continuousOn (hBn.sub hAn).continuousOn)]
        congr 1
        funext s
        noncomm_ring
      have hfirst : ‖∫ s in (0 : ℝ)..clampTime T t,
            (approximation k s - A s) * picardIterate (approximation k) T n s‖
          ≤ (∫ s in (0 : ℝ)..T, ‖approximation k s - A s‖)
            * (((∫ s in (0 : ℝ)..T, ‖A s‖) + 1) ^ n / n.factorial) := by
        refine (intervalIntegral.norm_integral_le_integral_norm hmem.1).trans ?_
        calc ∫ s in (0 : ℝ)..clampTime T t,
              ‖(approximation k s - A s) * picardIterate (approximation k) T n s‖
            ≤ ∫ s in (0 : ℝ)..clampTime T t, ‖approximation k s - A s‖
              * (((∫ s in (0 : ℝ)..T, ‖A s‖) + 1) ^ n / n.factorial) := by
              refine intervalIntegral.integral_mono_on hmem.1
                ((hBc.sub hAc).mul_continuousOn hBn.continuousOn).norm
                ((hBc.sub hAc).norm.mul_const _) fun s _ ↦ ?_
              exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left
                (norm_picardIterate_le_of_integral_norm_sub_le hT hA (hcontinuous k) hkone' n s)
                (norm_nonneg _))
          _ = (∫ s in (0 : ℝ)..clampTime T t, ‖approximation k s - A s‖)
              * (((∫ s in (0 : ℝ)..T, ‖A s‖) + 1) ^ n / n.factorial) :=
              intervalIntegral.integral_mul_const _ _
          _ ≤ (∫ s in (0 : ℝ)..T, ‖approximation k s - A s‖)
              * (((∫ s in (0 : ℝ)..T, ‖A s‖) + 1) ^ n / n.factorial) := by
              refine mul_le_mul_of_nonneg_right ?_ hbound0
              exact intervalIntegral.integral_mono_interval le_rfl hmem.1 hmem.2
                (ae_of_all _ fun _ ↦ norm_nonneg _)
                (((hcontinuous k).intervalIntegrable _ _).sub hA).norm
      have hsecond : ‖∫ s in (0 : ℝ)..clampTime T t,
            A s * (picardIterate (approximation k) T n s - picardIterate A T n s)‖
          ≤ (∫ s in (0 : ℝ)..T, ‖A s‖) * (ε / (2 * ((∫ s in (0 : ℝ)..T, ‖A s‖) + 1))) := by
        refine (intervalIntegral.norm_integral_le_integral_norm hmem.1).trans ?_
        calc ∫ s in (0 : ℝ)..clampTime T t,
              ‖A s * (picardIterate (approximation k) T n s - picardIterate A T n s)‖
            ≤ ∫ s in (0 : ℝ)..clampTime T t,
              ‖A s‖ * (ε / (2 * ((∫ s in (0 : ℝ)..T, ‖A s‖) + 1))) := by
              refine intervalIntegral.integral_mono_on hmem.1
                (hAc.mul_continuousOn (hBn.sub hAn).continuousOn).norm
                (hAc.norm.mul_const _) fun s _ ↦ ?_
              exact (norm_mul_le _ _).trans
                (mul_le_mul_of_nonneg_left (hk' s).le (norm_nonneg _))
          _ = (∫ s in (0 : ℝ)..clampTime T t, ‖A s‖)
              * (ε / (2 * ((∫ s in (0 : ℝ)..T, ‖A s‖) + 1))) :=
              intervalIntegral.integral_mul_const _ _
          _ ≤ (∫ s in (0 : ℝ)..T, ‖A s‖) * (ε / (2 * ((∫ s in (0 : ℝ)..T, ‖A s‖) + 1))) := by
              refine mul_le_mul_of_nonneg_right ?_ hη.le
              exact intervalIntegral.integral_mono_interval le_rfl hmem.1 hmem.2
                (ae_of_all _ fun _ ↦ norm_nonneg _) hA.norm
      have h1 : (∫ s in (0 : ℝ)..T, ‖approximation k s - A s‖)
            * (((∫ s in (0 : ℝ)..T, ‖A s‖) + 1) ^ n / n.factorial)
          ≤ ε / (2 * (((∫ s in (0 : ℝ)..T, ‖A s‖) + 1) ^ n / n.factorial + 1))
            * (((∫ s in (0 : ℝ)..T, ‖A s‖) + 1) ^ n / n.factorial) :=
        mul_le_mul_of_nonneg_right hkclose'.le hbound0
      have h2 : ε / (2 * (((∫ s in (0 : ℝ)..T, ‖A s‖) + 1) ^ n / n.factorial + 1))
            * (((∫ s in (0 : ℝ)..T, ‖A s‖) + 1) ^ n / n.factorial) < ε / 2 := by
        rw [div_mul_eq_mul_div, div_lt_div_iff₀ (by positivity) (by norm_num)]
        nlinarith
      have h3 : (∫ s in (0 : ℝ)..T, ‖A s‖) * (ε / (2 * ((∫ s in (0 : ℝ)..T, ‖A s‖) + 1)))
          < ε / 2 := by
        rw [mul_div_assoc', div_lt_div_iff₀ (by positivity) (by norm_num)]
        nlinarith
      rw [dist_comm, dist_eq_norm, hsplit]
      calc ‖(∫ s in (0 : ℝ)..clampTime T t,
              (approximation k s - A s) * picardIterate (approximation k) T n s)
            + ∫ s in (0 : ℝ)..clampTime T t,
              A s * (picardIterate (approximation k) T n s - picardIterate A T n s)‖
          ≤ ‖∫ s in (0 : ℝ)..clampTime T t,
              (approximation k s - A s) * picardIterate (approximation k) T n s‖
            + ‖∫ s in (0 : ℝ)..clampTime T t,
              A s * (picardIterate (approximation k) T n s - picardIterate A T n s)‖ :=
            norm_add_le _ _
        _ < ε := by linarith [hfirst, hsecond, h1, h2, h3]

/-- **The integrated factorial bound for integrable paths.**  The Picard iterates of a generator
path with integrable norm obey `‖Pₙ(t)‖ ≤ (∫₀ᵗ ‖A‖)ⁿ / n!`, with `t` clamped into the horizon. -/
theorem norm_picardIterate_le_integral_of_intervalIntegrable {A : ℝ → Matrix ι ι ℝ} {T : ℝ}
    (hT : 0 ≤ T) (hA : IntervalIntegrable A volume 0 T) (n : ℕ) (t : ℝ) :
    ‖picardIterate A T n t‖ ≤ (∫ r in (0 : ℝ)..clampTime T t, ‖A r‖) ^ n / n.factorial := by
  obtain ⟨B, hB, hclose⟩ := exists_continuous_approximation hT hA
  have hmem := clampTime_mem hT t
  have hAc : IntervalIntegrable A volume 0 (clampTime T t) :=
    hA.mono_set (Set.uIcc_subset_uIcc_left (Set.mem_uIcc_of_le hmem.1 hmem.2))
  have hconvergence := (tendstoUniformly_picardIterate hT hA hB hclose n).tendsto_at t
  have hprimitive : Tendsto (fun k ↦ ∫ r in (0 : ℝ)..clampTime T t, ‖B k r‖) atTop
      (𝓝 (∫ r in (0 : ℝ)..clampTime T t, ‖A r‖)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun k ↦ norm_nonneg _) (fun k ↦ ?_) hclose
    rw [← intervalIntegral.integral_sub ((hB k).norm.intervalIntegrable _ _) hAc.norm,
      Real.norm_eq_abs]
    refine (intervalIntegral.abs_integral_le_integral_abs hmem.1).trans ?_
    refine (intervalIntegral.integral_mono_on hmem.1
      (((hB k).norm.intervalIntegrable _ _).sub hAc.norm).abs
      (((hB k).intervalIntegrable _ _).sub hAc).norm fun s _ ↦ abs_norm_sub_norm_le _ _).trans ?_
    exact intervalIntegral.integral_mono_interval le_rfl hmem.1 hmem.2
      (ae_of_all _ fun _ ↦ norm_nonneg _) (((hB k).intervalIntegrable _ _).sub hA).norm
  exact le_of_tendsto_of_tendsto' hconvergence.norm ((hprimitive.pow n).div_const _)
    fun k ↦ norm_picardIterate_le_integral (hB k) hT n t

/-- The Picard series of a generator path with integrable norm converges absolutely at every
time. -/
theorem summable_picardIterate_of_intervalIntegrable {A : ℝ → Matrix ι ι ℝ} {T : ℝ}
    (hT : 0 ≤ T) (hA : IntervalIntegrable A volume 0 T) (t : ℝ) :
    Summable fun n ↦ picardIterate A T n t :=
  Summable.of_norm (Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _)
    (fun n ↦ norm_picardIterate_le_integral_of_intervalIntegrable hT hA n t)
    (Real.summable_pow_div_factorial _))

/-- **The Carathéodory fundamental matrix is the Picard series.**  For a generator path with
integrable norm on the horizon, the Carathéodory fundamental matrix is the Picard sum
`LinearFundamentalMatrix.fundamentalMatrix A T` on the horizon. -/
theorem caratheodoryFundamentalMatrix_eq_fundamentalMatrix_of_intervalIntegrable
    {A : ℝ → Matrix ι ι ℝ} {T : ℝ} (hT : 0 ≤ T) (hA : IntervalIntegrable A volume 0 T) :
    ∀ t ∈ Set.Icc 0 T, caratheodoryFundamentalMatrix A hT hA t = fundamentalMatrix A T t := by
  obtain ⟨B, hB, hclose⟩ := exists_continuous_approximation hT hA
  intro t ht
  have hlimit : Tendsto (fun k ↦ fundamentalMatrix (B k) T t) atTop
      (𝓝 (caratheodoryFundamentalMatrix A hT hA t)) :=
    (tendstoUniformlyOn_fundamentalMatrix_of_continuous hT hA hB hclose).tendsto_at ht
  have hseries : Tendsto (fun k ↦ ∑' n, picardIterate (B k) T n t) atTop
      (𝓝 (∑' n, picardIterate A T n t)) := by
    refine tendsto_tsum_of_dominated_convergence (f := fun k n ↦ picardIterate (B k) T n t)
      (g := fun n ↦ picardIterate A T n t)
      (bound := fun n ↦ ((∫ s in (0 : ℝ)..T, ‖A s‖) + 1) ^ n / n.factorial)
      (Real.summable_pow_div_factorial _)
      (fun n ↦ (tendstoUniformly_picardIterate hT hA hB hclose n).tendsto_at t) ?_
    filter_upwards [(tendsto_order.1 hclose).2 1 one_pos] with k hk n
    exact norm_picardIterate_le_of_integral_norm_sub_le hT hA (hB k) hk.le n t
  exact tendsto_nhds_unique hlimit hseries

/-- The Picard series of a generator path with integrable norm sums to its Carathéodory
fundamental matrix at every time of the horizon. -/
theorem hasSum_picardIterate_caratheodoryFundamentalMatrix {A : ℝ → Matrix ι ι ℝ} {T : ℝ}
    (hT : 0 ≤ T) (hA : IntervalIntegrable A volume 0 T) :
    ∀ t ∈ Set.Icc 0 T,
      HasSum (fun n ↦ picardIterate A T n t) (caratheodoryFundamentalMatrix A hT hA t) := by
  intro t ht
  rw [caratheodoryFundamentalMatrix_eq_fundamentalMatrix_of_intervalIntegrable hT hA t ht]
  exact (summable_picardIterate_of_intervalIntegrable hT hA t).hasSum

end

end Descent.Portability.CaratheodoryPicardSeries
