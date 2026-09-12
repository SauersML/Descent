/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.IntegralEquationDerivative

assert_below Descent.Decision Descent.Program

/-!
# The Carathéodory fundamental matrix of an integrable generator path

NOTE1 §2.4 and §4.2a allow measurable rates whose generator norm is merely integrable on the
horizon.  Their propagator is the Carathéodory solution of `U' = A(t) U`: the continuous `U` with
`U(t) = 1 + ∫₀ᵗ A(s) U(s) ds`.  The corpus already proves that such a solution exists as the
uniform limit of fundamental matrices of continuous approximations
(`IntegrableRateRealization.exists_integral_solution_of_continuous_approximation`), that it is
unique among continuous solutions (`IntegrableRateRealization.eq_of_integral_eq`), and that every
continuous solution is absolutely continuous with `U' = A U` almost everywhere
(`IntegralEquationDerivative`).  This module names the solution and proves the estimates a
consumer of the propagator needs.

The propagator.  `caratheodoryFundamentalMatrix A hT hA` is the continuous solution
(`exists_continuous_integral_solution`, `continuous_caratheodoryFundamentalMatrix`,
`caratheodoryFundamentalMatrix_eq_integral`, `caratheodoryFundamentalMatrix_zero`).  Every
continuous solution agrees with it on the horizon
(`eq_caratheodoryFundamentalMatrix_of_integral_eq`), it is absolutely continuous and differentiable
almost everywhere (`absolutelyContinuousOnInterval_caratheodoryFundamentalMatrix`,
`ae_hasDerivAt_caratheodoryFundamentalMatrix`), and for a continuous generator path it is the
Picard fundamental matrix of `LinearFundamentalMatrix`
(`caratheodoryFundamentalMatrix_eq_fundamentalMatrix`).

The estimates.  A solution of the integral equation for an integrable path and one for a continuous
path `B` differ on the horizon by at most the `L¹` distance of the paths times a bound on the first
solution times `exp ∫₀ᵗ ‖B‖`, by Gronwall's inequality with the continuous coefficient `‖B‖`
(`norm_sub_le_of_integral_eq`).  Comparing with continuous approximations gives the exponential
bound `‖U(t)‖ ≤ exp ∫₀ᵗ ‖A‖` (`norm_caratheodoryFundamentalMatrix_le`,
`norm_caratheodoryFundamentalMatrix_le_horizon`) and the variation-of-constants bound between two
integrable paths, `‖U_A(t) - U_B(t)‖ ≤ (∫₀ᵀ ‖A - B‖) e^{∫₀ᵀ ‖A‖} e^{∫₀ᵀ ‖B‖}`
(`norm_caratheodoryFundamentalMatrix_sub_le`).  So integrable paths converging in `L¹([0, T])` have
propagators converging uniformly on the horizon
(`tendstoUniformlyOn_caratheodoryFundamentalMatrix`), and so do the Picard fundamental matrices of
continuous approximations (`tendstoUniformlyOn_fundamentalMatrix_of_continuous`).

Scope.  The Picard series of an integrable path is not identified with the propagator here: its
factorial bound `(∫₀ᵗ ‖A‖)^n / n!` needs the simplex integral of an absolutely continuous
primitive, which this module does not prove.  The propagator is characterized by the integral
equation among continuous solutions.

## Empirical status

None.  The bodies here are integral inequalities and uniform limits in a finite-dimensional Banach
algebra, so no measurement can bear on them.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.CaratheodoryFundamentalMatrix

open MeasureTheory Filter Topology
open Descent.Portability.LinearFundamentalMatrix Descent.Portability.IntegrableGeneratorPropagator
  Descent.Portability.IntegrableRateRealization Descent.Portability.IntegralEquationDerivative
open scoped Matrix.Norms.Operator

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## The propagator -/

/-- Every generator path with integrable norm on the horizon has a continuous solution of
`U(t) = 1 + ∫₀ᵗ A(s) U(s) ds`. -/
theorem exists_continuous_integral_solution {A : ℝ → Matrix ι ι ℝ} {T : ℝ} (hT : 0 ≤ T)
    (hA : IntervalIntegrable A volume 0 T) :
    ∃ U : ℝ → Matrix ι ι ℝ, Continuous U ∧
      ∀ t ∈ Set.Icc 0 T, U t = 1 + ∫ s in (0 : ℝ)..t, A s * U s := by
  choose B hB hclose using fun k : ℕ ↦ exists_continuous_integral_norm_sub_le hT hA
    (show (0 : ℝ) < 1 / ((k : ℝ) + 1) by positivity)
  have hclose' : ∀ k : ℕ, ∫ s in (0 : ℝ)..T, ‖B k s - A s‖ ≤ 1 * (1 / ((k : ℝ) + 1)) := by
    intro k
    calc ∫ s in (0 : ℝ)..T, ‖B k s - A s‖ = ∫ s in (0 : ℝ)..T, ‖A s - B k s‖ :=
          intervalIntegral.integral_congr fun s _ ↦ norm_sub_rev _ _
      _ ≤ 1 / ((k : ℝ) + 1) := hclose k
      _ = 1 * (1 / ((k : ℝ) + 1)) := (one_mul _).symm
  obtain ⟨U, hU, hequation, _⟩ :=
    exists_integral_solution_of_continuous_approximation hT hA zero_le_one B hB hclose'
  exact ⟨U, hU, hequation⟩

/-- **The Carathéodory fundamental matrix** of a generator path with integrable norm on `[0, T]`:
the continuous solution of `U(t) = 1 + ∫₀ᵗ A(s) U(s) ds`. -/
def caratheodoryFundamentalMatrix (A : ℝ → Matrix ι ι ℝ) {T : ℝ} (hT : 0 ≤ T)
    (hA : IntervalIntegrable A volume 0 T) : ℝ → Matrix ι ι ℝ :=
  Classical.choose (exists_continuous_integral_solution hT hA)

/-- The Carathéodory fundamental matrix is continuous. -/
theorem continuous_caratheodoryFundamentalMatrix {A : ℝ → Matrix ι ι ℝ} {T : ℝ} (hT : 0 ≤ T)
    (hA : IntervalIntegrable A volume 0 T) :
    Continuous (caratheodoryFundamentalMatrix A hT hA) :=
  (Classical.choose_spec (exists_continuous_integral_solution hT hA)).1

/-- The Carathéodory fundamental matrix solves the integral equation on the horizon. -/
theorem caratheodoryFundamentalMatrix_eq_integral {A : ℝ → Matrix ι ι ℝ} {T : ℝ} (hT : 0 ≤ T)
    (hA : IntervalIntegrable A volume 0 T) :
    ∀ t ∈ Set.Icc 0 T, caratheodoryFundamentalMatrix A hT hA t
      = 1 + ∫ s in (0 : ℝ)..t, A s * caratheodoryFundamentalMatrix A hT hA s :=
  (Classical.choose_spec (exists_continuous_integral_solution hT hA)).2

/-- The Carathéodory fundamental matrix starts at the identity. -/
theorem caratheodoryFundamentalMatrix_zero {A : ℝ → Matrix ι ι ℝ} {T : ℝ} (hT : 0 ≤ T)
    (hA : IntervalIntegrable A volume 0 T) :
    caratheodoryFundamentalMatrix A hT hA 0 = 1 := by
  rw [caratheodoryFundamentalMatrix_eq_integral hT hA 0 ⟨le_rfl, hT⟩,
    intervalIntegral.integral_same, add_zero]

/-- **Uniqueness.**  Every continuous solution of the integral equation agrees with the
Carathéodory fundamental matrix on the horizon. -/
theorem eq_caratheodoryFundamentalMatrix_of_integral_eq {A : ℝ → Matrix ι ι ℝ} {T : ℝ}
    (hT : 0 ≤ T) (hA : IntervalIntegrable A volume 0 T) {V : ℝ → Matrix ι ι ℝ}
    (hV : Continuous V) (hVeq : ∀ t ∈ Set.Icc 0 T, V t = 1 + ∫ s in (0 : ℝ)..t, A s * V s) :
    ∀ t ∈ Set.Icc 0 T, V t = caratheodoryFundamentalMatrix A hT hA t :=
  eq_of_integral_eq hT hA hV (continuous_caratheodoryFundamentalMatrix hT hA) hVeq
    (caratheodoryFundamentalMatrix_eq_integral hT hA)

/-- The Carathéodory fundamental matrix is absolutely continuous on the horizon. -/
theorem absolutelyContinuousOnInterval_caratheodoryFundamentalMatrix {A : ℝ → Matrix ι ι ℝ}
    {T : ℝ} (hT : 0 ≤ T) (hA : IntervalIntegrable A volume 0 T) :
    AbsolutelyContinuousOnInterval (caratheodoryFundamentalMatrix A hT hA) 0 T :=
  absolutelyContinuousOnInterval_of_integral_eq hT hA
    (continuous_caratheodoryFundamentalMatrix hT hA)
    (caratheodoryFundamentalMatrix_eq_integral hT hA)

/-- The Carathéodory fundamental matrix satisfies `U' = A U` almost everywhere inside the
horizon, entry by entry. -/
theorem ae_hasDerivAt_caratheodoryFundamentalMatrix {A : ℝ → Matrix ι ι ℝ} {T : ℝ} (hT : 0 ≤ T)
    (hA : IntervalIntegrable A volume 0 T) :
    ∀ᵐ t, t ∈ Set.Ioo 0 T → ∀ row column : ι,
      HasDerivAt (fun time ↦ caratheodoryFundamentalMatrix A hT hA time row column)
        ((A t * caratheodoryFundamentalMatrix A hT hA t) row column) t :=
  ae_hasDerivAt_entry_of_integral_eq hA (continuous_caratheodoryFundamentalMatrix hT hA)
    (caratheodoryFundamentalMatrix_eq_integral hT hA)

/-- For a continuous generator path the Carathéodory fundamental matrix is the Picard fundamental
matrix of `LinearFundamentalMatrix` on the horizon. -/
theorem caratheodoryFundamentalMatrix_eq_fundamentalMatrix {A : ℝ → Matrix ι ι ℝ}
    (hAcontinuous : Continuous A) {T : ℝ} (hT : 0 ≤ T) :
    ∀ t ∈ Set.Icc 0 T, caratheodoryFundamentalMatrix A hT (hAcontinuous.intervalIntegrable 0 T) t
      = fundamentalMatrix A T t := by
  obtain ⟨K, hK, hbound⟩ := exists_bound_of_continuous hAcontinuous hT
  intro t ht
  exact (eq_caratheodoryFundamentalMatrix_of_integral_eq hT (hAcontinuous.intervalIntegrable 0 T)
    (continuous_fundamentalMatrix hAcontinuous hT hK hbound)
    (fun s hs ↦ fundamentalMatrix_eq_integral hAcontinuous hT hK hbound hs) t ht).symm

/-! ## Comparison with a continuous path -/

/-- **Comparison with a continuous path.**  Let `V` solve the integral equation of a generator
path `A` with integrable norm and `W` that of a continuous path `B`, with `‖V‖ ≤ M` on the
horizon.  Then `‖V(t) - W(t)‖ ≤ (∫₀ᵀ ‖A - B‖) M exp ∫₀ᵗ ‖B‖` on the horizon. -/
theorem norm_sub_le_of_integral_eq {A B V W : ℝ → Matrix ι ι ℝ} {T M : ℝ} (hT : 0 ≤ T)
    (hA : IntervalIntegrable A volume 0 T) (hB : Continuous B) (hV : Continuous V)
    (hW : Continuous W)
    (hVeq : ∀ t ∈ Set.Icc 0 T, V t = 1 + ∫ s in (0 : ℝ)..t, A s * V s)
    (hWeq : ∀ t ∈ Set.Icc 0 T, W t = 1 + ∫ s in (0 : ℝ)..t, B s * W s)
    (hM : ∀ s ∈ Set.Icc 0 T, ‖V s‖ ≤ M) :
    ∀ t ∈ Set.Icc 0 T, ‖V t - W t‖
      ≤ (∫ s in (0 : ℝ)..T, ‖A s - B s‖) * M * Real.exp (∫ s in (0 : ℝ)..t, ‖B s‖) := by
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0 ⟨le_rfl, hT⟩)
  have hsubinterval : ∀ t ∈ Set.Icc 0 T, IntervalIntegrable A volume 0 t := fun t ht ↦
    hA.mono_set (Set.uIcc_subset_uIcc_left (Set.mem_uIcc_of_le ht.1 ht.2))
  have hstep : ∀ r ∈ Set.Icc 0 T, ‖V r - W r‖ ≤
      (∫ s in (0 : ℝ)..T, ‖A s - B s‖) * M + ∫ s in (0 : ℝ)..r, ‖B s‖ * ‖V s - W s‖ := by
    intro r hr
    have hAr := hsubinterval r hr
    have hsplit : V r - W r = (∫ s in (0 : ℝ)..r, B s * (V s - W s)) +
        ∫ s in (0 : ℝ)..r, (A s - B s) * V s := by
      rw [hVeq r hr, hWeq r hr, add_sub_add_left_eq_sub,
        ← intervalIntegral.integral_sub (hAr.mul_continuousOn hV.continuousOn)
          ((hB.mul hW).intervalIntegrable _ _),
        ← intervalIntegral.integral_add ((hB.mul (hV.sub hW)).intervalIntegrable _ _)
          ((hAr.sub (hB.intervalIntegrable _ _)).mul_continuousOn hV.continuousOn)]
      congr 1
      funext s
      noncomm_ring
    have hfirst : ‖∫ s in (0 : ℝ)..r, B s * (V s - W s)‖ ≤
        ∫ s in (0 : ℝ)..r, ‖B s‖ * ‖V s - W s‖ :=
      (intervalIntegral.norm_integral_le_integral_norm hr.1).trans
        (intervalIntegral.integral_mono_on hr.1
          ((hB.mul (hV.sub hW)).norm.intervalIntegrable _ _)
          ((hB.norm.mul (hV.sub hW).norm).intervalIntegrable _ _) fun s _ ↦ norm_mul_le _ _)
    have hsecond : ‖∫ s in (0 : ℝ)..r, (A s - B s) * V s‖ ≤
        (∫ s in (0 : ℝ)..T, ‖A s - B s‖) * M := by
      refine (intervalIntegral.norm_integral_le_integral_norm hr.1).trans ?_
      calc ∫ s in (0 : ℝ)..r, ‖(A s - B s) * V s‖
          ≤ ∫ s in (0 : ℝ)..r, ‖A s - B s‖ * M := by
            refine intervalIntegral.integral_mono_on hr.1
              (((hAr.sub (hB.intervalIntegrable _ _)).mul_continuousOn hV.continuousOn).norm)
              ((hAr.sub (hB.intervalIntegrable _ _)).norm.mul_const _) fun s hs ↦ ?_
            exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left
              (hM s ⟨hs.1, hs.2.trans hr.2⟩) (norm_nonneg _))
        _ = (∫ s in (0 : ℝ)..r, ‖A s - B s‖) * M := intervalIntegral.integral_mul_const _ _
        _ ≤ (∫ s in (0 : ℝ)..T, ‖A s - B s‖) * M := by
            refine mul_le_mul_of_nonneg_right ?_ hM0
            exact intervalIntegral.integral_mono_interval le_rfl hr.1 hr.2
              (ae_of_all _ fun _ ↦ norm_nonneg _) (hA.sub (hB.intervalIntegrable _ _)).norm
    rw [hsplit]
    refine (norm_add_le _ _).trans ?_
    linarith [hfirst, hsecond]
  intro t ht
  exact le_mul_exp_integral_of_le_add_integral (a := fun s ↦ ‖B s‖)
    (u := fun s ↦ ‖V s - W s‖) hB.norm (hV.sub hW).norm (fun s _ ↦ norm_nonneg _) hstep t ht

/-! ## The exponential bound -/

/-- **The exponential bound.**  The Carathéodory fundamental matrix is bounded by the exponential
of the integrated generator norm: `‖U(t)‖ ≤ exp ∫₀ᵗ ‖A‖` on the horizon. -/
theorem norm_caratheodoryFundamentalMatrix_le {A : ℝ → Matrix ι ι ℝ} {T : ℝ} (hT : 0 ≤ T)
    (hA : IntervalIntegrable A volume 0 T) :
    ∀ t ∈ Set.Icc 0 T,
      ‖caratheodoryFundamentalMatrix A hT hA t‖ ≤ Real.exp (∫ s in (0 : ℝ)..t, ‖A s‖) := by
  obtain ⟨M, hM0, hM⟩ :=
    exists_bound_of_continuous (continuous_caratheodoryFundamentalMatrix hT hA) hT
  intro t ht
  have hAt : IntervalIntegrable A volume 0 t :=
    hA.mono_set (Set.uIcc_subset_uIcc_left (Set.mem_uIcc_of_le ht.1 ht.2))
  have hsmall : ∀ ε : ℝ, 0 < ε → ‖caratheodoryFundamentalMatrix A hT hA t‖
      ≤ (1 + ε * M) * Real.exp ((∫ s in (0 : ℝ)..t, ‖A s‖) + ε) := by
    intro ε hε
    obtain ⟨B, hB, hclose⟩ := exists_continuous_integral_norm_sub_le hT hA hε
    obtain ⟨K, hK, hboundB⟩ := exists_bound_of_continuous hB hT
    have hcompare := norm_sub_le_of_integral_eq hT hA hB
      (continuous_caratheodoryFundamentalMatrix hT hA)
      (continuous_fundamentalMatrix hB hT hK hboundB)
      (caratheodoryFundamentalMatrix_eq_integral hT hA)
      (fun s hs ↦ fundamentalMatrix_eq_integral hB hT hK hboundB hs) hM t ht
    have hBnorm := norm_fundamentalMatrix_le_exp_integral hB hT t ht
    have hnormB : (∫ s in (0 : ℝ)..t, ‖B s‖) ≤ (∫ s in (0 : ℝ)..t, ‖A s‖) + ε := by
      have htriangle : (∫ s in (0 : ℝ)..t, ‖B s‖) ≤
          ∫ s in (0 : ℝ)..t, (‖A s‖ + ‖A s - B s‖) :=
        intervalIntegral.integral_mono_on ht.1 (hB.norm.intervalIntegrable _ _)
          (hAt.norm.add (hAt.sub (hB.intervalIntegrable _ _)).norm) fun s _ ↦
            calc ‖B s‖ = ‖A s - (A s - B s)‖ := by rw [sub_sub_cancel]
              _ ≤ ‖A s‖ + ‖A s - B s‖ := norm_sub_le _ _
      rw [intervalIntegral.integral_add hAt.norm (hAt.sub (hB.intervalIntegrable _ _)).norm]
        at htriangle
      have hsub : (∫ s in (0 : ℝ)..t, ‖A s - B s‖) ≤ ∫ s in (0 : ℝ)..T, ‖A s - B s‖ :=
        intervalIntegral.integral_mono_interval le_rfl ht.1 ht.2
          (ae_of_all _ fun _ ↦ norm_nonneg _) (hA.sub (hB.intervalIntegrable _ _)).norm
      linarith
    have hexp : Real.exp (∫ s in (0 : ℝ)..t, ‖B s‖)
        ≤ Real.exp ((∫ s in (0 : ℝ)..t, ‖A s‖) + ε) := Real.exp_le_exp.mpr hnormB
    calc ‖caratheodoryFundamentalMatrix A hT hA t‖
        = ‖fundamentalMatrix B T t
            + (caratheodoryFundamentalMatrix A hT hA t - fundamentalMatrix B T t)‖ := by
          congr 1
          abel
      _ ≤ ‖fundamentalMatrix B T t‖
          + ‖caratheodoryFundamentalMatrix A hT hA t - fundamentalMatrix B T t‖ :=
          norm_add_le _ _
      _ ≤ Real.exp (∫ s in (0 : ℝ)..t, ‖B s‖)
          + (∫ s in (0 : ℝ)..T, ‖A s - B s‖) * M * Real.exp (∫ s in (0 : ℝ)..t, ‖B s‖) :=
          add_le_add hBnorm hcompare
      _ ≤ Real.exp ((∫ s in (0 : ℝ)..t, ‖A s‖) + ε)
          + ε * M * Real.exp ((∫ s in (0 : ℝ)..t, ‖A s‖) + ε) :=
          add_le_add hexp (mul_le_mul (mul_le_mul_of_nonneg_right hclose hM0) hexp
            (Real.exp_pos _).le (mul_nonneg hε.le hM0))
      _ = (1 + ε * M) * Real.exp ((∫ s in (0 : ℝ)..t, ‖A s‖) + ε) := by ring
  have hlimit : Tendsto (fun n : ℕ ↦ (1 + 1 / ((n : ℝ) + 1) * M)
        * Real.exp ((∫ s in (0 : ℝ)..t, ‖A s‖) + 1 / ((n : ℝ) + 1))) atTop
      (𝓝 ((1 + 0 * M) * Real.exp ((∫ s in (0 : ℝ)..t, ‖A s‖) + 0))) :=
    (tendsto_const_nhds.add (tendsto_one_div_add_atTop_nhds_zero_nat.mul_const M)).mul
      ((Real.continuous_exp.tendsto _).comp
        (tendsto_const_nhds.add tendsto_one_div_add_atTop_nhds_zero_nat))
  simp only [zero_mul, add_zero, one_mul] at hlimit
  exact ge_of_tendsto' hlimit fun n ↦ hsmall _ (by positivity)

/-- The Carathéodory fundamental matrix is bounded on the horizon by `exp ∫₀ᵀ ‖A‖`. -/
theorem norm_caratheodoryFundamentalMatrix_le_horizon {A : ℝ → Matrix ι ι ℝ} {T : ℝ}
    (hT : 0 ≤ T) (hA : IntervalIntegrable A volume 0 T) :
    ∀ t ∈ Set.Icc 0 T,
      ‖caratheodoryFundamentalMatrix A hT hA t‖ ≤ Real.exp (∫ s in (0 : ℝ)..T, ‖A s‖) :=
  fun t ht ↦ (norm_caratheodoryFundamentalMatrix_le hT hA t ht).trans (Real.exp_le_exp.mpr
    (intervalIntegral.integral_mono_interval le_rfl ht.1 ht.2
      (ae_of_all _ fun _ ↦ norm_nonneg _) hA.norm))

/-! ## Stability under `L¹` perturbation -/

/-- **Variation of constants for integrable paths.**  Two generator paths with integrable norm on
the horizon have Carathéodory fundamental matrices within
`(∫₀ᵀ ‖A - B‖) e^{∫₀ᵀ ‖A‖} e^{∫₀ᵀ ‖B‖}` at every time of the horizon. -/
theorem norm_caratheodoryFundamentalMatrix_sub_le {A B : ℝ → Matrix ι ι ℝ} {T : ℝ} (hT : 0 ≤ T)
    (hA : IntervalIntegrable A volume 0 T) (hB : IntervalIntegrable B volume 0 T) :
    ∀ t ∈ Set.Icc 0 T,
      ‖caratheodoryFundamentalMatrix A hT hA t - caratheodoryFundamentalMatrix B hT hB t‖
        ≤ (∫ s in (0 : ℝ)..T, ‖A s - B s‖) * Real.exp (∫ s in (0 : ℝ)..T, ‖A s‖)
          * Real.exp (∫ s in (0 : ℝ)..T, ‖B s‖) := by
  intro t ht
  have hsmall : ∀ ε : ℝ, 0 < ε →
      ‖caratheodoryFundamentalMatrix A hT hA t - caratheodoryFundamentalMatrix B hT hB t‖
        ≤ (((∫ s in (0 : ℝ)..T, ‖A s - B s‖) + ε) * Real.exp (∫ s in (0 : ℝ)..T, ‖A s‖)
            + ε * Real.exp (∫ s in (0 : ℝ)..T, ‖B s‖))
          * Real.exp ((∫ s in (0 : ℝ)..T, ‖B s‖) + ε) := by
    intro ε hε
    obtain ⟨C, hC, hclose⟩ := exists_continuous_integral_norm_sub_le hT hB hε
    obtain ⟨K, hK, hboundC⟩ := exists_bound_of_continuous hC hT
    have hW := continuous_fundamentalMatrix hC hT hK hboundC
    have hWeq : ∀ s ∈ Set.Icc 0 T,
        fundamentalMatrix C T s = 1 + ∫ r in (0 : ℝ)..s, C r * fundamentalMatrix C T r :=
      fun s hs ↦ fundamentalMatrix_eq_integral hC hT hK hboundC hs
    have hAcompare := norm_sub_le_of_integral_eq hT hA hC
      (continuous_caratheodoryFundamentalMatrix hT hA) hW
      (caratheodoryFundamentalMatrix_eq_integral hT hA) hWeq
      (norm_caratheodoryFundamentalMatrix_le_horizon hT hA) t ht
    have hBcompare := norm_sub_le_of_integral_eq hT hB hC
      (continuous_caratheodoryFundamentalMatrix hT hB) hW
      (caratheodoryFundamentalMatrix_eq_integral hT hB) hWeq
      (norm_caratheodoryFundamentalMatrix_le_horizon hT hB) t ht
    have hAC : (∫ s in (0 : ℝ)..T, ‖A s - C s‖) ≤ (∫ s in (0 : ℝ)..T, ‖A s - B s‖) + ε := by
      have hstep : (∫ s in (0 : ℝ)..T, ‖A s - C s‖) ≤
          ∫ s in (0 : ℝ)..T, (‖A s - B s‖ + ‖B s - C s‖) :=
        intervalIntegral.integral_mono_on hT (hA.sub (hC.intervalIntegrable _ _)).norm
          ((hA.sub hB).norm.add (hB.sub (hC.intervalIntegrable _ _)).norm) fun s _ ↦
            calc ‖A s - C s‖ = ‖(A s - B s) + (B s - C s)‖ := by
                  congr 1
                  abel
              _ ≤ ‖A s - B s‖ + ‖B s - C s‖ := norm_add_le _ _
      rw [intervalIntegral.integral_add (hA.sub hB).norm
        (hB.sub (hC.intervalIntegrable _ _)).norm] at hstep
      linarith
    have hCnorm : (∫ s in (0 : ℝ)..t, ‖C s‖) ≤ (∫ s in (0 : ℝ)..T, ‖B s‖) + ε := by
      have hmono : (∫ s in (0 : ℝ)..t, ‖C s‖) ≤ ∫ s in (0 : ℝ)..T, ‖C s‖ :=
        intervalIntegral.integral_mono_interval le_rfl ht.1 ht.2
          (ae_of_all _ fun _ ↦ norm_nonneg _) (hC.norm.intervalIntegrable _ _)
      have htriangle : (∫ s in (0 : ℝ)..T, ‖C s‖) ≤
          ∫ s in (0 : ℝ)..T, (‖B s‖ + ‖B s - C s‖) :=
        intervalIntegral.integral_mono_on hT (hC.norm.intervalIntegrable _ _)
          (hB.norm.add (hB.sub (hC.intervalIntegrable _ _)).norm) fun s _ ↦
            calc ‖C s‖ = ‖B s - (B s - C s)‖ := by rw [sub_sub_cancel]
              _ ≤ ‖B s‖ + ‖B s - C s‖ := norm_sub_le _ _
      rw [intervalIntegral.integral_add hB.norm (hB.sub (hC.intervalIntegrable _ _)).norm]
        at htriangle
      linarith
    have hexp : Real.exp (∫ s in (0 : ℝ)..t, ‖C s‖)
        ≤ Real.exp ((∫ s in (0 : ℝ)..T, ‖B s‖) + ε) := Real.exp_le_exp.mpr hCnorm
    have hdistance : 0 ≤ (∫ s in (0 : ℝ)..T, ‖A s - B s‖) + ε :=
      add_nonneg (intervalIntegral.integral_nonneg hT fun s _ ↦ norm_nonneg _) hε.le
    calc ‖caratheodoryFundamentalMatrix A hT hA t - caratheodoryFundamentalMatrix B hT hB t‖
        = ‖(caratheodoryFundamentalMatrix A hT hA t - fundamentalMatrix C T t)
            - (caratheodoryFundamentalMatrix B hT hB t - fundamentalMatrix C T t)‖ := by
          congr 1
          abel
      _ ≤ ‖caratheodoryFundamentalMatrix A hT hA t - fundamentalMatrix C T t‖
          + ‖caratheodoryFundamentalMatrix B hT hB t - fundamentalMatrix C T t‖ :=
          norm_sub_le _ _
      _ ≤ (∫ s in (0 : ℝ)..T, ‖A s - C s‖) * Real.exp (∫ s in (0 : ℝ)..T, ‖A s‖)
            * Real.exp (∫ s in (0 : ℝ)..t, ‖C s‖)
          + (∫ s in (0 : ℝ)..T, ‖B s - C s‖) * Real.exp (∫ s in (0 : ℝ)..T, ‖B s‖)
            * Real.exp (∫ s in (0 : ℝ)..t, ‖C s‖) :=
          add_le_add hAcompare hBcompare
      _ ≤ ((∫ s in (0 : ℝ)..T, ‖A s - B s‖) + ε) * Real.exp (∫ s in (0 : ℝ)..T, ‖A s‖)
            * Real.exp ((∫ s in (0 : ℝ)..T, ‖B s‖) + ε)
          + ε * Real.exp (∫ s in (0 : ℝ)..T, ‖B s‖)
            * Real.exp ((∫ s in (0 : ℝ)..T, ‖B s‖) + ε) :=
          add_le_add
            (mul_le_mul (mul_le_mul_of_nonneg_right hAC (Real.exp_pos _).le) hexp
              (Real.exp_pos _).le (mul_nonneg hdistance (Real.exp_pos _).le))
            (mul_le_mul (mul_le_mul_of_nonneg_right hclose (Real.exp_pos _).le) hexp
              (Real.exp_pos _).le (mul_nonneg hε.le (Real.exp_pos _).le))
      _ = (((∫ s in (0 : ℝ)..T, ‖A s - B s‖) + ε) * Real.exp (∫ s in (0 : ℝ)..T, ‖A s‖)
            + ε * Real.exp (∫ s in (0 : ℝ)..T, ‖B s‖))
          * Real.exp ((∫ s in (0 : ℝ)..T, ‖B s‖) + ε) := by ring
  have hlimit : Tendsto (fun n : ℕ ↦
        (((∫ s in (0 : ℝ)..T, ‖A s - B s‖) + 1 / ((n : ℝ) + 1))
            * Real.exp (∫ s in (0 : ℝ)..T, ‖A s‖)
          + 1 / ((n : ℝ) + 1) * Real.exp (∫ s in (0 : ℝ)..T, ‖B s‖))
          * Real.exp ((∫ s in (0 : ℝ)..T, ‖B s‖) + 1 / ((n : ℝ) + 1))) atTop
      (𝓝 ((((∫ s in (0 : ℝ)..T, ‖A s - B s‖) + 0) * Real.exp (∫ s in (0 : ℝ)..T, ‖A s‖)
          + 0 * Real.exp (∫ s in (0 : ℝ)..T, ‖B s‖))
          * Real.exp ((∫ s in (0 : ℝ)..T, ‖B s‖) + 0))) :=
    (((tendsto_const_nhds.add tendsto_one_div_add_atTop_nhds_zero_nat).mul_const _).add
      (tendsto_one_div_add_atTop_nhds_zero_nat.mul_const _)).mul
      ((Real.continuous_exp.tendsto _).comp
        (tendsto_const_nhds.add tendsto_one_div_add_atTop_nhds_zero_nat))
  simp only [add_zero, zero_mul] at hlimit
  exact ge_of_tendsto' hlimit fun n ↦ hsmall _ (by positivity)

/-- **Uniform convergence under `L¹` approximation.**  If generator paths with integrable norm
converge to `A` in `L¹([0, T])`, their Carathéodory fundamental matrices converge to that of `A`
uniformly on the horizon. -/
theorem tendstoUniformlyOn_caratheodoryFundamentalMatrix {A : ℝ → Matrix ι ι ℝ}
    {approximation : ℕ → ℝ → Matrix ι ι ℝ} {T : ℝ} (hT : 0 ≤ T)
    (hA : IntervalIntegrable A volume 0 T)
    (happroximation : ∀ k, IntervalIntegrable (approximation k) volume 0 T)
    (hclose : Tendsto (fun k ↦ ∫ s in (0 : ℝ)..T, ‖approximation k s - A s‖) atTop (𝓝 0)) :
    TendstoUniformlyOn
      (fun k ↦ caratheodoryFundamentalMatrix (approximation k) hT (happroximation k))
      (caratheodoryFundamentalMatrix A hT hA) atTop (Set.Icc 0 T) := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have hδ := (hclose.mul_const (Real.exp ((∫ s in (0 : ℝ)..T, ‖A s‖) + 1))).mul_const
    (Real.exp (∫ s in (0 : ℝ)..T, ‖A s‖))
  rw [zero_mul, zero_mul] at hδ
  filter_upwards [(tendsto_order.1 hclose).2 1 one_pos, (tendsto_order.1 hδ).2 ε hε]
    with k hk1 hkε t ht
  rw [dist_comm, dist_eq_norm]
  refine lt_of_le_of_lt ?_ hkε
  have hnormk : (∫ s in (0 : ℝ)..T, ‖approximation k s‖) ≤ (∫ s in (0 : ℝ)..T, ‖A s‖) + 1 := by
    have hstep : (∫ s in (0 : ℝ)..T, ‖approximation k s‖) ≤
        ∫ s in (0 : ℝ)..T, (‖A s‖ + ‖approximation k s - A s‖) :=
      intervalIntegral.integral_mono_on hT (happroximation k).norm
        (hA.norm.add ((happroximation k).sub hA).norm) fun s _ ↦
          calc ‖approximation k s‖ = ‖A s + (approximation k s - A s)‖ := by
                congr 1
                abel
            _ ≤ ‖A s‖ + ‖approximation k s - A s‖ := norm_add_le _ _
    rw [intervalIntegral.integral_add hA.norm ((happroximation k).sub hA).norm] at hstep
    linarith
  have hnonneg : 0 ≤ ∫ s in (0 : ℝ)..T, ‖approximation k s - A s‖ :=
    intervalIntegral.integral_nonneg hT fun s _ ↦ norm_nonneg _
  exact (norm_caratheodoryFundamentalMatrix_sub_le hT (happroximation k) hA t ht).trans
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hnormk) hnonneg) (Real.exp_pos _).le)

/-- **Continuous approximations.**  If continuous generator paths converge to `A` in
`L¹([0, T])`, their Picard fundamental matrices converge to the Carathéodory fundamental matrix of
`A` uniformly on the horizon. -/
theorem tendstoUniformlyOn_fundamentalMatrix_of_continuous {A : ℝ → Matrix ι ι ℝ}
    {approximation : ℕ → ℝ → Matrix ι ι ℝ} {T : ℝ} (hT : 0 ≤ T)
    (hA : IntervalIntegrable A volume 0 T) (hcontinuous : ∀ k, Continuous (approximation k))
    (hclose : Tendsto (fun k ↦ ∫ s in (0 : ℝ)..T, ‖approximation k s - A s‖) atTop (𝓝 0)) :
    TendstoUniformlyOn (fun k ↦ fundamentalMatrix (approximation k) T)
      (caratheodoryFundamentalMatrix A hT hA) atTop (Set.Icc 0 T) :=
  (tendstoUniformlyOn_caratheodoryFundamentalMatrix hT hA
    (fun k ↦ (hcontinuous k).intervalIntegrable 0 T) hclose).congr
    (Eventually.of_forall fun k t ht ↦
      caratheodoryFundamentalMatrix_eq_fundamentalMatrix (hcontinuous k) hT t ht)

end

end Descent.Portability.CaratheodoryFundamentalMatrix
