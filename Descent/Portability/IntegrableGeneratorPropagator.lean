/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.LinearFundamentalMatrix

assert_below Descent.Decision Descent.Program

/-!
# Propagators of generator paths with integrable norm

NOTE1 section 2.4 allows nonnegative measurable rates whose generator norm is merely integrable
on the horizon.  Its argument bounds propagator differences by the `L¹` distance of the
generators and passes to the limit.  With an unbounded generator the uniform bound `K` of
`Descent.Portability.LinearFundamentalMatrix` is not available, so every estimate here is stated
through the integrated norm `∫₀ᵗ ‖A‖` instead.

`le_mul_exp_integral_of_le_add_integral` is Gronwall's inequality with a continuous nonnegative
coefficient: `u t ≤ c + ∫₀ᵗ a u` on `[0, T]` gives `u t ≤ c exp (∫₀ᵗ a)`.  The proof compares the
damped primitive `e^{-∫₀ᵗ a} ∫₀ᵗ a u` with `c (1 - e^{-∫₀ᵗ a})` by their right derivatives.

For a continuous generator path, `norm_fundamentalMatrix_le_exp_integral` bounds the fundamental
matrix by `exp (∫₀ᵗ ‖A‖)`, and `norm_fundamentalMatrix_sub_le_exp_integral` is the variation of
constants estimate `‖U_A(t) - U_B(t)‖ ≤ (∫₀ᵀ ‖A - B‖) e^{∫₀ᵀ ‖B‖} e^{∫₀ᵗ ‖A‖}`: the constant
depends on the generators only through their integrated norms, so it survives approximation of
an unbounded integrable path.  `exists_continuous_integral_norm_sub_le` supplies such
approximations: every function integrable on `[0, T]` is within any `ε` in `L¹([0, T])` of a
continuous function.

## Empirical status

None.  The bodies here are calculus: integral inequalities, derivatives of primitives and the
density of continuous functions in `L¹`, so no measurement can bear on them.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.IntegrableGeneratorPropagator

open MeasureTheory
open Descent.Portability.LinearFundamentalMatrix
open scoped Matrix.Norms.Operator

noncomputable section

/-! ## Gronwall's inequality with a continuous coefficient -/

/-- **Gronwall's inequality with a continuous nonnegative coefficient.**  If `u t ≤ c + ∫₀ᵗ a u`
on `[0, T]`, then `u t ≤ c exp (∫₀ᵗ a)` there. -/
theorem le_mul_exp_integral_of_le_add_integral {a u : ℝ → ℝ} (ha : Continuous a)
    (hu : Continuous u) {T c : ℝ} (hanonneg : ∀ s ∈ Set.Icc 0 T, 0 ≤ a s)
    (hbound : ∀ t ∈ Set.Icc 0 T, u t ≤ c + ∫ s in (0 : ℝ)..t, a s * u s) :
    ∀ t ∈ Set.Icc 0 T, u t ≤ c * Real.exp (∫ s in (0 : ℝ)..t, a s) := by
  have hprimitive : ∀ t, HasDerivAt (fun r ↦ ∫ s in (0 : ℝ)..r, a s) (a t) t := fun t ↦
    intervalIntegral.integral_hasDerivAt_right (ha.intervalIntegrable 0 t)
      (ha.stronglyMeasurableAtFilter _ _) ha.continuousAt
  have hweighted : ∀ t, HasDerivAt (fun r ↦ ∫ s in (0 : ℝ)..r, a s * u s) (a t * u t) t :=
    fun t ↦ intervalIntegral.integral_hasDerivAt_right ((ha.mul hu).intervalIntegrable 0 t)
      ((ha.mul hu).stronglyMeasurableAtFilter _ _) (ha.mul hu).continuousAt
  have hdamped : ∀ t, HasDerivAt
      (fun r ↦ Real.exp (-∫ s in (0 : ℝ)..r, a s) * ∫ s in (0 : ℝ)..r, a s * u s)
      (Real.exp (-∫ s in (0 : ℝ)..t, a s) *
        (a t * u t - a t * ∫ s in (0 : ℝ)..t, a s * u s)) t := by
    intro t
    convert ((hprimitive t).neg.exp).mul (hweighted t) using 1
    simp only [Pi.neg_apply]
    ring
  have hceiling : ∀ t, HasDerivAt (fun r ↦ c * (1 - Real.exp (-∫ s in (0 : ℝ)..r, a s)))
      (c * (a t * Real.exp (-∫ s in (0 : ℝ)..t, a s))) t := by
    intro t
    convert (((hprimitive t).neg.exp).const_sub 1).const_mul c using 1
    simp only [Pi.neg_apply]
    ring
  have hslope : ∀ t ∈ Set.Ico (0 : ℝ) T,
      Real.exp (-∫ s in (0 : ℝ)..t, a s) * (a t * u t - a t * ∫ s in (0 : ℝ)..t, a s * u s) ≤
        c * (a t * Real.exp (-∫ s in (0 : ℝ)..t, a s)) := by
    intro t ht
    have hmem : t ∈ Set.Icc (0 : ℝ) T := Set.Ico_subset_Icc_self ht
    have hscaled := mul_le_mul_of_nonneg_left (hbound t hmem) (hanonneg t hmem)
    have hgap : a t * u t - a t * ∫ s in (0 : ℝ)..t, a s * u s ≤ a t * c := by
      nlinarith [hscaled]
    calc Real.exp (-∫ s in (0 : ℝ)..t, a s) *
          (a t * u t - a t * ∫ s in (0 : ℝ)..t, a s * u s)
        ≤ Real.exp (-∫ s in (0 : ℝ)..t, a s) * (a t * c) :=
          mul_le_mul_of_nonneg_left hgap (Real.exp_pos _).le
      _ = c * (a t * Real.exp (-∫ s in (0 : ℝ)..t, a s)) := by ring
  have hcompare := image_le_of_deriv_right_le_deriv_boundary
    (f := fun r ↦ Real.exp (-∫ s in (0 : ℝ)..r, a s) * ∫ s in (0 : ℝ)..r, a s * u s)
    (B := fun r ↦ c * (1 - Real.exp (-∫ s in (0 : ℝ)..r, a s))) (a := 0) (b := T)
    (fun t _ ↦ (hdamped t).continuousAt.continuousWithinAt)
    (fun t _ ↦ (hdamped t).hasDerivWithinAt) (by simp)
    (fun t _ ↦ (hceiling t).continuousAt.continuousWithinAt)
    (fun t _ ↦ (hceiling t).hasDerivWithinAt) hslope
  intro t ht
  have hle := hcompare ht
  have hproduct : Real.exp (∫ s in (0 : ℝ)..t, a s) * Real.exp (-∫ s in (0 : ℝ)..t, a s) = 1 := by
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  have hscaled := mul_le_mul_of_nonneg_left hle (Real.exp_pos (∫ s in (0 : ℝ)..t, a s)).le
  have hleft : Real.exp (∫ s in (0 : ℝ)..t, a s) *
      (Real.exp (-∫ s in (0 : ℝ)..t, a s) * ∫ s in (0 : ℝ)..t, a s * u s) =
        ∫ s in (0 : ℝ)..t, a s * u s := by
    rw [← mul_assoc, hproduct, one_mul]
  have hright : Real.exp (∫ s in (0 : ℝ)..t, a s) *
      (c * (1 - Real.exp (-∫ s in (0 : ℝ)..t, a s))) =
        c * Real.exp (∫ s in (0 : ℝ)..t, a s) - c := by
    linear_combination (-c) * hproduct
  simp only at hscaled
  rw [hleft, hright] at hscaled
  linarith [hbound t ht]

/-! ## Continuous generator paths -/

/-- A continuous generator path is bounded on the horizon. -/
theorem exists_bound_of_continuous {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : ℝ → Matrix ι ι ℝ} (hA : Continuous A) {T : ℝ} (hT : 0 ≤ T) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ s ∈ Set.Icc 0 T, ‖A s‖ ≤ K := by
  obtain ⟨maximizer, _, hmax⟩ :=
    isCompact_Icc.exists_isMaxOn (Set.nonempty_Icc.mpr hT) hA.norm.continuousOn
  exact ⟨‖A maximizer‖, norm_nonneg _, fun s hs ↦ isMaxOn_iff.mp hmax s hs⟩

/-- **The fundamental matrix of a continuous path is bounded by the exponential of the
integrated generator norm.** -/
theorem norm_fundamentalMatrix_le_exp_integral {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : ℝ → Matrix ι ι ℝ} (hA : Continuous A) {T : ℝ} (hT : 0 ≤ T) :
    ∀ t ∈ Set.Icc 0 T, ‖fundamentalMatrix A T t‖ ≤ Real.exp (∫ s in (0 : ℝ)..t, ‖A s‖) := by
  obtain ⟨K, hK, hbound⟩ := exists_bound_of_continuous hA hT
  have hU := continuous_fundamentalMatrix hA hT hK hbound
  have hstep : ∀ t ∈ Set.Icc 0 T, ‖fundamentalMatrix A T t‖ ≤
      1 + ∫ s in (0 : ℝ)..t, ‖A s‖ * ‖fundamentalMatrix A T s‖ := by
    intro t ht
    rw [fundamentalMatrix_eq_integral hA hT hK hbound ht]
    refine (norm_add_le _ _).trans (add_le_add norm_identityMatrix_le_one ?_)
    exact (intervalIntegral.norm_integral_le_integral_norm ht.1).trans
      (intervalIntegral.integral_mono_on ht.1 ((hA.mul hU).norm.intervalIntegrable _ _)
        ((hA.norm.mul hU.norm).intervalIntegrable _ _) fun s _ ↦ norm_mul_le _ _)
  intro t ht
  exact (le_mul_exp_integral_of_le_add_integral (a := fun s ↦ ‖A s‖)
    (u := fun s ↦ ‖fundamentalMatrix A T s‖) hA.norm hU.norm (fun s _ ↦ norm_nonneg _)
    hstep t ht).trans_eq (one_mul _)

/-- **Variation of constants with integrated norms.**  Two continuous generator paths have
fundamental matrices within `(∫₀ᵀ ‖A - B‖) e^{∫₀ᵀ ‖B‖} e^{∫₀ᵗ ‖A‖}` at every time of the
horizon. -/
theorem norm_fundamentalMatrix_sub_le_exp_integral {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A B : ℝ → Matrix ι ι ℝ} (hA : Continuous A) (hB : Continuous B) {T : ℝ} (hT : 0 ≤ T) :
    ∀ t ∈ Set.Icc 0 T, ‖fundamentalMatrix A T t - fundamentalMatrix B T t‖ ≤
      (∫ s in (0 : ℝ)..T, ‖A s - B s‖) * Real.exp (∫ s in (0 : ℝ)..T, ‖B s‖) *
        Real.exp (∫ s in (0 : ℝ)..t, ‖A s‖) := by
  obtain ⟨K, hK, hboundA⟩ := exists_bound_of_continuous hA hT
  obtain ⟨L, hL, hboundB⟩ := exists_bound_of_continuous hB hT
  have hUA := continuous_fundamentalMatrix hA hT hK hboundA
  have hUB := continuous_fundamentalMatrix hB hT hL hboundB
  have hstep : ∀ t ∈ Set.Icc 0 T, ‖fundamentalMatrix A T t - fundamentalMatrix B T t‖ ≤
      (∫ s in (0 : ℝ)..T, ‖A s - B s‖) * Real.exp (∫ s in (0 : ℝ)..T, ‖B s‖) +
        ∫ s in (0 : ℝ)..t, ‖A s‖ * ‖fundamentalMatrix A T s - fundamentalMatrix B T s‖ := by
    intro t ht
    have hsplit : fundamentalMatrix A T t - fundamentalMatrix B T t =
        (∫ s in (0 : ℝ)..t, A s * (fundamentalMatrix A T s - fundamentalMatrix B T s)) +
          ∫ s in (0 : ℝ)..t, (A s - B s) * fundamentalMatrix B T s := by
      rw [fundamentalMatrix_eq_integral hA hT hK hboundA ht,
        fundamentalMatrix_eq_integral hB hT hL hboundB ht, add_sub_add_left_eq_sub,
        ← intervalIntegral.integral_sub ((hA.mul hUA).intervalIntegrable _ _)
          ((hB.mul hUB).intervalIntegrable _ _),
        ← intervalIntegral.integral_add ((hA.mul (hUA.sub hUB)).intervalIntegrable _ _)
          (((hA.sub hB).mul hUB).intervalIntegrable _ _)]
      congr 1
      funext s
      noncomm_ring
    have hfirst :
        ‖∫ s in (0 : ℝ)..t, A s * (fundamentalMatrix A T s - fundamentalMatrix B T s)‖ ≤
          ∫ s in (0 : ℝ)..t, ‖A s‖ * ‖fundamentalMatrix A T s - fundamentalMatrix B T s‖ :=
      (intervalIntegral.norm_integral_le_integral_norm ht.1).trans
        (intervalIntegral.integral_mono_on ht.1
          ((hA.mul (hUA.sub hUB)).norm.intervalIntegrable _ _)
          ((hA.norm.mul (hUA.sub hUB).norm).intervalIntegrable _ _) fun s _ ↦ norm_mul_le _ _)
    have hsecond : ‖∫ s in (0 : ℝ)..t, (A s - B s) * fundamentalMatrix B T s‖ ≤
        (∫ s in (0 : ℝ)..T, ‖A s - B s‖) * Real.exp (∫ s in (0 : ℝ)..T, ‖B s‖) := by
      refine (intervalIntegral.norm_integral_le_integral_norm ht.1).trans ?_
      calc ∫ s in (0 : ℝ)..t, ‖(A s - B s) * fundamentalMatrix B T s‖
          ≤ ∫ s in (0 : ℝ)..t, ‖A s - B s‖ * Real.exp (∫ r in (0 : ℝ)..T, ‖B r‖) := by
            refine intervalIntegral.integral_mono_on ht.1
              (((hA.sub hB).mul hUB).norm.intervalIntegrable _ _)
              (((hA.sub hB).norm.mul continuous_const).intervalIntegrable _ _) fun s hs ↦ ?_
            have hsmem : s ∈ Set.Icc 0 T := ⟨hs.1, hs.2.trans ht.2⟩
            refine (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))
            refine (norm_fundamentalMatrix_le_exp_integral hB hT s hsmem).trans
              (Real.exp_le_exp.mpr ?_)
            exact intervalIntegral.integral_mono_interval le_rfl hsmem.1 hsmem.2
              (ae_of_all _ fun _ ↦ norm_nonneg _) (hB.norm.intervalIntegrable _ _)
        _ = (∫ s in (0 : ℝ)..t, ‖A s - B s‖) * Real.exp (∫ r in (0 : ℝ)..T, ‖B r‖) :=
            intervalIntegral.integral_mul_const _ _
        _ ≤ (∫ s in (0 : ℝ)..T, ‖A s - B s‖) * Real.exp (∫ s in (0 : ℝ)..T, ‖B s‖) := by
            refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
            exact intervalIntegral.integral_mono_interval le_rfl ht.1 ht.2
              (ae_of_all _ fun _ ↦ norm_nonneg _) ((hA.sub hB).norm.intervalIntegrable _ _)
    rw [hsplit]
    refine (norm_add_le _ _).trans ?_
    linarith [hfirst, hsecond]
  intro t ht
  exact le_mul_exp_integral_of_le_add_integral (a := fun s ↦ ‖A s‖)
    (u := fun s ↦ ‖fundamentalMatrix A T s - fundamentalMatrix B T s‖) hA.norm
    (hUA.sub hUB).norm (fun s _ ↦ norm_nonneg _) hstep t ht

/-! ## Continuous approximation in `L¹` -/

/-- **Continuous functions are dense in `L¹([0, T])`.**  A function integrable on the horizon is
within any `ε > 0` of a continuous function in `L¹([0, T])`. -/
theorem exists_continuous_integral_norm_sub_le {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {f : ℝ → E} {T : ℝ} (hT : 0 ≤ T) (hf : IntervalIntegrable f volume 0 T)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ g : ℝ → E, Continuous g ∧ ∫ s in (0 : ℝ)..T, ‖f s - g s‖ ≤ ε := by
  have hon : IntegrableOn f (Set.Ioc 0 T) volume :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hT).mp hf
  have hindicator : Integrable (Set.indicator (Set.Ioc 0 T) f) volume :=
    hon.integrable_indicator measurableSet_Ioc
  obtain ⟨g, _, hclose, hcontinuous, hintegrable⟩ :=
    Integrable.exists_hasCompactSupport_integral_sub_le hindicator hε
  refine ⟨g, hcontinuous, ?_⟩
  rw [intervalIntegral.integral_of_le hT]
  calc ∫ s in Set.Ioc 0 T, ‖f s - g s‖
      = ∫ s in Set.Ioc 0 T, ‖Set.indicator (Set.Ioc 0 T) f s - g s‖ := by
        refine setIntegral_congr_fun measurableSet_Ioc fun s hs ↦ ?_
        simp only [Set.indicator_of_mem hs]
    _ ≤ ∫ s, ‖Set.indicator (Set.Ioc 0 T) f s - g s‖ :=
        setIntegral_le_integral (hindicator.sub hintegrable).norm
          (ae_of_all _ fun _ ↦ norm_nonneg _)
    _ ≤ ε := hclose

end

end Descent.Portability.IntegrableGeneratorPropagator
