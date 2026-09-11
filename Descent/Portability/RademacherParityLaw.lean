/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.RademacherArrayWeakLimit
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

assert_below Descent.Decision Descent.Program

/-!
The product sign in a finite fair-sign row is balanced, and its mixed Fourier
transform with an infinitesimal weighted sum vanishes. This supplies the parity
independence calculation needed by the near-balanced HWE amplitude law.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.RademacherParityLaw

open scoped BigOperators Topology
open Filter HWEInteractionLaw BalancedHWEWeakLimit RademacherArrayWeakLimit

noncomputable def parity {ι : Type*} [Fintype ι] (x : ι → Bool) : ℝ :=
  ∏ i, signValue (x i)

theorem parity_square {ι : Type*} [Fintype ι] (x : ι → Bool) : parity x ^ 2 = 1 := by
  unfold parity
  rw [← Finset.prod_pow]
  have h (i : ι) : signValue (x i) ^ 2 = 1 := by cases x i <;> norm_num [signValue]
  simp only [h, Finset.prod_const_one]

/-- In every nonempty row the product sign has zero mean. -/
theorem parity_mean {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι] :
    (independentLaw (fun _ : ι ↦ signLaw)).expectation parity = 0 := by
  change (independentLaw (fun _ : ι ↦ signLaw)).expectation
    (fun x ↦ ∏ i, signValue (x i)) = _
  rw [expectation_independent_product (fun _ ↦ signLaw) (fun _ ↦ signValue)]
  have hs : signLaw.expectation signValue = 0 := by
    simpa only [one_mul] using sign_mean 1
  simp [hs]

/-- Exact mixed characteristic factor at one locus. -/
theorem mixed_sign_characteristic (a t : ℝ) :
    complexExpectation signLaw (fun b ↦ (signValue b : ℂ) *
      Complex.exp ((t * (a * signValue b) : ℝ) * Complex.I)) =
      Complex.I * (Real.sin (t * a) : ℂ) := by
  simp only [complexExpectation, Fintype.sum_bool, signLaw, signValue,
    Bool.false_eq_true, if_false, if_true, mul_one, mul_neg, Complex.ofReal_neg,
    Complex.ofReal_one, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  simp only [Real.cos_neg, Real.sin_neg, Complex.ofReal_neg]
  norm_num only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat]
  ring

/-- The actual mixed row transform is the product of its sine factors. -/
theorem mixed_characteristic {ι : Type*} [Fintype ι] [DecidableEq ι] (a : ι → ℝ) (t : ℝ) :
    complexExpectation (independentLaw (fun _ : ι ↦ signLaw)) (fun x ↦
      (parity x : ℂ) * Complex.exp ((t * weightedSum a x : ℝ) * Complex.I)) =
        ∏ i, (Complex.I * (Real.sin (t * a i) : ℂ)) := by
  simp only [parity, weightedSum, Finset.mul_sum, Complex.ofReal_sum,
    Finset.sum_mul, Complex.exp_sum, Complex.ofReal_prod, ← Finset.prod_mul_distrib]
  rw [complexExpectation_independent_product (fun _ ↦ signLaw)
    (fun i b ↦ (signValue b : ℂ) * Complex.exp ((t * (a i * signValue b) : ℝ) * Complex.I))]
  simp only [mixed_sign_characteristic]

/-- A uniformly small row has exponentially vanishing mixed parity transform. -/
theorem mixed_characteristic_limit (a : (m : ℕ) → Fin m → ℝ) (ε : ℕ → ℝ)
    (ha : ∀ m i, |a m i| ≤ ε m) (hε : Tendsto ε atTop (𝓝 0)) (t : ℝ) :
    Tendsto (fun m ↦ complexExpectation (independentLaw (fun _ : Fin m ↦ signLaw))
      (fun x ↦ (parity x : ℂ) * Complex.exp ((t * weightedSum (a m) x : ℝ) * Complex.I)))
      atTop (𝓝 0) := by
  simp_rw [mixed_characteristic]
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  have hsmall : ∀ᶠ m in atTop, |t| * ε m ≤ 1 / 2 := by
    have hh : Tendsto (fun m ↦ |t| * ε m) atTop (𝓝 0) := by
      simpa only [mul_zero] using hε.const_mul |t|
    exact (hh.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))).mono
      (fun _ h ↦ h.le)
  have hbound : ∀ᶠ m in atTop,
      ‖∏ i : Fin m, (Complex.I * (Real.sin (t * a m i) : ℂ))‖ ≤ (1 / 2 : ℝ) ^ m := by
    filter_upwards [hsmall] with m hm
    calc
      _ ≤ ∏ _i : Fin m, (1 / 2 : ℝ) := by
        rw [norm_prod]
        apply Finset.prod_le_prod (fun i _ ↦ norm_nonneg _)
        intro i _
        simp only [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
        have hsin := Real.abs_sin_le_abs (x := t * a m i)
        rw [abs_mul] at hsin
        exact hsin.trans ((mul_le_mul_of_nonneg_left (ha m i) (abs_nonneg t)).trans hm)
      _ = _ := by simp
  apply squeeze_zero' (Filter.Eventually.of_forall (fun _ ↦ norm_nonneg _)) hbound
  exact tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)

end Descent.Portability.RademacherParityLaw
