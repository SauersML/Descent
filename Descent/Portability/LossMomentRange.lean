/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.IndividualLossMoments

assert_below Descent.Decision Descent.Program

/-!
# Sharp loss-predictability range at fixed conditional second moments

Every member has the same distance law, zero conditional residual mean, and
conditional variance 1 or 4. Varying only tail weight realizes every oracle
loss-R² in (0,1]. Thus there is neither a universal ceiling below one nor a
positive lower bound based on these second moments. All laws have finite support.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.LossMomentRange

open Foundations IndividualLossMoments

attribute [local simp] Matrix.cons_val_two Matrix.head_cons Matrix.tail_cons

noncomputable section

def tailLaw (s : ℝ) (hs : 1 ≤ s) : ExpFunctional (Fin 3) :=
  weightedExp ![1 / (2 * s), 1 - 1 / s, 1 / (2 * s)]
    (by
      have hpos : 0 < s := by linarith
      intro i
      fin_cases i
      · dsimp; positivity
      · dsimp
        exact sub_nonneg.mpr ((div_le_one hpos).mpr hs)
      · change 0 ≤ 1 / (2 * s)
        positivity)
    (by
      have hn : s ≠ 0 := by linarith
      norm_num [Fin.sum_univ_three]
      field_simp
      ring)

def residual (s : ℝ) (z : Bool × Fin 3) : ℝ :=
  (if z.1 then 2 else 1) * (![-Real.sqrt s, 0, Real.sqrt s] : Fin 3 → ℝ) z.2

def conditionalVariance : Bool → ℝ := fun d ↦ if d then 4 else 1

/-- Tail changes preserve the entire conditional first/second-moment functions. -/
theorem conditional_moments (s : ℝ) (hs : 1 ≤ s) (d : Bool) :
    tailLaw s hs (fun i ↦ residual s (d, i)) = 0 ∧
      tailLaw s hs (fun i ↦ residual s (d, i) ^ 2) = conditionalVariance d ∧
      tailLaw s hs (fun i ↦ residual s (d, i) ^ 4) = s * conditionalVariance d ^ 2 := by
  have hpos : 0 < s := by linarith
  have hsqrt := Real.sq_sqrt hpos.le
  have hfour : Real.sqrt s ^ 4 = s ^ 2 := by
    calc
      Real.sqrt s ^ 4 = (Real.sqrt s ^ 2) ^ 2 := by ring
      _ = s ^ 2 := by rw [hsqrt]
  cases d <;>
    norm_num [tailLaw, weightedExp_apply, residual, conditionalVariance,
      Fin.sum_univ_three, mul_pow, hsqrt, hfour]
  all_goals field_simp
  all_goals norm_num

def oracleFraction (s : ℝ) (hs : 1 ≤ s) : ℝ :=
  variance (uniformExp Bool) (fun d ↦ tailLaw s hs (fun i ↦ residual s (d, i) ^ 2)) /
    variance (mixture (uniformExp Bool) (fun _ ↦ tailLaw s hs)) (fun z ↦ residual s z ^ 2)

/-- Exact total loss variance; it is positive throughout the family. -/
theorem loss_variance (s : ℝ) (hs : 1 ≤ s) :
    variance (mixture (uniformExp Bool) (fun _ ↦ tailLaw s hs))
      (fun z ↦ residual s z ^ 2) = (34 * s - 25) / 4 := by
  rw [squared_loss_total]
  simp only [(conditional_moments s hs _).2.1, (conditional_moments s hs _).2.2]
  norm_num [variance_eq_expect_sq_sub_sq_mean, uniformExp_apply,
    Fintype.sum_bool, conditionalVariance]
  field_simp
  ring

theorem oracleFraction_eq (s : ℝ) (hs : 1 ≤ s) :
    oracleFraction s hs = 9 / (34 * s - 25) := by
  have hd : 34 * s - 25 ≠ 0 := by linarith
  unfold oracleFraction
  rw [loss_variance]
  simp only [(conditional_moments s hs _).2.1]
  have hn : variance (uniformExp Bool) conditionalVariance = 9 / 4 := by
    norm_num [variance_eq_expect_sq_sub_sq_mean, uniformExp_apply,
      Fintype.sum_bool, conditionalVariance]
  rw [hn]
  field_simp

/-- Every permissible tail parameter gives a strictly positive fraction at most one. -/
theorem oracleFraction_bounds (s : ℝ) (hs : 1 ≤ s) :
    0 < oracleFraction s hs ∧ oracleFraction s hs ≤ 1 := by
  rw [oracleFraction_eq]
  have hden : 0 < 34 * s - 25 := by linarith
  exact ⟨div_pos (by norm_num) hden, (div_le_one hden).mpr (by linarith)⟩

/-- Converse: the entire interval (0,1] is attained with the same conditional
mean and variance. In particular, squared error can be perfectly predictable
despite a conditionally unbiased, genuinely random signed residual. -/
theorem every_fraction_attained (q : ℝ) (hq : 0 < q) (hq1 : q ≤ 1) :
    ∃ (s : ℝ) (hs : 1 ≤ s), oracleFraction s hs = q := by
  let s := (9 / q + 25) / 34
  have hsq : 1 ≤ s := by
    have hdiv : 9 ≤ 9 / q := (le_div_iff₀ hq).mpr (by linarith)
    dsimp [s]
    linarith
  refine ⟨s, hsq, ?_⟩
  rw [oracleFraction_eq]
  dsimp [s]
  field_simp
  ring

/-- The identified range in this fixed-second-moment family is exactly (0,1]. -/
theorem sharp_range (q : ℝ) :
    (∃ (s : ℝ) (hs : 1 ≤ s), oracleFraction s hs = q) ↔ 0 < q ∧ q ≤ 1 := by
  constructor
  · rintro ⟨s, hs, rfl⟩
    exact oracleFraction_bounds s hs
  · rintro ⟨hq, hq1⟩
    exact every_fraction_attained q hq hq1

/-- The same bounds hold for every conditional residual law with these second
moments, not only for the tail family. Total loss variance is derived positive. -/
theorem all_compatible_laws_bounds {Ω : Type*} (K : Bool → ExpFunctional Ω)
    (r : Bool × Ω → ℝ)
    (hsecond : ∀ d, K d (fun ω ↦ r (d, ω) ^ 2) = conditionalVariance d) :
    0 < variance (mixture (uniformExp Bool) K) (fun z ↦ r z ^ 2) ∧
      0 < variance (uniformExp Bool) (fun d ↦ K d (fun ω ↦ r (d, ω) ^ 2)) /
        variance (mixture (uniformExp Bool) K) (fun z ↦ r z ^ 2) ∧
      variance (uniformExp Bool) (fun d ↦ K d (fun ω ↦ r (d, ω) ^ 2)) /
        variance (mixture (uniformExp Bool) K) (fun z ↦ r z ^ 2) ≤ 1 := by
  have hbetween : variance (uniformExp Bool) (fun d ↦ K d (fun ω ↦ r (d, ω) ^ 2)) =
      9 / 4 := by
    simp only [hsecond]
    norm_num [variance_eq_expect_sq_sub_sq_mean, uniformExp_apply,
      Fintype.sum_bool, conditionalVariance]
  have hwithin : 0 ≤ uniformExp Bool (fun d ↦ variance (K d) (fun ω ↦ r (d, ω) ^ 2)) :=
    (uniformExp Bool).nonneg_eval _ (fun d ↦ (K d).nonneg_eval _ (fun _ ↦ sq_nonneg _))
  have ht := total_variance (uniformExp Bool) K (fun z ↦ r z ^ 2)
  rw [hbetween] at ht ⊢
  have hpos : 0 < variance (mixture (uniformExp Bool) K) (fun z ↦ r z ^ 2) := by linarith
  exact ⟨hpos, div_pos (by norm_num) hpos, (div_le_one hpos).mpr (by linarith)⟩

/-- Full identification region over all three-state conditional laws with the
fixed zero means and variance function, not just over the chosen witness family. -/
theorem fixed_second_moments_identified_set (q : ℝ) :
    (∃ (K : Bool → ExpFunctional (Fin 3)) (r : Bool × Fin 3 → ℝ),
      (∀ d, K d (fun i ↦ r (d, i)) = 0) ∧
      (∀ d, K d (fun i ↦ r (d, i) ^ 2) = conditionalVariance d) ∧
      variance (uniformExp Bool) (fun d ↦ K d (fun i ↦ r (d, i) ^ 2)) /
        variance (mixture (uniformExp Bool) K) (fun z ↦ r z ^ 2) = q) ↔
      0 < q ∧ q ≤ 1 := by
  constructor
  · rintro ⟨K, r, _, hsecond, rfl⟩
    exact (all_compatible_laws_bounds K r hsecond).2
  · rintro ⟨hq, hq1⟩
    obtain ⟨s, hs, heq⟩ := every_fraction_attained q hq hq1
    exact ⟨fun _ ↦ tailLaw s hs, residual s,
      fun d ↦ (conditional_moments s hs d).1,
      fun d ↦ (conditional_moments s hs d).2.1, heq⟩

end

end Descent.Portability.LossMomentRange
