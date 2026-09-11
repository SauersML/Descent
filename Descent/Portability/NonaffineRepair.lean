/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.IndividualLossMoments

assert_below Descent.Decision Descent.Program

/-!
# Affine repair is not all possible repair

TQ Proposition 4.2. The conditioning variable of a `mixture` is the score, so a
function of the score is a function of the outer coordinate.
`conditional_mean_decomposition` is the exact orthogonality identity: the squared
error of any such function splits into the conditional-variance floor and the
squared distance from the conditional mean. Hence the floor is a lower bound
(`conditional_variance_is_minimum`), is attained by the conditional mean
(`conditional_mean_attains`), and equality holds exactly when the competing
function matches the conditional mean in mean square
(`equality_iff_conditional_mean_matches`). Specialising to affine functions of a
score gives the manuscript's inequality against the best affine recalibration,
`conditional_variance_le_best_affine`, with `best_affine_residual` identifying
that value as the manuscript's `v(1 - q)`. The gap is strict: the symmetric
three-point score with outcome its own square has zero squared correlation, so
every affine recalibration leaves the whole outcome variance, while the square of
the score predicts it exactly.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.NonaffineRepair

open Foundations IndividualLossMoments

attribute [local simp] Matrix.cons_val_two

noncomputable section

variable {D Ω : Type*}

/-- The squared error of a constant predictor is the variance plus the squared
offset from the mean. -/
theorem constant_predictor_mse (F : ExpFunctional Ω) (Y : Ω → ℝ) (c : ℝ) :
    expMse F Y (fun _ ↦ c) = variance F Y + (c - F Y) ^ 2 := by
  have hv : variance F (fun _ : Ω ↦ c) = 0 := by
    rw [variance_eq_expect_sq_sub_sq_mean, F.eval_const, F.eval_const]
    ring
  have hmul : (fun ω : Ω ↦ Y ω * c) = c • Y := by
    funext ω
    show Y ω * c = c * Y ω
    ring
  have hc : covariance F Y (fun _ : Ω ↦ c) = 0 := by
    rw [covariance_eq_expect_mul_sub_means, hmul, F.smul_eval, F.eval_const]
    ring
  rw [mse_eq_variance_add_variance_sub_two_cov_add_bias_sq, hv, hc]
  unfold bias
  rw [F.eval_const]
  ring

/-- **TQ Proposition 4.2, orthogonality.** The squared error of any function of
the score splits exactly into the conditional-variance floor and the mean squared
distance from the conditional mean. -/
theorem conditional_mean_decomposition (E : ExpFunctional D) (K : D → ExpFunctional Ω)
    (Y : D × Ω → ℝ) (g : D → ℝ) :
    expMse (mixture E K) Y (fun z ↦ g z.1) =
      E (fun d ↦ variance (K d) (fun ω ↦ Y (d, ω))) +
        E (fun d ↦ (g d - K d (fun ω ↦ Y (d, ω))) ^ 2) := by
  have hpt : ∀ d : D, K d (fun ω ↦ (Y (d, ω) - g d) ^ 2) =
      variance (K d) (fun ω ↦ Y (d, ω)) + (g d - K d (fun ω ↦ Y (d, ω))) ^ 2 :=
    fun d ↦ constant_predictor_mse (K d) (fun ω ↦ Y (d, ω)) (g d)
  show E (fun d ↦ K d (fun ω ↦ (Y (d, ω) - g d) ^ 2)) = _
  rw [funext hpt]
  exact E.add_eval _ _

/-- **TQ equation (4.3), lower bound.** No function of the score beats the
conditional-variance floor. -/
theorem conditional_variance_is_minimum (E : ExpFunctional D) (K : D → ExpFunctional Ω)
    (Y : D × Ω → ℝ) (g : D → ℝ) :
    E (fun d ↦ variance (K d) (fun ω ↦ Y (d, ω))) ≤
      expMse (mixture E K) Y (fun z ↦ g z.1) := by
  rw [conditional_mean_decomposition E K Y g]
  have h : 0 ≤ E (fun d ↦ (g d - K d (fun ω ↦ Y (d, ω))) ^ 2) :=
    E.nonneg_eval _ fun d ↦ sq_nonneg _
  linarith

/-- **TQ equation (4.3), attainment.** The conditional mean achieves the floor,
so the infimum over functions of the score is a minimum. -/
theorem conditional_mean_attains (E : ExpFunctional D) (K : D → ExpFunctional Ω)
    (Y : D × Ω → ℝ) :
    expMse (mixture E K) Y (fun z ↦ K z.1 (fun ω ↦ Y (z.1, ω))) =
      E (fun d ↦ variance (K d) (fun ω ↦ Y (d, ω))) := by
  rw [conditional_mean_decomposition E K Y (fun d ↦ K d (fun ω ↦ Y (d, ω)))]
  have hzero : (fun d ↦ (K d (fun ω ↦ Y (d, ω)) - K d (fun ω ↦ Y (d, ω))) ^ 2) =
      fun _ : D ↦ (0 : ℝ) := by
    funext d
    ring
  rw [hzero, E.eval_const]
  ring

/-- **TQ Proposition 4.2, equality case.** A competing function of the score
achieves the floor exactly when it matches the conditional mean in mean square,
which is the manuscript's almost-sure equality condition. -/
theorem equality_iff_conditional_mean_matches (E : ExpFunctional D)
    (K : D → ExpFunctional Ω) (Y : D × Ω → ℝ) (g : D → ℝ) :
    expMse (mixture E K) Y (fun z ↦ g z.1) =
        E (fun d ↦ variance (K d) (fun ω ↦ Y (d, ω))) ↔
      E (fun d ↦ (g d - K d (fun ω ↦ Y (d, ω))) ^ 2) = 0 := by
  rw [conditional_mean_decomposition E K Y g]
  constructor <;> intro h <;> linarith

/-- The exact squared error of an arbitrary affine recalibration of a score. -/
theorem affine_repair_mse (F : ExpFunctional Ω) (Y X : Ω → ℝ) (a b : ℝ) :
    expMse F Y (fun ω ↦ a + b * X ω) =
      variance F Y + b ^ 2 * variance F X - 2 * b * covariance F Y X +
        (a + b * F X - F Y) ^ 2 := by
  rw [mse_eq_variance_add_variance_sub_two_cov_add_bias_sq, variance_affine,
    covariance_affine_right]
  unfold bias
  rw [eval_affine]
  ring

/-- The best affine recalibration leaves exactly the manuscript's residual. -/
theorem best_affine_residual (F : ExpFunctional Ω) (Y X : Ω → ℝ)
    (hu : variance F X ≠ 0) :
    expMse F Y (fun ω ↦ (F Y - covariance F Y X / variance F X * F X) +
        covariance F Y X / variance F X * X ω) =
      variance F Y - covariance F Y X ^ 2 / variance F X := by
  rw [affine_repair_mse]
  field_simp
  try ring

/-- The residual of the best affine recalibration in the manuscript's form
`v (1 - q)`, with `q` the squared correlation. -/
theorem best_affine_residual_eq_variance_scaled (F : ExpFunctional Ω) (Y X : Ω → ℝ)
    (hu : variance F X ≠ 0) (hv : variance F Y ≠ 0) :
    variance F Y - covariance F Y X ^ 2 / variance F X =
      variance F Y *
        (1 - covariance F Y X ^ 2 / (variance F X * variance F Y)) := by
  field_simp
  try ring

/-- **TQ equation (4.3).** The conditional-variance floor is below the residual
left by the best affine recalibration of any score, because that recalibration is
one particular function of the score. -/
theorem conditional_variance_le_best_affine (E : ExpFunctional D)
    (K : D → ExpFunctional Ω) (Y : D × Ω → ℝ) (s : D → ℝ)
    (hu : variance (mixture E K) (fun z ↦ s z.1) ≠ 0) :
    E (fun d ↦ variance (K d) (fun ω ↦ Y (d, ω))) ≤
      variance (mixture E K) Y -
        covariance (mixture E K) Y (fun z ↦ s z.1) ^ 2 /
          variance (mixture E K) (fun z ↦ s z.1) := by
  rw [← best_affine_residual (mixture E K) Y (fun z ↦ s z.1) hu]
  exact conditional_variance_is_minimum E K Y
    (fun d ↦ (mixture E K Y - covariance (mixture E K) Y (fun z ↦ s z.1) /
        variance (mixture E K) (fun z ↦ s z.1) * mixture E K (fun z ↦ s z.1)) +
      covariance (mixture E K) Y (fun z ↦ s z.1) /
        variance (mixture E K) (fun z ↦ s z.1) * s d)

/-- The symmetric three-point score of the manuscript's example. -/
def rademacherScore : Fin 3 → ℝ := ![-1, 0, 1]

/-- The outcome is the square of the score: perfectly predictable, but not
linearly. -/
def rademacherOutcome : Fin 3 → ℝ := fun i ↦ rademacherScore i ^ 2

/-- **TQ Proposition 4.2, the strict example.** On the symmetric three-point
score the squared correlation with the outcome is zero, so every affine
recalibration leaves the entire outcome variance `2/9`, while the square of the
score predicts the outcome exactly. The affine-optimal residual is therefore not
a universal irreducible prediction error. -/
theorem square_of_symmetric_score_beats_every_affine :
    covariance (uniformExp (Fin 3)) rademacherOutcome rademacherScore = 0 ∧
      variance (uniformExp (Fin 3)) rademacherScore = 2 / 3 ∧
      variance (uniformExp (Fin 3)) rademacherOutcome = 2 / 9 ∧
      (∀ a b : ℝ, 2 / 9 ≤ expMse (uniformExp (Fin 3)) rademacherOutcome
          (fun i ↦ a + b * rademacherScore i)) ∧
      expMse (uniformExp (Fin 3)) rademacherOutcome rademacherOutcome = 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · norm_num [covariance, uniformExp_apply, Fin.sum_univ_three, rademacherOutcome,
      rademacherScore]
  · norm_num [variance, uniformExp_apply, Fin.sum_univ_three, rademacherScore]
  · norm_num [variance, uniformExp_apply, Fin.sum_univ_three, rademacherOutcome,
      rademacherScore]
  · intro a b
    have hcalc : expMse (uniformExp (Fin 3)) rademacherOutcome
        (fun i ↦ a + b * rademacherScore i) =
        (3 : ℝ)⁻¹ * ((1 - (a + b * (-1))) ^ 2 + (0 - (a + b * 0)) ^ 2 +
          (1 - (a + b * 1)) ^ 2) := by
      norm_num [expMse, uniformExp_apply, Fin.sum_univ_three, rademacherOutcome,
        rademacherScore]
      try ring
    rw [hcalc]
    nlinarith [sq_nonneg (a - 2 / 3), sq_nonneg b]
  · norm_num [expMse, uniformExp_apply, Fin.sum_univ_three]

end

end Descent.Portability.NonaffineRepair
