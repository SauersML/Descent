/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.PortabilityMasterTheorem

assert_below Descent.Decision Descent.Program

/-!
# What individual squared-error predictability measures

An outer expectation describes covariates and an inner expectation describes the
conditional residual law. All moments below are computed from that law. This
includes empirical finite cells, without identifying bin-level partial R² with
individual residual variance. The fourth-moment assumption in the Gaussian-style
specialization is explicit; it is not evidence about any particular cohort.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.IndividualLossMoments

open Foundations

noncomputable section

variable {D Ω : Type*}

/-- Integrate a conditional law over the covariate distribution. -/
def mixture (E : ExpFunctional D) (K : D → ExpFunctional Ω) : ExpFunctional (D × Ω) where
  eval f := E (fun d ↦ K d (fun ω ↦ f (d, ω)))
  add_eval f g := by
    change E (fun d ↦ K d ((fun ω ↦ f (d, ω)) + (fun ω ↦ g (d, ω)))) = _
    simp only [ExpFunctional.add_eval]
    exact E.add_eval _ _
  smul_eval c f := by
    change E (fun d ↦ K d (c • (fun ω ↦ f (d, ω)))) = _
    simp only [ExpFunctional.smul_eval]
    exact E.smul_eval _ _
  const_one := by simp
  nonneg_eval f hf := E.nonneg_eval _ (fun d ↦ (K d).nonneg_eval _ (fun ω ↦ hf (d, ω)))

/-- Total variance derived from the conditional law, for any observable. -/
theorem total_variance (E : ExpFunctional D) (K : D → ExpFunctional Ω)
    (f : D × Ω → ℝ) :
    variance (mixture E K) f =
      E (fun d ↦ variance (K d) (fun ω ↦ f (d, ω))) +
        variance E (fun d ↦ K d (fun ω ↦ f (d, ω))) := by
  simp only [variance_eq_expect_sq_sub_sq_mean]
  change E (fun d ↦ K d (fun ω ↦ f (d, ω) ^ 2)) -
      E (fun d ↦ K d (fun ω ↦ f (d, ω))) ^ 2 = _
  rw [show (fun d ↦ K d (fun ω ↦ f (d, ω) ^ 2) -
      K d (fun ω ↦ f (d, ω)) ^ 2) =
      (fun d ↦ K d (fun ω ↦ f (d, ω) ^ 2)) -
        (fun d ↦ K d (fun ω ↦ f (d, ω)) ^ 2) from rfl,
    E.eval_sub]
  ring

/-- The predictable squared loss includes a covariance between conditional
variance and squared conditional bias. Neither channel is determined by signed R². -/
theorem squared_loss_between_decomposition (E : ExpFunctional D)
    (K : D → ExpFunctional Ω) (r : D × Ω → ℝ) :
    variance E (fun d ↦ K d (fun ω ↦ r (d, ω) ^ 2)) =
      variance E (fun d ↦ variance (K d) (fun ω ↦ r (d, ω))) +
      variance E (fun d ↦ K d (fun ω ↦ r (d, ω)) ^ 2) +
      2 * covariance E (fun d ↦ variance (K d) (fun ω ↦ r (d, ω)))
        (fun d ↦ K d (fun ω ↦ r (d, ω)) ^ 2) := by
  have h : (fun d ↦ K d (fun ω ↦ r (d, ω) ^ 2)) =
      (fun d ↦ variance (K d) (fun ω ↦ r (d, ω))) +
        (fun d ↦ K d (fun ω ↦ r (d, ω)) ^ 2) := by
    funext d
    simp only [Pi.add_apply, variance_eq_expect_sq_sub_sq_mean, sub_add_cancel]
  rw [h]
  convert variance_add_exp E
    (fun d ↦ variance (K d) (fun ω ↦ r (d, ω)))
    (fun d ↦ K d (fun ω ↦ r (d, ω)) ^ 2) using 1
  ring

/-- The exact denominator of loss-R² requires conditional fourth moments. -/
theorem squared_loss_total (E : ExpFunctional D) (K : D → ExpFunctional Ω)
    (r : D × Ω → ℝ) :
    variance (mixture E K) (fun z ↦ r z ^ 2) =
      E (fun d ↦ K d (fun ω ↦ r (d, ω) ^ 4) -
        K d (fun ω ↦ r (d, ω) ^ 2) ^ 2) +
      variance E (fun d ↦ K d (fun ω ↦ r (d, ω) ^ 2)) := by
  rw [total_variance]
  simp only [variance_eq_expect_sq_sub_sq_mean, ← pow_mul]

private theorem expected_square_shift (E : ExpFunctional Ω) (f : Ω → ℝ) (c : ℝ) :
    E (fun ω ↦ (f ω - c) ^ 2) = variance E f + (E f - c) ^ 2 := by
  have h : (fun ω ↦ (f ω - c) ^ 2) =
      (fun ω ↦ f ω ^ 2) + (-2 * c) • f + (fun _ ↦ c ^ 2) := by
    funext ω
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [h, E.add_eval, E.add_eval, E.smul_eval, E.eval_const,
    variance_eq_expect_sq_sub_sq_mean]
  ring

/-- The excess risk of any distance-only loss predictor is its squared distance
from the conditional second moment. This derives the oracle property, rather
than assuming that a fitted spline attains it. -/
theorem squared_loss_risk_decomposition (E : ExpFunctional D)
    (K : D → ExpFunctional Ω) (r : D × Ω → ℝ) (g : D → ℝ) :
    mixture E K (fun z ↦ (r z ^ 2 - g z.1) ^ 2) =
      E (fun d ↦ variance (K d) (fun ω ↦ r (d, ω) ^ 2)) +
        E (fun d ↦ (K d (fun ω ↦ r (d, ω) ^ 2) - g d) ^ 2) := by
  change E (fun d ↦ K d (fun ω ↦ (r (d, ω) ^ 2 - g d) ^ 2)) = _
  simp only [expected_square_shift]
  exact E.add_eval _ _

/-- Population loss-R² of a fixed predictor equals the oracle fraction minus
an approximation penalty. Data-dependent fitting requires a separate evaluation
law; this theorem does not identify an in-sample spline R² with the oracle. -/
theorem fitted_squared_loss_r2_gap (E : ExpFunctional D)
    (K : D → ExpFunctional Ω) (r : D × Ω → ℝ) (g : D → ℝ)
    (hpos : 0 < variance (mixture E K) (fun z ↦ r z ^ 2)) :
    1 - mixture E K (fun z ↦ (r z ^ 2 - g z.1) ^ 2) /
        variance (mixture E K) (fun z ↦ r z ^ 2) =
      variance E (fun d ↦ K d (fun ω ↦ r (d, ω) ^ 2)) /
          variance (mixture E K) (fun z ↦ r z ^ 2) -
        E (fun d ↦ (K d (fun ω ↦ r (d, ω) ^ 2) - g d) ^ 2) /
          variance (mixture E K) (fun z ↦ r z ^ 2) := by
  rw [squared_loss_risk_decomposition]
  have ht := total_variance E K (fun z ↦ r z ^ 2)
  field_simp
  linarith

/-- An ideal distance-only predictor bounds the population R² of every such
fixed fitted predictor, with no Gaussian hypothesis. -/
theorem fitted_squared_loss_r2_le_oracle (E : ExpFunctional D)
    (K : D → ExpFunctional Ω) (r : D × Ω → ℝ) (g : D → ℝ)
    (hpos : 0 < variance (mixture E K) (fun z ↦ r z ^ 2)) :
    1 - mixture E K (fun z ↦ (r z ^ 2 - g z.1) ^ 2) /
        variance (mixture E K) (fun z ↦ r z ^ 2) ≤
      variance E (fun d ↦ K d (fun ω ↦ r (d, ω) ^ 2)) /
        variance (mixture E K) (fun z ↦ r z ^ 2) := by
  rw [fitted_squared_loss_r2_gap E K r g hpos]
  exact sub_le_self _ (div_nonneg
    (E.nonneg_eval _ (fun _ ↦ sq_nonneg _)) hpos.le)

/-- General conditional squared-loss noise, including skewness. Apply this
to each conditional law K d; no Gaussian or symmetry hypothesis is used. -/
theorem squared_loss_central_moments (E : ExpFunctional Ω) (r : Ω → ℝ) :
    variance E (fun ω ↦ r ω ^ 2) =
      E (fun ω ↦ (r ω - E r) ^ 4) - variance E r ^ 2 +
      4 * E r * E (fun ω ↦ (r ω - E r) ^ 3) +
      4 * (E r) ^ 2 * variance E r := by
  let b := E r
  let z := fun ω ↦ r ω - b
  have hz : E z = 0 := eval_centered_zero E r
  have hv : E (fun ω ↦ z ω ^ 2) = variance E r := rfl
  have hpoint : (fun ω ↦ r ω ^ 4) =
      (fun ω ↦ z ω ^ 4) + (4 * b) • (fun ω ↦ z ω ^ 3) +
      (6 * b ^ 2) • (fun ω ↦ z ω ^ 2) + (4 * b ^ 3) • z +
      (fun _ ↦ b ^ 4) := by
    funext ω
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    dsimp [z]
    ring
  have hfour : E (fun ω ↦ r ω ^ 4) =
      E (fun ω ↦ z ω ^ 4) + 4 * b * E (fun ω ↦ z ω ^ 3) +
        6 * b ^ 2 * variance E r + b ^ 4 := by
    rw [hpoint, E.add_eval, E.add_eval, E.add_eval, E.add_eval,
      E.smul_eval, E.smul_eval, E.smul_eval, E.eval_const, hz, hv]
    ring
  have hsecond := variance_eq_expect_sq_sub_sq_mean E r
  rw [variance_eq_expect_sq_sub_sq_mean]
  simp only [← pow_mul]
  rw [hfour]
  dsimp [z, b] at *
  nlinarith [sq_nonneg (variance E r)]

/-- The Gaussian-style expression follows from second and fourth moments alone.
The hypotheses must be checked for the residuals from the actual analysis. -/
theorem gaussian_style_loss_variance (E : ExpFunctional D) (K : D → ExpFunctional Ω)
    (r : D × Ω → ℝ) (v : D → ℝ)
    (hsecond : ∀ d, K d (fun ω ↦ r (d, ω) ^ 2) = v d)
    (hfourth : ∀ d, K d (fun ω ↦ r (d, ω) ^ 4) = 3 * v d ^ 2) :
    variance (mixture E K) (fun z ↦ r z ^ 2) =
      2 * (E v) ^ 2 + 3 * variance E v := by
  rw [squared_loss_total]
  simp only [hsecond, hfourth]
  have h : (fun d ↦ 3 * v d ^ 2 - v d ^ 2) = (2 : ℝ) • (fun d ↦ v d ^ 2) := by
    funext d
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  rw [h, E.smul_eval, variance_eq_expect_sq_sub_sq_mean]
  ring

/-- A positive mean second moment makes the CV formula well-defined. -/
theorem gaussian_style_explainable_fraction (E : ExpFunctional D)
    (K : D → ExpFunctional Ω) (r : D × Ω → ℝ) (v : D → ℝ)
    (hsecond : ∀ d, K d (fun ω ↦ r (d, ω) ^ 2) = v d)
    (hfourth : ∀ d, K d (fun ω ↦ r (d, ω) ^ 4) = 3 * v d ^ 2)
    (hmean : E v ≠ 0) :
    variance E (fun d ↦ K d (fun ω ↦ r (d, ω) ^ 2)) /
        variance (mixture E K) (fun z ↦ r z ^ 2) =
      (variance E v / (E v) ^ 2) / (2 + 3 * (variance E v / (E v) ^ 2)) := by
  simp only [hsecond, gaussian_style_loss_variance E K r v hsecond hfourth]
  field_simp

/-- Sharp squared-CV bound. Positivity of the interval endpoints is essential.
This corrects the equal-endpoint-mass bound in the exploratory script. -/
theorem sharp_interval_cv_squared (E : ExpFunctional D) (v : D → ℝ)
    (a b : ℝ) (ha : 0 < a) (hab : a ≤ b)
    (hv : ∀ d, a ≤ v d ∧ v d ≤ b) :
    variance E v / (E v) ^ 2 ≤ (b - a) ^ 2 / (4 * a * b) := by
  have hb : 0 < b := lt_of_lt_of_le ha hab
  have hm : a ≤ E v := by
    simpa using E.eval_mono (fun d ↦ (hv d).1)
  have hmpos : 0 < E v := lt_of_lt_of_le ha hm
  have hs : E (fun d ↦ v d ^ 2) ≤ (a + b) * E v - a * b := by
    have hp := E.eval_mono (f := fun d ↦ v d ^ 2)
      (g := fun d ↦ (a + b) * v d - a * b) (fun d ↦ by
        nlinarith [mul_nonneg (sub_nonneg.mpr (hv d).1) (sub_nonneg.mpr (hv d).2)])
    have he : (fun d ↦ (a + b) * v d - a * b) =
        (a + b) • v - (fun _ ↦ a * b) := rfl
    simpa only [he, E.eval_sub, E.smul_eval, E.eval_const] using hp
  rw [div_le_div_iff₀ (sq_pos_of_pos hmpos) (by positivity)]
  rw [variance_eq_expect_sq_sub_sq_mean]
  have hmul := mul_le_mul_of_nonneg_left hs (show 0 ≤ 4 * a * b by positivity)
  nlinarith [sq_nonneg ((a + b) * E v - 2 * a * b)]

/-- The maximizing endpoint probabilities are b/(a+b) and a/(a+b). -/
def extremalIntervalLaw (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) : ExpFunctional Bool :=
  weightedExp (fun d ↦ if d then a / (a + b) else b / (a + b))
    (by
      have hb : 0 < b := lt_of_lt_of_le ha hab
      intro d; cases d <;> dsimp <;> positivity)
    (by simp only [Fintype.sum_bool, Bool.false_eq_true, if_false, if_true]
        have : a + b ≠ 0 := ne_of_gt (by linarith)
        field_simp)

theorem sharp_interval_cv_attained (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) :
    variance (extremalIntervalLaw a b ha hab) (fun d ↦ if d then b else a) /
        (extremalIntervalLaw a b ha hab (fun d ↦ if d then b else a)) ^ 2 =
      (b - a) ^ 2 / (4 * a * b) := by
  have hb : 0 < b := lt_of_lt_of_le ha hab
  have hs : a + b ≠ 0 := ne_of_gt (by linarith)
  rw [variance_eq_expect_sq_sub_sq_mean]
  simp only [extremalIntervalLaw, weightedExp_apply, Fintype.sum_bool,
    Bool.false_eq_true, if_false, if_true]
  field_simp
  ring

/-- A centered bias with rare larger shifts: variance one, fourth moment four. -/
def sparseBiasLaw : ExpFunctional (Fin 3) :=
  weightedExp ![1 / 8, 3 / 4, 1 / 8]
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_three, Matrix.cons_val_two])

/-- Two actual probability laws with identical signed-bias variance have
different squared-bias variance. No function of that one variance can recover it. -/
theorem signed_variance_does_not_determine_squared_bias :
    ¬ ∃ f : ℝ → ℝ, ∀ (Ω : Type) (E : ExpFunctional Ω) (m : Ω → ℝ),
      E m = 0 → variance E (fun ω ↦ m ω ^ 2) = f (variance E m) := by
  rintro ⟨f, hf⟩
  have h₁ := hf (Fin 2) (uniformExp (Fin 2)) ![-1, 1] (by
    norm_num [uniformExp_apply, Fin.sum_univ_two])
  have h₂ := hf (Fin 3) sparseBiasLaw ![-2, 0, 2] (by
    norm_num [sparseBiasLaw, weightedExp_apply, Fin.sum_univ_three, Matrix.cons_val_two])
  norm_num [variance_eq_expect_sq_sub_sq_mean, uniformExp_apply,
    sparseBiasLaw, weightedExp_apply, Fin.sum_univ_two, Fin.sum_univ_three,
    Matrix.cons_val_two] at h₁ h₂
  linarith

end

end Descent.Portability.IndividualLossMoments
