/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.IndividualLossMoments

assert_below Descent.Decision Descent.Program

/-!
# The Gaussian ceiling is a specialization, not a universal theorem

TQ Proposition 2.7, completing what `IndividualLossMoments` already proves. The
squared coefficient of variation bound `sharp_interval_cv_squared` is composed
with the increasing map `x ↦ x / (2 + 3x)` to give the boxed bound (2.19) on the
explainable fraction itself, and that bound is shown to be attained: the
maximizing two-valued variance profile `extremalIntervalLaw` is paired with an
explicit three-point conditional law `gaussianMomentLaw` whose second and fourth
moments are exactly `v` and `3v²`. The last theorem shows the ceiling is a
Gaussian artefact: with a fair-sign multiplier the realized loss is a
deterministic function of the covariate and the fraction is exactly one, so no
distribution-free ceiling below one exists.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.GaussianCeilingBound

open Foundations IndividualLossMoments

attribute [local simp] Matrix.cons_val_two Matrix.head_cons Matrix.tail_cons

noncomputable section

variable {D Ω : Type*}

/-- The map carrying a squared coefficient of variation to the Gaussian-style
explainable fraction is increasing on the nonnegative reals, and composing it
with the interval bound gives TQ (2.19) directly. -/
theorem cv_ratio_le_interval (x lo hi : ℝ) (hlo : 0 < lo) (hlohi : lo ≤ hi)
    (hx : 0 ≤ x) (hxle : x ≤ (hi - lo) ^ 2 / (4 * lo * hi)) :
    x / (2 + 3 * x) ≤ (hi - lo) ^ 2 / (8 * lo * hi + 3 * (hi - lo) ^ 2) := by
  have hhi : 0 < hi := lt_of_lt_of_le hlo hlohi
  have h4 : (0 : ℝ) < 4 * lo * hi := by nlinarith
  have h8 : (0 : ℝ) < 8 * lo * hi + 3 * (hi - lo) ^ 2 := by
    nlinarith [sq_nonneg (hi - lo)]
  have h2 : (0 : ℝ) < 2 + 3 * x := by linarith
  have hxq : x * (4 * lo * hi) ≤ (hi - lo) ^ 2 := (le_div_iff₀ h4).mp hxle
  rw [div_le_div_iff₀ h2 h8]
  nlinarith [hxq]

/-- The closed form of the extremal ratio in TQ (2.19). -/
theorem interval_ratio_eq (lo hi : ℝ) (hlo : 0 < lo) (hlohi : lo ≤ hi) :
    (hi - lo) ^ 2 / (4 * lo * hi) / (2 + 3 * ((hi - lo) ^ 2 / (4 * lo * hi)))
      = (hi - lo) ^ 2 / (8 * lo * hi + 3 * (hi - lo) ^ 2) := by
  have hhi : 0 < hi := lt_of_lt_of_le hlo hlohi
  have h4 : (0 : ℝ) < 4 * lo * hi := by nlinarith
  have h4ne : (4 : ℝ) * lo * hi ≠ 0 := ne_of_gt h4
  have hstep : (2 : ℝ) + 3 * ((hi - lo) ^ 2 / (4 * lo * hi))
      = (8 * lo * hi + 3 * (hi - lo) ^ 2) / (4 * lo * hi) := by
    field_simp
    try ring
  rw [hstep, div_div_eq_mul_div, div_mul_eq_mul_div, mul_div_assoc, div_self h4ne,
    mul_one]

/-- TQ (2.19): the sharp bound on the Gaussian-style explainable fraction when
the conditional variance profile is confined to a positive interval. -/
theorem gaussian_fraction_interval_bound (E : ExpFunctional D)
    (K : D → ExpFunctional Ω) (r : D × Ω → ℝ) (v : D → ℝ) (lo hi : ℝ)
    (hlo : 0 < lo) (hlohi : lo ≤ hi) (hv : ∀ d, lo ≤ v d ∧ v d ≤ hi)
    (hsecond : ∀ d, K d (fun ω ↦ r (d, ω) ^ 2) = v d)
    (hfourth : ∀ d, K d (fun ω ↦ r (d, ω) ^ 4) = 3 * v d ^ 2)
    (hmean : E v ≠ 0) :
    variance E (fun d ↦ K d (fun ω ↦ r (d, ω) ^ 2))
        / variance (mixture E K) (fun z ↦ r z ^ 2)
      ≤ (hi - lo) ^ 2 / (8 * lo * hi + 3 * (hi - lo) ^ 2) := by
  rw [gaussian_style_explainable_fraction E K r v hsecond hfourth hmean]
  exact cv_ratio_le_interval (variance E v / (E v) ^ 2) lo hi hlo hlohi
    (div_nonneg (E.nonneg_eval _ (fun _ ↦ sq_nonneg _)) (sq_nonneg _))
    (sharp_interval_cv_squared E v lo hi hlo hlohi hv)

/-- A three-point conditional law realizing the Gaussian second-to-fourth moment
ratio exactly, for every nonnegative conditional variance. -/
def gaussianMomentLaw : ExpFunctional (Fin 3) :=
  weightedExp ![1 / 6, 2 / 3, 1 / 6]
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_three])

/-- Its support values at scale `s`, namely `{-s, 0, s}`. -/
def gaussianMomentValue (s : ℝ) : Fin 3 → ℝ := ![-s, 0, s]

/-- The raw second and fourth moments of the three-point law at scale `s`. -/
theorem gaussianMomentLaw_raw_moments (s : ℝ) :
    gaussianMomentLaw (fun i ↦ gaussianMomentValue s i ^ 2) = s ^ 2 / 3 ∧
      gaussianMomentLaw (fun i ↦ gaussianMomentValue s i ^ 4) = s ^ 4 / 3 := by
  constructor
  · norm_num [gaussianMomentLaw, gaussianMomentValue, weightedExp_apply,
      Fin.sum_univ_three]
    all_goals ring
  · norm_num [gaussianMomentLaw, gaussianMomentValue, weightedExp_apply,
      Fin.sum_univ_three]
    all_goals ring

/-- The scale matching a centred Gaussian of conditional variance `v`. -/
def gaussianMomentScale (v : ℝ) : ℝ := Real.sqrt (3 * v)

/-- The three-point law has second moment `v` and fourth moment `3v²`, so it is
indistinguishable from a centred Gaussian at these two moments. -/
theorem gaussianMomentLaw_moments (v : ℝ) (hv : 0 ≤ v) :
    gaussianMomentLaw
        (fun i ↦ gaussianMomentValue (gaussianMomentScale v) i ^ 2) = v ∧
      gaussianMomentLaw
        (fun i ↦ gaussianMomentValue (gaussianMomentScale v) i ^ 4) = 3 * v ^ 2 := by
  have hs : gaussianMomentScale v ^ 2 = 3 * v := Real.sq_sqrt (by linarith)
  have hs4 : gaussianMomentScale v ^ 4 = 9 * v ^ 2 := by
    have hx : gaussianMomentScale v ^ 4 = (gaussianMomentScale v ^ 2) ^ 2 := by ring
    rw [hx, hs]
    ring
  obtain ⟨h2, h4⟩ := gaussianMomentLaw_raw_moments (gaussianMomentScale v)
  refine ⟨?_, ?_⟩
  · rw [h2, hs]
    ring
  · rw [h4, hs4]
    ring

/-- The mean of the maximizing two-valued variance profile. -/
theorem extremalIntervalLaw_mean (lo hi : ℝ) (hlo : 0 < lo) (hlohi : lo ≤ hi) :
    extremalIntervalLaw lo hi hlo hlohi (fun d ↦ if d then hi else lo)
      = 2 * lo * hi / (lo + hi) := by
  have hs : lo + hi ≠ 0 := ne_of_gt (by linarith)
  simp only [extremalIntervalLaw, weightedExp_apply, Fintype.sum_bool,
    Bool.false_eq_true, if_false, if_true]
  field_simp
  try ring

/-- TQ (2.19) is attained: the maximizing two-valued variance profile paired
with the explicit three-point conditional law realizes the bound exactly. -/
theorem gaussian_fraction_interval_attained (lo hi : ℝ) (hlo : 0 < lo)
    (hlohi : lo ≤ hi) :
    variance (extremalIntervalLaw lo hi hlo hlohi)
          (fun d ↦ gaussianMomentLaw
            (fun i ↦ gaussianMomentValue (gaussianMomentScale (if d then hi else lo)) i ^ 2))
        / variance (mixture (extremalIntervalLaw lo hi hlo hlohi)
            (fun _ ↦ gaussianMomentLaw))
          (fun z ↦ gaussianMomentValue (gaussianMomentScale (if z.1 then hi else lo)) z.2 ^ 2)
      = (hi - lo) ^ 2 / (8 * lo * hi + 3 * (hi - lo) ^ 2) := by
  have hhi : 0 < hi := lt_of_lt_of_le hlo hlohi
  have hvnn : ∀ d : Bool, (0 : ℝ) ≤ if d then hi else lo := by
    intro d
    cases d <;> norm_num <;> linarith
  have hsecond : ∀ d : Bool, gaussianMomentLaw
      (fun i ↦ gaussianMomentValue (gaussianMomentScale (if d then hi else lo)) i ^ 2)
      = if d then hi else lo := fun d ↦ (gaussianMomentLaw_moments _ (hvnn d)).1
  have hfourth : ∀ d : Bool, gaussianMomentLaw
      (fun i ↦ gaussianMomentValue (gaussianMomentScale (if d then hi else lo)) i ^ 4)
      = 3 * (if d then hi else lo) ^ 2 :=
    fun d ↦ (gaussianMomentLaw_moments _ (hvnn d)).2
  have hmean : extremalIntervalLaw lo hi hlo hlohi
      (fun d ↦ if d then hi else lo) ≠ 0 := by
    rw [extremalIntervalLaw_mean lo hi hlo hlohi]
    exact ne_of_gt (div_pos (by nlinarith) (by linarith))
  have hfrac := gaussian_style_explainable_fraction
    (extremalIntervalLaw lo hi hlo hlohi) (fun _ ↦ gaussianMomentLaw)
    (fun z ↦ gaussianMomentValue (gaussianMomentScale (if z.1 then hi else lo)) z.2)
    (fun d ↦ if d then hi else lo) hsecond hfourth hmean
  rw [sharp_interval_cv_attained lo hi hlo hlohi,
    interval_ratio_eq lo hi hlo hlohi] at hfrac
  exact hfrac

/-- The fair-sign residual `√v(D)·U`, the non-Gaussian contrast of TQ §2.5. -/
def signedResidual (v : D → ℝ) (z : D × Bool) : ℝ :=
  Real.sqrt (v z.1) * (if z.2 then 1 else -1)

/-- Its realized loss is exactly the conditional variance profile. -/
theorem signedResidual_sq (v : D → ℝ) (hv : ∀ d, 0 ≤ v d) (d : D) (x : Bool) :
    signedResidual v (d, x) ^ 2 = v d := by
  have hs : ((if x then (1 : ℝ) else -1)) ^ 2 = 1 := by
    cases x <;> norm_num
  show (Real.sqrt (v d) * (if x then (1 : ℝ) else -1)) ^ 2 = v d
  rw [mul_pow, Real.sq_sqrt (hv d), hs, mul_one]

/-- There is no distribution-free ceiling below one. With a fair-sign multiplier
the realized loss is a deterministic function of the covariate, so the same
conditional second moments that give the Gaussian ceiling give fraction one. -/
theorem signed_fraction_one (E : ExpFunctional D) (v : D → ℝ) (hv : ∀ d, 0 ≤ v d)
    (hvar : variance E v ≠ 0) :
    variance E (fun d ↦ uniformExp Bool (fun x ↦ signedResidual v (d, x) ^ 2))
        / variance (mixture E (fun _ ↦ uniformExp Bool))
          (fun z ↦ signedResidual v z ^ 2) = 1 := by
  have hcell : ∀ d : D, (fun x ↦ signedResidual v (d, x) ^ 2)
      = fun _ : Bool ↦ v d := by
    intro d
    funext x
    exact signedResidual_sq v hv d x
  have hnum : (fun d ↦ uniformExp Bool (fun x ↦ signedResidual v (d, x) ^ 2))
      = v := by
    funext d
    rw [hcell d, ExpFunctional.eval_const]
  have hzero : (fun d ↦ variance (uniformExp Bool)
      (fun x ↦ signedResidual v (d, x) ^ 2)) = fun _ : D ↦ (0 : ℝ) := by
    funext d
    rw [hcell d]
    simp only [variance_eq_expect_sq_sub_sq_mean, ExpFunctional.eval_const]
    ring
  have htot : variance (mixture E (fun _ ↦ uniformExp Bool))
      (fun z ↦ signedResidual v z ^ 2) = variance E v := by
    rw [total_variance E (fun _ ↦ uniformExp Bool)
      (fun z ↦ signedResidual v z ^ 2)]
    show E (fun d ↦ variance (uniformExp Bool)
          (fun x ↦ signedResidual v (d, x) ^ 2))
        + variance E (fun d ↦ uniformExp Bool
          (fun x ↦ signedResidual v (d, x) ^ 2)) = variance E v
    rw [hzero, hnum, ExpFunctional.eval_const]
    ring
  rw [hnum, htot, div_self hvar]

end

end Descent.Portability.GaussianCeilingBound
