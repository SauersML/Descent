/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.SimultaneousRealization

assert_below Descent.Decision Descent.Program

/-!
# Prescribed residual moments, and the simultaneous source-fixed construction

UPT Theorem 7.1.  On one fixed pre-outcome law -- a distance cell law and a
conditionally symmetric `±1` score -- an arbitrary prescribed cellwise squared
correlation `q_d ∈ [0,1)`, an arbitrary prescribed cellwise mean squared error
`m_d > 1`, and an arbitrary prescribed loss-explainability `η ∈ (0,1]` are realized
simultaneously by a target outcome kernel.  The source law, the fitted source score and
the distance variable are untouched, and varying `η` changes neither the conditional
mean nor the conditional variance of the outcome given the entire genotype and
distance.

The construction needs a residual law with three prescribed numbers: a mean `b`, a
second moment `a > b²`, and a variance `δ ≥ 0` for the squared residual.  The first half
of this module builds one explicitly -- an independent sign of bias `b/M` times a
two-point magnitude -- and proves its three moments exactly.  That is the finite
instance of the moment-completion step UPT Theorem 7.1 cites, with no appeal to an
existence theorem.

Builds on `IndividualLossMoments.mixture`, `Portability.weightedExp`,
`SimultaneousRealization.shift_one`, `SimultaneousRealization.shift_sq`,
`AlignmentFactorization.scoreAccuracy`, `Foundations.expMse` and
`TraitPortabilityRange.sign`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.SourceFixedRealization

open Foundations IndividualLossMoments AlignmentFactorization SimultaneousRealization

open TraitPortabilityRange (sign)

noncomputable section

variable {D : Type*}

/-- The scored sign at `false`. -/
theorem sign_false : sign false = -1 := rfl

/-- The scored sign at `true`. -/
theorem sign_true : sign true = 1 := rfl

/-- A scored sign squares to one. -/
theorem sign_sq (s : Bool) : sign s ^ 2 = 1 := by
  cases s
  · rw [sign_false]
    norm_num
  · rw [sign_true]
    norm_num

/-- The fair-sign expectation in two-point form. -/
theorem uniformBool_eval (f : Bool → ℝ) :
    uniformExp Bool f = 1 / 2 * f false + 1 / 2 * f true := by
  norm_num [uniformExp_apply, Fintype.sum_bool]
  ring

/-! ### A residual law with a prescribed mean, second moment and loss variance -/

/-- The low magnitude square `ℓ₀ = (a + b²)/2`: strictly above `b²` and at most `a`. -/
def lowerSquare (a b : ℝ) : ℝ := (a + b ^ 2) / 2

/-- The gap parameter `κ = ((a − b²)/2)²`, the squared-loss variance the two-point
magnitude law produces at weight one half of the way. -/
def gapSquare (a b : ℝ) : ℝ := ((a - b ^ 2) / 2) ^ 2

/-- The weight of the high-magnitude atom, `κ/(κ + δ)`: it is `1` at `δ = 0`, where the
squared residual is deterministic, and tends to `0` as `δ` grows. -/
def highWeight (a b delta : ℝ) : ℝ := gapSquare a b / (gapSquare a b + delta)

/-- The high magnitude square, fixed by the prescribed second moment. -/
def upperSquare (a b delta : ℝ) : ℝ :=
  (a * (gapSquare a b + delta) - delta * lowerSquare a b) / gapSquare a b

/-- The gap parameter is positive exactly where the prescribed moments leave slack. -/
theorem gapSquare_pos (a b : ℝ) (hab : b ^ 2 < a) : 0 < gapSquare a b := by
  have hpos : 0 < (a - b ^ 2) / 2 := by linarith
  exact pow_pos hpos 2

/-- The high-magnitude weight is a positive probability. -/
theorem highWeight_pos (a b delta : ℝ) (hab : b ^ 2 < a) (hd : 0 ≤ delta) :
    0 < highWeight a b delta := by
  have hk := gapSquare_pos a b hab
  exact div_pos hk (by linarith)

/-- The high-magnitude weight is at most one. -/
theorem highWeight_le_one (a b delta : ℝ) (hab : b ^ 2 < a) (hd : 0 ≤ delta) :
    highWeight a b delta ≤ 1 := by
  have hk := gapSquare_pos a b hab
  unfold highWeight
  rw [div_le_one (by linarith)]
  linarith

/-- The low magnitude square exceeds the squared mean, which is what makes the sign bias
admissible. -/
theorem lowerSquare_lt (a b : ℝ) (hab : b ^ 2 < a) : b ^ 2 < lowerSquare a b := by
  unfold lowerSquare
  linarith

/-- The low magnitude square is at most the prescribed second moment. -/
theorem lowerSquare_le (a b : ℝ) (hab : b ^ 2 < a) : lowerSquare a b ≤ a := by
  unfold lowerSquare
  linarith

/-- The low magnitude square is nonnegative, so its square root is a magnitude. -/
theorem lowerSquare_nonneg (a b : ℝ) (hab : b ^ 2 < a) : 0 ≤ lowerSquare a b := by
  have hb := sq_nonneg b
  unfold lowerSquare
  linarith

/-- The high magnitude square is at least the prescribed second moment. -/
theorem upperSquare_ge (a b delta : ℝ) (hab : b ^ 2 < a) (hd : 0 ≤ delta) :
    a ≤ upperSquare a b delta := by
  have hk := gapSquare_pos a b hab
  unfold upperSquare
  rw [le_div_iff₀ hk]
  unfold lowerSquare
  nlinarith [mul_nonneg hd (le_of_lt (sub_pos.mpr hab))]

/-- The high magnitude square is nonnegative. -/
theorem upperSquare_nonneg (a b delta : ℝ) (hab : b ^ 2 < a) (hd : 0 ≤ delta) :
    0 ≤ upperSquare a b delta := by
  have hge := upperSquare_ge a b delta hab hd
  have hb := sq_nonneg b
  linarith

/-- **The two-point magnitude law has the prescribed second moment.** -/
theorem two_point_second_moment (a b delta : ℝ) (hab : b ^ 2 < a) (hd : 0 ≤ delta) :
    (1 - highWeight a b delta) * lowerSquare a b
      + highWeight a b delta * upperSquare a b delta = a := by
  have hk := gapSquare_pos a b hab
  have hkne : gapSquare a b ≠ 0 := ne_of_gt hk
  have hkd : gapSquare a b + delta ≠ 0 := by
    intro hcon
    linarith
  unfold highWeight upperSquare
  field_simp <;> ring

/-- **The two-point magnitude law has the prescribed squared-loss variance.**  Its
fourth moment is the second moment squared plus `δ`, exactly. -/
theorem two_point_fourth_moment (a b delta : ℝ) (hab : b ^ 2 < a) (hd : 0 ≤ delta) :
    (1 - highWeight a b delta) * lowerSquare a b ^ 2
      + highWeight a b delta * upperSquare a b delta ^ 2 = a ^ 2 + delta := by
  have hk := gapSquare_pos a b hab
  have hrel : gapSquare a b = (a - lowerSquare a b) ^ 2 := by
    unfold gapSquare lowerSquare
    ring
  have hkne : (a - lowerSquare a b) ^ 2 ≠ 0 := by
    rw [← hrel]
    exact ne_of_gt hk
  have hkd : (a - lowerSquare a b) ^ 2 + delta ≠ 0 := by
    rw [← hrel]
    intro hcon
    linarith
  unfold highWeight upperSquare
  rw [hrel]
  field_simp <;> ring

/-- The two-point magnitude weights. -/
def magnitudeWeights (w : ℝ) : Bool → ℝ
  | false => 1 - w
  | true => w

/-- The asymmetric sign weights. -/
def signWeights (theta : ℝ) : Bool → ℝ
  | false => (1 - theta) / 2
  | true => (1 + theta) / 2

/-- The two-point magnitude law on `Bool`. -/
def magnitudeLaw (w : ℝ) (h0 : 0 ≤ w) (h1 : w ≤ 1) : ExpFunctional Bool :=
  weightedExp (magnitudeWeights w)
    (by
      intro t
      cases t
      · show (0:ℝ) ≤ 1 - w
        linarith
      · show (0:ℝ) ≤ w
        linarith)
    (by
      simp [Fintype.sum_bool, magnitudeWeights] <;> ring)

/-- The asymmetric sign law with mean `theta`. -/
def signLaw (theta : ℝ) (h0 : -1 ≤ theta) (h1 : theta ≤ 1) : ExpFunctional Bool :=
  weightedExp (signWeights theta)
    (by
      intro t
      cases t
      · show (0:ℝ) ≤ (1 - theta) / 2
        linarith
      · show (0:ℝ) ≤ (1 + theta) / 2
        linarith)
    (by
      simp [Fintype.sum_bool, signWeights] <;> ring)

/-- The magnitude law in two-point form. -/
theorem magnitudeLaw_eval (w : ℝ) (h0 : 0 ≤ w) (h1 : w ≤ 1) (f : Bool → ℝ) :
    magnitudeLaw w h0 h1 f = (1 - w) * f false + w * f true := by
  simp [magnitudeLaw, weightedExp_apply, magnitudeWeights, Fintype.sum_bool] <;> ring

/-- The sign law in two-point form. -/
theorem signLaw_eval (theta : ℝ) (h0 : -1 ≤ theta) (h1 : theta ≤ 1) (f : Bool → ℝ) :
    signLaw theta h0 h1 f
      = (1 - theta) / 2 * f false + (1 + theta) / 2 * f true := by
  simp [signLaw, weightedExp_apply, signWeights, Fintype.sum_bool] <;> ring

/-- The two magnitudes of the prescribed-moment residual. -/
def magnitude (a b delta : ℝ) : Bool → ℝ
  | false => Real.sqrt (lowerSquare a b)
  | true => Real.sqrt (upperSquare a b delta)

/-- The low magnitude. -/
theorem magnitude_false (a b delta : ℝ) :
    magnitude a b delta false = Real.sqrt (lowerSquare a b) := rfl

/-- The high magnitude. -/
theorem magnitude_true (a b delta : ℝ) :
    magnitude a b delta true = Real.sqrt (upperSquare a b delta) := rfl

/-- The mean magnitude `M`, which the sign bias is divided by. -/
def meanMagnitude (a b delta : ℝ) : ℝ :=
  (1 - highWeight a b delta) * Real.sqrt (lowerSquare a b)
    + highWeight a b delta * Real.sqrt (upperSquare a b delta)

/-- The mean magnitude is at least the low magnitude, because the high one is larger. -/
theorem sqrt_lowerSquare_le_mean (a b delta : ℝ) (hab : b ^ 2 < a) (hd : 0 ≤ delta) :
    Real.sqrt (lowerSquare a b) ≤ meanMagnitude a b delta := by
  have hw0 := (highWeight_pos a b delta hab hd).le
  have hle : Real.sqrt (lowerSquare a b) ≤ Real.sqrt (upperSquare a b delta) :=
    Real.sqrt_le_sqrt (le_trans (lowerSquare_le a b hab) (upperSquare_ge a b delta hab hd))
  unfold meanMagnitude
  nlinarith [mul_nonneg hw0 (sub_nonneg.mpr hle)]

/-- The mean magnitude is positive. -/
theorem meanMagnitude_pos (a b delta : ℝ) (hab : b ^ 2 < a) (hd : 0 ≤ delta) :
    0 < meanMagnitude a b delta := by
  have hlow := sqrt_lowerSquare_le_mean a b delta hab hd
  have hb := sq_nonneg b
  have hpos : 0 < Real.sqrt (lowerSquare a b) := by
    refine Real.sqrt_pos.mpr ?_
    have := lowerSquare_lt a b hab
    linarith
  linarith

/-- **The prescribed mean is inside the magnitude budget.**  This is the inequality that
makes the construction possible at every prescribed loss variance, and it holds because
the bulk magnitude stays above `|b|` however far the spike is pushed out. -/
theorem abs_le_meanMagnitude (a b delta : ℝ) (hab : b ^ 2 < a) (hd : 0 ≤ delta) :
    |b| ≤ meanMagnitude a b delta := by
  have h1 : |b| = Real.sqrt (b ^ 2) := (Real.sqrt_sq_eq_abs b).symm
  have h2 : Real.sqrt (b ^ 2) ≤ Real.sqrt (lowerSquare a b) :=
    Real.sqrt_le_sqrt (lowerSquare_lt a b hab).le
  have h3 := sqrt_lowerSquare_le_mean a b delta hab hd
  rw [h1]
  linarith

/-- The sign bias `θ = b/M`. -/
def signBias (a b delta : ℝ) : ℝ := b / meanMagnitude a b delta

/-- The sign bias is an admissible sign-law parameter. -/
theorem signBias_bounds (a b delta : ℝ) (hab : b ^ 2 < a) (hd : 0 ≤ delta) :
    -1 ≤ signBias a b delta ∧ signBias a b delta ≤ 1 := by
  have hm := meanMagnitude_pos a b delta hab hd
  have habs := abs_le_meanMagnitude a b delta hab hd
  have hb := abs_le.mp habs
  unfold signBias
  refine ⟨?_, ?_⟩
  · rw [le_div_iff₀ hm]
    linarith [hb.1]
  · rw [div_le_one hm]
    exact hb.2

/-- **The residual law with prescribed mean `b`, second moment `a` and squared-residual
variance `δ`**: an independent sign of bias `b/M` times a two-point magnitude. -/
def residualLaw (a b delta : ℝ) (hab : b ^ 2 < a) (hd : 0 ≤ delta) :
    ExpFunctional (Bool × Bool) :=
  mixture
    (magnitudeLaw (highWeight a b delta) (highWeight_pos a b delta hab hd).le
      (highWeight_le_one a b delta hab hd))
    (fun _ ↦ signLaw (signBias a b delta) (signBias_bounds a b delta hab hd).1
      (signBias_bounds a b delta hab hd).2)

/-- The residual value: a magnitude times a sign. -/
def residualValue (a b delta : ℝ) : Bool × Bool → ℝ :=
  fun r ↦ magnitude a b delta r.1 * sign r.2

/-- The residual value at an explicit pair. -/
theorem residualValue_apply (a b delta : ℝ) (t s : Bool) :
    residualValue a b delta (t, s) = magnitude a b delta t * sign s := rfl

/-- A product mixture evaluated as an iterated expectation. -/
theorem mixture_eval {A B : Type*} (E : ExpFunctional A) (K : A → ExpFunctional B)
    (f : A × B → ℝ) : mixture E K f = E (fun x ↦ K x (fun y ↦ f (x, y))) := rfl

/-- The residual law in four-point form. -/
theorem residualLaw_eval (a b delta : ℝ) (hab : b ^ 2 < a) (hd : 0 ≤ delta)
    (f : Bool × Bool → ℝ) :
    residualLaw a b delta hab hd f
      = (1 - highWeight a b delta)
          * ((1 - signBias a b delta) / 2 * f (false, false)
            + (1 + signBias a b delta) / 2 * f (false, true))
        + highWeight a b delta
          * ((1 - signBias a b delta) / 2 * f (true, false)
            + (1 + signBias a b delta) / 2 * f (true, true)) := by
  unfold residualLaw
  rw [mixture_eval, magnitudeLaw_eval, signLaw_eval, signLaw_eval]

/-- **The residual has the prescribed mean.** -/
theorem residual_first_moment (a b delta : ℝ) (hab : b ^ 2 < a) (hd : 0 ≤ delta) :
    residualLaw a b delta hab hd (residualValue a b delta) = b := by
  have hm := meanMagnitude_pos a b delta hab hd
  have hstep : residualLaw a b delta hab hd (residualValue a b delta)
      = signBias a b delta * meanMagnitude a b delta := by
    rw [residualLaw_eval]
    unfold meanMagnitude
    simp only [residualValue_apply, magnitude_false, magnitude_true, sign_false, sign_true]
    ring
  rw [hstep]
  unfold signBias
  field_simp

/-- **The residual has the prescribed second moment.** -/
theorem residual_second_moment (a b delta : ℝ) (hab : b ^ 2 < a) (hd : 0 ≤ delta) :
    residualLaw a b delta hab hd (fun r ↦ residualValue a b delta r ^ 2) = a := by
  have h0 : Real.sqrt (lowerSquare a b) ^ 2 = lowerSquare a b :=
    Real.sq_sqrt (lowerSquare_nonneg a b hab)
  have h1 : Real.sqrt (upperSquare a b delta) ^ 2 = upperSquare a b delta :=
    Real.sq_sqrt (upperSquare_nonneg a b delta hab hd)
  have hstep : residualLaw a b delta hab hd (fun r ↦ residualValue a b delta r ^ 2)
      = (1 - highWeight a b delta) * lowerSquare a b
        + highWeight a b delta * upperSquare a b delta := by
    rw [residualLaw_eval]
    simp only [residualValue_apply, magnitude_false, magnitude_true, sign_false, sign_true]
    linear_combination (1 - highWeight a b delta) * h0 + highWeight a b delta * h1
  rw [hstep, two_point_second_moment a b delta hab hd]

/-- **The squared residual has the prescribed variance.**  Its fourth moment is `a² + δ`,
so the variance of the individual loss it carries is exactly `δ`. -/
theorem residual_fourth_moment (a b delta : ℝ) (hab : b ^ 2 < a) (hd : 0 ≤ delta) :
    residualLaw a b delta hab hd (fun r ↦ residualValue a b delta r ^ 4)
      = a ^ 2 + delta := by
  have h0 : Real.sqrt (lowerSquare a b) ^ 2 = lowerSquare a b :=
    Real.sq_sqrt (lowerSquare_nonneg a b hab)
  have h1 : Real.sqrt (upperSquare a b delta) ^ 2 = upperSquare a b delta :=
    Real.sq_sqrt (upperSquare_nonneg a b delta hab hd)
  have hstep : residualLaw a b delta hab hd (fun r ↦ residualValue a b delta r ^ 4)
      = (1 - highWeight a b delta) * lowerSquare a b ^ 2
        + highWeight a b delta * upperSquare a b delta ^ 2 := by
    rw [residualLaw_eval]
    simp only [residualValue_apply, magnitude_false, magnitude_true, sign_false, sign_true]
    linear_combination
      ((1 - highWeight a b delta) * (Real.sqrt (lowerSquare a b) ^ 2 + lowerSquare a b))
          * h0
        + (highWeight a b delta
            * (Real.sqrt (upperSquare a b delta) ^ 2 + upperSquare a b delta)) * h1
  rw [hstep, two_point_fourth_moment a b delta hab hd]

end

end Descent.Portability.SourceFixedRealization
