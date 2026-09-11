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
  have hwne : highWeight a b delta ≠ 0 := ne_of_gt (highWeight_pos a b delta hab hd)
  have hTne : gapSquare a b + delta ≠ 0 := by
    intro hcon
    linarith
  have hgap : gapSquare a b = (a - lowerSquare a b) ^ 2 := by
    unfold gapSquare lowerSquare
    ring
  have hmean := two_point_second_moment a b delta hab hd
  have hdiff : highWeight a b delta * (upperSquare a b delta - lowerSquare a b)
      = a - lowerSquare a b := by
    linear_combination hmean
  have hratio : (1 - highWeight a b delta) * gapSquare a b
      = highWeight a b delta * delta := by
    unfold highWeight
    field_simp <;> ring
  have hvar : highWeight a b delta * (1 - highWeight a b delta)
      * (upperSquare a b delta - lowerSquare a b) ^ 2 = delta := by
    apply mul_left_cancel₀ hwne
    linear_combination
      ((1 - highWeight a b delta)
          * (highWeight a b delta * (upperSquare a b delta - lowerSquare a b)
            + (a - lowerSquare a b))) * hdiff
        - (1 - highWeight a b delta) * hgap + hratio
  linear_combination
    (((1 - highWeight a b delta) * lowerSquare a b
        + highWeight a b delta * upperSquare a b delta) + a) * hmean + hvar

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
      simp [magnitudeWeights] <;> ring)

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
      simp [signWeights] <;> ring)

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

/-! ### The simultaneous source-fixed construction -/

/-- A genotype observable read at an explicit pair. -/
theorem liftGenotype_apply {A B : Type*} (S : A → ℝ) (x : A) (y : B) :
    liftGenotype (Ω := B) S (x, y) = S x := rfl

/-- `x_d = √q_d + √(m_d − 1 + q_d)`, UPT equation (7.2). -/
def scaleX (q m : D → ℝ) (d : D) : ℝ := Real.sqrt (q d) + Real.sqrt (m d - 1 + q d)

/-- `v_d = x_d²`, the target conditional outcome variance. -/
def outcomeVar (q m : D → ℝ) (d : D) : ℝ := scaleX q m d ^ 2

/-- `k_d = √q_d x_d − 1`, the conditional residual mean coefficient. -/
def shiftK (q m : D → ℝ) (d : D) : ℝ := Real.sqrt (q d) * scaleX q m d - 1

/-- The scale is positive whenever the prescribed mean squared error exceeds one. -/
theorem scaleX_pos (q m : D → ℝ) (d : D) (hq0 : 0 ≤ q d) (hm : 1 < m d) :
    0 < scaleX q m d := by
  have h1 : 0 < m d - 1 + q d := by linarith
  have h2 : 0 < Real.sqrt (m d - 1 + q d) := Real.sqrt_pos.mpr h1
  have h3 : 0 ≤ Real.sqrt (q d) := Real.sqrt_nonneg _
  unfold scaleX
  linarith

/-- **UPT equation (7.3), first half: `m_d = 1 + v_d − 2√(q_d v_d)`.**  The scale is
built so that the prescribed mean squared error comes out exactly. -/
theorem mse_identity (q m : D → ℝ) (d : D) (hq0 : 0 ≤ q d) (hm : 1 ≤ m d) :
    m d = 1 + scaleX q m d ^ 2 - 2 * Real.sqrt (q d) * scaleX q m d := by
  have hq : Real.sqrt (q d) ^ 2 = q d := Real.sq_sqrt hq0
  have hr : Real.sqrt (m d - 1 + q d) ^ 2 = m d - 1 + q d :=
    Real.sq_sqrt (by linarith)
  unfold scaleX
  linear_combination hq - hr

/-- **UPT equation (7.3), second half: `m_d − k_d² = v_d(1 − q_d)`.**  This is the strict
conditional slack that lets the residual kernel exist. -/
theorem slack_identity (q m : D → ℝ) (d : D) (hq0 : 0 ≤ q d) (hm : 1 ≤ m d) :
    m d - shiftK q m d ^ 2 = outcomeVar q m d * (1 - q d) := by
  have hq : Real.sqrt (q d) ^ 2 = q d := Real.sq_sqrt hq0
  have hmid := mse_identity q m d hq0 hm
  unfold shiftK outcomeVar
  linear_combination hmid - scaleX q m d ^ 2 * hq

/-- The prescribed moments leave strict slack in every cell. -/
theorem shiftK_sq_lt (q m : D → ℝ) (d : D) (hq0 : 0 ≤ q d) (hq1 : q d < 1)
    (hm : 1 < m d) : shiftK q m d ^ 2 < m d := by
  have hslack := slack_identity q m d hq0 hm.le
  have hx := scaleX_pos q m d hq0 hm
  have hx2 : 0 < scaleX q m d ^ 2 := pow_pos hx 2
  have hpos : 0 < outcomeVar q m d * (1 - q d) := by
    unfold outcomeVar
    nlinarith
  linarith

/-- The slack survives multiplication by a scored sign, which is what the residual
kernel needs at every genotype. -/
theorem residual_slack (q m : D → ℝ) (hq0 : ∀ d, 0 ≤ q d) (hq1 : ∀ d, q d < 1)
    (hm : ∀ d, 1 < m d) :
    ∀ (d : D) (t : Bool), (shiftK q m d * sign t) ^ 2 < m d := by
  intro d t
  rw [mul_pow, sign_sq, mul_one]
  exact shiftK_sq_lt q m d (hq0 d) (hq1 d) (hm d)

/-- The conditional residual kernel given the whole genotype: distance cell and scored
sign. -/
def residualKernel (q m : D → ℝ) (delta : ℝ)
    (hk : ∀ (d : D) (t : Bool), (shiftK q m d * sign t) ^ 2 < m d) (hd : 0 ≤ delta)
    (d : D) (s : Bool) : ExpFunctional (Bool × Bool) :=
  residualLaw (m d) (shiftK q m d * sign s) delta (hk d s) hd

/-- The within-cell target law: a conditionally symmetric scored sign and the residual
kernel.  The scored sign law is the same for every prescribed curve and every
prescribed loss-explainability. -/
def cellTargetLaw (q m : D → ℝ) (delta : ℝ)
    (hk : ∀ (d : D) (t : Bool), (shiftK q m d * sign t) ^ 2 < m d) (hd : 0 ≤ delta)
    (d : D) : ExpFunctional (Bool × (Bool × Bool)) :=
  mixture (uniformExp Bool) (residualKernel q m delta hk hd d)

/-- The target phenotype `Y = S + E` in cell `d`. -/
def targetPhenotype (q m : D → ℝ) (delta : ℝ) (d : D) : Bool × (Bool × Bool) → ℝ :=
  fun z ↦ sign z.1 + residualValue (m d) (shiftK q m d * sign z.1) delta z.2

/-- The individual prediction residual on the joint cell-genotype-outcome space. -/
def targetResidual (q m : D → ℝ) (delta : ℝ) :
    D × (Bool × (Bool × Bool)) → ℝ :=
  fun z ↦ residualValue (m z.1) (shiftK q m z.1 * sign z.2.1) delta z.2.2

/-- The target phenotype at an explicit genotype. -/
theorem targetPhenotype_apply (q m : D → ℝ) (delta : ℝ) (d : D) (s : Bool)
    (r : Bool × Bool) :
    targetPhenotype q m delta d (s, r)
      = sign s + residualValue (m d) (shiftK q m d * sign s) delta r := rfl

/-- The prediction residual is the phenotype minus the deployed score. -/
theorem targetPhenotype_sub_score (q m : D → ℝ) (delta : ℝ) (d : D)
    (z : Bool × (Bool × Bool)) :
    targetPhenotype q m delta d z - liftGenotype sign z
      = targetResidual q m delta (d, z) := by
  show sign z.1 + residualValue (m d) (shiftK q m d * sign z.1) delta z.2 - sign z.1
    = residualValue (m d) (shiftK q m d * sign z.1) delta z.2
  ring

/-- The within-cell law in two-point form over the scored sign. -/
theorem cellTargetLaw_eval (q m : D → ℝ) (delta : ℝ)
    (hk : ∀ (d : D) (t : Bool), (shiftK q m d * sign t) ^ 2 < m d) (hd : 0 ≤ delta)
    (d : D) (f : Bool × (Bool × Bool) → ℝ) :
    cellTargetLaw q m delta hk hd d f
      = 1 / 2 * residualKernel q m delta hk hd d false (fun r ↦ f (false, r))
        + 1 / 2 * residualKernel q m delta hk hd d true (fun r ↦ f (true, r)) := by
  unfold cellTargetLaw
  rw [mixture_eval, uniformBool_eval]

/-- The fair scored sign has mean zero. -/
theorem uniformBool_sign_mean : uniformExp Bool sign = 0 := by
  rw [uniformBool_eval, sign_false, sign_true]
  ring

/-- The fair scored sign has variance one. -/
theorem uniformBool_sign_variance : variance (uniformExp Bool) sign = 1 := by
  have hsq : (fun s : Bool ↦ sign s ^ 2) = fun _ : Bool ↦ (1:ℝ) := funext sign_sq
  rw [variance_eq_expect_sq_sub_sq_mean, uniformBool_sign_mean, hsq,
    ExpFunctional.eval_const]
  ring

/-- The conditional residual mean is `k_d S`. -/
theorem kernel_first (q m : D → ℝ) (delta : ℝ)
    (hk : ∀ (d : D) (t : Bool), (shiftK q m d * sign t) ^ 2 < m d) (hd : 0 ≤ delta)
    (d : D) (s : Bool) :
    residualKernel q m delta hk hd d s
        (residualValue (m d) (shiftK q m d * sign s) delta)
      = shiftK q m d * sign s :=
  residual_first_moment (m d) (shiftK q m d * sign s) delta (hk d s) hd

/-- The conditional residual second moment is `m_d`. -/
theorem kernel_second (q m : D → ℝ) (delta : ℝ)
    (hk : ∀ (d : D) (t : Bool), (shiftK q m d * sign t) ^ 2 < m d) (hd : 0 ≤ delta)
    (d : D) (s : Bool) :
    residualKernel q m delta hk hd d s
        (fun r ↦ residualValue (m d) (shiftK q m d * sign s) delta r ^ 2)
      = m d :=
  residual_second_moment (m d) (shiftK q m d * sign s) delta (hk d s) hd

/-- The conditional individual-loss second moment is `m_d² + δ`. -/
theorem kernel_fourth (q m : D → ℝ) (delta : ℝ)
    (hk : ∀ (d : D) (t : Bool), (shiftK q m d * sign t) ^ 2 < m d) (hd : 0 ≤ delta)
    (d : D) (s : Bool) :
    residualKernel q m delta hk hd d s
        (fun r ↦ residualValue (m d) (shiftK q m d * sign s) delta r ^ 4)
      = m d ^ 2 + delta :=
  residual_fourth_moment (m d) (shiftK q m d * sign s) delta (hk d s) hd

/-- The conditional individual loss has second moment `m_d² + δ` in the joint
coordinates. -/
theorem kernel_residual_fourth (q m : D → ℝ) (delta : ℝ)
    (hk : ∀ (d : D) (t : Bool), (shiftK q m d * sign t) ^ 2 < m d) (hd : 0 ≤ delta)
    (d : D) (s : Bool) :
    residualKernel q m delta hk hd d s
        (fun r ↦ targetResidual q m delta (d, (s, r)) ^ 4)
      = m d ^ 2 + delta :=
  residual_fourth_moment (m d) (shiftK q m d * sign s) delta (hk d s) hd

/-- The conditional individual loss has mean `m_d` in the joint coordinates. -/
theorem kernel_residual_second (q m : D → ℝ) (delta : ℝ)
    (hk : ∀ (d : D) (t : Bool), (shiftK q m d * sign t) ^ 2 < m d) (hd : 0 ≤ delta)
    (d : D) (s : Bool) :
    residualKernel q m delta hk hd d s
        (fun r ↦ targetResidual q m delta (d, (s, r)) ^ 2)
      = m d :=
  residual_second_moment (m d) (shiftK q m d * sign s) delta (hk d s) hd

/-- **The conditional phenotype moments given the entire genotype and distance.**  Both
right-hand sides are free of `δ`: varying the prescribed loss-explainability changes
neither the conditional mean nor the conditional variance of the outcome. -/
theorem conditional_phenotype_moments (q m : D → ℝ) (delta : ℝ)
    (hk : ∀ (d : D) (t : Bool), (shiftK q m d * sign t) ^ 2 < m d) (hd : 0 ≤ delta)
    (d : D) (s : Bool) :
    residualKernel q m delta hk hd d s (fun r ↦ targetPhenotype q m delta d (s, r))
        = (1 + shiftK q m d) * sign s ∧
      residualKernel q m delta hk hd d s
          (fun r ↦ targetPhenotype q m delta d (s, r) ^ 2)
        = 1 + 2 * shiftK q m d + m d := by
  have hs := sign_sq s
  constructor
  · show residualKernel q m delta hk hd d s
        (fun r ↦ sign s + residualValue (m d) (shiftK q m d * sign s) delta r)
      = (1 + shiftK q m d) * sign s
    rw [shift_one, kernel_first]
    ring
  · show residualKernel q m delta hk hd d s
        (fun r ↦ (sign s + residualValue (m d) (shiftK q m d * sign s) delta r) ^ 2)
      = 1 + 2 * shiftK q m d + m d
    rw [shift_sq, kernel_first, kernel_second]
    linear_combination (1 + 2 * shiftK q m d) * hs

/-- The conditional cross moment of the score with the phenotype. -/
theorem kernel_score_cross (q m : D → ℝ) (delta : ℝ)
    (hk : ∀ (d : D) (t : Bool), (shiftK q m d * sign t) ^ 2 < m d) (hd : 0 ≤ delta)
    (d : D) (s : Bool) :
    residualKernel q m delta hk hd d s
        (fun r ↦ sign s * targetPhenotype q m delta d (s, r))
      = 1 + shiftK q m d := by
  have hs := sign_sq s
  show residualKernel q m delta hk hd d s
      (fun r ↦ sign s * (sign s + residualValue (m d) (shiftK q m d * sign s) delta r))
    = 1 + shiftK q m d
  rw [shift_mul, kernel_first]
  linear_combination (1 + shiftK q m d) * hs

/-- The cellwise phenotype mean is zero, by conditional score symmetry. -/
theorem cell_phenotype_mean (q m : D → ℝ) (delta : ℝ)
    (hk : ∀ (d : D) (t : Bool), (shiftK q m d * sign t) ^ 2 < m d) (hd : 0 ≤ delta)
    (d : D) :
    cellTargetLaw q m delta hk hd d (targetPhenotype q m delta d) = 0 := by
  rw [cellTargetLaw_eval, (conditional_phenotype_moments q m delta hk hd d false).1,
    (conditional_phenotype_moments q m delta hk hd d true).1, sign_false, sign_true]
  ring

/-- The cellwise score mean is zero. -/
theorem cell_score_mean (q m : D → ℝ) (delta : ℝ)
    (hk : ∀ (d : D) (t : Bool), (shiftK q m d * sign t) ^ 2 < m d) (hd : 0 ≤ delta)
    (d : D) : cellTargetLaw q m delta hk hd d (liftGenotype sign) = 0 := by
  rw [cellTargetLaw_eval]
  show 1 / 2 * residualKernel q m delta hk hd d false (fun _ ↦ sign false)
      + 1 / 2 * residualKernel q m delta hk hd d true (fun _ ↦ sign true) = 0
  rw [ExpFunctional.eval_const, ExpFunctional.eval_const, sign_false, sign_true]
  ring

/-- **The cellwise outcome variance is exactly `v_d`.** -/
theorem cell_phenotype_variance (q m : D → ℝ) (delta : ℝ)
    (hk : ∀ (d : D) (t : Bool), (shiftK q m d * sign t) ^ 2 < m d) (hd : 0 ≤ delta)
    (d : D) (hq0 : 0 ≤ q d) (hm : 1 ≤ m d) :
    variance (cellTargetLaw q m delta hk hd d) (targetPhenotype q m delta d)
      = outcomeVar q m d := by
  have hmid := mse_identity q m d hq0 hm
  rw [variance_eq_expect_sq_sub_sq_mean, cell_phenotype_mean, cellTargetLaw_eval,
    (conditional_phenotype_moments q m delta hk hd d false).2,
    (conditional_phenotype_moments q m delta hk hd d true).2]
  unfold shiftK outcomeVar
  linear_combination hmid

/-- **The cellwise predictive covariance is exactly `1 + k_d = √(q_d v_d)`.** -/
theorem cell_score_covariance (q m : D → ℝ) (delta : ℝ)
    (hk : ∀ (d : D) (t : Bool), (shiftK q m d * sign t) ^ 2 < m d) (hd : 0 ≤ delta)
    (d : D) :
    covariance (cellTargetLaw q m delta hk hd d) (liftGenotype sign)
        (targetPhenotype q m delta d) = 1 + shiftK q m d := by
  have hfun : (fun z : Bool × (Bool × Bool) ↦
      liftGenotype sign z * targetPhenotype q m delta d z)
      = fun z : Bool × (Bool × Bool) ↦ sign z.1 * targetPhenotype q m delta d z := rfl
  rw [covariance_eq_expect_mul_sub_means, cell_phenotype_mean, cell_score_mean, hfun,
    cellTargetLaw_eval, kernel_score_cross, kernel_score_cross]
  ring

/-- **UPT equation (7.1), first identity: the cellwise squared correlation with the
unchanged source-trained score is exactly the prescribed `q_d`.** -/
theorem cell_score_accuracy (q m : D → ℝ) (delta : ℝ)
    (hk : ∀ (d : D) (t : Bool), (shiftK q m d * sign t) ^ 2 < m d) (hd : 0 ≤ delta)
    (d : D) (hq0 : 0 ≤ q d) (hm : 1 < m d) :
    scoreAccuracy (uniformExp Bool) (residualKernel q m delta hk hd d) sign
      (targetPhenotype q m delta d) = q d := by
  have hqq : Real.sqrt (q d) ^ 2 = q d := Real.sq_sqrt hq0
  have hx := scaleX_pos q m d hq0 hm
  have hlaw : mixture (uniformExp Bool) (residualKernel q m delta hk hd d)
      = cellTargetLaw q m delta hk hd d := rfl
  unfold scoreAccuracy
  rw [hlaw, cell_score_covariance, cell_phenotype_variance q m delta hk hd d hq0 hm.le,
    uniformBool_sign_variance]
  unfold shiftK outcomeVar
  have hne : (1:ℝ) * scaleX q m d ^ 2 ≠ 0 := by
    have hpos : 0 < scaleX q m d ^ 2 := pow_pos hx 2
    intro hcon
    rw [one_mul] at hcon
    linarith
  rw [div_eq_iff hne]
  linear_combination scaleX q m d ^ 2 * hqq

/-- **UPT equation (7.1), second identity: the cellwise mean squared error of the
unchanged source-trained score is exactly the prescribed `m_d`.** -/
theorem cell_expected_mse (q m : D → ℝ) (delta : ℝ)
    (hk : ∀ (d : D) (t : Bool), (shiftK q m d * sign t) ^ 2 < m d) (hd : 0 ≤ delta)
    (d : D) :
    expMse (cellTargetLaw q m delta hk hd d) (targetPhenotype q m delta d)
      (liftGenotype sign) = m d := by
  have hfun : (fun z : Bool × (Bool × Bool) ↦
      (targetPhenotype q m delta d z - liftGenotype sign z) ^ 2)
      = fun z : Bool × (Bool × Bool) ↦ targetResidual q m delta (d, z) ^ 2 := by
    funext z
    rw [targetPhenotype_sub_score]
  unfold expMse
  rw [hfun, cellTargetLaw_eval, kernel_residual_second, kernel_residual_second]
  ring

/-- The conditional mean individual loss, as a function of the distance cell. -/
def cellLossMean (q m : D → ℝ) (delta : ℝ)
    (hk : ∀ (d : D) (t : Bool), (shiftK q m d * sign t) ^ 2 < m d) (hd : 0 ≤ delta) :
    D → ℝ :=
  fun d ↦ cellTargetLaw q m delta hk hd d (fun z ↦ targetResidual q m delta (d, z) ^ 2)

/-- The conditional mean individual loss is exactly the prescribed `m`. -/
theorem cellLossMean_eq (q m : D → ℝ) (delta : ℝ)
    (hk : ∀ (d : D) (t : Bool), (shiftK q m d * sign t) ^ 2 < m d) (hd : 0 ≤ delta) :
    cellLossMean q m delta hk hd = m := by
  funext d
  unfold cellLossMean
  rw [cellTargetLaw_eval, kernel_residual_second, kernel_residual_second]
  ring

/-- The full target law: distance cells, scored signs, outcome randomness. -/
def fullTargetLaw (E : ExpFunctional D) (q m : D → ℝ) (delta : ℝ)
    (hk : ∀ (d : D) (t : Bool), (shiftK q m d * sign t) ^ 2 < m d) (hd : 0 ≤ delta) :
    ExpFunctional (D × (Bool × (Bool × Bool))) :=
  mixture E (cellTargetLaw q m delta hk hd)

/-- `η_D`: the fraction of individual squared-loss variance the distance cell explains. -/
def lossFraction (E : ExpFunctional D) (q m : D → ℝ) (delta : ℝ)
    (hk : ∀ (d : D) (t : Bool), (shiftK q m d * sign t) ^ 2 < m d) (hd : 0 ≤ delta) : ℝ :=
  explainableFraction (variance E (cellLossMean q m delta hk hd))
    (variance (fullTargetLaw E q m delta hk hd) (fun z ↦ targetResidual q m delta z ^ 2))

/-- **The exact total variance of individual squared loss.**  The conditional loss
variance given the whole genotype is the constant `δ`, so the total is `δ + B`. -/
theorem loss_total_variance (E : ExpFunctional D) (q m : D → ℝ) (delta : ℝ)
    (hk : ∀ (d : D) (t : Bool), (shiftK q m d * sign t) ^ 2 < m d) (hd : 0 ≤ delta) :
    variance (fullTargetLaw E q m delta hk hd) (fun z ↦ targetResidual q m delta z ^ 2)
      = delta + variance E m := by
  have hint : (fun d ↦ cellTargetLaw q m delta hk hd d
          (fun z ↦ targetResidual q m delta (d, z) ^ 4)
        - cellTargetLaw q m delta hk hd d
            (fun z ↦ targetResidual q m delta (d, z) ^ 2) ^ 2)
      = fun _ : D ↦ delta := by
    funext d
    rw [cellTargetLaw_eval, cellTargetLaw_eval, kernel_residual_fourth,
      kernel_residual_fourth, kernel_residual_second, kernel_residual_second]
    ring
  have hbet : (fun d ↦ cellTargetLaw q m delta hk hd d
      (fun z ↦ targetResidual q m delta (d, z) ^ 2)) = m := cellLossMean_eq q m delta hk hd
  unfold fullTargetLaw
  rw [squared_loss_total, hint, ExpFunctional.eval_const, hbet]

/-- The exact loss-explainability of the construction. -/
theorem lossFraction_eq (E : ExpFunctional D) (q m : D → ℝ) (delta : ℝ)
    (hk : ∀ (d : D) (t : Bool), (shiftK q m d * sign t) ^ 2 < m d) (hd : 0 ≤ delta) :
    lossFraction E q m delta hk hd = variance E m / (delta + variance E m) := by
  unfold lossFraction explainableFraction Descent.Core.ratio
  rw [cellLossMean_eq, loss_total_variance]

/-- The conditional loss variance `δ = B(1/η − 1)` prescribed by a target
loss-explainability. -/
def lossSlack (E : ExpFunctional D) (m : D → ℝ) (eta : ℝ) : ℝ :=
  variance E m * (eta⁻¹ - 1)

/-- The prescribed conditional loss variance is admissible for every `η ∈ (0,1]`. -/
theorem lossSlack_nonneg (E : ExpFunctional D) (m : D → ℝ) (eta : ℝ)
    (hB : 0 ≤ variance E m) (heta0 : 0 < eta) (heta1 : eta ≤ 1) :
    0 ≤ lossSlack E m eta := by
  have h1 : 1 ≤ eta⁻¹ := by
    have hmul := mul_le_mul_of_nonneg_right heta1 (inv_pos.mpr heta0).le
    rw [mul_inv_cancel₀ (ne_of_gt heta0), one_mul] at hmul
    exact hmul
  unfold lossSlack
  exact mul_nonneg hB (by linarith)

/-- **UPT equation (7.1), third identity: the prescribed loss-explainability is
attained exactly.** -/
theorem lossFraction_eq_eta (E : ExpFunctional D) (q m : D → ℝ) (eta : ℝ)
    (hk : ∀ (d : D) (t : Bool), (shiftK q m d * sign t) ^ 2 < m d)
    (hB : 0 < variance E m) (heta0 : 0 < eta) (heta1 : eta ≤ 1) :
    lossFraction E q m (lossSlack E m eta) hk
        (lossSlack_nonneg E m eta hB.le heta0 heta1) = eta := by
  have hetane : eta ≠ 0 := ne_of_gt heta0
  have hBne : variance E m ≠ 0 := ne_of_gt hB
  rw [lossFraction_eq]
  unfold lossSlack
  field_simp <;> ring

/-- **UPT Theorem 7.1: the simultaneous source-fixed portability construction.**

On one fixed pre-outcome law -- an arbitrary distance cell law and a conditionally
symmetric `±1` score -- an arbitrary prescribed cellwise squared correlation
`q_d ∈ [0,1)`, an arbitrary prescribed cellwise mean squared error `m_d > 1` and an
arbitrary prescribed loss-explainability `η ∈ (0,1]` hold simultaneously.  The genotype
law, the deployed score and the distance variable do not depend on any of the three
prescriptions, and `conditional_phenotype_moments` shows that varying `η` leaves the
conditional phenotype mean and variance given the entire genotype untouched. -/
theorem simultaneous_source_fixed_construction (E : ExpFunctional D) (q m : D → ℝ)
    (eta : ℝ) (hq0 : ∀ d, 0 ≤ q d) (hq1 : ∀ d, q d < 1) (hm : ∀ d, 1 < m d)
    (hB : 0 < variance E m) (heta0 : 0 < eta) (heta1 : eta ≤ 1) :
    lossFraction E q m (lossSlack E m eta) (residual_slack q m hq0 hq1 hm)
          (lossSlack_nonneg E m eta hB.le heta0 heta1) = eta ∧
      ∀ d : D,
        scoreAccuracy (uniformExp Bool)
            (residualKernel q m (lossSlack E m eta) (residual_slack q m hq0 hq1 hm)
              (lossSlack_nonneg E m eta hB.le heta0 heta1) d)
            sign (targetPhenotype q m (lossSlack E m eta) d) = q d ∧
          expMse
            (cellTargetLaw q m (lossSlack E m eta) (residual_slack q m hq0 hq1 hm)
              (lossSlack_nonneg E m eta hB.le heta0 heta1) d)
            (targetPhenotype q m (lossSlack E m eta) d) (liftGenotype sign) = m d :=
  ⟨lossFraction_eq_eta E q m eta (residual_slack q m hq0 hq1 hm) hB heta0 heta1,
    fun d ↦
      ⟨cell_score_accuracy q m (lossSlack E m eta) (residual_slack q m hq0 hq1 hm)
          (lossSlack_nonneg E m eta hB.le heta0 heta1) d (hq0 d) (hm d),
        cell_expected_mse q m (lossSlack E m eta) (residual_slack q m hq0 hq1 hm)
          (lossSlack_nonneg E m eta hB.le heta0 heta1) d⟩⟩

end

end Descent.Portability.SourceFixedRealization
