import Calibrator.TransportIdentities
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring

namespace Calibrator

noncomputable section

/-!
# Second-moment shift identities

This module formalizes the distribution-free algebra behind residual-score
identification and movement of linear projections.  Expectations are modeled
by `ExpFunctional`; no covariance inverse is assumed.  Consequently the
identities remain valid for singular second-moment matrices.  Invertibility is
needed only by a downstream procedure that wishes to recover a unique
coefficient vector from the identified moment equation.
-/

variable {Ω ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Raw cross moment `E[X Y]`. -/
def rawCrossMoment (E : ExpFunctional Ω) (X : Ω → ι → ℝ)
    (Y : Ω → ℝ) : ι → ℝ :=
  fun i => E (fun ω => X ω i * Y ω)

/-- Observable covariance between each coordinate and the residual of a
deployed linear coefficient. -/
def residualScoreMoment (E : ExpFunctional Ω) (X : Ω → ι → ℝ)
    (Y : Ω → ℝ) (w : ι → ℝ) : ι → ℝ :=
  rawCrossMoment E X (fun ω => Y ω - dot w (X ω))

/-- Cross moments of a linear score are obtained by applying the second-moment
matrix to its coefficient vector. -/
theorem rawCrossMoment_linScore
    (E : ExpFunctional Ω) (X : Ω → ι → ℝ) (w : ι → ℝ) :
    rawCrossMoment E X (linScore w X) =
      (secondMomentMatrix E X).mulVec w := by
  ext i
  unfold rawCrossMoment linScore secondMomentMatrix
  have hexpand :
      (fun ω => X ω i * dot w (X ω)) =
        ∑ j, (w j) • (fun ω => X ω i * X ω j) := by
    funext ω
    simp [dot, Finset.mul_sum, smul_eq_mul, mul_left_comm, mul_comm]
  rw [hexpand, ExpFunctional.eval_sum]
  simp [Matrix.mulVec, dotProduct, E.smul_eval, mul_comm]

/-- Expanding the deployed residual separates its outcome cross moment from
the second-moment action on the deployed coefficient. -/
theorem residualScoreMoment_eq_cross_sub_secondMoment
    (E : ExpFunctional Ω) (X : Ω → ι → ℝ)
    (Y : Ω → ℝ) (w : ι → ℝ) :
    residualScoreMoment E X Y w =
      rawCrossMoment E X Y - (secondMomentMatrix E X).mulVec w := by
  ext i
  unfold residualScoreMoment rawCrossMoment
  have hexpand :
      (fun ω => X ω i * (Y ω - dot w (X ω))) =
        (fun ω => X ω i * Y ω) - (fun ω => X ω i * dot w (X ω)) := by
    funext ω
    change X ω i * (Y ω - dot w (X ω)) =
      X ω i * Y ω - X ω i * dot w (X ω)
    ring
  rw [hexpand, E.eval_sub]
  have hlinear := congrFun (rawCrossMoment_linScore E X w) i
  simpa [rawCrossMoment, linScore] using congrArg (fun z => E (fun ω => X ω i * Y ω) - z) hlinear

/-- Exact residual-score identity.  The change from a deployed coefficient
`w` to any normal-equation solution `v` is identified through the singular-safe
equation `E[X(Y-wᵀX)] = E[XXᵀ](v-w)`. -/
theorem residual_score_identifies_projection_shift
    (E : ExpFunctional Ω) (X : Ω → ι → ℝ)
    (Y : Ω → ℝ) (w v : ι → ℝ)
    (hnormal : residualScoreMoment E X Y v = 0) :
    residualScoreMoment E X Y w =
      (secondMomentMatrix E X).mulVec (fun i => v i - w i) := by
  rw [residualScoreMoment_eq_cross_sub_secondMoment]
  rw [residualScoreMoment_eq_cross_sub_secondMoment] at hnormal
  have hcross : rawCrossMoment E X Y = (secondMomentMatrix E X).mulVec v := by
    exact sub_eq_zero.mp hnormal
  rw [hcross]
  ext i
  change
    (∑ j, secondMomentMatrix E X i j * v j) -
        (∑ j, secondMomentMatrix E X i j * w j) =
      ∑ j, secondMomentMatrix E X i j * (v j - w j)
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Projection movement under a change of expectation.  The target residual
score at the old coefficient is exactly the target second-moment matrix applied
to the coefficient movement, while its source counterpart is zero. -/
theorem projection_movement_under_measure_shift
    (P Q : ExpFunctional Ω) (X : Ω → ι → ℝ)
    (h : Ω → ℝ) (u v : ι → ℝ)
    (hsource : residualScoreMoment P X h u = 0)
    (htarget : residualScoreMoment Q X h v = 0) :
    residualScoreMoment Q X h u =
        (secondMomentMatrix Q X).mulVec (fun i => v i - u i) ∧
      residualScoreMoment P X h u = 0 := by
  exact ⟨residual_score_identifies_projection_shift Q X h u v htarget, hsource⟩

/-- Residual scores are additive in the outcome function.  This is the
algebraic step separating conditional-mean change from projection movement. -/
omit [DecidableEq ι] in
theorem residualScoreMoment_outcome_change
    (E : ExpFunctional Ω) (X : Ω → ι → ℝ)
    (hOld hNew : Ω → ℝ) (w : ι → ℝ) :
    residualScoreMoment E X hNew w =
      residualScoreMoment E X hOld w +
        rawCrossMoment E X (fun ω => hNew ω - hOld ω) := by
  ext i
  unfold residualScoreMoment rawCrossMoment
  have hexpand :
      (fun ω => X ω i * (hNew ω - dot w (X ω))) =
        (fun ω => X ω i * (hOld ω - dot w (X ω))) +
          (fun ω => X ω i * (hNew ω - hOld ω)) := by
    funext ω
    change X ω i * (hNew ω - dot w (X ω)) =
      X ω i * (hOld ω - dot w (X ω)) +
        X ω i * (hNew ω - hOld ω)
    ring
  rw [hexpand, E.add_eval]
  rfl

/-- Exact genuine-change/artifact decomposition.  The total target
coefficient movement solves a moment equation whose two summands are the
target projection of the changed outcome function and the residual score of
the old function at the source coefficient. -/
theorem projection_shift_genuine_artifact_decomposition
    (Q : ExpFunctional Ω) (X : Ω → ι → ℝ)
    (hOld hNew : Ω → ℝ) (u v : ι → ℝ)
    (htarget : residualScoreMoment Q X hNew v = 0) :
    (secondMomentMatrix Q X).mulVec (fun i => v i - u i) =
      rawCrossMoment Q X (fun ω => hNew ω - hOld ω) +
        residualScoreMoment Q X hOld u := by
  rw [← residual_score_identifies_projection_shift Q X hNew u v htarget]
  rw [residualScoreMoment_outcome_change]
  abel

/-- Pointwise conditional excess risk when the target conditional mean has a
nonlinear residual `η = m - vᵀx`. -/
theorem nonlinear_conditional_excess_risk_identity
    (m : ℝ) (x w v : ι → ℝ) :
    (m - dot w x) ^ 2 - (m - dot v x) ^ 2 =
      dot (fun i => w i - v i) x ^ 2 -
        2 * dot (fun i => w i - v i) x * (m - dot v x) := by
  rw [dot_sub_left]
  ring

/-- Although nonlinear misspecification changes conditional excess risk, its
mean remains the usual quadratic form because the nonlinear residual is
orthogonal to every linear score at the target projection. -/
theorem mean_nonlinear_conditional_excess_eq_quadratic
    (E : ExpFunctional Ω) (X : Ω → ι → ℝ)
    (m : Ω → ℝ) (w v : ι → ℝ)
    (hnormal : ∀ i,
      E (fun ω => X ω i * (m ω - dot v (X ω))) = 0) :
    E (fun ω =>
        (m ω - dot w (X ω)) ^ 2 - (m ω - dot v (X ω)) ^ 2) =
      E (fun ω => (dot (fun i => w i - v i) (X ω)) ^ 2) := by
  have horth :
      E (fun ω =>
        dot (fun i => w i - v i) (X ω) * (m ω - dot v (X ω))) = 0 := by
    simpa [mul_comm] using
      normal_equations_orthogonality E X m v (fun i => w i - v i) hnormal
  have hpointwise :
      (fun ω =>
        (m ω - dot w (X ω)) ^ 2 - (m ω - dot v (X ω)) ^ 2) =
        (fun ω => (dot (fun i => w i - v i) (X ω)) ^ 2) +
          (-2 : ℝ) •
            (fun ω => dot (fun i => w i - v i) (X ω) *
              (m ω - dot v (X ω))) := by
    funext ω
    rw [nonlinear_conditional_excess_risk_identity]
    simp [smul_eq_mul]
    ring
  rw [hpointwise, E.add_eval, E.smul_eval, horth]
  ring

end

end Calibrator
