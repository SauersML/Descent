/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Calibrator.TransportIdentities
import Mathlib.LinearAlgebra.Matrix.Symmetric
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace Calibrator

noncomputable section

/-!
# Singular quadratic risk and post-hoc correction floors

All statements are finite-dimensional and allow a singular second-moment
matrix.  A pseudoinverse is not logically required: the exact excess-risk
identity follows from any solution of the normal equations `B v = b`.
-/

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Quadratic risk up to an arbitrary outcome-only constant.

    Empirical status: UNTESTED. -/
def quadraticRisk (outcomeSecondMoment : ℝ) (B : Matrix ι ι ℝ)
    (b w : ι → ℝ) : ℝ :=
  outcomeSecondMoment - 2 * dot w b + dot w (B.mulVec w)

/-- Symmetry of the bilinear form represented by a second-moment matrix. -/
def IsSymmetricBilinearMatrix (B : Matrix ι ι ℝ) : Prop :=
  ∀ x y : ι → ℝ, dot x (B.mulVec y) = dot y (B.mulVec x)

omit [DecidableEq ι] in
/-- Every symmetric matrix represents a symmetric bilinear form.

    Fourteen theorems in this file take `IsSymmetricBilinearMatrix B` as a
    hypothesis. This says which matrices satisfy it: every symmetric one, and so
    every second-moment matrix, which is the case those theorems are for.

    `Matrix.IsSymm B` is spelled out rather than written `B.IsSymm`: dot
    notation there resolves against the unfolded function type and asks for
    `Function.IsSymm`, which does not exist. -/
theorem isSymmetricBilinearMatrix_of_isSymm {B : Matrix ι ι ℝ}
    (hB : Matrix.IsSymm B) :
    IsSymmetricBilinearMatrix B := by
  intro x y
  simp only [dot, Matrix.mulVec, dotProduct, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ ↦ Finset.sum_congr rfl fun i _ ↦ ?_
  rw [Matrix.IsSymm.apply hB i j]
  ring

/-- A concrete inhabitant, so the hypothesis class is demonstrably nonempty and
    the fourteen results above are not vacuous. -/
theorem isSymmetricBilinearMatrix_one :
    IsSymmetricBilinearMatrix (1 : Matrix ι ι ℝ) := by
  intro x y
  simp [dot, Matrix.one_mulVec, mul_comm]

omit [DecidableEq ι] in
theorem matrix_mulVec_sub (B : Matrix ι ι ℝ) (x y : ι → ℝ) :
    B.mulVec (fun i ↦ x i - y i) =
      fun i ↦ B.mulVec x i - B.mulVec y i := by
  ext i
  simp only [Matrix.mulVec, dotProduct]
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib]

omit [DecidableEq ι] in
theorem matrix_mulVec_smul (B : Matrix ι ι ℝ) (c : ℝ) (x : ι → ℝ) :
    B.mulVec (c • x) = c • B.mulVec x := by
  ext i
  simp [Matrix.mulVec, dotProduct, Finset.mul_sum, mul_left_comm]

omit [DecidableEq ι] in
theorem dot_sub_right (x y z : ι → ℝ) :
    dot x (fun i ↦ y i - z i) = dot x y - dot x z := by
  simp [dot, mul_sub, Finset.sum_sub_distrib]

omit [DecidableEq ι] in
theorem dot_smul_left (c : ℝ) (x y : ι → ℝ) :
    dot (c • x) y = c * dot x y := by
  simp [dot, Finset.mul_sum, mul_assoc]

omit [DecidableEq ι] in
theorem dot_smul_right (c : ℝ) (x y : ι → ℝ) :
    dot x (c • y) = c * dot x y := by
  simp [dot, Finset.mul_sum, mul_left_comm]

/-- The usual excess-risk identity remains exact for singular `B`.  The only
needed fact is range compatibility, expressed directly as `B v = b`. -/
theorem singular_quadratic_excess_risk_identity
    (outcomeSecondMoment : ℝ) (B : Matrix ι ι ℝ)
    (b w v : ι → ℝ)
    (hsymmetric : IsSymmetricBilinearMatrix B)
    (hnormal : B.mulVec v = b) :
    quadraticRisk outcomeSecondMoment B b w -
        quadraticRisk outcomeSecondMoment B b v =
      dot (fun i ↦ w i - v i)
        (B.mulVec (fun i ↦ w i - v i)) := by
  have hnormalDotW : dot w b = dot w (B.mulVec v) := by rw [← hnormal]
  have hnormalDotV : dot v b = dot v (B.mulVec v) := by rw [← hnormal]
  have hcross : dot v (B.mulVec w) = dot w (B.mulVec v) := hsymmetric v w
  rw [quadraticRisk, quadraticRisk, hnormalDotW, hnormalDotV,
    matrix_mulVec_sub, dot_sub_left, dot_sub_right, dot_sub_right, hcross]
  ring

/-- Positive semidefiniteness turns the singular identity into global
optimality; uniqueness is deliberately not asserted. -/
theorem normal_solution_minimizes_singular_quadratic_risk
    (outcomeSecondMoment : ℝ) (B : Matrix ι ι ℝ)
    (b v : ι → ℝ)
    (hsymmetric : IsSymmetricBilinearMatrix B)
    (hpsd : ∀ z : ι → ℝ, 0 ≤ dot z (B.mulVec z))
    (hnormal : B.mulVec v = b) :
    ∀ w, quadraticRisk outcomeSecondMoment B b v ≤
      quadraticRisk outcomeSecondMoment B b w := by
  intro w
  have hid := singular_quadratic_excess_risk_identity
    outcomeSecondMoment B b w v hsymmetric hnormal
  linarith [hpsd (fun i ↦ w i - v i)]

/-- Moving a normal-equation solution by a kernel vector produces another
solution with exactly the same risk. -/
theorem singular_minimizer_kernel_invariance
    (outcomeSecondMoment : ℝ) (B : Matrix ι ι ℝ)
    (b v k : ι → ℝ)
    (hsymmetric : IsSymmetricBilinearMatrix B)
    (hnormal : B.mulVec v = b)
    (hkernel : B.mulVec k = 0) :
    B.mulVec (fun i ↦ v i + k i) = b ∧
      quadraticRisk outcomeSecondMoment B b (fun i ↦ v i + k i) =
        quadraticRisk outcomeSecondMoment B b v := by
  have hnormalShift : B.mulVec (fun i ↦ v i + k i) = b := by
    rw [matrix_mulVec_add, hnormal, hkernel]
    simp
  refine ⟨hnormalShift, ?_⟩
  have hid := singular_quadratic_excess_risk_identity
    outcomeSecondMoment B b (fun i ↦ v i + k i) v hsymmetric hnormal
  have hzero :
      dot (fun i ↦ (v i + k i) - v i)
        (B.mulVec (fun i ↦ (v i + k i) - v i)) = 0 := by
    have hdiff : (fun i ↦ (v i + k i) - v i) = k := by
      funext i
      ring
    rw [hdiff, hkernel]
    simp [dot]
  linarith

/-- Quadratic-form distance between two coefficient vectors. -/
def quadraticCoefficientDistance (B : Matrix ι ι ℝ)
    (w v : ι → ℝ) : ℝ :=
  dot (fun i ↦ w i - v i) (B.mulVec (fun i ↦ w i - v i))

/-- Best scalar rescaling of a deployed direction toward a target direction. -/
def bestScalarCorrection (B : Matrix ι ι ℝ)
    (u v : ι → ℝ) : ℝ :=
  dot u (B.mulVec v) / dot u (B.mulVec u)

/-- **bestScalarCorrection at a null correction direction, named.** With the correction direction
identically zero its energy `⟪u, B u⟫` vanishes, so the optimal scalar is undefined -- there is
no direction to scale. Lean returns `0`, which reads as the correct answer being no correction at
all, rather than as an ill-posed problem. Consumers must exclude it by hypothesis. -/
theorem bestScalarCorrection_null_direction_is_junk (B : Matrix ι ι ℝ) (v : ι → ℝ) :
    bestScalarCorrection B (fun _ ↦ 0) v = 0 := by
  unfold bestScalarCorrection dot
  simp

/-- Irreducible quadratic risk after optimizing over scalar rescalings. -/
def scalarCorrectionFloor (B : Matrix ι ι ℝ)
    (u v : ι → ℝ) : ℝ :=
  dot v (B.mulVec v) -
    dot u (B.mulVec v) ^ 2 / dot u (B.mulVec u)

/-- Completed-square identity for post-hoc scalar correction.  It gives both
the exact optimum and the exact geometric floor. -/
theorem quadraticCoefficientDistance_eq_floor_add_sq
    (B : Matrix ι ι ℝ) (u v : ι → ℝ) (c : ℝ)
    (hsymmetric : IsSymmetricBilinearMatrix B)
    (hu : dot u (B.mulVec u) ≠ 0) :
    quadraticCoefficientDistance B (fun i ↦ c * u i) v =
      scalarCorrectionFloor B u v +
        dot u (B.mulVec u) * (c - bestScalarCorrection B u v) ^ 2 := by
  have hcross : dot v (B.mulVec u) = dot u (B.mulVec v) := hsymmetric v u
  have hscaled : (fun i ↦ c * u i) = c • u := by
    funext i
    simp
  have hleftScaled : dot (c • u) (B.mulVec v) = c * dot u (B.mulVec v) :=
    dot_smul_left c u (B.mulVec v)
  have hrightScaled : dot v (c • B.mulVec u) = c * dot v (B.mulVec u) :=
    dot_smul_right c v (B.mulVec u)
  have hbothScaled :
      dot (c • u) (c • B.mulVec u) = c ^ 2 * dot u (B.mulVec u) := by
    calc
      dot (c • u) (c • B.mulVec u)
          = c * dot u (c • B.mulVec u) := dot_smul_left c u _
      _ = c * (c * dot u (B.mulVec u)) := by
        rw [dot_smul_right]
      _ = c ^ 2 * dot u (B.mulVec u) := by ring
  unfold quadraticCoefficientDistance scalarCorrectionFloor bestScalarCorrection
  rw [hscaled]
  rw [matrix_mulVec_sub, matrix_mulVec_smul, dot_sub_left,
    dot_sub_right, dot_sub_right, hleftScaled, hrightScaled, hbothScaled, hcross]
  field_simp [hu]
  ring

/-- With positive variance along the deployed direction, the floor is attained
by the reported scalar and no scalar correction can do better. -/
theorem best_scalar_correction_attains_floor
    (B : Matrix ι ι ℝ) (u v : ι → ℝ)
    (hsymmetric : IsSymmetricBilinearMatrix B)
    (hu : 0 < dot u (B.mulVec u)) :
      quadraticCoefficientDistance B
        (fun i ↦ bestScalarCorrection B u v * u i) v =
        scalarCorrectionFloor B u v ∧
      ∀ c : ℝ, scalarCorrectionFloor B u v ≤
        quadraticCoefficientDistance B (fun i ↦ c * u i) v := by
  constructor
  · rw [quadraticCoefficientDistance_eq_floor_add_sq B u v
      (bestScalarCorrection B u v) hsymmetric hu.ne']
    ring
  · intro c
    rw [quadraticCoefficientDistance_eq_floor_add_sq B u v c hsymmetric hu.ne']
    exact le_add_of_nonneg_right (mul_nonneg (le_of_lt hu) (sq_nonneg _))

end

end Calibrator
