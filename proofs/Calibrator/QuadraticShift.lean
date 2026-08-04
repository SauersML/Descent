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

The pooled-environment section proves that nonnegative covariance energies cannot cancel.
With nonnegative sampling weights, the pooled kernel is the intersection over exactly the
positive-weight environments; a second ancestry gives a strict identifiability gain precisely
when it detects a reference-null direction. That same direction rules out every finite uniform
reference-to-pool portability constant.

## Main results

- `singular_quadratic_excess_risk_identity`: exact excess risk without invertibility.
- `finiteEnvironmentCovariancePool_mulVec_eq_zero_iff_active`: active-kernel intersection.
- `finiteEnvironmentCovariancePool_kernel_ssubset`: exact strict-diversity criterion.
- `no_uniformQuadraticPortabilityBound_to_finiteEnvironmentPool`: diversity/shift bridge.
- `best_scalar_correction_attains_floor`: exact post-hoc scalar-correction optimum.
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

omit [DecidableEq ι] in
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

omit [DecidableEq ι] in
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

omit [DecidableEq ι] in
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

omit [DecidableEq ι] in
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

omit [DecidableEq ι] in
/-- A correction direction with no energy sends the subtracted quotient to junk `0`, so the
floor collapses to the whole target energy: no correction is credited, because the term that
would credit it is undefined. -/
theorem scalarCorrectionFloor_at_zero_energy_is_junk
    (B : Matrix ι ι ℝ) (u v : ι → ℝ) (hzero : dot u (B.mulVec u) = 0) :
    scalarCorrectionFloor B u v = dot v (B.mulVec v) := by
  unfold scalarCorrectionFloor
  rw [hzero, div_zero, sub_zero]


omit [DecidableEq ι] in
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

omit [DecidableEq ι] in
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

/-! ## Pooled-environment nullspace geometry -/

/-- Weighted covariance of two labeled environments. -/
def weightedCovariancePool (weightLeft weightRight : ℝ)
    (left right : Matrix ι ι ℝ) : Matrix ι ι ℝ :=
  fun i j ↦ weightLeft * left i j + weightRight * right i j

omit [DecidableEq ι] in
/-- Matrix-vector action of a two-environment covariance pool. -/
theorem weightedCovariancePool_mulVec
    (weightLeft weightRight : ℝ) (left right : Matrix ι ι ℝ)
    (shift : ι → ℝ) :
    (weightedCovariancePool weightLeft weightRight left right).mulVec shift =
      fun i ↦ weightLeft * left.mulVec shift i + weightRight * right.mulVec shift i := by
  ext i
  simp only [weightedCovariancePool, Matrix.mulVec, dotProduct, add_mul]
  rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
  apply congrArg₂ (fun x y : ℝ ↦ x + y) <;>
    apply Finset.sum_congr rfl <;>
    intro j _ <;>
    ring

omit [DecidableEq ι] in
/-- Quadratic energy of a pooled covariance is the weighted sum of environmental energies. -/
theorem weightedCovariancePool_energy
    (weightLeft weightRight : ℝ) (left right : Matrix ι ι ℝ)
    (shift : ι → ℝ) :
    dot shift ((weightedCovariancePool weightLeft weightRight left right).mulVec shift) =
      weightLeft * dot shift (left.mulVec shift) +
        weightRight * dot shift (right.mulVec shift) := by
  rw [weightedCovariancePool_mulVec]
  simp only [dot, mul_add]
  rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
  apply congrArg₂ (fun x y : ℝ ↦ x + y) <;>
    apply Finset.sum_congr rfl <;>
    intro i _ <;>
    ring

omit [DecidableEq ι] in
/-- **Exact multi-environment kernel-intersection law.** With positive environment weights,
positive-semidefinite covariance energies cannot cancel. Hence a coefficient direction is
invisible to the pooled design exactly when it is invisible in both environments.

The `energy = 0 ↔ kernel` hypotheses are the finite-dimensional PSD fact stated explicitly,
so the theorem is reusable for any covariance representation satisfying it. -/
theorem weightedCovariancePool_mulVec_eq_zero_iff
    (weightLeft weightRight : ℝ) (left right : Matrix ι ι ℝ)
    (hweightLeft : 0 < weightLeft) (hweightRight : 0 < weightRight)
    (hleftNonneg : ∀ shift : ι → ℝ, 0 ≤ dot shift (left.mulVec shift))
    (hrightNonneg : ∀ shift : ι → ℝ, 0 ≤ dot shift (right.mulVec shift))
    (hleftZero : ∀ shift : ι → ℝ,
      dot shift (left.mulVec shift) = 0 ↔ left.mulVec shift = 0)
    (hrightZero : ∀ shift : ι → ℝ,
      dot shift (right.mulVec shift) = 0 ↔ right.mulVec shift = 0)
    (shift : ι → ℝ) :
    (weightedCovariancePool weightLeft weightRight left right).mulVec shift = 0 ↔
      left.mulVec shift = 0 ∧ right.mulVec shift = 0 := by
  constructor
  · intro hpool
    have henergy : weightLeft * dot shift (left.mulVec shift) +
        weightRight * dot shift (right.mulVec shift) = 0 := by
      rw [← weightedCovariancePool_energy weightLeft weightRight left right shift, hpool]
      simp [dot]
    have hleftEnergy : dot shift (left.mulVec shift) = 0 := by
      nlinarith [hleftNonneg shift, hrightNonneg shift]
    have hrightEnergy : dot shift (right.mulVec shift) = 0 := by
      nlinarith [hleftNonneg shift, hrightNonneg shift]
    exact ⟨(hleftZero shift).mp hleftEnergy, (hrightZero shift).mp hrightEnergy⟩
  · rintro ⟨hleft, hright⟩
    rw [weightedCovariancePool_mulVec, hleft, hright]
    ext i
    simp

/-- Weighted covariance of an arbitrary finite environment panel. -/
def finiteEnvironmentCovariancePool
    {κ : Type*} [Fintype κ]
    (weight : κ → ℝ) (covariance : κ → Matrix ι ι ℝ) : Matrix ι ι ℝ :=
  fun i j ↦ ∑ environment, weight environment * covariance environment i j

omit [DecidableEq ι] in
/-- Matrix-vector action of a finite weighted covariance pool. -/
theorem finiteEnvironmentCovariancePool_mulVec
    {κ : Type*} [Fintype κ]
    (weight : κ → ℝ) (covariance : κ → Matrix ι ι ℝ) (shift : ι → ℝ) :
    (finiteEnvironmentCovariancePool weight covariance).mulVec shift =
      fun i ↦ ∑ environment, weight environment *
        (covariance environment).mulVec shift i := by
  classical
  ext i
  simp only [finiteEnvironmentCovariancePool, Matrix.mulVec, dotProduct]
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro environment _
  apply Finset.sum_congr rfl
  intro j _
  ring

omit [DecidableEq ι] in
/-- Pooled quadratic energy is the weighted sum of all environment-specific energies. -/
theorem finiteEnvironmentCovariancePool_energy
    {κ : Type*} [Fintype κ]
    (weight : κ → ℝ) (covariance : κ → Matrix ι ι ℝ) (shift : ι → ℝ) :
    dot shift ((finiteEnvironmentCovariancePool weight covariance).mulVec shift) =
      ∑ environment, weight environment *
        dot shift ((covariance environment).mulVec shift) := by
  classical
  rw [finiteEnvironmentCovariancePool_mulVec]
  simp only [dot]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro environment _
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- **A positive-semidefinite family of environment covariances, named once.**

Five statements below are conditioned on the same two facts about the family: every
environment's quadratic form is nonnegative, and it vanishes exactly on that environment's
kernel.  Written out at each theorem, that block was five identical lines repeated five
times.  It is one property of the family, so it is one structure. -/
structure PositiveSemidefiniteFamily {κ : Type*}
    (covariance : κ → Matrix ι ι ℝ) : Prop where
  /-- Every environment's quadratic form is nonnegative. -/
  energy_nonneg : ∀ environment shift,
    0 ≤ dot shift ((covariance environment).mulVec shift)
  /-- ... and vanishes exactly on that environment's kernel. -/
  energy_eq_zero_iff : ∀ environment shift,
    dot shift ((covariance environment).mulVec shift) = 0 ↔
      (covariance environment).mulVec shift = 0

/-- **The family is inhabited.**  Theorems conditioned on a bundle nothing satisfies are
true and empty.  The identity covariance in every environment is such a family: its
quadratic form is the squared norm, nonnegative and vanishing only at zero. -/
theorem positiveSemidefiniteFamily_one {κ : Type*} :
    PositiveSemidefiniteFamily (fun _ : κ ↦ (1 : Matrix ι ι ℝ)) where
  energy_nonneg := by
    intro _ shift
    simp only [Matrix.one_mulVec, dot]
    exact Finset.sum_nonneg fun i _ ↦ mul_self_nonneg (shift i)
  energy_eq_zero_iff := by
    intro _ shift
    simp only [Matrix.one_mulVec, dot]
    constructor
    · intro h
      funext i
      have hi := (Finset.sum_eq_zero_iff_of_nonneg
        (fun j _ ↦ mul_self_nonneg (shift j))).mp h i (Finset.mem_univ i)
      exact mul_self_eq_zero.mp hi
    · intro h
      simp [h]

omit [DecidableEq ι] in
/-- **Active-environment kernel law.** With merely nonnegative sampling weights, the pooled
kernel is the intersection of the kernels of exactly those environments assigned positive
weight. Zero-weight environments contribute neither information nor constraints. -/
theorem finiteEnvironmentCovariancePool_mulVec_eq_zero_iff_active
    {κ : Type*} [Fintype κ]
    (weight : κ → ℝ) (covariance : κ → Matrix ι ι ℝ)
    (hweight : ∀ environment, 0 ≤ weight environment)
    (hpsd : PositiveSemidefiniteFamily covariance)
    (shift : ι → ℝ) :
    (finiteEnvironmentCovariancePool weight covariance).mulVec shift = 0 ↔
      ∀ environment, 0 < weight environment →
        (covariance environment).mulVec shift = 0 := by
  classical
  constructor
  · intro hpool environment hactive
    have henergySum :
        ∑ environment, weight environment *
          dot shift ((covariance environment).mulVec shift) = 0 := by
      rw [← finiteEnvironmentCovariancePool_energy weight covariance shift, hpool]
      simp [dot]
    have htermNonneg : ∀ environment ∈ (Finset.univ : Finset κ),
        0 ≤ weight environment * dot shift ((covariance environment).mulVec shift) := by
      intro environment _
      exact mul_nonneg (hweight environment) (hpsd.energy_nonneg environment shift)
    have hweightedZero :=
      (Finset.sum_eq_zero_iff_of_nonneg htermNonneg).mp henergySum
        environment (Finset.mem_univ environment)
    have henergyZero : dot shift ((covariance environment).mulVec shift) = 0 :=
      (mul_eq_zero.mp hweightedZero).resolve_left hactive.ne'
    exact (hpsd.energy_eq_zero_iff environment shift).mp henergyZero
  · intro hkernel
    rw [finiteEnvironmentCovariancePool_mulVec]
    ext i
    apply Finset.sum_eq_zero
    intro environment _
    rcases (hweight environment).eq_or_lt with hweightZero | hweightPos
    · rw [← hweightZero]
      simp
    · rw [hkernel environment hweightPos]
      simp

omit [DecidableEq ι] in
/-- **Finite-panel kernel-intersection law.** For any finite collection of PSD covariance
environments with strictly positive sampling weights, pooling shrinks nonidentifiability to the
intersection of all environmental kernels. No number of positive-semidefinite environments can
cancel information supplied by another one. -/
theorem finiteEnvironmentCovariancePool_mulVec_eq_zero_iff
    {κ : Type*} [Fintype κ]
    (weight : κ → ℝ) (covariance : κ → Matrix ι ι ℝ)
    (hweight : ∀ environment, 0 < weight environment)
    (hpsd : PositiveSemidefiniteFamily covariance)
    (shift : ι → ℝ) :
    (finiteEnvironmentCovariancePool weight covariance).mulVec shift = 0 ↔
      ∀ environment, (covariance environment).mulVec shift = 0 := by
  rw [finiteEnvironmentCovariancePool_mulVec_eq_zero_iff_active
    weight covariance (fun environment ↦ (hweight environment).le) hpsd shift]
  constructor
  · intro hactive environment
    exact hactive environment (hweight environment)
  · intro hkernel environment _
    exact hkernel environment

omit [DecidableEq ι] in
/-- A direction detected by at least one active environment cannot remain in the pooled
nullspace; inactive environments are irrelevant. -/
theorem finiteEnvironmentCovariancePool_mulVec_ne_zero_of_exists_active
    {κ : Type*} [Fintype κ]
    (weight : κ → ℝ) (covariance : κ → Matrix ι ι ℝ)
    (hweight : ∀ environment, 0 ≤ weight environment)
    (hpsd : PositiveSemidefiniteFamily covariance)
    (shift : ι → ℝ)
    (hdetected : ∃ environment, 0 < weight environment ∧
      (covariance environment).mulVec shift ≠ 0) :
    (finiteEnvironmentCovariancePool weight covariance).mulVec shift ≠ 0 := by
  intro hpool
  obtain ⟨environment, hactive, hdetect⟩ := hdetected
  exact hdetect ((finiteEnvironmentCovariancePool_mulVec_eq_zero_iff_active
    weight covariance hweight hpsd shift).mp hpool environment hactive)

omit [DecidableEq ι] in
/-- A direction detected by at least one positively weighted environment cannot remain in the
pooled nullspace. -/
theorem finiteEnvironmentCovariancePool_mulVec_ne_zero_of_exists
    {κ : Type*} [Fintype κ]
    (weight : κ → ℝ) (covariance : κ → Matrix ι ι ℝ)
    (hweight : ∀ environment, 0 < weight environment)
    (hpsd : PositiveSemidefiniteFamily covariance)
    (shift : ι → ℝ)
    (hdetected : ∃ environment, (covariance environment).mulVec shift ≠ 0) :
    (finiteEnvironmentCovariancePool weight covariance).mulVec shift ≠ 0 := by
  obtain ⟨environment, hdetect⟩ := hdetected
  exact finiteEnvironmentCovariancePool_mulVec_ne_zero_of_exists_active
    weight covariance (fun environment ↦ (hweight environment).le) hpsd shift
      ⟨environment, hweight environment, hdetect⟩

omit [DecidableEq ι] in
/-- **Strict active-diversity gain.** The pooled nullspace is strictly smaller than an active
reference environment's nullspace exactly when some active environment detects a direction the
reference misses. Inactive cohorts cannot witness strict shrinkage. -/
theorem finiteEnvironmentCovariancePool_kernel_ssubset_active
    {κ : Type*} [Fintype κ]
    (weight : κ → ℝ) (covariance : κ → Matrix ι ι ℝ)
    (reference : κ)
    (hweight : ∀ environment, 0 ≤ weight environment)
    (hreferenceActive : 0 < weight reference)
    (hpsd : PositiveSemidefiniteFamily covariance)
    (hseparates : ∃ shift : ι → ℝ,
      (covariance reference).mulVec shift = 0 ∧
        ∃ environment, 0 < weight environment ∧
          (covariance environment).mulVec shift ≠ 0) :
    {shift : ι → ℝ |
      (finiteEnvironmentCovariancePool weight covariance).mulVec shift = 0} ⊂
        {shift : ι → ℝ | (covariance reference).mulVec shift = 0} := by
  apply Set.ssubset_iff_subset_ne.mpr
  constructor
  · intro shift hpool
    exact (finiteEnvironmentCovariancePool_mulVec_eq_zero_iff_active
      weight covariance hweight hpsd shift).mp hpool reference hreferenceActive
  · obtain ⟨shift, hreference, hdetected⟩ := hseparates
    intro hequal
    have hpool : (finiteEnvironmentCovariancePool weight covariance).mulVec shift = 0 := by
      change shift ∈ {shift : ι → ℝ |
        (finiteEnvironmentCovariancePool weight covariance).mulVec shift = 0}
      rw [hequal]
      exact hreference
    exact finiteEnvironmentCovariancePool_mulVec_ne_zero_of_exists_active
      weight covariance hweight hpsd shift hdetected hpool

omit [DecidableEq ι] in
/-- **Strict diversity gain.** The pooled nullspace is strictly smaller than a reference
environment's nullspace whenever another environment detects at least one direction that the
reference environment misses. This is the exact algebraic condition under which adding an
ancestry removes a genuine nonidentifiability direction. -/
theorem finiteEnvironmentCovariancePool_kernel_ssubset
    {κ : Type*} [Fintype κ]
    (weight : κ → ℝ) (covariance : κ → Matrix ι ι ℝ)
    (reference : κ)
    (hweight : ∀ environment, 0 < weight environment)
    (hpsd : PositiveSemidefiniteFamily covariance)
    (hseparates : ∃ shift : ι → ℝ,
      (covariance reference).mulVec shift = 0 ∧
        ∃ environment, (covariance environment).mulVec shift ≠ 0) :
    {shift : ι → ℝ |
      (finiteEnvironmentCovariancePool weight covariance).mulVec shift = 0} ⊂
        {shift : ι → ℝ | (covariance reference).mulVec shift = 0} := by
  apply finiteEnvironmentCovariancePool_kernel_ssubset_active
    weight covariance reference (fun environment ↦ (hweight environment).le)
      (hweight reference) hpsd
  obtain ⟨shift, hreference, environment, hdetect⟩ := hseparates
  exact ⟨shift, hreference, environment, hweight environment, hdetect⟩

/-! ## Singular portability boundary -/

/-- A uniform coefficient-space portability bound: target excess risk is at most `constant`
times source excess risk in every coefficient direction.  No nonsingularity is assumed. -/
def UniformQuadraticPortabilityBound
    (source target : Matrix ι ι ℝ) (constant : ℝ) : Prop :=
  ∀ shift : ι → ℝ,
    dot shift (target.mulVec shift) ≤
      constant * dot shift (source.mulVec shift)

omit [DecidableEq ι] in
/-- **A uniform portability bound cannot create target risk on a source-null direction.**
Positive semidefiniteness of the target closes the inequality to an equality. -/
theorem target_energy_eq_zero_of_uniformPortability_of_source_kernel
    (source target : Matrix ι ι ℝ) (constant : ℝ)
    (hbound : UniformQuadraticPortabilityBound source target constant)
    (htarget : ∀ shift : ι → ℝ, 0 ≤ dot shift (target.mulVec shift))
    (shift : ι → ℝ) (hsourceKernel : source.mulVec shift = 0) :
    dot shift (target.mulVec shift) = 0 := by
  apply le_antisymm
  · have h := hbound shift
    rw [hsourceKernel] at h
    simpa [dot] using h
  · exact htarget shift

omit [DecidableEq ι] in
/-- If zero target quadratic energy characterizes the target kernel, every uniform portability
bound forces the source kernel into the target kernel.  This is the coefficient-space form of
`ker source ⊆ ker target`. -/
theorem target_kernel_of_uniformPortability_of_source_kernel
    (source target : Matrix ι ι ℝ) (constant : ℝ)
    (hbound : UniformQuadraticPortabilityBound source target constant)
    (htargetNonneg : ∀ shift : ι → ℝ, 0 ≤ dot shift (target.mulVec shift))
    (htargetZero : ∀ shift : ι → ℝ,
      dot shift (target.mulVec shift) = 0 ↔ target.mulVec shift = 0)
    (shift : ι → ℝ) (hsourceKernel : source.mulVec shift = 0) :
    target.mulVec shift = 0 := by
  apply (htargetZero shift).mp
  exact target_energy_eq_zero_of_uniformPortability_of_source_kernel
    source target constant hbound htargetNonneg shift hsourceKernel

omit [DecidableEq ι] in
/-- **Catastrophic shift certificate.**  If a direction is invisible in training but has
strictly positive deployment risk, then no finite uniform source-to-target portability constant
exists.  This is the sharp algebraic obstruction behind nonportable singular fits. -/
theorem no_uniformQuadraticPortabilityBound_of_source_kernel_target_pos
    (source target : Matrix ι ι ℝ) (shift : ι → ℝ)
    (hsourceKernel : source.mulVec shift = 0)
    (htargetPos : 0 < dot shift (target.mulVec shift)) :
    ¬ ∃ constant : ℝ, UniformQuadraticPortabilityBound source target constant := by
  rintro ⟨constant, hbound⟩
  have h := hbound shift
  rw [hsourceKernel] at h
  simp [dot] at h
  unfold dot at htargetPos
  exact (not_lt_of_ge h) htargetPos

omit [DecidableEq ι] in
/-- **Diversity gain forces reference-to-pool nonportability.** If one direction is invisible
in a reference environment but detected by any positively weighted environment, pooled target
risk is strictly positive along that direction. Therefore no finite constant can bound pooled
deployment risk by reference-environment risk uniformly over coefficients. -/
theorem no_uniformQuadraticPortabilityBound_to_finiteEnvironmentPool
    {κ : Type*} [Fintype κ]
    (weight : κ → ℝ) (covariance : κ → Matrix ι ι ℝ)
    (reference : κ)
    (hweight : ∀ environment, 0 < weight environment)
    (hpsd : PositiveSemidefiniteFamily covariance)
    (shift : ι → ℝ)
    (hreference : (covariance reference).mulVec shift = 0)
    (hdetected : ∃ environment, (covariance environment).mulVec shift ≠ 0) :
    ¬ ∃ constant : ℝ, UniformQuadraticPortabilityBound
      (covariance reference) (finiteEnvironmentCovariancePool weight covariance) constant := by
  classical
  obtain ⟨detector, hdetector⟩ := hdetected
  have hdetectorEnergyNe :
      dot shift ((covariance detector).mulVec shift) ≠ 0 := by
    intro henergy
    exact hdetector ((hpsd.energy_eq_zero_iff detector shift).mp henergy)
  have hdetectorEnergyPos : 0 < dot shift ((covariance detector).mulVec shift) :=
    lt_of_le_of_ne (hpsd.energy_nonneg detector shift) (Ne.symm hdetectorEnergyNe)
  have htermNonneg : ∀ environment ∈ (Finset.univ : Finset κ),
      0 ≤ weight environment * dot shift ((covariance environment).mulVec shift) := by
    intro environment _
    exact mul_nonneg (hweight environment).le (hpsd.energy_nonneg environment shift)
  have hdetectorLe : weight detector * dot shift ((covariance detector).mulVec shift) ≤
      ∑ environment, weight environment *
        dot shift ((covariance environment).mulVec shift) :=
    Finset.single_le_sum htermNonneg (Finset.mem_univ detector)
  have hpoolEnergyPos : 0 < dot shift
      ((finiteEnvironmentCovariancePool weight covariance).mulVec shift) := by
    rw [finiteEnvironmentCovariancePool_energy]
    exact (mul_pos (hweight detector) hdetectorEnergyPos).trans_le hdetectorLe
  exact no_uniformQuadraticPortabilityBound_of_source_kernel_target_pos
    (covariance reference) (finiteEnvironmentCovariancePool weight covariance)
      shift hreference hpoolEnergyPos

end

end Calibrator
