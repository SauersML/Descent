import Calibrator.Probability
import Mathlib.Probability.CondVar

namespace Calibrator

noncomputable section

/-!
# Algebraic Transport and Metric Identities

This file isolates the algebraic core used by the portability arguments:

- expectation-style linear functionals,
- variance/covariance/MSE identities,
- least-squares transport decompositions,
- scalar-summary insufficiency for linear summaries,
- trait-specific transported covariance decompositions,
- binary metric identities relating prevalence, recall, FPR, and precision.

The point is to keep these results independent of any particular probability
space representation. Downstream modules can instantiate `ExpFunctional` with
an actual expectation operator.
-/

/--
A normalized linear expectation functional on real-valued observables.
The algebraic transport and metric identities below use only these axioms.
-/
structure ExpFunctional (Ω : Type*) where
  eval : (Ω → ℝ) → ℝ
  add_eval : ∀ f g : Ω → ℝ, eval (f + g) = eval f + eval g
  smul_eval : ∀ (c : ℝ) (f : Ω → ℝ), eval (c • f) = c * eval f
  const_one : eval (fun _ => (1 : ℝ)) = 1

instance {Ω : Type*} : CoeFun (ExpFunctional Ω) (fun _ => (Ω → ℝ) → ℝ) :=
  ⟨ExpFunctional.eval⟩

namespace ExpFunctional

variable {Ω : Type*}

@[simp] theorem eval_zero (E : ExpFunctional Ω) : E (0 : Ω → ℝ) = 0 := by
  have h := E.smul_eval (0 : ℝ) (fun _ => (1 : ℝ))
  simpa using h

@[simp] theorem eval_neg (E : ExpFunctional Ω) (f : Ω → ℝ) : E (-f) = -E f := by
  have h := E.smul_eval (-1 : ℝ) f
  simpa using h

@[simp] theorem eval_sub (E : ExpFunctional Ω) (f g : Ω → ℝ) :
    E (f - g) = E f - E g := by
  rw [sub_eq_add_neg, E.add_eval, E.eval_neg]
  simp [sub_eq_add_neg]

@[simp] theorem eval_const (E : ExpFunctional Ω) (c : ℝ) : E (fun _ : Ω => c) = c := by
  have hconst : (fun _ : Ω => c) = c • (fun _ : Ω => (1 : ℝ)) := by
    funext ω
    simp
  rw [hconst, E.smul_eval, E.const_one]
  ring

@[simp] theorem eval_sum {ι : Type*} [DecidableEq ι]
    (E : ExpFunctional Ω) (s : Finset ι) (f : ι → Ω → ℝ) :
    E (Finset.sum s f) = Finset.sum s (fun i => E (f i)) := by
  induction s using Finset.induction with
  | empty =>
      simp [eval_zero]
  | @insert a s ha hs =>
      simp [Finset.sum_insert, ha, E.add_eval, hs]

end ExpFunctional

section MetricIdentities

variable {Ω : Type*}

def mean (E : ExpFunctional Ω) (Z : Ω → ℝ) : ℝ := E Z

def variance (E : ExpFunctional Ω) (Z : Ω → ℝ) : ℝ :=
  E (fun ω => (Z ω - E Z) ^ 2)

def covariance (E : ExpFunctional Ω) (X Y : Ω → ℝ) : ℝ :=
  E (fun ω => (X ω - E X) * (Y ω - E Y))

def expMse (E : ExpFunctional Ω) (Y S : Ω → ℝ) : ℝ :=
  E (fun ω => (Y ω - S ω) ^ 2)

def bias (E : ExpFunctional Ω) (Y S : Ω → ℝ) : ℝ :=
  E S - E Y

theorem eval_centered_zero (E : ExpFunctional Ω) (Z : Ω → ℝ) :
    E (fun ω => Z ω - E Z) = 0 := by
  rw [show (fun ω => Z ω - E Z) = Z - (fun _ => E Z) by
    funext ω
    simp]
  rw [E.eval_sub, E.eval_const]
  ring

theorem variance_eq_expect_sq_sub_sq_mean (E : ExpFunctional Ω) (Z : Ω → ℝ) :
    variance E Z = E (fun ω => Z ω ^ 2) - (E Z) ^ 2 := by
  unfold variance
  have h_expand :
      (fun ω => (Z ω - E Z) ^ 2)
        = (fun ω => Z ω ^ 2) + ((-2 * E Z) • Z) + (fun _ => (E Z) ^ 2) := by
    funext ω
    simp [smul_eq_mul]
    ring
  rw [h_expand]
  rw [E.add_eval, E.add_eval, E.smul_eval, E.eval_const]
  ring

theorem covariance_eq_expect_mul_sub_means (E : ExpFunctional Ω) (X Y : Ω → ℝ) :
    covariance E X Y = E (fun ω => X ω * Y ω) - (E X) * (E Y) := by
  unfold covariance
  have h_expand :
      (fun ω => (X ω - E X) * (Y ω - E Y))
        = (fun ω => X ω * Y ω)
          + (-(E Y)) • X
          + (-(E X)) • Y
          + (fun _ => (E X) * (E Y)) := by
    funext ω
    simp [smul_eq_mul]
    ring
  rw [h_expand]
  rw [E.add_eval, E.add_eval, E.add_eval, E.smul_eval, E.smul_eval, E.eval_const]
  ring

theorem mse_eq_variance_add_variance_sub_two_cov_add_bias_sq
    (E : ExpFunctional Ω) (Y S : Ω → ℝ) :
    expMse E Y S =
      variance E Y + variance E S - 2 * covariance E Y S + (bias E Y S) ^ 2 := by
  unfold expMse bias
  rw [variance_eq_expect_sq_sub_sq_mean, variance_eq_expect_sq_sub_sq_mean,
      covariance_eq_expect_mul_sub_means]
  have h_expand :
      (fun ω => (Y ω - S ω) ^ 2)
        = (fun ω => Y ω ^ 2) + ((-2 : ℝ) • (fun ω => Y ω * S ω)) + (fun ω => S ω ^ 2) := by
    funext ω
    simp [smul_eq_mul]
    ring
  rw [h_expand, E.add_eval, E.add_eval, E.smul_eval]
  ring

theorem covariance_add_right (E : ExpFunctional Ω) (X Y Z : Ω → ℝ) :
    covariance E X (fun ω => Y ω + Z ω) = covariance E X Y + covariance E X Z := by
  rw [covariance_eq_expect_mul_sub_means, covariance_eq_expect_mul_sub_means,
      covariance_eq_expect_mul_sub_means]
  have hxy :
      E (fun ω => X ω * (Y ω + Z ω))
        = E (fun ω => X ω * Y ω) + E (fun ω => X ω * Z ω) := by
    have h :
        (fun ω => X ω * (Y ω + Z ω))
          = (fun ω => X ω * Y ω) + (fun ω => X ω * Z ω) := by
      funext ω
      change X ω * (Y ω + Z ω) = X ω * Y ω + X ω * Z ω
      rw [mul_add]
    rw [h, E.add_eval]
  have hyz : E (fun ω => Y ω + Z ω) = E Y + E Z := by
    simpa using E.add_eval Y Z
  rw [hxy, hyz]
  ring

theorem covariance_smul_right (E : ExpFunctional Ω) (X Y : Ω → ℝ) (c : ℝ) :
    covariance E X (c • Y) = c * covariance E X Y := by
  rw [covariance_eq_expect_mul_sub_means, covariance_eq_expect_mul_sub_means]
  have hxy : E (fun ω => X ω * (c • Y) ω) = c * E (fun ω => X ω * Y ω) := by
    have h :
        (fun ω => X ω * (c • Y) ω) = c • (fun ω => X ω * Y ω) := by
      funext ω
      simp [smul_eq_mul, mul_assoc, mul_left_comm]
    rw [h, E.smul_eval]
  have hy : E (c • Y) = c * E Y := by
    rw [E.smul_eval]
  rw [hxy, hy]
  ring

theorem covariance_finset_sum_right
    {ι : Type*} [DecidableEq ι]
    (E : ExpFunctional Ω) (X : Ω → ℝ) (s : Finset ι) (Y : ι → Ω → ℝ) :
    covariance E X (fun ω => Finset.sum s (fun i => Y i ω))
      = Finset.sum s (fun i => covariance E X (Y i)) := by
  induction s using Finset.induction with
  | empty =>
      simp [covariance_eq_expect_mul_sub_means, ExpFunctional.eval_zero]
  | @insert a s ha hs =>
      simp [Finset.sum_insert, ha, covariance_add_right, hs]

end MetricIdentities

section LinearAlgebraicPortability

variable {Ω : Type*}
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def dot (x y : ι → ℝ) : ℝ := ∑ i, x i * y i

theorem dot_add_left (x y z : ι → ℝ) :
    dot (fun i => x i + y i) z = dot x z + dot y z := by
  simp [dot, add_mul, Finset.sum_add_distrib]

theorem dot_sub_left (x y z : ι → ℝ) :
    dot (fun i => x i - y i) z = dot x z - dot y z := by
  simp [dot, sub_eq_add_neg, add_mul, Finset.sum_add_distrib]

theorem normal_equations_orthogonality
    (E : ExpFunctional Ω)
    (X : Ω → ι → ℝ) (Y : Ω → ℝ)
    (wStar u : ι → ℝ)
    (hnormal : ∀ i, E (fun ω => X ω i * (Y ω - dot wStar (X ω))) = 0) :
    E (fun ω => (Y ω - dot wStar (X ω)) * dot u (X ω)) = 0 := by
  have h_expand :
      (fun ω => (Y ω - dot wStar (X ω)) * dot u (X ω))
        = ∑ i, (u i) • (fun ω => X ω i * (Y ω - dot wStar (X ω))) := by
    funext ω
    simp [dot, Finset.mul_sum, smul_eq_mul, mul_assoc, mul_left_comm, mul_comm]
  rw [h_expand, ExpFunctional.eval_sum]
  rw [show (∑ i, E ((u i) • (fun ω => X ω i * (Y ω - dot wStar (X ω)))))
        = ∑ i, u i * E (fun ω => X ω i * (Y ω - dot wStar (X ω))) by
        apply Finset.sum_congr rfl
        intro i hi
        rw [E.smul_eval]]
  rw [show (∑ i, u i * E (fun ω => X ω i * (Y ω - dot wStar (X ω))))
        = ∑ i, u i * 0 by
        apply Finset.sum_congr rfl
        intro i hi
        rw [hnormal i]]
  simp

theorem mse_transport_decomposition
    (E : ExpFunctional Ω)
    (X : Ω → ι → ℝ) (Y : Ω → ℝ)
    (wStar u : ι → ℝ)
    (hnormal : ∀ i, E (fun ω => X ω i * (Y ω - dot wStar (X ω))) = 0) :
    E (fun ω => (Y ω - dot (fun i => wStar i + u i) (X ω)) ^ 2)
      = E (fun ω => (Y ω - dot wStar (X ω)) ^ 2)
        + E (fun ω => (dot u (X ω)) ^ 2) := by
  let R : Ω → ℝ := fun ω => Y ω - dot wStar (X ω)
  let U : Ω → ℝ := fun ω => dot u (X ω)
  have horth : E (fun ω => R ω * U ω) = 0 := by
    simpa [R, U, mul_comm] using normal_equations_orthogonality E X Y wStar u hnormal
  have hdot :
      ∀ ω, dot (fun i => wStar i + u i) (X ω) = dot wStar (X ω) + dot u (X ω) := by
    intro ω
    simpa using dot_add_left wStar u (X ω)
  have hsq :
      (fun ω => (Y ω - dot (fun i => wStar i + u i) (X ω)) ^ 2)
        = (fun ω => (R ω - U ω) ^ 2) := by
    funext ω
    rw [hdot ω]
    simp [R, U]
    ring
  have hexpand :
      (fun ω => (R ω - U ω) ^ 2)
        = (fun ω => R ω ^ 2) + ((-2 : ℝ) • (fun ω => R ω * U ω)) + (fun ω => U ω ^ 2) := by
    funext ω
    simp [smul_eq_mul]
    ring_nf
  rw [hsq, hexpand, E.add_eval, E.add_eval, E.smul_eval, horth]
  ring_nf
  have hRexp :
      (fun ω => R ω ^ 2)
        = (fun ω => -(Y ω * dot wStar (X ω) * 2) + Y ω ^ 2 + dot wStar (X ω) ^ 2) := by
    funext ω
    simp [R]
    ring
  have hUsq : (fun ω => U ω ^ 2) = (fun ω => (dot u (X ω)) ^ 2) := by
    rfl
  rw [hRexp, hUsq]

theorem mse_transport_decomposition_general
    (E : ExpFunctional Ω)
    (X : Ω → ι → ℝ) (Y : Ω → ℝ)
    (wStar w : ι → ℝ)
    (hnormal : ∀ i, E (fun ω => X ω i * (Y ω - dot wStar (X ω))) = 0) :
    E (fun ω => (Y ω - dot w (X ω)) ^ 2)
      = E (fun ω => (Y ω - dot wStar (X ω)) ^ 2)
        + E (fun ω => (dot (fun i => w i - wStar i) (X ω)) ^ 2) := by
  have h :=
    mse_transport_decomposition E X Y wStar (fun i => w i - wStar i) hnormal
  have hw : (fun i => wStar i + (w i - wStar i)) = w := by
    funext i
    ring
  simpa [hw] using h

end LinearAlgebraicPortability

section MasterTransport

variable {Ω : Type*}
variable {J L : Type*} [Fintype J] [DecidableEq J] [Fintype L] [DecidableEq L]

/-- Linear score `wᵀX`. -/
def linScore (w : J → ℝ) (X : Ω → J → ℝ) : Ω → ℝ :=
  fun ω => dot w (X ω)

/-- Second-moment matrix `E[X_i X_j]`. -/
def secondMomentMatrix (E : ExpFunctional Ω) (X : Ω → J → ℝ) : Matrix J J ℝ :=
  Matrix.of fun i j => E (fun ω => X ω i * X ω j)

/-- Covariance matrix `Cov(X_i, X_j)`. -/
def covarianceMatrix (E : ExpFunctional Ω) (X : Ω → J → ℝ) : Matrix J J ℝ :=
  Matrix.of fun i j => covariance E (fun ω => X ω i) (fun ω => X ω j)

/-- Cross-covariance vector `Cov(X_i, Y)`. -/
def crossCovVector (E : ExpFunctional Ω) (X : Ω → J → ℝ) (Y : Ω → ℝ) : J → ℝ :=
  fun i => covariance E (fun ω => X ω i) Y

/-- Tag/causal covariance transport object `K`. -/
def predictorCausalCovariance
    (E : ExpFunctional Ω) (X : Ω → J → ℝ) (C : Ω → L → ℝ) : Matrix J L ℝ :=
  Matrix.of fun j l => covariance E (fun ω => X ω j) (fun ω => C ω l)

/-- Context-dependent cross-covariance correction `c`. -/
def contextCrossCovVector
    (E : ExpFunctional Ω) (X : Ω → J → ℝ) (h : Ω → ℝ) : J → ℝ :=
  fun j => covariance E (fun ω => X ω j) h

/-- Causal linear signal `Cᵀβ`. -/
def causalSignal (β : L → ℝ) (C : Ω → L → ℝ) : Ω → ℝ :=
  fun ω => dot β (C ω)

/-- Closed-form moment map `Σ^{-1} Σ_xy`. -/
def optimalWeightsFromMoments
    (sigmaInv : Matrix J J ℝ)
    (E : ExpFunctional Ω) (X : Ω → J → ℝ) (Y : Ω → ℝ) : J → ℝ :=
  sigmaInv.mulVec (crossCovVector E X Y)

theorem matrix_mulVec_add (A : Matrix J J ℝ) (x y : J → ℝ) :
    A.mulVec (fun i => x i + y i) = A.mulVec x + A.mulVec y := by
  ext j
  simp [Matrix.mulVec, dotProduct, left_distrib, Finset.sum_add_distrib]

theorem covariance_with_causal_signal
    (E : ExpFunctional Ω) (Xj : Ω → ℝ) (C : Ω → L → ℝ) (β : L → ℝ) :
    covariance E Xj (causalSignal β C)
      = dot (fun l => covariance E Xj (fun ω => C ω l)) β := by
  unfold causalSignal dot
  have hsum :
      (fun ω => ∑ l, β l * C ω l)
        = (fun ω => ∑ l, ((β l) • (fun ω' => C ω' l)) ω) := by
    funext ω
    simp
  rw [hsum, covariance_finset_sum_right]
  rw [show (∑ i, covariance E Xj ((β i) • fun ω => C ω i))
        = ∑ i, β i * covariance E Xj (fun ω => C ω i) by
        apply Finset.sum_congr rfl
        intro i hi
        rw [covariance_smul_right]]
  simp [dot, mul_comm]

theorem crossCovVector_decomposition
    (E : ExpFunctional Ω) (X : Ω → J → ℝ) (C : Ω → L → ℝ)
    (β : L → ℝ) (h : Ω → ℝ) :
    crossCovVector E X (fun ω => causalSignal β C ω + h ω)
      = (predictorCausalCovariance E X C).mulVec β + contextCrossCovVector E X h := by
  ext j
  unfold crossCovVector predictorCausalCovariance contextCrossCovVector
  rw [covariance_add_right]
  rw [covariance_with_causal_signal]
  simp [Matrix.mulVec, dotProduct, dot]

theorem optimalWeightsFromMoments_decomposition
    (sigmaInv : Matrix J J ℝ)
    (E : ExpFunctional Ω) (X : Ω → J → ℝ) (C : Ω → L → ℝ)
    (β : L → ℝ) (h : Ω → ℝ) :
    optimalWeightsFromMoments sigmaInv E X (fun ω => causalSignal β C ω + h ω)
      = sigmaInv.mulVec ((predictorCausalCovariance E X C).mulVec β)
        + sigmaInv.mulVec (contextCrossCovVector E X h) := by
  unfold optimalWeightsFromMoments
  rw [crossCovVector_decomposition]
  simpa [Pi.add_apply] using
    matrix_mulVec_add sigmaInv ((predictorCausalCovariance E X C).mulVec β) (contextCrossCovVector E X h)

theorem secondMoment_quadratic_form
    (E : ExpFunctional Ω) (X : Ω → J → ℝ) (u : J → ℝ) :
    E (fun ω => (dot u (X ω)) ^ 2)
      = dot u ((secondMomentMatrix E X).mulVec u) := by
  have h_expand :
      (fun ω => (dot u (X ω)) ^ 2)
        = ∑ i, ∑ j, (u i * u j) • (fun ω => X ω i * X ω j) := by
    funext ω
    simp [dot, pow_two, Finset.sum_mul_sum, smul_eq_mul, mul_assoc, mul_left_comm, mul_comm]
  rw [h_expand, ExpFunctional.eval_sum]
  rw [show (∑ i, E (∑ j, (u i * u j) • fun ω => X ω i * X ω j))
        = ∑ i, ∑ j, E ((u i * u j) • fun ω => X ω i * X ω j) by
        apply Finset.sum_congr rfl
        intro i hi
        rw [ExpFunctional.eval_sum]]
  rw [show (∑ i, ∑ j, E ((u i * u j) • fun ω => X ω i * X ω j))
        = ∑ i, ∑ j, (u i * u j) * E (fun ω => X ω i * X ω j) by
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro j hj
        rw [E.smul_eval]]
  unfold dot secondMomentMatrix
  simp [Matrix.mulVec, dotProduct]
  apply Finset.sum_congr rfl
  intro i hi
  calc
    ∑ x, u i * u x * E (fun ω => X ω i * X ω x)
      = u i * ∑ x, u x * E (fun ω => X ω i * X ω x) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro x hx
          ring
    _ = u i * ∑ x, E (fun ω => X ω i * X ω x) * u x := by
          apply congrArg (fun t => u i * t)
          apply Finset.sum_congr rfl
          intro x hx
          ring

theorem secondMoment_eq_covariance_of_centered
    (E : ExpFunctional Ω) (X : Ω → J → ℝ)
    (hcentered : ∀ i, E (fun ω => X ω i) = 0) :
    secondMomentMatrix E X = covarianceMatrix E X := by
  ext i j
  unfold secondMomentMatrix covarianceMatrix
  simp [covariance_eq_expect_mul_sub_means, hcentered]

theorem master_transport_theorem
    (E : ExpFunctional Ω)
    (X : Ω → J → ℝ) (Y : Ω → ℝ)
    (wStar w : J → ℝ)
    (hnormal : ∀ i, E (fun ω => X ω i * (Y ω - dot wStar (X ω))) = 0)
    (hcentered : ∀ i, E (fun ω => X ω i) = 0) :
    expMse E Y (linScore w X)
      = expMse E Y (linScore wStar X)
        + dot (fun i => w i - wStar i)
            ((covarianceMatrix E X).mulVec (fun i => w i - wStar i)) := by
  have hdecomp :=
    mse_transport_decomposition_general E X Y wStar w hnormal
  have hquad :
      E (fun ω => (dot (fun i => w i - wStar i) (X ω)) ^ 2)
        = dot (fun i => w i - wStar i)
            ((covarianceMatrix E X).mulVec (fun i => w i - wStar i)) := by
    rw [← secondMoment_eq_covariance_of_centered E X hcentered]
    exact secondMoment_quadratic_form E X (fun i => w i - wStar i)
  unfold expMse linScore
  simpa using hdecomp.trans (by rw [hquad])

theorem expected_coordinate_dot_eq_covariance_mulVec
    (E : ExpFunctional Ω)
    (X : Ω → J → ℝ) (w : J → ℝ)
    (i : J)
    (hcentered : ∀ j, E (fun ω => X ω j) = 0) :
    E (fun ω => X ω i * dot w (X ω))
      = ((covarianceMatrix E X).mulVec w) i := by
  have h_expand :
      (fun ω => X ω i * dot w (X ω))
        = ∑ j, (w j) • (fun ω => X ω i * X ω j) := by
    funext ω
    simp [dot, Finset.mul_sum, smul_eq_mul, mul_assoc, mul_left_comm, mul_comm]
  rw [h_expand, ExpFunctional.eval_sum]
  rw [show (∑ j, E ((w j) • fun ω => X ω i * X ω j))
        = ∑ j, w j * E (fun ω => X ω i * X ω j) by
        apply Finset.sum_congr rfl
        intro j hj
        rw [E.smul_eval]]
  unfold covarianceMatrix
  simp [Matrix.mulVec, dotProduct, covariance_eq_expect_mul_sub_means, hcentered]
  apply Finset.sum_congr rfl
  intro j hj
  ring

theorem optimalWeightsFromMoments_normal_equations
    (sigmaInv : Matrix J J ℝ)
    (E : ExpFunctional Ω)
    (X : Ω → J → ℝ) (Y : Ω → ℝ)
    (hcentered : ∀ i, E (fun ω => X ω i) = 0)
    (hsigmaInv : covarianceMatrix E X * sigmaInv = 1) :
    ∀ i,
      E
        (fun ω =>
          X ω i *
            (Y ω - dot (optimalWeightsFromMoments sigmaInv E X Y) (X ω))) = 0 := by
  intro i
  have hxy :
      E (fun ω => X ω i * Y ω) = crossCovVector E X Y i := by
    unfold crossCovVector
    rw [covariance_eq_expect_mul_sub_means, hcentered]
    ring
  have hpred :
      E
        (fun ω =>
          X ω i * dot (optimalWeightsFromMoments sigmaInv E X Y) (X ω))
        = ((covarianceMatrix E X).mulVec (optimalWeightsFromMoments sigmaInv E X Y)) i := by
    exact expected_coordinate_dot_eq_covariance_mulVec E X
      (optimalWeightsFromMoments sigmaInv E X Y) i hcentered
  have hw :
      (covarianceMatrix E X).mulVec (optimalWeightsFromMoments sigmaInv E X Y)
        = crossCovVector E X Y := by
    unfold optimalWeightsFromMoments
    have hmul := Matrix.mulVec_mulVec (crossCovVector E X Y) (covarianceMatrix E X) sigmaInv
    rw [hsigmaInv, Matrix.one_mulVec] at hmul
    simpa using hmul
  have hsub :
      (fun ω =>
        X ω i * (Y ω - dot (optimalWeightsFromMoments sigmaInv E X Y) (X ω)))
        = (fun ω => X ω i * Y ω)
          - (fun ω =>
              X ω i * dot (optimalWeightsFromMoments sigmaInv E X Y) (X ω)) := by
    funext ω
    simp [Pi.sub_apply]
    ring
  rw [hsub, E.eval_sub, hxy, hpred, hw]
  ring

theorem master_transport_theorem_closed_form
    (sigmaInv : Matrix J J ℝ)
    (E : ExpFunctional Ω)
    (X : Ω → J → ℝ) (Y : Ω → ℝ)
    (w : J → ℝ)
    (hcentered : ∀ i, E (fun ω => X ω i) = 0)
    (hsigmaInv : covarianceMatrix E X * sigmaInv = 1) :
    expMse E Y (linScore w X)
      = expMse E Y (linScore (optimalWeightsFromMoments sigmaInv E X Y) X)
        + dot (fun i => w i - optimalWeightsFromMoments sigmaInv E X Y i)
            ((covarianceMatrix E X).mulVec
              (fun i => w i - optimalWeightsFromMoments sigmaInv E X Y i)) := by
  apply master_transport_theorem E X Y (optimalWeightsFromMoments sigmaInv E X Y) w
  · exact optimalWeightsFromMoments_normal_equations sigmaInv E X Y hcentered hsigmaInv
  · exact hcentered

end MasterTransport

section ScalarSummary

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

theorem scalar_summary_insufficient_linear
    (f A : V →ₗ[ℝ] ℝ)
    (h : ∃ η : V, f η = 0 ∧ A η ≠ 0) :
    ∀ θ : V, ∃ θ' : V, f θ' = f θ ∧ A θ' ≠ A θ := by
  intro θ
  rcases h with ⟨η, hηf, hηA⟩
  refine ⟨θ + η, ?_, ?_⟩
  · rw [LinearMap.map_add, hηf, add_zero]
  · intro hEq
    have hmap : A (θ + η) = A θ + A η := by
      rw [LinearMap.map_add]
    apply hηA
    linarith [hEq, hmap]

theorem scalar_summary_factorization_of_kernel_inclusion
    (f A : V →ₗ[ℝ] ℝ)
    (hker : ∀ η : V, f η = 0 → A η = 0) :
    ∃ c : ℝ, A = c • f := by
  by_cases hf : f = 0
  · refine ⟨0, ?_⟩
    ext θ
    have hAθ : A θ = 0 := by
      apply hker θ
      simpa [hf]
    simp [hf, hAθ]
  · have hnonzero : ∃ v : V, f v ≠ 0 := by
      by_contra hnone
      push_neg at hnone
      apply hf
      ext v
      exact hnone v
    rcases hnonzero with ⟨v, hv⟩
    refine ⟨A v / f v, ?_⟩
    ext θ
    let η : V := θ - (f θ / f v) • v
    have hfη : f η = 0 := by
      dsimp [η]
      rw [LinearMap.map_sub, LinearMap.map_smul, smul_eq_mul]
      field_simp [hv]
      ring
    have hAη : A η = 0 := hker η hfη
    have hAeq : A θ = (f θ / f v) * A v := by
      dsimp [η] at hAη
      rw [LinearMap.map_sub, LinearMap.map_smul, smul_eq_mul] at hAη
      linarith
    calc
      A θ = (f θ / f v) * A v := hAeq
      _ = (A v / f v) * f θ := by
            field_simp [hv]
      _ = ((A v / f v) • f) θ := by
            simp

theorem exists_kernel_witness_of_not_scalar_factorization
    (f A : V →ₗ[ℝ] ℝ)
    (hnot : ¬ ∃ c : ℝ, A = c • f) :
    ∃ η : V, f η = 0 ∧ A η ≠ 0 := by
  by_contra hcontra
  push_neg at hcontra
  exact hnot (scalar_summary_factorization_of_kernel_inclusion f A hcontra)

theorem scalar_summary_insufficient_of_not_scalar_factorization
    (f A : V →ₗ[ℝ] ℝ)
    (hnot : ¬ ∃ c : ℝ, A = c • f) :
    ∀ θ : V, ∃ θ' : V, f θ' = f θ ∧ A θ' ≠ A θ := by
  exact scalar_summary_insufficient_linear f A
    (exists_kernel_witness_of_not_scalar_factorization f A hnot)

end ScalarSummary

section TraitTransport

variable {J L : Type*}
variable [Fintype J] [DecidableEq J] [Fintype L] [DecidableEq L]

def transportedCovariance (w : J → ℝ) (K : J → L → ℝ) (β : L → ℝ) : ℝ :=
  ∑ j, ∑ l, w j * K j l * β l

def locusTerm (w : J → ℝ) (K : J → L → ℝ) (β : L → ℝ) (l : L) : ℝ :=
  (∑ j, w j * K j l) * β l

theorem transported_covariance_decomposes
    (w : J → ℝ) (K : J → L → ℝ) (β : L → ℝ) :
    transportedCovariance w K β = ∑ l, locusTerm w K β l := by
  unfold transportedCovariance locusTerm
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro l hl
  simpa [mul_assoc, mul_left_comm, mul_comm] using
    (Finset.sum_mul (s := Finset.univ) (f := fun j => w j * K j l) (a := β l)).symm

theorem normalized_transport_as_weighted_average
    (aT τ : L → ℝ) :
    (∑ l, aT l * τ l) / (∑ l, aT l)
      = ∑ l, (aT l / (∑ m, aT m)) * τ l := by
  rw [div_eq_mul_inv, mul_comm, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro l hl
  rw [div_eq_mul_inv]
  ring

def baselineWeight (aT : L → ℝ) (l : L) : ℝ :=
  aT l / (∑ m, aT m)

def transportFactor (aQ aT : L → ℝ) (l : L) : ℝ :=
  aQ l / aT l

theorem normalized_transport_from_factors
    (aQ aT : L → ℝ)
    (hbase : ∀ l, aT l ≠ 0) :
    (∑ l, aQ l) / (∑ l, aT l)
      = ∑ l, baselineWeight aT l * transportFactor aQ aT l := by
  unfold baselineWeight transportFactor
  rw [← normalized_transport_as_weighted_average aT (fun l => aQ l / aT l)]
  apply congrArg (fun z => z / (∑ m, aT m))
  apply Finset.sum_congr rfl
  intro l hl
  field_simp [hbase l]

theorem normalized_transport_constant_factor
    (aT τ : L → ℝ) (φ : ℝ)
    (hden : ∑ m, aT m ≠ 0)
    (hτ : ∀ l, τ l = φ) :
    (∑ l, aT l * τ l) / (∑ l, aT l)
      = φ := by
  have hsum :
      ∑ l, aT l * τ l = φ * ∑ l, aT l := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro l hl
    rw [hτ l]
    ring
  rw [hsum]
  field_simp [hden]

end TraitTransport

def explainableFraction (between total : ℝ) : ℝ := between / total

section NoiseFloor

theorem explainable_fraction_bound_of_noise_floor
    (between total within noiseFloor : ℝ)
    (htotal : total = between + within)
    (htotal_pos : 0 < total)
    (hbetween_nonneg : 0 ≤ between)
    (hnoise_nonneg : 0 ≤ noiseFloor)
    (hnoise_le : noiseFloor ≤ within) :
    explainableFraction between total
      ≤ between / (between + noiseFloor) := by
  unfold explainableFraction
  by_cases hbetween_zero : between = 0
  · simp [hbetween_zero]
  · have hbetween_pos : 0 < between := lt_of_le_of_ne hbetween_nonneg (by simpa [eq_comm] using hbetween_zero)
    have hden_pos : 0 < between + noiseFloor := by
      linarith
    rw [htotal]
    have hother_pos : 0 < between + within := by
      linarith
    have hden_le : between + noiseFloor ≤ between + within := by
      linarith
    have hw : between + within ≠ 0 := by linarith
    have hn : between + noiseFloor ≠ 0 := by linarith
    field_simp [hw, hn]
    nlinarith

theorem explainable_fraction_bound_of_gaussian_floor
    (between total within sigma4 : ℝ)
    (htotal : total = between + within)
    (htotal_pos : 0 < total)
    (hbetween_nonneg : 0 ≤ between)
    (hsigma4_nonneg : 0 ≤ sigma4)
    (hgauss_floor : 2 * sigma4 ≤ within) :
    explainableFraction between total
      ≤ between / (between + 2 * sigma4) := by
  apply explainable_fraction_bound_of_noise_floor between total within (2 * sigma4)
    htotal htotal_pos hbetween_nonneg
  · nlinarith
  · exact hgauss_floor

end NoiseFloor

section MeasureTheoreticNoiseFloor

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}
variable {μ : Measure[mΩ] Ω} [IsProbabilityMeasure μ]
variable {m : MeasurableSpace Ω}

def conditionalMean (μ : Measure[mΩ] Ω) (m : MeasurableSpace Ω) (L : Ω → ℝ) : Ω → ℝ :=
  μ[L | m]

def conditionalVariance (μ : Measure[mΩ] Ω) (m : MeasurableSpace Ω) (L : Ω → ℝ) : Ω → ℝ :=
  Var[L; μ | m]

theorem total_variance_decomposition_subsigma
    (hm : m ≤ mΩ)
    {L : Ω → ℝ}
    (hL : MemLp L 2 μ) :
    Var[L; μ] = (∫ ω, conditionalVariance μ m L ω ∂μ) + Var[conditionalMean μ m L; μ] := by
  simpa [add_comm] using
    (ProbabilityTheory.integral_condVar_add_variance_condExp (μ := μ) (m := m) hm hL).symm

theorem explainable_fraction_bound_of_conditional_noise_floor
    (hm : m ≤ mΩ)
    {L noiseFloor : Ω → ℝ}
    (hL : MemLp L 2 μ)
    (hVar_pos : 0 < Var[L; μ])
    (hNoise_int : Integrable noiseFloor μ)
    (hNoise_nonneg : 0 ≤ μ[noiseFloor])
    (hNoise_le : noiseFloor ≤ᵐ[μ] conditionalVariance μ m L) :
    explainableFraction (Var[conditionalMean μ m L; μ]) (Var[L; μ])
      ≤ Var[conditionalMean μ m L; μ] / (Var[conditionalMean μ m L; μ] + μ[noiseFloor]) := by
  have hwithin_ge : μ[noiseFloor] ≤ ∫ ω, conditionalVariance μ m L ω ∂μ := by
    exact integral_mono_ae hNoise_int
      (ProbabilityTheory.integrable_condVar (X := L) (μ := μ) (m := m)) hNoise_le
  have htotal :
      Var[L; μ] = Var[conditionalMean μ m L; μ] + ∫ ω, conditionalVariance μ m L ω ∂μ := by
    rw [add_comm]
    exact total_variance_decomposition_subsigma (μ := μ) (m := m) hm hL
  have hbetween_nonneg : 0 ≤ Var[conditionalMean μ m L; μ] := by
    exact ProbabilityTheory.variance_nonneg _ _
  exact explainable_fraction_bound_of_noise_floor
    (between := Var[conditionalMean μ m L; μ])
    (total := Var[L; μ])
    (within := ∫ ω, conditionalVariance μ m L ω ∂μ)
    (noiseFloor := μ[noiseFloor])
    htotal hVar_pos hbetween_nonneg hNoise_nonneg hwithin_ge

theorem explainable_fraction_bound_of_conditional_gaussian_floor
    (hm : m ≤ mΩ)
    {L sigma4 : Ω → ℝ}
    (hL : MemLp L 2 μ)
    (hVar_pos : 0 < Var[L; μ])
    (hsigma4_int : Integrable sigma4 μ)
    (hsigma4_nonneg : 0 ≤ μ[sigma4])
    (hGaussianFloor : (fun ω => (2 : ℝ) * sigma4 ω) ≤ᵐ[μ] conditionalVariance μ m L) :
    explainableFraction (Var[conditionalMean μ m L; μ]) (Var[L; μ])
      ≤ Var[conditionalMean μ m L; μ] / (Var[conditionalMean μ m L; μ] + 2 * μ[sigma4]) := by
  have hNoise_int : Integrable (fun ω => (2 : ℝ) * sigma4 ω) μ := hsigma4_int.const_mul 2
  have hNoise_eq : μ[fun ω => (2 : ℝ) * sigma4 ω] = (2 : ℝ) * μ[sigma4] := by
    rw [integral_const_mul]
  have hNoise_nonneg : 0 ≤ μ[fun ω => (2 : ℝ) * sigma4 ω] := by
    rw [hNoise_eq]
    nlinarith
  have hbound :=
    explainable_fraction_bound_of_conditional_noise_floor
      (μ := μ) (m := m) hm hL hVar_pos hNoise_int hNoise_nonneg hGaussianFloor
  simpa [hNoise_eq] using hbound

end MeasureTheoreticNoiseFloor

section ContinuousMetrics

variable {Ω : Type*}

theorem mse_from_variance_ratio_corr_bias
    (E : ExpFunctional Ω) (Y S : Ω → ℝ)
    (ρ lam : ℝ)
    (hvarY : 0 < variance E Y)
    (hlam : variance E S = variance E Y * lam)
    (hρ : covariance E Y S = ρ * variance E Y * Real.sqrt lam) :
    expMse E Y S
      = variance E Y * (1 + lam - 2 * ρ * Real.sqrt lam)
        + (bias E Y S) ^ 2 := by
  rw [mse_eq_variance_add_variance_sub_two_cov_add_bias_sq, hlam, hρ]
  ring

end ContinuousMetrics

section BinaryMetrics

structure ConfusionMatrix where
  tp : ℝ
  fp : ℝ
  tn : ℝ
  fn : ℝ
  tp_nonneg : 0 ≤ tp
  fp_nonneg : 0 ≤ fp
  tn_nonneg : 0 ≤ tn
  fn_nonneg : 0 ≤ fn
  mass_one : tp + fp + tn + fn = 1

namespace ConfusionMatrix

def prevalence (c : ConfusionMatrix) : ℝ := c.tp + c.fn

def recallRate (c : ConfusionMatrix) : ℝ := c.tp / (c.tp + c.fn)

def fpr (c : ConfusionMatrix) : ℝ := c.fp / (c.fp + c.tn)

def precision (c : ConfusionMatrix) : ℝ := c.tp / (c.tp + c.fp)

theorem one_sub_prevalence (c : ConfusionMatrix) :
    1 - prevalence c = c.fp + c.tn := by
  unfold prevalence
  linarith [c.mass_one]

theorem prevalence_mul_recall (c : ConfusionMatrix) :
    prevalence c * recallRate c = c.tp := by
  unfold prevalence recallRate
  by_cases h : c.tp + c.fn = 0
  · have htp : c.tp = 0 := by
      linarith [c.tp_nonneg, c.fn_nonneg, h]
    simp [h, htp]
  · field_simp [h]

theorem one_sub_prevalence_mul_fpr (c : ConfusionMatrix) :
    (1 - prevalence c) * fpr c = c.fp := by
  rw [one_sub_prevalence]
  unfold fpr
  by_cases h : c.fp + c.tn = 0
  · have hfp : c.fp = 0 := by
      linarith [c.fp_nonneg, c.tn_nonneg, h]
    simp [h, hfp]
  · field_simp [h]

theorem precision_eq_prevalence_recall_fpr (c : ConfusionMatrix) :
    precision c =
      (prevalence c * recallRate c) /
        (prevalence c * recallRate c + (1 - prevalence c) * fpr c) := by
  rw [prevalence_mul_recall, one_sub_prevalence_mul_fpr]
  unfold precision
  rfl

theorem constant_precision_construction
    {π p r : ℝ}
    (hnum : π * r ≠ 0)
    (hpi : 1 - π ≠ 0)
    (hp : p ≠ 0) :
    (let f := π * r * (1 - p) / ((1 - π) * p);
      (π * r) / (π * r + (1 - π) * f) = p) := by
  dsimp
  have hπ : π ≠ 0 := by
    intro h
    apply hnum
    simp [h]
  have hr : r ≠ 0 := by
    intro h
    apply hnum
    simp [h]
  field_simp [hpi, hp, hπ, hr]
  ring

end ConfusionMatrix

end BinaryMetrics

end

end Calibrator
