/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.PCCorrectability.Core
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace Descent

/-!
# The ridge that keeps the projection solve factorizable

`map/project.rs` projects samples onto a fitted PC basis by solving weighted
normal equations per sample.  `build_dense_lower_info_matrix` assembles the
information matrix and adds `WLS_RIDGE = 1e-5` to its diagonal;
`factorize_spd_lower_in_place` then runs a Cholesky factorization and **returns
`false`** the moment a pivot is not finite or not strictly positive, which sends
the caller down a fallback path.

The information matrix is a Gram matrix, so it is positive semidefinite but not
necessarily definite: with fewer informative markers than components, or with a
sample missing every variant loading on some axis, it is singular and the
factorization has no positive pivot to find.  The ridge is what makes the solve
well posed, and `1e-5` is a number in the source with nothing anywhere saying
what it has to satisfy.

This module states what it has to satisfy: **strictly positive**.  That is the
whole requirement, and the results below are the reason.

This is deliberately narrow.  It is not a model of the projection solve -- the
missing-axis renormalization, the sparse/dense missingness split and the
per-sample downdate are not formalized, and saying so is more useful than a
table row claiming otherwise.  What is here is the one invariant the shipped
fallback branch exists to protect.
-/

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The quadratic form of a matrix, as the projection solve uses it. -/
noncomputable def infoQuadraticForm (A : Matrix n n ℝ) (x : n → ℝ) : ℝ :=
  x ⬝ᵥ A.mulVec x

/-- The ridge-regularized information matrix the solver actually factorizes. -/
noncomputable def ridgedInfoMatrix (A : Matrix n n ℝ) (ridge : ℝ) : Matrix n n ℝ :=
  A + ridge • (1 : Matrix n n ℝ)

/-- Adding `ridge` to the diagonal adds exactly `ridge * ‖x‖²` to the form. -/
theorem infoQuadraticForm_ridged (A : Matrix n n ℝ) (ridge : ℝ) (x : n → ℝ) :
    infoQuadraticForm (ridgedInfoMatrix A ridge) x =
      infoQuadraticForm A x + ridge * ∑ i, x i ^ 2 := by
  unfold infoQuadraticForm ridgedInfoMatrix
  rw [Matrix.add_mulVec, dotProduct_add]
  congr 1
  rw [Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_smul]
  simp [dotProduct, Finset.mul_sum, pow_two]

/-- **The ridge bound.**  On a positive-semidefinite information matrix -- which
a Gram matrix always is -- the regularized form is at least `ridge * ‖x‖²`.

This is the inequality the Cholesky loop needs: it is what stops a pivot from
reaching zero on a rank-deficient design. -/
theorem ridged_infoQuadraticForm_lower_bound
    (A : Matrix n n ℝ) (ridge : ℝ) (x : n → ℝ)
    (hA : 0 ≤ infoQuadraticForm A x) :
    ridge * (∑ i, x i ^ 2) ≤ infoQuadraticForm (ridgedInfoMatrix A ridge) x := by
  rw [infoQuadraticForm_ridged]
  linarith

/-- **A strictly positive ridge makes the solve strictly definite.**  For any
nonzero direction the regularized form is strictly positive, so the matrix the
solver factorizes is positive definite and its Cholesky pivots are strictly
positive.  `factorize_spd_lower_in_place` therefore cannot take its
`diag <= 0.0` failure branch for arithmetic reasons -- only for numerical ones.

The hypothesis is `0 < ridge`, nothing more.  `1e-5` is one admissible choice
and this says so; it also says that `0` is not, which is the content the source
constant carries and does not state. -/
theorem ridged_infoQuadraticForm_pos
    (A : Matrix n n ℝ) (ridge : ℝ) (hridge : 0 < ridge) (x : n → ℝ) (hx : x ≠ 0)
    (hA : 0 ≤ infoQuadraticForm A x) :
    0 < infoQuadraticForm (ridgedInfoMatrix A ridge) x := by
  have hnorm : 0 < ∑ i, x i ^ 2 := by
    rcases Function.ne_iff.mp hx with ⟨j, hj⟩
    refine Finset.sum_pos' (fun i _ ↦ sq_nonneg (x i)) ⟨j, Finset.mem_univ j, ?_⟩
    exact sq_pos_of_ne_zero (by simpa using hj)
  have hbound := ridged_infoQuadraticForm_lower_bound A ridge x hA
  nlinarith [mul_pos hridge hnorm]

/-- **A zero ridge does not.**  With `ridge = 0` the regularized matrix is the
information matrix itself, so a rank-deficient design keeps a null direction and
the factorization has a zero pivot to find.  This is the failure the constant in
`map/project.rs` is there to prevent, stated rather than assumed. -/
theorem ridged_infoQuadraticForm_zero_ridge_degenerate
    (A : Matrix n n ℝ) (x : n → ℝ) (hnull : infoQuadraticForm A x = 0) :
    infoQuadraticForm (ridgedInfoMatrix A 0) x = 0 := by
  rw [infoQuadraticForm_ridged, hnull]
  ring

/-- **The ridge floor, at the direction PC correction leaves behind.**

`PCCorrectionModel.residualBiasEnergy` is the squared magnitude of the
confounding that survives top-PC residualization, and it is a sum of squares --
exactly the quantity the ridge bound is stated over.  So the projection solve's
regularized form is at least `ridge` times the confounding energy the correction
did not remove: the direction the solve still has to resolve is the one the
ridge guarantees a floor on.

This also ties this module to `PCCorrectability.Core`.  A module whose theorems
only ever mention its own definitions cannot be contradicted by anything else in
the corpus, and a wrong definition sheltered there is consistent with everything
-- so the relation is stated rather than left implicit. -/
theorem ridged_form_dominates_residualBiasEnergy
    (m : PCCorrectionModel) (bias : Fin m.p → ℝ)
    (A : Matrix (Fin m.p) (Fin m.p) ℝ) (ridge : ℝ)
    (hA : 0 ≤ infoQuadraticForm A (m.removeTopPCs bias)) :
    ridge * m.residualBiasEnergy bias ≤
      infoQuadraticForm (ridgedInfoMatrix A ridge) (m.removeTopPCs bias) := by
  have hbound :=
    ridged_infoQuadraticForm_lower_bound A ridge (m.removeTopPCs bias) hA
  unfold PCCorrectionModel.residualBiasEnergy
  exact hbound

end Descent
