/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.PortabilityMasterTheorem

assert_below Descent.Decision Descent.Program

/-!
# Exact finite-cohort evaluation operators

The group evaluation procedure of the source study is written here as an exact matrix operator
on a finite cohort `Fin n`, and its report is computed exactly.  The report is the partial
squared correlation `(zᵀr)² / ((zᵀz)(rᵀr))` of TQ Theorem 4.3 (4.4), UPT Theorem 8.2 (8.3),
DC Proposition 7.1 (7.2) and PL Proposition 6.1 (6.1).  It is proved here to equal the angular
quadratic form `rᵀΠ_z r / rᵀr` with `Π_z = zzᵀ/zᵀz`, and separately to equal the ratio of the
reduction in residual sum of squares to the reduced residual sum of squares, where both sums of
squares are the genuine least-squares minima over their model spaces
(`residual_quadForm_isLeast`).  The degenerate cases the manuscripts single out are also proved:
a zero residual score contributes exactly zero reduction, and the report always lies in `[0,1]`
on its domain.

Every projection property is a hypothesis in the form of an equation between explicit matrices
(`Pᵀ = P`, `P * P = P`), never a named predicate, and each such hypothesis is discharged for the
concrete matrices built here: `rankOneProj_transpose` and `rankOneProj_mul_self` for `Π_z`, and
`augmentedProj_transpose` and `augmentedProj_mul_self` for the score-augmented nuisance
projection.  Singular nuisance designs are therefore allowed: nothing below inverts `WᵀW`.

Built on `Descent.Foundations.dot` and on the empirical cohort expectation `uniformExp` of
`Descent.Portability.PortabilityMasterTheorem`, to which `binMeanSquaredError_eq_uniformExp`
ties the bin mean squared error.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.CohortEvaluationOperators

open Foundations Matrix

noncomputable section

variable {n m : ℕ}

/-! ## Bilinear vocabulary -/

/-- The quadratic form `vᵀ B v`, written through the corpus inner sum `Foundations.dot`. -/
def quadForm (B : Matrix (Fin n) (Fin n) ℝ) (v : Fin n → ℝ) : ℝ :=
  dot v (B.mulVec v)

/-- The corpus inner sum is the Mathlib dot product. -/
theorem dot_eq_dotProduct (x y : Fin n → ℝ) : dot x y = dotProduct x y := rfl

/-- The inner sum is symmetric. -/
theorem dot_comm (x y : Fin n → ℝ) : dot x y = dot y x := by
  simp only [dot, Descent.Core.innerSum]
  exact Finset.sum_congr rfl fun _ _ ↦ mul_comm _ _

/-- The inner sum of a vector with itself is nonnegative. -/
theorem dot_self_nonneg (x : Fin n → ℝ) : 0 ≤ dot x x := by
  simp only [dot, Descent.Core.innerSum]
  exact Finset.sum_nonneg fun _ _ ↦ mul_self_nonneg _

/-- Additivity of the inner sum in the left slot, in `Pi` form. -/
theorem dot_add_left' (x y z : Fin n → ℝ) : dot (x + y) z = dot x z + dot y z :=
  dot_add_left x y z

/-- Scalars pull out of the left slot of the inner sum. -/
theorem dot_smul_left (c : ℝ) (x y : Fin n → ℝ) : dot (c • x) y = c * dot x y := by
  simp only [dot, Descent.Core.innerSum, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ ↦ by ring

/-- Scalars pull out of the right slot of the inner sum. -/
theorem dot_smul_right (c : ℝ) (x y : Fin n → ℝ) : dot x (c • y) = c * dot x y := by
  rw [dot_comm, dot_smul_left, dot_comm]

/-- Moving a matrix across the inner sum transposes it. -/
theorem dot_mulVec_left (A : Matrix (Fin m) (Fin n) ℝ) (u : Fin m → ℝ) (v : Fin n → ℝ) :
    dot u (A.mulVec v) = dot (Aᵀ.mulVec u) v := by
  have hl : dot u (A.mulVec v) = ∑ i, ∑ j, u i * (A i j * v j) := by
    simp [dot, Descent.Core.innerSum, Matrix.mulVec, dotProduct, Finset.mul_sum]
  have hr : dot (Aᵀ.mulVec u) v = ∑ j, ∑ i, A i j * u i * v j := by
    simp [dot, Descent.Core.innerSum, Matrix.mulVec, dotProduct, Finset.sum_mul,
      Matrix.transpose_apply]
  rw [hl, hr, Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ ↦ Finset.sum_congr rfl fun _ _ ↦ by ring

/-- The squared length of `A v` is the quadratic form of `AᵀA`. -/
theorem dot_mulVec_self (A : Matrix (Fin m) (Fin n) ℝ) (v : Fin n → ℝ) :
    dot (A.mulVec v) (A.mulVec v) = quadForm (Aᵀ * A) v := by
  have h : quadForm (Aᵀ * A) v = dot v (Aᵀ.mulVec (A.mulVec v)) := by
    rw [quadForm, Matrix.mulVec_mulVec]
  rw [h, dot_comm v]
  exact dot_mulVec_left A (A.mulVec v) v

/-- The quadratic form is additive in the matrix. -/
theorem quadForm_sub (A B : Matrix (Fin n) (Fin n) ℝ) (v : Fin n → ℝ) :
    quadForm (A - B) v = quadForm A v - quadForm B v := by
  simp only [quadForm, Matrix.sub_mulVec]
  exact dot_sub_right' v (A.mulVec v) (B.mulVec v)

/-- The quadratic form is homogeneous of degree two in the vector. -/
theorem quadForm_smul (B : Matrix (Fin n) (Fin n) ℝ) (c : ℝ) (v : Fin n → ℝ) :
    quadForm B (c • v) = c ^ 2 * quadForm B v := by
  simp only [quadForm, Matrix.mulVec_smul, dot_smul_left, dot_smul_right]
  ring

/-- The identity matrix has the squared length as its quadratic form. -/
theorem quadForm_one (v : Fin n → ℝ) : quadForm (1 : Matrix (Fin n) (Fin n) ℝ) v = dot v v := by
  rw [quadForm, Matrix.one_mulVec]

/-- Polarization of the quadratic form along a sum. -/
theorem quadForm_add (B : Matrix (Fin n) (Fin n) ℝ) (u v : Fin n → ℝ) :
    quadForm B (u + v)
      = quadForm B u + dot u (B.mulVec v) + dot v (B.mulVec u) + quadForm B v := by
  simp only [quadForm, Matrix.mulVec_add]
  rw [dot_add_left' u v (B.mulVec u + B.mulVec v), dot_add_right u (B.mulVec u) (B.mulVec v),
    dot_add_right v (B.mulVec u) (B.mulVec v)]
  ring

/-- Evaluating a quadratic form on standard basis vectors reads off a matrix entry. -/
theorem dot_single_mulVec_single (D : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) :
    dot (Pi.single i (1 : ℝ)) (D.mulVec (Pi.single j 1)) = D i j := by
  rw [Matrix.mulVec_single_one]
  simp only [dot, Descent.Core.innerSum, Pi.single_apply]
  rw [Finset.sum_eq_single i]
  · simp
  · intro b _ hb
    simp [hb]
  · intro h
    exact absurd (Finset.mem_univ i) h

/-- A symmetric matrix whose quadratic form vanishes everywhere is the zero matrix.  Testing
basis vectors kills the diagonal and testing their pairwise sums kills the rest. -/
theorem eq_zero_of_quadForm_eq_zero (D : Matrix (Fin n) (Fin n) ℝ) (hD : Dᵀ = D)
    (h : ∀ v : Fin n → ℝ, quadForm D v = 0) : D = 0 := by
  have hsymm : ∀ i j : Fin n, D j i = D i j := by
    intro i j
    have hij := congrFun (congrFun hD i) j
    simpa [Matrix.transpose_apply] using hij
  have hquad : ∀ i : Fin n, quadForm D (Pi.single i (1 : ℝ)) = D i i := fun i ↦
    dot_single_mulVec_single D i i
  ext i j
  have hij := h (Pi.single i 1 + Pi.single j 1)
  rw [quadForm_add, dot_single_mulVec_single, dot_single_mulVec_single, hquad i, hquad j,
    hsymm i j] at hij
  have hi0 : D i i = 0 := by rw [← hquad i]; exact h _
  have hj0 : D j j = 0 := by rw [← hquad j]; exact h _
  simp only [Matrix.zero_apply]
  rw [hi0, hj0] at hij
  linarith

/-- **Quadratic forms determine symmetric matrices.**  This is the step that turns an
"equality for every outcome vector" clause into a matrix identity. -/
theorem quadForm_ext_iff (A B : Matrix (Fin n) (Fin n) ℝ) (hA : Aᵀ = A) (hB : Bᵀ = B) :
    (∀ v : Fin n → ℝ, quadForm A v = quadForm B v) ↔ A = B := by
  constructor
  · intro h
    have hz : A - B = 0 := by
      refine eq_zero_of_quadForm_eq_zero (A - B) ?_ ?_
      · rw [Matrix.transpose_sub, hA, hB]
      · intro v
        rw [quadForm_sub, h v, sub_self]
    exact sub_eq_zero.mp hz
  · intro h v
    rw [h]

/-! ## Orthogonal projections and residual makers -/

/-- The residual maker `M_P = I - P` of a projection matrix. -/
def residualMaker (P : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  1 - P

/-- The residual maker of a symmetric matrix is symmetric. -/
theorem residualMaker_transpose (P : Matrix (Fin n) (Fin n) ℝ) (hs : Pᵀ = P) :
    (residualMaker P)ᵀ = residualMaker P := by
  rw [residualMaker, Matrix.transpose_sub, Matrix.transpose_one, hs]

/-- The residual maker of an idempotent matrix is idempotent. -/
theorem residualMaker_mul_self (P : Matrix (Fin n) (Fin n) ℝ) (hi : P * P = P) :
    residualMaker P * residualMaker P = residualMaker P := by
  simp only [residualMaker, sub_mul, mul_sub, Matrix.one_mul, Matrix.mul_one, hi]
  abel

/-- A residual maker annihilates its own projection on the right. -/
theorem residualMaker_mul (P : Matrix (Fin n) (Fin n) ℝ) (hi : P * P = P) :
    residualMaker P * P = 0 := by
  simp only [residualMaker, sub_mul, Matrix.one_mul, hi, sub_self]

/-- A projection annihilates its own residual maker on the right. -/
theorem mul_residualMaker (P : Matrix (Fin n) (Fin n) ℝ) (hi : P * P = P) :
    P * residualMaker P = 0 := by
  simp only [residualMaker, mul_sub, Matrix.mul_one, hi, sub_self]

/-- The quadratic form of a symmetric idempotent matrix is the squared length of the image. -/
theorem quadForm_proj_eq_sq_norm (P : Matrix (Fin n) (Fin n) ℝ) (hs : Pᵀ = P)
    (hi : P * P = P) (y : Fin n → ℝ) :
    quadForm P y = dot (P.mulVec y) (P.mulVec y) := by
  rw [dot_mulVec_self, hs, hi]

/-- The quadratic form of an orthogonal projection is nonnegative. -/
theorem quadForm_proj_nonneg (P : Matrix (Fin n) (Fin n) ℝ) (hs : Pᵀ = P)
    (hi : P * P = P) (y : Fin n → ℝ) : 0 ≤ quadForm P y := by
  rw [quadForm_proj_eq_sq_norm P hs hi y]
  exact dot_self_nonneg _

/-- An orthogonal projection may be moved onto one slot of an inner sum. -/
theorem dot_proj_mulVec (Q : Matrix (Fin n) (Fin n) ℝ) (hs : Qᵀ = Q) (hi : Q * Q = Q)
    (x y : Fin n → ℝ) : dot (Q.mulVec x) (Q.mulVec y) = dot (Q.mulVec x) y := by
  rw [dot_mulVec_left Q (Q.mulVec x) y, hs, Matrix.mulVec_mulVec, hi]

/-- **The residual sum of squares of an orthogonal projection is the least-squares minimum.**
The set is the achievable sums of squares `‖y - v‖²` over the fitted values `v` fixed by the
projection, that is over its model space; the least such value is `yᵀ M_P y`.  This is what
makes the "reduction in residual sum of squares" below an actual regression statement rather
than a name for an algebraic difference. -/
theorem residual_quadForm_isLeast (P : Matrix (Fin n) (Fin n) ℝ) (hs : Pᵀ = P)
    (hi : P * P = P) (y : Fin n → ℝ) :
    IsLeast {t : ℝ | ∃ v : Fin n → ℝ, P.mulVec v = v ∧ t = dot (y - v) (y - v)}
      (quadForm (residualMaker P) y) := by
  have hMs : (residualMaker P)ᵀ = residualMaker P := residualMaker_transpose P hs
  have hMi : residualMaker P * residualMaker P = residualMaker P := residualMaker_mul_self P hi
  have hq : quadForm (residualMaker P) y
      = dot ((residualMaker P).mulVec y) ((residualMaker P).mulVec y) := by
    rw [dot_mulVec_self, hMs, hMi]
  have hsplit : ∀ v : Fin n → ℝ, y - v = (residualMaker P).mulVec y + (P.mulVec y - v) := by
    intro v
    funext i
    simp [residualMaker, Matrix.sub_mulVec, Matrix.one_mulVec]
  constructor
  · refine ⟨P.mulVec y, ?_, ?_⟩
    · rw [Matrix.mulVec_mulVec, hi]
    · rw [hsplit (P.mulVec y)]
      simp only [sub_self, add_zero]
      exact hq
  · rintro t ⟨v, hv, rfl⟩
    have hcross : dot ((residualMaker P).mulVec y) (P.mulVec y - v) = 0 := by
      have hPv : P.mulVec y - v = P.mulVec (y - v) := by
        rw [Matrix.mulVec_sub, hv]
      rw [hPv, dot_mulVec_left, hs, Matrix.mulVec_mulVec, mul_residualMaker P hi,
        Matrix.zero_mulVec]
      simp [dot, Descent.Core.innerSum]
    have hexp : dot (y - v) (y - v)
        = dot ((residualMaker P).mulVec y) ((residualMaker P).mulVec y)
          + dot (P.mulVec y - v) (P.mulVec y - v) := by
      rw [hsplit v, dot_add_left', dot_add_right, dot_add_right, hcross,
        dot_comm (P.mulVec y - v) ((residualMaker P).mulVec y), hcross]
      ring
    rw [hexp, hq]
    have hnn : 0 ≤ dot (P.mulVec y - v) (P.mulVec y - v) := dot_self_nonneg _
    linarith

/-! ## The rank-one angular projection -/

/-- The rank-one angular projection `Π_z = z zᵀ / (zᵀ z)` onto the residual score direction. -/
def rankOneProj (z : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  (dot z z)⁻¹ • Matrix.vecMulVec z z

/-- The outer product of a vector with itself is idempotent up to its squared length. -/
theorem vecMulVec_mul_self (z : Fin n → ℝ) :
    Matrix.vecMulVec z z * Matrix.vecMulVec z z = (dot z z) • Matrix.vecMulVec z z := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.vecMulVec_apply, Matrix.smul_apply, smul_eq_mul,
    dot, Descent.Core.innerSum, Finset.sum_mul]
  exact Finset.sum_congr rfl fun _ _ ↦ by ring

/-- The rank-one angular projection is symmetric. -/
theorem rankOneProj_transpose (z : Fin n → ℝ) : (rankOneProj z)ᵀ = rankOneProj z := by
  ext i j
  simp only [rankOneProj, Matrix.transpose_apply, Matrix.smul_apply, Matrix.vecMulVec_apply,
    smul_eq_mul]
  ring

/-- The rank-one angular projection is idempotent on a nonzero direction. -/
theorem rankOneProj_mul_self (z : Fin n → ℝ) (hz : dot z z ≠ 0) :
    rankOneProj z * rankOneProj z = rankOneProj z := by
  simp only [rankOneProj, Matrix.smul_mul, Matrix.mul_smul, vecMulVec_mul_self, smul_smul]
  congr 1
  field_simp

/-- Applying the rank-one angular projection to a vector. -/
theorem rankOneProj_mulVec (z v : Fin n → ℝ) :
    (rankOneProj z).mulVec v = ((dot z z)⁻¹ * dot z v) • z := by
  funext i
  have hl : (rankOneProj z).mulVec v i = ∑ j, (dot z z)⁻¹ * (z i * z j) * v j := by
    simp [rankOneProj, Matrix.mulVec, dotProduct, Matrix.vecMulVec_apply]
  have hr : (((dot z z)⁻¹ * dot z v) • z) i = ∑ j, (dot z z)⁻¹ * (z i * z j) * v j := by
    simp only [Pi.smul_apply, smul_eq_mul, dot, Descent.Core.innerSum, Finset.sum_mul,
      Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ ↦ by ring
  rw [hl, hr]

/-- The quadratic form of the rank-one angular projection is the squared inner sum over the
squared length of the direction. -/
theorem quadForm_rankOneProj (z v : Fin n → ℝ) :
    quadForm (rankOneProj z) v = (dot z v) ^ 2 / dot z z := by
  rw [quadForm, rankOneProj_mulVec, dot_smul_right, dot_comm v z, div_eq_inv_mul]
  ring

/-- A zero residual score direction gives the zero angular projection, so it contributes exactly
zero reduction in the residual sum of squares.  This is the case the manuscripts single out:
"when `z = 0` but reduced SSE is positive, the SSE-defined partial `R²` is zero". -/
theorem rankOneProj_zero : rankOneProj (0 : Fin n → ℝ) = 0 := by
  ext i j
  simp [rankOneProj]

/-! ## The exact group report -/

/-- **The group evaluation report.**  TQ (4.4), UPT (8.3), DC (7.2), PL (6.1): the partial
squared correlation of the residualized outcome `r` with the residualized score `z`. -/
def partialR2 (z r : Fin n → ℝ) : ℝ :=
  (dot z r) ^ 2 / (dot z z * dot r r)

/-- **The group report is an angular quadratic form.**  This is the second equality of PL (6.1),
`q̂ = rᵀ Π_z r / rᵀ r`, and it holds with no nondegeneracy hypothesis at all. -/
theorem partialR2_eq_angular_ratio (z r : Fin n → ℝ) :
    partialR2 z r = quadForm (rankOneProj z) r / dot r r := by
  rw [partialR2, quadForm_rankOneProj, div_div]

/-- The score-augmented nuisance projection `P + Π_z` with `z = M_P s` the residual score. -/
def augmentedProj (P : Matrix (Fin n) (Fin n) ℝ) (s : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  P + rankOneProj ((residualMaker P).mulVec s)

/-- The score-augmented nuisance projection is symmetric. -/
theorem augmentedProj_transpose (P : Matrix (Fin n) (Fin n) ℝ) (hs : Pᵀ = P) (s : Fin n → ℝ) :
    (augmentedProj P s)ᵀ = augmentedProj P s := by
  rw [augmentedProj, Matrix.transpose_add, hs, rankOneProj_transpose]

/-- Multiplying an outer product on the left. -/
theorem mul_vecMulVec (A : Matrix (Fin n) (Fin n) ℝ) (x y : Fin n → ℝ) :
    A * Matrix.vecMulVec x y = Matrix.vecMulVec (A.mulVec x) y := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.vecMulVec_apply, Matrix.mulVec, dotProduct, Finset.sum_mul]
  exact Finset.sum_congr rfl fun _ _ ↦ by ring

/-- Multiplying an outer product on the right. -/
theorem vecMulVec_mul (A : Matrix (Fin n) (Fin n) ℝ) (x y : Fin n → ℝ) :
    Matrix.vecMulVec x y * A = Matrix.vecMulVec x (Aᵀ.mulVec y) := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.vecMulVec_apply, Matrix.mulVec, dotProduct,
    Matrix.transpose_apply, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ ↦ by ring

/-- An outer product with a zero factor is the zero matrix. -/
theorem vecMulVec_zero_left (y : Fin n → ℝ) :
    Matrix.vecMulVec (0 : Fin n → ℝ) y = 0 := by
  ext i j
  simp [Matrix.vecMulVec_apply]

/-- The nuisance projection annihilates the rank-one angular projection built on its own
residual score direction. -/
theorem proj_mul_rankOneProj (P : Matrix (Fin n) (Fin n) ℝ) (hi : P * P = P) (s : Fin n → ℝ) :
    P * rankOneProj ((residualMaker P).mulVec s) = 0 := by
  have hPz : P.mulVec ((residualMaker P).mulVec s) = 0 := by
    rw [Matrix.mulVec_mulVec, mul_residualMaker P hi, Matrix.zero_mulVec]
  rw [rankOneProj, Matrix.mul_smul, mul_vecMulVec, hPz, vecMulVec_zero_left, smul_zero]

/-- The rank-one angular projection built on a residual score direction annihilates the
nuisance projection. -/
theorem rankOneProj_mul_proj (P : Matrix (Fin n) (Fin n) ℝ) (hs : Pᵀ = P) (hi : P * P = P)
    (s : Fin n → ℝ) : rankOneProj ((residualMaker P).mulVec s) * P = 0 := by
  have h := proj_mul_rankOneProj P hi s
  have ht := congrArg Matrix.transpose h
  rw [Matrix.transpose_mul, rankOneProj_transpose, hs, Matrix.transpose_zero] at ht
  exact ht

/-- The score-augmented nuisance projection is idempotent. -/
theorem augmentedProj_mul_self (P : Matrix (Fin n) (Fin n) ℝ) (hs : Pᵀ = P) (hi : P * P = P)
    (s : Fin n → ℝ)
    (hz : dot ((residualMaker P).mulVec s) ((residualMaker P).mulVec s) ≠ 0) :
    augmentedProj P s * augmentedProj P s = augmentedProj P s := by
  simp only [augmentedProj, add_mul, mul_add, hi, proj_mul_rankOneProj P hi s,
    rankOneProj_mul_proj P hs hi s, rankOneProj_mul_self _ hz]
  abel

/-- The residual maker of the augmented projection subtracts the angular projection. -/
theorem residualMaker_augmentedProj (P : Matrix (Fin n) (Fin n) ℝ) (s : Fin n → ℝ) :
    residualMaker (augmentedProj P s)
      = residualMaker P - rankOneProj ((residualMaker P).mulVec s) := by
  simp only [residualMaker, augmentedProj]
  abel

/-- **The group report is the relative reduction in residual sum of squares.**  Both sums of
squares are least-squares minima by `residual_quadForm_isLeast`: the denominator over the
nuisance model space and the subtracted term over the score-augmented model space.  This is the
content of the proofs of TQ Theorem 4.3, UPT Theorem 8.2, DC Proposition 7.1 and
PL Proposition 6.1.  The hypotheses are the manuscripts' own domain conditions: a symmetric
idempotent nuisance projection, a nonzero residual score, and a nonzero residual outcome. -/
theorem partialR2_eq_sse_reduction_ratio (P : Matrix (Fin n) (Fin n) ℝ) (hs : Pᵀ = P)
    (hi : P * P = P) (s y : Fin n → ℝ) :
    partialR2 ((residualMaker P).mulVec s) ((residualMaker P).mulVec y)
      = (quadForm (residualMaker P) y - quadForm (residualMaker (augmentedProj P s)) y)
          / quadForm (residualMaker P) y := by
  have hMs : (residualMaker P)ᵀ = residualMaker P := residualMaker_transpose P hs
  have hMi : residualMaker P * residualMaker P = residualMaker P := residualMaker_mul_self P hi
  have hrr : quadForm (residualMaker P) y
      = dot ((residualMaker P).mulVec y) ((residualMaker P).mulVec y) :=
    quadForm_proj_eq_sq_norm _ hMs hMi y
  have hzy : dot ((residualMaker P).mulVec s) y
      = dot ((residualMaker P).mulVec s) ((residualMaker P).mulVec y) :=
    (dot_proj_mulVec (residualMaker P) hMs hMi s y).symm
  rw [residualMaker_augmentedProj, quadForm_sub,
    quadForm_rankOneProj ((residualMaker P).mulVec s) y, hzy, hrr, partialR2]
  ring

/-! ## Domain facts for the group report -/

/-- The group report is nonnegative. -/
theorem partialR2_nonneg (z r : Fin n → ℝ) : 0 ≤ partialR2 z r := by
  rw [partialR2]
  exact div_nonneg (sq_nonneg _) (mul_nonneg (dot_self_nonneg z) (dot_self_nonneg r))

/-- The Cauchy-Schwarz inequality for the corpus inner sum, proved from positive
semidefiniteness of the residual `I - Π_z` rather than assumed. -/
theorem dot_sq_le (z r : Fin n → ℝ) : (dot z r) ^ 2 ≤ dot z z * dot r r := by
  rcases eq_or_ne (dot z z) 0 with hz | hz
  · have hzero : ∀ i, z i = 0 := by
      have hsum : ∑ i, z i * z i = 0 := hz
      intro i
      have := (Finset.sum_eq_zero_iff_of_nonneg
        (fun j _ ↦ mul_self_nonneg (z j))).mp hsum i (Finset.mem_univ i)
      exact mul_self_eq_zero.mp this
    have : dot z r = 0 := by
      simp only [dot, Descent.Core.innerSum]
      exact Finset.sum_eq_zero fun i _ ↦ by rw [hzero i, zero_mul]
    rw [this, hz]
    simp
  · have hpos : 0 < dot z z := lt_of_le_of_ne (dot_self_nonneg z) (Ne.symm hz)
    have hnn : 0 ≤ quadForm (residualMaker (rankOneProj z)) r :=
      quadForm_proj_nonneg _ (residualMaker_transpose _ (rankOneProj_transpose z))
        (residualMaker_mul_self _ (rankOneProj_mul_self z hz)) r
    rw [residualMaker, quadForm_sub, quadForm_one, quadForm_rankOneProj] at hnn
    have hle : (dot z r) ^ 2 / dot z z ≤ dot r r := by linarith
    calc (dot z r) ^ 2 = ((dot z r) ^ 2 / dot z z) * dot z z := by field_simp
      _ ≤ dot r r * dot z z := by exact mul_le_mul_of_nonneg_right hle (le_of_lt hpos)
      _ = dot z z * dot r r := by ring

/-- The group report never exceeds one on its domain.  Together with `partialR2_nonneg` this
places the exact report in `[0,1]`. -/
theorem partialR2_le_one (z r : Fin n → ℝ) (hz : dot z z ≠ 0) (hr : dot r r ≠ 0) :
    partialR2 z r ≤ 1 := by
  have hzp : 0 < dot z z := lt_of_le_of_ne (dot_self_nonneg z) (Ne.symm hz)
  have hrp : 0 < dot r r := lt_of_le_of_ne (dot_self_nonneg r) (Ne.symm hr)
  rw [partialR2, div_le_one (by positivity)]
  exact dot_sq_le z r

/-! ## The individual procedure: composite residual maker and bin report -/

/-- Two matrices agreeing on every vector are equal. -/
theorem matrix_eq_of_mulVec_eq (A B : Matrix (Fin n) (Fin n) ℝ)
    (h : ∀ v : Fin n → ℝ, A.mulVec v = B.mulVec v) : A = B := by
  ext i j
  have hj := congrFun (h (Pi.single j 1)) i
  rw [Matrix.mulVec_single_one, Matrix.mulVec_single_one] at hj
  simpa [Matrix.transpose_apply] using hj

/-- The composite residual maker `𝒜 = M_C M_B M_A` of the individual-level procedure: the
bin-specific first stage `M_A`, the global second stage `M_B`, and the final score regression
`M_C`, applied in the source study's stated order. -/
def sequentialResidualOperator (MC MB MA : Matrix (Fin n) (Fin n) ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  MC * MB * MA

/-- **TQ (4.5), UPT (8.4), DC (7.3), PL (6.2).**  Successive residualizations apply successive
residual makers in their stated order, so the individual residual vector is `𝒜 y`. -/
theorem sequentialResidualOperator_mulVec (MC MB MA : Matrix (Fin n) (Fin n) ℝ)
    (y : Fin n → ℝ) :
    (sequentialResidualOperator MC MB MA).mulVec y = MC.mulVec (MB.mulVec (MA.mulVec y)) := by
  rw [sequentialResidualOperator, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]

/-- The unstandardized bin mean squared error of the individual procedure, with `J` the
selection matrix of the bin and `size` its count. -/
def binMeanSquaredError (size : ℝ) (J : Matrix (Fin m) (Fin n) ℝ)
    (A : Matrix (Fin n) (Fin n) ℝ) (y : Fin n → ℝ) : ℝ :=
  size⁻¹ * dot (J.mulVec (A.mulVec y)) (J.mulVec (A.mulVec y))

/-- **TQ (4.6), UPT (8.5).**  The bin mean squared error is the quadratic form of
`𝒜ᵀ Jᵀ J 𝒜` divided by the bin count. -/
theorem binMeanSquaredError_eq_quadForm (size : ℝ) (J : Matrix (Fin m) (Fin n) ℝ)
    (A : Matrix (Fin n) (Fin n) ℝ) (y : Fin n → ℝ) :
    binMeanSquaredError size J A y = size⁻¹ * quadForm (Aᵀ * (Jᵀ * J) * A) y := by
  have hm : (J * A)ᵀ * (J * A) = Aᵀ * (Jᵀ * J) * A := by
    rw [Matrix.transpose_mul, Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_assoc]
  rw [binMeanSquaredError, Matrix.mulVec_mulVec, dot_mulVec_self, hm]

/-- **TQ (4.7), UPT (8.6).**  The individual procedure's bin sum of squared errors equals the
group full-model sum of squares for *every* outcome vector exactly when the two symmetric
matrices coincide.  Only the group residual maker is assumed symmetric, which it is because it
is an orthogonal projection's complement. -/
theorem individual_bin_sse_eq_group_sse_iff (J : Matrix (Fin m) (Fin n) ℝ)
    (A : Matrix (Fin n) (Fin n) ℝ) (Mfull : Matrix (Fin m) (Fin m) ℝ) (hM : Mfullᵀ = Mfull) :
    (∀ y : Fin n → ℝ,
        dot (J.mulVec (A.mulVec y)) (J.mulVec (A.mulVec y)) = quadForm (Jᵀ * Mfull * J) y)
      ↔ Aᵀ * (Jᵀ * J) * A = Jᵀ * Mfull * J := by
  have hlhs : ∀ y : Fin n → ℝ,
      dot (J.mulVec (A.mulVec y)) (J.mulVec (A.mulVec y)) = quadForm (Aᵀ * (Jᵀ * J) * A) y := by
    intro y
    have hm : (J * A)ᵀ * (J * A) = Aᵀ * (Jᵀ * J) * A := by
      rw [Matrix.transpose_mul, Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_assoc]
    rw [Matrix.mulVec_mulVec, dot_mulVec_self, hm]
  have hsym1 : (Aᵀ * (Jᵀ * J) * A)ᵀ = Aᵀ * (Jᵀ * J) * A := by
    rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_mul,
      Matrix.transpose_transpose, Matrix.transpose_transpose, Matrix.mul_assoc,
      Matrix.mul_assoc, Matrix.mul_assoc]
  have hsym2 : (Jᵀ * Mfull * J)ᵀ = Jᵀ * Mfull * J := by
    rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, hM,
      Matrix.mul_assoc]
  constructor
  · intro h
    refine (quadForm_ext_iff _ _ hsym1 hsym2).mp ?_
    intro v
    rw [← hlhs v]
    exact h v
  · intro h y
    rw [hlhs y, h]

/-! ## Sequential versus joint residualization -/

/-- **TQ Proposition 4.4 (4.8).**  Residualizing on `A` and then on `B` equals residualizing on
the joint design exactly when the two orthogonal projections commute.  The joint residual maker
`N` is pinned by the four equations characterizing the orthogonal projection onto the common
kernel of `P` and `Q`: it is symmetric, idempotent, annihilated by both projections, and fixes
every vector both projections kill.  `sequential_eq_joint_witness` inhabits all
of them. -/
theorem sequential_eq_joint_iff_commute
    (P Q N : Matrix (Fin n) (Fin n) ℝ)
    (hP : Pᵀ = P) (hPi : P * P = P) (hQ : Qᵀ = Q) (hQi : Q * Q = Q)
    (hN : Nᵀ = N) (hPN : P * N = 0) (hQN : Q * N = 0)
    (hNfix : ∀ v : Fin n → ℝ, P.mulVec v = 0 → Q.mulVec v = 0 → N.mulVec v = v) :
    residualMaker Q * residualMaker P = N ↔ P * Q = Q * P := by
  have expand1 : residualMaker Q * residualMaker P = 1 - P - Q + Q * P := by
    simp only [residualMaker, sub_mul, mul_sub, Matrix.one_mul, Matrix.mul_one]
    abel
  have expand2 : residualMaker P * residualMaker Q = 1 - Q - P + P * Q := by
    simp only [residualMaker, sub_mul, mul_sub, Matrix.one_mul, Matrix.mul_one]
    abel
  constructor
  · intro h
    have ht : (residualMaker Q * residualMaker P)ᵀ = residualMaker Q * residualMaker P := by
      rw [h, hN]
    rw [Matrix.transpose_mul, residualMaker_transpose Q hQ, residualMaker_transpose P hP,
      expand1, expand2] at ht
    have h5 := sub_eq_zero_of_eq ht
    rw [show (1 - Q - P + P * Q) - (1 - P - Q + Q * P) = P * Q - Q * P by abel] at h5
    exact sub_eq_zero.mp h5
  · intro hc
    have hTsym : (residualMaker Q * residualMaker P)ᵀ = residualMaker Q * residualMaker P := by
      rw [Matrix.transpose_mul, residualMaker_transpose Q hQ, residualMaker_transpose P hP,
        expand1, expand2, hc]
      abel
    have hPT : P * (residualMaker Q * residualMaker P) = 0 := by
      rw [expand1]
      have hPQP : P * (Q * P) = P * Q := by
        rw [← Matrix.mul_assoc, hc, Matrix.mul_assoc, hPi]
      simp only [mul_add, mul_sub, Matrix.mul_one, hPi, hPQP]
      abel
    have hQT : Q * (residualMaker Q * residualMaker P) = 0 := by
      rw [expand1]
      have hQQP : Q * (Q * P) = Q * P := by
        rw [← Matrix.mul_assoc, hQi]
      simp only [mul_add, mul_sub, Matrix.mul_one, hQi, hQQP]
      abel
    have hNT : N * (residualMaker Q * residualMaker P) = residualMaker Q * residualMaker P := by
      refine matrix_eq_of_mulVec_eq _ _ fun v ↦ ?_
      rw [← Matrix.mulVec_mulVec]
      refine hNfix _ ?_ ?_
      · rw [Matrix.mulVec_mulVec, hPT, Matrix.zero_mulVec]
      · rw [Matrix.mulVec_mulVec, hQT, Matrix.zero_mulVec]
    have hTN : residualMaker Q * residualMaker P * N = N := by
      rw [Matrix.mul_assoc]
      have h1 : residualMaker P * N = N := by
        simp only [residualMaker, sub_mul, Matrix.one_mul, hPN, sub_zero]
      rw [h1]
      simp only [residualMaker, sub_mul, Matrix.one_mul, hQN, sub_zero]
    have e2 := congrArg Matrix.transpose hNT
    rw [Matrix.transpose_mul, hTsym, hN] at e2
    rw [← e2, hTN]

/-- The residual maker of a diagonal matrix is diagonal with complemented entries. -/
theorem residualMaker_diagonal (d : Fin n → ℝ) :
    residualMaker (Matrix.diagonal d) = Matrix.diagonal (fun i ↦ 1 - d i) := by
  rw [residualMaker, ← Matrix.diagonal_one, ← Matrix.diagonal_sub]

/-- **A concrete inhabitant of every hypothesis of
`sequential_eq_joint_iff_commute`.**  On two coordinates the two designs are the
two axes, they commute, their common kernel is trivial, and sequential residualization really
does give the joint residual maker `0`. -/
theorem sequential_eq_joint_witness :
    residualMaker (Matrix.diagonal ![(0 : ℝ), 1])
        * residualMaker (Matrix.diagonal ![(1 : ℝ), 0])
      = (0 : Matrix (Fin 2) (Fin 2) ℝ) := by
  refine (sequential_eq_joint_iff_commute
    (Matrix.diagonal ![(1 : ℝ), 0]) (Matrix.diagonal ![(0 : ℝ), 1]) 0
    (Matrix.diagonal_transpose _) ?_ (Matrix.diagonal_transpose _) ?_
    (Matrix.transpose_zero) (by simp) (by simp) ?_).mpr ?_
  · rw [Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    fin_cases i <;> norm_num
  · rw [Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    fin_cases i <;> norm_num
  · intro v hv1 hv2
    rw [Matrix.zero_mulVec]
    have h0 := congrFun hv1 0
    have h1 := congrFun hv2 1
    rw [Matrix.mulVec_diagonal] at h0 h1
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, one_mul,
      Pi.zero_apply] at h0 h1
    funext i
    fin_cases i
    · simpa using h0.symm
    · simpa using h1.symm
  · rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    fin_cases i <;> norm_num

/-! ## The individual loss-regression report -/

/-- The coordinatewise squared-residual vector `ℓ = e ∘ e`. -/
def lossVector (e : Fin n → ℝ) : Fin n → ℝ :=
  fun i ↦ e i * e i

/-- The squared-loss vector of the individual procedure, `ℓ = (𝒜y) ∘ (𝒜y)`. -/
def individualLoss (MC MB MA : Matrix (Fin n) (Fin n) ℝ) (y : Fin n → ℝ) : Fin n → ℝ :=
  lossVector ((sequentialResidualOperator MC MB MA).mulVec y)

/-- The in-cohort explained fraction of the least-squares loss regression on a design containing
the intercept: `η̂_H = ℓᵀ J_H ℓ / ℓᵀ M₁ ℓ`. -/
def lossExplainedFraction (Jh M1 : Matrix (Fin n) (Fin n) ℝ) (loss : Fin n → ℝ) : ℝ :=
  quadForm Jh loss / quadForm M1 loss

/-- Conjugating the vector of a quadratic form conjugates the matrix. -/
theorem quadForm_conj (B Q : Matrix (Fin n) (Fin n) ℝ) (v : Fin n → ℝ) :
    quadForm B (Q.mulVec v) = quadForm (Qᵀ * B * Q) v := by
  have h1 : quadForm B (Q.mulVec v) = dot ((B * Q).mulVec v) (Q.mulVec v) := by
    rw [quadForm, Matrix.mulVec_mulVec, dot_comm]
  rw [h1, dot_mulVec_left, Matrix.mulVec_mulVec, quadForm, dot_comm, Matrix.mul_assoc]

/-- Because the loss-regression design contains the intercept, the intercept projection commutes
past it on the left as well. -/
theorem intercept_mul_loss_design (P1 Ph : Matrix (Fin n) (Fin n) ℝ) (h1 : P1ᵀ = P1)
    (hh : Phᵀ = Ph) (hc : Ph * P1 = P1) : P1 * Ph = P1 := by
  have ht := congrArg Matrix.transpose hc
  rw [Matrix.transpose_mul, h1, hh] at ht
  exact ht

/-- `J_H = P_H - P_1` is symmetric. -/
theorem lossProjection_transpose (P1 Ph : Matrix (Fin n) (Fin n) ℝ) (h1 : P1ᵀ = P1)
    (hh : Phᵀ = Ph) : (Ph - P1)ᵀ = Ph - P1 := by
  rw [Matrix.transpose_sub, h1, hh]

/-- `J_H = P_H - P_1` is idempotent, hence an orthogonal projection onto the part of the
loss-regression span orthogonal to the intercept. -/
theorem lossProjection_mul_self (P1 Ph : Matrix (Fin n) (Fin n) ℝ) (h1 : P1ᵀ = P1)
    (hh : Phᵀ = Ph) (h1i : P1 * P1 = P1) (hhi : Ph * Ph = Ph) (hc : Ph * P1 = P1) :
    (Ph - P1) * (Ph - P1) = Ph - P1 := by
  have hc' : P1 * Ph = P1 := intercept_mul_loss_design P1 Ph h1 hh hc
  simp only [sub_mul, mul_sub, hhi, h1i, hc, hc']
  abel

/-- `J_H` annihilates the intercept projection, so centering the loss leaves the numerator of
the report unchanged.  This is the step PL (6.3) states as "replacing `ℓ` by `M₁ℓ` leaves the
numerator unchanged". -/
theorem lossProjection_mul_residualMaker (P1 Ph : Matrix (Fin n) (Fin n) ℝ)
    (h1i : P1 * P1 = P1) (hc : Ph * P1 = P1) :
    (Ph - P1) * residualMaker P1 = Ph - P1 := by
  simp only [residualMaker, mul_sub, sub_mul, Matrix.mul_one, hc, h1i]
  abel

/-- The left-hand form of the previous identity. -/
theorem residualMaker_mul_lossProjection (P1 Ph : Matrix (Fin n) (Fin n) ℝ) (h1 : P1ᵀ = P1)
    (hh : Phᵀ = Ph) (h1i : P1 * P1 = P1) (hc : Ph * P1 = P1) :
    residualMaker P1 * (Ph - P1) = Ph - P1 := by
  have hc' : P1 * Ph = P1 := intercept_mul_loss_design P1 Ph h1 hh hc
  simp only [residualMaker, sub_mul, mul_sub, Matrix.one_mul, hc', h1i]
  abel

/-- **PL (6.3), DC (7.4), UPT (8.7): the exact individual report.**  The explained fraction of
the loss regression equals the centered angular form `z_Lᵀ J_H z_L / z_Lᵀ z_L` with
`z_L = M₁ ℓ`.  The hypotheses are exactly that both projections are orthogonal projections and
that the loss-regression design contains the intercept; nothing about the outcome law is
assumed. -/
theorem lossExplainedFraction_centered (P1 Ph : Matrix (Fin n) (Fin n) ℝ) (h1 : P1ᵀ = P1)
    (hh : Phᵀ = Ph) (h1i : P1 * P1 = P1) (hc : Ph * P1 = P1) (loss : Fin n → ℝ) :
    lossExplainedFraction (Ph - P1) (residualMaker P1) loss
      = quadForm (Ph - P1) ((residualMaker P1).mulVec loss)
          / dot ((residualMaker P1).mulVec loss) ((residualMaker P1).mulVec loss) := by
  have hnum : quadForm (Ph - P1) ((residualMaker P1).mulVec loss)
      = quadForm (Ph - P1) loss := by
    rw [quadForm_conj, residualMaker_transpose P1 h1,
      residualMaker_mul_lossProjection P1 Ph h1 hh h1i hc,
      lossProjection_mul_residualMaker P1 Ph h1i hc]
  have hden : quadForm (residualMaker P1) loss
      = dot ((residualMaker P1).mulVec loss) ((residualMaker P1).mulVec loss) :=
    quadForm_proj_eq_sq_norm _ (residualMaker_transpose P1 h1)
      (residualMaker_mul_self P1 h1i) loss
  rw [lossExplainedFraction, hnum, hden]

/-- The explained fraction of the loss regression is nonnegative on its domain. -/
theorem lossExplainedFraction_nonneg (P1 Ph : Matrix (Fin n) (Fin n) ℝ) (h1 : P1ᵀ = P1)
    (hh : Phᵀ = Ph) (h1i : P1 * P1 = P1) (hhi : Ph * Ph = Ph) (hc : Ph * P1 = P1)
    (loss : Fin n → ℝ) : 0 ≤ lossExplainedFraction (Ph - P1) (residualMaker P1) loss := by
  refine div_nonneg ?_ ?_
  · exact quadForm_proj_nonneg _ (lossProjection_transpose P1 Ph h1 hh)
      (lossProjection_mul_self P1 Ph h1 hh h1i hhi hc) loss
  · exact quadForm_proj_nonneg _ (residualMaker_transpose P1 h1)
      (residualMaker_mul_self P1 h1i) loss

/-- **A common positive reference normalization of every individual loss cancels.**  PL
Proposition 6.1 and DC Proposition 7.2 both record this; it does not identify the group and
individual reporting operators with one another. -/
theorem lossExplainedFraction_smul (Jh M1 : Matrix (Fin n) (Fin n) ℝ) (c : ℝ) (hc : c ≠ 0)
    (loss : Fin n → ℝ) :
    lossExplainedFraction Jh M1 (c • loss) = lossExplainedFraction Jh M1 loss := by
  rw [lossExplainedFraction, lossExplainedFraction, quadForm_smul, quadForm_smul,
    mul_div_mul_left _ _ (pow_ne_zero 2 hc)]

/-- Each coordinate of the squared-residual vector is quadratic in its argument. -/
theorem lossVector_smul (c : ℝ) (e : Fin n → ℝ) :
    lossVector (c • e) = (c ^ 2) • lossVector e := by
  funext i
  simp only [lossVector, Pi.smul_apply, smul_eq_mul]
  ring

/-- **The bin mean squared error is the empirical cohort expectation of the squared-residual
vector.**  Taking the bin to be the whole cohort, the operator quantity of TQ (4.6) and
UPT (8.5) is the corpus empirical expectation `uniformExp` of the squared-residual vector, so
the individual procedure's report is an average of actual per-individual losses. -/
theorem binMeanSquaredError_eq_uniformExp [NeZero n] (A : Matrix (Fin n) (Fin n) ℝ)
    (y : Fin n → ℝ) :
    binMeanSquaredError (Fintype.card (Fin n) : ℝ) (1 : Matrix (Fin n) (Fin n) ℝ) A y
      = uniformExp (Fin n) (lossVector (A.mulVec y)) := by
  rw [binMeanSquaredError, uniformExp_apply, Matrix.one_mulVec]
  simp only [dot, Descent.Core.innerSum, lossVector, Finset.mul_sum]

/-- **UPT Corollary 8.3, the degree assertion.**  Numerator and denominator of the
loss-regression report are exactly homogeneous of degree four in the outcome vector, which is
what "quartic polynomials in `y`" asserts. -/
theorem loss_report_quartic (B A : Matrix (Fin n) (Fin n) ℝ) (c : ℝ) (y : Fin n → ℝ) :
    quadForm B (lossVector (A.mulVec (c • y)))
      = c ^ 4 * quadForm B (lossVector (A.mulVec y)) := by
  rw [Matrix.mulVec_smul, lossVector_smul, quadForm_smul]
  ring

/-- The individual squared-loss vector of the composite residual maker is quadratic in the
outcome vector. -/
theorem individualLoss_smul (MC MB MA : Matrix (Fin n) (Fin n) ℝ) (c : ℝ) (y : Fin n → ℝ) :
    individualLoss MC MB MA (c • y) = (c ^ 2) • individualLoss MC MB MA y := by
  rw [individualLoss, individualLoss, Matrix.mulVec_smul, lossVector_smul]

/-- **The loss-regression report is scale invariant in the outcome vector.**  Rescaling `y`
multiplies both quartic forms by `c⁴`, so the report of UPT (8.7) is unchanged: the fourth-order
structure is exactly a degree-four homogeneity, not an approximation. -/
theorem lossReport_outcome_scale_invariant (Jh M1 MC MB MA : Matrix (Fin n) (Fin n) ℝ)
    (c : ℝ) (hc : c ≠ 0) (y : Fin n → ℝ) :
    lossExplainedFraction Jh M1 (individualLoss MC MB MA (c • y))
      = lossExplainedFraction Jh M1 (individualLoss MC MB MA y) := by
  rw [individualLoss_smul, lossExplainedFraction_smul _ _ _ (pow_ne_zero 2 hc)]

end

end Descent.Portability.CohortEvaluationOperators
