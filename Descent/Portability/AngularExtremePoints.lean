/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.AngularExtremalReports
import Mathlib.Analysis.Convex.Extreme

assert_below Descent.Decision Descent.Program

/-!
# Extreme points of the feasible angular set

This module proves the perturbation mechanism behind the rank bound of PL Corollary 6.3: an
extreme point of the feasible set of angular matrices with prescribed projection reports admits
no nonzero symmetric direction that is carried by the eigendirections of positive eigenvalue and
annihilates both the trace and every report.

`feasibleAngular` is the feasible set of PL (6.8) with `m` prescribed reports added.
`not_mem_extremePoints_of_perturbation` is the elementary half: a feasible matrix sitting at the
midpoint of two distinct feasible matrices is not extreme.  `diagonal_perturb_quadForm_nonneg`
is the quantitative half: a symmetric perturbation supported where the eigenvalues are at least
`μ`, with row and column absolute sums at most `B`, keeps the quadratic form nonnegative for
every scale `ε` with `|ε| B ≤ μ`.  Conjugating that bound back by the eigenvector unitary
(`conjPerturb`) gives `extremePoint_no_supported_direction`, which is the contradiction the
Barvinok-Pataki argument needs.

At `m = 0` the bound is closed outright: `extremePoint_unique_positive_eigenvalue` proves that
an extreme point with no prescribed reports has at most one positive eigenvalue, which is
`r(r+1)/2 ≤ 1`, by feeding the criterion the explicit two-point direction `pairDirection`.  That
also shows the criterion is not vacuous, which matters because its conclusion is `False`.

SCOPE.  For general `m` what is proved here is the perturbation step, not the whole rank bound
`r(r+1)/2 ≤ m + 1`.  The step still missing is the counting one: the symmetric matrices carried
by an `r`-dimensional eigenspace form a space of dimension `r(r+1)/2`, so when
`r(r+1)/2 > m + 1` the `m + 1` linear conditions on trace and reports must vanish on some
nonzero such direction, which `extremePoint_no_supported_direction` then rules out.  Producing
that direction needs a rank-nullity count over unordered index pairs, which is not formalized
here, so PL Corollary 6.3's rank bound is closed only at `m = 0`.  Everything below is
unconditional.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.AngularExtremePoints

open Foundations Matrix CohortEvaluationOperators AngularReportClosure AngularSpectralBounds
open AngularExtremalReports

noncomputable section

variable {d mm : ℕ}

/-! ## Linearity of the quadratic form in the matrix -/

/-- The quadratic form is additive in the matrix. -/
theorem quadForm_add_matrix (A B : Matrix (Fin d) (Fin d) ℝ) (v : Fin d → ℝ) :
    quadForm (A + B) v = quadForm A v + quadForm B v := by
  simp only [quadForm, Matrix.add_mulVec]
  exact dot_add_right v (A.mulVec v) (B.mulVec v)

/-- The quadratic form is homogeneous in the matrix. -/
theorem quadForm_smul_matrix (c : ℝ) (A : Matrix (Fin d) (Fin d) ℝ) (v : Fin d → ℝ) :
    quadForm (c • A) v = c * quadForm A v := by
  simp only [quadForm, Matrix.smul_mulVec]
  exact dot_smul_right c v (A.mulVec v)

/-- The quadratic form written out over the matrix entries. -/
theorem quadForm_entries (C : Matrix (Fin d) (Fin d) ℝ) (w : Fin d → ℝ) :
    quadForm C w = ∑ i, ∑ j, w i * (C i j * w j) := by
  simp [quadForm, dot, Descent.Core.innerSum, Matrix.mulVec, dotProduct, Finset.mul_sum]

/-! ## The feasible angular set with prescribed reports -/

/-- The feasible set of PL (6.8) with `m` prescribed projection reports: symmetric, positive
semidefinite, trace one, and matching the prescribed report in each test direction. -/
def feasibleAngular (V : Fin mm → Fin d → ℝ) (a : Fin mm → ℝ) :
    Set (Matrix (Fin d) (Fin d) ℝ) :=
  {G | Gᵀ = G ∧ (∀ v, 0 ≤ quadForm G v) ∧ Matrix.trace G = 1 ∧ ∀ k, quadForm G (V k) = a k}

/-- **A feasible matrix at the midpoint of two distinct feasible matrices is not extreme.**
This is the elementary half of the Barvinok-Pataki argument. -/
theorem not_mem_extremePoints_of_perturbation (V : Fin mm → Fin d → ℝ) (a : Fin mm → ℝ)
    (G D : Matrix (Fin d) (Fin d) ℝ) (hD : D ≠ 0) (hplus : G + D ∈ feasibleAngular V a)
    (hminus : G - D ∈ feasibleAngular V a) :
    G ∉ (feasibleAngular V a).extremePoints ℝ := by
  intro hext
  have hseg : G ∈ openSegment ℝ (G + D) (G - D) := by
    refine ⟨1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num, ?_⟩
    ext i j
    simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
    ring
  have hfix := hext.2 hplus hminus hseg
  apply hD
  have h1 : G + D = G := hfix
  have h2 : D = 0 := by
    have := congrArg (fun M ↦ M - G) h1
    simpa using this
  exact h2

/-! ## The quantitative perturbation bound in the eigenbasis -/

/-- **A supported symmetric perturbation of a nonnegative diagonal stays nonnegative.**  If the
perturbation is carried by coordinates whose diagonal entry is at least `μ`, and its row and
column absolute sums are at most `B`, then any scale with `|ε| B ≤ μ` keeps the quadratic form
nonnegative.  This is the quantitative half of the Barvinok-Pataki argument. -/
theorem diagonal_perturb_quadForm_nonneg (lam : Fin d → ℝ) (C : Matrix (Fin d) (Fin d) ℝ)
    (mu B eps : ℝ) (hmu : 0 < mu) (hlam : ∀ i, 0 ≤ lam i)
    (hsupp : ∀ i j, C i j ≠ 0 → mu ≤ lam i ∧ mu ≤ lam j)
    (hB : ∀ i, ∑ j, |C i j| ≤ B) (hB' : ∀ j, ∑ i, |C i j| ≤ B)
    (hsmall : |eps| * B ≤ mu) (w : Fin d → ℝ) :
    0 ≤ quadForm (Matrix.diagonal lam) w + eps * quadForm C w := by
  set Q : ℝ := ∑ i, lam i * w i ^ 2 with hQdef
  have hQ : quadForm (Matrix.diagonal lam) w = Q := quadForm_diagonal lam w
  have hQnn : 0 ≤ Q := Finset.sum_nonneg fun i _ ↦ mul_nonneg (hlam i) (sq_nonneg _)
  have hrow : ∀ i j, |C i j| * mu ≤ |C i j| * lam i := by
    intro i j
    rcases eq_or_ne (C i j) 0 with h | h
    · simp [h]
    · exact mul_le_mul_of_nonneg_left (hsupp i j h).1 (abs_nonneg _)
  have hcol : ∀ i j, |C i j| * mu ≤ |C i j| * lam j := by
    intro i j
    rcases eq_or_ne (C i j) 0 with h | h
    · simp [h]
    · exact mul_le_mul_of_nonneg_left (hsupp i j h).2 (abs_nonneg _)
  have habs : |quadForm C w| ≤ ∑ i, ∑ j, |C i j| * ((w i ^ 2 + w j ^ 2) / 2) := by
    rw [quadForm_entries]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ ↦ ?_)
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ ↦ ?_)
    rw [abs_mul, abs_mul]
    have hw : |w i| * (|C i j| * |w j|) = |C i j| * (|w i| * |w j|) := by ring
    rw [hw]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    nlinarith [sq_nonneg (|w i| - |w j|), sq_abs (w i), sq_abs (w j)]
  have hmid : mu * (∑ i, ∑ j, |C i j| * ((w i ^ 2 + w j ^ 2) / 2)) ≤ B * Q := by
    have hstep : mu * (∑ i, ∑ j, |C i j| * ((w i ^ 2 + w j ^ 2) / 2))
        ≤ (∑ i, ∑ j, |C i j| * lam i * w i ^ 2) / 2
          + (∑ i, ∑ j, |C i j| * lam j * w j ^ 2) / 2 := by
      rw [Finset.mul_sum]
      have hone : ∀ i : Fin d, mu * ∑ j, |C i j| * ((w i ^ 2 + w j ^ 2) / 2)
          ≤ (∑ j, |C i j| * lam i * w i ^ 2) / 2 + (∑ j, |C i j| * lam j * w j ^ 2) / 2 := by
        intro i
        have hR : (∑ j, |C i j| * lam i * w i ^ 2) / 2 + (∑ j, |C i j| * lam j * w j ^ 2) / 2
            = ∑ j, (|C i j| * lam i * w i ^ 2 / 2 + |C i j| * lam j * w j ^ 2 / 2) := by
          rw [Finset.sum_div, Finset.sum_div, ← Finset.sum_add_distrib]
        rw [Finset.mul_sum, hR]
        refine Finset.sum_le_sum fun j _ ↦ ?_
        have h1 : |C i j| * mu * w i ^ 2 ≤ |C i j| * lam i * w i ^ 2 :=
          mul_le_mul_of_nonneg_right (hrow i j) (sq_nonneg _)
        have h2 : |C i j| * mu * w j ^ 2 ≤ |C i j| * lam j * w j ^ 2 :=
          mul_le_mul_of_nonneg_right (hcol i j) (sq_nonneg _)
        nlinarith [h1, h2]
      calc ∑ i, mu * ∑ j, |C i j| * ((w i ^ 2 + w j ^ 2) / 2)
          ≤ ∑ i, ((∑ j, |C i j| * lam i * w i ^ 2) / 2
              + (∑ j, |C i j| * lam j * w j ^ 2) / 2) := Finset.sum_le_sum fun i _ ↦ hone i
        _ = (∑ i, ∑ j, |C i j| * lam i * w i ^ 2) / 2
              + (∑ i, ∑ j, |C i j| * lam j * w j ^ 2) / 2 := by
            rw [Finset.sum_add_distrib, ← Finset.sum_div, ← Finset.sum_div]
    have hfirst : (∑ i, ∑ j, |C i j| * lam i * w i ^ 2) ≤ B * Q := by
      have hi : ∀ i : Fin d, ∑ j, |C i j| * lam i * w i ^ 2 ≤ B * (lam i * w i ^ 2) := by
        intro i
        have hsum : ∑ j, |C i j| * lam i * w i ^ 2 = (∑ j, |C i j|) * (lam i * w i ^ 2) := by
          rw [Finset.sum_mul]
          exact Finset.sum_congr rfl fun _ _ ↦ by ring
        rw [hsum]
        exact mul_le_mul_of_nonneg_right (hB i) (mul_nonneg (hlam i) (sq_nonneg _))
      calc ∑ i, ∑ j, |C i j| * lam i * w i ^ 2
          ≤ ∑ i, B * (lam i * w i ^ 2) := Finset.sum_le_sum fun i _ ↦ hi i
        _ = B * Q := by rw [hQdef, Finset.mul_sum]
    have hsecond : (∑ i, ∑ j, |C i j| * lam j * w j ^ 2) ≤ B * Q := by
      have hswap : ∑ i, ∑ j, |C i j| * lam j * w j ^ 2
          = ∑ j, ∑ i, |C i j| * lam j * w j ^ 2 := Finset.sum_comm
      rw [hswap]
      have hj : ∀ j : Fin d, ∑ i, |C i j| * lam j * w j ^ 2 ≤ B * (lam j * w j ^ 2) := by
        intro j
        have hsum : ∑ i, |C i j| * lam j * w j ^ 2 = (∑ i, |C i j|) * (lam j * w j ^ 2) := by
          rw [Finset.sum_mul]
          exact Finset.sum_congr rfl fun _ _ ↦ by ring
        rw [hsum]
        exact mul_le_mul_of_nonneg_right (hB' j) (mul_nonneg (hlam j) (sq_nonneg _))
      calc ∑ j, ∑ i, |C i j| * lam j * w j ^ 2
          ≤ ∑ j, B * (lam j * w j ^ 2) := Finset.sum_le_sum fun j _ ↦ hj j
        _ = B * Q := by rw [hQdef, Finset.mul_sum]
    linarith
  have hSnn : 0 ≤ ∑ i, ∑ j, |C i j| * ((w i ^ 2 + w j ^ 2) / 2) := by
    refine Finset.sum_nonneg fun i _ ↦ Finset.sum_nonneg fun j _ ↦ ?_
    have : (0 : ℝ) ≤ (w i ^ 2 + w j ^ 2) / 2 := by positivity
    exact mul_nonneg (abs_nonneg _) this
  have hfinal : |eps| * |quadForm C w| ≤ Q := by
    have h1 : |eps| * |quadForm C w|
        ≤ |eps| * ∑ i, ∑ j, |C i j| * ((w i ^ 2 + w j ^ 2) / 2) :=
      mul_le_mul_of_nonneg_left habs (abs_nonneg _)
    nlinarith [hmid, hmu, hsmall, hSnn, hQnn, h1, abs_nonneg eps]
  rw [hQ]
  have hb : -(|eps| * |quadForm C w|) ≤ eps * quadForm C w := by
    have := abs_mul eps (quadForm C w)
    have habs2 : |eps * quadForm C w| ≤ |eps| * |quadForm C w| := le_of_eq this
    linarith [neg_abs_le (eps * quadForm C w), habs2]
  linarith

/-! ## Conjugating the perturbation back to the original basis -/

/-- A perturbation written in the eigenbasis of the matrix being perturbed. -/
def conjPerturb (G : Matrix (Fin d) (Fin d) ℝ) (hG : Matrix.IsHermitian G)
    (C : Matrix (Fin d) (Fin d) ℝ) : Matrix (Fin d) (Fin d) ℝ :=
  eigenUnitary G hG * C * (eigenUnitary G hG)ᵀ

/-- The conjugated perturbation is symmetric when its eigenbasis form is. -/
theorem conjPerturb_transpose (G : Matrix (Fin d) (Fin d) ℝ) (hG : Matrix.IsHermitian G)
    (C : Matrix (Fin d) (Fin d) ℝ) (hC : Cᵀ = C) : (conjPerturb G hG C)ᵀ = conjPerturb G hG C := by
  simp [conjPerturb, Matrix.transpose_mul, hC, Matrix.mul_assoc]

/-- Conjugation preserves the trace. -/
theorem trace_conjPerturb (G : Matrix (Fin d) (Fin d) ℝ) (hG : Matrix.IsHermitian G)
    (C : Matrix (Fin d) (Fin d) ℝ) : Matrix.trace (conjPerturb G hG C) = Matrix.trace C := by
  rw [conjPerturb, Matrix.trace_mul_comm, ← Matrix.mul_assoc, eigenUnitary_transpose_mul,
    Matrix.one_mul]

/-- The quadratic form of the conjugated perturbation, read in eigenvector coordinates. -/
theorem quadForm_conjPerturb (G : Matrix (Fin d) (Fin d) ℝ) (hG : Matrix.IsHermitian G)
    (C : Matrix (Fin d) (Fin d) ℝ) (v : Fin d → ℝ) :
    quadForm (conjPerturb G hG C) v = quadForm C ((eigenUnitary G hG)ᵀ.mulVec v) := by
  rw [quadForm_conj, Matrix.transpose_transpose, conjPerturb]

/-- The matrix itself is the conjugate of its eigenvalue diagonal. -/
theorem quadForm_eq_diagonal_conj (G : Matrix (Fin d) (Fin d) ℝ) (hG : Matrix.IsHermitian G)
    (v : Fin d → ℝ) :
    quadForm G v = quadForm (Matrix.diagonal hG.eigenvalues) ((eigenUnitary G hG)ᵀ.mulVec v) := by
  rw [quadForm_conj, Matrix.transpose_transpose, ← spectral_conj]

/-- A nonzero eigenbasis perturbation conjugates to a nonzero matrix. -/
theorem conjPerturb_ne_zero (G : Matrix (Fin d) (Fin d) ℝ) (hG : Matrix.IsHermitian G)
    (C : Matrix (Fin d) (Fin d) ℝ) (hC : C ≠ 0) : conjPerturb G hG C ≠ 0 := by
  intro h
  apply hC
  have hU := eigenUnitary_transpose_mul G hG
  have hback : (eigenUnitary G hG)ᵀ * conjPerturb G hG C * eigenUnitary G hG = C := by
    calc (eigenUnitary G hG)ᵀ * conjPerturb G hG C * eigenUnitary G hG
        = ((eigenUnitary G hG)ᵀ * eigenUnitary G hG) * C
            * ((eigenUnitary G hG)ᵀ * eigenUnitary G hG) := by
          simp [conjPerturb, Matrix.mul_assoc]
      _ = C := by rw [hU, Matrix.one_mul, Matrix.mul_one]
  rw [h] at hback
  simpa using hback.symm

/-- **An extreme point of the feasible angular set admits no supported symmetric direction.**
If the eigenbasis perturbation is nonzero, symmetric, carried by the eigendirections whose
eigenvalue is at least `μ`, has row and column absolute sums at most `B`, and annihilates both
the trace and every prescribed report, then the matrix it perturbs is not an extreme point.
This is the step the Barvinok-Pataki rank bound contradicts; see the scope note in the module
header for the counting step that is still missing. -/
theorem extremePoint_no_supported_direction (V : Fin mm → Fin d → ℝ) (a : Fin mm → ℝ)
    (G : Matrix (Fin d) (Fin d) ℝ) (hG : Matrix.IsHermitian G)
    (hext : G ∈ (feasibleAngular V a).extremePoints ℝ) (C : Matrix (Fin d) (Fin d) ℝ)
    (hC : Cᵀ = C) (hCne : C ≠ 0) (mu B : ℝ) (hmu : 0 < mu) (hBpos : 0 < B)
    (hsupp : ∀ i j, C i j ≠ 0 → mu ≤ hG.eigenvalues i ∧ mu ≤ hG.eigenvalues j)
    (hB : ∀ i, ∑ j, |C i j| ≤ B) (hB' : ∀ j, ∑ i, |C i j| ≤ B) (htr : Matrix.trace C = 0)
    (hrep : ∀ k, quadForm (conjPerturb G hG C) (V k) = 0) : False := by
  obtain ⟨hGsym, hGpsd, hGtr, hGrep⟩ := hext.1
  have hlamnn : ∀ i, 0 ≤ hG.eigenvalues i := by
    intro i
    have hq : 0 ≤ quadForm G (angularEigenVector G hG i) := hGpsd _
    rwa [quadForm_at_eigenVector] at hq
  have hmulcancel : mu / B * B = mu := by
    field_simp
  have heps : |mu / B| * B ≤ mu := by
    rw [abs_of_pos (div_pos hmu hBpos)]
    exact le_of_eq hmulcancel
  have hepspos : 0 < mu / B := div_pos hmu hBpos
  set D : Matrix (Fin d) (Fin d) ℝ := (mu / B) • conjPerturb G hG C with hDdef
  have hDne : D ≠ 0 := by
    rw [hDdef]
    exact smul_ne_zero (ne_of_gt hepspos) (conjPerturb_ne_zero G hG C hCne)
  have hquad : ∀ (s : ℝ) (v : Fin d → ℝ),
      quadForm (G + s • conjPerturb G hG C) v
        = quadForm (Matrix.diagonal hG.eigenvalues) ((eigenUnitary G hG)ᵀ.mulVec v)
          + s * quadForm C ((eigenUnitary G hG)ᵀ.mulVec v) := by
    intro s v
    rw [quadForm_add_matrix, quadForm_smul_matrix, quadForm_conjPerturb,
      quadForm_eq_diagonal_conj]
  have hmem : ∀ s : ℝ, |s| * B ≤ mu → G + s • conjPerturb G hG C ∈ feasibleAngular V a := by
    intro s hs
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [Matrix.transpose_add, Matrix.transpose_smul, hGsym,
        conjPerturb_transpose G hG C hC]
    · intro v
      rw [hquad s v]
      exact diagonal_perturb_quadForm_nonneg hG.eigenvalues C mu B s hmu hlamnn hsupp hB hB'
        hs _
    · rw [Matrix.trace_add, Matrix.trace_smul, trace_conjPerturb, htr, hGtr]
      simp
    · intro k
      rw [quadForm_add_matrix, quadForm_smul_matrix, hrep k, hGrep k]
      ring
  refine not_mem_extremePoints_of_perturbation V a G D hDne ?_ ?_ hext
  · rw [hDdef]
    exact hmem (mu / B) heps
  · have hsub : G - (mu / B) • conjPerturb G hG C = G + (-(mu / B)) • conjPerturb G hG C := by
      module
    rw [hDdef, hsub]
    refine hmem (-(mu / B)) ?_
    rwa [abs_neg]

/-! ## The rank bound with no prescribed reports -/

/-- The trace-zero two-point direction that separates a pair of positive eigenvalues. -/
def pairDirection (i₀ i₁ : Fin d) : Matrix (Fin d) (Fin d) ℝ :=
  Matrix.diagonal fun i ↦ (if i = i₀ then (1 : ℝ) else 0) - (if i = i₁ then (1 : ℝ) else 0)

/-- The two-point direction is symmetric. -/
theorem pairDirection_transpose (i₀ i₁ : Fin d) :
    (pairDirection i₀ i₁)ᵀ = pairDirection i₀ i₁ :=
  Matrix.diagonal_transpose _

/-- The two-point direction has zero trace. -/
theorem trace_pairDirection (i₀ i₁ : Fin d) : Matrix.trace (pairDirection i₀ i₁) = 0 := by
  rw [pairDirection, Matrix.trace_diagonal, Finset.sum_sub_distrib]
  simp

/-- The two-point direction is nonzero when the two points differ. -/
theorem pairDirection_ne_zero (i₀ i₁ : Fin d) (hne : i₀ ≠ i₁) : pairDirection i₀ i₁ ≠ 0 := by
  intro h
  have hentry := congrFun (congrFun h i₀) i₀
  rw [pairDirection, Matrix.diagonal_apply_eq] at hentry
  simp [hne] at hentry

/-- Off its two points the two-point direction vanishes. -/
theorem pairDirection_support (i₀ i₁ i j : Fin d) (hij : pairDirection i₀ i₁ i j ≠ 0) :
    i = j ∧ (i = i₀ ∨ i = i₁) := by
  rw [pairDirection] at hij
  rcases eq_or_ne i j with hEq | hEq
  · subst hEq
    refine ⟨rfl, ?_⟩
    by_contra hcon
    push_neg at hcon
    rw [Matrix.diagonal_apply_eq] at hij
    simp [hcon.1, hcon.2] at hij
  · rw [Matrix.diagonal_apply_ne _ hEq] at hij
    exact absurd rfl hij

/-- Each row of the two-point direction has absolute sum at most one. -/
theorem pairDirection_row_sum (i₀ i₁ i : Fin d) : ∑ j, |pairDirection i₀ i₁ i j| ≤ 1 := by
  have hsingle : ∑ j, |pairDirection i₀ i₁ i j| = |pairDirection i₀ i₁ i i| := by
    refine Finset.sum_eq_single i (fun b _ hb ↦ ?_) (fun h ↦ absurd (Finset.mem_univ i) h)
    rw [pairDirection, Matrix.diagonal_apply_ne _ (Ne.symm hb), abs_zero]
  rw [hsingle, pairDirection, Matrix.diagonal_apply_eq]
  split_ifs <;> norm_num

/-- Each column of the two-point direction has absolute sum at most one. -/
theorem pairDirection_col_sum (i₀ i₁ j : Fin d) : ∑ i, |pairDirection i₀ i₁ i j| ≤ 1 := by
  have hsingle : ∑ i, |pairDirection i₀ i₁ i j| = |pairDirection i₀ i₁ j j| := by
    refine Finset.sum_eq_single j (fun b _ hb ↦ ?_) (fun h ↦ absurd (Finset.mem_univ j) h)
    rw [pairDirection, Matrix.diagonal_apply_ne _ hb, abs_zero]
  rw [hsingle, pairDirection, Matrix.diagonal_apply_eq]
  split_ifs <;> norm_num

/-- **PL Corollary 6.3 with no prescribed reports.**  An extreme point of the feasible angular
set has at most one positive eigenvalue, which is the rank bound `r(r+1)/2 ≤ m + 1` at `m = 0`:
it forces `r ≤ 1`, so an extreme angular matrix with no reports prescribed is a single rank-one
projection and its attaining law lives on one residual direction.  Proving it here also shows
that the hypotheses of `extremePoint_no_supported_direction` are satisfiable, so that criterion
is not vacuous. -/
theorem extremePoint_unique_positive_eigenvalue (G : Matrix (Fin d) (Fin d) ℝ)
    (hG : Matrix.IsHermitian G)
    (hext : G ∈ (feasibleAngular (fun _ : Fin 0 ↦ (0 : Fin d → ℝ)) (fun _ ↦ 0)).extremePoints ℝ)
    (i₀ i₁ : Fin d) (hne : i₀ ≠ i₁) (hpos₀ : 0 < hG.eigenvalues i₀)
    (hpos₁ : 0 < hG.eigenvalues i₁) : False := by
  refine extremePoint_no_supported_direction _ _ G hG hext (pairDirection i₀ i₁)
    (pairDirection_transpose i₀ i₁) (pairDirection_ne_zero i₀ i₁ hne)
    (min (hG.eigenvalues i₀) (hG.eigenvalues i₁)) 1 (lt_min hpos₀ hpos₁) one_pos ?_
    (pairDirection_row_sum i₀ i₁) (pairDirection_col_sum i₀ i₁) (trace_pairDirection i₀ i₁)
    (fun k ↦ k.elim0)
  intro i j hij
  obtain ⟨hEq, hmem⟩ := pairDirection_support i₀ i₁ i j hij
  subst hEq
  rcases hmem with hEq0 | hEq1
  · subst hEq0
    exact ⟨min_le_left _ _, min_le_left _ _⟩
  · subst hEq1
    exact ⟨min_le_right _ _, min_le_right _ _⟩

/-! ## The symmetric directions carried by an index set -/

/-- The inner sum against a standard basis vector reads off a coordinate. -/
theorem dot_single_left (i : Fin d) (v : Fin d → ℝ) : dot (Pi.single i (1 : ℝ)) v = v i := by
  simp only [dot, Descent.Core.innerSum, Pi.single_apply]
  rw [Finset.sum_eq_single i]
  · simp
  · intro b _ hb
    simp [hb]
  · intro h
    exact absurd (Finset.mem_univ i) h

/-- The trace of an outer product is the inner sum of its factors. -/
theorem trace_vecMulVec (x y : Fin d → ℝ) :
    Matrix.trace (Matrix.vecMulVec x y) = dot x y := by
  simp [Matrix.trace, Matrix.diag_apply, Matrix.vecMulVec_apply, dot, Descent.Core.innerSum]

/-- The quadratic form of an outer product factors. -/
theorem quadForm_vecMulVec_pair (x y v : Fin d → ℝ) :
    quadForm (Matrix.vecMulVec x y) v = dot x v * dot y v := by
  rw [quadForm, vecMulVec_mulVec, dot_smul_right, dot_comm v x]
  ring

/-- The quadratic form of a finite sum of matrices. -/
theorem quadForm_sum {ι : Type*} (s : Finset ι) (M : ι → Matrix (Fin d) (Fin d) ℝ)
    (v : Fin d → ℝ) : quadForm (∑ z ∈ s, M z) v = ∑ z ∈ s, quadForm (M z) v := by
  classical
  induction s using Finset.induction with
  | empty => simp [quadForm, dot, Descent.Core.innerSum, Matrix.zero_mulVec]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, quadForm_add_matrix, ih]

/-- The symmetric direction attached to an ordered pair of coordinates. -/
def pairBasis (i j : Fin d) : Matrix (Fin d) (Fin d) ℝ :=
  Matrix.vecMulVec (Pi.single i 1) (Pi.single j 1)
    + Matrix.vecMulVec (Pi.single j 1) (Pi.single i 1)

/-- The pair direction does not depend on the order of its two coordinates. -/
theorem pairBasis_comm (i j : Fin d) : pairBasis i j = pairBasis j i := by
  rw [pairBasis, pairBasis, add_comm]

/-- The pair direction is symmetric. -/
theorem pairBasis_transpose (i j : Fin d) : (pairBasis i j)ᵀ = pairBasis i j := by
  ext p q
  simp only [pairBasis, Matrix.transpose_apply, Matrix.add_apply, Matrix.vecMulVec_apply]
  ring

/-- The trace of a pair direction. -/
theorem trace_pairBasis (i j : Fin d) :
    Matrix.trace (pairBasis i j) = 2 * (if i = j then (1 : ℝ) else 0) := by
  rw [pairBasis, Matrix.trace_add, trace_vecMulVec, trace_vecMulVec, dot_single_left,
    dot_single_left, Pi.single_apply, Pi.single_apply]
  by_cases h : i = j <;> (simp [h, eq_comm]; norm_num)

/-- The quadratic form of a pair direction. -/
theorem quadForm_pairBasis (i j : Fin d) (w : Fin d → ℝ) :
    quadForm (pairBasis i j) w = 2 * (w i * w j) := by
  rw [pairBasis, quadForm_add_matrix, quadForm_vecMulVec_pair, quadForm_vecMulVec_pair,
    dot_single_left, dot_single_left]
  ring

/-- An entry of a pair direction, read off explicitly. -/
theorem pairBasis_apply (i j p q : Fin d) :
    pairBasis i j p q = (if p = i then (1 : ℝ) else 0) * (if q = j then (1 : ℝ) else 0)
      + (if p = j then (1 : ℝ) else 0) * (if q = i then (1 : ℝ) else 0) := by
  simp [pairBasis, Matrix.vecMulVec_apply, Pi.single_apply]

/-- The symmetric direction attached to an unordered pair of coordinates. -/
def sym2Basis (z : Sym2 (Fin d)) : Matrix (Fin d) (Fin d) ℝ :=
  Sym2.lift ⟨fun i j ↦ pairBasis i j, fun i j ↦ pairBasis_comm i j⟩ z

/-- The unordered pair direction at a represented pair. -/
theorem sym2Basis_mk (i j : Fin d) : sym2Basis s(i, j) = pairBasis i j :=
  Sym2.lift_mk _ i j

/-- The unordered pair direction is symmetric. -/
theorem sym2Basis_transpose (z : Sym2 (Fin d)) : (sym2Basis z)ᵀ = sym2Basis z := by
  refine Sym2.ind (fun i j ↦ ?_) z
  rw [sym2Basis_mk, pairBasis_transpose]

/-- A nonzero entry of an unordered pair direction pins the pair. -/
theorem sym2Basis_apply_ne_zero (z : Sym2 (Fin d)) (p q : Fin d) (h : sym2Basis z p q ≠ 0) :
    z = s(p, q) := by
  revert h
  refine Sym2.ind (fun i j h ↦ ?_) z
  rw [sym2Basis_mk, pairBasis_apply] at h
  have hcase : (p = i ∧ q = j) ∨ (p = j ∧ q = i) := by
    by_contra hcon
    push_neg at hcon
    apply h
    rcases eq_or_ne p i with hp | hp
    · rw [if_pos hp, if_neg (hcon.1 hp)]
      simp only [one_mul, zero_add]
      rcases eq_or_ne p j with hp' | hp'
      · rw [if_pos hp', if_neg (hcon.2 hp'), mul_zero]
      · rw [if_neg hp', zero_mul]
    · rw [if_neg hp, zero_mul, zero_add]
      rcases eq_or_ne p j with hp' | hp'
      · rw [if_pos hp', if_neg (hcon.2 hp'), mul_zero]
      · rw [if_neg hp', zero_mul]
  rcases hcase with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h1, h2]
  · rw [h1, h2, Sym2.eq_swap]

/-- The diagonal-pair entry of an unordered pair direction is positive. -/
theorem sym2Basis_apply_self (i j : Fin d) : sym2Basis s(i, j) i j ≠ 0 := by
  rw [sym2Basis_mk, pairBasis_apply]
  by_cases h : i = j <;> simp [h]

/-! ## The dimension count -/

/-- The constraint coefficients of the symmetric directions carried by an index set: the trace
in the first row, and the report in each prescribed test direction in the remaining rows. -/
def constraintMatrix (V : Fin mm → Fin d → ℝ) (G : Matrix (Fin d) (Fin d) ℝ)
    (hG : Matrix.IsHermitian G) (S : Finset (Fin d)) :
    Matrix (Fin (mm + 1)) ↥(S.sym2) ℝ :=
  Matrix.of fun k z ↦ Fin.cases (Matrix.trace (sym2Basis (z : Sym2 (Fin d))))
    (fun k' ↦ quadForm (sym2Basis (z : Sym2 (Fin d)))
      ((eigenUnitary G hG)ᵀ.mulVec (V k'))) k

/-- The constraint coefficients as a linear map on coefficient vectors. -/
def constraintMap (V : Fin mm → Fin d → ℝ) (G : Matrix (Fin d) (Fin d) ℝ)
    (hG : Matrix.IsHermitian G) (S : Finset (Fin d)) :
    (↥(S.sym2) → ℝ) →ₗ[ℝ] (Fin (mm + 1) → ℝ) where
  toFun f := (constraintMatrix V G hG S).mulVec f
  map_add' f g := by
    funext k
    simp only [Matrix.mulVec, dotProduct, Pi.add_apply, mul_add]
    rw [Finset.sum_add_distrib]
  map_smul' c f := by
    funext k
    simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul, RingHom.id_apply,
      Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ ↦ by ring

/-- **More symmetric directions than constraints leaves a nonzero direction annihilating all of
them.**  This is the rank-nullity step of the Barvinok-Pataki argument. -/
theorem exists_nonzero_kernel (V : Fin mm → Fin d → ℝ) (G : Matrix (Fin d) (Fin d) ℝ)
    (hG : Matrix.IsHermitian G) (S : Finset (Fin d))
    (hcard : mm + 1 < Fintype.card ↥(S.sym2)) :
    ∃ f : ↥(S.sym2) → ℝ, f ≠ 0 ∧ (constraintMatrix V G hG S).mulVec f = 0 := by
  have hrange : Module.finrank ℝ (LinearMap.range (constraintMap V G hG S)) ≤ mm + 1 := by
    have hle := Submodule.finrank_le (LinearMap.range (constraintMap V G hG S))
    rwa [Module.finrank_fin_fun (R := ℝ)] at hle
  have hsplit := LinearMap.finrank_range_add_finrank_ker (constraintMap V G hG S)
  rw [Module.finrank_pi] at hsplit
  have hpos : 0 < Module.finrank ℝ (LinearMap.ker (constraintMap V G hG S)) := by omega
  have hne : LinearMap.ker (constraintMap V G hG S) ≠ ⊥ := by
    intro hbot
    rw [hbot, finrank_bot] at hpos
    exact lt_irrefl 0 hpos
  obtain ⟨f, hfmem, hfne⟩ := (Submodule.ne_bot_iff _).mp hne
  exact ⟨f, hfne, hfmem⟩

/-! ## The rank bound -/

/-- **PL Corollary 6.3, the Barvinok-Pataki rank bound.**  An extreme point of the feasible
angular set with `m` prescribed reports has `r` positive eigenvalues with `r(r+1)/2 ≤ m + 1`,
written with the binomial coefficient `(r+1).choose 2`, which `Nat.choose_two_right` identifies
with `(r+1)r/2`.  The proof is the perturbation criterion above fed by a rank-nullity count: the
symmetric directions carried by the positive eigenspace outnumber the `m + 1` linear conditions
on trace and reports, so one of them annihilates all of them, and perturbing along it in both
signs exhibits the point as a midpoint of two feasible matrices. -/
theorem extremePoint_rank_bound (V : Fin mm → Fin d → ℝ) (a : Fin mm → ℝ)
    (G : Matrix (Fin d) (Fin d) ℝ) (hG : Matrix.IsHermitian G)
    (hext : G ∈ (feasibleAngular V a).extremePoints ℝ) :
    Nat.choose ((Finset.univ.filter fun i ↦ 0 < hG.eigenvalues i).card + 1) 2 ≤ mm + 1 := by
  classical
  by_contra hcon
  push_neg at hcon
  set S : Finset (Fin d) := Finset.univ.filter fun i ↦ 0 < hG.eigenvalues i with hSdef
  have hSne : S.Nonempty := by
    rcases Finset.eq_empty_or_nonempty S with hemp | hne
    · rw [hemp] at hcon
      simp at hcon
    · exact hne
  have hSpos : ∀ i ∈ S, 0 < hG.eigenvalues i := by
    intro i hi
    rw [hSdef, Finset.mem_filter] at hi
    exact hi.2
  have hcard : mm + 1 < Fintype.card ↥(S.sym2) := by
    rw [Fintype.card_coe, Finset.card_sym2]
    exact hcon
  obtain ⟨f, hfne, hfker⟩ := exists_nonzero_kernel V G hG S hcard
  set C : Matrix (Fin d) (Fin d) ℝ :=
    ∑ z : ↥(S.sym2), f z • sym2Basis (z : Sym2 (Fin d)) with hCdef
  have hCentry : ∀ p q, C p q = ∑ z : ↥(S.sym2), f z * sym2Basis (z : Sym2 (Fin d)) p q := by
    intro p q
    rw [hCdef]
    simp [Matrix.sum_apply]
  have hCsym : Cᵀ = C := by
    ext p q
    rw [Matrix.transpose_apply, hCentry, hCentry]
    refine Finset.sum_congr rfl fun z _ ↦ ?_
    have hz := congrFun (congrFun (sym2Basis_transpose (z : Sym2 (Fin d))) p) q
    rw [Matrix.transpose_apply] at hz
    rw [hz]
  have hCne : C ≠ 0 := by
    obtain ⟨z₀, hz₀⟩ : ∃ z₀ : ↥(S.sym2), f z₀ ≠ 0 := by
      by_contra hall
      push_neg at hall
      exact hfne (funext hall)
    have key : ∀ w : Sym2 (Fin d), w = (z₀ : Sym2 (Fin d)) → C ≠ 0 := by
      refine Sym2.ind fun i j hw ↦ ?_
      have hij : C i j ≠ 0 := by
        rw [hCentry]
        rw [Finset.sum_eq_single z₀]
        · rw [← hw]
          exact mul_ne_zero hz₀ (sym2Basis_apply_self i j)
        · intro b _ hb
          by_contra hbne
          apply hb
          have hb2 : sym2Basis (b : Sym2 (Fin d)) i j ≠ 0 := fun h ↦ hbne (by rw [h, mul_zero])
          have hbeq : (b : Sym2 (Fin d)) = s(i, j) := sym2Basis_apply_ne_zero _ i j hb2
          exact Subtype.ext (by rw [hbeq, hw])
        · intro hmem
          exact absurd (Finset.mem_univ z₀) hmem
      intro hzero
      apply hij
      rw [hzero, Matrix.zero_apply]
    exact key _ rfl
  have hmemS : ∀ p q, C p q ≠ 0 → p ∈ S ∧ q ∈ S := by
    intro p q hpq
    rw [hCentry] at hpq
    obtain ⟨z, -, hz⟩ := Finset.exists_ne_zero_of_sum_ne_zero hpq
    have hbne : sym2Basis (z : Sym2 (Fin d)) p q ≠ 0 := fun h ↦ hz (by rw [h, mul_zero])
    have hzeq : (z : Sym2 (Fin d)) = s(p, q) := sym2Basis_apply_ne_zero _ p q hbne
    have hmem := z.2
    rw [hzeq, Finset.mk_mem_sym2_iff] at hmem
    exact hmem
  set mu : ℝ := S.inf' hSne hG.eigenvalues with hmudef
  have hmupos : 0 < mu := by
    rw [hmudef, Finset.lt_inf'_iff]
    exact hSpos
  have hsuppmu : ∀ p q, C p q ≠ 0 → mu ≤ hG.eigenvalues p ∧ mu ≤ hG.eigenvalues q := by
    intro p q hpq
    obtain ⟨hp, hq⟩ := hmemS p q hpq
    exact ⟨Finset.inf'_le _ hp, Finset.inf'_le _ hq⟩
  set B : ℝ := (∑ p, ∑ q, |C p q|) + 1 with hBdef
  have hsumnn : 0 ≤ ∑ p, ∑ q, |C p q| :=
    Finset.sum_nonneg fun _ _ ↦ Finset.sum_nonneg fun _ _ ↦ abs_nonneg _
  have hBpos : 0 < B := by
    rw [hBdef]
    linarith
  have hBrow : ∀ i, ∑ q, |C i q| ≤ B := by
    intro i
    have hle : ∑ q, |C i q| ≤ ∑ p, ∑ q, |C p q| :=
      Finset.single_le_sum (f := fun p ↦ ∑ q, |C p q|)
        (fun _ _ ↦ Finset.sum_nonneg fun _ _ ↦ abs_nonneg _) (Finset.mem_univ i)
    rw [hBdef]
    linarith
  have hBcol : ∀ j, ∑ p, |C p j| ≤ B := by
    intro j
    have hle : ∑ p, |C p j| ≤ ∑ p, ∑ q, |C p q| :=
      Finset.sum_le_sum fun p _ ↦
        Finset.single_le_sum (f := fun q ↦ |C p q|) (fun _ _ ↦ abs_nonneg _) (Finset.mem_univ j)
    rw [hBdef]
    linarith
  have htrC : Matrix.trace C = 0 := by
    have hexp : Matrix.trace C
        = ∑ z : ↥(S.sym2), f z * Matrix.trace (sym2Basis (z : Sym2 (Fin d))) := by
      rw [hCdef, Matrix.trace_sum]
      exact Finset.sum_congr rfl fun z _ ↦ by rw [Matrix.trace_smul, smul_eq_mul]
    have hmv : ∑ z : ↥(S.sym2), f z * Matrix.trace (sym2Basis (z : Sym2 (Fin d)))
        = (constraintMatrix V G hG S).mulVec f 0 := by
      simp only [Matrix.mulVec, dotProduct, constraintMatrix, Matrix.of_apply, Fin.cases_zero]
      exact Finset.sum_congr rfl fun _ _ ↦ mul_comm _ _
    rw [hexp, hmv, hfker]
    rfl
  have hrepC : ∀ k, quadForm (conjPerturb G hG C) (V k) = 0 := by
    intro k
    rw [quadForm_conjPerturb]
    have hexp : quadForm C ((eigenUnitary G hG)ᵀ.mulVec (V k))
        = ∑ z : ↥(S.sym2), f z * quadForm (sym2Basis (z : Sym2 (Fin d)))
            ((eigenUnitary G hG)ᵀ.mulVec (V k)) := by
      rw [hCdef, quadForm_sum]
      exact Finset.sum_congr rfl fun z _ ↦ quadForm_smul_matrix _ _ _
    have hmv : ∑ z : ↥(S.sym2), f z * quadForm (sym2Basis (z : Sym2 (Fin d)))
          ((eigenUnitary G hG)ᵀ.mulVec (V k))
        = (constraintMatrix V G hG S).mulVec f k.succ := by
      simp only [Matrix.mulVec, dotProduct, constraintMatrix, Matrix.of_apply, Fin.cases_succ]
      exact Finset.sum_congr rfl fun _ _ ↦ mul_comm _ _
    rw [hexp, hmv, hfker]
    rfl
  exact extremePoint_no_supported_direction V a G hG hext C hCsym hCne mu B hmupos hBpos
    hsuppmu hBrow hBcol htrC hrepC

end

end Descent.Portability.AngularExtremePoints
