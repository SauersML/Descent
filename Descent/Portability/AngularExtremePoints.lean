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

end

end Descent.Portability.AngularExtremePoints
