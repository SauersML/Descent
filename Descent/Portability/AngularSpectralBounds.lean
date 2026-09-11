/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.AngularReportClosure

assert_below Descent.Decision Descent.Program

/-!
# Spectral limits, exact feasibility, and angular metric discrepancies

This module proves the parts of PL Corollary 6.3 and PL Theorem 9.2 that concern the feasible
set of angular matrices and the comparison of two of them.

`angular_feasibility` is the boxed feasibility statement PL (6.8): a matrix is the conditional
angular matrix of some finite law on nonzero residual directions exactly when it is positive
semidefinite with trace one.  The hard direction is a construction, not an abstract argument:
`angularEigenLaw` puts the eigenvalue `λ_i` on the `i`-th eigenvector of the matrix, and
`angularMatrix_angularEigenLaw` evaluates the angular matrix of that law to be the target
exactly.  The realized law lives on at most `d` residual directions, which is the support bound
the corollary states for the spectral realization.

`trace_proj_mul_nonneg` and `trace_proj_mul_le_one` are the two-sided bound `0 ≤ tr(PΓ) ≤ 1`
for every orthogonal projection, which is the `k = d` endpoint of (6.7) together with its
trivial endpoint.

For PL Theorem 9.2, `eq_of_quadForm_mono_of_trace_eq` proves the boxed qualitative conclusion:
if expected projection accuracy does not decrease in any direction then the two angular matrices
are equal, so a strict increase somewhere forces a strict decrease somewhere else
(`strict_increase_forces_decrease`).  The proof is elementary, by testing basis vectors and
their weighted pairwise sums; no eigenvalue theory is used.

PL (6.9) is the two-dimensional example.  `two_dim_plus_direction_report` evaluates the report
in the diagonal direction exactly, `two_dim_plus_direction_bound` is the boxed inequality
`|E q_{v₊} − 1/2| ≤ √(a(1−a))`, and `two_dim_plus_direction_attained` realizes every value of
that interval by an explicit finite law through the feasibility theorem.

The Ky Fan identity (6.7) for a general rank `k`, and PL Theorem 9.3, are not proved here; see
the report accompanying this module.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.AngularSpectralBounds

open Foundations Matrix CohortEvaluationOperators AngularReportClosure

noncomputable section

variable {d : ℕ}

/-! ## Elementary positive semidefiniteness -/

/-- A nonnegative quadratic form is Mathlib positive semidefiniteness. -/
theorem posSemidef_of_quadForm_nonneg (G : Matrix (Fin d) (Fin d) ℝ) (hs : Gᵀ = G)
    (h : ∀ v : Fin d → ℝ, 0 ≤ quadForm G v) : Matrix.PosSemidef G := by
  refine ⟨?_, fun x ↦ h x⟩
  unfold Matrix.IsHermitian
  rw [Matrix.conjTranspose_eq_transpose_of_trivial]
  exact hs

/-- Mathlib positive semidefiniteness gives a nonnegative quadratic form. -/
theorem quadForm_nonneg_of_posSemidef (G : Matrix (Fin d) (Fin d) ℝ) (h : Matrix.PosSemidef G)
    (v : Fin d → ℝ) : 0 ≤ quadForm G v := h.2 v

/-- Symmetry read off entrywise. -/
theorem entry_symm (G : Matrix (Fin d) (Fin d) ℝ) (hs : Gᵀ = G) (i j : Fin d) :
    G j i = G i j := by
  have h := congrFun (congrFun hs i) j
  simpa [Matrix.transpose_apply] using h

/-- The quadratic form of a symmetric matrix along a scaled basis vector plus another basis
vector, computed exactly.  This is the test vector both extremality arguments use. -/
theorem quadForm_single_pair (G : Matrix (Fin d) (Fin d) ℝ) (hs : Gᵀ = G) (i j : Fin d)
    (t : ℝ) :
    quadForm G (t • (Pi.single i 1 : Fin d → ℝ) + Pi.single j 1)
      = t ^ 2 * G i i + 2 * t * G i j + G j j := by
  have hi : quadForm G (Pi.single i (1 : ℝ)) = G i i := dot_single_mulVec_single G i i
  have hj : quadForm G (Pi.single j (1 : ℝ)) = G j j := dot_single_mulVec_single G j j
  rw [quadForm_add, quadForm_smul, Matrix.mulVec_smul, dot_smul_left, dot_smul_right,
    dot_single_mulVec_single, dot_single_mulVec_single, hi, hj, entry_symm G hs i j]
  ring

/-- **A symmetric matrix with a nonnegative quadratic form and zero trace is zero.**  Testing
basis vectors kills the diagonal; testing a basis vector scaled by the negated off-diagonal
entry, plus a second basis vector, kills the rest. -/
theorem eq_zero_of_quadForm_nonneg_trace_zero (D : Matrix (Fin d) (Fin d) ℝ) (hD : Dᵀ = D)
    (hpsd : ∀ v : Fin d → ℝ, 0 ≤ quadForm D v) (htr : Matrix.trace D = 0) : D = 0 := by
  have hquad : ∀ i : Fin d, quadForm D (Pi.single i (1 : ℝ)) = D i i := fun i ↦
    dot_single_mulVec_single D i i
  have hdiag : ∀ i, D i i = 0 := by
    have hsum : ∑ i, D i i = 0 := htr
    intro i
    refine (Finset.sum_eq_zero_iff_of_nonneg ?_).mp hsum i (Finset.mem_univ i)
    intro j _
    rw [← hquad j]
    exact hpsd _
  ext i j
  have h := hpsd ((-(D i j)) • (Pi.single i 1 : Fin d → ℝ) + Pi.single j 1)
  rw [quadForm_single_pair D hD i j, hdiag i, hdiag j] at h
  simp only [Matrix.zero_apply]
  nlinarith [sq_nonneg (D i j)]

/-- **PL Theorem 9.2, the boxed qualitative conclusion.**  If the expected projection report
does not decrease in any direction and the two angular matrices carry the same total mass, the
matrices are equal. -/
theorem eq_of_quadForm_mono_of_trace_eq (G₀ G₁ : Matrix (Fin d) (Fin d) ℝ) (h₀ : G₀ᵀ = G₀)
    (h₁ : G₁ᵀ = G₁) (htr : Matrix.trace G₀ = Matrix.trace G₁)
    (hmono : ∀ v : Fin d → ℝ, quadForm G₀ v ≤ quadForm G₁ v) : G₁ = G₀ := by
  have hzero : G₁ - G₀ = 0 := by
    refine eq_zero_of_quadForm_nonneg_trace_zero (G₁ - G₀) ?_ ?_ ?_
    · rw [Matrix.transpose_sub, h₀, h₁]
    · intro v
      rw [quadForm_sub]
      linarith [hmono v]
    · rw [Matrix.trace_sub, htr, sub_self]
  exact sub_eq_zero.mp hzero

/-- **A strict increase somewhere forces a decrease in another direction.**  This is the second
sentence of PL Theorem 9.2's boxed conclusion. -/
theorem strict_increase_forces_decrease (G₀ G₁ : Matrix (Fin d) (Fin d) ℝ) (h₀ : G₀ᵀ = G₀)
    (h₁ : G₁ᵀ = G₁) (htr : Matrix.trace G₀ = Matrix.trace G₁) (w : Fin d → ℝ)
    (hw : quadForm G₀ w < quadForm G₁ w) :
    ∃ v : Fin d → ℝ, quadForm G₁ v < quadForm G₀ v := by
  by_contra hcon
  push_neg at hcon
  have := eq_of_quadForm_mono_of_trace_eq G₀ G₁ h₀ h₁ htr hcon
  rw [this] at hw
  exact lt_irrefl _ hw

/-- **Cauchy-Schwarz for the entries of a positive semidefinite symmetric matrix.**  This is the
inequality `Γ₁₂² ≤ Γ₁₁Γ₂₂` that PL (6.9) invokes. -/
theorem offDiag_sq_le (G : Matrix (Fin d) (Fin d) ℝ) (hs : Gᵀ = G)
    (hpsd : ∀ v : Fin d → ℝ, 0 ≤ quadForm G v) (i j : Fin d) :
    (G i j) ^ 2 ≤ G i i * G j j := by
  have hq : ∀ t : ℝ, 0 ≤ t ^ 2 * G i i + 2 * t * G i j + G j j := by
    intro t
    have h := hpsd (t • (Pi.single i 1 : Fin d → ℝ) + Pi.single j 1)
    rwa [quadForm_single_pair G hs i j] at h
  have hii : 0 ≤ G i i := by
    have hval : quadForm G (Pi.single i (1 : ℝ)) = G i i := dot_single_mulVec_single G i i
    rw [← hval]
    exact hpsd _
  rcases eq_or_lt_of_le hii with h0 | hpos
  · have hij : G i j = 0 := by
      by_contra hne
      have hval := hq (-(G j j + 1) / (2 * G i j))
      have hcalc : 2 * (-(G j j + 1) / (2 * G i j)) * G i j = -(G j j + 1) := by
        field_simp
      rw [← h0, mul_zero, zero_add, hcalc] at hval
      linarith
    rw [hij, ← h0]
    norm_num
  · have hval := hq (-(G i j) / G i i)
    have hne : G i i ≠ 0 := ne_of_gt hpos
    have hcalc : (-(G i j) / G i i) ^ 2 * G i i + 2 * (-(G i j) / G i i) * G i j
        = -((G i j) ^ 2 / G i i) := by
      field_simp
      ring
    rw [hcalc] at hval
    have h2 : 0 ≤ (-((G i j) ^ 2 / G i i) + G j j) * G i i :=
      mul_nonneg hval (le_of_lt hpos)
    have h3 : (-((G i j) ^ 2 / G i i) + G j j) * G i i = -((G i j) ^ 2) + G j j * G i i := by
      field_simp
    rw [h3] at h2
    linarith

/-! ## Trace pairing with an orthogonal projection -/

/-- The diagonal entry of `P G P` is the quadratic form of `G` along a row of `P`. -/
theorem conj_proj_diag (P G : Matrix (Fin d) (Fin d) ℝ) (hPs : Pᵀ = P) (i : Fin d) :
    (P * G * P) i i = quadForm G (fun j ↦ P i j) := by
  simp only [Matrix.mul_apply, quadForm, dot, Descent.Core.innerSum, Matrix.mulVec,
    dotProduct, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ ↦ Finset.sum_congr rfl fun k _ ↦ ?_
  rw [entry_symm P hPs i k]
  ring

/-- **The trace pairing of an orthogonal projection with a positive semidefinite matrix is
nonnegative.**  This is the lower endpoint of PL (6.7). -/
theorem trace_proj_mul_nonneg (P G : Matrix (Fin d) (Fin d) ℝ) (hPs : Pᵀ = P) (hPi : P * P = P)
    (hpsd : ∀ v : Fin d → ℝ, 0 ≤ quadForm G v) : 0 ≤ Matrix.trace (P * G) := by
  have h1 : Matrix.trace (P * G) = Matrix.trace (P * G * P) := by
    nth_rewrite 1 [← hPi]
    rw [Matrix.mul_assoc, Matrix.trace_mul_comm]
  rw [h1]
  simp only [Matrix.trace, Matrix.diag_apply]
  exact Finset.sum_nonneg fun i _ ↦ by rw [conj_proj_diag P G hPs i]; exact hpsd _

/-- **The trace pairing of an orthogonal projection with an angular matrix never exceeds one.**
This is the upper endpoint of PL (6.7), attained at the full-rank projection. -/
theorem trace_proj_mul_le_one (P G : Matrix (Fin d) (Fin d) ℝ) (hPs : Pᵀ = P) (hPi : P * P = P)
    (hpsd : ∀ v : Fin d → ℝ, 0 ≤ quadForm G v) (htr : Matrix.trace G = 1) :
    Matrix.trace (P * G) ≤ 1 := by
  have hres := trace_proj_mul_nonneg (residualMaker P) G (residualMaker_transpose P hPs)
    (residualMaker_mul_self P hPi) hpsd
  have hsplit : Matrix.trace (residualMaker P * G)
      = Matrix.trace G - Matrix.trace (P * G) := by
    rw [residualMaker, Matrix.sub_mul, Matrix.trace_sub, Matrix.one_mul]
  rw [hsplit, htr] at hres
  linarith

/-! ## The spectral realization of an angular matrix -/

/-- The `p`-th eigenvector of a Hermitian matrix, as a plain vector. -/
def angularEigenVector (G : Matrix (Fin d) (Fin d) ℝ) (hG : Matrix.IsHermitian G) :
    Fin d → Fin d → ℝ :=
  fun p j ↦ (Matrix.IsHermitian.eigenvectorUnitary hG : Matrix (Fin d) (Fin d) ℝ) j p

/-- The eigenvectors are unit vectors, so the angular normalization does nothing to them. -/
theorem angularEigenVector_dot_self (G : Matrix (Fin d) (Fin d) ℝ) (hG : Matrix.IsHermitian G)
    (p : Fin d) : dot (angularEigenVector G hG p) (angularEigenVector G hG p) = 1 := by
  have hU : (star (Matrix.IsHermitian.eigenvectorUnitary hG : Matrix (Fin d) (Fin d) ℝ))
      * (Matrix.IsHermitian.eigenvectorUnitary hG : Matrix (Fin d) (Fin d) ℝ) = 1 :=
    (Matrix.mem_unitaryGroup_iff').mp (Matrix.IsHermitian.eigenvectorUnitary hG).2
  have hpp := congrFun (congrFun hU p) p
  rw [Matrix.one_apply_eq] at hpp
  simp only [Matrix.mul_apply, Matrix.star_apply, star_trivial] at hpp
  simpa [dot, Descent.Core.innerSum, angularEigenVector] using hpp

/-- The eigenvectors are nonzero, so the law built on them avoids the degenerate set. -/
theorem angularEigenVector_ne_zero (G : Matrix (Fin d) (Fin d) ℝ) (hG : Matrix.IsHermitian G)
    (p : Fin d) : angularEigenVector G hG p ≠ 0 := by
  intro h
  have h1 := angularEigenVector_dot_self G hG p
  rw [h] at h1
  simp [dot, Descent.Core.innerSum] at h1

/-- **The entrywise spectral theorem.**  Every entry of a Hermitian matrix is the eigenvalue
weighted sum of the products of eigenvector coordinates. -/
theorem eigen_entry (G : Matrix (Fin d) (Fin d) ℝ) (hG : Matrix.IsHermitian G) (j k : Fin d) :
    G j k = ∑ p, hG.eigenvalues p
      * (angularEigenVector G hG p j * angularEigenVector G hG p k) := by
  conv_lhs => rw [hG.spectral_theorem]
  simp only [Matrix.mul_apply, Matrix.star_apply, Matrix.diagonal_apply, Function.comp_apply,
    star_trivial, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true,
    angularEigenVector, RCLike.ofReal_real_eq_id, id_eq]
  exact Finset.sum_congr rfl fun _ _ ↦ by ring

/-- The eigenvalues of a positive semidefinite trace-one matrix are a probability vector. -/
theorem sum_eigenvalues_eq_one (G : Matrix (Fin d) (Fin d) ℝ) (hG : Matrix.IsHermitian G)
    (htr : Matrix.trace G = 1) : ∑ p, hG.eigenvalues p = 1 := by
  have h := hG.trace_eq_sum_eigenvalues
  rw [htr] at h
  simpa using h.symm

/-- **The explicit finite law realizing an angular matrix.**  It places the eigenvalue `λ_p` on
the `p`-th eigenvector of the target matrix, so it lives on at most `d` residual directions. -/
def angularEigenLaw (G : Matrix (Fin d) (Fin d) ℝ) (hG : Matrix.PosSemidef G)
    (htr : Matrix.trace G = 1) : ExpFunctional (Fin d) :=
  weightedExp hG.1.eigenvalues (fun p ↦ hG.eigenvalues_nonneg p)
    (sum_eigenvalues_eq_one G hG.1 htr)

/-- **PL (6.8), the realization.**  The angular matrix of the explicit eigenvalue law on the
eigenvectors is the target matrix exactly. -/
theorem angularMatrix_angularEigenLaw (G : Matrix (Fin d) (Fin d) ℝ) (hG : Matrix.PosSemidef G)
    (htr : Matrix.trace G = 1) :
    angularMatrix (angularEigenLaw G hG htr) (angularEigenVector G hG.1) = G := by
  ext j k
  simp only [angularMatrix, Matrix.of_apply, angularEigenLaw, weightedExp_apply]
  rw [eigen_entry G hG.1 j k]
  exact Finset.sum_congr rfl fun p _ ↦ by
    rw [angularEigenVector_dot_self G hG.1 p, div_one]

/-- **PL (6.8), the exact feasibility statement.**  A matrix is the conditional angular matrix
of a finite law on nonzero directions exactly when it is positive semidefinite with trace one.
Necessity is PL Theorem 6.2; sufficiency is the explicit spectral construction above, which uses
at most `d` residual directions. -/
theorem angular_feasibility (G : Matrix (Fin d) (Fin d) ℝ) :
    (∃ (Ω : Type) (_ : Fintype Ω) (E : ExpFunctional Ω) (V : Ω → Fin d → ℝ),
        (∀ ω, V ω ≠ 0) ∧ angularMatrix E V = G)
      ↔ Matrix.PosSemidef G ∧ Matrix.trace G = 1 := by
  constructor
  · rintro ⟨Ω, _, E, V, hV, rfl⟩
    exact ⟨angularMatrix_posSemidef E V, angularMatrix_trace E V hV⟩
  · rintro ⟨hpsd, htr⟩
    exact ⟨Fin d, inferInstance, angularEigenLaw G hpsd htr, angularEigenVector G hpsd.1,
      angularEigenVector_ne_zero G hpsd.1, angularMatrix_angularEigenLaw G hpsd htr⟩

/-- The realizing law of `angular_feasibility` puts mass exactly the eigenvalue on each
eigendirection, so it puts no mass at all on a direction whose eigenvalue vanishes. -/
theorem angularEigenLaw_weight (G : Matrix (Fin d) (Fin d) ℝ) (hG : Matrix.PosSemidef G)
    (htr : Matrix.trace G = 1) (i : Fin d) :
    angularEigenLaw G hG htr (fun ω ↦ if ω = i then (1 : ℝ) else 0)
      = Matrix.IsHermitian.eigenvalues hG.1 i := by
  simp [angularEigenLaw]

/-- **The support bound of PL Corollary 6.3.**  Together with `angularEigenLaw_weight` this is
the manuscript's "an attaining law on at most `r` residual directions": the realizing law is
carried by the eigendirections of nonzero eigenvalue, and there are exactly `rank Γ` of those. -/
theorem angularEigenLaw_support_card (G : Matrix (Fin d) (Fin d) ℝ)
    (hG : Matrix.IsHermitian G) :
    Fintype.card {i : Fin d // Matrix.IsHermitian.eigenvalues hG i ≠ 0} = Matrix.rank G :=
  (Matrix.IsHermitian.rank_eq_card_non_zero_eigs hG).symm

/-! ## PL (6.9): the two-dimensional example -/

/-- The diagonal direction `v₊ = (v₁ + v₂)/√2` in two coordinates. -/
def plusDirection : Fin 2 → ℝ :=
  fun _ ↦ (Real.sqrt 2)⁻¹

/-- **The exact report in the diagonal direction.**  For a trace-one symmetric matrix it is
`1/2 + Γ₁₂`, so the whole question is the size of the off-diagonal entry. -/
theorem two_dim_plus_direction_report (G : Matrix (Fin 2) (Fin 2) ℝ) (hs : Gᵀ = G)
    (htr : Matrix.trace G = 1) : quadForm G plusDirection = 1 / 2 + G 0 1 := by
  have htr' : G 0 0 + G 1 1 = 1 := by
    simpa [Matrix.trace, Matrix.diag_apply, Fin.sum_univ_two] using htr
  have hsq : (Real.sqrt 2)⁻¹ * (Real.sqrt 2)⁻¹ = 1 / 2 := by
    rw [← mul_inv, ← Real.sqrt_mul_self (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  have hsymm : G 1 0 = G 0 1 := entry_symm G hs 0 1
  have hexp : quadForm G plusDirection
      = (Real.sqrt 2)⁻¹ * (Real.sqrt 2)⁻¹ * (G 0 0 + G 0 1 + G 1 0 + G 1 1) := by
    simp only [quadForm, dot, Descent.Core.innerSum, Matrix.mulVec, dotProduct,
      Fin.sum_univ_two, plusDirection]
    ring
  rw [hexp, hsq, hsymm]
  linarith

/-- **PL (6.9), the boxed inequality.**  With `a = Γ₁₁` the expected report in the diagonal
direction differs from `1/2` by at most `√(a(1−a))`. -/
theorem two_dim_plus_direction_bound (G : Matrix (Fin 2) (Fin 2) ℝ) (hs : Gᵀ = G)
    (hpsd : ∀ v : Fin 2 → ℝ, 0 ≤ quadForm G v) (htr : Matrix.trace G = 1) :
    |quadForm G plusDirection - 1 / 2| ≤ Real.sqrt (G 0 0 * (1 - G 0 0)) := by
  have htr' : G 0 0 + G 1 1 = 1 := by
    simpa [Matrix.trace, Matrix.diag_apply, Fin.sum_univ_two] using htr
  have hrep := two_dim_plus_direction_report G hs htr
  have hcs := offDiag_sq_le G hs hpsd 0 1
  have h11 : G 1 1 = 1 - G 0 0 := by linarith
  rw [hrep]
  have habs : |1 / 2 + G 0 1 - 1 / 2| = |G 0 1| := by
    congr 1
    ring
  rw [habs, ← Real.sqrt_sq_eq_abs (G 0 1)]
  refine Real.sqrt_le_sqrt ?_
  rw [← h11]
  exact hcs

/-- **PL (6.9), attainment.**  Every off-diagonal value permitted by the inequality is realized
by an explicit finite law, so the whole interval of reports occurs.  The realizing law is the
spectral construction of `angularEigenLaw` applied to the two by two matrix displayed here. -/
theorem two_dim_plus_direction_attained (a rho : ℝ) (ha0 : 0 ≤ a)
    (hrho : rho ^ 2 ≤ a * (1 - a)) :
    ∃ (E : ExpFunctional (Fin 2)) (V : Fin 2 → Fin 2 → ℝ),
      (∀ ω, V ω ≠ 0) ∧ Matrix.trace (angularMatrix E V) = 1 ∧
        quadForm (angularMatrix E V) plusDirection = 1 / 2 + rho := by
  set G : Matrix (Fin 2) (Fin 2) ℝ := Matrix.of ![![a, rho], ![rho, 1 - a]] with hGdef
  have hentry00 : G 0 0 = a := rfl
  have hentry01 : G 0 1 = rho := rfl
  have hentry10 : G 1 0 = rho := rfl
  have hentry11 : G 1 1 = 1 - a := rfl
  have hs : Gᵀ = G := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hGdef]
  have htr : Matrix.trace G = 1 := by
    simp only [Matrix.trace, Matrix.diag_apply, Fin.sum_univ_two, hentry00, hentry11]
    ring
  have hpsd : ∀ v : Fin 2 → ℝ, 0 ≤ quadForm G v := by
    intro v
    have hval : quadForm G v = a * v 0 ^ 2 + 2 * rho * (v 0 * v 1) + (1 - a) * v 1 ^ 2 := by
      simp only [quadForm, dot, Descent.Core.innerSum, Matrix.mulVec, dotProduct,
        Fin.sum_univ_two, hentry00, hentry01, hentry10, hentry11]
      ring
    rw [hval]
    rcases eq_or_lt_of_le ha0 with h0 | hpos
    · have hr : rho = 0 := by nlinarith [sq_nonneg rho]
      rw [hr, ← h0]
      nlinarith [sq_nonneg (v 1)]
    · nlinarith [sq_nonneg (a * v 0 + rho * v 1), sq_nonneg (v 1), hpos]
  have hpos : Matrix.PosSemidef G := posSemidef_of_quadForm_nonneg G hs hpsd
  refine ⟨angularEigenLaw G hpos htr, angularEigenVector G hpos.1,
    angularEigenVector_ne_zero G hpos.1, ?_, ?_⟩
  · rw [angularMatrix_angularEigenLaw G hpos htr]
    exact htr
  · rw [angularMatrix_angularEigenLaw G hpos htr,
      two_dim_plus_direction_report G hs htr, hentry01]

end

end Descent.Portability.AngularSpectralBounds
