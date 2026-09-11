/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.AngularSpectralBounds

assert_below Descent.Decision Descent.Program

/-!
# Extremal projection reports and exact angular metric discrepancies

This module proves the two remaining boxed extremal formulas of the reporting layer, both by
conjugating with the eigenvector unitary of the matrix being paired against.

`trace_mul_eq_sum_eigen` is the working identity: the trace pairing of any fixed matrix with a
symmetric matrix is the eigenvalue weighted sum of the quadratic forms of that fixed matrix
along the eigenvectors.  `quadForm_eq_sum_eigen` is its rank-one companion, and
`sum_sq_eigen_coeff` is the Parseval identity for the eigenvector coordinates.

PL (6.7), the Ky Fan identity, is `kyFan_isGreatest`: among orthogonal projections of trace `k`,
equivalently of rank `k`, the largest trace pairing with an angular matrix is the largest sum of
`k` of its eigenvalues.  "The sum of the `k` largest eigenvalues" is written as the maximum over
`k`-element index sets, which needs no sorting.  The maximizer is realized by the explicit
spectral projection `eigenSubsetProj`, so the identity is an attained maximum and not only a
bound.  The upper bound is `sum_weight_le_powersetCard_sup`, an exchange argument: at a
maximizing index set every selected eigenvalue dominates every unselected one, and that single
threshold value dominates the whole fractional relaxation.

PL (9.4) is two formulas about the difference `D = Γ₁ − Γ₀` of two angular matrices.  The first,
`quadForm_abs_isGreatest`, evaluates the largest absolute quadratic form over unit directions as
the largest absolute eigenvalue, which for a symmetric matrix is its spectral norm.  The second,
`trace_pairing_abs_isGreatest`, evaluates the largest absolute trace pairing over matrices
between `0` and the identity as half the sum of the absolute eigenvalues, which for a symmetric
matrix is half its trace norm; the maximum is attained by the orthogonal projection onto the
positive eigenspace, exactly as the manuscript states.  The trace-zero hypothesis is the
manuscript's own: both angular matrices have trace one, so their difference has trace zero.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.AngularExtremalReports

open Foundations Matrix CohortEvaluationOperators AngularReportClosure AngularSpectralBounds

noncomputable section

variable {d : ℕ}

/-! ## The eigenvector unitary as a change of basis -/

/-- The eigenvector unitary of a symmetric matrix, as a plain matrix. -/
def eigenUnitary (G : Matrix (Fin d) (Fin d) ℝ) (hG : Matrix.IsHermitian G) :
    Matrix (Fin d) (Fin d) ℝ :=
  (Matrix.IsHermitian.eigenvectorUnitary hG : Matrix (Fin d) (Fin d) ℝ)

/-- The columns of the eigenvector unitary are the eigenvectors. -/
theorem angularEigenVector_eq_col (G : Matrix (Fin d) (Fin d) ℝ) (hG : Matrix.IsHermitian G)
    (p j : Fin d) : angularEigenVector G hG p j = eigenUnitary G hG j p := rfl

/-- The eigenvector unitary has orthonormal columns. -/
theorem eigenUnitary_transpose_mul (G : Matrix (Fin d) (Fin d) ℝ) (hG : Matrix.IsHermitian G) :
    (eigenUnitary G hG)ᵀ * eigenUnitary G hG = 1 := by
  have h := (Matrix.mem_unitaryGroup_iff').mp (Matrix.IsHermitian.eigenvectorUnitary hG).2
  rwa [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial] at h

/-- The eigenvector unitary has orthonormal rows. -/
theorem eigenUnitary_mul_transpose (G : Matrix (Fin d) (Fin d) ℝ) (hG : Matrix.IsHermitian G) :
    eigenUnitary G hG * (eigenUnitary G hG)ᵀ = 1 := by
  have h := (Matrix.mem_unitaryGroup_iff).mp (Matrix.IsHermitian.eigenvectorUnitary hG).2
  rwa [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial] at h

/-- The real spectral decomposition, with the transpose in place of the star. -/
theorem spectral_conj (G : Matrix (Fin d) (Fin d) ℝ) (hG : Matrix.IsHermitian G) :
    G = eigenUnitary G hG * Matrix.diagonal hG.eigenvalues * (eigenUnitary G hG)ᵀ := by
  have h := hG.spectral_theorem
  rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial] at h
  simpa [eigenUnitary, Function.comp_def, RCLike.ofReal_real_eq_id, id_eq] using h

/-- Trace against a diagonal matrix reads off the diagonal. -/
theorem trace_mul_diagonal (M : Matrix (Fin d) (Fin d) ℝ) (f : Fin d → ℝ) :
    Matrix.trace (M * Matrix.diagonal f) = ∑ i, M i i * f i := by
  simp [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.diagonal_apply, mul_ite]

/-- The quadratic form of a diagonal matrix. -/
theorem quadForm_diagonal (f w : Fin d → ℝ) :
    quadForm (Matrix.diagonal f) w = ∑ i, f i * w i ^ 2 := by
  simp only [quadForm, dot, Descent.Core.innerSum, Matrix.mulVec_diagonal]
  exact Finset.sum_congr rfl fun _ _ ↦ by ring

/-- A diagonal entry of the conjugated matrix is the quadratic form along an eigenvector. -/
theorem diag_conj_eq_quadForm (A G : Matrix (Fin d) (Fin d) ℝ) (hG : Matrix.IsHermitian G)
    (i : Fin d) :
    ((eigenUnitary G hG)ᵀ * A * eigenUnitary G hG) i i
      = quadForm A (angularEigenVector G hG i) := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply, quadForm, dot, Descent.Core.innerSum,
    Matrix.mulVec, dotProduct, angularEigenVector, eigenUnitary, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ ↦ Finset.sum_congr rfl fun _ _ ↦ by ring

/-- **The trace pairing is the eigenvalue weighted sum of the quadratic forms along the
eigenvectors.**  Every extremal statement below is this identity plus a scalar optimization. -/
theorem trace_mul_eq_sum_eigen (A G : Matrix (Fin d) (Fin d) ℝ) (hG : Matrix.IsHermitian G) :
    Matrix.trace (A * G)
      = ∑ i, hG.eigenvalues i * quadForm A (angularEigenVector G hG i) := by
  conv_lhs => rw [spectral_conj G hG]
  have hassoc : A * (eigenUnitary G hG * Matrix.diagonal hG.eigenvalues * (eigenUnitary G hG)ᵀ)
      = (A * eigenUnitary G hG * Matrix.diagonal hG.eigenvalues) * (eigenUnitary G hG)ᵀ := by
    simp [Matrix.mul_assoc]
  rw [hassoc, Matrix.trace_mul_comm, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
    trace_mul_diagonal]
  exact Finset.sum_congr rfl fun i _ ↦ by rw [diag_conj_eq_quadForm]; ring

/-- The eigenvector coordinates of a vector. -/
theorem eigen_coeff (G : Matrix (Fin d) (Fin d) ℝ) (hG : Matrix.IsHermitian G) (v : Fin d → ℝ)
    (i : Fin d) : ((eigenUnitary G hG)ᵀ.mulVec v) i = dot (angularEigenVector G hG i) v := by
  simp [Matrix.mulVec, dotProduct, dot, Descent.Core.innerSum, Matrix.transpose_apply,
    angularEigenVector, eigenUnitary]

/-- **Parseval.**  The squared eigenvector coordinates sum to the squared length. -/
theorem sum_sq_eigen_coeff (G : Matrix (Fin d) (Fin d) ℝ) (hG : Matrix.IsHermitian G)
    (v : Fin d → ℝ) : ∑ i, (dot (angularEigenVector G hG i) v) ^ 2 = dot v v := by
  have hsq : dot ((eigenUnitary G hG)ᵀ.mulVec v) ((eigenUnitary G hG)ᵀ.mulVec v)
      = quadForm (eigenUnitary G hG * (eigenUnitary G hG)ᵀ) v := by
    rw [dot_mulVec_self, Matrix.transpose_transpose]
  rw [eigenUnitary_mul_transpose, quadForm_one] at hsq
  have hself : ∀ w : Fin d → ℝ, dot w w = ∑ i, w i * w i := fun _ ↦ rfl
  rw [← hsq, hself]
  exact Finset.sum_congr rfl fun i _ ↦ by rw [eigen_coeff]; ring

/-- **The quadratic form in the eigenbasis.** -/
theorem quadForm_eq_sum_eigen (G : Matrix (Fin d) (Fin d) ℝ) (hG : Matrix.IsHermitian G)
    (v : Fin d → ℝ) :
    quadForm G v = ∑ i, hG.eigenvalues i * (dot (angularEigenVector G hG i) v) ^ 2 := by
  have hc : quadForm (Matrix.diagonal hG.eigenvalues) ((eigenUnitary G hG)ᵀ.mulVec v)
      = quadForm G v := by
    rw [quadForm_conj, Matrix.transpose_transpose, ← spectral_conj]
  rw [← hc, quadForm_diagonal]
  exact Finset.sum_congr rfl fun i _ ↦ by rw [eigen_coeff]

/-- The eigenvectors are orthonormal. -/
theorem eigen_coeff_eigenVector (G : Matrix (Fin d) (Fin d) ℝ) (hG : Matrix.IsHermitian G)
    (i j : Fin d) :
    dot (angularEigenVector G hG i) (angularEigenVector G hG j) = if i = j then 1 else 0 := by
  have hU := eigenUnitary_transpose_mul G hG
  have hij := congrFun (congrFun hU i) j
  rw [Matrix.one_apply] at hij
  simp only [Matrix.mul_apply, Matrix.transpose_apply] at hij
  simpa [dot, Descent.Core.innerSum, angularEigenVector, eigenUnitary] using hij

/-- Evaluating the quadratic form at an eigenvector returns the eigenvalue. -/
theorem quadForm_at_eigenVector (G : Matrix (Fin d) (Fin d) ℝ) (hG : Matrix.IsHermitian G)
    (j : Fin d) :
    quadForm G (angularEigenVector G hG j) = hG.eigenvalues j := by
  rw [quadForm_eq_sum_eigen G hG]
  rw [Finset.sum_eq_single j]
  · rw [eigen_coeff_eigenVector, if_pos rfl]
    ring
  · intro b _ hb
    rw [eigen_coeff_eigenVector, if_neg hb]
    ring
  · intro h
    exact absurd (Finset.mem_univ j) h

/-! ## PL (9.4), first formula: the largest absolute quadratic form -/

/-- **PL (9.4), first formula.**  Over unit directions the largest absolute quadratic form of a
symmetric matrix is its largest absolute eigenvalue, which is its spectral norm.  The maximum is
attained, at an eigenvector of a largest absolute eigenvalue. -/
theorem quadForm_abs_isGreatest (G : Matrix (Fin d) (Fin d) ℝ) (hG : Matrix.IsHermitian G)
    (hne : (Finset.univ : Finset (Fin d)).Nonempty) :
    IsGreatest {t : ℝ | ∃ v : Fin d → ℝ, dot v v = 1 ∧ t = |quadForm G v|}
      (Finset.univ.sup' hne fun i ↦ |hG.eigenvalues i|) := by
  obtain ⟨j, _, hj⟩ := Finset.exists_mem_eq_sup' hne fun i ↦ |hG.eigenvalues i|
  constructor
  · refine ⟨angularEigenVector G hG j, ?_, ?_⟩
    · exact angularEigenVector_dot_self G hG j
    · rw [quadForm_at_eigenVector, hj]
  · rintro t ⟨v, hv, rfl⟩
    set M := Finset.univ.sup' hne fun i ↦ |hG.eigenvalues i| with hM
    have hbound : ∀ i : Fin d, |hG.eigenvalues i| ≤ M := fun i ↦
      Finset.le_sup' (fun i ↦ |hG.eigenvalues i|) (Finset.mem_univ i)
    rw [quadForm_eq_sum_eigen G hG]
    calc |∑ i, hG.eigenvalues i * (dot (angularEigenVector G hG i) v) ^ 2|
        ≤ ∑ i, |hG.eigenvalues i * (dot (angularEigenVector G hG i) v) ^ 2| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i, M * (dot (angularEigenVector G hG i) v) ^ 2 := by
          refine Finset.sum_le_sum fun i _ ↦ ?_
          rw [abs_mul, abs_of_nonneg (sq_nonneg (dot (angularEigenVector G hG i) v))]
          exact mul_le_mul_of_nonneg_right (hbound i) (sq_nonneg _)
      _ = M * ∑ i, (dot (angularEigenVector G hG i) v) ^ 2 := by rw [Finset.mul_sum]
      _ = M := by rw [sum_sq_eigen_coeff, hv, mul_one]

/-! ## Spectral projections onto index sets -/

/-- The orthogonal projection onto the span of a set of eigenvectors. -/
def eigenSubsetProj (G : Matrix (Fin d) (Fin d) ℝ) (hG : Matrix.IsHermitian G)
    (S : Finset (Fin d)) : Matrix (Fin d) (Fin d) ℝ :=
  eigenUnitary G hG * Matrix.diagonal (fun i ↦ if i ∈ S then (1 : ℝ) else 0)
    * (eigenUnitary G hG)ᵀ

/-- The indicator diagonal is idempotent. -/
theorem indicator_diagonal_mul_self (S : Finset (Fin d)) :
    Matrix.diagonal (fun i ↦ if i ∈ S then (1 : ℝ) else 0)
        * Matrix.diagonal (fun i ↦ if i ∈ S then (1 : ℝ) else 0)
      = Matrix.diagonal (fun i ↦ if i ∈ S then (1 : ℝ) else 0) := by
  rw [Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  by_cases h : i ∈ S <;> simp [h]

/-- The spectral projection is symmetric. -/
theorem eigenSubsetProj_transpose (G : Matrix (Fin d) (Fin d) ℝ) (hG : Matrix.IsHermitian G)
    (S : Finset (Fin d)) : (eigenSubsetProj G hG S)ᵀ = eigenSubsetProj G hG S := by
  simp [eigenSubsetProj, Matrix.transpose_mul, Matrix.diagonal_transpose, Matrix.mul_assoc]

/-- The spectral projection is idempotent. -/
theorem eigenSubsetProj_mul_self (G : Matrix (Fin d) (Fin d) ℝ) (hG : Matrix.IsHermitian G)
    (S : Finset (Fin d)) :
    eigenSubsetProj G hG S * eigenSubsetProj G hG S = eigenSubsetProj G hG S := by
  have hU := eigenUnitary_transpose_mul G hG
  have hD := indicator_diagonal_mul_self S
  calc eigenSubsetProj G hG S * eigenSubsetProj G hG S
      = eigenUnitary G hG * (Matrix.diagonal (fun i ↦ if i ∈ S then (1 : ℝ) else 0)
          * ((eigenUnitary G hG)ᵀ * eigenUnitary G hG)
          * Matrix.diagonal (fun i ↦ if i ∈ S then (1 : ℝ) else 0))
          * (eigenUnitary G hG)ᵀ := by
        simp [eigenSubsetProj, Matrix.mul_assoc]
    _ = eigenSubsetProj G hG S := by
        rw [hU, Matrix.mul_one, hD, eigenSubsetProj]

/-- The conjugate of a spectral projection is its indicator diagonal. -/
theorem conj_eigenSubsetProj (G : Matrix (Fin d) (Fin d) ℝ) (hG : Matrix.IsHermitian G)
    (S : Finset (Fin d)) :
    (eigenUnitary G hG)ᵀ * eigenSubsetProj G hG S * eigenUnitary G hG
      = Matrix.diagonal (fun i ↦ if i ∈ S then (1 : ℝ) else 0) := by
  have hU := eigenUnitary_transpose_mul G hG
  calc (eigenUnitary G hG)ᵀ * eigenSubsetProj G hG S * eigenUnitary G hG
      = ((eigenUnitary G hG)ᵀ * eigenUnitary G hG)
          * Matrix.diagonal (fun i ↦ if i ∈ S then (1 : ℝ) else 0)
          * ((eigenUnitary G hG)ᵀ * eigenUnitary G hG) := by
        simp [eigenSubsetProj, Matrix.mul_assoc]
    _ = Matrix.diagonal (fun i ↦ if i ∈ S then (1 : ℝ) else 0) := by
        rw [hU, Matrix.one_mul, Matrix.mul_one]

/-- The quadratic form of a spectral projection along an eigenvector is the indicator. -/
theorem quadForm_eigenSubsetProj_eigenVector (G : Matrix (Fin d) (Fin d) ℝ)
    (hG : Matrix.IsHermitian G) (S : Finset (Fin d)) (i : Fin d) :
    quadForm (eigenSubsetProj G hG S) (angularEigenVector G hG i)
      = if i ∈ S then (1 : ℝ) else 0 := by
  rw [← diag_conj_eq_quadForm (eigenSubsetProj G hG S) G hG i, conj_eigenSubsetProj,
    Matrix.diagonal_apply_eq]

/-- The trace of a spectral projection is the size of its index set, that is its rank. -/
theorem trace_eigenSubsetProj (G : Matrix (Fin d) (Fin d) ℝ) (hG : Matrix.IsHermitian G)
    (S : Finset (Fin d)) : Matrix.trace (eigenSubsetProj G hG S) = (S.card : ℝ) := by
  have hU := eigenUnitary_transpose_mul G hG
  rw [eigenSubsetProj, Matrix.trace_mul_comm, ← Matrix.mul_assoc, hU, Matrix.one_mul,
    Matrix.trace_diagonal]
  simp

/-- The trace pairing of a spectral projection with the matrix is the sum of the selected
eigenvalues. -/
theorem trace_eigenSubsetProj_mul (G : Matrix (Fin d) (Fin d) ℝ) (hG : Matrix.IsHermitian G)
    (S : Finset (Fin d)) :
    Matrix.trace (eigenSubsetProj G hG S * G) = ∑ i ∈ S, hG.eigenvalues i := by
  rw [trace_mul_eq_sum_eigen (eigenSubsetProj G hG S) G hG]
  have hstep : ∀ i : Fin d,
      hG.eigenvalues i * quadForm (eigenSubsetProj G hG S) (angularEigenVector G hG i)
        = if i ∈ S then hG.eigenvalues i else 0 := by
    intro i
    rw [quadForm_eigenSubsetProj_eigenVector]
    by_cases h : i ∈ S <;> simp [h]
  rw [Finset.sum_congr rfl fun i _ ↦ hstep i, Finset.sum_ite_mem, Finset.univ_inter]

/-! ## PL (6.7): the Ky Fan identity -/

/-- **The fractional relaxation bound.**  A weight vector in the unit cube with total mass `k`
cannot beat the best `k` coordinates.  At a maximizing index set every selected value dominates
every unselected one, and that threshold dominates the whole relaxation. -/
theorem sum_weight_le_powersetCard_sup {k : ℕ} (lam b : Fin d → ℝ) (hb0 : ∀ i, 0 ≤ b i)
    (hb1 : ∀ i, b i ≤ 1) (hbs : ∑ i, b i = (k : ℝ))
    (hne : ((Finset.univ : Finset (Fin d)).powersetCard k).Nonempty) :
    ∑ i, lam i * b i
      ≤ ((Finset.univ : Finset (Fin d)).powersetCard k).sup' hne fun S ↦ ∑ i ∈ S, lam i := by
  obtain ⟨T, hT, hTsup⟩ :=
    Finset.exists_mem_eq_sup' hne fun S ↦ ∑ i ∈ S, lam i
  rw [Finset.mem_powersetCard] at hT
  obtain ⟨-, hTcard⟩ := hT
  rw [hTsup]
  rcases Nat.eq_zero_or_pos k with hk0 | hkpos
  · have hTempty : T = ∅ := Finset.card_eq_zero.mp (by rw [hTcard, hk0])
    have hball : ∀ i : Fin d, b i = 0 := by
      intro i
      refine (Finset.sum_eq_zero_iff_of_nonneg fun j _ ↦ hb0 j).mp ?_ i (Finset.mem_univ i)
      rw [hbs, hk0]
      norm_num
    rw [hTempty, Finset.sum_empty]
    refine le_of_eq (Finset.sum_eq_zero fun i _ ↦ ?_)
    rw [hball i, mul_zero]
  · have hTne : T.Nonempty := Finset.card_pos.mp (by rw [hTcard]; exact hkpos)
    obtain ⟨i₀, hi₀, hc⟩ := Finset.exists_mem_eq_inf' hTne lam
    have hin : ∀ i ∈ T, lam i₀ ≤ lam i := by
      intro i hi
      rw [← hc]
      exact Finset.inf'_le lam hi
    have hout : ∀ i, i ∉ T → lam i ≤ lam i₀ := by
      intro j hj
      have hmem : insert j (T.erase i₀) ∈ (Finset.univ : Finset (Fin d)).powersetCard k := by
        rw [Finset.mem_powersetCard]
        refine ⟨Finset.subset_univ _, ?_⟩
        rw [Finset.card_insert_of_notMem, Finset.card_erase_of_mem hi₀, hTcard]
        · omega
        · exact fun hmem ↦ hj (Finset.mem_of_mem_erase hmem)
      have hle : ∑ i ∈ insert j (T.erase i₀), lam i ≤ ∑ i ∈ T, lam i := by
        rw [← hTsup]
        exact Finset.le_sup' (fun S ↦ ∑ i ∈ S, lam i) hmem
      rw [Finset.sum_insert (fun hmem ↦ hj (Finset.mem_of_mem_erase hmem))] at hle
      have hsplit : ∑ i ∈ T.erase i₀, lam i = ∑ i ∈ T, lam i - lam i₀ := by
        rw [eq_sub_iff_add_eq, Finset.sum_erase_add _ _ hi₀]
      rw [hsplit] at hle
      linarith
    have hind : ∑ i, lam i * (if i ∈ T then (1 : ℝ) else 0) = ∑ i ∈ T, lam i := by
      have hpt : ∀ i : Fin d, lam i * (if i ∈ T then (1 : ℝ) else 0)
          = if i ∈ T then lam i else 0 := by
        intro i
        by_cases h : i ∈ T <;> simp [h]
      rw [Finset.sum_congr rfl fun i _ ↦ hpt i, Finset.sum_ite_mem, Finset.univ_inter]
    have hmass : ∑ i, (if i ∈ T then (1 : ℝ) else 0) = (k : ℝ) := by
      rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul, mul_one,
        hTcard]
    have hterm : ∀ i : Fin d,
        lam i * b i - lam i * (if i ∈ T then (1 : ℝ) else 0)
          ≤ lam i₀ * (b i - (if i ∈ T then (1 : ℝ) else 0)) := by
      intro i
      by_cases h : i ∈ T
      · simp only [h, if_true]
        have h1 : b i - 1 ≤ 0 := by linarith [hb1 i]
        nlinarith [hin i h, h1]
      · simp only [h, if_false]
        nlinarith [hout i h, hb0 i]
    have hsum : ∑ i, (lam i * b i - lam i * (if i ∈ T then (1 : ℝ) else 0))
        ≤ ∑ i, lam i₀ * (b i - (if i ∈ T then (1 : ℝ) else 0)) :=
      Finset.sum_le_sum fun i _ ↦ hterm i
    rw [Finset.sum_sub_distrib] at hsum
    have hrhs : ∑ i, lam i₀ * (b i - (if i ∈ T then (1 : ℝ) else 0)) = 0 := by
      rw [← Finset.mul_sum, Finset.sum_sub_distrib, hbs, hmass, sub_self, mul_zero]
    rw [hrhs, hind] at hsum
    linarith

/-- **PL (6.7), the Ky Fan identity.**  Among orthogonal projections of trace `k`, equivalently
of rank `k`, the largest trace pairing with an angular matrix is the largest sum of `k` of its
eigenvalues.  The maximum is attained, by the spectral projection onto a maximizing set of
eigenvectors.  Only symmetry of the matrix is used; the angular hypotheses of positive
semidefiniteness and unit trace are not needed for the identity itself. -/
theorem kyFan_isGreatest (G : Matrix (Fin d) (Fin d) ℝ) (hG : Matrix.IsHermitian G) (k : ℕ)
    (hne : ((Finset.univ : Finset (Fin d)).powersetCard k).Nonempty) :
    IsGreatest
      {t : ℝ | ∃ P : Matrix (Fin d) (Fin d) ℝ, Pᵀ = P ∧ P * P = P ∧
        Matrix.trace P = (k : ℝ) ∧ t = Matrix.trace (P * G)}
      (((Finset.univ : Finset (Fin d)).powersetCard k).sup' hne fun S ↦ ∑ i ∈ S, hG.eigenvalues i)
      := by
  obtain ⟨T, hT, hTsup⟩ :=
    Finset.exists_mem_eq_sup' hne fun S ↦ ∑ i ∈ S, hG.eigenvalues i
  rw [Finset.mem_powersetCard] at hT
  obtain ⟨-, hTcard⟩ := hT
  constructor
  · refine ⟨eigenSubsetProj G hG T, eigenSubsetProj_transpose G hG T,
      eigenSubsetProj_mul_self G hG T, ?_, ?_⟩
    · rw [trace_eigenSubsetProj, hTcard]
    · rw [trace_eigenSubsetProj_mul, hTsup]
  · rintro t ⟨P, hPs, hPi, hPtr, rfl⟩
    rw [trace_mul_eq_sum_eigen P G hG]
    refine sum_weight_le_powersetCard_sup hG.eigenvalues
      (fun i ↦ quadForm P (angularEigenVector G hG i)) ?_ ?_ ?_ hne
    · intro i
      exact quadForm_proj_nonneg P hPs hPi _
    · intro i
      have hcomp : 0 ≤ quadForm (residualMaker P) (angularEigenVector G hG i) :=
        quadForm_proj_nonneg _ (residualMaker_transpose P hPs) (residualMaker_mul_self P hPi) _
      rw [residualMaker, quadForm_sub, quadForm_one,
        angularEigenVector_dot_self G hG i] at hcomp
      linarith
    · have hconj : ∀ i : Fin d, quadForm P (angularEigenVector G hG i)
          = ((eigenUnitary G hG)ᵀ * P * eigenUnitary G hG) i i := fun i ↦
        (diag_conj_eq_quadForm P G hG i).symm
      rw [Finset.sum_congr rfl fun i _ ↦ hconj i]
      have htr : Matrix.trace ((eigenUnitary G hG)ᵀ * P * eigenUnitary G hG)
          = Matrix.trace P := by
        rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, eigenUnitary_mul_transpose,
          Matrix.one_mul]
      rw [show ∑ i, ((eigenUnitary G hG)ᵀ * P * eigenUnitary G hG) i i
          = Matrix.trace ((eigenUnitary G hG)ᵀ * P * eigenUnitary G hG) from rfl, htr, hPtr]

/-! ## PL (9.4), second formula: the largest absolute trace pairing -/

/-- The positive eigenvalue index set of a symmetric matrix. -/
def positiveEigenSet (G : Matrix (Fin d) (Fin d) ℝ) (hG : Matrix.IsHermitian G) :
    Finset (Fin d) :=
  Finset.univ.filter fun i ↦ 0 < hG.eigenvalues i

/-- The sum of the positive eigenvalues is half the sum of the absolute eigenvalues when the
trace vanishes.  This is the trace-norm identity the manuscript uses. -/
theorem sum_pos_eigen_eq_half_abs (G : Matrix (Fin d) (Fin d) ℝ) (hG : Matrix.IsHermitian G)
    (htr : Matrix.trace G = 0) :
    ∑ i ∈ positiveEigenSet G hG, hG.eigenvalues i = (∑ i, |hG.eigenvalues i|) / 2 := by
  have hsum : ∑ i, hG.eigenvalues i = 0 := by
    have h := hG.trace_eq_sum_eigenvalues
    rw [htr] at h
    simpa using h.symm
  have habs : ∀ i : Fin d,
      |hG.eigenvalues i|
        = 2 * (if i ∈ positiveEigenSet G hG then hG.eigenvalues i else 0) - hG.eigenvalues i := by
    intro i
    by_cases h : 0 < hG.eigenvalues i
    · have hmem : i ∈ positiveEigenSet G hG := by
        simp [positiveEigenSet, h]
      rw [if_pos hmem, abs_of_pos h]
      ring
    · have hmem : i ∉ positiveEigenSet G hG := by
        simp [positiveEigenSet, h]
      rw [if_neg hmem, abs_of_nonpos (not_lt.mp h)]
      ring
  rw [Finset.sum_congr rfl fun i _ ↦ habs i, Finset.sum_sub_distrib, hsum, ← Finset.mul_sum,
    Finset.sum_ite_mem, Finset.univ_inter]
  ring

/-- **PL (9.4), second formula.**  Over the matrices between zero and the identity, the largest
absolute trace pairing with a symmetric trace-zero matrix is half the sum of the absolute
eigenvalues, that is half its trace norm, and the maximum is attained by the orthogonal
projection onto its positive eigenspace.  The order conditions `0 ⪯ B ⪯ I` are written as
inequalities between quadratic forms, so no order-theoretic interface is assumed. -/
theorem trace_pairing_abs_isGreatest (D : Matrix (Fin d) (Fin d) ℝ) (hD : Matrix.IsHermitian D)
    (htr : Matrix.trace D = 0) :
    IsGreatest
      {t : ℝ | ∃ B : Matrix (Fin d) (Fin d) ℝ, Bᵀ = B ∧ (∀ v, 0 ≤ quadForm B v) ∧
        (∀ v, quadForm B v ≤ dot v v) ∧ t = |Matrix.trace (B * D)|}
      ((∑ i, |hD.eigenvalues i|) / 2) := by
  have hpos := sum_pos_eigen_eq_half_abs D hD htr
  constructor
  · refine ⟨eigenSubsetProj D hD (positiveEigenSet D hD), eigenSubsetProj_transpose D hD _,
      ?_, ?_, ?_⟩
    · intro v
      exact quadForm_proj_nonneg _ (eigenSubsetProj_transpose D hD _)
        (eigenSubsetProj_mul_self D hD _) v
    · intro v
      have hcomp : 0 ≤ quadForm (residualMaker (eigenSubsetProj D hD (positiveEigenSet D hD))) v :=
        quadForm_proj_nonneg _
          (residualMaker_transpose _ (eigenSubsetProj_transpose D hD _))
          (residualMaker_mul_self _ (eigenSubsetProj_mul_self D hD _)) v
      rw [residualMaker, quadForm_sub, quadForm_one] at hcomp
      linarith
    · rw [trace_eigenSubsetProj_mul, hpos]
      have hnn : 0 ≤ (∑ i, |hD.eigenvalues i|) / 2 := by positivity
      rw [abs_of_nonneg hnn]
  · rintro t ⟨B, hBs, hB0, hB1, rfl⟩
    have hb : ∀ i : Fin d, 0 ≤ quadForm B (angularEigenVector D hD i) ∧
        quadForm B (angularEigenVector D hD i) ≤ 1 := by
      intro i
      refine ⟨hB0 _, ?_⟩
      have h := hB1 (angularEigenVector D hD i)
      rwa [angularEigenVector_dot_self D hD i] at h
    rw [trace_mul_eq_sum_eigen B D hD]
    have hupper : ∑ i, hD.eigenvalues i * quadForm B (angularEigenVector D hD i)
        ≤ ∑ i ∈ positiveEigenSet D hD, hD.eigenvalues i := by
      have hterm : ∀ i : Fin d, hD.eigenvalues i * quadForm B (angularEigenVector D hD i)
          ≤ if i ∈ positiveEigenSet D hD then hD.eigenvalues i else 0 := by
        intro i
        by_cases h : 0 < hD.eigenvalues i
        · have hmem : i ∈ positiveEigenSet D hD := by simp [positiveEigenSet, h]
          rw [if_pos hmem]
          nlinarith [(hb i).2, le_of_lt h]
        · have hmem : i ∉ positiveEigenSet D hD := by simp [positiveEigenSet, h]
          rw [if_neg hmem]
          nlinarith [(hb i).1, not_lt.mp h]
      calc ∑ i, hD.eigenvalues i * quadForm B (angularEigenVector D hD i)
          ≤ ∑ i, if i ∈ positiveEigenSet D hD then hD.eigenvalues i else 0 :=
            Finset.sum_le_sum fun i _ ↦ hterm i
        _ = ∑ i ∈ positiveEigenSet D hD, hD.eigenvalues i := by
            rw [Finset.sum_ite_mem, Finset.univ_inter]
    have hlower : -(∑ i ∈ positiveEigenSet D hD, hD.eigenvalues i)
        ≤ ∑ i, hD.eigenvalues i * quadForm B (angularEigenVector D hD i) := by
      have hterm : ∀ i : Fin d,
          (if i ∈ positiveEigenSet D hD then (0 : ℝ) else hD.eigenvalues i)
            ≤ hD.eigenvalues i * quadForm B (angularEigenVector D hD i) := by
        intro i
        by_cases h : 0 < hD.eigenvalues i
        · have hmem : i ∈ positiveEigenSet D hD := by simp [positiveEigenSet, h]
          rw [if_pos hmem]
          nlinarith [(hb i).1, le_of_lt h]
        · have hmem : i ∉ positiveEigenSet D hD := by simp [positiveEigenSet, h]
          rw [if_neg hmem]
          nlinarith [(hb i).2, not_lt.mp h]
      have hsum : ∑ i, hD.eigenvalues i = 0 := by
        have h := hD.trace_eq_sum_eigenvalues
        rw [htr] at h
        simpa using h.symm
      have hsplit : ∑ i, (if i ∈ positiveEigenSet D hD then (0 : ℝ) else hD.eigenvalues i)
          = -(∑ i ∈ positiveEigenSet D hD, hD.eigenvalues i) := by
        have hid : ∀ i : Fin d,
            (if i ∈ positiveEigenSet D hD then (0 : ℝ) else hD.eigenvalues i)
              = hD.eigenvalues i
                - (if i ∈ positiveEigenSet D hD then hD.eigenvalues i else 0) := by
          intro i
          by_cases h : i ∈ positiveEigenSet D hD <;> simp [h]
        rw [Finset.sum_congr rfl fun i _ ↦ hid i, Finset.sum_sub_distrib, hsum,
          Finset.sum_ite_mem, Finset.univ_inter, zero_sub]
      calc -(∑ i ∈ positiveEigenSet D hD, hD.eigenvalues i)
          = ∑ i, (if i ∈ positiveEigenSet D hD then (0 : ℝ) else hD.eigenvalues i) :=
            hsplit.symm
        _ ≤ ∑ i, hD.eigenvalues i * quadForm B (angularEigenVector D hD i) :=
            Finset.sum_le_sum fun i _ ↦ hterm i
    rw [← hpos, abs_le]
    exact ⟨hlower, hupper⟩

end

end Descent.Portability.AngularExtremalReports
