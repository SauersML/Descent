/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.DecisionInformationRank
import Mathlib.LinearAlgebra.Matrix.Rank

assert_below Descent.Decision Descent.Program

/-!
Decision-Directed Portability, Theorem 2 in the manuscript's actual matrix
coordinates. Affine contrast constants and nonzero frame normalization do
not change identification. The determining-summary criterion is exactly
row-space inclusion, and a target-range basis attains the minimum number
of scalar summaries. Admissible mean domains may be closed provided their
interior is nonempty.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.MatrixDecisionInformation

open Matrix DecisionInformationRank
open scoped BigOperators

variable {ι J K : Type*} [Fintype ι] [DecidableEq ι]
variable [Fintype J] [DecidableEq J] [Fintype K] [DecidableEq K]

/-- The span of the rows of a linear summary or decision matrix. -/
def rowSpace (A : Matrix K ι ℝ) : Submodule ℝ (ι → ℝ) := Submodule.span ℝ (Set.range A)

/-- Row-space inclusion is equivalent to an actual matrix reconstruction of the decisions. -/
theorem rows_iff_factorization (A : Matrix K ι ℝ) (B : Matrix J ι ℝ) :
    rowSpace B ≤ rowSpace A ↔ ∃ C : Matrix J K ℝ, C * A = B := by
  classical
  constructor
  · intro hrow
    have hcoeff (j : J) : ∃ c : K → ℝ, ∑ k, c k • A k = B j :=
      (Submodule.mem_span_range_iff_exists_fun ℝ).mp
        (hrow (Submodule.subset_span ⟨j, rfl⟩))
    choose C hC using hcoeff
    refine ⟨C, ?_⟩
    ext j i
    have he := congrFun (hC j) i
    simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Matrix.mul_apply] using he
  · rintro ⟨C, hC⟩
    apply Submodule.span_le.mpr
    rintro _ ⟨j, rfl⟩
    apply (Submodule.mem_span_range_iff_exists_fun ℝ).mpr
    refine ⟨C j, ?_⟩
    ext i
    have he := congrFun (congrFun hC j) i
    simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Matrix.mul_apply] using he

/-- Linear reconstruction and ordinary matrix multiplication express the same factorization. -/
theorem linear_iff_matrix_factorization (A : Matrix K ι ℝ) (B : Matrix J ι ℝ) :
    (∃ C : (K → ℝ) →ₗ[ℝ] (J → ℝ), C.comp A.mulVecLin = B.mulVecLin) ↔
      ∃ C : Matrix J K ℝ, C * A = B := by
  constructor
  · rintro ⟨C, hC⟩
    refine ⟨C.toMatrix', ?_⟩
    apply Matrix.toLin'.injective
    rw [Matrix.toLin'_mul, Matrix.toLin'_toMatrix']
    exact hC
  · rintro ⟨C, hC⟩
    refine ⟨C.mulVecLin, ?_⟩
    rw [← Matrix.mulVecLin_mul, hC]

/-- Linear summaries determine all decision contrasts exactly when their row space contains them. -/
theorem identifies_iff_rows (S : Set (ι → ℝ)) (hne : (interior S).Nonempty)
    (A : Matrix K ι ℝ) (B : Matrix J ι ℝ) :
    IdentifiesOn S A.mulVecLin B.mulVecLin ↔ rowSpace B ≤ rowSpace A := by
  rw [identifies_iff_factorization_of_interior S hne A.mulVecLin B.mulVecLin,
    linear_iff_matrix_factorization A B, rows_iff_factorization A B]

/-- The actual affine decision report, with its explicit target-frame normalization. -/
noncomputable def report (a : J → ℝ) (B : Matrix J ι ℝ) (N : ℝ) (μ : ι → ℝ) : J → ℝ :=
  a + N⁻¹ • (B *ᵥ μ)

/-- Known affine terms and nonzero normalization preserve exactly the same decision information. -/
theorem report_eq_iff (a : J → ℝ) (B : Matrix J ι ℝ) (N : ℝ) (hN : N ≠ 0)
    (μ ν : ι → ℝ) : report a B N μ = report a B N ν ↔ B *ᵥ μ = B *ᵥ ν := by
  unfold report
  rw [add_right_inj, smul_right_inj (inv_ne_zero hN)]

/-- Exact identification of normalized affine reports is equivalent to row-space inclusion. -/
theorem report_identification_iff (S : Set (ι → ℝ)) (hne : (interior S).Nonempty)
    (A : Matrix K ι ℝ) (a : J → ℝ) (B : Matrix J ι ℝ) (N : ℝ) (hN : N ≠ 0) :
    (∀ μ ∈ S, ∀ ν ∈ S, A *ᵥ μ = A *ᵥ ν → report a B N μ = report a B N ν) ↔
      rowSpace B ≤ rowSpace A := by
  simp only [report_eq_iff a B N hN]
  exact identifies_iff_rows S hne A B

/-- The matrix rank is the exact minimum scalar summary count, on the actual admissible mean set. -/
theorem exact_matrix_summary_count (S : Set (ι → ℝ)) (hne : (interior S).Nonempty)
    (B : Matrix J ι ℝ) :
    IsLeast {q : ℕ | ∃ A : (ι → ℝ) →ₗ[ℝ] (Fin q → ℝ), IdentifiesOn S A B.mulVecLin}
      B.rank :=
  exact_summary_count S hne B.mulVecLin

end Descent.Portability.MatrixDecisionInformation
