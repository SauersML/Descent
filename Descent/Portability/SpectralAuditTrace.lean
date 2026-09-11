/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.SpectralAuditDesign
import Mathlib.Analysis.InnerProductSpace.Trace

assert_below Descent.Decision Descent.Program

/-!
Decision-Directed Portability, Theorems 14 and 15. Trace identities for the
actual audit covariance produce the spectral dual lower bound and the
dimension-dependent cost obstruction. Positive trace-one operators average
genuine repair directions; top-eigenspace support makes the bound exact.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.SpectralAuditTrace

open AuditCovarianceSpectrum AuditRayleighGeometry SpectralAuditDesign
open scoped BigOperators

variable {ι E : Type*} [Fintype ι]
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- The covariance trace is the sum of squared row norms weighted by marginal variances. -/
theorem covariance_trace (w : ι → ℝ) (u : ι → E) :
    LinearMap.trace ℝ E (covariance w u) = ∑ i, w i * ‖u i‖ ^ 2 := by
  simp only [covariance, map_sum, map_smul, LinearMap.trace_smulRight,
    ContinuousLinearMap.coe_coe, innerSL_apply, smul_eq_mul, real_inner_self_eq_norm_sq]

/-- Applying a dual operator to the covariance yields exactly the stated row contributions. -/
theorem trace_pairing (w : ι → ℝ) (u : ι → E) (W : E →ₗ[ℝ] E) :
    LinearMap.trace ℝ E (W.comp (covariance w u)) = ∑ i, w i * inner ℝ (u i) (W (u i)) := by
  have he : W.comp (covariance w u) =
      ∑ i, w i • (innerSL ℝ (u i)).toLinearMap.smulRight (W (u i)) := by
    ext a
    simp only [covariance, LinearMap.comp_apply, LinearMap.sum_apply,
      LinearMap.smul_apply, LinearMap.smulRight_apply, map_sum, map_smul]
  rw [he]
  simp only [map_sum, map_smul, LinearMap.trace_smulRight, smul_eq_mul,
    ContinuousLinearMap.coe_coe, innerSL_apply]

/-- Every positive trace-one operator gives a valid lower bound on the top covariance eigenvalue. -/
theorem positive_trace_bound (w : ι → ℝ) (u : ι → E) (hw : ∀ i, 0 ≤ w i)
    (W : E →ₗ[ℝ] E) (hW : W.IsPositive) (htrace : LinearMap.trace ℝ E W = 1) :
    LinearMap.trace ℝ E (W.comp (covariance w u)) ≤ largest w u := by
  let b := hW.isSymmetric.eigenvectorBasis rfl
  let e := hW.isSymmetric.eigenvalues rfl
  have hsum : ∑ j, e j = 1 := by
    have he := hW.isSymmetric.trace_eq_sum_eigenvalues rfl
    rw [htrace] at he
    simpa [e] using he.symm
  rw [LinearMap.trace_eq_sum_inner _ b]
  calc
    _ = ∑ j, e j * inner ℝ (b j) (covariance w u (b j)) := by
      apply Finset.sum_congr rfl
      intro j _
      change inner ℝ (b j) (W (covariance w u (b j))) = _
      rw [← hW.isSymmetric]
      have he := hW.isSymmetric.apply_eigenvectorBasis rfl j
      change W (b j) = e j • b j at he
      rw [he, inner_smul_left]
      simp
    _ ≤ ∑ j, e j * largest w u := by
      apply Finset.sum_le_sum
      intro j _
      apply mul_le_mul_of_nonneg_left
      · rw [quadratic]
        exact unit_quadratic_le w u hw (b j) (b.orthonormal.1 j).le
      · exact hW.nonneg_eigenvalues rfl j
    _ = largest w u := by rw [← Finset.sum_mul, hsum, one_mul]

/-- Support in the top eigenspace gives exact equality in the spectral trace bound. -/
theorem top_support_equality (w : ι → ℝ) (u : ι → E) (W : E →ₗ[ℝ] E)
    (htrace : LinearMap.trace ℝ E W = 1)
    (hsupport : (covariance w u).comp W = largest w u • W) :
    LinearMap.trace ℝ E (W.comp (covariance w u)) = largest w u := by
  rw [LinearMap.trace_comp_comm', hsupport, map_smul, htrace, smul_eq_mul, mul_one]

/-- The covariance trace cannot exceed the dimension times the worst-direction variance. -/
theorem trace_le_dimension (w : ι → ℝ) (u : ι → E) (hw : ∀ i, 0 ≤ w i) :
    (∑ i, w i * ‖u i‖ ^ 2) ≤ (Module.finrank ℝ E : ℝ) * largest w u := by
  rw [← covariance_trace, LinearMap.trace_eq_sum_inner _ (stdOrthonormalBasis ℝ E)]
  calc
    _ ≤ ∑ _j : Fin (Module.finrank ℝ E), largest w u := by
      apply Finset.sum_le_sum
      intro j _
      rw [quadratic]
      exact unit_quadratic_le w u hw _ ((stdOrthonormalBasis ℝ E).orthonormal.1 j).le
    _ = _ := by simp

end Descent.Portability.SpectralAuditTrace
