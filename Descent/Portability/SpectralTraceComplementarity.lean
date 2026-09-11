/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.SpectralAuditTrace

assert_below Descent.Decision Descent.Program

/-!
The equality case needed for spectral audit dual attainment. An exact
Rayleigh maximizer lies in the actual top eigenspace. Equality of a positive
trace-one operator's trace pairing with the largest covariance eigenvalue
then forces the operator's range into that eigenspace.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.SpectralTraceComplementarity

open AuditCovarianceSpectrum SpectralAuditTrace
open scoped BigOperators

variable {ι E : Type*} [Fintype ι]
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- Equality in the Rayleigh bound forces an actual top-eigenvector equation. -/
theorem rayleigh_equality (w : ι → ℝ) (u : ι → E) (a : E)
    (he : inner ℝ a (covariance w u a) = largest w u * ‖a‖ ^ 2) :
    covariance w u a = largest w u • a := by
  have hsum : (∑ j, (largest w u - eigenvalues w u j) * ((basis w u).repr a j) ^ 2) = 0 := by
    simp only [sub_mul, Finset.sum_sub_distrib, ← Finset.mul_sum,
      sum_coordinates_sq, ← spectral_quadratic, he, sub_self]
  have hn (j : Fin (Module.finrank ℝ E)) (_hj : j ∈ Finset.univ) :
      0 ≤ (largest w u - eigenvalues w u j) * ((basis w u).repr a j) ^ 2 :=
    mul_nonneg (sub_nonneg.mpr (eigenvalue_le_largest w u j)) (sq_nonneg _)
  apply (basis w u).repr.injective
  ext j
  have hz := (Finset.sum_eq_zero_iff_of_nonneg hn).mp hsum j (Finset.mem_univ j)
  have hc := (symmetric w u).eigenvectorBasis_apply_self_apply rfl a j
  change (basis w u).repr (covariance w u a) j =
    eigenvalues w u j * (basis w u).repr a j at hc
  rw [hc, map_smul]
  change eigenvalues w u j * (basis w u).repr a j = largest w u * (basis w u).repr a j
  rcases mul_eq_zero.mp hz with ht | hz
  · rw [sub_eq_zero.mp ht]
  · rw [sq_eq_zero_iff.mp hz, mul_zero, mul_zero]

/-- Equality in the positive trace bound forces the exact top-eigenspace support condition. -/
theorem support_of_trace_equality (w : ι → ℝ) (u : ι → E) (hw : ∀ i, 0 ≤ w i)
    (W : E →ₗ[ℝ] E) (hW : W.IsPositive) (htrace : LinearMap.trace ℝ E W = 1)
    (he : LinearMap.trace ℝ E (W.comp (covariance w u)) = largest w u) :
    (covariance w u).comp W = largest w u • W := by
  let b := hW.isSymmetric.eigenvectorBasis rfl
  let e := hW.isSymmetric.eigenvalues rfl
  have hsum : ∑ j, e j = 1 := by
    have hh := hW.isSymmetric.trace_eq_sum_eigenvalues rfl
    rw [htrace] at hh
    exact hh.symm
  have hpair : (∑ j, e j * inner ℝ (b j) (covariance w u (b j))) = largest w u := by
    rw [← he, LinearMap.trace_eq_sum_inner _ b]
    apply Finset.sum_congr rfl
    intro j _
    change _ = inner ℝ (b j) (W (covariance w u (b j)))
    rw [← hW.isSymmetric]
    have hh := hW.isSymmetric.apply_eigenvectorBasis rfl j
    change W (b j) = e j • b j at hh
    rw [hh, inner_smul_left]
    simp
  have hgap : (∑ j, e j * (largest w u - inner ℝ (b j) (covariance w u (b j)))) = 0 := by
    simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hsum, one_mul, hpair,
      sub_self]
  have hn (j : Fin (Module.finrank ℝ E)) (_hj : j ∈ Finset.univ) :
      0 ≤ e j * (largest w u - inner ℝ (b j) (covariance w u (b j))) := by
    apply mul_nonneg (hW.nonneg_eigenvalues rfl j)
    apply sub_nonneg.mpr
    rw [quadratic]
    exact AuditRayleighGeometry.unit_quadratic_le w u hw (b j) (b.orthonormal.1 j).le
  apply b.toBasis.ext
  intro j
  have hz := (Finset.sum_eq_zero_iff_of_nonneg hn).mp hgap j (Finset.mem_univ j)
  have hWj := hW.isSymmetric.apply_eigenvectorBasis rfl j
  change W (b j) = e j • b j at hWj
  change covariance w u (W (b j)) = largest w u • W (b j)
  rw [hWj, map_smul]
  rcases mul_eq_zero.mp hz with hz | ht
  · simp [hz]
  · have hr : inner ℝ (b j) (covariance w u (b j)) = largest w u * ‖b j‖ ^ 2 := by
      rw [b.orthonormal.1 j]
      simpa using (sub_eq_zero.mp ht).symm
    rw [rayleigh_equality w u (b j) hr, smul_comm]

end Descent.Portability.SpectralTraceComplementarity
