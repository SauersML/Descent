/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.SpectralAuditStrongDuality
import Descent.Portability.FiniteAuditAllocationLaw

assert_below Descent.Decision Descent.Program

/-!
Decision-Directed Portability, Theorem 14: the actual attained spectral
optimizers obey the coordinate allocation law. The positive trace-one dual
operator determines a single weighted contrast, so the previously proved
coordinate uniqueness theorem applies exactly. Zero budget multipliers keep
the coordinate-minimum statement; only positive multipliers permit division
and yield the clipped square-root formula.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.SpectralAuditAllocationLaw

open FiniteAuditDesign SpectralAuditDesign AuditCovarianceSpectrum SpectralAuditTrace
open SpectralAuditDualCertificate
open scoped BigOperators

variable {ι E : Type*} [Fintype ι]
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- The dual operator's one weighted contrast is exactly its covariance trace pairing. -/
theorem one_row_objective (κ p : ι → ℝ) (u : ι → E) (W : E →ₗ[ℝ] E) :
    FiniteAuditDesign.worstVariance
      (fun _ : Unit ↦ SpectralAuditDualCertificate.contribution κ u W) p =
      LinearMap.trace ℝ E (W.comp (covariance (fun i ↦ κ i / p i) u)) := by
  simp only [FiniteAuditDesign.worstVariance, FiniteAuditDesign.rowVariance,
    Finset.univ_unique, Finset.sup'_singleton, trace_pairing]
  apply Finset.sum_congr rfl
  intro i _
  unfold SpectralAuditDualCertificate.contribution
  ring

/-- The one-row dual is identically the explicit spectral dual, including zero multipliers. -/
theorem one_row_dual (κ floor c : ι → ℝ) (u : ι → E) (B lam : ℝ) (W : E →ₗ[ℝ] E) :
    FiniteAuditDesign.dualBound (fun _ : Unit ↦ SpectralAuditDualCertificate.contribution κ u W)
      floor c B (fun _ ↦ 1) lam = SpectralAuditDualCertificate.dualBound κ floor c u B lam W := by
  simp only [FiniteAuditDesign.dualBound, FiniteAuditDesign.contribution,
    Finset.univ_unique, Finset.sum_singleton, one_mul, SpectralAuditDualCertificate.dualBound]

/-- Zero gap and eigenspace support force every actual coordinate to attain its scalar minimum. -/
theorem coordinate_optimality (κ floor c p : ι → ℝ) (u : ι → E) (B lam : ℝ)
    (W : E →ₗ[ℝ] E) (hκ : ∀ i, 0 ≤ κ i) (hf : ∀ i, 0 < floor i)
    (hc : ∀ i, 0 ≤ c i) (hlam : 0 ≤ lam) (hW : W.IsPositive)
    (htrace : LinearMap.trace ℝ E W = 1) (hp : Feasible floor c B p)
    (hdual : SpectralAuditDualCertificate.dualBound κ floor c u B lam W = objective κ u p)
    (hsupport : (covariance (fun i ↦ κ i / p i) u).comp W = objective κ u p • W) (i : ι) :
    AuditAllocationCoordinate.objective (SpectralAuditDualCertificate.contribution κ u W i)
      (lam * c i) (p i) =
    AuditAllocationCoordinate.objective (SpectralAuditDualCertificate.contribution κ u W i)
      (lam * c i) (AuditAllocationCoordinate.choice
        (SpectralAuditDualCertificate.contribution κ u W i) (lam * c i) (floor i)) := by
  have hd : FiniteAuditDesign.dualBound
      (fun _ : Unit ↦ SpectralAuditDualCertificate.contribution κ u W)
      floor c B (fun _ ↦ 1) lam =
      FiniteAuditDesign.worstVariance
        (fun _ : Unit ↦ SpectralAuditDualCertificate.contribution κ u W) p := by
    rw [one_row_dual, one_row_objective, top_support_equality _ u W htrace hsupport]
    exact hdual
  have hh := FiniteAuditAllocationLaw.coordinate_optimality
    (fun _ : Unit ↦ SpectralAuditDualCertificate.contribution κ u W) floor c p B (fun _ ↦ 1) lam
    (fun _ i ↦ SpectralAuditDualCertificate.contribution_nonneg κ u W hκ hW i)
    hf hc (fun _ ↦ zero_le_one) (by simp) hlam hp hd i
  simpa only [FiniteAuditDesign.contribution, Finset.univ_unique,
    Finset.sum_singleton, one_mul] using hh

/-- A positive budget multiplier gives the exact clipped square-root spectral allocation. -/
theorem allocation_formula (κ floor c p : ι → ℝ) (u : ι → E) (B lam : ℝ)
    (W : E →ₗ[ℝ] E) (hκ : ∀ i, 0 ≤ κ i) (hf : ∀ i, 0 < floor i)
    (hc : ∀ i, 0 < c i) (hlam : 0 < lam) (hW : W.IsPositive)
    (htrace : LinearMap.trace ℝ E W = 1) (hp : Feasible floor c B p)
    (hdual : SpectralAuditDualCertificate.dualBound κ floor c u B lam W = objective κ u p)
    (hsupport : (covariance (fun i ↦ κ i / p i) u).comp W = objective κ u p • W) (i : ι) :
    p i = AuditVarianceGeometry.clip (floor i) 1
      (Real.sqrt (SpectralAuditDualCertificate.contribution κ u W i / (lam * c i))) := by
  have he := coordinate_optimality κ floor c p u B lam W hκ hf (fun i ↦ (hc i).le)
    hlam.le hW htrace hp hdual hsupport i
  rw [AuditAllocationCoordinate.choice, if_neg (mul_pos hlam (hc i)).ne'] at he
  exact FiniteAuditAllocationLaw.positive_multiplier_unique _ _ _ _
    (SpectralAuditDualCertificate.contribution_nonneg κ u W hκ hW i)
    (mul_pos hlam (hc i)) (hf i) (hp.1 i) he

/-- Strict feasibility produces spectral optimizers satisfying the complete allocation law. -/
theorem attained_allocation_law (κ floor c p₀ : ι → ℝ) (u : ι → E) (B : ℝ)
    (hκ : ∀ i, 0 ≤ κ i) (hf : ∀ i, 0 < floor i) (hc : ∀ i, 0 < c i)
    (hd : 0 < Module.finrank ℝ E)
    (hp₀ : ∀ i, p₀ i ∈ Set.Icc (floor i) 1) (hbudget : spending c p₀ < B) :
    ∃ (p : ι → ℝ) (W : E →ₗ[ℝ] E) (lam : ℝ),
      Feasible floor c B p ∧ IsMinOn (objective κ u) {q | Feasible floor c B q} p ∧
      W.IsPositive ∧ LinearMap.trace ℝ E W = 1 ∧ 0 ≤ lam ∧
      SpectralAuditDualCertificate.dualBound κ floor c u B lam W = objective κ u p ∧
      lam * (spending c p - B) = 0 ∧
      (covariance (fun i ↦ κ i / p i) u).comp W = objective κ u p • W ∧
      (∀ i, AuditAllocationCoordinate.objective (SpectralAuditDualCertificate.contribution κ u W i)
        (lam * c i) (p i) = AuditAllocationCoordinate.objective
        (SpectralAuditDualCertificate.contribution κ u W i) (lam * c i)
        (AuditAllocationCoordinate.choice (SpectralAuditDualCertificate.contribution κ u W i)
          (lam * c i) (floor i))) ∧
      (0 < lam → ∀ i, p i = AuditVarianceGeometry.clip (floor i) 1
        (Real.sqrt (SpectralAuditDualCertificate.contribution κ u W i / (lam * c i)))) := by
  obtain ⟨p, W, lam, hp, hmin, hW, htrace, hlam, hdual, hb, hsupport⟩ :=
    SpectralAuditStrongDuality.attained_strong_duality κ floor c p₀ u B hκ hf
      (fun i ↦ (hc i).le) hd hp₀ hbudget
  exact ⟨p, W, lam, hp, hmin, hW, htrace, hlam, hdual, hb, hsupport,
    coordinate_optimality κ floor c p u B lam W hκ hf (fun i ↦ (hc i).le)
      hlam hW htrace hp hdual hsupport,
    fun hpos ↦ allocation_formula κ floor c p u B lam W hκ hf hc hpos
      hW htrace hp hdual hsupport⟩

end Descent.Portability.SpectralAuditAllocationLaw
