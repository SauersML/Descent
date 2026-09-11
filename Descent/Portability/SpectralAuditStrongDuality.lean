/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.SpectralOperatorEpigraph
import Descent.Portability.PositiveOperatorFunctional
import Descent.Portability.SpectralTraceComplementarity
import Descent.Portability.SpectralAuditDualCertificate

assert_below Descent.Decision Descent.Program

/-!
Decision-Directed Portability, Theorem 14: attained spectral strong duality.
The actual compact primal problem supplies an optimizer. Operator Slater
separation constructs a positive functional, whose trace representation
produces the actual positive trace-one dual matrix. The explicit coordinate
dual value equals the primal eigenvalue, and both budget complementarity
and top-eigenspace support follow. No dual optimizer is supplied as a premise.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.SpectralAuditStrongDuality

open FiniteAuditDesign SpectralAuditDesign AuditCovarianceSpectrum
open SpectralOperatorEpigraph PositiveOperatorFunctional SpectralAuditDualCertificate
open scoped BigOperators

variable {ι E : Type*} [Fintype ι]
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- Strict budget feasibility constructs both spectral optimizers and their exact certificate. -/
theorem attained_strong_duality (κ floor c p₀ : ι → ℝ) (u : ι → E) (B : ℝ)
    (hκ : ∀ i, 0 ≤ κ i) (hf : ∀ i, 0 < floor i) (hc : ∀ i, 0 ≤ c i)
    (hd : 0 < Module.finrank ℝ E)
    (hp₀ : ∀ i, p₀ i ∈ Set.Icc (floor i) 1) (hbudget : spending c p₀ < B) :
    ∃ (p : ι → ℝ) (W : E →ₗ[ℝ] E) (lam : ℝ),
      Feasible floor c B p ∧ IsMinOn (objective κ u) {q | Feasible floor c B q} p ∧
      W.IsPositive ∧ LinearMap.trace ℝ E W = 1 ∧ 0 ≤ lam ∧
      SpectralAuditDualCertificate.dualBound κ floor c u B lam W = objective κ u p ∧
      lam * (spending c p - B) = 0 ∧
      (covariance (fun i ↦ κ i / p i) u).comp W = objective κ u p • W := by
  obtain ⟨p, hp, hmin⟩ := SpectralAuditDesign.optimum_exists κ floor c u B hκ hf
    ⟨p₀, hp₀, hbudget.le⟩
  obtain ⟨lam, R, hlam, hR, hL, hb, hcomp⟩ :=
    epigraph_multipliers κ floor c p p₀ u B hκ hf hd hp hmin hp₀ hbudget
  have hidentity := functional_normalized κ floor c p u B lam R hp.1 hL hb hcomp
  let W := representative R
  have hW : W.IsPositive := representative_positive R hR
  have htrace : LinearMap.trace ℝ E W = 1 := (representative_trace R).trans hidentity
  have hpair : LinearMap.trace ℝ E (W.comp (covariance (fun i ↦ κ i / p i) u)) =
      objective κ u p := by
    have ht := trace_representation R
      (covariance (fun i ↦ κ i / p i) u).toContinuousLinearMap
    change LinearMap.trace ℝ E (W.comp (covariance (fun i ↦ κ i / p i) u)) = _ at ht
    rw [ht]
    rw [functional_residual, hidentity, mul_one] at hcomp
    exact sub_eq_zero.mp hcomp
  have hdual : SpectralAuditDualCertificate.dualBound κ floor c u B lam W =
      objective κ u p := by
    apply le_antisymm (SpectralAuditDualCertificate.weak_duality
      κ floor c p u B lam W hκ hf hc hlam hW htrace hp)
    let q (i : ι) := AuditAllocationCoordinate.choice (contribution κ u W i)
      (lam * c i) (floor i)
    have hq : ∀ i, q i ∈ Set.Icc (floor i) 1 := fun i ↦
      AuditAllocationCoordinate.choice_mem _ _ _ ((hp₀ i).1.trans (hp₀ i).2)
    have hl := hL (q, 0) hq
    simp only [functional_residual, Prod.fst, Prod.snd, zero_add, zero_mul, sub_zero] at hl
    have ht := trace_representation R
      (covariance (fun i ↦ κ i / q i) u).toContinuousLinearMap
    change LinearMap.trace ℝ E (W.comp (covariance (fun i ↦ κ i / q i) u)) = _ at ht
    have he : SpectralAuditDualCertificate.dualBound κ floor c u B lam W =
        R ((covariance (fun i ↦ κ i / q i) u).toContinuousLinearMap) +
          lam * (spending c q - B) := by
      change -lam * B + ∑ i, AuditAllocationCoordinate.objective
        (contribution κ u W i) (lam * c i) (q i) = _
      rw [SpectralAuditDualCertificate.lagrangian_identity, ht]
    rw [he]
    linarith
  exact ⟨p, W, lam, hp, hmin, hW, htrace, hlam, hdual, hb,
    SpectralTraceComplementarity.support_of_trace_equality _ u
      (fun i ↦ div_nonneg (hκ i) ((hf i).trans_le (hp.1 i).1).le) W hW htrace hpair⟩

end Descent.Portability.SpectralAuditStrongDuality
