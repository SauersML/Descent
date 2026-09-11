/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.SpectralAuditDualCertificate
import Descent.Portability.SpectralRangeAuditDesign
import Descent.Portability.AuditDesignNumericalCertificate

assert_below Descent.Decision Descent.Program

/-!
Decision-Directed Portability, Theorem 16: numerical errors for the actual
spectral design. A feasible allocation and a positive trace-one dual operator
certify an additive variance gap. At a fixed range cap this gives the stated
vector confidence-radius error, including its factor two. Capped problems
use their actual increased probability floors in the dual objective.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.SpectralAuditNumericalCertificate

open FiniteAuditDesign SpectralAuditDesign BernsteinTailBound AuditRangeCaps

variable {ι E : Type*} [Fintype ι]
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- The gap between an actual spectral primal objective and a valid explicit dual bound. -/
noncomputable def dualGap (κ floor c p : ι → ℝ) (u : ι → E) (B lam : ℝ)
    (W : E →ₗ[ℝ] E) : ℝ :=
  objective κ u p - SpectralAuditDualCertificate.dualBound κ floor c u B lam W

/-- The gap is nonnegative and bounds variance error against every feasible competitor. -/
theorem certified_variance_error (κ floor c p : ι → ℝ) (u : ι → E)
    (B lam : ℝ) (W : E →ₗ[ℝ] E)
    (hκ : ∀ i, 0 ≤ κ i) (hf : ∀ i, 0 < floor i) (hc : ∀ i, 0 ≤ c i)
    (hlam : 0 ≤ lam) (hW : W.IsPositive) (htrace : LinearMap.trace ℝ E W = 1)
    (hp : Feasible floor c B p) :
    0 ≤ dualGap κ floor c p u B lam W ∧ ∀ q, Feasible floor c B q →
      objective κ u p ≤ objective κ u q + dualGap κ floor c p u B lam W := by
  constructor
  · exact sub_nonneg.mpr (SpectralAuditDualCertificate.weak_duality
      κ floor c p u B lam W hκ hf hc hlam hW htrace hp)
  · intro q hq
    have hh := SpectralAuditDualCertificate.weak_duality
      κ floor c q u B lam W hκ hf hc hlam hW htrace hq
    unfold dualGap
    linarith

/-- The spectral primal-dual gap controls the full vector radius at a fixed range cap. -/
theorem certified_radius_error (κ floor c p : ι → ℝ) (u : ι → E)
    (B lam M x : ℝ) (W : E →ₗ[ℝ] E)
    (hκ : ∀ i, 0 ≤ κ i) (hf : ∀ i, 0 < floor i) (hc : ∀ i, 0 ≤ c i)
    (hlam : 0 ≤ lam) (hW : W.IsPositive) (htrace : LinearMap.trace ℝ E W = 1)
    (hx : 0 ≤ x) (hp : Feasible floor c B p) (q : ι → ℝ) (hq : Feasible floor c B q) :
    2 * radius M (objective κ u p) x ≤ 2 * radius M (objective κ u q) x +
      2 * Real.sqrt (2 * dualGap κ floor c p u B lam W * x) := by
  have hg := certified_variance_error κ floor c p u B lam W hκ hf hc hlam hW htrace hp
  have hr := AuditDesignNumericalCertificate.radius_error M (objective κ u q)
    (objective κ u p) x (dualGap κ floor c p u B lam W)
    (objective_nonneg κ u q hκ (fun i ↦ (hf i).trans_le (hq.1 i).1)) hx hg.1 (hg.2 q hq)
  linarith

/-- A capped numerical solve certifies its actual range, rather than only a nominal cap. -/
theorem capped_radius_error [Nonempty ι] (κ floor c h p : ι → ℝ) (u : ι → E)
    (B lam M x : ℝ) (W : E →ₗ[ℝ] E)
    (hκ : ∀ i, 0 ≤ κ i) (hf : ∀ i, 0 < floor i) (hc : ∀ i, 0 ≤ c i)
    (hlam : 0 ≤ lam) (hW : W.IsPositive) (htrace : LinearMap.trace ℝ E W = 1)
    (hM : 0 < M) (hx : 0 ≤ x) (hp : Feasible (cappedFloor floor h M) c B p)
    (q : ι → ℝ) (hq : Feasible (cappedFloor floor h M) c B q) :
    SpectralRangeAuditDesign.fullRadius κ h p u x ≤
      2 * radius M (objective κ u q) x +
        2 * Real.sqrt (2 * dualGap κ (cappedFloor floor h M) c p u B lam W * x) := by
  have hrange := ((capped_feasible_iff floor c h p B M hf hM).mp hp).2
  have hr := radius_mono (maxRange h p) M (objective κ u p) (objective κ u p)
    x hrange (le_refl _) hx
  have hgap := certified_radius_error κ (cappedFloor floor h M) c p u B lam M x W hκ
    (fun i ↦ (hf i).trans_le (le_max_left _ _)) hc hlam hW htrace hx hp q hq
  change 2 * radius (maxRange h p) (objective κ u p) x ≤ _
  linarith

end Descent.Portability.SpectralAuditNumericalCertificate
