/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.SpectralAuditTrace

assert_below Descent.Decision Descent.Program

/-!
Decision-Directed Portability, Theorem 14. Positive trace-one operators give
the exact stated spectral dual lower bounds. Coordinate minimization,
top-eigenspace support and budget complementarity certify a global optimizer.
These are checked sufficient certificates; existence of a dual optimizer is
a separate convex-duality obligation, not an assumption hidden in this theorem.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.SpectralAuditDualCertificate

open AuditCovarianceSpectrum SpectralAuditDesign SpectralAuditTrace FiniteAuditDesign
open scoped BigOperators

variable {ι E : Type*} [Fintype ι]
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- The row importance selected by the positive dual operator. -/
noncomputable def contribution (κ : ι → ℝ) (u : ι → E) (W : E →ₗ[ℝ] E) (i : ι) : ℝ :=
  κ i * inner ℝ (u i) (W (u i))

/-- The stated dual objective, with its box minimizations evaluated by the exact coordinate rule. -/
noncomputable def dualBound (κ floor c : ι → ℝ) (u : ι → E) (B lam : ℝ)
    (W : E →ₗ[ℝ] E) : ℝ :=
  -lam * B + ∑ i, AuditAllocationCoordinate.objective (contribution κ u W i) (lam * c i)
    (AuditAllocationCoordinate.choice (contribution κ u W i) (lam * c i) (floor i))

/-- Positive semidefinite dual weights give nonnegative coordinate contributions. -/
theorem contribution_nonneg (κ : ι → ℝ) (u : ι → E) (W : E →ₗ[ℝ] E)
    (hκ : ∀ i, 0 ≤ κ i) (hW : W.IsPositive) (i : ι) : 0 ≤ contribution κ u W i :=
  mul_nonneg (hκ i) (hW.inner_nonneg_right (u i))

/-- The separated Lagrangian is the actual trace pairing plus the expected-budget term. -/
theorem lagrangian_identity (κ c p : ι → ℝ) (u : ι → E) (B lam : ℝ) (W : E →ₗ[ℝ] E) :
    -lam * B + ∑ i, AuditAllocationCoordinate.objective (contribution κ u W i) (lam * c i) (p i) =
      LinearMap.trace ℝ E (W.comp (covariance (fun i ↦ κ i / p i) u)) +
        lam * (spending c p - B) := by
  rw [trace_pairing]
  simp only [AuditAllocationCoordinate.objective, contribution, spending,
    Finset.sum_add_distrib, Finset.mul_sum]
  have he : (∑ i, κ i * inner ℝ (u i) (W (u i)) / p i) =
      ∑ i, κ i / p i * inner ℝ (u i) (W (u i)) := by
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [he]
  have hc : (∑ i, lam * c i * p i) = ∑ i, lam * (c i * p i) := by
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hc, ← Finset.mul_sum]
  ring

/-- Every valid spectral dual choice bounds every feasible primal allocation from below. -/
theorem weak_duality (κ floor c p : ι → ℝ) (u : ι → E) (B lam : ℝ) (W : E →ₗ[ℝ] E)
    (hκ : ∀ i, 0 ≤ κ i) (hf : ∀ i, 0 < floor i) (hc : ∀ i, 0 ≤ c i)
    (hlam : 0 ≤ lam) (hW : W.IsPositive) (htrace : LinearMap.trace ℝ E W = 1)
    (hp : Feasible floor c B p) : dualBound κ floor c u B lam W ≤ objective κ u p := by
  unfold dualBound
  calc
    _ ≤ -lam * B + ∑ i,
        AuditAllocationCoordinate.objective (contribution κ u W i) (lam * c i) (p i) := by
      apply add_le_add_left
      exact Finset.sum_le_sum (fun i _ ↦ AuditAllocationCoordinate.choice_minimum
        (contribution κ u W i) (lam * c i) (floor i) (p i)
        (contribution_nonneg κ u W hκ hW i) (mul_nonneg hlam (hc i)) (hf i) (hp.1 i))
    _ = _ := lagrangian_identity κ c p u B lam W
    _ ≤ objective κ u p := by
      have ht := positive_trace_bound (fun i ↦ κ i / p i) u
        (fun i ↦ div_nonneg (hκ i) ((hf i).trans_le (hp.1 i).1).le) W hW htrace
      have hb : lam * (spending c p - B) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos hlam (sub_nonpos.mpr hp.2)
      exact (add_le_of_nonpos_right hb).trans ht

/-- Coordinate minimization and actual operator complementarity close the primal-dual gap. -/
theorem certificate_equality (κ floor c p : ι → ℝ) (u : ι → E)
    (B lam : ℝ) (W : E →ₗ[ℝ] E) (htrace : LinearMap.trace ℝ E W = 1)
    (hchoice : ∀ i, p i = AuditAllocationCoordinate.choice
      (contribution κ u W i) (lam * c i) (floor i))
    (hsupport : (covariance (fun i ↦ κ i / p i) u).comp W = objective κ u p • W)
    (hbudget : lam * (spending c p - B) = 0) :
    dualBound κ floor c u B lam W = objective κ u p := by
  unfold dualBound
  simp_rw [← hchoice]
  rw [lagrangian_identity, top_support_equality _ u W htrace hsupport, hbudget, add_zero]
  rfl

/-- The stated explicit certificate proves optimality against every feasible competing audit. -/
theorem certified_optimum (κ floor c p : ι → ℝ) (u : ι → E)
    (B lam : ℝ) (W : E →ₗ[ℝ] E)
    (hκ : ∀ i, 0 ≤ κ i) (hf : ∀ i, 0 < floor i) (hc : ∀ i, 0 ≤ c i)
    (hlam : 0 ≤ lam) (hW : W.IsPositive) (htrace : LinearMap.trace ℝ E W = 1)
    (hp : Feasible floor c B p)
    (hchoice : ∀ i, p i = AuditAllocationCoordinate.choice
      (contribution κ u W i) (lam * c i) (floor i))
    (hsupport : (covariance (fun i ↦ κ i / p i) u).comp W = objective κ u p • W)
    (hbudget : lam * (spending c p - B) = 0) :
    Feasible floor c B p ∧ IsMinOn (objective κ u) {q | Feasible floor c B q} p := by
  refine ⟨hp, ?_⟩
  intro q hq
  rw [← certificate_equality κ floor c p u B lam W htrace hchoice hsupport hbudget]
  exact weak_duality κ floor c q u B lam W hκ hf hc hlam hW htrace hq

/-- A positive budget multiplier gives the clipped square-root allocation formula. -/
theorem positive_multiplier_choice (κ floor c : ι → ℝ) (u : ι → E)
    (lam : ℝ) (W : E →ₗ[ℝ] E) (hlam : 0 < lam) (hc : ∀ i, 0 < c i) (i : ι) :
    AuditAllocationCoordinate.choice (contribution κ u W i) (lam * c i) (floor i) =
      AuditVarianceGeometry.clip (floor i) 1
        (Real.sqrt (contribution κ u W i / (lam * c i))) := by
  rw [AuditAllocationCoordinate.choice, if_neg (mul_pos hlam (hc i)).ne']

end Descent.Portability.SpectralAuditDualCertificate
