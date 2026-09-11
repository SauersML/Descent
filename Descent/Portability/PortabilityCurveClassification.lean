/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.PortabilityMasterTheorem
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Pow

assert_below Descent.Decision Descent.Program

/-!
# Exact local trend conditions for a family of deployment populations

Covariance and variances here are computed from each population's score and
phenotype. Their differentiability is a regularity premise, not an assumed
direction of change. Zero predictive covariance is treated separately.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.PortabilityCurveClassification

variable {Ω J L : Type*} [Fintype J] [Fintype L]

theorem r2_derivative (P : ℝ → DeploymentPopulation Ω J L) (w : J → ℝ)
    (d c' u' v' : ℝ)
    (hc : HasDerivAt (fun x ↦ (P x).predictiveCovariance w) c' d)
    (hu : HasDerivAt (fun x ↦ (P x).scoreVariance w) u' d)
    (hv : HasDerivAt (fun x ↦ (P x).outcomeVariance) v' d)
    (hcn : (P d).predictiveCovariance w ≠ 0)
    (hun : (P d).scoreVariance w ≠ 0) (hvn : (P d).outcomeVariance ≠ 0) :
    HasDerivAt (fun x ↦ (P x).r2 w)
      ((P d).r2 w * (2 * c' / (P d).predictiveCovariance w -
        u' / (P d).scoreVariance w - v' / (P d).outcomeVariance)) d := by
  have h := (hc.pow 2).div (hu.mul hv) (mul_ne_zero hun hvn)
  simp only [Pi.pow_apply, Pi.mul_apply] at h
  unfold DeploymentPopulation.r2
  convert h using 1
  field_simp
  ring

/-- Necessary and sufficient condition for a negative derivative of accuracy.
A zero derivative at one point is not a claim of constancy on a neighborhood. -/
theorem r2_declines_iff (P : ℝ → DeploymentPopulation Ω J L) (w : J → ℝ)
    (d c' u' v' : ℝ)
    (hc : HasDerivAt (fun x ↦ (P x).predictiveCovariance w) c' d)
    (hu : HasDerivAt (fun x ↦ (P x).scoreVariance w) u' d)
    (hv : HasDerivAt (fun x ↦ (P x).outcomeVariance) v' d)
    (hcn : (P d).predictiveCovariance w ≠ 0)
    (hup : 0 < (P d).scoreVariance w) (hvp : 0 < (P d).outcomeVariance) :
    deriv (fun x ↦ (P x).r2 w) d < 0 ↔
      2 * c' / (P d).predictiveCovariance w <
        u' / (P d).scoreVariance w + v' / (P d).outcomeVariance := by
  rw [(r2_derivative P w d c' u' v' hc hu hv hcn hup.ne' hvp.ne').deriv]
  have hpos : 0 < (P d).r2 w := by
    unfold DeploymentPopulation.r2
    exact div_pos (sq_pos_of_ne_zero hcn) (mul_pos hup hvp)
  rw [← mul_zero ((P d).r2 w), mul_lt_mul_iff_right₀ hpos]
  constructor <;> intro h <;> linarith

/-- At a covariance zero, accuracy has zero derivative whenever its moment
inputs are differentiable and the variances are nonzero. -/
theorem r2_derivative_at_zero_covariance
    (P : ℝ → DeploymentPopulation Ω J L) (w : J → ℝ) (d c' u' v' : ℝ)
    (hc : HasDerivAt (fun x ↦ (P x).predictiveCovariance w) c' d)
    (hu : HasDerivAt (fun x ↦ (P x).scoreVariance w) u' d)
    (hv : HasDerivAt (fun x ↦ (P x).outcomeVariance) v' d)
    (hzero : (P d).predictiveCovariance w = 0)
    (hun : (P d).scoreVariance w ≠ 0) (hvn : (P d).outcomeVariance ≠ 0) :
    HasDerivAt (fun x ↦ (P x).r2 w) 0 d := by
  have h := (hc.pow 2).div (hu.mul hv) (mul_ne_zero hun hvn)
  simpa [DeploymentPopulation.r2, hzero] using h

end Descent.Portability.PortabilityCurveClassification
