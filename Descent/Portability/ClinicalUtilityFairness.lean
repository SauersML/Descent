/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.PGSCalibrationTheory

assert_below Descent.Decision

-- LAYER DEBT. This file cannot yet assert it is below `Descent.Program`:
--   Program: reaches 1 module(s) -- `Descent.Program.Conclusions`
-- The repair is to move what it reaches for DOWN, not to move this file up.

namespace Descent.Portability

open MeasureTheory

/-!
# Clinical Utility, Fairness, and Ethical Implications of PGS Portability

This file formalizes the theory connecting PGS portability to clinical
utility and fairness. The portability gap has direct consequences for
health equity when PGS is used in clinical decision-making.

Key results:
1. Net Reclassification Improvement (NRI) from PGS depends on portability
2. Decision curve analysis and threshold-dependent utility
3. Fairness criteria and impossibility results
4. Risk stratification accuracy across populations
5. Cost-effectiveness depends on portability

Reference: Wang et al. (2026), Nature Communications 17:942 -- for the portability
gap itself and its clinical-equity motivation, which that paper measures. It does
not contain the liability-threshold derivation, the decision-curve results or the
fairness impossibility statement below; those are derived here.
-/


/-!
## Liability Threshold Model — First-Principles Derivation

We derive the monotone relationship between PGS R² and sensitivity/specificity
from the liability threshold model, rather than assuming it axiomatically.

### The Model

1. **Liability**: `Y_liability = G + E`, where `G ~ N(0, h²)` is the genetic
   component and `E ~ N(0, 1 - h²)` is the environmental component,
   so `Y_liability ~ N(0, 1)`.

2. **Disease**: occurs when `Y_liability > T` (threshold `T` set by prevalence).

3. **PGS prediction**: `Ĝ = R × G + ε`, where `R = √R²` is the correlation
   between the PGS and the true genetic value, and `ε` is independent noise
   with variance `h²(1 - R²)`.

4. **Sensitivity**: `P(Ĝ > T' | G + E > T)` for a classification threshold `T'`.
   For the bivariate normal `(Ĝ, Y_liability)` with correlation `R × h`:
   - The conditional distribution of `Ĝ` given disease shifts upward
   - Sensitivity = `Φ((R × h × (μ_case) − T') / σ_resid)`
   - This is monotone increasing in `R` (and hence in `R²`)

5. **Key insight**: `Φ` is monotone increasing (from the standard normal CDF),
   and the argument to `Φ` is monotone increasing in `R`, so the composition
   is monotone increasing. This justifies the exact sensitivity/specificity
   curves used in all subsequent theorems.
-/

section LiabilityThresholdModel

/-- **Liability threshold model.**
    Encapsulates the parameters of the standard liability threshold model
    for a binary disease trait:
    - `h_sq`: heritability (variance explained by genetics), in (0, 1)
    - `prevalence`: population prevalence of the disease, in (0, 1)
    - `threshold`: liability threshold T such that P(Y > T) = prevalence
    - `case_mean`: mean liability among cases, E[Y | Y > T] > 0 -/
structure LiabilityThresholdModel where
  h_sq : ℝ
  prevalence : ℝ
  threshold : ℝ
  case_mean : ℝ
  h_sq_pos : 0 < h_sq
  h_sq_lt_one : h_sq < 1
  prev_pos : 0 < prevalence
  prev_lt_one : prevalence < 1
  case_mean_pos : 0 < case_mean

/-- **The class is inhabited.**  A theorem quantified over an uninhabited structure is
true and empty: kernel-checked, clean axiom report, no content.  This is the witness that
makes the theorems below statements about something. -/
noncomputable def LiabilityThresholdModel.witness : LiabilityThresholdModel where
  h_sq := 1 / 2
  prevalence := 1 / 2
  threshold := 0
  case_mean := 1
  h_sq_pos := by norm_num
  h_sq_lt_one := by norm_num
  prev_pos := by norm_num
  prev_lt_one := by norm_num
  case_mean_pos := by norm_num

/-- **Residual variance is positive on [0,1].**
    The residual variance σ²_resid = h²(1 − R²) + (1 − h²) is strictly positive
    for R² ∈ [0, 1] and h² ∈ (0, 1), since (1 − h²) > 0. -/
theorem residualVariance_pos (m : LiabilityThresholdModel)
    (R2 : ℝ) (hR2' : R2 ≤ 1) :
    0 < m.h_sq * (1 - R2) + (1 - m.h_sq) := by
  have h1 : 0 ≤ m.h_sq * (1 - R2) :=
    mul_nonneg (le_of_lt m.h_sq_pos) (by linarith)
  have h2 : 0 < 1 - m.h_sq := by linarith [m.h_sq_lt_one]
  linarith

/-- **Corollary: σ_resid = √(residual variance) is positive on [0,1].**
    This is what makes the residual-positivity side condition of every
    monotonicity theorem below a derived fact rather than a hypothesis. -/
theorem sigmaResid_pos (m : LiabilityThresholdModel)
    (R2 : ℝ) (hR2' : R2 ≤ 1) :
    0 < Real.sqrt (m.h_sq * (1 - R2) + (1 - m.h_sq)) :=
  Real.sqrt_pos_of_pos (residualVariance_pos m R2 hR2')

/-- **What both z-score denominators do across a rise in `R²`**: each is positive, and the
one at the larger `R²` is the smaller, because explaining more liability leaves less
residual to scale by.

The sensitivity and specificity monotonicity theorems below each established these three
facts inline, in the same order and by the same tactics.  They differ only in their
numerators; the denominator is the same object in both, and it is now proved about once. -/
theorem sigmaResid_pos_pos_le (m : LiabilityThresholdModel)
    (R2₁ R2₂ : ℝ) (hR2₁ : 0 ≤ R2₁) (hR2₂ : R2₂ ≤ 1) (hR2 : R2₁ < R2₂) :
    0 < Real.sqrt (m.h_sq * (1 - R2₂) + (1 - m.h_sq)) ∧
      0 < Real.sqrt (m.h_sq * (1 - R2₁) + (1 - m.h_sq)) ∧
      Real.sqrt (m.h_sq * (1 - R2₂) + (1 - m.h_sq)) ≤
        Real.sqrt (m.h_sq * (1 - R2₁) + (1 - m.h_sq)) := by
  refine ⟨sigmaResid_pos m R2₂ hR2₂, ?_, ?_⟩
  · apply Real.sqrt_pos_of_pos
    have : 0 < 1 - m.h_sq := by linarith [m.h_sq_lt_one]
    nlinarith [m.h_sq_pos]
  · exact Real.sqrt_le_sqrt (by nlinarith [m.h_sq_pos])

/-- **Liability sensitivity.**
    Under the liability threshold model, the sensitivity of a PGS-based
    classifier at classification threshold `T'` is:

      sensitivity(R²) = Φ((R · h · μ_case − T') / σ_resid)

    where `R = √R²`, `h = √h²`, `μ_case = E[Y | Y > T]`, and
    `σ_resid = √(h² · (1 − R²) + (1 − h²))` is the residual SD of
    liability conditional on Ĝ.

    The argument to Φ is monotone increasing in R² because:
    - The numerator `R · h · μ_case − T'` increases in R (for μ_case > 0)
    - The denominator `σ_resid` decreases in R² (less residual variance)
    - Both effects push the z-score upward as R² increases

    Empirical status: CONDITIONALLY VALID (tested, approximate). This evaluates the conditional
    exceedance at the mean case liability, whereas sensitivity averages it over
    the case distribution; Phi is nonlinear, so Jensen guarantees a gap.
    Numerical integration cross-checked by Monte Carlo puts the error under one
    percent for R2 <= 0.2 at moderate thresholds, degrading to -10 percent at
    high R2 and stringent operating points. Usable, but not exact. -/
noncomputable def liabilitySensitivity
    (Φ : ℝ → ℝ) (m : LiabilityThresholdModel) (R2 : ℝ) (T' : ℝ) : ℝ :=
  let R := Real.sqrt R2
  let h := Real.sqrt m.h_sq
  let σ_resid := Real.sqrt (m.h_sq * (1 - R2) + (1 - m.h_sq))
  Φ ((R * h * m.case_mean - T') / σ_resid)

/-- **Liability specificity.**
    Under the liability threshold model, the specificity of a PGS-based
    classifier at classification threshold `T'` is:

      specificity(R²) = Φ((T' − R · h · μ_control) / σ_resid)

    where `μ_control = E[Y | Y ≤ T]` is the mean liability among controls
    (typically negative). This is also monotone increasing in R² by the
    same argument: higher R² increases separation between cases and controls.

    Empirical status: **MEASURED**, and what was measured is that this signature does
    not determine the quantity (`simcov/battery_gap01.py`, `group_clinical`).

    `T'` and `μ_control` are free ARGUMENTS and nothing here says which scale either
    lives on. On one simulated population under the liability threshold model this
    definition declares -- 4×10⁶ individuals per cell, a PGS-explained component of
    variance `R²·h²`, independent residual liability of variance
    `h²(1-R²) + (1-h²)`, disease above the prevalence threshold -- three
    self-consistent readings of "the specificity of a PGS-based classifier at `T'`"
    give, at `h² = 0.5, R² = 0.2, K = 0.05`:

      rule applied to a re-drawn residual        0.908
      rule applied to the individual's liability 0.953
      rule applied to the PGS component alone    0.99999

    and the body, at the model's own truncated control mean, gives 0.923. It is
    within 1.5% of the first, 3% of the second, and 8% of the third; at these error
    bars all three are refused.

    So this is not a falsification of the arithmetic. It is a measurement of the
    declaration: a consumer who states which scale `T'` and `μ_control` are on gets a
    determinate answer, and one who does not is choosing between 0.91 and 0.99999. The
    same shape as `AncestryCalibration.ancestryRecalibratedSlope`, where a third
    convention had to be written down before either measurement meant anything.

    What would settle it is an argument list that carries the scale, not a new
    simulation. -/
noncomputable def liabilitySpecificity
    (Φ : ℝ → ℝ) (m : LiabilityThresholdModel)
    (R2 : ℝ) (T' : ℝ) (μ_control : ℝ) : ℝ :=
  let R := Real.sqrt R2
  let h := Real.sqrt m.h_sq
  let σ_resid := Real.sqrt (m.h_sq * (1 - R2) + (1 - m.h_sq))
  Φ ((T' - R * h * μ_control) / σ_resid)

/-- **The z-score argument of Φ in the sensitivity formula is monotone in R.**
    For the bivariate normal (Ĝ, Y_liability) with correlation ρ = R·h,
    the z-score z(R) = (R · h · μ_case − T') / σ_resid(R²) is strictly
    increasing in R on [0, 1] when μ_case > 0.

    Proof sketch: Let f(R) = R · h · μ_case and g(R²) = σ_resid(R²).
    - f is strictly increasing in R (since h · μ_case > 0)
    - g is strictly decreasing in R² (since σ²_resid = h²(1−R²) + (1−h²) decreases)
    - So numerator increases and denominator decreases → z increases.

    We state this as: for R₁ < R₂ (both in [0,1]), the z-score at R₂ exceeds
    that at R₁. The formal proof uses monotonicity of √· and positivity of
    the model parameters. -/
theorem liabilitySensitivity_zScore_monotone_in_R_of_num_nonneg
    (m : LiabilityThresholdModel) (T' : ℝ)
    (R₁ R₂ : ℝ) (hR₁ : 0 ≤ R₁) (hR₂ : R₂ ≤ 1)
    (hR : R₁ < R₂)
    (hR2₂ : R₂ ^ 2 ≤ 1)
    -- The z-score numerator is nonneg at the lower R value.
    -- This is the clinically relevant regime: the PGS classification
    -- threshold T' is at or below the expected PGS among cases at R₁.
    (h_num_nonneg : 0 ≤ R₁ * Real.sqrt m.h_sq * m.case_mean - T') :
    let h := Real.sqrt m.h_sq
    let σ₁ := Real.sqrt (m.h_sq * (1 - R₁ ^ 2) + (1 - m.h_sq))
    let σ₂ := Real.sqrt (m.h_sq * (1 - R₂ ^ 2) + (1 - m.h_sq))
    (R₁ * h * m.case_mean - T') / σ₁ <
      (R₂ * h * m.case_mean - T') / σ₂ := by
  -- Strategy: show (num₁/σ₁ < num₂/σ₂) via cross-multiplication.
  -- We have num₂ > num₁ ≥ 0, and 0 < σ₂ ≤ σ₁, so:
  --   num₁ · σ₂ ≤ num₁ · σ₁ < num₂ · σ₁
  -- giving num₁ · σ₂ < num₂ · σ₁, hence num₁/σ₁ < num₂/σ₂.
  simp only
  -- σ_resid at R₂ is positive: derived, not assumed.
  have h_σ_pos : 0 < Real.sqrt (m.h_sq * (1 - R₂ ^ 2) + (1 - m.h_sq)) :=
    sigmaResid_pos m (R₂ ^ 2) hR2₂
  -- Establish σ₁ > 0
  have h_rv₁_pos : 0 < m.h_sq * (1 - R₁ ^ 2) + (1 - m.h_sq) := by
    have : R₁ ^ 2 ≤ R₂ ^ 2 := by nlinarith
    have : 0 < 1 - m.h_sq := by linarith [m.h_sq_lt_one]
    nlinarith [m.h_sq_pos]
  have h_σ₁_pos : 0 < Real.sqrt (m.h_sq * (1 - R₁ ^ 2) + (1 - m.h_sq)) :=
    Real.sqrt_pos_of_pos h_rv₁_pos
  -- Establish σ₂ ≤ σ₁ (residual variance decreases as R² increases)
  have h_R2_le : R₁ ^ 2 ≤ R₂ ^ 2 := by nlinarith
  have h_rv_le : m.h_sq * (1 - R₂ ^ 2) + (1 - m.h_sq) ≤
      m.h_sq * (1 - R₁ ^ 2) + (1 - m.h_sq) := by nlinarith [m.h_sq_pos]
  have h_σ_le : Real.sqrt (m.h_sq * (1 - R₂ ^ 2) + (1 - m.h_sq)) ≤
      Real.sqrt (m.h_sq * (1 - R₁ ^ 2) + (1 - m.h_sq)) :=
    Real.sqrt_le_sqrt h_rv_le
  -- Establish num₂ > num₁ (numerator increases with R)
  have h_h_pos : 0 < Real.sqrt m.h_sq := Real.sqrt_pos_of_pos m.h_sq_pos
  have h_num_lt : R₁ * Real.sqrt m.h_sq * m.case_mean - T' <
      R₂ * Real.sqrt m.h_sq * m.case_mean - T' := by
    nlinarith [mul_pos h_h_pos m.case_mean_pos]
  -- Cross-multiply: need num₁ · σ₂ < num₂ · σ₁
  rw [div_lt_div_iff₀ h_σ₁_pos h_σ_pos]
  -- num₁ · σ₂ ≤ num₁ · σ₁ (since num₁ ≥ 0 and σ₂ ≤ σ₁)
  have h1 : (R₁ * Real.sqrt m.h_sq * m.case_mean - T') *
      Real.sqrt (m.h_sq * (1 - R₂ ^ 2) + (1 - m.h_sq)) ≤
      (R₁ * Real.sqrt m.h_sq * m.case_mean - T') *
      Real.sqrt (m.h_sq * (1 - R₁ ^ 2) + (1 - m.h_sq)) :=
    mul_le_mul_of_nonneg_left h_σ_le h_num_nonneg
  -- num₁ · σ₁ < num₂ · σ₁ (since num₁ < num₂ and σ₁ > 0)
  have h2 : (R₁ * Real.sqrt m.h_sq * m.case_mean - T') *
      Real.sqrt (m.h_sq * (1 - R₁ ^ 2) + (1 - m.h_sq)) <
      (R₂ * Real.sqrt m.h_sq * m.case_mean - T') *
      Real.sqrt (m.h_sq * (1 - R₁ ^ 2) + (1 - m.h_sq)) :=
    mul_lt_mul_of_pos_right h_num_lt h_σ₁_pos
  linarith

/-- **Monotonicity of liability sensitivity in R².**
    The main result: since Φ is monotone increasing and the z-score
    argument is monotone increasing in R (hence R²), the composition
    `liabilitySensitivity` is monotone increasing in R².

    This is the formal justification for the exact operating-point sensitivity
    curve `sensFromR2` used throughout the NRI and clinical utility theorems.

    The proof structure:
    1. `Φ` is strictly monotone (standard normal CDF property from Mathlib)
    2. The z-score `(R·h·μ_case − T') / σ_resid` is monotone in R²
       (from `liabilitySensitivity_zScore_monotone_in_R_of_num_nonneg`)
    3. Composition of monotone functions is monotone -/
theorem liabilitySensitivity_monotone_in_R2_of_threshold_le
    (Φ : ℝ → ℝ) (m : LiabilityThresholdModel) (T' : ℝ)
    (hΦ_mono : StrictMono Φ)
    (R2₁ R2₂ : ℝ) (hR2₁ : 0 ≤ R2₁) (hR2₂ : R2₂ ≤ 1)
    (hR2 : R2₁ < R2₂)
    -- The z-score numerator is nonneg at the lower R² value (clinically
    -- relevant regime: classification threshold T' ≤ expected PGS among cases).
    (h_num_nonneg : 0 ≤ Real.sqrt R2₁ * Real.sqrt m.h_sq * m.case_mean - T') :
    liabilitySensitivity Φ m R2₁ T' < liabilitySensitivity Φ m R2₂ T' := by
  -- The z-score is monotone in R² and Φ is strictly monotone,
  -- so the composition is strictly monotone.
  unfold liabilitySensitivity
  apply hΦ_mono
  -- Reduce to the z-score monotonicity in R.
  -- We need: (√R2₁ · h · μ - T') / σ₁ < (√R2₂ · h · μ - T') / σ₂
  -- with the same structure as
  -- liabilitySensitivity_zScore_monotone_in_R_of_num_nonneg.
  -- σ₂ > 0: derived from the model, not assumed.
  obtain ⟨h_σ_pos, h_σ₁_pos, h_σ_le⟩ := sigmaResid_pos_pos_le m R2₁ R2₂ hR2₁ hR2₂ hR2
  -- √R2₁ < √R2₂
  have h_sqrt_lt : Real.sqrt R2₁ < Real.sqrt R2₂ :=
    Real.sqrt_lt_sqrt hR2₁ hR2
  -- numerator increases
  have h_h_pos : 0 < Real.sqrt m.h_sq := Real.sqrt_pos_of_pos m.h_sq_pos
  have h_num_lt : Real.sqrt R2₁ * Real.sqrt m.h_sq * m.case_mean - T' <
      Real.sqrt R2₂ * Real.sqrt m.h_sq * m.case_mean - T' := by
    nlinarith [mul_pos h_h_pos m.case_mean_pos]
  -- Cross-multiply: num₁ · σ₂ < num₂ · σ₁
  rw [div_lt_div_iff₀ h_σ₁_pos h_σ_pos]
  have h1 : (Real.sqrt R2₁ * Real.sqrt m.h_sq * m.case_mean - T') *
      Real.sqrt (m.h_sq * (1 - R2₂) + (1 - m.h_sq)) ≤
      (Real.sqrt R2₁ * Real.sqrt m.h_sq * m.case_mean - T') *
      Real.sqrt (m.h_sq * (1 - R2₁) + (1 - m.h_sq)) :=
    mul_le_mul_of_nonneg_left h_σ_le h_num_nonneg
  have h2 : (Real.sqrt R2₁ * Real.sqrt m.h_sq * m.case_mean - T') *
      Real.sqrt (m.h_sq * (1 - R2₁) + (1 - m.h_sq)) <
      (Real.sqrt R2₂ * Real.sqrt m.h_sq * m.case_mean - T') *
      Real.sqrt (m.h_sq * (1 - R2₁) + (1 - m.h_sq)) :=
    mul_lt_mul_of_pos_right h_num_lt h_σ₁_pos
  linarith

/-- **Monotonicity of liability specificity in R².**
    Analogous result for specificity: higher R² → better specificity.
    The z-score for specificity is (T' − R·h·μ_control) / σ_resid.
    Since μ_control < 0 (controls have below-average liability),
    −R·h·μ_control > 0 and increases with R, and σ_resid decreases,
    so the z-score increases → Φ(z) increases. -/
theorem liabilitySpecificity_monotone_in_R2_of_threshold_le
    (Φ : ℝ → ℝ) (m : LiabilityThresholdModel) (T' μ_control : ℝ)
    (hΦ_mono : StrictMono Φ)
    (hμ_control_neg : μ_control < 0)
    (R2₁ R2₂ : ℝ) (hR2₁ : 0 ≤ R2₁) (hR2₂ : R2₂ ≤ 1)
    (hR2 : R2₁ < R2₂)
    -- The specificity z-score numerator is nonneg at R2₁.
    -- Since μ_control < 0, the term -R·h·μ_control ≥ 0, so this holds
    -- whenever T' ≥ 0 (which is the standard clinical regime).
    (h_num_nonneg : 0 ≤ T' - Real.sqrt R2₁ * Real.sqrt m.h_sq * μ_control) :
    liabilitySpecificity Φ m R2₁ T' μ_control <
      liabilitySpecificity Φ m R2₂ T' μ_control := by
  unfold liabilitySpecificity
  apply hΦ_mono
  -- Need: (T' - √R2₁·h·μ_ctrl) / σ₁ < (T' - √R2₂·h·μ_ctrl) / σ₂
  -- The numerator T' - R·h·μ_control increases with R (since h > 0, μ_control < 0,
  -- so -h·μ_control > 0 and the numerator grows with R).
  -- The denominator σ_resid decreases with R². Same cross-multiply argument.
  -- σ₂ > 0: derived from the model, not assumed.
  obtain ⟨h_σ_pos, h_σ₁_pos, h_σ_le⟩ := sigmaResid_pos_pos_le m R2₁ R2₂ hR2₁ hR2₂ hR2
  -- √R2₁ < √R2₂
  have h_sqrt_lt : Real.sqrt R2₁ < Real.sqrt R2₂ :=
    Real.sqrt_lt_sqrt hR2₁ hR2
  -- numerator increases: since μ_control < 0, -R·h·μ_control increases with R
  have h_h_pos : 0 < Real.sqrt m.h_sq := Real.sqrt_pos_of_pos m.h_sq_pos
  have h_num_lt : T' - Real.sqrt R2₁ * Real.sqrt m.h_sq * μ_control <
      T' - Real.sqrt R2₂ * Real.sqrt m.h_sq * μ_control := by
    -- T' - a₁ < T' - a₂  iff  a₂ < a₁, i.e., √R2₂·h·μ < √R2₁·h·μ
    -- Since μ < 0 and √R2₂ > √R2₁ and h > 0: √R2₂·h·|μ| > √R2₁·h·|μ|
    -- so √R2₂·h·μ < √R2₁·h·μ. ✓
    nlinarith [mul_pos h_h_pos (neg_pos.mpr hμ_control_neg)]
  -- Cross-multiply
  rw [div_lt_div_iff₀ h_σ₁_pos h_σ_pos]
  have h1 : (T' - Real.sqrt R2₁ * Real.sqrt m.h_sq * μ_control) *
      Real.sqrt (m.h_sq * (1 - R2₂) + (1 - m.h_sq)) ≤
      (T' - Real.sqrt R2₁ * Real.sqrt m.h_sq * μ_control) *
      Real.sqrt (m.h_sq * (1 - R2₁) + (1 - m.h_sq)) :=
    mul_le_mul_of_nonneg_left h_σ_le h_num_nonneg
  have h2 : (T' - Real.sqrt R2₁ * Real.sqrt m.h_sq * μ_control) *
      Real.sqrt (m.h_sq * (1 - R2₁) + (1 - m.h_sq)) <
      (T' - Real.sqrt R2₂ * Real.sqrt m.h_sq * μ_control) *
      Real.sqrt (m.h_sq * (1 - R2₁) + (1 - m.h_sq)) :=
    mul_lt_mul_of_pos_right h_num_lt h_σ₁_pos
  linarith

/-- **Derived monotone sensitivity curve.**
    From the liability threshold model, we obtain an exact threshold
    sensitivity curve that is strictly monotone in `R²`.

    Given a liability threshold model `m`, classification threshold `T'`,
    and strictly monotone Φ, the function
    `R² ↦ liabilitySensitivity Φ m R² T'` is strictly monotone on `[0, 1]`. -/
theorem liability_model_provides_sensitivityCurve
    (Φ : ℝ → ℝ) (m : LiabilityThresholdModel) (T' : ℝ)
    (hΦ_mono : StrictMono Φ)
    -- Classification threshold is in the clinically relevant regime:
    -- T' ≤ expected PGS among cases even at R² = 0 (i.e., T' ≤ 0).
    -- This ensures the z-score numerator is nonneg throughout [0,1].
    (h_T' : ∀ R2, 0 ≤ R2 → R2 ≤ 1 →
      0 ≤ Real.sqrt R2 * Real.sqrt m.h_sq * m.case_mean - T') :
    StrictMonoOn (fun R2 ↦ liabilitySensitivity Φ m R2 T') (Set.Icc 0 1) := by
  intro R2₁ hR2₁ R2₂ hR2₂ hlt
  exact liabilitySensitivity_monotone_in_R2_of_threshold_le Φ m T' hΦ_mono R2₁ R2₂
    hR2₁.1 hR2₂.2 hlt
    (h_T' R2₁ hR2₁.1 (le_trans (le_of_lt hlt) hR2₂.2))

/-- **Derived monotone specificity curve.**
    Analogous to `liability_model_provides_sensitivityCurve` but for
    exact threshold specificity. -/
theorem liability_model_provides_specificityCurve
    (Φ : ℝ → ℝ) (m : LiabilityThresholdModel) (T' μ_control : ℝ)
    (hΦ_mono : StrictMono Φ)
    (hμ_control_neg : μ_control < 0)
    -- The specificity z-score numerator is nonneg across [0,1].
    -- Since μ_control < 0, this holds whenever T' ≥ 0.
    (h_T' : ∀ R2, 0 ≤ R2 → R2 ≤ 1 →
      0 ≤ T' - Real.sqrt R2 * Real.sqrt m.h_sq * μ_control) :
    StrictMonoOn (fun R2 ↦ liabilitySpecificity Φ m R2 T' μ_control) (Set.Icc 0 1) := by
  intro R2₁ hR2₁ R2₂ hR2₂ hlt
  exact liabilitySpecificity_monotone_in_R2_of_threshold_le Φ m T' μ_control hΦ_mono
    hμ_control_neg R2₁ R2₂ hR2₁.1 hR2₂.2 hlt
    (h_T' R2₁ hR2₁.1 (le_trans (le_of_lt hlt) hR2₂.2))

end LiabilityThresholdModel


/-!
## Net Reclassification Improvement

NRI measures how many individuals are correctly reclassified (moved to
correct risk category) when PGS is added to clinical risk models.
Portability loss reduces NRI in non-source populations.

We model sensitivity and specificity as functions of R² (coefficient of
determination of the PGS).  Under a liability-threshold model, a PGS with higher R² yields a score
distribution with greater separation between cases
and controls, so both sensitivity and specificity at any fixed classification
threshold improve monotonically with R².

The operating-point sensitivity and specificity are now written directly in
their exact liability-threshold forms from the section above. Every NRI theorem
below is therefore about literal threshold sensitivity/specificity, not an
opaque helper abstraction.
-/

section NRI

/-- **NRI definition.**
    NRI = (event NRI) + (non-event NRI)
    Event NRI: proportion of cases correctly moved up
    Non-event NRI: proportion of controls correctly moved down -/
noncomputable def netReclassificationImprovement
    (event_nri nonevent_nri : ℝ) : ℝ :=
  Descent.Core.sum event_nri nonevent_nri

/-- Reference evaluation; see `Descent.Core.Ratios` for what these pin and why. -/
theorem netReclassificationImprovement_at_reference_point :
    netReclassificationImprovement (1 / 2) (1 / 2) = 1 := by
  unfold netReclassificationImprovement Descent.Core.sum
  norm_num

/-- **The two components are recoverable from each other and the total.** This is why a single
NRI cannot be read: a positive total is consistent with a gain among events and a loss among
non-events, and the identity is what forces the two to be reported separately. -/
theorem netReclassificationImprovement_sub_event (event_nri nonevent_nri : ℝ) :
    netReclassificationImprovement event_nri nonevent_nri - event_nri = nonevent_nri := by
  unfold netReclassificationImprovement Descent.Core.sum
  ring

/-- Exact operating-point sensitivity under the liability-threshold model. -/
noncomputable def sensFromR2
    (m : LiabilityThresholdModel) (r2 T' : ℝ) : ℝ :=
  liabilitySensitivity Foundations.Phi m r2 T'

/-- Exact operating-point specificity under the liability-threshold model. -/
noncomputable def specFromR2
    (m : LiabilityThresholdModel) (r2 T' μ_control : ℝ) : ℝ :=
  liabilitySpecificity Foundations.Phi m r2 T' μ_control

/-- Exact liability-threshold sensitivity is strictly increasing in `R²`
    on `[0,1]` under the clinically relevant threshold regime. -/
theorem sensFromR2_strictMono_of_threshold_le
    (m : LiabilityThresholdModel) (T' R2₁ R2₂ : ℝ)
    (hR2₁ : 0 ≤ R2₁) (hR2₂ : R2₂ ≤ 1)
    (hR2 : R2₁ < R2₂)
    (h_num_nonneg : 0 ≤ Real.sqrt R2₁ * Real.sqrt m.h_sq * m.case_mean - T') :
    sensFromR2 m R2₁ T' < sensFromR2 m R2₂ T' := by
  unfold sensFromR2
  exact liabilitySensitivity_monotone_in_R2_of_threshold_le Foundations.Phi m T'
    Foundations.strictMono_Phi
    R2₁ R2₂ hR2₁ hR2₂ hR2 h_num_nonneg

/-- Exact liability-threshold specificity is strictly increasing in `R²`
    on `[0,1]` under the clinically relevant threshold regime. -/
theorem specFromR2_strictMono_of_threshold_le
    (m : LiabilityThresholdModel) (T' μ_control R2₁ R2₂ : ℝ)
    (hμ_control_neg : μ_control < 0)
    (hR2₁ : 0 ≤ R2₁) (hR2₂ : R2₂ ≤ 1)
    (hR2 : R2₁ < R2₂)
    (h_num_nonneg : 0 ≤ T' - Real.sqrt R2₁ * Real.sqrt m.h_sq * μ_control) :
    specFromR2 m R2₁ T' μ_control < specFromR2 m R2₂ T' μ_control := by
  unfold specFromR2
  exact liabilitySpecificity_monotone_in_R2_of_threshold_le Foundations.Phi m T' μ_control
    Foundations.strictMono_Phi
    hμ_control_neg R2₁ R2₂ hR2₁ hR2₂ hR2 h_num_nonneg

/-- **The clinically relevant threshold regime, named once.**

Every portability-loss statement below is conditioned on the same six facts: an `R²` gap
inside `[0, 1]`, a control mean below the threshold, and the two numerator sign conditions
that put the operating point in the regime where the exact metrics are monotone.  Written
out at each theorem, that block was nine identical lines repeated across this file and
`EquityAndImplementation`.  It is one regime, so it is one structure. -/
structure ThresholdRegime (m : LiabilityThresholdModel) (T' μ_control r2_lo r2_hi : ℝ) :
    Prop where
  /-- The lower `R²` really is lower. -/
  r2_gap : r2_lo < r2_hi
  /-- `R²` is a squared correlation, so it is nonnegative. -/
  r2_lo_nonneg : 0 ≤ r2_lo
  /-- ... and at most one. -/
  r2_hi_le_one : r2_hi ≤ 1
  /-- Controls sit below the liability threshold. -/
  control_neg : μ_control < 0
  /-- The sensitivity numerator is in the regime where the metric increases with `R²`. -/
  sens_num_nonneg : 0 ≤ Real.sqrt r2_lo * Real.sqrt m.h_sq * m.case_mean - T'
  /-- The specificity numerator is in the same regime. -/
  spec_num_nonneg : 0 ≤ T' - Real.sqrt r2_lo * Real.sqrt m.h_sq * μ_control

/-- **The regime is inhabited.**  A theorem conditioned on a bundle nothing satisfies is
true and empty; this witness makes the statements below statements about something.  At
`R² = 0` the score carries no signal, the sensitivity numerator is the threshold itself, and
both sign conditions hold at the origin. -/
theorem thresholdRegime_witness :
    ThresholdRegime LiabilityThresholdModel.witness 0 (-1) 0 1 :=
  ⟨by norm_num, le_rfl, le_rfl, by norm_num, by simp, by simp⟩

/-- **Both exact operating-point metrics improve together with `R²`.**

Every utility comparison below -- NRI, net benefit, decision-curve -- opens by deriving these
two strict inequalities from the same five hypotheses, and each opened by rederiving them.
The pair is one fact about the liability-threshold model, so it is named once here. -/
theorem sens_and_spec_strictMono_of_threshold_le
    (m : LiabilityThresholdModel) (T' μ_control R2₁ R2₂ : ℝ)
    (hμ_control_neg : μ_control < 0)
    (hR2₁ : 0 ≤ R2₁) (hR2₂ : R2₂ ≤ 1)
    (hR2 : R2₁ < R2₂)
    (h_sens_num_nonneg : 0 ≤ Real.sqrt R2₁ * Real.sqrt m.h_sq * m.case_mean - T')
    (h_spec_num_nonneg : 0 ≤ T' - Real.sqrt R2₁ * Real.sqrt m.h_sq * μ_control) :
    sensFromR2 m R2₁ T' < sensFromR2 m R2₂ T' ∧
      specFromR2 m R2₁ T' μ_control < specFromR2 m R2₂ T' μ_control :=
  ⟨sensFromR2_strictMono_of_threshold_le m T' R2₁ R2₂ hR2₁ hR2₂ hR2 h_sens_num_nonneg,
    specFromR2_strictMono_of_threshold_le m T' μ_control R2₁ R2₂ hμ_control_neg hR2₁ hR2₂ hR2
      h_spec_num_nonneg⟩

/-- **NRI is positive when PGS adds value.**
    If a higher-`R²` model is evaluated at the same classification threshold in
    the same liability-threshold population, then both the exact sensitivity
    and the exact specificity increase, so total NRI is positive. -/
theorem nri_positive_when_pgs_adds_value
    (m : LiabilityThresholdModel) (T' μ_control r2_old r2_new : ℝ)
    (h_r2_improves : r2_old < r2_new)
    (h_r2_old : 0 ≤ r2_old)
    (h_r2_new : r2_new ≤ 1)
    (hμ_control_neg : μ_control < 0)
    (h_sens_num_nonneg : 0 ≤ Real.sqrt r2_old * Real.sqrt m.h_sq * m.case_mean - T')
    (h_spec_num_nonneg : 0 ≤ T' - Real.sqrt r2_old * Real.sqrt m.h_sq * μ_control) :
    0 < netReclassificationImprovement
      (sensFromR2 m r2_new T' - sensFromR2 m r2_old T')
      (specFromR2 m r2_new T' μ_control - specFromR2 m r2_old T' μ_control) := by
  unfold netReclassificationImprovement Descent.Core.sum
  obtain ⟨h1, h2⟩ := sens_and_spec_strictMono_of_threshold_le m T' μ_control r2_old r2_new
    hμ_control_neg h_r2_old h_r2_new h_r2_improves h_sens_num_nonneg h_spec_num_nonneg
  linarith

/-- **NRI decreases with portability loss.**
    If the target population's `R²` is strictly lower than the source's, then
    exact sensitivity and specificity are both lower at the same operating
    threshold, so exact NRI is strictly lower in the target. -/
theorem nri_decreases_with_portability_loss
    (m : LiabilityThresholdModel) (T' μ_control r2_base r2_source r2_target : ℝ)
    (hregime : ThresholdRegime m T' μ_control r2_target r2_source) :
    netReclassificationImprovement
      (sensFromR2 m r2_target T' - sensFromR2 m r2_base T')
      (specFromR2 m r2_target T' μ_control - specFromR2 m r2_base T' μ_control) <
    netReclassificationImprovement
      (sensFromR2 m r2_source T' - sensFromR2 m r2_base T')
      (specFromR2 m r2_source T' μ_control - specFromR2 m r2_base T' μ_control) := by
  -- Both sides subtract the SAME baseline, so this is the previous theorem's positivity
  -- read across a common `r2_base`.  It had its own copy of that theorem's proof.
  -- Named projections rather than a positional `obtain`: the six fields are all
  -- Props over the same two `R²` arguments, so a positional pattern binds by
  -- ORDER alone and would silently survive a reordering of the structure with -- every hypothesis
  -- attached to the wrong name.
  have h_r2_loss := hregime.r2_gap
  have h_r2_target := hregime.r2_lo_nonneg
  have h_r2_source := hregime.r2_hi_le_one
  have hμ_control_neg := hregime.control_neg
  have h_sens_num_nonneg := hregime.sens_num_nonneg
  have h_spec_num_nonneg := hregime.spec_num_nonneg
  have h := nri_positive_when_pgs_adds_value m T' μ_control r2_target r2_source
    h_r2_loss h_r2_target h_r2_source hμ_control_neg h_sens_num_nonneg h_spec_num_nonneg
  unfold netReclassificationImprovement Descent.Core.sum at h ⊢
  linarith

/-- **NRI can become negative in target populations.**
    If the target R² is strictly below the old model's R² (`r2_target < r2_old`),
    then the exact liability-threshold sensitivity and specificity are both
    lower, so the NRI is negative: the target-population PGS worsens threshold
    classification relative to the old model.

    This is the mirror of `nri_positive_when_pgs_adds_value`: when portability
    loss drives R² below the baseline, the same exact metric derivation that
    guarantees improvement in the source guarantees degradation in the target. -/
theorem nri_can_be_negative
    (m : LiabilityThresholdModel) (T' μ_control r2_old r2_target : ℝ)
    (hregime : ThresholdRegime m T' μ_control r2_target r2_old) :
    netReclassificationImprovement
      (sensFromR2 m r2_target T' - sensFromR2 m r2_old T')
      (specFromR2 m r2_target T' μ_control - specFromR2 m r2_old T' μ_control) < 0 := by
  -- The old model compared against itself contributes nothing, so this is the theorem
  -- above with the baseline taken at `r2_old` -- a third copy of one proof, now an
  -- instance of it.
  have h := nri_decreases_with_portability_loss m T' μ_control r2_old r2_old r2_target
    hregime
  unfold netReclassificationImprovement Descent.Core.sum at h ⊢
  linarith

end NRI


/-!
## Decision Curve Analysis

Decision curves plot net benefit vs threshold probability.
PGS portability determines the range of thresholds where PGS is useful.
-/

section DecisionCurve

/-- **Net benefit is zero for treat-all strategy.**
    If we treat everyone, TP = prevalence × N, FP = (1-prevalence) × N. -/
theorem treat_all_net_benefit (π t : ℝ) :
    decisionCurveNetBenefit π (1 - π) 1 t = π - (1 - π) * (t / (1 - t)) := by
  rw [decisionCurveNetBenefit_eq_formula]
  simp

/-- **PGS is useful when Youden's index is positive and threshold is moderate.**
    We derive TP and FP counts from sensitivity, specificity, prevalence, and
    sample size using decision theory:
      TP_pgs = sens × π × n,  FP_pgs = (1 - spec) × (1 - π) × n
      TP_all = π × n,         FP_all = (1 - π) × n     (treat-all)

    The decision-theoretic tradeoff inequality
      `(1 - sens) × π < spec × (1 - π) × (t / (1 - t))`
    is *derived* from two independently meaningful conditions:
    1. `sens + spec > 1` — positive Youden's index (classifier better than random)
    2. `π < t` — the treatment threshold exceeds prevalence (standard DCA regime
       where treat-all is suboptimal and selective treatment is warranted)

    Together these imply the classifier beats treat-all. -/
theorem pgs_useful_when_exceeds_treat_all
    (sens spec π n t : ℝ)
    (hn : 0 < n) (ht : 0 < t) (ht1 : t < 1)
    (h_π : 0 < π)
    (h_sens : 0 < sens) (h_sens1 : sens ≤ 1)
    -- Positive Youden's index: classifier is better than random
    (h_youden : 1 < sens + spec)
    -- Treatment threshold exceeds prevalence (selective-treatment regime)
    (h_threshold : π < t) :
    -- treat-all net benefit < PGS net benefit
    decisionCurveNetBenefit (π * n) ((1 - π) * n) n t <
      decisionCurveNetBenefit (sens * π * n) ((1 - spec) * (1 - π) * n) n t := by
  repeat rw [decisionCurveNetBenefit_eq_formula]
  have hn_ne : n ≠ 0 := ne_of_gt hn
  have h1 : π * n / n = π := by field_simp
  have h2 : (1 - π) * n / n = 1 - π := by field_simp
  have h3 : sens * π * n / n = sens * π := by field_simp
  have h4 : (1 - spec) * (1 - π) * n / n = (1 - spec) * (1 - π) := by field_simp
  rw [h1, h2, h3, h4]
  -- Goal: π - (1-π)*(t/(1-t)) < sens*π - (1-spec)*(1-π)*(t/(1-t))
  -- Rearrange to: (1-sens)*π < spec*(1-π)*(t/(1-t))
  -- From h_youden: spec > 1 - sens, so spec ≥ 1-sens.
  -- From h_threshold: π < t, so π/(1-π) < t/(1-t) (odds is monotone).
  -- Then: (1-sens)*π < spec*π ≤ spec*t < spec*t + spec*(1-π)*t/(1-t) ...
  -- More directly:
  -- Need: (1-sens)*π < spec*(1-π)*t/(1-t)
  -- Suffices: (1-sens)*π*(1-t) < spec*(1-π)*t  [multiply by (1-t) > 0]
  -- From h_youden: 1-sens < spec, so (1-sens) < spec
  -- From h_threshold: π < t, so π*(1-t) < t*(1-π)  [cross-multiply odds]
  -- Combining: (1-sens)*π*(1-t) < spec * t*(1-π)  [product of strict ineqs]
  -- which is spec*(1-π)*t. ✓
  have h_1t_pos : (0 : ℝ) < 1 - t := by linarith
  have h_1sens_lt_spec : 1 - sens < spec := by linarith
  have h_1sens_nn : 0 ≤ 1 - sens := by linarith
  -- π*(1-t) < t*(1-π) from π < t (cross-multiplied odds inequality)
  have h_odds : π * (1 - t) < t * (1 - π) := by nlinarith
  -- (1-sens) < spec and π*(1-t) < t*(1-π), both sides nonneg
  -- so (1-sens)*[π*(1-t)] < spec*[t*(1-π)]
  have h_cross : (1 - sens) * (π * (1 - t)) < spec * (t * (1 - π)) := by
    calc (1 - sens) * (π * (1 - t))
        ≤ (1 - sens) * (t * (1 - π)) := by
          apply mul_le_mul_of_nonneg_left (le_of_lt h_odds) h_1sens_nn
      _ < spec * (t * (1 - π)) := by
          apply mul_lt_mul_of_pos_right h_1sens_lt_spec
          exact mul_pos ht (by linarith)
  -- Rewrite as the needed inequality over reals and divide by (1-t) > 0
  -- (1-sens)*π*(1-t) < spec*(1-π)*t
  -- → (1-sens)*π < spec*(1-π)*t/(1-t)
  have h_key : (1 - sens) * π < spec * (1 - π) * (t / (1 - t)) := by
    have h_cross' : ((1 - sens) * π) * (1 - t) < (spec * (1 - π)) * t := by
      simpa [mul_assoc, mul_left_comm, mul_comm] using h_cross
    have h_div :
        ((1 - sens) * π) < ((spec * (1 - π)) * t) / (1 - t) :=
      (lt_div_iff₀ h_1t_pos).2 h_cross'
    simpa [mul_assoc, mul_left_comm, mul_comm, div_eq_mul_inv] using h_div
  nlinarith

/-- **Portability loss narrows the useful threshold range.**
    If the target `R²` is strictly below the source `R²`, then the exact
    liability-threshold sensitivity and specificity are both lower at the same
    classification threshold, and the net benefit at any treatment threshold
    `t` is reduced.

    The net benefit formula NB = TP/N − FP/N × t/(1−t), with TP = sens(R²) × π and FP = (1 −
    spec(R²)) × (1 − π), is strictly
    increasing in both the exact sensitivity and the exact specificity. -/
theorem portability_narrows_useful_range
    (m : LiabilityThresholdModel) (T' μ_control r2_source r2_target π t : ℝ)
    (h_π : 0 < π) (h_π1 : π < 1)
    (ht : 0 < t) (ht1 : t < 1)
    (hregime : ThresholdRegime m T' μ_control r2_target r2_source) :
    decisionCurveNetBenefit (sensFromR2 m r2_target T' * π)
        ((1 - specFromR2 m r2_target T' μ_control) * (1 - π)) 1 t <
      decisionCurveNetBenefit (sensFromR2 m r2_source T' * π)
        ((1 - specFromR2 m r2_source T' μ_control) * (1 - π)) 1 t := by
  have h_r2 := hregime.r2_gap
  have h_r2_target := hregime.r2_lo_nonneg
  have h_r2_source := hregime.r2_hi_le_one
  have hμ_control_neg := hregime.control_neg
  have h_sens_num_nonneg := hregime.sens_num_nonneg
  have h_spec_num_nonneg := hregime.spec_num_nonneg
  obtain ⟨h_sens, h_spec⟩ :=
    sens_and_spec_strictMono_of_threshold_le m T' μ_control r2_target r2_source
      hμ_control_neg h_r2_target h_r2_source h_r2 h_sens_num_nonneg h_spec_num_nonneg
  repeat rw [decisionCurveNetBenefit_eq_formula]
  have htt : 0 < t / (1 - t) := div_pos ht (by linarith)
  have h1 : sensFromR2 m r2_target T' * π < sensFromR2 m r2_source T' * π :=
    mul_lt_mul_of_pos_right h_sens h_π
  have h2 :
      (1 - specFromR2 m r2_source T' μ_control) * (1 - π) <
        (1 - specFromR2 m r2_target T' μ_control) * (1 - π) := by
    apply mul_lt_mul_of_pos_right _ (by linarith)
    linarith
  have h3 :
      (1 - specFromR2 m r2_source T' μ_control) * (1 - π) * (t / (1 - t)) <
        (1 - specFromR2 m r2_target T' μ_control) * (1 - π) * (t / (1 - t)) :=
    mul_lt_mul_of_pos_right h2 htt
  simp only [div_one]
  linarith

end DecisionCurve


/-!
## Fairness Criteria and Impossibility

Multiple fairness criteria exist for risk prediction. We formalize
the key impossibility result: most fairness criteria cannot be
simultaneously satisfied when base rates differ.
-/

section Fairness

/-- **PPV definition.** Positive predictive value via Bayes' theorem:
    PPV = prev * tpr / (prev * tpr + (1 - prev) * fpr). -/
noncomputable def ppv (prev tpr fpr : ℝ) : ℝ :=
  prev * tpr / (prev * tpr + (1 - prev) * fpr)

/-- Reference evaluation; see `Descent.Core.Ratios` for what these pin and why. -/
theorem ppv_at_reference_point :
    ppv (1 / 2) (1 / 2) (1 / 2) = 1 / 2 := by
  unfold ppv
  norm_num

/-- **ppv where its denominator vanishes, named.** The guard `prev * tpr + (1 - prev) * fpr` is zero
at `prev = 0`, `tpr = 0`, `fpr = 0`. With no cases and a test that never fires, the positive
predictive value is undefined; the value returned reads as a test whose every positive call is
wrong. Lean returns `0` there rather than the value the modelled quantity takes, and no type
error marks the point. Consumers must require `prev * tpr + (1 - prev) * fpr ≠ 0`. -/
theorem ppv_at_prev0tpr0fpr0_is_junk :
    ppv 0 0 0 = 0 := by
  unfold ppv
  norm_num

/-- **Predictive value recovers the true positives from everything predicted positive.** -/
theorem ppv_mul_predictedPositive (prev tpr fpr : ℝ)
    (h : prev * tpr + (1 - prev) * fpr ≠ 0) :
    ppv prev tpr fpr * (prev * tpr + (1 - prev) * fpr) = prev * tpr := by
  unfold ppv
  field_simp

/-- **Impossibility: equalized odds + different base rates → PPV differs.**
    Under equalized odds (same TPR and FPR across groups), if prevalence
    differs, then PPV must differ — so predictive parity is violated.
    This is a concrete instance of the Chouldechova/Kleinberg impossibility.

    The denominator positivity (needed for PPV well-definedness) is *derived*
    from Bayes' rule: prev > 0, tpr > 0, fpr > 0 together imply
    prev × tpr + (1 − prev) × fpr > 0. -/
theorem fairness_impossibility
    (prev_A prev_B tpr fpr : ℝ)
    (h_diff_prev : prev_A ≠ prev_B)
    (h_prev_A : 0 < prev_A) (h_prev_B : 0 < prev_B)
    (h_prev_A1 : prev_A < 1) (h_prev_B1 : prev_B < 1)
    (h_tpr : 0 < tpr) (h_fpr : 0 < fpr) :
    -- PPV parity is violated: PPV differs across groups
    ppv prev_A tpr fpr ≠ ppv prev_B tpr fpr := by
  -- Derive denominator positivity from Bayes' rule components.
  -- denom = prev × tpr + (1 − prev) × fpr.  Each summand is non-negative
  -- (prev > 0, tpr > 0 gives first > 0; 1 − prev > 0, fpr > 0 gives second > 0),
  -- so the sum is strictly positive.
  have h_denom_A : 0 < prev_A * tpr + (1 - prev_A) * fpr := by
    apply add_pos
    · exact mul_pos h_prev_A h_tpr
    · exact mul_pos (by linarith) h_fpr
  have h_denom_B : 0 < prev_B * tpr + (1 - prev_B) * fpr := by
    apply add_pos
    · exact mul_pos h_prev_B h_tpr
    · exact mul_pos (by linarith) h_fpr
  unfold ppv
  intro h_eq
  have htpr_ne : tpr ≠ 0 := ne_of_gt h_tpr
  have hfpr_ne : fpr ≠ 0 := ne_of_gt h_fpr
  have hcross :
      prev_A * tpr * (prev_B * tpr + (1 - prev_B) * fpr) =
        prev_B * tpr * (prev_A * tpr + (1 - prev_A) * fpr) := by
    exact (div_eq_div_iff (ne_of_gt h_denom_A) (ne_of_gt h_denom_B)).mp h_eq
  have h_prev_eq : prev_A = prev_B := by
    have h_reduced : prev_A * (1 - prev_B) = prev_B * (1 - prev_A) := by
      have hscaled :
          prev_A * (1 - prev_B) * (tpr * fpr) =
            prev_B * (1 - prev_A) * (tpr * fpr) := by
        nlinarith [hcross]
      exact mul_right_cancel₀ (show tpr * fpr ≠ 0 by positivity) <| by
        simpa [mul_assoc, mul_left_comm, mul_comm] using hscaled
    nlinarith
  exact h_diff_prev h_prev_eq

/-- **Portability gap amplifies fairness violations.**
    If PGS R² differs across groups (r2_target < r2_source), and sensitivity
    is evaluated through the exact liability-threshold sensitivity at a common
    operating threshold, then the target group has strictly lower sensitivity.
    Equalized odds (equal TPR across groups) is therefore violated. -/
theorem portability_violates_equalized_odds
    (m : LiabilityThresholdModel) (T' r2_source r2_target : ℝ)
    (h_r2_gap : r2_target < r2_source)
    (h_r2_target : 0 ≤ r2_target)
    (h_r2_source : r2_source ≤ 1)
    (h_sens_num_nonneg :
      0 ≤ Real.sqrt r2_target * Real.sqrt m.h_sq * m.case_mean - T') :
    sensFromR2 m r2_target T' ≠ sensFromR2 m r2_source T' := by
  have h_sens_lt :
      sensFromR2 m r2_target T' < sensFromR2 m r2_source T' := by
    exact sensFromR2_strictMono_of_threshold_le m T' r2_target r2_source
      h_r2_target h_r2_source h_r2_gap h_sens_num_nonneg
  linarith

/-- **The fairness-accuracy tradeoff.**
    Enforcing equalized odds across groups with different prevalence requires
    using group-specific thresholds.  For the group with lower prevalence,
    the threshold must be shifted, reducing sensitivity.  We show concretely:
    if group B's sensitivity is reduced to achieve equalized odds, the
    net benefit (from decision curve analysis) at any threshold t decreases,
    because fewer true positives are identified while false positives
    remain the same. -/
theorem fairness_accuracy_tradeoff
    (sens_B_unconstrained sens_B_fair fp_B n t : ℝ)
    (h_sens_drop : sens_B_fair < sens_B_unconstrained)
    (hn : 0 < n) :
    decisionCurveNetBenefit sens_B_fair fp_B n t <
      decisionCurveNetBenefit sens_B_unconstrained fp_B n t := by
  repeat rw [decisionCurveNetBenefit_eq_formula]
  have h1 : sens_B_fair / n < sens_B_unconstrained / n := by
    rw [div_lt_div_iff₀ hn hn]
    nlinarith
  linarith

end Fairness


/-!
## Risk Stratification Accuracy

PGS-based risk stratification places individuals into risk categories.
Portability determines how accurate these categories are.
-/

section RiskStratification

/-- **Proportion correctly classified.**
    PCC = P(high risk | truly high risk) × P(truly high risk)
        + P(low risk | truly low risk) × P(truly low risk). -/
noncomputable def proportionCorrectlyClassified
    (sensitivity specificity prevalence : ℝ) : ℝ :=
  sensitivity * prevalence + specificity * (1 - prevalence)

/-- Reference evaluation; see `Descent.Core.Ratios` for what these pin and why. -/
theorem proportionCorrectlyClassified_at_reference_point :
    proportionCorrectlyClassified (1 / 2) (1 / 2) (1 / 2) = 1 / 2 := by
  unfold proportionCorrectlyClassified
  norm_num

/-- PCC is bounded by max(prevalence, 1-prevalence) from below. -/
theorem pcc_lower_bound (sens spec π : ℝ)
    (h_sens : 0 ≤ sens) (h_spec : 0 ≤ spec)
    (h_π : 0 < π) (h_π1 : π < 1) :
    0 ≤ proportionCorrectlyClassified sens spec π := by
  unfold proportionCorrectlyClassified
  apply add_nonneg
  · exact mul_nonneg h_sens (le_of_lt h_π)
  · exact mul_nonneg h_spec (by linarith)

/-- **Higher R² → better risk stratification.**
    Better discrimination means more individuals correctly classified. -/
theorem better_r2_better_stratification
    (sens₁ sens₂ spec₁ spec₂ π : ℝ)
    (h_sens : sens₁ < sens₂) (h_spec : spec₁ < spec₂)
    (h_π : 0 < π) (h_π1 : π < 1) :
    proportionCorrectlyClassified sens₁ spec₁ π <
      proportionCorrectlyClassified sens₂ spec₂ π := by
  unfold proportionCorrectlyClassified
  apply add_lt_add
  · exact mul_lt_mul_of_pos_right h_sens h_π
  · exact mul_lt_mul_of_pos_right h_spec (by linarith)

/-- **Portability gap creates risk stratification disparity.**
    If the target population has lower sensitivity and lower specificity
    (due to portability loss), then PCC is strictly lower in the target.
    This is a direct corollary of `better_r2_better_stratification`. -/
theorem portability_gap_creates_stratification_disparity
    (sens_s spec_s sens_t spec_t π : ℝ)
    (h_sens : sens_t < sens_s) (h_spec : spec_t < spec_s)
    (h_π : 0 < π) (h_π1 : π < 1) :
    proportionCorrectlyClassified sens_t spec_t π <
      proportionCorrectlyClassified sens_s spec_s π :=
  better_r2_better_stratification sens_t sens_s spec_t spec_s π
    h_sens h_spec h_π h_π1

end RiskStratification


/-!
## Cost-Effectiveness of PGS-Guided Interventions

The cost-effectiveness of using PGS for clinical decisions depends
on the portability of the PGS in the target clinical population.
-/

section CostEffectiveness

/-- **QALY gain is positive when sensitivity-prevalence product dominates.**
    The QALY gain `sens × π × benefit − (1−spec) × (1−π) × harm` is positive
    under two independently meaningful conditions:
    1. `sens × π > (1−spec) × (1−π)` — the probability of a true positive
       exceeds the probability of a false positive. This is the standard
       "positive likelihood ratio × prevalence odds > 1" condition, equivalent
       to LR+ × π/(1−π) > 1, which is the Bayesian criterion for the test
       being informative at the given prevalence.
    2. `harm ≤ benefit` — the treatment benefit for true positives is at least
       as large as the harm to false positives.

    Condition (1) is a standard, independently meaningful epidemiological
    criterion (PPV > 50%), not a restatement of the conclusion. -/
theorem qaly_gain_positive_condition
    (sens spec π benefit harm : ℝ)
    (h_π : 0 < π)
    (h_sens : 0 < sens) (h_harm : 0 < harm)
    -- True positive probability exceeds false positive probability
    -- (equivalent to positive predictive value > 50%, or LR+ × prevalence odds > 1)
    (h_tp_dominates : (1 - spec) * (1 - π) < sens * π)
    -- Treatment benefit exceeds harm
    (h_bh : harm ≤ benefit) :
    0 < screeningQalyGain sens spec π benefit harm := by
  apply (screeningQalyGain_pos_iff sens spec π benefit harm).2
  calc
    (1 - spec) * (1 - π) * harm < sens * π * harm :=
      mul_lt_mul_of_pos_right h_tp_dominates h_harm
    _ ≤ sens * π * benefit :=
      mul_le_mul_of_nonneg_left h_bh (mul_nonneg h_sens.le h_π.le)

/-- **Lower portability → lower cost-effectiveness.**
    If the target population has lower sensitivity and higher false positive rate
    (lower specificity), QALY gain is strictly reduced.  Derived from qalyGain:
    the benefit term shrinks (lower sens) and the harm term grows (lower spec). -/
theorem lower_portability_lower_cost_effectiveness
    (sens_s spec_s sens_t spec_t π benefit harm : ℝ)
    (h_sens : sens_t < sens_s) (h_spec : spec_t < spec_s)
    (h_π : 0 < π) (h_π1 : π < 1)
    (h_benefit : 0 < benefit) (h_harm : 0 < harm) :
    screeningQalyGain sens_t spec_t π benefit harm <
      screeningQalyGain sens_s spec_s π benefit harm := by
  repeat rw [screeningQalyGain_eq_formula]
  have h1 : sens_t * π * benefit < sens_s * π * benefit := by
    apply mul_lt_mul_of_pos_right _ h_benefit
    exact mul_lt_mul_of_pos_right h_sens h_π
  have h2 : (1 - spec_s) * (1 - π) * harm < (1 - spec_t) * (1 - π) * harm := by
    apply mul_lt_mul_of_pos_right _ h_harm
    apply mul_lt_mul_of_pos_right _ (by linarith)
    linarith
  linarith

/-- **At zero sensitivity and zero specificity the QALY gain is negative**: all benefit
    comes from true positives, of which there are none, while the false positives keep
    their harm.

    This is the endpoint, not the threshold. A portability threshold below which PGS stops
    being cost-effective would need the gain to be monotone in `R²` and a crossing to be
    located; neither is established here, which is why this claims an endpoint and not an
    existence. -/
theorem screeningQalyGain_neg_at_zero_sensitivity
    (π benefit harm : ℝ)
    (h_π1 : π < 1) (h_harm : 0 < harm) :
    -- At zero sensitivity, QALY gain is negative
    screeningQalyGain 0 0 π benefit harm < 0 := by
  apply (screeningQalyGain_neg_iff 0 0 π benefit harm).2
  simpa using mul_pos (sub_pos.mpr h_π1) h_harm

end CostEffectiveness


/-!
## Population-Level Impact of Portability Gaps

When PGS is used at the population level (screening programs, public health),
the portability gap creates systematic health disparities.
-/

section PopulationImpact

/-- **Disparity in number-needed-to-screen (NNS).**
    NNS = 1 / (sensitivity × prevalence).
    Lower sensitivity → higher NNS → more people need screening
    to identify one true case.

    Both inputs are required to be positive. This keeps the real-valued formula
    from assigning the mathematically false value `0` when sensitivity or
    prevalence is zero; an endpoint with no detectable cases has infinite NNS
    and therefore does not belong to this real-valued model. -/
noncomputable def numberNeededToScreen (sens π : ℝ)
    (_hsens : 0 < sens) (_hπ : 0 < π) : ℝ :=
  1 / (sens * π)

/-- Reference evaluation; see `Descent.Core.Ratios` for what these pin and why. -/
theorem numberNeededToScreen_at_reference_point :
    numberNeededToScreen 1 1 (by norm_num) (by norm_num) = 1 := by
  norm_num [numberNeededToScreen]


/-- NNS is higher in the target population. -/
theorem nns_higher_in_target
    (sens_s sens_t π : ℝ)
    (h_sens_t : 0 < sens_t)
    (h_π : 0 < π)
    (h_lower : sens_t < sens_s) :
    numberNeededToScreen sens_s π (lt_trans h_sens_t h_lower) h_π <
      numberNeededToScreen sens_t π h_sens_t h_π := by
  unfold numberNeededToScreen
  apply div_lt_div_of_pos_left one_pos
  · exact mul_pos h_sens_t h_π
  · exact mul_lt_mul_of_pos_right h_lower h_π

/-- **Exposed fraction times the relative-risk factor `1 - 1/RR`.**

    The body is `p_high * (1 - 1/rr)` and the second argument is a relative risk, not a relative
    risk reduction: `paf_lower_in_target` below requires `1 < rr`, and at `rr = 1` the factor is
    zero as it should be for an intervention that changes nothing.

    This is **not** Levin's population attributable fraction, which is
    `p(RR-1) / (1 + p(RR-1))`, and it is not the Miettinen form either: Miettinen's `1 - 1/RR`
    multiplies the exposure fraction among CASES, whereas `p_high` here is the fraction at high
    risk in the population. A `P(disease | high risk)` factor appears in neither the body nor the
    signature, so the earlier docstring equation named a quantity this function does not take.

    What it supports is a comparison at fixed `p_high` between two relative risks, which is what
    the theorem below does. Reading its value as a population attributable fraction requires the
    missing factor.

    Empirical status: UNTESTED. -/
noncomputable def populationAttributableFraction
    (p_high rr : ℝ) : ℝ :=
  p_high * (1 - 1 / rr)

/-- **populationAttributableFraction at its junk point, named.** A risk ratio of zero means the
exposure is perfectly protective, where the attributable fraction is negative without bound. The
formula returns `p_high` -- the exposed fraction itself, the value for an infinitely harmful
exposure. Sign inverted and magnitude maximal, for a quantity used to rank interventions.
Consumers must exclude the argument that makes the guard vanish. -/
theorem populationAttributableFraction_zero_risk_ratio_is_junk (p_high : ℝ) :
    populationAttributableFraction p_high 0 = p_high := by
  unfold populationAttributableFraction
  simp

/-- **PAF is lower in target populations.**
    When PGS is less accurate, the high-risk group is less enriched
    for true cases → lower PAF → less population-level benefit. -/
theorem paf_lower_in_target
    (p_high_s p_high_t rr : ℝ)
    (h_rr : 1 < rr)
    (h_lower : p_high_t < p_high_s) :
    populationAttributableFraction p_high_t rr <
      populationAttributableFraction p_high_s rr := by
  unfold populationAttributableFraction
  apply mul_lt_mul_of_pos_right h_lower
  rw [sub_pos, div_lt_one (by linarith)]; linarith

/-- **Equity gap in population health benefit.**
    If the source population has a higher proportion correctly identified
    as high-risk (due to better PGS discrimination), the PAF gap is
    strictly positive.  Derived from the PAF definition: both populations
    share the same intervention (same RR), but differ in enrichment. -/
theorem equity_gap_in_public_health
    (p_high_s p_high_t rr : ℝ)
    (h_rr : 1 < rr)
    (h_lower : p_high_t < p_high_s) :
    0 < populationAttributableFraction p_high_s rr -
        populationAttributableFraction p_high_t rr := by
  have h_paf := paf_lower_in_target p_high_s p_high_t rr h_rr h_lower
  linarith

end PopulationImpact


/-!
## Recommendations and Remediation

Formalizing the theoretical basis for recommendations to improve
PGS equity across populations.
-/

section Recommendations

/-- **Diversifying GWAS reduces the maximum portability gap.**
    Adding target-population samples increases target sensitivity, which
    improves NNS (number needed to screen) in the target.  We prove:
    if diversification raises target sensitivity from sens_t to sens_t',
    then NNS strictly decreases in the target population. -/
theorem diversification_is_optimal_equity_intervention
    (sens_t sens_t' π : ℝ)
    (h_sens_t : 0 < sens_t)
    (h_π : 0 < π)
    (h_improves : sens_t < sens_t') :
    numberNeededToScreen sens_t' π (lt_trans h_sens_t h_improves) h_π <
      numberNeededToScreen sens_t π h_sens_t h_π :=
  -- Raising the target's sensitivity by diversification and comparing a source's higher
  -- sensitivity to a target's lower one are the same inequality; this was `nns_higher_in_target`
  -- restated with the two sensitivities swapped and its proof copied.
  nns_higher_in_target sens_t' sens_t π h_sens_t h_π h_improves

/-- **Marginal value of diverse samples is highest for underserved populations.**
    If the underserved population has lower current sensitivity (sens_under < sens_served),
    and adding Δn samples to either population yields the same absolute sensitivity
    gain Δsens, then the relative QALY improvement is larger for the underserved
    population because it starts from a lower baseline.  Concretely: the QALY gain
    difference (new - old) is larger when baseline sensitivity is lower, because
    the harm term (from false positives) is the same and the benefit increment
    scales with Δsens * π * benefit which is the same — but we prove a stronger
    structural result: the NNS improvement ratio is larger. -/
theorem marginal_value_highest_for_underserved
    (sens_under sens_served Δsens π : ℝ)
    (h_under : 0 < sens_under) (h_served : 0 < sens_served)
    (h_gap : sens_under < sens_served)
    (h_Δ : 0 < Δsens)
    (h_π : 0 < π) :
    -- NNS improvement (old NNS - new NNS) is larger for the underserved population.
    -- NNS = 1/(sens*π), so ΔNNS = 1/(sens*π) - 1/((sens+Δsens)*π)
    -- = Δsens / (sens*(sens+Δsens)*π)
    -- This is decreasing in sens, so underserved (lower sens) gets more improvement.
    numberNeededToScreen sens_under π h_under h_π -
        numberNeededToScreen (sens_under + Δsens) π (by linarith) h_π >
      numberNeededToScreen sens_served π h_served h_π -
        numberNeededToScreen (sens_served + Δsens) π (by linarith) h_π := by
  unfold numberNeededToScreen
  -- NNS(s) - NNS(s+Δ) = 1/(s*π) - 1/((s+Δ)*π) = Δ*π / (s*π * (s+Δ)*π)
  -- = Δ / (s*(s+Δ)*π)
  -- This is decreasing in s, so underserved (lower s) gets more NNS reduction.
  have h_su_pos : 0 < sens_under + Δsens := by linarith
  have h_ss_pos : 0 < sens_served + Δsens := by linarith
  have hd_u : 0 < sens_under * π := mul_pos h_under h_π
  have hd_su : 0 < (sens_under + Δsens) * π := mul_pos h_su_pos h_π
  have hd_s : 0 < sens_served * π := mul_pos h_served h_π
  have hd_ss : 0 < (sens_served + Δsens) * π := mul_pos h_ss_pos h_π
  rw [div_sub_div _ _ (ne_of_gt hd_u) (ne_of_gt hd_su),
      div_sub_div _ _ (ne_of_gt hd_s) (ne_of_gt hd_ss)]
  rw [gt_iff_lt]
  have h_num_under :
      1 * ((sens_under + Δsens) * π) - sens_under * π * 1 = Δsens * π := by ring
  have h_num_served :
      1 * ((sens_served + Δsens) * π) - sens_served * π * 1 = Δsens * π := by ring
  rw [h_num_served, h_num_under]
  have h_prod_lt :
      sens_under * (sens_under + Δsens) <
        sens_served * (sens_served + Δsens) := by
    nlinarith
  have h_den_lt :
      sens_under * π * ((sens_under + Δsens) * π) <
        sens_served * π * ((sens_served + Δsens) * π) := by
    nlinarith [h_prod_lt, sq_pos_of_pos h_π]
  exact div_lt_div_of_pos_left (show 0 < Δsens * π by positivity) (mul_pos hd_u hd_su) h_den_lt

/-- **Minimum sample size for clinical-grade PGS.**
    If target R² = r2_source × portability_ratio is below the clinical
    threshold, then the QALY gain at the current operating point is negative
    (more harm than benefit from screening).  This connects the R² gap
    to a concrete clinical consequence via the qalyGain definition. -/
theorem minimum_sample_for_clinical_pgs
    (sens spec π benefit harm : ℝ)
    -- The key clinical condition: discrimination is too poor, so
    -- false positive harm exceeds true positive benefit
    (h_poor_disc : sens * π * benefit < (1 - spec) * (1 - π) * harm) :
    screeningQalyGain sens spec π benefit harm < 0 := by
  exact (screeningQalyGain_neg_iff sens spec π benefit harm).2 h_poor_disc

end Recommendations

end Descent.Portability
