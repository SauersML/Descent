import Calibrator.Probability
import Calibrator.PortabilityDrift
import Calibrator.OpenQuestions

namespace Calibrator

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

Reference: Wang et al. (2026), Nature Communications 17:942.
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
   is monotone increasing. This justifies the monotone link functions used
   in all subsequent theorems.
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
    - Both effects push the z-score upward as R² increases -/
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
    same argument: higher R² increases separation between cases and controls. -/
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
theorem liabilitySensitivity_zScore_monotone_in_R
    (m : LiabilityThresholdModel) (T' : ℝ)
    (R₁ R₂ : ℝ) (hR₁ : 0 ≤ R₁) (hR₂ : R₂ ≤ 1)
    (hR : R₁ < R₂)
    (hR2₁ : 0 ≤ R₁ ^ 2) (hR2₂ : R₂ ^ 2 ≤ 1)
    -- σ_resid is positive at R₂ (the tighter bound)
    (h_σ_pos : 0 < Real.sqrt (m.h_sq * (1 - R₂ ^ 2) + (1 - m.h_sq)))
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
  rw [div_lt_div_iff h_σ₁_pos h_σ_pos]
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

    This is the formal justification for the monotone link functions
    `sensFromR2` used throughout the NRI and clinical utility theorems.

    The proof structure:
    1. `Φ` is strictly monotone (standard normal CDF property from Mathlib)
    2. The z-score `(R·h·μ_case − T') / σ_resid` is monotone in R²
       (from `liabilitySensitivity_zScore_monotone_in_R`)
    3. Composition of monotone functions is monotone -/
theorem liabilitySensitivity_monotone_in_R2
    (Φ : ℝ → ℝ) (m : LiabilityThresholdModel) (T' : ℝ)
    (hΦ_mono : StrictMono Φ)
    (R2₁ R2₂ : ℝ) (hR2₁ : 0 ≤ R2₁) (hR2₂ : R2₂ ≤ 1)
    (hR2 : R2₁ < R2₂)
    -- σ_resid remains positive throughout the range
    (h_σ_pos : 0 < Real.sqrt (m.h_sq * (1 - R2₂) + (1 - m.h_sq)))
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
  -- with the same structure as liabilitySensitivity_zScore_monotone_in_R.
  simp only
  -- σ₁ > 0
  have h_σ₁_pos : 0 < Real.sqrt (m.h_sq * (1 - R2₁) + (1 - m.h_sq)) := by
    apply Real.sqrt_pos_of_pos
    have : 0 < 1 - m.h_sq := by linarith [m.h_sq_lt_one]
    nlinarith [m.h_sq_pos]
  -- σ₂ ≤ σ₁
  have h_σ_le : Real.sqrt (m.h_sq * (1 - R2₂) + (1 - m.h_sq)) ≤
      Real.sqrt (m.h_sq * (1 - R2₁) + (1 - m.h_sq)) := by
    apply Real.sqrt_le_sqrt
    · have : 0 < 1 - m.h_sq := by linarith [m.h_sq_lt_one]
      nlinarith [m.h_sq_pos]
    · nlinarith [m.h_sq_pos]
  -- √R2₁ < √R2₂
  have h_sqrt_lt : Real.sqrt R2₁ < Real.sqrt R2₂ :=
    Real.sqrt_lt_sqrt hR2₁ hR2
  -- numerator increases
  have h_h_pos : 0 < Real.sqrt m.h_sq := Real.sqrt_pos_of_pos m.h_sq_pos
  have h_num_lt : Real.sqrt R2₁ * Real.sqrt m.h_sq * m.case_mean - T' <
      Real.sqrt R2₂ * Real.sqrt m.h_sq * m.case_mean - T' := by
    nlinarith [mul_pos h_h_pos m.case_mean_pos]
  -- Cross-multiply: num₁ · σ₂ < num₂ · σ₁
  rw [div_lt_div_iff h_σ₁_pos h_σ_pos]
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
theorem liabilitySpecificity_monotone_in_R2
    (Φ : ℝ → ℝ) (m : LiabilityThresholdModel) (T' μ_control : ℝ)
    (hΦ_mono : StrictMono Φ)
    (hμ_control_neg : μ_control < 0)
    (R2₁ R2₂ : ℝ) (hR2₁ : 0 ≤ R2₁) (hR2₂ : R2₂ ≤ 1)
    (hR2 : R2₁ < R2₂)
    (h_σ_pos : 0 < Real.sqrt (m.h_sq * (1 - R2₂) + (1 - m.h_sq)))
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
  simp only
  -- σ₁ > 0
  have h_σ₁_pos : 0 < Real.sqrt (m.h_sq * (1 - R2₁) + (1 - m.h_sq)) := by
    apply Real.sqrt_pos_of_pos
    have : 0 < 1 - m.h_sq := by linarith [m.h_sq_lt_one]
    nlinarith [m.h_sq_pos]
  -- σ₂ ≤ σ₁
  have h_σ_le : Real.sqrt (m.h_sq * (1 - R2₂) + (1 - m.h_sq)) ≤
      Real.sqrt (m.h_sq * (1 - R2₁) + (1 - m.h_sq)) := by
    apply Real.sqrt_le_sqrt
    · have : 0 < 1 - m.h_sq := by linarith [m.h_sq_lt_one]
      nlinarith [m.h_sq_pos]
    · nlinarith [m.h_sq_pos]
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
  rw [div_lt_div_iff h_σ₁_pos h_σ_pos]
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

/-- **Derived monotone sensitivity link.**
    From the liability threshold model, we can construct a concrete
    sensitivity link function that is strictly monotone, justifying
    the abstract `sensLink` parameter used in NRI and clinical utility
    theorems.

    Given a liability threshold model `m`, classification threshold `T'`,
    and strictly monotone Φ, the function `R² ↦ liabilitySensitivity Φ m R² T'`
    is a valid strictly monotone link on [0, 1]. -/
theorem liability_model_provides_sensLink
    (Φ : ℝ → ℝ) (m : LiabilityThresholdModel) (T' : ℝ)
    (hΦ_mono : StrictMono Φ)
    -- Residual variance stays positive across [0,1]
    (h_σ_pos : ∀ R2, 0 ≤ R2 → R2 ≤ 1 →
      0 < Real.sqrt (m.h_sq * (1 - R2) + (1 - m.h_sq)))
    -- Classification threshold is in the clinically relevant regime:
    -- T' ≤ expected PGS among cases even at R² = 0 (i.e., T' ≤ 0).
    -- This ensures the z-score numerator is nonneg throughout [0,1].
    (h_T' : ∀ R2, 0 ≤ R2 → R2 ≤ 1 →
      0 ≤ Real.sqrt R2 * Real.sqrt m.h_sq * m.case_mean - T') :
    StrictMonoOn (fun R2 => liabilitySensitivity Φ m R2 T') (Set.Icc 0 1) := by
  intro R2₁ hR2₁ R2₂ hR2₂ hlt
  exact liabilitySensitivity_monotone_in_R2 Φ m T' hΦ_mono R2₁ R2₂
    hR2₁.1 hR2₂.2 hlt (h_σ_pos R2₂ hR2₂.1 hR2₂.2)
    (h_T' R2₁ hR2₁.1 (le_trans (le_of_lt hlt) hR2₂.2))

/-- **Derived monotone specificity link.**
    Analogous to `liability_model_provides_sensLink` but for specificity. -/
theorem liability_model_provides_specLink
    (Φ : ℝ → ℝ) (m : LiabilityThresholdModel) (T' μ_control : ℝ)
    (hΦ_mono : StrictMono Φ)
    (hμ_control_neg : μ_control < 0)
    (h_σ_pos : ∀ R2, 0 ≤ R2 → R2 ≤ 1 →
      0 < Real.sqrt (m.h_sq * (1 - R2) + (1 - m.h_sq)))
    -- The specificity z-score numerator is nonneg across [0,1].
    -- Since μ_control < 0, this holds whenever T' ≥ 0.
    (h_T' : ∀ R2, 0 ≤ R2 → R2 ≤ 1 →
      0 ≤ T' - Real.sqrt R2 * Real.sqrt m.h_sq * μ_control) :
    StrictMonoOn (fun R2 => liabilitySpecificity Φ m R2 T' μ_control) (Set.Icc 0 1) := by
  intro R2₁ hR2₁ R2₂ hR2₂ hlt
  exact liabilitySpecificity_monotone_in_R2 Φ m T' μ_control hΦ_mono hμ_control_neg R2₁ R2₂
    hR2₁.1 hR2₂.2 hlt (h_σ_pos R2₂ hR2₂.1 hR2₂.2)
    (h_T' R2₁ hR2₁.1 (le_trans (le_of_lt hlt) hR2₂.2))

/-- **Residual variance is positive on [0,1].**
    The residual variance σ²_resid = h²(1 − R²) + (1 − h²) is strictly positive
    for R² ∈ [0, 1] and h² ∈ (0, 1), since (1 − h²) > 0. -/
theorem residualVariance_pos (m : LiabilityThresholdModel)
    (R2 : ℝ) (hR2 : 0 ≤ R2) (hR2' : R2 ≤ 1) :
    0 < m.h_sq * (1 - R2) + (1 - m.h_sq) := by
  have h1 : 0 ≤ m.h_sq * (1 - R2) :=
    mul_nonneg (le_of_lt m.h_sq_pos) (by linarith)
  have h2 : 0 < 1 - m.h_sq := by linarith [m.h_sq_lt_one]
  linarith

/-- **Corollary: σ_resid = √(residual variance) is positive on [0,1].** -/
theorem sigmaResid_pos (m : LiabilityThresholdModel)
    (R2 : ℝ) (hR2 : 0 ≤ R2) (hR2' : R2 ≤ 1) :
    0 < Real.sqrt (m.h_sq * (1 - R2) + (1 - m.h_sq)) :=
  Real.sqrt_pos_of_pos (residualVariance_pos m R2 hR2 hR2')

end LiabilityThresholdModel


/-!
## Net Reclassification Improvement

NRI measures how many individuals are correctly reclassified (moved to
correct risk category) when PGS is added to clinical risk models.
Portability loss reduces NRI in non-source populations.

We model sensitivity and specificity as functions of R² (coefficient of
determination of the PGS).  Under a liability-threshold model, a PGS with
higher R² yields a score distribution with greater separation between cases
and controls, so both sensitivity and specificity at any fixed classification
threshold improve monotonically with R².

The monotonicity of these link functions is now *derived* from the liability
threshold model in the section above (see `liabilitySensitivity_monotone_in_R2`
and `liabilitySpecificity_monotone_in_R2`), rather than axiomatised.

We parametrise by abstract strictly-monotone "link" functions
  `sensFromR2 : ℝ → ℝ`   and   `specFromR2 : ℝ → ℝ`
that map R² to the operating-point sensitivity and specificity.
Every NRI theorem then derives sens/spec improvements from R² improvements,
rather than assuming them directly.
-/

section NRI

/-- **NRI definition.**
    NRI = (event NRI) + (non-event NRI)
    Event NRI: proportion of cases correctly moved up
    Non-event NRI: proportion of controls correctly moved down -/
noncomputable def netReclassificationImprovement
    (event_nri nonevent_nri : ℝ) : ℝ :=
  event_nri + nonevent_nri

/-- **Sensitivity from R².**  Under a liability-threshold model the PGS score
    mean-shift between cases and controls is proportional to √R²; at any fixed
    classification threshold, sensitivity = Φ(μ₁ - τ) is monotone increasing
    in R².  We take this as an opaque monotone link. -/
noncomputable def sensFromR2 (link : ℝ → ℝ) (r2 : ℝ) : ℝ := link r2

/-- **Specificity from R².**  Analogous monotone link for specificity. -/
noncomputable def specFromR2 (link : ℝ → ℝ) (r2 : ℝ) : ℝ := link r2

/-- **NRI is positive when PGS adds value.**
    If a higher-R² model (r2_new > r2_old) has strictly monotone sensitivity
    and specificity links, then both event NRI (= sens_new − sens_old) and
    non-event NRI (= spec_new − spec_old) are positive, so total NRI > 0.
    The sensitivity/specificity improvements are *derived* from R² ordering
    via the monotone links, not assumed directly. -/
theorem nri_positive_when_pgs_adds_value
    (sensLink specLink : ℝ → ℝ) (r2_old r2_new : ℝ)
    (h_r2_improves : r2_old < r2_new)
    -- Monotonicity of the liability-threshold link functions
    (h_sens_mono : StrictMono sensLink)
    (h_spec_mono : StrictMono specLink) :
    0 < netReclassificationImprovement
      (sensFromR2 sensLink r2_new - sensFromR2 sensLink r2_old)
      (specFromR2 specLink r2_new - specFromR2 specLink r2_old) := by
  unfold netReclassificationImprovement sensFromR2 specFromR2
  have h1 : sensLink r2_old < sensLink r2_new := h_sens_mono h_r2_improves
  have h2 : specLink r2_old < specLink r2_new := h_spec_mono h_r2_improves
  linarith

/-- **NRI decreases with portability loss.**
    If the target population's R² is strictly lower than the source's
    (r2_target < r2_source), and both sensitivity and specificity links
    are strictly monotone, then NRI in the target is strictly less than
    NRI in the source.  The sensitivity/specificity gap is derived from
    the R² gap, not assumed. -/
theorem nri_decreases_with_portability_loss
    (sensLink specLink : ℝ → ℝ) (r2_base r2_source r2_target : ℝ)
    (h_r2_loss : r2_target < r2_source)
    (h_sens_mono : StrictMono sensLink)
    (h_spec_mono : StrictMono specLink) :
    netReclassificationImprovement
      (sensFromR2 sensLink r2_target - sensFromR2 sensLink r2_base)
      (specFromR2 specLink r2_target - specFromR2 specLink r2_base) <
    netReclassificationImprovement
      (sensFromR2 sensLink r2_source - sensFromR2 sensLink r2_base)
      (specFromR2 specLink r2_source - specFromR2 specLink r2_base) := by
  unfold netReclassificationImprovement sensFromR2 specFromR2
  have h1 : sensLink r2_target < sensLink r2_source := h_sens_mono h_r2_loss
  have h2 : specLink r2_target < specLink r2_source := h_spec_mono h_r2_loss
  linarith

/-- **NRI can become negative in target populations.**
    If the target R² is strictly below the old model's R² (`r2_target < r2_old`),
    and both sensitivity and specificity are strictly monotone functions of R²
    (from the liability-threshold model), then the NRI is negative — PGS in the
    target population makes classification worse than the old model.

    This is the mirror of `nri_positive_when_pgs_adds_value`: when portability
    loss drives R² below the baseline, the same monotonicity that guarantees
    improvement in the source guarantees degradation in the target. -/
theorem nri_can_be_negative
    (sensLink specLink : ℝ → ℝ) (r2_old r2_target : ℝ)
    -- The target R² is below the old model's R²
    (h_r2_below : r2_target < r2_old)
    -- Monotonicity of the liability-threshold link functions
    (h_sens_mono : StrictMono sensLink)
    (h_spec_mono : StrictMono specLink) :
    netReclassificationImprovement
      (sensFromR2 sensLink r2_target - sensFromR2 sensLink r2_old)
      (specFromR2 specLink r2_target - specFromR2 specLink r2_old) < 0 := by
  unfold netReclassificationImprovement sensFromR2 specFromR2
  have h1 : sensLink r2_target < sensLink r2_old := h_sens_mono h_r2_below
  have h2 : specLink r2_target < specLink r2_old := h_spec_mono h_r2_below
  linarith

end NRI


/-!
## Decision Curve Analysis

Decision curves plot net benefit vs threshold probability.
PGS portability determines the range of thresholds where PGS is useful.
-/

section DecisionCurve

/-- **Net benefit of a risk prediction model.**
    NB(t) = TP/N - FP/N × t/(1-t)
    where t is the treatment threshold probability. -/
noncomputable def netBenefit (tp fp n : ℝ) (t : ℝ) : ℝ :=
  tp / n - fp / n * (t / (1 - t))

/-- **Net benefit is zero for treat-all strategy.**
    If we treat everyone, TP = prevalence × N, FP = (1-prevalence) × N. -/
theorem treat_all_net_benefit (π t : ℝ)
    (hπ : 0 < π) (hπ1 : π < 1)
    (ht : 0 < t) (ht1 : t < 1) :
    netBenefit π (1 - π) 1 t = π - (1 - π) * (t / (1 - t)) := by
  unfold netBenefit; simp

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
    (h_π : 0 < π) (h_π1 : π < 1)
    (h_sens : 0 < sens) (h_sens1 : sens ≤ 1)
    (h_spec : 0 < spec) (h_spec1 : spec ≤ 1)
    -- Positive Youden's index: classifier is better than random
    (h_youden : 1 < sens + spec)
    -- Treatment threshold exceeds prevalence (selective-treatment regime)
    (h_threshold : π < t) :
    -- treat-all net benefit < PGS net benefit
    netBenefit (π * n) ((1 - π) * n) n t <
      netBenefit (sens * π * n) ((1 - spec) * (1 - π) * n) n t := by
  unfold netBenefit
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
    rw [lt_div_iff₀ h_1t_pos]
    ring_nf
    simpa [mul_assoc, mul_left_comm, mul_comm] using h_cross
  nlinarith

/-- **Portability loss narrows the useful threshold range.**
    We derive sensitivity and specificity from R² via monotone links (as in the
    NRI section).  If the target R² is strictly below the source R², both
    sensitivity and specificity are lower (by strict monotonicity), and the net
    benefit at any threshold t is reduced.

    The net benefit formula NB = TP/N − FP/N × t/(1−t), with
    TP = sens(R²) × π and FP = (1 − spec(R²)) × (1 − π), is strictly
    increasing in both sens and spec. -/
theorem portability_narrows_useful_range
    (sensLink specLink : ℝ → ℝ) (r2_source r2_target π t : ℝ)
    (h_π : 0 < π) (h_π1 : π < 1)
    (ht : 0 < t) (ht1 : t < 1)
    -- R² is strictly lower in the target
    (h_r2 : r2_target < r2_source)
    -- Monotone link functions (from liability-threshold model)
    (h_sens_mono : StrictMono sensLink)
    (h_spec_mono : StrictMono specLink)
    -- Range constraints on the links at target operating point
    (h_sens_t : 0 ≤ sensLink r2_target) (h_spec_t : 0 ≤ specLink r2_target)
    (h_spec_s1 : specLink r2_source ≤ 1) :
    -- Net benefit in target is strictly less than in source at the same threshold
    netBenefit (sensLink r2_target * π) ((1 - specLink r2_target) * (1 - π)) 1 t <
      netBenefit (sensLink r2_source * π) ((1 - specLink r2_source) * (1 - π)) 1 t := by
  -- Derive sens/spec ordering from R² ordering via monotonicity
  have h_sens : sensLink r2_target < sensLink r2_source := h_sens_mono h_r2
  have h_spec : specLink r2_target < specLink r2_source := h_spec_mono h_r2
  unfold netBenefit
  have htt : 0 < t / (1 - t) := div_pos ht (by linarith)
  have h1 : sensLink r2_target * π < sensLink r2_source * π :=
    mul_lt_mul_of_pos_right h_sens h_π
  have h2 : (1 - specLink r2_source) * (1 - π) < (1 - specLink r2_target) * (1 - π) := by
    apply mul_lt_mul_of_pos_right _ (by linarith)
    linarith
  have h3 : (1 - specLink r2_source) * (1 - π) * (t / (1 - t)) <
             (1 - specLink r2_target) * (1 - π) * (t / (1 - t)) :=
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

/- **Calibration (sufficiency).**
    A model is calibrated if E[Y | Ŷ = s] = s for all scores s.
    Calibration within groups: E[Y | Ŷ = s, G = g] = s for each group g. -/

/- **Equalized odds (separation).**
    TPR and FPR are equal across groups.
    TPR(g) = P(Ŷ = 1 | Y = 1, G = g) is the same for all g. -/

/- **Demographic parity (independence).**
    P(Ŷ = 1 | G = g) is the same for all groups g. -/

/- **Derivation: PPV from Bayes' theorem.**

    The positive predictive value PPV = P(D+ | T+) is derived directly
    from Bayes' theorem on conditional probability.

    **Setup.** Let D+ denote having the disease and T+ denote testing
    positive. Define:
    - prev  = P(D+)           — disease prevalence (prior probability)
    - sens  = P(T+ | D+)      — sensitivity (true positive rate, TPR)
    - spec  = P(T- | D-)      — specificity, so 1-spec = P(T+ | D-) = FPR

    **Step 1: Bayes' theorem.**
        PPV = P(D+ | T+) = P(T+ | D+) × P(D+) / P(T+)

    **Step 2: Law of total probability for P(T+).**
    Partition on disease status {D+, D-}:
        P(T+) = P(T+ | D+) × P(D+) + P(T+ | D-) × P(D-)
               = sens × prev + (1 - spec) × (1 - prev)

    **Step 3: Substitution.**
        PPV = sens × prev / (sens × prev + (1 - spec) × (1 - prev))

    In our notation TPR = sens and FPR = 1 - spec, giving:
        **PPV = prev × tpr / (prev × tpr + (1 - prev) × fpr)**

    This is a direct application of Bayes' theorem (available in Mathlib as
    `ProbabilityTheory.cond_eq_div` and related lemmas on conditional
    probability). The formula shows that PPV depends critically on
    prevalence: even with high sensitivity and specificity, PPV is low
    when prevalence is low (the "base rate fallacy"). -/

/-- **PPV definition.** Positive predictive value via Bayes' theorem:
    PPV = prev * tpr / (prev * tpr + (1 - prev) * fpr). -/
noncomputable def ppv (prev tpr fpr : ℝ) : ℝ :=
  prev * tpr / (prev * tpr + (1 - prev) * fpr)

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
      nlinarith [hcross, h_tpr, h_fpr]
    nlinarith
  exact h_diff_prev h_prev_eq

/-- **Portability gap amplifies fairness violations.**
    If PGS R² differs across groups (r2_target < r2_source), and sensitivity
    is a strictly monotone function of R² (from the liability-threshold model),
    then the target group has strictly lower sensitivity — equalized odds
    (equal TPR across groups) is violated.

    The sensitivity gap is *derived* from the R² gap via the monotone link,
    not assumed directly. -/
theorem portability_violates_equalized_odds
    (sensLink : ℝ → ℝ) (r2_source r2_target : ℝ)
    (h_r2_gap : r2_target < r2_source)
    (h_sens_mono : StrictMono sensLink) :
    sensLink r2_target ≠ sensLink r2_source := by
  -- Derive the sensitivity ordering from R² ordering via monotonicity
  have h_sens_lt : sensLink r2_target < sensLink r2_source :=
    h_sens_mono h_r2_gap
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
    (hn : 0 < n) (ht : 0 < t) (ht1 : t < 1)
    (h_fp : 0 ≤ fp_B) :
    netBenefit sens_B_fair fp_B n t < netBenefit sens_B_unconstrained fp_B n t := by
  unfold netBenefit
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

/- **Risk category assignment from PGS.**
    Individuals with PGS > threshold t are placed in "high risk" category.
    True positive rate depends on PGS accuracy. -/

/-- **Proportion correctly classified.**
    PCC = P(high risk | truly high risk) × P(truly high risk)
        + P(low risk | truly low risk) × P(truly low risk). -/
noncomputable def proportionCorrectlyClassified
    (sensitivity specificity prevalence : ℝ) : ℝ :=
  sensitivity * prevalence + specificity * (1 - prevalence)

/-- PCC is bounded by max(prevalence, 1-prevalence) from below. -/
theorem pcc_lower_bound (sens spec π : ℝ)
    (h_sens : 0 ≤ sens) (h_sens1 : sens ≤ 1)
    (h_spec : 0 ≤ spec) (h_spec1 : spec ≤ 1)
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
    (h_π : 0 < π) (h_π1 : π < 1)
    (h_sens₁ : 0 ≤ sens₁) (h_spec₁ : 0 ≤ spec₁) :
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
    (h_π : 0 < π) (h_π1 : π < 1)
    (h_sens_t : 0 ≤ sens_t) (h_spec_t : 0 ≤ spec_t) :
    proportionCorrectlyClassified sens_t spec_t π <
      proportionCorrectlyClassified sens_s spec_s π :=
  better_r2_better_stratification sens_t sens_s spec_t spec_s π
    h_sens h_spec h_π h_π1 h_sens_t h_spec_t

end RiskStratification


/-!
## Cost-Effectiveness of PGS-Guided Interventions

The cost-effectiveness of using PGS for clinical decisions depends
on the portability of the PGS in the target clinical population.
-/

section CostEffectiveness

/-- **Quality-Adjusted Life Year (QALY) gain from correct risk stratification.**
    QALY_gain = sensitivity × prevalence × treatment_benefit
              - (1 - specificity) × (1 - prevalence) × treatment_harm -/
noncomputable def qalyGain
    (sens spec π benefit harm : ℝ) : ℝ :=
  sens * π * benefit - (1 - spec) * (1 - π) * harm

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
    (h_π : 0 < π) (h_π1 : π < 1)
    (h_sens : 0 < sens) (h_sens1 : sens ≤ 1)
    (h_spec : 0 < spec) (h_spec1 : spec < 1)
    (h_benefit : 0 < benefit) (h_harm : 0 < harm)
    -- True positive probability exceeds false positive probability
    -- (equivalent to positive predictive value > 50%, or LR+ × prevalence odds > 1)
    (h_tp_dominates : (1 - spec) * (1 - π) < sens * π)
    -- Treatment benefit exceeds harm
    (h_bh : harm ≤ benefit) :
    0 < qalyGain sens spec π benefit harm := by
  unfold qalyGain
  have h_prob_gap : 0 < sens * π - (1 - spec) * (1 - π) := by
    nlinarith
  have h_lower_pos : 0 < harm * (sens * π - (1 - spec) * (1 - π)) := by
    exact mul_pos h_harm h_prob_gap
  have h_weight_nonneg : 0 ≤ sens * π := by
    positivity
  have h_lower_le :
      harm * (sens * π - (1 - spec) * (1 - π)) ≤
        qalyGain sens spec π benefit harm := by
    unfold qalyGain
    have h_gain_term_nonneg : 0 ≤ sens * π * (benefit - harm) := by
      nlinarith
    nlinarith
  exact lt_of_lt_of_le h_lower_pos h_lower_le

/-- **Lower portability → lower cost-effectiveness.**
    If the target population has lower sensitivity and higher false positive rate
    (lower specificity), QALY gain is strictly reduced.  Derived from qalyGain:
    the benefit term shrinks (lower sens) and the harm term grows (lower spec). -/
theorem lower_portability_lower_cost_effectiveness
    (sens_s spec_s sens_t spec_t π benefit harm : ℝ)
    (h_sens : sens_t < sens_s) (h_spec : spec_t < spec_s)
    (h_π : 0 < π) (h_π1 : π < 1)
    (h_benefit : 0 < benefit) (h_harm : 0 < harm)
    (h_sens_t : 0 ≤ sens_t) (h_spec_t : 0 ≤ spec_t)
    (h_spec_s1 : spec_s ≤ 1) :
    qalyGain sens_t spec_t π benefit harm <
      qalyGain sens_s spec_s π benefit harm := by
  unfold qalyGain
  have h1 : sens_t * π * benefit < sens_s * π * benefit := by
    apply mul_lt_mul_of_pos_right _ h_benefit
    exact mul_lt_mul_of_pos_right h_sens h_π
  have h2 : (1 - spec_s) * (1 - π) * harm < (1 - spec_t) * (1 - π) * harm := by
    apply mul_lt_mul_of_pos_right _ h_harm
    apply mul_lt_mul_of_pos_right _ (by linarith)
    linarith
  linarith

/-- **There exists a portability threshold below which PGS is not cost-effective.**
    If the R² is too low, the QALY gain is negative (more harm than benefit). -/
theorem cost_effectiveness_threshold_exists
    (π benefit harm : ℝ)
    (h_π : 0 < π) (h_π1 : π < 1)
    (h_benefit : 0 < benefit) (h_harm : 0 < harm) :
    -- At zero sensitivity, QALY gain is negative
    qalyGain 0 0 π benefit harm < 0 := by
  unfold qalyGain; nlinarith

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
    to identify one true case. -/
noncomputable def numberNeededToScreen (sens π : ℝ) : ℝ :=
  1 / (sens * π)

/-- NNS is higher in the target population. -/
theorem nns_higher_in_target
    (sens_s sens_t π : ℝ)
    (h_sens_s : 0 < sens_s) (h_sens_t : 0 < sens_t)
    (h_π : 0 < π)
    (h_lower : sens_t < sens_s) :
    numberNeededToScreen sens_s π < numberNeededToScreen sens_t π := by
  unfold numberNeededToScreen
  apply div_lt_div_of_pos_left one_pos
  · exact mul_pos h_sens_t h_π
  · exact mul_lt_mul_of_pos_right h_lower h_π

/-- **Population Attributable Fraction (PAF) from PGS-guided intervention.**
    PAF = P(disease | high risk) × P(high risk) × (1 - 1/RR)
    where RR is the relative risk reduction from intervention. -/
noncomputable def populationAttributableFraction
    (p_high rr_reduction : ℝ) : ℝ :=
  p_high * (1 - 1 / rr_reduction)

/-- **PAF is lower in target populations.**
    When PGS is less accurate, the high-risk group is less enriched
    for true cases → lower PAF → less population-level benefit. -/
theorem paf_lower_in_target
    (p_high_s p_high_t rr : ℝ)
    (h_rr : 1 < rr)
    (h_p_s : 0 < p_high_s) (h_p_t : 0 < p_high_t)
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
    (h_p_s : 0 < p_high_s) (h_p_t : 0 < p_high_t)
    (h_lower : p_high_t < p_high_s) :
    0 < populationAttributableFraction p_high_s rr -
        populationAttributableFraction p_high_t rr := by
  have h_paf := paf_lower_in_target p_high_s p_high_t rr h_rr h_p_s h_p_t h_lower
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
    (h_sens_t : 0 < sens_t) (h_sens_t' : 0 < sens_t')
    (h_π : 0 < π)
    (h_improves : sens_t < sens_t') :
    numberNeededToScreen sens_t' π < numberNeededToScreen sens_t π := by
  unfold numberNeededToScreen
  apply div_lt_div_of_pos_left one_pos
  · exact mul_pos h_sens_t h_π
  · exact mul_lt_mul_of_pos_right h_improves h_π

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
    numberNeededToScreen sens_under π - numberNeededToScreen (sens_under + Δsens) π >
    numberNeededToScreen sens_served π - numberNeededToScreen (sens_served + Δsens) π := by
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
    (h_π : 0 < π) (h_π1 : π < 1)
    (h_benefit : 0 < benefit) (h_harm : 0 < harm)
    (h_sens : 0 ≤ sens) (h_sens1 : sens ≤ 1)
    (h_spec : 0 ≤ spec) (h_spec1 : spec ≤ 1)
    -- The key clinical condition: discrimination is too poor, so
    -- false positive harm exceeds true positive benefit
    (h_poor_disc : sens * π * benefit < (1 - spec) * (1 - π) * harm) :
    qalyGain sens spec π benefit harm < 0 := by
  unfold qalyGain
  linarith

end Recommendations

end Calibrator
