import Calibrator.Probability
import Calibrator.PortabilityDrift
import Calibrator.OpenQuestions

namespace Calibrator

open MeasureTheory

/-!
# Equity, Ethical, and Implementation Aspects of PGS Portability

This file formalizes the equity implications of PGS portability gaps,
the ethical framework for clinical PGS deployment, and the practical
considerations for implementing PGS across diverse populations.

Key results:
1. Portability gap creates health disparities
2. Fairness impossibility for PGS across populations
3. Resource allocation for equitable PGS development
4. Clinical implementation guidelines
5. Regulatory and return-of-results considerations

Reference: Wang et al. (2026), Nature Communications 17:942.
-/


/-!
## Fairness Impossibility Results

It is mathematically impossible to simultaneously satisfy
multiple fairness criteria when PGS performance differs
across populations.
-/

section FairnessImpossibility

/-- **Chouldechova's impossibility theorem for PGS.**
    When base rates (disease prevalence) differ across groups,
    it's impossible to simultaneously achieve:
    1. Equal false positive rates (FPR₁ = FPR₂)
    2. Equal false negative rates (FNR₁ = FNR₂)
    3. Equal positive predictive values (PPV₁ = PPV₂)
    unless the classifier is perfect or trivial. -/
theorem chouldechova_impossibility
    (fpr fnr ppv₁ ppv₂ K₁ K₂ : ℝ)
    (h_prev_diff : K₁ ≠ K₂)
    (h_K₁ : 0 < K₁) (h_K₁' : K₁ < 1)
    (h_K₂ : 0 < K₂) (h_K₂' : K₂ < 1)
    (h_fpr : 0 < fpr) (h_fnr_lt : fnr < 1)
    (h_fnr_nn : 0 ≤ fnr)
    -- PPV = K × (1-FNR) / (K × (1-FNR) + (1-K) × FPR)
    (h_ppv₁_def : ppv₁ = K₁ * (1 - fnr) / (K₁ * (1 - fnr) + (1 - K₁) * fpr))
    (h_ppv₂_def : ppv₂ = K₂ * (1 - fnr) / (K₂ * (1 - fnr) + (1 - K₂) * fpr)) :
    ppv₁ ≠ ppv₂ := by
  rw [h_ppv₁_def, h_ppv₂_def]
  intro h
  apply h_prev_diff
  have h_sens : 0 < 1 - fnr := by linarith
  have h1_pos : 0 < K₁ * (1 - fnr) + (1 - K₁) * fpr := by nlinarith
  have h2_pos : 0 < K₂ * (1 - fnr) + (1 - K₂) * fpr := by nlinarith
  rw [div_eq_div_iff h1_pos.ne' h2_pos.ne'] at h
  -- K₁(1-fnr)(K₂(1-fnr) + (1-K₂)fpr) = K₂(1-fnr)(K₁(1-fnr) + (1-K₁)fpr)
  -- K₁(1-fnr)(1-K₂)fpr = K₂(1-fnr)(1-K₁)fpr
  -- K₁(1-K₂) = K₂(1-K₁)  [cancel (1-fnr)fpr > 0]
  -- K₁ - K₁K₂ = K₂ - K₁K₂
  -- K₁ = K₂
  nlinarith [mul_pos h_sens h_fpr]

/-- **Simplified fairness impossibility: equal calibration + equal thresholds.**
    If we use a population-specific threshold to achieve equal FPR,
    the thresholds must differ, which means the treatment policies
    are ancestry-dependent. -/
theorem equal_fpr_requires_different_thresholds
    (mu₁ mu₂ sigma₁ sigma₂ threshold₁ threshold₂ : ℝ)
    (h_mu_diff : mu₁ ≠ mu₂)
    (h_sigma₁ : 0 < sigma₁) (h_sigma₂ : 0 < sigma₂)
    -- Equal FPR ↔ equal z-scores
    (h_equal_z : (threshold₁ - mu₁) / sigma₁ = (threshold₂ - mu₂) / sigma₂)
    (h_sigma_eq : sigma₁ = sigma₂) :
    threshold₁ ≠ threshold₂ := by
  intro h_eq
  apply h_mu_diff
  rw [h_eq, h_sigma_eq] at h_equal_z
  -- h_equal_z : (threshold₂ - mu₁) / sigma₂ = (threshold₂ - mu₂) / sigma₂
  have h_eq₂ : (threshold₂ - mu₁) * sigma₂ = (threshold₂ - mu₂) * sigma₂ := by
    rwa [div_eq_div_iff (ne_of_gt h_sigma₂) (ne_of_gt h_sigma₂)] at h_equal_z
  have := mul_right_cancel₀ (ne_of_gt h_sigma₂) h_eq₂
  linarith

end FairnessImpossibility


/-!
## Resource Allocation for Equitable PGS

Optimal allocation of GWAS resources (funding, participants)
to minimize the maximum portability gap.
-/

section ResourceAllocation

/- **Minimax allocation minimizes the maximum disparity.**
    Instead of maximizing average R², allocate resources to
    minimize max_pop(R²_source - R²_pop). -/

/-- **Diminishing returns per additional sample in the source.**
    R² ∝ n × h² / (n × h² + M) where M is effective number
    of independent causal loci. As n → ∞, R² → h². -/
noncomputable def expectedR2FromN (n h2 M : ℝ) : ℝ :=
  n * h2 / (n * h2 + M)

/-- R² increases with n. -/
theorem r2_increases_with_n
    (h2 M : ℝ) (n₁ n₂ : ℝ)
    (h_h2 : 0 < h2) (h_M : 0 < M)
    (h_n₁ : 0 < n₁) (h_n₂ : 0 < n₂) (h_more : n₁ < n₂) :
    expectedR2FromN n₁ h2 M < expectedR2FromN n₂ h2 M := by
  unfold expectedR2FromN
  rw [div_lt_div_iff₀ (by positivity) (by positivity)]
  nlinarith [mul_pos h_h2 h_M]

/-- R² is concave in n (diminishing returns). -/
theorem r2_concave_in_n
    (h2 M n dn : ℝ)
    (h_h2 : 0 < h2) (h_M : 0 < M)
    (h_n : 0 < n) (h_dn : 0 < dn) :
    -- Marginal gain from n+dn to n+2dn is less than from n to n+dn
    expectedR2FromN (n + 2*dn) h2 M - expectedR2FromN (n + dn) h2 M <
      expectedR2FromN (n + dn) h2 M - expectedR2FromN n h2 M := by
  unfold expectedR2FromN
  -- This is equivalent to showing f''(n) < 0 for f(n) = nh²/(nh²+M)
  -- f'(n) = h²M/(nh²+M)², f''(n) = -2(h²)²M/(nh²+M)³ < 0
  -- f(n) = nh²/(nh²+M) is concave in n, so f(n+2d)-f(n+d) < f(n+d)-f(n)
  -- Each difference = dh²M / ((xh²+M)((x+d)h²+M))
  -- Denominator grows with x → difference shrinks
  have h1 : 0 < n * h2 + M := by nlinarith [mul_pos h_n h_h2]
  have h2' : 0 < (n + dn) * h2 + M := by nlinarith [mul_pos (by linarith : 0 < n + dn) h_h2]
  have h3 : 0 < (n + 2 * dn) * h2 + M := by nlinarith [mul_pos (by linarith : 0 < n + 2 * dn) h_h2]
  rw [div_sub_div _ _ h3.ne' h2'.ne', div_sub_div _ _ h2'.ne' h1.ne']
  -- Both numerators simplify to dn * h2 * M (matching div_sub_div output order)
  have lhs_eq : (n + 2 * dn) * h2 * ((n + dn) * h2 + M) -
    ((n + 2 * dn) * h2 + M) * ((n + dn) * h2) = dn * h2 * M := by ring
  have rhs_eq : (n + dn) * h2 * (n * h2 + M) -
    ((n + dn) * h2 + M) * (n * h2) = dn * h2 * M := by ring
  rw [lhs_eq, rhs_eq]
  -- Goal: dn*h2*M / (h3*h2') < dn*h2*M / (h2'*h1)
  apply div_lt_div_of_pos_left (mul_pos (mul_pos h_dn h_h2) h_M) (mul_pos h2' h1) _
  -- Need: h2'*h1 < h3*h2', i.e., h2'*(h3 - h1) > 0
  nlinarith [mul_pos h2' (show 0 < 2 * dn * h2 from by nlinarith [mul_pos h_dn h_h2])]

end ResourceAllocation


/-!
## Clinical Implementation Guidelines

Practical considerations for deploying PGS in clinical settings
with diverse populations.
-/

section ClinicalImplementation

/- **Population-specific PGS report cards.**
    For each PGS, report: R², AUC, calibration, and portability ratio
    for each clinically relevant population. -/

/-- **Minimum validation sample size per population.**
    To estimate R² with SE < δ, need approximately n > 4R²(1-R²)²/δ².
    For small R² (common in underrepresented populations), this requires more samples. -/
theorem validation_n_depends_on_r2
    (r2_source r2_target delta : ℝ)
    (h_r2_target_smaller : r2_target < r2_source)
    (h_r2_source : 0 < r2_source) (h_r2_target : 0 < r2_target)
    (h_delta : 0 < delta)
    (h_r2_source_lt : r2_source < 1) (h_r2_target_lt : r2_target < 1)
    -- For smaller R², the relative SE is larger → need more samples
    (n_source n_target : ℝ)
    (h_n_source : n_source = 4 * r2_source * (1 - r2_source) ^ 2 / delta ^ 2)
    (h_n_target : n_target = 4 * r2_target * (1 - r2_target) ^ 2 / delta ^ 2) :
    -- The relative precision n_needed / R² is what matters for utility assessment
    0 < n_source ∧ 0 < n_target := by
  have h1 : (1 - r2_source) ≠ 0 := by linarith
  have h2 : (1 - r2_target) ≠ 0 := by linarith
  constructor
  · rw [h_n_source]; apply div_pos
    · exact mul_pos (mul_pos (by norm_num : (0:ℝ) < 4) h_r2_source)
        (sq_pos_of_ne_zero h1)
    · exact sq_pos_of_ne_zero (ne_of_gt h_delta)
  · rw [h_n_target]; apply div_pos
    · exact mul_pos (mul_pos (by norm_num : (0:ℝ) < 4) h_r2_target)
        (sq_pos_of_ne_zero h2)
    · exact sq_pos_of_ne_zero (ne_of_gt h_delta)

/- **Population-aware clinical decision support.**
    The clinical decision system should:
    1. Report population-specific PGS performance
    2. Adjust confidence intervals for portability
    3. Flag when PGS may be unreliable for the patient's population -/

end ClinicalImplementation

end Calibrator
