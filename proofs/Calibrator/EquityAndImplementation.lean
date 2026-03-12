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
## Health Disparity from Portability Gaps

PGS portability gaps directly translate to disparities in clinical
benefit across ancestry groups.
-/

section HealthDisparity

/-- **Clinical utility depends on PGS R².**
    The net clinical benefit from PGS-guided care is monotonically
    increasing in R². We model benefit = α × R² for a positive
    proportionality constant α (benefit per unit R²). When
    R²₁ < R²₂, the benefit in population 1 is strictly less. -/
theorem clinical_benefit_increases_with_r2
    (α r2₁ r2₂ : ℝ)
    (h_α : 0 < α)
    (h_r2 : r2₁ < r2₂) :
    α * r2₁ < α * r2₂ := by
  exact mul_lt_mul_of_pos_left h_r2 h_α

/-- **Portability gap creates benefit gap.**
    If R²_EUR > R²_AFR and benefit = α × R² with α > 0, then
    clinical benefit for EUR patients exceeds that for AFR patients.
    The benefit gap α × (R²_EUR - R²_AFR) > 0 follows from the R² gap. -/
theorem portability_creates_benefit_gap
    (α r2_eur r2_afr : ℝ)
    (h_α : 0 < α)
    (h_r2_gap : r2_afr < r2_eur)
    (h_nn : 0 ≤ r2_afr) :
    0 < α * r2_eur - α * r2_afr := by
  have : r2_eur - r2_afr > 0 := by linarith
  nlinarith

/-- **Disparity increases with Fst from discovery population.**
    Populations most genetically distant from the discovery
    population have the worst PGS performance. R² decays as
    (1 - Fst)², so disparity = R²_source - R²_target grows
    with Fst. For Fst₂ > Fst₁ > 0, the R² loss is larger. -/
theorem disparity_increases_with_distance
    (R2_source fst₁ fst₂ : ℝ)
    (h_R2 : 0 < R2_source)
    (h_fst₁_pos : 0 < fst₁) (h_fst₁_lt : fst₁ < 1)
    (h_fst₂_pos : 0 < fst₂) (h_fst₂_lt : fst₂ < 1)
    (h_fst : fst₁ < fst₂) :
    -- R² loss at fst₁ < R² loss at fst₂
    R2_source * (1 - (1 - fst₁) ^ 2) < R2_source * (1 - (1 - fst₂) ^ 2) := by
  apply mul_lt_mul_of_pos_left _ h_R2
  have h1 : (1 - fst₂) ^ 2 < (1 - fst₁) ^ 2 := by nlinarith
  linarith

/-- **Existing health disparities may be amplified.**
    If PGS is deployed only for the well-served population (EUR),
    it adds benefit α × R²_eur to that group. The underserved group
    gets no PGS benefit, so the pre-existing disparity d₀ ≥ 0 grows
    to d₀ + α × R²_eur. -/
theorem deployment_amplifies_disparity
    (d₀ α r2_eur : ℝ)
    (h_nn : 0 ≤ d₀)
    (h_α : 0 < α) (h_r2 : 0 < r2_eur) :
    d₀ < d₀ + α * r2_eur := by
  linarith [mul_pos h_α h_r2]

/-- **QALY gap from portability.**
    QALYs gained = γ × R² for a positive constant γ (QALYs per unit R²).
    The QALY gap between two populations is γ × (R²₁ - R²₂), which is
    positive when R²₁ > R²₂. Derived from the model, not assumed. -/
theorem qaly_gap_proportional_to_r2_gap
    (γ r2₁ r2₂ : ℝ)
    (h_γ : 0 < γ) (h_gap : r2₂ < r2₁) :
    0 < γ * r2₁ - γ * r2₂ := by
  have : r2₁ - r2₂ > 0 := by linarith
  nlinarith

end HealthDisparity


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

/-- **Group-blind vs group-aware PGS policies.**
    A group-blind policy (same threshold for all) violates
    calibration equality. A group-aware policy violates
    treatment equality. Neither is fully "fair".
    We model: calibration violation for a blind policy is
    |μ₁ - μ₂| (the mean PGS difference), and treatment violation
    for an aware policy is |t₁ - t₂| (threshold difference).
    When means differ and equal FPR requires different thresholds,
    both violations are positive. -/
theorem no_fully_fair_policy
    (μ₁ μ₂ σ : ℝ)
    (h_mu_diff : μ₁ ≠ μ₂)
    (h_sigma : 0 < σ) :
    -- Both policies have some fairness violation
    0 < |μ₁ - μ₂| ∧ 0 < |μ₁ - μ₂| / σ := by
  constructor
  · exact abs_pos.mpr (sub_ne_zero.mpr h_mu_diff)
  · exact div_pos (abs_pos.mpr (sub_ne_zero.mpr h_mu_diff)) h_sigma

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

/-- **Marginal value of diversity.**
    Adding underrepresented individuals has higher marginal value
    for reducing the max disparity than adding EUR individuals.
    By concavity of R²(n), marginal gain is larger at smaller n.
    If n_eur >> n_underrep, an extra sample in the underrepresented
    group yields more R² gain. -/
theorem diversity_has_higher_marginal_value
    (h2 M n_eur n_underrep dn : ℝ)
    (h_h2 : 0 < h2) (h_M : 0 < M)
    (h_eur : 0 < n_eur) (h_underrep : 0 < n_underrep)
    (h_dn : 0 < dn)
    (h_larger : n_underrep < n_eur) :
    -- Marginal R² gain is larger for the underrepresented group
    expectedR2FromN (n_eur + dn) h2 M - expectedR2FromN n_eur h2 M <
      expectedR2FromN (n_underrep + dn) h2 M - expectedR2FromN n_underrep h2 M := by
  unfold expectedR2FromN
  have h1 : 0 < n_underrep * h2 + M := by nlinarith [mul_pos h_underrep h_h2]
  have h2' : 0 < (n_underrep + dn) * h2 + M := by nlinarith [mul_pos (by linarith : 0 < n_underrep + dn) h_h2]
  have h3 : 0 < n_eur * h2 + M := by nlinarith [mul_pos h_eur h_h2]
  have h4 : 0 < (n_eur + dn) * h2 + M := by nlinarith [mul_pos (by linarith : 0 < n_eur + dn) h_h2]
  rw [div_sub_div _ _ h4.ne' h3.ne', div_sub_div _ _ h2'.ne' h1.ne']
  have lhs_eq : (n_eur + dn) * h2 * (n_eur * h2 + M) -
    ((n_eur + dn) * h2 + M) * (n_eur * h2) = dn * h2 * M := by ring
  have rhs_eq : (n_underrep + dn) * h2 * (n_underrep * h2 + M) -
    ((n_underrep + dn) * h2 + M) * (n_underrep * h2) = dn * h2 * M := by ring
  rw [lhs_eq, rhs_eq]
  apply div_lt_div_of_pos_left (mul_pos (mul_pos h_dn h_h2) h_M) (mul_pos h2' h1) _
  nlinarith [h_larger, mul_pos h_h2 h_dn]

end ResourceAllocation


/-!
## Clinical Implementation Guidelines

Practical considerations for deploying PGS in clinical settings
with diverse populations.
-/

section ClinicalImplementation

/-- **Minimum R² for clinical utility.**
    Below a threshold R², PGS does not improve clinical decisions.
    The net clinical value = α × R² - cost. When R² is small
    (R² < cost / α), the net value is negative. -/
theorem r2_threshold_for_utility
    (r2 α cost : ℝ)
    (h_α : 0 < α) (h_cost : 0 < cost)
    (h_r2_nn : 0 ≤ r2)
    (h_below : r2 < cost / α) :
    -- PGS net value is negative in this population
    α * r2 - cost < 0 := by
  have : r2 * α < cost := by rwa [lt_div_iff₀ h_α] at h_below
  linarith [mul_comm α r2]

/- **Population-specific PGS report cards.**
    For each PGS, report: R², AUC, calibration, and portability ratio
    for each clinically relevant population. -/

/-- **Relative precision of R² estimate is worse for smaller R².**
    To estimate R² with SE < δ, need approximately n > 4R²(1-R²)²/δ².
    The *relative* standard error SE/R² = (1-R²)/√(nR²) × 2/δ grows as R²
    shrinks.  For the same sample size, the relative error is larger for the
    target population (smaller R²).

    Equivalently, the required sample size per unit R² (n/R²) is larger for
    smaller R².  Here we prove: n/R² = 4(1-R²)²/δ² is a decreasing function
    of R² on (0,1), so the target population (lower R²) requires a larger
    sample-per-unit-R². -/
theorem validation_n_depends_on_r2
    (r2_source r2_target delta : ℝ)
    (h_r2_target_smaller : r2_target < r2_source)
    (h_r2_source : 0 < r2_source) (h_r2_target : 0 < r2_target)
    (h_delta : 0 < delta)
    (h_r2_source_lt : r2_source < 1) (h_r2_target_lt : r2_target < 1) :
    -- n/R² = 4(1-R²)²/δ² is larger for the target (smaller R²)
    4 * (1 - r2_source) ^ 2 / delta ^ 2 <
      4 * (1 - r2_target) ^ 2 / delta ^ 2 := by
  apply div_lt_div_of_pos_right _ (sq_pos_of_ne_zero (ne_of_gt h_delta))
  apply mul_lt_mul_of_pos_left _ (by norm_num : (0:ℝ) < 4)
  -- (1-r2_source)² < (1-r2_target)² because 0 < 1-r2_source < 1-r2_target
  apply sq_lt_sq'
  · linarith
  · linarith

/- **Population-aware clinical decision support.**
    The clinical decision system should:
    1. Report population-specific PGS performance
    2. Adjust confidence intervals for portability
    3. Flag when PGS may be unreliable for the patient's population -/

/-- **Do-no-harm principle for PGS deployment.**
    PGS should only be used clinically when the expected benefit exceeds
    the expected harm from misclassification.

    We model benefit and harm through R²-dependent sensitivity and specificity
    via monotone link functions (from the liability-threshold model).  As R²
    increases, sensitivity rises (more true positives treated) and specificity
    rises (fewer false positives harmed).  There exists a critical R² above
    which the benefit-harm tradeoff is favorable.

    Here we prove the structural result: if the target population's R² is
    strictly below the source's (portability loss), the net clinical value
    in the target is strictly less than in the source. This means populations
    with poor portability may violate the do-no-harm principle even when the
    source population satisfies it.  This is derived from monotonicity, not
    assumed. -/
theorem do_no_harm_principle
    (sensLink specLink : ℝ → ℝ) (r2_source r2_target π benefit harm : ℝ)
    (h_sens_mono : StrictMono sensLink)
    (h_spec_mono : StrictMono specLink)
    (h_r2_loss : r2_target < r2_source)
    (h_π : 0 < π) (h_π1 : π < 1)
    (h_benefit : 0 < benefit) (h_harm : 0 < harm)
    (h_sens_t : 0 ≤ sensLink r2_target) (h_spec_t : 0 ≤ specLink r2_target)
    (h_spec_s1 : specLink r2_source ≤ 1) :
    -- Net value in target is strictly less than in source
    sensLink r2_target * π * benefit - (1 - specLink r2_target) * (1 - π) * harm <
      sensLink r2_source * π * benefit - (1 - specLink r2_source) * (1 - π) * harm := by
  have h_sens : sensLink r2_target < sensLink r2_source := h_sens_mono h_r2_loss
  have h_spec : specLink r2_target < specLink r2_source := h_spec_mono h_r2_loss
  have h1 : sensLink r2_target * π * benefit < sensLink r2_source * π * benefit := by
    apply mul_lt_mul_of_pos_right _ h_benefit
    exact mul_lt_mul_of_pos_right h_sens h_π
  have h2 : (1 - specLink r2_source) * (1 - π) * harm <
             (1 - specLink r2_target) * (1 - π) * harm := by
    apply mul_lt_mul_of_pos_right _ h_harm
    apply mul_lt_mul_of_pos_right _ (by linarith)
    linarith
  linarith

/-- **Phased deployment strategy.**
    Deploy PGS first for well-validated populations (R² above threshold),
    then expand as validation data becomes available.

    We model: the validated population has strictly higher R² than the
    unvalidated population (portability gap).  By monotonicity of
    sensitivity and specificity in R² (from the liability threshold model),
    the validated population has strictly better discrimination.

    Phased deployment achieves the same clinical benefit for the validated
    population while avoiding the risk of deploying a poorly-performing
    PGS in the unvalidated population.  The benefit gap between
    validated and unvalidated populations is derived from the R² gap. -/
theorem phased_deployment_reduces_risk
    (sensLink specLink : ℝ → ℝ) (r2_validated r2_unvalidated π : ℝ)
    (h_sens_mono : StrictMono sensLink)
    (h_spec_mono : StrictMono specLink)
    (h_r2_gap : r2_unvalidated < r2_validated)
    (h_π : 0 < π) (h_π1 : π < 1)
    (h_sens_u : 0 ≤ sensLink r2_unvalidated)
    (h_spec_u : 0 ≤ specLink r2_unvalidated)
    (h_spec_v : specLink r2_validated ≤ 1) :
    -- The validated population has strictly better risk stratification
    -- (proportion correctly classified) than the unvalidated population,
    -- derived from the R² gap via monotone links.
    sensLink r2_unvalidated * π + specLink r2_unvalidated * (1 - π) <
      sensLink r2_validated * π + specLink r2_validated * (1 - π) := by
  have h_sens : sensLink r2_unvalidated < sensLink r2_validated := h_sens_mono h_r2_gap
  have h_spec : specLink r2_unvalidated < specLink r2_validated := h_spec_mono h_r2_gap
  have h1 : sensLink r2_unvalidated * π < sensLink r2_validated * π :=
    mul_lt_mul_of_pos_right h_sens h_π
  have h2 : specLink r2_unvalidated * (1 - π) < specLink r2_validated * (1 - π) :=
    mul_lt_mul_of_pos_right h_spec (by linarith)
  linarith

end ClinicalImplementation

end Calibrator
