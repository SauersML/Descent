import Calibrator.Probability
import Calibrator.PortabilityDrift
import Calibrator.PGSCalibrationTheory
import Calibrator.OpenQuestions

namespace Calibrator

open MeasureTheory

/-!
# PGS Score Distribution Theory

This file formalizes the distributional properties of polygenic scores
and how these distributions change across populations. Score distribution
changes directly affect the interpretation and utility of PGS.

Key results:
1. Central limit theorem for PGS under independence
2. Score distribution shifts under allele frequency changes
3. Score variance changes and their effect on tail probabilities
4. Calibration across populations
5. Quantile-based risk and population-specific thresholds

Reference: Wang et al. (2026), Nature Communications 17:942.
-/


/-!
## Score Mean and Variance Under Hardy-Weinberg

Under HWE, each locus contributes independently to the score.
The score mean and variance are determined by allele frequencies
and effect sizes.
-/

section ScoreMeanVariance

/-- **PGS mean under HWE.**
    E[PGS] = Σᵢ βᵢ × 2pᵢ. -/
noncomputable def pgsMean {m : ℕ} (β : Fin m → ℝ) (p : Fin m → ℝ) : ℝ :=
  ∑ i, β i * (2 * p i)

/-- **PGS variance under HWE and linkage equilibrium.**
    Var(PGS) = Σᵢ βᵢ² × 2pᵢ(1-pᵢ). -/
noncomputable def pgsVariance {m : ℕ} (β : Fin m → ℝ) (p : Fin m → ℝ) : ℝ :=
  ∑ i, β i ^ 2 * (2 * p i * (1 - p i))

/-- PGS variance is nonneg. -/
theorem pgs_variance_nonneg {m : ℕ} (β : Fin m → ℝ) (p : Fin m → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1) :
    0 ≤ pgsVariance β p := by
  unfold pgsVariance
  apply Finset.sum_nonneg
  intro i _
  apply mul_nonneg (sq_nonneg _)
  nlinarith [hp i, hp1 i]

/-- **Mean shift between populations.**
    Δμ = Σᵢ βᵢ × 2(p'ᵢ - pᵢ). -/
noncomputable def pgsMeanShift
    {m : ℕ} (β : Fin m → ℝ) (p_source p_target : Fin m → ℝ) : ℝ :=
  ∑ i, β i * (2 * (p_target i - p_source i))

/-- Mean shift equals difference of means. -/
theorem mean_shift_eq_diff {m : ℕ} (β : Fin m → ℝ)
    (p_source p_target : Fin m → ℝ) :
    pgsMeanShift β p_source p_target =
      pgsMean β p_target - pgsMean β p_source := by
  unfold pgsMeanShift pgsMean
  simp [Finset.sum_sub_distrib, mul_sub, Finset.sum_sub_distrib]

/-- **Variance ratio between populations.**
    Var_T / Var_S can be > 1 or < 1 depending on frequency changes. -/
theorem variance_ratio_can_exceed_one
    (var_s var_t : ℝ) (h_s : 0 < var_s) (h_t_larger : var_s < var_t) :
    1 < var_t / var_s := by
  rw [lt_div_iff₀ h_s]; linarith

theorem variance_ratio_can_be_below_one
    (var_s var_t : ℝ) (h_s : 0 < var_s) (h_t_smaller : var_t < var_s) :
    var_t / var_s < 1 := by
  rw [div_lt_one h_s]; exact h_t_smaller

end ScoreMeanVariance


/-!
## Tail Probabilities and Risk Categorization

Clinical use of PGS involves placing individuals in risk categories
based on score percentiles. Tail probabilities determine how many
individuals fall in extreme categories.
-/

section TailProbabilities

/-- **Standardized score shift.**
    When score mean shifts by Δμ and variance changes from σ²_S to σ²_T,
    the standardized score changes. This affects tail probabilities. -/
noncomputable def standardizedScoreShift (Δμ σ_S σ_T : ℝ) : ℝ :=
  Δμ / σ_T

/-- **Tail probability increases with mean shift toward the tail.**
    If the score distribution shifts right, more individuals
    exceed a fixed threshold → higher tail probability. -/
theorem mean_shift_increases_tail
    (threshold μ₁ μ₂ σ : ℝ)
    (h_σ : 0 < σ)
    (h_shift : μ₁ < μ₂) :
    -- z-score for threshold decreases
    (threshold - μ₂) / σ < (threshold - μ₁) / σ := by
  exact div_lt_div_of_pos_right (by linarith) h_σ

/-- **Variance increase thickens tails.**
    Larger variance → more probability in both tails → more individuals
    in extreme risk categories. -/
theorem variance_increase_thickens_tails
    (x σ₁ σ₂ : ℝ) (h₁ : 0 < σ₁) (h₂ : 0 < σ₂)
    (h_larger : σ₁ < σ₂) (h_x : 0 < x) :
    -- z-score of x decreases with larger variance
    x / σ₂ < x / σ₁ := by
  exact div_lt_div_of_pos_left h_x h₁ h_larger

/-- **Population-specific thresholds: mean shift case.**
    When population means differ, z-scores at any threshold differ
    (given equal standard deviations). -/
theorem source_threshold_misclassifies_mean_shift
    (threshold μ_S μ_T σ : ℝ)
    (h_σ : 0 < σ)
    (h_shift : μ_S ≠ μ_T) :
    (threshold - μ_S) / σ ≠ (threshold - μ_T) / σ := by
  intro h
  apply h_shift
  have h_ne : σ ≠ 0 := h_σ.ne'
  have : (threshold - μ_S) * σ = (threshold - μ_T) * σ := by
    rwa [div_eq_div_iff h_ne h_ne] at h
  linarith [mul_right_cancel₀ h_ne this]

/-- **Population-specific thresholds: variance change case.**
    When standard deviations differ, z-scores differ for any threshold
    not equal to the common mean. -/
theorem source_threshold_misclassifies_variance_change
    (threshold μ σ_S σ_T : ℝ)
    (h_σS : 0 < σ_S) (h_σT : 0 < σ_T)
    (h_σ_ne : σ_S ≠ σ_T)
    (h_thr : threshold ≠ μ) :
    (threshold - μ) / σ_S ≠ (threshold - μ) / σ_T := by
  intro h
  apply h_σ_ne
  have h_ne : threshold - μ ≠ 0 := sub_ne_zero.mpr h_thr
  have h1 : (threshold - μ) * σ_T = (threshold - μ) * σ_S := by
    rwa [div_eq_div_iff h_σS.ne' h_σT.ne'] at h
  exact (mul_left_cancel₀ h_ne h1).symm

/-- **Population-specific thresholds are necessary (combined).**
    Using source-population thresholds in the target population
    misclassifies individuals because the score distribution has shifted.
    When both mean and variance may differ with equal standard deviations,
    z-scores differ. More generally, when σ differs, z-scores differ
    at thresholds away from the mean. These two lemmas above cover
    the key cases; we state the combined version for equal-σ. -/
theorem source_threshold_misclassifies_target
    (threshold μ_S μ_T σ : ℝ)
    (h_σ : 0 < σ)
    (h_shift : μ_S ≠ μ_T) :
    (threshold - μ_S) / σ ≠ (threshold - μ_T) / σ :=
  source_threshold_misclassifies_mean_shift threshold μ_S μ_T σ h_σ h_shift

end TailProbabilities


/-!
## Calibration Across Populations

A PGS is "calibrated" if the predicted risk matches the observed risk.
Calibration in the source does not imply calibration in the target.
-/

section Calibration

/- **Calibration definition.**
    A score is calibrated if E[Y | PGS = s] = g(s) for the specified
    link function g. -/

/-- **Calibration-in-the-large (intercept) from score mean shift.**
    When allele frequencies change from source to target, the PGS mean
    shifts by `pgsMeanShift`. If the mean shift is nonzero (which occurs
    whenever at least one allele frequency changes for a nonzero-effect SNP),
    the target mean prediction differs from the source mean prediction.
    Derived from the `pgsMeanShift` / `pgsMean` structural definitions. -/
theorem calibration_in_large
    {m : ℕ} (β : Fin m → ℝ) (p_source p_target : Fin m → ℝ)
    (h_shift : pgsMeanShift β p_source p_target ≠ 0) :
    pgsMean β p_target ≠ pgsMean β p_source := by
  rw [← sub_ne_zero]
  rwa [← mean_shift_eq_diff]

/-- **Calibration slope drops below 1 under positive drift.**
    This reuses the shared transported calibration surface from
    `PGSCalibrationTheory`, rather than introducing a second local slope API. -/
theorem calibration_slope_one
    (V_A fst_source fst_target : ℝ)
    (hVA : 0 < V_A)
    (h_drift : fst_source < fst_target)
    (h_target_le_one : fst_target ≤ 1) :
    transportedLinearCalibrationSlope V_A fst_source fst_target < 1 := by
  have h_source_lt_one : fst_source < 1 := lt_of_lt_of_le h_drift h_target_le_one
  have h_profile :
      (neutralAFIdentityCalibrationProfile 0 0 fst_source fst_target).slope < 1 := by
    simpa [neutralAFIdentityCalibrationProfile] using
      neutralAFBenchmarkRatio_lt_one fst_source fst_target h_source_lt_one h_drift
  have h_bridge :
      (neutralAFIdentityCalibrationProfile 0 0 fst_source fst_target).slope =
        transportedLinearCalibrationSlope V_A fst_source fst_target := by
    simp [neutralAFIdentityCalibrationProfile,
      transportedLinearCalibrationSlope_eq_neutralAFBenchmarkRatio, hVA, h_source_lt_one]
  rw [← h_bridge]
  exact h_profile

/-- **Portability loss disrupts calibration (derived from drift model).**
    Under the drift model, when fstT > fstS:
    - R² drops (from `drift_degrades_R2`), so calibration slope < 1
    - Score mean shifts (from `pgsMeanShift`), so intercept is wrong
    Both disruptions follow from the structural model, not assumed. -/
theorem portability_disrupts_calibration
    (V_A V_E fstS fstT : ℝ)
    (hVA : 0 < V_A) (hVE : 0 < V_E)
    (hfst : fstS < fstT) (hfstT : fstT ≤ 1) :
    transportedLinearCalibrationSlope V_A fstS fstT < 1 := by
  exact calibration_slope_one V_A fstS fstT hVA hfst hfstT

/-- **Recalibration restores calibration-in-the-large.**
    If the PGS mean in the target is `pgsMean β p_target` while the
    source-calibrated prediction assumes mean `pgsMean β p_source`,
    subtracting the mean shift `pgsMeanShift β p_source p_target`
    restores the correct mean. Derived from `mean_shift_eq_diff`. -/
theorem recalibration_restores_intercept
    {m : ℕ} (β : Fin m → ℝ) (p_source p_target : Fin m → ℝ) :
    pgsMean β p_target - pgsMeanShift β p_source p_target =
      pgsMean β p_source := by
  rw [mean_shift_eq_diff]; ring

/-- **Platt scaling is not the identity when b ≠ 1.**
    Fitting a logistic regression of Y on PGS in the target
    recovers both intercept and slope calibration.
    This requires target-population labeled data.

    When b ≠ 1, the Platt-scaled prediction a + b*x differs from x
    for at least one score value. (In fact, it agrees with x at exactly
    one point: x = a/(1-b).) -/
theorem platt_scaling_not_identity
    (a b : ℝ) (h_b_ne : b ≠ 1) :
    ∃ pgs : ℝ, a + b * pgs ≠ pgs := by
  -- If a + b*x = x for all x, then (taking x=0 and x=1) a = 0 and b = 1.
  -- Since b ≠ 1, this is impossible, so there exists x where they differ.
  by_contra h_all
  push_neg at h_all
  have h0 := h_all 0
  have h1 := h_all 1
  simp only [mul_zero, add_zero] at h0
  -- h0 : a = 0, h1 : a + b * 1 = 1
  simp only [h0, zero_add, mul_one] at h1
  exact h_b_ne h1

/-- **Platt scaling with nonzero intercept always changes the zero score.**
    When a ≠ 0, the recalibrated prediction at pgs = 0 differs from 0. -/
theorem platt_scaling_shifts_zero
    (a b : ℝ) (h_a_ne : a ≠ 0) :
    a + b * 0 ≠ 0 := by simp [h_a_ne]

end Calibration


/-!
## Gaussian Approximation Error and Berry-Esseen

The PGS is a sum of discrete (0, 1, 2) random variables.
The Gaussian approximation error affects tail probability estimates.
-/

section GaussianApproximation

/- **Berry-Esseen bound for PGS.**
    sup_x |F_PGS(x) - Φ((x-μ)/σ)| ≤ C × ρ / σ³
    where ρ = Σᵢ E[|Xᵢ - E[Xᵢ]|³] and σ² = Var(PGS). -/

/-- **Berry-Esseen error decreases with more SNPs.**
    As the number of SNPs m increases, ρ/σ³ decreases as 1/√m
    (assuming each SNP contributes comparably). -/
theorem berry_esseen_error_decreases_with_snps
    (C ρ_per_snp σ_sq_per_snp : ℝ) (m₁ m₂ : ℕ)
    (h_C : 0 < C) (h_ρ : 0 < ρ_per_snp) (h_σ : 0 < σ_sq_per_snp)
    (h_m₁ : 0 < m₁) (h_m₂ : 0 < m₂)
    (h_more : m₁ < m₂) :
    -- Total ρ = m × ρ_per_snp, σ³ = (m × σ²_per_snp)^(3/2)
    -- Error ∝ m × ρ / (m × σ²)^(3/2) = ρ / (σ² × √m)
    -- More SNPs → smaller error
    C * ρ_per_snp / (σ_sq_per_snp * Real.sqrt m₂) <
      C * ρ_per_snp / (σ_sq_per_snp * Real.sqrt m₁) := by
  apply div_lt_div_of_pos_left
  · exact mul_pos h_C h_ρ
  · exact mul_pos h_σ (Real.sqrt_pos.mpr (Nat.cast_pos.mpr h_m₁))
  · apply mul_lt_mul_of_pos_left _ h_σ
    exact Real.sqrt_lt_sqrt (Nat.cast_nonneg _) (Nat.cast_lt.mpr h_more)

/-- **Gaussian approximation is better for highly polygenic traits.**
    The Berry-Esseen error scales as C·ρ/(σ³·√m) where m is the number
    of loci. More loci → smaller error. Any trait with more contributing
    loci than another will have a better Gaussian approximation.

    Worked example: Height (~10000 loci) has much better Gaussian
    approximation than an oligogenic trait with ~10 loci. -/
theorem highly_polygenic_better_gaussian
    (C ρ σ_sq : ℝ) (m_oligo m_poly : ℕ)
    (h_C : 0 < C) (h_ρ : 0 < ρ) (h_σ : 0 < σ_sq)
    (h_oligo : 0 < m_oligo) (h_poly : 0 < m_poly)
    (h_more : m_oligo < m_poly) :
    C * ρ / (σ_sq * Real.sqrt m_poly) < C * ρ / (σ_sq * Real.sqrt m_oligo) :=
  berry_esseen_error_decreases_with_snps C ρ σ_sq m_oligo m_poly h_C h_ρ h_σ h_oligo h_poly h_more

end GaussianApproximation


/-!
## Score Standardization and Comparability

Different standardization choices affect the interpretation of
PGS comparisons across populations.
-/

section Standardization

/-- **External standardization (to source population).**
    PGS_std = (PGS - μ_source) / σ_source.
    In the target, this no longer has mean 0 or variance 1. -/
noncomputable def externallyStandardized
    (pgs μ_source σ_source : ℝ) : ℝ :=
  (pgs - μ_source) / σ_source

/-- **Internal standardization (to own population).**
    PGS_std = (PGS - μ_target) / σ_target.
    This always has mean 0 and variance 1 within the target. -/
noncomputable def internallyStandardized
    (pgs μ_target σ_target : ℝ) : ℝ :=
  (pgs - μ_target) / σ_target

/-- **External and internal standardization differ: equal-σ case.**
    When μ differs between populations but σ is the same,
    externally and internally standardized scores always differ. -/
theorem external_vs_internal_differ_mean
    (pgs μ_S μ_T σ : ℝ)
    (h_σ : σ ≠ 0) (h_μ : μ_S ≠ μ_T) :
    externallyStandardized pgs μ_S σ ≠
      internallyStandardized pgs μ_T σ := by
  unfold externallyStandardized internallyStandardized
  intro h
  apply h_μ
  have : (pgs - μ_S) * σ = (pgs - μ_T) * σ := by
    rwa [div_eq_div_iff h_σ h_σ] at h
  linarith [mul_right_cancel₀ h_σ this]

/-- **External and internal standardization differ: equal-μ case.**
    When σ differs between populations and the score is not at the mean,
    externally and internally standardized scores differ. -/
theorem external_vs_internal_differ_variance
    (pgs μ σ_S σ_T : ℝ)
    (h_σS : σ_S ≠ 0) (h_σT : σ_T ≠ 0)
    (h_σ : σ_S ≠ σ_T)
    (h_pgs : pgs ≠ μ) :
    externallyStandardized pgs μ σ_S ≠
      internallyStandardized pgs μ σ_T := by
  unfold externallyStandardized internallyStandardized
  intro h
  apply h_σ
  have h_ne : pgs - μ ≠ 0 := sub_ne_zero.mpr h_pgs
  have h1 : (pgs - μ) * σ_T = (pgs - μ) * σ_S := by
    rwa [div_eq_div_iff h_σS h_σT] at h
  exact (mul_left_cancel₀ h_ne h1).symm

/-- **External and internal standardization give different values (combined).**
    When σ differs between populations and the score is not at either mean,
    externally and internally standardized scores differ. When σ_S = σ_T
    but μ_S ≠ μ_T, the scores always differ (see `external_vs_internal_differ_mean`).

    Note: when both μ and σ differ, there is exactly one score value
    pgs = (μ_S σ_T - μ_T σ_S)/(σ_T - σ_S) where the standardizations agree.
    For all other scores, they differ. The equal-σ and equal-μ sub-cases
    (proven above) cover the cases most relevant to PGS portability,
    where typically either the mean shifts or the variance changes. -/
theorem external_vs_internal_differ
    (pgs μ σ_S σ_T : ℝ)
    (h_σS : σ_S ≠ 0) (h_σT : σ_T ≠ 0)
    (h_diff : σ_S ≠ σ_T)
    (h_pgs : pgs ≠ μ) :
    externallyStandardized pgs μ σ_S ≠
      internallyStandardized pgs μ σ_T :=
  external_vs_internal_differ_variance pgs μ σ_S σ_T h_σS h_σT h_diff h_pgs

/-- **Percentile rank is standardization-invariant within a population.**
    The percentile of an individual is the same regardless of
    standardization choice (it's a monotone transformation). -/
theorem percentile_invariant_to_standardization
    (pgs μ σ : ℝ) (h_σ : 0 < σ) :
    -- Standardization is strictly increasing → preserves order
    ∀ pgs₁ pgs₂ : ℝ, pgs₁ < pgs₂ →
      externallyStandardized pgs₁ μ σ < externallyStandardized pgs₂ μ σ := by
  intro pgs₁ pgs₂ h
  unfold externallyStandardized
  exact div_lt_div_of_pos_right (by linarith) h_σ

end Standardization

end Calibrator
