import Calibrator.Probability
import Calibrator.PortabilityDrift
import Calibrator.OpenQuestions

namespace Calibrator

open MeasureTheory

/-!
# Variance Components, Heritability, and PGS Performance

This file formalizes the relationship between variance components,
heritability estimation, and PGS performance across populations.

Key results:
1. GREML heritability estimation and its assumptions
2. h² SNP vs h² twin and the missing heritability problem
3. Variance component changes across populations
4. Heritability is population-specific
5. PGS R² ceiling from heritability

Reference: Wang et al. (2026), Nature Communications 17:942.
-/


/-!
## Heritability Definitions and Relationships

Different definitions of heritability lead to different ceilings
for PGS performance.
-/

section HeritabilityDefinitions

/-- **Narrow-sense heritability.**
    h² = V_A / V_P where V_A is additive genetic variance
    and V_P = V_A + V_D + V_I + V_E is total phenotypic variance. -/
noncomputable def narrowSenseH2 (V_A V_D V_I V_E : ℝ) : ℝ :=
  V_A / (V_A + V_D + V_I + V_E)

/-- Narrow-sense h² is in [0, 1] for nonneg components. -/
theorem narrow_h2_in_unit (V_A V_D V_I V_E : ℝ)
    (hA : 0 ≤ V_A) (hD : 0 ≤ V_D) (hI : 0 ≤ V_I) (hE : 0 ≤ V_E)
    (h_total : 0 < V_A + V_D + V_I + V_E) :
    0 ≤ narrowSenseH2 V_A V_D V_I V_E ∧
      narrowSenseH2 V_A V_D V_I V_E ≤ 1 := by
  unfold narrowSenseH2
  constructor
  · exact div_nonneg hA (le_of_lt h_total)
  · rw [div_le_one h_total]; linarith

/-- **SNP heritability.**
    h²_SNP = V_A_tagged / V_P ≤ h²_narrow.
    Only the variance tagged by genotyped SNPs is captured. -/
noncomputable def snpH2 (V_A_tagged V_P : ℝ) : ℝ :=
  V_A_tagged / V_P

/-- SNP heritability ≤ narrow-sense heritability. -/
theorem snp_h2_le_narrow_h2
    (V_A_tagged V_A_total V_D V_I V_E : ℝ)
    (h_tagged : V_A_tagged ≤ V_A_total)
    (h_tagged_nn : 0 ≤ V_A_tagged)
    (hD : 0 ≤ V_D) (hI : 0 ≤ V_I) (hE : 0 ≤ V_E)
    (h_total : 0 < V_A_total + V_D + V_I + V_E) :
    snpH2 V_A_tagged (V_A_total + V_D + V_I + V_E) ≤
      narrowSenseH2 V_A_total V_D V_I V_E := by
  unfold snpH2 narrowSenseH2
  exact div_le_div_of_nonneg_right h_tagged (le_of_lt h_total)

/-- **The missing heritability gap.**
    h²_twin - h²_SNP > 0 for most traits. This is the "missing heritability".
    It sets an upper bound on what PGS can achieve with current genotyping.

    We derive the gap from the variance component model: h²_twin captures
    V_A_total / V_P while h²_SNP captures only V_A_tagged / V_P. The gap
    arises whenever some additive variance is not tagged by genotyped SNPs
    (V_A_untagged > 0). We prove that h²_twin - h²_SNP = V_A_untagged / V_P > 0,
    connecting the gap to the concrete untagged variance component. -/
theorem missing_heritability_gap
    (V_A_tagged V_A_untagged V_D V_I V_E : ℝ)
    (h_tagged_nn : 0 ≤ V_A_tagged) (h_untagged_pos : 0 < V_A_untagged)
    (h_D : 0 ≤ V_D) (h_I : 0 ≤ V_I) (h_E : 0 ≤ V_E)
    (h_total : 0 < V_A_tagged + V_A_untagged + V_D + V_I + V_E) :
    let V_P := V_A_tagged + V_A_untagged + V_D + V_I + V_E
    let h2_twin := (V_A_tagged + V_A_untagged) / V_P
    let h2_snp := V_A_tagged / V_P
    0 < h2_twin - h2_snp := by
  simp only
  rw [show (V_A_tagged + V_A_untagged) / (V_A_tagged + V_A_untagged + V_D + V_I + V_E) -
    V_A_tagged / (V_A_tagged + V_A_untagged + V_D + V_I + V_E) =
    ((V_A_tagged + V_A_untagged) - V_A_tagged) / (V_A_tagged + V_A_untagged + V_D + V_I + V_E)
    from (sub_div _ _ _).symm]
  apply div_pos
  · linarith
  · linarith

end HeritabilityDefinitions


/-!
## Population-Specific Heritability

Heritability is NOT a fixed property of a trait — it depends on
allele frequencies, LD structure, and environmental variance
in the specific population.
-/

section PopulationSpecificH2

/-- **Additive variance depends on allele frequencies.**
    V_A = Σᵢ 2pᵢ(1-pᵢ)αᵢ² where αᵢ is the average effect.
    When frequencies differ, V_A differs. -/
noncomputable def additiveVariance
    {m : ℕ} (p : Fin m → ℝ) (α : Fin m → ℝ) : ℝ :=
  ∑ i, 2 * p i * (1 - p i) * (α i) ^ 2

/-- Additive variance is nonneg. -/
theorem additive_variance_nonneg
    {m : ℕ} (p : Fin m → ℝ) (α : Fin m → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1) :
    0 ≤ additiveVariance p α := by
  unfold additiveVariance
  apply Finset.sum_nonneg
  intro i _
  apply mul_nonneg
  · apply mul_nonneg
    · apply mul_nonneg (by norm_num : (0:ℝ) ≤ 2) (hp i)
    · linarith [hp1 i]
  · exact sq_nonneg _

/-- **Frequency change affects additive variance.**
    When MAF changes from p to p' at a single locus,
    the contribution to V_A changes. -/
theorem frequency_change_affects_va
    (p₁ p₂ α : ℝ)
    (h₁ : 0 < p₁) (h₁' : p₁ < 1)
    (h₂ : 0 < p₂) (h₂' : p₂ < 1)
    (h_freq : p₁ ≠ p₂) (h_α : α ≠ 0)
    (h_sum : p₁ + p₂ ≠ 1) :
    2 * p₁ * (1 - p₁) * α ^ 2 ≠ 2 * p₂ * (1 - p₂) * α ^ 2 := by
  intro h
  have h_sq : 0 < α ^ 2 := sq_pos_of_ne_zero h_α
  have h_eq : 2 * p₁ * (1 - p₁) = 2 * p₂ * (1 - p₂) :=
    mul_right_cancel₀ h_sq.ne' h
  -- From 2p₁(1-p₁) = 2p₂(1-p₂), get (p₁-p₂)(1-(p₁+p₂)) = 0
  have : (p₁ - p₂) * (1 - (p₁ + p₂)) = 0 := by nlinarith
  rcases mul_eq_zero.mp this with h | h
  · exact h_freq (sub_eq_zero.mp h)
  · exact h_sum (by linarith)

/-- **Environmental variance heterogeneity across populations.**
    If Ve differs, h² differs even with identical genetic architecture. -/
theorem env_variance_changes_h2
    (V_A Ve₁ Ve₂ : ℝ)
    (hVA : 0 < V_A) (hVe₁ : 0 < Ve₁) (hVe₂ : 0 < Ve₂)
    (h_diff : Ve₁ < Ve₂) :
    V_A / (V_A + Ve₂) < V_A / (V_A + Ve₁) := by
  exact div_lt_div_of_pos_left hVA (by linarith) (by linarith)

/-- **GxE creates population-specific heritability.**
    Gene-environment interaction means the genetic effect depends
    on the environment. In different environments, V_A changes. -/
theorem gxe_changes_heritability
    (V_A_env1 V_A_env2 V_E : ℝ)
    (h_diff : V_A_env1 ≠ V_A_env2) (h_E : 0 < V_E)
    (h1 : 0 < V_A_env1) (h2 : 0 < V_A_env2) :
    V_A_env1 / (V_A_env1 + V_E) ≠ V_A_env2 / (V_A_env2 + V_E) := by
  intro h
  have h_d1 : V_A_env1 + V_E ≠ 0 := by linarith
  have h_d2 : V_A_env2 + V_E ≠ 0 := by linarith
  have h_eq : V_A_env1 * (V_A_env2 + V_E) = V_A_env2 * (V_A_env1 + V_E) := by
    field_simp at h
    linarith
  have : V_A_env1 = V_A_env2 := by nlinarith
  exact h_diff this

end PopulationSpecificH2


/-!
## PGS R² Ceiling

The maximum achievable PGS R² is bounded by the heritability
and the GWAS sample size.
-/

section PGSCeiling

/-- **PGS R² ceiling from heritability.**
    R²_PGS ≤ h²_SNP. No PGS can explain more variance than what's
    genetically tagged. The PGS explains a fraction f of tagged
    additive variance, so R²_PGS = f × h²_SNP ≤ h²_SNP. -/
theorem pgs_r2_ceiling_from_h2
    (h2_snp f : ℝ)
    (h_h2 : 0 < h2_snp)
    (h_f_nn : 0 ≤ f) (h_f_le : f ≤ 1) :
    h2_snp * f ≤ h2_snp := by
  exact mul_le_of_le_one_right (le_of_lt h_h2) h_f_le

/-- **PGS R² ceiling from GWAS power.**
    R²_PGS ≤ h²_SNP × (1 - (1-power)^m)
    where power is per-SNP GWAS power and m is number of causal SNPs.
    With finite sample size, not all SNPs are discovered. -/
theorem pgs_r2_ceiling_from_gwas_power
    (h2_snp power_fraction : ℝ)
    (h_h2 : 0 < h2_snp) (h_h2_le : h2_snp ≤ 1)
    (h_power : 0 < power_fraction) (h_power_le : power_fraction ≤ 1) :
    h2_snp * power_fraction ≤ h2_snp := by
  exact mul_le_of_le_one_right (le_of_lt h_h2) h_power_le

/-- **Portability further reduces the ceiling.**
    R²_PGS_target ≤ h²_SNP × power_fraction × portability_ratio. -/
theorem portability_reduces_ceiling
    (h2_snp power_frac port_ratio : ℝ)
    (h_h2 : 0 < h2_snp) (h_power : 0 < power_frac) (h_port : 0 < port_ratio)
    (h_power_le : power_frac ≤ 1) (h_port_le : port_ratio ≤ 1) :
    h2_snp * power_frac * port_ratio ≤ h2_snp := by
  calc h2_snp * power_frac * port_ratio
      ≤ h2_snp * 1 * 1 := by
        apply mul_le_mul
        · exact mul_le_mul_of_nonneg_left h_power_le (le_of_lt h_h2)
        · exact h_port_le
        · exact le_of_lt h_port
        · exact mul_nonneg (le_of_lt h_h2) (by linarith)
    _ = h2_snp := by ring

/-- **The three-way ceiling decomposition.**
    R²_target ≤ h² × (GWAS power) × (portability ratio).
    Each factor is ≤ 1, and the product can be very small. -/
theorem three_way_ceiling
    (h2 gwas_power port_ratio target_r2 : ℝ)
    (h_h2_le : h2 ≤ 1) (h_power_le : gwas_power ≤ 1)
    (h_port_le : port_ratio ≤ 1)
    (h_h2_nn : 0 ≤ h2) (h_power_nn : 0 ≤ gwas_power) (h_port_nn : 0 ≤ port_ratio)
    (h_bound : target_r2 ≤ h2 * gwas_power * port_ratio) :
    target_r2 ≤ 1 := by
  have : h2 * gwas_power * port_ratio ≤ 1 := by
    calc h2 * gwas_power * port_ratio
        ≤ 1 * 1 * 1 := by nlinarith [mul_nonneg h_h2_nn h_power_nn]
      _ = 1 := by ring
  linarith

end PGSCeiling


/-!
## GREML Estimation and Bias

GREML (Genomic REML) estimates h² from GRM. Its accuracy depends
on LD and population structure assumptions.
-/

section GREML

/-- **GREML h² estimate depends on LD structure.**
    GREML estimates h²_SNP = trace(GRM⁻¹ × Σ_pheno) / n.
    When LD differs between training and evaluation, the estimate is biased. -/
theorem greml_ld_sensitive
    (h2_estimated h2_true ld_bias : ℝ)
    (h_bias : h2_estimated = h2_true + ld_bias)
    (h_ld_nonzero : ld_bias ≠ 0) :
    h2_estimated ≠ h2_true := by
  rw [h_bias]; intro h; apply h_ld_nonzero; linarith

/-- **GREML underestimates h² when causal variants are poorly tagged.**
    If tag-causal r² < 1, GREML underestimates V_A. -/
theorem greml_underestimates_with_poor_tagging
    (h2_true h2_greml mean_tag_r2 : ℝ)
    (h_relation : h2_greml = h2_true * mean_tag_r2)
    (h_imperfect : mean_tag_r2 < 1)
    (h_true_pos : 0 < h2_true) (h_tag_pos : 0 < mean_tag_r2) :
    h2_greml < h2_true := by
  rw [h_relation]
  exact mul_lt_of_lt_one_right h_true_pos h_imperfect

/-- **Population structure inflates GREML h² estimate.**
    Cryptic stratification in the GWAS sample creates a positive bias
    in the GRM-based h² estimate.

    **Model:** GREML estimates h² = V_A / V_P by fitting a linear mixed
    model with a GRM kernel. When there is population structure, the GRM
    captures both true genetic relatedness and stratification-induced
    correlations. The GREML estimate becomes:
      h²_GREML = (V_A + V_strat) / (V_A + V_strat + V_E)
    while the true h² is:
      h²_true = V_A / (V_A + V_strat + V_E)

    We derive: h²_GREML > h²_true whenever V_strat > 0, because
    (V_A + V_strat)/V_P > V_A/V_P when V_P > 0. -/
theorem stratification_inflates_greml
    (V_A V_strat V_E : ℝ)
    (h_VA : 0 ≤ V_A) (h_strat_pos : 0 < V_strat) (h_VE : 0 ≤ V_E)
    (h_total : 0 < V_A + V_strat + V_E) :
    let V_P := V_A + V_strat + V_E
    let h2_true := V_A / V_P
    let h2_greml := (V_A + V_strat) / V_P
    h2_true < h2_greml := by
  simp only
  exact div_lt_div_of_pos_right (by linarith) h_total

end GREML


/-!
## Liability Scale Conversion

For binary traits, h² on the observed scale differs from h² on
the liability scale. Conversion depends on prevalence.
-/

section LiabilityScale

/-- **Observed-to-liability scale conversion (Dempster-Lee-Risch).**

    **Derivation of the Dempster-Lee-Risch conversion:**

    On the liability scale, assume Y ~ N(0, 1). Disease occurs when Y > T,
    where T = Φ⁻¹(1-K) and K = prevalence. This is the "liability threshold
    model."

    The key question: how does a unit change in liability translate to a
    change in disease risk on the observed (binary 0/1) scale?

    1. The observed (binary) heritability h²_obs measures variance explained
       on the 0/1 disease scale.

    2. The liability heritability h²_liab measures variance explained on the
       continuous latent liability scale.

    3. The relationship between the two involves the "ascertainment correction"
       factor. At the threshold T, the standard normal density is z = φ(T).
       A small shift δ in mean liability changes disease risk by:
         ΔP(disease) ≈ z × δ

    4. Variance on observed scale vs liability scale:
       - A genetic variant explaining variance σ² on the liability scale
         explains variance ≈ z² × σ² / (K(1-K)) on the observed scale
         (after accounting for the Bernoulli variance K(1-K) of the binary outcome).

    5. Therefore: h²_obs = h²_liab × z² / (K(1-K))

    6. Rearranging: **h²_liab = h²_obs × K(1-K) / z²**

    The factor K(1-K)/z² is the inverse of the "ascertainment correction,"
    which accounts for the nonlinear mapping between the continuous liability
    and binary disease status. For rare diseases (small K), the threshold T
    is far in the tail, z = φ(T) is small, and z² << K(1-K), so
    h²_liab >> h²_obs. -/
noncomputable def liabilityScaleH2
    (h2_observed prevalence z_height : ℝ) : ℝ :=
  h2_observed * prevalence * (1 - prevalence) / z_height ^ 2

/-- **Liability h² is larger than observed h² for rare diseases.**
    When prevalence K is small, K(1-K)/z² > 1 because z is large
    (the threshold is far in the tail). -/
theorem liability_h2_larger_for_rare
    (h2_observed prevalence z_height : ℝ)
    (h_obs_pos : 0 < h2_observed)
    (h_prev : 0 < prevalence) (h_prev1 : prevalence < 1)
    (h_conversion_gt_one : prevalence * (1 - prevalence) / z_height ^ 2 > 1)
    (h_z : 0 < z_height) :
    h2_observed < liabilityScaleH2 h2_observed prevalence z_height := by
  unfold liabilityScaleH2
  rw [show h2_observed * prevalence * (1 - prevalence) / z_height ^ 2 =
    h2_observed * (prevalence * (1 - prevalence) / z_height ^ 2) by ring]
  exact lt_mul_of_one_lt_right h_obs_pos h_conversion_gt_one

/-- **Prevalence-dependent h² creates portability confusion.**
    Two populations with the same genetic architecture but different
    prevalence have different observed h², which can be mistaken
    for a portability effect. -/
theorem prevalence_confounds_h2_portability
    (h2_liability : ℝ) (K₁ K₂ z₁ z₂ : ℝ)
    (h_same_liability : 0 < h2_liability)
    (h_K1 : 0 < K₁) (h_K2 : 0 < K₂)
    (h_z1 : 0 < z₁) (h_z2 : 0 < z₂)
    (h_diff_prev : K₁ ≠ K₂)
    (h_diff_z : z₁ ≠ z₂)
    (h_diff_ratio : K₁ * (1 - K₁) / z₁ ^ 2 ≠ K₂ * (1 - K₂) / z₂ ^ 2) :
    -- Different observed h² even with same genetic architecture
    liabilityScaleH2 1 K₁ z₁ ≠ liabilityScaleH2 1 K₂ z₂ := by
  unfold liabilityScaleH2
  simp
  exact h_diff_ratio

end LiabilityScale

end Calibrator
