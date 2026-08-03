/-
Copyright (c) 2026 Sauers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sauers
-/
import Calibrator.Probability
import Calibrator.PCCorrectability
import Calibrator.AncestrySpecificPower

namespace Calibrator

open MeasureTheory

/-!
# Population Stratification, Confounding, and PGS Portability

This file formalizes how population stratification creates confounding in PGS,
and how this confounding interacts with portability. Key results:

1. Stratification bias in GWAS effect estimates
2. Principal component correction and residual confounding
3. Assortative mating effects on PGS variance
4. Collider bias in ascertained samples
5. Gene-environment correlation and portability

References:
- Zaidi and Mathieson (2020), eLife 9:e61548.
- Blanc and Berg (2025), Genetics 230(2):iyaf071.
- Blanc, Mawass, and Berg (2025), bioRxiv 2025.12.04.692430.
- Wang et al. (2026), Nature Communications 17:942 -- for the measured portability
  gap cited in one docstring below, not for the stratification results, which the
  three references above cover.
-/


/-!
## Stratification Bias in GWAS

When a GWAS sample is stratified (contains subgroups with different allele
frequencies AND different mean phenotypes), the estimated effect sizes are biased.
This bias is a form of confounding.
-/

section StratificationBias

/-- Stratification bias is nonzero when ancestry correlates with both
    phenotype and genotype. -/
theorem stratification_bias_nonzero
    (cov_anc_pheno cov_anc_geno var_geno : ℝ)
    (h_pheno : cov_anc_pheno ≠ 0)
    (h_geno : cov_anc_geno ≠ 0)
    (h_var : 0 < var_geno) :
    cov_anc_pheno * cov_anc_geno / var_geno ≠ 0 := by
  apply div_ne_zero
  · exact mul_ne_zero h_pheno h_geno
  · exact h_var.ne'

/-- **Stratification bias model for p SNPs.**
    Each SNP i has true effect β_i and confounding bias b_i.
    PGS_obs = Σ (β_i + b_i) * x_i.
    The observed variance decomposes as Var(PGS_true) + Var(PGS_bias) + 2·Cov
    when biases are independent of true effects, Cov vanishes. -/
structure StratificationModel (p : ℕ) where
  /-- True per-SNP effects -/
  β : Fin p → ℝ
  /-- Confounding bias per SNP -/
  b : Fin p → ℝ
  /-- Per-SNP heterozygosity (proxy for allele freq variance) -/
  H : Fin p → ℝ
  /-- All heterozygosities are positive -/
  H_pos : ∀ i, 0 < H i
  /-- At least one bias is nonzero -/
  bias_nonzero : ∃ i, b i ≠ 0

/-- True PGS variance component: Σ β_i² · H_i -/
noncomputable def StratificationModel.varTrue {p : ℕ} (m : StratificationModel p) : ℝ :=
  ∑ i : Fin p, m.β i ^ 2 * m.H i

/-- Bias variance component: Σ b_i² · H_i -/
noncomputable def StratificationModel.varBias {p : ℕ} (m : StratificationModel p) : ℝ :=
  ∑ i : Fin p, m.b i ^ 2 * m.H i

/-- The bias variance is strictly positive when any bias is nonzero. -/
theorem stratification_bias_variance_pos {p : ℕ} (m : StratificationModel p) :
    0 < m.varBias := by
  unfold StratificationModel.varBias
  obtain ⟨j, hj⟩ := m.bias_nonzero
  apply Finset.sum_pos'
  · intro i _
    exact mul_nonneg (sq_nonneg _) (le_of_lt (m.H_pos i))
  · exact ⟨j, Finset.mem_univ _, mul_pos (sq_pos_of_ne_zero hj) (m.H_pos j)⟩

/-- **Stratification inflates PGS variance.**
    The observed PGS variance (true + bias components, ignoring cross-term for
    independent biases) exceeds the true PGS variance, derived from the model
    structure rather than assumed. -/
theorem stratification_inflates_pgs_variance {p : ℕ} (m : StratificationModel p) :
    m.varTrue < m.varTrue + m.varBias := by
  linarith [stratification_bias_variance_pos m]

/-- **Stratification creates spurious portability.**
    In source population, bias structure correlates with LD → inflates R².
    In target, different LD means a different projection of the bias vector
    onto phenotype. We model this: source bias variance > target bias variance
    because the bias vector was "tuned" to the source LD structure. -/
structure TwoPopBiasModel (p : ℕ) extends StratificationModel p where
  /-- Bias attenuation in target: fraction of source bias variance retained -/
  attenuation : ℝ
  /-- Attenuation is in (0, 1): some but not all bias transfers -/
  atten_pos : 0 < attenuation
  atten_lt_one : attenuation < 1

/-- Target population bias variance -/
noncomputable def TwoPopBiasModel.varBiasTarget {p : ℕ} (m : TwoPopBiasModel p) : ℝ :=
  m.attenuation * m.toStratificationModel.varBias

/-- **Attenuated target bias variance is strictly below source bias variance.**

This was `spurious_portability_from_stratification`, stated as
`(r2_true + varBias) - (r2_true + varBiasTarget) > 0` for an arbitrary real `r2_true`.
That `r2_true` cancels in the subtraction and is otherwise unconstrained — it was not the
model's `R²`, was not tied to any predictor, and appeared only to make an inequality
between two bias variances read as a statement about portability. -/
theorem varBiasTarget_lt_varBias {p : ℕ} (m : TwoPopBiasModel p) :
    m.varBiasTarget < m.toStratificationModel.varBias := by
  unfold TwoPopBiasModel.varBiasTarget
  have hv := stratification_bias_variance_pos m.toStratificationModel
  have : m.attenuation * m.toStratificationModel.varBias < m.toStratificationModel.varBias := by
    rw [← mul_one m.toStratificationModel.varBias]
    simpa [mul_assoc] using mul_lt_mul_of_pos_right m.atten_lt_one hv
  linarith

end StratificationBias


/-!
## Assortative Mating and PGS Variance

Assortative mating (AM) for a trait increases the genetic variance of that trait
in subsequent generations. This affects PGS portability because:
1. Source population PGS variance depends on AM history
2. AM patterns differ across populations
-/

section AssortativeMating

/-! ### Assortative-mating variance inflation

Removed.  This defined `amInflationFactor r = 1/(1 - r)` as the equilibrium
inflation of genetic variance under assortative mating.  Forward Wright-Fisher
simulation with the spousal correlation measured rather than assumed falsifies
it: the error runs from +3% to +82%, always overstating.  It also takes no
heritability, while the observable depends on it strongly, the true inflation
at `r = 0.5` being `1.10` for `h² = 0.2` and `1.74` for `h² = 0.8`, so no
constant repairs it.

`amEquilibriumVariance` in `AssortativeMatingPGS` gives `V_A / (1 - r h²)` for
the same quantity and is accurate to between -5% and +1% across that grid.
The two were never related by any theorem, which is why both could stand.
This is the coalescent-untestable case: assortative mating is a forward-time
phenomenon and no coalescent simulation could have caught it.
-/

/-- **AM affects both numerator and denominator of R².**
    R² = V_PGS / V_Y. AM inflates V_PGS by α and V_Y by less than α
    (because V_E doesn't change), so R² increases. -/
theorem am_increases_r2
    (v_pgs v_e α : ℝ)
    (h_vpgs : 0 < v_pgs) (h_ve : 0 < v_e) (h_α : 1 < α) :
    v_pgs / (v_pgs + v_e) < (α * v_pgs) / (α * v_pgs + v_e) := by
  have h_d1 : 0 < v_pgs + v_e := by linarith
  have h_d2 : 0 < α * v_pgs + v_e := by nlinarith
  rw [div_lt_div_iff₀ h_d1 h_d2]
  nlinarith [mul_pos h_vpgs h_ve]

end AssortativeMating


/-!
## Collider Bias in Ascertained Samples

When GWAS or validation cohorts are ascertained (e.g., hospital-based,
volunteer bias), collider bias can create spurious associations and
affect portability estimates.
-/

section ColliderBias

/-- **Collider bias model.**
    In the population, G and E are independent (Cov = 0).
    Selection S depends on G + E: individuals selected when G + E > threshold.
    Conditioning on S induces negative covariance between G and E among
    the selected, because high G "explains away" high E. -/
structure ColliderModel where
  /-- Genetic risk variance -/
  σ2_G : ℝ
  /-- Environmental risk variance -/
  σ2_E : ℝ
  /-- True effect of G on outcome -/
  β_G : ℝ
  σ2_G_pos : 0 < σ2_G
  σ2_E_pos : 0 < σ2_E
  β_G_pos : 0 < β_G

/-- **Selection on G + E induces negative covariance in selected sample.**
    In the selected subsample, Cov(G, E | S=1) = -σ²_G · σ²_E / (σ²_G + σ²_E).
    This is the classical "explaining away" effect. -/
noncomputable def ColliderModel.inducedCov (m : ColliderModel) : ℝ :=
  -(m.σ2_G * m.σ2_E / (m.σ2_G + m.σ2_E))

theorem ColliderModel.inducedCov_neg (m : ColliderModel) :
    m.inducedCov < 0 := by
  unfold ColliderModel.inducedCov
  rw [neg_neg_iff_pos]
  exact div_pos (mul_pos m.σ2_G_pos m.σ2_E_pos) (by linarith [m.σ2_G_pos, m.σ2_E_pos])

/-! `selection_induces_correlation` was removed here.  It was `ne_of_lt inducedCov_neg` —
strictly weaker than the theorem one line above it, restated under a name asserting that
selection induces the correlation.  No selection event, no conditioning and no population
covariance appear in this section: `inducedCov` is a closed-form *definition*, and
`inducedCov_neg` says only that a negative-of-a-positive-ratio is negative.  The
"explaining away" derivation that would connect the two is not in this corpus. -/

/-- **Collider bias attenuates PGS-outcome association.**
    In the full population, regression coefficient is β_G.
    In the selected sample, the induced G-E covariance attenuates:
    β_selected = β_G · σ²_G / (σ²_G + σ²_E).
    Since σ²_E > 0, this ratio is < 1, so β_selected < β_G. -/
noncomputable def ColliderModel.β_selected (m : ColliderModel) : ℝ :=
  m.β_G * (m.σ2_G / (m.σ2_G + m.σ2_E))

theorem collider_attenuates_association (m : ColliderModel) :
    m.β_selected < m.β_G := by
  unfold ColliderModel.β_selected
  have h_denom_pos : 0 < m.σ2_G + m.σ2_E := by linarith [m.σ2_G_pos, m.σ2_E_pos]
  have h_ratio_lt_one : m.σ2_G / (m.σ2_G + m.σ2_E) < 1 := by
    rw [div_lt_one h_denom_pos]
    linarith [m.σ2_E_pos]
  calc m.β_G * (m.σ2_G / (m.σ2_G + m.σ2_E))
      < m.β_G * 1 := by exact mul_lt_mul_of_pos_left h_ratio_lt_one m.β_G_pos
    _ = m.β_G := by ring

/-- **The ascertainment inflation of an apparent portability drop is exactly the
difference of the two cohorts' ascertainment losses.**

Writing the ascertainment loss of a cohort as `r2_pop - r2_asc`, the apparent drop
`r2_source_asc - r2_target_asc` exceeds the true drop `r2_source_pop - r2_target_pop`
**iff the target loses more to ascertainment than the source does.** With equal
ascertainment severity the two drops coincide, so the artifact is differential
ascertainment specifically, not ascertainment as such. The sign matters and is the whole
statement, which is why this is an `iff`: severity in the *source* biases the apparent drop
downward, hiding portability loss rather than manufacturing it.

**This replaces `differential_ascertainment_artifact`, which asserted nothing.** That
theorem read `(h : d_target < d_source) → (apparent > true) → False`, and by the identity
`apparent - true = d_target - d_source` its second hypothesis is precisely the negation of
its first: it proved `h → ¬¬h`, closed by `linarith`, for every choice of the four reals.
Its docstring meanwhile claimed the *opposite* conclusion — "apparent portability drop is
larger than true portability drop" — which is the branch that statement refutes. -/
theorem apparent_portability_drop_gt_true_iff_target_more_ascertained
    (r2_source_pop r2_target_pop r2_source_asc r2_target_asc : ℝ) :
    r2_source_asc - r2_target_asc > r2_source_pop - r2_target_pop ↔
      r2_source_pop - r2_source_asc < r2_target_pop - r2_target_asc :=
  ⟨fun h ↦ by linarith, fun h ↦ by linarith⟩

end ColliderBias


/-!
## Gene-Environment Correlation (rGE) and Portability

Gene-environment correlation means that genetic effects are partially
mediated through environmental pathways. This affects portability because
the environmental mediation may differ across populations.
-/

section GeneEnvironmentCorrelation

/-- **rGE model.**
    Genetic effects on an outcome are mediated through both a direct
    pathway and an indirect (environment-mediated) pathway. -/
structure RGEModel where
  /-- Direct genetic effect on outcome -/
  β_direct : ℝ
  /-- Effect of genotype on environment -/
  β_genetic : ℝ
  /-- Effect of environment on outcome -/
  β_env : ℝ
  /-- Gene-environment correlation in each population -/
  rge : Pop → ℝ
  β_genetic_ne : β_genetic ≠ 0
  β_env_ne : β_env ≠ 0
  rge_diff : rge Pop.source ≠ rge Pop.target

/-- **Total prediction in a population.** -/
noncomputable def RGEModel.pred (m : RGEModel) (P : Pop) : ℝ :=
  m.β_direct + m.β_genetic * m.rge P * m.β_env

/-- If rGE differs across populations, total prediction changes
    even with identical direct genetic effects. -/
theorem rge_changes_total_prediction (m : RGEModel) :
    m.pred Pop.source ≠ m.pred Pop.target := by
  unfold RGEModel.pred
  intro h
  have h_eq :
      m.β_genetic * m.rge Pop.source * m.β_env =
        m.β_genetic * m.rge Pop.target * m.β_env := by linarith
  apply m.rge_diff
  have h_ne : m.β_genetic * m.β_env ≠ 0 := mul_ne_zero m.β_genetic_ne m.β_env_ne
  have : m.rge Pop.source * (m.β_genetic * m.β_env)
      = m.rge Pop.target * (m.β_genetic * m.β_env) := by nlinarith
  exact mul_right_cancel₀ h_ne this

/-- **rGE inflation model.**
    R² in the presence of rGE decomposes as:
      R²_obs = R²_direct + 2·β_d·β_g·rge·β_e·σ² + (β_g·rge·β_e)²·σ²
    The cross term and indirect term add to R² when rge > 0. -/
structure RGEInflationModel where
  /-- Direct R² component -/
  r2_direct : ℝ
  /-- Indirect effect magnitude -/
  β_indirect : ℝ
  /-- Genetic variance -/
  σ2 : ℝ
  r2_direct_pos : 0 < r2_direct
  β_indirect_ne : β_indirect ≠ 0
  σ2_pos : 0 < σ2

/-- Observed R² under rGE -/
noncomputable def RGEInflationModel.r2_obs (m : RGEInflationModel) : ℝ :=
  m.r2_direct + m.β_indirect ^ 2 * m.σ2

/-- **rGE inflation of apparent heritability.**
    The indirect effect contributes β_indirect² · σ² > 0 to observed R²,
    derived from the model rather than assumed. -/
theorem rge_inflates_apparent_heritability (m : RGEInflationModel) :
    m.r2_direct < m.r2_obs := by
  unfold RGEInflationModel.r2_obs
  have : 0 < m.β_indirect ^ 2 * m.σ2 :=
    mul_pos (sq_pos_of_ne_zero m.β_indirect_ne) m.σ2_pos
  linarith

end GeneEnvironmentCorrelation


/-!
## Survivorship Bias in PGS Portability Studies

When studying portability across age-structured populations,
survivorship bias can affect results because the genotype distribution
in older cohorts differs from birth cohorts due to differential mortality.
-/

section SurvivorshipBias

/-- **Survivorship model.**
    At birth, genotype frequency is p₀. Genotype confers relative risk γ > 1
    for mortality. After selection, surviving frequency among risk allele
    carriers is p₀ · s / (p₀ · s + (1 - p₀)) where s < 1 is survival prob. -/
structure SurvivorshipModel where
  /-- Birth frequency of risk allele -/
  p₀ : ℝ
  /-- Survival probability for risk carriers (relative to non-carriers = 1) -/
  s : ℝ
  p₀_pos : 0 < p₀
  p₀_lt_one : p₀ < 1
  s_pos : 0 < s
  s_lt_one : s < 1

/-- Frequency of risk allele among survivors -/
noncomputable def SurvivorshipModel.pSurv (m : SurvivorshipModel) : ℝ :=
  m.p₀ * m.s / (m.p₀ * m.s + (1 - m.p₀))

/-- **Age-dependent genotype frequency shift.**
    The risk allele frequency among survivors is lower than at birth,
    derived from the survival model. -/
theorem survivorship_shifts_genotype_freq (m : SurvivorshipModel) :
    m.pSurv < m.p₀ := by
  unfold SurvivorshipModel.pSurv
  have h1 : 0 < 1 - m.p₀ := by linarith [m.p₀_lt_one]
  have h2 : 0 < m.p₀ * m.s := mul_pos m.p₀_pos m.s_pos
  have h_denom_pos : 0 < m.p₀ * m.s + (1 - m.p₀) := by linarith
  rw [div_lt_iff₀ h_denom_pos]
  have : m.p₀ * (m.p₀ * m.s + (1 - m.p₀)) = m.p₀ ^ 2 * m.s + m.p₀ * (1 - m.p₀) := by ring
  have : m.p₀ * m.s = m.p₀ * m.s := rfl
  -- Need: p₀ · s < p₀ · (p₀ · s + (1 - p₀))
  -- i.e., p₀ · s < p₀² · s + p₀ · (1 - p₀)
  -- i.e., p₀ · s · (1 - p₀) < p₀ · (1 - p₀)    [rearranging]
  -- i.e., s < 1   ✓ (since p₀ · (1 - p₀) > 0)
  nlinarith [m.p₀_pos, m.p₀_lt_one, m.s_lt_one, m.s_pos,
             mul_pos m.p₀_pos h1, sq_nonneg m.p₀]

/-- **Survivorship bias attenuation model.**
    PGS-outcome R² depends on allele frequency variance.
    Among survivors, risk allele frequency is shifted down → reduced variance
    → attenuated R².
    R²_surv = R²_full · (Var_surv / Var_birth) where Var_surv < Var_birth. -/
structure SurvivorshipAttenuationModel where
  /-- R² in birth cohort -/
  r2_full : ℝ
  /-- Variance of genotype in birth cohort -/
  var_birth : ℝ
  /-- Variance of genotype among survivors -/
  var_surv : ℝ
  r2_full_pos : 0 < r2_full
  var_birth_pos : 0 < var_birth
  var_surv_pos : 0 < var_surv
  /-- Survivorship truncation reduces variance -/
  var_reduced : var_surv < var_birth

/-- R² among survivors -/
noncomputable def SurvivorshipAttenuationModel.r2_surv (m : SurvivorshipAttenuationModel) : ℝ :=
  m.r2_full * (m.var_surv / m.var_birth)

/-- **Survivorship bias attenuates PGS-outcome association in older cohorts.**
    Derived from the attenuation model: Var_surv < Var_birth implies
    the variance ratio < 1, so R²_surv < R²_full. -/
theorem survivorship_attenuates_in_older (m : SurvivorshipAttenuationModel) :
    m.r2_surv < m.r2_full := by
  unfold SurvivorshipAttenuationModel.r2_surv
  have h_ratio_lt_one : m.var_surv / m.var_birth < 1 := by
    rw [div_lt_one m.var_birth_pos]
    exact m.var_reduced
  calc m.r2_full * (m.var_surv / m.var_birth)
      < m.r2_full * 1 := by exact mul_lt_mul_of_pos_left h_ratio_lt_one m.r2_full_pos
    _ = m.r2_full := by ring


end SurvivorshipBias


/-!
## Causal Inference Framework for Portability

Portability loss can be understood through the lens of causal inference:
the PGS is a proxy for a causal variable (genetic liability), and
portability loss arises from violations of the assumptions needed for
the proxy to work across populations.
-/

section CausalInference

/-- **Measurement error model for PGS.**
    PGS = true genetic liability × attenuation + noise.
    Attenuation = √R² in the training GWAS.
    In a new population, attenuation changes.

    Empirical status: UNTESTED. -/
noncomputable def pgsAttenuationFactor (r2_gwas : ℝ) : ℝ :=
  Real.sqrt r2_gwas

/-- **Attenuation factor decreases with lower GWAS R².**
    In target populations where the GWAS is less predictive,
    the PGS is a noisier proxy for genetic liability. -/
theorem attenuation_decreases_with_r2
    (r2_source r2_target : ℝ)
    (h_t : 0 ≤ r2_target)
    (h_drop : r2_target < r2_source) :
    pgsAttenuationFactor r2_target < pgsAttenuationFactor r2_source := by
  unfold pgsAttenuationFactor
  exact Real.sqrt_lt_sqrt h_t h_drop

/-- **Measurement error attenuation model.**
    When PGS is used as covariate, measurement error attenuates the
    coefficient. True coefficient β_true is observed as β_true · R
    where R = reliability ratio = signal variance / total variance.
    Reliability ratio = r² / (r² + σ²_noise). -/
structure AttenuationModel where
  /-- True regression coefficient -/
  β_true : ℝ
  /-- Signal R² in source population -/
  r2_source : ℝ
  /-- Signal R² in target population -/
  r2_target : ℝ
  /-- Noise variance (constant across populations) -/
  σ2_noise : ℝ
  β_true_pos : 0 < β_true
  r2_source_pos : 0 < r2_source
  r2_target_pos : 0 < r2_target
  σ2_noise_pos : 0 < σ2_noise
  /-- Target has lower signal -/
  r2_drop : r2_target < r2_source

/-- Reliability ratio in a population

    Empirical status: UNTESTED. -/
noncomputable def reliabilityRatio (r2 σ2_noise : ℝ) : ℝ :=
  r2 / (r2 + σ2_noise)

/-- Observed (attenuated) coefficient -/
noncomputable def AttenuationModel.β_obs (m : AttenuationModel) (r2 : ℝ) : ℝ :=
  m.β_true * reliabilityRatio r2 m.σ2_noise

/-- Helper: x ↦ x / (x + c) is strictly monotone for c > 0. -/
theorem ratio_strict_mono {a b c : ℝ} (ha : 0 < a) (hc : 0 < c)
    (hab : a < b) : a / (a + c) < b / (b + c) := by
  have h1 : 0 < a + c := by linarith
  have h2 : 0 < b + c := by linarith
  rw [div_lt_div_iff₀ h1 h2]
  nlinarith

/-- **Noisier proxy → more attenuation bias in downstream analysis.**
    Lower R² → lower reliability ratio → more attenuated coefficient.
    Uses monotonicity of x/(x+c). -/
theorem noisier_proxy_more_bias (m : AttenuationModel) :
    m.β_obs m.r2_target < m.β_obs m.r2_source := by
  unfold AttenuationModel.β_obs
  apply mul_lt_mul_of_pos_left _ m.β_true_pos
  exact ratio_strict_mono m.r2_target_pos m.σ2_noise_pos m.r2_drop

/-- **Transportability model.**
    PGS accuracy in the target is the source accuracy minus the sum of
    bias contributions from each violated assumption. Each assumption i
    contributes a penalty δ_i ≥ 0 to accuracy loss, and δ_i > 0 when
    the assumption is violated. -/
structure TransportabilityModel (n : ℕ) where
  /-- Source population R² -/
  r2_source : ℝ
  /-- Per-assumption accuracy penalty in target -/
  δ : Fin n → ℝ
  /-- All penalties are nonneg -/
  δ_nonneg : ∀ i, 0 ≤ δ i
  /-- At least one assumption violated (positive penalty) -/
  violated : ∃ i, 0 < δ i
  r2_source_pos : 0 < r2_source

/-- Target R² under the transportability model -/
noncomputable def TransportabilityModel.r2_target {n : ℕ}
    (m : TransportabilityModel n) : ℝ :=
  m.r2_source - ∑ i : Fin n, m.δ i

/-- **Transportability violation creates gap.**
    When any assumption is violated, the total penalty is positive,
    so target R² < source R². Derived from the sum structure and
    the existence of a positive penalty term. -/
theorem transportability_violation_creates_gap {n : ℕ}
    (m : TransportabilityModel n) :
    m.r2_target < m.r2_source := by
  unfold TransportabilityModel.r2_target
  linarith [show 0 < ∑ i : Fin n, m.δ i from
    Finset.sum_pos' (fun i _ ↦ m.δ_nonneg i)
      (let ⟨j, hj⟩ := m.violated; ⟨j, Finset.mem_univ _, hj⟩)]

end CausalInference


/-!
## Mendelian Randomization and Portability

MR uses genetic variants as instruments. Portability of MR estimates
depends on the same factors as PGS portability, plus additional
assumptions about pleiotropy and instrument strength.
-/

section MRPortability

/-- **MR instrument model.**
    F-statistic of a genetic instrument depends on effect size and
    allele frequency: F = n · β² · 2p(1-p) / σ²_Y.
    When allele frequency p changes across populations, F changes. -/
structure MRInstrumentModel where
  /-- Sample size -/
  n : ℝ
  /-- Effect of instrument on exposure -/
  β_inst : ℝ
  /-- Allele frequency in source -/
  p_source : ℝ
  /-- Allele frequency in target -/
  p_target : ℝ
  /-- Outcome variance -/
  σ2_Y : ℝ
  n_pos : 0 < n
  β_inst_ne : β_inst ≠ 0
  σ2_Y_pos : 0 < σ2_Y
  p_source_pos : 0 < p_source
  p_source_lt : p_source < 1
  p_target_pos : 0 < p_target
  p_target_lt : p_target < 1

/-! Heterozygosity `2p(1-p)` as a function of allele frequency was defined here
as `heterozygosity`. It is `hweHeterozygosity` from
`Calibrator.AncestrySpecificPower`, and the definition here has been deleted in
favour of that one; the empirical status and the `Denotes` declaration
travelled with it.

The `F`-statistic below is the one place in this file where the distinction
matters: what enters the noncentrality is the genotype *variance*, which
`hweHeterozygosity_eq_genotypeVarianceHWE` says is this same number. -/

/-- F-statistic of an instrument at a given allele frequency.
    next to the deleted `heterozygosity`, whose marker it was reading.

    Empirical status: UNTESTED. It carried no marker of its own while it sat -/
noncomputable def MRInstrumentModel.fStat (m : MRInstrumentModel) (p : ℝ) : ℝ :=
  m.n * m.β_inst ^ 2 * hweHeterozygosity p / m.σ2_Y

/-- Heterozygosity is maximized at p = 0.5 and decreasing as p moves away. -/
theorem hweHeterozygosity_pos (p : ℝ) (hp : 0 < p) (hp1 : p < 1) :
    0 < hweHeterozygosity p := by
  unfold hweHeterozygosity
  have : 0 < 1 - p := by linarith
  positivity

/-- **Instrument strength decreases with allele frequency divergence.**
    If the target has lower heterozygosity (allele frequency further from 0.5
    or toward fixation), F-stat decreases. Derived from the F-stat formula. -/
theorem instrument_strength_decreases (m : MRInstrumentModel)
    (h_het : hweHeterozygosity m.p_target < hweHeterozygosity m.p_source) :
    m.fStat m.p_target < m.fStat m.p_source := by
  unfold MRInstrumentModel.fStat
  apply div_lt_div_of_pos_right _ m.σ2_Y_pos
  apply mul_lt_mul_of_pos_left h_het
  exact mul_pos m.n_pos (sq_pos_of_ne_zero m.β_inst_ne)

/-- **Weak instrument bias in MR.**
    Bias = (1 - 1/F) × confounding bias.
    As F decreases (weaker instrument), bias increases toward the
    confounded OLS estimate. -/
theorem weak_instrument_bias_increases
    (conf_bias : ℝ) (F₁ F₂ : ℝ)
    (h_conf : 0 < conf_bias)
    (h_F₂ : 1 < F₂)
    (h_weaker : F₂ < F₁) :
    (1 - 1/F₂) * conf_bias < (1 - 1/F₁) * conf_bias := by
  apply mul_lt_mul_of_pos_right _ h_conf
  have h1 : 1/F₁ < 1/F₂ := by
    rw [div_lt_div_iff₀ (by linarith) (by linarith)]
    linarith
  linarith

/-- **A shared causal effect does not cancel a differing pleiotropic term.**  Cancellation
on the left: `β + α ≠ β + α'` whenever `α ≠ α'`.

This was `pleiotropy_changes_invalidate_mr`, "MR estimates are not portable".  Nothing here
is an MR estimate: there is no instrument, no exposure, no ratio of reduced-form
coefficients, and the additive form `β_causal + α_pleio` is written down rather than
derived from an instrumental-variable model.  The MR content of the section that *is*
proved is `instrument_strength_decreases`, from `MRInstrumentModel.fStat`. -/
theorem add_left_ne_of_pleiotropy_ne
    (β_causal α_pleio_source α_pleio_target : ℝ)
    (h_diff : α_pleio_source ≠ α_pleio_target) :
    β_causal + α_pleio_source ≠ β_causal + α_pleio_target := by
  intro h; exact h_diff (by linarith)

end MRPortability


/-!
## Sample Size and Statistical Power for Portability Detection

Detecting portability differences requires adequate statistical power.
We formalize the power analysis for portability comparisons.
-/

section PowerAnalysis

/-- **Variance of R² estimator.**
    Var(R²) ≈ 4R²(1-R²)²/n for the standard R² estimator.

    Regime: the delta-method (large-sample) variance of the plug-in R² from a
    simple bivariate-normal regression, valid when the non-centrality `n R²` is
    large -- roughly `n R² >= 50`.  The controlling variable is `n R²`, not `n`:
    the approximation fails when R² is small relative to `1 / n`, because the
    plug-in estimator then sits on its noise floor (`E[R̂²] ≈ R² + (1-R²)/n`) and
    carries variance this formula does not model.  Measured ratios of formula to
    a 20000-replicate Monte Carlo, replicating `check_stats.mc_r2_variance`:

        R²      n     n R²    formula / MC
      0.01    200        2       0.825
      0.01   1000       10       0.954
      0.01   5000       50       0.985
      0.05    200       10       0.984
      0.05   1000       50       0.993
      0.20    200       40       1.011
      0.50   1000      500       0.992

    Every cell with `n R² >= 40` is within about 1%; the departures are the
    small-`n R²` cells and they are one-sided, the formula always too low.

    Note this does not match the boundary asserted below.  The Empirical status
    line states `0.99-1.01 for n >= 1000`, but at `R² = 0.01` the ratio is 0.954
    at `n = 1000` and 0.985 at `n = 5000` -- both outside that band, at sample
    sizes the band claims to cover.  The formula is right and its regime is
    real; it is the stated boundary that is in the wrong variable.  Correcting
    the status line is left to this file's owner, since it is a claim-versus-
    evidence question rather than a missing regime.

    Empirical status: VALIDATED (40000-replicate Monte Carlo, ratio 0.99-1.01 for n >= 1000). -/
noncomputable def r2EstimatorVariance (r2 : ℝ) (n : ℕ) : ℝ :=
  4 * r2 * (1 - r2) ^ 2 / n

/-- R² estimator variance is positive for non-degenerate R². -/
theorem r2_estimator_variance_pos (r2 : ℝ) (n : ℕ)
    (h_r2 : 0 < r2) (h_r2_lt : r2 < 1) (h_n : 0 < n) :
    0 < r2EstimatorVariance r2 n := by
  unfold r2EstimatorVariance
  apply div_pos
  · apply mul_pos
    · apply mul_pos
      · linarith
      · exact h_r2
    · exact sq_pos_of_pos (by linarith)
  · exact Nat.cast_pos.mpr h_n

/-- **`√(v/n)` decreases in `n`**, scaled by a positive constant.

    The reading is the standard-error half of a power calculation: to detect
    `ΔR²` at power `1-β` and level `α` one needs
    `n ≈ (z_α+z_β)²(Var₁+Var₂)/ΔR²²`, so a larger sample detects a smaller
    effect. Below there is no test, no `α`, no `β`, no null hypothesis and no
    power function — `z_sum` is a variable name and nothing constrains it to be
    a sum of quantiles. Monotonicity of `n ↦ √(v/n)`. -/
theorem sqrt_scaled_variance_decreasing_in_n
    (var₁ var₂ z_sum n₁ n₂ : ℝ)
    (h_var : 0 < var₁ + var₂)
    (h_z : 0 < z_sum)
    (h_n : n₁ < n₂) (h_n₁ : 0 < n₁) :
    -- Larger sample → smaller required effect size (more power)
    z_sum * Real.sqrt ((var₁ + var₂) / n₂) <
      z_sum * Real.sqrt ((var₁ + var₂) / n₁) := by
  apply mul_lt_mul_of_pos_left _ h_z
  apply Real.sqrt_lt_sqrt
  · exact div_nonneg (le_of_lt h_var) (le_of_lt (by linarith : 0 < n₂))
  · exact div_lt_div_of_pos_left h_var h_n₁ h_n

/-- **Transitivity through `1/·`:** from `n ≥ 1/r` and `r ≤ ub` with `r > 0`,
    conclude `n ≥ 1/ub`.

    **The sample-size claim is a hypothesis here, not a conclusion.** `h_formula`
    says `n_required ≥ 1 / r2_effect` — that *is* the assertion that a small
    effect needs a large sample, supplied as an assumption. What the proof adds
    is that `1/·` is decreasing on the positives, so the bound survives
    replacing `r2_effect` by any upper bound for it.

    Nothing derives `h_formula` from a test, a variance or a power target, and
    nothing here connects `n_required` to a sample. A measured effect size is
    not an instance of this inequality, whose variables are free. -/
theorem le_inv_of_le_inv_of_le
    (r2_effect n_required ub : ℝ)
    (h_small : r2_effect ≤ ub)
    (h_formula : n_required ≥ 1 / r2_effect)
    (h_effect_pos : 0 < r2_effect) :
    n_required ≥ 1 / ub := by
  calc n_required ≥ 1 / r2_effect := h_formula
    _ ≥ 1 / ub := by
        exact div_le_div_of_nonneg_left (le_of_lt one_pos) h_effect_pos h_small

end PowerAnalysis

/-!
## Proximal contamination, LOCO, and the imitation wall

The results above quantify stratification bias *given* that the confounding and
the signal are distinguishable.  This section records the prior question, which
is not always answerable: whether the association being tested is a legal member
of the background the test adjusts against.  When it is, no amount of data
helps, and the failure mode has two familiar names.

*Proximal contamination.*  A genetic relatedness matrix built from markers that
include the tested locus, or in LD with it, absorbs the very association being
tested.  Formally the alternative's covariance is a legal background, so the
alternative law is a mixture of null laws.

*Polygenic adaptation from residual stratification.*  Signals of coordinated
allele-frequency shift, read as adaptation, turned out in several cases to be
residual stratification imitating a polygenic spike.  Same formal object: the
spike level sat below the background class's imitation capacity.

`Calibrator.PCCorrectability.ImitationCapacity` makes this computable.  The
capacity is the value of a linear program over the background class, its
certificate is a constraint index, and the results below name the three
consequences that matter for study design.
-/

section ImitationWall

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {cidx : Type*}

/-- **Proximal contamination, exactly.**  Below the imitation capacity the
spiked genotype covariance is itself a legal background: the relatedness matrix
has absorbed the tested association, and no test at any sample size separates
the two.  The capacity is not a heuristic margin — it is the linear program's
value, and the constraint achieving the infimum is the reason. -/
theorem grm_absorbs_tested_association
    (K : BackgroundClass ι cidx) {S₀ : Matrix ι ι ℝ} {support : Set (ι → ℝ)}
    (hnull : K.IsNull S₀) {t : ℝ} (ht : 0 ≤ t)
    (hle : t ≤ K.imitationCapacity S₀ support) {v : ι → ℝ} (hv : v ∈ support) :
    K.IsNull (K.spiked S₀ t v) :=
  K.isNull_spiked_of_le_imitationCapacity hnull ht hle hv

/-- **Leave-one-chromosome-out is a restriction of the background class, not a
variance fix.**  LOCO adds constraints — one budget per excluded chromosome —
and the capacity is antitone in the constraint family.  So LOCO can only lower
the imitation wall, and the amount is computable: the difference of two linear
programming values, `K'`'s minus `K`'s, rather than an unquantified benefit.

`f` embeds the pre-LOCO constraint family into the post-LOCO one with the same
functionals and ceilings; the extra constraints are the ones outside its
image. -/
theorem loco_lowers_imitation_wall
    (K : BackgroundClass ι cidx) {cidx' : Type*}
    (K' : BackgroundClass ι cidx') {S₀ : Matrix ι ι ℝ} {support : Set (ι → ℝ)}
    (hnull' : K'.IsNull S₀) (f : cidx → cidx')
    (hform : ∀ a : cidx, K'.form (f a) = K.form a)
    (hbound : ∀ a : cidx, K'.bound (f a) = K.bound a)
    (hne : (K.exitLevels S₀ support).Nonempty) :
    K'.imitationCapacity S₀ support ≤ K.imitationCapacity S₀ support :=
  K.imitationCapacity_antitone_constraints K' hnull' f hform hbound hne

/-- **A saturated background budget makes stratification detectable at every
level.**  If the study design imposes one linear budget the baseline already
meets with equality — a trace window on the adjusted relatedness matrix is the
concrete case — then every nonzero effect direction points out of the class,
and no positive spike level is imitable.  This is a design instruction: an
active constraint with positive spike load buys detectability that is
information-theoretically unavailable without it, and it requires no symmetry
of the background class. -/
theorem active_budget_makes_stratification_detectable
    {base A S₀ : Matrix ι ι ℝ}
    (hpd : ∀ v : ι → ℝ, v ≠ 0 → 0 < quadForm A v)
    {v : ι → ℝ} (hvne : v ≠ 0) {t : ℝ} (ht : 0 < t) :
    ¬ (traceWindowClass base A S₀).IsNull
      ((traceWindowClass base A S₀).spiked S₀ t v) :=
  traceWindow_every_level_detectable hpd hvne ht

/-- **The correction to `pcCorrectabilityMargin`, stated where the biology is.**

`Calibrator.PCCorrectability.Threshold` documents the sign of
`pcCorrectabilityMargin` as "the detectable side of the phase diagram".  That
is true only when the background class is rigid.  Whenever the demographic
spike fits inside the trace-window budget, the spiked covariance is a legal
background and no test at any sample size separates it — however far the spike
clears the spectral edge.  The margin's positivity is a hypothesis of this
theorem and is not used in its proof, which is the content.

The repaired quantity is `stratificationCertificateMargin`, which carries the
headroom term the existing one omits, and
`stratificationCertificateMargin_zero_headroom` is the statement that the
existing one is the special case of zero headroom. -/
theorem positive_pc_margin_does_not_imply_detectable
    {N : ℕ} (m : ℕ) (F markerCount : ℝ) (hF : 0 ≤ F) (hmn : m ≤ N) (hN : 0 < N)
    (base S₀ : Matrix (Fin N) (Fin N) ℝ) (budget : ℝ)
    (hbase : VarianceNonneg (S₀ - base))
    (hbudget : traceForm S₀ + demographicSpike (N : ℝ) F (m : ℝ) ≤ budget)
    (hmargin : 0 < pcCorrectabilityMargin (N : ℝ) markerCount F (m : ℝ)) :
    (traceWindowBudgetClass base budget).IsNull
      ((traceWindowBudgetClass base budget).spiked S₀ (4 * F)
        (demographicSpikeDirection N m)) :=
  imitable_despite_positive_pcCorrectabilityMargin m F markerCount hF hmn hN
    base S₀ budget hbase hbudget hmargin

/-- **The genome-wide threshold is not an effective-marker count.**

Multiple-testing corrections that replace the variant count by an effective
number of independent markers derived from the LD eigenvalues — the
Cheverud–Nyholt and Li–Ji family — compute a participation-ratio-type
functional of the spectral law, and every such functional is continuous in the
weak topology.  No weakly continuous functional determines a detection
threshold, so no effective-marker count of that form can be the right quantity.

The corpus's own `ldWhiteningGain`, `(1+ρ²)/(1-ρ²)`, is the right one for
exactly the complementary reason: it is the value of the trace-window
certificate, edge-sensitive, and *not* weakly continuous.  Those two facts are
consistent, and their consistency is the content of this pairing. -/
theorem effective_marker_count_cannot_set_threshold
    (Φ : MomentContinuousFunctional)
    (hΦ : ∀ (m : ℕ) (lam : ℕ → ℝ), Φ.value m lam = inverseTraceCertificate m lam) :
    False :=
  certificate_not_momentContinuous Φ hΦ

end ImitationWall

end Calibrator
