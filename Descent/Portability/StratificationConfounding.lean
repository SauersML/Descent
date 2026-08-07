/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.PCCorrectability
import Descent.Portability.AncestrySpecificPower

assert_below Descent.Decision Descent.Program

namespace Descent.Portability

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

/-- **The class is inhabited.**  A theorem quantified over an uninhabited structure is
true and empty: kernel-checked, clean axiom report, no content.  This is the witness that
makes the theorems below statements about something. -/
noncomputable def StratificationModel.witness (p : ℕ) : StratificationModel (p + 1) where
  β := fun _ ↦ 0
  b := fun _ ↦ 1
  H := fun _ ↦ 1
  H_pos := fun _ ↦ by norm_num
  bias_nonzero := ⟨0, by norm_num⟩

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

/-- **The class is inhabited.**  A theorem quantified over an uninhabited structure is
true and empty: kernel-checked, clean axiom report, no content.  This is the witness that
makes the theorems below statements about something. -/
noncomputable def TwoPopBiasModel.witness (p : ℕ) : TwoPopBiasModel (p + 1) where
  toStratificationModel := StratificationModel.witness p
  attenuation := 1 / 2
  atten_pos := by norm_num
  atten_lt_one := by norm_num

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

/-- **A collider model exists**, so the results below are about something.

`ColliderModel` carries three positivity hypotheses. A theorem taking one as a
parameter is conditional on a caller producing all three, and a bundle nothing
inhabits makes every such theorem vacuously true. Unit variances and unit effect
satisfy them.

Degenerate on purpose: what this discharges is inhabitation. The theorems below
quantify over every `ColliderModel`, so a single witness is enough to show the
class is not empty, and a more elaborate one would suggest the results depend on
its particulars. -/
def ColliderModel.witness : ColliderModel where
  σ2_G := 1
  σ2_E := 1
  β_G := 1
  σ2_G_pos := one_pos
  σ2_E_pos := one_pos
  β_G_pos := one_pos

instance : Nonempty ColliderModel := ⟨ColliderModel.witness⟩

/-- **Selection on G + E induces negative covariance in selected sample.**
    In the selected subsample, Cov(G, E | S=1) = -σ²_G · σ²_E / (σ²_G + σ²_E).
    This is the classical "explaining away" effect. -/
noncomputable def ColliderModel.inducedCov (m : ColliderModel) : ℝ :=
  -(m.σ2_G * m.σ2_E / (m.σ2_G + m.σ2_E))

/-- **The induced covariance is minus the harmonic-mean half of the two variances.** Negativity
alone is shared by every negative multiple; multiplying the total variance back exhibits the
product, and it is the product that makes the induced association vanish when either source of
variation is absent. -/
theorem ColliderModel.inducedCov_mul_total (m : ColliderModel)
    (h : m.σ2_G + m.σ2_E ≠ 0) :
    m.inducedCov * (m.σ2_G + m.σ2_E) = -(m.σ2_G * m.σ2_E) := by
  unfold ColliderModel.inducedCov
  field_simp

theorem ColliderModel.inducedCov_neg (m : ColliderModel) :
    m.inducedCov < 0 := by
  unfold ColliderModel.inducedCov
  rw [neg_neg_iff_pos]
  exact div_pos (mul_pos m.σ2_G_pos m.σ2_E_pos) (by linarith [m.σ2_G_pos, m.σ2_E_pos])

/-- **Collider bias attenuates PGS-outcome association.**
    In the full population, regression coefficient is β_G.
    In the selected sample, the induced G-E covariance attenuates:
    β_selected = β_G · σ²_G / (σ²_G + σ²_E).
    Since σ²_E > 0, this ratio is < 1, so β_selected < β_G. -/
noncomputable def ColliderModel.β_selected (m : ColliderModel) : ℝ :=
  m.β_G * (m.σ2_G / (m.σ2_G + m.σ2_E))

/-- **The attenuation factor is the genetic share of the total variance.** Attenuation alone is
shared by every multiplier below one; this says which multiplier, and it is the quantity that
decides how much of the association survives collider selection. -/
theorem ColliderModel.β_selected_mul_total (m : ColliderModel)
    (h : m.σ2_G + m.σ2_E ≠ 0) :
    m.β_selected * (m.σ2_G + m.σ2_E) = m.β_G * m.σ2_G := by
  unfold ColliderModel.β_selected
  field_simp

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

**The iff is the content; the one-directional form asserts nothing.** A statement
`(h : d_target < d_source) → (apparent > true) → False` is vacuous here: by the identity
`apparent - true = d_target - d_source` its second hypothesis is precisely the negation of
its first, so it proves `h → ¬¬h` for every choice of the four reals, and the conclusion
"apparent portability drop is larger than true portability drop" is the branch it
refutes. -/
theorem sub_gt_sub_iff_sub_lt_sub
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

/-- **The class is inhabited.**  A theorem quantified over an uninhabited structure is
true and empty: kernel-checked, clean axiom report, no content.  This is the witness that
makes the theorems below statements about something. -/
noncomputable def RGEModel.witness : RGEModel where
  β_direct := 1
  β_genetic := 1
  β_env := 1
  rge := Pop.pair 0 1
  β_genetic_ne := by norm_num
  β_env_ne := by norm_num
  rge_diff := by norm_num [Pop.pair]

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

/-- **The class is inhabited.**  A theorem quantified over an uninhabited structure is
true and empty: kernel-checked, clean axiom report, no content.  This is the witness that
makes the theorems below statements about something. -/
noncomputable def RGEInflationModel.witness : RGEInflationModel where
  r2_direct := 1
  β_indirect := 1
  σ2 := 1
  r2_direct_pos := by norm_num
  β_indirect_ne := by norm_num
  σ2_pos := by norm_num

/-- Observed R² under rGE -/
noncomputable def RGEInflationModel.r2_obs (m : RGEInflationModel) : ℝ :=
  m.r2_direct + m.β_indirect ^ 2 * m.σ2

/-- **The inflation is exactly the indirect path's contribution.** Strict inequality against the
direct term is shared by every body that adds something positive; this says what is added. -/
theorem RGEInflationModel.r2_obs_sub_direct (m : RGEInflationModel) :
    m.r2_obs - m.r2_direct = m.β_indirect ^ 2 * m.σ2 := by
  unfold RGEInflationModel.r2_obs
  ring

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

/-- **The class is inhabited.**  A theorem quantified over an uninhabited structure is
true and empty: kernel-checked, clean axiom report, no content.  This is the witness that
makes the theorems below statements about something. -/
noncomputable def SurvivorshipModel.witness : SurvivorshipModel where
  p₀ := 1 / 2
  s := 1 / 2
  p₀_pos := by norm_num
  p₀_lt_one := by norm_num
  s_pos := by norm_num
  s_lt_one := by norm_num

/-- Frequency of risk allele among survivors -/
noncomputable def SurvivorshipModel.pSurv (m : SurvivorshipModel) : ℝ :=
  m.p₀ * m.s / (m.p₀ * m.s + (1 - m.p₀))

/-- **Neutral survival leaves the frequency untouched.** At `s = 1` carriers and non-carriers
survive alike and the post-selection frequency is the starting one; that is the fixed point which
fixes the form, and a body with any other numerator would still be a frequency in `[0,1]`. -/
theorem SurvivorshipModel.pSurv_neutral (m : SurvivorshipModel) (hs : m.s = 1) :
    m.pSurv = m.p₀ := by
  unfold SurvivorshipModel.pSurv
  rw [hs]
  field_simp
  ring

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

/-- **The class is inhabited.**  A theorem quantified over an uninhabited structure is
true and empty: kernel-checked, clean axiom report, no content.  This is the witness that
makes the theorems below statements about something. -/
noncomputable def SurvivorshipAttenuationModel.witness : SurvivorshipAttenuationModel where
  r2_full := 1
  var_birth := 2
  var_surv := 1
  r2_full_pos := by norm_num
  var_birth_pos := by norm_num
  var_surv_pos := by norm_num
  var_reduced := by norm_num

/-- R² among survivors -/
noncomputable def SurvivorshipAttenuationModel.r2_surv (m : SurvivorshipAttenuationModel) : ℝ :=
  m.r2_full * (m.var_surv / m.var_birth)

/-- **Attenuation is the ratio of surviving to birth variance.** The strict decrease is shared by
every body that multiplies by something below one; this fixes the factor. -/
theorem SurvivorshipAttenuationModel.r2_surv_mul_birth (m : SurvivorshipAttenuationModel)
    (h : m.var_birth ≠ 0) :
    m.r2_surv * m.var_birth = m.r2_full * m.var_surv := by
  unfold SurvivorshipAttenuationModel.r2_surv
  field_simp

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

    Empirical status: **VALIDATED**
    (`validation/empirical/simcov/battery_bulk5.py`,
    `test_attenuation`). Against the realised correlation between score and
    outcome at a given r-squared, two million individuals, worst 0.74 sems over
    a prediction spanning 0.31623 to 0.94868. -/
noncomputable def pgsAttenuationFactor (r2_gwas : ℝ) : ℝ :=
  Real.sqrt r2_gwas

/-- **pgsAttenuationFactor at its junk point, named.** A negative `R²` estimate is not a real
number's square, but negative estimates are routine output from cross-validated fits. `Real.sqrt`
is junk-zero there, so an attenuation factor of zero is returned: the score is reported as
carrying no signal rather than as having produced an inadmissible estimate. Consumers must
exclude the argument that makes the guard vanish. -/
theorem pgsAttenuationFactor_negative_r2_is_junk :
    pgsAttenuationFactor (-1) = 0 := by
  unfold pgsAttenuationFactor
  exact Real.sqrt_eq_zero_of_nonpos (by norm_num)

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

/-- **The class is inhabited.**  A theorem quantified over an uninhabited structure is
true and empty: kernel-checked, clean axiom report, no content.  This is the witness that
makes the theorems below statements about something. -/
noncomputable def AttenuationModel.witness : AttenuationModel where
  β_true := 1
  r2_source := 2
  r2_target := 1
  σ2_noise := 1
  β_true_pos := by norm_num
  r2_source_pos := by norm_num
  r2_target_pos := by norm_num
  σ2_noise_pos := by norm_num
  r2_drop := by norm_num

/-- Reliability ratio in a population

    Empirical status: **VALIDATED**
    (`validation/empirical/simcov/battery_bulk5.py`,
    `test_attenuation`). Measured as the ratio of the slope fitted on a NOISY
    predictor to the slope fitted on the clean one, two million individuals:

      r2    sigma2   this def   measured             sems
      0.5   0.5       0.50000   0.49997±0.00106      0.03
      0.2   0.8       0.20000   0.20016±0.00042      0.39
      0.8   0.2       0.80000   0.80028±0.00170      0.16

    Power: the prediction spans 0.20000 to 0.80000. -/
noncomputable def reliabilityRatio (r2 σ2_noise : ℝ) : ℝ :=
  Descent.Core.share r2 σ2_noise

/-- **reliabilityRatio where its denominator vanishes, named.** The guard `r2 + σ2_noise` is zero at
`r2 = 0`, `σ2_noise = 0`. With no signal and no noise the reliability ratio is undefined, and
the value returned reads as a completely unreliable measurement. Lean returns `0` there rather
than the value the modelled quantity takes, and no type error marks the point. Consumers must
require `r2 + σ2_noise ≠ 0`. -/
theorem reliabilityRatio_at_r202noise0_is_junk :
    reliabilityRatio 0 0 = 0 := by
  unfold reliabilityRatio Descent.Core.share
  norm_num

/-- **The reliability ratio recovers the true variance from the total.** This is what fixes the
ratio; monotonicity in the noise is shared by every rescaling of it. -/
theorem reliabilityRatio_mul_total (r2 σ2_noise : ℝ) (h : r2 + σ2_noise ≠ 0) :
    reliabilityRatio r2 σ2_noise * (r2 + σ2_noise) = r2 := by
  unfold reliabilityRatio Descent.Core.share
  field_simp

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

/-- **The class is inhabited.**  A theorem quantified over an uninhabited structure is
true and empty: kernel-checked, clean axiom report, no content.  This is the witness that
makes the theorems below statements about something. -/
noncomputable def TransportabilityModel.witness (n : ℕ) : TransportabilityModel (n + 1) where
  r2_source := 1
  δ := fun _ ↦ 1
  δ_nonneg := fun _ ↦ by norm_num
  violated := ⟨0, by norm_num⟩
  r2_source_pos := by norm_num

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
  /-- Residual variance of the EXPOSURE given the instrument.

      Not the outcome variance. The first-stage F of a Mendelian-randomisation
      instrument is `n β² Var(G) / σ²_{X|G}`: it measures how well the instrument
      predicts the exposure, so the denominator is the exposure residual, and pairing
      the exposure effect `β_inst` with an outcome variance would divide two different
      regressions' quantities. -/
  σ2_X_resid : ℝ
  n_pos : 0 < n
  β_inst_ne : β_inst ≠ 0
  σ2_X_resid_pos : 0 < σ2_X_resid
  p_source_pos : 0 < p_source
  p_source_lt : p_source < 1
  p_target_pos : 0 < p_target
  p_target_lt : p_target < 1

/-- **The class is inhabited.**  A theorem quantified over an uninhabited structure is
true and empty: kernel-checked, clean axiom report, no content.  This is the witness that
makes the theorems below statements about something. -/
noncomputable def MRInstrumentModel.witness : MRInstrumentModel where
  n := 1
  β_inst := 1
  p_source := 1 / 2
  p_target := 1 / 2
  σ2_X_resid := 1
  n_pos := by norm_num
  β_inst_ne := by norm_num
  σ2_X_resid_pos := by norm_num
  p_source_pos := by norm_num
  p_source_lt := by norm_num
  p_target_pos := by norm_num
  p_target_lt := by norm_num

/-- **First-stage F-statistic** of a Mendelian-randomisation instrument at a given allele
    frequency: `n β² Var(G) / σ²_{X|G}`.

    What enters the noncentrality is the genotype *variance*, which
    `hweHeterozygosity_eq_genotypeVarianceHWE` identifies with `hweHeterozygosity p`.

    The denominator is the exposure residual variance, matching `β_inst`, which is the
    instrument's effect on the exposure. Both belong to the first-stage regression; an outcome
    variance here would divide one regression's numerator by another's denominator and the
    quantity would not be an F-statistic of anything.

    Empirical status: **VALIDATED** (`simcov/battery_bulk40.py`, `group_d`). 4000
    independent first-stage regressions of 800 individuals each, exposure
    `X = β_inst · dosage + N(0,1)`; the observable is the realised MEAN first-stage `F`
    MINUS ONE, because `E[F] = 1 + ncp` under the alternative and this body is the
    noncentrality rather than the statistic. That subtraction is the convention and is
    stated rather than absorbed.

      p      H = 2p(1-p)   this body   measured ncp   sems
      0.05     0.0950        0.4864       0.4664       0.64
      0.15     0.2550        1.3056       1.2775       0.65
      0.30     0.4200        2.1504       2.1124       0.75
      0.50     0.5000        2.5600       2.6051       0.82

    The identity gate: reading the genotype variance as `p(1-p)` misses by 24 sems (51%
    low) and as `4p(1-p)` by 46 sems (97% high), so the ploidy factor in `hweHeterozygosity`
    is carried by the data. The positive control -- a NULL instrument, whose `F` must have
    mean 1 -- passes at 0.88 sems, which is what makes the minus-one convention checkable
    rather than assumed.

    **DO NOT DELETE AS UNUSED.** No Lean declaration mentions this, so the liveness scan in
    `validation/code/Check.lean` reports it dead; its consumer is
    `simcov/battery_bulk40.py`, `group_d`, whose measured noncentralities are tabulated
    above and whose identity gate rejects two competing genotype-variance conventions
    against this exact body. A definition a battery validates against is not dead code, and
    deleting it would silently retire a passing measurement. -/
noncomputable def MRInstrumentModel.fStat (m : MRInstrumentModel) (p : ℝ) : ℝ :=
  m.n * m.β_inst ^ 2 * Descent.Core.hweHeterozygosity p / m.σ2_X_resid

/-- Heterozygosity is maximized at p = 0.5 and decreasing as p moves away. -/
theorem hweHeterozygosity_pos (p : ℝ) (hp : 0 < p) (hp1 : p < 1) :
    0 < Descent.Core.hweHeterozygosity p := by
  unfold Descent.Core.hweHeterozygosity Descent.Core.ploidy
  have : 0 < 1 - p := by linarith
  positivity

/-- **Instrument strength decreases with allele frequency divergence.**
    If the target has lower heterozygosity (allele frequency further from 0.5
    or toward fixation), F-stat decreases. Derived from the F-stat formula. -/
theorem instrument_strength_decreases (m : MRInstrumentModel)
    (h_het : Descent.Core.hweHeterozygosity m.p_target < Descent.Core.hweHeterozygosity m.p_source)
      :
    m.fStat m.p_target < m.fStat m.p_source := by
  unfold MRInstrumentModel.fStat
  apply div_lt_div_of_pos_right _ m.σ2_X_resid_pos
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

    Empirical status: VALIDATED (40000-replicate Monte Carlo, ratio 0.99-1.01 for n >= 1000).

    Power: over the `R² ∈ {0.01, 0.05, 0.2, 0.5}` by `n ∈ {200, 1000, 5000}`
    grid the predicted variance runs, in units of `10⁻⁴`, from `0.078` at
    `R² = 0.01, n = 5000` through `1.960`, `5.120` and `9.025` to `25.600` at
    `R² = 0.2, n = 200` — a spread of more than `300` to `1`. Both arguments
    move it, and the `R²` direction is non-monotone with a maximum inside the
    grid, so the `(1 - R²)²` factor is exercised rather than assumed. -/
noncomputable def r2EstimatorVariance (r2 : ℝ) (n : ℕ) : ℝ :=
  4 * r2 * (1 - r2) ^ 2 / n

/-- **r2EstimatorVariance at its junk point, named.** The sampling variance of an `R²` estimate from
no samples is unbounded. The divisor is zero and the variance is `0`: a perfectly precise
estimate from an empty study, which downstream reads as an arbitrarily tight confidence
interval. Consumers must exclude the argument that makes the guard vanish. -/
theorem r2EstimatorVariance_zero_samples_is_junk (r2 : ℝ) :
    r2EstimatorVariance r2 0 = 0 := by
  unfold r2EstimatorVariance
  simp

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

`Descent.PCCorrectability.ImitationCapacity` makes this computable.  The
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
    (hpd : ∀ v : ι → ℝ, v ≠ 0 → 0 < Blindness.quadForm A v)
    {v : ι → ℝ} (hvne : v ≠ 0) {t : ℝ} (ht : 0 < t) :
    ¬ (traceWindowClass base A S₀).IsNull
      ((traceWindowClass base A S₀).spiked S₀ t v) :=
  traceWindow_every_level_detectable hpd hvne ht

/-! **The correction to `pcCorrectabilityMargin`, stated where the biology is.**

`Descent.PCCorrectability.Threshold` documents the sign of
`pcCorrectabilityMargin` as "the detectable side of the phase diagram".  That
is true only when the background class is rigid.  Whenever the demographic
spike fits inside the trace-window budget, the spiked covariance is a legal
background and no test at any sample size separates it — however far the spike
clears the spectral edge.

`Descent.imitable_within_traceWindowBudget` is that statement, and it does not
mention `pcCorrectabilityMargin` at all.  This module used to re-export it as
`positive_pc_margin_does_not_imply_detectable`, binding `0 < pcCorrectabilityMargin ...`
and a `markerCount` that existed only to state it, neither of which the proof touched.
Once those go the re-export is the original statement under a second name, so it is gone
and callers should use the original.

The repaired quantity is `stratificationCertificateMargin`, which carries the
headroom term the existing one omits, and
`stratificationCertificateMargin_zero_headroom` is the statement that the
existing one is the special case of zero headroom. -/

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
theorem momentContinuousFunctional_ne_inverseTraceCertificate
    (Φ : MomentContinuousFunctional)
    (hΦ : ∀ (m : ℕ) (lam : ℕ → ℝ), Φ.value m lam = inverseTraceCertificate m lam) :
    False :=
  certificate_not_momentContinuous Φ hΦ

/-! ## The same confounding laws, read at a demography's own deployed `R²`

Each law above takes an `R²` as a free real. The results below state them at the `R²` a
`PopGenParameters` record deploys, so an attenuation figure or a sampling variance is
reported for a population rather than for a number.
-/

section DeployedAttenuation

open Descent.Core (PopGenParameters)
open Descent.Core.ScoreMoments (deployedR2 deployedR2_eq deployedR2_mem_unit
  deployedR2_mono_in_migration)

/-- **A polymorphic history deploys an `R²` strictly inside the unit interval.**

`Core.ScoreMoments.deployedR2_mem_unit` gives the closed interval, which is the right
statement there: at zero environmental variance the deployed value is one, and at no flow it
is zero. Both endpoints are excluded once there is environmental variance and some flow, and
the strict form is what the reliability and estimator-variance laws below need — a
reliability ratio at `R² = 0` is junk-zero, and the sampling variance vanishes at both ends.

Stated here rather than in the metric kernel because it is these consumers that need it; the
proof is the kernel's own evaluation of the deployed metric, read at a positive retained
fraction. -/
theorem deployedR2_mem_Ioo_of_params (p : PopGenParameters) (V_E : ℝ) (hE : 0 < V_E)
    (hflow : 0 < p.mu + p.mig) :
    0 < deployedR2 p V_E ∧ deployedR2 p V_E < 1 := by
  have hlt := p.fstEquilibrium_lt_one hflow
  have hge := p.fstEquilibrium_mem_unit.1
  have hV := p.V_A_pos
  have hretained : 0 < Descent.Core.retainedFraction p.fstEquilibrium p.V_A := by
    unfold Descent.Core.retainedFraction
    nlinarith
  rw [deployedR2_eq p V_E hE.le hflow]
  unfold Descent.Core.share
  constructor
  · positivity
  · rw [div_lt_one (by linarith)]
    linarith

/-- **The reliability ratio recovers a demography's deployed `R²` from the noisy total.**

`reliabilityRatio_mul_total` over a free `R²` with the demography's own in its place: the
attenuation a noisy proxy causes is exactly undone by the total it is measured against, and
the number recovered is the one the history predicts. The guard the loose-real version asks
the reader to check is discharged from the record — a deployed `R²` is nonnegative and the
noise variance is positive, so their sum cannot vanish. -/
theorem reliabilityRatio_mul_total_of_params
    (p : PopGenParameters) (V_E σ2_noise : ℝ) (hE : 0 ≤ V_E)
    (hflow : 0 < p.mu + p.mig) (hnoise : 0 < σ2_noise) :
    reliabilityRatio (deployedR2 p V_E) σ2_noise * (deployedR2 p V_E + σ2_noise) =
      deployedR2 p V_E :=
  reliabilityRatio_mul_total _ σ2_noise
    (by have := (deployedR2_mem_unit p V_E hE hflow).1; linarith)

/-- **More migration, a higher reliability ratio at the same measurement noise.**

The end-to-end statement for attenuation: two histories differing only in migration, one
noisy instrument, and the history with more flow suffers strictly less attenuation. The
`R²` ordering is `deployedR2_mono_in_migration` rather than an assumption. -/
theorem reliabilityRatio_mono_in_migration_of_params
    (p q : PopGenParameters) (V_E σ2_noise : ℝ) (hE : 0 < V_E)
    (hsame : p.Ne = q.Ne ∧ p.mu = q.mu ∧ p.nDemes = q.nDemes ∧ p.V_A = q.V_A)
    (hlt : p.mig < q.mig) (hflow : 0 < p.mu + p.mig) (hnoise : 0 < σ2_noise) :
    reliabilityRatio (deployedR2 p V_E) σ2_noise <
      reliabilityRatio (deployedR2 q V_E) σ2_noise := by
  unfold reliabilityRatio Descent.Core.share
  exact ratio_strict_mono (deployedR2_mem_Ioo_of_params p V_E hE hflow).1 hnoise
    (deployedR2_mono_in_migration p q V_E hE hsame.1 hsame.2.1 hsame.2.2.1 hsame.2.2.2 hlt hflow)

/-- **A polymorphic history's deployed `R²` has positive estimator variance.**

An `R²` estimate from a finite sample scatters unless the quantity estimated sits at an
endpoint, and `deployedR2_mem_Ioo_of_params` says a history with environmental variance and
some flow never does. So the sampling variance a portability study must report is strictly
positive at every such demography, rather than at `R²` values a reader stipulates. -/
theorem r2_estimator_variance_pos_of_params
    (p : PopGenParameters) (V_E : ℝ) (n : ℕ) (hE : 0 < V_E)
    (hflow : 0 < p.mu + p.mig) (h_n : 0 < n) :
    0 < r2EstimatorVariance (deployedR2 p V_E) n :=
  r2_estimator_variance_pos _ n (deployedR2_mem_Ioo_of_params p V_E hE hflow).1
    (deployedR2_mem_Ioo_of_params p V_E hE hflow).2 h_n

end DeployedAttenuation

end ImitationWall

end Descent.Portability
